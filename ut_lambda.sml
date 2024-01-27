datatype term =
    True
    | False
    | If     of term * term * term
    | Zero
    | Succ   of term
    | Pred   of term
    | IsZero of term
    | Var    of string
    | Lambda of string * term
    | App    of term * term
    | Let    of term * term
    | Fix    of term

(* LEXER *)

datatype token =
    TRUE     | FALSE
    | IF     | THEN     | ELSE
    | ZERO   | SUCC     | PRED | ISZERO
    | VAR    | LAMBDA   | APP  | LET    |IN   | FIX (*WIP*)
    | LPAREN | RPAREN
    | EOF

exception LexError of string
exception ParseError of string

fun lexer (input : string) =
    let
        val keywords = ["true", "false", "if", "then", "else", 0, "succ", "pred", "iszero", "(", ")", 
        (*WIP*) "lambda", "app", "let", "fix", (*WIP*)"EOF"]
        val rec tokenize str =
            case str of
            [] => []
            | #" " :: rest => tokenize rest
            | #"\n" :: rest => tokenize rest
            | #"t" :: #"r" :: #"u" :: #"e" :: rest => TRUE :: tokenize rest
            | #"f" :: #"a" :: #"l" :: #"s" :: #"e" :: rest => FALSE :: tokenize rest
            | #"i" :: #"f" :: rest => IF :: tokenize rest
            | #"t" :: #"h" :: #"e" :: #"n" :: rest => THEN :: tokenize rest
            | #"e" :: #"l" :: #"s" :: #"e" :: rest => ELSE :: tokenize rest
            | #"0" :: rest => ZERO :: tokenize rest
            | #"s" :: #"u" :: #"c" :: #"c" :: rest => SUCC :: tokenize rest
            | #"p" :: #"r" :: #"e" :: #"d" :: rest => PRED :: tokenize rest
            | #"i" :: #"s" :: #"z" :: #"e" :: #"r" :: #"o" :: rest => ISZERO :: tokenize rest
            | #"(" :: rest => LPAREN :: tokenize rest
            | #")" :: rest => RPAREN :: tokenize rest
            | #"l" :: #"a" :: #"m" :: #"b" :: #"d" :: #"a" :: rest => LAMBDA :: tokenize rest
            | #"a" :: #"p" :: #"p" :: rest => APP :: tokenize rest
            | #"l" :: #"e" :: #"t" :: rest => LET :: tokenize rest
            | #"i" :: #"n" :: rest => IN :: tokenize rest
            | #"f" :: #"i" :: #"x" :: rest => FIX :: tokenize rest
            | _ :: rest => (* WIP *)
                let 
                    val (var, rest') = extractVar (fn x => not (Char.isSpace x)) rest
                in
                    VAR (String.implode (var)) :: tokenize rest'
                end

        fun extractVar notSpace str = (* WIP *)
            case str of
            [] => ("", [])
            | x :: xs =>
            if notSpace x then
                let
                    val (rest, _) = extractVar notSpace xs
                in
                    (String.str x ^ rest, xs) (* WIP *)
                end
            else
                ("", str)
    in
        tokenize (explode input) @ [EOF]
    end

(* PARSER *)

fun parse (tokens : token list) : term =
  let
    fun parseExpr tokens =
        case tokens of
        TRUE :: rest => (True, rest)
        | FALSE :: rest => (False, rest)
        | IF :: rest =>
        let
            val (t1, rest1) = parseExpr rest
            val rest2 = eat THEN rest1
            val (t2, rest3) = parseExpr rest2
            val rest4 = eat ELSE rest3
            val (t3, rest5) = parseExpr rest4
        in
            (If (t1, t2, t3), rest5)
        end
        | ZERO :: rest => (Zero, rest)
        | SUCC :: rest =>
            let
                val (t, rest1) = parseExpr rest
            in
                (Succ t, rest1)
            end
        | PRED :: rest =>
            let
                val (t, rest1) = parseExpr rest
            in
                (Pred t, rest1)
            end
        | ISZERO :: rest =>
            let
                val (t, rest1) = parseExpr rest
            in
                (IsZero t, rest1)
            end
        | LPAREN :: rest =>
            let
                val (t, rest1) = parseExpr rest
                val rest2 = eat RPAREN rest1
            in
                (t, rest2)
            end
        | LAMBDA :: rest =>
            let
                val (t1, rest1) = extractVar (fn x => not (Char.isSpace x)) rest
                val rest2 = eat VAR rest1
                val (t2, rest3) = parseExpr rest2
            in
                (Lambda (t1, t2), rest2)
            end
        | APP :: rest =>
            let
                val (t1, rest1) = parseExpr rest
                val rest2 = eat VAR rest1
                val (t2, rest3) = parseExpr rest2
            in
                (App (t1,t2), rest3)
            end
        | LET :: rest =>
            let
                val (t1, rest1) = parseExpr rest
                val rest2 = eat IN rest1
                val (t2, rest3) = parseExpr rest2
            in
                (Let (t1, t2), rest3)
            end
        | FIX :: rest =>
            let
                val (t, rest1) = parseExpr rest
            in
                (Fix t, rest1)
            end
        | VAR :: rest =>
            let
                val (t, rest1) = extractVar (fn x => not (Char.isSpace x)) rest
            in
                (Var t, rest1)
            end
        | _ => raise (ParseError "Unexpected token")

    fun eat expected rest =
        case rest of
        [] => raise (ParseError "Unexpected end of input")
        | tok :: rest' =>
        if tok = expected then rest' else raise (ParseError "Unexpected token")

    in
        case parseExpr tokens of
            (term, []) => term
            | _ => raise (ParseError "Unused tokens after parsing")
    end

(* EVALUATOR *)

datatype value =
    Bool      of bool
    | Int     of int
    | Closure of string * term * environment

type environment = (string * value) list


exception EvalError of string

fun lookupVal env var =
    case List.find (fn (v, _) => v = var) env of
    SOME (_, value) => value
    | NONE => raise (EvalError ("Variable not bound " ^ var))

fun extendEnv var val env = (var, val) :: env

fun varConfirm (t : term) = 
    case t of Var x => x 
    | _ => raise EvalError "Expected variable binding in let expression"

fun eval (t : term) =
    let
        fun evalTerm t env =
            case t of 
                True => Bool true
                | False => Bool false
                | If (t1, t2, t3) => 
                    (case eval t1 env of 
                    Bool true => eval t2 env
                    | Bool false => eval t3 env
                    | _ => raise (EvalError "Condition of if expression must be a boolean value"))
                | Zero => Int 0
                | Succ t' => 
                    (case eval t' env of Int n => Int (n + 1)
                    | _ => raise (EvalError "Argument of succ must be an integer value"))
                | Pred t' =>
                    (case eval t' env of Int 0 => 0
                    | Int n => Int (n - 1)
                    | _ => raise (EvalError "Argument of pred must be an integer value"))
                | IsZero t' =>
                    (case eval t' env of Int 0 => Bool true
                    | Int _ => Bool false
                    | _ => raise (EvalError "Argument of iszero must be an integer value"))
                | Lambda (var, body) => Closure (var, body, env)
                | App (t1, t2) => 
                    case evalTerm t1 env of Closure (var, body, lambdaEnv) => 
                        evalTerm body (extendEnv var (evalTerm t2 env)) lambdaEnv (* WIP *)
                    | Var x => case lookupVar env x of Closure (var, body, lambdaEnv) => 
                        evalTerm body (extendEnv var (evalTerm t2 env)) lambdaEnv (* WIP *)
                    | _ => raise (EvalError "Applying a non-lambda abstraction")
                | Let (t1, t2) => 
                    let
                        val v1 = evalTerm t1 env
                    in
                        evalTerm t2 (extendEnv (varConfirm t1) v1 env) (* CHECKS THAT TERM IS A VARIABLE *)
                    end
                | Fix t' => (* WIP *)
                    let
                        val fixClosure = Closure ("fix", t', env)
                    in
                        evalTerm t' (extendEnv "fix" fixClosure env)
                    end
    in
        evalTerm t []
    end
;