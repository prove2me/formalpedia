-- Prove2me | Definitions.Def_MetaSearch_Heyting_Machine
-- name    : MetaSearch_Heyting_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:20:35.411108+00:00
-- url     : https://prove2.me/theorems/7dcc5b84-87df-4166-925d-13c572fa30c8
-- title:
--   Binary strings, the pairing ⟨x, y⟩, multi-tape Turing machines with binary codes, and step-counted runs
-- statement:
--   Strings are finite bit strings $x\in\{0,1\}^*$ (`List Bool`, with `false` the bit $0$), and $|x|$ is the length. The **pairing** of two strings is
--   $$\langle x,y\rangle \;=\; x_1x_1\,x_2x_2\cdots x_nx_n\;01\;y,$$
--   each bit of $x$ doubled, then the separator $01$, then $y$; it is injective and decodable in linear time. The **polynomial growth rates** are $p_k(n)=n^k+k$ for $k\in\mathbb N$.
--
--   All machines are deterministic **multi-tape Turing machines** over the tape alphabet $\{\sqcup,0,1\}$ ($\sqcup$ the blank). A machine has $T+1$ two-way infinite tapes and a finite list of rules; a rule says: in state $q$, scanning the symbols $(a_0,\dots,a_T)$ on the tapes, go to state $q'$, write a symbol on each tape and move each head left, right or not at all. The run on input $x$ starts in state $0$ with $x$ on tape $0$ (head on its first cell) and the other tapes blank. In each step the first rule whose state and scanned symbols match is applied; the machine **halts** when no rule applies. $M$ **halts within $t$ steps** on $x$ if it reaches a halted configuration after at most $t$ steps; its **output** is then the string of bits on tape $0$ from the head rightwards up to the first blank. `evalWithin M x t` is that output if $M$ halts within $t$ steps, and `none` otherwise ("$M(x)$ takes more than $t$ steps").
--
--   Every machine has a **code** $\langle M\rangle\in\{0,1\}^*$: the machine is written as a list of natural numbers (number of tapes, number of rules, then each rule with its states, scanned symbols, written symbols and moves, every list length-prefixed), and each number $n$ is written as $1^n0$. `decode` reads a string back: `decode c = some M` when $c$ is a code of $M$, and `none` when $c$ is not a code ("poorly formatted"). Decoding inverts encoding, `decode (encode M) = some M`.
--
--   This model is used for everything: polynomial-time functions, verifiers, polynomial-time algorithms, and the machines given as inputs to the refutation tasks.
--
--   **Formalization Note.** The paper fixes no model; a multi-tape model is chosen so that reformatting an input or padding a code costs linear time, as the proof of Lemma 3.8 uses. Machines with the same behaviour but extra rules that never apply have longer codes, which is how a code is padded. Inputs of two arguments $g(x,y)$ are run on $\langle x,y\rangle$.
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), pp. 6-7 (Definitions 1.1-1.2, footnotes 5-6), p. 15 (p_k), pp. 22-25 (Definitions 3.2, 3.7)

import Mathlib

namespace MetaSearch.Heyting

/-! # Binary strings, the pairing `⟨x, y⟩`, multi-tape Turing machines, their codes and
step-counted runs

Strings are `List Bool` (`false` is the bit `0`, `true` the bit `1`). One concrete deterministic
multi-tape Turing machine model is used for everything: polynomial-time functions, verifiers,
`FP` algorithms, and the machines `⟨A⟩`, `⟨f, g⟩` given as inputs to the refutation tasks. -/

/-- The pairing `⟨x, y⟩` of two strings: every bit of `x` doubled, then the separator `01`,
then `y`. It is injective and decodable in linear time. -/
def pair (x y : List Bool) : List Bool :=
  x.flatMap (fun b => [b, b]) ++ [false, true] ++ y

/-- The polynomial growth rate `p_k(n) = n^k + k`. -/
def p (k n : ℕ) : ℕ := n ^ k + k

/-- A tape symbol: `none` is the blank, `some b` the bit `b`. -/
abbrev Sym := Option Bool

/-- A head move. -/
inductive Dir
  | left
  | stay
  | right
  deriving DecidableEq

/-- A two-way infinite tape: the cells left of the head (nearest first), the scanned cell, and
the cells right of the head (nearest first); all other cells are blank. -/
structure Tape where
  left : List Sym
  head : Sym
  right : List Sym

/-- The blank tape. -/
def Tape.blank : Tape := ⟨[], none, []⟩

/-- The tape holding the string `x` (as bits), head on its first cell. -/
def Tape.ofString (x : List Bool) : Tape :=
  match x with
  | [] => ⟨[], none, []⟩
  | b :: x => ⟨[], some b, x.map some⟩

/-- Write a symbol into the scanned cell. -/
def Tape.write (s : Sym) (t : Tape) : Tape := ⟨t.left, s, t.right⟩

/-- Move the head one cell. -/
def Tape.move : Dir → Tape → Tape
  | .left, ⟨[], h, r⟩ => ⟨[], none, h :: r⟩
  | .left, ⟨a :: l, h, r⟩ => ⟨l, a, h :: r⟩
  | .stay, t => t
  | .right, ⟨l, h, []⟩ => ⟨h :: l, none, []⟩
  | .right, ⟨l, h, a :: r⟩ => ⟨h :: l, a, r⟩

/-- The bits from a list of cells up to (excluding) the first blank. -/
def bitsUntilBlank : List Sym → List Bool
  | [] => []
  | none :: _ => []
  | some b :: l => b :: bitsUntilBlank l

/-- The string written on a tape: the bits from the scanned cell rightwards up to the first
blank. -/
def Tape.output (t : Tape) : List Bool := bitsUntilBlank (t.head :: t.right)

/-- A transition rule: in state `q`, scanning `read` (one symbol per tape, tape `0` first),
go to state `q'`, write `write` and move `move` (entry `i` for tape `i`; a missing entry
means "rewrite the scanned symbol" resp. "stay"). -/
structure Rule where
  q : ℕ
  read : List Sym
  q' : ℕ
  write : List Sym
  move : List Dir

/-- A deterministic multi-tape Turing machine with `numTapes + 1` tapes (tape `0` is the
input/output tape), start state `0`, and a list of rules. The first rule whose state and
scanned symbols match applies; the machine halts when no rule applies. -/
structure Machine where
  numTapes : ℕ
  rules : List Rule

/-- A configuration: the state and the tapes. -/
structure Config where
  state : ℕ
  tapes : List Tape

/-- The start configuration on input `x`: state `0`, `x` on tape `0`, all other tapes blank. -/
def Machine.init (M : Machine) (x : List Bool) : Config :=
  ⟨0, Tape.ofString x :: List.replicate M.numTapes Tape.blank⟩

/-- The rule that applies in configuration `c`, if any. -/
def Machine.findRule (M : Machine) (c : Config) : Option Rule :=
  M.rules.find? (fun r => decide (r.q = c.state ∧ r.read = c.tapes.map Tape.head))

/-- One step of `M`; `none` when `c` is halted (no rule applies). -/
def Machine.step (M : Machine) (c : Config) : Option Config :=
  (M.findRule c).map fun r =>
    ⟨r.q', c.tapes.mapIdx fun i t =>
      (t.write (r.write.getD i t.head)).move (r.move.getD i Dir.stay)⟩

/-- Run `M` for at most `t` steps from `c` (stopping early at a halted configuration). -/
def Machine.runFor (M : Machine) : ℕ → Config → Config
  | 0, c => c
  | t + 1, c =>
    match M.step c with
    | none => c
    | some c' => M.runFor t c'

/-- The output of `M` on input `x` if the run halts within `t` steps (`some` of the string on
tape `0` from the head up to the first blank), and `none` if it has not halted after `t`
steps. -/
def Machine.evalWithin (M : Machine) (x : List Bool) (t : ℕ) : Option (List Bool) :=
  let c := M.runFor t (M.init x)
  match M.step c with
  | none => some ((c.tapes.headD Tape.blank).output)
  | some _ => none

/-! ### The binary code `⟨M⟩` of a machine

A machine is first written as a list of natural numbers
`[numTapes, #rules, rule₁, rule₂, …]`, each rule as
`[q, q', |read|, read…, |write|, write…, |move|, move…]` (blank `0`, bit `0` ↦ `1`,
bit `1` ↦ `2`; left `0`, stay `1`, right `2`), and each number `n` is written as `1ⁿ0`. -/

/-- The number of a symbol. -/
def symToNat : Sym → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- The symbol of a number (`none` for a number that names no symbol). -/
def natToSym : ℕ → Option Sym
  | 0 => some none
  | 1 => some (some false)
  | 2 => some (some true)
  | _ => none

/-- The number of a move. -/
def dirToNat : Dir → ℕ
  | .left => 0
  | .stay => 1
  | .right => 2

/-- The move of a number. -/
def natToDir : ℕ → Option Dir
  | 0 => some .left
  | 1 => some .stay
  | 2 => some .right
  | _ => none

/-- A rule as a list of numbers. -/
def Rule.toNats (r : Rule) : List ℕ :=
  [r.q, r.q', r.read.length] ++ r.read.map symToNat ++ [r.write.length] ++
    r.write.map symToNat ++ [r.move.length] ++ r.move.map dirToNat

/-- A machine as a list of numbers. -/
def Machine.toNats (M : Machine) : List ℕ :=
  [M.numTapes, M.rules.length] ++ M.rules.flatMap Rule.toNats

/-- A list of numbers as bits, each `n` as `1ⁿ0`. -/
def natsToBits (l : List ℕ) : List Bool :=
  l.flatMap fun n => List.replicate n true ++ [false]

/-- Read back a list of numbers from bits (`acc` counts the `1`s of the current number);
`none` if the bits end inside a number. -/
def bitsToNatsAux : ℕ → List Bool → Option (List ℕ)
  | 0, [] => some []
  | _ + 1, [] => none
  | n, true :: bs => bitsToNatsAux (n + 1) bs
  | n, false :: bs => (bitsToNatsAux 0 bs).map (n :: ·)

/-- Read back a list of numbers from bits. -/
def bitsToNats (bs : List Bool) : Option (List ℕ) := bitsToNatsAux 0 bs

/-- Read a length-prefixed list `[n, a₁, …, aₙ]` off the front, decoding each entry. -/
def parseList {α : Type} (dec : ℕ → Option α) : List ℕ → Option (List α × List ℕ)
  | [] => none
  | n :: l =>
    if n ≤ l.length then (((l.take n).mapM dec).map fun xs => (xs, l.drop n)) else none

/-- Read one rule off the front. -/
def parseRule : List ℕ → Option (Rule × List ℕ)
  | q :: q' :: l =>
    match parseList natToSym l with
    | none => none
    | some (rd, l) =>
      match parseList natToSym l with
      | none => none
      | some (wr, l) =>
        match parseList natToDir l with
        | none => none
        | some (mv, l) => some (⟨q, rd, q', wr, mv⟩, l)
  | _ => none

/-- Read `n` rules off the front. -/
def parseRules : ℕ → List ℕ → Option (List Rule × List ℕ)
  | 0, l => some ([], l)
  | n + 1, l =>
    match parseRule l with
    | none => none
    | some (r, l) =>
      match parseRules n l with
      | none => none
      | some (rs, l) => some (r :: rs, l)

/-- Read a machine from a list of numbers; the whole list must be consumed. -/
def natsToMachine : List ℕ → Option Machine
  | t :: n :: l =>
    match parseRules n l with
    | some (rs, []) => some ⟨t, rs⟩
    | _ => none
  | _ => none

/-- The code `⟨M⟩ ∈ {0,1}*` of a machine. -/
def Machine.encode (M : Machine) : List Bool := natsToBits M.toNats

/-- Decoding: the machine a string is a code of, or `none` if the string is not a code
("poorly formatted"). Every machine has a code: `decode (encode M) = some M`. Machines with
the same behaviour but different rule lists (e.g. extra rules that never apply) have different
codes, so codes can be padded. -/
def decode (c : List Bool) : Option Machine :=
  match bitsToNats c with
  | none => none
  | some l => natsToMachine l

end MetaSearch.Heyting


