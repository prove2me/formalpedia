-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Encoding
-- name    : STOC2027BoolCSP_Approximation_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:58.092583+00:00
-- url     : https://prove2.me/theorems/2a3909b8-45cc-424d-aa83-f066cd16a408
-- title:
--   Explicit bit encodings of instances, requests and accuracies; precision $p=\max(0,\lceil\log_2(1/\varepsilon)\rceil)$
-- statement:
--   The explicit input of Theorem 1.1 is a bit string. Natural numbers are written in self-delimiting binary (the bit length in unary, then the binary digits), integers with a sign bit, and rationals as a reduced numerator over a positive denominator. The variable list is written in unary, so the input length is at least the number $n$ of output coordinates. A constraint is written as its number of positions, its incidence list, its explicit truth table of $2^r$ bits and its weight. A request $(I,\varepsilon)$ is the instance code followed by the code of the rational accuracy $\varepsilon$; its length $L$ is the **explicit input bit length**, which includes the accuracy, as the paper's preamble to Theorem 1.1 requires.
--
--   The requested precision of an accuracy $\varepsilon>0$ is
--   $$p(\varepsilon)=\max\bigl(0,\lceil\log_2(1/\varepsilon)\rceil\bigr).$$
--   An output word is read as the assignment giving variable $i$ the $i$-th bit of the word.
--
--   These encodings fix what "polynomial in the explicit input bit length and in $\log(1/\varepsilon)$" means for every algorithmic statement of the mission.
--
--   **Formalization Note** `Int.clog 2 (1/ε)` is $\lceil\log_2(1/\varepsilon)\rceil$; `toNat` truncates negative values to $0$.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 1 (PDF 4), preamble of Section 1.1 (rational weights and accuracies; input length includes the accuracy) and Section 2

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance

namespace STOC2027BoolCSP.Approximation

/-- Unary code of a natural number: `n` ones and a terminating zero. Used for the explicit
variable list, so that the input length is at least the number of output coordinates. -/
def unaryCode (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Self-delimiting binary code of a natural number: the bit length in unary, then the binary
digits (`Nat.bits`, least significant first, no leading zeros). Its length is
`2 · bitlength + 1`. -/
def natCode (x : ℕ) : List Bool := unaryCode (Nat.bits x).length ++ Nat.bits x

/-- Code of an integer: a sign bit (`true` for negative), then the binary code of `|z|`. -/
def intCode (z : ℤ) : List Bool := decide (z < 0) :: natCode z.natAbs

/-- Code of a rational number: binary numerator, then binary positive denominator (reduced form). -/
def ratCode (q : ℚ) : List Bool := intCode q.num ++ natCode q.den

/-- Code of a list: its length, then its elements. -/
def listCode {α : Type} (f : α → List Bool) (l : List α) : List Bool :=
  natCode l.length ++ l.flatMap f

/-- The explicit truth table of a predicate on `r` positions: its `2^r` values, the input with
index `j` assigning bit `Nat.testBit j i` to position `i`. -/
def truthTableCode (r : ℕ) (P : (Fin r → Bool) → Bool) : List Bool :=
  List.ofFn (fun j : Fin (2 ^ r) => P (fun i => Nat.testBit j.val i.val))

/-- Code of a constraint: its number of positions, its incidence list, its explicit truth table
and its rational weight. -/
def constraintCode {n : ℕ} (c : Constraint n) : List Bool :=
  natCode c.arity ++ (List.ofFn c.scope).flatMap (fun v => natCode v.val) ++
    truthTableCode c.arity c.pred ++ ratCode c.weight

/-- Code of an instance: the explicit variable list (in unary), then the list of constraints. -/
def instanceCode (I : Instance) : List Bool :=
  unaryCode I.n ++ listCode constraintCode I.cons

/-- Code of a request `(I, ε)`: the instance followed by the requested accuracy. Its length is
the explicit input bit length `L` of Theorem 1.1. -/
def requestCode (I : Instance) (ε : ℚ) : List Bool := instanceCode I ++ ratCode ε

/-- The requested precision `p = max(0, ⌈log₂(1/ε)⌉)` of an accuracy `ε > 0`. -/
def precBits (ε : ℚ) : ℕ := (Int.clog 2 (1 / ε)).toNat

/-- The assignment read off an output word: variable `i` gets bit `i` of the word. -/
def decodeAssignment (n : ℕ) (out : List Bool) : Fin n → Bool := fun i => out.getD i.val false

end STOC2027BoolCSP.Approximation


