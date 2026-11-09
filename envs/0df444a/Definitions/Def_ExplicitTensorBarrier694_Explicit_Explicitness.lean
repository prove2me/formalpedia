-- Prove2me | Definitions.Def_ExplicitTensorBarrier694_Explicit_Explicitness
-- name    : ExplicitTensorBarrier694_Explicit_Explicitness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:37.739133+00:00
-- url     : https://prove2.me/theorems/60ccaf8b-6f68-4af7-a04a-b9d5ffd27f0b
-- title:
--   Uniform polynomial binary-output explicitness by a finite deterministic machine
-- statement:
--   For an integer tensor family $F_n\in\mathbb Z^{n\times n\times n}$, polynomial-time explicitness means one fixed finite-state deterministic Turing machine outputs every entry in binary. Input is the standard most-significant-bit-first binary encoding of $n$. Output lists the entries in lexicographic order, last coordinate fastest; each entry has a sign, the binary absolute value (one zero digit for zero), and a delimiter. The tape alphabet is fixed with blank, two bit symbols, two signs, a delimiter and two work symbols.
--
--   Writing $\mathrm{run}_M(w,t)$ for $t$ actual Mathlib Post-Turing move/write steps from input $w$, the requirement is
--
--   $$\exists M,\ C\in\mathbb N_{\ge1},\ d\in\mathbb N\ \forall n\ge1\ \exists t\le C(n+1)^d:\quad M\text{ halts at }t\text{ with output }\operatorname{enc}(F_n).$$
--
--   The machine has a finite nonempty state set. A halted computation stutters; the halting condition is checked explicitly. Output is exact equality of the right half-tape with the encoded list, modulo trailing blanks, with the head at its start. The program, state set and constants are independent of $n$. The bound is polynomial in $n$, as in the paper, rather than in the input length $\log n$.
--
--   A fixed single tape and this alphabet are standard computational encoding choices with polynomial simulation overhead. The definition contains actual execution semantics and no assumed cost field. It is a predicate to be proved of a family, not a certificate supplied in the goal hypotheses.
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), paragraph immediately after Theorem 1.1, p.2 (PDF p.2); operational machine and serialization conventions implementing that definition; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Construction

namespace ExplicitTensorBarrier694.Explicit

/-- Fixed finite tape alphabet: 0 blank, 1 binary zero, 2 binary one, 3 plus,
4 minus, 5 entry delimiter; 6 and 7 are available as work symbols. -/
abbrev Symbol := Fin 8

/-- Standard binary, most significant digit first, with one zero digit for zero. -/
def binary (n : ℕ) : List Symbol :=
  (if n = 0 then [0] else (Nat.digits 2 n).reverse).map
    (fun b => if b = 0 then 1 else 2)

/-- A sign, binary absolute value, and delimiter. No integer has unit-cost output. -/
def integerWord (z : ℤ) : List Symbol :=
  [if z < 0 then 4 else 3] ++ binary z.natAbs ++ [5]

/-- All n³ entries in lexicographic order, with the last coordinate fastest. -/
def tensorWord {n : ℕ} (T : Fin n → Fin n → Fin n → ℤ) : List Symbol :=
  (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
    (List.finRange n).flatMap fun k => integerWord (T i j k)

/-- Actual TM0 execution, stuttering only after halting. Each successor applies
at most one Post-Turing move/write instruction; no numerical cost oracle. -/
def runMachine {k : ℕ} (M : Turing.TM0.Machine Symbol (Fin (k + 1)))
    (input : List Symbol) : ℕ → Turing.TM0.Cfg Symbol (Fin (k + 1))
  | 0 => Turing.TM0.init input
  | t + 1 => let c := runMachine M input t
             (Turing.TM0.step M c).getD c

/-- The p.2 explicitness requirement: one fixed finite-state deterministic TM
prints the same integer family in binary, in polynomial time in n (not log n).
Its head is at the first output symbol when it halts. Trailing blank equality is
Mathlib's exact half-tape equality. C,d and the program are uniform in n.
A fixed binary-work alphabet and single tape change time only polynomially. -/
def PolynomialTimeExplicit (F : (n : ℕ) → Fin n → Fin n → Fin n → ℤ) : Prop :=
  ∃ k : ℕ, ∃ M : Turing.TM0.Machine Symbol (Fin (k + 1)),
    ∃ C d : ℕ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → ∃ t : ℕ,
      t ≤ C * (n + 1) ^ d ∧
      Turing.TM0.step M (runMachine M (binary n) t) = none ∧
      (runMachine M (binary n) t).Tape.right₀ = Turing.ListBlank.mk (tensorWord (F n))

end ExplicitTensorBarrier694.Explicit


