-- Prove2me | Definitions.Def_IPPComplexities_Unconditional_Supplement_classes
-- name    : IPPComplexities_Unconditional_Supplement_classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:24:06.285646+00:00
-- url     : https://prove2.me/theorems/55a58fe0-6e77-4b77-9bb8-010dd83eef1d
-- title:
--   The classes E and NP, and almost-everywhere small-exponential circuit hardness
-- statement:
--   The complexity classes and the hardness notion of Theorem 1.2, over the published single-tape deterministic machines (`Decider`, with `DecidesWithin M L T` meaning that $M$ halts within $T(|x|)$ steps on every string $x$ with the correct verdict).
--
--   1. $L\in\mathsf{E}$ if some machine decides $L$ within $2^{C(n+1)}$ steps on inputs of length $n$, for a constant $C>0$.
--   2. $L\in\mathsf{P}$ if some machine decides $L$ within $(n+1)^k$ steps, for a constant $k$.
--   3. $L\in\mathsf{NP}$ if there are a set $R\in\mathsf{P}$ and a constant $k$ such that $x\in L$ if and only if some witness $w$ with $|w|\le(|x|+1)^k$ has $\langle x,w\rangle\in R$. The pairing $\langle x,w\rangle$ doubles every bit of $x$, then writes the separator $01$, then $w$; it is injective and computable in linear time.
--   4. A one-output circuit $C$ with $n$ input wires **decides $S$ on length $n$** if, for every $x\in\{0,1\}^n$, $C(x)=1$ exactly when $x\in S$.
--   5. $S$ is **almost-everywhere hard for small-exponential circuits** if there is a constant $\alpha>0$ such that, for all but finitely many $n$, no well-formed one-output circuit with $n$ inputs and size at most $2^{\alpha n}$ decides $S$ on length $n$; that is, every such circuit errs on some $n$-bit string.
--
--   Item 5 is the hypothesis as Theorem 4.1 states it, of which Theorem 1.2 is the special case $\mathcal C\in\{\mathsf E,\mathsf{NP}\}$.
--
--   **Formalization Note** Circuits are the published Boolean circuits (constants, $\neg$, binary $\wedge,\vee$), whose size counts the $n$ input wires as well as the gates; this differs from the gate count by $n\le2^{\alpha n}$ and so defines the same hard sets up to the choice of $\alpha$. The classes are robust to the single-tape machine model.
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), p. 1, Theorem 1.2 (PDF p. 3); p. 9, Theorem 4.1 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_timedDecider
import Definitions.Def_PPADSIS_SubexpSIS_Circuit

namespace IPPComplexities.Unconditional.Supplement

open PPADSIS.SubexpSIS

/-- The class E: sets decided by one single-tape machine within `2^(C·(n+1))` steps
on every input of length `n`, for some constant `C`. -/
def InE (L : Property) : Prop :=
  ∃ (M : Decider) (C : ℕ), 0 < C ∧ DecidesWithin M L (fun n => 2 ^ (C * (n + 1)))

/-- The class P: sets decided by one single-tape machine within `(n+1)^k` steps. -/
def InP (L : Property) : Prop :=
  ∃ (M : Decider) (k : ℕ), DecidesWithin M L (fun n => (n + 1) ^ k)

/-- Fixed injective pairing of two Boolean strings into one: each bit of `x` is
doubled, then the separator `01`, then `w` verbatim. -/
def pairEnc (x w : List Bool) : List Bool :=
  x.flatMap (fun b => [b, b]) ++ [false, true] ++ w

/-- The class NP: membership is witnessed by a string of polynomial length that is
checked by a polynomial-time relation on the paired input. -/
def InNP (L : Property) : Prop :=
  ∃ (R : Property) (k : ℕ), InP R ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ w : List Bool, w.length ≤ (x.length + 1) ^ k ∧ pairEnc x w ∈ R

/-- A one-output circuit with `n` input wires decides `S` on length `n`: on every
`n`-bit string it outputs `1` exactly on the members of `S`. -/
def DecidesOnLength (C : Circuit) (S : Property) (n : ℕ) : Prop :=
  ∀ x : List Bool, x.length = n → (C.eval x = [true] ↔ x ∈ S)

/-- Almost-everywhere small-exponential circuit hardness: for some constant `α > 0`
and all but finitely many `n`, no well-formed one-output circuit with `n` inputs and
size at most `2^(α·n)` decides `S` correctly on all `n`-bit strings. -/
def AEHard (S : Property) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ C : Circuit, C.WF → C.nIn = n → C.outs.length = 1 →
      (C.size : ℝ) ≤ (2 : ℝ) ^ (α * n) → ¬ DecidesOnLength C S n

end IPPComplexities.Unconditional.Supplement


