-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_QSampler
-- name    : QuantumKtSoI_Supplement_QSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:27:26.168801+00:00
-- url     : https://prove2.me/theorems/5fd4fca7-1bef-4b41-af01-32d13e066102
-- title:
--   Quantum polynomial-time samplers and their output events (p.51)
-- statement:
--   A **quantum polynomial-time sampler** is a machine $S$ of Definition 3.1 together with a polynomial $q_S$ such that $S$ halts on every branch within $q_S(n)$ steps on input $1^n$. Its output distribution is $w\mapsto P_S(1^n;q_S(n),w)$, written $(x,y)\sim S(1^n)$.
--
--   For a property $E$ of pairs, $\Pr_{(x,y)\sim S(1^n)}[\,|x|=|y|=n \text{ and } E(x,y)]$ is the total probability of the outputs $\langle x,y\rangle=xy$ with $x,y\in\{0,1\}^n$ and $E(x,y)$; an output that is not such a pair does not belong to the event.
--
--   This is the sampling convention of the average-case statement, Theorem 5.16.
--
--   **Formalization Note** The polynomial is taken in the normal form $q_S(n)=c(n+2)^k$. Every polynomial is bounded by one of this form, and a machine that has halted on every branch has the same output law at every later deadline, so neither the samplers nor their laws change.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), p.51 (sampling convention before Definition 5.1)

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_CodedMachine

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- A **quantum polynomial-time sampler** (p.51 of Myrisiotis, STOC 2027 submission, held version
sha256 6616571c…): a machine `S` of Definition 3.1 (a valid coded machine) and a polynomial
`q_S(n) = c(n+2)^k` such that `S` halts on every branch within `q_S(n)` steps on input `1ⁿ`. Its
output distribution is `w ↦ P_S(1ⁿ; q_S(n), w)`.

**Formalization Note** Every polynomial is bounded by one of the form `c(n+2)^k`, and a machine
that halts on every branch by a deadline has the same output law at every later deadline (a
halted branch is continued only by final records, Definition 3.4), so this normal form changes
neither the samplers nor their output laws. -/
structure QSampler where
  B : CodedMachine
  valid : B.Valid
  c : ℕ
  k : ℕ
  halts : ∀ n : ℕ, B.toMachine.HaltsWithin (ones n) (c * (n + 2) ^ k)

namespace QSampler

variable (S : QSampler)

/-- The all-branch deadline `q_S(n) = c(n+2)^k`. -/
def time (n : ℕ) : ℕ := S.c * (n + 2) ^ S.k

/-- The probability `P_S(1ⁿ; q_S(n), w)` that `S(1ⁿ)` outputs `w`. -/
def outProb (n : ℕ) (w : List Bool) : ℝ := S.B.toMachine.outputProb (ones n) (S.time n) w

/-- `Pr_{(x,y) ∼ S(1ⁿ)}[|x| = |y| = n and E(x, y)]` (p.51): the total probability of the outputs
`⟨x, y⟩ = xy` with `x, y ∈ {0,1}ⁿ` and `E(x, y)`. An output that is not such a pair is outside the
event. -/
def pairProb (n : ℕ) (E : List Bool → List Bool → Prop) : ℝ :=
  ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
    if E (List.ofFn x) (List.ofFn y) then S.outProb n (pair (List.ofFn x) (List.ofFn y)) else 0

end QSampler

end QuantumKtSoI.Supplement


