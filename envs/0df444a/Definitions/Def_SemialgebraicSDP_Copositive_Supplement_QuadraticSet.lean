-- Prove2me | Definitions.Def_SemialgebraicSDP_Copositive_Supplement_QuadraticSet
-- name    : SemialgebraicSDP_Copositive_Supplement_QuadraticSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:42:13.972971+00:00
-- url     : https://prove2.me/theorems/0b277213-1dd7-4c01-a015-40f632519460
-- title:
--   §7.4, (7.3) and (7.5), pp. 315–316 — the unit-sphere set $\mathcal A$ of quadratic inequalities and the quartic form of (7.5)
-- statement:
--   Let $A_1, \dots, A_m$ be real $n \times n$ matrices, and write $A_i(x) := x^T A_i x$ for $x \in \mathbb R^n$. This module defines two objects from §7.4 of the paper.
--
--   1. **The set (7.3).** The unit vectors that satisfy every quadratic inequality:
--   $$
--   \mathcal A := \{\, x \in \mathbb R^n \mid x^T A_i x \ge 0 \text{ for } i = 1, \dots, m,\ \ \|x\| = 1 \,\},
--   $$
--   where $\|x\|$ is the Euclidean norm, written as $\sum_k x_k^2 = 1$.
--   2. **The left-hand side of (7.5).** Given further real $n \times n$ matrices $Q_1, \dots, Q_m$ and real numbers $r_{ij}$, with $Q_i(x) := x^T Q_i x$, the quartic form
--   $$
--   \sum_{i=1}^m Q_i(x) A_i(x) + \sum_{1 \le i < j \le m} r_{ij} A_i(x) A_j(x).
--   $$
--   Each pair $i < j$ appears exactly once.
--
--   These are the set whose emptiness Theorem 7.5 certifies and the quartic form that serves as the certificate. Deciding whether a set of the form $\mathcal A$ is empty covers the semidefinite relaxations of quadratic programs such as MAX-CUT that §7.4 discusses.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`. Because Lean's default norm on `Fin n → ℝ` is the sup norm, the Euclidean unit sphere is written as $\sum_k x_k^2 = 1$. The quadratic evaluation $x^T D x$ is the published `MurtyKabadi.Reduction.Q`. The multipliers $r$ are given as a full array `Fin m → Fin m → ℝ`, but only the entries with $i < j$ enter the form. Symmetry of $A_i$ and positive semidefiniteness of $Q_i$ are not part of these definitions; Theorem 7.5 states them as hypotheses.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 315, §7.4 (7.3); p. 316, Theorem 7.5 (7.5)

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

namespace SemialgebraicSDP.Copositive.Supplement

open MurtyKabadi.Reduction

/-- The set (7.3) of Parrilo (2003, §7.4, p. 315): for real `n × n` matrices `A₁, …, Aₘ`,
`𝒜 := {x ∈ ℝⁿ | xᵀAᵢx ≥ 0 for every i, ‖x‖ = 1}`, with `‖x‖` the Euclidean norm, written as
`∑ₖ xₖ² = 1`. Here `Q D x = xᵀDx` is the published quadratic evaluation. -/
def setA {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ Q (A i) x) ∧ ∑ k, x k ^ 2 = 1}

/-- The left-hand side of (7.5) (Parrilo 2003, p. 316), the quartic form
`∑ᵢ Qᵢ(x) Aᵢ(x) + ∑_{1 ≤ i < j ≤ m} rᵢⱼ Aᵢ(x) Aⱼ(x)` with `Qᵢ(x) = xᵀQᵢx` and
`Aᵢ(x) = xᵀAᵢx`. Every pair `i < j` occurs exactly once; the entries `r i j` with `i ≥ j`
are not used. -/
def quarticLHS {n m : ℕ} (A Qm : Fin m → Matrix (Fin n) (Fin n) ℝ) (r : Fin m → Fin m → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, Q (Qm i) x * Q (A i) x +
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), r i j * Q (A i) x * Q (A j) x

end SemialgebraicSDP.Copositive.Supplement


