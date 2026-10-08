-- Prove2me | Definitions.Def_MatroidProphetKW_Single_Algorithm
-- name    : MatroidProphetKW_Single_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:42.77523+00:00
-- url     : https://prove2.me/theorems/75432a30-0347-481e-8fff-c93f2213c9e0
-- title:
--   (9) — the threshold $T_i = \tfrac12\,\mathbb E[w'(R(A_{i-1})) - w'(R(A_{i-1}\cup\{x_i\}))]$
-- statement:
--   The algorithm of §3.3 processes the elements in the order chosen by the adversary. In step $i$, having already selected the (possibly empty) set $A_{i-1}$, it sets the threshold $T_i = \infty$ if $A_{i-1} \cup \{x_i\} \notin \mathcal I$, and otherwise
--   $$T_i = \tfrac12\, \mathbb E\big[w'(R(A_{i-1})) - w'(R(A_{i-1} \cup \{x_i\}))\big], \tag{9}$$
--   where the expectation is over the ghost sample $w' \sim \bigotimes_x F_x$ only. It selects $x_i$ if and only if $w(x_i) \ge T_i$. The threshold depends only on the current selection $A_{i-1}$ and the arriving element $x_i$, written $T(A, x)$.
--
--   This is the algorithm with 2-balanced thresholds whose guarantee is the main theorem.
--
--   **Formalization Note** `kwT M F A x` is the real number in (9); `kwThr M F` is the corresponding threshold rule, constant in the revealed prefix and the weights. The value $\infty$ on infeasible steps is supplied by the independence guard of the online run. The expectation is a Bochner integral; under finite means the integrand is integrable.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 7, §3.3, (9)

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting

namespace MatroidProphetKW.Single

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The threshold (9) of §3.3 (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 7) for the element `x`
when `A = A_{i−1}` has been selected:
  `T(A, x) = ½ · E[w′(R(A)) − w′(R(A ∪ {x}))]`,
the expectation over `w′ ∼ Measure.pi F`. (The value `∞` when `A ∪ {x} ∉ ℐ` is the feasibility
guard of `run`.) -/
noncomputable def kwT (M : Matroid α) (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (A : Finset α) (x : α) : ℝ :=
  (1 / 2) * ∫ w', (wt w' (Rset M A w') - wt w' (Rset M (insert x A) w')) ∂(Measure.pi F)

/-- The algorithm of §3.3 as a threshold rule: the threshold depends only on the current selection
`A_{i−1}` and on the arriving element `x_i`. -/
noncomputable def kwThr (M : Matroid α) (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] :
    Finset α → List α → (α → ℝ) → α → ℝ :=
  fun A _ _ x => kwT M F A x

end MatroidProphetKW.Single


