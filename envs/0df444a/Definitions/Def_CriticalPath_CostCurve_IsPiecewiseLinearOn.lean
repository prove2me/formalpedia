-- Prove2me | Definitions.Def_CriticalPath_CostCurve_IsPiecewiseLinearOn
-- name    : CriticalPath_CostCurve_IsPiecewiseLinearOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:30:55.381131+00:00
-- url     : https://prove2.me/theorems/4ec8278a-df27-496c-83e3-91ff62c34aa4
-- title:
--   Piecewise linear on a set of reals, with finitely many affine pieces covering it
-- statement:
--   A function $f : \mathbb{R} \to \mathbb{R}$ is **piecewise linear on** $S \subseteq \mathbb{R}$ if there are finitely many breakpoints $\beta_0 < \beta_1 < \dots < \beta_m$ with $S \subseteq [\beta_0, \infty)$ and real numbers $\sigma_k, \iota_k$ ($0 \le k \le m$) such that
--
--   $$
--   f(x) = \sigma_k x + \iota_k \ \ \text{for } x \in S \cap [\beta_k, \beta_{k+1}]\ (k < m), \qquad f(x) = \sigma_m x + \iota_m \ \ \text{for } x \in S \cap [\beta_m, \infty).
--   $$
--
--   The pieces are finitely many and together cover all of $S$; at an interior breakpoint lying in $S$ the two adjacent affine pieces agree. This is the one-variable notion used for the project cost curve, whose domain is a half-line.
--
--   **Formalization Note** The condition "for all $k' > k$, $x \le \beta_{k'}$" encodes $x \le \beta_{k+1}$ (it is vacuous for the last piece), so piece $k$ is used on $S \cap [\beta_k, \beta_{k+1}]$.
-- source:
--   Kelley, Walker, Critical-Path Planning and Scheduling, Proc. Eastern Joint Computer Conf. 1959, DOI 10.1145/1460299.1460318, p. 165, Part I §3 Minimum Project Costs, paragraph under Fig. 3 ("a non-increasing, piecewise linear, convex function")

import Mathlib

namespace CriticalPath.CostCurve

/-- `f` is piecewise linear on `S ⊆ ℝ` with finitely many pieces: there are breakpoints
`β 0 < β 1 < ⋯ < β m` with `S ⊆ [β 0, ∞)` and slopes/intercepts `σ k, ι k` such that on
`S ∩ [β k, β (k+1)]` (and on `S ∩ [β m, ∞)` for the last piece) `f x = σ k * x + ι k`.
The pieces cover all of `S`. -/
def IsPiecewiseLinearOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ (m : ℕ) (β σ ι : Fin (m + 1) → ℝ), StrictMono β ∧ S ⊆ Set.Ici (β 0) ∧
    ∀ (k : Fin (m + 1)) (x : ℝ), x ∈ S → β k ≤ x → (∀ k', k < k' → x ≤ β k') →
      f x = σ k * x + ι k

end CriticalPath.CostCurve


