-- Prove2me | Definitions.Def_TechBreakthrough_Model
-- name    : TechBreakthrough_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:24.49299+00:00
-- url     : https://prove2.me/theorems/80aedba2-774c-4402-a39c-e98eb8166f53
-- title:
--   The primitives $(\alpha,\beta,r,\mu,\sigma,P,R,G,f)$ of the stopping problem
-- statement:
--   A model consists of the endpoints $\alpha,\beta$, the discount rate $r$, the coefficients $\mu,\sigma$, the laws $(P_x)$ on the canonical space, the payoff functions $R,G$, and the density $f$ of the threshold $Y$. From these the mission uses:
--
--   1. the generator $\mathcal Lu(x)=\mu(x)u'(x)+\frac12\sigma^2(x)u''(x)$, (11);
--   2. the law $Q$ of $Y$, with density $f$ on $\mathcal I$, and its distribution function $F(m)=\int_{\mathcal I\cap(-\infty,m]}f$;
--   3. the filters of $x\to\alpha^+$ and $x\to\beta^-$.
--
--   The assumptions on these data are `Model.Valid`.
--
--   **Formalization Note** The filters are comaps of one-sided neighbourhoods in `EReal`: at an infinite endpoint they are `atBot` and `atTop`.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, §4, pp.9–12; (11), p.10; A8, p.12

import Definitions.Def_TechBreakthrough_PathSpace

open MeasureTheory
open scoped NNReal

namespace TechBreakthrough

/-- The primitives of the general stopping problem of arXiv:2106.05112v1, §4, pp.9–12: the
endpoints `α`, `β`, the discount rate `r`, the coefficients `μ`, `σ`, the laws `P x`, the payoffs
`R`, `G`, and the density `f` of the threshold `Y`. Their assumptions are `Model.Valid`. -/
structure Model where
  α : EReal
  β : EReal
  r : ℝ
  μ : ℝ → ℝ
  σ : ℝ → ℝ
  P : ℝ → Measure (PathSpace α β)
  R : ℝ → ℝ
  G : ℝ → ℝ
  f : ℝ → ℝ

namespace Model

variable (M : Model)

/-- The state space `𝓘`, arXiv:2106.05112v1, p.9. -/
abbrev I : Set ℝ := stateSpace M.α M.β

/-- The canonical space. -/
abbrev Ω : Type := PathSpace M.α M.β

/-- The canonical process `X`. -/
abbrev X (t : ℝ≥0) (ω : M.Ω) : ℝ := canonicalProcess M.α M.β t ω

/-- `T_X`, arXiv:2106.05112v1, p.9. -/
abbrev T : Set (M.Ω → WithTop ℝ≥0) := stoppingTimes M.α M.β

/-- The generator `Lu(x) = μ(x)u′(x) + ½σ²(x)u″(x)`, arXiv:2106.05112v1, (11), p.10. -/
noncomputable def gen (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  M.μ x * deriv u x + 1 / 2 * M.σ x ^ 2 * deriv (deriv u) x

/-- The law `Q` of `Y`: density `f` on `𝓘` with respect to Lebesgue measure,
arXiv:2106.05112v1, A8, p.12. -/
noncomputable def Q : Measure ℝ :=
  (volume.restrict M.I).withDensity fun y => ENNReal.ofReal (M.f y)

/-- The cumulative distribution function `F` of `Y`, arXiv:2106.05112v1, p.12. -/
noncomputable def F (m : ℝ) : ℝ := ∫ y in {y ∈ M.I | y ≤ m}, M.f y

/-- The filter of `x → α⁺` on the line: `x → −∞` when `α = −∞`. -/
noncomputable def atLeftEnd : Filter ℝ := Filter.comap ((↑) : ℝ → EReal) (nhdsWithin M.α (Set.Ioi M.α))

/-- The filter of `x → β⁻` on the line: `x → ∞` when `β = ∞`. -/
noncomputable def atRightEnd : Filter ℝ := Filter.comap ((↑) : ℝ → EReal) (nhdsWithin M.β (Set.Iio M.β))

end Model

end TechBreakthrough


