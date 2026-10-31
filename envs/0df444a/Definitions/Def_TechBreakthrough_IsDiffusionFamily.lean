-- Prove2me | Definitions.Def_TechBreakthrough_IsDiffusionFamily
-- name    : TechBreakthrough_IsDiffusionFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:22.453552+00:00
-- url     : https://prove2.me/theorems/31a46878-b729-4ad7-8e4f-41aa0519f6ba
-- title:
--   The diffusion on $\mathcal I$ with natural endpoints
-- statement:
--   The family $(P_x)_{x\in\mathcal I}$ is the diffusion of §4.1 when $\mu$ and $\sigma$ are continuous on $\mathcal I=(\alpha,\beta)$, $\sigma>0$ on $\mathcal I$, both endpoints are natural, and each $P_x$ is the law of a weak solution of (7) started at $x$.
--
--   An endpoint $e$ is natural when both Feller integrals diverge: with $c\in\mathcal I$, scale density $s(y)=\exp(-\int_c^y2\mu/\sigma^2)$ and speed density $n(y)=2/(\sigma^2(y)s(y))$,
--
--   $$\int_c^e\Big|\int_c^y n\Big|\,s(y)\,dy=\infty,\qquad\int_c^e\Big|\int_c^y s\Big|\,n(y)\,dy=\infty.$$
--
--   These are the regularity conditions under which the paper states that $X$ is regular on $\mathcal I$ and that (7) has a weak solution unique in law.
--
--   **Formalization Note** The two integrals are the published `EthierKurtz.diffusionBoundaryTests` with $a=\sigma^2$, $b=\mu$, valued in $[0,\infty]$.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, §4.1, p.9

import Definitions.Def_TechBreakthrough_IsWeakSolution
import Definitions.Def_EthierKurtz_diffusionBoundaryTests

open MeasureTheory
open scoped ENNReal

namespace TechBreakthrough

/-- The endpoint `e` is **natural** in Feller's classification for the diffusion with drift `μ`
and volatility `σ`, tested from the interior point `c`: both endpoint integrals of the published
`EthierKurtz.diffusionBoundaryTests` (built from the scale density
`exp(−∫_c^y 2μ/σ²)` and the speed density) diverge. arXiv:2106.05112v1, §4.1, p.9. -/
def IsNaturalEndpoint (μ σ : ℝ → ℝ) (c : ℝ) (e : EReal) : Prop :=
  EthierKurtz.diffusionBoundaryTests (fun y => σ y ^ 2) μ c e = (⊤, ⊤)

/-- The diffusion of arXiv:2106.05112v1, §4.1, p.9: `μ`, `σ` continuous on `𝓘 = (α, β)`,
`σ > 0` on `𝓘`, the endpoints `α`, `β` natural, and for each `x ∈ 𝓘`, `P x` is the law of a weak
solution of (7) started at `x`.

**Formalization Note** The law `P x` is unique, by uniqueness in law for (7), which the page
derives from these assumptions. Outside `𝓘` the coefficients and `P` are immaterial. -/
structure IsDiffusionFamily (α β : EReal) (μ σ : ℝ → ℝ) (P : ℝ → Measure (PathSpace α β)) :
    Prop where
  endpoints_lt : α < β
  drift_continuous : ContinuousOn μ (stateSpace α β)
  volatility_continuous : ContinuousOn σ (stateSpace α β)
  volatility_pos : ∀ x ∈ stateSpace α β, 0 < σ x
  natural : ∃ c ∈ stateSpace α β, IsNaturalEndpoint μ σ c α ∧ IsNaturalEndpoint μ σ c β
  weak_solution : ∀ x ∈ stateSpace α β, IsWeakSolution μ σ (P x) x

end TechBreakthrough


