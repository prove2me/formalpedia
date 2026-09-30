-- Prove2me | Definitions.Def_TierneyMH_Mixture_canonDensity
-- name    : TierneyMH_Mixture_canonDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T01:40:20.388024+00:00
-- url     : https://prove2.me/theorems/1f492e2f-4898-43c6-96ed-401e874d740b
-- title:
--   The density $h = d\mu/d(\mu+\mu^T)$ for $\mu(dx,dy) = \pi(dx)Q(x,dy)$
-- statement:
--   Let $\pi$ be a measure on $(E,\mathcal E)$ and $Q$ a transition kernel on $E$, and put $\mu(dx,dy)=\pi(dx)Q(x,dy)$ and $\mu^T(dx,dy)=\mu(dy,dx)$. Following the proof of Proposition 1, let $\nu=\mu+\mu^T$, a symmetric measure dominating both $\mu$ and $\mu^T$, and let
--
--   $$h(x,y) = \frac{d\mu}{d\nu}(x,y)$$
--
--   be the Radon–Nikodym density of $\mu$ with respect to $\nu$. Then $h(y,x)$ is a density of $\mu^T$ with respect to $\nu$.
--
--   This density is the raw material for the set $R$, the ratio $r$ and the acceptance probability $\alpha_{MH}$ of the mission.
--
--   **Formalization Note** $\mu$ is `π ⊗ₘ Q`, $\mu^T$ is its image under `Prod.swap`, and $h$ is Mathlib's `Measure.rnDeriv`, one fixed measurable version of a density that is determined only $\nu$-almost everywhere.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 2, proof of Proposition 1 (ν and h)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Mixture

/-- The density `h` of the proof of Proposition 1 (Tierney 1998, p. 2), for the measure
`μ(dx, dy) = π(dx) Q(x, dy)` (`μ = π ⊗ₘ Q`): with the symmetric measure
`ν = μ + μᵀ`, `μᵀ = μ.map Prod.swap` (`μᵀ(dx, dy) = μ(dy, dx)`), `h = dμ/dν` is the
Radon–Nikodym derivative `μ.rnDeriv ν`.

It is one fixed version of a density that the paper determines only `ν`-almost everywhere. -/
noncomputable def canonDensity {E : Type*} [MeasurableSpace E] (π : Measure E) (Q : Kernel E E) :
    E × E → ℝ≥0∞ :=
  (π ⊗ₘ Q).rnDeriv ((π ⊗ₘ Q) + (π ⊗ₘ Q).map Prod.swap)

end TierneyMH.Mixture


