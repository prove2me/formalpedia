-- Prove2me | Definitions.Def_TierneyMH_Mixture_canonR
-- name    : TierneyMH_Mixture_canonR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T01:50:34.320584+00:00
-- url     : https://prove2.me/theorems/62342ab3-e7de-493a-a8c4-18e513ec7655
-- title:
--   The set $R = \{(x,y) : h(x,y)>0,\ h(y,x)>0\}$ for $\mu(dx,dy) = \pi(dx)Q(x,dy)$
-- statement:
--   Let $\mu(dx,dy)=\pi(dx)Q(x,dy)$ and let $h=d\mu/d(\mu+\mu^T)$ be the density of the proof of Proposition 1. The set
--
--   $$R = \{(x,y)\in E\times E : h(x,y)>0 \text{ and } h(y,x)>0\}$$
--
--   is the set of Proposition 1 for $\mu$: it is symmetric, $\mu$ and $\mu^T$ are mutually absolutely continuous on it, and mutually singular off it. It consists of the pairs of states between which the proposal chain started from $\pi$ can move in both directions.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 2, proof of Proposition 1 (the set R)

import Mathlib
import Definitions.Def_TierneyMH_Mixture_canonDensity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Mixture

/-- The set `R` of the proof of Proposition 1 (Tierney 1998, p. 2) for
`μ(dx, dy) = π(dx) Q(x, dy)`: `R = {(x, y) : h(x, y) > 0 and h(y, x) > 0}`, where
`h = canonDensity π Q = dμ/d(μ + μᵀ)`. -/
def canonR {E : Type*} [MeasurableSpace E] (π : Measure E) (Q : Kernel E E) : Set (E × E) :=
  {p | 0 < canonDensity π Q p ∧ 0 < canonDensity π Q p.swap}

end TierneyMH.Mixture


