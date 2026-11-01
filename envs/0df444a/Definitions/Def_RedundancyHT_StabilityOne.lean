-- Prove2me | Definitions.Def_RedundancyHT_StabilityOne
-- name    : RedundancyHT_StabilityOne
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:08.458059+00:00
-- url     : https://prove2.me/theorems/327efc44-d3b2-4b19-97b5-75e6bf67a30b
-- title:
--   The stability conditions (1)
-- statement:
--   The stability conditions (1) require
--   $$N\lambda\sum_{S\in\mathcal T}p_S<\sum_{n\in\bigcup_{S\in\mathcal T}S}\mu_n$$
--   for every non-empty set $\mathcal T$ of job types: the arrival rate of the types in $\mathcal T$ is below the service rate of the servers that can handle them.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Assumption 1, display (1), p.5

import Definitions.Def_RedundancyHT_pSet
import Definitions.Def_RedundancyHT_muSet

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The stability conditions (1)** (arXiv:2005.14566v5, Assumption 1, p.5): for every non-empty
`𝒯 ⊆ 𝒮`, `N λ Σ_{S∈𝒯} p_S < Σ_{n∈∪_{S∈𝒯} S} µ_n`. -/
def StabilityOne {n m : ℕ} (D : Model n m) (lam : ℝ) : Prop :=
  ∀ T : Finset (Fin n), T.Nonempty → (m : ℝ) * lam * pSet D T < muSet D T

end RedundancyHT


