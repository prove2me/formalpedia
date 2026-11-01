-- Prove2me | Definitions.Def_RedundancyHT_IsCapacityMaximizer
-- name    : RedundancyHT_IsCapacityMaximizer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:18.237332+00:00
-- url     : https://prove2.me/theorems/a94fa4ac-1dfa-44f3-9454-6761d909db47
-- title:
--   A non-empty maximizer of the capacity ratio
-- statement:
--   A non-empty set $\mathcal T$ of job types maximizes the capacity ratio if
--   $$\rho_{\mathcal T'}\le\rho_{\mathcal T}\qquad\text{for every non-empty }\mathcal T'\subseteq\mathcal S.$$
--   Uniqueness is not part of this notion. The equivalence of the stability conditions with $\lambda<\lambda^*$ needs only a maximizer.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Definition 1, p.9

import Definitions.Def_RedundancyHT_capacityRatio

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **A maximizer of the capacity ratio**, `𝒯 ∈ arg max_{𝒯⊆𝒮} ρ_𝒯` (arXiv:2005.14566v5, Definition 1,
p.9), without the uniqueness of Assumption 3. The maximum runs over non-empty `𝒯'`, since `ρ_∅` is
undefined. -/
def IsCapacityMaximizer {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) : Prop :=
  T.Nonempty ∧ ∀ T' : Finset (Fin n), T'.Nonempty → capacityRatio D T' ≤ capacityRatio D T

end RedundancyHT


