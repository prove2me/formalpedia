-- Prove2me | Definitions.Def_RedundancyHT_StabilityTwo
-- name    : RedundancyHT_StabilityTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:27.765822+00:00
-- url     : https://prove2.me/theorems/69fe5dfa-32a1-45fc-9ada-7356a449557f
-- title:
--   The stability conditions (2)
-- statement:
--   The stability conditions (2) require
--   $$N\lambda\sum_{S:\,S\subseteq U}p_S<\sum_{n\in U}\mu_n$$
--   for every non-empty set $U$ of servers: the servers in $U$ can handle the jobs that can only be served within $U$.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Assumption 1, display (2), p.5

import Definitions.Def_RedundancyHT_pSet

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The stability conditions (2)** (arXiv:2005.14566v5, Assumption 1, p.5): for every non-empty
`U ⊆ {1,…,N}`, `N λ Σ_{S:S⊆U} p_S < Σ_{n∈U} µ_n`. The published `onlyClasses D.edge U` is the set of
types all of whose compatible servers lie in `U`, and `D.capacity U` is `Σ_{n∈U} µ_n`. -/
def StabilityTwo {n m : ℕ} (D : Model n m) (lam : ℝ) : Prop :=
  ∀ U : Finset (Fin m), U.Nonempty →
    (m : ℝ) * lam * pSet D (onlyClasses D.edge U) < D.capacity U

end RedundancyHT


