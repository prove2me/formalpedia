-- Prove2me | Definitions.Def_RedundancyHT_lamStar
-- name    : RedundancyHT_lamStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:01.208+00:00
-- url     : https://prove2.me/theorems/55ece827-5d01-4fcf-a101-bf9e5334cc05
-- title:
--   The critical normalized arrival rate $\lambda^*=\mu_{\mathcal T^*}/(Np_{\mathcal T^*})$
-- statement:
--   For a set $\mathcal T^*$ of job types,
--   $$\lambda^*=\frac{1}{N\rho_{\mathcal T^*}}=\frac{\mu_{\mathcal T^*}}{Np_{\mathcal T^*}}.$$
--   When $\mathcal T^*$ is the critical subset, this is the value of the normalized arrival rate at which the system leaves its stability region.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Definition 1, p.9

import Definitions.Def_RedundancyHT_pSet
import Definitions.Def_RedundancyHT_muSet

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The critical normalized arrival rate** `λ* = 1/(Nρ_𝒯*) = µ_𝒯*/(N p_𝒯*)`
(arXiv:2005.14566v5, Definition 1, p.9). -/
def lamStar {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) : ℝ :=
  muSet D T / ((m : ℝ) * pSet D T)

end RedundancyHT


