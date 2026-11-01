-- Prove2me | Definitions.Def_RedundancyHT_capacityRatio
-- name    : RedundancyHT_capacityRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:55.769376+00:00
-- url     : https://prove2.me/theorems/5d93f7ba-a4d6-49a0-939a-d42c4ef8ae3f
-- title:
--   The capacity ratio $\rho_{\mathcal T}=p_{\mathcal T}/\mu_{\mathcal T}$
-- statement:
--   The capacity ratio of a set $\mathcal T$ of job types is
--   $$\rho_{\mathcal T}=\frac{p_{\mathcal T}}{\mu_{\mathcal T}}.$$
--   It compares the fraction of jobs in $\mathcal T$ to the service rate available to them. The set with the largest ratio saturates first when $\lambda$ grows.
--
--   **Formalization Note** The ratio is undefined for the empty set, which reads $0/0=0$ in Lean. The definitions built on it quantify over non-empty sets only.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Definition 1, p.9

import Definitions.Def_RedundancyHT_pSet
import Definitions.Def_RedundancyHT_muSet

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The capacity ratio `ρ_𝒯 := p_𝒯 / µ_𝒯`** (arXiv:2005.14566v5, Definition 1, p.9).

**Formalization Note.** On `𝒯 = ∅` this reads `0 / 0 = 0` in Lean. The ratio is undefined there, and
every definition below quantifies over non-empty `𝒯` only. -/
def capacityRatio {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) : ℝ :=
  pSet D T / muSet D T

end RedundancyHT


