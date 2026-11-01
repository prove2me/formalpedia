-- Prove2me | Definitions.Def_RedundancyHT_muSet
-- name    : RedundancyHT_muSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:48.763992+00:00
-- url     : https://prove2.me/theorems/660c04e0-703d-4e5f-bc94-1c2188442c9e
-- title:
--   The aggregate service rate $\mu_{\mathcal T}$ of a set of job types
-- statement:
--   For a set $\mathcal T$ of job types,
--   $$\mu_{\mathcal T}=\sum_{n\in\bigcup_{S\in\mathcal T}S}\mu_n$$
--   is the aggregate service rate of the servers compatible with $\mathcal T$. The prefix rate $\mu(c_1,\dots,c_i)$ of equation (4) is this quantity for the set $\{c_1,\dots,c_i\}$.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §3, p.9, and display (4), p.7

import Definitions.Def_RedundancyHT_serversOf

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **`µ_𝒯 := Σ_{n∈∪_{S∈𝒯} S} µ_n`**, the aggregate service rate of the servers compatible with `𝒯`
(arXiv:2005.14566v5, §3, p.9). -/
def muSet {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) : ℝ :=
  ∑ j ∈ serversOf D T, D.service j

end RedundancyHT


