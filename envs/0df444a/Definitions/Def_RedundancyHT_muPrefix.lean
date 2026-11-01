-- Prove2me | Definitions.Def_RedundancyHT_muPrefix
-- name    : RedundancyHT_muPrefix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:34.755898+00:00
-- url     : https://prove2.me/theorems/c22b91db-92a4-4f00-983f-6fcf92e219aa
-- title:
--   The rate $\mu(S_1,\dots,S_j)$ of an ordered vector of job types
-- statement:
--   For an ordered vector of distinct job types,
--   $$\mu(S_1,\dots,S_j)=\sum_{n\in\bigcup_{m=1}^{j}S_m}\mu_n.$$
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, display (4), p.7, and Proposition 1, p.13

import Definitions.Def_RedundancyHT_muSet
import Definitions.Def_RedundancyHT_prefixSet

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **`µ(S₁,…,S_j)` of (4)** (arXiv:2005.14566v5, p.7, and Proposition 1, p.13). -/
def muPrefix {n m k : ℕ} (D : Model n m) (S : Fin k ↪ Fin n) (j : Fin k) : ℝ :=
  muSet D (prefixSet S j)

end RedundancyHT


