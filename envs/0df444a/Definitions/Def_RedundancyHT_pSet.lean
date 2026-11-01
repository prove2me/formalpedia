-- Prove2me | Definitions.Def_RedundancyHT_pSet
-- name    : RedundancyHT_pSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:02.625325+00:00
-- url     : https://prove2.me/theorems/ef5d4952-e35d-4478-898e-6531cb96a77a
-- title:
--   The fraction $p_{\mathcal T}$ of jobs in a set of job types
-- statement:
--   For a set $\mathcal T$ of job types,
--   $$p_{\mathcal T}=\sum_{S\in\mathcal T}p_S$$
--   is the fraction of jobs whose type lies in $\mathcal T$.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §3, p.9

import Definitions.Def_RedundancyHT_pOf

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **`p_𝒯 := Σ_{S∈𝒯} p_S`** (arXiv:2005.14566v5, §3, p.9). -/
def pSet {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) : ℝ :=
  ∑ i ∈ T, pOf D i

end RedundancyHT


