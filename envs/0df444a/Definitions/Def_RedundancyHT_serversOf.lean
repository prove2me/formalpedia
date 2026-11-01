-- Prove2me | Definitions.Def_RedundancyHT_serversOf
-- name    : RedundancyHT_serversOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:56.878267+00:00
-- url     : https://prove2.me/theorems/ca8dae66-cd42-403e-8598-44eb930d2b26
-- title:
--   The servers $\bigcup_{S\in\mathcal T}S$ compatible with a set of job types
-- statement:
--   For a set $\mathcal T$ of job types, this is the set of servers
--   $$\bigcup_{S\in\mathcal T}S\subseteq\{1,\dots,N\}$$
--   to which at least one type in $\mathcal T$ is replicated.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §3, p.9

import Definitions.Def_BipartiteMatchingHT_Delay_Primitives

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The compatible servers `⋃_{S∈𝒯} S`** of a set `𝒯` of job types (arXiv:2005.14566v5, §3, p.9). -/
def serversOf {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter (fun j => ∃ i ∈ T, D.compatible i j = true)

end RedundancyHT


