-- Prove2me | Definitions.Def_RedundancyHT_prefixSet
-- name    : RedundancyHT_prefixSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:40.715574+00:00
-- url     : https://prove2.me/theorems/9c95c1e5-686e-4456-a103-6d86afb73b4e
-- title:
--   The set $\{S_1,\dots,S_j\}$ of the first entries of an ordered vector
-- statement:
--   For an ordered vector $S=[S_1,\dots,S_k]$ of distinct entries and $1\le j\le k$, this is the set $\{S_1,\dots,S_j\}$.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Proposition 1, p.13

import Mathlib

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The set `{S₁,…,S_j}`** of the first `j` entries of an ordered vector of distinct entries
(arXiv:2005.14566v5, Proposition 1, p.13). -/
def prefixSet {α : Type} [DecidableEq α] {k : ℕ} (S : Fin k ↪ α) (j : Fin k) : Finset α :=
  (Finset.univ.filter (fun i => i ≤ j)).image S

end RedundancyHT


