-- Prove2me | Definitions.Def_SPFacilityGraph_Selector
-- name    : SPFacilityGraph_Selector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:56:16.324044+00:00
-- url     : https://prove2.me/theorems/91fdcf13-b3f3-4501-adc7-358ad1660cc2
-- title:
--   Selector family $\Pi(W)$
-- statement:
--   For a finite set $W \subseteq G$ of locations, the selector family is
--   $$
--   \Pi(W) = \{\pi_i : i \in N\} \cup \{\kappa_w : w \in W\},
--   $$
--   where the **report selector** (dictatorship) $\pi_i$ outputs agent $i$'s report and the **constant mechanism** $\kappa_w$ always outputs $w$. These are the component mechanisms of the deterministic attributions in Theorem 7.2.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), (2.7), p.5

import Mathlib
import Definitions.Def_SPFacilityGraph_Profile

set_option autoImplicit false

namespace SPFacilityGraph

/-- The selector family `Π(W) = {πᵢ : i ∈ N} ∪ {κ_y : y ∈ W}` for a finite `W ⊆ G` (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049),
(2.7), p.5): a report selector (dictatorship) `πᵢ` or a constant mechanism `κ_w` with
`w ∈ W`. Their values are given by `Selector.eval`. -/
inductive Selector {k : ℕ} (G : MetricGraph k) (n : ℕ) (W : Finset G.Pt) : Type
  /-- the report selector `πᵢ(𝒙) = xᵢ` -/
  | report (i : Fin n) : Selector G n W
  /-- the constant mechanism `κ_w(𝒙) = w`, for `w ∈ W` -/
  | const (w : G.Pt) (hw : w ∈ W) : Selector G n W

end SPFacilityGraph


