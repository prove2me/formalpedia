-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_Decimal
-- name    : SharpIntermediateSubgroupBounds_Decimal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:41:01.643454+00:00
-- url     : https://prove2.me/theorems/42d9c1e0-7b04-4e9a-9d89-fafb6a5e0639
-- title:
--   Decimal
-- statement:
--   Definitions and structural lemmas for Decimal, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Decimal.lean

import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators
open Filter Finset Topology
noncomputable def eulerUpper20 : ℝ :=
  (∏ n ∈ Finset.range 20, (1 - (1 / 2 : ℝ) ^ (n + 1))⁻¹) *
    (1 - (1 / 2 : ℝ) ^ 20)⁻¹
noncomputable def thetaUpper4 : ℝ :=
  1 + 2 * (∑ n ∈ Finset.range 4, (1 / 2 : ℝ) ^ ((n + 1) ^ 2)) +
    2 * ((1 / 2 : ℝ) ^ 25 * (1 - (1 / 2 : ℝ) ^ 11)⁻¹)
noncomputable def eulerLower50 : ℝ :=
  ∏ n ∈ Finset.range 50, (1 - (1 / 2 : ℝ) ^ (n + 1))⁻¹
noncomputable def eulerUpper50 : ℝ :=
  eulerLower50 * (1 - (1 / 2 : ℝ) ^ 50)⁻¹
noncomputable def thetaLower6 : ℝ :=
  1 + 2 * ∑ n ∈ Finset.range 6, (1 / 2 : ℝ) ^ ((n + 1) ^ 2)
noncomputable def thetaUpper6 : ℝ :=
  thetaLower6 +
    2 * ((1 / 2 : ℝ) ^ 49 * (1 - (1 / 2 : ℝ) ^ 15)⁻¹)
end SharpIntermediateSubgroupBounds


