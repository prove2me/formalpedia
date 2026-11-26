-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_Theta
-- name    : SharpIntermediateSubgroupBounds_Theta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:40:41.696276+00:00
-- url     : https://prove2.me/theorems/c8792dba-ed00-5191-8f38-00d8051b65e9
-- title:
--   Theta
-- statement:
--   Definitions and structural lemmas for Theta, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Theta.lean

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
noncomputable def gammaR (p : ℝ) (r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r, (1 - p⁻¹ ^ (j + 1))
noncomputable def eulerC (p : ℝ) : ℝ :=
  ∏' n : ℕ, (1 - p⁻¹ ^ (n + 1))⁻¹
noncomputable def gaussianTheta (p : ℝ) : ℝ :=
  ∑' z : ℤ, Real.exp (-Real.log p * (z : ℝ) ^ 2)
noncomputable def sharpConstant (p : ℝ) : ℝ :=
  eulerC p * gaussianTheta p
noncomputable def shiftedTheta (p x : ℝ) : ℝ :=
  ∑' z : ℤ, Real.exp (-Real.log p * ((z : ℝ) - x) ^ 2)
noncomputable def eulerCorrection (p : ℝ) (n : ℕ) : ℝ :=
  p⁻¹ ^ (n + 1) / (1 - p⁻¹ ^ (n + 1))
noncomputable def finiteThetaSum (p L : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (Nat.floor L + 1),
    (gammaR p r)⁻¹ * Real.exp (Real.log p * (r : ℝ) * (L - r))
end SharpIntermediateSubgroupBounds


