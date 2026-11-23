-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul
-- name    : Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:54.63602+00:00
-- url     : https://prove2.me/theorems/6a9cafee-bc1a-4f73-a4ac-d3e91727aba3
-- title:
--   Exists Unit Mul
-- statement:
--   Definitions and structural lemmas for Exists Unit Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsUnitMul.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SameZeroScheme
theorem top_le_preimage {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ V := by
  intro x _
  apply h
  have : hU.fromSpec (Spec.map φ x) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
  rw [hU.range_fromSpec] at this
  exact this
end GlobalTheory.SameZeroScheme


