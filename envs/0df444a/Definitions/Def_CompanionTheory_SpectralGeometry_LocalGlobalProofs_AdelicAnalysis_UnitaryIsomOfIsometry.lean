-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:19.686797+00:00
-- url     : https://prove2.me/theorems/e134af41-426d-4dcd-9002-d392ed6081f6
-- title:
--   Unitary Isom Of Isometry
-- statement:
--   Definitions and structural lemmas for Unitary Isom Of Isometry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryIsomOfIsometry.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.HIsom
section Generic
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
def conjHomeo {T : Type} [Group T] [TopologicalSpace T] [ContinuousMul T] (H' H : Subgroup T) (G : T)
    (h₁ : ∀ u ∈ H', G * u * G⁻¹ ∈ H) (h₂ : ∀ u ∈ H, G⁻¹ * u * G ∈ H') : H' ≃ₜ* H where
  toFun u := ⟨G * u * G⁻¹, h₁ u u.2⟩
  invFun u := ⟨G⁻¹ * u * G, h₂ u u.2⟩
  left_inv u := by ext; simp [mul_assoc]
  right_inv u := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
end Generic
section Base
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
end Base
end GlobalTheory.CompanionTheory.SW.HIsom


