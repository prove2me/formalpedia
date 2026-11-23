-- Prove2me | Definitions.Def_GroundTheory_LocalFields_Ramification
-- name    : GroundTheory_LocalFields_Ramification
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:20.868012+00:00
-- url     : https://prove2.me/theorems/fa1f385e-d610-41f8-86fe-62a414f8cd2e
-- title:
--   Ramification
-- statement:
--   Definitions and structural lemmas for Ramification, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
section Action
variable {K L}
theorem integerAlgEquiv_mem_maximalIdeal_pow_iff (σ : L ≃ₐ[K] L) (n : ℕ) (x : 𝒪[L]) :
    integerAlgEquiv K L σ x ∈ 𝓂[L] ^ n ↔ x ∈ 𝓂[L] ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hσϖ : Irreducible (integerAlgEquiv K L σ ϖ) :=
    (MulEquiv.irreducible_iff (f := (integerAlgEquiv K L σ : 𝒪[L] ≃* 𝒪[L]))).mpr hϖ
  rw [mem_maximalIdeal_pow_iff hσϖ, mem_maximalIdeal_pow_iff hϖ, ← map_pow,
    map_dvd_iff (integerAlgEquiv K L σ)]
end Action
def lowerRamificationGroup (i : ℤ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (i + 1).toNat}
  one_mem' x := by simp
  mul_mem' {σ τ} hσ hτ x := by
    have h : integerAlgEquiv K L (σ * τ) x - x =
        (integerAlgEquiv K L σ (integerAlgEquiv K L τ x) - integerAlgEquiv K L τ x) +
          (integerAlgEquiv K L τ x - x) := by
      rw [map_mul, AlgEquiv.mul_apply]; ring
    rw [h]
    exact add_mem (hσ _) (hτ x)
  inv_mem' {σ} hσ x := by
    have h := hσ (integerAlgEquiv K L σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply] at h
    rw [← neg_sub]
    exact neg_mem h
variable {K L}
variable (K L)
instance lowerRamificationGroup_normal (i : ℤ) : (lowerRamificationGroup K L i).Normal where
  conj_mem σ hσ τ x := by
    set y := integerAlgEquiv K L τ⁻¹ x
    have hx : x = integerAlgEquiv K L τ y := by
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    have h : integerAlgEquiv K L (τ * σ * τ⁻¹) x - x =
        integerAlgEquiv K L τ (integerAlgEquiv K L σ y - y) := by
      rw [map_sub, map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hx]
    rw [h, integerAlgEquiv_mem_maximalIdeal_pow_iff]
    exact hσ y
variable {K L}
variable (K L)
end GroundTheory.LocalField


