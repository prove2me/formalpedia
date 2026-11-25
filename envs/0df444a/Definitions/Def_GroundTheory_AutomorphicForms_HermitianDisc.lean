-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
-- name    : GroundTheory_AutomorphicForms_HermitianDisc
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:08:08.900032+00:00
-- url     : https://prove2.me/theorems/42bcaf08-de13-47cd-8c45-6be00c4b78f9
-- title:
--   Hermitian Disc
-- statement:
--   Definitions and structural lemmas for Hermitian Disc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_algebraMap
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_conj_eq_self_iff
import Theorems.Thm_GroundTheory_Automorphic_isHermitianFor_gram
import Theorems.Thm_GroundTheory_Automorphic_isUnit_det_gram
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Module Matrix GroundTheory.LocalField
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
namespace HermitianForm
variable [Algebra.IsSeparable F E]
theorem det_gram_mem_range (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι E V) : (gram h.toSesq b).det ∈ Set.range (algebraMap F E) := by
  apply conj_eq_self_iff.1
  rw [← conjHom_apply, RingHom.map_det, RingHom.mapMatrix_apply, ← det_transpose,
    isHermitianFor_gram h b]
def detUnit (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι E V) : Fˣ :=
  Units.mk0 (h.det_gram_mem_range b).choose (by
    intro h0
    have := (h.det_gram_mem_range b).choose_spec
    rw [h0, map_zero] at this
    exact (isUnit_det_gram h b).ne_zero this.symm)
def disc [FiniteDimensional E V] (h : HermitianForm F E V) : Fˣ ⧸ (normUnits F E).range :=
  QuotientGroup.mk (h.detUnit (Module.finBasis E V))
end HermitianForm
def diagForm {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ) :
    HermitianForm F E (ι → E) where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => ∑ i, conj F E (x i) * algebraMap F E (a i) * y i)
    (fun x x' y => by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conjHom_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
  isSymm := ⟨fun x y => by
    simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_sum, map_mul, conj_conj,
      conj_algebraMap]
    exact Finset.sum_congr rfl fun i _ => by ring⟩
  nonsingular := by
    have ha : ∀ i, algebraMap F E (a i) ≠ 0 := fun i => by simp
    have key : ∀ (x : ι → E) (j : ι),
        (∑ i, conj F E (x i) * algebraMap F E (a i) * (Pi.single j 1 : ι → E) i) =
          conj F E (x j) * algebraMap F E (a j) := by
      intro x j
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [Pi.single_apply, hij]
      · simp
    constructor
    · intro x y hxy
      funext j
      have h1 := LinearMap.congr_fun hxy (Pi.single j 1)
      simp only [LinearMap.mk₂'ₛₗ_apply, key] at h1
      have h2 := mul_right_cancel₀ (ha j) h1
      rw [← conj_conj (F := F) (x j), h2, conj_conj]
    · intro f
      refine ⟨fun j => conj F E (f (Pi.single j 1) * (algebraMap F E (a j))⁻¹),
        LinearMap.ext fun y => ?_⟩
      simp only [LinearMap.mk₂'ₛₗ_apply, conj_conj]
      conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ f y]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : (fun j => if i = j then (1 : E) else 0) = Pi.single i 1 := by
        funext j; simp [Pi.single_apply, eq_comm]
      rw [this, smul_eq_mul]
      field_simp [ha i]
end GroundTheory.Automorphic
end


