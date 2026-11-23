-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
-- name    : GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:10:15.141279+00:00
-- url     : https://prove2.me/theorems/805cc7ac-35f8-4d1c-95dc-96d3d6b1f369
-- title:
--   Real Groups Iwasawa Haar
-- statement:
--   Definitions and structural lemmas for Real Groups Iwasawa Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsIwasawaHaar.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic
open Matrix Set
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
theorem rclike_inv_pos {z : 𝕜} (hz : 0 < z) : 0 < z⁻¹ := by
  obtain ⟨hre, him⟩ := RCLike.pos_iff.1 hz
  have hz' : z = (RCLike.re z : 𝕜) := by rw [← RCLike.re_add_im z, him]; simp
  rw [hz', ← RCLike.ofReal_inv]
  exact RCLike.ofReal_pos.2 (inv_pos.2 hre)
def upperPosSubgroup (n 𝕜 : Type*) [RCLike 𝕜] [Fintype n] [LinearOrder n] : Subgroup (GL n 𝕜) where
  carrier := {g | (g : Matrix n n 𝕜).IsUpperTriangular ∧ ∀ i, 0 < (g : Matrix n n 𝕜) i i}
  mul_mem' {a b} ha hb := ⟨ha.1.mul hb.1, fun i => by
    rw [Units.val_mul, mul_apply_self_of_isUpperTriangular ha.1 hb.1]
    exact mul_pos (ha.2 i) (hb.2 i)⟩
  one_mem' := ⟨blockTriangular_one, fun i => by simp⟩
  inv_mem' {a} ha := by
    let : Invertible (a : Matrix n n 𝕜) :=
      invertibleOfIsUnitDet _ ((isUnit_iff_isUnit_det _).1 a.isUnit)
    have hinv : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜) = (a : Matrix n n 𝕜)⁻¹ := coe_units_inv a
    have hU : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜).IsUpperTriangular := by
      rw [hinv]; exact blockTriangular_inv_of_blockTriangular ha.1
    refine ⟨hU, fun i => ?_⟩
    have e0 : ((a⁻¹ : GL n 𝕜) : Matrix n n 𝕜) * (a : Matrix n n 𝕜) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e := congrFun (congrFun e0 i) i
    rw [mul_apply_self_of_isUpperTriangular hU ha.1, one_apply_eq] at e
    rw [eq_inv_of_mul_eq_one_left e]
    exact rclike_inv_pos (ha.2 i)
theorem mem_upperPosSubgroup {g : GL n 𝕜} :
    g ∈ upperPosSubgroup n 𝕜 ↔
      (g : Matrix n n 𝕜).IsUpperTriangular ∧ ∀ i, 0 < (g : Matrix n n 𝕜) i i := Iff.rfl
def kbMul (p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜) : GL n 𝕜 :=
  Unitary.toUnits p.1 * p.2
section Split
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
theorem conjTranspose_iwasawaK_mul_mem (g : GL n 𝕜) :
    (Unitary.toUnits (iwasawaK g))⁻¹ * g ∈ upperPosSubgroup n 𝕜 := by
  have e : (((Unitary.toUnits (iwasawaK g))⁻¹ * g : GL n 𝕜) : Matrix n n 𝕜) =
      ((iwasawaK g : Matrix n n 𝕜))ᴴ * g := rfl
  rw [mem_upperPosSubgroup, e, iwasawaK_conjTranspose_mul]
  refine ⟨(blockTriangular_diagonal _).mul (iwasawaEquiv.symm g).2.2.2.1, fun i => ?_⟩
  rw [diagonal_mul, (iwasawaEquiv.symm g).2.2.2.2 i, mul_one]
  exact RCLike.ofReal_pos.2 ((iwasawaEquiv.symm g).2.1.2 i)
noncomputable def kbSplit (g : GL n 𝕜) : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜 :=
  (iwasawaK g, ⟨_, conjTranspose_iwasawaK_mul_mem g⟩)
theorem iwasawaK_kbMul (p : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜) :
    iwasawaK (kbMul p) = p.1 := by
  symm
  apply eq_iwasawaK_of_mem
  have e : ((p.1 : Matrix n n 𝕜))ᴴ * (kbMul p : Matrix n n 𝕜) = ((p.2 : GL n 𝕜) : Matrix n n 𝕜) := by
    show ((p.1 : Matrix n n 𝕜))ᴴ * ((p.1 : Matrix n n 𝕜) * ((p.2 : GL n 𝕜) : Matrix n n 𝕜)) = _
    rw [← Matrix.mul_assoc, show ((p.1 : Matrix n n 𝕜))ᴴ * p.1 = 1 from p.1.2.1, Matrix.one_mul]
  refine ⟨?_, fun i => ?_⟩
  · rw [e]; exact p.2.2.1
  · rw [e]
    obtain ⟨hre, him⟩ := RCLike.pos_iff.1 (p.2.2.2 i)
    exact ⟨hre.le, him⟩
noncomputable def kbHomeomorph : unitaryGroup n 𝕜 × upperPosSubgroup n 𝕜 ≃ₜ GL n 𝕜 where
  toFun := kbMul
  invFun := kbSplit
  left_inv p := by
    ext : 1
    · exact iwasawaK_kbMul p
    · apply Subtype.ext
      show (Unitary.toUnits (iwasawaK (kbMul p)))⁻¹ * (Unitary.toUnits p.1 * p.2) = p.2
      rw [iwasawaK_kbMul, inv_mul_cancel_left]
  right_inv g := by
    show Unitary.toUnits (iwasawaK g) * ((Unitary.toUnits (iwasawaK g))⁻¹ * g) = g
    rw [mul_inv_cancel_left]
  continuous_toFun := by
    have ht : Continuous (fun k : unitaryGroup n 𝕜 => Unitary.toUnits k) :=
      Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
    exact (ht.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have ht : Continuous (fun k : unitaryGroup n 𝕜 => Unitary.toUnits k) :=
      Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
    refine continuous_iwasawaK.prodMk (Continuous.subtype_mk ?_ _)
    exact ((ht.comp continuous_iwasawaK).inv).mul continuous_id
end Split
section HaarKB
open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator
instance : SecondCountableTopology (Matrix n n ℝ) :=
  inferInstanceAs (SecondCountableTopology (n → n → ℝ))
instance : SecondCountableTopology (GL n ℝ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℝ)).isEmbedding.secondCountableTopology
instance : LocallyCompactSpace (GL n ℝ) :=
  (Units.isOpenEmbedding_val (R := Matrix n n ℝ)).locallyCompactSpace
instance : SecondCountableTopology (upperPosSubgroup n ℝ) :=
  TopologicalSpace.Subtype.secondCountableTopology _
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
theorem isClosed_upperPosSubgroup : IsClosed (upperPosSubgroup n ℝ : Set (GL n ℝ)) := by
  have e : (upperPosSubgroup n ℝ : Set (GL n ℝ)) =
      (⋂ i, ⋂ j, {g : GL n ℝ | j < i → (g : Matrix n n ℝ) i j = 0}) ∩
        ⋂ i, {g : GL n ℝ | 0 ≤ (g : Matrix n n ℝ) i i} := by
    ext g
    simp only [SetLike.mem_coe, mem_upperPosSubgroup, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨hU, hpos⟩; exact ⟨fun i j h => hU h, fun i => (hpos i).le⟩
    · rintro ⟨hU, hnn⟩
      have hU' : (g : Matrix n n ℝ).IsUpperTriangular := fun i j h => hU i j h
      refine ⟨hU', fun i => lt_of_le_of_ne (hnn i) (Ne.symm ?_)⟩
      have hdet := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
      rw [det_of_isUpperTriangular hU'] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
    (isClosed_iInter fun i => ?_)
  · by_cases h : j < i
    · simp only [h, forall_const]
      exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    · simp only [h, IsEmpty.forall_iff, ofPred_true, isClosed_univ]
  · exact isClosed_le continuous_const (Units.continuous_val.matrix_elem i i)
instance : LocallyCompactSpace (upperPosSubgroup n ℝ) :=
  isClosed_upperPosSubgroup.locallyCompactSpace
noncomputable def kbInvHomeomorph : GL n ℝ ≃ₜ unitaryGroup n ℝ × upperPosSubgroup n ℝ :=
  kbHomeomorph.symm.trans ((Homeomorph.refl _).prodCongr (Homeomorph.inv _))
end HaarKB
end GroundTheory.Automorphic


