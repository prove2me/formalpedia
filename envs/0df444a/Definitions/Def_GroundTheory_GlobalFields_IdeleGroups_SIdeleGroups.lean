-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
-- name    : GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:14.999863+00:00
-- url     : https://prove2.me/theorems/0e3c91dd-bce0-46db-97db-1dff6e65656f
-- title:
--   SIdele Groups
-- statement:
--   Definitions and structural lemmas for SIdele Groups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ker_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding


set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace IdeleGroup
def sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ v ∉ S, ord v x = 0}
  one_mem' v _ := ord_one v
  mul_mem' {x y} hx hy v hv := by rw [ord_mul, hx v hv, hy v hv, add_zero]
  inv_mem' {x} hx v hv := by rw [ord_inv, hx v hv, neg_zero]
variable (S : Set (HeightOneSpectrum (𝓞 K)))
theorem mem_sIdeles {x : IdeleGroup K} : x ∈ sIdeles S ↔ ∀ v ∉ S, ord v x = 0 :=
  Iff.rfl
theorem neg_log_eq_zero_iff {y : ℤᵐ⁰} (hy : y ≠ 0) : -log y = 0 ↔ y = 1 := by
  rw [neg_eq_zero]
  constructor
  · intro h
    rw [← exp_log hy, h, exp_zero]
  · rintro rfl
    exact log_one
theorem diagonal_mem_sIdeles_iff (a : Kˣ) : diagonal K a ∈ sIdeles S ↔ a ∈ S.unit K := by
  have ha : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (a : K) ≠ 0 := fun v ↦
    (Valuation.ne_zero_iff _).2 a.ne_zero
  simp only [mem_sIdeles, ord_diagonal, neg_log_eq_zero_iff (ha _)]
  rfl
theorem exists_diagonal_mul_of_sup_eq_top (h : (diagonal K).range ⊔ sIdeles S = ⊤)
    (x : IdeleGroup K) : ∃ a : Kˣ, ∃ s ∈ sIdeles S, diagonal K a * s = x := by
  have hx : x ∈ (diagonal K).range ⊔ sIdeles S := h ▸ Subgroup.mem_top x
  obtain ⟨_, ⟨a, rfl⟩, s, hs, hx⟩ := Subgroup.mem_sup.1 hx
  exact ⟨a, s, hs, hx⟩
def sUnitsToSIdeles : S.unit K →* sIdeles S :=
  ((diagonal K).comp (S.unit K).subtype).codRestrict (sIdeles S) fun a ↦
    (diagonal_mem_sIdeles_iff S a).2 a.2
@[simp]
theorem coe_sUnitsToSIdeles (a : S.unit K) :
    (sUnitsToSIdeles S a : IdeleGroup K) = diagonal K a :=
  rfl
def sIdelesToIdeleClassGroup : sIdeles S →* IdeleClassGroup K :=
  (IdeleClassGroup.mk K).comp (sIdeles S).subtype
@[simp]
theorem sIdelesToIdeleClassGroup_apply (s : sIdeles S) :
    sIdelesToIdeleClassGroup S s = IdeleClassGroup.mk K s :=
  rfl
theorem range_sUnitsToSIdeles :
    (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, coe_sUnitsToSIdeles]
    exact IdeleClassGroup.mk_diagonal K a
  · intro hy
    rw [MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, ← MonoidHom.mem_ker,
      IdeleClassGroup.ker_mk] at hy
    obtain ⟨a, ha⟩ := hy
    have haS : a ∈ S.unit K := (diagonal_mem_sIdeles_iff S a).1 (ha ▸ y.2)
    exact ⟨⟨a, haS⟩, Subtype.ext ha⟩
theorem sIdelesToIdeleClassGroup_surjective_iff :
    Function.Surjective (sIdelesToIdeleClassGroup S) ↔ (diagonal K).range ⊔ sIdeles S = ⊤ := by
  constructor
  · intro h
    refine eq_top_iff.2 fun y _ ↦ ?_
    obtain ⟨s, hs⟩ := h (IdeleClassGroup.mk K y)
    rw [sIdelesToIdeleClassGroup_apply] at hs
    have hr : (s : IdeleGroup K)⁻¹ * y ∈ (diagonal K).range := by
      rw [← IdeleClassGroup.ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    have h' := mul_mem (Subgroup.mem_sup_right (S := (diagonal K).range) s.2)
      (Subgroup.mem_sup_left (T := sIdeles S) hr)
    rwa [mul_inv_cancel_left] at h'
  · intro h c
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective K c
    obtain ⟨a, s, hs, rfl⟩ := exists_diagonal_mul_of_sup_eq_top S h y
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [sIdelesToIdeleClassGroup_apply, map_mul, IdeleClassGroup.mk_diagonal]
    exact (one_mul (IdeleClassGroup.mk K s)).symm
instance : (sUnitsToSIdeles S).range.Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
def sIdelesQuotientEquiv (h : (diagonal K).range ⊔ sIdeles S = ⊤) :
    sIdeles S ⧸ (sUnitsToSIdeles S).range ≃* IdeleClassGroup K :=
  (QuotientGroup.quotientMulEquivOfEq (range_sUnitsToSIdeles S)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((sIdelesToIdeleClassGroup_surjective_iff S).2 h))
end IdeleGroup
end
end GroundTheory.Global


