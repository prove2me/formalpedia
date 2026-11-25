-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
-- name    : GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:23:25.003057+00:00
-- url     : https://prove2.me/theorems/75831135-50b0-410f-adad-3a0cf3080b42
-- title:
--   Norm One Compact
-- statement:
--   Definitions and structural lemmas for Norm One Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/NormOneCompact.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_normOneSubgroup_eq_map
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_diagonal_unitsToUnits_mem
import Theorems.Thm_GroundTheory_Global_IdeleGroup_exists_unit_forall_abs_log_le
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteModule_eq_one_of_mem
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isClosed_normOneSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isCompact_abs_log_le_inter_standardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace IdeleGroup
theorem exists_finset_mul_mem_standardOpenSubgroup :
    ∃ R : Finset (IdeleGroup K), ∀ x : IdeleGroup K, ∃ k : Kˣ, ∃ r ∈ R,
      diagonal K k * x * r⁻¹ ∈ standardOpenSubgroup K := by
  classical
  let s : ClassGroup (𝓞 K) → IdeleGroup K := Function.invFun toClassGroup
  refine ⟨Finset.univ.image s, fun x ↦ ?_⟩
  have hs : toClassGroup (s (toClassGroup x)) = toClassGroup x :=
    Function.invFun_eq (toClassGroup_surjective _)
  have hmem : x * (s (toClassGroup x))⁻¹ ∈ (diagonal K).range ⊔ standardOpenSubgroup K := by
    rw [← ker_toClassGroup, MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
  obtain ⟨_, ⟨k, rfl⟩, u, hu, hku⟩ := Subgroup.mem_sup.1 hmem
  refine ⟨k⁻¹, s (toClassGroup x), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  rw [map_inv, mul_assoc, ← hku, inv_mul_cancel_left]
  exact hu
theorem exists_isCompact_of_finset (R : Finset (IdeleGroup K))
    (hR : ∀ x : IdeleGroup K, ∃ k : Kˣ, ∃ r ∈ R,
      diagonal K k * x * r⁻¹ ∈ standardOpenSubgroup K) :
    ∃ D : Set (IdeleGroup K), IsCompact D ∧
      ∀ x ∈ normOneSubgroup K, ∃ k : Kˣ, diagonal K k * x ∈ D := by
  obtain ⟨M, hM⟩ := exists_unit_forall_abs_log_le (K := K)
    (∑ r ∈ R, |Real.log (ideleModule K r : ℝ)|)
  let S := {x : IdeleGroup K | (∀ w : InfinitePlace K, |Real.log ‖(x : 𝔸[K]).1 w‖| ≤ M) ∧
    x ∈ standardOpenSubgroup K}
  refine ⟨⋃ r ∈ R, (fun s ↦ s * r) '' S, R.isCompact_biUnion fun r _ ↦
    (isCompact_abs_log_le_inter_standardOpenSubgroup K M).image
      (continuous_id.mul continuous_const), fun x hx ↦ ?_⟩
  obtain ⟨k, r, hr, hy⟩ := hR x
  set y := diagonal K k * x * r⁻¹ with hydef
  have hmod : ideleModule K y = (ideleModule K r)⁻¹ := by
    rw [hydef, map_mul, map_mul, map_inv, ideleModule_diagonal, MonoidHom.mem_ker.1 hx, one_mul,
      one_mul]
  have hinf : |Real.log (infiniteModule y)| ≤ ∑ r ∈ R, |Real.log (ideleModule K r : ℝ)| := by
    have h1 : infiniteModule y = ((ideleModule K r : ℝ))⁻¹ := by
      have := congrArg Subtype.val hmod
      rw [ideleModule_apply, finiteModule_eq_one_of_mem hy, mul_one] at this
      exact this
    rw [h1, Real.log_inv, abs_neg]
    exact Finset.single_le_sum (f := fun r ↦ |Real.log (ideleModule K r : ℝ)|)
      (fun r _ ↦ abs_nonneg _) hr
  obtain ⟨u, hu⟩ := hM y hinf
  refine ⟨unitsToUnits K u * k, Set.mem_biUnion hr
    ⟨diagonal K (unitsToUnits K u) * y, ⟨hu, mul_mem (diagonal_unitsToUnits_mem K u) hy⟩, ?_⟩⟩
  simp only [hydef, map_mul, mul_assoc, inv_mul_cancel, mul_one]
theorem exists_isCompact_normOneSubgroup :
    ∃ D : Set (IdeleGroup K), IsCompact D ∧ D ⊆ normOneSubgroup K ∧
      ∀ x ∈ normOneSubgroup K, ∃ k : Kˣ, diagonal K k * x ∈ D := by
  obtain ⟨R, hR⟩ := exists_finset_mul_mem_standardOpenSubgroup K
  obtain ⟨D, hD, hxD⟩ := exists_isCompact_of_finset K R hR
  refine ⟨D ∩ normOneSubgroup K, hD.inter_right (isClosed_normOneSubgroup K),
    Set.inter_subset_right, fun x hx ↦ ?_⟩
  obtain ⟨k, hk⟩ := hxD x hx
  exact ⟨k, hk, mul_mem (range_diagonal_le_normOneSubgroup K ⟨k, rfl⟩) hx⟩
instance compactSpace_normOneSubgroup_quotient :
    CompactSpace (normOneSubgroup K ⧸ (diagonal K).range.subgroupOf (normOneSubgroup K)) := by
  obtain ⟨D, hD, -, hxD⟩ := exists_isCompact_normOneSubgroup K
  have hD' : IsCompact ((Subtype.val : normOneSubgroup K → IdeleGroup K) ⁻¹' D) :=
    (isClosed_normOneSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hD
  have h : (QuotientGroup.mk : normOneSubgroup K →
      normOneSubgroup K ⧸ (diagonal K).range.subgroupOf (normOneSubgroup K)) ''
      ((Subtype.val : normOneSubgroup K → IdeleGroup K) ⁻¹' D) = Set.univ := by
    refine Set.eq_univ_of_forall fun q ↦ ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hxD x x.2
    refine ⟨⟨diagonal K k * x, mul_mem (range_diagonal_le_normOneSubgroup K ⟨k, rfl⟩) x.2⟩, hk,
      (QuotientGroup.eq.2 ?_).symm⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨k, ?_⟩
    change diagonal K k = ((x : IdeleGroup K))⁻¹ * (diagonal K k * x)
    rw [mul_comm (diagonal K k) x, inv_mul_cancel_left]
  exact isCompact_univ_iff.1 (h ▸ hD'.image QuotientGroup.continuous_mk)
end IdeleGroup
namespace IdeleClassGroup
theorem isCompact_normOneSubgroup :
    IsCompact (normOneSubgroup K : Set (IdeleClassGroup K)) := by
  obtain ⟨D, hD, hDJ, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup K
  have h : (normOneSubgroup K : Set (IdeleClassGroup K)) = mk K '' D := by
    rw [normOneSubgroup_eq_map, Subgroup.coe_map]
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hxD x hx
      refine ⟨IdeleGroup.diagonal K k * x, hk, ?_⟩
      rw [map_mul, mk_diagonal]
      exact one_mul (mk K x)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hDJ hx, rfl⟩
  rw [h]
  exact hD.image (continuous_mk K)
instance compactSpace_normOneSubgroup : CompactSpace (normOneSubgroup K) :=
  isCompact_iff_compactSpace.1 (isCompact_normOneSubgroup K)
end IdeleClassGroup
end
end GroundTheory.Global


