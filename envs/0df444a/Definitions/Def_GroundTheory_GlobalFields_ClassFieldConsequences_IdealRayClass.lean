-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_IdealRayClass
-- name    : GroundTheory_GlobalFields_ClassFieldConsequences_IdealRayClass
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:05:41.922358+00:00
-- url     : https://prove2.me/theorems/17770483-ab69-5d3a-ba82-3ddee8bb9268
-- title:
--   Ideal Ray Class
-- statement:
--   Definitions and structural lemmas for Ideal Ray Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/IdealRayClass.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_RayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApproxUnits
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_Modulus_congruenceSubgroup_eq_inf
import Theorems.Thm_GroundTheory_Global_Modulus_congruenceSubgroup_le_idelesOneMod
import Theorems.Thm_GroundTheory_Global_Modulus_congruenceSubgroup_le_standardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_Modulus_finite_support_exponent
import Theorems.Thm_GroundTheory_Global_Modulus_mem_idelesOneMod
import Theorems.Thm_GroundTheory_Global_Modulus_one_le_exponent_iff
import Theorems.Thm_GroundTheory_Global_Modulus_quotientMapCongruenceEquiv_mk
import Theorems.Thm_GroundTheory_Global_Modulus_rayClassGroupEquiv_of_real_eq_univ_mk
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_denseRange_units_prod_pi
import Theorems.Thm_GroundTheory_Global_isOpen_unitsLevel
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.Modulus.quotientMapCongruenceEquiv_mk
attribute [local simp] GroundTheory.Global.Modulus.rayClassGroupEquiv_of_real_eq_univ_mk
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_circleToUnits
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
namespace GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open IdeleGroup
namespace Modulus
variable (𝔪 : Modulus K)
def coprimeIdeals : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.ideal →
    count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  one_mem' v _ := by rw [Units.val_one, count_one]
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul, count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, count_inv, hI v hv, neg_zero]
theorem ord_eq_zero_of_mem_idelesOneMod {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.ideal) : ord v x = 0 := by
  have h := ((𝔪.mem_idelesOneMod.1 hx).1 v hv).1
  rw [coe_finiteProj] at h
  rw [ord, h, log_one, neg_zero]
theorem toFractionalIdeal_mem_coprimeIdeals {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    toFractionalIdeal x ∈ 𝔪.coprimeIdeals := fun v hv ↦ by
  rw [count_toFractionalIdeal, 𝔪.ord_eq_zero_of_mem_idelesOneMod hx hv]
def principalRay : Subgroup 𝔪.coprimeIdeals :=
  (𝔪.rayUnits.map (toPrincipalIdeal (𝓞 K) K)).subgroupOf 𝔪.coprimeIdeals
theorem mem_principalRay {I : 𝔪.coprimeIdeals} :
    I ∈ 𝔪.principalRay ↔
      ∃ a ∈ 𝔪.rayUnits, toPrincipalIdeal (𝓞 K) K a = (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  rw [principalRay, Subgroup.mem_subgroupOf, Subgroup.mem_map]
abbrev IdealRayClassGroup : Type _ :=
  𝔪.coprimeIdeals ⧸ 𝔪.principalRay
theorem exists_diagonal_mul_mem_idelesOneMod (x : IdeleGroup K) :
    ∃ a : Kˣ, diagonal K a * x ∈ 𝔪.idelesOneMod := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 K)) := 𝔪.finite_support_exponent.toFinset
  let T : Finset (InfinitePlace K) := Finset.univ
  let O : Set (((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ)) :=
    (Set.univ.pi fun v : S ↦ {z | z * finiteProj v.1 x ∈ unitsLevel v.1 (𝔪.exponent v.1)}) ×ˢ
      (Set.univ.pi fun w : T ↦ {z | ∀ hw : w.1.IsReal,
        (⟨w.1, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ 𝔪.real →
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
            ((z * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)})
  have hO : IsOpen O := by
    refine (isOpen_set_pi Set.finite_univ fun v _ ↦ ?_).prod
      (isOpen_set_pi Set.finite_univ fun w _ ↦ ?_)
    · exact (isOpen_unitsLevel v.1 _).preimage (continuous_mul_const _)
    · simp only [Set.ofPred_forall]
      refine isOpen_iInter_of_finite fun hw ↦ isOpen_iInter_of_finite fun _ ↦ ?_
      exact isOpen_lt continuous_const
        ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp
          (Units.continuous_val.comp (continuous_mul_const _)))
  have hne : O.Nonempty := by
    refine ⟨(fun v ↦ (finiteProj v.1 x)⁻¹, fun w ↦ (infiniteProj w.1 x)⁻¹),
      Set.mem_univ_pi.2 fun v ↦ ?_, Set.mem_univ_pi.2 fun w ↦ ?_⟩
    · show (finiteProj v.1 x)⁻¹ * finiteProj v.1 x ∈ unitsLevel v.1 (𝔪.exponent v.1)
      rw [inv_mul_cancel]
      exact one_mem _
    · intro hw _
      show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (((infiniteProj w.1 x)⁻¹ * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)
      rw [inv_mul_cancel, Units.val_one, map_one]
      exact one_pos
  obtain ⟨a, ha⟩ := (denseRange_units_prod_pi S T).exists_mem_open hO hne
  refine ⟨a, 𝔪.mem_idelesOneMod.2 ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩⟩
  · have hvS : v ∈ S := by
      rw [Set.Finite.mem_toFinset, mem_support, ← Nat.one_le_iff_ne_zero]
      exact (𝔪.one_le_exponent_iff v).2 hv
    have h := Set.mem_univ_pi.1 ha.1 ⟨v, hvS⟩
    have he : finiteProj v (diagonal K a) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
      refine Units.ext ?_
      change ((a : K) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) a
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [map_mul, he]
    exact h
  · have h := Set.mem_univ_pi.1 ha.2 ⟨w.1, Finset.mem_univ _⟩ w.2 hw
    have he : infiniteProj w.1 (diagonal K a) =
        Units.map (algebraMap K w.1.Completion).toMonoidHom a :=
      Units.ext rfl
    rw [map_mul, he]
    exact h
def idelesOneModToCoprimeIdeals : 𝔪.idelesOneMod →* 𝔪.coprimeIdeals :=
  ((toFractionalIdeal (K := K)).comp 𝔪.idelesOneMod.subtype).codRestrict _
    fun x ↦ 𝔪.toFractionalIdeal_mem_coprimeIdeals x.2
@[simp]
theorem coe_idelesOneModToCoprimeIdeals (x : 𝔪.idelesOneMod) :
    ((𝔪.idelesOneModToCoprimeIdeals x : 𝔪.coprimeIdeals) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toFractionalIdeal (x : IdeleGroup K) :=
  rfl
def toIdealRayClassGroup : 𝔪.idelesOneMod →* 𝔪.IdealRayClassGroup :=
  (QuotientGroup.mk' _).comp 𝔪.idelesOneModToCoprimeIdeals
def toRayClassGroup : 𝔪.idelesOneMod →* 𝔪.RayClassGroup :=
  (QuotientGroup.mk' _).comp 𝔪.idelesOneMod.subtype
theorem exists_mem_idelesOneMod_toFractionalIdeal_eq {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    ∃ x ∈ 𝔪.idelesOneMod, toFractionalIdeal x = primeIdealUnit v := by
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h
    rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'
    exact exp_ne_zero h'
  refine ⟨finiteEmbedding v (Units.mk0 _ hne), 𝔪.mem_idelesOneMod.2 ⟨fun w hw ↦ ?_, fun w _ ↦ ?_⟩,
    toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩
  · have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
    rw [finiteProj_finiteEmbedding_of_ne hwv]
    exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos
  · rw [count_primeIdealUnit]
    split_ifs with h
    · subst h
      rw [ord_finiteEmbedding_self, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ, log_exp,
        neg_neg]
    · exact ord_finiteEmbedding_of_ne h _
theorem idelesOneModToCoprimeIdeals_surjective : Surjective 𝔪.idelesOneModToCoprimeIdeals := by
  rintro ⟨I, hI⟩
  have h : I ∈ 𝔪.idelesOneMod.map (toFractionalIdeal (K := K)) := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    refine finprod_induction (· ∈ 𝔪.idelesOneMod.map (toFractionalIdeal (K := K))) (one_mem _)
      (fun _ _ ↦ mul_mem) fun v ↦ ?_
    by_cases hv : v.asIdeal ∣ 𝔪.ideal
    · rw [hI v hv, zpow_zero]
      exact one_mem _
    · obtain ⟨x, hx, hxI⟩ := 𝔪.exists_mem_idelesOneMod_toFractionalIdeal_eq hv
      exact zpow_mem (Subgroup.mem_map.2 ⟨x, hx, hxI⟩) _
  obtain ⟨x, hx, hxI⟩ := h
  exact ⟨⟨x, hx⟩, Subtype.ext hxI⟩
theorem toIdealRayClassGroup_surjective : Surjective 𝔪.toIdealRayClassGroup :=
  (QuotientGroup.mk'_surjective _).comp 𝔪.idelesOneModToCoprimeIdeals_surjective
theorem toRayClassGroup_surjective : Surjective 𝔪.toRayClassGroup := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, ha⟩ := 𝔪.exists_diagonal_mul_mem_idelesOneMod x
  refine ⟨⟨_, ha⟩, ?_⟩
  change (QuotientGroup.mk (diagonal K a * x) : 𝔪.RayClassGroup) = QuotientGroup.mk x
  rw [QuotientGroup.eq, show (diagonal K a * x)⁻¹ * x = (diagonal K a)⁻¹ by
    rw [mul_inv_rev, mul_comm x⁻¹, mul_assoc, inv_mul_cancel, mul_one]]
  exact inv_mem (𝔪.diagonal_range_le_rayGroup ⟨a, rfl⟩)
theorem ker_toRayClassGroup :
    𝔪.toRayClassGroup.ker = 𝔪.rayGroup.subgroupOf 𝔪.idelesOneMod := by
  ext x
  rw [MonoidHom.mem_ker, toRayClassGroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl
theorem ker_toIdealRayClassGroup :
    𝔪.toIdealRayClassGroup.ker = 𝔪.rayGroup.subgroupOf 𝔪.idelesOneMod := by
  ext ⟨x, hx⟩
  rw [MonoidHom.mem_ker, toIdealRayClassGroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_principalRay, Subgroup.mem_subgroupOf, rayGroup, Subgroup.mem_sup]
  constructor
  · rintro ⟨a, ha, hax⟩
    change toPrincipalIdeal (𝓞 K) K a = toFractionalIdeal x at hax
    refine ⟨diagonal K a, ⟨a, rfl⟩, (diagonal K a)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩
    rw [congruenceSubgroup_eq_inf, Subgroup.mem_inf, ← ker_toFractionalIdeal, MonoidHom.mem_ker,
      map_mul, map_inv, toFractionalIdeal_diagonal, hax]
    exact ⟨mul_mem (inv_mem ha) hx, inv_mul_cancel _⟩
  · rintro ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
    have hu' := 𝔪.congruenceSubgroup_le_idelesOneMod hu
    have ha : a ∈ 𝔪.rayUnits := by
      change diagonal K a ∈ 𝔪.idelesOneMod
      rw [← mul_inv_cancel_right (diagonal K a) u]
      exact mul_mem hx (inv_mem hu')
    refine ⟨a, ha, ?_⟩
    change toPrincipalIdeal (𝓞 K) K a = toFractionalIdeal (diagonal K a * u)
    have hu0 : toFractionalIdeal u = 1 := by
      rw [← MonoidHom.mem_ker, ker_toFractionalIdeal]
      exact 𝔪.congruenceSubgroup_le_standardOpenSubgroup hu
    rw [map_mul, hu0, mul_one, toFractionalIdeal_diagonal]
def rayClassGroupEquiv : 𝔪.RayClassGroup ≃* 𝔪.IdealRayClassGroup :=
  (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toRayClassGroup_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (𝔪.ker_toRayClassGroup.trans 𝔪.ker_toIdealRayClassGroup.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toIdealRayClassGroup_surjective))
def quotientEquivIdealRayClassGroup :
    IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≃* 𝔪.IdealRayClassGroup :=
  𝔪.quotientMapCongruenceEquiv.trans 𝔪.rayClassGroupEquiv
def idealRayClassGroupEquiv_of_real_eq_univ (h : 𝔪.real = Set.univ) :
    _root_.GroundTheory.Global.RayClassGroup K 𝔪.ideal ≃* 𝔪.IdealRayClassGroup :=
  (𝔪.rayClassGroupEquiv_of_real_eq_univ h).symm.trans 𝔪.rayClassGroupEquiv
instance : Finite 𝔪.IdealRayClassGroup :=
  Finite.of_equiv _ 𝔪.rayClassGroupEquiv.toEquiv
end Modulus
end
end GroundTheory.Global


