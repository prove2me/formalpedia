-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
-- name    : GroundTheory_GlobalFields_TateThesis_HeckeChar
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:00:26.122729+00:00
-- url     : https://prove2.me/theorems/c357b201-762c-58d3-b52f-6e97842f680d
-- title:
--   Hecke Char
-- statement:
--   Definitions and structural lemmas for Hecke Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Theorems.Thm_GroundTheory_Global_Circle_noSmallSubgroups
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_conductor_ne_bot
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding_of_ne
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_map_idealLevel_le_ker_iff
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_finiteLevel
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_unitsLevel_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply


set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
namespace GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
abbrev HeckeCharacter : Type _ := IdeleClassGroup K →ₜ* Circle
variable {K}
def idealsPrimeTo (𝔪 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 →
    count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  one_mem' := fun v _ ↦ by rw [Units.val_one, count_one]
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul, count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, count_inv, hI v hv, neg_zero]
theorem primeIdealUnit_mem_idealsPrimeTo {𝔪 : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪) : primeIdealUnit v ∈ idealsPrimeTo 𝔪 := by
  classical
  intro w hw
  rw [count_primeIdealUnit, if_neg]
  rintro rfl
  exact hv hw
namespace IdeleGroup
theorem exists_uniformizer (v : HeightOneSpectrum (𝓞 K)) :
    ∃ π : (v.adicCompletion K)ˣ, Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h
    rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'
    exact exp_ne_zero h'
  exact ⟨Units.mk0 _ hne, by rw [Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ]⟩
@[simp]
theorem toInfinite_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    toInfinite K (finiteEmbedding v a) = 1 :=
  Units.ext rfl
theorem finiteComponent_toFinite (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    finiteComponent v (toFinite K x) = finiteProj v x :=
  Units.ext rfl
@[simp]
theorem ofFinite_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ofFinite (finiteUnitsSingle v a) = finiteEmbedding v a :=
  Units.ext rfl
theorem ofFinite_toFinite_of_toInfinite_eq_one {x : IdeleGroup K} (hx : toInfinite K x = 1) :
    ofFinite (toFinite K x) = x := by
  apply (prodEquiv K).injective
  refine Prod.ext ?_ ?_
  · change toInfinite K (ofFinite (toFinite K x)) = toInfinite K x
    rw [toInfinite_ofFinite, hx]
  · change toFinite K (ofFinite (toFinite K x)) = toFinite K x
    rw [toFinite_ofFinite]
theorem toFractionalIdeal_finiteEmbedding_of_uniformizer {v : HeightOneSpectrum (𝓞 K)}
    {π : (v.adicCompletion K)ˣ} (hπ : Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ)) :
    toFractionalIdeal (finiteEmbedding v π) = primeIdealUnit v := by
  classical
  refine toFractionalIdeal_eq_iff.2 fun w ↦ ?_
  rw [count_primeIdealUnit]
  split_ifs with h
  · subst h
    rw [ord_finiteEmbedding_self, hπ, log_exp, neg_neg]
  · exact ord_finiteEmbedding_of_ne h _
def primeToLevel (𝔪 : Ideal (𝓞 K)) : Subgroup (IdeleGroup K) :=
  (toInfinite K).ker ⊓ ⨅ v : HeightOneSpectrum (𝓞 K), ⨅ (_ : v.asIdeal ∣ 𝔪),
    (unitsLevel v (multiplicity v.asIdeal 𝔪)).comap (finiteProj v)
theorem mem_primeToLevel {𝔪 : Ideal (𝓞 K)} {x : IdeleGroup K} :
    x ∈ primeToLevel 𝔪 ↔ toInfinite K x = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪 →
      finiteProj v x ∈ unitsLevel v (multiplicity v.asIdeal 𝔪) := by
  simp only [primeToLevel, Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_iInf,
    Subgroup.mem_comap]
theorem finiteEmbedding_mem_primeToLevel {𝔪 : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪) (a : (v.adicCompletion K)ˣ) : finiteEmbedding v a ∈ primeToLevel 𝔪 := by
  refine mem_primeToLevel.2 ⟨toInfinite_finiteEmbedding v a, fun w hw ↦ ?_⟩
  have hwv : w ≠ v := by
    rintro rfl
    exact hv hw
  rw [finiteProj_finiteEmbedding_of_ne hwv]
  exact one_mem _
theorem exists_mem_primeToLevel {𝔪 : Ideal (𝓞 K)} {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hI : I ∈ idealsPrimeTo 𝔪) : ∃ x ∈ primeToLevel 𝔪, toFractionalIdeal x = I := by
  have key : ∀ v : HeightOneSpectrum (𝓞 K), primeIdealUnit v ^ count K v
      (I : FractionalIdeal (𝓞 K)⁰ K) ∈ (primeToLevel 𝔪).map toFractionalIdeal := by
    intro v
    by_cases hv : v.asIdeal ∣ 𝔪
    · rw [hI v hv, zpow_zero]
      exact one_mem _
    · obtain ⟨π, hπ⟩ := exists_uniformizer v
      exact zpow_mem (Subgroup.mem_map.2 ⟨finiteEmbedding v π, finiteEmbedding_mem_primeToLevel hv π,
        toFractionalIdeal_finiteEmbedding_of_uniformizer hπ⟩) _
  have h : I ∈ (primeToLevel 𝔪).map toFractionalIdeal := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    exact finprod_induction (· ∈ (primeToLevel 𝔪).map toFractionalIdeal) (one_mem _)
      (fun _ _ ↦ mul_mem) key
  obtain ⟨x, hx, hxI⟩ := h
  exact ⟨x, hx, hxI⟩
theorem mem_map_idealLevel_of_mem_primeToLevel {𝔪 : Ideal (𝓞 K)} {x : IdeleGroup K}
    (hx : x ∈ primeToLevel 𝔪) (h1 : toFractionalIdeal x = 1) :
    x ∈ (idealLevel 𝔪).map ofFinite := by
  obtain ⟨hinf, hfin⟩ := mem_primeToLevel.1 hx
  refine ⟨toFinite K x, mem_finiteLevel.2 fun v ↦ ?_, ofFinite_toFinite_of_toInfinite_eq_one hinf⟩
  rw [finiteComponent_toFinite]
  by_cases hv : v.asIdeal ∣ 𝔪
  · exact hfin v hv
  · have hord : ord v x = 0 := by
      rw [← count_toFractionalIdeal, h1, Units.val_one, count_one]
    change finiteProj v x ∈ unitsLevel v (multiplicity v.asIdeal 𝔪)
    rw [multiplicity_eq_zero.2 hv, unitsLevel_zero, Submonoid.mem_units_iff]
    exact (ord_eq_zero_iff v x).1 hord
end IdeleGroup
namespace HeckeCharacter
open IdeleGroup
variable (χ : HeckeCharacter K)
def toIdele : IdeleGroup K →* Circle :=
  (χ : IdeleClassGroup K →* Circle).comp (IdeleClassGroup.mk K)
theorem continuous_toIdele : Continuous χ.toIdele :=
  χ.continuous.comp (IdeleClassGroup.continuous_mk K)
def localComponent (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →ₜ* Circle where
  toMonoidHom := χ.toIdele.comp (finiteEmbedding v)
  continuous_toFun := χ.continuous_toIdele.comp (continuous_finiteEmbedding v)
def infiniteComponent (w : InfinitePlace K) : (w.Completion)ˣ →ₜ* Circle where
  toMonoidHom := χ.toIdele.comp (infiniteEmbedding w)
  continuous_toFun := χ.continuous_toIdele.comp (continuous_infiniteEmbedding w)
def conductor : Ideal (𝓞 K) :=
  IdeleGroup.conductor (χ.toIdele.comp ofFinite)
theorem conductor_ne_bot : χ.conductor ≠ ⊥ :=
  IdeleGroup.conductor_ne_bot _
theorem map_idealLevel_le_ker_iff {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (idealLevel 𝔪).map ofFinite ≤ χ.toIdele.ker ↔ χ.conductor ∣ 𝔪 :=
  IdeleGroup.map_idealLevel_le_ker_iff Circle.noSmallSubgroups χ.toIdele χ.continuous_toIdele h𝔪
theorem map_idealLevel_conductor_le_ker : (idealLevel χ.conductor).map ofFinite ≤ χ.toIdele.ker :=
  (χ.map_idealLevel_le_ker_iff χ.conductor_ne_bot).2 dvd_rfl
theorem toIdele_eq_of_toFractionalIdeal_eq {x y : IdeleGroup K}
    (hx : x ∈ primeToLevel χ.conductor) (hy : y ∈ primeToLevel χ.conductor)
    (h : toFractionalIdeal x = toFractionalIdeal y) : χ.toIdele x = χ.toIdele y := by
  have hmem : x * y⁻¹ ∈ (idealLevel χ.conductor).map ofFinite :=
    mem_map_idealLevel_of_mem_primeToLevel (mul_mem hx (inv_mem hy))
      (by rw [map_mul, map_inv, h, mul_inv_cancel])
  have h' := χ.map_idealLevel_conductor_le_ker hmem
  rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h'
def idealCharacter : idealsPrimeTo χ.conductor →* Circle where
  toFun I := χ.toIdele (exists_mem_primeToLevel I.2).choose
  map_one' := by
    obtain ⟨hx, hx1⟩ := (exists_mem_primeToLevel (1 : idealsPrimeTo χ.conductor).2).choose_spec
    rw [← map_one χ.toIdele]
    exact χ.toIdele_eq_of_toFractionalIdeal_eq hx (one_mem _) (by rw [hx1, map_one]; rfl)
  map_mul' I J := by
    obtain ⟨hx, hxI⟩ := (exists_mem_primeToLevel I.2).choose_spec
    obtain ⟨hy, hyJ⟩ := (exists_mem_primeToLevel J.2).choose_spec
    obtain ⟨hz, hzIJ⟩ := (exists_mem_primeToLevel (I * J).2).choose_spec
    rw [← map_mul]
    exact χ.toIdele_eq_of_toFractionalIdeal_eq hz (mul_mem hx hy)
      (by rw [hzIJ, map_mul, hxI, hyJ]; rfl)
end HeckeCharacter
end
end GroundTheory.Global


