-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_BaseChangeDefs
-- name    : GroundTheory_ProfiniteCohomology_RestrictedRamification_BaseChangeDefs
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:04.704255+00:00
-- url     : https://prove2.me/theorems/53a7cbd5-abf9-5403-adaf-1e5cb8f73ce8
-- title:
--   Base Change Defs
-- statement:
--   Definitions and structural lemmas for Base Change Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseChangeDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_sup
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_exists_subset_of_subset_maxUnramifiedOutside
import Theorems.Thm_GroundTheory_ProfCoh_galUnramifiedOutside_isProfinite
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedAt_tower_iff
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open NumberField IsDedekindDomain
universe u
noncomputable section
section Abstract
variable {F L Ω : Type u} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] {E : IntermediateField F Ω} {E' : IntermediateField L Ω}
  (h : E'.restrictScalars F = E)
include h in
theorem mem_of_restrictScalars_eq {x : Ω} (hx : x ∈ E') : x ∈ E := by
  rw [← h]
  exact hx
include h in
theorem mem_of_restrictScalars_eq' {x : Ω} (hx : x ∈ E) : x ∈ E' := by
  rw [← h] at hx
  exact hx
def fieldEquivOfRestrictScalarsEq : E ≃ₐ[F] E' where
  toFun x := ⟨x.1, mem_of_restrictScalars_eq' h x.2⟩
  invFun y := ⟨y.1, mem_of_restrictScalars_eq h y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
@[simp]
theorem coe_fieldEquivOfRestrictScalarsEq (x : E) :
    ((fieldEquivOfRestrictScalarsEq h x : E') : Ω) = x :=
  rfl
@[simp]
theorem coe_fieldEquivOfRestrictScalarsEq_symm (y : E') :
    (((fieldEquivOfRestrictScalarsEq h).symm y : E) : Ω) = y :=
  rfl
def embeddingOfRestrictScalarsEq : L →ₐ[F] E :=
  (IsScalarTower.toAlgHom F L Ω).codRestrict E.toSubalgebra fun x =>
    mem_of_restrictScalars_eq h (E'.algebraMap_mem x)
@[simp]
theorem coe_embeddingOfRestrictScalarsEq (x : L) :
    ((embeddingOfRestrictScalarsEq h x : E) : Ω) = algebraMap L Ω x :=
  rfl
def fixingOfRestrictScalarsEq : Subgroup Gal(E/F) :=
  (embeddingOfRestrictScalarsEq h).fieldRange.fixingSubgroup
theorem mem_fixingOfRestrictScalarsEq_iff (σ : Gal(E/F)) :
    σ ∈ fixingOfRestrictScalarsEq h ↔
      ∀ x : L, σ (embeddingOfRestrictScalarsEq h x) = embeddingOfRestrictScalarsEq h x := by
  change σ ∈ (embeddingOfRestrictScalarsEq h).fieldRange.fixingSubgroup ↔ _
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ x
    exact hσ _ ⟨x, rfl⟩
  · rintro hσ _ ⟨x, rfl⟩
    exact hσ x
def autOfRestrictScalarsEq (σ : Gal(E/F)) (hσ : σ ∈ fixingOfRestrictScalarsEq h) : Gal(E'/L) :=
  AlgEquiv.ofRingEquiv (f := ((fieldEquivOfRestrictScalarsEq h).symm.toRingEquiv.trans
      σ.toRingEquiv).trans (fieldEquivOfRestrictScalarsEq h).toRingEquiv) fun x => by
    change fieldEquivOfRestrictScalarsEq h (σ (embeddingOfRestrictScalarsEq h x)) = _
    rw [(mem_fixingOfRestrictScalarsEq_iff h σ).1 hσ x]
    rfl
def autOfRestrictScalarsEqInv (τ : Gal(E'/L)) : Gal(E/F) :=
  (fieldEquivOfRestrictScalarsEq h).trans ((τ.restrictScalars F).trans
    (fieldEquivOfRestrictScalarsEq h).symm)
theorem autOfRestrictScalarsEqInv_mem (τ : Gal(E'/L)) :
    autOfRestrictScalarsEqInv h τ ∈ fixingOfRestrictScalarsEq h := by
  rw [mem_fixingOfRestrictScalarsEq_iff]
  intro x
  apply Subtype.ext
  change ((τ (algebraMap L E' x) : E') : Ω) = algebraMap L Ω x
  rw [τ.commutes]
  rfl
def fixingMulEquivOfRestrictScalarsEq : fixingOfRestrictScalarsEq h ≃* Gal(E'/L) where
  toFun σ := autOfRestrictScalarsEq h σ.1 σ.2
  invFun τ := ⟨autOfRestrictScalarsEqInv h τ, autOfRestrictScalarsEqInv_mem h τ⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
theorem continuous_coe_fixingMulEquivOfRestrictScalarsEq_symm [Algebra.IsIntegral L E'] :
    Continuous fun τ : Gal(E'/L) =>
      (((fixingMulEquivOfRestrictScalarsEq h).symm τ : fixingOfRestrictScalarsEq h) : Gal(E/F)) := by
  let f : Gal(E'/L) →* Gal(E/F) :=
    (fixingOfRestrictScalarsEq h).subtype.comp (fixingMulEquivOfRestrictScalarsEq h).symm.toMonoidHom
  change Continuous f
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨K, hK, hKs⟩ := (krullTopology_mem_nhds_one_iff F E s).1 hs
  classical
  let b := Module.finBasis F K
  let K' : IntermediateField L E' :=
    IntermediateField.adjoin L (Set.range fun i => fieldEquivOfRestrictScalarsEq h (b i : E))
  have hK' : FiniteDimensional L K' :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  rw [Filter.mem_map]
  refine Filter.mem_of_superset
    ((krullTopology_mem_nhds_one_iff L E' _).2 ⟨K', hK', le_rfl⟩) fun τ hτ => hKs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
  have hb : ∀ i, f τ (b i : E) = b i := fun i => by
    apply Subtype.ext
    change ((τ (fieldEquivOfRestrictScalarsEq h (b i : E)) : E') : Ω) = _
    rw [hτ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)]
    rfl
  intro y hy
  have hy' : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : E) := by
    have := congrArg K.val (b.sum_repr ⟨y, hy⟩)
    rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  rw [hy', map_sum]
  simp only [map_smul, hb]
end Abstract
section Fields
variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
variable [IsGalois F Ω]
theorem exists_le_of_algebraMap_mem (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) :
    ∃ E : IntermediateField F Ω, FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
      ∀ x : L, algebraMap L Ω x ∈ E := by
  classical
  let b := Module.finBasis F L
  obtain ⟨E, hf, hu, hE⟩ := exists_subset_of_subset_maxUnramifiedOutside S
    (Finset.univ.image fun i => algebraMap L Ω (b i)) fun x hx => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact hL (b i)
  refine ⟨E, hf, hu, fun x => ?_⟩
  have hx : algebraMap L Ω x = ∑ i, b.repr x i • algebraMap L Ω (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    change IsScalarTower.toAlgHom F L Ω _ = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [hx]
  exact sum_mem fun i _ => E.smul_mem (hE _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
theorem isUnramifiedIn_of_algebraMap_mem
    (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) :
    ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal := by
  obtain ⟨E, hf, hu, hE⟩ := exists_le_of_algebraMap_mem S hL
  let j : L →ₐ[F] E := (IsScalarTower.toAlgHom F L Ω).codRestrict E.toSubalgebra hE
  let _ : Algebra L E := j.toRingHom.toAlgebra
  have : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have := NumberField.of_module_finite F E
  intro v hv P hP hPv
  obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 E)))
  have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
  have h := ((isUnramifiedAt_tower_iff (F := F) (L := L) Q).1 (hu v hv Q hQ this)).1
  have e : P = Q.under (𝓞 L) := Ideal.over_def Q P
  subst e
  exact h
omit [IsGalois F Ω] in

theorem isUnramifiedOutside_restrictScalars_iff_of_isUnramifiedIn
    (hL : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) (M : IntermediateField L Ω)
    [FiniteDimensional L M] :
    IsUnramifiedOutside S (M.restrictScalars F) ↔ IsUnramifiedOutside (placesOver S) M := by
  have : FiniteDimensional F M := FiniteDimensional.trans F L M
  have := NumberField.of_module_finite L M
  change (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal) ↔ _
  constructor
  · intro hM w hw Q hQ hQw
    have hv0 : w.asIdeal.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) w.ne_bot
    let v : HeightOneSpectrum (𝓞 F) := ⟨w.asIdeal.under (𝓞 F), inferInstance, hv0⟩
    have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
    have hv : v ∉ S := fun hvS => hw ⟨v, hvS, hwv⟩
    have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q w.asIdeal v.asIdeal
    exact ((isUnramifiedAt_tower_iff (F := F) (L := L) Q).1 (hM v hv Q hQ this)).2
  · intro hM v hv Q hQ hQv
    have hP0 : Q.under (𝓞 L) ≠ ⊥ := by
      have : (Q.under (𝓞 L)).LiesOver v.asIdeal :=
        ⟨by rw [Ideal.under_under]; exact hQv.over⟩
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot (Q.under (𝓞 L))
    let w : HeightOneSpectrum (𝓞 L) := ⟨Q.under (𝓞 L), inferInstance, hP0⟩
    have hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by
      change v.asIdeal = (Q.under (𝓞 L)).under (𝓞 F)
      rw [Ideal.under_under]; exact hQv.over⟩
    have hw : w ∉ placesOver S := by
      rintro ⟨u, huS, hwu⟩
      have huv : u = v := HeightOneSpectrum.ext (hwu.over.trans hwv.over.symm)
      exact hv (huv ▸ huS)
    have h1 := hM w hw Q hQ ⟨rfl⟩
    have h2 := hL v hv (Q.under (𝓞 L)) inferInstance hwv
    exact (isUnramifiedAt_tower_iff (F := F) (L := L) Q).2 ⟨h2, h1⟩
theorem restrictScalars_maxUnramifiedOutside_eq
    (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) :
    (maxUnramifiedOutside L Ω (placesOver S)).restrictScalars F = maxUnramifiedOutside F Ω S := by
  have hLu := isUnramifiedIn_of_algebraMap_mem S hL
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois F L Ω
  ext x
  rw [IntermediateField.mem_restrictScalars]
  constructor
  · intro hx
    obtain ⟨M, hf, hu, hxM⟩ := (mem_maxUnramifiedOutside_iff (placesOver S)).1 hx
    have : FiniteDimensional F (M.restrictScalars F) := FiniteDimensional.trans F L M
    exact le_maxUnramifiedOutside S
      ((isUnramifiedOutside_restrictScalars_iff_of_isUnramifiedIn S hLu M).2 hu) hxM
  · intro hx
    obtain ⟨E, hf, hu, hxE⟩ := (mem_maxUnramifiedOutside_iff S).1 hx
    obtain ⟨E₀, hf₀, hu₀, hE₀⟩ := exists_le_of_algebraMap_mem S hL
    let E' : IntermediateField F Ω := E₀ ⊔ E
    have hE' : ∀ y : L, algebraMap L Ω y ∈ E'.toSubfield := fun y =>
      le_sup_left (α := IntermediateField F Ω) (hE₀ y)
    let M : IntermediateField L Ω := E'.toSubfield.toIntermediateField hE'
    have hMF : M.restrictScalars F = E' := by
      ext y
      exact Iff.rfl
    have : FiniteDimensional F M := (inferInstance : FiniteDimensional F E')
    have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite F L M
    have hMu : IsUnramifiedOutside S (M.restrictScalars F) := by
      rw [hMF]
      exact hu₀.sup hu
    exact le_maxUnramifiedOutside (placesOver S)
      ((isUnramifiedOutside_restrictScalars_iff_of_isUnramifiedIn S hLu M).1 hMu)
      (le_sup_right (α := IntermediateField F Ω) hxE)
variable {S} (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)
abbrev gsFieldEquiv :
    maxUnramifiedOutside F Ω S ≃ₐ[F] maxUnramifiedOutside L Ω (placesOver S) :=
  fieldEquivOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL)
abbrev gsEmbedding : L →ₐ[F] maxUnramifiedOutside F Ω S :=
  embeddingOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL)
end Fields
section Groups
variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)
instance finiteDimensional_fieldRange_gsEmbedding :
    FiniteDimensional F (gsEmbedding (S := S) hL).fieldRange := by
  exact LinearEquiv.finiteDimensional (gsEmbedding hL).equivFieldRange.toLinearEquiv
def gsOpenSubgroup : OpenSubgroup (galUnramifiedOutside F Ω S) :=
  ⟨fixingOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL),
    (gsEmbedding (S := S) hL).fieldRange.fixingSubgroup_isOpen⟩
def gsBaseChange : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside F Ω S)) ≃ₜ*
    galUnramifiedOutside L Ω (placesOver S) :=
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois F L Ω
  have : CompactSpace (galUnramifiedOutside L Ω (placesOver S)) :=
    (galUnramifiedOutside_isProfinite (placesOver S)).1
  have : T2Space (galUnramifiedOutside F Ω S) := (galUnramifiedOutside_isProfinite S).2.1
  have hc : Continuous (fixingMulEquivOfRestrictScalarsEq
      (restrictScalars_maxUnramifiedOutside_eq S hL)).symm :=
    (continuous_coe_fixingMulEquivOfRestrictScalarsEq_symm _).subtype_mk _
  let e := hc.homeoOfEquivCompactToT2
    (f := (fixingMulEquivOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL)).symm.toEquiv)
  { fixingMulEquivOfRestrictScalarsEq (restrictScalars_maxUnramifiedOutside_eq S hL) with
    continuous_toFun := e.symm.continuous
    continuous_invFun := hc }
variable {S}
end Groups
end
end GroundTheory.ProfCoh


