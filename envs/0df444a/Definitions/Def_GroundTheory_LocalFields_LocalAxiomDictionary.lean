-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
-- name    : GroundTheory_LocalFields_LocalAxiomDictionary
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:09:18.763874+00:00
-- url     : https://prove2.me/theorems/b13e10c5-a882-4b6d-9c3c-5d7f83feb7ff
-- title:
--   Local Axiom Dictionary
-- statement:
--   Definitions and structural lemmas for Local Axiom Dictionary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_fixedModule
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
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
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.LocalField
open Abstract IntermediateField
section Embeddings
variable (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
end Embeddings
section Fields
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
local notation "G" => Ω ≃ₐ[K] Ω
def fixingOpenSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] : OpenSubgroup G :=
  ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen⟩
@[simp]
theorem coe_fixingOpenSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    (fixingOpenSubgroup L : Subgroup G) = L.fixingSubgroup :=
  rfl
variable [IsGalois K Ω]
theorem fixingSubgroup_fixedField_openSubgroup (U : OpenSubgroup G) :
    (fixedField (U : Subgroup G)).fixingSubgroup = U :=
  InfiniteGalois.fixingSubgroup_fixedField (⟨(U : Subgroup G), U.isClosed⟩ : ClosedSubgroup G)
instance finiteDimensional_fixedField_openSubgroup (U : OpenSubgroup G) :
    FiniteDimensional K (fixedField (U : Subgroup G)) :=
  (InfiniteGalois.isOpen_iff_finite _).1 (by
    rw [fixingSubgroup_fixedField_openSubgroup]
    exact U.isOpen)
theorem mem_iff_forall_fixingSubgroup (L : IntermediateField K Ω) (x : Ω) :
    x ∈ L ↔ ∀ σ ∈ L.fixingSubgroup, σ x = x := by
  conv_lhs => rw [← InfiniteGalois.fixedField_fixingSubgroup L]
  rw [IntermediateField.mem_fixedField_iff]
end Fields
section Units
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
local notation "G" => Ω ≃ₐ[K] Ω
omit [IsGalois K Ω] in

theorem mem_fixedModule_units_iff' (H : Subgroup G) (a : Ωˣ) :
    a ∈ fixedModule Ωˣ H ↔ ∀ σ ∈ H, σ (a : Ω) = a := by
  rw [mem_fixedModule]
  refine forall₂_congr fun σ _ => ?_
  rw [Units.ext_iff]
  rfl
def unitsEquivOfForall {k : Type*} [Field k] [Algebra k Ω] (H : Subgroup G)
    (F : IntermediateField k Ω) (hF : ∀ x : Ω, x ∈ F ↔ ∀ σ ∈ H, σ x = x) :
    fixedModule Ωˣ H ≃* Fˣ where
  toFun a :=
    ⟨⟨((a : Ωˣ) : Ω), (hF _).2 ((mem_fixedModule_units_iff' H a).1 a.2)⟩,
      ⟨((a⁻¹ : fixedModule Ωˣ H) : Ωˣ), (hF _).2 ((mem_fixedModule_units_iff' H _).1 (a⁻¹).2)⟩,
      Subtype.ext (by simp), Subtype.ext (by simp)⟩
  invFun u := ⟨Units.map (algebraMap F Ω : F →* Ω) u,
    (mem_fixedModule_units_iff' H _).2 ((hF _).1 (by simp))⟩
  left_inv a := by
    ext
    rfl
  right_inv u := by
    ext
    rfl
  map_mul' a b := by
    ext
    rfl
omit [IsGalois K Ω] in
@[simp]
theorem coe_unitsEquivOfForall {k : Type*} [Field k] [Algebra k Ω] (H : Subgroup G)
    (F : IntermediateField k Ω) (hF : ∀ x : Ω, x ∈ F ↔ ∀ σ ∈ H, σ x = x) (a : fixedModule Ωˣ H) :
    (((unitsEquivOfForall H F hF a : Fˣ) : F) : Ω) = ((a : Ωˣ) : Ω) :=
  rfl
omit [IsGalois K Ω] in
@[simp]
theorem coe_unitsEquivOfForall_symm {k : Type*} [Field k] [Algebra k Ω] (H : Subgroup G)
    (F : IntermediateField k Ω) (hF : ∀ x : Ω, x ∈ F ↔ ∀ σ ∈ H, σ x = x) (u : Fˣ) :
    ((((unitsEquivOfForall H F hF).symm u : fixedModule Ωˣ H) : Ωˣ) : Ω) = ((u : F) : Ω) :=
  rfl
def fixedModuleUnitsEquiv (L : IntermediateField K Ω) : fixedModule Ωˣ L.fixingSubgroup ≃* Lˣ :=
  unitsEquivOfForall L.fixingSubgroup L (mem_iff_forall_fixingSubgroup L)
@[simp]
theorem coe_fixedModuleUnitsEquiv (L : IntermediateField K Ω)
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    (((fixedModuleUnitsEquiv L a : Lˣ) : L) : Ω) = ((a : Ωˣ) : Ω) :=
  rfl
@[simp]
theorem coe_fixedModuleUnitsEquiv_symm (L : IntermediateField K Ω) (u : Lˣ) :
    ((((fixedModuleUnitsEquiv L).symm u : fixedModule Ωˣ L.fixingSubgroup) : Ωˣ) : Ω) =
      ((u : L) : Ω) :=
  rfl
noncomputable def baseUnitsEquiv : fixedModule Ωˣ (⊤ : Subgroup G) ≃* Kˣ :=
  (MulEquiv.subgroupCongr (by rw [IntermediateField.fixingSubgroup_bot])).trans <|
    (fixedModuleUnitsEquiv (⊥ : IntermediateField K Ω)).trans
      (Units.mapEquiv (IntermediateField.botEquiv K Ω).toMulEquiv)
omit [IsGalois K Ω] in
theorem algebraMap_botEquiv (y : (⊥ : IntermediateField K Ω)) :
    algebraMap K Ω (IntermediateField.botEquiv K Ω y) = (y : Ω) := by
  conv_rhs => rw [← (IntermediateField.botEquiv K Ω).symm_apply_apply y]
  rw [IntermediateField.botEquiv_symm]
  rfl
@[simp]
theorem algebraMap_baseUnitsEquiv (a : fixedModule Ωˣ (⊤ : Subgroup G)) :
    algebraMap K Ω (baseUnitsEquiv a : Kˣ) = ((a : Ωˣ) : Ω) := by
  simp only [baseUnitsEquiv, MulEquiv.trans_apply, Units.coe_mapEquiv]
  exact algebraMap_botEquiv _
end Units
section Norm
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
local notation "G" => Ω ≃ₐ[K] Ω
variable (L : IntermediateField K Ω)
def restrictEmbedding (σ : G) : L →ₐ[K] Ω :=
  (σ : Ω →ₐ[K] Ω).comp L.val
omit [IsGalois K Ω] in
@[simp]
theorem restrictEmbedding_apply (σ : G) (x : L) : restrictEmbedding L σ x = σ x :=
  rfl
omit [IsGalois K Ω] in

theorem restrictEmbedding_eq_iff (σ τ : G) :
    restrictEmbedding L σ = restrictEmbedding L τ ↔ σ⁻¹ * τ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have h' : σ x = τ x := AlgHom.congr_fun h ⟨x, hx⟩
    rw [AlgEquiv.mul_apply, ← h', AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · intro h
    ext x
    have h' := h x x.2
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h'
    exact h'.symm
theorem restrictEmbedding_surjective : Function.Surjective (restrictEmbedding L) := by
  intro τ
  let σ₀ : Ω →ₐ[K] Ω := τ.liftNormal Ω
  refine ⟨AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀), ?_⟩
  ext x
  simp only [restrictEmbedding_apply, AlgEquiv.coe_ofBijective]
  exact τ.liftNormal_commutes Ω x
noncomputable def cosetEmbeddingEquiv :
    (⊤ : Subgroup G) ⧸ L.fixingSubgroup.subgroupOf ⊤ ≃ (L →ₐ[K] Ω) :=
  Equiv.ofBijective
    (Quotient.lift (fun σ : (⊤ : Subgroup G) => restrictEmbedding L σ) fun σ τ h => by
      have h' : σ⁻¹ * τ ∈ L.fixingSubgroup.subgroupOf ⊤ := QuotientGroup.leftRel_apply.mp h
      rw [Subgroup.mem_subgroupOf] at h'
      exact (restrictEmbedding_eq_iff L σ τ).2 (by simpa using h'))
    ⟨fun p q h => by
      induction p using QuotientGroup.induction_on with
      | H σ =>
      induction q using QuotientGroup.induction_on with
      | H τ =>
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using (restrictEmbedding_eq_iff L σ τ).1 h,
     fun τ => by
      obtain ⟨σ, rfl⟩ := restrictEmbedding_surjective L τ
      exact ⟨((⟨σ, Subgroup.mem_top σ⟩ : (⊤ : Subgroup G)) : _ ⧸ _), rfl⟩⟩
@[simp]
theorem cosetEmbeddingEquiv_mk (σ : (⊤ : Subgroup G)) :
    cosetEmbeddingEquiv L (σ : (⊤ : Subgroup G) ⧸ L.fixingSubgroup.subgroupOf ⊤) =
      restrictEmbedding L σ :=
  rfl
variable [FiniteDimensional K L]
end Norm
section Normal
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) {E F : IntermediateField K Ω} (hEF : E ≤ F)
  (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')
instance isSeparable_extendScalars : Algebra.IsSeparable E (extendScalars hEF) :=
  have : Algebra.IsSeparable E Ω := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  Algebra.isSeparable_tower_bot_of_isSeparable E (extendScalars hEF) Ω
include hL in
theorem mem_extendScalars_iff_forall (x : Ω) : x ∈ extendScalars hEF ↔ ∀ σ ∈ L', σ x = x := by
  rw [IntermediateField.mem_extendScalars, mem_iff_forall_fixingSubgroup, hL]
variable [Normal E (extendScalars hEF)]
noncomputable def restrictHom : K' →* (extendScalars hEF ≃ₐ[E] extendScalars hEF) :=
  (AlgEquiv.restrictNormalHom (extendScalars hEF)).comp
    ((IntermediateField.fixingSubgroupEquiv E).toMonoidHom.comp
      (MulEquiv.subgroupCongr hK.symm).toMonoidHom)
omit [IsGalois K Ω] in
theorem coe_restrictHom_apply (σ : K') (x : extendScalars hEF) :
    ((restrictHom K' hEF hK σ x : extendScalars hEF) : Ω) = (σ : Ω ≃ₐ[K] Ω) x :=
  AlgEquiv.restrictNormal_commutes _ _ x
omit [IsGalois K Ω] in
include hL in
theorem ker_restrictHom : (restrictHom K' hEF hK).ker = L'.subgroupOf K' := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hL, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := congrArg
      (fun τ : (extendScalars hEF ≃ₐ[E] extendScalars hEF) =>
        ((τ ⟨x, hx⟩ : extendScalars hEF) : Ω)) h
    simpa [coe_restrictHom_apply] using this
  · intro h
    ext x
    rw [coe_restrictHom_apply]
    exact h x x.2
theorem restrictHom_surjective : Function.Surjective (restrictHom K' hEF hK) := by
  have : Normal E Ω := Normal.tower_top_of_normal K E Ω
  refine (AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := extendScalars hEF) (E := Ω)).comp ?_
  exact (IntermediateField.fixingSubgroupEquiv E).surjective.comp
    (MulEquiv.subgroupCongr hK.symm).surjective
noncomputable def galoisTateModel :
    TateModel Ωˣ K' L' (extendScalars hEF ≃ₐ[E] extendScalars hEF) (extendScalars hEF)ˣ where
  le := hK ▸ hL ▸ IntermediateField.fixingSubgroup_antitone hEF
  hom := restrictHom K' hEF hK
  surjective_hom := restrictHom_surjective K' hEF hK
  ker_hom := ker_restrictHom K' L' hEF hK hL
  equiv := unitsEquivOfForall L' (extendScalars hEF) (mem_extendScalars_iff_forall L' hEF hL)
  coe_equiv_symm_smul σ a := by
    ext
    rw [coe_unitsEquivOfForall_symm]
    change ((restrictHom K' hEF hK σ _ : extendScalars hEF) : Ω) = _
    rw [coe_restrictHom_apply]
    rfl
@[simp]
theorem coe_galoisTateModel_equiv (a : fixedModule Ωˣ L') :
    ((((galoisTateModel K' L' hEF hK hL).equiv a : (extendScalars hEF)ˣ) : extendScalars hEF) : Ω) =
      ((a : Ωˣ) : Ω) :=
  rfl
end Normal
section Relative
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) {E F : IntermediateField K Ω} (hEF : E ≤ F)
  (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')
include hK in
theorem mem_iff_forall_of_fixingSubgroup_eq (x : Ω) : x ∈ E ↔ ∀ σ ∈ K', σ x = x := by
  rw [mem_iff_forall_fixingSubgroup, hK]
def restrictEmbeddingRel (σ : K') : extendScalars hEF →ₐ[E] Ω :=
  ((IntermediateField.fixingSubgroupEquiv E ⟨σ, hK ▸ σ.2⟩ : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω).comp
    (extendScalars hEF).val
omit [IsGalois K Ω] in
@[simp]
theorem restrictEmbeddingRel_apply (σ : K') (x : extendScalars hEF) :
    restrictEmbeddingRel K' hEF hK σ x = (σ : Ω ≃ₐ[K] Ω) x :=
  rfl
omit [IsGalois K Ω] in
include hL in
theorem restrictEmbeddingRel_eq_iff (σ τ : K') :
    restrictEmbeddingRel K' hEF hK σ = restrictEmbeddingRel K' hEF hK τ ↔
      σ⁻¹ * τ ∈ L'.subgroupOf K' := by
  rw [Subgroup.mem_subgroupOf, ← hL, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have h' : (σ : Ω ≃ₐ[K] Ω) x = (τ : Ω ≃ₐ[K] Ω) x := AlgHom.congr_fun h ⟨x, hx⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, ← h', AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_apply]
  · intro h
    ext x
    have h' := h x x.2
    rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_eq] at h'
    exact h'.symm
theorem restrictEmbeddingRel_surjective : Function.Surjective (restrictEmbeddingRel K' hEF hK) := by
  intro τ
  have : Normal E Ω := Normal.tower_top_of_normal K E Ω
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := K) E
  let σ₀ : Ω →ₐ[E] Ω := τ.liftNormal Ω
  let σ' : Ω ≃ₐ[E] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  let σ : E.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv E).symm σ'
  refine ⟨⟨σ, hK ▸ σ.2⟩, ?_⟩
  ext x
  exact τ.liftNormal_commutes Ω x
noncomputable def cosetEmbeddingEquivRel : K' ⧸ L'.subgroupOf K' ≃ (extendScalars hEF →ₐ[E] Ω) :=
  Equiv.ofBijective
    (Quotient.lift (restrictEmbeddingRel K' hEF hK) fun σ τ h =>
      (restrictEmbeddingRel_eq_iff K' L' hEF hK hL σ τ).2 (QuotientGroup.leftRel_apply.mp h))
    ⟨fun p q h => by
      induction p using QuotientGroup.induction_on with
      | H σ =>
      induction q using QuotientGroup.induction_on with
      | H τ =>
        exact QuotientGroup.eq.2 ((restrictEmbeddingRel_eq_iff K' L' hEF hK hL σ τ).1 h),
     fun τ => by
      obtain ⟨σ, rfl⟩ := restrictEmbeddingRel_surjective K' hEF hK τ
      exact ⟨(σ : K' ⧸ L'.subgroupOf K'), rfl⟩⟩
end Relative
end GroundTheory.LocalField


