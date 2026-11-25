-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_LatticeOfLocalisationsHyps
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:36.399745+00:00
-- url     : https://prove2.me/theorems/ca22dec2-e364-4a7f-a3e1-46f8c07c19d7
-- title:
--   Lattice Of Localisations Hyps
-- statement:
--   Definitions and structural lemmas for Lattice Of Localisations Hyps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/LatticeOfLocalisationsHyps.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FibreSpace_inner_equiv_9aa4479f01dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_finrank_eq_7a942c89c61a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianMetric_scale_inner_e0efacf96584
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_lTensor_complex_smul_450d1267bf4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_standardFlag_monotone_8be64143f027
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_standardFlag_saturated_e86c126ee556

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct GroundTheory.Heights₂.Heights
  GroundTheory.Heights₂.Heights.ComplexAt
noncomputable section
section Basic
variable {K : Type*} [Field K] [NumberField K]
def degOf {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) : ℝ :=
  arithDegree h / Module.finrank ℚ K
def deg (M : HermitianBundle K) : ℝ := degOf M.metric
def normAt {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (σ : K →+* ℂ) (x : Fibre σ E) : ℝ :=
  ‖FibreSpace.equiv h σ x‖
def vecNorm {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (σ : K →+* ℂ) (e : E) : ℝ :=
  ‖fibreVec h σ e‖
def fmap (σ : K →+* ℂ) {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [AddCommGroup E']
    [Module (𝓞 K) E'] (f : E' →ₗ[𝓞 K] E) : Fibre σ E' →ₗ[ℂ] Fibre σ E where
  toFun x := f.lTensor (ComplexAt σ) x
  map_add' := map_add _
  map_smul' := lTensor_complex_smul σ f
omit [NumberField K] in
theorem conjMap_fmap (σ : K →+* ℂ) {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [AddCommGroup E'] [Module (𝓞 K) E'] (f : E' →ₗ[𝓞 K] E) (x : Fibre σ E') :
    conjMap σ E (fmap σ f x) = fmap (conjugate σ) f (conjMap σ E' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
omit [NumberField K] in

theorem conjMap_surjective (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E] :
    Function.Surjective (conjMap σ E) := by
  intro u
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul w e =>
    refine ⟨ofComplex σ (starRingEnd ℂ ((ofComplex (conjugate σ)).symm w)) ⊗ₜ e, ?_⟩
    rw [conjMap_tmul, conj_ofComplex, Complex.conj_conj]
    rfl
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
end Basic
section Sub
variable {K : Type*} [Field K] [NumberField K]
def restrictedMetric (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) :
    HermitianMetric K F :=
  M.metric.comap F.subtype F.injective_subtype
def sub (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) : HermitianBundle K :=
  ⟨F, restrictedMetric M F⟩
end Sub
section Quotient
variable {K : Type*} [Field K] [NumberField K]
theorem isTorsionFree_quotient {M : HermitianBundle K} {F : Submodule (𝓞 K) M.carrier}
    (hF : M.Saturated F) : Module.IsTorsionFree (𝓞 K) (M.carrier ⧸ F) := by
  refine ⟨fun a ha z w hzw ↦ ?_⟩
  have ha0 : a ≠ 0 := ha.ne_zero
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective F z
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective F w
  change a • Submodule.Quotient.mk x = a • Submodule.Quotient.mk y at hzw
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    ← smul_sub] at hzw
  exact (Submodule.Quotient.eq F).mpr (hF a _ ha0 hzw)
theorem projective_quotient {M : HermitianBundle K} {F : Submodule (𝓞 K) M.carrier}
    (hF : M.Saturated F) : Module.Projective (𝓞 K) (M.carrier ⧸ F) :=
  haveI := isTorsionFree_quotient hF
  projective_of_isTorsionFree _
variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier)
def subImage (σ : K →+* ℂ) : Submodule ℂ (FibreSpace M.metric σ) :=
  LinearMap.range ((FibreSpace.equiv M.metric σ).toLinearMap ∘ₗ fmap σ F.subtype)
def quotMap (σ : K →+* ℂ) : FibreSpace M.metric σ →ₗ[ℂ] Fibre σ (M.carrier ⧸ F) :=
  fmap σ F.mkQ ∘ₗ (FibreSpace.equiv M.metric σ).symm.toLinearMap
theorem quotMap_eq_zero_iff (σ : K →+* ℂ) (x : FibreSpace M.metric σ) :
    quotMap M F σ x = 0 ↔ x ∈ subImage M F σ := by
  have hex := Module.Flat.lTensor_exact (ComplexAt σ) (LinearMap.exact_subtype_mkQ F)
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hex ((FibreSpace.equiv M.metric σ).symm x)).mp hx
    exact ⟨y, by
      change FibreSpace.equiv M.metric σ (F.subtype.lTensor (ComplexAt σ) y) = x
      rw [hy]; rfl⟩
  · rintro ⟨y, rfl⟩
    exact (hex _).mpr ⟨y, rfl⟩
theorem quotMap_surjective (σ : K →+* ℂ) : Function.Surjective (quotMap M F σ) := by
  intro ξ
  obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective (ComplexAt σ) (Submodule.mkQ_surjective F) ξ
  exact ⟨FibreSpace.equiv M.metric σ y, hy⟩
theorem quotMap_perp_bijective (σ : K →+* ℂ) :
    Function.Bijective (quotMap M F σ ∘ₗ (subImage M F σ)ᗮ.subtype) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have h1 : (x : FibreSpace M.metric σ) ∈ subImage M F σ := (quotMap_eq_zero_iff M F σ _).mp hx
    have h2 : (x : FibreSpace M.metric σ) ∈ subImage M F σ ⊓ (subImage M F σ)ᗮ := ⟨h1, x.2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h2
    exact Subtype.ext h2
  · intro ξ
    obtain ⟨y, rfl⟩ := quotMap_surjective M F σ ξ
    have hy : y ∈ subImage M F σ ⊔ (subImage M F σ)ᗮ := by
      rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; exact Submodule.mem_top
    obtain ⟨w, hw, x, hx, rfl⟩ := Submodule.mem_sup.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    change quotMap M F σ x = quotMap M F σ (w + x)
    rw [map_add, (quotMap_eq_zero_iff M F σ w).mpr hw, zero_add]
def perpEquiv (σ : K →+* ℂ) : (subImage M F σ)ᗮ ≃ₗ[ℂ] Fibre σ (M.carrier ⧸ F) :=
  LinearEquiv.ofBijective _ (quotMap_perp_bijective M F σ)
theorem perpEquiv_apply (σ : K →+* ℂ) (x : (subImage M F σ)ᗮ) :
    perpEquiv M F σ x = quotMap M F σ x := rfl
theorem conj_mem_perp (σ : K →+* ℂ) (x : (subImage M F σ)ᗮ) :
    FibreSpace.equiv M.metric (conjugate σ)
        (conjMap σ M.carrier ((FibreSpace.equiv M.metric σ).symm x)) ∈
      (subImage M F (conjugate σ))ᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨u, rfl⟩
  obtain ⟨u', rfl⟩ := conjMap_surjective σ F u
  change (M.metric.form (conjugate σ)).inner (fmap (conjugate σ) F.subtype (conjMap σ F u'))
    (conjMap σ M.carrier ((FibreSpace.equiv M.metric σ).symm x)) = 0
  rw [← conjMap_fmap, M.metric.form_conj]
  have h0 : inner ℂ (FibreSpace.equiv M.metric σ (fmap σ F.subtype u'))
      (x : FibreSpace M.metric σ) = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (LinearMap.mem_range.mpr ⟨u', rfl⟩ : _ ∈ subImage M F σ) x.2
  change starRingEnd ℂ (inner ℂ (FibreSpace.equiv M.metric σ (fmap σ F.subtype u'))
    (FibreSpace.equiv M.metric σ ((FibreSpace.equiv M.metric σ).symm x))) = 0
  rw [LinearEquiv.apply_symm_apply, h0, map_zero]
theorem perpEquiv_symm_conj (σ : K →+* ℂ) (ξ : Fibre σ (M.carrier ⧸ F)) :
    (perpEquiv M F (conjugate σ)).symm (conjMap σ (M.carrier ⧸ F) ξ) =
      ⟨_, conj_mem_perp M F σ ((perpEquiv M F σ).symm ξ)⟩ := by
  apply (perpEquiv M F (conjugate σ)).injective
  rw [LinearEquiv.apply_symm_apply, perpEquiv_apply]
  change conjMap σ (M.carrier ⧸ F) ξ = fmap (conjugate σ) F.mkQ
    (conjMap σ M.carrier ((FibreSpace.equiv M.metric σ).symm ((perpEquiv M F σ).symm ξ)))
  rw [← conjMap_fmap]
  congr 1
  conv_lhs => rw [← LinearEquiv.apply_symm_apply (perpEquiv M F σ) ξ]
  rfl
def quotientMetric (hF : M.Saturated F) :
    @HermitianMetric K _ _ (M.carrier ⧸ F) _ _ _ (projective_quotient hF) := by
  haveI := projective_quotient hF
  exact
    { form := fun σ ↦
        coreOfInjective (perpEquiv M F σ).symm.toLinearMap (perpEquiv M F σ).symm.injective
      form_conj := fun σ ξ η ↦ by
        simp only [coreOfInjective_inner, LinearEquiv.coe_coe, perpEquiv_symm_conj,
          Submodule.coe_inner]
        change (M.metric.form (conjugate σ)).inner (conjMap σ M.carrier _)
          (conjMap σ M.carrier _) = _
        rw [M.metric.form_conj]
        rfl }
def quotient (hF : M.Saturated F) : HermitianBundle K :=
  @HermitianBundle.mk K _ _ (M.carrier ⧸ F) _ _ _ (projective_quotient hF) (quotientMetric M F hF)
end Quotient
section BaseChange
variable {K : Type*} [Field K] [NumberField K] {E : Type*} [Field E] [NumberField E] [Algebra K E]
variable (K) in

abbrev resEmb (τ : E →+* ℂ) : K →+* ℂ := τ.comp (algebraMap K E)
omit [NumberField K] [NumberField E] in
theorem coe_algebraMap_integers (a : 𝓞 K) :
    ((algebraMap (𝓞 K) (𝓞 E) a : 𝓞 E) : E) = algebraMap K E (a : K) := rfl
variable (K) in

def bcScalar (τ : E →+* ℂ) (z : ComplexAt τ) : 𝓞 E →ₗ[𝓞 K] ComplexAt (resEmb K τ) where
  toFun b := ofComplex _ (τ (b : E) * (ofComplex τ).symm z)
  map_add' b b' := by
    change (τ ((b + b' : 𝓞 E) : E) * _ : ℂ) = τ (b : E) * _ + τ (b' : E) * _
    push_cast; rw [map_add, add_mul]
  map_smul' a b := by
    rw [Algebra.smul_def]
    change τ ((algebraMap (𝓞 K) (𝓞 E) a : E) * (b : E)) * _ = τ (algebraMap K E (a : K)) * (τ (b : E) * _)
    rw [coe_algebraMap_integers, map_mul, mul_assoc]
variable (M : HermitianBundle K)
def bcInner (τ : E →+* ℂ) (z : ComplexAt τ) :
    𝓞 E ⊗[𝓞 K] M.carrier →ₗ[𝓞 K] Fibre (resEmb K τ) M.carrier :=
  TensorProduct.map (bcScalar K τ z) LinearMap.id
theorem bcInner_tmul (τ : E →+* ℂ) (z : ComplexAt τ) (b : 𝓞 E) (m : M.carrier) :
    bcInner M τ z (b ⊗ₜ m) = bcScalar K τ z b ⊗ₜ m := rfl
theorem bcInner_add (τ : E →+* ℂ) (z z' : ComplexAt τ) (t : 𝓞 E ⊗[𝓞 K] M.carrier) :
    bcInner M τ (z + z') t = bcInner M τ z t + bcInner M τ z' t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul b m =>
    rw [bcInner_tmul, bcInner_tmul, bcInner_tmul, ← add_tmul]
    congr 1
    change (τ (b : E) * (ofComplex τ).symm (z + z') : ℂ) =
      τ (b : E) * (ofComplex τ).symm z + τ (b : E) * (ofComplex τ).symm z'
    rw [map_add, mul_add]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel
def bcAdd (τ : E →+* ℂ) : ComplexAt τ →+ (𝓞 E ⊗[𝓞 K] M.carrier →+ Fibre (resEmb K τ) M.carrier) :=
  AddMonoidHom.mk' (fun z ↦ (bcInner M τ z).toAddMonoidHom)
    (fun z z' ↦ AddMonoidHom.ext fun t ↦ bcInner_add M τ z z' t)
def bcFwdAdd (τ : E →+* ℂ) :
    Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier) →+ Fibre (resEmb K τ) M.carrier :=
  TensorProduct.liftAddHom (bcAdd M τ) fun e z t ↦ by
    change bcInner M τ (e • z) t = bcInner M τ z (e • t)
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | tmul b m =>
      rw [smul_tmul', bcInner_tmul, bcInner_tmul]
      congr 1
      change (τ (b : E) * (ofComplex τ).symm (ofComplex τ (τ (e : E)) * z) : ℂ) =
        τ ((e : E) * (b : E)) * (ofComplex τ).symm z
      rw [map_mul, map_mul, AlgEquiv.symm_apply_apply]; ring
    | add x y hx hy => rw [map_add, hx, hy, smul_add, map_add]
theorem bcFwdAdd_tmul (τ : E →+* ℂ) (z : ComplexAt τ) (t : 𝓞 E ⊗[𝓞 K] M.carrier) :
    bcFwdAdd M τ (z ⊗ₜ t) = bcInner M τ z t := rfl
def bcFwd (τ : E →+* ℂ) :
    Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier) →ₗ[ℂ] Fibre (resEmb K τ) M.carrier where
  toFun := bcFwdAdd M τ
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z x =>
      rw [smul_tmul', bcFwdAdd_tmul, bcFwdAdd_tmul, RingHom.id_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul b m =>
        rw [bcInner_tmul, bcInner_tmul, smul_tmul']
        congr 1
        change (τ (b : E) * (ofComplex τ).symm (ofComplex τ c * z) : ℂ) =
          c * (τ (b : E) * (ofComplex τ).symm z)
        rw [map_mul, AlgEquiv.symm_apply_apply]; ring
      | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
theorem bcFwd_tmul_tmul (τ : E →+* ℂ) (z : ComplexAt τ) (b : 𝓞 E) (m : M.carrier) :
    bcFwd M τ (z ⊗ₜ (b ⊗ₜ m)) = bcScalar K τ z b ⊗ₜ m := rfl
def bcInv (τ : E →+* ℂ) :
    Fibre (resEmb K τ) M.carrier →+ Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun w ↦ AddMonoidHom.mk'
        (fun m ↦ ((ofComplex τ ((ofComplex (resEmb K τ)).symm w)) ⊗ₜ[𝓞 E]
          ((1 : 𝓞 E) ⊗ₜ[𝓞 K] m) : Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier)))
        (fun m m' ↦ by simp only [tmul_add]))
      (fun w w' ↦ AddMonoidHom.ext fun m ↦ by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_tmul]))
    fun a w m ↦ by
      simp only [AddMonoidHom.mk'_apply]
      have h1 : (ofComplex τ ((ofComplex (resEmb K τ)).symm (a • w)) : ComplexAt τ) =
          (algebraMap (𝓞 K) (𝓞 E) a) • ofComplex τ ((ofComplex (resEmb K τ)).symm w) := rfl
      rw [h1, TensorProduct.smul_tmul]
      congr 1
      rw [smul_tmul', ← TensorProduct.smul_tmul, algebraMap_smul]
theorem bcInv_bcFwd (τ : E →+* ℂ) (t : Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier)) :
    bcInv M τ (bcFwd M τ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z x =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero]
    | tmul b m =>
      rw [bcFwd_tmul_tmul]
      change (ofComplex τ (τ (b : E) * (ofComplex τ).symm z)) ⊗ₜ[𝓞 E] ((1 : 𝓞 E) ⊗ₜ[𝓞 K] m) = _
      have h1 : (ofComplex τ (τ (b : E) * (ofComplex τ).symm z) : ComplexAt τ) = b • z := rfl
      rw [h1, TensorProduct.smul_tmul, smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
theorem bcFwd_injective (τ : E →+* ℂ) : Function.Injective (bcFwd M τ) := fun x y h ↦ by
  rw [← bcInv_bcFwd M τ x, ← bcInv_bcFwd M τ y, h]
theorem bcFwd_conj (τ : E →+* ℂ) (x : Fibre τ (𝓞 E ⊗[𝓞 K] M.carrier)) :
    bcFwd M (conjugate τ) (conjMap τ _ x) = conjMap (resEmb K τ) M.carrier (bcFwd M τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z t =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero]
    | tmul b m =>
      rw [conjMap_tmul, bcFwd_tmul_tmul, bcFwd_tmul_tmul, conjMap_tmul]
      congr 1
      change (starRingEnd ℂ (τ (b : E)) * starRingEnd ℂ ((ofComplex τ).symm z) : ℂ) =
        starRingEnd ℂ (τ (b : E) * (ofComplex τ).symm z)
      rw [map_mul]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]
def baseChangeMetric : HermitianMetric E (𝓞 E ⊗[𝓞 K] M.carrier) where
  form τ := coreOfInjective ((FibreSpace.equiv M.metric (resEmb K τ)).toLinearMap ∘ₗ bcFwd M τ)
    (by rw [LinearMap.coe_comp]
        exact (FibreSpace.equiv M.metric (resEmb K τ)).injective.comp (bcFwd_injective M τ))
  form_conj τ x y := by
    have h := M.metric.form_conj (resEmb K τ) (bcFwd M τ x) (bcFwd M τ y)
    rw [← bcFwd_conj, ← bcFwd_conj] at h
    exact h
variable (E) in

def baseChange : HermitianBundle E := ⟨𝓞 E ⊗[𝓞 K] M.carrier, baseChangeMetric M⟩
end BaseChange
structure HermitianSpace (K : Type*) [Field K] (r : ℕ) where

  form : (K →+* ℂ) → InnerProductSpace.Core ℂ (Fin r → ℂ)

  form_conj : ∀ (σ : K →+* ℂ) (x y : Fin r → ℂ),
    (form (conjugate σ)).inner (star x) (star y) = starRingEnd ℂ ((form σ).inner x y)
section Space
variable {K : Type*} [Field K] [NumberField K]
theorem tmul_smul_field (σ : K →+* ℂ) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (z : ComplexAt σ) (c : K) (x : V) :
    z ⊗ₜ[𝓞 K] (c • x) = (ofComplex σ (σ c) * z) ⊗ₜ[𝓞 K] x := by
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) c
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hσd : σ (algebraMap (𝓞 K) K d) ≠ 0 := (map_ne_zero σ).mpr hd0
  set w : ComplexAt σ := ofComplex σ ((ofComplex σ).symm z / σ (algebraMap (𝓞 K) K d)) with hw
  have hz : z = d • w := by
    rw [smul_def]
    change (ofComplex σ).symm z = σ (algebraMap (𝓞 K) K d) * ((ofComplex σ).symm z / σ (algebraMap (𝓞 K) K d))
    field_simp
  have hx : d • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) • x) = a • x := by
    rw [← smul_assoc, Algebra.smul_def, mul_div_cancel₀ _ hd0, algebraMap_smul]
  rw [hz, TensorProduct.smul_tmul, hx, ← TensorProduct.smul_tmul]
  congr 1
  rw [smul_def, hw]
  change σ (algebraMap (𝓞 K) K a) * ((ofComplex σ).symm z / σ (algebraMap (𝓞 K) K d)) =
    σ (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) * (ofComplex σ).symm (d • w)
  rw [← hz, map_div₀]
  field_simp
def fieldCoordO (σ : K →+* ℂ) : Fibre σ K →ₗ[𝓞 K] ComplexAt σ :=
  TensorProduct.lift (LinearMap.mk₂ (𝓞 K) (fun z c ↦ ofComplex σ (σ c) * z)
    (fun z z' c ↦ mul_add _ _ _)
    (fun a z c ↦ by
      change ofComplex σ (σ c) * (ofComplex σ (σ (a : K)) * z) =
        ofComplex σ (σ (a : K)) * (ofComplex σ (σ c) * z)
      ring)
    (fun z c c' ↦ by rw [map_add, map_add, add_mul])
    (fun a z c ↦ by
      change ofComplex σ (σ ((a : K) * c)) * z = ofComplex σ (σ (a : K)) * (ofComplex σ (σ c) * z)
      rw [map_mul, map_mul, mul_assoc]))
def fieldCoord (σ : K →+* ℂ) : Fibre σ K →ₗ[ℂ] ℂ where
  toFun t := (ofComplex σ).symm (fieldCoordO σ t)
  map_add' s t := by rw [map_add, map_add]
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z a =>
      rw [smul_tmul', RingHom.id_apply, smul_eq_mul]
      change (ofComplex σ).symm (ofComplex σ (σ a) * (ofComplex σ c * z)) =
        c * (ofComplex σ).symm (ofComplex σ (σ a) * z)
      simp only [map_mul, AlgEquiv.symm_apply_apply]; ring
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
variable (r : ℕ)
def coordMap (σ : K →+* ℂ) : Fibre σ (Fin r → K) →ₗ[ℂ] (Fin r → ℂ) :=
  LinearMap.pi fun i ↦ fieldCoord σ ∘ₗ fmap σ (LinearMap.proj i)
variable {r}
theorem coordMap_tmul (σ : K →+* ℂ) (z : ComplexAt σ) (v : Fin r → K) (i : Fin r) :
    coordMap r σ (z ⊗ₜ v) i = σ (v i) * (ofComplex σ).symm z := by
  change (ofComplex σ).symm (ofComplex σ (σ (v i)) * z) = _
  rw [map_mul, AlgEquiv.symm_apply_apply]
def coordInv (σ : K →+* ℂ) (w : Fin r → ℂ) : Fibre σ (Fin r → K) :=
  ∑ i, ofComplex σ (w i) ⊗ₜ[𝓞 K] (Pi.single i (1 : K) : Fin r → K)
theorem coordInv_coordMap (σ : K →+* ℂ) (t : Fibre σ (Fin r → K)) :
    coordInv σ (coordMap r σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | tmul z v =>
    simp only [coordInv, coordMap_tmul]
    have h : ∀ i, ofComplex σ (σ (v i) * (ofComplex σ).symm z) ⊗ₜ[𝓞 K]
        (Pi.single i (1 : K) : Fin r → K) = z ⊗ₜ[𝓞 K] (v i • (Pi.single i (1 : K) : Fin r → K)) := by
      intro i
      rw [tmul_smul_field, map_mul, AlgEquiv.apply_symm_apply]
    simp only [h, ← tmul_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  | add x y hx hy =>
    rw [map_add]
    simp only [coordInv, Pi.add_apply, map_add, add_tmul, Finset.sum_add_distrib] at hx hy ⊢
    rw [hx, hy]
theorem coordMap_injective (σ : K →+* ℂ) : Function.Injective (coordMap r σ) := fun s t h ↦ by
  rw [← coordInv_coordMap σ s, ← coordInv_coordMap σ t, h]
def latticeMap (σ : K →+* ℂ) (L : Submodule (𝓞 K) (Fin r → K)) : Fibre σ L →ₗ[ℂ] (Fin r → ℂ) :=
  coordMap r σ ∘ₗ fmap σ L.subtype
theorem latticeMap_injective (σ : K →+* ℂ) (L : Submodule (𝓞 K) (Fin r → K)) :
    Function.Injective (latticeMap σ L) := by
  rw [latticeMap, LinearMap.coe_comp]
  exact (coordMap_injective σ).comp
    (Module.Flat.lTensor_preserves_injective_linearMap L.subtype L.injective_subtype)
theorem latticeMap_conj (σ : K →+* ℂ) (L : Submodule (𝓞 K) (Fin r → K)) (x : Fibre σ L) :
    latticeMap (conjugate σ) L (conjMap σ L x) = star (latticeMap σ L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | tmul z l =>
    ext i
    rw [conjMap_tmul]
    change coordMap r (conjugate σ) (conj σ z ⊗ₜ (l : Fin r → K)) i =
      starRingEnd ℂ (coordMap r σ (z ⊗ₜ (l : Fin r → K)) i)
    rw [coordMap_tmul, coordMap_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]
def IsLattice (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin r → K)) = ⊤
omit [NumberField K] in
theorem finite_of_fg {L : Submodule (𝓞 K) (Fin r → K)} (hL : L.FG) : Module.Finite (𝓞 K) L :=
  Module.Finite.iff_fg.mpr hL
theorem projective_of_fg {L : Submodule (𝓞 K) (Fin r → K)} (hL : L.FG) :
    Module.Projective (𝓞 K) L :=
  haveI := finite_of_fg hL
  projective_of_isTorsionFree L
def HermitianSpace.latticeMetric (H : HermitianSpace K r) (L : Submodule (𝓞 K) (Fin r → K))
    (hL : L.FG) : @HermitianMetric K _ _ L _ _ (finite_of_fg hL) (projective_of_fg hL) :=
  @HermitianMetric.mk K _ _ L _ _ (finite_of_fg hL) (projective_of_fg hL)
    (fun σ ↦ coreComap (H.form σ) (latticeMap σ L) (latticeMap_injective σ L))
    (fun σ x y ↦ by
      rw [coreComap_inner, coreComap_inner, latticeMap_conj, latticeMap_conj, H.form_conj])
def HermitianSpace.lattice (H : HermitianSpace K r) (L : Submodule (𝓞 K) (Fin r → K))
    (hL : L.FG) : HermitianBundle K :=
  @HermitianBundle.mk K _ _ L _ _ (finite_of_fg hL) (projective_of_fg hL) (H.latticeMetric L hL)
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
open IsDedekindDomain.HeightOneSpectrum in

def locVec (x : Fin r → K) : Fin r → v.adicCompletion K :=
  fun i ↦ algebraMap K (v.adicCompletion K) (x i)
def localLattice (L : Submodule (𝓞 K) (Fin r → K)) :
    Submodule (v.adicCompletionIntegers K) (Fin r → v.adicCompletion K) :=
  Submodule.span _ (locVec v '' (L : Set (Fin r → K)))
def IsLocalLattice (N : Submodule (v.adicCompletionIntegers K) (Fin r → v.adicCompletion K)) :
    Prop :=
  N.FG ∧ Submodule.span (v.adicCompletion K) (N : Set (Fin r → v.adicCompletion K)) = ⊤
theorem locVec_smul (a : 𝓞 K) (x : Fin r → K) :
    locVec v (a • x) = (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) • locVec v x := by
  funext i
  change algebraMap K _ ((a : K) * x i) =
    ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) :
      v.adicCompletion K) * algebraMap K _ (x i)
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, map_mul]
  rfl
theorem locVec_zero : locVec v (0 : Fin r → K) = 0 := by funext i; simp [locVec]
theorem locVec_add (x y : Fin r → K) : locVec v (x + y) = locVec v x + locVec v y := by
  funext i; simp [locVec]
variable {v} in

def ofLocal (N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    Submodule (v.adicCompletionIntegers K) (Fin r → v.adicCompletion K)) :
    Submodule (𝓞 K) (Fin r → K) where
  carrier := {x | ∀ v, locVec v x ∈ N v}
  add_mem' {x y} hx hy v := by
    rw [locVec_add]
    exact (N v).add_mem (hx v) (hy v)
  zero_mem' v := by
    rw [locVec_zero]
    exact (N v).zero_mem
  smul_mem' a x hx v := by
    rw [locVec_smul]
    exact (N v).smul_mem _ (hx v)
def glMap (g : Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)) :
    (Fin r → v.adicCompletion K) →ₗ[v.adicCompletionIntegers K] (Fin r → v.adicCompletion K) :=
  (Matrix.toLin' (g : Matrix (Fin r) (Fin r) (v.adicCompletion K))).restrictScalars _
end Space
section Chain
variable {K : Type*} [Field K] [NumberField K]
theorem saturated_comap {M : HermitianBundle K} {F : Submodule (𝓞 K) M.carrier}
    (hF : M.Saturated F) (G : Submodule (𝓞 K) M.carrier) :
    (sub M G).Saturated (F.comap G.subtype) := fun a x ha hx ↦ hF a (G.subtype x) ha hx
def chainStep {M : HermitianBundle K} {k : ℕ} (C : Fin (k + 1) → Submodule (𝓞 K) M.carrier)
    (a : Fin k) : Submodule (𝓞 K) (sub M (C a.castSucc)).carrier :=
  (C a.succ).comap (C a.castSucc).subtype
end Chain
universe u v w
def BaseChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (E : Type w) [Field E] [NumberField E] [Algebra K E],
    deg (baseChange E M) = deg M
def Sublattice.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier),
    Module.finrank (𝓞 K) F = Module.finrank (𝓞 K) M.carrier →
    deg M = deg (sub M F) + Real.log (Nat.card (M.carrier ⧸ F)) / Module.finrank ℚ K ∧
      deg (sub M F) ≤ deg M
def LatticeOfLocalisations.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (r : ℕ),
    (∀ (M₁ : Submodule (𝓞 K) (Fin r → K)), IsLattice M₁ →
      ∀ (N : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          Submodule (v.adicCompletionIntegers K) (Fin r → v.adicCompletion K)),
        (∀ v, IsLocalLattice v (N v)) → {v | N v ≠ localLattice v M₁}.Finite →
        IsLattice (ofLocal N) ∧ ∀ v, localLattice v (ofLocal N) = N v) ∧
    ∀ (L L' : Submodule (𝓞 K) (Fin r → K)), IsLattice L → IsLattice L' →
      (L ≤ L' ↔ ∀ v, localLattice v L ≤ localLattice v L')
def LocalChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (r : ℕ) (H : HermitianSpace K r)
    (M₁ M₂ : Submodule (𝓞 K) (Fin r → K)) (h₁ : IsLattice M₁) (h₂ : IsLattice M₂)
    (g : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K)),
    {v | g v ≠ 1}.Finite →
    (∀ v, localLattice v M₂ = (localLattice v M₁).map (glMap v (g v))) →
    deg (H.lattice M₂ h₂.1) = deg (H.lattice M₁ h₁.1) +
      (∑ᶠ v, Real.log ‖(g v : Matrix (Fin r) (Fin r) (v.adicCompletion K)).det‖) /
        Module.finrank ℚ K
def NormComparison.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (E : Type v) [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (h h' : HermitianMetric K E)
    (A : (K →+* ℂ) → ℝ),
    (∀ (σ : K →+* ℂ) (x : Fibre σ E), normAt h' σ x ≤ A σ * normAt h σ x) →
    degOf h - Module.finrank (𝓞 K) E * ∑ σ : K →+* ℂ, Real.log (A σ) / Module.finrank ℚ K ≤
      degOf h'
def DiagonalChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (E : Type v) [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (h h' : HermitianMetric K E)
    (T : ∀ σ : K →+* ℂ, Fibre σ E →ₗ[ℂ] Fibre σ E),
    (∀ (σ : K →+* ℂ) (x : Fibre σ E), normAt h' σ x = normAt h σ (T σ x)) →
    (∀ σ : K →+* ℂ, ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (FibreSpace h σ)) (c : Fin n → ℂ),
      ∀ i, FibreSpace.equiv h σ (T σ ((FibreSpace.equiv h σ).symm (b i))) = c i • b i) →
    degOf h' = degOf h - ∑ σ : K →+* ℂ, Real.log ‖LinearMap.det (T σ)‖ / Module.finrank ℚ K
def ExactSequence.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F),
    deg M = deg (sub M F) + deg (quotient M F hF)
def QuotientNorm.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F) (σ : K →+* ℂ) (x : Fibre σ M.carrier),
    normAt (quotient M F hF).metric σ (fmap σ F.mkQ x) =
      ⨅ y : {y : Fibre σ M.carrier // fmap σ F.mkQ y = fmap σ F.mkQ x}, normAt M.metric σ y
def ChainSum.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K) (k : ℕ)
    (C : Fin (k + 1) → Submodule (𝓞 K) M.carrier) (_ : C 0 = ⊤) (_ : Antitone C)
    (hC : ∀ a, M.Saturated (C a)),
    deg M = deg (sub M (C (Fin.last k))) +
      ∑ a : Fin k, deg (quotient (sub M (C a.castSucc)) (chainStep C a)
        (saturated_comap (hC a.succ) (C a.castSucc)))
def Hadamard.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (x : Fin (Module.finrank (𝓞 K) M.carrier) → M.carrier) (La : ℝ),
    LinearIndependent (𝓞 K) x → (∀ i (σ : K →+* ℂ), vecNorm M.metric σ (x i) ≤ La) →
    -(Module.finrank (𝓞 K) M.carrier : ℝ) * Real.log La ≤ deg M
def HadamardQuotient.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F) (S : Set M.carrier) (La : ℝ),
    Module.finrank (𝓞 K) (Submodule.span (𝓞 K) S) = Module.finrank (𝓞 K) M.carrier →
    (∀ x ∈ S, ∀ σ : K →+* ℂ, vecNorm M.metric σ x ≤ La) →
    -(Module.finrank (𝓞 K) (M.carrier ⧸ F) : ℝ) * Real.log La ≤ deg (quotient M F hF)
def HadamardMean.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (x : Fin (Module.finrank (𝓞 K) M.carrier) → M.carrier),
    LinearIndependent (𝓞 K) x →
    -(∑ i, ∑ σ : K →+* ℂ, Real.log (vecNorm M.metric σ (x i)) / Module.finrank ℚ K) ≤ deg M
def HadamardMeanQuotient.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F) (ι : Type w) [Fintype ι] (x : ι → M.carrier),
    Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range x)) = Module.finrank (𝓞 K) M.carrier →
    (∃ J : Finset ι, LinearIndependent (𝓞 K) (fun j : J ↦ F.mkQ (x j)) ∧
      J.card = Module.finrank (𝓞 K) (M.carrier ⧸ F)) ∧
    ∀ J : Finset ι, LinearIndependent (𝓞 K) (fun j : J ↦ F.mkQ (x j)) →
      J.card = Module.finrank (𝓞 K) (M.carrier ⧸ F) →
      -(∑ j ∈ J, ∑ σ : K →+* ℂ, Real.log (vecNorm M.metric σ (x j)) / Module.finrank ℚ K) ≤
        deg (quotient M F hF)
section Examples
variable (K : Type*) [Field K] [NumberField K]
abbrev firstLine : Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier := standardFlag K 1
theorem firstLine_saturated : (HermitianBundle.standard K 2).Saturated (firstLine K) :=
  standardFlag_saturated 1
def exampleSub : HermitianBundle K := sub (HermitianBundle.standard K 2) (firstLine K)
def exampleQuotient : HermitianBundle K :=
  quotient (HermitianBundle.standard K 2) (firstLine K) (firstLine_saturated K)
def exampleBaseChange : HermitianBundle GaussianField := baseChange GaussianField (ratStandard 2)
example : HermitianBundle ℚ := exampleSub ℚ
example : HermitianBundle GaussianField := exampleSub GaussianField
example : HermitianBundle ℚ := exampleQuotient ℚ
example : HermitianBundle GaussianField := exampleQuotient GaussianField
example : Algebra ℚ GaussianField := inferInstance
def stdVec (i : Fin 2) : (HermitianBundle.standard K 2).carrier := Pi.single i 1
theorem range_stdVec :
    Set.range (stdVec K) = Set.range (Pi.basisFun (𝓞 K) (Fin 2)) := by
  congr 1; funext i; rw [Pi.basisFun_apply]; rfl
theorem span_stdVec : Submodule.span (𝓞 K) (Set.range (stdVec K)) = ⊤ := by
  rw [range_stdVec]; exact (Pi.basisFun (𝓞 K) (Fin 2)).span_eq
theorem linearIndependent_stdVec : LinearIndependent (𝓞 K) (stdVec K) := by
  have h := (Pi.basisFun (𝓞 K) (Fin 2)).linearIndependent
  rwa [show ⇑(Pi.basisFun (𝓞 K) (Fin 2)) = stdVec K from
    funext fun i ↦ by rw [Pi.basisFun_apply]; rfl] at h
theorem vecNorm_stdVec (σ : K →+* ℂ) (i : Fin 2) :
    vecNorm (HermitianBundle.standard K 2).metric σ (stdVec K i) = 1 := by
  refine (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp ?_
  rw [one_pow, norm_fibreVec_sq]
  change (((HermitianMetric.standard K (Fin 2)).form σ).inner (1 ⊗ₜ Pi.single i 1)
    (1 ⊗ₜ Pi.single i 1)).re = 1
  rw [HermitianMetric.standard_inner_single]; rfl
theorem finrank_standard_two : Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier = 2 :=
  Module.finrank_fin_fun _
def stdFamily : Fin (Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier) →
    (HermitianBundle.standard K 2).carrier :=
  fun i ↦ stdVec K (Fin.cast (finrank_standard_two K) i)
theorem linearIndependent_stdFamily : LinearIndependent (𝓞 K) (stdFamily K) :=
  (linearIndependent_stdVec K).comp _ (Fin.cast_injective _)
def twiceLattice : Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  LinearMap.range ((2 : 𝓞 K) • LinearMap.id)
theorem twiceLattice_rank : Module.finrank (𝓞 K) (twiceLattice K) =
    Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier := by
  have hinj : Function.Injective
      ((2 : 𝓞 K) • LinearMap.id : (HermitianBundle.standard K 2).carrier →ₗ[𝓞 K] _) := by
    intro x y hxy
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
    exact smul_right_injective _ two_ne_zero hxy
  exact (LinearEquiv.ofInjective _ hinj).finrank_eq.symm
theorem normAt_scale {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c) (σ : K →+* ℂ)
    (x : Fibre σ E) : normAt (h.scale c hc) σ x = c * normAt h σ x := by
  refine (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hc.le (norm_nonneg _))).mp ?_
  show ‖FibreSpace.equiv (h.scale c hc) σ x‖ ^ 2 = (c * ‖FibreSpace.equiv h σ x‖) ^ 2
  rw [mul_pow, @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ,
    FibreSpace.inner_equiv, FibreSpace.inner_equiv, HermitianMetric.scale_inner]
  exact Complex.re_ofReal_mul _ _
theorem normComparison_hyps {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) :
    ∀ (σ : K →+* ℂ) (x : Fibre σ E), normAt (h.scale 2 two_pos) σ x ≤ 2 * normAt h σ x :=
  fun σ x ↦ (normAt_scale K h 2 two_pos σ x).le
theorem diagonalChange_hyps {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) :
    (∀ (σ : K →+* ℂ) (x : Fibre σ E),
      normAt (h.scale 2 two_pos) σ x = normAt h σ (((2 : ℂ) • LinearMap.id : Fibre σ E →ₗ[ℂ] _) x)) ∧
    (∀ σ : K →+* ℂ, ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (FibreSpace h σ)) (c : Fin n → ℂ),
      ∀ i, FibreSpace.equiv h σ (((2 : ℂ) • LinearMap.id : Fibre σ E →ₗ[ℂ] _)
        ((FibreSpace.equiv h σ).symm (b i))) = c i • b i) := by
  refine ⟨fun σ x ↦ ?_, fun σ ↦ ⟨_, stdOrthonormalBasis ℂ (FibreSpace h σ), fun _ ↦ 2, fun i ↦ ?_⟩⟩
  · rw [normAt_scale]
    show 2 * ‖FibreSpace.equiv h σ x‖ =
      ‖FibreSpace.equiv h σ (((2 : ℂ) • LinearMap.id : Fibre σ E →ₗ[ℂ] _) x)‖
    rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, norm_smul]
    norm_num
  · rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearEquiv.apply_symm_apply]
def exampleChain : Fin 3 → Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  fun a ↦ standardFlag K a.rev
theorem exampleChain_hyps : exampleChain K 0 = ⊤ ∧ Antitone (exampleChain K) ∧
    ∀ a, (HermitianBundle.standard K 2).Saturated (exampleChain K a) :=
  ⟨rfl, fun _ _ hab ↦ standardFlag_monotone (Fin.rev_le_rev.mpr hab),
    fun _ ↦ standardFlag_saturated _⟩
theorem hadamard_hyps : LinearIndependent (𝓞 K) (stdFamily K) ∧
    ∀ i (σ : K →+* ℂ), vecNorm (HermitianBundle.standard K 2).metric σ (stdFamily K i) ≤ 1 :=
  ⟨linearIndependent_stdFamily K, fun _ σ ↦ (vecNorm_stdVec K σ _).le⟩
theorem hadamardQuotient_hyps :
    Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range (stdVec K))) =
      Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier ∧
    ∀ x ∈ Set.range (stdVec K), ∀ σ : K →+* ℂ,
      vecNorm (HermitianBundle.standard K 2).metric σ x ≤ 1 := by
  refine ⟨by rw [span_stdVec, finrank_top], ?_⟩
  rintro _ ⟨i, rfl⟩ σ
  exact (vecNorm_stdVec K σ i).le
def HermitianSpace.standard (r : ℕ) : HermitianSpace K r where
  form _ := coreOfInjective (WithLp.linearEquiv 2 ℂ (Fin r → ℂ)).symm.toLinearMap
    (WithLp.linearEquiv 2 ℂ (Fin r → ℂ)).symm.injective
  form_conj σ x y := by
    simp only [coreOfInjective_inner, LinearEquiv.coe_coe, PiLp.inner_apply, RCLike.inner_apply,
      map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change star (y i) * starRingEnd ℂ (star (x i)) = starRingEnd ℂ (y i) * x i
    simp
variable (r : ℕ)
def stdLattice : Submodule (𝓞 K) (Fin r → K) :=
  Submodule.span (𝓞 K) (Set.range fun i : Fin r ↦ (Pi.single i (1 : K) : Fin r → K))
omit [NumberField K] in
theorem isLattice_std : IsLattice (stdLattice K r) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), top_unique ?_⟩
  rw [← (Pi.basisFun K (Fin r)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨i, by simp⟩
variable {K r}
theorem locVec_single (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (i : Fin r) :
    locVec v (Pi.single i (1 : K)) = Pi.single i 1 := by
  funext j; by_cases h : j = i
  · subst h; simp [locVec]
  · simp [locVec, h]
theorem localLattice_span (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (S : Set (Fin r → K)) :
    localLattice v (Submodule.span (𝓞 K) S) = Submodule.span _ (locVec v '' S) := by
  apply le_antisymm
  · rw [localLattice, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [locVec_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [locVec_add]; exact add_mem hy hz
    | smul a y _ hy => rw [locVec_smul]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
variable (K r)
theorem isLocalLattice_std (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsLocalLattice v (localLattice v (stdLattice K r)) := by
  refine ⟨?_, top_unique ?_⟩
  · rw [stdLattice, localLattice_span]
    exact Submodule.fg_span ((Set.finite_range _).image _)
  · rw [← (Pi.basisFun (v.adicCompletion K) (Fin r)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨Pi.single i 1, Submodule.subset_span ⟨i, rfl⟩, ?_⟩
    rw [locVec_single]; simp
theorem latticeOfLocalisations_hyps :
    IsLattice (stdLattice K r) ∧ (∀ v, IsLocalLattice v (localLattice v (stdLattice K r))) ∧
      {v | localLattice v (stdLattice K r) ≠ localLattice v (stdLattice K r)}.Finite :=
  ⟨isLattice_std K r, isLocalLattice_std K r, by simp⟩
open Classical in

def signChange (v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Matrix.GeneralLinearGroup (Fin r) (v.adicCompletion K) :=
  if v = v₀ then -1 else 1
theorem localChange_hyps (v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    {v | signChange K r v₀ v ≠ 1}.Finite ∧
    ∀ v, localLattice v (stdLattice K r) =
      (localLattice v (stdLattice K r)).map (glMap v (signChange K r v₀ v)) := by
  refine ⟨(Set.finite_singleton v₀).subset fun v hv ↦ ?_, fun v ↦ ?_⟩
  · by_contra h
    exact hv (by rw [signChange, if_neg (by simpa using h)])
  · by_cases h : v = v₀
    · have : glMap v (signChange K r v₀ v) = -LinearMap.id := by
        rw [signChange, if_pos h]
        refine LinearMap.ext fun x ↦ ?_
        simp only [glMap, LinearMap.restrictScalars_apply, Units.val_neg, Units.val_one,
          Matrix.toLin'_apply, Matrix.neg_mulVec, Matrix.one_mulVec, LinearMap.neg_apply,
          LinearMap.id_apply]
      rw [this, Submodule.map_neg, Submodule.map_id]
    · have : glMap v (signChange K r v₀ v) = LinearMap.id := by
        rw [signChange, if_neg h]
        refine LinearMap.ext fun x ↦ ?_
        simp only [glMap, LinearMap.restrictScalars_apply, Units.val_one, Matrix.toLin'_apply,
          Matrix.one_mulVec, LinearMap.id_apply]
      rw [this, Submodule.map_id]
example : HermitianSpace ℚ 2 := HermitianSpace.standard ℚ 2
example : HermitianSpace GaussianField 2 := HermitianSpace.standard GaussianField 2
example : HermitianBundle ℚ := (HermitianSpace.standard ℚ 2).lattice (stdLattice ℚ 2) (isLattice_std ℚ 2).1
example : HermitianBundle GaussianField :=
  (HermitianSpace.standard GaussianField 2).lattice (stdLattice GaussianField 2)
    (isLattice_std GaussianField 2).1
example := latticeOfLocalisations_hyps ℚ 2
example := latticeOfLocalisations_hyps GaussianField 2
example := localChange_hyps ℚ 2
example := localChange_hyps GaussianField 2
example := twiceLattice_rank ℚ
example := twiceLattice_rank GaussianField
example := normComparison_hyps ℚ (HermitianBundle.standard ℚ 2).metric
example := normComparison_hyps GaussianField (HermitianBundle.standard GaussianField 2).metric
example := diagonalChange_hyps ℚ (HermitianBundle.standard ℚ 2).metric
example := diagonalChange_hyps GaussianField (HermitianBundle.standard GaussianField 2).metric
example := exampleChain_hyps ℚ
example := exampleChain_hyps GaussianField
example := hadamard_hyps ℚ
example := hadamard_hyps GaussianField
example := hadamardQuotient_hyps ℚ
example := hadamardQuotient_hyps GaussianField
example := firstLine_saturated ℚ
example := firstLine_saturated GaussianField
end Examples
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LatticeLemmas


