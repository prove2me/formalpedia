-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsBundles
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsBundles
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:02:36.035375+00:00
-- url     : https://prove2.me/theorems/4576dade-b84e-4cae-b3a6-ceea642e749b
-- title:
--   Statements Bundles
-- statement:
--   Definitions and structural lemmas for Statements Bundles, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsBundles.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace HermitianBundle
def deg (M : HermitianBundle K) : ℝ := M.arithDegree / Module.finrank ℚ K
def normAt (M : HermitianBundle K) (σ : K →+* ℂ) (e : M.carrier) : ℝ := ‖fibreVec M.metric σ e‖
def sub (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) : HermitianBundle K :=
  ⟨F, M.metric.comap F.subtype F.injective_subtype⟩
variable {M : HermitianBundle K} {F : Submodule (𝓞 K) M.carrier}
theorem isTorsionFree_quotient (hF : M.Saturated F) :
    Module.IsTorsionFree (𝓞 K) (M.carrier ⧸ F) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a x hax ↦ ?_
  obtain ⟨x, rfl⟩ := F.mkQ_surjective x
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hax
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hF a x ha hax
theorem quot_projective (hF : M.Saturated F) : Module.Projective (𝓞 K) (M.carrier ⧸ F) :=
  haveI := isTorsionFree_quotient hF
  projective_of_isTorsionFree _
variable (M F)
def quotSection (hF : M.Saturated F) : (M.carrier ⧸ F) →ₗ[𝓞 K] M.carrier :=
  letI := quot_projective hF
  (Module.projective_lifting_property F.mkQ LinearMap.id F.mkQ_surjective).choose
theorem mkQ_comp_quotSection (hF : M.Saturated F) :
    F.mkQ ∘ₗ quotSection M F hF = LinearMap.id :=
  letI := quot_projective hF
  (Module.projective_lifting_property F.mkQ LinearMap.id F.mkQ_surjective).choose_spec
end HermitianBundle
section Fibres
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] in

theorem fibreMap_fibreMap {E' E'' : Type*} [AddCommGroup E'] [Module (𝓞 K) E']
    [AddCommGroup E''] [Module (𝓞 K) E'']
    (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) (g : E'' →ₗ[𝓞 K] E') (x : Fibre σ E'') :
    fibreMap σ f (fibreMap σ g x) = fibreMap σ (f ∘ₗ g) x :=
  (LinearMap.lTensor_comp_apply _ _ _ _).symm
def subFibre (h : HermitianMetric K E) (σ : K →+* ℂ) (F : Submodule (𝓞 K) E) :
    Submodule ℂ (FibreSpace h σ) :=
  LinearMap.range ((FibreSpace.equiv h σ).toLinearMap ∘ₗ fibreMap σ F.subtype)
def conjFS (h : HermitianMetric K E) (σ : K →+* ℂ) (y : FibreSpace h σ) :
    FibreSpace h (conjugate σ) :=
  FibreSpace.equiv h (conjugate σ) (conjMap σ E ((FibreSpace.equiv h σ).symm y))
variable (h : HermitianMetric K E) (σ : K →+* ℂ)
theorem conjFS_inner (y z : FibreSpace h σ) :
    inner ℂ (conjFS h σ y) (conjFS h σ z) = starRingEnd ℂ (inner ℂ y z) :=
  h.form_conj σ _ _
theorem conjFS_sub (y z : FibreSpace h σ) : conjFS h σ (y - z) = conjFS h σ y - conjFS h σ z := by
  simp only [conjFS, map_sub]
theorem conjFS_mem_subFibre (F : Submodule (𝓞 K) E) {y : FibreSpace h σ}
    (hy : y ∈ subFibre h σ F) : conjFS h σ y ∈ subFibre h (conjugate σ) F := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨conjMap σ F z, (conjMap_fibreMap σ F.subtype z).symm⟩
theorem mem_subFibre_conj (F : Submodule (𝓞 K) E) {w : FibreSpace h (conjugate σ)}
    (hw : w ∈ subFibre h (conjugate σ) F) : ∃ y ∈ subFibre h σ F, w = conjFS h σ y := by
  obtain ⟨z, rfl⟩ := hw
  obtain ⟨z', rfl⟩ := conjMap_surjective (σ := σ) (E := F) z
  refine ⟨_, ⟨z', rfl⟩, ?_⟩
  simp only [conjFS, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [conjMap_fibreMap]
theorem starProjection_conjFS (F : Submodule (𝓞 K) E) (y : FibreSpace h σ) :
    (subFibre h (conjugate σ) F)ᗮ.starProjection (conjFS h σ y) =
      conjFS h σ ((subFibre h σ F)ᗮ.starProjection y) := by
  set V := subFibre h σ F
  set V' := subFibre h (conjugate σ) F
  have hp : Vᗮ.starProjection y ∈ Vᗮ := Vᗮ.starProjection_apply_mem y
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [Submodule.mem_orthogonal]
    intro w hw
    obtain ⟨w', hw', rfl⟩ := mem_subFibre_conj h σ F hw
    rw [conjFS_inner, Submodule.inner_right_of_mem_orthogonal hw' hp, map_zero]
  · intro w hw
    rw [← conjFS_sub]
    have hq : y - Vᗮ.starProjection y ∈ V := by
      have e : Vᗮ.starProjection y = y - V.starProjection y := by
        rw [Submodule.starProjection_orthogonal']
        rfl
      rw [e, sub_sub_cancel]
      exact V.starProjection_apply_mem y
    exact Submodule.inner_right_of_mem_orthogonal (conjFS_mem_subFibre h σ F hq) hw
end Fibres
namespace HermitianBundle
variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)
def quotFibreMap (σ : K →+* ℂ) :
    letI := quot_projective hF
    Fibre σ (M.carrier ⧸ F) →ₗ[ℂ] FibreSpace M.metric σ :=
  letI := quot_projective hF
  (subFibre M.metric σ F)ᗮ.starProjection.toLinearMap ∘ₗ
    (FibreSpace.equiv M.metric σ).toLinearMap ∘ₗ fibreMap σ (quotSection M F hF)
theorem quotFibreMap_injective (σ : K →+* ℂ) : Function.Injective (quotFibreMap M F hF σ) := by
  have := quot_projective hF
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  set V := subFibre M.metric σ F
  have h1 : FibreSpace.equiv M.metric σ (fibreMap σ (quotSection M F hF) x) ∈ V := by
    rw [← Submodule.orthogonal_orthogonal V, ← Submodule.starProjection_apply_eq_zero_iff]
    exact hx
  obtain ⟨y, hy⟩ := h1
  have h2 : fibreMap σ F.subtype y = fibreMap σ (quotSection M F hF) x := hy
  have h3 := congrArg (fibreMap σ F.mkQ) h2
  rw [fibreMap_fibreMap, fibreMap_fibreMap, mkQ_comp_quotSection] at h3
  have h4 : F.mkQ ∘ₗ F.subtype = 0 := by
    ext z
    simp
  rw [h4] at h3
  simpa [fibreMap] using h3.symm
def quotMetric :
    letI := quot_projective hF
    HermitianMetric K (M.carrier ⧸ F) :=
  letI := quot_projective hF
  { form := fun σ ↦ coreOfInjective (quotFibreMap M F hF σ) (quotFibreMap_injective M F hF σ)
    form_conj := fun σ x y ↦ by
      simp only [coreOfInjective_inner]
      have key : ∀ z : Fibre σ (M.carrier ⧸ F),
          quotFibreMap M F hF (conjugate σ) (conjMap σ _ z) =
            conjFS M.metric σ (quotFibreMap M F hF σ z) := by
        intro z
        simp only [quotFibreMap, LinearMap.coe_comp, Function.comp_apply,
          ContinuousLinearMap.coe_coe]
        rw [← starProjection_conjFS]
        congr 1
        simp only [conjFS, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        rw [conjMap_fibreMap]
      rw [key, key, conjFS_inner] }
def quot : HermitianBundle K :=
  letI := quot_projective hF
  ⟨M.carrier ⧸ F, quotMetric M F hF⟩
end HermitianBundle
namespace HermitianBundle
variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)
end HermitianBundle
section BaseChange
variable {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
def baseChangeCoord (τ : L →+* ℂ) :
    Fibre τ (𝓞 L ⊗[𝓞 K] E) ≃ₗ[ℂ] Fibre (τ.comp (algebraMap K L)) E :=
  letI : Algebra (𝓞 K) (ComplexAt τ) :=
    (inferInstance : Algebra (𝓞 K) (ComplexAt (τ.comp (algebraMap K L))))
  haveI : IsScalarTower (𝓞 K) (𝓞 L) (ComplexAt τ) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  { (AlgebraTensorModule.cancelBaseChange (𝓞 K) (𝓞 L) (ComplexAt τ) (ComplexAt τ) E).toAddEquiv
    with
    map_smul' := fun c x ↦
      (AlgebraTensorModule.cancelBaseChange (𝓞 K) (𝓞 L) (ComplexAt τ) (ComplexAt τ) E).map_smul
        (ofComplex τ c) x }
omit [NumberField K] [NumberField L] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] in
theorem baseChangeCoord_tmul (τ : L →+* ℂ) (z : ComplexAt τ) (b : 𝓞 L) (e : E) :
    baseChangeCoord τ (z ⊗ₜ (b ⊗ₜ e)) =
      (ofComplex _ (τ (b : L) * (ofComplex τ).symm z) : ComplexAt (τ.comp (algebraMap K L))) ⊗ₜ e :=
  rfl
omit [NumberField K] [NumberField L] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] in
theorem baseChangeCoord_conjMap (τ : L →+* ℂ) (x : Fibre τ (𝓞 L ⊗[𝓞 K] E)) :
    baseChangeCoord (conjugate τ) (conjMap τ _ x) =
      (conjMap (τ.comp (algebraMap K L)) E (baseChangeCoord τ x) :
        Fibre ((conjugate τ).comp (algebraMap K L)) E) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z t =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero]
    | tmul b e =>
      rw [conjMap_tmul, baseChangeCoord_tmul, baseChangeCoord_tmul, conjMap_tmul, conj_ofComplex]
      congr 1
      change ofComplex _ _ = ofComplex _ _
      simp only [map_mul]
      rfl
    | add s t hs ht => simp only [tmul_add, map_add, hs, ht]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
def HermitianMetric.baseChange (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (h : HermitianMetric K E) : HermitianMetric L (𝓞 L ⊗[𝓞 K] E) where
  form τ := coreOfInjective
    ((FibreSpace.equiv h (τ.comp (algebraMap K L))).toLinearMap ∘ₗ (baseChangeCoord τ).toLinearMap)
    ((FibreSpace.equiv h _).injective.comp (baseChangeCoord τ).injective)
  form_conj τ x y := by
    change inner ℂ (FibreSpace.equiv h ((conjugate τ).comp (algebraMap K L))
        (baseChangeCoord (conjugate τ) (conjMap τ _ x)))
        (FibreSpace.equiv h ((conjugate τ).comp (algebraMap K L))
          (baseChangeCoord (conjugate τ) (conjMap τ _ y))) =
      starRingEnd ℂ (inner ℂ (FibreSpace.equiv h (τ.comp (algebraMap K L)) (baseChangeCoord τ x))
        (FibreSpace.equiv h (τ.comp (algebraMap K L)) (baseChangeCoord τ y)))
    rw [baseChangeCoord_conjMap, baseChangeCoord_conjMap]
    exact h.form_conj _ _ _
def HermitianBundle.baseChange (M : HermitianBundle K) (L : Type*) [Field L] [NumberField L]
    [Algebra K L] : HermitianBundle L :=
  ⟨𝓞 L ⊗[𝓞 K] M.carrier, M.metric.baseChange L⟩
end BaseChange
end
end GroundTheory.Heights₂.Heights


