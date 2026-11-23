-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianTensor
-- name    : GroundTheory_HeightsAndTheta_Heights_HermitianTensor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:10.190863+00:00
-- url     : https://prove2.me/theorems/4fb1f3b4-b66c-498a-b07a-f5be82f5152c
-- title:
--   Hermitian Tensor
-- statement:
--   Definitions and structural lemmas for Hermitian Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HermitianTensor.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K]
section SMul
variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]
theorem fibre_smul_eq (a : ComplexAt σ) (x : Fibre σ E) :
    a • x = (ofComplex σ).symm a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | tmul z e => rw [smul_tmul', smul_tmul', complex_smul_def, smul_eq_mul]; rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]
instance (F : Type*) [AddCommGroup F] [Module (𝓞 K) F] :
    CompatibleSMul ℂ (ComplexAt σ) (Fibre σ E) (Fibre σ F) where
  smul_tmul a x y := by
    rw [fibre_smul_eq, fibre_smul_eq σ F, TensorProduct.smul_tmul]
instance (F : Type*) [AddCommGroup F] [Module (𝓞 K) F] :
    CompatibleSMul (ComplexAt σ) ℂ (Fibre σ E) (Fibre σ F) where
  smul_tmul c x y := by
    rw [show c • x = (ofComplex σ c) • x from (fibre_smul_eq σ E _ x).symm,
      show c • y = (ofComplex σ c) • y from (fibre_smul_eq σ F _ y).symm, TensorProduct.smul_tmul]
end SMul
variable [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
def FibreSpace (_h : HermitianMetric K E) (σ : K →+* ℂ) : Type _ := Fibre σ E
namespace FibreSpace
variable (h : HermitianMetric K E) (σ : K →+* ℂ)
instance : AddCommGroup (FibreSpace h σ) := inferInstanceAs (AddCommGroup (Fibre σ E))
instance : Module ℂ (FibreSpace h σ) := inferInstanceAs (Module ℂ (Fibre σ E))
instance : NormedAddCommGroup (FibreSpace h σ) :=
  letI : InnerProductSpace.Core ℂ (FibreSpace h σ) := h.form σ
  this.toNormedAddCommGroup
instance : InnerProductSpace ℂ (FibreSpace h σ) := InnerProductSpace.ofCore _
def equiv : Fibre σ E ≃ₗ[ℂ] FibreSpace h σ := LinearEquiv.refl ℂ _
end FibreSpace
variable {F : Type*} [AddCommGroup F] [Module (𝓞 K) F] [Module.Finite (𝓞 K) F]
  [Module.Projective (𝓞 K) F]
def tensorCoord (hE : HermitianMetric K E) (hF : HermitianMetric K F) (σ : K →+* ℂ) :
    Fibre σ (E ⊗[𝓞 K] F) ≃ₗ[ℂ] FibreSpace hE σ ⊗[ℂ] FibreSpace hF σ :=
  ((AlgebraTensorModule.distribBaseChange (𝓞 K) (ComplexAt σ) E F).restrictScalars ℂ).trans
    ((equivOfCompatibleSMul ℂ (ComplexAt σ) ℂ (Fibre σ E) (Fibre σ F)).trans
      (TensorProduct.congr (FibreSpace.equiv hE σ) (FibreSpace.equiv hF σ)))
theorem tensorCoord_tmul (hE : HermitianMetric K E) (hF : HermitianMetric K F) (σ : K →+* ℂ)
    (z : ComplexAt σ) (e : E) (f : F) :
    tensorCoord hE hF σ (z ⊗ₜ (e ⊗ₜ f)) =
      FibreSpace.equiv hE σ (z ⊗ₜ e) ⊗ₜ FibreSpace.equiv hF σ (1 ⊗ₜ f) := rfl
variable (hE : HermitianMetric K E) (hF : HermitianMetric K F)
theorem tensorCoord_inner_tmul (σ : K →+* ℂ) (z w : ComplexAt σ) (e e' : E) (f f' : F) :
    inner ℂ (tensorCoord hE hF σ (z ⊗ₜ (e ⊗ₜ f))) (tensorCoord hE hF σ (w ⊗ₜ (e' ⊗ₜ f'))) =
      (hE.form σ).inner (z ⊗ₜ e) (w ⊗ₜ e') * (hF.form σ).inner (1 ⊗ₜ f) (1 ⊗ₜ f') := by
  rw [tensorCoord_tmul, tensorCoord_tmul, TensorProduct.inner_tmul]
  rfl
theorem tensorCoord_inner_conjMap (σ : K →+* ℂ) (x y : Fibre σ (E ⊗[𝓞 K] F)) :
    inner ℂ (tensorCoord hE hF (conjugate σ) (conjMap σ _ x))
        (tensorCoord hE hF (conjugate σ) (conjMap σ _ y)) =
      starRingEnd ℂ (inner ℂ (tensorCoord hE hF σ x) (tensorCoord hE hF σ y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, inner_zero_left]
  | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']
  | tmul z t =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero, inner_zero_left]
    | add t t' ht ht' => simp only [tmul_add, map_add, inner_add_left, ht, ht']
    | tmul e f =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, inner_zero_right]
      | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
      | tmul w s =>
        induction s using TensorProduct.induction_on with
        | zero => simp only [tmul_zero, map_zero, inner_zero_right]
        | add s s' hs hs' => simp only [tmul_add, map_add, inner_add_right, hs, hs']
        | tmul e' f' =>
          rw [conjMap_tmul, conjMap_tmul, tensorCoord_inner_tmul, tensorCoord_inner_tmul, map_mul,
            ← hE.form_conj, ← hF.form_conj, conjMap_tmul, conjMap_tmul, conjMap_tmul,
            conjMap_tmul, map_one]
def HermitianMetric.tensor : HermitianMetric K (E ⊗[𝓞 K] F) where
  form σ := coreOfInjective (tensorCoord hE hF σ).toLinearMap (tensorCoord hE hF σ).injective
  form_conj σ x y := tensorCoord_inner_conjMap hE hF σ x y
def HermitianBundle.tensor (A B : HermitianBundle K) : HermitianBundle K :=
  ⟨A.carrier ⊗[𝓞 K] B.carrier, A.metric.tensor B.metric⟩
example : HermitianBundle GaussianField := (gaussianStandard 2).tensor (gaussianStandard 3)
end
end GroundTheory.Heights₂.Heights


