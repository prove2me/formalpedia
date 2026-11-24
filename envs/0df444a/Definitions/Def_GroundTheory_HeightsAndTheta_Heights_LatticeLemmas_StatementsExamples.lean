-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:14.310317+00:00
-- url     : https://prove2.me/theorems/273a537c-d645-4d58-8f69-4cbaf40594c8
-- title:
--   Statements Examples
-- statement:
--   Definitions and structural lemmas for Statements Examples, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
def embLinear (σ : K →+* ℂ) : K →ₗ[𝓞 K] ComplexAt σ where
  toFun x := ofComplex σ (σ x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    rw [RingHom.id_apply, smul_def, Algebra.smul_def, map_mul, map_mul]
def fieldCoord (σ : K →+* ℂ) : Fibre σ K →ₗ[ℂ] ℂ :=
  (ofComplex σ).symm.toLinearEquiv.toLinearMap ∘ₗ
    ((embLinear σ).liftBaseChange (ComplexAt σ)).restrictScalars ℂ
theorem fieldCoord_tmul (σ : K →+* ℂ) (z : ComplexAt σ) (x : K) :
    fieldCoord σ (z ⊗ₜ x) = (ofComplex σ).symm z * σ x :=
  rfl
theorem eq_fieldCoord_tmul_one (σ : K →+* ℂ) (t : Fibre σ K) :
    t = ofComplex σ (fieldCoord σ t) ⊗ₜ (1 : K) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, zero_tmul]
  | tmul z x =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    have hb' : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have hσb : σ (algebraMap (𝓞 K) K b) ≠ 0 := by rwa [map_ne_zero]
    set w : ComplexAt σ := ofComplex σ ((σ (algebraMap (𝓞 K) K b))⁻¹ * (ofComplex σ).symm z)
    have e1 : z = b • w := by
      rw [smul_def]
      apply (ofComplex σ).symm.injective
      simp only [w, map_mul, AlgEquiv.symm_apply_apply]
      rw [← mul_assoc, mul_inv_cancel₀ hσb, one_mul]
    have e2 : b • (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) = a • (1 : K) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_div_cancel₀ _ hb']
    calc z ⊗ₜ[𝓞 K] (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b)
        = (b • w) ⊗ₜ[𝓞 K] (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) := by rw [← e1]
      _ = w ⊗ₜ[𝓞 K] (a • (1 : K)) := by rw [smul_tmul, e2]
      _ = (a • w) ⊗ₜ[𝓞 K] (1 : K) := (smul_tmul a w 1).symm
      _ = _ := by
        congr 1
        rw [fieldCoord_tmul, smul_def]
        apply (ofComplex σ).symm.injective
        simp only [w, map_mul, AlgEquiv.symm_apply_apply, map_div₀]
        rw [div_eq_mul_inv]
        ring
  | add s t hs ht =>
    rw [map_add, map_add, add_tmul, ← hs, ← ht]
theorem fieldCoord_injective (σ : K →+* ℂ) : Function.Injective (fieldCoord σ) := by
  intro s t h
  rw [eq_fieldCoord_tmul_one σ s, eq_fieldCoord_tmul_one σ t, h]
def fieldStdCoord (σ : K →+* ℂ) (n : ℕ) : Fibre σ (Fin n → K) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i ↦ fieldCoord σ ∘ₗ LinearMap.proj i) ∘ₗ
      ((piRight (𝓞 K) (ComplexAt σ) (ComplexAt σ) fun _ : Fin n ↦ K).restrictScalars ℂ).toLinearMap
theorem fieldStdCoord_apply (σ : K →+* ℂ) (n : ℕ) (x : Fibre σ (Fin n → K)) (i : Fin n) :
    fieldStdCoord σ n x i = fieldCoord σ (piRight (𝓞 K) (ComplexAt σ) (ComplexAt σ)
      (fun _ : Fin n ↦ K) x i) :=
  rfl
theorem fieldStdCoord_injective (σ : K →+* ℂ) (n : ℕ) : Function.Injective (fieldStdCoord σ n) := by
  intro x y h
  apply (piRight (𝓞 K) (ComplexAt σ) (ComplexAt σ) fun _ : Fin n ↦ K).injective
  funext i
  apply fieldCoord_injective σ
  rw [← fieldStdCoord_apply, ← fieldStdCoord_apply, h]
theorem fieldStdCoord_conjMap (σ : K →+* ℂ) (n : ℕ) (x : Fibre σ (Fin n → K)) (i : Fin n) :
    fieldStdCoord (conjugate σ) n (conjMap σ _ x) i = starRingEnd ℂ (fieldStdCoord σ n x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, PiLp.zero_apply]
  | tmul z f =>
    rw [conjMap_tmul, fieldStdCoord_apply, fieldStdCoord_apply, piRight_apply, piRight_apply,
      piRightHom_tmul, piRightHom_tmul, fieldCoord_tmul, fieldCoord_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, PiLp.add_apply, hx, hy, map_add, PiLp.add_apply, map_add]
variable (K) in

def HermitianNorms.standard (n : ℕ) : HermitianNorms K (Fin n → K) where
  form σ := coreOfInjective (fieldStdCoord σ n) (fieldStdCoord_injective σ n)
  form_conj σ x y := by
    simp only [coreOfInjective_inner, PiLp.inner_apply, RCLike.inner_apply, fieldStdCoord_conjMap,
      map_sum, map_mul, Complex.conj_conj]
variable (K) in

def FullLattice.standard (n : ℕ) : FullLattice K (Fin n → K) where
  carrier := Submodule.span (𝓞 K) (Set.range fun i : Fin n ↦ (Pi.single i 1 : Fin n → K))
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq := by
    have e : (Set.range fun i : Fin n ↦ (Pi.single i 1 : Fin n → K)) =
        Set.range (Pi.basisFun K (Fin n)) :=
      congrArg Set.range (funext fun i ↦ (Pi.basisFun_apply K (Fin n) i).symm)
    rw [Submodule.span_span_of_tower, e, (Pi.basisFun K (Fin n)).span_eq]
example : HermitianBundle K := (HermitianNorms.standard K 2).bundle (FullLattice.standard K 2)
section Local
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (v : HeightOneSpectrum (𝓞 K))
end Local
def swapCoord : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) := LinearEquiv.funCongrLeft K K (Equiv.swap 0 1)
def swapAt (v₀ : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K ⊗[K] (Fin 2 → K)) ≃ₗ[v.adicCompletion K]
      (v.adicCompletion K ⊗[K] (Fin 2 → K)) :=
  open Classical in
  if v = v₀ then swapCoord.baseChange K (v.adicCompletion K) _ _ else 1
end
end GroundTheory.Heights₂.Heights


