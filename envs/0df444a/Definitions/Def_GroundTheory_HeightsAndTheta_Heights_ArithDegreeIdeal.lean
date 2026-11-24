-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:20.41962+00:00
-- url     : https://prove2.me/theorems/139bdea6-967b-4548-9916-688b01b338f4
-- title:
--   Arith Degree Ideal
-- statement:
--   Definitions and structural lemmas for Arith Degree Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeIdeal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianMetric_integers_inner_66e5d940cc4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_lTensor_complex_smul_450d1267bf4b

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
theorem projective_of_isTorsionFree (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.IsTorsionFree (𝓞 K) M] : Module.Projective (𝓞 K) M := by
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation
instance submodule_projective {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] (F : Submodule (𝓞 K) E) :
    Module.Projective (𝓞 K) F := by
  have : Module.IsTorsionFree (𝓞 K) F := inferInstance
  exact projective_of_isTorsionFree F
example (I : Ideal (𝓞 K)) : Module.Projective (𝓞 K) I := inferInstance
example (I : Ideal (𝓞 K)) : Module.Finite (𝓞 K) I := inferInstance
section Comap
variable {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup E'] [Module (𝓞 K) E'] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E']
def fibreMap (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) : Fibre σ E' →ₗ[ℂ] Fibre σ E where
  toFun x := f.lTensor (ComplexAt σ) x
  map_add' := map_add _
  map_smul' := lTensor_complex_smul σ f
omit [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E'] in

theorem fibreMap_injective (σ : K →+* ℂ) {f : E' →ₗ[𝓞 K] E} (hf : Function.Injective f) :
    Function.Injective (fibreMap σ f) :=
  Module.Flat.lTensor_preserves_injective_linearMap f hf
omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]
  [Module.Finite (𝓞 K) E'] [Module.Projective (𝓞 K) E'] in

theorem conjMap_fibreMap (σ : K →+* ℂ) (f : E' →ₗ[𝓞 K] E) (x : Fibre σ E') :
    conjMap σ E (fibreMap σ f x) = fibreMap (conjugate σ) f (conjMap σ E' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
def HermitianMetric.comap (h : HermitianMetric K E) (f : E' →ₗ[𝓞 K] E)
    (hf : Function.Injective f) : HermitianMetric K E' where
  form σ := coreComap (h.form σ) (fibreMap σ f) (fibreMap_injective σ hf)
  form_conj σ x y := by
    rw [coreComap_inner, coreComap_inner, ← conjMap_fibreMap, ← conjMap_fibreMap, h.form_conj]
theorem HermitianMetric.comap_inner (h : HermitianMetric K E) (f : E' →ₗ[𝓞 K] E)
    (hf : Function.Injective f) (σ : K →+* ℂ) (x y : Fibre σ E') :
    ((h.comap f hf).form σ).inner x y = (h.form σ).inner (fibreMap σ f x) (fibreMap σ f y) := rfl
end Comap
def HermitianMetric.ideal (I : Ideal (𝓞 K)) : HermitianMetric K I :=
  (HermitianMetric.integers K).comap (Submodule.subtype I) (Submodule.injective_subtype I)
def HermitianBundle.ideal (I : Ideal (𝓞 K)) : HermitianBundle K := ⟨I, HermitianMetric.ideal I⟩
theorem finrank_ideal {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : Module.finrank (𝓞 K) I = 1 := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hle : Module.finrank (𝓞 K) I ≤ 1 := by
    have := Submodule.finrank_le I
    rwa [Module.finrank_self] at this
  have hge : 1 ≤ Module.finrank (𝓞 K) I := by
    have hli : LinearIndependent (𝓞 K) (fun _ : Fin 1 ↦ (⟨a, haI⟩ : I)) :=
      linearIndependent_unique_iff.mpr (by simpa using ha)
    simpa using hli.fintype_card_le_finrank
  omega
theorem arithDegree_ideal {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (HermitianBundle.ideal I).arithDegree = -Real.log (Ideal.absNorm I) := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  set s : I := ⟨a, haI⟩
  have hs : s ≠ 0 := by simpa [s] using ha
  change arithDegree (HermitianMetric.ideal I) = _
  rw [arithDegree_line _ (finrank_ideal hI) hs]

  set T : Ideal (𝓞 K) := Ideal.span {a}
  have hTI : T ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr haI
  have hcard : Nat.card (I ⧸ Submodule.span (𝓞 K) {s}) * Ideal.absNorm I =
      (Algebra.norm ℤ a).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply,
      ← Submodule.card_quotient_mul_card_quotient I T hTI]
    congr 1
    have hker : LinearMap.ker (T.mkQ ∘ₗ I.subtype) = Submodule.span (𝓞 K) {s} := by
      ext x
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, T, Ideal.mem_span_singleton',
        Submodule.mem_span_singleton]
      constructor
      · rintro ⟨c, hc⟩; exact ⟨c, Subtype.ext hc⟩
      · rintro ⟨c, hc⟩; exact ⟨c, congrArg Subtype.val hc⟩
    have hrange : Submodule.map T.mkQ I = LinearMap.range (T.mkQ ∘ₗ I.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [← hker, hrange]
    exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv

  have hnorm : ∀ σ : K →+* ℂ, ‖fibreVec (HermitianMetric.ideal I) σ s‖ = ‖σ (a : K)‖ := by
    intro σ
    have h1 := norm_fibreVec_sq (HermitianMetric.ideal I) σ s
    rw [HermitianMetric.ideal, HermitianMetric.comap_inner] at h1
    erw [HermitianMetric.integers_inner] at h1
    simp only [Submodule.subtype_apply, s, LinearMap.id_apply, map_one, mul_one] at h1
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  simp only [hnorm, sum_log_norm_embedding a ha]
  have hN : (0 : ℝ) < Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hc : (Nat.card (I ⧸ Submodule.span (𝓞 K) {s}) : ℝ) =
      (Algebra.norm ℤ a).natAbs / Ideal.absNorm I := by
    rw [eq_div_iff hN.ne', ← hcard]
    push_cast; ring
  rw [hc, Real.log_div]
  · ring
  · exact_mod_cast Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha)
  · exact hN.ne'
example : (HermitianBundle.ideal (⊤ : Ideal (𝓞 K))).arithDegree = 0 := by
  rw [arithDegree_ideal top_ne_bot, Ideal.absNorm_top, Nat.cast_one, Real.log_one, neg_zero]
end
end GroundTheory.Heights₂.Heights


