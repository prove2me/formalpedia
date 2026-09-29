-- Prove2me | solution 1 for AutomorphicForm.isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e7c33930-3c4e-50d1-a63d-a6bbe91934eb

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TensorProduct
open scoped TensorProduct.RightActions

section Commutant

variable {R : Type*} [CommRing R]

private theorem exists_eq_smul_one_add_smul_of_commute (g m : Matrix (Fin 2) (Fin 2) R)
    (hg : IsUnit (g.trace ^ 2 - 4 * g.det)) (hm : m * g = g * m) :
    ∃ x y : R, m = x • (1 : Matrix (Fin 2) (Fin 2) R) + y • g := by
  obtain ⟨u, hu⟩ := hg
  have hinv : (↑u⁻¹ : R) * ((g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) = 1 := by
    have h := u.inv_mul
    rwa [hu, Matrix.trace_fin_two, Matrix.det_fin_two] at h
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  refine ⟨m 0 0 - (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)) * g 0 0,
    (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.zero_eta, Fin.mk_one, Fin.isValue, if_true, if_false, mul_one, mul_zero, zero_add, one_ne_zero,
    zero_ne_one]
  · ring
  · linear_combination (-(m 0 1)) * hinv + (-((↑u⁻¹ : R) * (g 0 0 - g 1 1))) * h01 + (2 * (↑u⁻¹ : R) * g 0 1) * h00
  · linear_combination (-(m 1 0)) * hinv + ((↑u⁻¹ : R) * (g 0 0 - g 1 1)) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h00
  · linear_combination (m 0 0 - m 1 1) * hinv + (2 * (↑u⁻¹ : R) * g 0 1) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h01

private theorem commute_of_commute_of_commute {g m m' : Matrix (Fin 2) (Fin 2) R}
    (hg : IsUnit (g.trace ^ 2 - 4 * g.det)) (hm : m * g = g * m) (hm' : m' * g = g * m') : m * m' = m' * m := by
  obtain ⟨x, y, rfl⟩ := exists_eq_smul_one_add_smul_of_commute g m hg hm
  obtain ⟨x', y', rfl⟩ := exists_eq_smul_one_add_smul_of_commute g m' hg hm'
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

end Commutant

section IntegralUnits

variable {A : Type*} [CommRing A]

private theorem mul_mem_integralUnitsSet {S : Type*} [SetLike S A] [SubringClass S A] (R : S) {g h : GL (Fin 2) A}
    (hg : g ∈ AutomorphicForm.integralUnitsSet (R : Set A)) (hh : h ∈ AutomorphicForm.integralUnitsSet (R : Set A)) :
    g * h ∈ AutomorphicForm.integralUnitsSet (R : Set A) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hh.2 i k) (hg.2 k j)

private theorem inv_mem_integralUnitsSet (U : Set A) {g : GL (Fin 2) A} (hg : g ∈ AutomorphicForm.integralUnitsSet U) :
    g⁻¹ ∈ AutomorphicForm.integralUnitsSet U :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

end IntegralUnits

section SectionFunction

open MeasureTheory
open scoped ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem exists_section_of_forall_eq_of_forall_exists (μ : Measure G) [μ.IsMulLeftInvariant] (U : Set G)
    (hUo : IsOpen U) (hUc : IsCompact U) (hμU : μ U = 1) (h1U : (1 : G) ∈ U) (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U)
    (hUinv : ∀ a ∈ U, a⁻¹ ∈ U) (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts τ] [τ.IsOpenPosMeasure] (ψ : G → ℂ)
    (hψ : ∀ t ∈ T, ∀ x : G, ∀ u ∈ U, ψ (t * x * u) = ψ x) (S : Finset G)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s)
    (hcov : ∀ x, ψ x ≠ 0 → ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      (∀ x, ψ x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1) ∧
      ∫ x, ψ x * (w x : ℂ) ∂μ = ∑ s ∈ S, ψ s / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ) := by
  classical
  have hTemb : Topology.IsClosedEmbedding ((↑) : T → G) := hT.isClosedEmbedding_subtypeVal

  have hst : ∀ s : G,
      IsOpen {t : T | s⁻¹ * (t : G) * s ∈ U} ∧ IsCompact {t : T | s⁻¹ * (t : G) * s ∈ U} := by
    intro s
    have hφ : IsCompact ((fun y : G => s⁻¹ * y * s) ⁻¹' U) :=
      ((Homeomorph.mulLeft s⁻¹).trans (Homeomorph.mulRight s)).isCompact_preimage.2 hUc
    exact ⟨hUo.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const),
      hTemb.isCompact_preimage hφ⟩
  have hm : ∀ s : G, 0 < (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal := fun s =>
    ENNReal.toReal_pos ((hst s).1.measure_ne_zero τ ⟨1, by simpa using h1U⟩) (hst s).2.measure_lt_top.ne

  have hA : ∀ s : G, MeasurableSet {y : G | s⁻¹ * y ∈ U} ∧ μ {y : G | s⁻¹ * y ∈ U} = 1 ∧
      IsCompact {y : G | s⁻¹ * y ∈ U} := fun s =>
    ⟨(hUo.preimage (continuous_const.mul continuous_id)).measurableSet, (measure_preimage_mul μ s⁻¹ U).trans hμU,
      (Homeomorph.mulLeft s⁻¹).isCompact_preimage.2 hUc⟩
  have hψA : ∀ s y : G, s⁻¹ * y ∈ U → ψ y = ψ s := fun s y hy => by
    have h := hψ 1 T.one_mem s (s⁻¹ * y) hy
    rwa [one_mul, mul_inv_cancel_left] at h
  refine ⟨fun y => ∑ s ∈ S, {y : G | s⁻¹ * y ∈ U}.indicator
      (fun _ => (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal⁻¹) y, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun y => Finset.sum_nonneg fun s _ =>
      Set.indicator_nonneg (fun _ _ => inv_nonneg.2 ENNReal.toReal_nonneg) _
  · exact Finset.measurable_sum _ fun s _ => measurable_const.indicator (hA s).1
  · refine HasCompactSupport.intro (S.isCompact_biUnion fun s _ => (hA s).2.2) fun y hy => ?_
    exact Finset.sum_eq_zero fun s hs =>
      Set.indicator_of_notMem (fun hys => hy (Set.mem_iUnion₂.2 ⟨s, hs, hys⟩)) _
  ·
    intro x hx
    obtain ⟨s₀, hs₀, t₀, ht₀, u₀, hu₀, rfl⟩ := hcov x hx
    have hsum : ∀ t : T,
        (∑ s ∈ S, {y : G | s⁻¹ * y ∈ U}.indicator (fun _ => (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal⁻¹)
          ((t : G) * (t₀ * s₀ * u₀))) =
        ((fun t' : T => t' * ⟨t₀, ht₀⟩) ⁻¹' {t' : T | s₀⁻¹ * (t' : G) * s₀ ∈ U}).indicator
          (fun _ => (τ {t : T | s₀⁻¹ * (t : G) * s₀ ∈ U}).toReal⁻¹) t := by
      intro t
      have h0 : ∀ s ∈ S, s ≠ s₀ → {y : G | s⁻¹ * y ∈ U}.indicator
          (fun _ => (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal⁻¹) ((t : G) * (t₀ * s₀ * u₀)) = 0 := by
        intro s hs hne
        refine Set.indicator_of_notMem (fun h => hne ?_) _
        have h' : s⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) ∈ U := h
        exact hS s₀ hs₀ s hs ((t : G) * t₀) (T.mul_mem t.2 ht₀) (u₀ * (s⁻¹ * ((t : G) * (t₀ * s₀ * u₀)))⁻¹)
          (hUmul _ hu₀ _ (hUinv _ h')) (by group)
      rw [Finset.sum_eq_single_of_mem s₀ hs₀ h0]
      by_cases h : s₀⁻¹ * ((t : G) * t₀) * s₀ ∈ U
      · have h' : (t : G) * (t₀ * s₀ * u₀) ∈ {y : G | s₀⁻¹ * y ∈ U} := by
          have e : s₀⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) = s₀⁻¹ * ((t : G) * t₀) * s₀ * u₀ := by group
          rw [Set.mem_setOf_eq, e]
          exact hUmul _ h _ hu₀
        rw [Set.indicator_of_mem h', Set.indicator_of_mem]
        simpa using h
      · have h' : (t : G) * (t₀ * s₀ * u₀) ∉ {y : G | s₀⁻¹ * y ∈ U} :=
          fun (h' : s₀⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) ∈ U) => h (by
            have e : s₀⁻¹ * ((t : G) * t₀) * s₀ = s₀⁻¹ * ((t : G) * (t₀ * s₀ * u₀)) * u₀⁻¹ := by group
            rw [e]
            exact hUmul _ h' _ (hUinv _ hu₀))
        rw [Set.indicator_of_notMem h', Set.indicator_of_notMem]
        simpa using h
    have hmeas : MeasurableSet
        ((fun t' : T => t' * ⟨t₀, ht₀⟩) ⁻¹' {t' : T | s₀⁻¹ * (t' : G) * s₀ ∈ U}) :=
      (hst s₀).1.measurableSet.preimage (measurable_mul_const _)
    simp only [hsum]
    rw [integral_indicator_const _ hmeas, measureReal_def, measure_preimage_mul_right, smul_eq_mul,
      mul_inv_cancel₀ (hm s₀).ne']
  ·
    have hpt : ∀ y : G,
        ψ y * ((∑ s ∈ S, {y : G | s⁻¹ * y ∈ U}.indicator
          (fun _ => (τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal⁻¹) y : ℝ) : ℂ) =
        ∑ s ∈ S, {y : G | s⁻¹ * y ∈ U}.indicator
          (fun _ => ψ s / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ)) y := by
      intro y
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hy : y ∈ {y : G | s⁻¹ * y ∈ U}
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hψA s y hy, Complex.ofReal_inv, div_eq_mul_inv]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, Complex.ofReal_zero, mul_zero]
    have hint : ∀ s ∈ S, Integrable ({y : G | s⁻¹ * y ∈ U}.indicator
        fun _ => ψ s / ((τ {t : T | s⁻¹ * (t : G) * s ∈ U}).toReal : ℂ)) μ := fun s _ =>
      (integrableOn_const (hs := by rw [(hA s).2.1]; exact ENNReal.one_ne_top)).integrable_indicator (hA s).1
    simp only [hpt]
    rw [integral_finsetSum S hint]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_indicator_const _ (hA s).1, measureReal_def, (hA s).2.1, ENNReal.toReal_one, one_smul]

end SectionFunction

section Twist

open TensorProduct
open scoped TensorProduct.RightActions

variable {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A] [Algebra K A]

private theorem sigmaTensor_tmul (σ : L ≃ₐ[K] L) (ℓ : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (ℓ ⊗ₜ[K] a) = σ ℓ ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]

private theorem sigmaTensor_mul_apply (σ σ' : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    AutomorphicForm.sigmaTensor K L A (σ * σ') z =
      AutomorphicForm.sigmaTensor K L A σ (AutomorphicForm.sigmaTensor K L A σ' z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul ℓ a => rw [sigmaTensor_tmul, sigmaTensor_tmul, sigmaTensor_tmul, AlgEquiv.mul_apply]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

private theorem sigmaTensor_one_apply (z : L ⊗[K] A) : AutomorphicForm.sigmaTensor K L A 1 z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul ℓ a => rw [sigmaTensor_tmul, AlgEquiv.one_apply]
  | add z₁ z₂ h₁ h₂ => rw [map_add, h₁, h₂]

private theorem iterate_sigmaTensor_apply (σ : L ≃ₐ[K] L) (k : ℕ) (z : L ⊗[K] A) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[k] z = AutomorphicForm.sigmaTensor K L A (σ ^ k) z := by
  induction k generalizing z with
  | zero => rw [Function.iterate_zero_apply, pow_zero, sigmaTensor_one_apply]
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaTensor_mul_apply]

private theorem pow_finrank_eq_one (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (θ : E ≃ₐ[F] E) : θ ^ Module.finrank F E = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _ (Module.finrank_mul_finrank F (IntermediateField.fixedField (Subgroup.zpowers θ)) E)

private theorem iterate_sigmaTensor_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[Module.finrank K L] z = z := by
  rw [iterate_sigmaTensor_apply, pow_finrank_eq_one K L σ, sigmaTensor_one_apply]

variable (σ : L ≃ₐ[K] L)

open AutomorphicForm

private theorem iterate_sigmaGL_eq_self (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z)
    (x : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] x = x :=
  LT.TwistedNorm.iterate_generalLinearGroup_map_eq_self hσn x

private theorem normString_eq_sigmaNormPow (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = LT.TwistedNorm.sigmaNormPow (sigmaGL K L A σ) (Module.finrank K L) δ :=
  (LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range (sigmaGL K L A σ) δ (Module.finrank K L)).symm

private theorem commute_normString_of_mem_twistedCentralizer
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {δ t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ twistedCentralizer K L A σ δ) : t * normString K L A σ δ = normString K L A σ δ * t := by
  have h1 : t⁻¹ * δ * sigmaGL K L A σ t = δ := mem_sigmaCentralizer_iff_inv.1 ht
  have key := LT.TwistedNorm.sigmaNormPow_sigmaConjElt (sigmaGL K L A σ) (Module.finrank K L)
    (iterate_sigmaGL_eq_self σ hσn t) δ
  rw [h1] at key
  rw [normString_eq_sigmaNormPow]
  conv_lhs => rw [key]
  group

private theorem mul_comm_of_mem_twistedCentralizer
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {δ : GL (Fin 2) (L ⊗[K] A)}
    (hδ : IsRegularSemisimple (normString K L A σ δ)) (s t : twistedCentralizer K L A σ δ) : s * t = t * s := by
  have hs : ((s : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (normString K L A σ δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (normString K L A σ δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
        ((s : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    rw [← Units.val_mul, ← Units.val_mul, commute_normString_of_mem_twistedCentralizer σ hσn s.2]
  have ht : ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (normString K L A σ δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (normString K L A σ δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
        ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    rw [← Units.val_mul, ← Units.val_mul, commute_normString_of_mem_twistedCentralizer σ hσn t.2]
  exact Subtype.ext (Units.ext (commute_of_commute_of_commute hδ hs ht))

end Twist

section SemiLocal

open TensorProduct
open scoped TensorProduct.RightActions

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
  {v : HeightOneSpectrum (𝓞 K)}

open AutomorphicForm

private theorem continuous_sigmaTensor : Continuous (sigmaTensor K L (v.adicCompletion K) σ) := by
  have h : ⇑(sigmaTensor K L (v.adicCompletion K) σ) =
      ⇑(TensorProduct.RightActions.LinearMap.baseChange K L L (v.adicCompletion K) σ.toLinearMap) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul ℓ a =>
      rw [sigmaTensor_tmul]
      simp [TensorProduct.RightActions.LinearMap.baseChange, LinearMap.baseChange_tmul]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

private theorem continuous_sigmaGL : Continuous (sigmaGL K L (v.adicCompletion K) σ) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  have hf := continuous_sigmaTensor σ (v := v)
  rw [Units.continuous_iff]
  refine ⟨Units.continuous_val.matrix_map hf, ?_⟩
  have h : (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (((sigmaGL K L (v.adicCompletion K) σ g)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) =
      fun g => ((g⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).map (sigmaTensor K L (v.adicCompletion K) σ) := by
    funext g
    rw [← map_inv]
    rfl
  rw [h]
  exact Units.continuous_coe_inv.matrix_map hf

omit [NumberField L] in

private theorem sigmaTensor_mem_semiLocalIntegers {z : L ⊗[K] v.adicCompletion K}
    (hz : z ∈ semiLocalIntegers K L v) :
    sigmaTensor K L (v.adicCompletion K) σ z ∈ semiLocalIntegers K L v := by
  obtain ⟨t, rfl⟩ := hz
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp only [map_zero]⟩
  | tmul b x =>
    refine ⟨NumberField.RingOfIntegers.mapRingHom (σ : L →+* L) b ⊗ₜ x, ?_⟩
    rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul,
      sigmaTensor_tmul]
    rfl
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨a₁, ha₁⟩ := h₁
    obtain ⟨a₂, ha₂⟩ := h₂
    exact ⟨a₁ + a₂, by simp only [map_add, ha₁, ha₂]⟩

omit [NumberField L] in

private theorem sigmaGL_mem_semiLocalIntegralSet {u : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hu : u ∈ semiLocalIntegralSet K L v) : sigmaGL K L (v.adicCompletion K) σ u ∈ semiLocalIntegralSet K L v :=
  ⟨fun i j => sigmaTensor_mem_semiLocalIntegers σ (hu.1 i j), fun i j => by
    rw [← map_inv]
    exact sigmaTensor_mem_semiLocalIntegers σ (hu.2 i j)⟩

end SemiLocal

open AutomorphicForm

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ u₁ ∈ AutomorphicForm.semiLocalIntegralSet K L v, ∀ u₂ ∈ AutomorphicForm.semiLocalIntegralSet K L v,
        φ (u₁ * g * u₂) = φ g)
    (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∀ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 →
          ∃ s ∈ S,
            ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
              ∃ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, x = t * s * u) :
    AutomorphicForm.IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ
      (AutomorphicForm.semiLocalHaar K L v) δ τ' φ
      (∑ s ∈ S, φ (s⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ s) /
        ((τ' {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈
            AutomorphicForm.semiLocalIntegralSet K L v}).toReal : ℂ)) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := borelSpace_glBorelOf _
  letI : MeasurableSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) :=
    twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure τ' := hτ'
  haveI := isHaarMeasure_semiLocalHaar K L v

  have hσn : ∀ z : L ⊗[K] v.adicCompletion K,
      (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[Module.finrank K L] z = z :=
    iterate_sigmaTensor_finrank σ
  haveI : τ'.IsMulRightInvariant := ⟨fun t => by
    rw [show (fun s => s * t) = fun s => t * s from
      funext fun s => mul_comm_of_mem_twistedCentralizer σ hσn hδ s t]
    exact map_mul_left_eq_self τ' t⟩

  have hT : IsClosed ((twistedCentralizer K L (v.adicCompletion K) σ δ) :
      Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
    show IsClosed {t : GL (Fin 2) (L ⊗[K] v.adicCompletion K) | t * δ * (sigmaGL K L (v.adicCompletion K) σ t)⁻¹ = δ}
    exact isClosed_eq ((continuous_id.mul continuous_const).mul (continuous_sigmaGL σ).inv) continuous_const

  have hU : semiLocalIntegers K L v =
      (((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range :
        Subalgebra (𝓞 L) (L ⊗[K] v.adicCompletion K)) : Set (L ⊗[K] v.adicCompletion K)) :=
    Set.ext fun _ => (AlgHom.mem_range _).symm

  have hψ : ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ u ∈ semiLocalIntegralSet K L v,
        φ ((t * x * u)⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ (t * x * u)) =
          φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) := by
    intro t ht x u hu
    have ht' : t⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ t = δ := mem_sigmaCentralizer_iff_inv.1 ht
    have e : (t * x * u)⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ (t * x * u) =
        u⁻¹ * (x⁻¹ * (t⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ t) * sigmaGL K L (v.adicCompletion K) σ x) *
          sigmaGL K L (v.adicCompletion K) σ u := by
      rw [map_mul, map_mul]
      group
    rw [e, ht']
    exact hφ _ u⁻¹ (inv_mem_integralUnitsSet _ hu) _ (sigmaGL_mem_semiLocalIntegralSet σ hu)
  obtain ⟨w, h0, hw, hcpt, hsec, hint⟩ := exists_section_of_forall_eq_of_forall_exists (semiLocalHaar K L v)
    (semiLocalIntegralSet K L v) (isOpen_semiLocalIntegralSet K L v) (isCompact_semiLocalIntegralSet K L v)
    (semiLocalHaar_semiLocalIntegralSet K L v) (one_mem_semiLocalIntegralSet K L v)
    (fun a ha b hb => by
      rw [semiLocalIntegralSet, hU] at ha hb ⊢
      exact mul_mem_integralUnitsSet _ ha hb)
    (fun a ha => inv_mem_integralUnitsSet _ ha) (twistedCentralizer K L (v.adicCompletion K) σ δ) hT τ'
    (fun x => φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x)) hψ S hS hcov
  exact ⟨w, ⟨h0, hw, hcpt, hsec⟩, hint.symm⟩

end S_AutomorphicForm_isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists
end P2MW
export P2MW.S_AutomorphicForm_isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists (solution)
