-- Prove2me | solution 1 for AutomorphicForm.lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_of_map_coe_eq_smul_withDensity_gram_of_forall_le_mul_one_add_norm_rpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/90deba45-1eb8-551f-805c-96f489bfd21f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_of_map_coe_eq_smul_withDensity_gram_of_forall_le_mul_one_add_norm_rpow_neg

set_option autoImplicit false

open MeasureTheory Filter Topology NumberField
open scoped ENNReal TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

namespace ArchFactorCore

variable {Y : Type*} [MeasurableSpace Y]

theorem integrand_eq (w : Y → ℝ) (hw0 : ∀ y, 0 ≤ w y) (G : Y → ℝ) (s₁ : ℝ) (hs₁ : 0 < s₁) (y : Y) :
    ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ s₁) * (ENNReal.ofReal (w y))⁻¹ =
      {y | w y ≠ 0}.indicator (fun y => ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ (s₁ - 1))) y := by
  by_cases h : w y = 0
  · have : y ∉ {y | w y ≠ 0} := by simp [h]
    rw [Set.indicator_of_notMem this, h, Real.zero_rpow hs₁.ne']
    simp
  · have hpos : 0 < w y := lt_of_le_of_ne (hw0 y) (Ne.symm h)
    have : y ∈ {y | w y ≠ 0} := h
    rw [Set.indicator_of_mem this, mul_assoc, ← ENNReal.ofReal_inv_of_pos hpos,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (hw0 y) _)]
    congr 2
    rw [Real.rpow_sub_one h, div_eq_mul_inv]

theorem main (μ : Measure Y) (w : Y → ℝ) (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (G : Y → ℝ) (hG0 : ∀ y, 0 ≤ G y) (hGm : Measurable G)
    (S : Set Y) (hSm : MeasurableSet S) (hS : μ S < ∞) (hGS : ∀ y ∉ S, G y = 0)
    (M : ℝ) (hGM : ∀ y, G y ≤ M) (B : ℝ) (hB1 : 1 ≤ B) (hB : ∀ y ∈ S, w y ≤ B)
    (hnull : μ {y | w y = 0} = 0) :
    (∀ s₁ : ℝ, 1 ≤ s₁ →
      ∫⁻ y, ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ s₁)
        ∂(μ.withDensity fun y => (ENNReal.ofReal (w y))⁻¹) < ∞) ∧
    Tendsto (fun s₁ : ℝ => ∫⁻ y, ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ s₁)
        ∂(μ.withDensity fun y => (ENNReal.ofReal (w y))⁻¹)) (𝓝[>] 1)
      (𝓝 (∫⁻ y, ENNReal.ofReal (G y) ∂μ)) ∧
    ∫⁻ y, ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ (1 : ℝ))
        ∂(μ.withDensity fun y => (ENNReal.ofReal (w y))⁻¹) = ∫⁻ y, ENNReal.ofReal (G y) ∂μ := by
  have hdens : Measurable fun y => (ENNReal.ofReal (w y))⁻¹ :=
    (ENNReal.measurable_ofReal.comp hw).inv

  have hunf : ∀ s₁ : ℝ, 0 < s₁ →
      ∫⁻ y, ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ s₁) ∂(μ.withDensity fun y => (ENNReal.ofReal (w y))⁻¹) =
        ∫⁻ y, {y | w y ≠ 0}.indicator (fun y => ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ (s₁ - 1))) y ∂μ := by
    intro s₁ hs₁
    have hfm : Measurable fun y => ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ s₁) :=
      (ENNReal.measurable_ofReal.comp hGm).mul
        (ENNReal.measurable_ofReal.comp (hw.pow_const s₁))
    rw [lintegral_withDensity_eq_lintegral_mul _ hdens hfm]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm, integrand_eq w hw0 G s₁ hs₁ y]

  have hnull' : ∀ f : Y → ℝ≥0∞, ∫⁻ y, {y | w y ≠ 0}.indicator f y ∂μ = ∫⁻ y, f y ∂μ := by
    intro f
    refine lintegral_congr_ae ?_
    have : ∀ᵐ y ∂μ, y ∈ {y | w y ≠ 0} := by
      rw [ae_iff]; simpa using hnull
    filter_upwards [this] with y hy
    rw [Set.indicator_of_mem hy]
  have hval : ∫⁻ y, ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ (1 : ℝ))
        ∂(μ.withDensity fun y => (ENNReal.ofReal (w y))⁻¹) = ∫⁻ y, ENNReal.ofReal (G y) ∂μ := by
    rw [hunf 1 one_pos, hnull']
    refine lintegral_congr fun y => ?_
    simp

  have hdom : ∀ s₁ : ℝ, 1 ≤ s₁ → s₁ ≤ 2 → ∀ y,
      {y | w y ≠ 0}.indicator (fun y => ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ (s₁ - 1))) y ≤
        S.indicator (fun _ => ENNReal.ofReal (M * B)) y := by
    intro s₁ h1 h2 y
    by_cases hyS : y ∈ S
    · rw [Set.indicator_of_mem hyS]
      refine (Set.indicator_le_self _ _ y).trans ?_
      rw [← ENNReal.ofReal_mul (hG0 y)]
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul (hGM y) ?_ (Real.rpow_nonneg (hw0 y) _) ((hG0 y).trans (hGM y))
      calc w y ^ (s₁ - 1) ≤ B ^ (s₁ - 1) := Real.rpow_le_rpow (hw0 y) (hB y hyS) (by linarith)
        _ ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
        _ = B := Real.rpow_one B
    · rw [Set.indicator_of_notMem hyS]
      refine (Set.indicator_le_self _ _ y).trans ?_
      simp [hGS y hyS]
  have hdomS : ∀ s₁ : ℝ, 1 ≤ s₁ → ∀ y,
      {y | w y ≠ 0}.indicator (fun y => ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ (s₁ - 1))) y ≤
        S.indicator (fun _ => ENNReal.ofReal (M * B ^ (s₁ - 1))) y := by
    intro s₁ h1 y
    by_cases hyS : y ∈ S
    · rw [Set.indicator_of_mem hyS]
      refine (Set.indicator_le_self _ _ y).trans ?_
      rw [← ENNReal.ofReal_mul (hG0 y)]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul (hGM y) (Real.rpow_le_rpow (hw0 y) (hB y hyS) (by linarith))
        (Real.rpow_nonneg (hw0 y) _) ((hG0 y).trans (hGM y))
    · rw [Set.indicator_of_notMem hyS]
      refine (Set.indicator_le_self _ _ y).trans ?_
      simp [hGS y hyS]
  have hconst : ∀ C : ℝ, ∫⁻ y, S.indicator (fun _ => ENNReal.ofReal C) y ∂μ < ∞ := by
    intro C
    rw [lintegral_indicator hSm, setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS
  refine ⟨?_, ?_, hval⟩
  · intro s₁ hs₁
    rw [hunf s₁ (by linarith)]
    exact lt_of_le_of_lt (lintegral_mono (hdomS s₁ hs₁)) (hconst _)
  ·
    rw [← hval]
    have hev : ∀ᶠ s₁ in 𝓝[>] (1 : ℝ), 1 ≤ s₁ ∧ s₁ ≤ 2 := by
      have h1 : ∀ᶠ s₁ in 𝓝[>] (1 : ℝ), 1 ≤ s₁ := by
        filter_upwards [self_mem_nhdsWithin] with s hs; exact le_of_lt hs
      have h2 : ∀ᶠ s₁ in 𝓝[>] (1 : ℝ), s₁ ≤ 2 := by
        have : Set.Iio (2 : ℝ) ∈ 𝓝 (1 : ℝ) := Iio_mem_nhds (by norm_num)
        filter_upwards [mem_nhdsWithin_of_mem_nhds this] with s hs; exact le_of_lt hs
      exact h1.and h2
    have key : Tendsto (fun s₁ : ℝ => ∫⁻ y, {y | w y ≠ 0}.indicator
          (fun y => ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ (s₁ - 1))) y ∂μ) (𝓝[>] 1)
        (𝓝 (∫⁻ y, {y | w y ≠ 0}.indicator
          (fun y => ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ ((1 : ℝ) - 1))) y ∂μ)) := by
      refine tendsto_lintegral_filter_of_dominated_convergence
        (S.indicator (fun _ => ENNReal.ofReal (M * B))) ?_ ?_ (hconst _).ne ?_
      · refine Eventually.of_forall fun s₁ => ?_
        exact ((ENNReal.measurable_ofReal.comp hGm).mul
          (ENNReal.measurable_ofReal.comp (hw.pow_const _))).indicator (hw (measurableSet_singleton 0).compl)
      · filter_upwards [hev] with s₁ hs₁
        exact Eventually.of_forall (hdom s₁ hs₁.1 hs₁.2)
      · refine Eventually.of_forall fun y => ?_
        by_cases hy : y ∈ {y | w y ≠ 0}
        · simp only [Set.indicator_of_mem hy]
          have hne : w y ≠ 0 := hy
          have hc : ContinuousAt ((fun x : ℝ => w y ^ x) ∘ (fun s₁ : ℝ => s₁ - 1)) 1 :=
            ContinuousAt.comp (Real.continuousAt_const_rpow hne) (continuousAt_id.sub continuousAt_const)
          refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
          exact ((ENNReal.continuous_ofReal.tendsto _).comp hc.tendsto).mono_left nhdsWithin_le_nhds
        · simp only [Set.indicator_of_notMem hy]
          exact tendsto_const_nhds
    have e1 : ∀ᶠ s₁ in 𝓝[>] (1 : ℝ), ∫⁻ y, ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ s₁)
        ∂(μ.withDensity fun y => (ENNReal.ofReal (w y))⁻¹) =
        ∫⁻ y, {y | w y ≠ 0}.indicator (fun y => ENNReal.ofReal (G y) * ENNReal.ofReal (w y ^ (s₁ - 1))) y ∂μ := by
      filter_upwards [hev] with s₁ hs₁; exact hunf s₁ (by linarith)
    rw [hunf 1 one_pos]
    exact key.congr' (e1.mono fun s h => h.symm)

end ArchFactorCore

namespace ContNormDet

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

@[reducible] noncomputable def algRK : Algebra ℝ (InfiniteAdeleRing K) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra

@[reducible] noncomputable def algRE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
  letI : Algebra ℝ (InfiniteAdeleRing K) := algRK K
  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
    (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra

theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :
      mixedEmbedding.mixedSpace K → InfiniteAdeleRing K) := by
  refine continuous_pi fun v => ?_
  by_cases hv : v.IsReal
  · have h : ∀ y : mixedEmbedding.mixedSpace K, (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v =
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      intro y
      have e : InfinitePlace.Completion.ringEquivRealOfIsReal hv
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.1 ⟨v, hv⟩ :=
        congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
      rw [← e]
      exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm_apply_apply _).symm
    rw [show (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) =
        fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) from funext h]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have h : ∀ y : mixedEmbedding.mixedSpace K, (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v =
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm (y.2 ⟨v, hv'⟩) := by
      intro y
      have e : InfinitePlace.Completion.ringEquivComplexOfIsComplex hv'
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) = y.2 ⟨v, hv'⟩ :=
        congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hv'⟩)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
      rw [← e]
      exact ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm_apply_apply _).symm
    rw [show (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v) =
        fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm (y.2 ⟨v, hv'⟩) from funext h]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

noncomputable def algEquivK :
    letI : Algebra ℝ (InfiniteAdeleRing K) := algRK K
    InfiniteAdeleRing K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
  letI : Algebra ℝ (InfiniteAdeleRing K) := algRK K
  AlgEquiv.ofRingEquiv (f := InfiniteAdeleRing.ringEquiv_mixedSpace K) (fun r => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace K
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (algebraMap ℝ (mixedEmbedding.mixedSpace K) r)) = _
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _)

end ContNormDet

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (τa : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ))
    (s : ℝ≥0∞) (hs : s ≠ ⊤)
    (G : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞)
    (hGm : Measurable[borel _] G) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
    ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ e₂ →
      Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) →
      ∀ s₁ : ℝ, 1 ≤ s₁ → ∀ (r C : ℝ),
        (n₂ : ℝ) + 2 * (Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) : ℝ) * (s₁ - 1) < r →
        (∀ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i) ≤ ENNReal.ofReal (C * (1 + ‖c‖) ^ (-r))) →
        ∫⁻ t, G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| ^ s₁) ∂τa < ⊤ := by
  classical
  letI iRK : Algebra ℝ (InfiniteAdeleRing K) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
  letI iRE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
      (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
  letI mM : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
  intro n₂ e₂ he hτ s₁ hs₁ r C hr hC
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI bM : BorelSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := ⟨rfl⟩
  haveI hfinK : Module.Finite ℝ (InfiniteAdeleRing K) :=
    Module.Finite.equiv (ContNormDet.algEquivK K).symm.toLinearEquiv
  haveI hST : IsScalarTower ℝ (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) :=
    @IsScalarTower.of_algebraMap_eq ℝ (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) _ _ _
      iRK inferInstance iRE (fun r => rfl)
  haveI hfinE : Module.Finite ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    Module.Finite.trans (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  have hcont_alg : Continuous (algebraMap ℝ (InfiniteAdeleRing K)) := by
    show Continuous (fun r : ℝ => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (algebraMap ℝ (mixedEmbedding.mixedSpace K) r))
    exact (ContNormDet.continuous_ringEquiv_mixedSpace_symm K).comp
      (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace K))
  haveI : ContinuousSMul (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) :=
    IsModuleTopology.toContinuousSMul (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  haveI hsmul : ContinuousSMul ℝ (L ⊗[K] InfiniteAdeleRing K) := by
    refine ⟨?_⟩
    have : (fun p : ℝ × (L ⊗[K] InfiniteAdeleRing K) => p.1 • p.2) =
        fun p => (algebraMap ℝ (InfiniteAdeleRing K) p.1) • p.2 := by
      funext p; exact (algebraMap_smul (InfiniteAdeleRing K) p.1 p.2).symm
    rw [this]
    exact (hcont_alg.comp continuous_fst).smul continuous_snd
  haveI : IsTopologicalAddGroup (L ⊗[K] InfiniteAdeleRing K) := inferInstance
  have hnorm : Continuous (Algebra.norm ℝ : L ⊗[K] InfiniteAdeleRing K → ℝ) := by
    let b := Module.finBasis ℝ (L ⊗[K] InfiniteAdeleRing K)
    have : (Algebra.norm ℝ : L ⊗[K] InfiniteAdeleRing K → ℝ) =
        fun s => (Algebra.leftMulMatrix b s).det := funext (Algebra.norm_eq_matrix_det b)
    rw [this]
    exact ((Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional).matrix_det
  set w : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ :=
    fun X => |Algebra.norm ℝ (Matrix.det X)| with hw_def
  have hwc : Continuous w := continuous_abs.comp (hnorm.comp (continuous_id.matrix_det))
  have hwm : Measurable w := hwc.measurable
  have hw0 : ∀ X, 0 ≤ w X := fun X => abs_nonneg _
  set Gr : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
      Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) with hGr_def
  have hGr : Gr ≠ ⊤ := ENNReal.ofReal_ne_top
  set Lmap : (Fin n₂ → ℝ) → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) :=
    fun c => ∑ i, c i • e₂ i with hL_def
  have hLlin : Lmap = ⇑(Fintype.linearCombination ℝ e₂) := by
    funext c; simp [hL_def, Fintype.linearCombination_apply]
  have hLcont : Continuous Lmap :=
    continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hLm : Measurable Lmap := hLcont.measurable
  set μL : Measure (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    Gr • Measure.map Lmap volume with hμL_def
  haveI : BorelSpace ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := ⟨rfl⟩
  have hcoe_c : Continuous (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
      ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcoe_m := hcoe_c.measurable
  have hFm : ∀ s₁ : ℝ, Measurable fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      G X * ENNReal.ofReal (w X ^ s₁) := fun s₁ =>
    hGm.mul (ENNReal.measurable_ofReal.comp (hwm.pow_const s₁))

  have stepA :
      ∫⁻ t, G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| ^ s₁) ∂τa =
        s * ∫⁻ X, G X * ENNReal.ofReal (w X ^ s₁) ∂(μL.withDensity fun X => (ENNReal.ofReal (w X))⁻¹) := by
    have h1 := lintegral_map (μ := τa) (hFm s₁) hcoe_m
    simp only [hw_def] at h1
    rw [← h1, hτ, lintegral_smul_measure, smul_eq_mul]
  rw [stepA]
  refine ENNReal.mul_lt_top hs.lt_top ?_

  have hdens : Measurable fun X => (ENNReal.ofReal (w X))⁻¹ := (ENNReal.measurable_ofReal.comp hwm).inv
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens (hFm s₁)]
  have hle : ∀ X, ((fun X => (ENNReal.ofReal (w X))⁻¹) * fun X => G X * ENNReal.ofReal (w X ^ s₁)) X ≤
      G X * ENNReal.ofReal (w X ^ (s₁ - 1)) := by
    intro X
    simp only [Pi.mul_apply]
    by_cases h : w X = 0
    · rw [h, Real.zero_rpow (by linarith)]; simp
    · have hpos : 0 < w X := lt_of_le_of_ne (hw0 X) (Ne.symm h)
      rw [mul_comm, mul_assoc, ← ENNReal.ofReal_inv_of_pos hpos,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hw0 X) _), Real.rpow_sub_one h, div_eq_mul_inv]
  refine lt_of_le_of_lt (lintegral_mono hle) ?_

  have hHm : Measurable fun X => G X * ENNReal.ofReal (w X ^ (s₁ - 1)) := hFm (s₁ - 1)
  simp only [hμL_def]
  rw [lintegral_smul_measure, smul_eq_mul, lintegral_map hHm hLm]
  refine ENNReal.mul_lt_top hGr.lt_top ?_

  set d : ℕ := 2 * Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) with hd_def
  have hhom : ∀ (r : ℝ) (c : Fin n₂ → ℝ), w (Lmap (r • c)) = |r| ^ d * w (Lmap c) := by
    intro r c
    have hL : Lmap (r • c) = r • Lmap c := by
      rw [hLlin]; exact map_smul _ r c
    have hdet : Matrix.det (r • Lmap c) = (algebraMap ℝ (L ⊗[K] InfiniteAdeleRing K) r) ^ 2 * Matrix.det (Lmap c) := by
      rw [show r • Lmap c = (algebraMap ℝ (L ⊗[K] InfiniteAdeleRing K) r) • Lmap c from
        (algebraMap_smul (L ⊗[K] InfiniteAdeleRing K) r (Lmap c)).symm, Matrix.det_smul]
      simp
    simp only [hw_def, hL, hdet, map_mul, map_pow, Algebra.norm_algebraMap, abs_mul, abs_pow]
    rw [hd_def, pow_mul]
    ring
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ c : Fin n₂ → ℝ, ‖c‖ = 1 → w (Lmap c) ≤ M₀ := by
    obtain ⟨B, hB⟩ := (isCompact_sphere (0 : Fin n₂ → ℝ) 1).bddAbove_image (hwc.comp hLcont).continuousOn
    exact ⟨B, fun c hc => hB ⟨c, by simpa using hc, rfl⟩⟩
  have hM₀0 : 0 ≤ max M₀ 0 := le_max_right _ _
  have hpoly : ∀ c : Fin n₂ → ℝ, w (Lmap c) ≤ max M₀ 0 * (1 + ‖c‖) ^ (d : ℝ) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      have h0 : Lmap 0 = 0 := by rw [hLlin]; exact map_zero _
      have hw00 : w (Lmap 0) = 0 := by
        have hd0 : d ≠ 0 := by
          have : 0 < Module.finrank ℝ (L ⊗[K] InfiniteAdeleRing K) := Module.finrank_pos
          simp only [hd_def]; omega
        have := hhom 0 0
        rw [smul_zero, abs_zero, zero_pow hd0, zero_mul] at this
        exact this
      rw [hw00]; positivity
    · have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
      have hnpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
      have hc1 : ‖(‖c‖⁻¹ • c)‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have key : w (Lmap c) = ‖c‖ ^ d * w (Lmap (‖c‖⁻¹ • c)) := by
        have := hhom ‖c‖ (‖c‖⁻¹ • c)
        rwa [smul_smul, mul_inv_cancel₀ hn, one_smul, abs_of_pos hnpos] at this
      rw [key]
      calc ‖c‖ ^ d * w (Lmap (‖c‖⁻¹ • c)) ≤ (1 + ‖c‖) ^ d * max M₀ 0 := by
            apply mul_le_mul (pow_le_pow_left₀ hnpos.le (by linarith) d) ((hM₀ _ hc1).trans (le_max_left _ _))
              (hw0 _) (by positivity)
        _ = max M₀ 0 * (1 + ‖c‖) ^ (d : ℝ) := by rw [Real.rpow_natCast, mul_comm]

  have hC0 : ∀ c, G (Lmap c) ≤ ENNReal.ofReal (max C 0 * (1 + ‖c‖) ^ (-r)) := by
    intro c
    refine (hC c).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)

  have hbound : ∀ c : Fin n₂ → ℝ, G (Lmap c) * ENNReal.ofReal (w (Lmap c) ^ (s₁ - 1)) ≤
      ENNReal.ofReal (max C 0 * (max M₀ 0) ^ (s₁ - 1)) * ENNReal.ofReal ((1 + ‖c‖) ^ (-(r - (d : ℝ) * (s₁ - 1)))) := by
    intro c
    have h1c : (1 : ℝ) ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
    have hwle : w (Lmap c) ^ (s₁ - 1) ≤ (max M₀ 0) ^ (s₁ - 1) * (1 + ‖c‖) ^ ((d : ℝ) * (s₁ - 1)) := by
      calc w (Lmap c) ^ (s₁ - 1) ≤ (max M₀ 0 * (1 + ‖c‖) ^ (d : ℝ)) ^ (s₁ - 1) :=
            Real.rpow_le_rpow (hw0 _) (hpoly c) (by linarith)
        _ = (max M₀ 0) ^ (s₁ - 1) * (1 + ‖c‖) ^ ((d : ℝ) * (s₁ - 1)) := by
            rw [Real.mul_rpow hM₀0 (Real.rpow_nonneg (by positivity) _), ← Real.rpow_mul (by positivity)]
    calc G (Lmap c) * ENNReal.ofReal (w (Lmap c) ^ (s₁ - 1))
        ≤ ENNReal.ofReal (max C 0 * (1 + ‖c‖) ^ (-r)) *
            ENNReal.ofReal ((max M₀ 0) ^ (s₁ - 1) * (1 + ‖c‖) ^ ((d : ℝ) * (s₁ - 1))) :=
          mul_le_mul' (hC0 c) (ENNReal.ofReal_le_ofReal hwle)
      _ = ENNReal.ofReal (max C 0 * (max M₀ 0) ^ (s₁ - 1) *
            ((1 + ‖c‖) ^ (-r) * (1 + ‖c‖) ^ ((d : ℝ) * (s₁ - 1)))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
      _ = ENNReal.ofReal (max C 0 * (max M₀ 0) ^ (s₁ - 1)) * ENNReal.ofReal ((1 + ‖c‖) ^ (-(r - (d : ℝ) * (s₁ - 1)))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by positivity)]
          ring_nf
  refine lt_of_le_of_lt (lintegral_mono (g := fun c : Fin n₂ → ℝ =>
    ENNReal.ofReal (max C 0 * (max M₀ 0) ^ (s₁ - 1)) * ENNReal.ofReal ((1 + ‖c‖) ^ (-(r - (d : ℝ) * (s₁ - 1)))))
    fun c => hbound c) ?_
  rw [lintegral_const_mul _ (by fun_prop)]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hr' : (Module.finrank ℝ (Fin n₂ → ℝ) : ℝ) < r - (d : ℝ) * (s₁ - 1) := by
    rw [Module.finrank_fin_fun]; simp only [hd_def]; push_cast; linarith
  exact finite_integral_one_add_norm (E := Fin n₂ → ℝ) (μ := volume) hr'

end S_AutomorphicForm_lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_of_map_coe_eq_smul_withDensity_gram_of_forall_le_mul_one_add_norm_rpow_neg
end P2MW
export P2MW.S_AutomorphicForm_lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_of_map_coe_eq_smul_withDensity_gram_of_forall_le_mul_one_add_norm_rpow_neg (solution)
