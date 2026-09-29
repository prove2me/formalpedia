-- Prove2me | solution 1 for AutomorphicForm.lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_and_tendsto_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1ea9b1c2-cfe0-5b9a-8696-dd5604d051d6

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_and_tendsto_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram

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
    (hGm : Measurable[borel _] G) (C : ℝ≥0∞) (hC : C ≠ ⊤) (hGC : ∀ X, G X ≤ C)
    (S : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) (hS : IsCompact S)
    (hGS : ∀ X ∉ S, G X = 0) :
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
      (∀ s₁ : ℝ, 1 ≤ s₁ →
        ∫⁻ t, G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| ^ s₁) ∂τa < ⊤) ∧
      Tendsto (fun s₁ : ℝ =>
        ∫⁻ t, G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| ^ s₁) ∂τa) (𝓝[>] 1)
        (𝓝 (s * (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
              ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i)))) ∧
      ∫⁻ t, G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| ^ (1 : ℝ)) ∂τa =
        s * (ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|) *
              ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i)) := by
  classical
  letI iRK : Algebra ℝ (InfiniteAdeleRing K) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
  letI iRE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
      (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
  letI mM : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
  intro n₂ e₂ he hτ
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
  have hLce : IsClosedEmbedding Lmap := by
    rw [hLlin]
    refine LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr ?_)
    exact he.fintypeLinearCombination_injective

  set μL : Measure (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    Gr • Measure.map Lmap volume with hμL_def

  haveI : BorelSpace ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := ⟨rfl⟩
  have hcoe_c : Continuous (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
      ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) :=
    Units.continuous_val.comp continuous_subtype_val
  have hcoe_m : Measurable (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
      ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) :=
    hcoe_c.measurable
  have hFm : ∀ s₁ : ℝ, Measurable fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      G X * ENNReal.ofReal (w X ^ s₁) := fun s₁ =>
    hGm.mul (ENNReal.measurable_ofReal.comp (hwm.pow_const s₁))

  have stepA : ∀ s₁ : ℝ,
      ∫⁻ t, G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| ^ s₁) ∂τa =
        s * ∫⁻ X, G X * ENNReal.ofReal (w X ^ s₁) ∂(μL.withDensity fun X => (ENNReal.ofReal (w X))⁻¹) := by
    intro s₁
    have h1 := lintegral_map (μ := τa) (hFm s₁) hcoe_m
    simp only [hw_def] at h1
    rw [← h1, hτ, lintegral_smul_measure, smul_eq_mul]

  set G' : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ := fun X => (G X).toReal with hG'_def
  have hGeq : ∀ X, ENNReal.ofReal (G' X) = G X := fun X =>
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top hC (hGC X))
  have hG'0 : ∀ X, 0 ≤ G' X := fun X => ENNReal.toReal_nonneg
  have hG'm : Measurable G' := ENNReal.measurable_toReal.comp hGm
  have hG'S : ∀ X ∉ S, G' X = 0 := fun X hX => by simp [hG'_def, hGS X hX]
  have hG'M : ∀ X, G' X ≤ C.toReal := fun X => ENNReal.toReal_mono hC (hGC X)

  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  obtain ⟨B₀, hB₀⟩ := hS.bddAbove_image hwc.continuousOn
  have hB : ∀ X ∈ S, w X ≤ max 1 B₀ := fun X hX => (hB₀ ⟨X, hX, rfl⟩).trans (le_max_right _ _)
  have hμS : μL S < ⊤ := by
    simp only [hμL_def, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply hLm hSm]
    exact ENNReal.mul_lt_top hGr.lt_top (hLce.isCompact_preimage hS).measure_lt_top

  have stepC : ∫⁻ X, G X ∂μL = Gr * ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i) := by
    simp only [hμL_def]
    rw [lintegral_smul_measure, smul_eq_mul, lintegral_map hGm hLm]

  by_cases hdeg : s = 0 ∨ Gr = 0
  · have hzero : ∀ s₁ : ℝ,
        ∫⁻ t, G ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          ENNReal.ofReal (|Algebra.norm ℝ (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| ^ s₁) ∂τa = 0 := by
      intro s₁
      rw [stepA s₁]
      rcases hdeg with h0 | h0
      · simp [h0]
      · have : μL = 0 := by simp [hμL_def, h0]
        simp [this]
    have hrhs : s * (Gr * ∫⁻ c : Fin n₂ → ℝ, G (∑ i, c i • e₂ i)) = 0 := by
      rcases hdeg with h0 | h0 <;> simp [h0]
    refine ⟨fun s₁ _ => by rw [hzero s₁]; exact ENNReal.zero_lt_top, ?_, ?_⟩
    · simp only [hzero, hrhs]; exact tendsto_const_nhds
    · rw [hzero, hrhs]
  push_neg at hdeg
  obtain ⟨hs0, hGr0⟩ := hdeg

  have hZm : MeasurableSet {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) | w X = 0} :=
    hwm (measurableSet_singleton 0)
  have hnull : μL {X | w X = 0} = 0 := by
    have h0 : (Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
        ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa)
        {X | w X = 0} = 0 := by
      rw [Measure.map_apply hcoe_m hZm]
      convert measure_empty (μ := τa)
      ext t
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hw_def,
        abs_eq_zero]
      have hu : IsUnit (Matrix.det ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) :=
        ⟨Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)), rfl⟩
      exact (hu.map (Algebra.norm ℝ)).ne_zero
    rw [hτ, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 hs0
    rw [withDensity_apply _ hZm] at h0
    have : ∫⁻ X in {X | w X = 0}, (ENNReal.ofReal (w X))⁻¹ ∂μL = ∫⁻ X in {X | w X = 0}, ⊤ ∂μL := by
      refine setLIntegral_congr_fun hZm ?_
      intro X hX
      rw [Set.mem_setOf_eq] at hX
      simp [hX]
    rw [this, setLIntegral_const] at h0
    simpa using h0

  obtain ⟨cA, cB, cC⟩ := ArchFactorCore.main μL w hwm hw0 G' hG'0 hG'm S hSm hμS hG'S (C.toReal) hG'M
    (max 1 B₀) (le_max_left _ _) hB hnull
  simp only [hGeq] at cA cB cC
  refine ⟨fun s₁ hs₁ => ?_, ?_, ?_⟩
  · rw [stepA s₁]
    exact ENNReal.mul_lt_top hs.lt_top (cA s₁ hs₁)
  · have := ENNReal.Tendsto.const_mul cB (Or.inr hs)
    rw [stepC] at this
    refine this.congr' ?_
    exact Eventually.of_forall fun s₁ => (stepA s₁).symm
  · rw [stepA 1, cC, stepC]

end S_AutomorphicForm_lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_and_tendsto_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram
end P2MW
export P2MW.S_AutomorphicForm_lintegral_twistedCentralizer_mul_rpow_abs_algebraNorm_det_lt_top_and_tendsto_nhdsGT_one_of_map_coe_eq_smul_withDensity_gram (solution)
