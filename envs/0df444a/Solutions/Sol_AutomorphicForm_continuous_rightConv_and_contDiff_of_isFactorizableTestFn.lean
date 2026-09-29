-- Prove2me | solution 1 for AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ddcd2d35-47ff-502b-9401-df31466ddbc9

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn

open NumberField IsDedekindDomain AutomorphicForm MeasureTheory Topology Filter
open scoped Classical

noncomputable section

namespace RightConvRegularity

universe u

section Shape

private theorem exists_integrable_bound
    {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {P : Type u} [NormedAddCommGroup P] [ProperSpace P] {E' : Type u} [NormedAddCommGroup E']
    (H : P → α → E') (hH : Continuous fun p : P × α => H p.1 p.2) (z₀ : P)
    {S : Set α} (hS : IsCompact S) (hHS : ∀ z ∈ Metric.ball z₀ 1, ∀ a, a ∉ S → H z a = 0) :
    ∃ bound : α → ℝ, Integrable bound μ ∧ ∀ z ∈ Metric.ball z₀ 1, ∀ a, ‖H z a‖ ≤ bound a := by
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedBall z₀ 1).prod hS).exists_bound_of_continuousOn hH.continuousOn
  refine ⟨S.indicator fun _ => M, ?_, ?_⟩
  · exact (integrable_indicator_iff hS.isClosed.measurableSet).2
      (integrableOn_const hS.measure_lt_top.ne)
  · intro z hz a
    by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha]
      exact hM (z, a) ⟨Metric.ball_subset_closedBall hz, ha⟩
    · rw [Set.indicator_of_notMem ha, hHS z hz a ha, norm_zero]

private theorem integrable_of_vanish
    {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {P : Type u} [NormedAddCommGroup P] {E' : Type u} [NormedAddCommGroup E']
    (H : P → α → E') (hH : Continuous fun p : P × α => H p.1 p.2) (z₀ : P)
    {S : Set α} (hS : IsCompact S) (hHS : ∀ z ∈ Metric.ball z₀ 1, ∀ a, a ∉ S → H z a = 0)
    (z : P) (hz : z ∈ Metric.ball z₀ 1) : Integrable (H z) μ := by
  have hcz : Continuous (H z) := hH.comp (Continuous.prodMk continuous_const continuous_id)
  exact hcz.integrable_of_hasCompactSupport
    (HasCompactSupport.intro' hS hS.isClosed fun a ha => hHS z hz a ha)

private theorem continuous_shape {α : Type*} [TopologicalSpace α]
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E E' : Type u} [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedSpace ℝ E]
    [NormedSpace ℝ E'] (L : P →L[ℝ] X)
    (Ψ : X → E) (hΨ : Continuous Ψ) (T : α → E →L[ℝ] E') (hT : Continuous T)
    (c : α → X) (hc : Continuous c) :
    Continuous fun p : P × α => T p.2 (Ψ (c p.2 + L p.1)) :=
  (hT.comp continuous_snd).clm_apply
    (hΨ.comp ((hc.comp continuous_snd).add (L.continuous.comp continuous_fst)))

private theorem contDiff_integral_shape
    {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] (L : P →L[ℝ] X) (n : ℕ) :
    ∀ {E E' : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
      [NormedSpace ℝ E'] [CompleteSpace E']
      (Ψ : X → E) (_hΨ : ∀ m : ℕ, ContDiff ℝ m Ψ) (T : α → E →L[ℝ] E') (_hT : Continuous T)
      (c : α → X) (_hc : Continuous c)
      (_hsupp : ∀ z₀ : P, ∃ S : Set α, IsCompact S ∧
        ∀ z ∈ Metric.ball z₀ 1, ∀ a, a ∉ S → T a (Ψ (c a + L z)) = 0),
      ContDiff ℝ n fun z : P => ∫ a, T a (Ψ (c a + L z)) ∂μ := by
  induction n with
  | zero =>
    intro E E' _ _ _ _ _ Ψ hΨ T hT c hc hsupp
    rw [Nat.cast_zero, contDiff_zero]
    refine continuous_iff_continuousAt.2 fun z₀ => ?_
    obtain ⟨S, hS, hSz⟩ := hsupp z₀
    have hH := continuous_shape L Ψ (hΨ 0).continuous T hT c hc
    obtain ⟨bound, hbi, hb⟩ :=
      exists_integrable_bound (μ := μ) (fun z a => T a (Ψ (c a + L z))) hH z₀ hS hSz
    have hball : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ one_pos
    refine continuousAt_of_dominated (F := fun z a => T a (Ψ (c a + L z))) ?_ ?_ hbi ?_
    · exact eventually_of_mem hball fun z hz =>
        (integrable_of_vanish (μ := μ) (fun z a => T a (Ψ (c a + L z))) hH z₀ hS hSz z
          hz).aestronglyMeasurable
    · exact eventually_of_mem hball fun z hz => Eventually.of_forall (hb z hz)
    · refine Eventually.of_forall fun a => ?_
      exact ((T a).continuous.comp ((hΨ 0).continuous.comp
        (continuous_const.add L.continuous))).continuousAt
  | succ n ih =>
    intro E E' _ _ _ _ _ Ψ hΨ T hT c hc hsupp

    let T' : α → (X →L[ℝ] E) →L[ℝ] (P →L[ℝ] E') := fun a =>
      (ContinuousLinearMap.compL ℝ P E E' (T a)).comp ((ContinuousLinearMap.compL ℝ P X E).flip L)
    have hT'_apply : ∀ (a : α) (D : X →L[ℝ] E), T' a D = (T a).comp (D.comp L) := by
      intro a D
      simp only [T', ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.compL_apply]
    have hT' : Continuous T' :=
      ((ContinuousLinearMap.compL ℝ P E E').continuous.comp hT).clm_comp continuous_const
    have hΨ' : ∀ m : ℕ, ContDiff ℝ m (fderiv ℝ Ψ) := fun m =>
      (hΨ (m + 1)).fderiv_right (by norm_cast)
    have hderiv : ∀ (a : α) (z : P),
        HasFDerivAt (fun w : P => T a (Ψ (c a + L w))) (T' a (fderiv ℝ Ψ (c a + L z))) z := by
      intro a z
      rw [hT'_apply]
      have h1 : HasFDerivAt (fun w : P => c a + L w) L z := L.hasFDerivAt.const_add (c a)
      have h2 : HasFDerivAt Ψ (fderiv ℝ Ψ (c a + L z)) (c a + L z) :=
        (((hΨ 1).differentiable (by norm_cast)) (c a + L z)).hasFDerivAt
      exact (T a).hasFDerivAt.comp z (h2.comp z h1)
    have hsupp' : ∀ z₀ : P, ∃ S : Set α, IsCompact S ∧
        ∀ z ∈ Metric.ball z₀ 1, ∀ a, a ∉ S → T' a (fderiv ℝ Ψ (c a + L z)) = 0 := by
      intro z₀
      obtain ⟨S, hS, hSz⟩ := hsupp z₀
      refine ⟨S, hS, fun z hz a ha => ?_⟩
      rw [← (hderiv a z).fderiv]
      have hzero : (fun w : P => T a (Ψ (c a + L w))) =ᶠ[𝓝 z] fun _ => (0 : E') := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw using hSz w hw a ha
      rw [hzero.fderiv_eq]
      simp

    have hF' : ContDiff ℝ n fun z : P => ∫ a, T' a (fderiv ℝ Ψ (c a + L z)) ∂μ :=
      ih (fderiv ℝ Ψ) hΨ' T' hT' c hc hsupp'
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_hasFDerivAt.2
      ⟨fun z => ∫ a, T' a (fderiv ℝ Ψ (c a + L z)) ∂μ, hF', fun z₀ => ?_⟩
    obtain ⟨S, hS, hSz⟩ := hsupp z₀
    obtain ⟨S', hS', hSz'⟩ := hsupp' z₀
    have hH := continuous_shape L Ψ (hΨ 0).continuous T hT c hc
    have hH' := continuous_shape L (fderiv ℝ Ψ) (hΨ' 0).continuous T' hT' c hc
    obtain ⟨bound, hbi, hb⟩ :=
      exists_integrable_bound (μ := μ) (fun z a => T' a (fderiv ℝ Ψ (c a + L z))) hH' z₀ hS' hSz'
    have hball : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ one_pos
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (F := fun z a => T a (Ψ (c a + L z))) (F' := fun z a => T' a (fderiv ℝ Ψ (c a + L z)))
      (bound := bound) hball ?_ ?_ ?_ ?_ hbi ?_
    · exact eventually_of_mem hball fun z hz =>
        (integrable_of_vanish (μ := μ) (fun z a => T a (Ψ (c a + L z))) hH z₀ hS hSz z
          hz).aestronglyMeasurable
    · exact integrable_of_vanish (μ := μ) (fun z a => T a (Ψ (c a + L z))) hH z₀ hS hSz z₀
        (Metric.mem_ball_self one_pos)
    · exact (integrable_of_vanish (μ := μ) (fun z a => T' a (fderiv ℝ Ψ (c a + L z))) hH' z₀ hS'
        hSz' z₀ (Metric.mem_ball_self one_pos)).aestronglyMeasurable
    · exact Eventually.of_forall fun a z hz => hb z hz a
    · exact Eventually.of_forall fun a z _ => hderiv a z

end Shape

private theorem entry_affine {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) (a : R)
    (i j : Fin 2) :
    (A * !![1, a; 0, 1] * B) i j =
      (A * B) i j + a * (A * (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) R) * B) i j := by
  have h : (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) R) =
      1 + a • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.add_apply, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

section Slice

variable (K : Type) [Field K] [NumberField K]

private abbrev instNG : NormedAddCommGroup (mixedEmbedding.mixedSpace K) := inferInstance
attribute [local instance] instNG
private abbrev instNS : NormedSpace ℝ (mixedEmbedding.mixedSpace K) := inferInstance
attribute [local instance] instNS

private abbrev Par : Type :=
  (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) ×
    ((Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) × mixedEmbedding.mixedSpace K)

private def sliceL : mixedEmbedding.mixedSpace K →L[ℝ] Par K :=
  (ContinuousLinearMap.inr ℝ (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)
      ((Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) × mixedEmbedding.mixedSpace K)).comp
    (ContinuousLinearMap.inr ℝ (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)
      (mixedEmbedding.mixedSpace K))

omit [NumberField K] in
private theorem sliceL_apply (z : mixedEmbedding.mixedSpace K) : sliceL K z = (0, (0, z)) := by
  simp [sliceL]

private def slicePsi (Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ) (q : Par K) : ℂ :=
  Φ fun i j => q.1 i j + q.2.2 * q.2.1 i j

private theorem contDiff_entries (m : ℕ) :
    ContDiff ℝ m fun q : Par K =>
      (fun i j => q.1 i j + q.2.2 * q.2.1 i j : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have h1 : ContDiff ℝ m fun q : Par K => q.1 i j :=
    ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i)).comp contDiff_fst
  have h2 : ContDiff ℝ m fun q : Par K => q.2.1 i j :=
    ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i)).comp (contDiff_fst.comp contDiff_snd)
  exact h1.add ((contDiff_snd.comp contDiff_snd).mul h2)

private theorem contDiff_slicePsi (Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (m : ℕ) : ContDiff ℝ m (slicePsi K Φ) :=
  (contDiff_infty.1 hΦ m).comp (contDiff_entries K m)

omit [NumberField K] in
private theorem slicePsi_add (Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (C D : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) (z : mixedEmbedding.mixedSpace K) :
    slicePsi K Φ ((C, (D, 0)) + sliceL K z) = Φ fun i j => C i j + z * D i j := by
  simp [slicePsi, sliceL_apply]

private theorem shape_applies {α : Type} [TopologicalSpace α] [T2Space α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsFiniteMeasureOnCompacts μ]
    (Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (wt : α → ℂ) (hwt : Continuous wt)
    (cd : α → (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) ×
      (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)) (hcd : Continuous cd)
    (hsupp : ∀ z₀ : mixedEmbedding.mixedSpace K, ∃ S : Set α, IsCompact S ∧
      ∀ z ∈ Metric.ball z₀ 1, ∀ a, a ∉ S →
        wt a * Φ (fun i j => (cd a).1 i j + z * (cd a).2 i j) = 0) (m : ℕ) :
    ContDiff ℝ m fun z : mixedEmbedding.mixedSpace K =>
      ∫ a, wt a * Φ (fun i j => (cd a).1 i j + z * (cd a).2 i j) ∂μ := by
  let T : α → ℂ →L[ℝ] ℂ := fun a => ContinuousLinearMap.mul ℝ ℂ (wt a)
  have hT : Continuous T := (ContinuousLinearMap.mul ℝ ℂ).continuous.comp hwt
  let cc : α → Par K := fun a => ((cd a).1, ((cd a).2, 0))
  have hcc : Continuous cc :=
    (continuous_fst.comp hcd).prodMk ((continuous_snd.comp hcd).prodMk continuous_const)
  have hid : ∀ (z : mixedEmbedding.mixedSpace K) (a : α),
      T a (slicePsi K Φ (cc a + sliceL K z)) =
        wt a * Φ (fun i j => (cd a).1 i j + z * (cd a).2 i j) := by
    intro z a
    simp only [T, cc, ContinuousLinearMap.mul_apply', slicePsi_add]
  have hsupp' : ∀ z₀ : mixedEmbedding.mixedSpace K, ∃ S : Set α, IsCompact S ∧
      ∀ z ∈ Metric.ball z₀ 1, ∀ a, a ∉ S → T a (slicePsi K Φ (cc a + sliceL K z)) = 0 := by
    intro z₀
    obtain ⟨S, hS, h⟩ := hsupp z₀
    exact ⟨S, hS, fun z hz a ha => by rw [hid]; exact h z hz a ha⟩
  have hkey : (fun z : mixedEmbedding.mixedSpace K =>
      ∫ a, wt a * Φ (fun i j => (cd a).1 i j + z * (cd a).2 i j) ∂μ) =
      fun z => ∫ a, T a (slicePsi K Φ (cc a + sliceL K z)) ∂μ := by
    funext z
    simp_rw [hid]
  rw [hkey]
  exact contDiff_integral_shape (sliceL K) m (slicePsi K Φ) (contDiff_slicePsi K Φ hΦ) T hT cc hcc
    hsupp'

private def nz (z : mixedEmbedding.mixedSpace K) : AdelicGL2 (𝓞 K) K :=
  unipotentGL2 (R := AdeleRing (𝓞 K) K) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0)

omit [NumberField K] in
private theorem continuous_symm_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  refine continuous_pi fun v => ?_
  by_cases hv : v.IsReal
  · have h : (fun x : mixedEmbedding.mixedSpace K =>
          (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x v) =
        fun x => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (x.1 ⟨v, hv⟩) := by
      funext x
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      have hx := congrArg (fun p : mixedEmbedding.mixedSpace K => p.1 ⟨v, hv⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply x)
      exact hx
    rw [h]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have h : (fun x : mixedEmbedding.mixedSpace K =>
          (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x v) =
        fun x => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm
          (x.2 ⟨v, hc⟩) := by
      funext x
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      have hx := congrArg (fun p : mixedEmbedding.mixedSpace K => p.2 ⟨v, hc⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply x)
      exact hx
    rw [h]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

private theorem continuous_nz : Continuous (nz K) := by
  have h : Continuous fun z : mixedEmbedding.mixedSpace K =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) : AdeleRing (𝓞 K) K) :=
    (continuous_symm_ringEquiv_mixedSpace K).prodMk continuous_const
  exact continuous_unipotentGL2.comp h

private theorem glArch_unipotent (a : InfiniteAdeleRing K) (b : FiniteAdeleRing (𝓞 K) K) :
    AdelicLevel.glArch (𝓞 K) K (unipotentGL2 ((a, b) : AdeleRing (𝓞 K) K)) = unipotentGL2 a := by
  ext i j
  rw [AdelicLevel.glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem glFin_unipotent (a : InfiniteAdeleRing K) (b : FiniteAdeleRing (𝓞 K) K) :
    AdelicLevel.glFin (𝓞 K) K (unipotentGL2 ((a, b) : AdeleRing (𝓞 K) K)) = unipotentGL2 b := by
  ext i j
  rw [AdelicLevel.glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

omit [NumberField K] in
private theorem unipotentGL2_inv' (a : InfiniteAdeleRing K) :
    (unipotentGL2 a)⁻¹ = unipotentGL2 (-a) :=
  Units.ext rfl

private def sliceCD (g y : AdelicGL2 (𝓞 K) K) :
    (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) × (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :=
  (fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace K
      (((((AdelicLevel.glArch (𝓞 K) K g)⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
        (AdelicLevel.glArch (𝓞 K) K y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) i j),
   fun i j => - InfiniteAdeleRing.ringEquiv_mixedSpace K
      (((((AdelicLevel.glArch (𝓞 K) K g)⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) *
        (AdelicLevel.glArch (𝓞 K) K y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) i j))

private theorem continuous_sliceCD (g : AdelicGL2 (𝓞 K) K) : Continuous (sliceCD K g) := by
  have he := AdelicBox.continuous_ringEquiv_mixedSpace K
  have hB : Continuous fun y : AdelicGL2 (𝓞 K) K =>
      (AdelicLevel.glArch (𝓞 K) K y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    Units.continuous_val.comp (AdelicLevel.continuous_glArch (𝓞 K) K)
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j =>
      he.comp ((continuous_const.matrix_mul hB).matrix_elem i j)
  · exact continuous_pi fun i => continuous_pi fun j =>
      (he.comp ((continuous_const.matrix_mul hB).matrix_elem i j)).neg

private theorem archEntries_slice (g y : AdelicGL2 (𝓞 K) K) (z : mixedEmbedding.mixedSpace K) :
    archEntries K (AdelicLevel.glArch (𝓞 K) K ((nz K z * g)⁻¹ * y)) =
      fun i j => (sliceCD K g y).1 i j + z * (sliceCD K g y).2 i j := by
  funext i j
  simp only [sliceCD]
  have h1 : AdelicLevel.glArch (𝓞 K) K ((nz K z * g)⁻¹ * y) =
      (AdelicLevel.glArch (𝓞 K) K g)⁻¹ *
        unipotentGL2 (-(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z) *
        AdelicLevel.glArch (𝓞 K) K y := by
    rw [mul_inv_rev, map_mul, map_mul, map_inv, map_inv, nz, glArch_unipotent, unipotentGL2_inv']
  rw [archEntries_apply, h1, Units.val_mul, Units.val_mul, unipotentGL2_coe, entry_affine, map_add,
    map_mul, map_neg, RingEquiv.apply_symm_apply, neg_mul, ← mul_neg]

private theorem glFin_slice (g y : AdelicGL2 (𝓞 K) K) (z : mixedEmbedding.mixedSpace K) :
    AdelicLevel.glFin (𝓞 K) K ((nz K z * g)⁻¹ * y) =
      (AdelicLevel.glFin (𝓞 K) K g)⁻¹ * AdelicLevel.glFin (𝓞 K) K y := by
  rw [mul_inv_rev, map_mul, map_mul, map_inv, map_inv, nz, glFin_unipotent, unipotentGL2_zero,
    inv_one, mul_one]

private theorem contDiff_slice (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) (hfs : HasCompactSupport f)
    (g : AdelicGL2 (𝓞 K) K) (m : ℕ) :
    ContDiff ℝ m fun z : mixedEmbedding.mixedSpace K => rightConv K φ f (nz K z * g) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfaΦ⟩, -⟩, ⟨hff, -⟩, hfeq⟩ := hf
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  set wt : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
    φ y * ff ((AdelicLevel.glFin (𝓞 K) K g)⁻¹ * AdelicLevel.glFin (𝓞 K) K y) with hwt_def
  have hwt : Continuous wt :=
    hcont.mul (hff.continuous.comp (continuous_const.mul (AdelicLevel.continuous_glFin (𝓞 K) K)))

  have hid : ∀ (z : mixedEmbedding.mixedSpace K) (y : AdelicGL2 (𝓞 K) K),
      φ y * f ((nz K z * g)⁻¹ * y) =
        wt y * Φ (fun i j => (sliceCD K g y).1 i j + z * (sliceCD K g y).2 i j) := by
    intro z y
    rw [hfeq, hfaΦ, archEntries_slice, glFin_slice]
    simp only [hwt_def]
    ring

  have hsupp : ∀ z₀ : mixedEmbedding.mixedSpace K, ∃ S : Set (AdelicGL2 (𝓞 K) K), IsCompact S ∧
      ∀ z ∈ Metric.ball z₀ 1, ∀ y, y ∉ S →
        wt y * Φ (fun i j => (sliceCD K g y).1 i j + z * (sliceCD K g y).2 i j) = 0 := by
    intro z₀
    refine ⟨(fun p : mixedEmbedding.mixedSpace K × AdelicGL2 (𝓞 K) K => nz K p.1 * g * p.2) ''
      (Metric.closedBall z₀ 1 ×ˢ tsupport f), ?_, ?_⟩
    · exact ((isCompact_closedBall z₀ 1).prod hfs.isCompact).image
        ((((continuous_nz K).comp continuous_fst).mul continuous_const).mul continuous_snd)
    · intro z hz y hy
      rw [← hid]
      have hfy : f ((nz K z * g)⁻¹ * y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hx
        exact hy ⟨(z, (nz K z * g)⁻¹ * y), ⟨Metric.ball_subset_closedBall hz, hx⟩,
          mul_inv_cancel_left (nz K z * g) y⟩
      rw [hfy, mul_zero]

  have hkey : (fun z : mixedEmbedding.mixedSpace K => rightConv K φ f (nz K z * g)) =
      fun z => ∫ y, wt y * Φ (fun i j => (sliceCD K g y).1 i j + z * (sliceCD K g y).2 i j)
        ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    funext z
    simp_rw [← hid]
    rw [← integral_mul_left_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
      (fun y => φ y * f ((nz K z * g)⁻¹ * y)) (nz K z * g)]
    simp only [inv_mul_cancel_left]
    rfl
  rw [hkey]
  exact shape_applies K (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) Φ hΦ wt hwt (sliceCD K g)
    (continuous_sliceCD K g) hsupp m

private theorem continuous_rightConv (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    Continuous (rightConv K φ f) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hint : ∀ h : AdelicGL2 (𝓞 K) K,
      Integrable (fun x => φ (h * x) * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro h
    have hc : Continuous fun x : AdelicGL2 (𝓞 K) K => φ (h * x) * f x :=
      (hcont.comp (continuous_const.mul continuous_id)).mul hfc
    have hs : HasCompactSupport fun x : AdelicGL2 (𝓞 K) K => φ (h * x) * f x := by
      refine HasCompactSupport.intro' hfs.isCompact (isClosed_tsupport f) fun x hx => ?_
      show φ (h * x) * f x = 0
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    exact hc.integrable_of_hasCompactSupport hs
  have hnorm : Integrable (fun x => ‖f x‖) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (hfc.integrable_of_hasCompactSupport hfs).norm
  set M : ℝ := ∫ x, ‖f x‖ ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) with hM
  have hM0 : 0 ≤ M := integral_nonneg fun x => norm_nonneg _
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hM1 : 0 < M + 1 := by linarith
  set δ : ℝ := ε / (M + 1) with hδ
  have hδpos : 0 < δ := div_pos hε hM1
  have hev : ∀ᶠ h in 𝓝 g₀, ∀ x ∈ tsupport f, dist (φ (h * x)) (φ (g₀ * x)) < δ := by
    refine hfs.isCompact.eventually_forall_of_forall_eventually fun x _ => ?_
    have hc : Continuous fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        dist (φ (p.1 * p.2)) (φ (g₀ * p.2)) :=
      (hcont.comp (continuous_fst.mul continuous_snd)).dist
        (hcont.comp (continuous_const.mul continuous_snd))
    have h0 : dist (φ ((g₀, x).1 * (g₀, x).2)) (φ (g₀ * (g₀, x).2)) < δ := by
      simpa using hδpos
    exact hc.continuousAt.eventually_lt continuousAt_const h0
  filter_upwards [hev] with h hh
  have hsub : rightConv K φ f h - rightConv K φ f g₀ =
      ∫ x, (φ (h * x) - φ (g₀ * x)) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    simp_rw [sub_mul]
    rw [integral_sub (hint h) (hint g₀)]
    rfl
  rw [dist_eq_norm, hsub]
  calc ‖∫ x, (φ (h * x) - φ (g₀ * x)) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ ∫ x, δ * ‖f x‖ ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
        refine norm_integral_le_of_norm_le (hnorm.const_mul δ) (Eventually.of_forall fun x => ?_)
        rw [norm_mul]
        by_cases hx : x ∈ tsupport f
        · exact mul_le_mul_of_nonneg_right (by rw [← dist_eq_norm]; exact (hh x hx).le)
            (norm_nonneg _)
        · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero, mul_zero]
    _ = δ * M := integral_const_mul δ _
    _ < δ * (M + 1) := mul_lt_mul_of_pos_left (lt_add_one M) hδpos
    _ = ε := by rw [hδ]; field_simp

end Slice

end RightConvRegularity

end

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    Continuous (rightConv K φ f) ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        ContDiff ℝ (Module.finrank ℚ K + 1) (fun z : mixedEmbedding.mixedSpace K =>
          rightConv K φ f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g)) := by
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf
  refine ⟨RightConvRegularity.continuous_rightConv K φ hcont f hfc hfs, fun g => ?_⟩
  have h := RightConvRegularity.contDiff_slice K φ hcont f hf hfs g (Module.finrank ℚ K + 1)
  exact_mod_cast h

end S_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn (solution)
