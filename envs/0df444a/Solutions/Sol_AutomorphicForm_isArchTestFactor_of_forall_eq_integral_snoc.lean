-- Prove2me | solution 1 for AutomorphicForm.isArchTestFactor_of_forall_eq_integral_snoc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/00548ec3-4238-5136-8e8e-641052005277

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isArchTestFactor_of_forall_eq_integral_snoc

set_option autoImplicit false

open NumberField MeasureTheory
open scoped Classical

namespace ArchIdentification

variable (F : Type) [Field F] [NumberField F]

private theorem secondCountableTopology_infiniteAdeleRing_mixed : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

open scoped Classical in
omit [NumberField F] in
private theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F => InfiniteAdeleRing.ringEquiv_mixedSpace F x
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

open scoped Classical in
private theorem isOpenMap_ringEquiv_mixedSpace : IsOpenMap (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  haveI := secondCountableTopology_infiniteAdeleRing_mixed F
  exact ((InfiniteAdeleRing.ringEquiv_mixedSpace F :
      InfiniteAdeleRing F →+* mixedEmbedding.mixedSpace F).toAddMonoidHom).isOpenMap_of_sigmaCompact
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).surjective (continuous_ringEquiv_mixedSpace F)

open scoped Classical in

private noncomputable def archMixedHomeomorph : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv.toHomeomorphOfContinuousOpen
    (continuous_ringEquiv_mixedSpace F) (isOpenMap_ringEquiv_mixedSpace F)

open scoped Classical in
private theorem coe_archMixedHomeomorph : ⇑(archMixedHomeomorph F) = ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) := rfl

open scoped Classical in
private theorem continuous_archMixedHomeomorph_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm :=
  (archMixedHomeomorph F).symm.continuous

end ArchIdentification

namespace EntryLocus

open AutomorphicForm

section Entries

variable (F : Type) [Field F]

open scoped Classical in
private theorem continuous_archEntries : Continuous (archEntries F) := by
  have hc : Continuous fun x : InfiniteAdeleRing F => InfiniteAdeleRing.ringEquiv_mixedSpace F x := by
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := Units.continuous_val
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact hc.comp (hval.matrix_elem i j)

end Entries

end EntryLocus

namespace GLCarrierFacts

section GLCarrier

variable (A : Type) [CommRing A] [TopologicalSpace A]

private theorem secondCountableTopology_gl [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private theorem locallyCompactSpace_gl [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

private theorem sigmaCompactSpace_gl [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A] : SigmaCompactSpace (GL (Fin 2) A) := by
  haveI := locallyCompactSpace_gl A
  haveI := secondCountableTopology_gl A
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

end GLCarrier

end GLCarrierFacts

namespace FibreSmoothing

open MeasureTheory Filter Topology
open scoped ENNReal

variable {α : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α]
  [T2Space α] {ν : Measure α}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

private noncomputable def partialDeriv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (Ξ : V × M → F)
    (p : V × M) :
    M →L[ℝ] F :=
  (fderiv ℝ Ξ p).comp (ContinuousLinearMap.inr ℝ V M)

omit [FiniteDimensional ℝ M] in
private theorem contDiff_partialDeriv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ξ : V × M → F}
    (hΞ : ContDiff ℝ (⊤ : ℕ∞) Ξ) : ContDiff ℝ (⊤ : ℕ∞) (partialDeriv Ξ) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Ξ) := (contDiff_infty_iff_fderiv.1 hΞ).2
  show ContDiff ℝ (⊤ : ℕ∞) fun p => (fderiv ℝ Ξ p).comp (ContinuousLinearMap.inr ℝ V M)
  exact ContDiff.clm_comp h1 contDiff_const

omit [FiniteDimensional ℝ M] in
private theorem hasFDerivAt_partial {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ξ : V × M → F}
    (hΞ : ContDiff ℝ (⊤ : ℕ∞) Ξ) (v : V) (m : M) :
    HasFDerivAt (fun m' => Ξ (v, m')) (partialDeriv Ξ (v, m)) m := by
  have h1 : HasFDerivAt Ξ (fderiv ℝ Ξ (v, m)) (v, m) :=
    ((ContDiff.differentiable hΞ (by simp)) (v, m)).hasFDerivAt
  exact h1.comp m (hasFDerivAt_prodMk_right v m)

omit [FiniteDimensional ℝ M] in
private theorem partialDeriv_eq_zero_of_forall_eq_zero {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ξ : V × M → F}
    (hΞ : ContDiff ℝ (⊤ : ℕ∞) Ξ) {v : V} (hv : ∀ m, Ξ (v, m) = 0) (m : M) : partialDeriv Ξ (v, m) = 0 := by
  have h1 := hasFDerivAt_partial hΞ v m
  have h2 : (fun m' => Ξ (v, m')) = fun _ => (0 : F) := funext hv
  rw [h2] at h1
  exact h1.unique (hasFDerivAt_const (0 : F) m)

section Bounds

variable {k : Set α} (hk : IsCompact k) {u : α → V} (hu : Continuous u)
include hk hu

omit [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α] [T2Space α] [NormedSpace ℝ V] in
private theorem exists_bound {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Θ : V × M → F} (hΘ : Continuous Θ)
    (hsupp : ∀ c, c ∉ k → ∀ m, Θ (u c, m) = 0) (m₀ : M) :
    ∃ C : ℝ, ∀ c, ∀ m ∈ Metric.closedBall m₀ 1, ‖Θ (u c, m)‖ ≤ k.indicator (fun _ => C) c := by
  have hcont : ContinuousOn (fun p : α × M => Θ (u p.1, p.2)) (k ×ˢ Metric.closedBall m₀ 1) :=
    (hΘ.comp ((hu.comp continuous_fst).prodMk continuous_snd)).continuousOn
  obtain ⟨C, hC⟩ := (hk.prod (isCompact_closedBall m₀ 1)).exists_bound_of_continuousOn hcont
  refine ⟨C, fun c m hm => ?_⟩
  by_cases hc : c ∈ k
  · rw [Set.indicator_of_mem hc]
    exact hC (c, m) ⟨hc, hm⟩
  · rw [Set.indicator_of_notMem hc, hsupp c hc m, norm_zero]

omit [SecondCountableTopology α] [NormedAddCommGroup V] [NormedSpace ℝ V] hu in
private theorem integrable_indicator_const (hνk : ν k ≠ ∞) (C : ℝ) : Integrable (k.indicator fun _ => C) ν :=
  (integrableOn_const (C := C) hνk).integrable_indicator hk.isClosed.measurableSet

omit [T2Space α] [NormedSpace ℝ V] [NormedSpace ℝ M] [FiniteDimensional ℝ M] hk in
private theorem aestronglyMeasurable_slice {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {Θ : V × M → F}
    (hΘ : Continuous Θ) (m : M) : AEStronglyMeasurable (fun c => Θ (u c, m)) ν :=
  (hΘ.comp (hu.prodMk continuous_const)).aestronglyMeasurable

omit [NormedSpace ℝ V] in
private theorem continuous_integral {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (hνk : ν k ≠ ∞) {Θ : V × M → F}
    (hΘ : Continuous Θ) (hsupp : ∀ c, c ∉ k → ∀ m, Θ (u c, m) = 0) :
    Continuous fun m => ∫ c, Θ (u c, m) ∂ν := by
  refine continuous_iff_continuousAt.2 fun m₀ => ?_
  obtain ⟨C, hC⟩ := exists_bound hk hu hΘ hsupp m₀
  refine continuousAt_of_dominated (bound := k.indicator fun _ => C) ?_ ?_ (integrable_indicator_const hk hνk C) ?_
  · exact Eventually.of_forall fun m => aestronglyMeasurable_slice hu hΘ m
  · filter_upwards [Metric.closedBall_mem_nhds m₀ one_pos] with m hm
    exact Eventually.of_forall fun c => hC c m hm
  · exact Eventually.of_forall fun c => (hΘ.comp (continuous_const.prodMk continuous_id)).continuousAt

private theorem hasFDerivAt_integral {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hνk : ν k ≠ ∞)
    {Ξ : V × M → F} (hΞ : ContDiff ℝ (⊤ : ℕ∞) Ξ) (hsupp : ∀ c, c ∉ k → ∀ m, Ξ (u c, m) = 0) (m₀ : M) :
    HasFDerivAt (fun m => ∫ c, Ξ (u c, m) ∂ν) (∫ c, partialDeriv Ξ (u c, m₀) ∂ν) m₀ := by
  have hΞ' : ContDiff ℝ (⊤ : ℕ∞) (partialDeriv Ξ) := contDiff_partialDeriv hΞ
  have hsupp' : ∀ c, c ∉ k → ∀ m, partialDeriv Ξ (u c, m) = 0 := fun c hc m =>
    partialDeriv_eq_zero_of_forall_eq_zero hΞ (hsupp c hc) m
  obtain ⟨C, hC⟩ := exists_bound hk hu (ContDiff.continuous hΞ) hsupp m₀
  obtain ⟨C', hC'⟩ := exists_bound hk hu (ContDiff.continuous hΞ') hsupp' m₀
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun m c => partialDeriv Ξ (u c, m))
    (bound := k.indicator fun _ => C') (Metric.closedBall_mem_nhds m₀ one_pos) ?_ ?_ ?_ ?_
    (integrable_indicator_const hk hνk C') ?_
  · exact Eventually.of_forall fun m => aestronglyMeasurable_slice hu (ContDiff.continuous hΞ) m
  · refine (integrable_indicator_const hk hνk C).mono'
      (aestronglyMeasurable_slice hu (ContDiff.continuous hΞ) m₀) ?_
    exact Eventually.of_forall fun c => hC c m₀ (Metric.mem_closedBall_self zero_le_one)
  · exact aestronglyMeasurable_slice hu (ContDiff.continuous hΞ') m₀
  · exact Eventually.of_forall fun c m hm => hC' c m hm
  · exact Eventually.of_forall fun c m _ => hasFDerivAt_partial hΞ (u c) m

private theorem contDiff_integral_nat (hνk : ν k ≠ ∞) (j : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Ξ : V × M → F),
      ContDiff ℝ (⊤ : ℕ∞) Ξ → (∀ c, c ∉ k → ∀ m, Ξ (u c, m) = 0) →
        ContDiff ℝ j fun m => ∫ c, Ξ (u c, m) ∂ν := by
  induction j with
  | zero =>
    intro F _ _ _ Ξ hΞ hsupp
    exact contDiff_zero.2 (continuous_integral hk hu hνk (ContDiff.continuous hΞ) hsupp)
  | succ j ih =>
    intro F _ _ _ Ξ hΞ hsupp
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨fun m => ∫ c, partialDeriv Ξ (u c, m) ∂ν, ?_, ?_⟩
    · exact ih (M →L[ℝ] F) (partialDeriv Ξ) (contDiff_partialDeriv hΞ) fun c hc m =>
        partialDeriv_eq_zero_of_forall_eq_zero hΞ (hsupp c hc) m
    · exact fun m₀ => hasFDerivAt_integral hk hu hνk hΞ hsupp m₀

private theorem contDiff_integral (hνk : ν k ≠ ∞) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {Ξ : V × M → F} (hΞ : ContDiff ℝ (⊤ : ℕ∞) Ξ) (hsupp : ∀ c, c ∉ k → ∀ m, Ξ (u c, m) = 0) :
    ContDiff ℝ (⊤ : ℕ∞) fun m => ∫ c, Ξ (u c, m) ∂ν :=
  contDiff_infty.2 fun j => contDiff_integral_nat hk hu hνk j F Ξ hΞ hsupp

end Bounds

end FibreSmoothing

namespace EntryLocus

open AutomorphicForm

variable (K : Type) [Field K]

private abbrev EntrySpace : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

private def DetOk (m : EntrySpace K) : Prop :=
  (∀ w, ((Matrix.of m).det).1 w ≠ 0) ∧ ∀ w, ((Matrix.of m).det).2 w ≠ 0

private theorem isOpen_detOk [NumberField K] : IsOpen {m : EntrySpace K | DetOk K m} := by
  have hdet : Continuous fun m : EntrySpace K => (Matrix.of m).det :=
    Continuous.matrix_det (continuous_id : Continuous fun m : EntrySpace K => m)
  have h1 : {m : EntrySpace K | DetOk K m} =
      (⋂ w, {m : EntrySpace K | ((Matrix.of m).det).1 w ≠ 0}) ∩
        ⋂ w, {m : EntrySpace K | ((Matrix.of m).det).2 w ≠ 0} := by
    ext m
    simp only [DetOk, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h1]
  refine IsOpen.inter (isOpen_iInter_of_finite fun w => ?_) (isOpen_iInter_of_finite fun w => ?_)
  · exact isOpen_ne.preimage ((continuous_apply w).comp (continuous_fst.comp hdet))
  · exact isOpen_ne.preimage ((continuous_apply w).comp (continuous_snd.comp hdet))

private theorem detOk_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) : DetOk K (archEntries K g) := by
  have hof : Matrix.of (archEntries K g) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K →+* mixedEmbedding.mixedSpace K).mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
    exact Matrix.ext fun i j => rfl
  have hunit : IsUnit (Matrix.of (archEntries K g)).det := by
    rw [hof, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).map _
  refine ⟨fun w => ?_, fun w => ?_⟩
  · exact ((hunit.map (RingHom.fst _ _)).map (Pi.evalRingHom _ w)).ne_zero
  · exact ((hunit.map (RingHom.snd _ _)).map (Pi.evalRingHom _ w)).ne_zero

variable {K}

private theorem exists_smooth_cutoff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C U : Set E} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∀ t ∈ C, χ t = 1 := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : E)
  have hW : IsOpen (U ∩ Metric.ball (0 : E) (R + 1)) := hU.inter Metric.isOpen_ball
  have hCW : C ⊆ U ∩ Metric.ball (0 : E) (R + 1) := fun t ht =>
    ⟨hCU ht, Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 (hR ht)) (by linarith))⟩
  obtain ⟨g, hg_supp, hg_smooth, hg_range⟩ := hW.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hg_cont : Continuous g := hg_smooth.continuous
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t => (hg_range ⟨t, rfl⟩).1
  obtain ⟨ε, hε, hεC⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ C, ε ≤ g t := by
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · exact ⟨1, one_pos, fun t ht => by simp [hCe] at ht⟩
    · obtain ⟨t₀, ht₀, hmin⟩ := hC.exists_isMinOn hCne hg_cont.continuousOn
      have h0 : g t₀ ≠ 0 := by
        have : t₀ ∈ Function.support g := by rw [hg_supp]; exact hCW ht₀
        exact this
      exact ⟨g t₀, lt_of_le_of_ne (hg_nonneg t₀) (Ne.symm h0), fun t ht => hmin ht⟩
  refine ⟨fun t => Real.smoothTransition (2 / ε * g t - 1), ?_, ?_, ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul hg_smooth).sub contDiff_const)
  · have hsub : tsupport (fun t => Real.smoothTransition (2 / ε * g t - 1)) ⊆ {t | ε / 2 ≤ g t} := by
      refine closure_minimal ?_ (isClosed_le continuous_const hg_cont)
      intro t ht
      have hpos : 0 < 2 / ε * g t - 1 := by
        by_contra hle
        exact ht (Real.smoothTransition.zero_of_nonpos (not_lt.1 hle))
      show ε / 2 ≤ g t
      have h2 : 2 / ε * g t > 1 := by linarith
      rw [div_mul_eq_mul_div, gt_iff_lt, lt_div_iff₀ hε] at h2
      linarith
    have hcl : {t : E | ε / 2 ≤ g t} ⊆ Metric.closedBall (0 : E) (R + 1) := by
      intro t ht
      have hmem : t ∈ Function.support g := fun h0 => by
        have : ε / 2 ≤ (0 : ℝ) := by simpa [h0] using ht
        linarith
      rw [hg_supp] at hmem
      exact Metric.ball_subset_closedBall hmem.2
    exact (isCompact_closedBall (0 : E) (R + 1)).of_isClosed_subset (isClosed_tsupport _) (hsub.trans hcl)
  · intro t ht
    have hsub : tsupport (fun t => Real.smoothTransition (2 / ε * g t - 1)) ⊆ {t | ε / 2 ≤ g t} := by
      refine closure_minimal ?_ (isClosed_le continuous_const hg_cont)
      intro t ht
      have hpos : 0 < 2 / ε * g t - 1 := by
        by_contra hle
        exact ht (Real.smoothTransition.zero_of_nonpos (not_lt.1 hle))
      show ε / 2 ≤ g t
      have h2 : 2 / ε * g t > 1 := by linarith
      rw [div_mul_eq_mul_div, gt_iff_lt, lt_div_iff₀ hε] at h2
      linarith
    have hmem : t ∈ Function.support g := fun h0 => by
      have : ε / 2 ≤ (0 : ℝ) := by simpa [h0] using hsub ht
      linarith
    rw [hg_supp] at hmem
    exact hmem.1
  · intro t ht
    apply Real.smoothTransition.one_of_one_le
    have h1 : ε ≤ g t := hεC t ht
    have h2 : 2 / ε * ε = 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (div_pos two_pos hε))]

private theorem exists_smooth_rep_generic {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type} [TopologicalSpace X] {e : X → E} (he : Continuous e) {U : Set E} (hU : IsOpen U)
    (heU : ∀ x, e x ∈ U) {Φ : X → ℂ} {Ψ : E → ℂ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΦΨ : ∀ x, Φ x = Ψ (e x))
    (hΦc : HasCompactSupport Φ) :
    ∃ Ψ₁ : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ₁ ∧ HasCompactSupport Ψ₁ ∧ tsupport Ψ₁ ⊆ U ∧ ∀ x, Φ x = Ψ₁ (e x) := by
  have hC : IsCompact (e '' tsupport Φ) := hΦc.image he
  have hCU : e '' tsupport Φ ⊆ U := by
    rintro _ ⟨x, -, rfl⟩
    exact heU x
  obtain ⟨χ, hχ, hχc, hχU, hχ1⟩ := exists_smooth_cutoff hC hU hCU
  refine ⟨fun t => χ t • Ψ t, ContDiff.smul hχ hΨ, ?_, ?_, fun x => ?_⟩
  · exact hχc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left χ Ψ)
  · exact (tsupport_smul_subset_left χ Ψ).trans hχU
  · by_cases hx : x ∈ tsupport Φ
    · have h1 : χ (e x) = 1 := hχ1 _ ⟨x, hx, rfl⟩
      show Φ x = χ (e x) • Ψ (e x)
      rw [h1, one_smul]
      exact hΦΨ x
    · have h0 : Φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have h0' : Ψ (e x) = 0 := by rw [← h0]; exact (hΦΨ x).symm
      show Φ x = χ (e x) • Ψ (e x)
      rw [h0, h0', smul_zero]

variable (K)

private def UnitLocus (n : ℕ) : Set (Fin (n + 1) → Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :=
  {t | ∀ k, DetOk K (t k)}

private theorem isOpen_unitLocus [NumberField K] (n : ℕ) : IsOpen (UnitLocus K n) := by
  have h : UnitLocus K n =
      ⋂ k, (fun t : Fin (n + 1) → Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K => t k) ⁻¹' {m | DetOk K m} := by
    ext t
    simp only [UnitLocus, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact isOpen_iInter_of_finite fun k => (isOpen_detOk K).preimage (continuous_apply k)

private noncomputable def entryTuple (n : ℕ) (x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K)) :
    Fin (n + 1) → Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K :=
  fun k => archEntries K (x k)

private theorem entryTuple_mem_unitLocus (n : ℕ) (x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K)) :
    entryTuple K n x ∈ UnitLocus K n :=
  fun k => detOk_archEntries K (x k)

private theorem continuous_entryTuple (n : ℕ) (hE : Continuous (archEntries K)) : Continuous (entryTuple K n) :=
  continuous_pi fun k => hE.comp (continuous_apply k)

end EntryLocus

namespace EntryLocus

open AutomorphicForm

section Inverse

variable (K : Type) [Field K]

private noncomputable def detInv (d : mixedEmbedding.mixedSpace K) : mixedEmbedding.mixedSpace K :=
  (fun w => (d.1 w)⁻¹, fun w => (d.2 w)⁻¹)

private theorem detInv_mul_det {m : EntrySpace K} (h : DetOk K m) :
    detInv K (Matrix.of m).det * (Matrix.of m).det = 1 := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · simp [detInv, h.1 w]
  · simp [detInv, h.2 w]

private noncomputable abbrev entriesInv : mixedEmbedding.mixedSpace K →+* InfiniteAdeleRing K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm

private noncomputable def toMat (m : EntrySpace K) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) :=
  (entriesInv K).mapMatrix (Matrix.of m)

private noncomputable def invMat (m : EntrySpace K) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) :=
  (entriesInv K).mapMatrix (detInv K (Matrix.of m).det • (Matrix.of m).adjugate)

private theorem toMat_mul_invMat {m : EntrySpace K} (h : DetOk K m) : toMat K m * invMat K m = 1 := by
  unfold toMat invMat
  rw [← map_mul, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, detInv_mul_det K h, one_smul, map_one]

private theorem invMat_mul_toMat {m : EntrySpace K} (h : DetOk K m) : invMat K m * toMat K m = 1 := by
  unfold toMat invMat
  rw [← map_mul, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, detInv_mul_det K h, one_smul, map_one]

private def DetOkSet : Set (EntrySpace K) := {m | DetOk K m}

private noncomputable def glOfEntries (m : DetOkSet K) : GL (Fin 2) (InfiniteAdeleRing K) :=
  ⟨toMat K m.1, invMat K m.1, toMat_mul_invMat K m.2, invMat_mul_toMat K m.2⟩

private theorem continuous_glOfEntries (hEinv : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm) :
    Continuous (glOfEntries K) := by
  have hof : Continuous fun m : DetOkSet K => Matrix.of m.1 := continuous_subtype_val
  have hdet : Continuous fun m : DetOkSet K => (Matrix.of m.1).det := hof.matrix_det
  have hdetInv : Continuous fun m : DetOkSet K => detInv K (Matrix.of m.1).det := by
    refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
    · exact ((continuous_apply w).comp (continuous_fst.comp hdet)).inv₀ fun m => m.2.1 w
    · exact ((continuous_apply w).comp (continuous_snd.comp hdet)).inv₀ fun m => m.2.2 w
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun m : DetOkSet K => toMat K m.1
    simp only [toMat, RingHom.mapMatrix_apply]
    exact hof.matrix_map hEinv
  · show Continuous fun m : DetOkSet K => invMat K m.1
    simp only [invMat, RingHom.mapMatrix_apply]
    exact (hdetInv.smul hof.matrix_adjugate).matrix_map hEinv

private theorem archEntries_glOfEntries (m : DetOkSet K) : archEntries K (glOfEntries K m) = m.1 := by
  funext i j
  show InfiniteAdeleRing.ringEquiv_mixedSpace K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (m.1 i j)) = m.1 i j
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply (m.1 i j)

private theorem glOfEntries_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    glOfEntries K ⟨archEntries K g, detOk_archEntries K g⟩ = g := by
  apply Units.ext
  show toMat K (archEntries K g) = (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
  refine Matrix.ext fun i j => ?_
  show (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j)) =
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply _

section Tuples

variable {K}
variable (hEinv : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm)

private def TupleLocus (n : ℕ) : Set (Fin n → EntrySpace K) := {s | ∀ i, DetOk K (s i)}

private noncomputable def glTupleOfEntries (n : ℕ) (s : Fin n → EntrySpace K) :
    Fin n → GL (Fin 2) (InfiniteAdeleRing K) :=
  if h : s ∈ TupleLocus (K := K) n then fun i => glOfEntries K ⟨s i, h i⟩ else 1

include hEinv in
private theorem continuousOn_glTupleOfEntries (n : ℕ) :
    ContinuousOn (glTupleOfEntries (K := K) n) (TupleLocus (K := K) n) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (TupleLocus (K := K) n).domRestrict (glTupleOfEntries (K := K) n) =
      fun s : TupleLocus (K := K) n => fun i => glOfEntries K ⟨s.1 i, s.2 i⟩ := by
    funext s
    simp only [Set.domRestrict_apply, glTupleOfEntries, dif_pos s.2]
  rw [h]
  refine continuous_pi fun i => (continuous_glOfEntries K hEinv).comp ?_
  exact Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _

include hEinv in

private theorem isCompact_setOf_entries_mem {n : ℕ} {S : Set (Fin n → EntrySpace K)} (hS : IsCompact S)
    (hSU : S ⊆ TupleLocus (K := K) n) :
    IsCompact {c : Fin n → GL (Fin 2) (InfiniteAdeleRing K) | (fun i => archEntries K (c i)) ∈ S} := by
  have himg : IsCompact (glTupleOfEntries (K := K) n '' S) :=
    hS.image_of_continuousOn ((continuousOn_glTupleOfEntries hEinv n).mono hSU)
  convert himg using 1
  ext c
  constructor
  · intro hc
    refine ⟨fun i => archEntries K (c i), hc, ?_⟩
    have hmem : (fun i => archEntries K (c i)) ∈ TupleLocus (K := K) n := fun i => detOk_archEntries K (c i)
    funext i
    simp only [glTupleOfEntries, dif_pos hmem]
    exact glOfEntries_archEntries K (c i)
  · rintro ⟨s, hs, rfl⟩
    have hmem : s ∈ TupleLocus (K := K) n := hSU hs
    show (fun i => archEntries K (glTupleOfEntries n s i)) ∈ S
    have h : (fun i => archEntries K (glTupleOfEntries (K := K) n s i)) = s := by
      funext i
      simp only [glTupleOfEntries, dif_pos hmem]
      exact archEntries_glOfEntries K ⟨s i, hmem i⟩
    rw [h]
    exact hs

end Tuples

end Inverse

end EntryLocus

namespace FibreAssembly

open MeasureTheory Filter Topology
open scoped BigOperators

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {R : Type} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

private def assemble (n : ℕ) (p : ((Fin n → Fin 2 → Fin 2 → R) × (Fin 2 → Fin 2 → R)) × (Fin 2 → Fin 2 → R)) :
    Fin (n + 1) → Fin 2 → Fin 2 → R :=
  Fin.snoc p.1.1 fun i j => (Matrix.of p.1.2 * Matrix.of p.2) i j

omit [FiniteDimensional ℝ R] in
private theorem contDiff_entry_mul :
    ContDiff ℝ (⊤ : ℕ∞) fun q : (Fin 2 → Fin 2 → R) × (Fin 2 → Fin 2 → R) =>
      fun i j => (Matrix.of q.1 * Matrix.of q.2) i j := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine ContDiff.sum fun l _ => ContDiff.mul ?_ ?_
  · exact ((ContinuousLinearMap.proj l : (Fin 2 → R) →L[ℝ] R).contDiff.comp
      ((ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → R) →L[ℝ] (Fin 2 → R)).contDiff)).comp contDiff_fst
  · exact ((ContinuousLinearMap.proj j : (Fin 2 → R) →L[ℝ] R).contDiff.comp
      ((ContinuousLinearMap.proj l : (Fin 2 → Fin 2 → R) →L[ℝ] (Fin 2 → R)).contDiff)).comp contDiff_snd

omit [FiniteDimensional ℝ R] in
private theorem contDiff_assemble (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (assemble (R := R) n) := by
  refine contDiff_pi.2 fun k => ?_
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [assemble, Fin.snoc_last]
    exact contDiff_entry_mul.comp (ContDiff.prodMk (contDiff_snd.comp contDiff_fst) contDiff_snd)
  · simp only [assemble, Fin.snoc_castSucc]
    exact ((ContinuousLinearMap.proj i : (Fin n → Fin 2 → Fin 2 → R) →L[ℝ] (Fin 2 → Fin 2 → R)).contDiff.comp
      (contDiff_fst.comp contDiff_fst))

private def cDatum (E : G → Fin 2 → Fin 2 → R) (n : ℕ) (c : Fin n → G) :
    (Fin n → Fin 2 → Fin 2 → R) × (Fin 2 → Fin 2 → R) :=
  (fun i => E (c i), E ((List.ofFn c).prod)⁻¹)

omit [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem continuous_list_ofFn_prod (n : ℕ) : Continuous fun c : Fin n → G => (List.ofFn c).prod := by
  have h : (fun c : Fin n → G => (List.ofFn c).prod) =
      fun c => ((List.finRange n).map fun i => c i).prod := by
    funext c
    rw [List.ofFn_eq_map]
  rw [h]
  exact continuous_list_prod _ fun i _ => continuous_apply i

omit [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] in
private theorem continuous_cDatum {E : G → Fin 2 → Fin 2 → R} (hE : Continuous E) (n : ℕ) : Continuous (cDatum E n) :=
  (continuous_pi fun i => hE.comp (continuous_apply i)).prodMk (hE.comp (continuous_list_ofFn_prod n).inv)

private def reassemble (n : ℕ) (t : Fin (n + 1) → G) : G :=
  (List.ofFn fun i => t (Fin.castSucc i)).prod * t (Fin.last n)

omit [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem continuous_reassemble (n : ℕ) : Continuous (reassemble (G := G) n) :=
  ((continuous_list_ofFn_prod n).comp (continuous_pi fun i => continuous_apply (Fin.castSucc i))).mul
    (continuous_apply (Fin.last n))

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem reassemble_snoc (n : ℕ) (c : Fin n → G) (h : G) :
    reassemble n (Fin.snoc c ((List.ofFn c).prod⁻¹ * h)) = h := by
  simp only [reassemble, Fin.snoc_castSucc, Fin.snoc_last]
  exact mul_inv_cancel_left _ _

private theorem isArchTestFactor_generic (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {E : G → Fin 2 → Fin 2 → R}
    (hE : Continuous E) (hEmul : ∀ x y : G, Matrix.of (E (x * y)) = Matrix.of (E x) * Matrix.of (E y))
    {U : Set (Fin 2 → Fin 2 → R)}
    (hKc : ∀ (m : ℕ) (S : Set (Fin m → Fin 2 → Fin 2 → R)), IsCompact S → (∀ s ∈ S, ∀ i, s i ∈ U) →
      IsCompact {c : Fin m → G | (fun i => E (c i)) ∈ S})
    {n : ℕ} {Φ : (Fin (n + 1) → G) → ℂ}
    (hΦ : ∃ Ψ₁ : (Fin (n + 1) → Fin 2 → Fin 2 → R) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ₁ ∧ HasCompactSupport Ψ₁ ∧
      tsupport Ψ₁ ⊆ {t | ∀ k, t k ∈ U} ∧ ∀ x, Φ x = Ψ₁ fun k => E (x k))
    (hΦc : HasCompactSupport Φ) {f : G → ℂ}
    (hf : ∀ h, f h = ∫ c : Fin n → G, Φ (Fin.snoc c ((List.ofFn c).prod⁻¹ * h)) ∂(Measure.pi fun _ => μ)) :
    (∃ Ψ' : (Fin 2 → Fin 2 → R) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ' ∧ ∀ g, f g = Ψ' (E g)) ∧ HasCompactSupport f := by
  obtain ⟨Ψ₁, hΨ₁, hΨ₁c, hΨ₁U, hΦΨ₁⟩ := hΦ

  have hΞ : ContDiff ℝ (⊤ : ℕ∞) fun p : ((Fin n → Fin 2 → Fin 2 → R) × (Fin 2 → Fin 2 → R)) × (Fin 2 → Fin 2 → R) =>
      Ψ₁ (assemble n p) :=
    ContDiff.comp hΨ₁ (contDiff_assemble n)

  have hS : IsCompact ((fun t : Fin (n + 1) → Fin 2 → Fin 2 → R => fun i => t (Fin.castSucc i)) '' tsupport Ψ₁) :=
    hΨ₁c.image (continuous_pi fun i => continuous_apply (Fin.castSucc i))
  have hSU : ∀ s ∈ (fun t : Fin (n + 1) → Fin 2 → Fin 2 → R => fun i => t (Fin.castSucc i)) '' tsupport Ψ₁,
      ∀ i, s i ∈ U := by
    rintro _ ⟨t, ht, rfl⟩ i
    exact hΨ₁U ht (Fin.castSucc i)
  have hk : IsCompact {c : Fin n → G |
      (fun i => E (c i)) ∈ (fun t : Fin (n + 1) → Fin 2 → Fin 2 → R => fun i => t (Fin.castSucc i)) '' tsupport Ψ₁} :=
    hKc n _ hS hSU
  have hsupp : ∀ c : Fin n → G, c ∉ {c : Fin n → G |
      (fun i => E (c i)) ∈ (fun t : Fin (n + 1) → Fin 2 → Fin 2 → R => fun i => t (Fin.castSucc i)) '' tsupport Ψ₁} →
      ∀ m, Ψ₁ (assemble n (cDatum E n c, m)) = 0 := by
    intro c hc m
    refine image_eq_zero_of_notMem_tsupport fun hmem => hc ⟨assemble n (cDatum E n c, m), hmem, ?_⟩
    funext i
    simp only [assemble, cDatum, Fin.snoc_castSucc]
  haveI : SigmaFinite μ := inferInstance
  have hνk : (Measure.pi fun _ : Fin n => μ) {c : Fin n → G | (fun i => E (c i)) ∈
      (fun t : Fin (n + 1) → Fin 2 → Fin 2 → R => fun i => t (Fin.castSucc i)) '' tsupport Ψ₁} ≠ ⊤ :=
    hk.measure_lt_top.ne
  refine ⟨⟨fun m => ∫ c, Ψ₁ (assemble n (cDatum E n c, m)) ∂(Measure.pi fun _ : Fin n => μ), ?_, fun g => ?_⟩, ?_⟩
  · exact FibreSmoothing.contDiff_integral hk (continuous_cDatum hE n) hνk hΞ hsupp
  ·
    rw [hf g]
    refine congrArg (fun F : (Fin n → G) → ℂ => ∫ c, F c ∂(Measure.pi fun _ : Fin n => μ)) (funext fun c => ?_)
    rw [hΦΨ₁]
    show Ψ₁ (E ∘ (Fin.snoc c ((List.ofFn c).prod⁻¹ * g) : Fin (n + 1) → G)) = Ψ₁ (assemble n (cDatum E n c, E g))
    rw [Fin.comp_snoc]
    refine congrArg Ψ₁ ?_
    show (Fin.snoc (E ∘ c) (E ((List.ofFn c).prod⁻¹ * g)) : Fin (n + 1) → Fin 2 → Fin 2 → R) =
      Fin.snoc (fun i => E (c i)) fun i j => (Matrix.of (E (List.ofFn c).prod⁻¹) * Matrix.of (E g)) i j
    congr 1
    funext i j
    exact congrFun (congrFun (hEmul _ _) i) j
  ·
    have hT : IsCompact (reassemble n '' tsupport Φ) := hΦc.image (continuous_reassemble n)
    refine hT.of_isClosed_subset (isClosed_tsupport f) (closure_minimal ?_ hT.isClosed)
    intro g hg
    by_contra hgT
    apply hg
    rw [hf g]
    have hzero : ∀ c : Fin n → G, Φ (Fin.snoc c ((List.ofFn c).prod⁻¹ * g)) = 0 := by
      intro c
      by_contra hne
      exact hgT ⟨_, subset_tsupport Φ hne, reassemble_snoc n c g⟩
    simp only [hzero, integral_zero]

end FibreAssembly

section Solution

open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [IsFiniteMeasureOnCompacts μ] {n : ℕ}
    (Φ : (Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K)) → ℂ)
    (hΦs : ∃ Ψ : (Fin (n + 1) → Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ ∀ x, Φ x = Ψ (fun k => AutomorphicForm.archEntries K (x k)))
    (hΦc : HasCompactSupport Φ)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (hf : ∀ h, f h = ∫ c : Fin n → GL (Fin 2) (InfiniteAdeleRing K),
      Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ)) :
    AutomorphicForm.IsArchTestFactor K f := by

  haveI : SecondCountableTopology (InfiniteAdeleRing K) :=
    ArchIdentification.secondCountableTopology_infiniteAdeleRing_mixed K
  haveI : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) :=
    GLCarrierFacts.secondCountableTopology_gl (InfiniteAdeleRing K)
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) :=
    GLCarrierFacts.locallyCompactSpace_gl (InfiniteAdeleRing K)

  letI : NormedAddCommGroup (mixedEmbedding.mixedSpace K) := inferInstance
  letI : NormedSpace ℝ (mixedEmbedding.mixedSpace K) := inferInstance
  letI instR : NormedRing (mixedEmbedding.mixedSpace K) := inferInstance
  letI : NormedAlgebra ℝ (mixedEmbedding.mixedSpace K) := inferInstance
  haveI : FiniteDimensional ℝ (mixedEmbedding.mixedSpace K) := inferInstance
  have hE : Continuous (archEntries K) := EntryLocus.continuous_archEntries K
  have hEinv : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :=
    ArchIdentification.continuous_archMixedHomeomorph_symm K

  have hΦs' : ∃ Ψ : (Fin (n + 1) → Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ ∀ x, Φ x = Ψ (fun k => archEntries K (x k)) := by
    obtain ⟨Ψ, hΨ, hΦΨ⟩ := hΦs
    exact ⟨Ψ, by convert hΨ, hΦΨ⟩
  obtain ⟨Ψ, hΨ, hΦΨ⟩ := hΦs'

  obtain ⟨Ψ₁, hΨ₁, hΨ₁c, hΨ₁U, hΦΨ₁⟩ := EntryLocus.exists_smooth_rep_generic
    (e := fun x : Fin (n + 1) → GL (Fin 2) (InfiniteAdeleRing K) => fun k => archEntries K (x k))
    (U := EntryLocus.UnitLocus K n) (continuous_pi fun k => hE.comp (continuous_apply k))
    (by convert EntryLocus.isOpen_unitLocus K n) (fun x k => EntryLocus.detOk_archEntries K (x k)) hΨ hΦΨ hΦc

  have hEmul : ∀ x y : GL (Fin 2) (InfiniteAdeleRing K),
      Matrix.of (archEntries K (x * y)) = Matrix.of (archEntries K x) * Matrix.of (archEntries K y) := by
    intro x y
    have hof : ∀ z : GL (Fin 2) (InfiniteAdeleRing K), Matrix.of (archEntries K z) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K →+* mixedEmbedding.mixedSpace K).mapMatrix
          (z : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := fun z => Matrix.ext fun i j => rfl
    rw [hof, hof, hof, Units.val_mul, map_mul]

  have hKc : ∀ (m : ℕ) (S : Set (Fin m → Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K)), IsCompact S →
      (∀ s ∈ S, ∀ i, s i ∈ {e | EntryLocus.DetOk K e}) →
        IsCompact {c : Fin m → GL (Fin 2) (InfiniteAdeleRing K) | (fun i => archEntries K (c i)) ∈ S} :=
    fun m S hS hSU => by convert EntryLocus.isCompact_setOf_entries_mem hEinv hS hSU

  unfold AutomorphicForm.IsArchTestFactor
  convert FibreAssembly.isArchTestFactor_generic μ hE hEmul (U := {e | EntryLocus.DetOk K e}) hKc
    ⟨Ψ₁, ?_, ?_, ?_, hΦΨ₁⟩ hΦc hf using 2
  · convert hΨ₁
  · exact hΨ₁c
  · exact hΨ₁U

end Solution

end S_AutomorphicForm_isArchTestFactor_of_forall_eq_integral_snoc
end P2MW
export P2MW.S_AutomorphicForm_isArchTestFactor_of_forall_eq_integral_snoc (solution)
