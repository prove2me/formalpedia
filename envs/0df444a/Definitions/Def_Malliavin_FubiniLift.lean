-- Prove2me | Definitions.Def_Malliavin_FubiniLift
-- name    : Malliavin_FubiniLift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:43:36.523552+00:00
-- url     : https://prove2.me/theorems/c8967ad2-c726-50de-a87f-8eca3ca8d581
-- title:
--   Fubini Lift
-- statement:
--   Definitions and structural lemmas for Fubini Lift, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Recall
set_option autoImplicit false
open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3
namespace Malliavin
section Generic
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
abbrev FiniteMeasurableSet (μ : Measure Ω) := {A : Set Ω // MeasurableSet A ∧ μ A ≠ ∞}
theorem memLp_tensor (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    MemLp (fun p : T × Ω ↦ g p.1 * A.1.indicator (1 : Ω → ℝ) p.2) 2 (ν.prod μ) := by
  have hg : MemLp (g : T → ℝ) 2 ν := Lp.memLp g
  have hA : MemLp (A.1.indicator (1 : Ω → ℝ)) 2 μ :=
    memLp_indicator_const 2 A.2.1 (1 : ℝ) (Or.inr A.2.2)
  refine (memLp_two_iff_integrable_sq (hg.1.comp_fst.mul hA.1.comp_snd)).mpr ?_
  refine (hg.integrable_sq.mul_prod hA.integrable_sq).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]
  ring
noncomputable def tensorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) : Lp ℝ 2 (ν.prod μ) :=
  (memLp_tensor A g).toLp _
theorem coeFn_tensorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    (tensorLp A g : T × Ω → ℝ) =ᵐ[ν.prod μ]
      fun p ↦ g p.1 * A.1.indicator (1 : Ω → ℝ) p.2 :=
  MemLp.coeFn_toLp _
noncomputable def indicatorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) : Lp (Lp ℝ 2 ν) 2 μ :=
  indicatorConstLp 2 A.2.1 A.2.2 g
theorem inner_indicatorLp (A A' : FiniteMeasurableSet μ) (g g' : Lp ℝ 2 ν) :
    ⟪indicatorLp A g, indicatorLp A' g'⟫_ℝ = μ.real (A.1 ∩ A'.1) * ⟪g, g'⟫_ℝ := by
  unfold indicatorLp
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ A.2.1 A.2.2 g,
    setIntegral_indicatorConstLp A.2.1 A'.2.1 A'.2.2, real_inner_smul_right, Set.inter_comm]
noncomputable def tensorStepToLp :
    (FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) →ₗ[ℝ] Lp (Lp ℝ 2 ν) 2 μ :=
  Finsupp.linearCombination ℝ fun x ↦ indicatorLp x.1 x.2
noncomputable def tensorStepToProd :
    (FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (ν.prod μ) :=
  Finsupp.linearCombination ℝ fun x ↦ tensorLp x.1 x.2
theorem tensorStepToLp_single (x : FiniteMeasurableSet μ × Lp ℝ 2 ν) (c : ℝ) :
    tensorStepToLp (Finsupp.single x c) = c • indicatorLp x.1 x.2 :=
  Finsupp.linearCombination_single _ _ _
theorem tensorStepToProd_single (x : FiniteMeasurableSet μ × Lp ℝ 2 ν) (c : ℝ) :
    tensorStepToProd (Finsupp.single x c) = c • tensorLp x.1 x.2 :=
  Finsupp.linearCombination_single _ _ _
theorem denseRange_tensorStepToLp : DenseRange (tensorStepToLp (μ := μ) (ν := ν)) := by
  change Dense (Set.range tensorStepToLp)
  rw [← LinearMap.coe_range, tensorStepToLp, Finsupp.range_linearCombination,
    Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  intro f _
  refine Lp.induction ENNReal.ofNat_ne_top
    (fun f : Lp (Lp ℝ 2 ν) 2 μ ↦ f ∈ (Submodule.span ℝ (Set.range fun x :
      FiniteMeasurableSet μ × Lp ℝ 2 ν ↦ indicatorLp x.1 x.2)).topologicalClosure)
    ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(⟨s, hs, hμs.ne⟩, c), rfl⟩)
  · intro f g _ _ _ hf hg
    exact Submodule.add_mem _ hf hg
  · exact Submodule.isClosed_topologicalClosure _
variable [SFinite μ] [SFinite ν]
theorem inner_tensorLp (A A' : FiniteMeasurableSet μ) (g g' : Lp ℝ 2 ν) :
    ⟪tensorLp A g, tensorLp A' g'⟫_ℝ = μ.real (A.1 ∩ A'.1) * ⟪g, g'⟫_ℝ := by
  rw [L2.inner_def]
  calc ∫ p, ⟪(tensorLp A g) p, (tensorLp A' g') p⟫_ℝ ∂(ν.prod μ)
      = ∫ p, (g p.1 * g' p.1) * ((A.1 ∩ A'.1).indicator (1 : Ω → ℝ) p.2) ∂(ν.prod μ) := by
        apply integral_congr_ae
        filter_upwards [coeFn_tensorLp A g, coeFn_tensorLp A' g'] with p h1 h2
        rw [h1, h2, Set.inter_indicator_one]
        simp only [RCLike.inner_apply, conj_trivial, Pi.mul_apply]
        ring
    _ = (∫ t, g t * g' t ∂ν) * ∫ ω, (A.1 ∩ A'.1).indicator (1 : Ω → ℝ) ω ∂μ :=
        integral_prod_mul (fun t ↦ g t * g' t) (fun ω ↦ (A.1 ∩ A'.1).indicator (1 : Ω → ℝ) ω)
    _ = μ.real (A.1 ∩ A'.1) * ⟪g, g'⟫_ℝ := by
        rw [integral_indicator_one (A.2.1.inter A'.2.1), L2.inner_def, mul_comm]
        congr 1
        apply integral_congr_ae
        filter_upwards with t
        simp only [RCLike.inner_apply, conj_trivial, mul_comm]
theorem inner_tensorStepToProd (v w : FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) :
    ⟪tensorStepToProd v, tensorStepToProd w⟫_ℝ = ⟪tensorStepToLp v, tensorStepToLp w⟫_ℝ := by
  unfold tensorStepToProd tensorStepToLp
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, inner_tensorLp, inner_indicatorLp]
theorem norm_tensorStepToProd (v : FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) :
    ‖tensorStepToProd v‖ = ‖tensorStepToLp v‖ := by
  have h := inner_tensorStepToProd v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
noncomputable def fubiniLiftL : Lp (Lp ℝ 2 ν) 2 μ →L[ℝ] Lp ℝ 2 (ν.prod μ) :=
  tensorStepToProd.extendOfNorm tensorStepToLp
theorem fubiniLiftL_tensorStepToLp (v : FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) :
    fubiniLiftL (tensorStepToLp v) = tensorStepToProd v :=
  LinearMap.extendOfNorm_eq denseRange_tensorStepToLp
    ⟨1, fun v ↦ by rw [norm_tensorStepToProd, one_mul]⟩ v
theorem fubiniLiftL_indicatorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    fubiniLiftL (indicatorLp A g) = tensorLp A g := by
  have := fubiniLiftL_tensorStepToLp (Finsupp.single (A, g) (1 : ℝ))
  rwa [tensorStepToLp_single, tensorStepToProd_single, one_smul, one_smul] at this
theorem inner_fubiniLiftL (f g : Lp (Lp ℝ 2 ν) 2 μ) :
    ⟪fubiniLiftL f, fubiniLiftL g⟫_ℝ = ⟪f, g⟫_ℝ := by
  refine denseRange_tensorStepToLp.induction_on₂
    (p := fun f g ↦ ⟪fubiniLiftL f, fubiniLiftL g⟫_ℝ = ⟪f, g⟫_ℝ) ?_ ?_ f g
  · exact isClosed_eq ((fubiniLiftL.continuous.comp continuous_fst).inner
      (fubiniLiftL.continuous.comp continuous_snd)) (continuous_fst.inner continuous_snd)
  · intro v w
    simp only [fubiniLiftL_tensorStepToLp, inner_tensorStepToProd]
theorem norm_fubiniLiftL (f : Lp (Lp ℝ 2 ν) 2 μ) : ‖fubiniLiftL f‖ = ‖f‖ := by
  have h := inner_fubiniLiftL f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
noncomputable def fubiniLift : Lp (Lp ℝ 2 ν) 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (ν.prod μ) :=
  ⟨fubiniLiftL.toLinearMap, norm_fubiniLiftL⟩
theorem fubiniLift_indicatorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    fubiniLift (indicatorLp A g) = tensorLp A g :=
  fubiniLiftL_indicatorLp A g
end Generic
section RankOne
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
noncomputable def smulLp (e : E) : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℝ e).compLpL 2 μ
theorem memLp_tensor' (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    MemLp (fun p : T × Ω ↦ g p.1 * G p.2) 2 (ν.prod μ) := by
  refine (memLp_two_iff_integrable_sq
    ((Lp.aestronglyMeasurable g).comp_fst.mul (Lp.aestronglyMeasurable G).comp_snd)).mpr ?_
  refine ((Lp.memLp g).integrable_sq.mul_prod (Lp.memLp G).integrable_sq).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]
  ring
noncomputable def tensor (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) : Lp ℝ 2 (ν.prod μ) :=
  (memLp_tensor' g G).toLp _
theorem coeFn_tensor (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    (tensor g G : T × Ω → ℝ) =ᵐ[ν.prod μ] fun p ↦ g p.1 * G p.2 :=
  MemLp.coeFn_toLp _
theorem tensor_add (g : Lp ℝ 2 ν) (G G' : Lp ℝ 2 μ) :
    tensor g (G + G') = tensor g G + tensor g G' := by
  apply Lp.ext
  have h5 : (fun p : T × Ω ↦ (G + G' : Lp ℝ 2 μ) p.2) =ᵐ[ν.prod μ]
      fun p ↦ G p.2 + G' p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_add G G')
  filter_upwards [coeFn_tensor g (G + G'), coeFn_tensor g G, coeFn_tensor g G',
    Lp.coeFn_add (tensor g G) (tensor g G'), h5] with p h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5]
  ring
theorem tensor_smul (g : Lp ℝ 2 ν) (c : ℝ) (G : Lp ℝ 2 μ) :
    tensor g (c • G) = c • tensor g G := by
  apply Lp.ext
  have h5 : (fun p : T × Ω ↦ (c • G : Lp ℝ 2 μ) p.2) =ᵐ[ν.prod μ] fun p ↦ c * G p.2 := by
    have h : (c • (G : Ω → ℝ)) =ᵐ[μ] fun ω ↦ c * G ω :=
      Filter.Eventually.of_forall fun ω ↦ by simp
    exact Measure.quasiMeasurePreserving_snd.ae_eq_comp ((Lp.coeFn_smul c G).trans h)
  filter_upwards [coeFn_tensor g (c • G), coeFn_tensor g G, Lp.coeFn_smul c (tensor g G), h5]
    with p h1 h2 h3 h5
  rw [h1, h3, Pi.smul_apply, h2, h5, smul_eq_mul]
  ring
theorem inner_tensor [SFinite μ] [SFinite ν]
    (g g' : Lp ℝ 2 ν) (G G' : Lp ℝ 2 μ) :
    inner ℝ (tensor g G) (tensor g' G') = inner ℝ g g' * inner ℝ G G' := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  calc
    ∫ p, tensor g' G' p * tensor g G p ∂ν.prod μ =
        ∫ p, (g' p.1 * g p.1) * (G' p.2 * G p.2) ∂ν.prod μ := by
      apply integral_congr_ae
      filter_upwards [coeFn_tensor g G, coeFn_tensor g' G'] with p hfirst hsecond
      rw [hfirst, hsecond]
      ring
    _ = (∫ t, g' t * g t ∂ν) * ∫ w, G' w * G w ∂μ :=
      integral_prod_mul (fun t ↦ g' t * g t) (fun w ↦ G' w * G w)
theorem norm_tensor [SFinite μ] [SFinite ν] (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    ‖tensor g G‖ = ‖g‖ * ‖G‖ := by
  have h := inner_tensor g g G G
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    ← mul_pow] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h
noncomputable def tensorL [SFinite μ] [SFinite ν] (g : Lp ℝ 2 ν) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (ν.prod μ) :=
  LinearMap.mkContinuous
    { toFun := tensor g
      map_add' := tensor_add g
      map_smul' := tensor_smul g } ‖g‖ fun G ↦ by
      change ‖tensor g G‖ ≤ ‖g‖ * ‖G‖
      rw [norm_tensor]
end RankOne
section Surj
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
theorem indicatorConstLp_congr_set {α E : Type*} [MeasurableSpace α] {m : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} {s t : Set α} (h : s = t) (hs : MeasurableSet s)
    (hms : m s ≠ ∞) (c : E) :
    indicatorConstLp p hs hms c = indicatorConstLp p (h ▸ hs) (h ▸ hms) c := by
  subst h
  rfl
variable [SFinite μ] [SFinite ν]
noncomputable abbrev fubiniRange : Submodule ℝ (Lp ℝ 2 (ν.prod μ)) :=
  LinearMap.range (fubiniLift (μ := μ) (ν := ν)).toLinearMap
theorem isClosed_fubiniRange : IsClosed (fubiniRange (μ := μ) (ν := ν) : Set (Lp ℝ 2 (ν.prod μ))) :=
  (fubiniLift (μ := μ) (ν := ν)).isometry.isClosedEmbedding.isClosed_range
theorem indicatorConstLp_prod_mem_fubiniRange {U : Set T} {A : Set Ω} (hU : MeasurableSet U)
    (hA : MeasurableSet A) (hνU : ν U ≠ ∞) (hμA : μ A ≠ ∞) (c : ℝ) :
    indicatorConstLp 2 (hU.prod hA) (by rw [Measure.prod_prod]; finiteness) c ∈
      fubiniRange (μ := μ) (ν := ν) := by
  refine ⟨indicatorLp ⟨A, hA, hμA⟩ (indicatorConstLp 2 hU hνU c), ?_⟩
  rw [LinearIsometry.coe_toLinearMap, fubiniLift_indicatorLp]
  apply Lp.ext
  filter_upwards [coeFn_tensorLp ⟨A, hA, hμA⟩ (indicatorConstLp 2 hU hνU c),
    indicatorConstLp_coeFn (p := 2) (hs := hU.prod hA)
      (hμs := by rw [Measure.prod_prod]; finiteness) (c := c),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := hU) (hμs := hνU) (c := c))] with p h1 h2 h3
  rw [h1, h2]
  simp only [Function.comp_apply] at h3
  rw [h3]
  by_cases hp1 : p.1 ∈ U <;> by_cases hp2 : p.2 ∈ A <;> simp [Set.indicator, hp1, hp2]
theorem norm_sq_eq_integral_norm_sq {α E : Type*} [MeasurableSpace α] {m : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : Lp E 2 m) :
    ‖X‖ ^ 2 = ∫ x, ‖X x‖ ^ 2 ∂m := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  exact real_inner_self_eq_norm_sq _
theorem indicator_iUnion_sub_sum {α : Type*} {f : ℕ → Set α} (hf : Pairwise (Disjoint on f))
    (c : ℝ) (N : ℕ) (x : α) :
    (⋃ i, f i).indicator (fun _ ↦ c) x - ∑ i ∈ Finset.range N, (f i).indicator (fun _ ↦ c) x =
      (⋃ i, ⋃ (_ : N ≤ i), f i).indicator (fun _ ↦ c) x := by
  by_cases hx : x ∈ ⋃ i, f i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    have hj' : ∀ i, i ≠ j → x ∉ f i := fun i hi hx' ↦ Set.disjoint_left.mp (hf hi) hx' hj
    rw [Set.indicator_of_mem hx]
    by_cases hjN : N ≤ j
    · rw [Finset.sum_eq_zero fun i hi ↦ Set.indicator_of_notMem
        (hj' i (by rw [Finset.mem_range] at hi; omega)) _,
        Set.indicator_of_mem (Set.mem_iUnion₂.mpr ⟨j, hjN, hj⟩), sub_zero]
    · have hnot : x ∉ ⋃ i, ⋃ (_ : N ≤ i), f i := fun h ↦ by
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h
        exact hj' i (by omega) hxi
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))
        (fun i _ hi ↦ Set.indicator_of_notMem (hj' i hi) _), Set.indicator_of_mem hj,
        Set.indicator_of_notMem hnot, sub_self]
  · have hnot : ∀ i, x ∉ f i := fun i hi ↦ hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
    have : x ∉ ⋃ i, ⋃ (_ : N ≤ i), f i := fun h ↦ by
      obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp h
      exact hnot i hxi
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this,
      Finset.sum_eq_zero fun i _ ↦ Set.indicator_of_notMem (hnot i) _, sub_zero]
theorem indicatorConstLp_iUnion_mem {α : Type*} [MeasurableSpace α] {m : Measure α}
    {K : Submodule ℝ (Lp ℝ 2 m)} (hK : IsClosed (K : Set (Lp ℝ 2 m))) {f : ℕ → Set α}
    (hf : Pairwise (Disjoint on f)) (hfm : ∀ i, MeasurableSet (f i))
    (hU : m (⋃ i, f i) ≠ ∞) (c : ℝ)
    (hmem : ∀ i, indicatorConstLp 2 (hfm i)
      (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c ∈ K) :
    indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c ∈ K := by
  set S : ℕ → Lp ℝ 2 m := fun N ↦ ∑ i ∈ Finset.range N, indicatorConstLp 2 (hfm i)
    (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c with hS
  have hSK : ∀ N, S N ∈ K := fun N ↦ Submodule.sum_mem _ fun i _ ↦ hmem i
  -- the tails `⋃ i ≥ N, f i` have measure tending to zero
  set tail : ℕ → Set α := fun N ↦ ⋃ i, ⋃ (_ : N ≤ i), f i with htail
  have htail_meas : ∀ N, MeasurableSet (tail N) := fun N ↦
    MeasurableSet.iUnion fun i ↦ MeasurableSet.iUnion fun _ ↦ hfm i
  have htail_sub : ∀ N, tail N ⊆ ⋃ i, f i := fun N ↦
    Set.iUnion_subset fun i ↦ Set.iUnion_subset fun _ ↦ Set.subset_iUnion f i
  have htail_anti : Antitone tail := fun N M hNM ↦
    Set.iUnion_mono fun i ↦ Set.iUnion_mono' fun h ↦ ⟨hNM.trans h, le_rfl⟩
  have htail_inter : ⋂ N, tail N = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp (hx 0)
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hx (i + 1))
    exact Set.disjoint_left.mp (hf (by omega : i ≠ j)) hxi hxj
  have htail_tendsto : Tendsto (fun N ↦ m (tail N)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (fun N ↦ (htail_meas N).nullMeasurableSet) htail_anti
      ⟨0, ne_top_of_le_ne_top hU (measure_mono (htail_sub 0))⟩
    rwa [htail_inter, measure_empty] at this
  -- the difference between the indicator of the union and a partial sum is the tail indicator
  have hdiff : ∀ N, ∀ᵐ x ∂m, (indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c : α → ℝ) x -
      (S N : α → ℝ) x = (tail N).indicator (fun _ ↦ c) x := by
    intro N
    have hsum := Lp.coeFn_finsetSum (Finset.range N) fun i ↦ indicatorConstLp 2 (hfm i)
      (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c
    have hind : ∀ᵐ x ∂m, ∀ i : ℕ, (indicatorConstLp 2 (hfm i)
        (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c : α → ℝ) x =
          (f i).indicator (fun _ ↦ c) x :=
      ae_all_iff.2 fun i ↦ indicatorConstLp_coeFn
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.iUnion hfm)
      (hμs := hU) (c := c), hsum, hind] with x h1 h2 h3
    rw [h1, hS, h2, Finset.sum_apply]
    simp_rw [h3]
    exact indicator_iUnion_sub_sum hf c N x
  have hnorm : ∀ N, ‖indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N‖ ^ 2 =
      c ^ 2 * (m (tail N)).toReal := by
    intro N
    rw [norm_sq_eq_integral_norm_sq]
    calc ∫ x, ‖(indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N) x‖ ^ 2 ∂m
        = ∫ x, (tail N).indicator (fun _ ↦ c ^ 2) x ∂m := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub (indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c) (S N),
            hdiff N] with x h1 h2
          rw [h1, Pi.sub_apply, h2, Real.norm_eq_abs, sq_abs]
          by_cases hx : x ∈ tail N <;> simp [hx]
      _ = c ^ 2 * (m (tail N)).toReal := by
          rw [integral_indicator_const _ (htail_meas N), smul_eq_mul, mul_comm]
          rfl
  have hlim : Tendsto (fun N ↦ ‖indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N‖)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N ↦ (m (tail N)).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail_tendsto
      rw [ENNReal.toReal_zero] at this
      exact this
    have h2 : Tendsto (fun N ↦ ‖indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N‖ ^ 2)
        atTop (𝓝 0) := by
      simp_rw [hnorm]
      simpa using h1.const_mul (c ^ 2)
    have := h2.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hS_tendsto : Tendsto S atTop (𝓝 (indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hlim
  exact hK.mem_of_tendsto hS_tendsto (Filter.Eventually.of_forall hSK)
theorem indicatorConstLp_inter_prod_mem_fubiniRange {U₀ : Set T} {A₀ : Set Ω}
    (hU₀ : MeasurableSet U₀) (hA₀ : MeasurableSet A₀) (hνU₀ : ν U₀ ≠ ∞) (hμA₀ : μ A₀ ≠ ∞) :
    ∀ (S : Set (T × Ω)) (hS : MeasurableSet S) (c : ℝ),
      indicatorConstLp 2 (hS.inter (hU₀.prod hA₀))
        (ne_top_of_le_ne_top (by rw [Measure.prod_prod]; finiteness)
          (measure_mono Set.inter_subset_right)) c ∈ fubiniRange (μ := μ) (ν := ν) := by
  have hR : (ν.prod μ) (U₀ ×ˢ A₀) ≠ ∞ := by rw [Measure.prod_prod]; finiteness
  have hfin : ∀ S : Set (T × Ω), (ν.prod μ) (S ∩ U₀ ×ˢ A₀) ≠ ∞ := fun S ↦
    ne_top_of_le_ne_top hR (measure_mono Set.inter_subset_right)
  refine MeasurableSpace.induction_on_inter
    (C := fun S hS ↦ ∀ c : ℝ, indicatorConstLp 2 (hS.inter (hU₀.prod hA₀)) (hfin S) c ∈
      fubiniRange (μ := μ) (ν := ν))
    generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
  · intro c
    rw [indicatorConstLp_congr_set (Set.empty_inter _), indicatorConstLp_empty]
    exact Submodule.zero_mem _
  · rintro _ ⟨U, hU, A, hA, rfl⟩ c
    rw [indicatorConstLp_congr_set (Set.prod_inter_prod (s₁ := U) (t₁ := A))]
    exact indicatorConstLp_prod_mem_fubiniRange (hU.inter hU₀) (hA.inter hA₀)
      (ne_top_of_le_ne_top hνU₀ (measure_mono Set.inter_subset_right))
      (ne_top_of_le_ne_top hμA₀ (measure_mono Set.inter_subset_right)) c
  · intro t ht hind c
    have hdisj : Disjoint (t ∩ U₀ ×ˢ A₀) (tᶜ ∩ U₀ ×ˢ A₀) :=
      Disjoint.mono Set.inter_subset_left Set.inter_subset_left disjoint_compl_right
    have hunion := indicatorConstLp_disjoint_union (p := 2) (μ := ν.prod μ)
      (ht.inter (hU₀.prod hA₀)) (ht.compl.inter (hU₀.prod hA₀)) (hfin t) (hfin tᶜ) hdisj c
    have hset : (t ∩ U₀ ×ˢ A₀) ∪ (tᶜ ∩ U₀ ×ˢ A₀) = U₀ ×ˢ A₀ := by
      ext p
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    rw [indicatorConstLp_congr_set hset] at hunion
    have hR' : indicatorConstLp 2 (hset ▸ (ht.inter (hU₀.prod hA₀)).union
        (ht.compl.inter (hU₀.prod hA₀))) (hset ▸ (by finiteness)) c ∈
          fubiniRange (μ := μ) (ν := ν) :=
      indicatorConstLp_prod_mem_fubiniRange hU₀ hA₀ hνU₀ hμA₀ c
    have heq : indicatorConstLp 2 (ht.compl.inter (hU₀.prod hA₀)) (hfin tᶜ) c =
        indicatorConstLp 2 (hset ▸ (ht.inter (hU₀.prod hA₀)).union
          (ht.compl.inter (hU₀.prod hA₀))) (hset ▸ (by finiteness)) c -
        indicatorConstLp 2 (ht.inter (hU₀.prod hA₀)) (hfin t) c := by
      rw [hunion, add_sub_cancel_left]
    rw [heq]
    exact Submodule.sub_mem _ hR' (hind c)
  · intro f hf hfm hind c
    rw [indicatorConstLp_congr_set (Set.iUnion_inter (U₀ ×ˢ A₀) f)]
    refine indicatorConstLp_iUnion_mem isClosed_fubiniRange
      (hf.mono fun i j hij ↦ Disjoint.mono Set.inter_subset_left Set.inter_subset_left hij)
      (fun i ↦ (hfm i).inter (hU₀.prod hA₀)) _ c fun i ↦ hind i c
variable [SigmaFinite μ] [SigmaFinite ν]
theorem indicatorConstLp_mem_fubiniRange {S : Set (T × Ω)} (hS : MeasurableSet S)
    (hμS : (ν.prod μ) S ≠ ∞) (c : ℝ) :
    indicatorConstLp 2 hS hμS c ∈ fubiniRange (μ := μ) (ν := ν) := by
  set R : ℕ → Set (T × Ω) := fun n ↦ spanningSets ν n ×ˢ spanningSets μ n with hR
  have hRm : ∀ n, MeasurableSet (R n) := fun n ↦
    (measurableSet_spanningSets ν n).prod (measurableSet_spanningSets μ n)
  have hRmono : Monotone R := fun n m hnm ↦
    Set.prod_mono (monotone_spanningSets ν hnm) (monotone_spanningSets μ hnm)
  have hRunion : ⋃ n, R n = Set.univ := by
    ext ⟨t, ω⟩
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_univ, iff_true, hR]
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ((iUnion_spanningSets ν).symm ▸ Set.mem_univ t)
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ((iUnion_spanningSets μ).symm ▸ Set.mem_univ ω)
    exact ⟨max n m, monotone_spanningSets ν (le_max_left n m) hn,
      monotone_spanningSets μ (le_max_right n m) hm⟩
  have hmem : ∀ n, indicatorConstLp 2 (hS.inter (hRm n))
      (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c ∈
        fubiniRange (μ := μ) (ν := ν) := fun n ↦
    indicatorConstLp_inter_prod_mem_fubiniRange (measurableSet_spanningSets ν n)
      (measurableSet_spanningSets μ n) (measure_spanningSets_lt_top ν n).ne
      (measure_spanningSets_lt_top μ n).ne S hS c
  -- the complements `S \ R n` shrink to `∅`
  set D : ℕ → Set (T × Ω) := fun n ↦ S \ R n with hD
  have hDm : ∀ n, MeasurableSet (D n) := fun n ↦ hS.diff (hRm n)
  have hDanti : Antitone D := fun n m hnm ↦ Set.sdiff_subset_sdiff_right (hRmono hnm)
  have hDinter : ⋂ n, D n = ∅ := by
    ext p
    simp only [Set.mem_iInter, hD, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_forall,
      not_and, not_not]
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hRunion ▸ Set.mem_univ p)
    exact ⟨n, fun _ ↦ hn⟩
  have hDtendsto : Tendsto (fun n ↦ (ν.prod μ) (D n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (fun n ↦ (hDm n).nullMeasurableSet) hDanti
      ⟨0, ne_top_of_le_ne_top hμS (measure_mono Set.sdiff_subset)⟩
    rwa [hDinter, measure_empty] at this
  -- the difference of indicators is the indicator of `S \ R n`
  have hdiff : ∀ n, ∀ᵐ p ∂(ν.prod μ), (indicatorConstLp 2 hS hμS c : T × Ω → ℝ) p -
      (indicatorConstLp 2 (hS.inter (hRm n))
        (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c : T × Ω → ℝ) p =
      (D n).indicator (fun _ ↦ c) p := by
    intro n
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hμS) (c := c),
      indicatorConstLp_coeFn (p := 2) (hs := hS.inter (hRm n))
        (hμs := ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) (c := c)]
      with p h1 h2
    rw [h1, h2]
    by_cases hp : p ∈ S <;> by_cases hpR : p ∈ R n <;> simp [Set.indicator, hD, hp, hpR]
  have hnorm : ∀ n, ‖indicatorConstLp 2 hS hμS c - indicatorConstLp 2 (hS.inter (hRm n))
      (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c‖ ^ 2 =
      c ^ 2 * ((ν.prod μ) (D n)).toReal := by
    intro n
    rw [norm_sq_eq_integral_norm_sq]
    calc ∫ p, ‖(indicatorConstLp 2 hS hμS c - indicatorConstLp 2 (hS.inter (hRm n))
          (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c) p‖ ^ 2 ∂(ν.prod μ)
        = ∫ p, (D n).indicator (fun _ ↦ c ^ 2) p ∂(ν.prod μ) := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub (indicatorConstLp 2 hS hμS c)
            (indicatorConstLp 2 (hS.inter (hRm n))
              (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c), hdiff n]
            with p h1 h2
          rw [h1, Pi.sub_apply, h2, Real.norm_eq_abs, sq_abs]
          by_cases hp : p ∈ D n <;> simp [hp]
      _ = c ^ 2 * ((ν.prod μ) (D n)).toReal := by
          rw [integral_indicator_const _ (hDm n), smul_eq_mul, mul_comm]
          rfl
  have hlim : Tendsto (fun n ↦ indicatorConstLp 2 (hS.inter (hRm n))
      (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c) atTop
      (𝓝 (indicatorConstLp 2 hS hμS c)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun n ↦ ((ν.prod μ) (D n)).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDtendsto
      rw [ENNReal.toReal_zero] at this
      exact this
    have h2 : Tendsto (fun n ↦ ‖indicatorConstLp 2 hS hμS c - indicatorConstLp 2
        (hS.inter (hRm n)) (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c‖ ^ 2)
        atTop (𝓝 0) := by
      simp_rw [hnorm]
      simpa using h1.const_mul (c ^ 2)
    have := h2.sqrt
    simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
    simpa only [norm_sub_rev] using this
  exact isClosed_fubiniRange.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
theorem fubiniRange_eq_top : fubiniRange (μ := μ) (ν := ν) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  refine Lp.induction ENNReal.ofNat_ne_top (fun f : Lp ℝ 2 (ν.prod μ) ↦ f ∈ fubiniRange) ?_ ?_
    isClosed_fubiniRange f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact indicatorConstLp_mem_fubiniRange hs hμs.ne c
  · intro f g _ _ _ hf hg
    exact Submodule.add_mem _ hf hg
theorem fubiniLift_surjective : Function.Surjective (fubiniLift (μ := μ) (ν := ν)) := fun y ↦ by
  have : y ∈ fubiniRange (μ := μ) (ν := ν) :=
    (fubiniRange_eq_top (μ := μ) (ν := ν)) ▸ Submodule.mem_top
  exact this
noncomputable def fubiniEquiv : Lp (Lp ℝ 2 ν) 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 (ν.prod μ) :=
  LinearIsometryEquiv.ofSurjective fubiniLift fubiniLift_surjective
end Surj
section Multiplier
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E]
theorem memLp_boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) : MemLp (fun x ↦ G x • U x) 2 μ := by
  refine MemLp.of_le ((Lp.memLp U).norm.const_mul C) (hG.smul (Lp.aestronglyMeasurable U))
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
  rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs (C * ‖U x‖),
    abs_of_nonneg (mul_nonneg hC0 (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
noncomputable def boundedSMulₗ {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) : Lp E 2 μ →ₗ[ℝ] Lp E 2 μ where
  toFun U := (memLp_boundedSMul hG hC U).toLp _
  map_add' U V := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_add U V] with x hx
    rw [hx, Pi.add_apply, Pi.add_apply, smul_add]
  map_smul' c U := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_smul c U] with x hx
    rw [hx, Pi.smul_apply, Pi.smul_apply, smul_comm]
theorem boundedSMulₗ_apply {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) :
    boundedSMulₗ hG hC U = (memLp_boundedSMul hG hC U).toLp _ := rfl
theorem norm_boundedSMulₗ_le {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) : ‖boundedSMulₗ hG hC U‖ ≤ C * ‖U‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_boundedSMul hG hC U)] with x hx
  rw [boundedSMulₗ_apply, hx, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
noncomputable def boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  LinearMap.mkContinuous (boundedSMulₗ hG hC) C (norm_boundedSMulₗ_le hG hC)
end Multiplier
section Compat
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
  [SFinite μ] [SFinite ν]
omit [SFinite μ] [SFinite ν] in
/-- A bounded measurable function of `ω`, viewed on `T × Ω`. -/
theorem aestronglyMeasurable_comp_snd {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) :
    AEStronglyMeasurable (fun p : T × Ω ↦ G p.2) (ν.prod μ) :=
  hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
end Compat
end Malliavin


