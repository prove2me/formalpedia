-- Prove2me | Definitions.Def_OAIQ27Sle000
-- name    : OAIQ27Sle000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T22:35:06.566032+00:00
-- url     : https://prove2.me/theorems/ed13484f-2c82-42fb-8409-4674a4a0a0be
-- title:
--   Definitions bundle OAIQ27Sle000 of the split of OpenAI, An explicit exact Hausdorff gauge for SLE
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SLEExactGauge.sourceLowerMain_proved`, carved from OpenAI's openai/math development (OpenAI, *An explicit exact Hausdorff gauge for SLE*, OpenAI Math Release, September 26, 2026, result family 230, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 514 declarations of OpenAI's Lean: 315 definitions, 14 inductive types or structures, 6 instances and 179 theorems. The definitions and types are `OAI.SLEExactGauge.AngularLocalization`, `OAI.SLEExactGauge.AngularLocalization.clock`, `OAI.SLEExactGauge.AngularLocalization.hit`, `OAI.SLEExactGauge.AngularLocalization.hitTime`, `OAI.SLEExactGauge.AngularLocalization.physicalWeight`, `OAI.SLEExactGauge.AngularLocalization.radiusKernel`, `OAI.SLEExactGauge.AngularLocalization.radiusPhysicalRate`, `OAI.SLEExactGauge.AngularLocalization.radiusValue`, `OAI.SLEExactGauge.AngularLocalization.weight`, `OAI.SLEExactGauge.BeforeFirstModulus`, `OAI.SLEExactGauge.BoundaryClockSolution`, `OAI.SLEExactGauge.BoundaryComparisonFailure`, `OAI.SLEExactGauge.BoundaryLocalization`, `OAI.SLEExactGauge.BrownianField.FieldRegular`, `OAI.SLEExactGauge.BrownianIto.quadraticSum`, `OAI.SLEExactGauge.BrownianPredictable.dyadicQuadraticError`, `OAI.SLEExactGauge.BrownianPredictable.dyadicTime`, `OAI.SLEExactGauge.BrownianPredictable.pastSigma`, `OAI.SLEExactGauge.BrownianPredictable.predictableFeatureSum`, `OAI.SLEExactGauge.ClippedLogSolution`, `OAI.SLEExactGauge.ClippedLogSolution.velocity`, `OAI.SLEExactGauge.FiniteIncreasingClock`, `OAI.SLEExactGauge.FiniteIncreasingClock.inverse`, `OAI.SLEExactGauge.FiniteIncreasingClock.iso`, `OAI.SLEExactGauge.IsPositiveBoundaryClockPath`, `OAI.SLEExactGauge.IsStripWeakGradient`, `OAI.SLEExactGauge.PreSwallowExcursion`, `OAI.SLEExactGauge.PredictableLimit.dyadicDriverSum`, `OAI.SLEExactGauge.RadialLocalization`, `OAI.SLEExactGauge.RegularSLEPresentation`, `OAI.SLEExactGauge.RegularSLEPresentation.boundedDiskHit`, `OAI.SLEExactGauge.RegularSLEPresentation.filtration`, `OAI.SLEExactGauge.RegularSLEPresentation.sourceFiniteGreenKernel`, `OAI.SLEExactGauge.RegularSLEPresentation.sourceScaled`, `OAI.SLEExactGauge.SmoothTimeBrownianField`, `OAI.SLEExactGauge.SourceActualSquareTailTarget_allKappa`, `OAI.SLEExactGauge.SourceCapacityScalingTarget`, `OAI.SLEExactGauge.SourceChartedDiskRuleTarget`, `OAI.SLEExactGauge.SourceConditionalApproachTarget`, `OAI.SLEExactGauge.SourceDisjointWindows` and 289 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `SLE_ActualRetainedKernel`, `SLE_AngularLaws`, `SLE_AngularMoments`, `SLE_AngularPowerDynkin`, `SLE_BoundaryDensity`, `SLE_BrownianGenerators`, `SLE_BrownianStrongMarkov`, `SLE_ChartMeasurability`, `SLE_ClippedCoordinates`, `SLE_DiskHalfPlane`, `SLE_DyadicStrips`, `SLE_ExponentialMartingales`, `SLE_FiniteMass`, `SLE_FiniteRadiusStop`, `SLE_FiniteStoppedLaw`, `SLE_GreenCovariance`, `SLE_HausdorffLimits`, `SLE_IntegralLimits`, `SLE_InteriorDiskProof`, `SLE_InteriorEntrance`, `SLE_IntervalDensity`, `SLE_InverseMoments`, `SLE_ItoIsometry`, `SLE_KernelConsistency`, `SLE_KernelExpectation`, `SLE_LoewnerCharts`, `SLE_LoewnerReflection`, `SLE_LowerRestartConditionalAllKappa`, `SLE_MeasureSupport`, `SLE_NearRealContraction`, `SLE_NestedMeans`, `SLE_OccupationBound`, `SLE_OptionalStopping`, `SLE_PhysicalKernelUtilities`, `SLE_PhysicalMeshPast`, `SLE_PhysicalMeshWindowCore`, `SLE_PhysicalTransport`, `SLE_RadiusClocks`, `SLE_RectangleMeans`, `SLE_RetainedDyadicGeometry`, `SLE_RetainedSeedMoments`, `SLE_SausagePointBound`, `SLE_SimpleFields`, `SLE_SimplePastMesh`, `SLE_SimpleTails`, `SLE_SpatialMeans`, `SLE_StochasticFubini`, `SLE_StochasticIntegrals`, `SLE_StoppedFields`, `SLE_StoppedKernels`, `SLE_StoppedMeasures`, `SLE_StoppedPower`, `SLE_StripKernels`, `SLE_StripProbabilities`, `SLE_SwallowExit`, `SLE_SwallowLyapunov`, `SLE_TracePosCombined`, `SLE_WindowAssembly`, `SLE_WindowBGeometry`, `SLE_WindowBounds`, `SLE_WindowGeometry`, `SLE_WindowPropagation`, `SLE_WindowTails`.
--
--   **Imports.** It imports the published bundle `Def_SLELowerPositivity`.
--
--   **Imported by** (directly, in this split): the statements `OAI.SLEExactGauge.RegularSLEPresentation.source_actual_retained_experiment_allKappa`, `OAI.SLEExactGauge.RegularSLEPresentation.source_past_spatial_slab_finite_exponential`, `OAI.SLEExactGauge.RegularSLEPresentation.spatial_slab_terminal_exponential`, `OAI.SLEExactGauge.sourceActualSquareTail_proved_allKappa` and `OAI.SLEExactGauge.source_mesh_parameters`; the proofs of `OAI.SLEExactGauge.RegularSLEPresentation.source_actual_retained_experiment_allKappa`, `OAI.SLEExactGauge.RegularSLEPresentation.source_past_spatial_slab_finite_exponential`, `OAI.SLEExactGauge.RegularSLEPresentation.spatial_slab_terminal_exponential`, `OAI.SLEExactGauge.sourceActualSquareTail_proved_allKappa`, `OAI.SLEExactGauge.sourceLowerMain_proved`, `OAI.SLEExactGauge.source_interior_disk_unnormalized` and `OAI.SLEExactGauge.source_mesh_parameters`.
-- source:
--   OpenAI, An explicit exact Hausdorff gauge for SLE, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 230; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_SLELowerPositivity

section
-- module Solutions.OAIQ27_SLE.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_BrownianGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Brownian Generators for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure SmoothTimeBrownianField {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t)) (K : ℝ≥0)
    (F a : ℝ≥0 → Ω → ℝ → ℝ) : Prop where
  smooth : ∀ t ω, ContDiff ℝ 3 (F t ω)
  adapted : ∀ t j, j ≤ 2 → Measurable[
    (Filtration.natural B (fun t => (hm t).stronglyMeasurable) t).prod (borel ℝ)]
    (fun q : Ω × ℝ => iteratedDeriv j (F t q.1) q.2)
  joint : ∀ j, j ≤ 2 → Measurable
    (fun q : (ℝ≥0 × Ω) × ℝ => iteratedDeriv j (F q.1.1 q.1.2) q.2)
  drift_joint : Measurable (fun q : (ℝ≥0 × Ω) × ℝ => a q.1.1 q.1.2 q.2)
  bound : ∀ t ω x j, j ≤ 3 → |iteratedDeriv j (F t ω) x| ≤ K
  drift_bound : ∀ t ω x, |a t ω x| ≤ K
  drift_lipschitz : ∀ t ω x y, |a t ω x - a t ω y| ≤ (K : ℝ) * |x - y|
  second_lipschitz : ∀ s t ω x y,
    |iteratedDeriv 2 (F t ω) x - iteratedDeriv 2 (F s ω) y| ≤
      (K : ℝ) * (|(t : ℝ) - s| + |x - y|)
  time_increment : ∀ s t : ℝ≥0, s ≤ t → ∀ ω x,
    F t ω x - F s ω x = ∫ u in (s : ℝ)..(t : ℝ), a u.toNNReal ω x

noncomputable def brownianFieldDrift {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F a : ℝ≥0 → Ω → ℝ → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  a u.toNNReal ω (B u.toNNReal ω) +
    (1 / 2 : ℝ) * iteratedDeriv 2 (F u.toNNReal ω) (B u.toNNReal ω)

noncomputable def standardGaussianAbsMoment (m : ℕ) : ℝ :=
  ∫ x : ℝ, |x| ^ m ∂gaussianReal 0 1

noncomputable def dynkinRate (δ : ℝ≥0) : ℝ :=
  Real.sqrt δ * standardGaussianAbsMoment 3 + Real.sqrt δ * standardGaussianAbsMoment 1 +
    (1 / 2 : ℝ) * ((δ : ℝ) + Real.sqrt δ * standardGaussianAbsMoment 1)



end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_OptionalStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Optional Stopping for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge


noncomputable def stopGridIndex (n : ℕ) (t : ℝ≥0) : ℕ :=
  Nat.ceil (((n : ℝ≥0) + 1) * t)

noncomputable def stopGridTime (n k : ℕ) : ℝ≥0 :=
  (k : ℝ≥0) / ((n : ℝ≥0) + 1)

noncomputable def stopGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  stopGridTime n (stopGridIndex n t)

noncomputable def brownianFieldCompensated {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F a : ℝ≥0 → Ω → ℝ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  F t ω (B t ω) - ∫ u in (0 : ℝ)..(t : ℝ), brownianFieldDrift B F a u ω

lemma monotone_stopGridTime (n : ℕ) : Monotone (stopGridTime n) := by
  intro i j hij
  dsimp only [stopGridTime]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)

noncomputable def gridFiltration {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (n : ℕ) : Filtration ℕ mΩ where
  seq j := ℱ (stopGridTime n j)
  mono' := fun _ _ hij => ℱ.mono (monotone_stopGridTime n hij)
  le' j := ℱ.le (stopGridTime n j)

noncomputable def picardApprox
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : ℝ → Ω → E → E) (x₀ : E) : ℕ → ℝ → Ω → E
  | 0, _, _ => x₀
  | n + 1, t, ω => x₀ + ∫ u in Ioc (0 : ℝ) t, V u ω (picardApprox V x₀ n u ω)

lemma picardApprox_measurable
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (V : ℝ → Ω → E → E) (x₀ : E)
    (hV : Measurable (fun q : (ℝ × Ω) × E => V q.1.1 q.1.2 q.2)) (n : ℕ) :
    Measurable (fun q : ℝ × Ω => picardApprox V x₀ n q.1 q.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hf : Measurable (fun q : (ℝ × Ω) × ℝ => V q.2 q.1.2 (picardApprox V x₀ n q.2 q.1.2)) :=
      hV.comp ((measurable_snd.prodMk measurable_fst.snd).prodMk
        (ih.comp (measurable_snd.prodMk measurable_fst.snd)))
    let A : Set ((ℝ × Ω) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ q.1.1}
    have hA : MeasurableSet A :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst.fst)
    have hm := ((hf.indicator hA).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
    apply measurable_const.add
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    funext q
    rw [← integral_indicator measurableSet_Ioc]
    rfl

lemma picardApprox_eq_iterate
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : ℝ → Ω → E → E} {x₀ : E} {T L K : ℝ≥0} (ω : Ω)
    (hf : IsPicardLindelof (fun t x => V t ω x)
      (⟨0, ⟨le_rfl, T.coe_nonneg⟩⟩ : Icc (0 : ℝ) T) x₀ (L * T) 0 L K)
    (α₀ : ODE.FunSpace (⟨0, ⟨le_rfl, T.coe_nonneg⟩⟩ : Icc (0 : ℝ) T) x₀ 0 L)
    (hα₀ : ∀ t, α₀ t = x₀) (n : ℕ) (t : Icc (0 : ℝ) T) :
    picardApprox V x₀ n t ω =
      ((ODE.FunSpace.next hf (Metric.mem_closedBall_self (le_refl (0 : ℝ))))^[n] α₀) t := by
  induction n generalizing t with
  | zero => exact (hα₀ t).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ODE.FunSpace.next_apply, ODE.picard_apply]
    dsimp only [picardApprox]
    congr 1
    rw [intervalIntegral.integral_of_le t.property.1]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) T := ⟨hu.1.le, hu.2.trans t.property.2⟩
    exact congrArg (V u ω) ((ih ⟨u, hu'⟩).trans (ODE.FunSpace.compProj_of_mem hu').symm)



noncomputable def clippedHeight (lo hi : ℝ) (hle : lo ≤ hi) (q : ℂ × ℝ) : ℝ :=
  Real.exp (projIcc lo hi hle q.1.im)

noncomputable def clippedCenter (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q : ℂ × ℝ) : ℂ :=
  ((q.1.re - u : ℝ) : ℂ) + (clippedHeight lo hi hle q : ℂ) * Complex.I

noncomputable def clippedLogLoewnerField (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ)
    (q : ℂ × ℝ) : ℂ × ℝ :=
  let v := (clippedCenter lo hi hle u q)⁻¹
  (((2 * v.re : ℝ) : ℂ) + ((-2 * Complex.normSq v : ℝ) : ℂ) * Complex.I,
    (-2 * v ^ 2).re)

lemma clippedHeight_pos (lo hi : ℝ) (hle : lo ≤ hi) (q : ℂ × ℝ) :
    0 < clippedHeight lo hi hle q := Real.exp_pos _

lemma clippedHeight_bounds (lo hi : ℝ) (hle : lo ≤ hi) (q : ℂ × ℝ) :
    Real.exp lo ≤ clippedHeight lo hi hle q ∧ clippedHeight lo hi hle q ≤ Real.exp hi := by
  exact ⟨Real.exp_le_exp.mpr (projIcc lo hi hle q.1.im).property.1,
    Real.exp_le_exp.mpr (projIcc lo hi hle q.1.im).property.2⟩

lemma clippedCenter_im (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q : ℂ × ℝ) :
    (clippedCenter lo hi hle u q).im = clippedHeight lo hi hle q := by
  simp [clippedCenter]

lemma clippedCenter_ne_zero (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q : ℂ × ℝ) :
    clippedCenter lo hi hle u q ≠ 0 := by
  intro hh
  have he := congrArg Complex.im hh
  rw [clippedCenter_im] at he
  exact (clippedHeight_pos lo hi hle q).ne' he

lemma exp_clamp_lipschitz (lo hi : ℝ) (hle : lo ≤ hi) :
    LipschitzWith ⟨Real.exp hi, (Real.exp_pos hi).le⟩
      (fun x : ℝ => Real.exp (projIcc lo hi hle x)) := by
  have hf : LipschitzOnWith ⟨Real.exp hi, (Real.exp_pos hi).le⟩ Real.exp (Icc lo hi) := by
    apply (convex_Icc lo hi).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    intro x hx
    change ‖Real.exp x‖ ≤ Real.exp hi
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
    exact Real.exp_le_exp.mpr hx.2
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ Real.exp hi * dist (projIcc lo hi hle x : ℝ) (projIcc lo hi hle y : ℝ) :=
      hf.dist_le_mul (projIcc lo hi hle x) (projIcc lo hi hle x).property
        (projIcc lo hi hle y) (projIcc lo hi hle y).property
    _ ≤ Real.exp hi * dist x y := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos hi).le
      have hp := (LipschitzWith.projIcc hle).dist_le_mul x y
      change dist (projIcc lo hi hle x : ℝ) (projIcc lo hi hle y : ℝ) ≤ (1 : ℝ) * dist x y at hp
      simpa only [one_mul] using hp

end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ClippedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipped Coordinates for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
lemma clippedCenter_norm_lower (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q : ℂ × ℝ) :
    Real.exp lo ≤ ‖clippedCenter lo hi hle u q‖ := by
  calc
    _ ≤ clippedHeight lo hi hle q := (clippedHeight_bounds lo hi hle q).1
    _ = (clippedCenter lo hi hle u q).im := (clippedCenter_im lo hi hle u q).symm
    _ ≤ ‖clippedCenter lo hi hle u q‖ := Complex.im_le_norm _

lemma clippedCenter_inv_norm_bound (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q : ℂ × ℝ) :
    ‖(clippedCenter lo hi hle u q)⁻¹‖ ≤ (Real.exp lo)⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (Real.exp_pos lo) (clippedCenter_norm_lower lo hi hle u q)

lemma clippedCenter_dist (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q r : ℂ × ℝ) :
    dist (clippedCenter lo hi hle u q) (clippedCenter lo hi hle u r) ≤
      (1 + Real.exp hi) * dist q r := by
  have he := (exp_clamp_lipschitz lo hi hle).dist_le_mul q.1.im r.1.im
  have hY : |clippedHeight lo hi hle q - clippedHeight lo hi hle r| ≤
      Real.exp hi * ‖q.1 - r.1‖ := by
    change |Real.exp (projIcc lo hi hle q.1.im) - Real.exp (projIcc lo hi hle r.1.im)| ≤ _
    change |Real.exp (projIcc lo hi hle q.1.im) - Real.exp (projIcc lo hi hle r.1.im)| ≤
      Real.exp hi * |q.1.im - r.1.im| at he
    exact he.trans
      (mul_le_mul_of_nonneg_left (show |q.1.im - r.1.im| ≤ ‖q.1 - r.1‖ from
        Complex.abs_im_le_norm (q.1 - r.1)) (Real.exp_pos hi).le)
  have hX : |q.1.re - r.1.re| ≤ ‖q.1 - r.1‖ := Complex.abs_re_le_norm (q.1 - r.1)
  have hsub : clippedCenter lo hi hle u q - clippedCenter lo hi hle u r =
      ((q.1.re - r.1.re : ℝ) : ℂ) +
        ((clippedHeight lo hi hle q - clippedHeight lo hi hle r : ℝ) : ℂ) * Complex.I := by
    simp only [clippedCenter, Complex.ofReal_sub]
    ring
  rw [dist_eq_norm, hsub]
  calc
    _ ≤ |q.1.re - r.1.re| + |clippedHeight lo hi hle q - clippedHeight lo hi hle r| := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] using
        norm_add_le ((q.1.re - r.1.re : ℝ) : ℂ)
          (((clippedHeight lo hi hle q - clippedHeight lo hi hle r : ℝ) : ℂ) * Complex.I)
    _ ≤ (1 + Real.exp hi) * ‖q.1 - r.1‖ := by linarith
    _ ≤ (1 + Real.exp hi) * dist q r := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [dist_eq_norm]
      exact norm_fst_le (q - r)

lemma clippedCenter_inv_dist (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ) (q r : ℂ × ℝ) :
    dist (clippedCenter lo hi hle u q)⁻¹ (clippedCenter lo hi hle u r)⁻¹ ≤
      ((Real.exp lo)⁻¹ ^ 2 * (1 + Real.exp hi)) * dist q r := by
  let b := (Real.exp lo)⁻¹
  have hb : 0 ≤ b := by dsimp [b]; positivity
  rw [dist_eq_norm, inv_sub_inv' (clippedCenter_ne_zero lo hi hle u q)
    (clippedCenter_ne_zero lo hi hle u r), norm_mul, norm_mul]
  calc
    _ ≤ b * ((1 + Real.exp hi) * dist q r) * b := by
      gcongr
      · exact clippedCenter_inv_norm_bound lo hi hle u q
      · simpa only [← dist_eq_norm, dist_comm] using clippedCenter_dist lo hi hle u q r
      · exact clippedCenter_inv_norm_bound lo hi hle u r
    _ = _ := by dsimp [b]; ring

noncomputable def logLoewnerVector (v : ℂ) : ℂ × ℝ :=
  (((2 * v.re : ℝ) : ℂ) + ((-2 * Complex.normSq v : ℝ) : ℂ) * Complex.I,
    (-2 * v ^ 2).re)

lemma bounded_normSq_dist {v w : ℂ} {b : ℝ} (hv : ‖v‖ ≤ b) (hw : ‖w‖ ≤ b) :
    |Complex.normSq v - Complex.normSq w| ≤ 2 * b * dist v w := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    show ‖v‖ ^ 2 - ‖w‖ ^ 2 = (‖v‖ - ‖w‖) * (‖v‖ + ‖w‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg v) (norm_nonneg w))]
  calc
    _ ≤ ‖v - w‖ * (‖v‖ + ‖w‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le v w)
        (add_nonneg (norm_nonneg v) (norm_nonneg w))
    _ ≤ ‖v - w‖ * (b + b) := by gcongr
    _ = _ := by rw [dist_eq_norm]; ring

lemma bounded_sq_dist {v w : ℂ} {b : ℝ} (hv : ‖v‖ ≤ b) (hw : ‖w‖ ≤ b) :
    ‖v ^ 2 - w ^ 2‖ ≤ 2 * b * dist v w := by
  rw [show v ^ 2 - w ^ 2 = (v - w) * (v + w) by ring, norm_mul]
  calc
    _ ≤ ‖v - w‖ * (‖v‖ + ‖w‖) := mul_le_mul_of_nonneg_left (norm_add_le v w) (norm_nonneg _)
    _ ≤ ‖v - w‖ * (b + b) := by gcongr
    _ = _ := by rw [dist_eq_norm]; ring

lemma logLoewnerVector_dist {v w : ℂ} {b : ℝ} (hv : ‖v‖ ≤ b) (hw : ‖w‖ ≤ b) :
    dist (logLoewnerVector v) (logLoewnerVector w) ≤ (2 + 4 * b) * dist v w := by
  rw [dist_eq_norm]
  apply norm_prod_le_iff.mpr
  constructor
  · have hr : ((logLoewnerVector v - logLoewnerVector w).1).re = 2 * (v.re - w.re) := by
      simp [logLoewnerVector]
      ring
    have hi : ((logLoewnerVector v - logLoewnerVector w).1).im =
        -2 * (Complex.normSq v - Complex.normSq w) := by
      simp [logLoewnerVector]
      ring
    have hRe : |v.re - w.re| ≤ dist v w := by
      simpa only [dist_eq_norm, Complex.sub_re] using Complex.abs_re_le_norm (v - w)
    calc
      _ ≤ |((logLoewnerVector v - logLoewnerVector w).1).re| +
          |((logLoewnerVector v - logLoewnerVector w).1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = 2 * |v.re - w.re| + 2 * |Complex.normSq v - Complex.normSq w| := by
        rw [hr, hi, abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * dist v w + 2 * (2 * b * dist v w) := by
        gcongr
        exact bounded_normSq_dist hv hw
      _ = _ := by ring
  · have he : (logLoewnerVector v - logLoewnerVector w).2 = (-2 * (v ^ 2 - w ^ 2)).re := by
      simp only [logLoewnerVector, Prod.snd_sub, mul_sub, Complex.sub_re]
    rw [he, Real.norm_eq_abs]
    calc
      _ ≤ ‖-2 * (v ^ 2 - w ^ 2)‖ := Complex.abs_re_le_norm _
      _ = 2 * ‖v ^ 2 - w ^ 2‖ := by rw [norm_mul]; norm_num
      _ ≤ 2 * (2 * b * dist v w) := by gcongr; exact bounded_sq_dist hv hw
      _ ≤ (2 + 4 * b) * dist v w := by nlinarith [show 0 ≤ dist v w from dist_nonneg]

lemma logLoewnerVector_norm {v : ℂ} {b : ℝ} (hb : 0 ≤ b) (hv : ‖v‖ ≤ b) :
    ‖logLoewnerVector v‖ ≤ (2 + 4 * b) * b := by
  have hh := logLoewnerVector_dist hv (show ‖(0 : ℂ)‖ ≤ b by simpa using hb)
  have h0 : logLoewnerVector 0 = 0 := by simp [logLoewnerVector]
  rw [h0, dist_zero_right, dist_zero_right] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hv (by positivity))

lemma clippedLogLoewnerField_bounds (lo hi : ℝ) (hle : lo ≤ hi) :
    ∃ (L K : ℝ≥0),
      (∀ u q, ‖clippedLogLoewnerField lo hi hle u q‖ ≤ L) ∧
      (∀ u, LipschitzWith K (clippedLogLoewnerField lo hi hle u)) := by
  let b : ℝ := (Real.exp lo)⁻¹
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let L : ℝ≥0 := ⟨(2 + 4 * b) * b, by positivity⟩
  let K : ℝ≥0 := ⟨(2 + 4 * b) * (b ^ 2 * (1 + Real.exp hi)), by positivity⟩
  refine ⟨L, K, ?_, ?_⟩
  · intro u q
    exact logLoewnerVector_norm hb (clippedCenter_inv_norm_bound lo hi hle u q)
  · intro u
    apply LipschitzWith.of_dist_le_mul
    intro q r
    change dist (logLoewnerVector (clippedCenter lo hi hle u q)⁻¹)
      (logLoewnerVector (clippedCenter lo hi hle u r)⁻¹) ≤ _
    calc
      _ ≤ (2 + 4 * b) * dist (clippedCenter lo hi hle u q)⁻¹ (clippedCenter lo hi hle u r)⁻¹ :=
        logLoewnerVector_dist (clippedCenter_inv_norm_bound lo hi hle u q)
          (clippedCenter_inv_norm_bound lo hi hle u r)
      _ ≤ (2 + 4 * b) * ((b ^ 2 * (1 + Real.exp hi)) * dist q r) :=
        mul_le_mul_of_nonneg_left (clippedCenter_inv_dist lo hi hle u q r) (by positivity)
      _ = _ := by
        change (2 + 4 * b) * (b ^ 2 * (1 + Real.exp hi) * dist q r) =
          ((2 + 4 * b) * (b ^ 2 * (1 + Real.exp hi))) * dist q r
        ring

lemma continuous_clippedLogLoewnerField (lo hi : ℝ) (hle : lo ≤ hi) :
    Continuous (fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) := by
  have hZ : Continuous (fun p : ℝ × (ℂ × ℝ) => clippedCenter lo hi hle p.1 p.2) := by
    dsimp only [clippedCenter, clippedHeight]
    fun_prop
  have hv : Continuous (fun p : ℝ × (ℂ × ℝ) => (clippedCenter lo hi hle p.1 p.2)⁻¹) :=
    hZ.inv₀ (fun p => clippedCenter_ne_zero lo hi hle p.1 p.2)
  have hF : Continuous logLoewnerVector := by fun_prop [logLoewnerVector]
  exact hF.comp hv



theorem exists_measurable_bounded_ode_picard
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (V : ℝ → Ω → E → E) (x₀ : E) (T L K : ℝ≥0)
    (hV : Measurable (fun q : (ℝ × Ω) × E => V q.1.1 q.1.2 q.2))
    (hc : ∀ ω x, Continuous (fun t : ℝ => V t ω x))
    (hl : ∀ ω t, LipschitzWith K (V t ω))
    (hb : ∀ ω t x, ‖V t ω x‖ ≤ L) :
    ∃ X : ℝ → Ω → E,
      Measurable (fun q : ℝ × Ω => X q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => X t ω)) ∧
      (∀ ω, X 0 ω = x₀) ∧
      (∀ ω t, t ∈ Icc 0 (T : ℝ) →
        HasDerivWithinAt (fun u => X u ω) (V t ω (X t ω)) (Icc 0 (T : ℝ)) t) ∧
      (∀ t ω, Tendsto (fun n => picardApprox V x₀ n (projIcc 0 (T : ℝ) T.coe_nonneg t) ω) atTop (𝓝 (X t ω))) := by
  let t₀ : Icc (0 : ℝ) T := ⟨0, ⟨le_rfl, T.coe_nonneg⟩⟩
  have hPL (ω : Ω) : IsPicardLindelof (fun t x => V t ω x) t₀ x₀ (L * T) 0 L K := by
    refine ⟨fun t ht => (hl ω t).lipschitzOnWith, fun x hx => (hc ω x).continuousOn,
      fun t ht x hx => hb ω t x, ?_⟩
    simp only [t₀, sub_zero, sub_self, max_eq_left T.coe_nonneg, NNReal.coe_mul,
      NNReal.coe_zero, le_refl]
  have hx : x₀ ∈ Metric.closedBall x₀ (0 : ℝ) := Metric.mem_closedBall_self le_rfl
  choose α hα using fun ω => ODE.FunSpace.exists_isFixedPt_next (hPL ω) hx
  let X (t : ℝ) (ω : Ω) := (α ω).compProj t
  let α₀ : ODE.FunSpace t₀ x₀ 0 L :=
    ⟨fun _ => x₀, (LipschitzWith.const x₀).weaken (show (0 : ℝ≥0) ≤ L from bot_le), hx⟩
  have hα₀ (t : Icc (0 : ℝ) T) : α₀ t = x₀ := rfl
  have hconv (t : Icc (0 : ℝ) T) (ω : Ω) :
      Tendsto (fun n => picardApprox V x₀ n t ω) atTop (𝓝 ((α ω) t)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => ?_) (by simpa only [zero_mul] using (FloorSemiring.tendsto_pow_div_factorial_atTop
        ((K : ℝ) * |(t : ℝ)|)).mul_const (dist α₀ (α ω)))
    have hh := ODE.FunSpace.dist_iterate_next_apply_le (hPL ω) hx α₀ (α ω) n t
    rw [(hα ω).iterate n] at hh
    simpa only [t₀, sub_zero, picardApprox_eq_iterate ω (hPL ω) α₀ hα₀ n t] using hh
  refine ⟨X, ?_, ?_, ?_, ?_, ?_⟩
  · apply measurable_of_tendsto_metrizable
      (f := fun n q => picardApprox V x₀ n (projIcc 0 (T : ℝ) T.coe_nonneg q.1) q.2)
    · intro n
      exact (picardApprox_measurable V x₀ hV n).comp
        (((continuous_subtype_val.comp (continuous_projIcc (h := T.coe_nonneg))).measurable.comp measurable_fst).prodMk measurable_snd)
    · apply tendsto_pi_nhds.mpr
      intro q
      exact hconv (projIcc 0 (T : ℝ) T.coe_nonneg q.1) q.2
  · intro ω
    simpa only [mul_one, X, ODE.FunSpace.compProj, Function.comp_def] using (α ω).lipschitzWith.comp (LipschitzWith.projIcc T.coe_nonneg)
  · intro ω
    change (α ω).compProj 0 = x₀
    rw [ODE.FunSpace.compProj_of_mem t₀.property]
    exact ODE.FunSpace.apply_of_zero (α ω)
  · intro ω t ht
    apply ODE.hasDerivWithinAt_picard_Icc t₀.property (hPL ω).continuousOn_uncurry
      (α ω).continuous_compProj.continuousOn
      (fun s hs => (α ω).compProj_mem_closedBall (t := s) (hPL ω).mul_max_le) x₀ ht
      |>.congr_of_mem _ ht
    intro s hs
    change (α ω).compProj s = ODE.picard (fun t x => V t ω x) t₀ x₀ (α ω).compProj s
    rw [ODE.FunSpace.compProj_of_mem hs]
    nth_rw 1 [← hα ω]
    exact ODE.FunSpace.next_apply (hPL ω) hx (α ω)

  · intro t ω
    exact hconv (projIcc 0 (T : ℝ) T.coe_nonneg t) ω

lemma picardApprox_congr_on
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V W : ℝ → Ω → E → E} (x₀ : E) (t : ℝ)
    (hVW : ∀ s ∈ Icc 0 t, ∀ ω x, V s ω x = W s ω x) (n : ℕ) :
    ∀ s ∈ Icc 0 t, ∀ ω, picardApprox V x₀ n s ω = picardApprox W x₀ n s ω := by
  induction n with
  | zero => intro s hs ω; rfl
  | succ n ih =>
    intro s hs ω
    dsimp only [picardApprox]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have hut : u ∈ Icc 0 t := ⟨hu.1.le, hu.2.trans hs.2⟩
    dsimp only
    rw [ih u hut ω, hVW u hut]

lemma measurable_driver_frozen
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ)
    (hU : Measurable (fun q : ℝ≥0 × Ω => U q.1 q.2))
    (hc : ∀ ω, Continuous (fun t : ℝ≥0 => U t ω)) (t : ℝ≥0) :
    @Measurable (ℝ × Ω) ℝ
      ((borel ℝ).prod (Filtration.natural U
        (fun t => (hU.comp (measurable_prodMk_left (x := t))).stronglyMeasurable) t))
      (borel ℝ) (fun q => U (min q.1.toNNReal t) q.2) := by
  let hm := fun t => (hU.comp (measurable_prodMk_left (x := t))).stronglyMeasurable
  have hp := (Filtration.stronglyAdapted_natural hm).isStronglyProgressive_of_continuous hc
  have hpt := (hp t).measurable
  let : MeasurableSpace Ω := Filtration.natural U hm t
  have htime : Measurable (fun s : ℝ => (⟨min s.toNNReal t, by change min s.toNNReal t ≤ t; exact min_le_right s.toNNReal t⟩ : Iic t)) :=
    ((continuous_real_toNNReal.min continuous_const).measurable).subtype_mk
  exact hpt.comp ((htime.comp measurable_fst).prodMk measurable_snd)



theorem exists_measurable_global_bounded_ode_picard
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (V : ℝ → Ω → E → E) (x₀ : E) (L K : ℝ≥0)
    (hV : Measurable (fun q : (ℝ × Ω) × E => V q.1.1 q.1.2 q.2))
    (hc : ∀ ω x, Continuous (fun t : ℝ => V t ω x))
    (hl : ∀ ω t, LipschitzWith K (V t ω))
    (hb : ∀ ω t x, ‖V t ω x‖ ≤ L) :
    ∃ X : ℝ → Ω → E,
      Measurable (fun q : ℝ × Ω => X q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => X t ω)) ∧
      (∀ ω, X 0 ω = x₀) ∧
      (∀ ω t, 0 ≤ t →
        HasDerivWithinAt (fun u => X u ω) (V t ω (X t ω)) (Ici 0) t) ∧
      (∀ t ω, Tendsto (fun n => picardApprox V x₀ n (max 0 t) ω) atTop (𝓝 (X t ω))) := by
  classical
  have hex (t : ℝ) (ω : Ω) : ∃ v : E,
      Tendsto (fun n => picardApprox V x₀ n (max 0 t) ω) atTop (𝓝 v) := by
    let T : ℝ≥0 := ⟨max 0 t, le_max_left _ _⟩
    obtain ⟨X, _, _, _, _, hconv⟩ := exists_measurable_bounded_ode_picard V x₀ T L K hV hc hl hb
    refine ⟨X t ω, ?_⟩
    have hc0 := hconv t ω
    change Tendsto (fun n => picardApprox V x₀ n (max 0 (min (max 0 t) t)) ω) atTop (𝓝 (X t ω)) at hc0
    simpa only [min_eq_right (le_max_right (0 : ℝ) t)] using hc0
  let Q (t : ℝ) (ω : Ω) := limUnder atTop (fun n => picardApprox V x₀ n (max 0 t) ω)
  have hlim (t : ℝ) (ω : Ω) :
      Tendsto (fun n => picardApprox V x₀ n (max 0 t) ω) atTop (𝓝 (Q t ω)) :=
    tendsto_nhds_limUnder (hex t ω)
  have hmatch (T : ℝ≥0) (X : ℝ → Ω → E)
      (hconv : ∀ t ω, Tendsto (fun n => picardApprox V x₀ n
        (projIcc 0 (T : ℝ) T.coe_nonneg t) ω) atTop (𝓝 (X t ω)))
      (t : ℝ) (ht : t ≤ T) (ω : Ω) : Q t ω = X t ω := by
    apply tendsto_nhds_unique (hlim t ω)
    simpa only [projIcc, min_eq_right ht] using hconv t ω
  refine ⟨Q, ?_, ?_, ?_, ?_, hlim⟩
  · apply measurable_of_tendsto_metrizable (f := fun n (q : ℝ × Ω) => picardApprox V x₀ n (max 0 q.1) q.2)
    · intro n
      exact (picardApprox_measurable V x₀ hV n).comp
        ((measurable_const.max measurable_fst).prodMk measurable_snd)
    · exact tendsto_pi_nhds.mpr fun q => hlim q.1 q.2
  · intro ω
    apply LipschitzWith.of_dist_le_mul
    intro s t
    let T : ℝ≥0 := ⟨max (max 0 s) t, (le_max_left 0 s).trans (le_max_left _ _)⟩
    obtain ⟨X, _, hXl, _, _, hconv⟩ := exists_measurable_bounded_ode_picard V x₀ T L K hV hc hl hb
    rw [hmatch T X hconv s ((le_max_right 0 s).trans (le_max_left _ _)) ω,
      hmatch T X hconv t (le_max_right _ _) ω]
    exact (hXl ω).dist_le_mul s t
  · intro ω
    obtain ⟨X, _, _, hX0, _, hconv⟩ := exists_measurable_bounded_ode_picard V x₀ 0 L K hV hc hl hb
    rw [hmatch 0 X hconv 0 le_rfl ω, hX0 ω]
  · intro ω t ht
    let T : ℝ≥0 := ⟨t + 1, by linarith⟩
    have hlt : t < (T : ℝ) := by change t < t + 1; linarith
    obtain ⟨X, _, _, _, hXd, hconv⟩ := exists_measurable_bounded_ode_picard V x₀ T L K hV hc hl hb
    have heq : (fun s => Q s ω) =ᶠ[𝓝 t] (fun s => X s ω) := by
      filter_upwards [Iic_mem_nhds hlt] with s hs
      exact hmatch T X hconv s hs ω
    have hd := hXd ω t ⟨ht, hlt.le⟩
    have hsets : Icc 0 (T : ℝ) =ᶠ[𝓝 t] Ici 0 := by
      filter_upwards [Iic_mem_nhds hlt] with s hs
      change (0 ≤ s ∧ s ≤ (T : ℝ)) = (0 ≤ s)
      exact propext ⟨And.left, fun h => ⟨h, hs⟩⟩
    have hd' := hd.congr_set hsets
    rw [← hmatch T X hconv t hlt.le ω] at hd'
    exact hd'.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) (heq.eq_of_nhds)

theorem clipped_log_loewner_global_adapted_solution
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ)
    (hU : Measurable (fun q : ℝ≥0 × Ω => U q.1 q.2))
    (hc : ∀ ω, Continuous (fun t : ℝ≥0 => U t ω))
    (lo hi : ℝ) (hle : lo ≤ hi) (q₀ : ℂ × ℝ) :
    ∃ (L : ℝ≥0) (Q : ℝ → Ω → ℂ × ℝ),
      Measurable (fun q : ℝ × Ω => Q q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => Q t ω)) ∧
      (∀ ω, Q 0 ω = q₀) ∧
      (∀ ω t, 0 ≤ t →
        HasDerivWithinAt (fun s => Q s ω)
          (clippedLogLoewnerField lo hi hle (U t.toNNReal ω) (Q t ω))
          (Ici 0) t) ∧
      Adapted (Filtration.natural U (fun t => (hU.comp (measurable_prodMk_left (x := t))).stronglyMeasurable))
        (fun t : ℝ≥0 => Q t) := by
  obtain ⟨L, K, hbound, hlip⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) (q : ℂ × ℝ) := clippedLogLoewnerField lo hi hle (U t.toNNReal ω) q
  have hF := continuous_clippedLogLoewnerField lo hi hle
  have hUr : Measurable (fun q : ℝ × Ω => U q.1.toNNReal q.2) :=
    hU.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun q : (ℝ × Ω) × (ℂ × ℝ) => V q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ × ℝ) => (U q.1.1.toNNReal q.1.2, q.2)))
    exact hF.measurable.comp ((hUr.comp measurable_fst).prodMk measurable_snd)
  have hcont (ω : Ω) (q : ℂ × ℝ) : Continuous (fun t : ℝ => V t ω q) := by
    change Continuous ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun t : ℝ => (U t.toNNReal ω, q)))
    exact hF.comp (((hc ω).comp continuous_real_toNNReal).prodMk continuous_const)
  obtain ⟨Q, hQm, hQl, hQ0, hQd, hQconv⟩ :=
    exists_measurable_global_bounded_ode_picard V q₀ L K hm hcont
      (fun ω t => hlip (U t.toNNReal ω)) (fun ω t q => hbound (U t.toNNReal ω) q)
  refine ⟨L, Q, hQm, hQl, hQ0, hQd, ?_⟩
  intro t
  have hUfrozen := measurable_driver_frozen U hU hc t
  let m := Filtration.natural U (fun t => (hU.comp measurable_prodMk_left).stronglyMeasurable) t
  let : MeasurableSpace Ω := m
  let W (s : ℝ) (ω : Ω) (q : ℂ × ℝ) :=
    clippedLogLoewnerField lo hi hle (U (min s.toNNReal t) ω) q
  have hW : Measurable (fun q : (ℝ × Ω) × (ℂ × ℝ) => W q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ × ℝ) => (U (min q.1.1.toNNReal t) q.1.2, q.2)))
    exact hF.measurable.comp ((hUfrozen.comp measurable_fst).prodMk measurable_snd)
  have heq (n : ℕ) (ω : Ω) : picardApprox W q₀ n (t : ℝ) ω = picardApprox V q₀ n (t : ℝ) ω := by
    apply picardApprox_congr_on q₀ (t : ℝ) _ n (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩ ω
    intro s hs ω q
    have hh : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    simp only [W, V, min_eq_left hh]
  apply measurable_of_tendsto_metrizable (f := fun n ω => picardApprox W q₀ n (t : ℝ) ω)
  · intro n
    exact (picardApprox_measurable W q₀ hW n).comp measurable_prodMk_left
  · apply tendsto_pi_nhds.mpr
    intro ω
    simpa only [heq, max_eq_right t.coe_nonneg] using hQconv t ω

noncomputable def spatialPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E × ℝ → ℝ) : ℕ → E × ℝ → ℝ
  | 0 => φ
  | n + 1 => fun p => fderiv ℝ (spatialPartial φ n) p (0, 1)

noncomputable def greenExponent (κ : ℝ) : ℝ := 8 / κ - 1

 

noncomputable def greenLogNormSq (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  (q.1.re - Real.sqrt κ * x) ^ 2 + Real.exp (2 * q.1.im)
noncomputable def greenLogDensity (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  Real.exp (-codimension κ * Real.log 2 + codimension κ * q.2 +
    (greenExponent κ - codimension κ) * q.1.im -
      (greenExponent κ / 2) * Real.log (greenLogNormSq κ q x))
noncomputable def physicalLogLoewnerField (u : ℝ) (q : ℂ × ℝ) : ℂ × ℝ :=
  let Z := ((q.1.re - u : ℝ) : ℂ) + (Real.exp q.1.im : ℂ) * Complex.I
  let v := Z⁻¹
  (((2 * v.re : ℝ) : ℂ) + ((-2 * Complex.normSq v : ℝ) : ℂ) * Complex.I,
    (-2 * v ^ 2).re)

lemma greenLogNormSq_pos (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    0 < greenLogNormSq κ q x :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (Real.exp_pos _)

lemma physicalLogLoewnerField_components (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    (physicalLogLoewnerField (Real.sqrt κ * x) q).1.re =
      2 * (q.1.re - Real.sqrt κ * x) / greenLogNormSq κ q x ∧
    (physicalLogLoewnerField (Real.sqrt κ * x) q).1.im =
      -2 / greenLogNormSq κ q x ∧
    (physicalLogLoewnerField (Real.sqrt κ * x) q).2 =
      -2 * ((q.1.re - Real.sqrt κ * x) ^ 2 - Real.exp (2 * q.1.im)) /
        (greenLogNormSq κ q x) ^ 2 := by
  let Z : ℂ := ((q.1.re - Real.sqrt κ * x : ℝ) : ℂ) + (Real.exp q.1.im : ℂ) * Complex.I
  have hre : Z.re = q.1.re - Real.sqrt κ * x := by simp [Z]
  have him : Z.im = Real.exp q.1.im := by
    simp only [Z, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]
  have he : Real.exp q.1.im * Real.exp q.1.im = Real.exp (2 * q.1.im) := by
    rw [← Real.exp_add]; congr 1; ring
  have hn : Complex.normSq Z = greenLogNormSq κ q x := by
    rw [Complex.normSq_apply, hre, him, he]
    simp only [greenLogNormSq, pow_two]
  change (((2 * Z⁻¹.re : ℝ) : ℂ) + ((-2 * Complex.normSq Z⁻¹ : ℝ) : ℂ) * Complex.I).re = _ ∧
    (((2 * Z⁻¹.re : ℝ) : ℂ) + ((-2 * Complex.normSq Z⁻¹ : ℝ) : ℂ) * Complex.I).im = _ ∧
    (-2 * Z⁻¹ ^ 2).re = _
  constructor
  · simp [Complex.inv_re, hre, hn, mul_div_assoc]
  constructor
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero,
      Complex.normSq_inv, hn, div_eq_mul_inv]
  · simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.re_ofNat, Complex.im_ofNat, neg_zero, zero_mul, sub_zero,
      Complex.inv_re, Complex.inv_im, hre, him, hn]
    have he2 : Real.exp q.1.im ^ 2 = Real.exp (2 * q.1.im) := by simpa only [pow_two] using he
    rw [← he2]
    field_simp


lemma clippedLogLoewnerField_eq_physical (lo hi : ℝ) (hle : lo ≤ hi) (u : ℝ)
    (q : ℂ × ℝ) (hq : q.1.im ∈ Icc lo hi) :
    clippedLogLoewnerField lo hi hle u q = physicalLogLoewnerField u q := by
  simp only [clippedLogLoewnerField, clippedCenter, clippedHeight, projIcc_of_mem hle hq,
    physicalLogLoewnerField]

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_LoewnerCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Loewner Charts for chordal SLE. -/

section
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge


lemma survivingDomain_antitone (γ : ℝ≥0 → ℂ) : Antitone (survivingDomain γ) := by
  intro s t hst z hz
  have hpast : γ '' Icc 0 s ⊆ γ '' Icc 0 t := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, ⟨hu.1, hu.2.trans hst⟩, rfl⟩
  have hb : upperHalfPlane \ (γ '' Icc 0 t) ⊆ upperHalfPlane \ (γ '' Icc 0 s) := by
    intro w hw
    exact ⟨hw.1, fun hh => hw.2 (hpast hh)⟩
  exact ⟨hb hz.1, fun hbounded => hz.2 (hbounded.subset (connectedComponentIn_mono z hb))⟩

lemma isOpen_upperHalfPlane : IsOpen upperHalfPlane := isOpen_lt continuous_const Complex.continuous_im

lemma isOpen_survivingDomain {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (t : ℝ≥0) :
    IsOpen (survivingDomain γ t) := by
  have hb : IsOpen (upperHalfPlane \ (γ '' Icc 0 t)) :=
    isOpen_upperHalfPlane.sdiff (isCompact_Icc.image hγ).isClosed
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  refine ⟨connectedComponentIn (upperHalfPlane \ (γ '' Icc 0 t)) z, ?_,
    hb.connectedComponentIn, mem_connectedComponentIn hz.1⟩
  intro w hw
  refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
  rw [← connectedComponentIn_eq hw]
  exact hz.2

lemma IsCapacityTwoWitness.time_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => G v.toNNReal z)
      (2 / (G u.toNNReal z - (U u.toNNReal : ℂ))) (Icc 0 (T : ℝ)) u := by
  rcases h with ⟨hγ, hγ0, hγim, hG, hF, hGmap, hFmap, hinv, hinv', h0, hode, hnorm, htip⟩
  have hlu : u.toNNReal ≤ T := by
    exact_mod_cast (show (u.toNNReal : ℝ) ≤ (T : ℝ) by rw [Real.coe_toNNReal _ hu.1]; exact hu.2)
  have hh := (hode u.toNNReal z (survivingDomain_antitone γ hlu hz)).mono
    (show Icc (0 : ℝ) T ⊆ Ici 0 from Icc_subset_Ici_self)
  simpa only [Real.coe_toNNReal _ hu.1] using hh

lemma IsCapacityTwoWitness.time_continuousOn
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) :
    ContinuousOn (fun v : ℝ => G v.toNNReal z) (Icc 0 (T : ℝ)) :=
  fun u hu => (h.time_derivative T z hz u hu).continuousWithinAt

lemma IsCapacityTwoWitness.imag_positive
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) : 0 < (G t z).im := h.2.2.2.2.2.1 t hz

lemma IsCapacityTwoWitness.centered_ne_zero
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) : G t z - (U t : ℂ) ≠ 0 := by
  intro hh
  have hi := congrArg Complex.im hh
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
  exact (h.imag_positive t z hz).ne' hi

lemma IsCapacityTwoWitness.imag_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => (G v.toNNReal z).im)
      (-2 * (G u.toNNReal z).im / Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ)))
      (Icc 0 (T : ℝ)) u := by
  have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt u (h.time_derivative T z hz u hu)
  simpa [Function.comp_def, Complex.div_im, neg_div] using hh

lemma IsCapacityTwoWitness.imag_antitoneOn
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) :
    AntitoneOn (fun v : ℝ => (G v.toNNReal z).im) (Icc 0 (T : ℝ)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (Complex.continuous_im.comp_continuousOn (h.time_continuousOn T z hz))
    (fun u hu => (h.imag_derivative T z hz u (interior_subset hu)).mono interior_subset)
  intro u hu
  have hu' : u ∈ Icc 0 (T : ℝ) := interior_subset hu
  have hle : u.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe).mpr hu'.2
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (h.imag_positive u.toNNReal z (survivingDomain_antitone γ hle hz)).le)
    (Complex.normSq_nonneg _)

 

lemma complex_linear_ode_exp (T : ℝ) (hT : 0 ≤ T) (f c : ℝ → ℂ)
    (hc : ContinuousOn c (Icc 0 T))
    (hf : ∀ u ∈ Icc 0 T, HasDerivWithinAt f (c u * f u) (Icc 0 T) u) :
    f T = f 0 * Complex.exp (∫ u in (0 : ℝ)..T, c u) := by
  by_cases hT0 : T = 0
  · simp [hT0]
  have hTp : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
  let C (u : ℝ) : ℂ := c (projIcc 0 T hT u)
  have hC : Continuous C := hc.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun u => (projIcc 0 T hT u).property)
  have hCc (u : ℝ) (hu : u ∈ Icc 0 T) : C u = c u := by simp only [C, projIcc_of_mem hT hu]
  let I (u : ℝ) : ℂ := ∫ v in (0 : ℝ)..u, C v
  have hI (u : ℝ) : HasDerivAt I (C u) u :=
    intervalIntegral.integral_hasDerivAt_right (hC.intervalIntegrable _ _)
      hC.aestronglyMeasurable.stronglyMeasurableAtFilter hC.continuousAt
  have hd (u : ℝ) (hu : u ∈ Icc 0 T) :
      HasDerivWithinAt (fun v => f v * Complex.exp (-I v)) 0 (Icc 0 T) u := by
    convert (hf u hu).mul ((hI u).neg.cexp.hasDerivWithinAt) using 1
    all_goals try with_reducible_and_instances rfl
    try rfl
    rw [hCc u hu]
    ring
  have hid : ∀ u ∈ Icc 0 T, DifferentiableWithinAt ℝ (fun v => f v * Complex.exp (-I v)) (Icc 0 T) u :=
    fun u hu => (hd u hu).differentiableWithinAt
  have he := constant_of_derivWithin_zero hid (fun u hu =>
    (hd u ⟨hu.1, hu.2.le⟩).derivWithin (uniqueDiffOn_Icc hTp u ⟨hu.1, hu.2.le⟩)) T ⟨hT, le_rfl⟩
  have hfactor : f T * Complex.exp (-I T) = f 0 := by
    simpa only [I, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, mul_one] using he
  have hInt : I T = ∫ u in (0 : ℝ)..T, c u := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact hCc u (by simpa only [uIcc_of_le hT] using hu)
  calc
    f T = (f T * Complex.exp (-I T)) * Complex.exp (I T) := by
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = _ := by rw [hfactor, hInt]

lemma IsCapacityTwoWitness.live_at_real_time
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (_h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ≤ (T : ℝ)) :
    z ∈ survivingDomain γ u.toNNReal :=
  survivingDomain_antitone γ (Real.toNNReal_le_iff_le_coe.mpr hu) hz

lemma IsCapacityTwoWitness.spatial_differentiableAt
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) : DifferentiableAt ℂ (G t) z :=
  (h.2.2.2.1 t z hz).differentiableAt ((isOpen_survivingDomain h.1 t).mem_nhds hz)

lemma IsCapacityTwoWitness.initial_value
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (z : ℂ) (hz : z ∈ upperHalfPlane) : G 0 z = z :=
  h.2.2.2.2.2.2.2.2.2.1 z hz

noncomputable def loewnerPairCoefficient
    (U : ℝ≥0 → ℝ) (G : ℝ≥0 → ℂ → ℂ) (w z : ℂ) (u : ℝ) : ℂ :=
  (-2 : ℂ) / ((G u.toNNReal w - (U u.toNNReal : ℂ)) *
    (G u.toNNReal z - (U u.toNNReal : ℂ)))

lemma IsCapacityTwoWitness.pair_coefficient_continuousOn
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w z : ℂ)
    (hw : w ∈ survivingDomain γ T) (hz : z ∈ survivingDomain γ T) :
    ContinuousOn (loewnerPairCoefficient U G w z) (Icc 0 (T : ℝ)) := by
  have hUc : Continuous (fun u : ℝ => (U u.toNNReal : ℂ)) :=
    Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)
  exact continuousOn_const.div
    (((h.time_continuousOn T w hw).sub hUc.continuousOn).mul
      ((h.time_continuousOn T z hz).sub hUc.continuousOn))
    (fun u hu => mul_ne_zero (h.centered_ne_zero _ w (h.live_at_real_time T w hw u hu.2))
      (h.centered_ne_zero _ z (h.live_at_real_time T z hz u hu.2)))

lemma IsCapacityTwoWitness.difference_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w z : ℂ)
    (hw : w ∈ survivingDomain γ T) (hz : z ∈ survivingDomain γ T)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => G v.toNNReal w - G v.toNNReal z)
      (loewnerPairCoefficient U G w z u * (G u.toNNReal w - G u.toNNReal z))
      (Icc 0 (T : ℝ)) u := by
  have hw0 := h.centered_ne_zero _ w (h.live_at_real_time T w hw u hu.2)
  have hz0 := h.centered_ne_zero _ z (h.live_at_real_time T z hz u hu.2)
  have he : loewnerPairCoefficient U G w z u * (G u.toNNReal w - G u.toNNReal z) =
      2 / (G u.toNNReal w - (U u.toNNReal : ℂ)) -
      2 / (G u.toNNReal z - (U u.toNNReal : ℂ)) := by
    unfold loewnerPairCoefficient
    field_simp
    ring
  rw [he]
  exact (h.time_derivative T w hw u hu).sub (h.time_derivative T z hz u hu)

lemma IsCapacityTwoWitness.difference_formula
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w z : ℂ)
    (hw : w ∈ survivingDomain γ T) (hz : z ∈ survivingDomain γ T) :
    G T w - G T z = (w - z) * Complex.exp
      (∫ u in (0 : ℝ)..(T : ℝ), loewnerPairCoefficient U G w z u) := by
  have hh := complex_linear_ode_exp (T : ℝ) T.coe_nonneg
    (fun v : ℝ => G v.toNNReal w - G v.toNNReal z)
    (loewnerPairCoefficient U G w z)
    (h.pair_coefficient_continuousOn hU T w z hw hz)
    (h.difference_derivative T w z hw hz)
  simpa only [Real.toNNReal_coe, Real.toNNReal_zero,
    h.initial_value w hw.1.1, h.initial_value z hz.1.1] using hh

lemma IsCapacityTwoWitness.imag_ge_terminal
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    (G T z).im ≤ (G u.toNNReal z).im := by
  simpa only [Real.toNNReal_coe] using h.imag_antitoneOn T z hz hu ⟨T.coe_nonneg, le_rfl⟩ hu.2

lemma IsCapacityTwoWitness.centered_norm_ge_terminal
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    (G T z).im ≤ ‖G u.toNNReal z - (U u.toNNReal : ℂ)‖ := by
  apply (h.imag_ge_terminal T z hz u hu).trans
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
    Complex.im_le_norm (G u.toNNReal z - (U u.toNNReal : ℂ))

lemma IsCapacityTwoWitness.pair_coefficient_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w z : ℂ)
    (hw : w ∈ survivingDomain γ T) (hz : z ∈ survivingDomain γ T)
    (c : ℝ) (hc : 0 < c) (hcw : c ≤ (G T w).im) (hcz : c ≤ (G T z).im)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    ‖loewnerPairCoefficient U G w z u‖ ≤ 2 / (c * c) := by
  have hw' := hcw.trans (h.centered_norm_ge_terminal T w hw u hu)
  have hz' := hcz.trans (h.centered_norm_ge_terminal T z hz u hu)
  unfold loewnerPairCoefficient
  rw [norm_div, norm_mul, norm_neg, Complex.norm_two]
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hc hc)
    (mul_le_mul hw' hz' hc.le (norm_nonneg _))

lemma IsCapacityTwoWitness.pair_coefficient_intervalIntegrable
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w z : ℂ)
    (hw : w ∈ survivingDomain γ T) (hz : z ∈ survivingDomain γ T) :
    IntervalIntegrable (loewnerPairCoefficient U G w z) volume 0 (T : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le T.coe_nonneg] using h.pair_coefficient_continuousOn hU T w z hw hz

lemma IsCapacityTwoWitness.pair_coefficient_tendsto
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ≤ (T : ℝ)) :
    Tendsto (fun w => loewnerPairCoefficient U G w z u) (𝓝 z)
      (𝓝 (loewnerPairCoefficient U G z z u)) := by
  have hzc := h.centered_ne_zero _ z (h.live_at_real_time T z hz u hu)
  have hG := (h.spatial_differentiableAt _ z (h.live_at_real_time T z hz u hu)).continuousAt
  exact tendsto_const_nhds.div ((hG.sub_const _).mul_const _) (mul_ne_zero hzc hzc)

lemma IsCapacityTwoWitness.pair_integral_tendsto
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) :
    Tendsto (fun w => ∫ u in (0 : ℝ)..(T : ℝ), loewnerPairCoefficient U G w z u) (𝓝 z)
      (𝓝 (∫ u in (0 : ℝ)..(T : ℝ), loewnerPairCoefficient U G z z u)) := by
  let c : ℝ := (G T z).im / 2
  have hp := h.imag_positive T z hz
  have hc : 0 < c := by dsimp [c]; positivity
  have hcz : c ≤ (G T z).im := by dsimp [c]; linarith
  have hlt : c < (G T z).im := by dsimp [c]; linarith
  have hlim : Tendsto (fun w => (G T w).im) (𝓝 z) (𝓝 (G T z).im) :=
    Complex.continuous_im.continuousAt.comp (h.spatial_differentiableAt T z hz).continuousAt
  have hmem : ∀ᶠ w in 𝓝 z, w ∈ survivingDomain γ T :=
    (isOpen_survivingDomain h.1 T).mem_nhds hz
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ survivingDomain γ T ∧ c < (G T w).im :=
    hmem.and (hlim.eventually (Ioi_mem_nhds hlt))
  simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 2 / (c * c))
  · filter_upwards [hnear] with w hw
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp
      (h.pair_coefficient_intervalIntegrable hU T w z hw.1 hz)).aestronglyMeasurable
  · filter_upwards [hnear] with w hw
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
    exact h.pair_coefficient_bound T w z hw.1 hz c hc hw.2.le hcz u ⟨hu.1.le, hu.2⟩
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
    exact h.pair_coefficient_tendsto T z hz u hu.2

 

theorem loewner_spatial_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    deriv (G T) z = Complex.exp
      (∫ u in (0 : ℝ)..(T : ℝ), (-2 : ℂ) / (G u.toNNReal z - (U u.toNNReal : ℂ)) ^ 2) := by
  let L (w : ℂ) := Complex.exp (∫ u in (0 : ℝ)..(T : ℝ), loewnerPairCoefficient U G w z u)
  have hL : Tendsto L (𝓝 z) (𝓝 (L z)) :=
    Complex.continuous_exp.continuousAt.tendsto.comp (h.pair_integral_tendsto hU T z hz)
  have he : slope (G T) z =ᶠ[𝓝[≠] z] L := by
    have hnear : ∀ᶠ w in 𝓝 z, w ∈ survivingDomain γ T := (isOpen_survivingDomain h.1 T).mem_nhds hz
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwz
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr hwz
    rw [slope_def_field, h.difference_formula hU T w z hw hz]
    change (w - z) * L w / (w - z) = L w
    field_simp
  have hs : Tendsto (slope (G T) z) (𝓝[≠] z) (𝓝 (L z)) :=
    (hL.mono_left nhdsWithin_le_nhds).congr' he.symm
  have heq := tendsto_nhds_unique (h.spatial_differentiableAt T z hz).hasDerivAt.tendsto_slope hs
  simpa only [L, loewnerPairCoefficient, pow_two] using heq

 
noncomputable def fullRadius (G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  2 * (G t z).im / ‖deriv (G t) z‖

lemma IsCapacityTwoWitness.derivative_norm_positive
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    0 < ‖deriv (G T) z‖ := by
  rw [loewner_spatial_derivative hU h T z hz, Complex.norm_exp]
  exact Real.exp_pos _

lemma IsCapacityTwoWitness.derivative_norm_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => ‖deriv (G v.toNNReal) z‖)
      (‖deriv (G u.toNNReal) z‖ * (loewnerPairCoefficient U G z z u).re)
      (Icc 0 (T : ℝ)) u := by
  let c := loewnerPairCoefficient U G z z
  let C (v : ℝ) : ℂ := c (projIcc 0 (T : ℝ) T.coe_nonneg v)
  have hc : ContinuousOn c (Icc 0 (T : ℝ)) := h.pair_coefficient_continuousOn hU T z z hz hz
  have hC : Continuous C := hc.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun v => (projIcc 0 (T : ℝ) T.coe_nonneg v).property)
  have hCc (v : ℝ) (hv : v ∈ Icc 0 (T : ℝ)) : C v = c v := by simp only [C, projIcc_of_mem T.coe_nonneg hv]
  let I (v : ℝ) : ℂ := ∫ t in (0 : ℝ)..v, C t
  have hI (v : ℝ) : HasDerivAt I (C v) v :=
    intervalIntegral.integral_hasDerivAt_right (hC.intervalIntegrable _ _)
      hC.aestronglyMeasurable.stronglyMeasurableAtFilter hC.continuousAt
  have heq (v : ℝ) (hv : v ∈ Icc 0 (T : ℝ)) :
      ‖deriv (G v.toNNReal) z‖ = Real.exp (I v).re := by
    rw [loewner_spatial_derivative hU h v.toNNReal z (h.live_at_real_time T z hz v hv.2), Complex.norm_exp]
    congr 2
    rw [Real.coe_toNNReal _ hv.1]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hv.1] at ht
    rw [hCc t ⟨ht.1, ht.2.trans hv.2⟩]
    simp only [c, loewnerPairCoefficient, pow_two]
  have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hI u)).exp.hasDerivWithinAt (s := Icc 0 (T : ℝ))
  have hh := hd.congr heq (heq u hu)
  simpa only [Function.comp_def, Complex.reCLM_apply, hCc u hu, ← heq u hu, c] using hh

noncomputable def logLoewnerCoordinates (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ) : ℂ × ℝ :=
  (((G t.toNNReal z).re : ℂ) + (Real.log (G t.toNNReal z).im : ℂ) * Complex.I,
    Real.log ‖deriv (G t.toNNReal) z‖)

lemma IsCapacityTwoWitness.log_height_bounds
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    Real.log (G T z).im ≤ Real.log (G u.toNNReal z).im ∧
      Real.log (G u.toNNReal z).im ≤ Real.log z.im := by
  have hanti := h.imag_antitoneOn T z hz
  have hlow := hanti hu (show (T : ℝ) ∈ Icc 0 (T : ℝ) from ⟨T.coe_nonneg, le_rfl⟩) hu.2
  have hupp := hanti (show (0 : ℝ) ∈ Icc 0 (T : ℝ) from ⟨le_rfl, T.coe_nonneg⟩) hu hu.1
  simp only [Real.toNNReal_coe] at hlow
  simp only [Real.toNNReal_zero, h.initial_value z hz.1.1] at hupp
  exact ⟨Real.log_le_log (h.imag_positive T z hz) hlow,
    Real.log_le_log (h.imag_positive _ z (h.live_at_real_time T z hz u hu.2)) hupp⟩

lemma clippedCenter_logCoordinates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (lo hi : ℝ) (hle : lo ≤ hi)
    (hlo : lo ≤ Real.log (G T z).im) (hhi : Real.log z.im ≤ hi)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    clippedCenter lo hi hle (U u.toNNReal) (logLoewnerCoordinates G z u) =
      G u.toNNReal z - (U u.toNNReal : ℂ) := by
  obtain ⟨ha, hb⟩ := h.log_height_bounds T z hz u hu
  have hmem : Real.log (G u.toNNReal z).im ∈ Icc lo hi := ⟨hlo.trans ha, hb.trans hhi⟩
  have him := h.imag_positive _ z (h.live_at_real_time T z hz u hu.2)
  simp only [clippedCenter, clippedHeight, logLoewnerCoordinates, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    mul_one, zero_add, projIcc_of_mem hle hmem, Real.exp_log him]
  apply Complex.ext <;> simp

lemma logLoewnerCoordinates_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (lo hi : ℝ) (hle : lo ≤ hi)
    (hlo : lo ≤ Real.log (G T z).im) (hhi : Real.log z.im ≤ hi)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (logLoewnerCoordinates G z)
      (clippedLogLoewnerField lo hi hle (U u.toNNReal) (logLoewnerCoordinates G z u))
      (Icc 0 (T : ℝ)) u := by
  have hzlive := h.live_at_real_time T z hz u hu.2
  have hy := h.imag_positive _ z hzlive
  have hj := h.derivative_norm_positive hU _ z hzlive
  have hdre := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt u (h.time_derivative T z hz u hu)
  have hdY := (h.imag_derivative T z hz u hu).log hy.ne'
  have hdJ := (h.derivative_norm_derivative hU T z hz u hu).log hj.ne'
  have hd := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt u hdre).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt u hdY).mul_const Complex.I)).prodMk hdJ
  convert hd using 1 <;> try rfl
  unfold clippedLogLoewnerField
  rw [clippedCenter_logCoordinates h T z hz lo hi hle hlo hhi u hu]
  dsimp only [Function.comp_def, Complex.reCLM_apply, Complex.ofRealCLM_apply]
  apply Prod.ext
  · apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero,
        div_eq_mul_inv, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
        zero_mul, sub_zero]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
        Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
        Complex.normSq_inv]
      field_simp [hy.ne']
  · change (-2 * (G u.toNNReal z - (U u.toNNReal : ℂ))⁻¹ ^ 2).re =
      (_ * (loewnerPairCoefficient U G z z u).re) / _
    rw [mul_div_cancel_left₀ _ hj.ne']
    congr 1
    simp only [loewnerPairCoefficient, div_eq_mul_inv, mul_inv_rev, pow_two]

lemma hasDerivWithinAt_Ici_of_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {a b u : ℝ} (hu : u ∈ Ico a b)
    (hf : HasDerivWithinAt f f' (Icc a b) u) : HasDerivWithinAt f f' (Ici u) u := by
  apply hf.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hu.2)] with x hx hxT
  exact ⟨hu.1.trans hx, hxT⟩

lemma logLoewnerCoordinates_initial
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (hz : z ∈ survivingDomain γ 0) :
    logLoewnerCoordinates G z 0 = ((z.re : ℂ) + (Real.log z.im : ℂ) * Complex.I, 0) := by
  simp only [logLoewnerCoordinates, Real.toNNReal_zero, h.initial_value z hz.1.1,
    loewner_spatial_derivative hU h 0 z hz, NNReal.coe_zero,
    intervalIntegral.integral_same, Complex.exp_zero, norm_one, Real.log_one]

 

theorem clipped_log_loewner_agrees
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (lo hi : ℝ) (hle : lo ≤ hi)
    (hlo : lo ≤ Real.log (G T z).im) (hhi : Real.log z.im ≤ hi)
    (Q : ℝ → ℂ × ℝ)
    (hQ0 : Q 0 = ((z.re : ℂ) + (Real.log z.im : ℂ) * Complex.I, 0))
    (hQ : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) (Icc 0 (T : ℝ)) t) :
    EqOn Q (logLoewnerCoordinates G z) (Icc 0 (T : ℝ)) := by
  obtain ⟨L, K, hb, hl⟩ := clippedLogLoewnerField_bounds lo hi hle
  have hd := logLoewnerCoordinates_derivative hU h T z hz lo hi hle hlo hhi
  apply ODE_solution_unique (fun t => hl (U t.toNNReal))
    (fun t ht => (hQ t ht).continuousWithinAt)
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hQ t ⟨ht.1, ht.2.le⟩))
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hd t ⟨ht.1, ht.2.le⟩))
  exact hQ0.trans (logLoewnerCoordinates_initial hU h z (survivingDomain_antitone γ bot_le hz)).symm

 

theorem loewner_survival_of_positive_solution
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (W : ℝ → ℂ)
    (hWp : ∀ u ∈ Icc 0 (T : ℝ), 0 < (W u).im)
    (hWd : ∀ u ∈ Icc 0 (T : ℝ), HasDerivWithinAt W
      (2 / (W u - (U u.toNNReal : ℂ))) (Icc 0 (T : ℝ)) u) :
    W 0 ∈ survivingDomain γ T ∧ G T (W 0) = W T := by
  let w := F T (W T)
  have hWT : W T ∈ upperHalfPlane := hWp T ⟨T.coe_nonneg, le_rfl⟩
  have hw : w ∈ survivingDomain γ T := h.2.2.2.2.2.2.1 T hWT
  have hGw : G T w = W T := h.2.2.2.2.2.2.2.2.1 T (W T) hWT
  have hWc : ContinuousOn W (Icc 0 (T : ℝ)) := fun u hu => (hWd u hu).continuousWithinAt
  have hWnz (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) : W u - (U u.toNNReal : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hh
    exact (hWp u hu).ne' hh
  let c (u : ℝ) : ℂ := (-2 : ℂ) /
    ((G u.toNNReal w - (U u.toNNReal : ℂ)) * (W u - (U u.toNNReal : ℂ)))
  have hUc : Continuous (fun u : ℝ => (U u.toNNReal : ℂ)) :=
    Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)
  have hc : ContinuousOn c (Icc 0 (T : ℝ)) :=
    continuousOn_const.div
      (((h.time_continuousOn T w hw).sub hUc.continuousOn).mul (hWc.sub hUc.continuousOn))
      (fun u hu => mul_ne_zero (h.centered_ne_zero _ w (h.live_at_real_time T w hw u hu.2)) (hWnz u hu))
  have hd (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
      HasDerivWithinAt (fun s : ℝ => G s.toNNReal w - W s)
        (c u * (G u.toNNReal w - W u)) (Icc 0 (T : ℝ)) u := by
    have hg := h.centered_ne_zero _ w (h.live_at_real_time T w hw u hu.2)
    have hn := hWnz u hu
    have he : c u * (G u.toNNReal w - W u) =
        2 / (G u.toNNReal w - (U u.toNNReal : ℂ)) - 2 / (W u - (U u.toNNReal : ℂ)) := by
      dsimp only [c]
      field_simp
      ring
    rw [he]
    exact (h.time_derivative T w hw u hu).sub (hWd u hu)
  have he := complex_linear_ode_exp (T : ℝ) T.coe_nonneg
    (fun s : ℝ => G s.toNNReal w - W s) c hc hd
  simp only [Real.toNNReal_coe, hGw, sub_self, Real.toNNReal_zero,
    h.initial_value w hw.1.1] at he
  have hw0 : w = W 0 := sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right (Complex.exp_ne_zero _))
  exact ⟨hw0 ▸ hw, hw0 ▸ hGw⟩

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_LoewnerReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Loewner Reflection for chordal SLE. -/

section
section

open Set Filter Complex Metric ComplexConjugate
open scoped Topology NNReal
namespace SLEExactGauge

 

noncomputable def loewnerMirror : ℂ ≃ₜ ℂ where
  toFun z := -conj z
  invFun z := -conj z
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := Complex.continuous_conj.neg
  continuous_invFun := Complex.continuous_conj.neg

@[simp] lemma loewnerMirror_apply (z : ℂ) : loewnerMirror z = -conj z := rfl
@[simp] lemma loewnerMirror_twice (z : ℂ) : loewnerMirror (loewnerMirror z) = z := by simp
@[simp] lemma loewnerMirror_im (z : ℂ) : (loewnerMirror z).im = z.im := by simp
@[simp] lemma loewnerMirror_re (z : ℂ) : (loewnerMirror z).re = -z.re := by simp
@[simp] lemma loewnerMirror_dist (z w : ℂ) : dist (loewnerMirror z) (loewnerMirror w) = dist z w := by
  simp only [loewnerMirror_apply,dist_neg_neg,Complex.dist_conj_conj]
@[simp] lemma loewnerMirror_norm (z : ℂ) : ‖loewnerMirror z‖ = ‖z‖ := by simp

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def rightCenter (a u : ℝ) (z : ℂ) : ℂ :=
  ((max a (z.re - u) : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I

noncomputable def rightField (a u : ℝ) (z : ℂ) : ℂ := 2 * (rightCenter a u z)⁻¹

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def reverseCenter (a u : ℝ) (z : ℂ) : ℂ :=
  ((z.re - u : ℝ) : ℂ) + ((max a z.im : ℝ) : ℂ) * I

noncomputable def reverseField (a u : ℝ) (z : ℂ) : ℂ := -2 * (reverseCenter a u z)⁻¹

lemma reverseCenter_im (a u : ℝ) (z : ℂ) : (reverseCenter a u z).im = max a z.im := by
  simp [reverseCenter]

lemma reverseCenter_norm (a u : ℝ) (z : ℂ) : a ≤ ‖reverseCenter a u z‖ :=
  (le_max_left a z.im).trans ((reverseCenter_im a u z).symm.le.trans (Complex.im_le_norm _))

lemma reverseCenter_ne_zero {a : ℝ} (ha : 0 < a) (u : ℝ) (z : ℂ) : reverseCenter a u z ≠ 0 :=
  norm_pos_iff.mp (ha.trans_le (reverseCenter_norm a u z))

lemma reverseCenter_eq {a u : ℝ} {z : ℂ} (hz : a ≤ z.im) : reverseCenter a u z = z - (u : ℂ) := by
  apply Complex.ext <;> simp [reverseCenter, max_eq_right hz]

lemma reverseCenter_dist (a u : ℝ) (z w : ℂ) :
    dist (reverseCenter a u z) (reverseCenter a u w) ≤ 2 * dist z w := by
  have hr : |z.re - w.re| ≤ ‖z - w‖ := Complex.abs_re_le_norm (z - w)
  have hi : |max a z.im - max a w.im| ≤ ‖z - w‖ := by
    have h := ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).const_max a).dist_le_mul z.im w.im
    have hh : |max a z.im - max a w.im| ≤ |z.im - w.im| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] using h
    exact hh.trans (Complex.abs_im_le_norm (z - w))
  have he : reverseCenter a u z - reverseCenter a u w =
      ((z.re - w.re : ℝ) : ℂ) + ((max a z.im - max a w.im : ℝ) : ℂ) * I := by
    simp only [reverseCenter, Complex.ofReal_sub]
    ring
  rw [dist_eq_norm, he]
  have hb := norm_add_le ((z.re - w.re : ℝ) : ℂ) (((max a z.im - max a w.im : ℝ) : ℂ) * I)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hb
  rw [dist_eq_norm]
  linarith

lemma reverseField_bound {a : ℝ} (ha : 0 < a) (u : ℝ) (z : ℂ) :
    ‖reverseField a u z‖ ≤ 2 * a⁻¹ := by
  have hi : ‖(reverseCenter a u z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ ha (reverseCenter_norm a u z)
  simpa only [reverseField, norm_mul, norm_neg, norm_ofNat] using mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)

lemma reverseField_lipschitz {a : ℝ} (ha : 0 < a) (u : ℝ) :
    LipschitzWith ⟨4 * a⁻¹ ^ 2, by positivity⟩ (reverseField a u) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hz : ‖(reverseCenter a u z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ ha (reverseCenter_norm a u z)
  have hw : ‖(reverseCenter a u w)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ ha (reverseCenter_norm a u w)
  rw [dist_eq_norm, reverseField, reverseField, ← mul_sub, norm_mul, norm_neg, norm_ofNat,
    inv_sub_inv' (reverseCenter_ne_zero ha _ _) (reverseCenter_ne_zero ha _ _), norm_mul, norm_mul]
  calc
    _ ≤ 2 * (a⁻¹ * (2 * dist z w) * a⁻¹) := by
      gcongr
      simpa only [← dist_eq_norm, dist_comm] using reverseCenter_dist a u z w
    _ = _ := by change 2 * (a⁻¹ * (2 * dist z w) * a⁻¹) = (4 * a⁻¹ ^ 2) * dist z w; ring

lemma continuous_reverseField {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × ℂ => reverseField a p.1 p.2) := by
  apply continuous_const.mul
  apply Continuous.inv₀
  · exact ((Complex.continuous_ofReal.comp ((Complex.continuous_re.comp continuous_snd).sub continuous_fst)).add
      ((Complex.continuous_ofReal.comp (continuous_const.max (Complex.continuous_im.comp continuous_snd))).mul continuous_const))
  · intro p; exact reverseCenter_ne_zero ha _ _

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma exists_random_initial_bounded_flow
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (V : ℝ → Ω → E → E) (q₀ : Ω → E) (hq₀ : Measurable q₀) (L K : ℝ≥0)
    (hV : Measurable (fun p : (ℝ × Ω) × E => V p.1.1 p.1.2 p.2))
    (hc : ∀ ω x, Continuous (fun t : ℝ => V t ω x))
    (hl : ∀ ω t, LipschitzWith K (V t ω))
    (hb : ∀ ω t x, ‖V t ω x‖ ≤ L) :
    ∃ X : ℝ → Ω → E,
      Measurable (fun p : ℝ × Ω => X p.1 p.2) ∧
      (∀ ω, X 0 ω = q₀ ω) ∧
      (∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => X s ω) (V t ω (X t ω)) (Ici 0) t) := by
  let W (t : ℝ) (ω : Ω) (x : E) := V t ω (q₀ ω + x)
  have hW : Measurable (fun p : (ℝ × Ω) × E => W p.1.1 p.1.2 p.2) :=
    hV.comp (measurable_fst.prodMk ((hq₀.comp (measurable_snd.comp measurable_fst)).add measurable_snd))
  have hWl (ω : Ω) (t : ℝ) : LipschitzWith K (W t ω) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [W, dist_add_left] using (hl ω t).dist_le_mul (q₀ ω + x) (q₀ ω + y)
  obtain ⟨Y, hYm, _, hY0, hYd, _⟩ := exists_measurable_global_bounded_ode_picard
    W 0 L K hW (fun ω x => hc ω (q₀ ω + x)) hWl (fun ω t x => hb ω t (q₀ ω + x))
  refine ⟨fun t ω => q₀ ω + Y t ω, (hq₀.comp measurable_snd).add hYm, ?_, ?_⟩
  · intro ω; change q₀ ω + Y 0 ω = q₀ ω; rw [hY0, add_zero]
  · intro ω t ht
    exact (hYd ω t ht).const_add (q₀ ω)

lemma exists_measurable_reverse_flow
    {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ → Ω → ℝ) (hUm : Measurable (fun p : ℝ × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω))
    (w : Ω → ℂ) (hwm : Measurable w) {a : ℝ} (ha : 0 < a) :
    ∃ Q : ℝ → Ω → ℂ,
      Measurable (fun p : ℝ × Ω => Q p.1 p.2) ∧
      (∀ ω, Q 0 ω = w ω) ∧
      (∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω)
        (reverseField a (U t ω) (Q t ω)) (Ici 0) t) := by
  have hm : Measurable (fun p : (ℝ × Ω) × ℂ => reverseField a (U p.1.1 p.1.2) p.2) := by
    have hj : Measurable (fun p : (ℝ × Ω) × ℂ => (U p.1.1 p.1.2, p.2)) :=
      (hUm.comp measurable_fst).prodMk measurable_snd
    have hf : Measurable (fun q : ℝ × ℂ => reverseField a q.1 q.2) :=
      (continuous_reverseField ha).measurable
    exact Measurable.comp (g := fun q : ℝ × ℂ => reverseField a q.1 q.2)
      (f := fun p : (ℝ × Ω) × ℂ => (U p.1.1 p.1.2, p.2)) hf hj
  have hc (ω : Ω) (z : ℂ) : Continuous (fun t : ℝ => reverseField a (U t ω) z) :=
    Continuous.comp (g := fun q : ℝ × ℂ => reverseField a q.1 q.2)
      (f := fun t : ℝ => (U t ω, z)) (continuous_reverseField ha)
      ((hUc ω).prodMk continuous_const)
  exact exists_random_initial_bounded_flow (fun t ω z => reverseField a (U t ω) z)
    w hwm ⟨2 * a⁻¹, by positivity⟩ ⟨4 * a⁻¹ ^ 2, by positivity⟩ hm hc
      (fun ω t => reverseField_lipschitz ha _) (fun ω t z => reverseField_bound ha _ _)

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.reverse_path_derivative
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w : ℂ) {a : ℝ}
    (ha : 0 < a) (haw : a ≤ w.im) (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun t : ℝ => G ((T : ℝ) - t).toNNReal (F T w))
      (reverseField a (U ((T : ℝ) - s).toNNReal) (G ((T : ℝ) - s).toNNReal (F T w)))
      (Icc 0 (T : ℝ)) s := by
  have hw : w ∈ upperHalfPlane := ha.trans_le haw
  have hz : F T w ∈ survivingDomain γ T := h.2.2.2.2.2.2.1 T hw
  have hi : G T (F T w) = w := h.2.2.2.2.2.2.2.2.1 T w hw
  have hmaps : MapsTo (fun t : ℝ => (T : ℝ) - t) (Icc 0 (T : ℝ)) (Icc 0 (T : ℝ)) := by
    intro t ht; constructor <;> linarith [ht.1, ht.2]
  have hd := (h.time_derivative T (F T w) hz ((T : ℝ) - s) (hmaps hs)).scomp s
    ((hasDerivAt_id s).const_sub (T : ℝ)).hasDerivWithinAt hmaps
  have hh : a ≤ (G ((T : ℝ) - s).toNNReal (F T w)).im := by
    have hh := h.imag_antitoneOn T (F T w) hz (hmaps hs) ⟨T.coe_nonneg, le_rfl⟩ (hmaps hs).2
    simp only [Real.toNNReal_coe, hi] at hh
    exact haw.trans hh
  simp only [Function.comp_def, neg_smul, one_smul] at hd
  simpa only [reverseField, reverseCenter_eq hh, div_eq_mul_inv, neg_mul] using hd

 

theorem IsCapacityTwoWitness.reverse_flow_identifies
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w : ℂ) {a : ℝ}
    (ha : 0 < a) (haw : a ≤ w.im) (Q : ℝ → ℂ) (hQ0 : Q 0 = w)
    (hQd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (reverseField a (U ((T : ℝ) - t).toNNReal) (Q t)) (Icc 0 (T : ℝ)) t) :
    Q T = F T w := by
  have hw : w ∈ upperHalfPlane := ha.trans_le haw
  have hp := h.reverse_path_derivative T w ha haw
  have he : EqOn Q (fun t : ℝ => G ((T : ℝ) - t).toNNReal (F T w)) (Icc 0 (T : ℝ)) := by
    apply ODE_solution_unique (fun t => reverseField_lipschitz ha (U ((T : ℝ) - t).toNNReal))
      (fun t ht => (hQd t ht).continuousWithinAt)
      (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hQd t ⟨ht.1, ht.2.le⟩))
      (fun t ht => (hp t ht).continuousWithinAt)
      (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hp t ⟨ht.1, ht.2.le⟩))
    simpa only [sub_zero, Real.toNNReal_coe, h.2.2.2.2.2.2.2.2.1 T w hw] using hQ0
  have hh := he ⟨T.coe_nonneg, le_rfl⟩
  simpa only [sub_self, Real.toNNReal_zero, h.initial_value (F T w)
    (h.2.2.2.2.2.2.1 T hw).1.1] using hh

end SLEExactGauge
end


section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge

 

noncomputable def positiveBoundaryField (a u x : ℝ) : ℝ :=
  2 * (max a (x-u))⁻¹

end SLEExactGauge
end


section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def boundaryClockField (a u : ℝ) (q : ℂ) : ℂ :=
  (positiveBoundaryField a u q.re : ℂ) + ((max a (q.re-u))⁻¹^2 : ℝ) * I

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure BoundaryClockSolution {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (κ a : ℝ) (q₀ : ℂ) where
  L : ℝ≥0
  Q : ℝ → Ω → ℂ
  measurable : Measurable (fun p : ℝ × Ω => Q p.1 p.2)
  lipschitz : ∀ ω, LipschitzWith L (fun t => Q t ω)
  initial : ∀ ω, Q 0 ω = q₀
  derivative : ∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω)
    (boundaryClockField a (Real.sqrt κ * B t.toNNReal ω) (Q t ω)) (Ici 0) t
  adapted : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun t : ℝ≥0 => Q t)

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_BoundaryDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Density for chordal SLE. -/

section
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

noncomputable def smoothPositiveGap (a x : ℝ) : ℝ :=
  a + (x-a)*(1-Real.smoothTransition ((2*a-x)/a))

noncomputable def boundaryDensity (κ α β : ℝ) (q : ℂ) (b : ℝ) : ℝ :=
  Real.exp (-β*α*q.im - β*Real.log (q.re-Real.sqrt κ*b))

noncomputable def smoothBoundaryDensity (κ α β a : ℝ) (q : ℂ) (b : ℝ) : ℝ :=
  Real.exp (-β*α*q.im - β*Real.log (smoothPositiveGap a (q.re-Real.sqrt κ*b)))

end SLEExactGauge
end


section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def logRadiusClock (η₀ : ℝ) (q : ℂ × ℝ) : ℝ :=
  η₀ - q.1.im + q.2

noncomputable def logAngleSq (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) : ℝ :=
  Real.exp (2 * q.1.im) / greenLogNormSq κ q b

noncomputable def logClockRate (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) : ℝ :=
  4 * Real.exp (2 * q.1.im) / greenLogNormSq κ q b ^ 2

lemma continuous_logRadiusClock (η₀ : ℝ) : Continuous (logRadiusClock η₀) :=
  (continuous_const.sub (Complex.continuous_im.comp continuous_fst)).add continuous_snd

lemma logClockRate_pos (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    0 < logClockRate κ q b := by
  unfold logClockRate
  exact div_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (sq_pos_of_pos (greenLogNormSq_pos κ q b))

lemma log_ode_im_derivative {Q : ℝ → ℂ × ℝ} {D : Set ℝ} {t κ b : ℝ}
    (hQ : HasDerivWithinAt Q (physicalLogLoewnerField (Real.sqrt κ * b) (Q t)) D t) :
    HasDerivWithinAt (fun s => (Q s).1.im) (-2 / greenLogNormSq κ (Q t) b) D t := by
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hQ.fst
  simpa only [Function.comp_def, Complex.imCLM_apply,
    (physicalLogLoewnerField_components κ (Q t) b).2.1] using hi

lemma log_ode_clock_derivative {Q : ℝ → ℂ × ℝ} {D : Set ℝ} {t κ b : ℝ}
    (η₀ : ℝ)
    (hQ : HasDerivWithinAt Q (physicalLogLoewnerField (Real.sqrt κ * b) (Q t)) D t) :
    HasDerivWithinAt (fun s => logRadiusClock η₀ (Q s))
      (logClockRate κ (Q t) b) D t := by
  have hs : HasDerivWithinAt (fun s => (Q s).2)
      (physicalLogLoewnerField (Real.sqrt κ * b) (Q t)).2 D t := hQ.snd
  have hd : HasDerivWithinAt (fun s => η₀ - (Q s).1.im + (Q s).2)
      (-(-2 / greenLogNormSq κ (Q t) b) +
        (physicalLogLoewnerField (Real.sqrt κ * b) (Q t)).2) D t :=
    ((log_ode_im_derivative hQ).const_sub η₀).add hs
  have he : -(-2 / greenLogNormSq κ (Q t) b) +
      (physicalLogLoewnerField (Real.sqrt κ * b) (Q t)).2 = logClockRate κ (Q t) b := by
    rw [(physicalLogLoewnerField_components κ (Q t) b).2.2]
    unfold logClockRate
    have hN := (greenLogNormSq_pos κ (Q t) b).ne'
    field_simp
    unfold greenLogNormSq
    ring
  simpa only [he, logRadiusClock, Pi.add_apply] using hd

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure ClippedLogSolution {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (κ lo hi : ℝ) (hle : lo ≤ hi) (q₀ : ℂ × ℝ) where
  L : ℝ≥0
  Q : ℝ → Ω → ℂ × ℝ
  measurable : Measurable (fun p : ℝ × Ω => Q p.1 p.2)
  lipschitz : ∀ ω, LipschitzWith L (fun t => Q t ω)
  initial : ∀ ω, Q 0 ω = q₀
  derivative : ∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω)
    (clippedLogLoewnerField lo hi hle (Real.sqrt κ * B t.toNNReal ω) (Q t ω))
    (Ici 0) t
  adapted : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun t : ℝ≥0 => Q t)

lemma exists_clippedLogSolution
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ lo hi : ℝ) (hle : lo ≤ hi) (q₀ : ℂ × ℝ) :
    Nonempty (ClippedLogSolution B hm κ lo hi hle q₀) := by
  let U (t : ℝ≥0) (ω : Ω) := Real.sqrt κ * B t ω
  have hUm : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2) := hBm.const_mul _
  have hUc (ω : Ω) : Continuous (fun t => U t ω) := (hBc ω).const_mul _
  obtain ⟨L, Q, hQm, hQl, hQ0, hQd, hQaU⟩ :=
    clipped_log_loewner_global_adapted_solution U hUm hUc lo hi hle q₀
  have hBa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  refine ⟨⟨L, Q, hQm, hQl, hQ0, hQd, ?_⟩⟩
  intro t
  apply (hQaU t).mono _ le_rfl
  change (⨆ j ≤ t, MeasurableSpace.comap (U j) (borel ℝ)) ≤ _
  refine iSup₂_le fun j hj => ?_
  exact ((hBa.measurable_le hj).const_mul (Real.sqrt κ)).comap_le

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_FiniteRadiusStop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Radius Stop for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



noncomputable def logStopMargin (κ η₀ u lo hi ε N : ℝ) (q : ℂ × ℝ) (b : ℝ) : ℝ :=
  min (u - logRadiusClock η₀ q)
    (min (logAngleSq κ q b - ε)
      (min (q.1.im - lo) (min (hi - q.1.im) (N - |b|))))

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def initialLogCoordinates (z : ℂ) : ℂ × ℝ :=
  ((z.re : ℂ) + (Real.log z.im : ℂ) * Complex.I, 0)

noncomputable def restoreLogPoint (q : ℂ × ℝ) : ℂ :=
  (q.1.re : ℂ) + (Real.exp q.1.im : ℂ) * Complex.I

lemma restoreLogPoint_im (q : ℂ × ℝ) : (restoreLogPoint q).im = Real.exp q.1.im := by
  simp only [restoreLogPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]

lemma restoreLogPoint_initial (z : ℂ) (hz : z ∈ upperHalfPlane) :
    restoreLogPoint (initialLogCoordinates z) = z := by
  apply Complex.ext <;> simp [restoreLogPoint, initialLogCoordinates, Real.exp_log hz]

lemma restoreLogPoint_derivative {Q : ℝ → ℂ × ℝ} {D : Set ℝ} {t u : ℝ}
    (hQ : HasDerivWithinAt Q (physicalLogLoewnerField u (Q t)) D t) :
    HasDerivWithinAt (fun s => restoreLogPoint (Q s))
      (2 / (restoreLogPoint (Q t) - (u : ℂ))) D t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hQ.fst
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hQ.fst
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t hr).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t hi.exp).mul_const Complex.I)
  convert hd using 1 <;> try rfl
  · let Z := restoreLogPoint (Q t) - (u : ℂ)
    have he : (((Q t).1.re - u : ℝ) : ℂ) + (Real.exp (Q t).1.im : ℂ) * Complex.I = Z := by
      simp only [Z, restoreLogPoint, Complex.ofReal_sub]; ring
    have hZi : Z.im = Real.exp (Q t).1.im := by
      dsimp only [Z]
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero, restoreLogPoint_im]
    simp only [Function.comp_def, Complex.reCLM_apply, Complex.ofRealCLM_apply,
      Complex.imCLM_apply, physicalLogLoewnerField, he, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero, mul_one, zero_add]
    change 2 / Z = ((2 * Z⁻¹.re : ℝ) : ℂ) +
      ((Real.exp (Q t).1.im * (-2 * Complex.normSq Z⁻¹) : ℝ) : ℂ) * Complex.I
    apply Complex.ext
    · simp only [div_eq_mul_inv, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
        zero_mul, sub_zero, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero]
    · simp only [div_eq_mul_inv, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
        zero_mul, add_zero, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.inv_im,
        Complex.normSq_inv, hZi]
      ring

 

theorem clipped_log_identification
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (hz : z ∈ upperHalfPlane) (T : ℝ≥0)
    (lo hi : ℝ) (hle : lo ≤ hi) (Q : ℝ → ℂ × ℝ)
    (hQ0 : Q 0 = initialLogCoordinates z)
    (hQd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) (Icc 0 (T : ℝ)) t)
    (hb : ∀ t ∈ Icc 0 (T : ℝ), (Q t).1.im ∈ Icc lo hi) :
    z ∈ survivingDomain γ T ∧ EqOn Q (logLoewnerCoordinates G z) (Icc 0 (T : ℝ)) := by
  let W (t : ℝ) := restoreLogPoint (Q t)
  have hW0 : W 0 = z := by
    change restoreLogPoint (Q 0) = z
    rw [hQ0, restoreLogPoint_initial z hz]
  have hp (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : 0 < (W t).im := by
    change 0 < (restoreLogPoint (Q t)).im
    rw [restoreLogPoint_im]; exact Real.exp_pos _
  have hd (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt W
      (2 / (W t - (U t.toNNReal : ℂ))) (Icc 0 (T : ℝ)) t := by
    apply restoreLogPoint_derivative
    have hh := hQd t ht
    rwa [clippedLogLoewnerField_eq_physical lo hi hle _ _ (hb t ht)] at hh
  obtain ⟨hlive, he⟩ := loewner_survival_of_positive_solution hU h T W hp hd
  rw [hW0] at hlive he
  have hη : Real.log (G T z).im = (Q T).1.im := by
    rw [he]
    change Real.log (restoreLogPoint (Q T)).im = _
    rw [restoreLogPoint_im, Real.log_exp]
  have hh₀ := hb 0 ⟨le_rfl, T.coe_nonneg⟩
  rw [hQ0] at hh₀
  have hhi : Real.log z.im ≤ hi := by simpa [initialLogCoordinates] using hh₀.2
  exact ⟨hlive, clipped_log_loewner_agrees hU h T z hlive lo hi hle
    (by rw [hη]; exact (hb T ⟨T.coe_nonneg, le_rfl⟩).1) hhi Q hQ0 hQd⟩

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem exists_joint_clipped_flow
    {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ≥0 → Ω → ℝ)
    (hUm : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω))
    (q₀ : Ω → ℂ × ℝ) (hq₀ : Measurable q₀)
    (lo hi : ℝ) (hle : lo ≤ hi) :
    ∃ Q : ℝ → Ω → ℂ × ℝ,
      Measurable (fun p : ℝ × Ω => Q p.1 p.2) ∧
      (∀ ω, Q 0 ω = q₀ ω) ∧
      (∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω)
        (clippedLogLoewnerField lo hi hle (U t.toNNReal ω) (Q t ω)) (Ici 0) t) := by
  obtain ⟨L, K, hbound, hlip⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) (x : ℂ × ℝ) :=
    clippedLogLoewnerField lo hi hle (U t.toNNReal ω) (q₀ ω + x)
  have hUr : Measurable (fun p : ℝ × Ω => U p.1.toNNReal p.2) :=
    hUm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hV : Measurable (fun p : (ℝ × Ω) × (ℂ × ℝ) => V p.1.1 p.1.2 p.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun p : (ℝ × Ω) × (ℂ × ℝ) => (U p.1.1.toNNReal p.1.2, q₀ p.1.2 + p.2)))
    exact (continuous_clippedLogLoewnerField lo hi hle).measurable.comp
      ((hUr.comp measurable_fst).prodMk
        ((hq₀.comp (measurable_snd.comp measurable_fst)).add measurable_snd))
  have hVc (ω : Ω) (x : ℂ × ℝ) : Continuous (fun t : ℝ => V t ω x) := by
    change Continuous ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun t : ℝ => (U t.toNNReal ω, q₀ ω + x)))
    exact (continuous_clippedLogLoewnerField lo hi hle).comp
      (((hUc ω).comp continuous_real_toNNReal).prodMk continuous_const)
  have hVl (ω : Ω) (t : ℝ) : LipschitzWith K (V t ω) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [V, dist_add_left] using (hlip (U t.toNNReal ω)).dist_le_mul (q₀ ω + x) (q₀ ω + y)
  obtain ⟨X, hXm, _, hX0, hXd, _⟩ := exists_measurable_global_bounded_ode_picard
    V 0 L K hV hVc hVl (fun ω t x => hbound _ _)
  refine ⟨fun t ω => q₀ ω + X t ω, (hq₀.comp measurable_snd).add hXm, ?_, ?_⟩
  · intro ω; change q₀ ω + X 0 ω = q₀ ω; rw [hX0, add_zero]
  · intro ω t ht
    simpa only [V] using (hXd ω t ht).const_add (q₀ ω)

lemma measurable_initialLogCoordinates : Measurable initialLogCoordinates := by
  exact ((Complex.measurable_ofReal.comp Complex.measurable_re).add
    ((Complex.measurable_ofReal.comp (Real.measurable_log.comp Complex.measurable_im)).mul_const
      Complex.I)).prodMk measurable_const

 
theorem exists_spatial_clipped_flow
    {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ≥0 → Ω → ℝ)
    (hUm : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω)) (n : ℕ) :
    ∃ Q : ℝ → ℂ × Ω → ℂ × ℝ,
      Measurable (fun p : ℝ × (ℂ × Ω) => Q p.1 p.2) ∧
      (∀ z ω, Q 0 (z, ω) = initialLogCoordinates z) ∧
      (∀ z ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s (z, ω))
        (clippedLogLoewnerField (-(n : ℝ)) n (by linarith [Nat.cast_nonneg (α := ℝ) n])
          (U t.toNNReal ω) (Q t (z, ω))) (Ici 0) t) := by
  obtain ⟨Q, hQm, hQ0, hQd⟩ := exists_joint_clipped_flow (fun t (p : ℂ × Ω) => U t p.2)
    (hUm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    (fun p => hUc p.2) (fun p => initialLogCoordinates p.1)
    (measurable_initialLogCoordinates.comp measurable_fst) (-(n : ℝ)) n (by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact ⟨Q, hQm, fun z ω => hQ0 (z, ω), fun z ω t ht => hQd (z, ω) t ht⟩

end SLEExactGauge
end

 
section

open Set Filter
open scoped Topology NNReal
namespace SLEExactGauge

lemma clipped_log_height_derivative
    {U : ℝ≥0 → ℝ} {lo hi : ℝ} {hle : lo ≤ hi} {Q : ℝ → ℂ × ℝ}
    {t : ℝ} {S : Set ℝ}
    (hd : HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) S t) :
    HasDerivWithinAt (fun s => (Q s).1.im)
      (-2 * Complex.normSq (clippedCenter lo hi hle (U t.toNNReal) (Q t))⁻¹) S t := by
  simpa only [Function.comp_def, Complex.imCLM_apply, clippedLogLoewnerField,
    Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    using Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd.fst

lemma clipped_log_height_antitone
    {U : ℝ≥0 → ℝ} {lo hi : ℝ} {hle : lo ≤ hi} {Q : ℝ → ℂ × ℝ}
    (T : ℝ≥0)
    (hd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) (Icc 0 (T : ℝ)) t) :
    AntitoneOn (fun t => (Q t).1.im) (Icc 0 (T : ℝ)) := by
  have he (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) := clipped_log_height_derivative (hd t ht)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (fun t ht => (he t ht).continuousWithinAt)
    (fun t ht => (he t (interior_subset ht)).mono interior_subset)
  intro t ht
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Complex.normSq_nonneg _)

 

lemma clipped_log_identification_of_endpoint
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ upperHalfPlane)
    (lo hi : ℝ) (hle : lo ≤ hi) (Q : ℝ → ℂ × ℝ)
    (hQ0 : Q 0 = initialLogCoordinates z)
    (hQd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t)) (Icc 0 (T : ℝ)) t)
    (hlo : lo ≤ (Q T).1.im) (hhi : Real.log z.im ≤ hi) :
    z ∈ survivingDomain γ T ∧ EqOn Q (logLoewnerCoordinates G z) (Icc 0 (T : ℝ)) := by
  apply clipped_log_identification hU h z hz T lo hi hle Q hQ0 hQd
  have hm := clipped_log_height_antitone T hQd
  intro t ht
  refine ⟨hlo.trans (hm ht ⟨T.coe_nonneg, le_rfl⟩ ht.2), ?_⟩
  have hh := hm (show (0 : ℝ) ∈ Icc 0 (T : ℝ) from ⟨le_rfl, T.coe_nonneg⟩) ht ht.1
  change (Q t).1.im ≤ (Q 0).1.im at hh
  rw [hQ0] at hh
  have hinit : (initialLogCoordinates z).1.im = Real.log z.im := by
    simp [initialLogCoordinates]
  rw [hinit] at hh
  exact hh.trans hhi

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def powerLogDensity (κ p a : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  Real.exp (-p * Real.log 2 + p * q.2 +
    (a - p) * q.1.im -
      (a / 2) * Real.log (greenLogNormSq κ q x))

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SwallowLyapunov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Swallow Lyapunov for chordal SLE. -/

section
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def radialLogPower (κ β : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  Real.exp ((β/2)*Real.log (greenLogNormSq κ q x))
noncomputable def heightLogPower (β : ℝ) (q : ℂ × ℝ) : ℝ := Real.exp (β*q.1.im)
noncomputable def swallowLyapunov (κ β C : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  radialLogPower κ β q x + C*heightLogPower β q

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def swallowGenerator (κ β C : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  β*radialLogPower κ β q x*
    ((2+κ*(β-1)/2)*(q.1.re-Real.sqrt κ*x)^2+(κ/2-2)*Real.exp (2*q.1.im)) /
      (greenLogNormSq κ q x)^2 - 2*C*β*heightLogPower β q/greenLogNormSq κ q x

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

structure RadialLocalization
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (R : ℝ) (T : ℝ≥0) where
  τ : Ω → ℝ≥0
  stopping : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (τ ω : WithTop ℝ≥0))
  bounded : ∀ ω, τ ω ≤ T
  inside : ∀ ω t, t ≤ τ ω → greenLogNormSq κ (c.Q t ω) (B t ω) ≤ R^2 ∧ lo ≤ (c.Q t ω).1.im
  before : ∀ ω t, t < τ ω → greenLogNormSq κ (c.Q t ω) (B t ω) < R^2 ∧ lo < (c.Q t ω).1.im
  boundary : ∀ ω, τ ω < T → greenLogNormSq κ (c.Q (τ ω) ω) (B (τ ω) ω) = R^2 ∨
    (c.Q (τ ω) ω).1.im = lo

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StoppedPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopped Power for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def powerLogGenerator (κ p α : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  powerLogDensity κ p α q x *
    ((-4 * α + κ * α * (α + 1) / 2) * (q.1.re - Real.sqrt κ * x) ^ 2 +
      (4 * p - κ * α / 2) * Real.exp (2 * q.1.im)) /
    (greenLogNormSq κ q x) ^ 2

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SwallowExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Swallow Exit for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure BoundaryLocalization
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ a : ℝ} {q₀ : ℂ} (c : BoundaryClockSolution B hm κ a q₀)
    (α β R H : ℝ) (T : ℝ≥0) where
  τ : Ω → ℝ≥0
  stopping : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (τ ω : WithTop ℝ≥0))
  bounded : ∀ ω, τ ω ≤ T
  inside : ∀ ω t, t ≤ τ ω → ‖(c.Q t ω,B t ω)‖ ≤ R ∧
    3*a ≤ (c.Q t ω).re-Real.sqrt κ*B t ω ∧
    boundaryDensity κ α β (c.Q t ω) (B t ω) ≤ H
  before : ∀ ω t, t < τ ω → ‖(c.Q t ω,B t ω)‖ < R ∧
    3*a < (c.Q t ω).re-Real.sqrt κ*B t ω ∧
    boundaryDensity κ α β (c.Q t ω) (B t ω) < H
  boundary : ∀ ω, τ ω < T → ‖(c.Q (τ ω) ω,B (τ ω) ω)‖ = R ∨
    (c.Q (τ ω) ω).re-Real.sqrt κ*B (τ ω) ω = 3*a ∨
    boundaryDensity κ α β (c.Q (τ ω) ω) (B (τ ω) ω) = H

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

def IsPositiveBoundaryClockPath (U : ℝ≥0 → ℝ) (x : ℝ) (T : ℝ≥0) (Q : ℝ → ℂ) : Prop :=
  Q 0 = (x:ℂ) ∧
  (∀ t ∈ Icc 0 (T:ℝ), 0 < (Q t).re-U t.toNNReal) ∧
  (∀ t ∈ Icc 0 (T:ℝ), HasDerivWithinAt Q
    (((2/((Q t).re-U t.toNNReal):ℝ):ℂ)+
      (((Q t).re-U t.toNNReal)⁻¹^2:ℝ)*I) (Icc 0 (T:ℝ)) t)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def greenDensity (κ : ℝ) (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ survivingDomain γ t then
    (fullRadius G t z) ^ (-codimension κ) *
      (Real.sin (Complex.arg (G t z - (U t : ℂ)))) ^ greenExponent κ
  else 0

noncomputable def initialGreen (κ : ℝ) (z : ℂ) : ℝ :=
  (2 * z.im) ^ (-codimension κ) *
    (Real.sin (Complex.arg z)) ^ greenExponent κ

 

noncomputable def radiusLevelTime (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (u : ℝ) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | s < ∞ ∧ z ∈ survivingDomain γ s.toNNReal ∧
    fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u)}

 
noncomputable def stoppedGreen (κ : ℝ) (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (u : ℝ) : ℝ :=
  if radiusLevelTime γ G z u < ∞ then
    greenDensity κ U γ G (radiusLevelTime γ G z u).toNNReal z
  else 0

lemma logCoordinates_re (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0) :
    (logLoewnerCoordinates G z t).1.re = (G t z).re := by
  simp only [logLoewnerCoordinates, Real.toNNReal_coe, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_self, add_zero]

lemma logCoordinates_im (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0) :
    (logLoewnerCoordinates G z t).1.im = Real.log (G t z).im := by
  simp only [logLoewnerCoordinates, Real.toNNReal_coe, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    add_zero, zero_add]

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_NearRealContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near Real Contraction for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

def BoundaryComparisonFailure (U : ℝ≥0 → ℝ) (x r δ : ℝ) : Prop :=
  ∃ (T : ℝ≥0) (Q Z : ℝ → ℂ), IsPositiveBoundaryClockPath U x T Q ∧
    (∀ t ∈ Icc 0 (T:ℝ), HasDerivWithinAt Z
      (2/(Z t-(U t.toNNReal:ℂ))) (Icc 0 (T:ℝ)) t) ∧
    ‖Z 0-(x:ℂ)‖ ≤ r ∧
    (∀ t ∈ Icc 0 (T:ℝ), ‖Z t-((Q t).re:ℂ)‖ ≤ δ*((Q t).re-U t.toNNReal)) ∧
    δ*((Q T).re-U T) ≤ ‖Z T-((Q T).re:ℂ)‖

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_BrownianStrongMarkov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Brownian Strong Markov for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def shiftedFDD {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (I : Finset ℝ≥0) (s : ℝ≥0) (ω : Ω) : I → ℝ :=
  fun i => B (s + i) ω - B s ω

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def brownianRestart {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ := B (τ ω + t) ω - B (τ ω) ω

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

section
variable {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
  (U : ℝ≥0 → Ω → ℝ) (hUa : Adapted ℱ U)
  (hUc : ∀ ω, Continuous (fun t => U t ω))
include hUa hUc

lemma measurable_reverse_driver (T : ℝ≥0) :
    @Measurable (ℝ × Ω) ℝ ((borel ℝ).prod (ℱ T)) (borel ℝ)
      (fun p => U (min ((T : ℝ) - p.1).toNNReal T) p.2) := by
  have hsa : StronglyAdapted ℱ U := fun t => (hUa t).stronglyMeasurable
  have hp := (hsa.isStronglyProgressive_of_continuous hUc T).measurable
  let : MeasurableSpace Ω := ℱ T
  have ht : Measurable (fun s : ℝ => (⟨min ((T : ℝ) - s).toNNReal T,
      by change min ((T : ℝ) - s).toNNReal T ≤ T; exact min_le_right _ _⟩ : Iic T)) :=
    ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).min continuous_const).measurable.subtype_mk
  exact hp.comp ((ht.comp measurable_fst).prodMk measurable_snd)

 

theorem inverse_vertical_measurable
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (h : ∀ ω, IsCapacityTwoWitness (fun t => U t ω) (γ ω) (G ω) (F ω))
    (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    @Measurable Ω ℂ (ℱ T) (borel ℂ)
      (fun ω => F ω T ((U T ω : ℂ) + (a : ℂ) * I)) := by
  let V (s : ℝ) (ω : Ω) := U (min ((T : ℝ) - s).toNNReal T) ω
  have hVm := measurable_reverse_driver ℱ U hUa hUc T
  have hVc (ω : Ω) : Continuous (fun s : ℝ => V s ω) :=
    (hUc ω).comp ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).min continuous_const)
  let : MeasurableSpace Ω := ℱ T
  have hwm : Measurable (fun ω => (U T ω : ℂ) + (a : ℂ) * I) :=
    (Complex.continuous_ofReal.measurable.comp (hUa T)).add_const _
  obtain ⟨Q, hQm, hQ0, hQd⟩ := exists_measurable_reverse_flow V hVm hVc
    (fun ω => (U T ω : ℂ) + (a : ℂ) * I) hwm ha
  have he (ω : Ω) : Q (T : ℝ) ω = F ω T ((U T ω : ℂ) + (a : ℂ) * I) := by
    apply (h ω).reverse_flow_identifies T _ ha (by simp) (fun s => Q s ω) (hQ0 ω)
    intro s hs
    have hsT : ((T : ℝ) - s).toNNReal ≤ T :=
      Real.toNNReal_le_iff_le_coe.mpr (by linarith [hs.1])
    simpa only [V, min_eq_left hsT] using
      (hQd ω s hs.1).mono (show Icc (0 : ℝ) T ⊆ Ici 0 from Icc_subset_Ici_self)
  have hefun : (fun ω => Q (T : ℝ) ω) = (fun ω => F ω T ((U T ω : ℂ) + (a : ℂ) * I)) := funext he
  rw [← hefun]
  exact hQm.comp (measurable_prodMk_left (x := (T : ℝ)))

 

theorem capacity_trace_adapted
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (h : ∀ ω, IsCapacityTwoWitness (fun t => U t ω) (γ ω) (G ω) (F ω)) :
    Adapted ℱ (fun t ω => γ ω t) := by
  intro T
  have hn (n : ℕ) : @Measurable Ω ℂ (ℱ T) (borel ℂ)
      (fun ω => F ω T ((U T ω : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I)) :=
    inverse_vertical_measurable ℱ U hUa hUc γ G F h T (by positivity)
  let : MeasurableSpace Ω := ℱ T
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => F ω T ((U T ω : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I))
  · exact hn
  · apply tendsto_pi_nhds.mpr
    intro ω
    have hy : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall (fun n => by change (0 : ℝ) < 1 / ((n : ℝ) + 1); positivity)⟩
    exact ((h ω).2.2.2.2.2.2.2.2.2.2.2.2 T).comp hy

end
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



structure RegularSLEPresentation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) where
  samples : Set Ω
  measurable_samples : MeasurableSet samples
  full_samples : ∀ᵐ ω ∂P, ω ∈ samples
  B : ℝ≥0 → samples → ℝ
  measurable_B : ∀ t, Measurable (B t)
  continuous_B : ∀ ω, Continuous (fun t => B t ω)
  zero_B : ∀ ω, B 0 ω = 0
  brownian : IsBrownianReal B (P.comap (Subtype.val : samples → Ω))
  G : samples → ℝ≥0 → ℂ → ℂ
  F : samples → ℝ≥0 → ℂ → ℂ
  witness : ∀ ω : samples, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
    (γ ω) (G ω) (F ω)

namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}

instance probability [IsProbabilityMeasure P] (a : RegularSLEPresentation P κ γ) :
    IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) :=
  (MeasurableEmbedding.subtype_coe a.measurable_samples).isProbabilityMeasure_comap
    (by simpa only [Subtype.range_coe] using a.full_samples)

def filtration (a : RegularSLEPresentation P κ γ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace a.samples) :=
  Filtration.natural a.B (fun t => (a.measurable_B t).stronglyMeasurable)

lemma trace_adapted (a : RegularSLEPresentation P κ γ) :
    Adapted a.filtration (fun t ω => γ ω t) := by
  apply capacity_trace_adapted a.filtration (fun t ω => Real.sqrt κ * a.B t ω)
    ?_ ?_ (γ ∘ Subtype.val) a.G a.F a.witness
  · intro t
    exact measurable_const.mul
      ((Filtration.stronglyAdapted_natural (fun t => (a.measurable_B t).stronglyMeasurable)) t).measurable
  · intro ω
    exact continuous_const.mul (a.continuous_B ω)

lemma trace_continuous (a : RegularSLEPresentation P κ γ) (ω : a.samples) :
    Continuous (γ ω) := (a.witness ω).1

end RegularSLEPresentation



end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_DiskHalfPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Half Plane for chordal SLE. -/

section
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def diskToHalfPlane (w ζ : ℂ) : ℂ := (w - star w * ζ) / (1 - ζ)

@[simp] lemma diskToHalfPlane_zero (w : ℂ) : diskToHalfPlane w 0 = w := by simp [diskToHalfPlane]

end SLEExactGauge
end


section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure FiniteIncreasingClock (Ω : Type*) where
  S : ℝ → Ω → ℝ
  T : Ω → ℝ≥0
  zero : ∀ ω, S 0 ω = 0
  continuous : ∀ ω, Continuous (fun t => S t ω)
  strict : ∀ ω, StrictMonoOn (fun t => S t ω) (Icc 0 (T ω : ℝ))

namespace FiniteIncreasingClock
variable {Ω : Type*} (c : FiniteIncreasingClock Ω)

lemma terminal_nonneg (ω : Ω) : 0 ≤ c.S (c.T ω) ω := by
  rw [← c.zero ω]
  exact (c.strict ω).monotoneOn ⟨le_rfl, (c.T ω).coe_nonneg⟩
    ⟨(c.T ω).coe_nonneg, le_rfl⟩ (c.T ω).coe_nonneg

noncomputable def iso (ω : Ω) : Icc (0 : ℝ) (c.T ω : ℝ) ≃o Icc (0 : ℝ) (c.S (c.T ω) ω) := by
  let f : Icc (0 : ℝ) (c.T ω : ℝ) → Icc (0 : ℝ) (c.S (c.T ω) ω) := fun t =>
    ⟨c.S t ω, by
      constructor
      · simpa only [c.zero ω] using
          ((c.strict ω).monotoneOn ⟨le_rfl, (c.T ω).coe_nonneg⟩ t.property t.property.1)
      · exact (c.strict ω).monotoneOn t.property ⟨(c.T ω).coe_nonneg, le_rfl⟩ t.property.2⟩
  apply StrictMono.orderIsoOfSurjective f
  · intro s t hst
    exact c.strict ω s.property t.property hst
  · intro s
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc (c.T ω).coe_nonneg
      (c.continuous ω).continuousOn (show (s : ℝ) ∈ Icc (c.S 0 ω) (c.S (c.T ω) ω) by
        simpa only [c.zero ω] using s.property)
    exact ⟨⟨t, ht⟩, Subtype.ext he⟩

noncomputable def inverse (s : ℝ) (ω : Ω) : ℝ :=
  ((c.iso ω).symm ⟨min (max s 0) (c.S (c.T ω) ω),
    ⟨le_min (le_max_right _ _) (c.terminal_nonneg ω), min_le_right _ _⟩⟩ : ℝ)

end FiniteIncreasingClock
end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure AngularLocalization {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t)) (κ : ℝ)
    (z : ℂ) (u ε : ℝ) where
  lo : ℝ
  hi : ℝ
  le : lo ≤ hi
  solution : ClippedLogSolution B hm κ lo hi le (initialLogCoordinates z)
  T : ℝ≥0
  τ : Ω → ℝ≥0
  stopping : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (τ ω : WithTop ℝ≥0))
  bounded : ∀ ω, τ ω ≤ T
  inside : ∀ ω t, t ≤ τ ω →
    logRadiusClock (Real.log z.im) (solution.Q t ω) ≤ u ∧
    ε ≤ logAngleSq κ (solution.Q t ω) (B t ω) ∧
    lo ≤ (solution.Q t ω).1.im ∧ (solution.Q t ω).1.im ≤ hi
  before : ∀ ω t, t < τ ω →
    logRadiusClock (Real.log z.im) (solution.Q t ω) < u ∧
    ε < logAngleSq κ (solution.Q t ω) (B t ω)
  boundary : ∀ ω,
    logRadiusClock (Real.log z.im) (solution.Q (τ ω) ω) = u ∨
    logAngleSq κ (solution.Q (τ ω) ω) (B (τ ω) ω) = ε

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

lemma clock_stopped_measurable :
    Measurable[a.stopping.measurableSpace]
      (fun ω => logRadiusClock (Real.log z.im) (a.solution.Q (a.τ ω) ω)) := by
  have hQa : StronglyAdapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t : ℝ≥0 => a.solution.Q t) := fun t => (a.solution.adapted t).stronglyMeasurable
  have hQc (ω : Ω) : Continuous (fun t : ℝ≥0 => a.solution.Q t ω) :=
    (a.solution.lipschitz ω).continuous.comp NNReal.continuous_coe
  have hQ := measurable_stoppedValue (hQa.isStronglyProgressive_of_continuous hQc) a.stopping
  have hmQ : Measurable[a.stopping.measurableSpace] (fun ω => a.solution.Q (a.τ ω) ω) := by
    exact hQ
  exact (continuous_logRadiusClock _).measurable.comp hmQ

end AngularLocalization
end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_AngularPowerDynkin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Power Dynkin for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε δ : ℝ}

 

lemma synchronize (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v δ) (ω : Ω)
    (t : ℝ≥0) (ha : t ≤ a.τ ω) (hb : t ≤ b.τ ω) :
    a.solution.Q t ω = b.solution.Q t ω := by
  let lo := min a.lo b.lo
  let hi := max a.hi b.hi
  have hle : lo ≤ hi := (min_le_left _ _).trans (a.le.trans (le_max_left _ _))
  obtain ⟨L, K, hbound, hlip⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (s : ℝ) := clippedLogLoewnerField lo hi hle (Real.sqrt κ * B s.toNNReal ω)
  have hd (c : AngularLocalization B hm κ z u ε) (hc : t ≤ c.τ ω)
      (hlo : lo ≤ c.lo) (hhi : c.hi ≤ hi) (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      HasDerivWithinAt (fun s => c.solution.Q s ω) (V s (c.solution.Q s ω)) (Icc 0 (t : ℝ)) s := by
    have hsc : s.toNNReal ≤ c.τ ω := (Real.toNNReal_le_iff_le_coe.mpr hs.2).trans hc
    have hcbar := (c.inside ω s.toNNReal hsc).2.2
    rw [Real.coe_toNNReal _ hs.1] at hcbar
    have hder := (c.solution.derivative ω s hs.1).mono
      (show Icc (0 : ℝ) (t : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
    rwa [clippedLogLoewnerField_eq_physical _ _ _ _ _ hcbar,
      ← clippedLogLoewnerField_eq_physical lo hi hle _ _ ⟨hlo.trans hcbar.1, hcbar.2.trans hhi⟩] at hder
  have hda := hd a ha (min_le_left _ _) (le_max_left _ _)
  have hdb (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      HasDerivWithinAt (fun s => b.solution.Q s ω) (V s (b.solution.Q s ω)) (Icc 0 (t : ℝ)) s := by
    have hsb : s.toNNReal ≤ b.τ ω := (Real.toNNReal_le_iff_le_coe.mpr hs.2).trans hb
    have hcbar := (b.inside ω s.toNNReal hsb).2.2
    rw [Real.coe_toNNReal _ hs.1] at hcbar
    have hder := (b.solution.derivative ω s hs.1).mono
      (show Icc (0 : ℝ) (t : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
    rwa [clippedLogLoewnerField_eq_physical _ _ _ _ _ hcbar,
      ← clippedLogLoewnerField_eq_physical lo hi hle _ _
        ⟨(min_le_right _ _).trans hcbar.1, hcbar.2.trans (le_max_right _ _)⟩] at hder
  have he : EqOn (fun s => a.solution.Q s ω) (fun s => b.solution.Q s ω) (Icc 0 (t : ℝ)) := by
    apply ODE_solution_unique (fun s => hlip (Real.sqrt κ * B s.toNNReal ω))
      (fun s hs => (hda s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hda s ⟨hs.1, hs.2.le⟩))
      (fun s hs => (hdb s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hdb s ⟨hs.1, hs.2.le⟩))
    exact (a.solution.initial ω).trans (b.solution.initial ω).symm
  exact he ⟨t.coe_nonneg, le_rfl⟩

lemma stopping_le (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v δ) (huv : u ≤ v) (hδε : δ ≤ ε)
    (ω : Ω) : a.τ ω ≤ b.τ ω := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have he := a.synchronize b ω (b.τ ω) hlt.le le_rfl
  have hh := a.before ω _ hlt
  rw [he] at hh
  rcases b.boundary ω with hc | hθ
  · linarith [hh.1]
  · linarith [hh.2]

lemma hit_time_unique (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z u δ) (ω : Ω)
    (ha : logRadiusClock (Real.log z.im) (a.solution.Q (a.τ ω) ω) = u)
    (hb : logRadiusClock (Real.log z.im) (b.solution.Q (b.τ ω) ω) = u) :
    a.τ ω = b.τ ω := by
  apply le_antisymm
  · by_contra hn
    have hlt := lt_of_not_ge hn
    have he := a.synchronize b ω (b.τ ω) hlt.le le_rfl
    have hh := (a.before ω _ hlt).1
    rw [he, hb] at hh
    exact lt_irrefl _ hh
  · by_contra hn
    have hlt := lt_of_not_ge hn
    have he := b.synchronize a ω (a.τ ω) hlt.le le_rfl
    have hh := (b.before ω _ hlt).1
    rw [he, ha] at hh
    exact lt_irrefl _ hh

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

lemma radius_clock_derivative (ω : Ω) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (a.τ ω : ℝ)) :
    HasDerivWithinAt (fun t => logRadiusClock (Real.log z.im) (a.solution.Q t ω))
      (logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω)) (Icc (0 : ℝ) (a.τ ω : ℝ)) t := by
  have hd := (a.solution.derivative ω t ht.1).mono
    (show Icc (0 : ℝ) (a.τ ω : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
  have hb := (a.inside ω t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2)).2.2
  rw [Real.coe_toNNReal t ht.1] at hb
  rw [clippedLogLoewnerField_eq_physical _ _ _ _ _ hb] at hd
  exact log_ode_clock_derivative (Real.log z.im) hd

noncomputable def clock : FiniteIncreasingClock Ω where
  S t ω := logRadiusClock (Real.log z.im) (a.solution.Q t ω)
  T := a.τ
  zero ω := by rw [a.solution.initial]; simp [logRadiusClock, initialLogCoordinates]
  continuous ω := (continuous_logRadiusClock _).comp (a.solution.lipschitz ω).continuous
  strict ω := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (0 : ℝ) (a.τ ω : ℝ))
      ((continuous_logRadiusClock _).comp (a.solution.lipschitz ω).continuous).continuousOn
    · intro t ht
      exact (a.radius_clock_derivative ω t (interior_subset ht)).mono interior_subset
    · intro t ht
      exact logClockRate_pos κ (a.solution.Q t ω) (B t.toNNReal ω)

lemma clock_upper (ω : Ω) : a.clock.S (a.τ ω) ω ≤ u := (a.inside ω _ le_rfl).1

noncomputable def radiusValue (p α s : ℝ) (ω : Ω) : ℝ :=
  powerLogDensity κ p α (a.solution.Q (a.clock.inverse s ω) ω)
    (B (a.clock.inverse s ω).toNNReal ω)

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε v δ : ℝ}
  (a : AngularLocalization B hm κ z u ε)

noncomputable def radiusKernel (p α s : ℝ) (ω : Ω) : ℝ :=
  if s ≤ a.clock.S (a.τ ω) ω then a.radiusValue p α s ω else 0

lemma terminal_clock_le (b : AngularLocalization B hm κ z v δ)
    (huv : u ≤ v) (hδε : δ ≤ ε) (ω : Ω) :
    a.clock.S (a.τ ω) ω ≤ b.clock.S (b.τ ω) ω := by
  have ht := a.stopping_le b huv hδε ω
  have he := a.synchronize b ω (a.τ ω) le_rfl ht
  change logRadiusClock _ _ ≤ logRadiusClock _ _
  rw [he]
  exact (b.clock.strict ω).monotoneOn ⟨(a.τ ω).coe_nonneg, by exact_mod_cast ht⟩
    ⟨(b.τ ω).coe_nonneg, le_rfl⟩ (by exact_mod_cast ht)

end AngularLocalization
end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε δ : ℝ}

lemma terminal_clock_min (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v ε) (huv : u ≤ v) (ω : Ω) :
    a.clock.S (a.τ ω) ω = min u (b.clock.S (b.τ ω) ω) := by
  have ht := a.stopping_le b huv le_rfl ω
  apply le_antisymm
  · exact le_min (a.clock_upper ω) (a.terminal_clock_le b huv le_rfl ω)
  · rcases a.boundary ω with hc | ha
    · exact (min_le_left _ _).trans_eq hc.symm
    · have he : a.τ ω = b.τ ω := by
        apply le_antisymm ht
        by_contra hn
        have hh := (b.before ω _ (lt_of_not_ge hn)).2
        rw [← a.synchronize b ω (a.τ ω) le_rfl ht, ha] at hh
        exact lt_irrefl _ hh
      have hq := a.synchronize b ω (a.τ ω) le_rfl ht
      change min u (logRadiusClock _ _) ≤ logRadiusClock _ _
      rw [hq, he]
      exact min_le_right _ _

end AngularLocalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

 

noncomputable def limitRadiusKernel (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (p α s : ℝ) (ω : Ω) : ℝ :=
  if h : ∃ n, max s 0 ≤ (a n).clock.S ((a n).τ ω) ω then
    (a (Nat.find h)).radiusKernel p α (max s 0) ω else 0

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}

def hit (a : AngularLocalization B hm κ z u ε) : Set Ω :=
  {ω | logRadiusClock (Real.log z.im) (a.solution.Q (a.τ ω) ω) = u}

lemma measurable_hit (a : AngularLocalization B hm κ z u ε) :
    MeasurableSet[a.stopping.measurableSpace] a.hit :=
  measurableSet_eq_fun a.clock_stopped_measurable measurable_const

noncomputable def hitTime (a : AngularLocalization B hm κ z u ε) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ a.hit then (a.τ ω : WithTop ℝ≥0) else ⊤

end AngularLocalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

 

noncomputable def localizedRadiusStop
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ n, (a n).hitTime ω

lemma localizedRadiusStop_eq_hit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω) (n : ℕ)
    (hn : ω ∈ (a n).hit) : localizedRadiusStop a ω = ((a n).τ ω : WithTop ℝ≥0) := by
  apply le_antisymm
  · exact (iInf_le _ n).trans_eq (by rw [AngularLocalization.hitTime, ite_eq_left hn])
  · apply le_iInf
    intro m
    by_cases h : ω ∈ (a m).hit
    · have he := (a m).hit_time_unique (a n) ω h hn
      rw [AngularLocalization.hitTime, ite_eq_left h, he]
    · rw [AngularLocalization.hitTime, ite_eq_right h]
      exact le_top

lemma localizedRadiusStop_eq_top
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω)
    (hn : ∀ n, ω ∉ (a n).hit) : localizedRadiusStop a ω = ⊤ := by
  simp [localizedRadiusStop, AngularLocalization.hitTime, hn]

lemma localizedRadiusStop_le_iff
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω) (t : ℝ≥0) :
    localizedRadiusStop a ω ≤ (t : WithTop ℝ≥0) ↔ ∃ n, ω ∈ (a n).hit ∧ (a n).τ ω ≤ t := by
  constructor
  · intro h
    by_cases he : ∃ n, ω ∈ (a n).hit
    · obtain ⟨n, hn⟩ := he
      rw [localizedRadiusStop_eq_hit a ω n hn, WithTop.coe_le_coe] at h
      exact ⟨n, hn, h⟩
    · rw [localizedRadiusStop_eq_top a ω (not_exists.mp he)] at h
      exact False.elim (WithTop.coe_ne_top (a := t) (top_le_iff.mp h))
  · rintro ⟨n, hn, ht⟩
    rw [localizedRadiusStop_eq_hit a ω n hn, WithTop.coe_le_coe]
    exact ht

lemma localizedRadiusStop_stopping
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) :
    IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (localizedRadiusStop a) := by
  intro t
  have he : {ω | localizedRadiusStop a ω ≤ (t : WithTop ℝ≥0)} =
      ⋃ n, ((a n).hit ∩ {ω | ((a n).τ ω : WithTop ℝ≥0) ≤ t}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, WithTop.coe_le_coe]
    exact localizedRadiusStop_le_iff a ω t
  rw [he]
  exact MeasurableSet.iUnion fun n => (a n).measurable_hit.2 t

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_KernelExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Expectation for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}

noncomputable def weight (a : AngularLocalization B hm κ z u ε) (ω : Ω) : ℝ :=
  greenLogDensity κ (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)

end AngularLocalization

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def stoppedAngleSq (κ : ℝ) (B : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (u : ℝ) : ℝ :=
  if radiusLevelTime γ G z u < ∞ then
    (Real.sin (Complex.arg (G (radiusLevelTime γ G z u).toNNReal z -
      ((Real.sqrt κ * B (radiusLevelTime γ G z u).toNNReal : ℝ) : ℂ)))) ^ 2
  else 0

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_FiniteStoppedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Stopped Law for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



noncomputable def finiteCenteredLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (u : ℝ) : Measure Ω :=
  P.withDensity (fun ω => ENNReal.ofReal
    (stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u / initialGreen κ z))

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ≥0} {ε : ℕ → ℝ}

noncomputable def radiusMoment (P : Measure Ω)
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (b s : ℝ) : ℝ :=
  (∫ ω, limitRadiusKernel c (codimension κ) (greenExponent κ - b) s ω ∂P) / initialGreen κ z

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 
noncomputable def stoppedInverseAngle (κ : ℝ) (B : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (u b : ℝ) : ℝ :=
  (stoppedAngleSq κ B γ G z u) ^ (-b / 2)

end SLEExactGauge
end


section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

noncomputable def lyapunovBarrier (r K δ t : ℝ) : ℝ := K ^ r * (t + δ) ^ (-r)

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def lyapunovA (κ b : ℝ) : ℝ := (κ * b / 8) * (1 + (greenExponent κ - b))
noncomputable def lyapunovC (κ b : ℝ) : ℝ := (κ * b / 8) * (greenExponent κ - b)
noncomputable def angularMomentBound (κ b η : ℝ) : ℝ :=
  ((2 * lyapunovA κ b + b / 2 + 1) / lyapunovC κ b / η) ^ (b / 2)

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RadiusClocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radius Clocks for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge
lemma measurableSet_exists_zero_compact
    {Ω K : Type*} [MeasurableSpace Ω] [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace.SeparableSpace K] [Nonempty K]
    (f : K → Ω → ℝ) (hm : ∀ t, Measurable (f t))
    (hc : ∀ ω, Continuous (fun t => f t ω)) :
    MeasurableSet {ω | ∃ t, f t ω = 0} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense K
  let : Countable D := hDc.to_subtype
  have hi : Measurable (fun ω => ⨅ t : D, |f t ω|) :=
    Measurable.iInf (fun t => (hm t).abs)
  have he (ω : Ω) : (∃ t, f t ω = 0) ↔ (⨅ t : D, |f t ω|) = 0 := by
    have hb : BddBelow (range (fun t => |f t ω|)) := ⟨0, by rintro _ ⟨t, rfl⟩; exact abs_nonneg _⟩
    rw [hDd.ciInf (hc ω).abs hb]
    obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set K).Nonempty)
      (hc ω).abs.continuousOn
    have hv : (⨅ s, |f s ω|) = |f t ω| :=
      le_antisymm (ciInf_le hb t) (le_ciInf (fun s => ht (mem_univ s)))
    rw [hv]
    constructor
    · rintro ⟨s, hs⟩
      have ht' : |f t ω| ≤ |f s ω| := ht (mem_univ s)
      rw [hs, abs_zero] at ht'
      exact le_antisymm ht' (abs_nonneg _)
    · intro h
      exact ⟨t, abs_eq_zero.mp h⟩
  have hs : MeasurableSet {ω | (⨅ t : D, |f t ω|) = 0} :=
    measurableSet_eq_fun hi measurable_const
  have heSet : {ω | ∃ t, f t ω = 0} = {ω | (⨅ t : D, |f t ω|) = 0} :=
    Set.ext he
  rw [heSet]
  exact hs

lemma hittingAfter_zero_le_iff
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => X t ω)) (n T : ℝ≥0) (ω : Ω) :
    hittingAfter X {0} n ω ≤ (T : WithTop ℝ≥0) ↔
      ∃ t ∈ Icc n T, X t ω = 0 := by
  classical
  let V : Set ℝ≥0 := {t | n ≤ t ∧ X t ω = 0}
  have hV : IsClosed V := isClosed_Ici.inter (isClosed_eq (hc ω) continuous_const)
  have hb : BddBelow V := ⟨0, fun t _ => bot_le⟩
  change (if V.Nonempty then ((sInf V : ℝ≥0) : WithTop ℝ≥0) else ⊤) ≤ (T : WithTop ℝ≥0) ↔ _
  by_cases hv : V.Nonempty
  · obtain ⟨v, hv⟩ := hv
    have he : ∃ t, n ≤ t ∧ X t ω ∈ ({0} : Set ℝ) := ⟨v, hv.1, hv.2⟩
    have hin : sInf V ∈ V := hV.csInf_mem ⟨v, hv⟩ hb
    rw [ite_eq_left (show V.Nonempty from ⟨v, hv⟩), WithTop.coe_le_coe]
    constructor
    · intro h
      exact ⟨sInf V, ⟨hin.1, h⟩, hin.2⟩
    · rintro ⟨t, ht, hx⟩
      exact (csInf_le hb ⟨ht.1, hx⟩).trans ht.2
  · have he : ¬ ∃ t, n ≤ t ∧ X t ω ∈ ({0} : Set ℝ) := by
      exact hv
    rw [ite_eq_right hv]
    simp only [WithTop.not_top_le_coe, false_iff]
    rintro ⟨t, ht, hx⟩
    exact hv ⟨t, ht.1, hx⟩



end SLEExactGauge

end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge

lemma stopped_min_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 m} {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime ℱ (fun ω => (ρ ω : WithTop ℝ≥0))) (T : ℝ≥0) :
    Measurable[ℱ T] (fun ω => min (ρ ω) T) := by
  have h := ((hρ.min_const T).measurable_of_le (fun _ => min_le_right _ _)).untopD 0
  simpa only [← WithTop.coe_min, WithTop.untopD_coe] using h

 

theorem continuous_zero_hit_after_stopping
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (X : ℝ≥0 → Ω → ℝ) (hXa : Adapted ℱ X)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) (ρ : Ω → ℝ≥0)
    (hρ : IsStoppingTime ℱ (fun ω => (ρ ω : WithTop ℝ≥0))) :
    IsStoppingTime ℱ (fun ω => hittingAfter X {0} (ρ ω) ω) := by
  intro T
  let f : Icc (0 : ℝ≥0) T → Ω → ℝ :=
    fun t ω => |X t ω| + max (((min (ρ ω) T : ℝ≥0) : ℝ) - (t : ℝ≥0)) 0
  have he : {ω | hittingAfter X {0} (ρ ω) ω ≤ (T : WithTop ℝ≥0)} =
      {ω | ρ ω ≤ T} ∩ {ω | ∃ t : Icc (0 : ℝ≥0) T, f t ω = 0} := by
    ext ω
    rw [mem_ofPred_eq, hittingAfter_zero_le_iff X hXc]
    constructor
    · rintro ⟨t, ht, hx⟩
      have hr : ρ ω ≤ T := ht.1.trans ht.2
      refine ⟨hr, ⟨⟨t, bot_le, ht.2⟩, ?_⟩⟩
      dsimp only [f]
      rw [hx, abs_zero, min_eq_left hr, max_eq_right (sub_nonpos.mpr (show (ρ ω : ℝ) ≤ (t : ℝ) from ht.1))]
      exact zero_add 0
    · rintro ⟨hr, t, ht⟩
      have hp : 0 ≤ max (((min (ρ ω) T : ℝ≥0) : ℝ) - (t : ℝ≥0)) 0 := le_max_right _ _
      have hx : X t ω = 0 := abs_eq_zero.mp (by dsimp only [f] at ht; linarith [abs_nonneg (X t ω)])
      have hle : (ρ ω : ℝ) ≤ (t : ℝ≥0) := by
        dsimp only [f] at ht
        rw [min_eq_left hr] at ht
        have hh := le_max_left ((ρ ω : ℝ) - (t : ℝ≥0)) 0
        linarith [abs_nonneg (X t ω)]
      exact ⟨t, ⟨hle, t.property.2⟩, hx⟩
  rw [he]
  have hmρ := stopped_min_measurable hρ T
  have hmX (t : Icc (0 : ℝ≥0) T) : Measurable[ℱ T] (X t) :=
    (hXa t).mono (ℱ.mono t.property.2) le_rfl
  let : MeasurableSpace Ω := ℱ T
  have hm (t : Icc (0 : ℝ≥0) T) : Measurable (f t) :=
    (hmX t).abs.add (((NNReal.continuous_coe.measurable.comp hmρ).sub measurable_const).max measurable_const)
  have hme : MeasurableSet {ω | ∃ t : Icc (0 : ℝ≥0) T, f t ω = 0} := by
    let : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, bot_le⟩⟩
    apply measurableSet_exists_zero_compact f hm
    intro ω
    exact ((hXc ω).comp continuous_subtype_val).abs.add
      ((continuous_const.sub (NNReal.continuous_coe.comp continuous_subtype_val)).max continuous_const)
  have hmle : MeasurableSet {ω | ρ ω ≤ T} := by
    simpa only [WithTop.coe_le_coe] using hρ T
  exact hmle.inter hme

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def diskHitAfter {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (ρ : Ω → ℝ≥0) (z : ℂ) (r : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  hittingAfter (fun t ω => dist (γ ω t) z - r) {0} (ρ ω) ω

namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma diskHitAfter_stopping (ρ : a.samples → ℝ≥0)
    (hρ : IsStoppingTime a.filtration (fun ω => (ρ ω : WithTop ℝ≥0)))
    (z : ℂ) (r : ℝ) :
    IsStoppingTime a.filtration (diskHitAfter (γ ∘ Subtype.val) ρ z r) := by
  apply continuous_zero_hit_after_stopping a.filtration
    (fun t ω => dist (γ ω t) z - r) ?_ ?_ ρ hρ
  · intro t
    have hm := a.trace_adapted t
    let : MeasurableSpace a.samples := a.filtration t
    exact (hm.dist measurable_const).sub measurable_const
  · intro ω
    exact ((a.trace_continuous ω).dist continuous_const).sub continuous_const

noncomputable def boundedDiskHit (ρ : a.samples → ℝ≥0) (z : ℂ) (r : ℝ)
    (T : ℝ≥0) (ω : a.samples) : ℝ≥0 :=
  (min (diskHitAfter (γ ∘ Subtype.val) ρ z r ω) T).untopD 0

end RegularSLEPresentation
end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

noncomputable def polarPoint (r θ : ℝ) : ℂ := r • circleMap 0 1 θ

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian
namespace SLEExactGauge

noncomputable def polarRadialFlux (u : ℂ → ℝ) (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (Real.log R - Real.log p.1) *
    fderiv ℝ u (polarPoint p.1 p.2) (circleMap 0 1 p.2) + u (polarPoint p.1 p.2)

noncomputable def polarAngularFlux (u : ℂ → ℝ) (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Real.log R - Real.log p.1) / p.1 *
    fderiv ℝ u (polarPoint p.1 p.2) (polarPoint p.1 p.2 * I)

end SLEExactGauge

end


section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge

noncomputable def annulusDensity (u : ℂ → ℝ) (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (Real.log R - Real.log p.1) * (-(Δ u) (polarPoint p.1 p.2))

def greenRectangle (a R : ℝ) : Set (ℝ × ℝ) := Icc a R ×ˢ Icc (-Real.pi) Real.pi

noncomputable def greenTruncation (u : ℂ → ℝ) (a R : ℝ) : ℝ × ℝ → ℝ :=
  (greenRectangle a R).indicator (annulusDensity u R)

end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_AngularLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Laws for chordal SLE. -/

section
section
section
open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge
noncomputable def greenInner (n : ℕ) : ℝ := (1 / 2) * (1 / ((n : ℝ) + 1))
noncomputable def greenOuter (n : ℕ) : ℝ := 1 - greenInner n

def polarUnitDisk : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo (-Real.pi) Real.pi

noncomputable def polarGreenTarget (u : ℂ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  polarUnitDisk.indicator (fun p : ℝ × ℝ =>
    ENNReal.ofReal (p.1 * (-Real.log p.1) * (-(Δ u) (polarPoint p.1 p.2)))) p

end SLEExactGauge

end


section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian RealInnerProductSpace
namespace SLEExactGauge

noncomputable def diskWeight (z : ℂ) : ℝ := 1 - ‖z‖ ^ 2

end SLEExactGauge

end


section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian RealInnerProductSpace
namespace SLEExactGauge

noncomputable def diskLogRadius (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  Real.log (diskWeight z) + Real.log ‖deriv f z‖

end SLEExactGauge
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StoppedKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopped Kernels for chordal SLE. -/

section
section


section

open Set Filter Metric
open scoped Topology
namespace SLEExactGauge

 

noncomputable def layerProfile (r q x : ℝ) : ℝ :=
  r ^ 2 * Real.exp (q * (x - Real.log r)) / (1 + Real.exp (q * (x - Real.log r)))

noncomputable def layerProfileDeriv (r q x : ℝ) : ℝ :=
  q * r ^ 2 * Real.exp (q * (x - Real.log r)) /
    (1 + Real.exp (q * (x - Real.log r))) ^ 2

end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

noncomputable def layerExponent : ℝ := (2 * (2560 * Real.pi + 6) ^ 2 + 1)⁻¹

noncomputable def diskLayerBarrier (f : ℂ → ℂ) (r : ℝ) : ℂ → ℝ :=
  layerProfile r layerExponent ∘ diskLogRadius f

end SLEExactGauge

end


section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

noncomputable def layerGreenConstant : ℝ :=
  (8 * Real.pi / layerExponent) * (256 * Real.pi) ^ 2

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def halfPlaneToDisk (w v : ℂ) : ℂ := (v - w) / (v - star w)

end SLEExactGauge

end

 
section

open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
namespace SLEExactGauge

 

noncomputable def halfPlaneGreen (z w : ℂ) : ℝ :=
  Real.log ‖(z - conj w) / (z - w)‖



end SLEExactGauge
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_KernelConsistency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Consistency for chordal SLE. -/

section
section


section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def chartPoissonRate (U : ℝ≥0 → ℝ) (G : ℝ≥0 → ℂ → ℂ)
    (t : ℝ≥0) (z : ℂ) : ℝ := (G t z).im / ‖G t z - (U t : ℂ)‖ ^ 2

end SLEExactGauge

end


section

open Set Filter Metric MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def greenBrownianCoefficient (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  Real.sqrt κ * greenExponent κ * (G t z - (U t : ℂ)).re /
    ‖G t z - (U t : ℂ)‖ ^ 2 * greenDensity κ U γ G t z

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}

noncomputable def physicalWeight (a : AngularLocalization B hm κ z u ε)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  greenLogDensity κ (a.solution.Q (min t (a.τ ω)) ω) (B (min t (a.τ ω)) ω)

end AngularLocalization
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v : ℝ} {ε : ℕ → ℝ}

lemma localizedRadiusStop_mono
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (b : ∀ n, AngularLocalization B hm κ z v (ε n)) (huv : u ≤ v) :
    localizedRadiusStop a ≤ localizedRadiusStop b := by
  intro ω
  apply le_iInf
  intro n
  unfold AngularLocalization.hitTime
  split_ifs with hn
  · have hc := (a n).terminal_clock_min (b n) huv ω
    have hb : (b n).clock.S ((b n).τ ω) ω = v := hn
    rw [hb, min_eq_left huv] at hc
    rw [localizedRadiusStop_eq_hit a ω n hc]
    exact WithTop.coe_le_coe.mpr ((a n).stopping_le (b n) huv le_rfl ω)
  · exact le_top


noncomputable def radiusFiltration
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n)) : Filtration ℝ≥0 mΩ where
  seq u := (localizedRadiusStop_stopping (a u)).measurableSpace
  mono' u v huv := (localizedRadiusStop_stopping (a u)).measurableSpace_mono
    (localizedRadiusStop_stopping (a v)) (localizedRadiusStop_mono (a u) (a v) (by exact_mod_cast huv))
  le' u := (localizedRadiusStop_stopping (a u)).measurableSpace_le

end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_AngularMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Moments for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}
noncomputable def physicalGreenLimit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => (a n).physicalWeight t ω)

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def physicalStoppedGreen (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (u : ℝ) (t : ℝ≥0) : ℝ :=
  if radiusLevelTime γ G z u ≤ (t : ℝ≥0∞) then stoppedGreen κ U γ G z u
    else greenDensity κ U γ G t z

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

noncomputable def terminalGreenLimit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => (a n).weight ω)

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

def naturalNatFiltration (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t)) : Filtration ℕ mΩ where
  seq n := (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) n
  mono' := fun n m h => (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono (by exact_mod_cast h)
  le' n := (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le n

end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_InverseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse Moments for chordal SLE. -/

section
section


section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def spatialHitTime (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) : WithTop ℝ≥0 :=
  hittingAfter (fun t (_ : Unit) => dist (γ t) z - r) {0} 0 ()

lemma spatialHitTime_le_iff {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    spatialHitTime γ z r ≤ (T : WithTop ℝ≥0) ↔
      ∃ t ∈ Icc 0 T, dist (γ t) z = r := by
  simpa only [spatialHitTime, sub_eq_zero] using
    hittingAfter_zero_le_iff (fun t (_ : Unit) => dist (γ t) z - r)
      (fun _ => (hc.dist continuous_const).sub continuous_const) 0 T ()

noncomputable def spatialGreenWeight (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (r : ℝ) : ℝ :=
  if spatialHitTime γ z r = ⊤ then 0 else
    greenDensity κ U γ G ((spatialHitTime γ z r).untopD 0) z

noncomputable def boundedSpatialHit (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ)
    (T : ℝ≥0) : ℝ≥0 := (min (spatialHitTime γ z r) T).untopD 0

end SLEExactGauge

end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

structure SpatialClippedFamily {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ) where
  Q : ℕ → ℝ → ℂ × Ω → ℂ × ℝ
  measurable : ∀ n, Measurable (fun p : ℝ × (ℂ × Ω) => Q n p.1 p.2)
  initial : ∀ n z ω, Q n 0 (z, ω) = initialLogCoordinates z
  derivative : ∀ n z ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q n s (z, ω))
    (clippedLogLoewnerField (-(n : ℝ)) n (by linarith [Nat.cast_nonneg (α := ℝ) n])
      (U t.toNNReal ω) (Q n t (z, ω))) (Ici 0) t

noncomputable def spatialClippedFamily
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ)
    (hUm : Measurable (fun p : ℝ≥0 × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω)) : SpatialClippedFamily U where
  Q n := (exists_spatial_clipped_flow U hUm hUc n).choose
  measurable n := (exists_spatial_clipped_flow U hUm hUc n).choose_spec.1
  initial n := (exists_spatial_clipped_flow U hUm hUc n).choose_spec.2.1
  derivative n := (exists_spatial_clipped_flow U hUm hUc n).choose_spec.2.2

namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

def valid (n : ℕ) (t : ℝ≥0) (z : ℂ) (ω : Ω) : Prop :=
  0 < z.im ∧ Real.log z.im ≤ (n : ℝ) ∧ -(n : ℝ) ≤ (c.Q n t (z, ω)).1.im

end SpatialClippedFamily
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

noncomputable def greenApprox (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (p : ℝ≥0 × (ℂ × Ω)) : ℝ := by
  classical
  exact if c.valid n p.1 p.2.1 p.2.2 then greenLogDensity κ (c.Q n p.1 p.2) (B p.1 p.2.2) else 0

noncomputable def jointGreen (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (p : ℝ≥0 × (ℂ × Ω)) : ℝ := limUnder atTop (fun n => c.greenApprox κ B n p)

end SpatialClippedFamily



end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

noncomputable def chartApprox (n : ℕ) (p : ℝ≥0 × (ℂ × Ω)) : ℂ := by
  classical
  exact if c.valid n p.1 p.2.1 p.2.2 then
    ((c.Q n p.1 p.2).1.re : ℂ) + (Real.exp (c.Q n p.1 p.2).1.im : ℂ) * Complex.I
  else 0

end SpatialClippedFamily
end SLEExactGauge
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_OccupationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Occupation Bound for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def inverseAngleBound (κ b η : ℝ) : ℝ :=
  Real.exp (codimension κ * η) *
    (angularMomentBound κ b η * (1 + lyapunovA κ b * η) / lyapunovC κ b) / η

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def inverseAngleSubcritical (κ : ℝ) : ℝ :=
  greenExponent κ - min (greenExponent κ / 2) 1
noncomputable def inverseAngleBuffer (u₀ : ℝ) : ℝ := min (u₀ / 2) 1
noncomputable def uniformInverseAngleConstant (κ u₀ : ℝ) : ℝ :=
  inverseAngleBound κ (inverseAngleSubcritical κ) (inverseAngleBuffer u₀)

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_IntervalDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interval Density for chordal SLE. -/

section

section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge

noncomputable def smoothingWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

lemma smoothingWidth_pos (n : ℕ) : 0 < smoothingWidth n := by
  unfold smoothingWidth
  positivity

lemma smoothingWidth_le (n : ℕ) : smoothingWidth n ≤ 1/2 := by
  unfold smoothingWidth
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
  norm_num

noncomputable def intervalBump (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    ContDiffBump (a+l/2) where
  rIn := (l/2) * (1-smoothingWidth n)
  rOut := (l/2) * (1-smoothingWidth n/2)
  rIn_pos := mul_pos (by linarith) (by have := smoothingWidth_le n; linarith)
  rIn_lt_rOut := by
    apply mul_lt_mul_of_pos_left _ (by linarith)
    have := smoothingWidth_pos n
    linarith

noncomputable def intervalDensity (a l : ℝ) (hl : 0 < l) (n : ℕ) : ℝ → ℝ :=
  (intervalBump a l hl n).normed volume


noncomputable def densityPrimitive (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in a..x, f t

noncomputable def intervalTransport (a l : ℝ) (hl : 0 < l) (a' : ℝ) (n : ℕ) : ℝ → ℝ :=
  densityPrimitive a (fun x => intervalDensity a' (l/2) (by linarith) n x -
    intervalDensity a l hl n x)

def complexTensor (f g : ℝ → ℝ) (z : ℂ) : ℝ := f z.re * g z.im

noncomputable def rectangleDensity (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (n : ℕ) : ℂ → ℝ :=
  complexTensor (intervalDensity a lx hx n) (intervalDensity b ly hy n)

noncomputable def rectangleTransportX (a _b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) : ℂ → ℝ :=
  complexTensor (intervalTransport a lx hx a' n)
    (intervalDensity b' (ly/2) (by linarith) n)

noncomputable def rectangleTransportY (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (_a' b' : ℝ) (n : ℕ) : ℂ → ℝ :=
  complexTensor (intervalDensity a lx hx n)
    (intervalTransport b ly hy b' n)

noncomputable def scaleLength (j : ℕ) : ℝ := 1/(2:ℝ)^j
noncomputable def scaleOrigin (t : ℝ) (j : ℕ) : ℝ := t * (1-scaleLength j)

lemma scaleLength_pos (j : ℕ) : 0 < scaleLength j := by
  unfold scaleLength; positivity

def openUnitStrip : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < Real.pi}

 

def SourceIsStripWeakGradient (u : ℂ → ℝ) (D : ℂ → ℂ) : Prop :=
  MemLp u 2 (volume.restrict openUnitStrip) ∧
  MemLp D 2 (volume.restrict openUnitStrip) ∧
  ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ openUnitStrip →
    (∫ z in openUnitStrip, u z * (fderiv ℝ φ z) (1:ℂ)) =
      -(∫ z in openUnitStrip, (D z).re * φ z) ∧
    (∫ z in openUnitStrip, u z * (fderiv ℝ φ z) Complex.I) =
      -(∫ z in openUnitStrip, (D z).im * φ z)

noncomputable def stripDirichletEnergy (D : ℂ → ℂ) : ℝ :=
  ∫ z in openUnitStrip, ‖D z‖^2

end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StripKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strip Kernels for chordal SLE. -/

section
section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge

noncomputable def chainDensity (t s : ℝ) (j n : ℕ) : ℂ → ℝ :=
  rectangleDensity (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j)) n
noncomputable def chainX (t s : ℝ) (j n : ℕ) : ℂ → ℝ :=
  rectangleTransportX (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1)) n
noncomputable def chainY (t s : ℝ) (j n : ℕ) : ℂ → ℝ :=
  rectangleTransportY (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1)) n
noncomputable def chainKernel (t s : ℝ) (j n : ℕ) (z : ℂ) : ℝ :=
  |chainX t s j n z|+|chainY t s j n z|

noncomputable def aggregateX (t s : ℝ) (k n : ℕ) (z : ℂ) : ℝ :=
  ∑ j ∈ Finset.range k, chainX t s j n z
noncomputable def aggregateY (t s : ℝ) (k n : ℕ) (z : ℂ) : ℝ :=
  ∑ j ∈ Finset.range k, chainY t s j n z

def stripRectangle (a b l : ℝ) : Set ℂ :=
  {w | a ≤ w.re ∧ w.re ≤ a+l ∧ b ≤ w.im ∧ w.im ≤ b+Real.pi*l}

noncomputable def spatialAverage (u : ℂ → ℝ) (Q : Set ℂ) : ℝ :=
  (∫ z in Q, u z) / (volume Q).toReal

def openStripRectangle (a b l : ℝ) : Set ℂ :=
  {z | a < z.re ∧ z.re < a+l ∧ b < z.im ∧ z.im < b+Real.pi*l}

def dyadicStripRectangle (j : ℤ) (k : ℕ) (i m : Fin (2^k)) : Set ℂ :=
  stripRectangle ((j:ℝ)+(i:ℝ)/(2:ℝ)^k)
    (Real.pi*((m:ℝ)/(2:ℝ)^k)) (1/(2:ℝ)^k)



end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SausagePointBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sausage Point Bound for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def spatialSmallnessConstant : ℝ := 128 * Real.pi * Real.exp 1 + 1
noncomputable def spatialOnePointConstant (κ : ℝ) : ℝ :=
  uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ

noncomputable def sausagePointConstant (κ : ℝ) : ℝ :=
  max (spatialOnePointConstant κ * (2 : ℝ) ^ (-codimension κ))
    (spatialSmallnessConstant ^ codimension κ)

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def boundaryApproachPower (κ : ℝ) : ℝ := 3*(8-κ)/(4*κ)
noncomputable def annularApproachPower (κ : ℝ) : ℝ :=
  min (boundaryApproachPower κ/2) (codimension κ/2)
noncomputable def annularApproachConstant (κ : ℝ) : ℝ :=
  (8/((8-κ)/32))^boundaryApproachPower κ + sausagePointConstant κ

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def stripHittingConstant (κ : ℝ) : ℝ :=
  (annularApproachConstant κ+1) * (64*(1+Real.pi))^annularApproachPower κ

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SpatialMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial Means for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)
noncomputable def jointChart (p : ℝ≥0 × (ℂ × Ω)) : ℂ :=
  limUnder atTop (fun n => c.chartApprox n p)

end SpatialClippedFamily
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma spatialHitTime_mem {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (t : ℝ≥0) (ht : spatialHitTime γ z r = t) :
    dist (γ t) z = r := by
  obtain ⟨s, hs, he⟩ := (spatialHitTime_le_iff hc z r t).mp ht.le
  have hle := (spatialHitTime_le_iff hc z r s).mpr ⟨s, ⟨bot_le, le_rfl⟩, he⟩
  rw [ht] at hle
  have hst : s = t := le_antisymm hs.2 (WithTop.coe_le_coe.mp hle)
  exact hst ▸ he

 

noncomputable def liveSpatialHitTime (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) : WithTop ℝ≥0 :=
  if ({t : ℝ≥0 | z ∈ survivingDomain γ t ∧ dist (γ t) z ≤ r}).Nonempty then
    ↑(sInf {t : ℝ≥0 | z ∈ survivingDomain γ t ∧ dist (γ t) z ≤ r}) else ⊤

lemma spatialHitTime_le_of_dist_le {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z)
    (t : ℝ≥0) (ht : dist (γ t) z ≤ r) : spatialHitTime γ z r ≤ t := by
  obtain ⟨s, hst, he⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ t from bot_le)
    (hc.dist continuous_const).continuousOn ⟨ht, hs⟩
  exact (spatialHitTime_le_iff hc z r t).mpr ⟨s, hst, he⟩

lemma liveSpatialHitTime_eq {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z) :
    liveSpatialHitTime γ z r =
      if spatialHitTime γ z r = ⊤ then ⊤ else
        if z ∈ survivingDomain γ ((spatialHitTime γ z r).untopD 0) then
          spatialHitTime γ z r else ⊤ := by
  let V := {t : ℝ≥0 | z ∈ survivingDomain γ t ∧ dist (γ t) z ≤ r}
  by_cases hv : V.Nonempty
  · obtain ⟨t, ht⟩ := hv
    have hhit := spatialHitTime_le_of_dist_le hc z r hs t ht.2
    have hn : spatialHitTime γ z r ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hhit
    obtain ⟨v, he⟩ := WithTop.ne_top_iff_exists.mp hn
    have hvle : v ≤ t := WithTop.coe_le_coe.mp (he ▸ hhit)
    have hvl : z ∈ survivingDomain γ v := survivingDomain_antitone γ hvle ht.1
    have hvm : v ∈ V := ⟨hvl, (spatialHitTime_mem hc z r v he.symm).le⟩
    have hmin : sInf V = v := by
      apply le_antisymm (csInf_le ⟨0, fun _ _ => bot_le⟩ hvm)
      apply le_csInf ⟨v, hvm⟩
      intro s hs'
      exact WithTop.coe_le_coe.mp (he ▸ spatialHitTime_le_of_dist_le hc z r hs s hs'.2)
    change (if V.Nonempty then ((sInf V : ℝ≥0) : WithTop ℝ≥0) else ⊤) = _
    rw [ite_eq_left ⟨v, hvm⟩, hmin, ite_eq_right hn, ← he, WithTop.untopD_coe, ite_eq_left hvl]
  · change (if V.Nonempty then ((sInf V : ℝ≥0) : WithTop ℝ≥0) else ⊤) = _
    rw [ite_eq_right hv]
    by_cases hn : spatialHitTime γ z r = ⊤
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn]
      obtain ⟨v, he⟩ := WithTop.ne_top_iff_exists.mp hn
      rw [← he, WithTop.untopD_coe]
      have hnl : z ∉ survivingDomain γ v := fun h =>
        hv ⟨v, h, (spatialHitTime_mem hc z r v he.symm).le⟩
      rw [ite_eq_right hnl]



end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def spatialSlabCoefficient (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (r ε : ℝ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  if spatialHitTime γ z r ≤ t ∧ (t : WithTop ℝ≥0) ≤ spatialHitTime γ z ε ∧
      z ∈ survivingDomain γ t then greenBrownianCoefficient κ U γ G t z else 0

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

noncomputable def spatialRealMass (κ : ℝ) (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (r : ℝ) (A : Set ℂ) : ℝ :=
  ∫ z in A, spatialGreenWeight κ U γ G z r

end SLEExactGauge

end

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal

open Set Filter Metric Complex
open scoped Topology NNReal

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance sourceApproachComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _

noncomputable def sourceApproachKernel (ε r : ℝ) (p : ℂ × C(ℝ≥0, ℂ)) : ℝ :=
  if ∃ t : ℝ≥0, dist (p.2 t) p.1 < 8 * p.1.im * ε / r then 1 else 0

end
end SLEExactGauge

end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_MeasureSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measure Support for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {ε : ℕ → ℝ}

noncomputable def radiusInverseAngle
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (s : ℝ≥0) (ω : Ω) : ℝ :=
  (limitRadiusKernel (a s) 0 2 s ω) ^ (-greenExponent κ / 2)

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_FiniteMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Mass for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {ε : ℕ → ℝ}

noncomputable def initialAngleWindowConstant (κ : ℝ) (z : ℂ) : ℝ :=
  Real.exp (codimension κ * (1 - Real.log 2 - Real.log z.im)) / initialGreen κ z

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def angleEnvelopeConstant (κ : ℝ) (z : ℂ) : ℝ :=
  max (initialAngleWindowConstant κ z) (uniformInverseAngleConstant κ 1 * Real.exp (codimension κ))

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ} (a : AngularLocalization B hm κ z u ε)

noncomputable def radiusPhysicalRate (s : ℝ) (ω : Ω) : ℝ :=
  Real.exp (2 * (a.solution.Q (a.clock.inverse s ω) ω).1.im) /
    (4 * logAngleSq κ (a.solution.Q (a.clock.inverse s ω) ω)
      (B (a.clock.inverse s ω).toNNReal ω) ^ 2)

end AngularLocalization
end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def physicalTimeThreshold (κ : ℝ) (z : ℂ) (M : ℝ) : ℝ :=
  Real.exp (2 * Real.log z.im) / 2 * M ^ (4 / greenExponent κ)

end SLEExactGauge
end


open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def finiteSpatialGreenMass (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (r : ℝ) (T : ℝ≥0) (K : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ z in K, ENNReal.ofReal (if spatialHitTime γ z r ≤ T then
    spatialGreenWeight κ U γ G z r else 0)

noncomputable def halfClockThreshold (κ : ℝ) (z : ℂ) : ℝ :=
  physicalTimeThreshold κ z
    (angleEnvelopeConstant κ z / ((1 / 2) * (1 - Real.exp (-greenExponent κ / 8))))

end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window Assembly for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

def windowBefore {Ω ι : Type*} [LinearOrder ι]
    (σ : ι → Ω → WithTop ℝ≥0) (i j : ι) (ω : Ω) : Prop :=
  σ i ω < σ j ω ∨ σ i ω = σ j ω ∧ i < j



structure SourceDisjointWindows {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (D : Set ℂ) (r R K : ℝ) (γ : ℝ≥0 → Ω → ℂ)
    (σ τ : ℂ → Ω → WithTop ℝ≥0) (Y μ : ℂ → Ω → ℝ) : Prop where
  measurable_D : MeasurableSet D
  bounded_D : D ⊆ ball 0 1
  radius_pos : 0 < r
  radius_le : r ≤ R
  radius_small : 3 * R ≤ 1
  bound_nonneg : 0 ≤ K
  continuous_trace : ∀ ω, Continuous (fun t => γ t ω)
  adapted_trace : ∀ t, Measurable[ℱ t] (γ t)
  start : ∀ z, IsStoppingTime ℱ (σ z)
  finish : ∀ z, IsStoppingTime ℱ (τ z)
  time_le : ∀ z ω, σ z ω ≤ τ z ω
  contact : ∀ z ω, σ z ω ≠ ⊤ → dist (γ ((σ z ω).untopD 0) ω) z = r
  confined : ∀ z ω (t : ℝ≥0), σ z ω ≤ (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) < τ z ω →
    dist (γ t ω) z < R
  output_measurable : ∀ z, Measurable[(finish z).measurableSpace] (Y z)
  mean_measurable : ∀ z, Measurable[(start z).measurableSpace] (μ z)
  output_bound : ∀ z ω, 0 ≤ Y z ω ∧ Y z ω ≤ K
  mean_nonneg : ∀ z ω, 0 ≤ μ z ω
  mean_bounded : ∃ M : ℝ, ∀ z ω, μ z ω ≤ M
  upper_mean : ∀ z, ∀ᵐ ω ∂P, σ z ω ≠ ⊤ → P[Y z | (start z).measurableSpace] ω ≤ μ z ω
  no_start : ∀ z ω, σ z ω = ⊤ → Y z ω = 0 ∧ μ z ω = 0
  no_end : ∀ z ω, τ z ω = ⊤ → Y z ω = 0
  outside : ∀ z, z ∉ D → ∀ ω, σ z ω = ⊤ ∧ Y z ω = 0 ∧ μ z ω = 0
  joint_output : Measurable (fun p : ℂ × Ω => Y p.1 p.2)
  joint_mean : Measurable (fun p : ℂ × Ω => μ p.1 p.2)

noncomputable def windowSquare (a b : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))

instance windowSquare_finite (a b : ℝ) : IsFiniteMeasure (windowSquare a b) := by
  dsimp [windowSquare]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def windowShiftLaw (a : ℝ) : Measure (ℝ × ℝ) :=
  (ENNReal.ofReal (a^2))⁻¹ • windowSquare 0 a

noncomputable def windowCenter (a : ℝ) (ξ : ℝ × ℝ) {n : ℕ} (i : Fin n × Fin n) : ℂ :=
  Complex.measurableEquivRealProd.symm (ξ.1+a*i.1-2, ξ.2+a*i.2-2)

end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StoppedMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopped Measures for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal

section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

local instance sourceRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance sourceComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _

def sourceDriverPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) : C(ℝ≥0, ℝ) :=
  ⟨fun t => B t ω, hc ω⟩

def sourceTracePath {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (hc : ∀ ω, Continuous (γ ω)) (ω : Ω) : C(ℝ≥0, ℂ) := ⟨γ ω, hc ω⟩

noncomputable def sourceRestartDriverPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ : Ω → ℝ≥0) (ω : Ω) : C(ℝ≥0, ℝ) :=
  ⟨fun t => brownianRestart B τ t ω,
    ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const⟩

universe u_source_stopped

 

local instance sourceRealPathBorel_r9e5dc0_1 : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance sourceComplexPathBorel_r9e5dc0_1 : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
def SourceStoppedTraceLawTarget : Prop :=
  ∀ {Ω : Type u_source_stopped} [_m : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ), 0 < κ → κ < 8 →
  ∀ (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)),
  ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), Measurable Φ ∧
    (∀ ω, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
    ∀ (τ : Ω → ℝ≥0)
      (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0))),
      (∀ (A : Set Ω), MeasurableSet[hτ.measurableSpace] A →
        (P.restrict A).map (fun ω => Φ (sourceRestartDriverPath B hc τ ω)) =
          P A • P.map (sourceTracePath γ (fun ω => (hw ω).1))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Φ (sourceRestartDriverPath B hc τ ω) t ∈ upperHalfPlane →
        γ ω (τ ω + t) = F ω (τ ω)
          (Φ (sourceRestartDriverPath B hc τ ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ)))

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_path_evaluation_embedding {E : Type*} [TopologicalSpace E]
    [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)] [PolishSpace C(ℝ≥0, E)] :
    MeasurableEmbedding (fun f : C(ℝ≥0, E) => fun n => f (denseSeq ℝ≥0 n)) := by
  apply Continuous.measurableEmbedding
  · exact continuous_pi fun n => continuous_eval_const _
  · intro f g h
    apply DFunLike.coe_injective
    exact (denseRange_denseSeq ℝ≥0).equalizer f.continuous g.continuous h

lemma source_path_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)] [PolishSpace C(ℝ≥0, E)]
    (f : Ω → C(ℝ≥0, E)) (hf : ∀ t, Measurable (fun ω => f ω t)) : Measurable f := by
  apply source_path_evaluation_embedding.measurable_comp_iff.mp
  exact Measurable.of_eval (fun _ => hf _)

local instance stoppedTraceFactorRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance stoppedTraceFactorComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
end
end SLEExactGauge

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance stoppedReverseFlowRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance stoppedRestartLawRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance stoppedTraceLawRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance stoppedTraceLawComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance stoppedForwardLawRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance stoppedForwardLawComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _

universe u_source_stopped

end
end SLEExactGauge

end

section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

 

theorem source_killedChart_progressive
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (z : ℂ) :
    IsStronglyProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => if z ∈ survivingDomain (γ ω) t then G ω t z else 0) := by
  classical
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  have hnn (n : ℕ) : -(n : ℝ) ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) n]
  let c (n : ℕ) := (exists_clippedLogSolution B hm hBm hc κ (-(n : ℝ)) n (hnn n)
    (initialLogCoordinates z)).some
  let v (n : ℕ) (t : ℝ≥0) (ω : Ω) : Prop :=
    0 < z.im ∧ Real.log z.im ≤ (n : ℝ) ∧ -(n : ℝ) ≤ ((c n).Q t ω).1.im
  let A (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℂ :=
    if v n t ω then
      (((c n).Q t ω).1.re : ℂ) + (Real.exp ((c n).Q t ω).1.im : ℂ) * I
    else 0
  have hQp (n : ℕ) : IsStronglyProgressive f (fun t : ℝ≥0 => (c n).Q t) :=
    (show StronglyAdapted f (fun t : ℝ≥0 => (c n).Q t) from
      fun t => ((c n).adapted t).stronglyMeasurable).isStronglyProgressive_of_continuous
      (fun ω => ((c n).lipschitz ω).continuous.comp NNReal.continuous_coe)
  have hAp (n : ℕ) : IsStronglyProgressive f (A n) := by
    intro T
    have hQ := (hQp n T).measurable
    let : MeasurableSpace Ω := f T
    have hv : MeasurableSet {p : Iic T × Ω | v n p.1 p.2} :=
      (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
        (measurableSet_le measurable_const (Complex.measurable_im.comp hQ.fst)))
    exact (Measurable.ite hv
      ((Complex.measurable_ofReal.comp (Complex.measurable_re.comp hQ.fst)).add
        ((Complex.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
          (Complex.measurable_im.comp hQ.fst))).mul_const I)) measurable_const).stronglyMeasurable
  have hlim (t : ℝ≥0) (ω : Ω) : Tendsto (fun n => A n t ω) atTop
      (𝓝 (if z ∈ survivingDomain (γ ω) t then G ω t z else 0)) := by
    apply tendsto_nhds_of_eventually_eq
    have hU : Continuous (fun s => Real.sqrt κ * B s ω) := (hc ω).const_mul _
    have hd (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :=
      ((c n).derivative ω s hs.1).mono (show Icc (0 : ℝ) (t : ℝ) ⊆ Ici 0 from Icc_subset_Ici_self)
    by_cases hz : z ∈ survivingDomain (γ ω) t
    · obtain ⟨N, hN⟩ := exists_nat_ge (max (-Real.log (G ω t z).im) (Real.log z.im))
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hlo : -(n : ℝ) ≤ Real.log (G ω t z).im := by
        have hh := (le_max_left (-Real.log (G ω t z).im) (Real.log z.im)).trans (hN.trans hNn)
        linarith
      have hhi : Real.log z.im ≤ (n : ℝ) := (le_max_right _ _).trans (hN.trans hNn)
      have he : (c n).Q t ω = logLoewnerCoordinates (G ω) z t :=
        clipped_log_loewner_agrees hU (hw ω) t z hz _ _ _ hlo hhi
          (fun s => (c n).Q s ω) ((c n).initial ω) (hd n) ⟨t.coe_nonneg, le_rfl⟩
      have hv : v n t ω := ⟨hz.1.1, hhi, by simpa only [he, logCoordinates_im] using hlo⟩
      simp only [A, ite_eq_left hz, ite_eq_left hv, he, logCoordinates_re, logCoordinates_im,
        Real.exp_log ((hw ω).imag_positive t z hz)]
      exact Complex.re_add_im _
    · filter_upwards [] with n
      have hv : ¬ v n t ω := by
        intro hv
        exact hz (clipped_log_identification_of_endpoint hU (hw ω) t z hv.1 _ _ _
          (fun s => (c n).Q s ω) ((c n).initial ω) (hd n) hv.2.2 hv.2.1).1
      simp only [A, ite_eq_right hv, ite_eq_right hz]
  exact isStronglyProgressive_of_tendsto hAp
    (tendsto_pi_nhds.mpr (fun t => tendsto_pi_nhds.mpr (hlim t)))

end
end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ChartMeasurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chart Measurability for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal

section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal
namespace SLEExactGauge
noncomputable section
local instance instMeasurableSpaceContinuousMapElemComplexUpperHalfPlane : MeasurableSpace C(upperHalfPlane,ℂ) := borel _

local instance instBorelSpaceContinuousMapElemComplexUpperHalfPlane_r9e5dc0_1 : BorelSpace C(upperHalfPlane,ℂ) := ⟨rfl⟩
def sourceStoppedInversePath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0) (ω : Ω) : C(upperHalfPlane,ℂ) :=
  ⟨fun z => F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ)),
    ContinuousOn.comp_continuous ((hw ω).2.2.2.2.1 _).continuousOn
      (continuous_subtype_val.add continuous_const)
      (fun z => by simpa [upperHalfPlane] using z.2)⟩

end
end SLEExactGauge

end

section
open Set Filter MeasureTheory Metric Bornology
open scoped Topology NNReal
namespace SLEExactGauge
 

def square (R : ℝ) : Set ℂ := {z | |z.re| ≤ R ∧ |z.im| ≤ R}

def upperExterior (R : ℝ) : Set ℂ := upperHalfPlane ∩ (square R)ᶜ

lemma square_isCompact (R : ℝ) : IsCompact (square R) := by
  have hc : IsClosed (square R) :=
    (isClosed_le Complex.continuous_re.abs continuous_const).inter
      (isClosed_le Complex.continuous_im.abs continuous_const)
  apply isCompact_of_isClosed_isBounded hc
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2*R,fun z hz => ?_⟩
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith [hz.1,hz.2])

lemma upperExterior_eq (R : ℝ) (hR : 0 ≤ R) : upperExterior R =
    ({z : ℂ | z.re < -R} ∩ {z | 0 < z.im}) ∪ {z | R < z.im} ∪
    ({z : ℂ | R < z.re} ∩ {z | 0 < z.im}) := by
  ext z
  simp only [upperExterior,upperHalfPlane,square,mem_inter_iff,mem_ofPred_eq,
    mem_compl_iff,mem_union,abs_le]
  constructor
  · rintro ⟨hi,hs⟩
    by_cases hl : z.re < -R
    · exact Or.inl (Or.inl ⟨hl,hi⟩)
    by_cases hr : R < z.re
    · exact Or.inr ⟨hr,hi⟩
    exact Or.inl (Or.inr (by by_contra hn; exact hs ⟨⟨by linarith,by linarith⟩,
      ⟨by linarith,by linarith⟩⟩))
  · rintro ((⟨hl,hi⟩ | hi) | ⟨hr,hi⟩)
    · exact ⟨hi,fun hs => (not_lt_of_ge hs.1.1) hl⟩
    · exact ⟨by linarith,fun hs => (not_lt_of_ge hs.2.2) hi⟩
    · exact ⟨hi,fun hs => (not_lt_of_ge hs.1.2) hr⟩

lemma upperExterior_preconnected (R : ℝ) (hR : 0 ≤ R) : IsPreconnected (upperExterior R) := by
  rw [upperExterior_eq R hR]
  have hL := ((convex_halfSpace_re_lt (-R)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hU := (convex_halfSpace_im_gt R).isPreconnected
  have hV := ((convex_halfSpace_re_gt R).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hLU : (({z : ℂ | z.re < -R} ∩ {z | 0 < z.im}) ∩ {z | R < z.im}).Nonempty := by
    refine ⟨⟨-R-1,R+1⟩,?_,?_⟩ <;> simp only [mem_inter_iff,mem_ofPred_eq] <;> (try constructor) <;> linarith
  have hUV : ((({z : ℂ | z.re < -R} ∩ {z | 0 < z.im}) ∪ {z | R < z.im}) ∩
      ({z : ℂ | R < z.re} ∩ {z | 0 < z.im})).Nonempty := by
    refine ⟨⟨R+1,R+1⟩,Or.inr ?_,?_,?_⟩ <;> simp only [mem_ofPred_eq] <;> linarith
  exact (hL.union' hLU hU).union' hUV hV

lemma upperExterior_unbounded (R : ℝ) (hR : 0 ≤ R) : ¬ Bornology.IsBounded (upperExterior R) := by
  intro hb
  obtain ⟨C,hC⟩ := hb.exists_norm_le
  let y : ℝ := max C R + 1
  have hyR : R < y := by dsimp [y]; linarith [le_max_right C R]
  have hyC : C < y := by dsimp [y]; linarith [le_max_left C R]
  have hy0 : 0 < y := by linarith
  have hm : (⟨0,y⟩ : ℂ) ∈ upperExterior R := by
    exact ⟨hy0,fun h => (not_le_of_gt hyR) ((le_abs_self y).trans h.2)⟩
  have hb' := hC _ hm
  have hn := Complex.abs_im_le_norm (⟨0,y⟩ : ℂ)
  change |y| ≤ ‖(⟨0,y⟩ : ℂ)‖ at hn
  rw [abs_of_pos hy0] at hn
  linarith

lemma upperExterior_subset_survivingDomain {γ : ℝ≥0 → ℂ} {T : ℝ≥0} {R : ℝ}
    (hR : 0 ≤ R) (hγ : γ '' Icc 0 T ⊆ square R) :
    upperExterior R ⊆ survivingDomain γ T := by
  intro z hz
  have hs : upperExterior R ⊆ upperHalfPlane \ (γ '' Icc 0 T) := by
    intro w hw
    exact ⟨hw.1,fun ht => hw.2 (hγ ht)⟩
  refine ⟨hs hz,?_⟩
  intro hb
  exact upperExterior_unbounded R hR (hb.subset
    ((upperExterior_preconnected R hR).subset_connectedComponentIn hz hs))

end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma source_live_compact_bridge (γ : C(ℝ≥0,ℂ)) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) :
    ∃ (R δ : ℝ) (K : Set ℂ), 0 < R ∧ 0 < δ ∧ IsCompact K ∧
      IsPreconnected K ∧ Metric.closedBall z δ ⊆ K ∧
      (⟨0,R+1⟩ : ℂ) ∈ K ∧ K ⊆ upperHalfPlane ∧
      MapsTo γ (Icc 0 t) (Metric.ball 0 R \ K) := by
  obtain ⟨M,hM⟩ := (isCompact_Icc.image γ.continuous).isBounded.exists_norm_le
  let R := max M 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right M 0]
  have hnorm (s : ℝ≥0) (hs : s ∈ Icc 0 t) : ‖γ s‖ < R := by
    have hh := hM _ ⟨s,hs,rfl⟩
    dsimp [R]; linarith [le_max_left M 0]
  have htr : γ '' Icc 0 t ⊆ square R := by
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨(abs_re_le_norm _).trans (hnorm s hs).le,(abs_im_le_norm _).trans (hnorm s hs).le⟩
  let A : Set ℂ := upperHalfPlane \ γ '' Icc 0 t
  let C := connectedComponentIn A z
  have hA : IsOpen A := isOpen_upperHalfPlane.sdiff (isCompact_Icc.image γ.continuous).isClosed
  have hzC : z ∈ C := mem_connectedComponentIn hz.1
  have hCsub : C ⊆ A := connectedComponentIn_subset _ _
  have hnot : ¬ C ⊆ square R := fun hh => hz.2 ((square_isCompact R).isBounded.subset hh)
  obtain ⟨v,hv,hvR⟩ := Set.not_subset.mp hnot
  have hvE : v ∈ upperExterior R := ⟨(hCsub hv).1,hvR⟩
  have hEsub : upperExterior R ⊆ A := by
    intro w hw
    exact ⟨hw.1,fun ht => hw.2 (htr ht)⟩
  have hEC : upperExterior R ⊆ C := by
    have hc := (upperExterior_preconnected R hR.le).subset_connectedComponentIn hvE hEsub
    rwa [← connectedComponentIn_eq hv] at hc
  let p : ℂ := ⟨0,R+1⟩
  have hpE : p ∈ upperExterior R := by
    refine ⟨by change 0 < R+1; linarith,?_⟩
    intro hh
    have hhi : |R+1| ≤ R := hh.2
    linarith [le_abs_self (R+1)]
  have hpathc : IsPathConnected C := (hA.connectedComponentIn).isConnected_iff_isPathConnected.mp
    ⟨⟨z,hzC⟩,isPreconnected_connectedComponentIn⟩
  let η := (hpathc.joinedIn z hzC p (hEC hpE)).somePath
  have hη : range η ⊆ A := by
    rintro _ ⟨s,rfl⟩
    exact hCsub ((hpathc.joinedIn z hzC p (hEC hpE)).somePath_mem s)
  obtain ⟨ε,hε,hεsub⟩ := Metric.isOpen_iff.mp hA z hz.1
  let δ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hball : Metric.closedBall z δ ⊆ A := by
    apply subset_trans _ hεsub
    exact Metric.closedBall_subset_ball (by dsimp [δ]; linarith)
  let K := range η ∪ Metric.closedBall z δ
  have hKc : IsCompact K := (isCompact_range η.continuous).union (isCompact_closedBall z δ)
  have hKconn : IsPreconnected K :=
    (isConnected_range η.continuous).2.union z η.source_mem_range (Metric.mem_closedBall_self hδ.le)
      (convex_closedBall z δ).isPreconnected
  have hKsub : K ⊆ A := union_subset hη hball
  refine ⟨R,δ,K,hR,hδ,hKc,hKconn,subset_union_right,
    Or.inl η.target_mem_range,fun w hw => (hKsub hw).1,?_⟩
  intro s hs
  refine ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hnorm s hs,?_⟩
  intro hh
  exact (hKsub hh).2 ⟨s,hs,rfl⟩

 

lemma source_live_of_bridge {γ : ℝ≥0 → ℂ} {t : ℝ≥0} {z : ℂ} {R : ℝ} {K : Set ℂ}
    (hR : 0 ≤ R) (hK : IsPreconnected K) (hz : z ∈ K)
    (hp : (⟨0,R+1⟩ : ℂ) ∈ K) (hKH : K ⊆ upperHalfPlane)
    (hγ : MapsTo γ (Icc 0 t) (Metric.ball 0 R \ K)) :
    z ∈ survivingDomain γ t := by
  have hnorm (s : ℝ≥0) (hs : s ∈ Icc 0 t) : ‖γ s‖ < R := by
    simpa only [Metric.mem_ball,dist_zero_right] using (hγ hs).1
  have htr : γ '' Icc 0 t ⊆ square R := by
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨(abs_re_le_norm _).trans (hnorm s hs).le,(abs_im_le_norm _).trans (hnorm s hs).le⟩
  have hpE : (⟨0,R+1⟩ : ℂ) ∈ upperExterior R := by
    refine ⟨by change 0 < R+1; linarith,?_⟩
    intro hh
    have hhi : |R+1| ≤ R := hh.2
    linarith [le_abs_self (R+1)]
  have hpS := upperExterior_subset_survivingDomain hR htr hpE
  have hKa : K ⊆ upperHalfPlane \ γ '' Icc 0 t := by
    intro w hw
    refine ⟨hKH hw,?_⟩
    rintro ⟨s,hs,rfl⟩
    exact (hγ hs).2 hw
  have hpC := hK.subset_connectedComponentIn hz hKa hp
  refine ⟨hKa hz,?_⟩
  rw [connectedComponentIn_eq hpC]
  exact hpS.2

noncomputable def sourceRescaledPath (p : C(ℝ≥0,ℂ) × ℝ≥0) : C(ℝ≥0,ℂ) :=
  ⟨fun s => p.1 (p.2*s),p.1.continuous.comp (continuous_const.mul continuous_id)⟩

lemma sourceRescaledPath_continuous : Continuous sourceRescaledPath := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp
    ((continuous_fst.fst).prodMk ((continuous_fst.snd).mul continuous_snd))

lemma sourceRescaledPath_mapsTo {p : C(ℝ≥0,ℂ) × ℝ≥0} {A : Set ℂ} :
    MapsTo (sourceRescaledPath p) (Icc 0 1) A ↔ MapsTo p.1 (Icc 0 p.2) A := by
  have he : (fun s : ℝ≥0 => p.2*s) '' Icc 0 1 = Icc 0 p.2 := by
    simpa using image_mul_left_Icc (show 0 ≤ p.2 from bot_le) (show (0 : ℝ≥0) ≤ 1 by norm_num)
  rw [← he]
  constructor
  · intro h v hv
    rcases hv with ⟨s,hs,rfl⟩
    exact h hs
  · intro h s hs
    exact h ⟨s,hs,rfl⟩

lemma source_survival_open :
    IsOpen {p : (C(ℝ≥0,ℂ) × ℝ≥0) × ℂ | p.2 ∈ survivingDomain p.1.1 p.1.2} := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro ⟨⟨γ,t⟩,z⟩ hz
  obtain ⟨R,δ,K,hR,hδ,hKc,hKconn,hball,hp,hKH,hγ⟩ := source_live_compact_bridge γ t z hz
  let W : Set (C(ℝ≥0,ℂ) × ℝ≥0) := {p | MapsTo p.1 (Icc 0 p.2) (Metric.ball 0 R \ K)}
  have hWo : IsOpen W := by
    have hh := (ContinuousMap.isOpen_setOfPred_mapsTo (K := Icc (0 : ℝ≥0) 1) (U := Metric.ball (0 : ℂ) R \ K) isCompact_Icc
      (Metric.isOpen_ball.sdiff hKc.isClosed)).preimage sourceRescaledPath_continuous
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    exact sourceRescaledPath_mapsTo.symm
  refine ⟨W ×ˢ Metric.ball z δ,?_,hWo.prod Metric.isOpen_ball,⟨hγ,Metric.mem_ball_self hδ⟩⟩
  rintro ⟨⟨β,s⟩,w⟩ ⟨hβ,hw⟩
  exact source_live_of_bridge hR.le hKconn (hball (Metric.ball_subset_closedBall hw)) hp hKH hβ

end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge
abbrev SourceDiskParameter := (C(upperHalfPlane,ℂ) × ℂ) × (ℂ × ℝ)

end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex TopologicalSpace
open scoped Topology NNReal
namespace SLEExactGauge
noncomputable section
local instance instMeasurableSpaceContinuousMapNNRealComplex_solutions : MeasurableSpace C(ℝ≥0,ℂ) := borel _

def SourcePathInteriorDense (β : C(ℝ≥0,ℂ)) : Prop :=
  ∀ s t : ℝ≥0, s < t → ∃ u ∈ Ioo s t, 0 < (β u).im

end
end SLEExactGauge

end

end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RectangleMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangle Means for chordal SLE. -/

section
section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge
noncomputable def cellOrigin (k : ℕ) (i : Fin (2^k)) : ℝ := (i:ℝ)*scaleLength k
noncomputable def dyadicCell (k : ℕ) (p : Fin (2^k) × Fin (2^k)) : Set ℂ :=
  stripRectangle (cellOrigin k p.1) (Real.pi*cellOrigin k p.2) (scaleLength k)
noncomputable def dyadicInterior (k : ℕ) (p : Fin (2^k) × Fin (2^k)) : Set ℂ :=
  openStripRectangle (cellOrigin k p.1) (Real.pi*cellOrigin k p.2) (scaleLength k)

def leftChild (k : ℕ) (i : Fin (2^k)) : Fin (2^(k+1)) :=
  ⟨2*i.val, by have := i.isLt; rw [pow_succ]; omega⟩
def rightChild (k : ℕ) (i : Fin (2^k)) : Fin (2^(k+1)) :=
  ⟨2*i.val+1, by have := i.isLt; rw [pow_succ]; omega⟩

noncomputable def branchIndex (x : ℝ) : (k : ℕ) → Fin (2^k)
  | 0 => 0
  | k+1 => if x ≤ cellOrigin k (branchIndex x k)+scaleLength k/2 then
      leftChild k (branchIndex x k) else rightChild k (branchIndex x k)

noncomputable def pointBranch (z : ℂ) (k : ℕ) : Fin (2^k) × Fin (2^k) :=
  (branchIndex z.re k, branchIndex (z.im/Real.pi) k)

noncomputable def cellEnergy (D : ℂ → ℂ) (k : ℕ) (p : Fin (2^k) × Fin (2^k)) : ℝ :=
  ∫ z in dyadicInterior k p, ‖D z‖^2

noncomputable def exceptionalParents (D : ℂ → ℂ) (H : ℝ) (N j : ℕ) :
    Finset (Fin (2^(N+j)) × Fin (2^(N+j))) := by
  classical
  exact Finset.univ.filter (fun p => H^2/(9216*((j:ℝ)+2)^4) ≤ cellEnergy D (N+j) p)

noncomputable def polyGeometricSum (q : ℝ) : ℝ := ∑' j : ℕ, ((j:ℝ)+2)^4*q^j

noncomputable def energyDepth (H E : ℝ) : ℕ := ⌊H^2/(25600*E)⌋₊

universe u

 

def SourceStripRectangleEnergyTarget : Prop :=
  ∀ C0 α : ℝ, 0 < C0 → 0 < α →
    ∃ C c c0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < c0 ∧
      ∀ (H : ℝ), 0 < H → ∀ (u : ℂ → ℝ) (D : ℂ → ℂ),
      SourceIsStripWeakGradient u D → ContinuousOn u (stripRectangle 0 0 1) →
      (∀ z ∈ stripRectangle 0 0 1, 0 ≤ u z ∧ u z ≤ H) →
      spatialAverage u (stripRectangle 0 0 1) ≤ H/2 →
      ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P → ∀ X : Ω → Set ℂ,
      (∀ (k : ℕ) (i m : Fin (2^k)),
        P {ξ | (X ξ ∩ dyadicStripRectangle 0 k i m).Nonempty} ≤
          ENNReal.ofReal (C0 * (2:ℝ)^(-α*(k:ℝ)))) →
      stripDirichletEnergy D ≤ c0*H^2 →
      P {ξ | (X ξ ∩ {z | z ∈ stripRectangle 0 0 1 ∧ u z = H}).Nonempty} ≤
        ENNReal.ofReal (C * (stripDirichletEnergy D/H^2) *
          Real.exp (-c*H^2/stripDirichletEnergy D))



end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_DyadicStrips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic Strips for chordal SLE. -/

section

section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge

 
def IsStripWeakGradient (u : ℂ → ℝ) (D : ℂ → ℂ) : Prop :=
  MemLp u 2 (volume.restrict openUnitStrip) ∧
  MemLp D 2 (volume.restrict openUnitStrip) ∧
  ∀ φ : ℂ → ℝ, ContDiff ℝ ⊤ φ → HasCompactSupport φ → tsupport φ ⊆ openUnitStrip →
    (∫ z in openUnitStrip, u z * (fderiv ℝ φ z) (1:ℂ)) =
      -(∫ z in openUnitStrip, (D z).re * φ z) ∧
    (∫ z in openUnitStrip, u z * (fderiv ℝ φ z) Complex.I) =
      -(∫ z in openUnitStrip, (D z).im * φ z)

noncomputable def annulusKernel (q : ℂ) (r R : ℝ) (w : ℂ) : ℝ≥0∞ :=
  if r < ‖w-q‖ ∧ ‖w-q‖ < R then ENNReal.ofReal (‖w-q‖^2)⁻¹ else 0

noncomputable def truncatedConformalLog (F : ℂ → ℂ) (q : ℂ) (r H : ℝ) (z : ℂ) : ℝ :=
  min H (max 0 (Real.log (‖F z-q‖/r)))

noncomputable def conformalStripLog (F : ℂ → ℂ) (q : ℂ) (r H : ℝ) (z : ℂ) : ℝ :=
  min H (max 0 (Real.log (‖F (Complex.exp z)-q‖/r)))


noncomputable def sphericalTruncatedLog (q : ℂ) (r H : ℝ) : OnePoint ℂ → ℝ :=
  OnePoint.rec H (fun z => min H (max 0 (Real.log (‖z-q‖/r))))

@[simp] lemma sphericalTruncatedLog_coe (q z : ℂ) (r H : ℝ) :
    sphericalTruncatedLog q r H (z : OnePoint ℂ) =
      truncatedConformalLog id q r H z := rfl

@[simp] lemma sphericalTruncatedLog_infty (q : ℂ) (r H : ℝ) :
    sphericalTruncatedLog q r H OnePoint.infty = H := rfl



end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_NestedMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested Means for chordal SLE. -/

section
section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge
universe u

def complexCoordinates (p : ℝ × ℝ) : ℂ := p.1 + p.2*Complex.I

def cartesianRectangle (a b c d : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

def fullOpenStrip : Set ℂ := {z : ℂ | 0 < z.im ∧ z.im < Real.pi}
def fullClosedStrip : Set ℂ := {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi}

def SourceSlabSmallMeanTarget : Prop :=
  ∃ b H0 : ℝ, 0 < b ∧ 0 < H0 ∧ ∀ H : ℝ, H0 ≤ H → ∀ (u : ℂ → ℝ),
    ContinuousOn u {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi} →
    LocallyLipschitzOn {z : ℂ | 0 < z.im ∧ z.im < Real.pi} u →
    MemLp (gradient u) 2 (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < Real.pi}) →
    (∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi}, ‖gradient u z‖^2) ≤ 2*Real.pi*H →
    (∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (x + y*Complex.I) = 0) →
    ∀ j : ℤ, (j:ℝ) ≤ b*H →
      (Real.pi)⁻¹ * ∫ z in {z : ℂ | (j:ℝ) ≤ z.re ∧ z.re ≤ (j:ℝ)+1 ∧
          0 ≤ z.im ∧ z.im ≤ Real.pi}, u z ≤ H/2

def closedIntegerStrip (j : ℤ) : Set ℂ :=
  {z | (j:ℝ) ≤ z.re ∧ z.re ≤ (j:ℝ)+1 ∧ 0 ≤ z.im ∧ z.im ≤ Real.pi}

def openIntegerStrip (j : ℤ) : Set ℂ :=
  {z | (j:ℝ) < z.re ∧ z.re < (j:ℝ)+1 ∧ 0 < z.im ∧ z.im < Real.pi}

def slabShift (j : ℤ) (z : ℂ) : ℂ := (j:ℂ)+z



def SourceStripLocalizationTarget : Prop :=
  ∀ C0 α : ℝ, 0 < C0 → 0 < α → ∃ b C c H0 : ℝ,
    0 < b ∧ 0 < C ∧ 0 < c ∧ 0 < H0 ∧
    ∀ H : ℝ, H0 ≤ H → ∀ u : ℂ → ℝ,
    ContinuousOn u {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi} →
    LocallyLipschitzOn {z : ℂ | 0 < z.im ∧ z.im < Real.pi} u →
    (∀ z, 0 ≤ u z ∧ u z ≤ H) →
    MemLp (gradient u) 2 (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < Real.pi}) →
    (∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi}, ‖gradient u z‖^2) ≤ 2*Real.pi*H →
    (∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (x+y*Complex.I) = 0) →
    ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ X : Ω → Set ℂ,
      (∀ (j : ℤ) (k : ℕ) (i m : Fin (2^k)),
        P {xi | (X xi ∩ dyadicStripRectangle j k i m).Nonempty} ≤
          ENNReal.ofReal (C0*(2:ℝ)^(-α*(k:ℝ)))) →
      P {xi | ∃ z ∈ X xi, 0 ≤ z.im ∧ z.im ≤ Real.pi ∧ z.re ≤ b*H ∧ u z = H} ≤
        ENNReal.ofReal (C*Real.exp (-c*H))

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StripProbabilities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strip Probabilities for chordal SLE. -/

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



def BeforeFirstModulus (γ : ℝ≥0 → ℂ) (A : ℝ) (t : ℝ≥0) : Prop :=
  ∀ s : ℝ≥0, s < t → ‖γ s‖ < A

universe u
 
def SourceUniformConformalLocalizationTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 → ∃ b C c L0 : ℝ,
    0 < b ∧ 0 < C ∧ 0 < c ∧ 1 < L0 ∧
    ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P →
    ∀ (F : ℂ → ℂ) (Fbar : ℂ → OnePoint ℂ),
    DifferentiableOn ℂ F {z | 0 < z.im} → InjOn F {z | 0 < z.im} →
    ContinuousOn Fbar {z : ℂ | 0 ≤ z.im} →
    (∀ z : ℂ, 0 < z.im → Fbar z = (F z : OnePoint ℂ)) →
    ∀ (q : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (T : ℝ), 0 < T → ContinuousOn η (Icc 0 T) →
    η 0 = 0 → ‖η T‖ = 1 → (∀ t ∈ Icc 0 T, 0 ≤ (η t).im) →
    (∀ t ∈ Icc 0 T, ∃ w : ℂ, Fbar (η t) = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r) →
    ∀ L : ℝ, L0 ≤ L →
      P {xi | ∃ t : ℝ≥0, BeforeFirstModulus (γ xi) (L^b) t ∧
        Fbar (γ xi t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)} ≤
        ENNReal.ofReal (C*L^(-c))

end SLEExactGauge


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_InteriorEntrance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior Entrance for chordal SLE. -/

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

def PreSwallowExcursion (γ : ℝ≥0 → ℂ) (z : ℂ) (A : ℝ) : Prop :=
  ∃ t : ℝ≥0, A ≤ ‖γ t‖ ∧ ∀ u : ℝ≥0, u < t → z ∈ survivingDomain γ u



end SLEExactGauge
end

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge


universe u
 

def SourceChartedDiskRuleTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 → ∃ C c : ℝ,
    0 < C ∧ 0 < c ∧
    ∀ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P →
    ∀ (F : ℂ → ℂ) (Fbar : ℂ → OnePoint ℂ),
    DifferentiableOn ℂ F {z | 0 < z.im} → InjOn F {z | 0 < z.im} →
    ContinuousOn Fbar {z : ℂ | 0 ≤ z.im} →
    (∀ z : ℂ, 0 < z.im → Fbar z = (F z : OnePoint ℂ)) →
    ∀ (q : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (T : ℝ), 0 < T → ContinuousOn η (Icc 0 T) →
    η 0 = 0 → ‖η T‖ = 1 → 0 < (η T).im → F (η T) = q →
    (∀ t ∈ Icc 0 T, 0 ≤ (η t).im) →
    (∀ t ∈ Icc 0 T, ∃ w : ℂ, Fbar (η t) = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r) →
    ∀ L : ℝ, 1 ≤ L →
      P {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
        Fbar (γ xi t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)} ≤
        ENNReal.ofReal (C*L^(-c))

end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_InteriorDiskProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior Disk Proof for chordal SLE. -/

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
 

def SourceInteriorDiskRuleTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P →
    ∀ F : ℂ → ℂ,
    DifferentiableOn ℂ F {z | 0 < z.im} → InjOn F {z | 0 < z.im} →
    ∀ (q : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (T : ℝ), 0 < T → ContinuousOn η (Icc 0 T) →
    η 0 = 0 → ‖η T‖ = 1 → F (η T) = q →
    (∀ t ∈ Ioc 0 T, 0 < (η t).im) →
    (∀ t ∈ Ioc 0 T, ‖F (η t)-q‖ ≤ r) →
    ∀ L : ℝ, 1 ≤ L →
      P {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
        0 < (γ xi t).im ∧ L*r < ‖F (γ xi t)-q‖} ≤
        ENNReal.ofReal (C*L^(-c))

end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

def sourceScaleTime (c t : ℝ≥0) : ℝ≥0 := t / c ^ 2

def sourceScaleTrace (c : ℝ≥0) (γ : ℝ≥0 → ℂ) (t : ℝ≥0) : ℂ :=
  (c : ℂ) * γ (sourceScaleTime c t)

def sourceScaleChart (c : ℝ≥0) (F : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℂ :=
  (c : ℂ) * F (sourceScaleTime c t) (z / (c : ℂ))

universe u_source_scale
 

def SourceCapacityScalingTarget : Prop :=
  (∀ (c : ℝ≥0), 0 < c → ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
    IsCapacityTwoWitness (fun t => (c : ℝ) * U (sourceScaleTime c t))
      (sourceScaleTrace c γ) (sourceScaleChart c G) (sourceScaleChart c F)) ∧
  (∀ {Ω : Type u_source_scale} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ), 0 < κ → κ < 8 → ∀ (γ : Ω → ℝ≥0 → ℂ),
    IsOrdinaryChordalSLE κ γ P → ∀ (c : ℝ≥0), 0 < c →
    IsOrdinaryChordalSLE κ (fun ω => sourceScaleTrace c (γ ω)) P)
end
end SLEExactGauge
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_scale_time_image (c t : ℝ≥0) (hc : 0 < c) :
    sourceScaleTime c '' Icc 0 t = Icc 0 (sourceScaleTime c t) := by
  ext s
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨bot_le, div_le_div_of_nonneg_right hu.2 (by positivity)⟩
  · intro hs
    refine ⟨s * c ^ 2, ⟨bot_le, ?_⟩, ?_⟩
    · exact (le_div_iff₀ (pow_pos hc 2)).mp hs.2
    · simp [sourceScaleTime, ne_of_gt hc]

lemma source_scale_past (c t : ℝ≥0) (hc : 0 < c) (γ : ℝ≥0 → ℂ) :
    sourceScaleTrace c γ '' Icc 0 t =
      (fun z : ℂ => (c : ℂ) * z) '' (γ '' Icc 0 (sourceScaleTime c t)) := by
  rw [← source_scale_time_image c t hc, ← image_comp, ← image_comp]
  rfl

lemma source_scale_halfplane (c : ℝ≥0) (hc : 0 < c) :
    (fun z : ℂ => (c : ℂ) * z) '' upperHalfPlane = upperHalfPlane := by
  have hcR : 0 < (c : ℝ) := hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [upperHalfPlane, mem_ofPred_eq, mul_im, ofReal_re, ofReal_im, zero_mul,
      add_zero] at *
    exact mul_pos hcR hx
  · intro hz
    refine ⟨z / (c : ℂ), ?_, mul_div_cancel₀ z hcC⟩
    simpa only [upperHalfPlane, mem_ofPred_eq, div_ofReal_im] using
      div_pos hz hcR

lemma source_scale_bounded (c : ℂ) (hc : c ≠ 0) (s : Set ℂ) :
    Bornology.IsBounded ((fun z => c * z) '' s) ↔ Bornology.IsBounded s := by
  constructor
  · intro hs
    have hh := (hs.isCompact_closure.image
      (show Continuous (fun z : ℂ => z / c) by fun_prop)).isBounded
    have he : (fun z : ℂ => z / c) '' ((fun z => c*z) '' s) = s := by
      simp only [image_image]
      simp [mul_div_cancel_left₀ _ hc]
    rw [← he]
    exact hh.subset (image_mono subset_closure)
  · intro hs
    exact (hs.isCompact_closure.image (show Continuous (fun z : ℂ => c*z) by
      fun_prop)).isBounded.subset (image_mono subset_closure)

lemma source_scale_domain (c t : ℝ≥0) (hc : 0 < c) (γ : ℝ≥0 → ℂ) :
    survivingDomain (sourceScaleTrace c γ) t =
      (fun z : ℂ => (c : ℂ)*z) '' survivingDomain γ (sourceScaleTime c t) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let e := Homeomorph.mulLeft₀ (c : ℂ) hcC
  have he : (e : ℂ → ℂ) = fun z => (c : ℂ)*z := rfl
  have HD : upperHalfPlane \ (sourceScaleTrace c γ '' Icc 0 t) =
      e '' (upperHalfPlane \ γ '' Icc 0 (sourceScaleTime c t)) := by
    rw [image_sdiff e.injective, he, source_scale_halfplane c hc, source_scale_past c t hc γ]
  ext z
  constructor
  · rintro ⟨hz, hbound⟩
    rw [HD] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro hb
    apply hbound
    rw [HD, ← e.image_connectedComponentIn hx, he]
    exact (source_scale_bounded _ hcC _).2 hb
  · rintro ⟨x, ⟨hx, hb⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [HD]
      exact mem_image_of_mem e hx
    · intro hbound
      apply hb
      change Bornology.IsBounded (connectedComponentIn
        (upperHalfPlane \ sourceScaleTrace c γ '' Icc 0 t) (e x)) at hbound
      rw [HD, ← e.image_connectedComponentIn hx, he] at hbound
      exact (source_scale_bounded _ hcC _).1 hbound

lemma source_scale_domain_iff (c t : ℝ≥0) (hc : 0 < c) (γ : ℝ≥0 → ℂ) (z : ℂ) :
    z ∈ survivingDomain (sourceScaleTrace c γ) t ↔
      z / (c : ℂ) ∈ survivingDomain γ (sourceScaleTime c t) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [source_scale_domain c t hc γ]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_div_cancel_left₀ _ hcC] using hx
  · intro hz
    exact ⟨z/(c : ℂ), hz, mul_div_cancel₀ z hcC⟩
end
end SLEExactGauge
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_scale_halfplane_iff (c : ℝ≥0) (hc : 0 < c) (z : ℂ) :
    z / (c : ℂ) ∈ upperHalfPlane ↔ z ∈ upperHalfPlane := by
  change 0 < (z / (c : ℂ)).im ↔ 0 < z.im
  rw [div_ofReal_im, div_pos_iff_of_pos_right (show 0 < (c : ℝ) from hc)]

lemma source_scale_witness (c : ℝ≥0) (hc : 0 < c) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ) (hw : IsCapacityTwoWitness U γ G F) :
    IsCapacityTwoWitness (fun t => (c : ℝ) * U (sourceScaleTime c t))
      (sourceScaleTrace c γ) (sourceScaleChart c G) (sourceScaleChart c F) := by
  have hcR : 0 < (c : ℝ) := hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcm (z : ℂ) : (c : ℂ)*z ∈ upperHalfPlane ↔ z ∈ upperHalfPlane := by
    change 0 < ((c : ℂ)*z).im ↔ 0 < z.im
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    exact mul_pos_iff_of_pos_left hcR
  rcases hw with ⟨hγ, hγ0, hIm, hG, hF, hGmap, hFmap, hFG, hGF, hG0, hD, hInf, hLim⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have ht : Continuous (sourceScaleTime c) := by unfold sourceScaleTime; fun_prop
    exact continuous_const.mul (hγ.comp ht)
  · simp [sourceScaleTrace, sourceScaleTime, hγ0]
  · intro t
    simpa only [sourceScaleTrace, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      using mul_nonneg hcR.le (hIm (sourceScaleTime c t))
  · intro t
    exact (differentiableOn_const (c : ℂ)).mul ((hG (sourceScaleTime c t)).comp
      (differentiableOn_id.div_const _) (fun z hz => (source_scale_domain_iff c t hc γ z).1 hz))
  · intro t
    exact (differentiableOn_const (c : ℂ)).mul ((hF (sourceScaleTime c t)).comp
      (differentiableOn_id.div_const _) (fun z hz => (source_scale_halfplane_iff c hc z).2 hz))
  · intro t z hz
    exact (hcm _).2 (hGmap _ ((source_scale_domain_iff c t hc γ z).1 hz))
  · intro t z hz
    apply (source_scale_domain_iff c t hc γ _).2
    simpa [sourceScaleChart, hcC] using hFmap (sourceScaleTime c t)
      ((source_scale_halfplane_iff c hc z).2 hz)
  · intro t z hz
    dsimp [sourceScaleChart]
    rw [mul_div_cancel_left₀ _ hcC, hFG _ _ ((source_scale_domain_iff c t hc γ z).1 hz)]
    exact mul_div_cancel₀ z hcC
  · intro t z hz
    dsimp [sourceScaleChart]
    rw [mul_div_cancel_left₀ _ hcC, hGF _ _ ((source_scale_halfplane_iff c hc z).2 hz)]
    exact mul_div_cancel₀ z hcC
  · intro z hz
    simp only [sourceScaleChart, sourceScaleTime, zero_div]
    rw [hG0 _ ((source_scale_halfplane_iff c hc z).2 hz)]
    exact mul_div_cancel₀ z hcC
  · intro t z hz
    have hd := hD (sourceScaleTime c t) (z / (c : ℂ))
      ((source_scale_domain_iff c t hc γ z).1 hz)
    simp only [sourceScaleTime, NNReal.coe_div, NNReal.coe_pow] at hd
    have htime : HasDerivWithinAt (fun u : ℝ => u / (c : ℝ)^2) (1/(c : ℝ)^2)
        (Ici 0) (t : ℝ) := ((hasDerivAt_id (t : ℝ)).div_const _).hasDerivWithinAt
    have hs := (hd.scomp (t : ℝ) htime (fun u hu => div_nonneg hu (sq_nonneg _))).const_smul
      (c : ℂ)
    have he (u : ℝ) : Real.toNNReal (u / (c : ℝ)^2) = sourceScaleTime c (Real.toNNReal u) := by
      simp only [Real.toNNReal_div' (sq_nonneg _), Real.toNNReal_pow (by positivity),
        Real.toNNReal_coe, sourceScaleTime]
    change HasDerivWithinAt
      (fun u : ℝ => (c : ℂ) * G (Real.toNNReal (u / (c : ℝ)^2)) (z/(c : ℂ)))
      ((c : ℂ) * ((1/(c : ℝ)^2) • (2 / (G (t / c^2) (z/(c : ℂ)) - (U (t/c^2) : ℂ)))))
      (Ici 0) (t : ℝ) at hs
    simp only [he] at hs
    convert hs using 1 <;>
      simp only [sourceScaleChart, sourceScaleTime, Complex.real_smul, ofReal_mul,
        ofReal_div, ofReal_one, ofReal_pow]
    field_simp [hcC]
  · intro t
    let e := Homeomorph.mulLeft₀ ((c : ℂ)⁻¹) (inv_ne_zero hcC)
    have hco : Tendsto (fun z : ℂ => z/(c : ℂ)) (cocompact ℂ) (cocompact ℂ) := by
      have hh : Tendsto e (cocompact ℂ) (cocompact ℂ) := le_of_eq e.map_cocompact
      change Tendsto (fun z : ℂ => (c : ℂ)⁻¹ * z) (cocompact ℂ) (cocompact ℂ) at hh
      simpa only [div_eq_mul_inv, mul_comm] using hh
    have hp : Tendsto (fun z : ℂ => z/(c : ℂ))
        (𝓟 (survivingDomain (sourceScaleTrace c γ) t))
        (𝓟 (survivingDomain γ (sourceScaleTime c t))) :=
      tendsto_principal_principal.mpr (fun z hz => (source_scale_domain_iff c t hc γ z).1 hz)
    have hh := ((hInf (sourceScaleTime c t)).comp (hco.inf hp)).const_mul ((c : ℂ)^2)
    convert hh using 1
    · ext z
      dsimp [Function.comp_def, sourceScaleChart]
      field_simp
    · simp only [sourceScaleTime, NNReal.coe_div, NNReal.coe_pow, ofReal_div, ofReal_pow]
      field_simp
  · intro t
    have hy : Tendsto (fun y : ℝ => y/(c : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using ((continuous_id.div_const (c : ℝ)).continuousAt.tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds))
      · exact eventually_nhdsWithin_of_forall (fun y hy => div_pos hy hcR)
    have hh := ((hLim (sourceScaleTime c t)).comp hy).const_mul (c : ℂ)
    convert hh using 1
    · ext y
      dsimp [Function.comp_def, sourceScaleChart]
      congr 1
      push_cast
      field_simp
    · rfl
end
end SLEExactGauge
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_PhysicalTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Transport for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
def SourceInteriorTraceDensityTarget : Prop :=
  ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
  Continuous U → IsCapacityTwoWitness U γ G F →
  ∀ s t : ℝ≥0, s < t → ∃ u ∈ Ioo s t, 0 < (γ u).im

end SLEExactGauge

end

section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge
 

def SourceFirstHitPhysicalAccessTarget : Prop :=
  ∀ (γ : ℝ≥0 → ℂ), Continuous γ →
  ∀ (s τ : ℝ≥0) (z : ℂ) (r : ℝ), 0 < r →
    Metric.closedBall z r ⊆ survivingDomain γ s → s ≤ τ →
    dist (γ τ) z = r →
    (∀ t ∈ Ico s τ, dist (γ t) z ≠ r) → z ∈ survivingDomain γ τ →
    (∀ t : ℝ≥0, t < τ → γ t ≠ γ τ) ∧
    Metric.ball z r ⊆ survivingDomain γ τ ∧
    (∀ v ∈ Ioc (0:ℝ) 1, (1-v) • γ τ + v • z ∈ survivingDomain γ τ)

end SLEExactGauge

end

section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge
 

def SourceFirstHitChartAccessTarget : Prop :=
  ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
    Continuous U → IsCapacityTwoWitness U γ G F →
    ∀ (s τ : ℝ≥0) (z : ℂ) (r : ℝ), 0 < r →
      Metric.closedBall z r ⊆ survivingDomain γ s → s ≤ τ →
      dist (γ τ) z = r → (∀ t ∈ Ico s τ, dist (γ t) z ≠ r) →
      z ∈ survivingDomain γ τ →
      Tendsto (fun v : ℝ => G τ ((1-v) • γ τ + v • z) - (U τ : ℂ))
        (𝓝[>] 0) (𝓝 0)

end SLEExactGauge

end

end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_PhysicalKernelUtilities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Kernel Utilities for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance physicalDiskKernelTraceMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance physicalDiskKernelChartMeasurableSpace : MeasurableSpace C(upperHalfPlane,ℂ) := borel _

local instance physicalDiskKernelTraceBorelSpace_r9e5dc0_1 : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
local instance physicalDiskKernelChartBorelSpace_r9e5dc0_1 : BorelSpace C(upperHalfPlane,ℂ) := ⟨rfl⟩
def sourcePhysicalDiskKernel (p : SourceDiskParameter × C(ℝ≥0,ℂ)) : ℝ :=
  if ∃ t : ℝ≥0, p.1.1.2 ∈ survivingDomain p.2 t ∧
    ∃ h : p.2 t ∈ upperHalfPlane, p.1.2.2 < ‖p.1.1.1 ⟨p.2 t,h⟩-p.1.2.1‖ then 1 else 0

end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance finitePhysicalDiskTargetTraceMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance finitePhysicalDiskTargetDriverMeasurableSpace : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance finitePhysicalDiskTargetChartMeasurableSpace : MeasurableSpace C(upperHalfPlane,ℂ) := borel _


def SourceFinitePhysicalDiskTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_m : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ (hm : ∀ t, Measurable (B t)) (_hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (_hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (z : ℂ) (r : ℝ), 0 < r →
  ∀ (A : Set Ω), MeasurableSet[hτ.measurableSpace] A →
    (∀ ω ∈ A, ∃ s : ℝ≥0, s ≤ τ ω ∧
      Metric.closedBall z r ⊆ survivingDomain (γ ω) s ∧
      dist (γ ω (τ ω)) z = r ∧
      (∀ t ∈ Ico s (τ ω), dist (γ ω t) z ≠ r) ∧
      z ∈ survivingDomain (γ ω) (τ ω)) →
  ∀ L : ℝ, 1 ≤ L →
    ∀ᵐ ω ∂P, ω ∈ A →
      P[(fun ω => if ∃ t : ℝ≥0, z ∈ survivingDomain (γ ω) (τ ω+t) ∧
        L*r < dist (γ ω (τ ω+t)) z then (1 : ℝ) else 0) | hτ.measurableSpace] ω ≤ C*L^(-c)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 
noncomputable def sourceStopTruncate {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ≥0 := (min (τ ω) t).untopD 0

lemma sourceStopTruncate_coe {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) :
    (sourceStopTruncate τ t ω : WithTop ℝ≥0) = min (τ ω) t := by
  have hn : min (τ ω) (t : WithTop ℝ≥0) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hn
  change (((min (τ ω) (t : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = _
  rw [← hv, WithTop.untopD_coe]

lemma sourceStopTruncate_stopping {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => (sourceStopTruncate τ t ω : WithTop ℝ≥0)) := by
  simpa only [sourceStopTruncate_coe] using hτ.min_const t

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal NNReal
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance physicalClosedPrefixTraceMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance physicalDiskTargetTraceMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance physicalDiskTargetDriverMeasurableSpace : MeasurableSpace C(ℝ≥0,ℝ) := borel _


def SourcePhysicalDiskTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_m : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ (hm : ∀ t, Measurable (B t)) (_hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (_hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) τ)
    (z : ℂ) (r : ℝ), 0 < r →
  ∀ (A : Set Ω), MeasurableSet[hτ.measurableSpace] A →
    (∀ ω ∈ A, ∃ T s : ℝ≥0, τ ω = T ∧ s ≤ T ∧
      Metric.closedBall z r ⊆ survivingDomain (γ ω) s ∧
      dist (γ ω T) z = r ∧
      (∀ t ∈ Ico s T, dist (γ ω t) z ≠ r) ∧
      z ∈ survivingDomain (γ ω) T) →
  ∀ L : ℝ, 1 ≤ L →
    ∀ᵐ ω ∂P, ω ∈ A →
      P[(fun ω => if τ ω ≠ ⊤ ∧ ∃ t : ℝ≥0,
        z ∈ survivingDomain (γ ω) ((τ ω).untopD 0+t) ∧
        L*r ≤ dist (γ ω ((τ ω).untopD 0+t)) z
        then (1 : ℝ) else 0) | hτ.measurableSpace] ω ≤ C*L^(-c)

end
end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window Geometry for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
def sourceSpatialWindowSet (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : Set ℝ≥0 :=
  {t | liveSpatialHitTime γ z r ≤ (t : WithTop ℝ≥0) ∧
    (dist (γ t) z ≤ ε ∨ R ≤ dist (γ t) z ∨ z ∉ survivingDomain γ t)}
noncomputable def sourceSpatialWindowTime (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : WithTop ℝ≥0 :=
  if (sourceSpatialWindowSet γ z r ε R).Nonempty then
    ↑(sInf (sourceSpatialWindowSet γ z r ε R)) else ⊤
noncomputable def sourceSpatialWindowH (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : ℝ :=
  if sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
    z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopD 0) ∧
    dist (γ ((sourceSpatialWindowTime γ z r ε R).untopD 0)) z ≤ ε then 1 else 0
noncomputable def sourceSpatialWindowB (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : ℝ :=
  if sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
    z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopD 0) ∧
    R ≤ dist (γ ((sourceSpatialWindowTime γ z r ε R).untopD 0)) z then 1 else 0

 

def SourceSpatialWindowGeometryTarget : Prop :=
  ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
  Continuous U → IsCapacityTwoWitness U γ G F →
  ∀ (κ : ℝ), 0 < κ → κ < 8 → ∀ (z : ℂ) (ε r R : ℝ),
  0 < ε → ε < r → r < R → r ≤ z.im →
  let σ := liveSpatialHitTime γ z r
  let τ := sourceSpatialWindowTime γ z r ε R
  let H := sourceSpatialWindowH γ z r ε R
  let B := sourceSpatialWindowB γ z r ε R
  let W := spatialGreenWeight κ U γ G z ε
  σ ≤ τ ∧
  (∀ t : ℝ≥0, σ ≤ (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) < τ →
    z ∈ survivingDomain γ t ∧ ε < dist (γ t) z ∧ dist (γ t) z < R) ∧
  (τ = ⊤ → H = 0 ∧ B = 0) ∧
  (σ = ⊤ → τ = ⊤) ∧
  0 ≤ H ∧ H ≤ 1 ∧ 0 ≤ B ∧ B ≤ 1 ∧
  H ≤ (if liveSpatialHitTime γ z ε = ⊤ then (0 : ℝ) else 1) ∧
  (B = 1 → ∃ t : ℝ≥0, σ ≤ (t : WithTop ℝ≥0) ∧
    z ∈ survivingDomain γ t ∧ R ≤ dist (γ t) z ∧
    (t : WithTop ℝ≥0) < liveSpatialHitTime γ z ε) ∧
  (if liveSpatialHitTime γ z ε = ⊤ then (0 : ℝ) else 1) ≤ H+B ∧
  W ≤ W*H + ε^(-codimension κ)*B

lemma source_windowSet_closed {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) : IsClosed (sourceSpatialWindowSet γ z r ε R) := by
  have hl : IsOpen {t : ℝ≥0 | z ∈ survivingDomain γ t} := by
    let gp : C(ℝ≥0,ℂ) := ⟨γ,hc⟩
    exact source_survival_open.preimage
      ((continuous_const.prodMk continuous_id).prodMk continuous_const :
        Continuous (fun t : ℝ≥0 => ((gp,t),z)))
  exact (isClosed_le continuous_const (WithTop.continuous_coe : Continuous ((↑) : ℝ≥0 → WithTop ℝ≥0))).inter
    ((isClosed_le (hc.dist continuous_const) continuous_const).union
      ((isClosed_le continuous_const (hc.dist continuous_const)).union hl.isClosed_compl))

lemma source_window_le_of_mem (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ)
    (t : ℝ≥0) (ht : t ∈ sourceSpatialWindowSet γ z r ε R) :
    sourceSpatialWindowTime γ z r ε R ≤ (t : WithTop ℝ≥0) := by
  unfold sourceSpatialWindowTime
  rw [ite_eq_left ⟨t,ht⟩]
  exact WithTop.coe_le_coe.mpr (csInf_le ⟨0,fun _ _ => bot_le⟩ ht)

lemma source_window_mem {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (t : ℝ≥0)
    (ht : sourceSpatialWindowTime γ z r ε R = t) :
    t ∈ sourceSpatialWindowSet γ z r ε R := by
  unfold sourceSpatialWindowTime at ht
  split_ifs at ht with hn
  · have he := WithTop.coe_injective ht
    rw [← he]
    exact (source_windowSet_closed hc z r ε R).csInf_mem hn ⟨0,fun _ _ => bot_le⟩
  · exact (WithTop.coe_ne_top ht.symm).elim

end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
local instance windowGeometryPathMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance windowGeometryPathBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
 
noncomputable def sourceCollarStart (D : Set ℂ) (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) : WithTop ℝ≥0 :=
  if z ∈ D then liveSpatialHitTime γ z r else ⊤
noncomputable def sourceCollarFinish (D : Set ℂ) (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : WithTop ℝ≥0 :=
  if z ∈ D then sourceSpatialWindowTime γ z r ε R else ⊤
noncomputable def sourceCollarH (D : Set ℂ) (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : ℝ :=
  if z ∈ D then sourceSpatialWindowH γ z r ε R else 0
noncomputable def sourceCollarB (D : Set ℂ) (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : ℝ :=
  if z ∈ D then sourceSpatialWindowB γ z r ε R else 0


lemma source_window_le_iff {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (T : ℝ≥0) :
    sourceSpatialWindowTime γ z r ε R ≤ (T : WithTop ℝ≥0) ↔
      ∃ t ∈ Icc (0 : ℝ≥0) T, t ∈ sourceSpatialWindowSet γ z r ε R := by
  constructor
  · intro hh
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hh)
    exact ⟨t,⟨bot_le, WithTop.coe_le_coe.mp (by simpa only [← ht] using hh)⟩,
      source_window_mem hc z r ε R t ht.symm⟩
  · rintro ⟨t,ht,hmem⟩
    exact (source_window_le_of_mem γ z r ε R t hmem).trans (WithTop.coe_le_coe.mpr ht.2)

lemma source_liveTime_eq_killed {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z) :
    liveSpatialHitTime γ z r =
      if z ∈ survivingDomain γ (spatialHitTime γ z r).untopA
      then spatialHitTime γ z r else ⊤ := by
  rw [liveSpatialHitTime_eq hc z r hs]
  by_cases hn : spatialHitTime γ z r = ⊤
  · simp only [hn, ite_self]
  · obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
    rw [ite_eq_right hn, ← ht]
    rfl

lemma source_live_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    {τ : a.samples → WithTop ℝ≥0} (hτ : IsStoppingTime a.filtration τ) :
    MeasurableSet[hτ.measurableSpace] {ω | z ∈ survivingDomain (γ ω) (τ ω).untopA} := by
  have hm := measurable_stoppedValue
    (source_killedChart_progressive a.measurable_B a.continuous_B κ
      (fun ω : a.samples => γ ω) a.G a.F a.witness z) hτ
  have he : {ω : a.samples | z ∈ survivingDomain (γ ω) (τ ω).untopA} =
      {ω : a.samples | 0 < (stoppedValue (fun t (ω : a.samples) =>
        if z ∈ survivingDomain (γ ω) t then a.G ω t z else 0) τ ω).im} := by
    ext ω
    change (z ∈ survivingDomain (γ ω) (τ ω).untopA) ↔
      0 < (if z ∈ survivingDomain (γ ω) (τ ω).untopA then a.G ω (τ ω).untopA z else 0).im
    by_cases hl : z ∈ survivingDomain (γ ω) (τ ω).untopA
    · simp only [hl, true_iff]
      exact (a.witness ω).2.2.2.2.2.1 _ hl
    · simp [hl]
  rw [he]
  exact measurableSet_lt measurable_const (Complex.measurable_im.comp hm)

lemma source_liveHit_stopping
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    (r : ℝ) (hy : r ≤ z.im) :
    IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r) := by
  have hσ : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r) :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r
  have hA := source_live_stopped_measurable a z hσ
  intro T
  have he : {ω : a.samples | liveSpatialHitTime (γ ω) z r ≤ (T : WithTop ℝ≥0)} =
      {ω : a.samples | z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z r).untopA} ∩
      {ω : a.samples | spatialHitTime (γ ω) z r ≤ (T : WithTop ℝ≥0)} := by
    ext ω
    have hs : r ≤ dist (γ ω 0) z := by
      rw [(a.witness ω).2.1, dist_zero_left]
      exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [source_liveTime_eq_killed (a.trace_continuous ω) z r hs]
    by_cases hl : z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z r).untopA
    · simp only [hl, true_and, ite_true]
    · simp only [hl, false_and, iff_false, ite_false]
      exact not_le_of_gt (WithTop.coe_lt_top _)
  rw [he]
  exact hA.2 T

 
lemma source_windowKernel_closed (T : ℝ≥0) (ε R : ℝ) :
    IsClosed {p : (ℝ≥0 × C(ℝ≥0,ℂ)) × ℂ | ∃ t ∈ Icc (0 : ℝ≥0) T,
      p.1.1 ≤ t ∧ (dist (p.1.2 t) p.2 ≤ ε ∨ R ≤ dist (p.1.2 t) p.2 ∨
        p.2 ∉ survivingDomain p.1.2 t)} := by
  let A : Set (((ℝ≥0 × C(ℝ≥0,ℂ)) × ℂ) × Icc (0 : ℝ≥0) T) :=
    {p | p.1.1.1 ≤ p.2.1 ∧ (dist (p.1.1.2 p.2.1) p.1.2 ≤ ε ∨
      R ≤ dist (p.1.1.2 p.2.1) p.1.2 ∨ p.1.2 ∉ survivingDomain p.1.1.2 p.2.1)}
  have ht : Continuous (fun p : (((ℝ≥0 × C(ℝ≥0,ℂ)) × ℂ) × Icc (0 : ℝ≥0) T) => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hv : Continuous (fun p : (((ℝ≥0 × C(ℝ≥0,ℂ)) × ℂ) × Icc (0 : ℝ≥0) T) =>
      p.1.1.2 p.2.1) := continuous_eval.comp (continuous_fst.fst.snd.prodMk ht)
  have hl : IsOpen {p : (((ℝ≥0 × C(ℝ≥0,ℂ)) × ℂ) × Icc (0 : ℝ≥0) T) |
      p.1.2 ∈ survivingDomain p.1.1.2 p.2.1} := source_survival_open.preimage
      ((continuous_fst.fst.snd.prodMk ht).prodMk continuous_fst.snd)
  have hA : IsClosed A := (isClosed_le continuous_fst.fst.fst ht).inter
    ((isClosed_le (hv.dist continuous_fst.snd) continuous_const).union
      ((isClosed_le continuous_const (hv.dist continuous_fst.snd)).union hl.isClosed_compl))
  have hp := isClosedMap_fst_of_compactSpace A hA
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [A, Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Subtype.exists,
    exists_and_right, exists_eq_right]
  aesop

lemma source_min_time_coe (σ : WithTop ℝ≥0) (T : ℝ≥0) :
    (((min σ (T : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = min σ T := by
  have hn : min σ (T : WithTop ℝ≥0) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hn
  rw [← hs, WithTop.untopD_coe]

lemma source_window_kernel_iff {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (T : ℝ≥0) :
    sourceSpatialWindowTime γ z r ε R ≤ (T : WithTop ℝ≥0) ↔
    liveSpatialHitTime γ z r ≤ (T : WithTop ℝ≥0) ∧
    ∃ t ∈ Icc (0 : ℝ≥0) T, (min (liveSpatialHitTime γ z r) T).untopD 0 ≤ t ∧
      (dist (γ t) z ≤ ε ∨ R ≤ dist (γ t) z ∨ z ∉ survivingDomain γ t) := by
  rw [source_window_le_iff hc z r ε R T]
  constructor
  · rintro ⟨t,ht,hs,he⟩
    have hT := hs.trans (WithTop.coe_le_coe.mpr ht.2)
    refine ⟨hT,t,ht,?_,he⟩
    apply WithTop.coe_le_coe.mp
    rw [source_min_time_coe, min_eq_left hT]
    exact hs
  · rintro ⟨hT,t,ht,hs,he⟩
    refine ⟨t,ht,?_,he⟩
    have hs' := WithTop.coe_le_coe.mpr hs
    rw [source_min_time_coe, min_eq_left hT] at hs'
    exact hs'

def sourceCapPath (γ : C(ℝ≥0,ℂ)) (T : ℝ≥0) : C(ℝ≥0,ℂ) :=
  ⟨fun t => γ (min t T), γ.continuous.comp (continuous_id.min continuous_const)⟩

lemma source_cap_domain (γ : C(ℝ≥0,ℂ)) (T t : ℝ≥0) (ht : t ≤ T) :
    survivingDomain (sourceCapPath γ T) t = survivingDomain γ t := by
  have he : sourceCapPath γ T '' Icc 0 t = γ '' Icc 0 t := by
    apply Set.image_congr
    intro s hs
    change γ (min s T) = γ s
    rw [min_eq_left (hs.2.trans ht)]
  simp only [survivingDomain, he]

lemma source_window_kernel_cap (γ : C(ℝ≥0,ℂ)) (z : ℂ) (ε R : ℝ) (T b : ℝ≥0) :
    (∃ t ∈ Icc (0 : ℝ≥0) T, b ≤ t ∧
      (dist (sourceCapPath γ T t) z ≤ ε ∨ R ≤ dist (sourceCapPath γ T t) z ∨
        z ∉ survivingDomain (sourceCapPath γ T) t)) ↔
    (∃ t ∈ Icc (0 : ℝ≥0) T, b ≤ t ∧
      (dist (γ t) z ≤ ε ∨ R ≤ dist (γ t) z ∨ z ∉ survivingDomain γ t)) := by
  apply exists_congr
  intro t
  apply and_congr_right
  intro ht
  rw [source_cap_domain γ T t ht.2]
  have he : sourceCapPath γ T t = γ t := by dsimp [sourceCapPath]; rw [min_eq_left ht.2]
  rw [he]

lemma source_capPath_adapted
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (T : ℝ≥0) :
    Measurable[a.filtration T] (fun ω : a.samples =>
      sourceCapPath ⟨γ ω,a.trace_continuous ω⟩ T) := by
  refine @source_path_measurable a.samples ℂ (a.filtration T) _ _ _ _ _ _ _ _ ?_
  intro t
  exact (a.trace_adapted (min t T)).mono (a.filtration.mono (min_le_right _ _)) le_rfl

lemma source_window_stopping
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    (r ε R : ℝ) (hy : r ≤ z.im) :
    IsStoppingTime a.filtration (fun ω : a.samples => sourceSpatialWindowTime (γ ω) z r ε R) := by
  let σ := fun ω : a.samples => liveSpatialHitTime (γ ω) z r
  have hσ : IsStoppingTime a.filtration σ := source_liveHit_stopping a z r hy
  intro T
  have hm : Measurable[a.filtration T] (fun ω : a.samples => (min (σ ω) T).untopD 0) :=
    ((hσ.min_const T).measurable_of_le (fun _ => min_le_right _ _)).untopD 0
  have hp : Measurable[a.filtration T] (fun ω : a.samples =>
      (((min (σ ω) T).untopD 0, sourceCapPath ⟨γ ω,a.trace_continuous ω⟩ T),z)) :=
    (hm.prodMk (source_capPath_adapted a T)).prodMk measurable_const
  have hK := (source_windowKernel_closed T ε R).measurableSet.preimage hp
  have he : {ω : a.samples | sourceSpatialWindowTime (γ ω) z r ε R ≤ (T : WithTop ℝ≥0)} =
      {ω : a.samples | σ ω ≤ (T : WithTop ℝ≥0)} ∩
      {ω : a.samples | ∃ t ∈ Icc (0 : ℝ≥0) T, (min (σ ω) T).untopD 0 ≤ t ∧
        (dist (sourceCapPath ⟨γ ω,a.trace_continuous ω⟩ T t) z ≤ ε ∨
         R ≤ dist (sourceCapPath ⟨γ ω,a.trace_continuous ω⟩ T t) z ∨
         z ∉ survivingDomain (sourceCapPath ⟨γ ω,a.trace_continuous ω⟩ T) t)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [source_window_kernel_iff (a.trace_continuous ω) z r ε R T,
      source_window_kernel_cap]
    rfl
  rw [he]
  exact (hσ T).inter hK

lemma source_collarStart_stopping
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (r : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) :
    IsStoppingTime a.filtration (fun ω : a.samples => sourceCollarStart D (γ ω) z r) := by
  by_cases hz : z ∈ D
  · simpa only [sourceCollarStart, ite_eq_left hz] using source_liveHit_stopping a z r (hy z hz)
  · simpa only [sourceCollarStart, ite_eq_right hz] using (show IsStoppingTime a.filtration (fun _ => (⊤ : WithTop ℝ≥0)) from fun _ => MeasurableSet.const _)

lemma source_collarFinish_stopping
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (r ε R : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) :
    IsStoppingTime a.filtration (fun ω : a.samples => sourceCollarFinish D (γ ω) z r ε R) := by
  by_cases hz : z ∈ D
  · simpa only [sourceCollarFinish, ite_eq_left hz] using source_window_stopping a z r ε R (hy z hz)
  · simpa only [sourceCollarFinish, ite_eq_right hz] using (show IsStoppingTime a.filtration (fun _ => (⊤ : WithTop ℝ≥0)) from fun _ => MeasurableSet.const _)

end
end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window Bounds for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance windowBoundsPathMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _

end
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance windowBoundsApproachPathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _

noncomputable def sourceApproachConstant (κ : ℝ) : ℝ :=
  (uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ) *
    (512 * Real.pi) ^ codimension κ

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance windowBoundsLivePathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance windowBoundsIntegralPathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance windowBoundsDriverPathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℝ) := borel _

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
universe u_source_approach
 

def SourceConditionalApproachTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 → ∃ C : ℝ, 0 < C ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧
  ∀ (Ω : Type u_source_approach) (_ : MeasurableSpace Ω) (P : Measure Ω),
  IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (z : ℂ) (ε r : ℝ), 0 < ε → ε ≤ q * r → r ≤ z.im →
  ∃ hτ : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r),
    let μ := P.comap (Subtype.val : a.samples → Ω)
    μ[(fun ω : a.samples => if liveSpatialHitTime (γ ω) z ε = ⊤ then (0 : ℝ) else 1)
      | hτ.measurableSpace] ≤ᵐ[μ]
      (fun ω => C * ε ^ codimension κ * spatialGreenWeight κ
        (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r)

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window Tails for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
namespace SLEExactGauge
noncomputable section
universe u_source_spatial
def SourceSpatialConditionalMeanTarget : Prop :=
  ∀ (Ω : Type u_source_spatial) (_ : MeasurableSpace Ω) (P : Measure Ω),
  IsProbabilityMeasure P → ∀ (κ : ℝ), 0 < κ → κ < 8 →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (z : ℂ) (ε r : ℝ), 0 < ε → ε ≤ r → r ≤ z.im →
  ∃ hτ : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r),
    let μ := P.comap (Subtype.val : a.samples → Ω)
    let W := fun v ω => spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) z v
    μ[W ε | hτ.measurableSpace] =ᵐ[μ] W r ∧
    ∀ Y : a.samples → ℝ, Integrable Y μ → Y ≤ᵐ[μ] W ε →
      μ[Y | hτ.measurableSpace] ≤ᵐ[μ] W r

end
end SLEExactGauge

end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_PhysicalMeshWindowCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Mesh Window Core for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

 

structure SourceWindowCore {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (D : Set ℂ) (r R : ℝ)
    (γ : ℝ≥0 → Ω → ℂ) (σ τ : ℂ → Ω → WithTop ℝ≥0) : Prop where
  measurable_D : MeasurableSet D
  bounded_D : D ⊆ ball 0 1
  radius_pos : 0 < r
  radius_le : r ≤ R
  radius_small : 3*R ≤ 1
  continuous_trace : ∀ ω, Continuous (fun t => γ t ω)
  adapted_trace : ∀ t, Measurable[ℱ t] (γ t)
  start : ∀ z, IsStoppingTime ℱ (σ z)
  finish : ∀ z, IsStoppingTime ℱ (τ z)
  time_le : ∀ z ω, σ z ω ≤ τ z ω
  contact : ∀ z ω, σ z ω ≠ ⊤ → dist (γ ((σ z ω).untopD 0) ω) z = r
  confined : ∀ z ω (t : ℝ≥0), σ z ω ≤ (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) < τ z ω →
    dist (γ t ω) z < R
  outside : ∀ z, z ∉ D → ∀ ω, σ z ω = ⊤

end
end SLEExactGauge
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowBGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window BGeometry for chordal SLE. -/


section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
 

def SourceSpatialWindowMeansTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∃ C Cbad c q : ℝ, 0 < C ∧ 0 < Cbad ∧ 0 < c ∧ 0 < q ∧ q < 1 ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (z : ℂ) (ε r L : ℝ), 0 < ε → ε ≤ q*r → r < z.im → 1 < L →
  ∃ hσ : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r),
    let μ := P.comap (Subtype.val : a.samples → Ω)
    let W := fun v (ω : a.samples) => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z v
    let H := fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε (L*r)
    let B := fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε (L*r)
    μ[H | hσ.measurableSpace] ≤ᵐ[μ] (fun ω => C*ε^codimension κ*W r ω) ∧
    μ[(fun ω => r^codimension κ*W ε ω*H ω) | hσ.measurableSpace] ≤ᵐ[μ]
      (fun ω => r^codimension κ*W r ω) ∧
    μ[B | hσ.measurableSpace] ≤ᵐ[μ]
      (fun ω => Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1))

end
end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_PhysicalMeshPast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Mesh Past for chordal SLE. -/


section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

noncomputable def sourceMeshCount (p : ℝ) (D : Set ℂ) (γ : ℝ≥0 → ℂ) (r : ℝ) : ℝ :=
  r^(-p)*∫ z in D, if sourceCollarStart D γ z r = ⊤ then (0:ℝ) else 1

end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_mesh_grid_radius_le {q r δ : ℝ} (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hrδ : r ≤ δ) (n : ℕ) : r*q^n ≤ δ :=
  (mul_le_mul_of_nonneg_left (pow_le_one₀ hq.le hq1.le) hr.le).trans (by simpa using hrδ)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
structure SourceMeshParameters (κ : ℝ) where
  C : ℝ
  Cbad : ℝ
  c : ℝ
  q : ℝ
  u : ℝ
  L : ℝ
  hC : 0 < C
  hCb : 0 < Cbad
  hc : 0 < c
  hq : 0 < q
  hq1 : q < 1
  hu : 1 < u
  huq : u*q < 1
  hratio : 1 < q^codimension κ/(u*q)
  hL : 1 < L
  halpha : Cbad*L^(-c)*q^(-codimension κ) ≤ 1/2
  means :
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
      (z : ℂ) (ε r L : ℝ), 0 < ε → ε ≤ q*r → r < z.im → 1 < L →
    ∃ hσ : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r),
      let μ := P.comap (Subtype.val : a.samples → Ω)
      let W := fun v (ω : a.samples) => spatialGreenWeight κ
        (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z v
      let H := fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε (L*r)
      let B := fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε (L*r)
      μ[H | hσ.measurableSpace] ≤ᵐ[μ] (fun ω => C*ε^codimension κ*W r ω) ∧
      μ[(fun ω => r^codimension κ*W ε ω*H ω) | hσ.measurableSpace] ≤ᵐ[μ]
        (fun ω => r^codimension κ*W r ω) ∧
      μ[B | hσ.measurableSpace] ≤ᵐ[μ]
        (fun ω => Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1))

end
end SLEExactGauge
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window Propagation for chordal SLE. -/


section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
 

def SourcePhysicalMeshTailTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 → ∀ η : ℝ, 0 < η →
  ∃ C c δ₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ₀ ∧ δ₀ < η ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (ρ : a.samples → WithTop ℝ≥0) (hρ : IsStoppingTime a.filtration ρ)
    (z₀ : ℂ) (r_f δ : ℝ), 0 < r_f → r_f ≤ δ → δ ≤ δ₀ →
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let E := {ω : a.samples | C*δ^(-codimension κ) < spatialRealMass κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r_f (Metric.ball z₀ 1)}
  ∀ᵐ ω ∂μ, ρ ω ≠ ⊤ →
    Metric.closedBall z₀ (1+η) ⊆ survivingDomain (γ ω) ((ρ ω).untopD 0) →
    μ[(fun ω => if ω ∈ E then (1:ℝ) else 0) | hρ.measurableSpace] ω ≤
      C*Real.exp (-c*δ^(-2:ℝ))

end
end SLEExactGauge
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RetainedSeedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Seed Moments for chordal SLE. -/


section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceRetainedSeedTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (z₀ : ℂ), 2 < z₀.im →
  ∃ (T : ℝ≥0) (e₀ m₀ m₂ : ℝ),
    0 < T ∧ 0 < e₀ ∧ 0 < m₀ ∧ 0 < m₂ ∧
    ∀ r : ℝ, 0 < r → r ≤ e₀ →
      let X := fun ω : a.samples => finiteSpatialGreenMass κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r T (closedBall z₀ 1)
      ENNReal.ofReal m₀ ≤ ∫⁻ ω, X ω ∂(P.comap Subtype.val) ∧
      (∫⁻ ω, (X ω)^2 ∂(P.comap Subtype.val)) ≤ ENNReal.ofReal m₂
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceLiveEntranceTailTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∃ M C c : ℝ, 0 < M ∧ 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ),
    4 ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4)) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ 1 → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | M*u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ 1)} ≤
      ENNReal.ofReal (C*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ)))
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
def sourceScaled (a : RegularSLEPresentation P κ γ) (c : ℝ≥0) (hc : 0 < c) :
    RegularSLEPresentation P κ (fun ω => sourceScaleTrace c (γ ω)) where
  samples := a.samples
  measurable_samples := a.measurable_samples
  full_samples := a.full_samples
  B := fun t ω => (c:ℝ)*a.B (sourceScaleTime c t) ω
  measurable_B := fun t => measurable_const.mul (a.measurable_B _)
  continuous_B := fun ω => continuous_const.mul ((a.continuous_B ω).comp (by unfold sourceScaleTime; fun_prop))
  zero_B := fun ω => by simp [sourceScaleTime,a.zero_B ω]
  brownian := by
    have hh := a.brownian.smul (c := (c^2)⁻¹) (inv_ne_zero (pow_ne_zero 2 hc.ne'))
    simpa only [sourceScaleTime,NNReal.coe_inv,NNReal.coe_pow,Real.sqrt_inv,
      Real.sqrt_sq c.coe_nonneg,inv_inv,div_eq_mul_inv,mul_comm] using hh
  G := fun ω => sourceScaleChart c (a.G ω)
  F := fun ω => sourceScaleChart c (a.F ω)
  witness := fun ω => by
    have hh := source_scale_witness c hc (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (a.F ω) (a.witness ω)
    simpa only [mul_left_comm (c:ℝ) (Real.sqrt κ)] using hh
end RegularSLEPresentation

end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourcePhysicalBallAllTailTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ) (r : ℝ),
    0 < r → 4*r ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*(4*r))) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ r → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | r^dimension κ*u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ r)} ≤
      ENNReal.ofReal (C*r^codimension κ*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ)))
end
end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RetainedDyadicGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Dyadic Geometry for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
 
def retainedDyadicSquare (k : ℕ) (ij : ℤ × ℤ) : Set ℂ :=
  {z | (ij.1 : ℝ) ≤ (2:ℝ)^k*z.re ∧ (2:ℝ)^k*z.re < (ij.1 : ℝ)+1 ∧
    (ij.2 : ℝ) ≤ (2:ℝ)^k*z.im ∧ (2:ℝ)^k*z.im < (ij.2 : ℝ)+1}
noncomputable def retainedDyadicAddress (k : ℕ) (z : ℂ) : ℤ × ℤ :=
  (⌊(2:ℝ)^k*z.re⌋, ⌊(2:ℝ)^k*z.im⌋)
noncomputable def retainedCandidates (M k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(M:ℤ)*2^k) ((M:ℤ)*2^k)).product
    (Finset.Icc (-(M:ℤ)*2^k) ((M:ℤ)*2^k))

end SLEExactGauge
end

 
section
open Set Filter Metric Complex
open scoped Topology
namespace SLEExactGauge
noncomputable section
def sourceDyadicCenter (k : ℕ) (ij : ℤ × ℤ) : ℂ :=
  ⟨((ij.1:ℝ)+1/2)*(2:ℝ)^(-(k:ℝ)),((ij.2:ℝ)+1/2)*(2:ℝ)^(-(k:ℝ))⟩
end
end SLEExactGauge
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_HausdorffLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hausdorff Limits for chordal SLE. -/

section

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
noncomputable def retainedThreshold (κ D : ℝ) (k : ℕ) : ℝ :=
  D * ((2:ℝ)^(-(k:ℝ)))^dimension κ * (Real.log (k:ℝ))^(codimension κ/2)
 
def excessiveSquares {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) : Set ℂ :=
  ⋃ k ∈ Set.Icc k₀ N, ⋃ ij : ℤ × ℤ,
    {z | z ∈ retainedDyadicSquare k ij ∧
      ENNReal.ofReal (retainedThreshold κ D k) < ν N ω (retainedDyadicSquare k ij)}
noncomputable def retainedMeasure {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) : Measure ℂ :=
  (ν N ω).restrict (excessiveSquares κ D ν k₀ N ω)ᶜ
 

def SourceRetainedConstructionTarget : Prop :=
  ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ ν : ℕ → Kernel Ω ℂ, (∀ N, IsFiniteKernel (ν N)) →
  ∀ K : Set ℂ, IsCompact K → (∀ N ω, ν N ω Kᶜ = 0) →
  ∀ (A c m₀ m₂ : ℝ), 0 < A → 0 < c → 0 < m₀ → 0 < m₂ →
  ∀ kmin : ℕ,
  (∀ N, kmin ≤ N → ENNReal.ofReal m₀ ≤ ∫⁻ ω, ν N ω K ∂P) →
  (∀ N, kmin ≤ N → (∫⁻ ω, (ν N ω K)^2 ∂P) ≤ ENNReal.ofReal m₂) →
  (∀ N k, kmin ≤ k → k ≤ N → ∀ ij : ℤ × ℤ, ∀ u : ℝ, 1 ≤ u →
    P {ω | ((2:ℝ)^(-(k:ℝ)))^dimension κ * u <
      (ν N ω (retainedDyadicSquare k ij)).toReal} ≤
    ENNReal.ofReal (A*((2:ℝ)^(-(k:ℝ)))^codimension κ *
      Real.exp (-c*u^(2/codimension κ)))) →
  ∃ (D a p B : ℝ) (k₀ : ℕ), 1 ≤ D ∧ 0 < a ∧ 0 < p ∧ 0 < B ∧ kmin ≤ k₀ ∧
    (∀ N, k₀ ≤ N →
      Measurable (fun ω => retainedMeasure κ D ν k₀ N ω K) ∧
      (∀ ω, retainedMeasure κ D ν k₀ N ω K ≤ ENNReal.ofReal B) ∧
      (∀ ω k, k₀ ≤ k → k ≤ N → ∀ ij,
        retainedMeasure κ D ν k₀ N ω (retainedDyadicSquare k ij) ≤
          ENNReal.ofReal (retainedThreshold κ D k)) ∧
      ENNReal.ofReal p ≤ P {ω | ENNReal.ofReal a ≤ retainedMeasure κ D ν k₀ N ω K}) ∧
    ENNReal.ofReal p ≤
      P {ω | ∃ᶠ N in atTop, ENNReal.ofReal a ≤ retainedMeasure κ D ν k₀ N ω K}



def SourceRetainedBadSquareTarget : Prop :=
  ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (X : Ω → ℝ), Measurable X → (∀ ω, 0 ≤ X ω) →
  ∀ (A c l D : ℝ), 0 < A → 0 < c → 0 < l → 1 ≤ D →
  ∀ k : ℕ, 1 ≤ Real.log (k:ℝ) →
  (∀ u : ℝ, 1 ≤ u → P {ω | l^dimension κ * u < X ω} ≤
    ENNReal.ofReal (A*l^codimension κ*Real.exp (-c*u^(2/codimension κ)))) →
  (∫⁻ ω in {ω | D*l^dimension κ*(Real.log (k:ℝ))^(codimension κ/2) < X ω},
    ENNReal.ofReal (X ω) ∂P) ≤
    ENNReal.ofReal ((2*A/c)*l^2*(k:ℝ)^(-(c/2)*D^(2/codimension κ)))



noncomputable def retainedBadSquareMass {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (N k : ℕ) (ij : ℤ × ℤ) (ω : Ω) : ℝ≥0∞ :=
  if ENNReal.ofReal (retainedThreshold κ D k) < ν N ω (retainedDyadicSquare k ij)
  then ν N ω (retainedDyadicSquare k ij) else 0

end SLEExactGauge
end

 
section

 

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

noncomputable def retainedBallSquares (k : ℕ) (x : ℂ) : Finset (ℤ × ℤ) :=
  (Finset.Icc ((retainedDyadicAddress k x).1 - 1) ((retainedDyadicAddress k x).1 + 1)).product
    (Finset.Icc ((retainedDyadicAddress k x).2 - 1) ((retainedDyadicAddress k x).2 + 1))

end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ActualRetainedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Retained Kernel for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
variable (a : RegularSLEPresentation P κ γ)
def sourceFiniteGreenKernel (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) : Kernel a.samples ℂ :=
  (Kernel.const a.samples (volume.restrict (closedBall z₀ 1))).withDensity
    (fun ω z => ENNReal.ofReal (if spatialHitTime (γ ω) z ((2:ℝ)^(-(N:ℝ))) ≤ T then
      spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z ((2:ℝ)^(-(N:ℝ))) else 0))
end RegularSLEPresentation
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
def SourceRetainedDyadicInteriorTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∀ K E : Set ℂ, IsCompact K → IsClosed E →
  ∀ μ : ℕ → FiniteMeasure ℂ, ∀ a : ℝ≥0, 0 < a →
  (∃ᶠ N in atTop, a ≤ (μ N).mass) →
  (∀ N, μ N Kᶜ = 0) →
  ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) →
  (∀ N, (μ N : Measure ℂ) (Metric.cthickening (e N) E)ᶜ = 0) →
  ∀ D : ℝ, 0 < D → ∀ k₀ : ℕ,
  (∀ N k, k₀ ≤ k → k ≤ N → ∀ ij : ℤ × ℤ,
    μ N (retainedDyadicSquare k ij) ≤ ENNReal.ofReal (retainedThreshold κ D k)) →
  0 < hausdorffGauge h (K ∩ E)

end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Complex TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance actualRetainedKernelDriverMeasurableSpace : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance actualRetainedKernelTraceMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _


local instance actualRetainedKernelDriverBorelSpace_r9e5dc0_1 : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance actualRetainedKernelTraceBorelSpace_r9e5dc0_1 : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
def SourceTraceLawUniqueTarget : Prop :=
  ∀ {Ω : Type*} [_m : MeasurableSpace Ω] {P : Measure Ω} (κ : ℝ), 0 < κ → κ < 8 →
  ∀ (B B' : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → IsBrownianReal B' P →
  ∀ (_hm : ∀ t, Measurable (B t)) (_hm' : ∀ t, Measurable (B' t))
    (_hc : ∀ ω, Continuous (fun t => B t ω)) (_hc' : ∀ ω, Continuous (fun t => B' t ω))
    (γ η : Ω → ℝ≥0 → ℂ) (G F G' F' : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hw' : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B' t ω) (η ω) (G' ω) (F' ω)),
    P.map (sourceTracePath γ (fun ω => (hw ω).1)) =
      P.map (sourceTracePath η (fun ω => (hw' ω).1))
end
end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StochasticIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stochastic Integrals for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
namespace SLEExactGauge
noncomputable def spatialLaterKernel (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ)
    (r : ℝ) (z w : ℂ) : ℝ≥0∞ :=
  if spatialHitTime γ z r = ⊤ then 0 else
    let s := (spatialHitTime γ z r).untopD 0
    if z ∈ survivingDomain γ s ∧ w ∈ survivingDomain γ s ∧
        spatialHitTime γ w r ≤ s then ENNReal.ofReal (halfPlaneGreen (G s z) (G s w)) else 0

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal ComplexConjugate



open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal ComplexConjugate



open Set Filter MeasureTheory
open scoped ENNReal NNReal



open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal





noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.BrownianPredictable



abbrev pastSigma {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (t : Set.Iic s) => B t ω) inferInstance


def predictableFeatureSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (C : ℕ → Ω → ℝ) (φ : ℕ → ℝ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, C i ω * φ i (B (t (i+1)) ω - B (t i) ω)

end SLEExactGauge.BrownianPredictable
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_IntegralLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral Limits for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.BrownianPredictable


def dyadicTime (T : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  (i : ℝ≥0) * (T / (2 : ℝ≥0)^n)



def dyadicQuadraticError {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (C : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n), C n i ω *
    ((B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)^2 -
      (T : ℝ) / (2 : ℝ)^n)

end SLEExactGauge.BrownianPredictable

 

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge.PredictableLimit
open BrownianPredictable

def dyadicDriverSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (C : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n), C n i ω *
    (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)

end SLEExactGauge.PredictableLimit

 

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.TaylorMeshes

 
def remainder₂ (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  f y - f x - deriv f x * (y-x) - deriv (deriv f) x / 2 * (y-x)^2


def mesh (T : ℝ) (n i : ℕ) : ℝ := (i : ℝ) * (T / (2 : ℝ)^n)

end SLEExactGauge.TaylorMeshes

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ItoIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ito Isometry for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge.BrownianIto
open BrownianPredictable TaylorMeshes

def quadraticSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n),
    (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)^2

end SLEExactGauge.BrownianIto

namespace SLEExactGauge.BrownianField
open BrownianPredictable PredictableLimit TaylorMeshes BrownianIto



structure FieldRegular (F V : ℝ → ℝ → ℝ) (b : ℝ → ℝ) (T : ℝ) : Prop where
  smooth : ∀ t, ContDiff ℝ 3 (F t)
  third_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t x, |iteratedDeriv 3 (F t) x| ≤ K
  time_cont : ∀ x, ContinuousOn (fun t => F t x) (Icc 0 T)
  time_deriv : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun u => F u x) (V t x) t
  drift_cont : ContinuousOn (fun p : ℝ × ℝ => V p.1 (b p.2)) ((Icc 0 T) ×ˢ (Icc 0 T))
  second_cont : ContinuousOn (fun t => iteratedDeriv 2 (F t) (b t)) (Icc 0 T)



end SLEExactGauge.BrownianField



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}

noncomputable def ClippedLogSolution.velocity
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (t : ℝ) (ω : Ω) : ℂ × ℝ :=
  clippedLogLoewnerField lo hi hle (Real.sqrt κ * B t.toNNReal ω) (c.Q t ω)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianIto TaylorMeshes

noncomputable def stoppedDyadicIndex (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) : ℕ :=
  Nat.ceil (t / (T / (2 : ℝ≥0)^n))

end SLEExactGauge
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SimpleFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simple Fields for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

noncomputable def stoppedFieldSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (F : Ω → ℝ → ℝ → ℝ) (τ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2^n), (if dyadicTime T n i < τ ω then
    deriv (F ω (mesh T n i)) (B (dyadicTime T n i) ω) else 0) *
      (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}

 
noncomputable def greenLogCoefficient (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  greenLogDensity κ q x * (greenExponent κ * Real.sqrt κ *
    (q.1.re - Real.sqrt κ * x) / greenLogNormSq κ q x)



end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology



open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def driverPredictableSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, C i ω * (B (t (i+1)) ω - B (t i) ω)

noncomputable def driverPredictableEnergy {Ω : Type*} (t : ℕ → ℝ≥0)
    (C : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, C i ω ^ 2 * ((t (i+1) : ℝ) - t i)

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ExponentialMartingales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential Martingales for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal



open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable

noncomputable def areaWindowSample {Z : Type*} (f : ℝ × Z → ℝ)
    (σ τ : Z → ℝ≥0) (T : ℝ≥0) (n i : ℕ) (z : Z) : ℝ :=
  if σ z ≤ dyadicTime T n i ∧ dyadicTime T n i < τ z then f (dyadicTime T n i,z) else 0

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StochasticFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stochastic Fubini for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

def spatialFiltration {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    (f : Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 (mZ.prod mΩ) where
  seq t := mZ.prod (f t)
  mono' _ _ h := sup_le_sup le_rfl (MeasurableSpace.comap_mono (f.mono h))
  le' t := sup_le_sup le_rfl (MeasurableSpace.comap_mono (f.le t))

lemma spatial_stopping_section {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 mΩ} {τ : Z × Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (spatialFiltration (Z := Z) f) τ) (z : Z) :
    IsStoppingTime f (fun ω => τ (z,ω)) := by
  intro t
  have h := hτ t
  let : MeasurableSpace Ω := f t
  exact h.preimage (measurable_const.prodMk measurable_id)



end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StoppedFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopped Fields for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal



open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure SpatialAngularFamily {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (κ : ℝ) (z : Z → ℂ) (u ε : ℝ) where
  lo : ℝ
  hi : ℝ
  le : lo ≤ hi
  c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi le q
  T : ℝ≥0
  τ : Z × Ω → ℝ≥0
  stopping : IsStoppingTime (spatialFiltration (Z := Z)
    (Filtration.natural B (fun t => (hm t).stronglyMeasurable)))
    (fun p => (τ p : WithTop ℝ≥0))
  bounded : ∀ p, τ p ≤ T
  inside : ∀ x ω t, t ≤ τ (x,ω) →
    logRadiusClock (Real.log (z x).im) ((c (initialLogCoordinates (z x))).Q t ω) ≤ u ∧
    ε ≤ logAngleSq κ ((c (initialLogCoordinates (z x))).Q t ω) (B t ω) ∧
    lo ≤ ((c (initialLogCoordinates (z x))).Q t ω).1.im ∧
      ((c (initialLogCoordinates (z x))).Q t ω).1.im ≤ hi
  before : ∀ x ω t, t < τ (x,ω) →
    logRadiusClock (Real.log (z x).im) ((c (initialLogCoordinates (z x))).Q t ω) < u ∧
    ε < logAngleSq κ ((c (initialLogCoordinates (z x))).Q t ω) (B t ω)
  boundary : ∀ x ω,
    logRadiusClock (Real.log (z x).im) ((c (initialLogCoordinates (z x))).Q (τ (x,ω)) ω) = u ∨
    logAngleSq κ ((c (initialLogCoordinates (z x))).Q (τ (x,ω)) ω) (B (τ (x,ω)) ω) = ε

noncomputable def SpatialAngularFamily.section
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ : ℝ} {z : Z → ℂ} {u ε : ℝ}
    (a : SpatialAngularFamily B hm κ z u ε) (x : Z) :
    AngularLocalization B hm κ (z x) u ε where
  lo := a.lo
  hi := a.hi
  le := a.le
  solution := a.c (initialLogCoordinates (z x))
  T := a.T
  τ := fun ω => a.τ (x,ω)
  stopping := spatial_stopping_section a.stopping x
  bounded := fun ω => a.bounded (x,ω)
  inside := a.inside x
  before := a.before x
  boundary := a.boundary x

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped ENNReal NNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def slabVariance (κ ε r : ℝ) (A : Set ℂ) : ℝ :=
  (ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
    (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A))).toReal

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_GreenCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Green Covariance for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped ENNReal NNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def spatialSlabIncrement (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (A : Set ℂ) (ε r : ℝ) : ℝ :=
  ∫ z in A, spatialGreenWeight κ U γ G z ε - spatialGreenWeight κ U γ G z r

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def slabAmplitude (κ q : ℝ) (A : Set ℂ) : ℝ :=
  Real.sqrt (((Real.sqrt κ * greenExponent κ * q ^ (-codimension κ)) ^ 2 / 2) *
    (layerGreenConstant * (volume A).toReal))

lemma slabAmplitude_nonneg (κ q : ℝ) (A : Set ℂ) : 0 ≤ slabAmplitude κ q A :=
  Real.sqrt_nonneg _

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SimpleTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simple Tails for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric



open Set Filter Metric Complex
open scoped Topology NNReal



open Set Filter Metric Complex
open scoped Topology NNReal



open Set Filter Metric Complex
open scoped Topology NNReal



open Set Filter
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

lemma codimension_lt_one (κ : ℝ) (hκ : 0 < κ) : codimension κ < 1 := by
  dsimp [codimension, dimension]
  linarith

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def meshTailAmplitude (κ q : ℝ) (A : Set ℂ) : ℝ :=
  1 + slabAmplitude κ q A / (1-q^(1-codimension κ))

end SLEExactGauge

end
end

 
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_TracePosCombined
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Pos Combined for chordal SLE. -/

section

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section


def sourceFiniteOpenCover (h : ℝ → ℝ) (r ε : ℝ≥0∞) (K : Set ℂ) : Prop :=
  ∃ (U : ℕ → Set ℂ) (I : Finset ℕ), (∀ n ∈ I, IsOpen (U n)) ∧
    (∀ n ∈ I, ediam (U n) ≤ r) ∧ K ⊆ ⋃ n ∈ I, U n ∧
    (∑ n ∈ I, extendedGauge h (ediam (U n))) < ε

end
end SLEExactGauge
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

def sourceFineGaugeContent (h : ℝ → ℝ) (r : ℝ≥0∞) (K : Set ℂ) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, U n) (_ : ∀ n, ediam (U n) ≤ r),
    ∑' n, extendedGauge h (ediam (U n))

noncomputable def sourceCoverScale (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1/((n:ℝ)+1))
end
end SLEExactGauge
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance tracePosCoverComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _


def SourceTracePositiveMeasurableTarget : Prop :=
  ∀ (h : ℝ → ℝ), IsGauge h → ∀ (C : Set ℂ), IsClosed C → ∀ s t : ℝ≥0,
    @MeasurableSet C(ℝ≥0, ℂ) (borel _) {γ | 0 < hausdorffGauge h (C ∩ (γ '' Set.Icc s t))}
end
end SLEExactGauge
end
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SimplePastMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simple Past Mesh for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology


section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceSimpleEntranceMeshTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 4 →
  ∃ C c δ₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 4 ≤ z₀.im →
  ∀ rf δ : ℝ, 0 < rf → rf ≤ δ → δ ≤ δ₀ →
    (P.comap Subtype.val) {ω : a.samples | C*δ^(-codimension κ) < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ 1)} ≤
      (P.comap Subtype.val) {ω : a.samples | spatialHitTime (γ ω) z₀ 3 ≠ ⊤} *
        ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ)))
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
def SourceSimpleStretchedTailTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 4 →
  ∃ M C c : ℝ, 0 < M ∧ 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ),
    4 ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4)) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ 1 → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | M*u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ 1)} ≤
      ENNReal.ofReal (C*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ)))
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceSimplePhysicalBallAllTailTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 4 →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ) (r : ℝ),
    0 < r → 4*r ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*(4*r))) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ r → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | r^dimension κ*u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ r)} ≤
      ENNReal.ofReal (C*r^codimension κ*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ)))
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
def SourcePhysicalBallEveryKappaTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ) (r : ℝ),
    0 < r → 4*r ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*(4*r))) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ r → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | r^dimension κ*u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ r)} ≤
      ENNReal.ofReal (C*r^codimension κ*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ)))
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceActualSquareTailTarget_allKappa : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 2 < z₀.im →
  ∃ (A c : ℝ) (kmin : ℕ), 0 < A ∧ 0 < c ∧
  ∀ (T : ℝ≥0) (N k : ℕ), kmin ≤ k → k ≤ N → ∀ ij : ℤ × ℤ, ∀ u : ℝ, 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | ((2:ℝ)^(-(k:ℝ)))^dimension κ*u <
      (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω)
        ((2:ℝ)^(-(N:ℝ))) T (closedBall z₀ 1 ∩ retainedDyadicSquare k ij)).toReal} ≤
    ENNReal.ofReal (A*((2:ℝ)^(-(k:ℝ)))^codimension κ*Real.exp (-c*u^(2/codimension κ)))
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
 

def SourceInteriorRetainedTransferTarget_allKappa : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 2 < z₀.im →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∃ (T : ℝ≥0) (E : Set a.samples), 0 < T ∧ MeasurableSet E ∧
    0 < (P.comap Subtype.val) E ∧ ∀ ω ∈ E,
      0 < hausdorffGauge h (Metric.closedBall z₀ 1 ∩ (γ ω '' Set.Icc 0 T)) ∧
      ∀ (U : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
        IsCapacityTwoWitness U η G F → ∀ s : ℝ≥0,
          0 < hausdorffGauge h (F s '' (Metric.closedBall z₀ 1 ∩ (γ ω '' Set.Icc 0 T)))

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance simplePastMeshTraceMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _


def SourceUniformInteriorSeedTarget_allKappa : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (h : ℝ → ℝ), IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∃ p : ℝ≥0∞, 0 < p ∧ ∀ δ : ℝ≥0, 0 < δ →
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ upperHalfPlane ∧
      p ≤ (P.comap (Subtype.val : a.samples → Ω))
        {ω | 0 < hausdorffGauge h (K ∩ (γ ω '' Set.Icc 0 δ))}
end
end SLEExactGauge
end

 
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_LowerRestartConditionalAllKappa
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower Restart Conditional All Kappa for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance lowerRestartAllKappaRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance lowerRestartAllKappaComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section


def SourceLowerAllIntervalsTarget_allKappa : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (γ ω '' Set.Icc s t)
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
 

def SourceLowerAllKappaTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (γ ω '' Set.Icc s t)
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance lowerUniverseRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance lowerUniverseComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
end
end SLEExactGauge
end

 
end
end
end

end OAI
end


