-- Prove2me | Definitions.Def_OAIQ52Wh002
-- name    : OAIQ52Wh002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T18:38:26.292776+00:00
-- url     : https://prove2.me/theorems/40dc59b4-f443-43af-a766-82573d984d93
-- title:
--   Definitions bundle OAIQ52Wh002 of the split of OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 156 declarations of OpenAI's Lean: 59 definitions, 1 inductive type or structure, 2 instances and 94 theorems. The definitions and types are `OAI.WeakHessian.FormActionBound`, `OAI.WeakHessian.LocalGradientParallelogram`, `OAI.WeakHessian.QuadraticLipschitzBound`, `OAI.WeakHessian.ascendingSlope`, `OAI.WeakHessian.ascendingSlopeApprox`, `OAI.WeakHessian.backwardsHeatTime`, `OAI.WeakHessian.compactCTransform`, `OAI.WeakHessian.compactLipLp`, `OAI.WeakHessian.curvatureTailBound`, `OAI.WeakHessian.distDecayCover`, `OAI.WeakHessian.driftBochner`, `OAI.WeakHessian.exponentialMeasure`, `OAI.WeakHessian.fisherDensity`, `OAI.WeakHessian.fisherEpsilon`, `OAI.WeakHessian.gradientPairSum`, `OAI.WeakHessian.gradientParallelogramDefect`, `OAI.WeakHessian.graphBochner`, `OAI.WeakHessian.hopfUniformLip`, `OAI.WeakHessian.integratedBochner`, `OAI.WeakHessian.kernelMeasure`, `OAI.WeakHessian.localActionLimit`, `OAI.WeakHessian.localizedActionBound`, `OAI.WeakHessian.localizedHeatDen`, `OAI.WeakHessian.localizedHeatFactor`, `OAI.WeakHessian.localizedHeatM`, `OAI.WeakHessian.midpointDualTest`, `OAI.WeakHessian.normalizedRestriction`, `OAI.WeakHessian.positiveProbe`, `OAI.WeakHessian.quadraticWassersteinSq`, `OAI.WeakHessian.reducedEntropy`, `OAI.WeakHessian.regularizedEntropy`, `OAI.WeakHessian.regularizedLog`, `OAI.WeakHessian.regularizedRoot`, `OAI.WeakHessian.renormalizedEntropy`, `OAI.WeakHessian.rootClip`, `OAI.WeakHessian.rootCutoff`, `OAI.WeakHessian.secondDifference`, `OAI.WeakHessian.setDensity`, `OAI.WeakHessian.squareDensityMeasure`, `OAI.WeakHessian.squareDensityProbability` and 20 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/WeakHessian, in whole or in part: `WeakHessian_Calculus_CompactLipDense`, `WeakHessian_Calculus_IntegralSqFatou`, `WeakHessian_Calculus_NormLpSqIntegral`, `WeakHessian_Calculus_ScalarSecondDifference`, `WeakHessian_Calculus_TriangularFoldNorm`, `WeakHessian_Curvature_DecayWeight`, `WeakHessian_Entropy_DensityConvergence`, `WeakHessian_Entropy_EntropyContact`, `WeakHessian_Entropy_FisherDensity`, `WeakHessian_Entropy_FisherEpsilon`, `WeakHessian_Entropy_FisherRoot`, `WeakHessian_Entropy_GradientParallelogramDefect`, `WeakHessian_Entropy_LocalGradientParallelogram`, `WeakHessian_Entropy_NonnegativeParallelogram`, `WeakHessian_Entropy_PolarAddFourParallelograms`, `WeakHessian_Entropy_ReducedEntropy`, `WeakHessian_Entropy_RenormalizedEntropy`, `WeakHessian_Entropy_SmoothDensity`, `WeakHessian_Entropy_TruncatedLog`, `WeakHessian_Entropy_ZeroDensity`, `WeakHessian_Geodesics_MidpointDualTests`, `WeakHessian_Geodesics_MidpointSigmaLower`, `WeakHessian_HeatFlow_EulerStepGenerator`, `WeakHessian_HeatFlow_HeatCost`, `WeakHessian_HeatFlow_HeatInverseSymbol`, `WeakHessian_HeatFlow_HeatSymbol`, `WeakHessian_HeatFlow_PlanHeatEntropy`, `WeakHessian_LocalBounds_AscendingSlope`, `WeakHessian_LocalBounds_ClosedQuadraticEnergy`, `WeakHessian_LocalBounds_ComplexifyReal`, `WeakHessian_LocalBounds_ConstMul`, `WeakHessian_LocalBounds_CoreAlgebra`, `WeakHessian_LocalBounds_DecayTimesNatTwo`, `WeakHessian_LocalBounds_DistDecayCover`, `WeakHessian_LocalBounds_EnergyIdentification`, `WeakHessian_LocalBounds_EulerStep`, `WeakHessian_LocalBounds_ExpMulLp`, `WeakHessian_LocalBounds_ExpNegQuadraticBound`, `WeakHessian_LocalBounds_GraphReuse`, `WeakHessian_LocalBounds_LocalizedCertificate`, `WeakHessian_LocalBounds_LocalizedScaling`, `WeakHessian_LocalBounds_MinNatTendsto`, `WeakHessian_LocalBounds_MulBounded`, `WeakHessian_LocalBounds_PositiveProbes`, `WeakHessian_LocalBounds_QuadraticPotentials`, `WeakHessian_LocalBounds_ReLp`, `WeakHessian_LocalBounds_RootApproximation`, `WeakHessian_LocalBounds_RunningMin`, `WeakHessian_LocalBounds_SetDensities`, `WeakHessian_LocalBounds_TriangularFold`, `WeakHessian_Measure_AeDerivLevel`, `WeakHessian_Measure_AeMinimumDominated`, `WeakHessian_Measure_CurvatureTail`, `WeakHessian_Measure_DaviesTail`, `WeakHessian_Measure_DecayCutoffLp`, `WeakHessian_Measure_InlinedFile0`, `WeakHessian_Measure_IntegrableFatouNonneg`, `WeakHessian_Measure_IntegralExponentialMeasure`, `WeakHessian_Measure_RadialCutoffLp`, `WeakHessian_Sobolev_GradientPairSum`, `WeakHessian_Sobolev_MulBounded`, `WeakHessian_Sobolev_QuadraticGradient`, `WeakHessian_Sobolev_WeakGradientMul`, `WeakHessian_Transport_CcConst`, `WeakHessian_Transport_FormAction`, `WeakHessian_Transport_LocalizedActionBound`, `WeakHessian_Transport_PerturbedPlanDual`, `WeakHessian_Transport_QuadraticCost`.
--
--   **Imports.** It imports the published bundle `Def_WeakHessian`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ52Wh004`; the statements `OAI.WeakHessian.RCD.bounded_entropy_subdifferential`, `OAI.WeakHessian.RCD.compact_sobolev_entropy_subdifferential`, `OAI.WeakHessian.RCD.generator_entropy_subdifferential`, `OAI.WeakHessian.WeakHessianUpperBound.rcd_core_integrated`, `OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_BE` and `OAI.WeakHessian.WeakHessianUpperBound.rcd_weighted_graph_inequality`.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakHessian at commit adc7f12

import Mathlib
import Definitions.Def_WeakHessian

section
-- module Solutions.OAIQ52_WH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

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
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactLipDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile155
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

def compactLipLp (m : Measure X) : Submodule ℝ (Lp ℝ 2 m) where
  carrier := {u | ∃ f : X → ℝ,GloballyLipschitz f ∧ HasCompactSupport f ∧ f =ᵐ[m] u}
  zero_mem' := ⟨0,⟨0,LipschitzWith.const 0⟩,HasCompactSupport.zero,(Lp.coeFn_zero ℝ 2 m).symm⟩
  add_mem' := by
    rintro u v ⟨f,⟨L,hf⟩,hfc,hfe⟩ ⟨g,⟨T,hg⟩,hgc,hge⟩
    refine ⟨f+g,⟨L+T,hf.add hg⟩,hfc.add hgc,?_⟩
    filter_upwards [hfe,hge,Lp.coeFn_add u v] with x hx hy hz
    simpa only [Pi.add_apply,hx,hy] using hz.symm
  smul_mem' := by
    rintro a u ⟨f,⟨lip,hf⟩,hfc,hfe⟩
    have hmul : GloballyLipschitz (fun x => a*f x) := by
      refine ⟨‖a‖₊ * lip, LipschitzWith.of_dist_le_mul fun left right => ?_⟩
      simpa only [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm,
        Real.norm_eq_abs, mul_assoc] using
        mul_le_mul_of_nonneg_left (hf.dist_le_mul left right) (abs_nonneg a)
    refine ⟨fun x => a*f x,hmul,hfc.mul_left,?_⟩
    filter_upwards [hfe,Lp.coeFn_smul a u] with x hx hy
    simpa only [Pi.smul_apply,smul_eq_mul,hx] using hy.symm

end WeakHessian

end
end InlinedFile155

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_IntegralSqFatou
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology ENNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integral_sq_fatou {f : X → ℝ} (hf : AEStronglyMeasurable f m)
    {fs : ℕ → X → ℝ} (hfs : ∀ n, MemLp (fs n) 2 m)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) {B : ℝ}
    (hB : ∀ n, (∫ x, (fs n x)^2 ∂m) ≤ B) :
    MemLp f 2 m ∧ (∫ x, (f x)^2 ∂m) ≤ B := by
  have H : (∫⁻ x, ENNReal.ofReal ((f x)^2) ∂m) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal ((fs n x)^2)) atTop ∂m := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (hx.pow 2)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ((fs n x)^2) ∂m) atTop :=
        lintegral_liminf_le' (fun index => ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          ((hfs index).aestronglyMeasurable.pow 2).aemeasurable)
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le'
        apply Frequently.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hfs n).integrable_sq (ae_of_all _ (fun x => sq_nonneg _))]
        exact ENNReal.ofReal_le_ofReal (hB n)
  have hi : Integrable (fun x => (f x)^2) m := by
    refine ⟨hf.pow 2, ?_⟩
    change (∫⁻ x, ‖(f x)^2‖ₑ ∂m) < ∞
    simp only [Real.enorm_eq_ofReal (sq_nonneg _)]
    exact H.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq hf).mpr hi, ?_⟩
  have hB0 : 0 ≤ B := (integral_nonneg (fun x => sq_nonneg (fs 0 x))).trans (hB 0)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => sq_nonneg _)) hi.1]
  simpa only [ENNReal.toReal_ofReal hB0] using ENNReal.toReal_mono ENNReal.ofReal_ne_top H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_InlinedFile0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

variable {m ν : Measure X}

omit [BorelSpace X]

def exponentialMeasure (m : Measure X) (V : X → ℝ) : Measure X :=
  m.withDensity (fun x => ENNReal.ofReal (Real.exp (V x)))

omit [MetricSpace X] in
lemma exponentialMeasure_le {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, V x ≤ B) :
    exponentialMeasure m V ≤ ENNReal.ofReal (Real.exp B) • m := by
  rw [← withDensity_const]
  exact withDensity_mono (ae_of_all m fun x =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hV x)))

omit [MetricSpace X] in
lemma measure_le_exponentialMeasure {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, -B ≤ V x) :
    m ≤ ENNReal.ofReal (Real.exp B) • exponentialMeasure m V := by
  calc
    m = m.withDensity (fun _ => 1) := withDensity_one.symm
    _ ≤ m.withDensity (ENNReal.ofReal (Real.exp B) •
        (fun x => ENNReal.ofReal (Real.exp (V x)))) := by
      apply withDensity_mono
      filter_upwards with x
      change 1 ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (Real.exp (V x))
      rw [← ENNReal.ofReal_mul (Real.exp_pos B).le, ← Real.exp_add]
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (by linarith [hV x]))
    _ = ENNReal.ofReal (Real.exp B) • exponentialMeasure m V :=
      withDensity_smul' _ _ ENNReal.ofReal_ne_top

omit [MetricSpace X] in
lemma exponentialMeasure_comparable {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, |V x| ≤ B) :
    m ≤ ENNReal.ofReal (Real.exp B) • exponentialMeasure m V ∧
      exponentialMeasure m V ≤ ENNReal.ofReal (Real.exp B) • m := by
  exact ⟨measure_le_exponentialMeasure fun x => (abs_le.mp (hV x)).1,
    exponentialMeasure_le fun x => (abs_le.mp (hV x)).2⟩

omit [MeasurableSpace X] [BorelSpace X] in

lemma deriv_comp_le_metricSpeed {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) {t : ℝ}
    (hd : DifferentiableAt ℝ (fun s => f (evalReal γ s)) t) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      (L : ℝ≥0∞) * metricSpeed γ t := by
  have hlim : Tendsto
      (fun s => ENNReal.ofReal (|f (evalReal γ s) - f (evalReal γ t)| / |s-t|))
      (𝓝[≠] t) (𝓝 (ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t|)) := by
    simpa only [slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv,
      Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using
      ENNReal.tendsto_ofReal (hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt).norm
  calc
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| =
        limsup (fun s => ENNReal.ofReal
          (|f (evalReal γ s) - f (evalReal γ t)| / |s-t|)) (𝓝[≠] t) := hlim.limsup_eq.symm
    _ ≤ limsup (fun s => (L : ℝ≥0∞) * ENNReal.ofReal
        (dist (evalReal γ s) (evalReal γ t) / |s-t|)) (𝓝[≠] t) := by
      refine limsup_le_limsup ?_
      filter_upwards with s
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul L.coe_nonneg,
        ← mul_div_assoc]
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      simpa only [Real.dist_eq] using hf.dist_le_mul (evalReal γ s) (evalReal γ t)
    _ = (L : ℝ≥0∞) * metricSpeed γ t :=
      ENNReal.limsup_const_mul_of_ne_top ENNReal.coe_ne_top

omit [MeasurableSpace X] [BorelSpace X] in
lemma deriv_comp_le_metricSpeed_all {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      (L : ℝ≥0∞) * metricSpeed γ t := by
  by_cases hd : DifferentiableAt ℝ (fun s => f (evalReal γ s)) t
  · exact deriv_comp_le_metricSpeed hf γ hd
  · simp only [deriv_zero_of_not_differentiableAt hd, abs_zero, ENNReal.ofReal_zero]
    exact bot_le

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_MulBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessian
lemma ac_comp_lipschitzOn {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {q : ℝ → X} {a b : ℝ} (hq : AbsolutelyContinuousOnInterval q a b)
    {φ : X → Y} {s : Set X} {L : ℝ≥0} (hφ : LipschitzOnWith L φ s)
    (hs : MapsTo q (uIcc a b) s) : AbsolutelyContinuousOnInterval (φ ∘ q) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hq ⊢
  intro ε hε
  obtain ⟨δ,hδ,hδq⟩ := hq (ε / (L + 1)) (by positivity)
  refine ⟨δ,hδ,?_⟩
  rintro ⟨n,I⟩ hI hlen
  have hsum := hδq (n,I) hI hlen
  calc
    ∑ i ∈ Finset.range n, dist ((φ ∘ q) (I i).1) ((φ ∘ q) (I i).2) ≤
        L * ∑ i ∈ Finset.range n, dist (q (I i).1) (q (I i).2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      exact hφ.dist_le_mul _ (hs (hI.1 i hi).1) _ (hs (hI.1 i hi).2)
    _ ≤ L * (ε / (L + 1)) := by gcongr
    _ < (L + 1) * (ε / (L + 1)) := by gcongr; linarith
    _ = ε := by field

lemma ac_comp_contDiff {q : ℝ → ℝ} {a b : ℝ}
    (hq : AbsolutelyContinuousOnInterval q a b) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    AbsolutelyContinuousOnInterval (φ ∘ q) a b := by
  obtain ⟨M,hM⟩ := hq.exists_bound
  obtain ⟨L,hL⟩ := (hφ.contDiffOn (s := Icc (-M) M)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  apply ac_comp_lipschitzOn hq hL
  intro t ht
  simpa only [Real.norm_eq_abs, mem_Icc, abs_le] using hM t ht

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RunningMin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in

lemma locallyL2_of_bounded (hfinite : FiniteOnBoundedSets m) {f : X → ℝ}
    (hf : AEStronglyMeasurable f m) {L : ℝ} (hbound : ∀ᵐ x ∂m, ‖f x‖ ≤ L) :
    LocallyL2 m f := by
  intro o R _hR
  let : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      hfinite (Metric.ball o R) Metric.isBounded_ball⟩
  exact (memLp_const L).mono' hf.restrict (ae_restrict_of_ae hbound)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_AeMinimumDominated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessianCalculus



lemma exists_equivalent_integrable_measure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {B : X → ℝ} (hB : AEMeasurable B μ) :
    ∃ ν : Measure X, μ ≪ ν ∧ ν ≪ μ ∧ Integrable B ν := by
  let w : X → ℝ≥0∞ := fun x => ENNReal.ofReal (1 / (1 + |B x|))
  have hw : AEMeasurable w μ := (aemeasurable_const.div
    (aemeasurable_const.add hB.abs)).ennreal_ofReal
  have hpos : ∀ x, 0 < 1 + |B x| := fun x => by positivity
  have hμν : μ ≪ μ.withDensity w := withDensity_absolutelyContinuous' hw
    (ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (one_div_pos.mpr (hpos x))).ne')
  refine ⟨μ.withDensity w, hμν, withDensity_absolutelyContinuous μ w, ?_⟩
  rw [integrable_withDensity_iff_integrable_smul₀' hw
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  apply (integrable_const (1 : ℝ)).mono' (hw.ennreal_toReal.mul hB).aestronglyMeasurable
  filter_upwards [] with x
  change |(ENNReal.ofReal (1 / (1 + |B x|))).toReal * B x| ≤ 1
  rw [ENNReal.toReal_ofReal (le_of_lt (one_div_pos.mpr (hpos x))), abs_mul,
    abs_of_pos (one_div_pos.mpr (hpos x)), one_div_mul_eq_div]
  exact (div_le_one (hpos x)).mpr (by linarith [abs_nonneg (B x)])
end WeakHessianCalculus

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_WeakGradientMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma norm_toLp_le_mul_of_ae {f g : X → ℝ} (hf : MemLp f 2 m) (hg : MemLp g 2 m)
    {C : ℝ} (he : ∀ᵐ x ∂m, |f x| ≤ C*|g x|) :
    ‖hf.toLp f‖ ≤ C*‖hg.toLp g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [he,hf.coeFn_toLp,hg.coeFn_toLp] with x hx h1 h2
  simpa only [h1,h2,Real.norm_eq_abs] using hx

end WeakHessian

open Filter
open scoped Topology

lemma norm_sq_sub_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    (a b : E) {d : ℝ} (hd : ‖b‖ ≤ d) :
    |‖a‖^2 - ‖b‖^2| ≤ ‖a-b‖ * (2*d + ‖a-b‖) := by
  have H : |‖a‖ - ‖b‖| ≤ ‖a-b‖ := abs_norm_sub_norm_le a b
  have ha : ‖a‖ ≤ d+‖a-b‖ := by
    have hh := norm_sub_norm_le a b
    linarith
  calc
    _ = |‖a‖-‖b‖| * (‖a‖+‖b‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b)), ← abs_mul]
      congr 1
      ring
    _ ≤ ‖a-b‖ * (2*d+‖a-b‖) := mul_le_mul H (by linarith)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

lemma tendsto_norm_sq_sub_norm_sq {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {a b : ℕ → E} {u : ℕ → F} {c d : ℝ}
    (he : ∀ n, ‖a n-b n‖ ≤ c*‖u n‖) (hb : ∀ n, ‖b n‖ ≤ d)
    (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => ‖a n‖^2-‖b n‖^2) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ‖a n-b n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) he (by simpa using hu.norm.const_mul c)
  apply squeeze_zero_norm (fun n => by
    simpa only [Real.norm_eq_abs] using norm_sq_sub_norm_sq_le (a n) (b n) (hb n))
  simpa only [zero_mul] using ht.mul ((tendsto_const_nhds (x := 2*d)).add ht)

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_NormLpSqIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma norm_toLp_sq_eq_integral {f : X → ℝ} (hf : MemLp f 2 m) :
    ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂m := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hx]

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_NonnegativeParallelogram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology

namespace WeakHessianFunctional
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

structure NonnegativeParallelogram (q : V → ℝ) : Prop where
  nonneg : ∀ f, 0 ≤ q f
  smul : ∀ (a : ℝ) f, q (a • f) = a^2 * q f
  parallelogram : ∀ f g, q (f+g) + q (f-g) = 2 * q f + 2 * q g

variable {q : V → ℝ} (hq : NonnegativeParallelogram q)
include hq

lemma NonnegativeParallelogram.zero : q 0 = 0 := by
  simpa only [zero_smul, zero_pow (by omega : (2:ℕ) ≠ 0), zero_mul] using hq.smul 0 (0:V)

lemma NonnegativeParallelogram.neg (f : V) : q (-f) = q f := by
  simpa using hq.smul (-1) f

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ClosedQuadraticEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

namespace WeakHessianFunctional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {Q : E → ℝ≥0∞}

def proximalFunctional (Q : E → ℝ≥0∞) (u f : E) : ℝ≥0∞ :=
  Q f + ENNReal.ofReal (‖f-u‖^2/2)

omit [InnerProductSpace ℝ E] in
lemma proximalFunctional_lt_top {u f : E} (hf : Q f < ∞) :
    proximalFunctional Q u f < ∞ := by
  unfold proximalFunctional
  finiteness

omit [InnerProductSpace ℝ E] in
lemma proximalFunctional_toReal {u f : E} (hf : Q f < ∞) :
    (proximalFunctional Q u f).toReal = (Q f).toReal + ‖f-u‖^2/2 := by
  rw [proximalFunctional, ENNReal.toReal_add hf.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)]

end WeakHessianFunctional

open Set Filter Bornology
open scoped Topology

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ConstMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X]
variable [MeasurableSpace X] {m : Measure X}
attribute [local instance] Classical.propDecidable
omit [MeasurableSpace X] in
lemma GloballyLipschitz.const_mul {f : X → ℝ} (hf : GloballyLipschitz f) (c : ℝ) :
    GloballyLipschitz (fun x => c * f x) := by
  obtain ⟨L, hL⟩ := hf
  refine ⟨‖c‖₊ * L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
  simpa only [mul_assoc, Real.dist_eq] using
    mul_le_mul_of_nonneg_left (hL.dist_le_mul x y) (abs_nonneg c)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_ScalarSecondDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
open Set Filter MeasureTheory
open scoped Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian

def secondDifference (f : ℝ → ℝ) (h x : ℝ) : ℝ :=
  (f (x + h) + f (x - h) - 2 * f x) / h ^ 2

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_TriangularFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessian

def triangularFold (δ x : ℝ) : ℝ :=
  Metric.infDist x (Set.range fun k : ℤ => δ * (k : ℝ))

lemma triangularFold_lipschitz (δ : ℝ) : LipschitzWith 1 (triangularFold δ) :=
  Metric.lipschitz_infDist_pt _

lemma triangularFold_zero (δ : ℝ) : triangularFold δ 0 = 0 := by
  apply Metric.infDist_zero_of_mem
  exact ⟨0, by simp⟩

lemma triangularFold_nonneg (δ x : ℝ) : 0 ≤ triangularFold δ x :=
  Metric.infDist_nonneg

lemma triangularFold_eq_round {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    triangularFold δ x = |x - δ * (round (x / δ) : ℝ)| := by
  unfold triangularFold
  apply le_antisymm
  · simpa only [Real.dist_eq] using
      Metric.infDist_le_dist_of_mem (x := x) (Set.mem_range_self (round (x / δ)))
  · apply (Metric.le_infDist (Set.range_nonempty (fun k : ℤ => δ * (k : ℝ)))).2
    rintro y ⟨k, rfl⟩
    have H := mul_le_mul_of_nonneg_left (round_le (x / δ) k) (abs_nonneg δ)
    rw [← abs_mul, ← abs_mul] at H
    have h (j : ℤ) : δ * (x / δ - (j : ℝ)) = x - δ * (j : ℝ) := by
      field_simp
    simpa only [h, Real.dist_eq] using H

lemma triangularFold_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    triangularFold δ x ≤ δ / 2 := by
  rw [triangularFold_eq_round hδ]
  have H := mul_le_mul_of_nonneg_left (abs_sub_round (x / δ)) hδ.le
  have h : x - δ * (round (x / δ) : ℝ) =
      δ * (x / δ - (round (x / δ) : ℝ)) := by field_simp
  rw [h, abs_mul, abs_of_pos hδ]
  nlinarith

lemma triangularFold_piecewise {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ∃ k : ℤ, triangularFold δ x = x - δ * (k : ℝ) ∨
      triangularFold δ x = -(x - δ * (k : ℝ)) := by
  refine ⟨round (x / δ), ?_⟩
  rw [triangularFold_eq_round hδ]
  exact abs_choice _

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_TriangularFoldNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

lemma triangularFold_norm_le (δ x : ℝ) : ‖triangularFold δ x‖ ≤ ‖x‖ := by
  have H := (triangularFold_lipschitz δ).norm_sub_le x 0
  simpa only [triangularFold_zero, sub_zero, NNReal.coe_one, one_mul] using H

lemma triangularFold_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => triangularFold (1/((n:ℝ)+1)) x) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => triangularFold_nonneg _ _)
    (fun n => triangularFold_le (by positivity) x)
  have H : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [zero_div, one_div] using H.div_const 2

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma triangularFold_tendsto_Lp (f : Lp ℝ 2 m) :
    Tendsto (fun n : ℕ => (triangularFold_lipschitz (1/((n:ℝ)+1))).compLp
      (triangularFold_zero _) f) atTop (𝓝 0) := by
  let g : ℕ → X → ℝ := fun n x => triangularFold (1/((n:ℝ)+1)) (f x)
  have hg (n : ℕ) : MemLp (g n) 2 m :=
    (triangularFold_lipschitz _).comp_memLp (triangularFold_zero _) (Lp.memLp f)
  have hi : UnifIntegrable g 2 m := by
    intro ε hε
    obtain ⟨δ,hδ,hδf⟩ := (Lp.memLp f).eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ,hδ,fun n s hs hms => ?_⟩
    apply le_trans (eLpNorm_mono (fun x => ?_))
      (hδf s hs hms)
    by_cases hx : x ∈ s
    · simpa only [Set.indicator_of_mem hx,g] using triangularFold_norm_le (1/((n:ℝ)+1)) (f x)
    · simp only [Set.indicator_of_notMem hx,le_refl]
  have ht : UnifTight g 2 m := by
    intro ε hε
    obtain ⟨s,hsm,hs,hfs⟩ := UnifTight.exists_measurableSet_indicator
      (unifTight_const (ι := ℕ) (by norm_num) (Lp.memLp f)) (ENNReal.coe_ne_zero.mpr hε.ne')
    refine ⟨s,hs.ne,fun n => ?_⟩
    apply le_trans (eLpNorm_mono (fun x => ?_)) (hfs n)
    by_cases hx : x ∈ sᶜ
    · simpa only [Set.indicator_of_mem hx,g] using triangularFold_norm_le (1/((n:ℝ)+1)) (f x)
    · simp only [Set.indicator_of_notMem hx,le_refl]
  have hconv := tendsto_Lp_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 2)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun index => (hg index).aestronglyMeasurable)
      (MemLp.zero (α := X) (ε := ℝ))
      hi ht (Eventually.of_forall fun x => triangularFold_tendsto (f x))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  convert hconv using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  apply eLpNorm_congr_ae
  filter_upwards [(triangularFold_lipschitz (1/((n:ℝ)+1))).coeFn_compLp
      (triangularFold_zero _) f, Lp.coeFn_zero ℝ 2 m] with x hx hz
  simp only [Pi.sub_apply, hx, hz, Pi.zero_apply, sub_zero, Function.comp_apply, g]

lemma triangularFold_tendsto_toLp {f : X → ℝ} (hf : MemLp f 2 m) :
    Tendsto (fun n : ℕ => ((triangularFold_lipschitz (1/((n:ℝ)+1))).comp_memLp
      (triangularFold_zero _) hf).toLp (triangularFold (1/((n:ℝ)+1)) ∘ f)) atTop (𝓝 0) := by
  have he (n : ℕ) : ((triangularFold_lipschitz (1/((n:ℝ)+1))).comp_memLp
        (triangularFold_zero _) hf).toLp (triangularFold (1/((n:ℝ)+1)) ∘ f) =
      (triangularFold_lipschitz (1/((n:ℝ)+1))).compLp (triangularFold_zero _) (hf.toLp f) := by
    apply Lp.ext
    filter_upwards [((triangularFold_lipschitz (1/((n:ℝ)+1))).comp_memLp
      (triangularFold_zero _) hf).coeFn_toLp,
      (triangularFold_lipschitz (1/((n:ℝ)+1))).coeFn_compLp (triangularFold_zero _) (hf.toLp f),
      hf.coeFn_toLp] with x h1 h2 h3
    simp only [h1,h2,Function.comp_apply,h3]
  simpa only [he] using triangularFold_tendsto_Lp (hf.toLp f)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_MidpointSigmaLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def normalizedRestriction (m : Measure X) (Q : Set X) : Measure X :=
  (m Q)⁻¹ • m.restrict Q

omit [MetricSpace X] [BorelSpace X] in
lemma normalizedRestriction_ac (m : Measure X) (Q : Set X) :
    normalizedRestriction m Q ≪ m :=
  Measure.absolutelyContinuous_restrict.smul_left _

omit [MetricSpace X] [BorelSpace X] in
lemma normalizedRestriction_ae_mem (m : Measure X) {Q : Set X} (hQ : MeasurableSet Q) :
    ∀ᵐ x ∂normalizedRestriction m Q, x ∈ Q :=
  (Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le (ae_restrict_mem hQ)

omit [MetricSpace X] [BorelSpace X] in
lemma normalizedRestriction_probability (m : Measure X) {Q : Set X}
    (h₀ : m Q ≠ 0) (htop : m Q ≠ ∞) : IsProbabilityMeasure (normalizedRestriction m Q) := by
  refine ⟨?_⟩
  simp only [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h₀ htop

omit [MetricSpace X] [BorelSpace X] in
lemma rnDeriv_normalizedRestriction {m : Measure X} [SigmaFinite m] {Q : Set X}
    (hQ : MeasurableSet Q) (h₀ : m Q ≠ 0) :
    (normalizedRestriction m Q).rnDeriv m =ᵐ[normalizedRestriction m Q] fun _ => (m Q)⁻¹ := by
  have hs := Measure.rnDeriv_smul_left_of_ne_top' (m.restrict Q) m
    (ENNReal.inv_ne_top.mpr h₀)
  have hr := Measure.rnDeriv_restrict_self m hQ
  filter_upwards [(normalizedRestriction_ac m Q).ae_le hs,
    (normalizedRestriction_ac m Q).ae_le hr, normalizedRestriction_ae_mem m hQ] with x hx hy hmem
  change (normalizedRestriction m Q).rnDeriv m x = (m Q)⁻¹ * (m.restrict Q).rnDeriv m x at hx
  rw [hx, hy, indicator_of_mem hmem, Pi.one_apply, mul_one]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_DecayTimesNatTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

lemma decay_times_nat_le_two (n : ℕ) : (3/4:ℝ)^n*(n:ℝ) ≤ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases hn : 3 ≤ n
    · have hc : (3/4:ℝ)*((n:ℝ)+1) ≤ n := by
        have H : (3:ℝ)*((n:ℝ)+1) ≤ 4*(n:ℝ) := by exact_mod_cast (by omega : 3*(n+1) ≤ 4*n)
        linarith
      have hp := mul_le_mul_of_nonneg_left hc (pow_nonneg (by norm_num : 0 ≤ (3/4:ℝ)) n)
      simp only [pow_succ,Nat.cast_add,Nat.cast_one]
      nlinarith [hp]
    · interval_cases n <;> norm_num

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional

def heatSymbol (t s : ℝ) : ℝ :=
  if t = 0 then 1 else Real.exp t * expNegInvGlue (s / t)

@[simp] lemma heatSymbol_zero (s : ℝ) : heatSymbol 0 s = 1 := by simp [heatSymbol]

lemma heatSymbol_continuous (t : ℝ) : Continuous (heatSymbol t) := by
  unfold heatSymbol
  split_ifs
  · exact continuous_const
  · exact continuous_const.mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp (continuous_id.div_const t))

lemma heatSymbol_nonneg (t s : ℝ) : 0 ≤ heatSymbol t s := by
  unfold heatSymbol
  split_ifs
  · exact zero_le_one
  · exact mul_nonneg (Real.exp_pos _).le (expNegInvGlue.nonneg _)


open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventHeat (R : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H := cfc (heatSymbol t) R

lemma resolventHeat_zero {R : H →L[ℂ] H} (hR : R.IsPositive) :
    resolventHeat R 0 = 1 := by
  change cfc (heatSymbol 0) R = 1
  have he : heatSymbol 0 = fun _ : ℝ => 1 := funext heatSymbol_zero
  rw [he, cfc_const 1 R hR.isSelfAdjoint, map_one]

lemma resolvent_spectrum_bounds {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {s : ℝ} (hs : s ∈ spectrum ℝ R) : s ∈ Icc (0:ℝ) 1 := by
  have h0 : 0 ≤ R := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hR
  have h1 : R ≤ 1 := (ContinuousLinearMap.le_def _ _).mpr hR1
  refine ⟨spectrum_nonneg_of_nonneg h0 hs, ?_⟩
  exact (le_algebraMap_iff_spectrum_le hR.isSelfAdjoint).mp (by simpa using h1) s hs

lemma resolventHeat_positive (R : H →L[ℂ] H) (t : ℝ) :
    (resolventHeat R t).IsPositive := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
  exact cfc_nonneg (fun s _ => heatSymbol_nonneg t s)

end WeakHessianFunctional

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_EulerStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional

def eulerStep (t s : ℝ) : ℝ := s / (s+t*(1-s))

def eulerApproximation (t : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  eulerStep (t/(2:ℝ)^n) s ^ (2^n:ℕ)

lemma eulerStep_denom_pos {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    0 < s+t*(1-s) := by
  rcases hs.1.eq_or_lt with rfl | hsp
  · simpa using ht
  · exact add_pos_of_pos_of_nonneg hsp (mul_nonneg ht.le (sub_nonneg.mpr hs.2))

lemma eulerStep_continuousOn {t : ℝ} (ht : 0 < t) :
    ContinuousOn (eulerStep t) (Icc (0:ℝ) 1) := by
  apply continuousOn_id.div (continuousOn_id.add
    (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
  intro s hs
  exact (eulerStep_denom_pos ht hs).ne'

lemma eulerStep_of_pos (t : ℝ) {s : ℝ} (hs : 0 < s) :
    eulerStep t s = (1+t*(s⁻¹-1))⁻¹ := by
  rw [eulerStep]
  field_simp

lemma eulerStep_half_sq {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    (eulerStep (t/2) s)^2 ≤ eulerStep t s := by
  rcases hs.1.eq_or_lt with hsz | hsp
  · simp [← hsz, eulerStep]
  rw [eulerStep_of_pos (t/2) hsp, eulerStep_of_pos t hsp, inv_pow]
  have hr : 0 ≤ s⁻¹-1 := by
    have h := (one_le_inv₀ hsp).mpr hs.2
    linarith
  have hp : 0 < 1 + t*(s⁻¹-1) := by positivity
  have hp2 : 0 < (1+(t/2)*(s⁻¹-1))^2 := by positivity
  rw [inv_le_inv₀ hp2 hp]
  nlinarith [sq_nonneg ((t/2)*(s⁻¹-1))]

lemma eulerApproximation_antitone {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    Antitone (fun n => eulerApproximation t n s) := by
  apply antitone_nat_of_succ_le
  intro n
  have hn : 0 < t/(2:ℝ)^n := by positivity
  have H := eulerStep_half_sq hn hs
  have Hp := pow_le_pow_left₀ (sq_nonneg (eulerStep ((t/(2:ℝ)^n)/2) s)) H (2^n)
  dsimp [eulerApproximation]
  rw [pow_succ, ← div_div, Nat.pow_succ, mul_comm (2^n) 2, pow_mul]
  exact Hp

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_EulerStepGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma eulerStep_generator_eq {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    s*(eulerStep t s-t⁻¹*(eulerStep t s-1)) = eulerStep t s := by
  have hd := (eulerStep_denom_pos ht hs).ne'
  dsimp [eulerStep]
  field_simp
  ring

lemma cfc_eulerStep_eq {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) :
    R*(cfc (eulerStep t) R-(t⁻¹ : ℂ) • (cfc (eulerStep t) R-1)) = cfc (eulerStep t) R := by
  have hc : ContinuousOn (eulerStep t) (spectrum ℝ R) :=
    (eulerStep_continuousOn ht).mono fun _ hs => resolvent_spectrum_bounds hR hR1 hs
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  have hf : ContinuousOn (fun s => eulerStep t s-t⁻¹*(eulerStep t s-1)) (spectrum ℝ R) :=
    hc.sub (continuousOn_const.mul (hc.sub continuousOn_const))
  have he : cfc (fun s => s*(eulerStep t s-t⁻¹*(eulerStep t s-1))) R = cfc (eulerStep t) R :=
    cfc_congr fun s hs => eulerStep_generator_eq ht (resolvent_spectrum_bounds hR hR1 hs)
  rw [cfc_mul (fun s : ℝ => s) _ R continuous_id.continuousOn hf, hid,
    cfc_sub (eulerStep t) (fun s => t⁻¹*(eulerStep t s-1)) R hc (continuousOn_const.mul (hc.sub continuousOn_const))] at he
  have hsm : cfc (fun s => t⁻¹*(eulerStep t s-1)) R = t⁻¹ • cfc (fun s => eulerStep t s-1) R :=
    cfc_smul t⁻¹ _ _ (hc.sub continuousOn_const)
  rw [hsm, cfc_sub (eulerStep t) (fun _ => 1) R hc continuousOn_const,
    cfc_const 1 R hR.isSelfAdjoint, map_one] at he
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at he
  change R * (cfc (eulerStep t) R - Complex.ofReal (t⁻¹) • (cfc (eulerStep t) R - 1)) = _ at he
  simpa only [Complex.ofReal_inv] using he

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ReLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology


namespace WeakHessianFunctional

section QuadraticScaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : E → ℝ≥0∞}
variable [CompleteSpace E]

omit [CompleteSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma ClosedQuadraticEnergy.scale_lt_top_iff {t : ℝ} (ht : 0 < t) (u : E) :
    ENNReal.ofReal t * Q u < ∞ ↔ Q u < ∞ := by
  rw [ENNReal.mul_lt_top_iff]
  simp only [ENNReal.ofReal_lt_top, true_and, ENNReal.ofReal_eq_zero,
    not_le.mpr ht, false_or]
  constructor
  · rintro (hu | hu)
    · exact hu
    · simp [hu]
  · exact Or.inl

end QuadraticScaling

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

variable {X : Type*} [MeasurableSpace X] (m : Measure X)

def reLp : Lp ℂ 2 m →L[ℝ] Lp ℝ 2 m := Complex.reCLM.compLpL 2 m
def ofRealLp : Lp ℝ 2 m →L[ℝ] Lp ℂ 2 m := Complex.ofRealCLM.compLpL 2 m

lemma reLp_ae (f : Lp ℂ 2 m) : reLp m f =ᵐ[m] fun x => (f x).re :=
  Complex.reCLM.coeFn_compLpL f
lemma ofRealLp_ae (f : Lp ℝ 2 m) : ofRealLp m f =ᵐ[m] fun x => (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

@[simp] lemma re_ofRealLp (f : Lp ℝ 2 m) : reLp m (ofRealLp m f) = f := by
  apply Lp.ext
  filter_upwards [reLp_ae m (ofRealLp m f), ofRealLp_ae m f] with x hr hf
  simp [hr,hf]

local instance instAlgebraRealContinuousLinearMapComplexIdSubtypeAEEqFunMemAddSubgroupLpOfNatENNReal_solutions : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal

end WeakHessianFunctional

open Set Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ComplexifyReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
local instance instAlgebraRealContinuousLinearMapComplexIdSubtypeAEEqFunMemAddSubgroupLpOfNatENNReal_solutions_2 : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ExpNegQuadraticBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
lemma exp_neg_quadratic_bound {r : ℝ} (hr : 0 ≤ r) :
    Real.exp (-r) ≤ 1-r+r^2/2 := by
  let f : ℝ → ℝ := fun x => 1-x+x^2/2-Real.exp (-x)
  have hd (x : ℝ) : HasDerivAt f (-1+x+Real.exp (-x)) x := by
    have h := (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 2)).sub
      (Real.hasDerivAt_exp (-x) |>.comp x (hasDerivAt_id x).neg)
    convert h using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hm : Monotone f := monotone_of_hasDerivAt_nonneg hd (by
    intro x
    have h := Real.add_one_le_exp (-x)
    change 0 ≤ -1+x+Real.exp (-x)
    linarith)
  have h := hm hr
  simp only [f, sub_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div,
    add_zero, neg_zero, Real.exp_zero, sub_self] at h
  linarith

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatInverseSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma positive_contraction_norm {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) : ‖R‖ ≤ 1 := by
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg R
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hR)).mpr
    ((ContinuousLinearMap.le_def _ _).mpr hR1)

lemma resolvent_minus_id_bound {R : H →L[ℂ] H} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (u v : H) :
    dist (R u-u) (R v-v) ≤ 2*dist u v := by
  simp only [dist_eq_norm]
  have he : (R u-u)-(R v-v) = R (u-v)-(u-v) := by simp only [map_sub]; abel
  rw [he]
  calc
    _ ≤ ‖R (u-v)‖+‖u-v‖ := norm_sub_le _ _
    _ ≤ ‖R‖*‖u-v‖+‖u-v‖ := add_le_add (ContinuousLinearMap.le_opNorm R (u-v)) le_rfl
    _ ≤ 1*‖u-v‖+‖u-v‖ := by gcongr; exact positive_contraction_norm hR hR1
    _ = _ := by ring

def heatInverseSymbol (t s : ℝ) : ℝ :=
  (Real.exp t / t) * ((s/t)⁻¹ * expNegInvGlue (s/t))

lemma resolventHeat_commute_resolvent {R : H →L[ℂ] H} (hR : R.IsPositive) (t : ℝ) :
    Commute (resolventHeat R t) R := by
  have h := cfc_commute_cfc (heatSymbol t) (fun s : ℝ => s) R
  have hid : cfc (fun s : ℝ => s) R = R := cfc_id ℝ R hR.isSelfAdjoint
  rwa [hid] at h

lemma resolventHeat_resolvent {R : H →L[ℂ] H} (hR : R.IsPositive) (t : ℝ) (u : H) :
    resolventHeat R t (R u) = R (resolventHeat R t u) :=
  congrArg (fun T : H →L[ℂ] H => T u) (resolventHeat_commute_resolvent hR t).eq

end WeakHessianFunctional

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_PolarAddFourParallelograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
lemma polar_add_of_four_parallelograms {E : Type*} [AddCommGroup E]
    (q : E → ℝ) (x y z : E)
    (h₁ : q ((x+z)+y) + q ((x+z)-y) = 2*q (x+z)+2*q y)
    (h₂ : q ((x-z)+y) + q ((x-z)-y) = 2*q (x-z)+2*q y)
    (h₃ : q ((y+z)+x) + q ((y+z)-x) = 2*q (y+z)+2*q x)
    (h₄ : q ((y-z)+x) + q ((y-z)-x) = 2*q (y-z)+2*q x)
    (hn₁ : q (-(x-y-z)) = q (x-y-z))
    (hn₂ : q (-(x-y+z)) = q (x-y+z)) :
    (q ((x+y)+z)-q ((x+y)-z))/4 =
      (q (x+z)-q (x-z))/4 + (q (y+z)-q (y-z))/4 := by
  have e₁ : (x+z)+y = (x+y)+z := by abel
  have e₂ : (x+z)-y = x-y+z := by abel
  have e₃ : (x-z)+y = (x+y)-z := by abel
  have e₄ : (x-z)-y = x-y-z := by abel
  have e₅ : (y+z)+x = (x+y)+z := by abel
  have e₆ : (y+z)-x = -(x-y-z) := by abel
  have e₇ : (y-z)+x = (x+y)-z := by abel
  have e₈ : (y-z)-x = -(x-y+z) := by abel
  rw [e₁,e₂] at h₁
  rw [e₃,e₄] at h₂
  rw [e₅,e₆,hn₁] at h₃
  rw [e₇,e₈,hn₂] at h₄
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_LocalGradientParallelogram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

def LocalGradientParallelogram (m : Measure X) : Prop :=
  ∀ f g : X → ℝ, LocalSobolev m f → LocalSobolev m g →
    ∀ᵐ x ∂m, (weakGradient m (fun y => f y+g y) x)^2 +
      (weakGradient m (fun y => f y-g y) x)^2 =
      2*(weakGradient m f x)^2 + 2*(weakGradient m g x)^2

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_AeDerivLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian

lemma ae_deriv_zero_on_level (q : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ t ∂volume, DifferentiableAt ℝ q t → q t = c → deriv q t = 0 := by
  let s : Set ℝ := {t | q t = c}
  let e : Set ℝ := {t ∈ s | 𝓝[s ∩ Ioi t] t = ⊥}
  have he : e.Countable := countable_setOfPred_isolated_right_within
  have hne : ∀ᵐ t ∂volume, t ∉ e := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using he.measure_zero volume
  filter_upwards [hne] with t ht hdiff hqt
  have hright : (𝓝[s ∩ Ioi t] t).NeBot := by
    rw [neBot_iff]
    exact fun h => ht ⟨hqt,h⟩
  have hacc : AccPt t (𝓟 s) := by
    rw [accPt_principal_iff_nhdsWithin]
    apply hright.mono (nhdsWithin_mono t ?_)
    rintro y ⟨hy,hty⟩
    exact ⟨hy,ne_of_gt hty⟩
  have hzero : HasDerivWithinAt q 0 s t :=
    (hasDerivWithinAt_const t s c).congr (fun _ hx => hx) hqt
  exact (hdiff.hasDerivAt.hasDerivWithinAt.derivWithin hacc.uniqueDiffWithinAt).symm.trans
    (hzero.derivWithin hacc.uniqueDiffWithinAt)

lemma ae_deriv_eq_on_eq (q r : ℝ → ℝ) :
    ∀ᵐ t ∂volume, DifferentiableAt ℝ q t → DifferentiableAt ℝ r t →
      q t = r t → deriv q t = deriv r t := by
  filter_upwards [ae_deriv_zero_on_level (q-r) 0] with t ht hq hr heq
  have hz := ht (hq.sub hr) (by simp only [Pi.sub_apply, heq, sub_self])
  rwa [deriv_sub hq hr, sub_eq_zero] at hz

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_GradientPairSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

def gradientPairSum (m : Measure X) (f g : X → ℝ) (x : X) : ℝ :=
  weakGradient m (fun y => f y + g y) x ^ 2 +
  weakGradient m (fun y => f y - g y) x ^ 2

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_GradientParallelogramDefect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma lipschitz_inv_of_one_le {η : X → ℝ} {L : ℝ≥0}
    (hη : LipschitzWith L η) (h1 : ∀ x, 1 ≤ η x) :
    LipschitzWith L (fun x => (η x)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : 0 < η x := lt_of_lt_of_le zero_lt_one (h1 x)
  have hy : 0 < η y := lt_of_lt_of_le zero_lt_one (h1 y)
  have he : (η x)⁻¹ - (η y)⁻¹ = (η y - η x)/(η x*η y) := by
    field_simp
  rw [Real.dist_eq, he, abs_div, abs_of_pos (mul_pos hx hy)]
  calc
    _ ≤ |η y - η x| := div_le_self (abs_nonneg _) (one_le_mul_of_one_le_of_one_le (h1 x) (h1 y))
    _ = dist (η x) (η y) := by rw [Real.dist_eq, abs_sub_comm]
    _ ≤ _ := hη.dist_le_mul x y

def gradientParallelogramDefect (m : Measure X) (f g : X → ℝ) (x : X) : ℝ :=
  (weakGradient m (fun y => f y+g y) x)^2 +
    (weakGradient m (fun y => f y-g y) x)^2 -
    2*(weakGradient m f x)^2 - 2*(weakGradient m g x)^2

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_MulBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable



open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology


namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma LocallyL2.memLp_of_zero_outside_ball {f : X → ℝ} (hf : LocallyL2 m f)
    {o : X} {R : ℝ} (hR : 0 < R) (hz : ∀ᵐ x ∂m, x ∉ Metric.ball o R → f x = 0) :
    MemLp f 2 m := by
  have H := (memLp_indicator_iff_restrict measurableSet_ball).mpr (hf o R hR)
  apply H.ae_eq
  filter_upwards [hz] with x hx
  by_cases hmem : x ∈ Metric.ball o R
  · exact indicator_of_mem hmem f
  · rw [indicator_of_notMem hmem,hx hmem]

end WeakHessian

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_IntegralExponentialMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_exponentialMeasure {V : X → ℝ} (hV : AEMeasurable V m) (f : X → ℝ) :
    (∫ x, f x ∂exponentialMeasure m V) = ∫ x, Real.exp (V x)*f x ∂m := by
  have H := integral_withDensity_eq_integral_toReal_smul₀
    (Real.measurable_exp.comp_aemeasurable hV).ennreal_ofReal
    (ae_of_all m fun _ => ENNReal.ofReal_lt_top) f
  simpa only [exponentialMeasure,Function.comp_apply,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_ExpMulLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma sq_exp_eq (r : ℝ) : (Real.exp r)^2 = Real.exp (2*r) := by
  rw [pow_two,← Real.exp_add,two_mul]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_MinNatTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma min_nat_tendsto (v : ℝ) : Tendsto (fun n : ℕ => min v (n:ℝ)) atTop (𝓝 v) := by
  obtain ⟨k,hk⟩ := exists_nat_ge v
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (min_eq_left (hk.trans (by exact_mod_cast hn))).symm

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_RadialCutoffLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integrable_of_memLp_mul_exp {V f : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hV : MemLp (fun x => Real.exp (-V x)) 2 m) : Integrable f m := by
  apply (hf.integrable_mul hV).congr
  exact ae_of_all _ fun x => by
    change (f x*Real.exp (V x))*Real.exp (-V x) = f x
    rw [mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_CcConst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

namespace WeakHessianTransport
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y]

def ccConst (X : Type*) [TopologicalSpace X] [CompactSpace X] (r : ℝ) : C_c(X,ℝ) :=
  ⟨ContinuousMap.const X r, HasCompactSupport.of_compactSpace _⟩

@[simp] lemma ccConst_apply (r : ℝ) (x : X) : ccConst X r x = r := rfl

def marginalSum : (C_c(X,ℝ) × C_c(Y,ℝ)) →ₗ[ℝ] C_c(X×Y,ℝ) where
  toFun fg := ⟨⟨fun p => fg.1 p.1+fg.2 p.2, by fun_prop⟩,
    HasCompactSupport.of_compactSpace _⟩
  map_add' a b := by
    ext p
    change (a.1 p.1+b.1 p.1)+(a.2 p.2+b.2 p.2) = (a.1 p.1+a.2 p.2)+(b.1 p.1+b.2 p.2)
    ring
  map_smul' r a := by
    ext p
    change r*a.1 p.1+r*a.2 p.2 = r*(a.1 p.1+a.2 p.2)
    ring

@[simp] lemma marginalSum_apply (fg : C_c(X,ℝ) × C_c(Y,ℝ)) (p : X×Y) :
    marginalSum fg p = fg.1 p.1 + fg.2 p.2 := rfl

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

def marginalIntegral (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (C_c(X,ℝ) × C_c(Y,ℝ)) →ₗ[ℝ] ℝ :=
  (integralPositiveLinearMap μ).toLinearMap.comp (LinearMap.fst ℝ _ _) +
    (integralPositiveLinearMap ν).toLinearMap.comp (LinearMap.snd ℝ _ _)

@[simp] lemma marginalIntegral_apply (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (fg : C_c(X,ℝ) × C_c(Y,ℝ)) :
    marginalIntegral μ ν fg = (∫ x, fg.1 x ∂μ) + ∫ y, fg.2 y ∂ν := rfl

end WeakHessianTransport

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_QuadraticCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open scoped NNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology

open Set Filter
open scoped Topology ENNReal NNReal


namespace WeakHessianTransport
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

def quadraticCost (t : ℝ) : C_c(X×X,ℝ) :=
  ⟨⟨fun p => dist p.1 p.2 ^ 2 / (2*t), by fun_prop⟩,
    HasCompactSupport.of_compactSpace _⟩

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma quadraticCost_apply (t : ℝ) (p : X×X) :
    quadraticCost t p = dist p.1 p.2 ^ 2 / (2*t) := rfl

end WeakHessianTransport

open Set

end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_DecayCutoffLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integral_mul_le_weighted {V f η : X → ℝ}
    (hf : MemLp (fun x => f x*Real.exp (V x)) 2 m)
    (hη : MemLp (fun x => Real.exp (-V x)*η x) 2 m) :
    ‖∫ x, f x*η x ∂m‖ ≤
      ‖hf.toLp (fun x => f x*Real.exp (V x))‖*
      ‖hη.toLp (fun x => Real.exp (-V x)*η x)‖ := by
  let U := hf.toLp (fun x => f x*Real.exp (V x))
  let W := hη.toLp (fun x => Real.exp (-V x)*η x)
  have he : (∫ x, f x*η x ∂m) = ⟪U,W⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hη.coeFn_toLp] with x hu hw
    dsimp only [U,W]
    rw [hu,hw]
    simp only [RCLike.inner_apply,conj_trivial]
    calc f x*η x = f x*(Real.exp (V x)*Real.exp (-V x))*η x := by
           rw [← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
         _ = _ := by ring
  rw [he]
  exact norm_inner_le_norm _ _

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_DistDecayCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma exp_geometric_bound_eq (M C a : ℝ) (n : ℕ) :
    Real.exp (-a*(n:ℝ))*(M*Real.exp (C*((n:ℝ)+1))) =
      M*Real.exp C*(Real.exp (C-a))^n := by
  calc
    _ = M*(Real.exp (-a*(n:ℝ))*Real.exp (C*((n:ℝ)+1))) := by ring
    _ = M*Real.exp (-a*(n:ℝ)+C*((n:ℝ)+1)) := by rw [Real.exp_add]
    _ = M*Real.exp (C+(n:ℝ)*(C-a)) := by congr 2; ring
    _ = M*Real.exp C*Real.exp ((n:ℝ)*(C-a)) := by rw [Real.exp_add]; ring
    _ = _ := by rw [Real.exp_nat_mul]

noncomputable def distDecayCover (o : X) (a : ℝ) (n : ℕ) : X → ℝ≥0∞ :=
  (Metric.ball o ((n:ℝ)+1)).indicator (fun _ => ENNReal.ofReal (Real.exp (-a*(n:ℝ))))

lemma measurable_distDecayCover (o : X) (a : ℝ) (n : ℕ) : Measurable (distDecayCover o a n) :=
  measurable_const.indicator Metric.isOpen_ball.measurableSet

omit [MeasurableSpace X] [BorelSpace X] in
lemma exp_neg_dist_le_cover (o : X) {a : ℝ} (ha : 0 ≤ a) (x : X) :
    ENNReal.ofReal (Real.exp (-a*dist x o)) ≤ ∑' n, distDecayCover o a n x := by
  let n := ⌊dist x o⌋₊
  have hn : (n:ℝ) ≤ dist x o := Nat.floor_le dist_nonneg
  have hx : x ∈ Metric.ball o ((n:ℝ)+1) :=
    Metric.mem_ball.mpr (Nat.lt_floor_add_one (dist x o))
  calc
    _ ≤ distDecayCover o a n x := by
      simp only [distDecayCover,Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
    _ ≤ _ := ENNReal.le_tsum (f := fun index => distDecayCover o a index x) n

lemma lintegral_distDecayCover_le (o : X) {M C a : ℝ}
    (hvol : ∀ n : ℕ, m (Metric.ball o (n:ℝ)) ≤ ENNReal.ofReal (M*Real.exp (C*(n:ℝ)))) (n : ℕ) :
    (∫⁻ x, distDecayCover o a n x ∂m) ≤ ENNReal.ofReal (M*Real.exp C*(Real.exp (C-a))^n) := by
  have H := hvol (n+1)
  simp only [Nat.cast_add,Nat.cast_one] at H
  calc
    _ = ENNReal.ofReal (Real.exp (-a*(n:ℝ)))*m (Metric.ball o ((n:ℝ)+1)) := by
      simp only [distDecayCover,lintegral_indicator Metric.isOpen_ball.measurableSet,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (Real.exp (-a*(n:ℝ)))*ENNReal.ofReal (M*Real.exp (C*((n:ℝ)+1))) :=
      mul_le_mul_right H _
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,exp_geometric_bound_eq]

lemma integrable_exp_neg_dist_of_growth (o : X) {M C a : ℝ} (_hM : 0 ≤ M)
    (ha : 0 ≤ a) (hCa : C < a)
    (hvol : ∀ n : ℕ, m (Metric.ball o (n:ℝ)) ≤ ENNReal.ofReal (M*Real.exp (C*(n:ℝ)))) :
    Integrable (fun x => Real.exp (-a*dist x o)) m := by
  have hs : Summable (fun n : ℕ => M*Real.exp C*(Real.exp (C-a))^n) :=
    (summable_geometric_of_norm_lt_one (show ‖Real.exp (C-a)‖ < 1 by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]; linarith)).mul_left (M*Real.exp C)
  refine ⟨(Real.continuous_exp.comp (continuous_const.mul (continuous_id.dist continuous_const))).aestronglyMeasurable, ?_⟩
  change (∫⁻ x, ‖Real.exp (-a*dist x o)‖ₑ ∂m) < ∞
  simp only [Real.enorm_eq_ofReal (Real.exp_pos _).le]
  calc
    _ ≤ ∫⁻ x, ∑' n, distDecayCover o a n x ∂m := lintegral_mono (exp_neg_dist_le_cover o ha)
    _ = ∑' n, ∫⁻ x, distDecayCover o a n x ∂m :=
      lintegral_tsum (fun n => (measurable_distDecayCover o a n).aemeasurable)
    _ ≤ ∑' n, ENNReal.ofReal (M*Real.exp C*(Real.exp (C-a))^n) :=
      ENNReal.tsum_le_tsum (lintegral_distDecayCover_le o hvol)
    _ < ∞ := hs.tsum_ofReal_lt_top

lemma memLp_exp_neg_dist_of_growth (o : X) {M C a : ℝ} (hM : 0 ≤ M)
    (ha : 0 ≤ a) (hCa : C < 2*a)
    (hvol : ∀ n : ℕ, m (Metric.ball o (n:ℝ)) ≤ ENNReal.ofReal (M*Real.exp (C*(n:ℝ)))) :
    MemLp (fun x => Real.exp (-a*dist x o)) 2 m := by
  have hi := integrable_exp_neg_dist_of_growth o hM (by positivity : 0 ≤ 2*a) hCa hvol
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.dist continuous_const))).aestronglyMeasurable).mpr
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  change (Real.exp (-a*dist x o))^2 = Real.exp (-(2*a)*dist x o)
  rw [← Real.exp_nat_mul]
  congr 1; ring

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Curvature_DecayWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma memLp_exp_dist_of_support (u : Lp ℝ 2 m) {a : ℝ} (ha : 0 ≤ a)
    (o : X) {R : ℝ} (hR : ∀ᵐ x ∂m, R ≤ dist x o → u x = 0) :
    MemLp (fun x => u x*Real.exp (a*dist x o)) 2 m := by
  have H := (Lp.memLp u).const_mul (Real.exp (a*R))
  apply H.mono ((Lp.memLp u).aestronglyMeasurable.mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.dist continuous_const))).aestronglyMeasurable)
  filter_upwards [hR] with x hx
  change |u x*Real.exp (a*dist x o)| ≤ |Real.exp (a*R)*u x|
  rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
  by_cases hs : R ≤ dist x o
  · simp only [hx hs,abs_zero,mul_zero,zero_mul,le_refl]
  · rw [mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_not_ge hs) ha)) (abs_nonneg _)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_AscendingSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

def ascendingSlope (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  limsup (fun y => ENNReal.ofReal ((f y-f x)/dist y x)) (𝓝[≠] x)
def ascendingSlopeApprox (f : X → ℝ) (n : ℕ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist y x < 1/(n+1:ℝ)), ENNReal.ofReal ((f y-f x)/dist y x)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_EntropyContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile1
noncomputable section

noncomputable section
noncomputable section
namespace WeakHessianTransport
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

def lowerLipExtension (S : Set X) (f : S → ℝ) (D : ℝ≥0) (x : X) : ℝ :=
  ⨆ z : S, f z - D * dist x z

open WeakHessian

end WeakHessianTransport

end
end
end
end InlinedFile1

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_TruncatedLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal

noncomputable def truncatedLog (a x : ℝ) : ℝ := Real.log a + ∫ s in a..x, (max a s)⁻¹

lemma truncatedLog_hasDeriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (truncatedLog a) ((max a x)⁻¹) x := by
  have hc : Continuous (fun s : ℝ => (max a s)⁻¹) :=
    (continuous_const.max continuous_id).inv₀ (fun s => ne_of_gt (ha.trans_le (le_max_left _ _)))
  simpa only [truncatedLog] using! (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable _ _) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add (Real.log a)

lemma truncatedLog_deriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    deriv (truncatedLog a) x = (max a x)⁻¹ := (truncatedLog_hasDeriv ha x).deriv

lemma truncatedLog_deriv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |deriv (truncatedLog a) x| ≤ a⁻¹ := by
  rw [truncatedLog_deriv ha,abs_of_nonneg (inv_nonneg.mpr (ha.le.trans (le_max_left a x)))]
  exact inv_anti₀ ha (le_max_left _ _)

lemma truncatedLog_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith (⟨a⁻¹,inv_nonneg.mpr ha.le⟩ : ℝ≥0) (truncatedLog a) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (truncatedLog_hasDeriv ha x).differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  exact truncatedLog_deriv_bound ha x

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace

noncomputable def regularizedLog (a x : ℝ) : ℝ := truncatedLog a (x+a)-Real.log a
noncomputable def regularizedEntropy (a x : ℝ) : ℝ := ∫ s in 0..x, regularizedLog a s

lemma regularizedLog_zero (a : ℝ) : regularizedLog a 0 = 0 := by
  simp [regularizedLog,truncatedLog]
lemma regularizedLog_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith (⟨a⁻¹,inv_nonneg.mpr ha.le⟩ : ℝ≥0) (regularizedLog a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [regularizedLog,dist_sub_right,dist_add_right] using
    (truncatedLog_lipschitz ha).dist_le_mul (x+a) (y+a)

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma regularizedLog_memLp {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) :
    MemLp (fun x => regularizedLog a (u x)) 2 m :=
  (regularizedLog_lipschitz ha).comp_memLp (regularizedLog_zero a) (Lp.memLp u)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ZeroDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile3
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def squareDensityMeasure (n : Measure X) (w : X → ℝ) : Measure X :=
  n.withDensity (fun x => ENNReal.ofReal (w x ^ 2))

def squareLogFloor (a : ℝ) (w : X → ℝ) (x : X) : ℝ :=
  2*(regularizedLog a (w x)+Real.log a)

noncomputable def squareLogFloorBCF {a : ℝ} (ha : 0 < a) (w : X →ᵇ ℝ) : X →ᵇ ℝ :=
  (2:ℝ) • (BoundedContinuousFunction.comp (regularizedLog a) (regularizedLog_lipschitz ha) w +
    BoundedContinuousFunction.const X (Real.log a))

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma squareLogFloorBCF_apply {a : ℝ} (ha : 0 < a) (w : X →ᵇ ℝ) (x : X) :
    squareLogFloorBCF ha w x = squareLogFloor a w x := by rfl

end WeakHessian

end
end InlinedFile3

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_DensityConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile8
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

def squareDensityProbability (m : Measure X) (w : X → ℝ)
    (h : IsProbabilityMeasure (squareDensityMeasure m w)) : ProbabilityMeasure X :=
  ⟨squareDensityMeasure m w,h⟩

end WeakHessian

end
end InlinedFile8

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FisherDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

def fisherDensity (u : X → ℝ) (x : X) : ℝ := (weakGradient m u x)^2/u x

end WeakHessian
end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_RenormalizedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology

noncomputable def renormalizedEntropy (a x : ℝ) : ℝ :=
  regularizedEntropy a x+Real.log a*x

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_IntegrableFatouNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integrable_fatou_nonneg {f : X → ℝ} (hf : AEStronglyMeasurable f m)
    (hpos : ∀ᵐ x ∂m, 0 ≤ f x) {fs : ℕ → X → ℝ}
    (hfs : ∀ n, Integrable (fs n) m) (hfs0 : ∀ n, ∀ᵐ x ∂m, 0 ≤ fs n x)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    {B : ℝ} (hB : ∀ n, (∫ x, fs n x ∂m) ≤ B) :
    Integrable f m ∧ (∫ x,f x ∂m) ≤ B := by
  have H : (∫⁻ x, ENNReal.ofReal (f x) ∂m) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (fs n x)) atTop ∂m := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (fs n x) ∂m) atTop :=
        lintegral_liminf_le' (fun n => ENNReal.continuous_ofReal.measurable.comp_aemeasurable (hfs n).1.aemeasurable)
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le'
        apply Frequently.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hfs n) (hfs0 n)]
        exact ENNReal.ofReal_le_ofReal (hB n)
  have hi : Integrable f m := by
    refine ⟨hf, ?_⟩
    change (∫⁻ x, ‖f x‖ₑ ∂m) < ∞
    have he : (fun x => ‖f x‖ₑ) =ᵐ[m] (fun x => ENNReal.ofReal (f x)) :=
      hpos.mono fun x hx => Real.enorm_eq_ofReal hx
    rw [lintegral_congr_ae he]
    exact H.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi,?_⟩
  have hB0 : 0 ≤ B := (integral_nonneg_of_ae (hfs0 0)).trans (hB 0)
  rw [integral_eq_lintegral_of_nonneg_ae hpos hf]
  simpa only [ENNReal.toReal_ofReal hB0] using ENNReal.toReal_mono ENNReal.ofReal_ne_top H

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FisherEpsilon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable def fisherEpsilon (n : ℕ) : ℝ := 1/((n:ℝ)+1)
end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_FisherRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile45
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

def regularizedRoot (a x : ℝ) : ℝ := ∫ s in 0..x, (2*Real.sqrt (max a (s+a)))⁻¹

end WeakHessian

end
end InlinedFile45

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_ReducedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable def reducedEntropy (x : ℝ) : ℝ := x*Real.log x-x

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Entropy_SmoothDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]

 def kernelMeasure (κ : ℝ → ℝ) : Measure ℝ := volume.withDensity (fun r => ENNReal.ofReal (κ r))

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Geodesics_MidpointDualTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X]

def midpointDualTest (o : X) (R : ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max (R^2-dist x o^2) 0/2) (by fun_prop) (R^2/2) (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (max_le (by nlinarith [sq_nonneg (dist x o)]) (sq_nonneg R)) (by norm_num))

@[simp] lemma midpointDualTest_apply (o : X) (R : ℝ) (x : X) :
    midpointDualTest o R x = max (R^2-dist x o^2) 0/2 := rfl

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_QuadraticGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile26
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

def QuadraticLipschitzBound (o : X) (R : ℝ) (f : X → ℝ) : Prop :=
  ∀ x z, |f x-f z| ≤ ((dist x o+dist z o)/2+R)*dist x z

end WeakHessian

end
end InlinedFile26

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_QuadraticPotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile25
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

def compactCTransform (S : Set X) (ψ : X → ℝ) (x : X) : ℝ :=
  sInf ((fun y => dist x y^2/2-ψ y) '' S)

end WeakHessian

end
end InlinedFile25

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_RootApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile6
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

def rootClip (B : ℝ) (r : ℝ) : ℝ := max 0 (min B r)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

section

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

def rootCutoff (o : X) (R : ℝ) (x : X) : ℝ := rootClip 1 (R+2-dist x o)

end

end WeakHessian

end
end InlinedFile6

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_HeatCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile48
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

def quadraticWassersteinSq (μ ν : Measure X) : ℝ :=
  (⨅ q : Measure (X×X), ⨅ _ : IsCoupling q μ ν, QuadraticTransportCost q).toReal

end WeakHessian

end
end InlinedFile48

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_SetDensities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile76
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

def setDensity (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) : Lp ℝ 2 m :=
  (memLp_indicator_const 2 hS ((m S).toReal⁻¹) (Or.inr hfin)).toLp _

end WeakHessian

end
end InlinedFile76

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_PositiveProbes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile92
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

variable [MetricSpace X]

variable (o : X) {a : ℝ} (ha : 0 < a)
variable (hw : MemLp (fun x => Real.exp (-(a*dist x o))) 2 m)

def positiveProbe (u : Lp ℝ 2 m) (ε : ℝ) : Lp ℝ 2 m :=
  u+ε • hw.toLp (fun x => Real.exp (-(a*dist x o)))

end WeakHessian

end
end InlinedFile92

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_CoreAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile110
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def integratedBochner (m : Measure X) (g ξ : X → ℝ) : ℝ :=
  -(∫ x, gamma m ξ (fun y => gamma m g g y/2) x ∂m) +
    ∫ x, (ξ x*laplacian m g x+gamma m ξ g x)*laplacian m g x ∂m

def driftBochner (m : Measure X) (V g ξ : X → ℝ) : ℝ :=
  -(∫ x, Real.exp (V x)*gamma m ξ (fun y => gamma m g g y/2) x ∂m) +
    ∫ x, Real.exp (V x)*(ξ x*(laplacian m g x+gamma m V g x)+gamma m ξ g x)*
      (laplacian m g x+gamma m V g x) ∂m

end WeakHessian

end
end InlinedFile110

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_EnergyIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile182
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable (hfin : FiniteOnBoundedSets m)
variable (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
  ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))

include hfin hID

omit hfin [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma identified_cheegerEnergy_toReal {f : X → ℝ} (hf : Sobolev m f) :
    (cheegerEnergy m f).toReal = (∫ x,(weakGradient m f x)^2 ∂m)/2 := by
  rw [hID f hf,ENNReal.toReal_ofReal (by positivity)]

end WeakHessian

end
end InlinedFile182

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_GraphReuse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile173
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

def graphBochner (m : Measure X) (u A ξ B : X → ℝ) : ℝ :=
  (1/2)*(∫ x, B x*gamma m u u x ∂m) +
    (∫ x, A x*gamma m ξ u x ∂m) + ∫ x, ξ x*(A x)^2 ∂m

end WeakHessian

end
end InlinedFile173

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_FormAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

def FormActionBound (m : Measure X) (ρ : X → ℝ) (v : Lp ℝ 2 m) (A : ℝ) : Prop :=
  ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
    2 * ⟪v,f⟫_ℝ ≤ A + ∫ x, ρ x * (weakGradient m f x)^2 ∂m

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_HeatFlow_PlanHeatEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

def backwardsHeatTime (δ T s : ℝ) : ℝ := δ+T*max (1-s) 0

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LocalizedCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def localizedHeatM (K a CG T : ℝ) : ℝ := Real.exp (2*(|K|+a*CG)*T)
def localizedHeatDen (K a c CG T : ℝ) : ℝ := 1+2*max (-(K-a*c)) 0*T*localizedHeatM K a CG T
def localizedHeatFactor (K a c CG T : ℝ) : ℝ :=
  (1+2*max (K-a*c) 0*T/localizedHeatM K a CG T)/localizedHeatDen K a c CG T

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_DaviesTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma tail_exp_weight (o : X) {c β R : ℝ} (hcβ : c ≤ β)
    (hd : MemLp (fun x => Real.exp (-c*dist x o)) 2 m) :
    MemLp (fun x => Real.exp (-(β*dist x o))*
      (Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o)) 2 m := by
  let C := Real.exp (-(β-c)*R)
  have hm : Measurable (fun x : X => (Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o)) :=
    (measurable_const.indicator measurableSet_Ici).comp (continuous_id.dist continuous_const).measurable
  apply (hd.const_mul C).mono
    ((show Continuous (fun x : X => Real.exp (-(β*dist x o))) by fun_prop).aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    change |Real.exp (-(β*dist x o))*(Ici R).indicator (fun _ : ℝ => (1:ℝ)) (dist x o)| ≤
      |C*Real.exp (-c*dist x o)|
    by_cases hR : R ≤ dist x o
    · rw [indicator_of_mem (show dist x o ∈ Ici R from hR),mul_one,abs_of_pos (Real.exp_pos _),abs_of_pos (by dsimp [C]; positivity)]
      dsimp [C]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hcβ) (sub_nonneg.mpr hR)]
    · rw [indicator_of_notMem (show dist x o ∉ Ici R from hR),mul_zero,abs_zero]
      exact abs_nonneg _

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_CurvatureTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

def curvatureTailBound (K a c CG U Lf Q d β R r : ℝ) : ℝ :=
  2*a*U*(CG+|c|)*localizedHeatM K a CG U*Lf^2*Q*Real.exp (β^2*U-β*(R-r)+d*R)

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LocalizedActionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology

def localizedActionBound (K a c CG T : ℝ) : ℝ :=
  1-(K-a*c)*T+2*|K-a*c| *T*(localizedHeatM K a CG T-1)+4*(K-a*c)^2*T^2

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_LocalizedScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter
open scoped Topology

def localActionLimit (c CG s : ℝ) : ℝ :=
  1+c*s+2*|c| *s*(Real.exp (2*CG*s)-1)+4*c^2*s^2

end WeakHessian

end
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_PerturbedPlanDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

def hopfUniformLip (f : X →ᵇ ℝ) (q : ℝ) : ℝ :=
  Real.sqrt (4*(q+1)*‖f‖)/q+1/(2*q)+2*‖f‖

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma hopfUniformLip_nonneg (f : X →ᵇ ℝ) {q : ℝ} (hq : 0 < q) : 0 ≤ hopfUniformLip f q := by
  dsimp [hopfUniformLip]; positivity

end WeakHessian

end
end

end OAI
end


