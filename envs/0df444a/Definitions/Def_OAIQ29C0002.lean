-- Prove2me | Definitions.Def_OAIQ29C0002
-- name    : OAIQ29C0002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:47:09.060652+00:00
-- url     : https://prove2.me/theorems/63a0b5a0-8c1c-4f95-9178-8e141048ff78
-- title:
--   Definitions bundle OAIQ29C0002 of the split of OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 224 declarations of OpenAI's Lean: 47 definitions, 3 instances and 174 theorems. The definitions and types are `OAI.CAT0Fillings.ChartGeometry.isolatedL1`, `OAI.CAT0Fillings.ChartGeometry.pairing`, `OAI.CAT0Fillings.ChartGeometry.radialA`, `OAI.CAT0Fillings.ChartGeometry.radialB`, `OAI.CAT0Fillings.ChartGeometry.radialDefect`, `OAI.CAT0Fillings.ChartGeometry.radialNormSq`, `OAI.CAT0Fillings.ChartGeometry.radialPowerIntegrand`, `OAI.CAT0Fillings.ChartGeometry.radialVariation`, `OAI.CAT0Fillings.ChartGeometry.radialVariationChart`, `OAI.CAT0Fillings.ChartGeometry.spatialMass`, `OAI.CAT0Fillings.ChartGeometry.sweptMass`, `OAI.CAT0Fillings.ChartGeometry.testWeight`, `OAI.CAT0Fillings.ChartGeometry.value1`, `OAI.CAT0Fillings.ChordMeasure.probability`, `OAI.CAT0Fillings.CurrentOperations.pushCurrent`, `OAI.CAT0Fillings.Foundations.UnitTestClass`, `OAI.CAT0Fillings.IntegerChart.closedPrism`, `OAI.CAT0Fillings.IntegerChart.coordinateDomain`, `OAI.CAT0Fillings.IntegerChart.coordinateLayer`, `OAI.CAT0Fillings.IntegerChart.coordinateParam`, `OAI.CAT0Fillings.IntegerChart.coordinateSlice`, `OAI.CAT0Fillings.IntegerChart.coordinateSliceTotal`, `OAI.CAT0Fillings.IntegerChart.prism`, `OAI.CAT0Fillings.IntegerChart.prismDomain`, `OAI.CAT0Fillings.IntegerChart.prismParam`, `OAI.CAT0Fillings.IntegerChart.radialJacobian`, `OAI.CAT0Fillings.IntegerChart.sweptWeight`, `OAI.CAT0Fillings.IsMetricCurrent.fullMultilinear`, `OAI.CAT0Fillings.Prism.radialForm`, `OAI.CAT0Fillings.Prism.tail`, `OAI.CAT0Fillings.SliceReconstruction.TupleKernel`, `OAI.CAT0Fillings.SliceReconstruction.UnitRepresentation`, `OAI.CAT0Fillings.SliceReconstruction.atomDomain`, `OAI.CAT0Fillings.SliceReconstruction.jointGraphChart`, `OAI.CAT0Fillings.SliceReconstruction.jointGraphFunction`, `OAI.CAT0Fillings.SliceReconstruction.selectedAtom`, `OAI.CAT0Fillings.Slicing.fullSliceControl`, `OAI.CAT0Fillings.Slicing.parameterEquiv`, `OAI.CAT0Fillings.Slicing.projectedL1`, `OAI.CAT0Fillings.boundedLipSubmodule` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `CAT0Fillings_BV_JointPoincare`, `CAT0Fillings_Charts_ChainRule`, `CAT0Fillings_Charts_CurrentAxioms`, `CAT0Fillings_Charts_CurrentContinuity`, `CAT0Fillings_Charts_DomainRestriction`, `CAT0Fillings_Charts_ExactMass`, `CAT0Fillings_Charts_HilbertMass`, `CAT0Fillings_Charts_JacobianBound`, `CAT0Fillings_Charts_LinearMass`, `CAT0Fillings_Charts_MeasurePartition`, `CAT0Fillings_Charts_MultiplicityRestriction`, `CAT0Fillings_Charts_ScalarPieces`, `CAT0Fillings_Charts_StraightPieces`, `CAT0Fillings_Charts_Straightening`, `CAT0Fillings_Chord_NonnegativeMeasure`, `CAT0Fillings_Compactness_Atlas`, `CAT0Fillings_Compactness_Coordinates`, `CAT0Fillings_Currents_Addition`, `CAT0Fillings_Currents_AffineCalculus`, `CAT0Fillings_Currents_Contraction`, `CAT0Fillings_Currents_MassTests`, `CAT0Fillings_Currents_Negation`, `CAT0Fillings_Currents_Pushforward`, `CAT0Fillings_Currents_Summation`, `CAT0Fillings_Currents_WeakMeasures`, `CAT0Fillings_Density_InverseCutoff`, `CAT0Fillings_Differentiation_Centered`, `CAT0Fillings_Differentiation_Degenerate`, `CAT0Fillings_Differentiation_ErrorModulus`, `CAT0Fillings_Differentiation_FullRank`, `CAT0Fillings_Differentiation_HilbertCharts`, `CAT0Fillings_Differentiation_HilbertPartition`, `CAT0Fillings_Differentiation_LargePieces`, `CAT0Fillings_Differentiation_LocalBounds`, `CAT0Fillings_Differentiation_Parallelogram`, `CAT0Fillings_Differentiation_Partitions`, `CAT0Fillings_Differentiation_TwoPoint`, `CAT0Fillings_Euler_OppositePointwise`, `CAT0Fillings_Fillings_Attainment`, `CAT0Fillings_Fillings_WeightedCone`, `CAT0Fillings_Geometry_Determinant`, `CAT0Fillings_Geometry_MatrixRows`, `CAT0Fillings_Gradient_Determinant`, `CAT0Fillings_Gradient_Pairing`, `CAT0Fillings_Minimizers_SpatialVariation`, `CAT0Fillings_Prism_Chart`, `CAT0Fillings_Prism_ClosedCylinder`, `CAT0Fillings_Prism_ClosedFamily`, `CAT0Fillings_Prism_Family`, `CAT0Fillings_Prism_TimeAction`, `CAT0Fillings_Radial_ChartMass`, `CAT0Fillings_Radial_ClosedInequality`, `CAT0Fillings_Reconstruction_AtomGraphs`, `CAT0Fillings_Reconstruction_GraphCharts`, `CAT0Fillings_Reconstruction_Uniqueness`, `CAT0Fillings_Slices_FullSlices`, `CAT0Fillings_Slices_JointKernel`, `CAT0Fillings_Slices_Limits`, `CAT0Fillings_Slices_NormalBudget`, `CAT0Fillings_Slicing_CoordinateChart`, `CAT0Fillings_Slicing_CoordinateCoarea`, `CAT0Fillings_Slicing_CoordinateDerivative`, `CAT0Fillings_Slicing_CoordinateIntegral`, `CAT0Fillings_Slicing_EuclideanSplit`, `CAT0Fillings_Slicing_GeneralCoarea`, `CAT0Fillings_Slicing_IntegralBoundary`, `CAT0Fillings_Slicing_NormalRestriction`, `CAT0Fillings_Slicing_ProfileIntegral`, `CAT0Fillings_Slicing_Profiles`, `CAT0Fillings_Slicing_RectifiableCoarea`, `CAT0Fillings_Slicing_ScalarCoarea`, `CAT0Fillings_Slicing_Superlevels`, `CAT0Fillings_Sobolev_Constant`, `CAT0Fillings_Swept_Current`, `CAT0Fillings_Swept_RadialChart`, `CAT0Fillings_Variational_Extremizer`.
--
--   **Imports.** It imports the published bundle `Def_SharpCAT0Filling`; the bundles `OAIQ29C0000` and `OAIQ29C0001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.CAT0Fillings.ChartGeometry.chord_combined`, `OAI.CAT0Fillings.ChartGeometry.chord_energy`, `OAI.CAT0Fillings.ChartGeometry.chord_scalar_average`, `OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction`, `OAI.CAT0Fillings.ChartGeometry.opposite_all_center`, `OAI.CAT0Fillings.exists_filling_mass_eq`, `OAI.CAT0Fillings.extremal_closed_sobolev`, `OAI.CAT0Fillings.extremal_critical_minimizer`, `OAI.CAT0Fillings.extremal_euler_powers`, `OAI.CAT0Fillings.fillingVolume_le_two`, `OAI.CAT0Fillings.normalized_extremal_contradiction`, `OAI.CAT0Fillings.radial_inequality_of_extremal` and `OAI.CAT0Fillings.small_restriction_mass_bound`; the proofs of `OAI.CAT0Fillings.ChartGeometry.chord_combined`, `OAI.CAT0Fillings.ChartGeometry.chord_energy`, `OAI.CAT0Fillings.ChartGeometry.chord_scalar_average`, `OAI.CAT0Fillings.ChartGeometry.closed_added_tests`, `OAI.CAT0Fillings.ChartGeometry.closed_chord_product`, `OAI.CAT0Fillings.ChartGeometry.euler_chord_contradiction`, `OAI.CAT0Fillings.ChartGeometry.inclusion_compact`, `OAI.CAT0Fillings.ChartGeometry.opposite_all_center`, `OAI.CAT0Fillings.Slicing.exists_integral_weak_subsequence`, `OAI.CAT0Fillings.exists_filling_mass_eq`, `OAI.CAT0Fillings.extremal_closed_sobolev`, `OAI.CAT0Fillings.extremal_critical_minimizer`, `OAI.CAT0Fillings.extremal_euler_powers`, `OAI.CAT0Fillings.fillingVolume_le_two`, `OAI.CAT0Fillings.normalized_extremal_contradiction`, `OAI.CAT0Fillings.radial_inequality_of_extremal`, `OAI.CAT0Fillings.sharp_integral_filling` and `OAI.CAT0Fillings.small_restriction_mass_bound`.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0000
import Definitions.Def_OAIQ29C0001

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_CurrentContinuity
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal

namespace CAT0Fillings
namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma integrable_weight {b : X → ℝ} (hb : BoundedLip b) :
    Integrable (fun z => (C.multiplicity z : ℝ) * C.scalar b z)
      (volume.restrict C.domain) := by
  obtain ⟨K,hK⟩ := hb.1
  obtain ⟨M,hM⟩ := hb.2
  apply C.integrable.mul_bdd (C.measurable_scalar hK).aestronglyMeasurable
  filter_upwards [ae_restrict_mem C.borel] with z hz
  simpa [C.scalar_eq hz,Real.norm_eq_abs] using hM (C.param ⟨z,hz⟩)

lemma action_eq_extended_jacobian {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) {F : Fin k → Euc k → ℝ} {K : ℝ≥0}
    (hF : ∀ i, LipschitzWith K (F i))
    (heq : ∀ i, EqOn (C.scalar (π i)) (F i) C.domain) :
    C.action b π = ∫ z,
      C.domain.indicator (fun z => (C.multiplicity z : ℝ) * C.scalar b z) z *
        coordinateJacobian F (fun j => EuclideanSpace.single j 1) z := by
  rw [action,ite_eq_left h]
  have H := C.ae_jacobian_eq_extensions hF heq
  have H' : C.jacobian π =ᵐ[volume.restrict C.domain]
      coordinateJacobian F (fun j => EuclideanSpace.single j 1) := by
    filter_upwards [H] with z hz
    rw [hz,coordinateJacobian,← Matrix.det_transpose]
    rfl
  calc
    _ = ∫ z in C.domain, ((C.multiplicity z : ℝ) * C.scalar b z) *
        coordinateJacobian F (fun j => EuclideanSpace.single j 1) z := by
      apply integral_congr_ae
      filter_upwards [H'] with z hz
      rw [hz]
    _ = _ := by
      rw [← integral_indicator C.borel]
      apply integral_congr_ae
      filter_upwards [] with z
      exact Set.indicator_mul_left _ _ _

lemma action_sequentialContinuity (b : X → ℝ) (π : Fin k → X → ℝ)
    (πs : ℕ → Fin k → X → ℝ) (hb : BoundedLip b)
    (hπs : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hlim : ∀ i x, Tendsto (fun j => πs j i x) atTop (𝓝 (π i x))) :
    Tendsto (fun j => C.action b (πs j)) atTop (𝓝 (C.action b π)) := by
  obtain ⟨L,U,hφ,_⟩ := C.bilipschitz
  choose Ks hKs using hπs
  let K : ℝ≥0 := ∑ i, Ks i
  have hK (i : Fin k) : Ks i ≤ K :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
  have hseq (j : ℕ) (i : Fin k) : LipschitzWith K (πs j i) := (hKs i j).weaken (hK i)
  have hπ (i : Fin k) : LipschitzWith K (π i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hlim i x).dist (hlim i y))
      (Eventually.of_forall fun j => (hseq j i).dist_le_mul x y)
  have htot : TotallyBounded C.domain := C.bounded.isCompact_closure.totallyBounded.subset subset_closure
  have hsc (i : Fin k) (j : ℕ) : LipschitzOnWith (K*L) (C.scalar (πs j i)) C.domain :=
    C.scalar_lipschitzOn hφ (hseq j i)
  have hlsc (i : Fin k) (z : Euc k) (hz : z ∈ C.domain) :
      Tendsto (fun j => C.scalar (πs j i) z) atTop (𝓝 (C.scalar (π i) z)) := by
    simpa only [C.scalar_eq hz] using hlim i (C.param ⟨z,hz⟩)
  choose Fs F hFs hF heqs heq hlimF using fun i =>
    exists_convergent_lipschitz_extensions htot (hsc i) (hlsc i)
  let a : Euc k → ℝ := C.domain.indicator (fun z => (C.multiplicity z : ℝ) * C.scalar b z)
  have ha : Integrable a volume := (integrable_indicator_iff C.borel).mpr (C.integrable_weight hb)
  have H := weak_coordinateJacobian volume k (fun j i => hFs i j) hF hlimF
    (fun j => EuclideanSpace.single j 1) ha
  have heqs' (j : ℕ) := C.action_eq_extended_jacobian ⟨hb,fun i => ⟨K,hseq j i⟩⟩
    (fun i => hFs i j) (fun i => heqs i j)
  have heq' := C.action_eq_extended_jacobian ⟨hb,fun i => ⟨K,hπ i⟩⟩ hF heq
  simpa only [heqs',heq'] using H

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_LinearMass
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)

lemma majorant_controls {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * J z) (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (hdet : ∀ π : Fin k → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.jacobian π z| ≤ J z) :
    Controls C.action (C.majorantMeasure J) := by
  intro b π hb hπ
  let μ := volume.restrict C.domain
  have hbmeas := hb.continuous.measurable.comp C.measurable_paramExtended
  obtain ⟨M,hM⟩ := hb.2
  have hupper : Integrable (fun z => (|(C.multiplicity z : ℝ)| * J z)*|b (C.paramExtended z)|) μ :=
    hρ.mul_bdd hbmeas.abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_abs] using hM _)
  have hρ0 : 0 ≤ᵐ[μ] fun z => |(C.multiplicity z : ℝ)| * J z :=
    hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz
  rw [majorantMeasure,integral_densityPush μ C.measurable_paramExtended hρ hρ0 hb.continuous.abs]
  rw [action,ite_eq_left ⟨hb,fun i => ⟨1,hπ i⟩⟩]
  rw [← Real.norm_eq_abs]
  apply le_trans (norm_integral_le_integral_norm _) ?_
  change (∫ z, |(C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z| ∂μ) ≤ _
  apply integral_mono_ae
    (C.integrable_action_integrand hb (fun i => ⟨1,hπ i⟩)).abs hupper
  filter_upwards [hdet π hπ,C.scalar_ae_paramExtended b] with z hz hbz
  rw [abs_mul,abs_mul,hbz]
  change |(C.multiplicity z : ℝ)| * |b (C.paramExtended z)| * |C.jacobian π z| ≤ _
  calc _ ≤ (|(C.multiplicity z : ℝ)| * |b (C.paramExtended z)|) * J z :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

end IntegerChart
end CAT0Fillings

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_CurrentAxioms
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma action_linearFirst (b c : X → ℝ) (π : Fin k → X → ℝ) (a d : ℝ)
    (hb : BoundedLip b) (hc : BoundedLip c)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    C.action (fun x => a*b x+d*c x) π = a*C.action b π+d*C.action c π := by
  have hab : Admissible (fun x => a*b x+d*c x) π :=
    ⟨(hb.const_mul a).add (hc.const_mul d),hπ⟩
  rw [action,ite_eq_left hab,action,ite_eq_left ⟨hb,hπ⟩,action,ite_eq_left ⟨hc,hπ⟩,
    C.scalar_linear]
  have heq : (fun z => (C.multiplicity z : ℝ) * (a*C.scalar b z+d*C.scalar c z) * C.jacobian π z) =
      fun z => a*((C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z)+
        d*((C.multiplicity z : ℝ)*C.scalar c z*C.jacobian π z) := by funext z; ring
  rw [heq,integral_add ((C.integrable_action_integrand hb hπ).const_mul a)
    ((C.integrable_action_integrand hc hπ).const_mul d),integral_const_mul,integral_const_mul]

lemma ae_jacobian_linear (π : Fin k → X → ℝ) (i : Fin k) (f : X → ℝ) (a d : ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (fun x => a*π i x+d*f x)) z =
        a*C.jacobian π z+d*C.jacobian (Function.update π i f) z := by
  obtain ⟨K,hK⟩ := hπ i
  obtain ⟨L,hL⟩ := hf
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,C.ae_differentiableWithinAt_scalar hK,
    C.ae_differentiableWithinAt_scalar hL] with z hz hdπ hdf
  have hd : fderivWithin ℝ (C.scalar (fun x => a*π i x+d*f x)) C.domain z =
      a • fderivWithin ℝ (C.scalar (π i)) C.domain z +
        d • fderivWithin ℝ (C.scalar f) C.domain z := by
    rw [C.scalar_linear]
    exact ((hdπ.hasFDerivWithinAt.const_mul a).add (hdf.hasFDerivWithinAt.const_mul d)).fderivWithin hz
  rw [C.jacobian_update,C.jacobian_update]
  simp only [hd,_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun l j =>
    fderivWithin ℝ (C.scalar (π l)) C.domain z (EuclideanSpace.single j 1)
  let w : Fin k → ℝ := fun j => fderivWithin ℝ (C.scalar f) C.domain z (EuclideanSpace.single j 1)
  change (M.updateRow i (a • M i+d • w)).det = a*M.det+d*(M.updateRow i w).det
  rw [Matrix.det_updateRow_add,Matrix.det_updateRow_smul,Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self]

lemma action_linearCoord (b : X → ℝ) (π : Fin k → X → ℝ) (i : Fin k)
    (f : X → ℝ) (a d : ℝ) (h : Admissible b π)
    (hf : ∃ K : ℝ≥0, LipschitzWith K f) :
    C.action b (Function.update π i (fun x => a*π i x+d*f x)) =
      a*C.action b π+d*C.action b (Function.update π i f) := by
  have hup {g : X → ℝ} (hg : ∃ K : ℝ≥0, LipschitzWith K g) :
      Admissible b (Function.update π i g) := by
    refine ⟨h.1,fun j => ?_⟩
    by_cases hji : j=i
    · simpa [hji] using hg
    · simpa [hji] using h.2 j
  have hg : ∃ K : ℝ≥0, LipschitzWith K (fun x => a*π i x+d*f x) := by
    obtain ⟨K,hK⟩ := h.2 i
    obtain ⟨L,hL⟩ := hf
    refine ⟨‖a‖₊ * K + ‖d‖₊ * L,?_⟩
    simpa only [Function.comp_def,smul_eq_mul] using
      ((lipschitzWith_smul a).comp hK).add ((lipschitzWith_smul d).comp hL)
  rw [action,ite_eq_left (hup hg),action,ite_eq_left h,action,ite_eq_left (hup hf)]
  calc
    _ = ∫ z in C.domain, a*((C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z)+
        d*((C.multiplicity z : ℝ)*C.scalar b z*C.jacobian (Function.update π i f) z) := by
      apply integral_congr_ae
      filter_upwards [C.ae_jacobian_linear π i f a d h.2 hf] with z hz
      rw [hz]; ring
    _ = _ := by
      rw [integral_add ((C.integrable_action_integrand h.1 h.2).const_mul a)
        ((C.integrable_action_integrand h.1 (hup hf).2).const_mul d),
        integral_const_mul,integral_const_mul]

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma continuousOn_paramExtended : ContinuousOn C.paramExtended C.domain := by
  obtain ⟨L,U,hφ,_⟩ := C.bilipschitz
  have hl : LipschitzOnWith L C.paramExtended C.domain := by
    apply lipschitzOnWith_iff_restrict.mpr
    convert hφ using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    simp [paramExtended,z.2]
  exact hl.continuousOn

lemma action_locality (b : X → ℝ) (π : Fin k → X → ℝ) (h : Admissible b π)
    (hloc : ∃ (i : Fin k) (U : Set X) (c : ℝ), IsOpen U ∧ Function.support b ⊆ U ∧
      ∀ x ∈ U, π i x = c) : C.action b π = 0 := by
  obtain ⟨i,U,c,hU,hb,hπ⟩ := hloc
  rw [action,ite_eq_left h]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem C.borel] with z hz
  by_cases hbz : C.scalar b z = 0
  · simp [hbz]
  have hext : C.paramExtended z = C.param ⟨z,hz⟩ := by simp [paramExtended,hz]
  have hzU : C.paramExtended z ∈ U := by
    rw [hext]
    apply hb
    simpa [Function.mem_support,C.scalar_eq hz] using hbz
  have hh := (C.continuousOn_paramExtended z hz).preimage_mem_nhdsWithin (hU.mem_nhds hzU)
  have heq : C.scalar (π i) =ᶠ[𝓝[C.domain] z] fun _ => c := by
    filter_upwards [hh,eventually_mem_nhdsWithin] with y hy hys
    rw [C.scalar_eq hys]
    have hye : C.paramExtended y = C.param ⟨y,hys⟩ := by simp [paramExtended,hys]
    exact hπ _ (hye ▸ hy)
  have heqz : C.scalar (π i) z = c := by rw [C.scalar_eq hz]; exact hπ _ (hext ▸ hzU)
  have hd := heq.fderivWithin_eq (𝕜 := ℝ) heqz
  have hd0 : fderivWithin ℝ (C.scalar (π i)) C.domain z = 0 := by
    exact hd.trans (by
      simpa only [Function.const_def,Pi.zero_apply] using
        congrFun (fderivWithin_const (𝕜 := ℝ) (E := Euc k) (s := C.domain) c) z)
  have hdet : C.jacobian π z = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    change fderivWithin ℝ (C.scalar (π i)) C.domain z (EuclideanSpace.single j 1) = 0
    rw [hd0]; rfl
  rw [hdet,mul_zero]; rfl

variable [MeasurableSpace X] [BorelSpace X]
lemma action_finiteMass : ∃ μ : Measure X, IsFiniteMeasure μ ∧ Controls C.action μ := by
  obtain ⟨L,U,hφ,_⟩ := C.bilipschitz
  obtain ⟨B,hB,hdet⟩ := coordinateJacobian_uniform_bound L
    (fun j : Fin k => EuclideanSpace.single j (1 : ℝ))
  have hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * B) (volume.restrict C.domain) :=
    C.integrable.abs.mul_const B
  refine ⟨C.majorantMeasure (fun _ => B),densityPush_finite _ _ hρ,?_⟩
  apply C.majorant_controls hρ (Eventually.of_forall fun _ => hB)
  intro π hπ
  have hs (i : Fin k) : LipschitzOnWith L (C.scalar (π i)) C.domain := by
    simpa only [one_mul] using C.scalar_lipschitzOn hφ (hπ i)
  choose F hF heq using fun i => (hs i).extend_real
  filter_upwards [C.ae_jacobian_eq_extensions hF heq] with z hz
  have H := hdet F hF z
  rw [hz]
  have heqdet : Matrix.det (Matrix.of fun i j => fderiv ℝ (F i) z (EuclideanSpace.single j 1)) =
      coordinateJacobian F (fun j => EuclideanSpace.single j 1) z := by
    rw [coordinateJacobian,← Matrix.det_transpose]; rfl
  simpa only [heqdet,Real.norm_eq_abs] using H

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} (C : IntegerChart X k)

lemma action_isMetricCurrent : IsMetricCurrent C.action := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · have hd : C.domain = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact isEmptyElim (C.param ⟨z,hz⟩)
    have heq : C.action = fun _ _ => 0 := by
      funext b π
      simp [action,hd]
    rw [heq]
    exact isMetricCurrent_zero _
  · exact {
      offDomain := by intro b π h; simp [action,h]
      linearFirst := C.action_linearFirst
      linearCoord := C.action_linearCoord
      sequentialContinuity := C.action_sequentialContinuity
      locality := C.action_locality
      finiteMass := C.action_finiteMass }

end CAT0Fillings.IntegerChart

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Geometry_Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings

lemma abs_det_le_sqrt_det_of_posDef {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef)
    (h : ∀ i v, |L i ⬝ᵥ v| ≤ Real.sqrt (v ⬝ᵥ P.mulVec v)) :
    |L.det| ≤ Real.sqrt P.det := by
  let Q := CFC.sqrt P
  have hQdet : Q.det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.posSemidef.det_sqrt
  have hQpos : 0 < Q.det := by rw [hQdet]; exact Real.sqrt_pos.2 hP.det_pos
  have hQi : IsUnit Q.det := isUnit_iff_ne_zero.2 (ne_of_gt hQpos)
  have hQinv := Matrix.mul_nonsing_inv Q hQi
  have hinvQ := Matrix.nonsing_inv_mul Q hQi
  have htrans (v : Fin n → ℝ) :
      Real.sqrt ((Q⁻¹).mulVec v ⬝ᵥ P.mulVec ((Q⁻¹).mulVec v)) =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    rw [dot_mulVec_sqrt P hP.posSemidef]
    change Real.sqrt (Q.mulVec ((Q⁻¹).mulVec v) ⬝ᵥ Q.mulVec ((Q⁻¹).mulVec v)) = _
    rw [Matrix.mulVec_mulVec, hQinv, Matrix.one_mulVec]
    have hn : v ⬝ᵥ v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
        real_inner_self_eq_norm_sq (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
    rw [hn,Real.sqrt_sq (norm_nonneg _)]
  have hB : |(L * Q⁻¹).det| ≤ 1 := by
    apply abs_det_le_one_of_dot_bound
    intro i v
    have hh := h i ((Q⁻¹).mulVec v)
    rw [htrans] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    change ((L * Q⁻¹).mulVec v) i = (L.mulVec ((Q⁻¹).mulVec v)) i
    rw [Matrix.mulVec_mulVec]
  have heq : L = (L * Q⁻¹) * Q := by rw [Matrix.mul_assoc,hinvQ,Matrix.mul_one]
  calc
    |L.det| = |(L * Q⁻¹).det| * Q.det := by
      conv_lhs => rw [heq, Matrix.det_mul]
      rw [abs_mul,abs_of_pos hQpos]
    _ ≤ 1*Q.det := mul_le_mul_of_nonneg_right hB hQpos.le
    _ = Real.sqrt P.det := by rw [one_mul,hQdet]

lemma sqrt_det_le_pow_of_quadratic_bound {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Fin n → ℝ,
      Real.sqrt (v ⬝ᵥ P.mulVec v) ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    Real.sqrt P.det ≤ K^n := by
  have hdet : (CFC.sqrt P).det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.det_sqrt
  rw [←hdet]
  have hdnonneg : 0 ≤ (CFC.sqrt P).det := by rw [hdet]; exact Real.sqrt_nonneg _
  rw [←abs_of_nonneg hdnonneg]
  apply abs_det_le_pow_of_dot_bound _ hK
  intro i v
  have hn : ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (v ⬝ᵥ P.mulVec v) := by
    rw [dot_mulVec_sqrt P hP]
    have heq : (CFC.sqrt P).mulVec v ⬝ᵥ (CFC.sqrt P).mulVec v =
        ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
        real_inner_self_eq_norm_sq
          (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))
    rw [heq, Real.sqrt_sq (norm_nonneg _)]
  apply le_trans _ (h v)
  rw [←hn]
  exact PiLp.norm_apply_le (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n)) i

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Geometry_MatrixRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped RealInnerProductSpace MatrixOrder

lemma norm_sqrt_mulVec {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (v : Fin n → ℝ) :
    ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (v ⬝ᵥ P.mulVec v) := by
  rw [dot_mulVec_sqrt P hP]
  have heq : (CFC.sqrt P).mulVec v ⬝ᵥ (CFC.sqrt P).mulVec v =
      ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,star_trivial] using
      real_inner_self_eq_norm_sq
        (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))
  rw [heq,Real.sqrt_sq (norm_nonneg _)]

lemma sqrt_det_le_mul_sqrt_det {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (hQ : Q.PosDef) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Fin n → ℝ,
      Real.sqrt (v ⬝ᵥ P.mulVec v) ≤ K*Real.sqrt (v ⬝ᵥ Q.mulVec v)) :
    Real.sqrt P.det ≤ K^n * Real.sqrt Q.det := by
  let A := CFC.sqrt P
  let B := CFC.sqrt Q
  have hAdet : A.det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.det_sqrt
  have hBdet : B.det = Real.sqrt Q.det := by
    simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt
  have hBp : 0 < B.det := by rw [hBdet]; exact Real.sqrt_pos.2 hQ.det_pos
  have hBi : IsUnit B.det := isUnit_iff_ne_zero.2 (ne_of_gt hBp)
  have hBinv := Matrix.mul_nonsing_inv B hBi
  have hinvB := Matrix.nonsing_inv_mul B hBi
  have htrans (v : Fin n → ℝ) :
      Real.sqrt ((B⁻¹).mulVec v ⬝ᵥ Q.mulVec ((B⁻¹).mulVec v)) =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    rw [←norm_sqrt_mulVec Q hQ.posSemidef]
    change ‖(WithLp.toLp 2 (B.mulVec ((B⁻¹).mulVec v)) : EuclideanSpace ℝ (Fin n))‖ = _
    rw [Matrix.mulVec_mulVec,hBinv,Matrix.one_mulVec]
  have hbound : |(A * B⁻¹).det| ≤ K^n := by
    apply abs_det_le_pow_of_dot_bound _ hK
    intro i v
    have hh := h ((B⁻¹).mulVec v)
    rw [htrans,←norm_sqrt_mulVec P hP] at hh
    apply le_trans _ hh
    have hv : (A * B⁻¹) i ⬝ᵥ v = (A.mulVec ((B⁻¹).mulVec v)) i := by
      rw [Matrix.mulVec_mulVec]
      rfl
    rw [hv]
    exact PiLp.norm_apply_le
      (WithLp.toLp 2 (A.mulVec ((B⁻¹).mulVec v)) : EuclideanSpace ℝ (Fin n)) i
  have heq : A = (A*B⁻¹)*B := by rw [Matrix.mul_assoc,hinvB,Matrix.mul_one]
  calc
    Real.sqrt P.det = |A.det| := by rw [hAdet,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ = |(A*B⁻¹).det| *B.det := by
      conv_lhs => rw [heq,Matrix.det_mul]
      rw [abs_mul,abs_of_pos hBp]
    _ ≤ K^n*B.det := mul_le_mul_of_nonneg_right hbound hBp.le
    _ = K^n*Real.sqrt Q.det := by rw [hBdet]

lemma abs_matrixRow_sqrt_le {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (i : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    |matrixRowFunctional (CFC.sqrt P) i v| ≤ Real.sqrt (v ⬝ᵥ P.mulVec v) := by
  rw [matrixRowFunctional_apply,←norm_sqrt_mulVec P hP]
  exact PiLp.norm_apply_le
    (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n)) i

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_MeasurePartition
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma densityPush_mono_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {φ : α → β} (hφ : Measurable φ) {ρ σ : α → ℝ}
    (h : ρ ≤ᵐ[μ] σ) : densityPush μ φ ρ ≤ densityPush μ φ σ := by
  apply Measure.map_mono _ hφ
  exact withDensity_mono (h.mono fun _ hx => ENNReal.ofReal_le_ofReal hx)

lemma densityPush_const_mul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (φ : α → β) (ρ : α → ℝ) (c : ℝ≥0) (hφ : Measurable φ) :
    densityPush μ φ (fun z => (c : ℝ)*ρ z) = c • densityPush μ φ ρ := by
  unfold densityPush
  have hfun : (fun z => ENNReal.ofReal ((c : ℝ)*ρ z)) =
      (c : ENNReal) • (fun z => ENNReal.ofReal (ρ z)) := by
    ext z
    simp only [Pi.smul_apply,smul_eq_mul,ENNReal.ofReal_mul c.coe_nonneg,ENNReal.ofReal_coe_nnreal]
  rw [hfun,withDensity_smul' _ _ ENNReal.coe_ne_top,Measure.map_smul]
  rfl

lemma densityPush_sum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ι : Type*} (μ : ι → Measure α) {φ : α → β} (hφ : Measurable φ) (ρ : α → ℝ) :
    densityPush (Measure.sum μ) φ ρ = Measure.sum (fun i => densityPush (μ i) φ ρ) := by
  simp only [densityPush,withDensity_sum,Measure.map_sum hφ.aemeasurable]

lemma densityPush_le_of_partition {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {φ : α → β} (hφ : Measurable φ) (ρ : α → ℝ)
    {s : Set α} {t : ℕ → Set α} (ht : ∀ i, MeasurableSet (t i)) (hts : ∀ i, t i ⊆ s)
    (hdisj : Pairwise (fun i j => Disjoint (t i) (t j))) (hnull : μ (s \ ⋃ i, t i) = 0)
    (him : ∀ i, MeasurableSet (φ '' t i)) (hinj : Set.InjOn φ s)
    (hbound : ∀ i, densityPush (μ.restrict (t i)) φ ρ ≤ ν.restrict (φ '' t i)) :
    densityPush (μ.restrict s) φ ρ ≤ ν := by
  rw [restrict_eq_sum_of_ae_partition ht hts hdisj hnull,densityPush_sum _ hφ]
  have hdisj' : Pairwise (fun i j => Disjoint (φ '' t i) (φ '' t j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hxi,rfl⟩ ⟨y,hyj,hxy⟩
    have hxy' : y = x := hinj (hts j hyj) (hts i hxi) hxy
    subst y
    exact Set.disjoint_left.mp (hdisj hij) hxi hyj
  calc
    _ ≤ Measure.sum (fun i => ν.restrict (φ '' t i)) := by
      apply Measure.le_iff.mpr
      intro u hu
      simp only [Measure.sum_apply _ hu]
      exact ENNReal.tsum_le_tsum (fun i => hbound i u)
    _ = ν.restrict (⋃ i, φ '' t i) := (Measure.restrict_iUnion hdisj' him).symm
    _ ≤ ν := Measure.restrict_le_self
end CAT0Fillings

namespace CAT0Fillings
open Matrix MeasureTheory Set Filter
open scoped MatrixOrder NNReal Topology

lemma sqrt_polarization_quadratic {k : ℕ} (p : Seminorm ℝ (Euc k))
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) (v : Fin k → ℝ) :
    Real.sqrt (v ⬝ᵥ (polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).mulVec v)
      = p (WithLp.toLp 2 v) := by
  have hrepr : (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.repr (WithLp.toLp 2 v) = v := by
    ext j
    simp
  have hquad := polarizationMatrix_quadratic (EuclideanSpace.basisFun (Fin k) ℝ).toBasis p hp hpara (WithLp.toLp 2 v)
  rw [hrepr] at hquad
  rw [hquad,Real.sqrt_sq (apply_nonneg _ _)]

lemma sqrt_det_polarization_le {k : ℕ} (p q : Seminorm ℝ (Euc k))
    (hp : ∀ v, p v = 0 ↔ v = 0) (hq : ∀ v, q v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2)
    (hqpara : ∀ u v, q (u+v)^2+q (u-v)^2 = 2*q u^2+2*q v^2)
    {L : ℝ} (hL : 0 ≤ L) (h : ∀ v, p v ≤ L*q v) :
    Real.sqrt (polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≤
    L^k * Real.sqrt (polarizationMatrix q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  apply sqrt_det_le_mul_sqrt_det _ _
    (polarizationMatrix_posDef _ p hp hpara).posSemidef
    (polarizationMatrix_posDef _ q hq hqpara) hL
  intro v
  simpa only [sqrt_polarization_quadratic p hp hpara,
    sqrt_polarization_quadratic q hq hqpara] using h (WithLp.toLp 2 v)

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_Centered
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace CAT0Fillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] {f : E → X} {K : ℝ≥0}

lemma hasCenteredMetricDifferential_of_dense_directions [FiniteDimensional ℝ E]
    (hf : LipschitzWith K f) (x : E) (p : Seminorm ℝ E)
    (hp : LipschitzWith K p) {ι : Type*} {D : ι → E} (hD : DenseRange D)
    (hdir : ∀ j, Tendsto (fun t => metricQuotient f x t (D j)) (𝓝[≠] 0) (𝓝 (p (D j)))) :
    HasCenteredMetricDifferential f p x := by
  have hall (v : E) : Tendsto (fun t => metricQuotient f x t v) (𝓝[≠] 0) (𝓝 (p v)) :=
    tendsto_of_lipschitz_dense (metricQuotient_lipschitz hf x) hp hD hdir v
  apply IsLittleO.of_bound
  intro ε hε
  have hU := uniformly_tendsto_of_lipschitz (metricQuotient_lipschitz hf x) hp
    (isCompact_sphere (0 : E) 1) (fun v _ => hall v) hε
  obtain ⟨δ, hδ, hUδ⟩ := Metric.mem_nhdsWithin_iff.mp hU
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  by_cases hyx : y = x
  · simp [hyx]
  let r : ℝ := ‖y-x‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  let v : E := r⁻¹ • (y-x)
  have hv : v ∈ sphere (0 : E) 1 := by
    rw [mem_sphere, dist_zero_right]
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_cancel₀ hr.ne']
  have hrv : r • v = y-x := by dsimp [v]; exact smul_inv_smul₀ hr.ne' _
  have hry : x+r • v = y := by rw [hrv]; abel
  have hrδ : r ∈ ball (0 : ℝ) δ ∩ ({0} : Set ℝ)ᶜ := by
    constructor
    · change |r-0| < δ
      rw [sub_zero, abs_of_pos hr]
      simpa only [mem_ball, dist_eq_norm, r] using hy
    · exact hr.ne'
  have hh := hUδ hrδ v hv
  change dist (dist (f (x+r • v)) (f x)/|r|) (p v) < ε at hh
  rw [hry, abs_of_pos hr, Real.dist_eq] at hh
  have hpv : p (y-x) = r * p v := by
    rw [← hrv, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
  rw [hpv, Real.norm_eq_abs]
  change |dist (f y) (f x)-r*p v| ≤ ε*r
  have heq : dist (f y) (f x)-r*p v = r*(dist (f y) (f x)/r-p v) := by field_simp
  rw [heq, abs_mul, abs_of_pos hr]
  exact (mul_lt_mul_of_pos_left hh hr).le.trans_eq (mul_comm r ε)

variable [SeparableSpace X] [Nonempty X] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

theorem ae_hasCenteredMetricDifferential (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, HasCenteredMetricDifferential f (metricSeminorm f x) x := by
  filter_upwards [ae_dense_directionalSeminorm μ hf] with x hx
  exact hasCenteredMetricDifferential_of_dense_directions hf x _ (metricSeminorm_lipschitz hf x)
    (denseRange_denseSeq E) hx

end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_ErrorModulus
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_bound (hf : LipschitzWith K f) {r : ℝ} (x v : E)
    (hv : ‖v‖ < r) :
    |dist (f (x+v)) (f x)-metricSeminorm f x v| ≤ metricErrorModulus f r x * ‖v‖ := by
  let A : Set E := {w | |dist (f (x+w)) (f x)-metricSeminorm f x w| ≤
    metricErrorModulus f r x * ‖w‖}
  have hA : IsClosed A := isClosed_le
    (((hf.continuous.comp (continuous_const.add continuous_id)).dist continuous_const).sub
      (metricSeminorm_lipschitz hf x).continuous).abs
    (continuous_const.mul continuous_norm)
  have hsub : ball (0 : E) r ∩ range (denseSeq E) ⊆ A := by
    rintro w ⟨hq,⟨q,rfl⟩⟩
    by_cases hw : denseSeq E q = 0
    · simp [A,hw]
    have hqw : 0 < ‖denseSeq E q‖ := norm_pos_iff.mpr hw
    have hqr : ‖denseSeq E q‖ ≤ r := (by simpa only [mem_ball, dist_zero_right] using hq :
      ‖denseSeq E q‖ < r).le
    have hle := le_ciSup (bddAbove_metricErrorTerm hf r x) q
    rw [metricErrorTerm, ite_eq_left ⟨hqw,hqr⟩] at hle
    exact (div_le_iff₀ hqw).mp hle
  have hvcl := (denseRange_denseSeq E).open_subset_closure_inter isOpen_ball
    (by simpa only [mem_ball, dist_zero_right] using hv : v ∈ ball (0 : E) r)
  exact hA.closure_subset_iff.mpr hsub hvcl

end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_TwoPoint
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace CAT0Fillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]
lemma eventually_seminorm_bound_of_dense
    {ι κ : Type*} {l : Filter ι} {p : ι → Seminorm ℝ E} {q : Seminorm ℝ E}
    {K : ℝ≥0} (hp : ∀ i, LipschitzWith K (p i)) (hq : LipschitzWith K q)
    {D : κ → E} (hD : DenseRange D)
    (hc : ∀ j, Tendsto (fun i => p i (D j)) l (𝓝 (q (D j))))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ v : E, |p i v-q v| ≤ ε*‖v‖ := by
  have hlim := tendsto_of_lipschitz_dense hp hq hD hc
  have h := uniformly_tendsto_of_lipschitz hp hq (isCompact_sphere (0 : E) 1)
    (fun v _ => hlim v) hε
  filter_upwards [h] with i hi v
  apply seminorm_sub_bound_of_sphere hε.le _ v
  intro w hw
  exact (hi w (by simpa only [mem_sphere,dist_zero_right] using hw)).le

end CAT0Fillings

namespace CAT0Fillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

lemma hasTwoPointMetricDifferential_of_uniformModulus
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s) :
    HasTwoPointMetricDifferential f (metricSeminorm f x) s x := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hp := eventually_seminorm_bound_of_dense (fun y => metricSeminorm_lipschitz hf y)
    (metricSeminorm_lipschitz hf x) (denseRange_denseSeq E) hc (half_pos hε)
  obtain ⟨N,hN⟩ := (eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hu) (ε/2) (half_pos hε)))
  have hNN (y : E) (hy : y ∈ s) : metricErrorModulus f (r N) y < ε/2 := by
    have h := hN N le_rfl y hy
    simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (metricErrorModulus_nonneg hf _ _)] using h
  have hfst : Tendsto (fun q : E × E => q.1) (𝓝[s ×ˢ s] (x,x)) (𝓝[s] x) :=
    continuous_fst.continuousWithinAt.tendsto_nhdsWithin (fun _ hq => hq.1)
  have hnear : ∀ᶠ q : E × E in 𝓝[s ×ˢ s] (x,x), ‖q.2-q.1‖ < r N := by
    have ht : Tendsto (fun q : E × E => ‖q.2-q.1‖) (𝓝[s ×ˢ s] (x,x)) (𝓝 0) := by
      simpa using ((continuous_snd.sub continuous_fst).norm.continuousWithinAt.tendsto (s := s ×ˢ s) (x := (x,x)))
    exact (tendsto_order.1 ht).2 _ (hr N)
  filter_upwards [hfst.eventually hp,hnear,self_mem_nhdsWithin] with q hqp hqr hqs
  have he₁ := metricErrorModulus_bound hf q.1 (q.2-q.1) hqr
  have he₂ := hqp (q.2-q.1)
  have hm := hNN q.1 hqs.1
  have ht : ‖q.2-q.1‖ ≤ ‖q.1-x‖+‖q.2-x‖ := by
    calc ‖q.2-q.1‖ = ‖(q.2-x)-(q.1-x)‖ := by congr 1; abel
      _ ≤ ‖q.2-x‖+‖q.1-x‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have he : |dist (f q.1) (f q.2)-metricSeminorm f x (q.1-q.2)| ≤
      ε*(‖q.1-x‖+‖q.2-x‖) := by
    have hpneg : metricSeminorm f x (q.1-q.2) = metricSeminorm f x (q.2-q.1) := by
      rw [←neg_sub q.2 q.1,map_neg_eq_map]
    rw [hpneg,dist_comm]
    calc |dist (f q.2) (f q.1)-metricSeminorm f x (q.2-q.1)| ≤
          |dist (f q.2) (f q.1)-metricSeminorm f q.1 (q.2-q.1)| +
            |metricSeminorm f q.1 (q.2-q.1)-metricSeminorm f x (q.2-q.1)| := abs_sub_le _ _ _
      _ ≤ metricErrorModulus f (r N) q.1 * ‖q.2-q.1‖ + ε/2*‖q.2-q.1‖ := by
        apply add_le_add _ he₂
        simpa only [←add_sub_assoc,add_sub_cancel_left] using he₁
      _ ≤ ε*‖q.2-q.1‖ := by nlinarith [norm_nonneg (q.2-q.1)]
      _ ≤ ε*(‖q.1-x‖+‖q.2-x‖) := mul_le_mul_of_nonneg_left ht hε.le
  simpa only [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using he

end CAT0Fillings.MetricDifferentiation

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_LargePieces
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_large_twoPointMetricDifferential
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ∀ x ∈ t, HasTwoPointMetricDifferential f (metricSeminorm f x) t x := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
    filter_upwards [(ae_hasCenteredMetricDifferential μ hf).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))] with x hx
    exact metricErrorModulus_tendsto_zero hf hx hr0
  obtain ⟨t,hts,ht,hμt,hct,htu⟩ := exists_large_continuousOn_uniformly μ hs hsf
    (show Measurable (fun x j => metricSeminorm f x (denseSeq E j)) from
      Measurable.of_eval (fun index => measurable_metricSeminorm_apply hf (denseSeq E index)))
    (fun n => measurable_metricErrorModulus hf (r n)) hc hε
  refine ⟨t,hts,ht,hμt,?_⟩
  intro x hx
  apply hasTwoPointMetricDifferential_of_uniformModulus hf _ hr htu
  intro j
  exact (continuousOn_pi.1 hct j) x hx

end CAT0Fillings.MetricDifferentiation

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_Parallelogram
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
section MetricDifferential
variable {X : Type*} [MetricSpace X]
omit [MeasurableSpace E] [BorelSpace E] in

lemma HasTwoPointMetricDifferential.scaled_pair_limit
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x u v : E}
    (h : HasTwoPointMetricDifferential f p s x)
    {c : ℕ → ℝ} {d e : ℕ → E}
    (hc : Tendsto (fun j => ‖c j‖) atTop atTop)
    (hd : ∀ᶠ j in atTop, x + d j ∈ s) (he : ∀ᶠ j in atTop, x + e j ∈ s)
    (hcd : Tendsto (fun j => c j • d j) atTop (𝓝 u))
    (hce : Tendsto (fun j => c j • e j) atTop (𝓝 v)) :
    Tendsto (fun j => ‖c j‖ * dist (f (x + d j)) (f (x + e j)))
      atTop (𝓝 (p (u - v))) := by
  have hp := seminorm_continuous_finiteDimensional p
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have he₀ := tangentConeAt.lim_zero atTop hc hce
  have hpair : Tendsto (fun j => (x + d j, x + e j)) atTop (𝓝[s ×ˢ s] (x,x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.add hd₀).prodMk_nhds (tendsto_const_nhds.add he₀)
    · filter_upwards [hd, he] with j hj hj'
      exact ⟨hj, hj'⟩
  have hsmall := h.comp_tendsto hpair
  have hmul := hsmall.mul_isBigO (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => (‖(x + d j) - x‖ + ‖(x + e j) - x‖) * ‖c j‖)
      atTop (𝓝 (‖u‖ + ‖v‖)) := by
    simpa only [norm_smul, add_sub_cancel_left, add_mul, mul_comm] using hcd.norm.add hce.norm
  have hzero := hmul.tendsto_zero_of_tendsto hnorm
  have hdiff := hp.tendsto (u - v) |>.comp (hcd.sub hce)
  have hsum := hzero.add hdiff
  convert hsum using 1
  · ext j
    simp only [Function.comp_apply, add_sub_add_left_eq_sub, ← smul_sub, map_smul_eq_mul]
    ring
  · simp

lemma HasTwoPointMetricDifferential.distance_bound
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x : E}
    (h : HasTwoPointMetricDifferential f p s x)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) {A B : ℝ}
    (hAB : ∀ a ∈ s, ∀ b ∈ s, A * dist a b ≤ B * dist (f a) (f b)) (w : E) :
    A * ‖w‖ ≤ B * p w := by
  let z : Fin 2 → E := ![w, 0]
  have hz : z ∈ tangentConeAt ℝ {f : Fin 2 → E | ∀ i, f i ∈ s} (fun _ => x) := by
    rw [tangentConeAt_pi_eq_univ_of_density_one μ s x hx]
    exact mem_univ z
  obtain ⟨c, d, hc, hd, hcd⟩ :=
    mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hz
  have hcd₀ := tendsto_pi_nhds.mp hcd 0
  have hcd₁ := tendsto_pi_nhds.mp hcd 1
  have hl := h.scaled_pair_limit hc (hd.mono fun _ hj => hj 0)
    (hd.mono fun _ hj => hj 1) hcd₀ hcd₁
  have hl' : Tendsto (fun j => ‖c j‖ * dist (f (x + d j 0)) (f (x + d j 1)))
      atTop (𝓝 (p w)) := by simpa [z] using hl
  have hr : Tendsto (fun j => ‖c j‖ * dist (x + d j 0) (x + d j 1))
      atTop (𝓝 ‖w‖) := by
    simpa only [Pi.smul_apply, dist_eq_norm, add_sub_add_left_eq_sub, ← norm_smul, smul_sub,
      z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero]
      using (hcd₀.sub hcd₁).norm
  apply le_of_tendsto_of_tendsto (hr.const_mul A) (hl'.const_mul B)
  filter_upwards [hd] with j hj
  have H := mul_le_mul_of_nonneg_left
    (hAB (x + d j 0) (hj 0) (x + d j 1) (hj 1)) (norm_nonneg (c j))
  simpa only [mul_left_comm] using H

end MetricDifferential
end CAT0Fillings

namespace CAT0Fillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {X : Type*} [MetricSpace X]

lemma HasTwoPointMetricDifferential.parallelogram_of_quadrilateralOn
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x : E}
    (h : HasTwoPointMetricDifferential f p s x)
    (hQ : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (f a) (f c)^2 + dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2 + dist (f b) (f c)^2 + dist (f c) (f d)^2 + dist (f d) (f a)^2)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (u v : E) :
    p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2 := by
  have hle (u v : E) : p (u+v)^2+p (u-v)^2 ≤ 2*p u^2+2*p v^2 := by
    let z : Fin 4 → E := ![0,u,u+v,v]
    have hz : z ∈ tangentConeAt ℝ {f : Fin 4 → E | ∀ i, f i ∈ s} (fun _ => x) := by
      rw [tangentConeAt_pi_eq_univ_of_density_one μ s x hx]
      exact mem_univ z
    obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hz
    have hl (i j : Fin 4) :
        Tendsto (fun k => ‖c k‖*dist (f (x+d k i)) (f (x+d k j))) atTop (𝓝 (p (z i-z j))) := by
      apply h.scaled_pair_limit hc
      · filter_upwards [hd] with k hk
        exact hk i
      · filter_upwards [hd] with k hk
        exact hk j
      · exact tendsto_pi_nhds.mp hcd i
      · exact tendsto_pi_nhds.mp hcd j
    have hquad : ∀ᶠ k in atTop,
        (‖c k‖*dist (f (x+d k 0)) (f (x+d k 2)))^2 +
        (‖c k‖*dist (f (x+d k 1)) (f (x+d k 3)))^2 ≤
        (‖c k‖*dist (f (x+d k 0)) (f (x+d k 1)))^2 +
        (‖c k‖*dist (f (x+d k 1)) (f (x+d k 2)))^2 +
        (‖c k‖*dist (f (x+d k 2)) (f (x+d k 3)))^2 +
        (‖c k‖*dist (f (x+d k 3)) (f (x+d k 0)))^2 := by
      filter_upwards [hd] with k hk
      have H := hQ _ (hk 0) _ (hk 1) _ (hk 2) _ (hk 3)
      simpa only [Pi.add_apply,mul_add,mul_pow] using mul_le_mul_of_nonneg_left H (sq_nonneg ‖c k‖)
    have H := le_of_tendsto_of_tendsto
      (((hl 0 2).pow 2).add ((hl 1 3).pow 2))
      (((((hl 0 1).pow 2).add ((hl 1 2).pow 2)).add ((hl 2 3).pow 2)).add ((hl 3 0).pow 2)) hquad
    have hneg : p (-u+-v) = p (u+v) := by rw [←neg_add,map_neg_eq_map]
    simpa [z,map_neg_eq_map,hneg,two_mul,add_assoc,add_left_comm,add_comm] using H
  have hf := hle u v
  have hr := hle (u+v) (u-v)
  have he₁ : (u+v)+(u-v) = (2 : ℝ) • u := by module
  have he₂ : (u+v)-(u-v) = (2 : ℝ) • v := by module
  rw [he₁,he₂,map_smul_eq_mul,map_smul_eq_mul] at hr
  norm_num at hr
  linarith
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_HilbertCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem ae_metricSeminorm_parallelogram_on
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    (hQ : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (f a) (f c)^2 + dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2 + dist (f b) (f c)^2 + dist (f c) (f d)^2 + dist (f d) (f a)^2) :
    ∀ᵐ x ∂μ.restrict s, ∀ u v : E,
      metricSeminorm f x (u+v)^2+metricSeminorm f x (u-v)^2 =
        2*metricSeminorm f x u^2+2*metricSeminorm f x v^2 := by
  apply ae_restrict_of_arbitrarily_large_pieces μ hs
  intro ε hε
  obtain ⟨t,hts,ht,htμ,hD⟩ := exists_large_twoPointMetricDifferential μ hf hs hsf hε
  refine ⟨t,hts,ht,htμ,?_⟩
  filter_upwards [ae_restrict_mem ht, Besicovitch.ae_tendsto_measure_inter_div μ t] with x hx hxd u v
  exact (hD x hx).parallelogram_of_quadrilateralOn μ
    (fun a ha b hb c hc d hd => hQ a (hts ha) b (hts hb) c (hts hc) d (hts hd)) hxd u v
end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem ae_metricSeminorm_distance_bound_on
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {A B : ℝ}
    (hAB : ∀ a ∈ s, ∀ b ∈ s, A * dist a b ≤ B * dist (f a) (f b)) :
    ∀ᵐ x ∂μ.restrict s, ∀ w : E, A * ‖w‖ ≤ B * metricSeminorm f x w := by
  apply ae_restrict_of_arbitrarily_large_pieces μ hs
  intro ε hε
  obtain ⟨t,hts,ht,htμ,hD⟩ := exists_large_twoPointMetricDifferential μ hf hs hsf hε
  refine ⟨t,hts,ht,htμ,?_⟩
  filter_upwards [ae_restrict_mem ht, Besicovitch.ae_tendsto_measure_inter_div μ t] with x hx hxd w
  exact (hD x hx).distance_bound μ hxd
    (fun a ha b hb => hAB a (hts ha) b (hts hb)) w
end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]

theorem exists_hilbertian_chart_differential
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hJ : AntilipschitzWith J f)
    (hQ : ∀ a b c d : s,
      dist (f a) (f c)^2+dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2+dist (f b) (f c)^2+dist (f c) (f d)^2+dist (f d) (f a)^2) :
    ∃ p : E → Seminorm ℝ E,
      (∀ v, Measurable (fun x => p x v)) ∧
      (∀ x, LipschitzWith K (p x)) ∧
      ∀ᵐ x ∂μ.restrict s, (∀ hx : x ∈ s,
        HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩) ∧
        (∀ u v, p x (u+v)^2+p x (u-v)^2 = 2*p x u^2+2*p x v^2) ∧
        (∀ v, ‖v‖ ≤ (J : ℝ)*p x v) := by
  classical
  let Y := Set.range f
  let : SeparableSpace Y := (isSeparable_range hf.continuous).separableSpace
  let F : s → Y := fun x => ⟨f x,x,rfl⟩
  let e := kuratowskiEmbedding Y
  have he : Isometry e := kuratowskiEmbedding.isometry Y
  let F₀ : E → ↥(lp (fun _ : ℕ => ℝ) (⊤ : ENNReal)) :=
    fun x => if hx : x ∈ s then e (F ⟨x,hx⟩) else 0
  have hF₀ : LipschitzOnWith K F₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    dsimp only [F₀]
    rw [dite_eq_left hx,dite_eq_left hy,he.dist_eq]
    exact hf.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,heq⟩ := hF₀.extend_lp_infty
  let Z := Set.range g
  let : SeparableSpace Z := (isSeparable_range hg.continuous).separableSpace
  let : Nonempty Z := ⟨⟨g 0,0,rfl⟩⟩
  let G : E → Z := fun x => ⟨g x,x,rfl⟩
  have hG : LipschitzWith K G := by
    apply LipschitzWith.of_dist_le_mul
    exact hg.dist_le_mul
  have hdist (y z : s) : dist (G y) (G z) = dist (f y) (f z) := by
    change dist (g y) (g z) = _
    rw [←heq y.property, ←heq z.property]
    dsimp only [F₀]
    rw [dite_eq_left y.property,dite_eq_left z.property]
    exact he.dist_eq (F y) (F z)
  have hQG : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (G a) (G c)^2+dist (G b) (G d)^2 ≤
        dist (G a) (G b)^2+dist (G b) (G c)^2+dist (G c) (G d)^2+dist (G d) (G a)^2 := by
    intro a ha b hb c hc d hd
    simpa only [← hdist] using hQ ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩
  have hJG : ∀ a ∈ s, ∀ b ∈ s, (1 : ℝ)*dist a b ≤ (J : ℝ)*dist (G a) (G b) := by
    intro a ha b hb
    have hh := hJ.le_mul_dist ⟨a,ha⟩ ⟨b,hb⟩
    change dist a b ≤ (J : ℝ)*dist (f ⟨a,ha⟩) (f ⟨b,hb⟩) at hh
    simpa only [←hdist,one_mul] using hh
  refine ⟨metricSeminorm G,fun v => measurable_metricSeminorm_apply hG v,
    fun x => metricSeminorm_lipschitz hG x,?_⟩
  have hdiff := (ae_hasCenteredMetricDifferential μ hG).filter_mono
    (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))
  filter_upwards [hdiff, ae_metricSeminorm_parallelogram_on μ hG hs hsf hQG,
    ae_metricSeminorm_distance_bound_on μ hG hs hsf hJG] with x hdx hpx hjx
  refine ⟨?_,hpx,by simpa only [one_mul] using hjx⟩
  intro hx
  have hc : Tendsto (fun y : s => (y : E)) (𝓝 (⟨x,hx⟩ : s)) (𝓝 x) :=
    continuous_subtype_val.tendsto _
  have hr := hdx.comp_tendsto hc
  change (fun y : s => dist (G (y : E)) (G ((⟨x,hx⟩ : s) : E)) -
    metricSeminorm G x ((y : E)-x)) =o[𝓝 (⟨x,hx⟩ : s)] (fun y : s => (y : E)-x) at hr
  have hdist' (y : s) : dist (G (y : E)) (G x) = dist (f y) (f ⟨x,hx⟩) := hdist y ⟨x,hx⟩
  simpa only [HasCenteredMetricDifferentialWithin,hdist'] using hr
end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_LocalBounds
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma seminorm_le_of_centered_bound {s : Set E} {x : E}
    {r : E → ℝ} {p q : Seminorm ℝ E} {B : ℝ}
    (hx : Tendsto (fun t => μ (s ∩ closedBall x t) / μ (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (hr : (fun y => r y-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    (hbound : ∀ y ∈ s, r y ≤ B*q (y-x)) (v : E) : p v ≤ B*q v := by
  have hv : v ∈ tangentConeAt ℝ s x := by
    rw [tangentConeAt_eq_univ_of_density_one μ s x hx]
    exact mem_univ v
  obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hv
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd₀,hd⟩
  have hsmall := (hr.comp_tendsto ht).norm_right.mul_isBigO
    (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => ‖(x+d j)-x‖*‖c j‖) atTop (𝓝 ‖v‖) := by
    simpa only [norm_smul,add_sub_cancel_left,mul_comm] using hcd.norm
  have hzero := hsmall.tendsto_zero_of_tendsto hnorm
  have hp := (seminorm_continuous_finiteDimensional p).tendsto v |>.comp hcd
  have hlim : Tendsto (fun j => ‖c j‖*r (x+d j)) atTop (𝓝 (p v)) := by
    convert hzero.add hp using 1
    · ext j
      simp only [Function.comp_apply,add_sub_cancel_left,map_smul_eq_mul]
      ring
    · simp
  have hq : Tendsto (fun j => B*(‖c j‖*q (d j))) atTop (𝓝 (B*q v)) := by
    simpa only [Function.comp_apply,map_smul_eq_mul] using
      (((seminorm_continuous_finiteDimensional q).tendsto v).comp hcd).const_mul B
  apply le_of_tendsto_of_tendsto hlim hq
  filter_upwards [hd] with j hj
  have hh := mul_le_mul_of_nonneg_left (hbound (x+d j) hj) (norm_nonneg (c j))
  simpa only [add_sub_cancel_left,mul_left_comm] using hh

end CAT0Fillings

namespace CAT0Fillings.MetricDifferentiation
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {X : Type*} [MetricSpace X]

lemma HasCenteredMetricDifferentialWithin.seminorm_le_on_piece
    {s t : Set E} (hts : t ⊆ s) {f : s → X} {p q : Seminorm ℝ E} {x : s}
    (h : HasCenteredMetricDifferentialWithin s f p x)
    (hx : Tendsto (fun r => μ (t ∩ closedBall (x : E) r) / μ (closedBall (x : E) r))
      (𝓝[>] 0) (𝓝 1)) {B : ℝ}
    (hb : ∀ y (hy : y ∈ t), dist (f ⟨y,hts hy⟩) (f x) ≤ B*q (y-(x : E))) :
    ∀ v : E, p v ≤ B*q v := by
  classical
  let r : E → ℝ := fun z => if hz : z ∈ s then dist (f ⟨z,hz⟩) (f x) else 0
  have hr : (fun y => r y-p (y-(x : E))) =o[𝓝[s] (x : E)] (fun y => y-(x : E)) := by
    rw [nhdsWithin_eq_map_subtype_coe x.property,Asymptotics.isLittleO_map]
    simpa only [HasCenteredMetricDifferentialWithin,Function.comp_def,r,
      dite_eq_left (Subtype.coe_prop _),Subtype.coe_eta] using h
  apply seminorm_le_of_centered_bound μ hx (hr.mono (nhdsWithin_mono _ hts))
  intro y hy
  simpa only [r,dite_eq_left (hts hy)] using hb y hy

end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_HilbertMass
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix MeasureTheory Set Filter
open scoped MatrixOrder NNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma hilbert_piece_mass_le
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (p : Euc k → Seminorm ℝ (Euc k)) (q : Seminorm ℝ (Euc k))
    (hq : ∀ v, q v = 0 ↔ v = 0)
    (hqpara : ∀ u v, q (u+v)^2+q (u-v)^2 = 2*q u^2+2*q v^2)
    (hp : ∀ᵐ z ∂volume.restrict t,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ v, p z v = 0 ↔ v = 0) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2))
    (K L : ℝ≥0)
    (hnear : ∀ y (hy : y ∈ t) z (hz : z ∈ t),
      q (y-z) ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩) ∧
      dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩) ≤ (L : ℝ)*q (y-z)) :
    densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| *
        Real.sqrt (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      ≤ (((L*K)^k) • ν).restrict (C.paramExtended '' t) := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let Q := polarizationMatrix q b
  let Jq := Real.sqrt Q.det
  have hQ : Q.PosDef := polarizationMatrix_posDef b q hq hqpara
  let ℓ : Fin k → Euc k →L[ℝ] ℝ := fun i => matrixRowFunctional (CFC.sqrt Q) i
  have hrow : ∀ i y (hy : y ∈ t) z (hz : z ∈ t),
      |ℓ i y-ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩) := by
    intro i y hy z hz
    rw [←map_sub]
    apply (abs_matrixRow_sqrt_le Q hQ.posSemidef i (y-z)).trans
    simpa only [Q,b,sqrt_polarization_quadratic q hq hqpara,WithLp.toLp_ofLp] using
      (hnear y hy z hz).1
  have hm : (Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)) = CFC.sqrt Q := by
    ext i j
    simp only [ℓ,Matrix.of_apply,matrixRowFunctional_single]
  have hdet : |(CFC.sqrt Q).det| = Jq := by
    rw [show (CFC.sqrt Q).det = Real.sqrt Q.det by simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  have hpiece : densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| * Jq) ≤ ((K^k) • ν).restrict (C.paramExtended '' t) := by
    simpa only [hm,hdet] using C.linear_piece_mass_le hC hν ht hts ℓ K hrow
  have hJ : ∀ᵐ z ∂volume.restrict t,
      Real.sqrt (polarizationMatrix (p z) b).det ≤ (L : ℝ)^k * Jq := by
    filter_upwards [hp,ae_restrict_mem ht,Besicovitch.ae_tendsto_measure_inter_div volume t]
      with z hz hzt hzd
    apply sqrt_det_polarization_le (p z) q hz.2.1 hq hz.2.2 hqpara L.coe_nonneg
    apply (hz.1 (hts hzt)).seminorm_le_on_piece volume hts hzd
    intro y hy
    exact (hnear y hy z hzt).2
  calc
    _ ≤ densityPush (volume.restrict t) C.paramExtended
        (fun z => ((L^k : ℝ≥0) : ℝ) * (|(C.multiplicity z : ℝ)| * Jq)) := by
      apply densityPush_mono_ae C.measurable_paramExtended
      filter_upwards [hJ] with z hz
      have hh := mul_le_mul_of_nonneg_left hz (abs_nonneg (C.multiplicity z : ℝ))
      simpa only [NNReal.coe_pow,mul_left_comm] using hh
    _ = (L^k) • densityPush (volume.restrict t) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)| * Jq) :=
          densityPush_const_mul _ _ _ _ C.measurable_paramExtended
    _ ≤ (L^k) • (((K^k) • ν).restrict (C.paramExtended '' t)) := by
      exact smul_le_smul_left (L^k) hpiece
    _ = (((L*K)^k) • ν).restrict (C.paramExtended '' t) := by
      rw [Measure.restrict_smul,smul_smul,←mul_pow,←Measure.restrict_smul]

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_Partitions
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
lemma exists_radius_uniform_metric_error
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ s ∩ ball x δ, ∀ z ∈ s ∩ ball x δ,
      |dist (f y) (f z)-metricSeminorm f x (y-z)| ≤ ε*‖y-z‖ := by
  have hp := eventually_seminorm_bound_of_dense (fun y => metricSeminorm_lipschitz hf y)
    (metricSeminorm_lipschitz hf x) (denseRange_denseSeq E) hc (half_pos hε)
  obtain ⟨a,ha,hap⟩ := Metric.mem_nhdsWithin_iff.1 hp
  obtain ⟨N,hN⟩ := (eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hu (ε/2) (half_pos hε)))
  have hNN := hN N le_rfl
  refine ⟨min a (r N/3), lt_min ha (div_pos (hr N) (by norm_num)), ?_⟩
  intro y hy z hz
  have hyp : ∀ v : E, |metricSeminorm f y v-metricSeminorm f x v| ≤ ε/2*‖v‖ :=
    hap ⟨show dist y x < a from lt_of_lt_of_le hy.2 (min_le_left _ _),hy.1⟩
  have hyz : ‖z-y‖ < r N := by
    have h₁ : ‖y-x‖ < r N/3 := by
      exact lt_of_lt_of_le (by simpa only [mem_ball,dist_eq_norm] using hy.2) (min_le_right _ _)
    have h₂ : ‖z-x‖ < r N/3 := by
      exact lt_of_lt_of_le (by simpa only [mem_ball,dist_eq_norm] using hz.2) (min_le_right _ _)
    have h₃ : ‖z-y‖ ≤ ‖z-x‖+‖y-x‖ := by
      calc ‖z-y‖ = ‖(z-x)-(y-x)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith [hr N]
  have he₁ := metricErrorModulus_bound hf y (z-y) hyz
  have he₂ := hyp (z-y)
  have hm : metricErrorModulus f (r N) y < ε/2 := by
    have hm := hNN y hy.1
    simpa only [dist_zero_left,Real.norm_eq_abs,
      abs_of_nonneg (metricErrorModulus_nonneg hf _ _)] using hm
  have hpneg : metricSeminorm f x (y-z) = metricSeminorm f x (z-y) := by
    rw [←neg_sub z y,map_neg_eq_map]
  rw [hpneg,dist_comm,norm_sub_rev]
  calc |dist (f z) (f y)-metricSeminorm f x (z-y)| ≤
        |dist (f z) (f y)-metricSeminorm f y (z-y)| +
          |metricSeminorm f y (z-y)-metricSeminorm f x (z-y)| := abs_sub_le _ _ _
    _ ≤ metricErrorModulus f (r N) y*‖z-y‖+ε/2*‖z-y‖ := by
      apply add_le_add _ he₂
      simpa only [←add_sub_assoc,add_sub_cancel_left] using he₁
    _ ≤ ε*‖z-y‖ := by nlinarith [norm_nonneg (z-y)]

lemma exists_radius_nearIsometric
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ s ∩ ball x δ, ∀ z ∈ s ∩ ball x δ,
      (1-ε)*metricSeminorm f x (y-z) ≤ dist (f y) (f z) ∧
      dist (f y) (f z) ≤ (1+ε)*metricSeminorm f x (y-z) := by
  obtain ⟨δ,hδ,H⟩ := exists_radius_uniform_metric_error hf hc hr hu (div_pos hε hA)
  refine ⟨δ,hδ,?_⟩
  intro y hy z hz
  have he : |dist (f y) (f z)-metricSeminorm f x (y-z)| ≤
      ε*metricSeminorm f x (y-z) := by
    apply (H y hy z hz).trans
    calc (ε/A)*‖y-z‖ ≤ (ε/A)*(A*metricSeminorm f x (y-z)) :=
          mul_le_mul_of_nonneg_left (hbound _) (div_pos hε hA).le
      _ = ε*metricSeminorm f x (y-z) := by field_simp
  obtain ⟨hl,hr⟩ := abs_le.1 he
  constructor <;> linarith

lemma exists_nearIsometric_partition
    [MeasurableSpace E] [BorelSpace E] {s : Set E} [Nonempty s]
    (hs : MeasurableSet s) (hf : LipschitzWith K f)
    (hc : ∀ x ∈ s, ∀ j : ℕ, ContinuousWithinAt
      (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ x ∈ s, ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → s) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      (⋃ i, t i) = s ∧ ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  choose δ hδ hlocal using fun x : s =>
    exists_radius_nearIsometric hf (hc x x.property) hr hu hA (hbound x x.property) hε
  obtain ⟨c,hcvr⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
    (fun x : s => ball (x : E) (δ x)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨⟨x,hx⟩,mem_ball_self (hδ ⟨x,hx⟩)⟩)
  let t : ℕ → Set E := fun i => s ∩ ball (c i : E) (δ (c i))
  refine ⟨c,disjointed t, fun i => MeasurableSet.disjointed
    (fun j => hs.inter isOpen_ball.measurableSet) i,disjoint_disjointed t,?_,?_⟩
  · rw [iUnion_disjointed]
    apply Subset.antisymm
    · exact iUnion_subset (fun i => inter_subset_left)
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.1 (hcvr hx)
      exact mem_iUnion.2 ⟨i,hx,hi⟩
  · intro i y hy z hz
    exact hlocal (c i) y (disjointed_le t i hy) z (disjointed_le t i hz)

end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_ae_nearIsometric_partition
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ x ∈ s, ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      (∀ i, (t i).Nonempty → c i ∈ s) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  classical
  let r : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
    filter_upwards [(ae_hasCenteredMetricDifferential μ hf).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))] with x hx
    exact metricErrorModulus_tendsto_zero hf hx hr0
  have H (j : ℕ) := exists_large_continuousOn_uniformly μ hs hsf
    (show Measurable (fun x i => metricSeminorm f x (denseSeq E i)) from
      Measurable.of_eval (fun index => measurable_metricSeminorm_apply hf (denseSeq E index)))
    (fun i => measurable_metricErrorModulus hf (r i)) hc (hr j)
  choose u hus hum hμu hcu huu using H
  have HP (j : ℕ) : ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (⋃ i, t i) = u j ∧
      (∀ i, (t i).Nonempty → c i ∈ s) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
    by_cases hne : (u j).Nonempty
    · let _ : Nonempty (u j) := hne.to_subtype
      obtain ⟨c,t,ht,_,htu,hineq⟩ := exists_nearIsometric_partition (hum j) hf
        (fun x hx i => (continuousOn_pi.1 (hcu j) i) x hx) hr (huu j) hA
        (fun x hx => hbound x (hus j hx)) hε
      exact ⟨fun i => c i,t,ht,htu,fun i _ => hus j (c i).property,hineq⟩
    · refine ⟨fun _ => 0,fun _ => ∅,fun _ => MeasurableSet.empty,?_,?_,?_⟩
      · simp [not_nonempty_iff_eq_empty.mp hne]
      · simp
      · simp
  choose c t htm htunion hcs htineq using HP
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let T : ℕ → Set E := fun i => t (e i).1 (e i).2
  have hTunion : (⋃ i, T i) = ⋃ j, u j := by
    ext x
    simp only [T,mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨(e i).1,htunion (e i).1 ▸ mem_iUnion.2 ⟨(e i).2,hi⟩⟩
    · rintro ⟨j,hj⟩
      obtain ⟨i,hi⟩ := mem_iUnion.1 ((htunion j).symm ▸ hj)
      refine ⟨e.symm (j,i),?_⟩
      simpa using hi
  have hu0 : μ (s \ ⋃ j, u j) = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto (by simpa using ENNReal.tendsto_ofReal hr0)
    filter_upwards [] with j
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion u j))).trans (hμu j)
  refine ⟨fun i => c (e i).1 (e i).2,disjointed T,
    fun i => MeasurableSet.disjointed (fun k => htm (e k).1 (e k).2) i,
    ?_,disjoint_disjointed T,?_,?_,?_⟩
  · intro i x hx
    apply hus (e i).1
    rw [←htunion (e i).1]
    exact mem_iUnion.2 ⟨(e i).2,disjointed_le T i hx⟩
  · rw [iUnion_disjointed,hTunion]
    exact hu0
  · intro i hi
    exact hcs _ _ (hi.mono (disjointed_le T i))
  · intro i y hy z hz
    exact htineq _ _ y (disjointed_le T i hy) z (disjointed_le T i hz)

end CAT0Fillings.MetricDifferentiation
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_HilbertPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
theorem exists_ae_nearIsometric_partition_with_property
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {P : E → Prop} (hP : ∀ᵐ x ∂μ.restrict s, P x)
    {A : ℝ} (hA : 0 < A)
    (hbound : ∀ x ∈ s, P x → ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      (∀ i, (t i).Nonempty → c i ∈ s ∧ P (c i)) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  classical
  have hnull : μ {x | ¬(x ∈ s → P x)} = 0 :=
    ae_iff.mp ((ae_restrict_iff' hs).mp hP)
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null hnull
  let s₀ := s \ N
  have hs₀ : MeasurableSet s₀ := hs.diff hNm
  have hprop : ∀ x ∈ s₀, P x := by
    intro x hx
    by_contra hp
    exact hx.2 (hN (by simpa using And.intro hx.1 hp))
  obtain ⟨c,t,htm,hts,hdisj,ht0,hcs,hineq⟩ :=
    exists_ae_nearIsometric_partition μ hf hs₀
      ((measure_mono sdiff_subset).trans_lt hsf.lt_top).ne hA
      (fun x hx => hbound x hx.1 (hprop x hx)) hε
  refine ⟨c,t,htm,fun i => (hts i).trans sdiff_subset,hdisj,?_,?_,hineq⟩
  · apply le_antisymm _ bot_le
    calc μ (s \ ⋃ i, t i) ≤ μ (N ∪ (s₀ \ ⋃ i, t i)) := by
          apply measure_mono
          intro x hx
          by_cases hn : x ∈ N
          · exact Or.inl hn
          · exact Or.inr ⟨⟨hx.1,hn⟩,hx.2⟩
      _ ≤ μ N + μ (s₀ \ ⋃ i, t i) := measure_union_le _ _
      _ = 0 := by rw [hN0,ht0,add_zero]
  · intro i hi
    exact ⟨(hcs i hi).1,hprop _ (hcs i hi)⟩

end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]

theorem exists_hilbertian_nearIsometric_chart_partition
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hJ : AntilipschitzWith J f)
    (hQ : ∀ a b c d : s,
      dist (f a) (f c)^2+dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2+dist (f b) (f c)^2+dist (f c) (f d)^2+dist (f d) (f a)^2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (p : ℕ → Seminorm ℝ E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      (∀ i, LipschitzWith K (p i)) ∧
      (∀ i, (t i).Nonempty →
        (∀ u v, p i (u+v)^2+p i (u-v)^2 = 2*p i u^2+2*p i v^2) ∧
        (∀ v, ‖v‖ ≤ (J : ℝ)*p i v)) ∧
      ∀ i, ∀ y : s, (y : E) ∈ t i → ∀ z : s, (z : E) ∈ t i →
        (1-ε)*p i ((y : E)-(z : E)) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*p i ((y : E)-(z : E)) := by
  classical
  let Y := Set.range f
  let : SeparableSpace Y := (isSeparable_range hf.continuous).separableSpace
  let F : s → Y := fun x => ⟨f x,x,rfl⟩
  let e := kuratowskiEmbedding Y
  have he : Isometry e := kuratowskiEmbedding.isometry Y
  let F₀ : E → ↥(lp (fun _ : ℕ => ℝ) (⊤ : ENNReal)) :=
    fun x => if hx : x ∈ s then e (F ⟨x,hx⟩) else 0
  have hF₀ : LipschitzOnWith K F₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    dsimp only [F₀]
    rw [dite_eq_left hx,dite_eq_left hy,he.dist_eq]
    exact hf.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,heq⟩ := hF₀.extend_lp_infty
  let Z := Set.range g
  let : SeparableSpace Z := (isSeparable_range hg.continuous).separableSpace
  let : Nonempty Z := ⟨⟨g 0,0,rfl⟩⟩
  let G : E → Z := fun x => ⟨g x,x,rfl⟩
  have hG : LipschitzWith K G := by
    apply LipschitzWith.of_dist_le_mul
    exact hg.dist_le_mul
  have hdist (y z : s) : dist (G y) (G z) = dist (f y) (f z) := by
    change dist (g y) (g z) = _
    rw [←heq y.property, ←heq z.property]
    dsimp only [F₀]
    rw [dite_eq_left y.property,dite_eq_left z.property]
    exact he.dist_eq (F y) (F z)
  have hQG : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (G a) (G c)^2+dist (G b) (G d)^2 ≤
        dist (G a) (G b)^2+dist (G b) (G c)^2+dist (G c) (G d)^2+dist (G d) (G a)^2 := by
    intro a ha b hb c hc d hd
    simpa only [← hdist] using hQ ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩
  have hJG : ∀ a ∈ s, ∀ b ∈ s, (1 : ℝ)*dist a b ≤ (J : ℝ)*dist (G a) (G b) := by
    intro a ha b hb
    have hh := hJ.le_mul_dist ⟨a,ha⟩ ⟨b,hb⟩
    change dist a b ≤ (J : ℝ)*dist (f ⟨a,ha⟩) (f ⟨b,hb⟩) at hh
    simpa only [←hdist,one_mul] using hh
  let P : E → Prop := fun x =>
    (∀ u v, metricSeminorm G x (u+v)^2+metricSeminorm G x (u-v)^2 =
      2*metricSeminorm G x u^2+2*metricSeminorm G x v^2) ∧
    (∀ v, ‖v‖ ≤ (J : ℝ)*metricSeminorm G x v)
  have hP : ∀ᵐ x ∂μ.restrict s, P x := by
    filter_upwards [ae_metricSeminorm_parallelogram_on μ hG hs hsf hQG,
      ae_metricSeminorm_distance_bound_on μ hG hs hsf hJG] with x hx hj
    exact ⟨hx,by simpa only [one_mul] using hj⟩
  obtain ⟨c,t,htm,hts,hdisj,ht0,hcs,hineq⟩ :=
    exists_ae_nearIsometric_partition_with_property μ hG hs hsf hP
      (A := (J : ℝ)+1) (by positivity)
      (fun x _ hx v => (hx.2 v).trans <| mul_le_mul_of_nonneg_right
        (by linarith) (apply_nonneg (metricSeminorm G x) v)) hε
  refine ⟨fun i => metricSeminorm G (c i),t,htm,hts,hdisj,ht0,
    fun i => metricSeminorm_lipschitz hG (c i),fun i hi => (hcs i hi).2,?_⟩
  intro i y hy z hz
  simpa only [hdist] using hineq i y hy z hz
end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_ExactMass
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma hilbert_mass_measure_le (hX : IsCAT0 X)
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ v, p z v = 0 ↔ v = 0) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2)) :
    C.majorantMeasure (fun z => Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det) ≤ ν := by
  obtain ⟨A,B,hA,hB⟩ := C.bilipschitz
  apply measure_le_of_nearIsometry_factors k
  intro ε hε hε1
  let L : ℝ≥0 := ⟨1+ε,by linarith⟩
  let K : ℝ≥0 := ⟨(1-ε)⁻¹, inv_nonneg.mpr (by linarith)⟩
  have hcoeff : ENNReal.ofReal (((1+ε)/(1-ε))^k) = ((L*K)^k : ℝ≥0) := by
    rw [←ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [hcoeff]
  change _ ≤ ((L*K)^k) • ν
  obtain ⟨q,t,ht,hts,hdisj,hnull,_,hq,hnear⟩ :=
    MetricDifferentiation.exists_hilbertian_nearIsometric_chart_partition volume
      C.borel C.bounded.measure_lt_top.ne hA hB
      (fun a b c d => hX.quadrilateral (C.param a) (C.param b) (C.param c) (C.param d)) hε
  apply densityPush_le_of_partition C.measurable_paramExtended _ ht hts hdisj hnull
    (fun i => C.measurableSet_paramExtended_image (ht i) (hts i))
  · intro x hx y hy hxy
    exact congrArg (fun z : C.domain => (z : Euc k)) (hB.injective
      (show C.param ⟨x,hx⟩ = C.param ⟨y,hy⟩ from by
        simpa only [paramExtended,dite_eq_left hx,dite_eq_left hy] using hxy))
  intro i
  by_cases hi : (t i).Nonempty
  · have hq0 : ∀ v, q i v = 0 ↔ v = 0 := by
      intro v
      constructor
      · intro hv
        have hh := (hq i hi).2 v
        rw [hv,mul_zero] at hh
        exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
      · rintro rfl
        exact map_zero _
    apply C.hilbert_piece_mass_le hC hν (ht i) (hts i) p (q i) hq0 (hq i hi).1
      (hp.filter_mono (ae_mono (Measure.restrict_mono (hts i) le_rfl))) K L
    intro y hy z hz
    have hh := hnear i ⟨y,hts i hy⟩ hy ⟨z,hts i hz⟩ hz
    refine ⟨?_,hh.2⟩
    change q i (y-z) ≤ (1-ε)⁻¹ * _
    rw [←div_eq_inv_mul]
    apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
    simpa only [mul_comm] using hh.1
  · have he : t i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    simp only [he,Measure.restrict_empty,densityPush,withDensity_zero_left,Measure.map_zero,
      image_empty,le_refl]

end IntegerChart
end CAT0Fillings

namespace CAT0Fillings.MetricDifferentiation
open MeasureTheory Set Metric Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X]

lemma chart_matrix_determinant_bound {n : ℕ}
    {s : Set (Euc n)} (hs : MeasurableSet s) {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (p : Euc n → Seminorm ℝ (Euc n))
    (hpm : ∀ v, Measurable (fun x => p x v))
    (hpLip : ∀ x, LipschitzWith K (p x))
    (hae : ∀ᵐ x ∂volume.restrict s,
      (∀ hx : x ∈ s, HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩) ∧
      (∀ u v, p x (u+v)^2+p x (u-v)^2 = 2*p x u^2+2*p x v^2) ∧
      (∀ v, ‖v‖ ≤ (J : ℝ)*p x v)) :
    let P := fun x => polarizationMatrix (p x) (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (∀ i j, Measurable (fun x => P x i j)) ∧
    (∀ᵐ x ∂volume.restrict s, (P x).PosDef) ∧
    (∀ᵐ x ∂volume.restrict s, Real.sqrt (P x).det ≤ (K : ℝ)^n) ∧
    ∀ π : Fin n → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ x ∂volume.restrict s,
        |(Matrix.of fun i j =>
          fderivWithin ℝ (scalarOn f (π i)) s x (EuclideanSpace.single j 1)).det| ≤
              Real.sqrt (P x).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hzero : ∀ᵐ x ∂volume.restrict s, ∀ v, p x v = 0 ↔ v = 0 := by
    filter_upwards [hae] with x hx v
    constructor
    · intro hv
      have hn := hx.2.2 v
      rw [hv,mul_zero] at hn
      exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg v))
    · rintro rfl
      exact map_zero (p x)
  refine ⟨measurable_polarizationMatrix p b hpm,?_,?_,?_⟩
  · filter_upwards [hae,hzero] with x hx hz
    exact polarizationMatrix_posDef b (p x) hz hx.2.1
  · filter_upwards [hae,hzero] with x hx hz
    apply sqrt_det_le_pow_of_quadratic_bound _
      (polarizationMatrix_posDef b (p x) hz hx.2.1).posSemidef K.coe_nonneg
    intro v
    let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    have hrepr : b.repr w = v := by ext j; simp [b,w]
    have hJ : v ⬝ᵥ (polarizationMatrix (p x) b).mulVec v = (p x w)^2 := by
      simpa only [hrepr] using polarizationMatrix_quadratic b (p x) hz hx.2.1 w
    rw [hJ,Real.sqrt_sq (apply_nonneg (p x) w)]
    simpa only [dist_zero_right,map_zero,Real.norm_eq_abs, abs_of_nonneg (apply_nonneg (p x) w)] using (hpLip x).dist_le_mul w 0
  intro π hπ
  have hdiff : ∀ᵐ x ∂volume.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩ := hae.mono fun x hx => hx.1
  have hrows : ∀ᵐ x ∂volume.restrict s, ∀ i v,
      |fderivWithin ℝ (scalarOn f (π i)) s x v| ≤ p x v := by
    rw [eventually_all]
    intro i
    simpa only [NNReal.coe_one,one_mul] using ae_scalarOn_derivative_bound volume hs hf hdiff (hπ i)
  filter_upwards [hae,hzero,hrows] with x hx hz hrow
  apply abs_det_le_sqrt_det_of_posDef _ _ (polarizationMatrix_posDef b (p x) hz hx.2.1)
  intro i v
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hrepr : b.repr w = v := by
    ext j
    simp [b,w]
  have hJ : v ⬝ᵥ (polarizationMatrix (p x) b).mulVec v = (p x w)^2 := by
    simpa only [hrepr] using polarizationMatrix_quadratic b (p x) hz hx.2.1 w
  rw [hJ,Real.sqrt_sq (apply_nonneg (p x) w)]
  convert hrow i w using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  have hb : ∑ j, v j • EuclideanSpace.single j (1 : ℝ) = w := by
    convert b.sum_repr w using 1
    all_goals try with_reducible_and_instances rfl
    simp only [hrepr]
    congr 1
    ext j
    simp [b]
  rw [←hb,map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.of_apply, dotProduct, mul_comm]
end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings
open MeasureTheory Set Filter

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

theorem exists_exact_quadratic_mass (hX : IsCAT0 X) (hC : IsMetricCurrent C.action) :
    ∃ P : Euc k → Matrix (Fin k) (Fin k) ℝ,
      (∀ i j, Measurable (fun z => P z i j)) ∧
      (∀ᵐ z ∂volume.restrict C.domain, (P z).PosDef) ∧
      Integrable (fun z => |(C.multiplicity z : ℝ)| * Real.sqrt (P z).det)
        (volume.restrict C.domain) ∧
      IsFiniteMeasure (C.majorantMeasure (fun z => Real.sqrt (P z).det)) ∧
      Controls C.action (C.majorantMeasure (fun z => Real.sqrt (P z).det)) ∧
      (∀ (ν : Measure X), IsFiniteMeasure ν → Controls C.action ν →
        C.majorantMeasure (fun z => Real.sqrt (P z).det) ≤ ν) ∧
      ∃ p : Euc k → Seminorm ℝ (Euc k),
        P = (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) ∧
        (∀ v, Measurable (fun z => p z v)) ∧
        ∀ᵐ z ∂volume.restrict C.domain,
          (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
            C.domain C.param (p z) ⟨z,hz⟩) ∧
          (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
          (∀ v, p z v = 0 ↔ v = 0) := by
  obtain ⟨K,L,hK,hL⟩ := C.bilipschitz
  obtain ⟨p,hpm,hpLip,hae⟩ := MetricDifferentiation.exists_hilbertian_chart_differential
    volume C.borel C.bounded.measure_lt_top.ne hK hL
    (fun a b c d => hX.quadrilateral (C.param a) (C.param b) (C.param c) (C.param d))
  let P := fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  obtain ⟨hPm,hP,hJ,hdet⟩ := MetricDifferentiation.chart_matrix_determinant_bound
    C.borel hK p hpm hpLip hae
  have hJm : Measurable (fun z => Real.sqrt (P z).det) := by
    apply Measurable.sqrt
    simp only [Matrix.det_apply']
    fun_prop
  have hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * Real.sqrt (P z).det)
      (volume.restrict C.domain) := by
    apply (C.integrable.abs.mul_const ((K : ℝ)^k)).mono'
      (C.integrable.abs.aestronglyMeasurable.mul hJm.aestronglyMeasurable)
    filter_upwards [hJ] with z hz
    change ‖|(C.multiplicity z : ℝ)| * Real.sqrt (P z).det‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  refine ⟨P,hPm,hP,hρ,densityPush_finite _ _ hρ,?_,?_,p,rfl,hpm,?_⟩
  · apply C.majorant_controls hρ (Eventually.of_forall fun z => Real.sqrt_nonneg _)
    exact hdet
  · intro ν hνfin hν
    let := hνfin
    apply C.hilbert_mass_measure_le hX hC hν p
    filter_upwards [hae] with z hz
    refine ⟨hz.1,?_,hz.2.1⟩
    intro v
    constructor
    · intro hv
      have hh := hz.2.2 v
      rw [hv,mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
    · rintro rfl
      exact map_zero _
  · filter_upwards [hae] with z hz
    refine ⟨hz.1,hz.2.1,?_⟩
    intro v
    constructor
    · intro hv
      have hh := hz.2.2 v
      rw [hv,mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
    · rintro rfl
      exact map_zero _

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_JacobianBound
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped MatrixOrder

lemma abs_det_le_prod_mul_sqrt_det_of_posDef {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef)
    (K : Fin n → ℝ) (hK : ∀ i, 0 ≤ K i)
    (h : ∀ i v, |L i ⬝ᵥ v| ≤ K i * Real.sqrt (v ⬝ᵥ P.mulVec v)) :
    |L.det| ≤ (∏ i, K i) * Real.sqrt P.det := by
  let Q := CFC.sqrt P
  have hQdet : Q.det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.posSemidef.det_sqrt
  have hQpos : 0 < Q.det := by rw [hQdet]; exact Real.sqrt_pos.2 hP.det_pos
  have hQi : IsUnit Q.det := isUnit_iff_ne_zero.2 (ne_of_gt hQpos)
  have hQinv := Matrix.mul_nonsing_inv Q hQi
  have hinvQ := Matrix.nonsing_inv_mul Q hQi
  have htrans (v : Fin n → ℝ) :
      Real.sqrt ((Q⁻¹).mulVec v ⬝ᵥ P.mulVec ((Q⁻¹).mulVec v)) =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    rw [dot_mulVec_sqrt P hP.posSemidef]
    change Real.sqrt (Q.mulVec ((Q⁻¹).mulVec v) ⬝ᵥ Q.mulVec ((Q⁻¹).mulVec v)) = _
    rw [Matrix.mulVec_mulVec, hQinv, Matrix.one_mulVec]
    have hn : v ⬝ᵥ v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
        real_inner_self_eq_norm_sq (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
    rw [hn,Real.sqrt_sq (norm_nonneg _)]
  have hB : |(L * Q⁻¹).det| ≤ ∏ i, K i := by
    apply (abs_det_le_prod_row_norm _).trans
    apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
    intro i _
    apply row_norm_le_of_dot_bound_const _ (hK i)
    intro v
    have hh := h i ((Q⁻¹).mulVec v)
    rw [htrans] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    change ((L * Q⁻¹).mulVec v) i = (L.mulVec ((Q⁻¹).mulVec v)) i
    rw [Matrix.mulVec_mulVec]
  have heq : L = (L * Q⁻¹) * Q := by rw [Matrix.mul_assoc,hinvQ,Matrix.mul_one]
  calc
    |L.det| = |(L * Q⁻¹).det| * Q.det := by
      conv_lhs => rw [heq, Matrix.det_mul]
      rw [abs_mul,abs_of_pos hQpos]
    _ ≤ (∏ i, K i)*Q.det := mul_le_mul_of_nonneg_right hB hQpos.le
    _ = (∏ i, K i) * Real.sqrt P.det := by rw [hQdet]

end CAT0Fillings

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma ae_jacobian_bound_quadratic
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0) (hπ : ∀ i, LipschitzWith (K i) (π i)) :
    ∀ᵐ z ∂volume.restrict C.domain,
      |C.jacobian π z| ≤ (∏ i, (K i : ℝ)) *
        Real.sqrt (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hrows : ∀ᵐ z ∂volume.restrict C.domain, ∀ i v,
      |fderivWithin ℝ (C.scalar (π i)) C.domain z v| ≤ K i * p z v := by
    rw [eventually_all]
    intro i
    exact MetricDifferentiation.ae_scalarOn_derivative_bound volume C.borel hL
      (hp.mono fun z hz => hz.1) (hπ i)
  filter_upwards [hp,hrows] with z hz hrow
  apply abs_det_le_prod_mul_sqrt_det_of_posDef _ _
    (polarizationMatrix_posDef b (p z) hz.2.2 hz.2.1) _ (fun i => (K i).coe_nonneg)
  intro i v
  let w : Euc k := WithLp.toLp 2 v
  have hrepr : b.repr w = v := by ext j; simp [b,w]
  have hJ : v ⬝ᵥ (polarizationMatrix (p z) b).mulVec v = (p z w)^2 := by
    simpa only [hrepr] using polarizationMatrix_quadratic b (p z) hz.2.2 hz.2.1 w
  rw [hJ,Real.sqrt_sq (apply_nonneg (p z) w)]
  convert hrow i w using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  have hb : ∑ j, v j • EuclideanSpace.single j (1:ℝ) = w := by
    convert b.sum_repr w using 1
    all_goals try with_reducible_and_instances rfl
    simp only [hrepr]
    congr 1
    ext j
    simp [b]
  rw [←hb,map_sum]
  simp only [map_smul,smul_eq_mul,dotProduct,mul_comm]

end CAT0Fillings.IntegerChart

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_MassTests
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.Foundations
open MeasureTheory Set Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
abbrev UnitTestClass (d K : ℕ) :=
  {p : TestClass (X := X) d K // ∀ i, LipschitzWith 1 (p.val.2 i)}

instance unitTestClass_nonempty (d K : ℕ) : Nonempty (UnitTestClass (X := X) d K) := by
  refine ⟨⟨⟨(0,fun _ => 0),?_,?_,?_⟩,?_⟩⟩
  · exact (LipschitzWith.const 0).weaken (by positivity)
  · simp
  · intro i
    exact (LipschitzWith.const 0).weaken (by positivity)
  · intro i
    exact (LipschitzWith.const 0).weaken (by positivity)

lemma TestClass.continuous_integral_abs (d K : ℕ) (μ : Measure X) [IsFiniteMeasure μ] :
    Continuous (fun p : TestClass (X := X) d K => ∫ x, |p.val.1 x| ∂μ) := by
  apply continuous_of_dominated (bound := fun _ => (K:ℝ))
  · intro p
    exact p.val.1.continuous.abs.measurable.aestronglyMeasurable
  · intro p
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs,abs_abs] using (p.val.1.norm_coe_le_norm x).trans p.property.2.1
  · exact integrable_const _
  · exact Eventually.of_forall fun x => by fun_prop

theorem exists_countable_mass_tests (d : ℕ) :
    ∃ (b : ℕ → ℕ → X → ℝ) (π : ℕ → ℕ → Fin d → X → ℝ),
      (∀ K j, BoundedLip (b K j) ∧ ∀ i, LipschitzWith 1 (π K j i)) ∧
      ∀ T : Functional X d, IsMetricCurrent T →
        ∀ μ : Measure X, IsFiniteMeasure μ →
          (∀ K j, |T (b K j) (π K j)| ≤ ∫ x, |b K j x| ∂μ) → Controls T μ := by
  choose p hp using fun K : ℕ => TopologicalSpace.exists_dense_seq (UnitTestClass (X := X) d K)
  refine ⟨fun K j => (p K j).val.val.1,fun K j i => (p K j).val.val.2 i,?_,?_⟩
  · intro K j
    exact ⟨(p K j).val.boundedLip,(p K j).property⟩
  · intro T hT μ hμ he b π hb hπ
    let := hμ
    obtain ⟨K,q,hbq,hπq⟩ := admissible_mem_testClass (show Admissible b π from ⟨hb,fun i => ⟨1,hπ i⟩⟩)
    let q' : UnitTestClass (X := X) d K := ⟨q,by
      intro i
      have hi : (q.val.2 i : X → ℝ) = π i := congrFun hπq i
      simpa only [hi] using hπ i⟩
    have hh : |TestClass.eval T q'.val| ≤ ∫ x, |q'.val.val.1 x| ∂μ := by
      apply (hp K).induction_on (p := fun r : UnitTestClass (X := X) d K =>
        |TestClass.eval T r.val| ≤ ∫ x, |r.val.val.1 x| ∂μ) q'
      · apply isClosed_le
        · exact ((IsMetricCurrent.testClass_continuous hT K).comp continuous_subtype_val).abs
        · exact (TestClass.continuous_integral_abs d K μ).comp continuous_subtype_val
      · intro j
        exact he K j
    simpa only [q',TestClass.eval,hbq,hπq] using hh

theorem ae_controls_of_testwise_bound {A : Type*} [MeasurableSpace A] (ν : Measure A)
    {d : ℕ} {T : A → Functional X d} {μ : A → Measure X}
    (hT : ∀ᵐ a ∂ν, IsMetricCurrent (T a))
    (hμ : ∀ᵐ a ∂ν, IsFiniteMeasure (μ a))
    (hb : ∀ b π, BoundedLip b → (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ a ∂ν, |T a b π| ≤ ∫ x, |b x| ∂μ a) :
    ∀ᵐ a ∂ν, Controls (T a) (μ a) := by
  obtain ⟨b,π,ht,hd⟩ := exists_countable_mass_tests (X := X) d
  have hc : ∀ᵐ a ∂ν, ∀ K j, |T a (b K j) (π K j)| ≤ ∫ x, |b K j x| ∂μ a :=
    ae_all_iff.mpr fun K => ae_all_iff.mpr fun j => hb _ _ (ht K j).1 (ht K j).2
  filter_upwards [hT,hμ,hc] with a hta hma hca
  exact hd _ hta _ hma hca

end CAT0Fillings.Foundations
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_EuclideanSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Prism

lemma split_single_succ (k : ℕ) (j : Fin k) :
    split k (EuclideanSpace.single j.succ 1) = (0,EuclideanSpace.single j 1) := by
  ext <;> simp

end CAT0Fillings.Prism

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_CoordinateChart
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
noncomputable def coordinateLayer (k : ℕ) (t : ℝ) (z : Euc k) : Euc (k+1) :=
  (Prism.split k).symm (t,z)

lemma coordinateLayer_lipschitz (t : ℝ) :
    LipschitzWith ‖(Prism.split k).symm.toContinuousLinearMap‖₊ (coordinateLayer k t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := (Prism.split k).symm.toContinuousLinearMap.lipschitz.dist_le_mul (t,z) (t,w)
  simpa only [coordinateLayer,ContinuousLinearEquiv.coe_coe,Prod.dist_eq,dist_self,
    max_eq_right dist_nonneg] using h

lemma coordinateLayer_antilipschitz (t : ℝ) :
    AntilipschitzWith ‖(Prism.split k).toContinuousLinearMap‖₊ (coordinateLayer k t) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have h := (Prism.split k).toContinuousLinearMap.lipschitz.dist_le_mul (coordinateLayer k t z) (coordinateLayer k t w)
  simpa only [coordinateLayer,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply,Prod.dist_eq,dist_self,
    max_eq_right dist_nonneg] using h

noncomputable def coordinateDomain (t : ℝ) : Set (Euc k) :=
  coordinateLayer k t ⁻¹' C.domain

lemma measurableSet_coordinateDomain (t : ℝ) : MeasurableSet (C.coordinateDomain t) :=
  C.borel.preimage (coordinateLayer_lipschitz (k := k) t).continuous.measurable

lemma bounded_coordinateDomain (t : ℝ) : Bornology.IsBounded (C.coordinateDomain t) := by
  apply Bornology.IsBounded.subset (LipschitzWith.prod_snd.isBounded_image ((Prism.split k).toContinuousLinearMap.lipschitz.isBounded_image C.bounded))
  intro z hz
  refine ⟨(t,z),?_,rfl⟩
  exact ⟨coordinateLayer k t z,hz,(Prism.split k).apply_symm_apply (t,z)⟩

noncomputable def coordinateParam (t : ℝ) (z : C.coordinateDomain t) : X :=
  C.param ⟨coordinateLayer k t z,z.2⟩

lemma coordinateParam_lipschitz (t : ℝ) {L : ℝ≥0} (hL : LipschitzWith L C.param) :
    LipschitzWith (L * ‖(Prism.split k).symm.toContinuousLinearMap‖₊) (C.coordinateParam t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := hL.dist_le_mul ⟨coordinateLayer k t z,z.2⟩ ⟨coordinateLayer k t w,w.2⟩
  have hh := (coordinateLayer_lipschitz (k := k) t).dist_le_mul z.val w.val
  change dist (C.coordinateParam t z) (C.coordinateParam t w) ≤ _ at h
  calc
    _ ≤ (L:ℝ) * dist (coordinateLayer k t z) (coordinateLayer k t w) := h
    _ ≤ (L:ℝ) * (‖(Prism.split k).symm.toContinuousLinearMap‖₊ * dist z.val w.val) :=
      mul_le_mul_of_nonneg_left hh L.coe_nonneg
    _ = _ := by simp only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq]

lemma coordinateParam_antilipschitz (t : ℝ) {U : ℝ≥0} (hU : AntilipschitzWith U C.param) :
    AntilipschitzWith (‖(Prism.split k).toContinuousLinearMap‖₊ * U) (C.coordinateParam t) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have h := hU.le_mul_dist ⟨coordinateLayer k t z,z.2⟩ ⟨coordinateLayer k t w,w.2⟩
  have hh := (coordinateLayer_antilipschitz (k := k) t).le_mul_dist z.val w.val
  calc
    dist z w ≤ ‖(Prism.split k).toContinuousLinearMap‖₊ *
        dist (coordinateLayer k t z) (coordinateLayer k t w) := hh
    _ ≤ ‖(Prism.split k).toContinuousLinearMap‖₊ *
        ((U:ℝ)*dist (C.coordinateParam t z) (C.coordinateParam t w)) :=
      mul_le_mul_of_nonneg_left h (NNReal.coe_nonneg _)
    _ = _ := by simp only [NNReal.coe_mul,mul_assoc]

lemma coordinateParam_bilipschitz (t : ℝ) : ∃ L U : ℝ≥0,
    LipschitzWith L (C.coordinateParam t) ∧ AntilipschitzWith U (C.coordinateParam t) := by
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  exact ⟨_,_,C.coordinateParam_lipschitz t hL,C.coordinateParam_antilipschitz t hU⟩

lemma ae_integrable_coordinateMultiplicity : ∀ᵐ t : ℝ,
    Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)) := by
  have hi : Integrable (C.domain.indicator (fun z => (C.multiplicity z:ℝ))) :=
    (integrable_indicator_iff C.borel).mpr C.integrable
  have hip : Integrable (fun p : ℝ × Euc k =>
      C.domain.indicator (fun z => (C.multiplicity z:ℝ)) ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  filter_upwards [hip.prod_right_ae] with t ht
  apply (integrable_indicator_iff (C.measurableSet_coordinateDomain t)).mp
  have heq : (C.coordinateDomain t).indicator (fun z => (C.multiplicity (coordinateLayer k t z):ℝ)) =
      fun z => C.domain.indicator (fun w => (C.multiplicity w:ℝ)) ((Prism.split k).symm (t,z)) := by
    funext z
    change (C.coordinateDomain t).indicator _ z = C.domain.indicator _ (coordinateLayer k t z)
    by_cases hz : coordinateLayer k t z ∈ C.domain
    · rw [indicator_of_mem (show z ∈ C.coordinateDomain t from hz),indicator_of_mem hz]
    · rw [indicator_of_notMem (show z ∉ C.coordinateDomain t from hz),indicator_of_notMem hz]
  rw [heq]
  exact ht

noncomputable def coordinateSlice (t : ℝ)
    (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))) : IntegerChart X k where
  domain := C.coordinateDomain t
  borel := C.measurableSet_coordinateDomain t
  bounded := C.bounded_coordinateDomain t
  param := C.coordinateParam t
  bilipschitz := C.coordinateParam_bilipschitz t
  multiplicity z := C.multiplicity (coordinateLayer k t z)
  integrable := ht

end CAT0Fillings.IntegerChart

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_CoordinateDerivative
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
lemma coordinateSlice_scalar_eq (t : ℝ)
    (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))) (f : X → ℝ)
    {z : Euc k} (hz : z ∈ C.coordinateDomain t) :
    (C.coordinateSlice t ht).scalar f z = C.scalar f (coordinateLayer k t z) := by
  rw [(C.coordinateSlice t ht).scalar_eq hz,C.scalar_eq hz]
  rfl

lemma coordinateSlice_fderiv (t : ℝ)
    (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))) {f : X → ℝ} {F : Euc (k+1) → ℝ}
    (heq : EqOn F (C.scalar f) C.domain) {z : Euc k}
    (hz : z ∈ C.coordinateDomain t) (hF : DifferentiableAt ℝ F (coordinateLayer k t z))
    (hu : UniqueDiffWithinAt ℝ C.domain (coordinateLayer k t z))
    (hv : UniqueDiffWithinAt ℝ (C.coordinateDomain t) z) (j : Fin k) :
    (fderivWithin ℝ ((C.coordinateSlice t ht).scalar f) (C.coordinateDomain t) z)
      (EuclideanSpace.single j 1) =
    (fderivWithin ℝ (C.scalar f) C.domain (coordinateLayer k t z))
      (EuclideanSpace.single j.succ 1) := by
  have hFC : fderivWithin ℝ (C.scalar f) C.domain (coordinateLayer k t z) =
      fderiv ℝ F (coordinateLayer k t z) :=
    (hF.hasFDerivAt.hasFDerivWithinAt.congr (fun w hw => (heq hw).symm) (heq hz).symm).fderivWithin hu
  let L : Euc k →L[ℝ] Euc (k+1) :=
    (Prism.split k).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ (Euc k))
  have hl : HasFDerivAt (coordinateLayer k t) L z := by
    exact (Prism.split k).symm.hasFDerivAt.comp z
      ((hasFDerivAt_const (𝕜 := ℝ) t z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z))
  have hFS : fderivWithin ℝ ((C.coordinateSlice t ht).scalar f) (C.coordinateDomain t) z =
      (fderiv ℝ F (coordinateLayer k t z)).comp L := by
    apply HasFDerivWithinAt.fderivWithin _ hv
    apply (hF.hasFDerivAt.comp z hl).hasFDerivWithinAt.congr
    · intro w hw
      rw [C.coordinateSlice_scalar_eq t ht f hw]
      exact (heq hw).symm
    · rw [C.coordinateSlice_scalar_eq t ht f hz]
      exact (heq hz).symm
  rw [hFC,hFS,ContinuousLinearMap.comp_apply]
  have hb : L (EuclideanSpace.single j 1) = EuclideanSpace.single j.succ 1 := by
    apply (Prism.split k).injective
    change Prism.split k ((Prism.split k).symm (0,EuclideanSpace.single j 1)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply,Prism.split_single_succ]
  rw [hb]

lemma ae_coordinateSlice_fderiv {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ t : ℝ, ∀ (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))),
    ∀ᵐ z ∂volume.restrict (C.coordinateDomain t), ∀ j : Fin k,
      (fderivWithin ℝ ((C.coordinateSlice t ht).scalar f) (C.coordinateDomain t) z)
        (EuclideanSpace.single j 1) =
      (fderivWithin ℝ (C.scalar f) C.domain (coordinateLayer k t z))
        (EuclideanSpace.single j.succ 1) := by
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨F,hF,heq⟩ := (C.scalar_lipschitzOn hL hf).extend_real
  have hfull : ∀ᵐ w : Euc (k+1), w ∈ C.domain →
      DifferentiableAt ℝ F w ∧ UniqueDiffWithinAt ℝ C.domain w := by
    filter_upwards [hF.ae_differentiableAt (μ := volume),
      (ae_restrict_iff' C.borel).mp (ae_uniqueDiffWithinAt volume C.domain)] with w hw hu
    exact fun hm => ⟨hw,hu hm⟩
  have hp := (Prism.split_symm_measurePreserving k).quasiMeasurePreserving.ae hfull
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with t ht
  intro hi
  have ht' : ∀ᵐ z ∂volume.restrict (C.coordinateDomain t),
      DifferentiableAt ℝ F (coordinateLayer k t z) ∧
      UniqueDiffWithinAt ℝ C.domain (coordinateLayer k t z) :=
    (ae_restrict_iff' (C.measurableSet_coordinateDomain t)).mpr ht
  filter_upwards [ht',ae_restrict_mem (C.measurableSet_coordinateDomain t),
    ae_uniqueDiffWithinAt volume (C.coordinateDomain t)] with z hz hm hu
  exact fun j => C.coordinateSlice_fderiv t hi (fun w hw => (heq hw).symm) hm hz.1 hz.2 hu j

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

noncomputable def coordinateSliceTotal (t : ℝ) : IntegerChart X k := by
  classical
  exact if ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)) then C.coordinateSlice t ht
    else coordinateEmptyChart

lemma ae_coordinateSliceTotal_eq : ∀ᵐ t : ℝ,
    ∃ ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)),
      C.coordinateSliceTotal t = C.coordinateSlice t ht := by
  filter_upwards [C.ae_integrable_coordinateMultiplicity] with t ht
  exact ⟨ht,dite_eq_left ht⟩

end CAT0Fillings.IntegerChart
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_CoordinateIntegral
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma ae_coordinateSlice_jacobian (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∀ᵐ t : ℝ, ∀ (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))),
    ∀ᵐ z ∂volume.restrict (C.coordinateDomain t),
      (C.coordinateSlice t ht).jacobian π z = C.coordinateMinor π (coordinateLayer k t z) := by
  have hall : ∀ i, ∀ᵐ t : ℝ, ∀ ht, ∀ᵐ z ∂volume.restrict (C.coordinateDomain t), ∀ j : Fin k,
      (fderivWithin ℝ ((C.coordinateSlice t ht).scalar (π i)) (C.coordinateDomain t) z)
        (EuclideanSpace.single j 1) =
      (fderivWithin ℝ (C.scalar (π i)) C.domain (coordinateLayer k t z))
        (EuclideanSpace.single j.succ 1) := by
    intro i
    obtain ⟨K,hK⟩ := hπ i
    exact C.ae_coordinateSlice_fderiv hK
  filter_upwards [ae_all_iff.mpr hall] with t ht
  intro hi
  filter_upwards [ae_all_iff.mpr (fun i => ht i hi)] with z hz
  apply congrArg Matrix.det
  ext i j
  exact hz i j

lemma ae_coordinate_minor_eq {u : X → ℝ}
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    (π : Fin k → X → ℝ) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Matrix.vecCons u π) z = C.coordinateMinor π z := by
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,ae_restrict_mem C.borel] with z hz hm
  have hd : fderivWithin ℝ (C.scalar u) C.domain z =
      (ContinuousLinearMap.fst ℝ ℝ (Euc k)).comp (Prism.split k).toContinuousLinearMap := by
    apply HasFDerivWithinAt.fderivWithin _ hz
    apply (((ContinuousLinearMap.fst ℝ ℝ (Euc k)).hasFDerivAt).comp z
      (Prism.split k).hasFDerivAt).hasFDerivWithinAt.congr
    · intro w hw
      rw [C.scalar_eq hw,hu w hw]
      rfl
    · rw [C.scalar_eq hm,hu z hm]
      rfl
  let A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ := Matrix.of fun i j =>
    (fderivWithin ℝ (C.scalar (Matrix.vecCons u π i)) C.domain z) (EuclideanSpace.single j 1)
  have ha0 : ∀ j, A 0 j = if j=0 then 1 else 0 := by
    intro j
    dsimp only [A,Matrix.of_apply,Matrix.cons_val_zero]
    rw [hd]
    cases j using Fin.cases with
    | zero => simp [ContinuousLinearMap.comp_apply]
    | succ j => simp [ContinuousLinearMap.comp_apply]
  change A.det = _
  rw [Matrix.det_succ_row_zero]
  simp only [ha0,mul_ite,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true,
    Fin.val_zero,pow_zero,one_mul]
  apply congrArg Matrix.det
  ext i j
  simp only [Matrix.submatrix_apply,Fin.succAbove_zero,A,Matrix.of_apply,Matrix.cons_val_succ]

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma coordinate_indicator (g : Euc (k+1) → ℝ) (t : ℝ) :
    (fun z => C.domain.indicator g ((Prism.split k).symm (t,z))) =
      (C.coordinateDomain t).indicator (fun z => g (coordinateLayer k t z)) := by
  funext z
  change C.domain.indicator g (coordinateLayer k t z) = _
  by_cases hz : coordinateLayer k t z ∈ C.domain
  · rw [indicator_of_mem hz,indicator_of_mem (show z ∈ C.coordinateDomain t from hz)]
  · rw [indicator_of_notMem hz,indicator_of_notMem (show z ∉ C.coordinateDomain t from hz)]

lemma coordinate_setIntegral {g : Euc (k+1) → ℝ}
    (hg : Integrable g (volume.restrict C.domain)) :
    ∫ w in C.domain, g w = ∫ t : ℝ, ∫ z in C.coordinateDomain t,
      g (coordinateLayer k t z) := by
  rw [←integral_indicator C.borel,Prism.integral_split]
  have hi : Integrable (C.domain.indicator g) := (integrable_indicator_iff C.borel).mpr hg
  have hip : Integrable (fun p : ℝ × Euc k => C.domain.indicator g ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  change (∫ p : ℝ × Euc k, C.domain.indicator g ((Prism.split k).symm p) ∂volume.prod volume) = _
  rw [integral_prod _ hip]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [C.coordinate_indicator g t,integral_indicator (C.measurableSet_coordinateDomain t)]

lemma integrable_coordinate_setIntegral {g : Euc (k+1) → ℝ}
    (hg : Integrable g (volume.restrict C.domain)) :
    Integrable (fun t : ℝ => ∫ z in C.coordinateDomain t, g (coordinateLayer k t z)) := by
  have hi : Integrable (C.domain.indicator g) := (integrable_indicator_iff C.borel).mpr hg
  have hip : Integrable (fun p : ℝ × Euc k => C.domain.indicator g ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  convert hip.integral_prod_left using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [C.coordinate_indicator g t,integral_indicator (C.measurableSet_coordinateDomain t)]

lemma integrable_coordinateMinor {u : X → ℝ} {K : ℝ≥0} (hL : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    Integrable (fun w => (C.multiplicity w:ℝ)*C.scalar b w*C.coordinateMinor π w)
      (volume.restrict C.domain) := by
  have ha : ∀ i, ∃ L : ℝ≥0, LipschitzWith L (Matrix.vecCons u π i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact ⟨_,hL⟩
    | succ i => exact h.2 i
  apply (C.integrable_action_integrand h.1 ha).congr
  filter_upwards [C.ae_coordinate_minor_eq hu π] with z hz
  rw [hz]

lemma ae_coordinateSliceTotal_action {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) :
    ∀ᵐ t : ℝ, (C.coordinateSliceTotal t).action b π =
      ∫ z in C.coordinateDomain t, (C.multiplicity (coordinateLayer k t z):ℝ)*
        C.scalar b (coordinateLayer k t z)*C.coordinateMinor π (coordinateLayer k t z) := by
  filter_upwards [C.ae_coordinateSliceTotal_eq,C.ae_coordinateSlice_jacobian π h.2] with t ht hj
  obtain ⟨hi,heq⟩ := ht
  rw [heq,action,ite_eq_left h]
  apply integral_congr_ae
  filter_upwards [hj hi,ae_restrict_mem (C.measurableSet_coordinateDomain t)] with z hz hm
  change (C.multiplicity (coordinateLayer k t z):ℝ)*
    (C.coordinateSlice t hi).scalar b z*(C.coordinateSlice t hi).jacobian π z = _
  rw [C.coordinateSlice_scalar_eq t hi b hm,hz]

theorem coordinateSlice_action_integral {u : X → ℝ} {K : ℝ≥0} (hL : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    C.action b (Matrix.vecCons u π) = ∫ t : ℝ, (C.coordinateSliceTotal t).action b π := by
  have ha : Admissible b (Matrix.vecCons u π) := ⟨h.1,fun i => by
    cases i using Fin.cases with
    | zero => exact ⟨_,hL⟩
    | succ i => exact h.2 i⟩
  rw [action,ite_eq_left ha]
  calc
    _ = ∫ w in C.domain, (C.multiplicity w:ℝ)*C.scalar b w*C.coordinateMinor π w := by
      apply integral_congr_ae
      filter_upwards [C.ae_coordinate_minor_eq hu π] with z hz
      rw [hz]
    _ = ∫ t : ℝ, ∫ z in C.coordinateDomain t, (C.multiplicity (coordinateLayer k t z):ℝ)*
        C.scalar b (coordinateLayer k t z)*C.coordinateMinor π (coordinateLayer k t z) :=
      C.coordinate_setIntegral (C.integrable_coordinateMinor hL hu h)
    _ = _ := integral_congr_ae (Filter.EventuallyEq.symm (C.ae_coordinateSliceTotal_action h))

lemma coordinateSlice_action_integrable {u : X → ℝ} {K : ℝ≥0} (hL : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    Integrable (fun t : ℝ => (C.coordinateSliceTotal t).action b π) :=
  (C.integrable_coordinate_setIntegral (C.integrable_coordinateMinor hL hu h)).congr
    (Filter.EventuallyEq.symm (C.ae_coordinateSliceTotal_action h))

end CAT0Fillings.IntegerChart
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_CoordinateCoarea
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)
lemma majorant_test_bound {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * J z) (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (b : X → ℝ) (π : Fin k → X → ℝ) (hb : BoundedLip b)
    (hπ : ∀ i, LipschitzWith 1 (π i))
    (hdet : ∀ᵐ z ∂volume.restrict C.domain, |C.jacobian π z| ≤ J z) :
    |C.action b π| ≤ ∫ x, |b x| ∂C.majorantMeasure J := by
  let μ := volume.restrict C.domain
  have hbmeas := hb.continuous.measurable.comp C.measurable_paramExtended
  obtain ⟨M,hM⟩ := hb.2
  have hupper : Integrable (fun z => (|(C.multiplicity z : ℝ)| * J z)*|b (C.paramExtended z)|) μ :=
    hρ.mul_bdd hbmeas.abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_abs] using hM _)
  have hρ0 : 0 ≤ᵐ[μ] fun z => |(C.multiplicity z : ℝ)| * J z :=
    hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz
  rw [majorantMeasure,integral_densityPush μ C.measurable_paramExtended hρ hρ0 hb.continuous.abs]
  rw [action,ite_eq_left ⟨hb,fun i => ⟨1,hπ i⟩⟩]
  rw [← Real.norm_eq_abs]
  apply le_trans (norm_integral_le_integral_norm _) ?_
  change (∫ z, |(C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z| ∂μ) ≤ _
  apply integral_mono_ae
    (C.integrable_action_integrand hb (fun i => ⟨1,hπ i⟩)).abs hupper
  filter_upwards [hdet,C.scalar_ae_paramExtended b] with z hz hbz
  rw [abs_mul,abs_mul,hbz]
  change |(C.multiplicity z : ℝ)| * |b (C.paramExtended z)| * |C.jacobian π z| ≤ _
  calc _ ≤ (|(C.multiplicity z : ℝ)| * |b (C.paramExtended z)|) * J z :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring
end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma ae_integrable_coordinate {g : Euc (k+1) → ℝ}
    (hg : Integrable g (volume.restrict C.domain)) :
    ∀ᵐ t : ℝ, Integrable (fun z => g (coordinateLayer k t z))
      (volume.restrict (C.coordinateDomain t)) := by
  have hi : Integrable (C.domain.indicator g) := (integrable_indicator_iff C.borel).mpr hg
  have hip : Integrable (fun p : ℝ × Euc k => C.domain.indicator g ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  filter_upwards [hip.prod_right_ae] with t ht
  apply (integrable_indicator_iff (C.measurableSet_coordinateDomain t)).mp
  simpa only [C.coordinate_indicator g t] using ht

lemma ae_coordinate_of_ae {p : Euc (k+1) → Prop}
    (hp : ∀ᵐ w ∂volume.restrict C.domain, p w) :
    ∀ᵐ t : ℝ, ∀ᵐ z ∂volume.restrict (C.coordinateDomain t), p (coordinateLayer k t z) := by
  have hf := (ae_restrict_iff' C.borel).mp hp
  have hm := (Prism.split_symm_measurePreserving k).quasiMeasurePreserving.ae hf
  filter_upwards [Measure.ae_ae_of_ae_prod hm] with t ht
  exact (ae_restrict_iff' (C.measurableSet_coordinateDomain t)).mpr ht

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X (k+1))

theorem coordinate_coarea_majorant {J : Euc (k+1) → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z:ℝ)| * J z) (volume.restrict C.domain))
    (hJ : ∀ z, 0 ≤ J z)
    (hdet : ∀ π : Fin k → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.coordinateMinor π z| ≤ J z) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, mass (C.coordinateSliceTotal t).action ≤ G t) ∧
      (∫ t : ℝ, G t) = ∫ z in C.domain, |(C.multiplicity z:ℝ)| * J z := by
  let G : ℝ → ℝ := fun t => ∫ z in C.coordinateDomain t,
    |(C.multiplicity (coordinateLayer k t z):ℝ)| * J (coordinateLayer k t z)
  let μ : ℝ → Measure X := fun t => (C.coordinateSliceTotal t).majorantMeasure
    (fun z => J (coordinateLayer k t z))
  have hsliceρ : ∀ᵐ t : ℝ,
      Integrable (fun z => |((C.coordinateSliceTotal t).multiplicity z:ℝ)| *
        J (coordinateLayer k t z)) (volume.restrict (C.coordinateSliceTotal t).domain) := by
    filter_upwards [C.ae_coordinateSliceTotal_eq,C.ae_integrable_coordinate hρ] with t ht hρt
    obtain ⟨hi,heq⟩ := ht
    rw [heq]
    exact hρt
  have hfin : ∀ᵐ t : ℝ, IsFiniteMeasure (μ t) := by
    filter_upwards [hsliceρ] with t ht
    exact densityPush_finite _ _ ht
  have hcontrols : ∀ᵐ t : ℝ, Controls (C.coordinateSliceTotal t).action (μ t) := by
    apply Foundations.ae_controls_of_testwise_bound volume
      (Eventually.of_forall fun t => (C.coordinateSliceTotal t).action_isMetricCurrent) hfin
    intro b π hb hπ
    filter_upwards [hsliceρ,C.ae_coordinateSliceTotal_eq,
      C.ae_coordinateSlice_jacobian π (fun i => ⟨1,hπ i⟩),
      C.ae_coordinate_of_ae (hdet π hπ)] with t hρt ht hj hdt
    apply (C.coordinateSliceTotal t).majorant_test_bound hρt
      (Eventually.of_forall fun z => hJ (coordinateLayer k t z)) b π hb hπ
    obtain ⟨hi,heq⟩ := ht
    rw [heq]
    filter_upwards [hj hi,hdt] with z hz hd
    rw [hz]
    exact hd
  have hm : ∀ᵐ t : ℝ, (μ t).real univ = G t := by
    filter_upwards [hsliceρ,C.ae_coordinateSliceTotal_eq,hfin] with t hρt ht hμt
    let := hμt
    calc
      (μ t).real univ = ∫ x, (1:ℝ) ∂μ t := by simp
      _ = ∫ z in (C.coordinateSliceTotal t).domain,
          |((C.coordinateSliceTotal t).multiplicity z:ℝ)| * J (coordinateLayer k t z) := by
        rw [show μ t = (C.coordinateSliceTotal t).majorantMeasure
          (fun z => J (coordinateLayer k t z)) from rfl,majorantMeasure,
          integral_densityPush _ (C.coordinateSliceTotal t).measurable_paramExtended hρt
            (Eventually.of_forall fun z => mul_nonneg (abs_nonneg _) (hJ _)) continuous_const]
        simp only [mul_one]
      _ = G t := by
        obtain ⟨hi,heq⟩ := ht
        rw [heq]
        rfl
  refine ⟨G,C.integrable_coordinate_setIntegral hρ,fun t =>
    integral_nonneg (fun z => mul_nonneg (abs_nonneg _) (hJ _)),?_,?_⟩
  · filter_upwards [hcontrols,hfin,hm] with t hct hft hmt
    rw [←hmt]
    exact mass_le_measure hft hct
  · exact (C.coordinate_setIntegral hρ).symm

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X (k+1))

theorem sharp_coordinate_coarea_majorant (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, mass (C.coordinateSliceTotal t).action ≤ G t) ∧
      (∫ t : ℝ, G t) = K * mass C.action := by
  obtain ⟨P,hPm,hP,hρ,hfin,hctrl,hle,p,hpP,hpm,hp⟩ :=
    C.exists_exact_quadratic_mass hX C.action_isMetricCurrent
  let μ := C.majorantMeasure (fun z => Real.sqrt (P z).det)
  let : IsFiniteMeasure μ := hfin
  have hμmass : mass C.action = μ.real univ := by
    apply le_antisymm (mass_le_measure hfin hctrl)
    obtain ⟨ν,hνfin,hν,hνmass⟩ := C.action_isMetricCurrent.exists_controls_mass_eq
    let := hνfin
    rw [hνmass]
    exact ENNReal.toReal_mono (measure_ne_top ν univ) (hle ν hνfin hν univ)
  have hm : mass C.action = ∫ z in C.domain,
      |(C.multiplicity z:ℝ)| * Real.sqrt (P z).det := by
    rw [hμmass]
    calc
      μ.real univ = ∫ x, (1:ℝ) ∂μ := by simp
      _ = _ := by
        rw [show μ = C.majorantMeasure (fun z => Real.sqrt (P z).det) from rfl,
          majorantMeasure,integral_densityPush _ C.measurable_paramExtended hρ
            (Eventually.of_forall fun z => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
            continuous_const]
        simp only [mul_one]
  have hρK : Integrable (fun z => |(C.multiplicity z:ℝ)| *
      ((K:ℝ) * Real.sqrt (P z).det)) (volume.restrict C.domain) := by
    convert hρ.const_mul (K:ℝ) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    ring
  have hdet : ∀ π : Fin k → X → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.coordinateMinor π z| ≤
        (K:ℝ) * Real.sqrt (P z).det := by
    intro π hπ
    have hh := C.ae_jacobian_bound_quadratic p hp (Matrix.vecCons u π)
      (Matrix.vecCons K (fun _ => 1)) (fun i => by
        cases i using Fin.cases with
        | zero => exact hK
        | succ i => exact hπ i)
    filter_upwards [hh,C.ae_coordinate_minor_eq hu π] with z hz heq
    rw [heq] at hz
    simpa only [hpP,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      NNReal.coe_one,Finset.prod_const_one,mul_one] using hz
  obtain ⟨G,hG,hG0,hGm,hGI⟩ := C.coordinate_coarea_majorant hρK
    (fun z => mul_nonneg K.coe_nonneg (Real.sqrt_nonneg _)) hdet
  refine ⟨G,hG,hG0,hGm,?_⟩
  rw [hGI,hm,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by ring

end CAT0Fillings.IntegerChart

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_MultiplicityRestriction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
namespace IntegerChart
open BorelCoefficients BorelRestriction MassMeasure

variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [Nonempty X]
variable {k : ℕ} (C : IntegerChart X k)

lemma restrictMultiplicity_isMetricCurrent (hC : IsMetricCurrent C.action)
    {E : Set X} (hE : MeasurableSet E) :
    IsMetricCurrent (C.restrictMultiplicity E hE).action := by
  rw [C.restrictMultiplicity_action hC hE]
  exact restrictCurrent_isMetricCurrent hC hE

lemma restrictMultiplicity_mass_le (hC : IsMetricCurrent C.action)
    {E : Set X} (hE : MeasurableSet E) :
    mass (C.restrictMultiplicity E hE).action ≤ mass C.action := by
  rw [C.restrictMultiplicity_action hC hE,restriction_mass hC hE,
    ←currentMassMeasure_total hC]
  exact measureReal_mono (subset_univ E)

end IntegerChart
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_DomainRestriction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
open BorelCoefficients BorelRestriction MassMeasure

theorem integerRectifiable_restrict
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (hrect : IntegerRectifiable T) {E : Set X} (hE : MeasurableSet E) :
    IntegerRectifiable (restrictCurrent hT E) := by
  obtain ⟨C,hdis,hC,hsum,heq⟩ := hrect
  let D : ℕ → IntegerChart X k := fun i => (C i).restrictMultiplicity E hE
  have hD (i) : IsMetricCurrent (D i).action :=
    (C i).restrictMultiplicity_isMetricCurrent (hC i) hE
  refine ⟨D,hdis,hD,?_,?_⟩
  · apply hsum.of_nonneg_of_le (fun i => mass_nonneg (D i).action)
    exact fun i => (C i).restrictMultiplicity_mass_le (hC i) hE
  · let μ (i) := currentMassMeasure (hC i)
    have hμfin : ∀ i, IsFiniteMeasure (μ i) := fun i => inferInstance
    let := hμfin
    have hμsum : Summable (fun i => (μ i).real univ) := by
      simpa only [μ,currentMassMeasure_total] using hsum
    let := finite_sum_measure_of_summable_total μ hμsum
    have hμ (i) : Controls (C i).action (μ i) := currentMassMeasure_controls (hC i)
    intro b π
    by_cases hab : Admissible b π
    · rw [restrictCurrent_apply hT E hab,
        borelAction_independent (currentMassMeasure hT) hT
          (currentMassMeasure_controls hT) (controls_sum hμ heq)
          ((integrable_boundedLip _ hab.1).indicator hE)
          ((integrable_boundedLip _ hab.1).indicator hE) π hab.2,
        borelAction_sum μ hT hC hμ heq
          ((integrable_boundedLip _ hab.1).indicator hE) π hab.2]
      apply tsum_congr
      intro i
      change _ = ((C i).restrictMultiplicity E hE).action b π
      rw [(C i).restrictMultiplicity_action (hC i) hE,restrictCurrent_apply (hC i) E hab]
    · rw [(restrictCurrent_isMetricCurrent hT hE).offDomain b π hab]
      symm
      calc
        (∑' i, (D i).action b π) = ∑' (_i : ℕ), (0 : ℝ) :=
          tsum_congr (fun i => (hD i).offDomain b π hab)
        _ = 0 := tsum_zero

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Summation
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}

lemma mass_tsum_le {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i))) :
    mass (fun b π => ∑' i, T i b π) ≤ ∑' i, mass (T i) := by
  choose μ hfin hμ heq using fun i => (hT i).exists_controls_mass_eq
  let : ∀ i, IsFiniteMeasure (μ i) := hfin
  have hm : Summable (fun i => (μ i).real univ) := by simpa only [←heq] using hS
  let := finite_sum_measure_of_summable_total μ hm
  apply (mass_le_measure (inferInstance : IsFiniteMeasure (Measure.sum μ)) (controls_sum hμ (fun _ _ => rfl))).trans_eq
  rw [measureReal_def,Measure.sum_apply _ MeasurableSet.univ, ENNReal.tsum_toReal_eq]
  · exact tsum_congr (fun i => (heq i).symm)
  · intro i
    exact measure_ne_top _ _

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Straightening
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace EuclideanStraightening
variable {d : ℕ}

lemma replaceMap_lipschitz (j : Fin d) {g : Euc d → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊) (replaceMap j g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h1 := hg.dist_le_mul x y
  have h2 := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).lipschitz.dist_le_mul x y
  have h3 : ‖(g x-x j)-(g y-y j)‖ ≤ ((K:ℝ)+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊)*‖x-y‖ := by
    have htriangle : ‖(g x-x j)-(g y-y j)‖ ≤ ‖g x-g y‖+‖x j-y j‖ := by
      convert norm_sub_le (g x-g y) (x j-y j) using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)
    simp only [dist_eq_norm] at h1 h2
    change ‖x j-y j‖ ≤ _ at h2
    nlinarith
  simp only [replaceMap,dist_eq_norm]
  have he : x+(g x-x j) • EuclideanSpace.single j 1-
      (y+(g y-y j) • EuclideanSpace.single j 1) =
      (x-y)+((g x-x j)-(g y-y j)) • EuclideanSpace.single j 1 := by
    module
  rw [he]
  calc
    _ ≤ ‖x-y‖ + ‖((g x-x j)-(g y-y j)) • EuclideanSpace.single j 1‖ := norm_add_le _ _
    _ = ‖x-y‖+‖(g x-x j)-(g y-y j)‖ := by simp [norm_smul]
    _ ≤ ‖x-y‖+(((K:ℝ)+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊)*‖x-y‖) := add_le_add_right h3 ‖x-y‖
    _ = _ := by simp only [NNReal.coe_add,NNReal.coe_one]; ring

lemma replaceMap_hasFDerivAt {g : Euc d → ℝ} {x : Euc d} (hg : DifferentiableAt ℝ g x)
    (j : Fin d) : HasFDerivAt (replaceMap j g)
      (ContinuousLinearMap.id ℝ (Euc d)+(fderiv ℝ g x-EuclideanSpace.proj j).smulRight
        (EuclideanSpace.single j 1)) x :=
  (hasFDerivAt_id x).add ((hg.hasFDerivAt.sub (EuclideanSpace.proj j).hasFDerivAt).smul_const _)

lemma det_replaceMap_fderiv {g : Euc d → ℝ} {x : Euc d} (hg : DifferentiableAt ℝ g x)
    (j : Fin d) :
    (Matrix.of fun i l : Fin d => fderiv ℝ (replaceMap j g) x (EuclideanSpace.single l 1) i).det =
      fderiv ℝ g x (EuclideanSpace.single j 1) := by
  rw [(replaceMap_hasFDerivAt hg j).fderiv]
  have he : (Matrix.of fun i l : Fin d =>
      (ContinuousLinearMap.id ℝ (Euc d)+(fderiv ℝ g x-EuclideanSpace.proj j).smulRight
        (EuclideanSpace.single j 1)) (EuclideanSpace.single l 1) i) =
      Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j
        (fun l => fderiv ℝ g x (EuclideanSpace.single l 1)) := by
    ext i l
    by_cases hi : i=j
    · subst i
      simp [ContinuousLinearMap.smulRight_apply,PiLp.single_apply,
        Matrix.updateRow,Function.update]
    · simp [ContinuousLinearMap.smulRight_apply,PiLp.single_apply,
        Matrix.updateRow,Function.update,Matrix.one_apply,hi]
  rw [he,det_updateRow_one]

lemma straightenMap_lipschitz {k : ℕ} (j : Fin (k+1)) {g : Euc (k+1) → ℝ}
    {K : ℝ≥0} (hg : LipschitzWith K g) :
    LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc (k+1) →L[ℝ] ℝ)‖₊) (straightenMap j g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (switchZero j (replaceMap j g x)) (switchZero j (replaceMap j g y)) ≤ _
  rw [(switchZero j).isometry.dist_eq]
  exact (replaceMap_lipschitz j hg).dist_le_mul x y

end EuclideanStraightening
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_Degenerate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.MetricDifferentiation
open MeasureTheory Filter Set
open scoped Topology

variable {X : Type*} [MetricSpace X]

theorem ae_scalarOn_det_eq_zero_of_degenerate {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    {f : s → X} {K : ℝ≥0} (hf : LipschitzWith K f)
    {p : EuclideanSpace ℝ (Fin n) → Seminorm ℝ (EuclideanSpace ℝ (Fin n))}
    (hd : ∀ᵐ x ∂volume.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩)
    (π : Fin n → X → ℝ) (hπ : ∀ i, ∃ J : ℝ≥0, LipschitzWith J (π i)) :
    ∀ᵐ x ∂volume.restrict s, (¬ ∀ v, p x v = 0 → v = 0) →
      Matrix.det (fun i j => fderivWithin ℝ (scalarOn f (π i)) s x
        (EuclideanSpace.single j 1)) = 0 := by
  choose J hJ using hπ
  have hb : ∀ᵐ x ∂volume.restrict s, ∀ i v,
      |fderivWithin ℝ (scalarOn f (π i)) s x v| ≤ (J i : ℝ)*p x v := by
    rw [eventually_all]
    intro i
    exact ae_scalarOn_derivative_bound volume hs hf hd (hJ i)
  filter_upwards [hb] with x hx hker
  exact det_rows_eq_zero_of_seminorm_kernel (p x) _ (fun i => ⟨J i,hx i⟩) hker

end CAT0Fillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Differentiation_FullRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_ae_bilipschitz_partition_of_bound
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ (⊤ : ℝ≥0∞))
    {A : ℝ≥0} (hA : 0 < A)
    (hbound : ∀ x ∈ s, ∀ v : E, ‖v‖ ≤ (A : ℝ)*metricSeminorm f x v) :
    ∃ t : ℕ → Set E,
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      ∀ i, LipschitzWith K (fun x : t i => f x) ∧
        AntilipschitzWith (2*A) (fun x : t i => f x) := by
  obtain ⟨c,t,htm,hts,hdisj,ht0,hcs,hineq⟩ :=
    exists_ae_nearIsometric_partition μ hf hs hsf
      (show 0 < (A : ℝ) from hA) hbound (show (0 : ℝ) < 1/2 by norm_num)
  refine ⟨t,htm,hts,hdisj,ht0,fun i => ⟨LipschitzWith.of_dist_le_mul (fun a b => hf.dist_le_mul a b),?_⟩⟩
  apply AntilipschitzWith.of_le_mul_dist
  intro a b
  have hlo := (hineq i a a.property b b.property).1
  have hb := hbound (c i) (hcs i ⟨a,a.property⟩) ((a : E)-(b : E))
  change dist (a : E) (b : E) ≤ (↑(2*A) : ℝ)*dist (f a) (f b)
  rw [dist_eq_norm]
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (A : ℝ) from A.coe_nonneg)
    (show 0 ≤ dist (f a) (f b) - (1-(1:ℝ)/2)*metricSeminorm f (c i) ((a : E)-(b : E)) from sub_nonneg.mpr hlo)]

theorem exists_bilipschitz_fullRank_pieces
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ (⊤ : ℝ≥0∞)) :
    ∃ (t : ℕ → Set E) (J : ℕ → ℝ≥0),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      μ ((s ∩ {x | ∃ n : ℕ, ∀ v : E,
        ‖v‖ ≤ ((n : ℝ)+1)*metricSeminorm f x v}) \ ⋃ i, t i) = 0 ∧
      ∀ i, LipschitzWith K (fun x : t i => f x) ∧
        AntilipschitzWith (J i) (fun x : t i => f x) := by
  classical
  let U : ℕ → Set E := fun n => s ∩ {x | ∀ v : E,
    ‖v‖ ≤ ((n : ℝ)+1)*metricSeminorm f x v}
  have hU (n : ℕ) : MeasurableSet (U n) :=
    hs.inter (measurableSet_metricSeminorm_lower_bound hf _)
  have hUf (n : ℕ) : μ (U n) ≠ (⊤ : ℝ≥0∞) :=
    ((measure_mono inter_subset_left).trans_lt hsf.lt_top).ne
  have H (n : ℕ) := exists_ae_bilipschitz_partition_of_bound μ hf (hU n) (hUf n)
    (A := n+1) (by positivity) (by
      intro x hx v
      simpa using hx.2 v)
  choose T hTm hTs hTd hT0 hTb using H
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let V : ℕ → Set E := fun i => T (e i).1 (e i).2
  let t := disjointed V
  have htV (i : ℕ) : t i ⊆ T (e i).1 (e i).2 := disjointed_le V i
  have hcover (n : ℕ) : (⋃ j, T n j) ⊆ ⋃ i, t i := by
    rw [iUnion_disjointed]
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨e.symm (n,j),?_⟩
    simpa [V] using hj
  refine ⟨t,fun i => 2*((e i).1+1),
    fun i => MeasurableSet.disjointed (fun j => hTm _ _) i,
    fun i => (htV i).trans ((hTs _ _).trans inter_subset_left),disjoint_disjointed V,?_,?_⟩
  · have hnull (n : ℕ) : μ (U n \ ⋃ i, t i) = 0 :=
      measure_mono_null (sdiff_subset_sdiff_right (hcover n)) (hT0 n)
    apply measure_mono_null _ (measure_iUnion_null hnull)
    intro x hx
    obtain ⟨n,hn⟩ := hx.1.2
    exact mem_iUnion.mpr ⟨n,⟨⟨hx.1.1,hn⟩,hx.2⟩⟩
  · intro i
    refine ⟨LipschitzWith.of_dist_le_mul (fun a b => hf.dist_le_mul a b),?_⟩
    apply AntilipschitzWith.of_le_mul_dist
    intro a b
    exact (hTb _ _).2.le_mul_dist ⟨a,htV i a.property⟩ ⟨b,htV i b.property⟩

end CAT0Fillings.MetricDifferentiation

namespace CAT0Fillings.MetricDifferentiation
open MeasureTheory Filter Set Metric
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X]

theorem exists_lipschitz_chart_decomposition {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s) (hsf : volume s ≠ (⊤ : ℝ≥0∞))
    {f : s → X} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin n)))
      (J : ℕ → ℝ≥0) (hts : ∀ i, t i ⊆ s),
      (∀ i, MeasurableSet (t i)) ∧ Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      (∀ i, LipschitzWith K (fun x : t i => f ⟨x,hts i x.property⟩) ∧
        AntilipschitzWith (J i) (fun x : t i => f ⟨x,hts i x.property⟩)) ∧
      ∀ (π : Fin n → X → ℝ), (∀ i, ∃ L : ℝ≥0, LipschitzWith L (π i)) →
        ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i →
          Matrix.det (fun i j => fderivWithin ℝ (scalarOn f (π i)) s x
            (EuclideanSpace.single j 1)) = 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let Y := Set.range f
  let : SeparableSpace Y := (isSeparable_range hf.continuous).separableSpace
  let F : s → Y := fun x => ⟨f x,x,rfl⟩
  let e := kuratowskiEmbedding Y
  have he : Isometry e := kuratowskiEmbedding.isometry Y
  let F₀ : E → ↥(lp (fun _ : ℕ => ℝ) (⊤ : ENNReal)) :=
    fun x => if hx : x ∈ s then e (F ⟨x,hx⟩) else 0
  have hF₀ : LipschitzOnWith K F₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    dsimp only [F₀]
    rw [dite_eq_left hx,dite_eq_left hy,he.dist_eq]
    exact hf.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,heq⟩ := hF₀.extend_lp_infty
  let Z := Set.range g
  let : SeparableSpace Z := (isSeparable_range hg.continuous).separableSpace
  let : Nonempty Z := ⟨⟨g 0,0,rfl⟩⟩
  let G : E → Z := fun x => ⟨g x,x,rfl⟩
  have hG : LipschitzWith K G := LipschitzWith.of_dist_le_mul hg.dist_le_mul
  have hdist (y z : s) : dist (G y) (G z) = dist (f y) (f z) := by
    change dist (g y) (g z) = _
    rw [←heq y.property, ←heq z.property]
    dsimp only [F₀]
    rw [dite_eq_left y.property,dite_eq_left z.property]
    exact he.dist_eq (F y) (F z)
  let p := metricSeminorm G
  have hdiff : ∀ᵐ x ∂volume.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩ := by
    have hd := (ae_hasCenteredMetricDifferential volume hG).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := volume) (s := s)))
    filter_upwards [hd] with x hx hxs
    have hc : Tendsto (fun y : s => (y : E)) (𝓝 (⟨x,hxs⟩ : s)) (𝓝 x) :=
      continuous_subtype_val.tendsto _
    have hr := hx.comp_tendsto hc
    change (fun y : s => dist (G (y : E)) (G ((⟨x,hxs⟩ : s) : E)) -
      p x ((y : E)-x)) =o[𝓝 (⟨x,hxs⟩ : s)] (fun y : s => (y : E)-x) at hr
    have hdist' (y : s) : dist (G (y : E)) (G x) = dist (f y) (f ⟨x,hxs⟩) :=
      hdist y ⟨x,hxs⟩
    simpa only [HasCenteredMetricDifferentialWithin,hdist'] using hr
  obtain ⟨t,J,htm,hts,htd,ht0,htb⟩ := exists_bilipschitz_fullRank_pieces volume hG hs hsf
  refine ⟨t,J,hts,htm,htd,?_,?_⟩
  · intro i
    constructor
    · apply LipschitzWith.of_dist_le_mul
      intro a b
      exact hf.dist_le_mul ⟨a,hts i a.property⟩ ⟨b,hts i b.property⟩
    · apply AntilipschitzWith.of_le_mul_dist
      intro a b
      have hh := (htb i).2.le_mul_dist a b
      change dist (a : E) (b : E) ≤ (J i : ℝ)*dist (G a) (G b) at hh
      rw [hdist ⟨a,hts i a.property⟩ ⟨b,hts i b.property⟩] at hh
      exact hh
  · intro π hπ
    have hcover : ∀ᵐ x ∂volume.restrict s, (∀ v, p x v = 0 → v = 0) → x ∈ ⋃ i, t i := by
      have hz : ∀ᵐ x ∂volume, x ∉
          (s ∩ {x | ∃ n : ℕ, ∀ v : E, ‖v‖ ≤ ((n : ℝ)+1)*metricSeminorm G x v}) \ ⋃ i, t i :=
        ae_iff.mpr (by
          convert ht0 using 1
          all_goals try with_reducible_and_instances rfl
          congr 1
          ext x
          simp only [mem_ofPred_eq,not_not]
          rfl)
      filter_upwards [hz.filter_mono (ae_mono Measure.restrict_le_self),ae_restrict_mem hs] with x hx hxs hp0
      have hbound := (exists_nat_lower_bound_iff (metricSeminorm_lipschitz hG x).continuous).2 hp0
      by_contra hnot
      exact hx ⟨⟨hxs,hbound⟩,hnot⟩
    filter_upwards [hcover,ae_scalarOn_det_eq_zero_of_degenerate hs hf hdiff π hπ] with x hx hv hnot
    apply hv
    exact fun hp0 => hnot (hx hp0)

end CAT0Fillings.MetricDifferentiation

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_StraightPieces
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.EuclideanStraightening
open Set MeasureTheory Filter
open scoped Topology NNReal

variable {d : ℕ}
lemma coordinate_scalarOn_fderiv {s : Set (Euc d)} {x : Euc d}
    (hu : UniqueDiffWithinAt ℝ s x) (hxs : x ∈ s) {F : Euc d → Euc d}
    (hF : DifferentiableAt ℝ F x) (i : Fin d) :
    fderivWithin ℝ (MetricDifferentiation.scalarOn (fun y : s => F y)
      (EuclideanSpace.proj i)) s x =
      (EuclideanSpace.proj i).comp (fderiv ℝ F x) := by
  apply HasFDerivWithinAt.fderivWithin _ hu
  have hD := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt
  apply hD.hasFDerivWithinAt.congr
  · intro y hy
    simp only [MetricDifferentiation.scalarOn,dite_eq_left hy,Function.comp_apply]
  · simp only [MetricDifferentiation.scalarOn,dite_eq_left hxs,Function.comp_apply]

theorem exists_replaceMap_pieces {s : Set (Euc d)} (hs : MeasurableSet s)
    (hsf : volume s ≠ (⊤ : ℝ≥0∞)) (j : Fin d) {g : Euc d → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    ∃ (t : ℕ → Set (Euc d)) (J : ℕ → ℝ≥0) (_hts : ∀ i, t i ⊆ s),
      (∀ i, MeasurableSet (t i)) ∧ Pairwise (fun i l => Disjoint (t i) (t l)) ∧
      (∀ i, LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊)
          (fun x : t i => replaceMap j g x) ∧
        AntilipschitzWith (J i) (fun x : t i => replaceMap j g x)) ∧
      ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i →
        fderiv ℝ g x (EuclideanSpace.single j 1) = 0 := by
  classical
  let F : s → Euc d := fun x => replaceMap j g x
  have hF : LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊) F := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    exact (replaceMap_lipschitz j hg).dist_le_mul a b
  obtain ⟨t,J,hts,htm,htd,htb,hzero⟩ :=
    MetricDifferentiation.exists_lipschitz_chart_decomposition hs hsf hF
  refine ⟨t,J,hts,htm,htd,htb,?_⟩
  let π : Fin d → Euc d → ℝ := fun i x => x i
  have hπ (i : Fin d) : ∃ L : ℝ≥0, LipschitzWith L (π i) :=
    ⟨‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖₊,
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).lipschitz⟩
  filter_upwards [hzero π hπ,ae_uniqueDiffWithinAt volume s,
    (hg.ae_differentiableAt (μ := volume)).filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem hs] with x hx hu hgx hxs hnot
  have he (i : Fin d) : fderivWithin ℝ (MetricDifferentiation.scalarOn F (π i)) s x =
      (EuclideanSpace.proj i).comp (fderiv ℝ (replaceMap j g) x) :=
    coordinate_scalarOn_fderiv hu hxs (replaceMap_hasFDerivAt hgx j).differentiableAt i
  have hd := hx hnot
  simp only [he,ContinuousLinearMap.comp_apply] at hd
  rw [←det_replaceMap_fderiv hgx j]
  exact hd

end CAT0Fillings.EuclideanStraightening

namespace CAT0Fillings.EuclideanStraightening
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem exists_straightened_pieces {k : ℕ} {s : Set (Euc (k+1))}
    (hs : MeasurableSet s) (hsf : volume s ≠ (⊤ : ℝ≥0∞))
    {g : Euc (k+1) → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    ∃ (t : ℕ → Set (Euc (k+1))) (dir : ℕ → Fin (k+1)) (J : ℕ → ℝ≥0),
      (∀ i, t i ⊆ s) ∧ (∀ i, MeasurableSet (t i)) ∧
      Pairwise (fun i l => Disjoint (t i) (t l)) ∧
      (∀ i, LipschitzWith (1+K+‖(EuclideanSpace.proj (dir i) : Euc (k+1) →L[ℝ] ℝ)‖₊)
          (fun x : t i => straightenMap (dir i) g x) ∧
        AntilipschitzWith (J i) (fun x : t i => straightenMap (dir i) g x)) ∧
      ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i → fderiv ℝ g x = 0 := by
  classical
  choose t J hts htm _htd htb hz using fun j : Fin (k+1) =>
    exists_replaceMap_pieces hs hsf j hg
  let := Denumerable.ofEncodableOfInfinite (Fin (k+1) × ℕ)
  let e : ℕ ≃ Fin (k+1) × ℕ := (Denumerable.eqv _).symm
  let V : ℕ → Set (Euc (k+1)) := fun i => t (e i).1 (e i).2
  have hsub (i : ℕ) : disjointed V i ⊆ t (e i).1 (e i).2 := disjointed_le V i
  have hcover : (⋃ i, disjointed V i) = ⋃ j, ⋃ l, t j l := by
    rw [iUnion_disjointed]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨(e i).1,(e i).2,hi⟩
    · rintro ⟨j,l,h⟩
      refine ⟨e.symm (j,l),?_⟩
      simpa only [V,e.apply_symm_apply] using h
  refine ⟨disjointed V,fun i => (e i).1,fun i => J (e i).1 (e i).2,
    fun i => (hsub i).trans (hts _ _),
    fun i => MeasurableSet.disjointed (fun l => htm (e l).1 (e l).2) i,
    disjoint_disjointed V,?_,?_⟩
  · intro i
    constructor
    · apply LipschitzWith.of_dist_le_mul
      intro a b
      exact (straightenMap_lipschitz (e i).1 hg).dist_le_mul a b
    · apply AntilipschitzWith.of_le_mul_dist
      intro a b
      have h := (htb (e i).1 (e i).2).2.le_mul_dist
        ⟨a,hsub i a.property⟩ ⟨b,hsub i b.property⟩
      simpa only [straightenMap,Function.comp_apply,(switchZero (e i).1).isometry.dist_eq,
        Subtype.dist_eq] using h
  · filter_upwards [ae_all_iff.mpr hz] with x hx hnot
    have h0 (j : Fin (k+1)) : fderiv ℝ g x (EuclideanSpace.single j 1) = 0 := by
      apply hx j
      intro hj
      apply hnot
      rw [hcover]
      exact mem_iUnion.mpr ⟨j,hj⟩
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin (k+1)) ℝ).toBasis.ext
    intro j
    simpa only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe,
      _root_.zero_apply] using h0 j

end CAT0Fillings.EuclideanStraightening
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_ScalarPieces
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter BorelRestriction EuclideanStraightening
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma paramExtended_disjoint_images (C : IntegerChart X k) {s t : Set (Euc k)}
    (hs : s ⊆ C.domain) (ht : t ⊆ C.domain) (hd : Disjoint s t) :
    Disjoint (C.paramExtended '' s) (C.paramExtended '' t) := by
  rw [Set.disjoint_left] at hd ⊢
  rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
  have hy' : C.paramExtended x ∈ C.paramExtended '' t := ⟨y,hy,heq⟩
  exact hd hx ((C.paramExtended_mem_image_iff ht (hs hx)).mp hy')

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma restrictDomain_image (C : IntegerChart X k) {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain) :
    (C.restrictDomain ht hts).image = C.paramExtended '' t := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨z,z.property,by simp [paramExtended,restrictDomain,hts z.property]⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨⟨z,hz⟩,?_⟩
    simp [paramExtended,restrictDomain,hts hz]

theorem exists_scalar_straightened_charts (C : IntegerChart X (k+1))
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ D : ℕ → IntegerChart X (k+1),
      Pairwise (fun i j => Disjoint (D i).image (D j).image) ∧
      (∀ i, (D i).image ⊆ C.image) ∧
      (∀ i z (hz : z ∈ (D i).domain),
        u ((D i).param ⟨z,hz⟩) = (Prism.split k z).1) ∧
      Summable (fun i => mass (D i).action) ∧
      (∑' i, mass (D i).action) ≤ mass C.action ∧
      ∀ b π, Admissible b π →
        C.action b (Matrix.vecCons u π) = ∑' i, (D i).action b (Matrix.vecCons u π) := by
  classical
  obtain ⟨L,U,hL,_hU⟩ := C.bilipschitz
  obtain ⟨g,hg,hug⟩ := (C.scalar_lipschitzOn hL hK).extend_real
  obtain ⟨t,dir,J,hts,ht,hd,hbilip,hzero⟩ :=
    exists_straightened_pieces C.borel C.bounded.measure_lt_top.ne hg
  let E i := C.paramExtended '' t i
  have hE i : MeasurableSet (E i) := C.measurableSet_paramExtended_image (ht i) (hts i)
  have hEd : Pairwise (fun i j => Disjoint (E i) (E j)) :=
    fun i j hij => C.paramExtended_disjoint_images (hts i) (hts j) (hd hij)
  let R i := C.restrictDomain (ht i) (hts i)
  let F i := straightenMap (dir i) g
  have hF i : LipschitzOnWith
      (1+K*L+‖(EuclideanSpace.proj (dir i) : Euc (k+1) →L[ℝ] ℝ)‖₊) (F i) (R i).domain :=
    lipschitzOnWith_iff_restrict.mpr (hbilip i).1
  have hA i : ∀ x ∈ (R i).domain, ∀ y ∈ (R i).domain,
      dist x y ≤ (J i:ℝ) * dist (F i x) (F i y) := by
    intro x hx y hy
    exact (hbilip i).2.le_mul_dist ⟨x,hx⟩ ⟨y,hy⟩
  let D i := (R i).reparam (F i) (hF i) (hA i)
  have hDact i : (D i).action = restrictCurrent C.action_isMetricCurrent (E i) := by
    rw [show (D i).action = (R i).action from (R i).reparam_action _ _ _]
    exact C.restrictDomain_action _ _ C.action_isMetricCurrent
  have hDimage i : (D i).image = E i := by
    rw [show (D i).image = (R i).image from (R i).reparam_image _ _ _]
    exact C.restrictDomain_image _ _
  refine ⟨D,?_,?_,?_,?_,?_,?_⟩
  · intro i j hij
    rw [hDimage,hDimage]
    exact hEd hij
  · intro i x hx
    rw [hDimage] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    exact ⟨⟨z,hts i hz⟩,by simp [paramExtended,hts i hz]⟩
  · intro i y hy
    let x := Function.invFunOn (F i) (R i).domain y
    have hx : x ∈ (R i).domain := Function.invFunOn_mem hy
    have heq : F i x = y := Function.invFunOn_eq hy
    change u (C.param ⟨x,hts i hx⟩) = (Prism.split k y).1
    have hcx : x ∈ C.domain := hts i hx
    calc
      u (C.param ⟨x,hcx⟩) = C.scalar u x := (C.scalar_eq (f := u) hcx).symm
      _ = g x := hug hcx
      _ = (Prism.split k y).1 := by
        have hc := congrArg (fun w : Euc (k+1) => w 0) heq
        simpa only [F,straightenMap_zero,Prism.split_apply] using hc
  · simp_rw [hDact]
    exact summable_restriction_mass C.action_isMetricCurrent E hE hEd
  · simp_rw [hDact]
    exact tsum_restriction_mass_le C.action_isMetricCurrent E hE hEd
  · intro b π hab
    have hab' : Admissible b (Matrix.vecCons u π) := ⟨hab.1,fun i => by
      cases i using Fin.cases with
      | zero => exact ⟨K,hK⟩
      | succ i => exact hab.2 i⟩
    simp_rw [hDact]
    rw [←restrictCurrent_iUnion C.action_isMetricCurrent E hE hEd,
      ←C.restrictMultiplicity_action C.action_isMetricCurrent (MeasurableSet.iUnion hE)]
    rw [action,action,ite_eq_left hab',ite_eq_left hab']
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem C.borel,hzero,
      ae_fderivWithin_eq_fderiv_extension volume C.borel hg hug] with z hz hz0 hder
    change (C.multiplicity z:ℝ)*C.scalar b z*C.jacobian (Matrix.vecCons u π) z =
      ↑((C.paramExtended ⁻¹' ⋃ i, E i).indicator C.multiplicity z)*
        C.scalar b z*C.jacobian (Matrix.vecCons u π) z
    by_cases hzi : z ∈ ⋃ i, t i
    · have him : z ∈ C.paramExtended ⁻¹' ⋃ i, E i := by
        obtain ⟨i,hi⟩ := mem_iUnion.mp hzi
        exact mem_iUnion.mpr ⟨i,⟨z,hi,rfl⟩⟩
      rw [indicator_of_mem him]
    · have hj : C.jacobian (Matrix.vecCons u π) z = 0 := by
        apply Matrix.det_eq_zero_of_row_eq_zero 0
        intro j
        change (fderivWithin ℝ (C.scalar u) C.domain z) (EuclideanSpace.single j 1) = 0
        rw [hder,hz0 hzi]
        rfl
      rw [hj,mul_zero,mul_zero]

end CAT0Fillings.IntegerChart

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_ScalarCoarea
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
lemma coordinateSlice_u_eq {u : X → ℝ}
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    (t : ℝ) (hi : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)))
    (z : (C.coordinateSlice t hi).domain) : u ((C.coordinateSlice t hi).param z) = t := by
  have h := hu (coordinateLayer k t z) z.property
  change u ((C.coordinateSlice t hi).param z) = _ at h
  simpa only [coordinateLayer,ContinuousLinearEquiv.apply_symm_apply] using h

lemma ae_coordinateSliceTotal_weighted {u : X → ℝ}
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π)
    (φ : ℝ → ℝ) (hφ : BoundedLip (φ ∘ u)) :
    ∀ᵐ t : ℝ, (C.coordinateSliceTotal t).action (fun x => φ (u x)*b x) π =
      φ t * (C.coordinateSliceTotal t).action b π := by
  filter_upwards [C.ae_coordinateSliceTotal_eq] with t ht
  obtain ⟨hi,heq⟩ := ht
  rw [heq]
  have hab : Admissible (fun x => φ (u x)*b x) π := ⟨hφ.mul h.1,h.2⟩
  rw [action,ite_eq_left hab,action,ite_eq_left h,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (C.measurableSet_coordinateDomain t)] with z hz
  rw [(C.coordinateSlice t hi).scalar_eq hz,(C.coordinateSlice t hi).scalar_eq hz,
    C.coordinateSlice_u_eq hu t hi ⟨z,hz⟩]
  ring

end CAT0Fillings.IntegerChart
namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma coordinateSliceTotal_image_subset (t : ℝ) :
    (C.coordinateSliceTotal t).image ⊆ C.image := by
  classical
  unfold coordinateSliceTotal
  split_ifs with hi
  · rintro x ⟨z,rfl⟩
    exact ⟨⟨coordinateLayer k t z,z.property⟩,rfl⟩
  · rintro x ⟨z,_⟩
    exact False.elim z.property

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]

theorem exists_scalar_coarea (hX : IsCAT0 X) {u : X → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K u) :
    ∃ (S : ℝ → Functional X k) (G : ℝ → ℝ),
      Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, IsMetricCurrent (S t) ∧ IntegerRectifiable (S t) ∧ mass (S t) ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K * mass C.action ∧
      (∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
        C.action b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π) ∧
      (∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
        ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) := by
  obtain ⟨D,hDd,_hDsub,hDu,hDm,hDI,hDact⟩ := C.exists_scalar_straightened_charts hK
  choose G hG hG0 hGm hGI using fun i => (D i).sharp_coordinate_coarea_majorant hX hK (hDu i)
  let Q i t := (D i).coordinateSliceTotal t
  let S : ℝ → Functional X k := fun t b π => ∑' i, (Q i t).action b π
  have hGIs : Summable (fun i => ∫ t : ℝ, G i t) := by
    simp_rw [hGI]
    exact hDm.mul_left (K:ℝ)
  have hGn : Summable (fun i => ∫ t : ℝ, ‖G i t‖) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using hGIs
  have hGa : ∀ᵐ t : ℝ, Summable (fun i => G i t) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using ae_summable_norm_of_integral hG hGn
  have hQa : ∀ᵐ t : ℝ, Summable (fun i => mass (Q i t).action) := by
    filter_upwards [hGa,ae_all_iff.mpr hGm] with t hs hm
    exact hs.of_nonneg_of_le (fun i => mass_nonneg _) hm
  have hQd (t : ℝ) : Pairwise (fun i j => Disjoint (Q i t).image (Q j t).image) := by
    intro i j hij
    exact (hDd hij).mono ((D i).coordinateSliceTotal_image_subset t)
      ((D j).coordinateSliceTotal_image_subset t)
  refine ⟨S,fun t => ∑' i, G i t,integrable_series hG hGn,
    fun t => tsum_nonneg (fun i => hG0 i t),?_,?_,?_,?_⟩
  · filter_upwards [hQa,hGa,ae_all_iff.mpr hGm] with t hqt hgt hmt
    refine ⟨isMetricCurrent_tsum (fun i => (Q i t).action_isMetricCurrent) hqt,
      ⟨fun i => Q i t,hQd t,fun i => (Q i t).action_isMetricCurrent,hqt,fun _ _ => rfl⟩,?_⟩
    exact (mass_tsum_le (fun i => (Q i t).action_isMetricCurrent) hqt).trans
      (hqt.tsum_le_tsum hmt hgt)
  · rw [←integral_tsum_of_summable_integral_norm hG hGn]
    simp_rw [hGI]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hDI K.coe_nonneg
  · intro b π hab
    have hi i : Integrable (fun t : ℝ => (Q i t).action b π) :=
      (D i).coordinateSlice_action_integrable hK (hDu i) hab
    choose L hL using hab.2
    obtain ⟨M,hM⟩ := hab.1.2
    let A : ℝ := (∏ j, (L j:ℝ)) * max M 0
    have hA : 0 ≤ A := mul_nonneg (Finset.prod_nonneg fun j _ => (L j).coe_nonneg) (le_max_right _ _)
    have hbound i : ∀ᵐ t : ℝ, ‖(Q i t).action b π‖ ≤ A * G i t := by
      filter_upwards [hGm i] with t ht
      rw [Real.norm_eq_abs]
      exact ((Q i t).action_isMetricCurrent.mass_bound_uniform hab.1 L hL
        (fun x => (hM x).trans (le_max_left _ _))).trans
          (mul_le_mul_of_nonneg_left ht hA)
    have hIs : Summable (fun i => ∫ t : ℝ, ‖(Q i t).action b π‖) := by
      apply (hGIs.mul_left A).of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
      intro i
      rw [←integral_const_mul]
      exact integral_mono_ae (hi i).norm ((hG i).const_mul A) (hbound i)
    refine ⟨integrable_series hi hIs,?_⟩
    rw [show C.action b (Matrix.vecCons u π) = ∑' i, (D i).action b (Matrix.vecCons u π)
      from hDact b π hab]
    simp_rw [fun i => (D i).coordinateSlice_action_integral hK (hDu i) hab]
    exact integral_tsum_of_summable_integral_norm hi hIs
  · intro b π hab φ hφ
    filter_upwards [ae_all_iff.mpr (fun i =>
      (D i).ae_coordinateSliceTotal_weighted (hDu i) hab φ hφ)] with t ht
    change (∑' i, (Q i t).action (fun x => φ (u x)*b x) π) = φ t * ∑' i, (Q i t).action b π
    exact (tsum_congr fun i => ht i).trans tsum_mul_left

end CAT0Fillings.IntegerChart

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_RectifiableCoarea
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

theorem integerRectifiable_scalar_coarea {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hI : IntegerRectifiable T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ (S : ℝ → Functional X k) (G : ℝ → ℝ),
      Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, IsMetricCurrent (S t) ∧ IntegerRectifiable (S t) ∧ mass (S t) ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K * mass T ∧
      (∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
        T b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π) ∧
      (∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
        ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) := by
  obtain ⟨C,hd,hC,hCS,heq⟩ := hI
  have hmass := chartFamily_mass_sum_le hT C hd hC hCS heq
  choose Q G hG hG0 hQ hGI hQact hQweight using fun i => (C i).exists_scalar_coarea hX hK
  let S : ℝ → Functional X k := fun t b π => ∑' i, Q i t b π
  have hGIs : Summable (fun i => ∫ t : ℝ, G i t) := by
    apply (hCS.mul_left (K:ℝ)).of_nonneg_of_le
      (fun i => integral_nonneg (hG0 i)) hGI
  have hGn : Summable (fun i => ∫ t : ℝ, ‖G i t‖) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using hGIs
  have hGa : ∀ᵐ t : ℝ, Summable (fun i => G i t) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using ae_summable_norm_of_integral hG hGn
  have hQa : ∀ᵐ t : ℝ, Summable (fun i => mass (Q i t)) := by
    filter_upwards [hGa,ae_all_iff.mpr hQ] with t hs hm
    exact hs.of_nonneg_of_le (fun i => mass_nonneg _) (fun i => (hm i).2.2)
  refine ⟨S,fun t => ∑' i, G i t,integrable_series hG hGn,
    fun t => tsum_nonneg (fun i => hG0 i t),?_,?_,?_,?_⟩
  · filter_upwards [hQa,hGa,ae_all_iff.mpr hQ] with t hqt hgt hmt
    refine ⟨isMetricCurrent_tsum (fun i => (hmt i).1) hqt,
      integerRectifiable_tsum (fun i => (hmt i).1) (fun i => (hmt i).2.1) hqt,?_⟩
    exact (mass_tsum_le (fun i => (hmt i).1) hqt).trans
      (hqt.tsum_le_tsum (fun i => (hmt i).2.2) hgt)
  · rw [←integral_tsum_of_summable_integral_norm hG hGn]
    calc
      (∑' i, ∫ t : ℝ, G i t) ≤ ∑' i, (K:ℝ)*mass (C i).action :=
        hGIs.tsum_le_tsum hGI (hCS.mul_left _)
      _ = (K:ℝ)*(∑' i, mass (C i).action) := tsum_mul_left
      _ ≤ (K:ℝ)*mass T := mul_le_mul_of_nonneg_left hmass K.coe_nonneg
  · intro b π hab
    have hi i : Integrable (fun t : ℝ => Q i t b π) := (hQact i b π hab).1
    choose L hL using hab.2
    obtain ⟨M,hM⟩ := hab.1.2
    let A : ℝ := (∏ j, (L j:ℝ)) * max M 0
    have hA : 0 ≤ A := mul_nonneg (Finset.prod_nonneg fun j _ => (L j).coe_nonneg) (le_max_right _ _)
    have hbound i : ∀ᵐ t : ℝ, ‖Q i t b π‖ ≤ A * G i t := by
      filter_upwards [hQ i] with t ht
      rw [Real.norm_eq_abs]
      exact (ht.1.mass_bound_uniform hab.1 L hL
        (fun x => (hM x).trans (le_max_left _ _))).trans
          (mul_le_mul_of_nonneg_left ht.2.2 hA)
    have hIs : Summable (fun i => ∫ t : ℝ, ‖Q i t b π‖) := by
      apply (hGIs.mul_left A).of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
      intro i
      rw [←integral_const_mul]
      exact integral_mono_ae (hi i).norm ((hG i).const_mul A) (hbound i)
    refine ⟨integrable_series hi hIs,?_⟩
    rw [heq]
    simp_rw [fun i => (hQact i b π hab).2]
    exact integral_tsum_of_summable_integral_norm hi hIs
  · intro b π hab φ hφ
    filter_upwards [ae_all_iff.mpr (fun i => hQweight i b π hab φ hφ)] with t ht
    change (∑' i, Q i t (fun x => φ (u x)*b x) π) = φ t * ∑' i, Q i t b π
    exact (tsum_congr fun i => ht i).trans tsum_mul_left

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Addition
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter MassMeasure BorelCoefficients
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
lemma controls_add {T U : Functional X k} {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hT : Controls T μ) (hU : Controls U ν) :
    Controls (T+U) (μ+ν) := by
  intro b π hb hπ
  have hiμ := (integrable_boundedLip μ hb).abs
  have hiν := (integrable_boundedLip ν hb).abs
  change |T b π + U b π| ≤ _
  rw [integral_add_measure hiμ hiν]
  exact (abs_add_le _ _).trans (add_le_add (hT b π hb hπ) (hU b π hb hπ))

lemma IsMetricCurrent.add {T U : Functional X k} (hT : IsMetricCurrent T)
    (hU : IsMetricCurrent U) : IsMetricCurrent (T+U) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    simp only [Pi.add_apply,hT.offDomain b π hab,hU.offDomain b π hab,add_zero]
  · intro b c π a d hb hc hπ
    simp only [Pi.add_apply,hT.linearFirst b c π a d hb hc hπ,
      hU.linearFirst b c π a d hb hc hπ]
    ring
  · intro b π i f a c hb hf
    simp only [Pi.add_apply,hT.linearCoord b π i f a c hb hf,
      hU.linearCoord b π i f a c hb hf]
    ring
  · intro b π πs hb hπ hlim
    exact (hT.sequentialContinuity b π πs hb hπ hlim).add
      (hU.sequentialContinuity b π πs hb hπ hlim)
  · intro b π hab hl
    simp only [Pi.add_apply,hT.locality b π hab hl,hU.locality b π hab hl,add_zero]
  · obtain ⟨μ,hμ,hc⟩ := hT.finiteMass
    obtain ⟨ν,hν,hd⟩ := hU.finiteMass
    let := hμ; let := hν
    exact ⟨μ+ν,inferInstance,controls_add hc hd⟩

lemma mass_add_le {T U : Functional X k} (hT : IsMetricCurrent T)
    (hU : IsMetricCurrent U) : mass (T+U) ≤ mass T + mass U := by
  have hh := mass_le_measure (μ := currentMassMeasure hT + currentMassMeasure hU)
    inferInstance (controls_add (currentMassMeasure_controls hT) (currentMassMeasure_controls hU))
  have he : (currentMassMeasure hT + currentMassMeasure hU).real univ =
      (currentMassMeasure hT).real univ + (currentMassMeasure hU).real univ := by
    simp only [Measure.real,Measure.add_apply,ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [he,currentMassMeasure_total,currentMassMeasure_total] at hh
  exact hh

lemma IntegerRectifiable.add [Nonempty X] {T U : Functional X k}
    (hT : IsMetricCurrent T) (hU : IsMetricCurrent U)
    (hI : IntegerRectifiable T) (hJ : IntegerRectifiable U) : IntegerRectifiable (T+U) := by
  let A : ℕ → Functional X k := fun i => if i=0 then T else if i=1 then U else 0
  have hA i : IsMetricCurrent (A i) := by
    dsimp [A]; split_ifs <;> first | exact hT | exact hU | exact isMetricCurrent_zero _
  have hAI i : IntegerRectifiable (A i) := by
    dsimp [A]; split_ifs <;> first | exact hI | exact hJ | exact integerRectifiable_zero _
  have hAS : Summable (fun i => mass (A i)) := by
    apply summable_of_ne_finset_zero (s := {0,1})
    intro i hi
    have h0 : i ≠ 0 := fun h => hi (by simp [h])
    have h1 : i ≠ 1 := fun h => hi (by simp [h])
    simp only [A,ite_eq_right h0,ite_eq_right h1]
    exact mass_zero _
  have heq : (fun b π => ∑' i, A i b π) = T+U := by
    funext b π
    rw [tsum_eq_sum (s := {0,1}) (fun i hi => ?_)]
    · simp [A]
    · have h0 : i ≠ 0 := fun h => hi (by simp [h])
      have h1 : i ≠ 1 := fun h => hi (by simp [h])
      simp [A,h0,h1]
  rw [←heq]
  exact integerRectifiable_tsum hA hAI hAS

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Negation
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}

omit [BorelSpace X] in
lemma mass_neg (T : Functional X k) : mass (-T) = mass T := by
  simp only [mass,controls_neg_iff]

omit [BorelSpace X] in
lemma IsMetricCurrent.neg {T : Functional X k} (hT : IsMetricCurrent T) :
    IsMetricCurrent (-T) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    simp only [Pi.neg_apply,hT.offDomain b π hab,neg_zero]
  · intro b c π a d hb hc hπ
    simp only [Pi.neg_apply,hT.linearFirst b c π a d hb hc hπ]
    ring
  · intro b π i f a c hb hf
    simp only [Pi.neg_apply,hT.linearCoord b π i f a c hb hf]
    ring
  · intro b π πs hb hπ hlim
    exact (hT.sequentialContinuity b π πs hb hπ hlim).neg
  · intro b π hab hl
    simp only [Pi.neg_apply,hT.locality b π hab hl,neg_zero]
  · obtain ⟨μ,hμ,hc⟩ := hT.finiteMass
    exact ⟨μ,hμ,controls_neg_iff.mpr hc⟩

namespace IntegerChart
variable (C : IntegerChart X k)

omit [MeasurableSpace X] [BorelSpace X] in
lemma negate_action : C.negate.action = -C.action := by
  classical
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab,Pi.neg_apply]
    change (∫ z in C.domain,(-C.multiplicity z:ℤ)*C.scalar b z*C.jacobian π z) =
      -(∫ z in C.domain,(C.multiplicity z:ℝ)*C.scalar b z*C.jacobian π z)
    simp only [Int.cast_neg,neg_mul,integral_neg]
  · simp only [action,ite_eq_right hab,Pi.neg_apply,neg_zero]
end IntegerChart

omit [BorelSpace X] in
lemma IntegerRectifiable.neg {T : Functional X k} (hI : IntegerRectifiable T) :
    IntegerRectifiable (-T) := by
  obtain ⟨C,hd,hC,hS,heq⟩ := hI
  refine ⟨fun i => (C i).negate,hd,?_,?_,?_⟩
  · intro i
    rw [IntegerChart.negate_action]
    exact (hC i).neg
  · simp_rw [IntegerChart.negate_action,mass_neg]
    exact hS
  · intro b π
    simp only [IntegerChart.negate_action,Pi.neg_apply,heq,tsum_neg]

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Contraction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {k : ℕ}

omit [MeasurableSpace X] in
lemma contractCurrent_apply (u : X → ℝ) (T : Functional X (k+1))
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    contractCurrent u T b π = T b (Matrix.vecCons u π) := ite_eq_left h

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_ChainRule
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma ae_fderivWithin_scalar_comp {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t) :
    ∀ᵐ z ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (φ ∘ u)) C.domain z =
        dφ (C.scalar u z) • fderivWithin ℝ (C.scalar u) C.domain z := by
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,ae_restrict_mem C.borel,
    C.ae_differentiableWithinAt_scalar hu] with z hz hzs hdu
  have heq : EqOn (C.scalar (φ ∘ u)) (φ ∘ C.scalar u) C.domain := by
    intro y hy
    simp only [Function.comp_apply,C.scalar_eq hy]
  have hh := (hφ (C.scalar u z)).comp_hasFDerivWithinAt z hdu.hasFDerivWithinAt
  exact (hh.congr heq (heq hzs)).fderivWithin hz

lemma ae_jacobian_update_comp (π : Fin k → X → ℝ) (i : Fin k)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (φ ∘ u)) z =
        dφ (C.scalar u z) * C.jacobian (Function.update π i u) z := by
  filter_upwards [C.ae_fderivWithin_scalar_comp hu hφ] with z hz
  rw [C.jacobian_update,C.jacobian_update,hz]
  simpa only [_root_.smul_apply,Pi.smul_def,smul_eq_mul] using Matrix.det_updateRow_smul
    (Matrix.of fun a j => fderivWithin ℝ (C.scalar (π a)) C.domain z (EuclideanSpace.single j 1))
    i (dφ (C.scalar u z))
    (fun j => fderivWithin ℝ (C.scalar u) C.domain z (EuclideanSpace.single j 1))

lemma action_update_comp {b u : X → ℝ} (hb : BoundedLip b) (hu : BoundedLip u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hφu : BoundedLip (φ ∘ u)) (hdu : BoundedLip (dφ ∘ u))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) :
    C.action b (Function.update π i (φ ∘ u)) =
      C.action (fun x => b x * dφ (u x)) (Function.update π i u) := by
  obtain ⟨K,hK⟩ := hu.1
  have hup {a : X → ℝ} (ha : BoundedLip a) :
      ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i a) j) := by
    intro j
    by_cases hji : j = i
    · simpa [hji] using ha.1
    · simpa [hji] using hπ j
  rw [action,ite_eq_left ⟨hb,hup hφu⟩,action,ite_eq_left ⟨hb.mul hdu,hup hu⟩]
  apply integral_congr_ae
  filter_upwards [C.ae_jacobian_update_comp π i hK hφ,ae_restrict_mem C.borel] with z hz hzs
  rw [hz,C.scalar_eq hzs,C.scalar_eq hzs,C.scalar_eq hzs]
  ring

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [BorelSpace X] [CompactSpace X] in
lemma IntegerRectifiable.apply_update_comp {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b u : X → ℝ} (hb : BoundedLip b) (hu : BoundedLip u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hφu : BoundedLip (φ ∘ u)) (hdu : BoundedLip (dφ ∘ u))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) :
    T b (Function.update π i (φ ∘ u)) =
      T (fun x => b x * dφ (u x)) (Function.update π i u) := by
  obtain ⟨C,_,_,_,heq⟩ := hT
  rw [heq,heq]
  apply tsum_congr
  intro j
  exact (C j).action_update_comp hb hu hφ hφu hdu π hπ i

end CAT0Fillings.Foundations

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings.SmoothCutoff
open Set Filter
open scoped Topology NNReal

lemma profile_hasDerivAt (a : ℝ≥0) (t x : ℝ) :
    HasDerivAt (profile a t) (dprofile a t x) x := by
  have hd := ((@Real.smoothTransition.contDiff 1).differentiable (by norm_num) ((a:ℝ)*(x-t))).hasDerivAt
  change HasDerivAt (fun y => Real.smoothTransition ((a:ℝ)*(y-t)))
    ((a:ℝ)*deriv Real.smoothTransition ((a:ℝ)*(x-t))) x
  simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using
    hd.comp x (((hasDerivAt_id x).sub_const t).const_mul (a:ℝ))

lemma dprofile_zero {a : ℝ≥0} (ha : 0 < a) {t x : ℝ}
    (hx : x ∉ Icc t (t+(a:ℝ)⁻¹)) : dprofile a t x = 0 := by
  have ha' : 0 < (a:ℝ) := ha
  have hnot : (a:ℝ)*(x-t) ∉ Icc 0 1 := by
    intro h
    apply hx
    refine ⟨?_,?_⟩
    · have : 0 ≤ x-t := (mul_nonneg_iff_of_pos_left ha').mp h.1
      linarith
    · have : x-t ≤ (a:ℝ)⁻¹ := by
        rw [inv_eq_one_div]
        apply (le_div_iff₀ ha').mpr
        simpa [mul_comm] using h.2
      linarith
  simp [dprofile,deriv_transition_eq_zero hnot]

end CAT0Fillings.SmoothCutoff
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_NormalRestriction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter BorelCoefficients BorelRestriction MassMeasure SmoothCutoff
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma dprofile_comp_boundedLip {u : X → ℝ} (hu : BoundedLip u)
    (a : ℝ≥0) (t : ℝ) : BoundedLip (dprofile a t ∘ u) := by
  obtain ⟨K,hK⟩ := hu.1
  obtain ⟨C,hC⟩ := exists_profile_bounds
  refine ⟨⟨_,(hC a t).2.1.comp hK⟩,(C*a:ℝ≥0),fun x => ?_⟩
  exact (hC a t).2.2 (u x)

lemma profile_boundary_tendsto {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) {u : X → ℝ} (hu : BoundedLip u) (t : ℝ)
    (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π) :
    Tendsto (fun n : ℕ => boundarySucc (weightedCurrent (currentMassMeasure hT) hT
      (profile ((n:ℝ≥0)+1) t ∘ u)) b π) atTop
      (𝓝 (boundarySucc (restrictCurrent hT {x | t < u x}) b π)) := by
  let μ := currentMassMeasure hT
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
  have hcons : Admissible (fun _ : X => (1:ℝ)) (Matrix.vecCons b π) :=
    ⟨BoundedLip.const 1,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩
  simp only [boundarySucc,ite_eq_left hab,weightedCurrent,ite_eq_left hcons,mul_one,
    restrictCurrent,Function.comp_apply]
  exact borelAction_tendsto μ hT (currentMassMeasure_controls hT)
    ((integrable_const _).indicator hE)
    (fun n => integrable_boundedLip μ (profile_comp_boundedLip hu _ t))
    (profile_L1_tendsto μ hu t) (Matrix.vecCons b π) hcons.2

end CAT0Fillings.Slicing
open Set MeasureTheory Filter
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_ProfileIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings.SmoothCutoff
open Set MeasureTheory Filter Metric
open scoped Topology NNReal

lemma dprofile_integrable {a : ℝ≥0} (ha : 0 < a) (t : ℝ) :
    Integrable (dprofile a t) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  have hc := (hC a t).2.1.continuous
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro isCompact_Icc
  exact fun x hx => dprofile_zero ha hx

lemma integral_dprofile {a : ℝ≥0} (ha : 0 < a) (t : ℝ) :
    (∫ x : ℝ, dprofile a t x) = 1 := by
  have ha' : 0 < (a:ℝ) := ha
  obtain ⟨C,hC⟩ := exists_profile_bounds
  have hc := (hC a t).2.1.continuous
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => dprofile_zero ha hx),
    integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (show t ≤ t+(a:ℝ)⁻¹ from le_add_of_nonneg_right (inv_nonneg.mpr ha'.le)),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => profile_hasDerivAt a t x)
      (hc.intervalIntegrable _ _)]
  simp [profile,ha'.ne',Real.smoothTransition.one_of_one_le]

lemma dprofile_mul_integrable {f : ℝ → ℝ} (hf : Integrable f) (a : ℝ≥0) (t : ℝ) :
    Integrable (fun x => dprofile a t x * f x) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  exact hf.bdd_mul (hC a t).2.1.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (hC a t).2.2 x)

theorem ae_tendsto_dprofile_integral {f : ℝ → ℝ} (hf : Integrable f) :
    ∀ᵐ t : ℝ, Tendsto (fun n : ℕ => ∫ x : ℝ,
      dprofile ((n:ℝ≥0)+1) t x * f x) atTop (𝓝 (f t)) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  let a : ℕ → ℝ≥0 := fun n => (n:ℝ≥0)+1
  let r : ℕ → ℝ := fun n => ((a n:ℝ))⁻¹
  have hap n : 0 < a n := by dsimp [a]; positivity
  have harp n : 0 < (a n:ℝ) := hap n
  have hrp n : 0 < r n := inv_pos.mpr (harp n)
  have hrt : Tendsto r atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall fun n => hrp n⟩
    exact tendsto_inv_atTop_zero.comp
      (show Tendsto (fun n : ℕ => (a n:ℝ)) atTop atTop from by
        simpa only [a,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using
          tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hf.locallyIntegrable 0]
    with t ht
  have hav := ht (fun _ : ℕ => t) r hrt
    (Eventually.of_forall fun n => by simp only [zero_mul]; exact mem_closedBall_self le_rfl)
  have hbound n : ‖(∫ x : ℝ, dprofile (a n) t x * f x)-f t‖ ≤
      (2*(C:ℝ)) * (⨍ x in closedBall t (r n), ‖f x-f t‖) := by
    have hk := dprofile_integrable (hap n) t
    have hprod := dprofile_mul_integrable hf (a n) t
    have heq : (∫ x : ℝ, dprofile (a n) t x * f x)-f t =
        ∫ x : ℝ, dprofile (a n) t x * (f x-f t) := by
      simp only [mul_sub,integral_sub hprod (hk.mul_const _),integral_mul_const,
        integral_dprofile (hap n),one_mul]
    rw [heq]
    have herr : Integrable (fun x : ℝ => dprofile (a n) t x * (f x-f t)) := by
      apply (hprod.sub (hk.mul_const (f t))).congr
      filter_upwards [] with x
      exact (mul_sub _ _ _).symm
    have hnz (x : ℝ) (hx : x ∉ closedBall t (r n)) : dprofile (a n) t x = 0 := by
      apply dprofile_zero (hap n)
      intro hi
      apply hx
      rw [Real.closedBall_eq_Icc]
      change t-r n ≤ x ∧ x ≤ t+r n
      exact ⟨by linarith [hi.1,hrp n],hi.2⟩
    have hloc : IntegrableOn (fun x : ℝ => ‖f x-f t‖) (closedBall t (r n)) :=
      (hf.integrableOn.sub (integrableOn_const (measure_closedBall_lt_top.ne))).norm
    calc
      ‖∫ x : ℝ, dprofile (a n) t x * (f x-f t)‖ ≤
          ∫ x : ℝ, ‖dprofile (a n) t x * (f x-f t)‖ := norm_integral_le_integral_norm _
      _ = ∫ x in closedBall t (r n), ‖dprofile (a n) t x * (f x-f t)‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hnz x hx,zero_mul,norm_zero])).symm
      _ ≤ ∫ x in closedBall t (r n), ((C:ℝ)*(a n:ℝ)) * ‖f x-f t‖ := by
        apply setIntegral_mono_on herr.norm.integrableOn (hloc.const_mul _) isClosed_closedBall.measurableSet
        intro x _
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [Real.norm_eq_abs,NNReal.coe_mul] using (hC (a n) t).2.2 x
      _ = (2*(C:ℝ)) * (⨍ x in closedBall t (r n), ‖f x-f t‖) := by
        rw [integral_const_mul,setAverage_eq,Real.volume_real_closedBall (hrp n).le,
          smul_eq_mul]
        dsimp [r]
        field_simp
  have hzero := squeeze_zero_norm hbound (by simpa only [mul_zero] using hav.const_mul (2*(C:ℝ)))
  simpa only [sub_add_cancel,zero_add] using hzero.add_const (f t)

end CAT0Fillings.SmoothCutoff
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_GeneralCoarea
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter BorelCoefficients SmoothCutoff BorelRestriction MassMeasure
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
omit [Nonempty X] in
lemma weightedCurrent_boundary {T : Functional X (k+1)} (hT : IsMetricCurrent T)
    (hI : IntegerRectifiable T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : BoundedLip u) :
    boundarySucc (weightedCurrent (currentMassMeasure hT) hT u) =
      weightedCurrent (currentMassMeasure hB) hB u - contractCurrent u T := by
  classical
  funext b π
  by_cases hab : Admissible b π
  · have hcons : Admissible (fun _ : X => (1:ℝ)) (Matrix.vecCons b π) :=
      ⟨BoundedLip.const 1,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩
    simp only [boundarySucc,ite_eq_left hab,weightedCurrent,ite_eq_left hcons,mul_one,
      Pi.sub_apply,contractCurrent_apply _ _ hab]
    rw [borelAction_eq _ hT (currentMassMeasure_controls hT)
      ⟨hu,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩,
      borelAction_eq _ hB (currentMassMeasure_controls hB) ⟨hu.mul hab.1,hab.2⟩]
    have h := Foundations.IntegerRectifiable.product_rule hI hab.1 hu π hab.2
    have he : (fun x => b x*u x) = (fun x => u x*b x) := by funext x; exact mul_comm _ _
    rw [he] at h
    linarith
  · simp only [boundarySucc,ite_eq_right hab,Pi.sub_apply,weightedCurrent,contractCurrent,sub_zero]

omit [Nonempty X] in
lemma boundary_profile_coarea_general {T : Functional X (k+1)} (hT : IsMetricCurrent T)
    (hI : IntegerRectifiable T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : BoundedLip u) {S : ℝ → Functional X k}
    (hact : ∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π)
    (hweight : ∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
      ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π)
    (a : ℝ≥0) (t : ℝ) {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    boundarySucc (weightedCurrent (currentMassMeasure hT) hT (profile a t ∘ u)) b π =
      weightedCurrent (currentMassMeasure hB) hB (profile a t ∘ u) b π -
      ∫ s : ℝ, dprofile a t s * S s b π := by
  rw [weightedCurrent_boundary hT hI hB (profile_comp_boundedLip hu a t)]
  simp only [Pi.sub_apply,contractCurrent_apply _ _ hab]
  congr 1
  have hπ' : ∀ i, ∃ L : ℝ≥0, LipschitzWith L (Matrix.vecCons u π i) :=
    fun i => Fin.cases hu.1 (fun j => hab.2 j) i
  have hchain := Foundations.IntegerRectifiable.apply_update_comp hI hab.1 hu
    (profile_hasDerivAt a t) (profile_comp_boundedLip hu a t)
    (dprofile_comp_boundedLip hu a t) (Matrix.vecCons u π) hπ' 0
  simp only [vecCons_update_head] at hchain
  rw [hchain]
  have heq : (fun x => b x*dprofile a t (u x)) = (fun x => (dprofile a t ∘ u) x*b x) := by
    funext x; exact mul_comm _ _
  rw [heq,(hact _ π ⟨(dprofile_comp_boundedLip hu a t).mul hab.1,hab.2⟩).2]
  exact integral_congr_ae (hweight b π hab (dprofile a t) (dprofile_comp_boundedLip hu a t))

theorem ae_integral_restrict {T : Functional X (k+1)} (hT : IsIntegral (k+1) T)
    (hX : IsCAT0 X) {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K * mass T ∧
      ∀ᵐ t : ℝ, IsIntegral (k+1) (restrictCurrent hT.1 {x | t < u x}) ∧
        mass (boundarySucc (restrictCurrent hT.1 {x | t < u x})) ≤
          mass (restrictCurrent hT.2.2.1 {x | t < u x}) + G t := by
  have hu : BoundedLip u := ⟨⟨K,hK⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT.1 hT.2.1 hX hK
  let E (t : ℝ) := {x | t < u x}
  have hE t : MeasurableSet (E t) := measurableSet_lt measurable_const hu.continuous.measurable
  let B (t : ℝ) := restrictCurrent hT.2.2.1 (E t)
  have hB t : IsMetricCurrent (B t) := restrictCurrent_isMetricCurrent hT.2.2.1 (hE t)
  have htest (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π) :
      ∀ᵐ t : ℝ, boundarySucc (restrictCurrent hT.1 (E t)) b π = (B t + -S t) b π := by
    filter_upwards [ae_tendsto_dprofile_integral (hact b π hab).1] with t ht
    have hl := profile_boundary_tendsto hT.1 hu t b π hab
    have hr := (profile_current_tendsto hT.2.2.1 hu t b π hab).sub ht
    have heq (n : ℕ) := boundary_profile_coarea_general hT.1 hT.2.1 hT.2.2.1 hu hact hweight ((n:ℝ≥0)+1) t hab
    simpa only [Pi.add_apply,Pi.neg_apply,sub_eq_add_neg] using
      tendsto_nhds_unique (hl.congr (fun n => heq n)) hr
  have heq : ∀ᵐ t : ℝ, boundarySucc (restrictCurrent hT.1 (E t)) = B t + -S t :=
    Foundations.ae_boundary_eq_of_ae_test_eq volume
      (Eventually.of_forall fun t => restrictCurrent_isMetricCurrent hT.1 (hE t))
      (hS.mono fun t ht => (hB t).add ht.1.neg) htest
  refine ⟨G,hG,hG0,hGI,?_⟩
  filter_upwards [hS,heq] with t hs he
  have hBI := integerRectifiable_restrict hT.2.2.1 hT.2.2.2 (hE t)
  have hMC := (hB t).add hs.1.neg
  have hIR := hBI.add (hB t) hs.1.neg hs.2.1.neg
  refine ⟨⟨restrictCurrent_isMetricCurrent hT.1 (hE t),
    integerRectifiable_restrict hT.1 hT.2.1 (hE t),he.symm ▸ hMC,he.symm ▸ hIR⟩,?_⟩
  rw [he]
  exact (mass_add_le (hB t) hs.1.neg).trans (by simpa only [mass_neg] using add_le_add (le_rfl : mass (B t) ≤ mass (B t)) hs.2.2)

end CAT0Fillings.Slicing

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_Superlevels
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter BorelCoefficients SmoothCutoff BorelRestriction MassMeasure Foundations
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma ae_superlevelSlice_eq_coarea {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hI : IntegerRectifiable T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : BoundedLip u) {S : ℝ → Functional X k}
    (hS : ∀ᵐ t : ℝ, IsMetricCurrent (S t))
    (hact : ∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π)
    (hweight : ∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
      ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) :
    ∀ᵐ t : ℝ, superlevelSlice hT hB u t = S t := by
  let E (t : ℝ) := {x | t < u x}
  have hE t : MeasurableSet (E t) := measurableSet_lt measurable_const hu.continuous.measurable
  let B (t : ℝ) := restrictCurrent hB (E t)
  have hBc t : IsMetricCurrent (B t) := restrictCurrent_isMetricCurrent hB (hE t)
  have htest (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π) :
      ∀ᵐ t : ℝ, boundarySucc (restrictCurrent hT (E t)) b π = (B t + -S t) b π := by
    filter_upwards [ae_tendsto_dprofile_integral (hact b π hab).1] with t ht
    have hl := profile_boundary_tendsto hT hu t b π hab
    have hr := (profile_current_tendsto hB hu t b π hab).sub ht
    have heq (n : ℕ) := boundary_profile_coarea_general hT hI hB hu hact hweight ((n:ℝ≥0)+1) t hab
    simpa only [Pi.add_apply,Pi.neg_apply,sub_eq_add_neg] using
      tendsto_nhds_unique (hl.congr (fun n => heq n)) hr
  have heq : ∀ᵐ t : ℝ, boundarySucc (restrictCurrent hT (E t)) = B t + -S t :=
    ae_boundary_eq_of_ae_test_eq volume
      (Eventually.of_forall fun t => restrictCurrent_isMetricCurrent hT (hE t))
      (hS.mono fun t ht => (hBc t).add ht.neg) htest
  filter_upwards [heq] with t ht
  change B t - boundarySucc (restrictCurrent hT (E t)) = S t
  rw [ht]
  abel

lemma superlevelSlice_coarea_bound [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K*mass T ∧
      ∀ᵐ t : ℝ, IsMetricCurrent (superlevelSlice hT.1 hT.2.2.1 u t) ∧
        IntegerRectifiable (superlevelSlice hT.1 hT.2.2.1 u t) ∧
        mass (superlevelSlice hT.1 hT.2.2.1 u t) ≤ G t := by
  have hu : BoundedLip u := ⟨⟨K,hK⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT.1 hT.2.1 hX hK
  refine ⟨G,hG,hG0,hGI,?_⟩
  filter_upwards [hS,ae_superlevelSlice_eq_coarea hT.1 hT.2.1 hT.2.2.1 hu
    (hS.mono fun t ht => ht.1) hact hweight] with t ht he
  rw [he]
  exact ht

end CAT0Fillings.Slicing

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Set MeasureTheory Filter
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_IntegralBoundary
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter Foundations BorelRestriction MassMeasure
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma boundarySucc_sub {k : ℕ} (T U : Functional X (k+1)) :
    boundarySucc (T-U) = boundarySucc T - boundarySucc U := by
  funext b π
  by_cases h : Admissible b π <;> simp [boundarySucc,h]

omit [BorelSpace X] [CompactSpace X] in
lemma IsIntegral.boundarySucc {k : ℕ} {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) :
    IsIntegral k (boundarySucc T) := by
  cases k with
  | zero => exact hT.2.2
  | succ k =>
    refine ⟨hT.2.2.1,hT.2.2.2,?_,?_⟩ <;> rw [Foundations.boundarySucc_boundarySucc hT.1]
    · exact isMetricCurrent_zero k
    · exact integerRectifiable_zero k

lemma IsIntegral.sub [Nonempty X] {k : ℕ} {T U : Functional X k}
    (hT : IsIntegral k T) (hU : IsIntegral k U) : IsIntegral k (T-U) := by
  cases k with
  | zero =>
    change IsMetricCurrent (T-U) ∧ IntegerRectifiable (T-U)
    simpa only [sub_eq_add_neg] using
      And.intro (hT.1.add hU.1.neg) (hT.2.add hT.1 hU.1.neg hU.2.neg)
  | succ k =>
    have hmain : IsMetricCurrent (T-U) ∧ IntegerRectifiable (T-U) := by
      simpa only [sub_eq_add_neg] using
        And.intro (hT.1.add hU.1.neg) (hT.2.1.add hT.1 hU.1.neg hU.2.1.neg)
    refine ⟨hmain.1,hmain.2,?_,?_⟩ <;> rw [boundarySucc_sub,sub_eq_add_neg]
    · exact hT.2.2.1.add hU.2.2.1.neg
    · exact hT.2.2.2.add hT.2.2.1 hU.2.2.1.neg hU.2.2.2.neg

namespace Slicing

lemma restrictCurrent_zero_of_eq_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (hzero : T = 0) {E : Set X} (hE : MeasurableSet E) :
    restrictCurrent hT E = 0 := by
  apply (restrictCurrent_isMetricCurrent hT hE).eq_zero_of_mass_eq_zero
  apply le_antisymm _ (mass_nonneg _)
  rw [restriction_mass hT hE]
  have hm := ENNReal.toReal_mono (measure_ne_top (currentMassMeasure hT) univ)
    (measure_mono (subset_univ E) : currentMassMeasure hT E ≤ currentMassMeasure hT univ)
  change (currentMassMeasure hT).real E ≤ (currentMassMeasure hT).real univ at hm
  rw [currentMassMeasure_total] at hm
  have hz : mass T = 0 := by rw [hzero]; exact mass_zero k
  exact hm.trans_eq hz

lemma boundary_superlevelSlice {k : ℕ} {T : Functional X (k+1+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (hBB : IsMetricCurrent (boundarySucc (boundarySucc T)))
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ) :
    boundarySucc (superlevelSlice hT hB u t) = -superlevelSlice hB hBB u t := by
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
  have hzero := Foundations.boundarySucc_boundarySucc hT
  have hrzero := restrictCurrent_zero_of_eq_zero hBB hzero hE
  unfold superlevelSlice
  rw [boundarySucc_sub,Foundations.boundarySucc_boundarySucc (restrictCurrent_isMetricCurrent hT hE),hrzero]
  change (boundarySucc (restrictCurrent hB {x | t < u x}) - 0) = -(0 - boundarySucc (restrictCurrent hB {x | t < u x}))
  simp only [sub_zero,zero_sub,neg_neg]

lemma ae_superlevelSlice_integral [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∀ᵐ t : ℝ, IsIntegral k (superlevelSlice hT.1 hT.2.2.1 u t) := by
  obtain ⟨G,_,_,_,hrest⟩ := ae_integral_restrict hT hX hK
  cases k with
  | zero =>
    filter_upwards [hrest] with t ht
    have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hK.continuous.measurable
    have hB : IsIntegral 0 (restrictCurrent hT.2.2.1 {x | t < u x}) :=
      ⟨restrictCurrent_isMetricCurrent hT.2.2.1 hE,integerRectifiable_restrict hT.2.2.1 hT.2.2.2 hE⟩
    exact hB.sub ht.1.boundarySucc
  | succ k =>
    obtain ⟨H,_,_,_,hBr⟩ := ae_integral_restrict hT.boundarySucc hX hK
    filter_upwards [hrest,hBr] with t ht hbt
    exact hbt.1.sub ht.1.boundarySucc

lemma superlevelSlice_normal_coarea_bound [Nonempty X] {k : ℕ} {T : Functional X (k+1+1)}
    (hT : IsIntegral (k+1+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ G H : ℝ → ℝ, Integrable G ∧ Integrable H ∧
      (∀ t, 0 ≤ G t) ∧ (∀ t, 0 ≤ H t) ∧
      (∫ t : ℝ, G t) ≤ K*mass T ∧ (∫ t : ℝ, H t) ≤ K*mass (boundarySucc T) ∧
      ∀ᵐ t : ℝ, IsIntegral (k+1) (superlevelSlice hT.1 hT.2.2.1 u t) ∧
        mass (superlevelSlice hT.1 hT.2.2.1 u t) ≤ G t ∧
        mass (boundarySucc (superlevelSlice hT.1 hT.2.2.1 u t)) ≤ H t := by
  have hu : BoundedLip u := ⟨⟨K,hK⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  obtain ⟨G,hG,hG0,hGI,hS⟩ := superlevelSlice_coarea_bound hT hX hK
  obtain ⟨H,hH,hH0,hHI,hBS⟩ := superlevelSlice_coarea_bound hT.boundarySucc hX hK
  refine ⟨G,H,hG,hH,hG0,hH0,hGI,hHI,?_⟩
  filter_upwards [hS,hBS,ae_superlevelSlice_integral hT hX hK] with t ht hbt hIt
  refine ⟨hIt,ht.2.2,?_⟩
  have hBB : IsMetricCurrent (boundarySucc (boundarySucc T)) := by
    rw [Foundations.boundarySucc_boundarySucc hT.1]
    exact isMetricCurrent_zero k
  rw [boundary_superlevelSlice hT.1 hT.2.2.1 hBB hu t,mass_neg]
  exact hbt.2.2

end Slicing
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_WeakMeasures
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

theorem finiteMeasure_bounded_weak_subsequence (μs : ℕ → FiniteMeasure X)
    (M : ℝ≥0) (hM : ∀ j, (μs j).mass ≤ M) :
    ∃ μ : FiniteMeasure X, μ.mass ≤ M ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (μs ∘ ψ) atTop (𝓝 μ) := by
  obtain ⟨μ,hμ,hcluster⟩ :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X M).exists_mapClusterPt_of_frequently
      (l := atTop) (Eventually.of_forall hM).frequently
  let l := comap μs (𝓝 μ) ⊓ atTop
  have hl : NeBot l := neBot_inf_comap_iff_map'.mpr hcluster
  let := hl
  have hμlim : Tendsto μs l (𝓝 μ) := tendsto_iff_comap.mpr inf_le_left
  obtain ⟨D,hD⟩ := TopologicalSpace.exists_dense_seq C(X,ℝ)
  let F (ν : FiniteMeasure X) : ℕ → ℝ := fun i => ∫ x, D i x ∂(ν : Measure X)
  have hF : Tendsto (fun j => F (μs j)) l (𝓝 (F μ)) :=
    tendsto_pi_nhds.mpr fun i => (FiniteMeasure.continuous_integral_continuousMap (D i)).tendsto μ |>.comp hμlim
  obtain ⟨ψ,hψ,hψlim⟩ := (hF.mapClusterPt.mono (show l ≤ atTop from inf_le_right)).tendsto_subseq
  refine ⟨μ,hμ,ψ,hψ,FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_⟩
  intro f
  exact tendsto_of_lipschitz_dense
    (fun j => integral_continuousMap_lipschitz (μs (ψ j)) M (hM (ψ j)))
    (integral_continuousMap_lipschitz μ M hμ) hD
    (fun i => tendsto_pi_nhds.mp hψlim i) f.toContinuousMap

end CAT0Fillings
namespace CAT0Fillings
open Set MeasureTheory Filter MassMeasure
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma exists_weak_controlling_subsequence {k : ℕ}
    {Ts : ℕ → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (M : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    ∃ μs : ℕ → FiniteMeasure X, ∃ μ : FiniteMeasure X,
      (∀ j, Controls (Ts j) (μs j)) ∧ Controls T μ ∧ μ.mass ≤ M ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (μs ∘ ψ) atTop (𝓝 μ) := by
  let μs (j : ℕ) : FiniteMeasure X := ⟨currentMassMeasure (hTs j),inferInstance⟩
  have hc j : Controls (Ts j) (μs j) := currentMassMeasure_controls (hTs j)
  have hm j : (μs j).mass ≤ M := by
    apply NNReal.coe_le_coe.mp
    change (currentMassMeasure (hTs j)).real univ ≤ (M : ℝ)
    rw [currentMassMeasure_total]
    exact hM j
  obtain ⟨μ,hμ,ψ,hψ,hmulim⟩ := finiteMeasure_bounded_weak_subsequence μs M hm
  refine ⟨μs,μ,hc,?_,hμ,ψ,hψ,hmulim⟩
  exact controls_of_weak_limits hmulim (fun j => hc (ψ j))
    (fun b π _ => (hlim b π).comp hψ.tendsto_atTop)

lemma exists_joint_weak_controlling_subsequence {k m : ℕ}
    {Ts : ℕ → Functional X k} {T : Functional X k}
    {Us : ℕ → Functional X m} {U : Functional X m}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hUs : ∀ j, IsMetricCurrent (Us j))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (Us j) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hulim : ∀ b π, Tendsto (fun j => Us j b π) atTop (𝓝 (U b π))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ μs νs : ℕ → FiniteMeasure X, ∃ μ ν : FiniteMeasure X,
      (∀ j, Controls (Ts (ψ j)) (μs j)) ∧ Controls T μ ∧
      (∀ j, Controls (Us (ψ j)) (νs j)) ∧ Controls U ν ∧
      Tendsto μs atTop (𝓝 μ) ∧ Tendsto νs atTop (𝓝 ν) := by
  obtain ⟨μs,μ,hμs,hμ,_,φ,hφ,hφlim⟩ := exists_weak_controlling_subsequence hTs M hM hlim
  obtain ⟨νs,ν,hνs,hν,_,χ,hχ,hχlim⟩ := exists_weak_controlling_subsequence
    (fun j => hUs (φ j)) N (fun j => hN (φ j))
    (fun b π => (hulim b π).comp hφ.tendsto_atTop)
  exact ⟨φ ∘ χ,hφ.comp hχ,μs ∘ φ ∘ χ,νs ∘ χ,μ,ν,
    (fun j => hμs (φ (χ j))),hμ,(fun j => hνs (χ j)),hν,
    hφlim.comp hχ.tendsto_atTop,hχlim⟩

end CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_NormalBudget
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem NormalApprox.ae_slice {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∀ᵐ t : ℝ, NormalApprox k (superlevelSlice hT hB u t) := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := h
  have hu : BoundedLip u := boundedLip_of_lipschitz hK
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) C C hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) hT
    (fun j => (hTs (ψ j)).2.2.1) hB μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) hu
  cases k with
  | zero =>
    choose G hG hG0 hGI hS using fun j => superlevelSlice_coarea_bound (hTs (ψ j)) hX hK
    have hGI' j : (∫ t : ℝ, G j t) ≤ (K : ℝ)*C :=
      (hGI j).trans (mul_le_mul_of_nonneg_left (hM (ψ j)) K.coe_nonneg)
    have hfat := ae_exists_bounded_subsequence_of_integral_bound volume hG
      (fun j => Eventually.of_forall (hG0 j)) ((K : ℝ)*C) hGI'
    filter_upwards [hweak,ae_all_iff.mpr hS,hfat] with t ht hs hf
    obtain ⟨D,χ,hχ,hD⟩ := hf
    let R : ℝ≥0 := ⟨max D 0,le_max_right _ _⟩
    let Ss : ℕ → Functional X 0 := fun j =>
      superlevelSlice (hTs (ψ (χ j))).1 (hTs (ψ (χ j))).2.2.1 u t
    have hSs j : IsIntegral 0 (Ss j) := ⟨(hs (χ j)).1,(hs (χ j)).2.1⟩
    apply normalApprox_of_weak_limit hSs R 0
    · intro j
      exact ((hs (χ j)).2.2.trans (hD j)).trans (le_max_left _ _)
    · intro j
      simp only [boundary,mass_zero,NNReal.coe_zero,le_refl]
    · intro b π
      exact (ht b π).comp hχ.tendsto_atTop
  | succ k =>
    choose G H hG hH hG0 hH0 hGI hHI hS using fun j =>
      superlevelSlice_normal_coarea_bound (hTs (ψ j)) hX hK
    have hsum j : Integrable (fun t => G j t + H j t) volume := (hG j).add (hH j)
    have hsum0 j : 0 ≤ᵐ[volume] (fun t => G j t + H j t) :=
      Eventually.of_forall fun t => add_nonneg (hG0 j t) (hH0 j t)
    have hsumI j : (∫ t : ℝ, G j t + H j t) ≤ (K : ℝ)*(C+C) := by
      rw [integral_add (hG j) (hH j),mul_add]
      exact add_le_add ((hGI j).trans (mul_le_mul_of_nonneg_left (hM (ψ j)) K.coe_nonneg))
        ((hHI j).trans (mul_le_mul_of_nonneg_left (hN (ψ j)) K.coe_nonneg))
    have hfat := ae_exists_bounded_subsequence_of_integral_bound volume hsum hsum0
      ((K : ℝ)*(C+C)) hsumI
    filter_upwards [hweak,ae_all_iff.mpr hS,hfat] with t ht hs hf
    obtain ⟨D,χ,hχ,hD⟩ := hf
    let R : ℝ≥0 := ⟨max D 0,le_max_right _ _⟩
    let Ss : ℕ → Functional X (k+1) := fun j =>
      superlevelSlice (hTs (ψ (χ j))).1 (hTs (ψ (χ j))).2.2.1 u t
    have hSs j : IsIntegral (k+1) (Ss j) := (hs (χ j)).1
    apply normalApprox_of_weak_limit hSs R R
    · intro j
      exact (((hs (χ j)).2.1.trans (le_add_of_nonneg_right (hH0 (χ j) t))).trans
        (hD j)).trans (le_max_left _ _)
    · intro j
      exact (((hs (χ j)).2.2.trans (le_add_of_nonneg_left (hG0 (χ j) t))).trans
        (hD j)).trans (le_max_left _ _)
    · intro b π
      exact (ht b π).comp hχ.tendsto_atTop

lemma ae_normalSlice_eq {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    normalSlice h u =ᵐ[volume] superlevelSlice h.normal.1 h.normal.2 u := by
  filter_upwards [h.ae_slice hX h.normal.1 h.normal.2 hK] with t ht
  classical
  exact ite_eq_left ht

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_Limits
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma restrictCurrent_mass_le {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E) :
    mass (restrictCurrent hT E) ≤ mass T := by
  rw [restriction_mass hT hE, ← currentMassMeasure_total hT]
  exact measureReal_mono (subset_univ E)

lemma restrictCurrent_empty {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) :
    restrictCurrent hT ∅ = 0 := by
  apply (restrictCurrent_isMetricCurrent hT MeasurableSet.empty).eq_zero_of_mass_eq_zero
  rw [restriction_mass hT MeasurableSet.empty]
  simp

lemma restrictCurrent_univ {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) :
    restrictCurrent hT univ = T := by
  funext b π
  by_cases h : Admissible b π
  · rw [restrictCurrent_apply hT univ h, Set.indicator_univ]
    exact borelAction_eq _ hT (currentMassMeasure_controls hT) h
  · simp [restrictCurrent, h, hT.offDomain b π h]

lemma superlevelSlice_eq_zero_outside {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} {R : ℝ} (hR : ∀ x, |u x| ≤ R) {t : ℝ}
    (ht : t ∉ Icc (-R) R) : superlevelSlice hT hB u t = 0 := by
  have ht' : t < -R ∨ R < t := by simpa only [mem_Icc, not_and_or, not_le] using ht
  unfold superlevelSlice
  rcases ht' with ht | ht
  · have he : {x | t < u x} = univ := by
      ext x
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact ht.trans_le (abs_le.mp (hR x)).1
    rw [he, restrictCurrent_univ, restrictCurrent_univ, sub_self]
  · have he : {x | t < u x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact ((abs_le.mp (hR x)).2).trans ht.le
    rw [he, restrictCurrent_empty, restrictCurrent_empty]
    ext b π
    simp [boundarySucc]

lemma superlevelSlice_bound_uniform {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (t : ℝ)
    {b : X → ℝ} {Kb B : ℝ≥0} (hb : LipschitzWith Kb b) (hBnd : ∀ x, |b x| ≤ B)
    {π : Fin k → X → ℝ} (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |superlevelSlice hT hB u t b π| ≤
       ((∏ i, (K i : ℝ)) * B) * mass (boundarySucc T) +
       ((Kb : ℝ) * ∏ i, (K i : ℝ)) * mass T := by
  let E := {x | t < u x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hu.measurable
  have hbl : BoundedLip b := ⟨⟨Kb, hb⟩, B, hBnd⟩
  have hadm : Admissible b π := ⟨hbl, fun i => ⟨K i, hK i⟩⟩
  have hp : ∀ i, LipschitzWith ((Matrix.vecCons Kb K) i) ((Matrix.vecCons b π) i) :=
    fun i => Fin.cases hb (fun j => hK j) i
  change |restrictCurrent hB E b π - boundarySucc (restrictCurrent hT E) b π| ≤ _
  apply (abs_sub _ _).trans
  apply add_le_add
  · exact ((restrictCurrent_isMetricCurrent hB hE).mass_bound_uniform hbl K hK hBnd).trans
      (mul_le_mul_of_nonneg_left (restrictCurrent_mass_le hB hE) (by positivity))
  · rw [boundarySucc, ite_eq_left hadm]
    have h := (restrictCurrent_isMetricCurrent hT hE).mass_bound_uniform (BoundedLip.const 1)
      (Matrix.vecCons Kb K) hp (M := 1) (fun _ => by simp)
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (restrictCurrent_mass_le hT hE) (by positivity))

lemma superlevelSlice_integral [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    Integrable (fun t : ℝ => superlevelSlice hT.1 hT.2.2.1 u t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, superlevelSlice hT.1 hT.2.2.1 u t b π := by
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT.1 hT.2.1 hX hK
  have heq := ae_superlevelSlice_eq_coarea hT.1 hT.2.1 hT.2.2.1
    (boundedLip_of_lipschitz hK) (hS.mono fun t ht => ht.1) hact hweight
  have htest : (fun t : ℝ => S t b π) =ᵐ[volume]
      (fun t => superlevelSlice hT.1 hT.2.2.1 u t b π) :=
    heq.mono fun t ht => (congrFun (congrFun ht b) π).symm
  exact ⟨(hact b π h).1.congr htest, (hact b π h).2.trans (integral_congr_ae htest)⟩

theorem superlevelSlice_integral_of_bounded_weak_limit [Nonempty X]
    {k : ℕ} {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j))
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hX : IsCAT0 X) {u : X → ℝ} {Ku : ℝ≥0} (hu : LipschitzWith Ku u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    Integrable (fun t : ℝ => superlevelSlice hT hB u t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, superlevelSlice hT hB u t b π := by
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) M N hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) hT
    (fun j => (hTs (ψ j)).2.2.1) hB μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) (boundedLip_of_lipschitz hu)
  let F (j : ℕ) (t : ℝ) := superlevelSlice (hTs (ψ j)).1 (hTs (ψ j)).2.2.1 u t b π
  let f (t : ℝ) := superlevelSlice hT hB u t b π
  have hact j := superlevelSlice_integral (hTs (ψ j)) hX hu hab
  have hFi (j : ℕ) : Integrable (F j) := (hact j).1
  have hconv : ∀ᵐ t : ℝ, Tendsto (fun j => F j t) atTop (𝓝 (f t)) :=
    hweak.mono fun t ht => ht b π
  obtain ⟨Kb,hKb⟩ := hab.1.1
  obtain ⟨B₀,hB₀⟩ := hab.1.2
  let B : ℝ≥0 := ⟨max B₀ 0, le_max_right _ _⟩
  have hB' (x : X) : |b x| ≤ B := (hB₀ x).trans (le_max_left _ _)
  choose K hK using hab.2
  obtain ⟨R,hR⟩ := (boundedLip_of_lipschitz hu).2
  let C : ℝ := ((∏ i, (K i : ℝ)) * B) * N +
    ((Kb : ℝ) * ∏ i, (K i : ℝ)) * M
  let bound : ℝ → ℝ := (Icc (-R) R).indicator (fun _ => C)
  have hboundi : Integrable bound :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)
  have hbound (j : ℕ) (t : ℝ) : ‖F j t‖ ≤ bound t := by
    by_cases ht : t ∈ Icc (-R) R
    · simp only [bound, indicator_of_mem ht, Real.norm_eq_abs]
      exact (superlevelSlice_bound_uniform (hTs (ψ j)).1 (hTs (ψ j)).2.2.1
        hu.continuous t hKb hB' K hK).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hN (ψ j)) (by positivity))
          (mul_le_mul_of_nonneg_left (hM (ψ j)) (by positivity)))
    · have hz := superlevelSlice_eq_zero_outside (hTs (ψ j)).1 (hTs (ψ j)).2.2.1 hR ht
      have he : F j t = 0 := congrFun (congrFun hz b) π
      simp [he, bound, ht]
  have hfi : Integrable f := hboundi.mono'
    (aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hFi j).aestronglyMeasurable) hconv)
    (hconv.mono fun t ht => le_of_tendsto' ht.norm (fun j => hbound j t))
  have hlimI := tendsto_integral_of_dominated_convergence bound
    (fun j => (hFi j).aestronglyMeasurable) hboundi
    (fun j => Eventually.of_forall (hbound j)) hconv
  have heqI : (fun j => ∫ t : ℝ, F j t) = (fun j => Ts (ψ j) b (Matrix.vecCons u π)) :=
    funext fun j => (hact j).2.symm
  rw [heqI] at hlimI
  exact ⟨hfi, tendsto_nhds_unique ((hlim b (Matrix.vecCons u π)).comp hψ.tendsto_atTop) hlimI⟩

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_FullSlices
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [Nonempty X] in
lemma superlevelSlice_zero [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (hz : T = 0) {u : X → ℝ} (hu : Continuous u) (t : ℝ) :
    superlevelSlice hT hB u t = 0 := by
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.measurable
  have hBz : boundarySucc T = 0 := by rw [hz]; exact boundarySucc_zero k
  unfold superlevelSlice
  rw [restrictCurrent_zero_of_eq_zero hT hz hE, restrictCurrent_zero_of_eq_zero hB hBz hE]
  change (0 : Functional X k) - boundarySucc (fun _ _ => 0) = 0
  rw [boundarySucc_zero]
  ext b π
  simp

lemma normalSlice_zero {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hz : T = 0) {u : X → ℝ} (hu : Continuous u) (t : ℝ) :
    normalSlice h u t = 0 := by
  classical
  unfold normalSlice
  split_ifs
  · exact superlevelSlice_zero h.normal.1 h.normal.2 hz hu t
  · rfl

lemma normalSlice_eq_zero_outside {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) {u : X → ℝ} {R : ℝ} (hR : ∀ x, |u x| ≤ R) {t : ℝ}
    (ht : t ∉ Icc (-R) R) : normalSlice h u t = 0 := by
  classical
  unfold normalSlice
  split_ifs
  · exact superlevelSlice_eq_zero_outside h.normal.1 h.normal.2 hR ht
  · rfl

lemma superlevelSlice_total_coarea_bound {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∫ t, G t) ≤ (K:ℝ) * (mass T + mass (boundarySucc T)) ∧
      ∀ᵐ t : ℝ, IsIntegral k (superlevelSlice hT.1 hT.2.2.1 u t) ∧
        mass (superlevelSlice hT.1 hT.2.2.1 u t) ≤ G t ∧
        mass (boundary (superlevelSlice hT.1 hT.2.2.1 u t)) ≤ G t := by
  cases k with
  | zero =>
    obtain ⟨G,hG,hG0,hGI,hS⟩ := superlevelSlice_coarea_bound hT hX hK
    refine ⟨G,hG,hG0,hGI.trans ?_,?_⟩
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mass_nonneg _)) K.coe_nonneg
    · filter_upwards [hS] with t ht
      exact ⟨⟨ht.1,ht.2.1⟩,ht.2.2,by simpa only [boundary,mass_zero] using hG0 t⟩
  | succ k =>
    obtain ⟨G,H,hG,hH,hG0,hH0,hGI,hHI,hS⟩ := superlevelSlice_normal_coarea_bound hT hX hK
    refine ⟨fun t => G t + H t,hG.add hH,fun t => add_nonneg (hG0 t) (hH0 t),?_,?_⟩
    · rw [integral_add hG hH,mul_add]
      exact add_le_add hGI hHI
    · filter_upwards [hS] with t ht
      exact ⟨ht.1,ht.2.1.trans (le_add_of_nonneg_right (hH0 t)),
        ht.2.2.trans (le_add_of_nonneg_left (hG0 t))⟩

lemma normalSlice_cost_upper {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      (∫ t, g t) ≤ 2 * K * h.cost ∧
      ∀ᵐ t : ℝ, ((normalSlice_approx h u t).cost : ℝ) ≤ g t + 2 := by
  classical
  obtain ⟨Ts,hTs,hM,hN,hlim⟩ := h.cost_spec
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) h.cost h.cost hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) h.normal.1
    (fun j => (hTs (ψ j)).2.2.1) h.normal.2 μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) (boundedLip_of_lipschitz hK)
  choose G hG hG0 hGI hS using fun j => superlevelSlice_total_coarea_bound (hTs (ψ j)) hX hK
  have hGI' j : (∫ t, G j t) ≤ 2 * (K:ℝ) * h.cost := by
    calc (∫ t, G j t) ≤ K * (mass (Ts (ψ j)) + mass (boundarySucc (Ts (ψ j)))) := hGI j
      _ ≤ K * ((h.cost:ℝ) + h.cost) := mul_le_mul_of_nonneg_left (add_le_add (hM (ψ j)) (hN (ψ j))) K.coe_nonneg
      _ = _ := by ring
  obtain ⟨g,hg,hg0,hgI,hfat⟩ := exists_integrable_subsequence_bound volume hG
    (fun j => Eventually.of_forall (hG0 j)) (2 * (K:ℝ) * h.cost) hGI'
  refine ⟨g,hg,hg0,?_,?_⟩
  · simpa only [max_eq_left (show 0 ≤ 2 * (K:ℝ) * h.cost by positivity)] using hgI
  · filter_upwards [hweak,ae_all_iff.mpr hS,hfat,ae_normalSlice_eq h hX hK] with t ht hs hf he
    obtain ⟨χ,hχ,hχG⟩ := hf
    have hA : NormalApproxAt k (Nat.ceil (g t + 1)) (normalSlice h u t) := by
      refine ⟨fun j => superlevelSlice (hTs (ψ (χ j))).1 (hTs (ψ (χ j))).2.2.1 u t,
        fun j => (hs (χ j)).1,?_,?_,?_⟩
      · intro j
        exact ((hs (χ j)).2.1.trans (hχG j).le).trans (Nat.le_ceil _)
      · intro j
        exact ((hs (χ j)).2.2.trans (hχG j).le).trans (Nat.le_ceil _)
      · intro b π
        rw [he]
        exact (ht b π).comp hχ.tendsto_atTop
    have hc := (normalSlice_approx h u t).cost_le hA
    calc ((normalSlice_approx h u t).cost : ℝ) ≤ Nat.ceil (g t + 1) := by exact_mod_cast hc
      _ ≤ g t + 2 := by have hh := Nat.ceil_lt_add_one (show 0 ≤ g t + 1 by linarith [hg0 t]); linarith

theorem normalSlice_cost_integrable {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {R : ℝ} (hR : ∀ x, |u x| ≤ R) :
    Integrable (fun t : ℝ => ((normalSlice_approx h u t).cost : ℝ)) ∧
      (∫ t : ℝ, ((normalSlice_approx h u t).cost : ℝ)) ≤
        (2 * K + 2 * volume.real (Icc (-R) R)) * h.cost := by
  classical
  let f : ℝ → ℝ := fun t => (normalSlice_approx h u t).cost
  have hfm : Measurable f := (show Measurable (fun n : ℕ => (n:ℝ)) from measurable_from_nat).comp
    (measurable_normalSlice_cost h (boundedLip_of_lipschitz hK))
  have hf0 t : 0 ≤ f t := Nat.cast_nonneg _
  by_cases hz : h.cost = 0
  · have hfz : f = 0 := by
      funext t
      have he := normalSlice_zero h (h.eq_zero_of_cost_zero hz) hK.continuous t
      have hc := (normalSlice_approx h u t).cost_congr (normalApprox_zero k) he
      rw [(normalApprox_zero k).cost_zero] at hc
      change ((normalSlice_approx h u t).cost : ℝ) = 0
      simp only [hc,Nat.cast_zero]
    change Integrable f ∧ (∫ t, f t) ≤ _
    rw [hfz,hz]
    simp
  have hC : (1:ℝ) ≤ h.cost := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  obtain ⟨g,hg,hg0,hgI,hbound⟩ := normalSlice_cost_upper h hX hK
  let e : ℝ → ℝ := (Icc (-R) R).indicator (fun _ => 2 * (h.cost:ℝ))
  have he : Integrable e := by
    apply (integrable_indicator_iff isClosed_Icc.measurableSet).mpr
    exact integrableOn_const measure_Icc_lt_top.ne
  have hG : Integrable (g + e) := hg.add he
  have hle : ∀ᵐ t : ℝ, f t ≤ (g + e) t := by
    filter_upwards [hbound] with t ht
    by_cases htR : t ∈ Icc (-R) R
    · simp only [Pi.add_apply,e,indicator_of_mem htR]
      exact ht.trans (by linarith)
    · have hz' := normalSlice_eq_zero_outside h hR htR
      have hc := (normalSlice_approx h u t).cost_congr (normalApprox_zero k) hz'
      rw [(normalApprox_zero k).cost_zero] at hc
      simp only [f,hc,Nat.cast_zero,Pi.add_apply,e,indicator_of_notMem htR,add_zero]
      exact hg0 t
  have hf : Integrable f := hG.mono' hfm.aestronglyMeasurable (hle.mono fun t ht => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 t)] using ht)
  refine ⟨hf,(integral_mono_ae hf hG hle).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add hg he]
  have heI : (∫ t, e t) = 2 * (h.cost:ℝ) * volume.real (Icc (-R) R) := by
    dsimp only [e]
    rw [integral_indicator isClosed_Icc.measurableSet]
    simp only [setIntegral_const,smul_eq_mul]
    ring
  rw [heI]
  nlinarith [hgI]

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma fullSlice_integral {k : ℕ} {T : Functional X k} (h : NormalApprox k T)
    (π : Fin k → X → ℝ) (z : Euc k) : IsIntegral 0 (fullSlice h π z) :=
  (fullSlice_approx h π z).integral_zero

theorem fullSlice_cost_integrable {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hK : ∀ i, LipschitzWith K (π i))
    {R : ℝ} (hR : ∀ i x, |π i x| ≤ R) :
    Integrable (fun z : Euc k => ((fullSlice_approx h π z).cost : ℝ)) ∧
      (∫ z : Euc k, ((fullSlice_approx h π z).cost : ℝ)) ≤
        (2 * K + 2 * volume.real (Icc (-R) R))^k * h.cost := by
  induction k with
  | zero =>
    change Integrable (fun _ : Euc 0 => (h.cost:ℝ)) ∧ _
    rw [volume_euclideanSpace_eq_dirac]
    simp only [integral_dirac,pow_zero,one_mul]
    exact ⟨integrable_const _,le_rfl⟩
  | succ k ih =>
    let B : ℝ := 2 * K + 2 * volume.real (Icc (-R) R)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    let f : Euc (k+1) → ℝ := fun z => (fullSlice_approx h π z).cost
    let F : ℝ × Euc k → ℝ := fun p => (fullSlice_approx (normalSlice_approx h (π 0) p.1) (Fin.tail π) p.2).cost
    let c : ℝ → ℝ := fun t => (normalSlice_approx h (π 0) t).cost
    have he : F = f ∘ (Prism.split k).symm := by
      funext p
      rfl
    have hfm : Measurable f := measurable_from_nat.comp
      (measurable_fullSlice_cost h π (fun i => boundedLip_of_lipschitz (hK i)))
    have hFm : Measurable F := by rw [he]; exact hfm.comp (Prism.split k).symm.continuous.measurable
    have hF0 p : 0 ≤ F p := Nat.cast_nonneg _
    have ht (t : ℝ) : Integrable (fun z => F (t,z)) ∧
        (∫ z, F (t,z)) ≤ B^k * c t :=
      ih (normalSlice_approx h (π 0) t) (Fin.tail π) (fun i => hK i.succ) (fun i x => hR i.succ x)
    have hc : Integrable c ∧ (∫ t, c t) ≤ B * h.cost := normalSlice_cost_integrable h hX (hK 0) (hR 0)
    have hinnerM : AEStronglyMeasurable (fun t => ∫ z, F (t,z)) volume :=
      hFm.aestronglyMeasurable.integral_prod_right'
    have hinner0 t : 0 ≤ ∫ z, F (t,z) := integral_nonneg (fun z => hF0 (t,z))
    have hinner : Integrable (fun t => ∫ z, F (t,z)) :=
      (hc.1.const_mul (B^k)).mono' hinnerM (Eventually.of_forall fun t => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hinner0 t)] using (ht t).2)
    have hFi : Integrable F (volume.prod volume) := by
      apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
      refine ⟨Eventually.of_forall fun t => (ht t).1,?_⟩
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hF0 _)] using hinner
    have hfi : Integrable f := by
      apply ((Prism.split_symm_measurePreserving k).integrable_comp_emb
        (Prism.split k).symm.toHomeomorph.measurableEmbedding).mp
      simpa only [←he,Measure.volume_eq_prod] using hFi
    refine ⟨hfi,?_⟩
    change (∫ z, f z) ≤ B^(k+1) * h.cost
    rw [Prism.integral_split]
    change (∫ p, (f ∘ (Prism.split k).symm) p ∂volume.prod volume) ≤ _
    rw [←he,integral_prod _ hFi]
    calc (∫ t, ∫ z, F (t,z)) ≤ ∫ t, B^k * c t :=
        integral_mono hinner (hc.1.const_mul _) (fun t => (ht t).2)
      _ = B^k * ∫ t, c t := integral_const_mul _ _
      _ ≤ B^k * (B * h.cost) := mul_le_mul_of_nonneg_left hc.2 (pow_nonneg hB _)
      _ = _ := by rw [pow_succ]; ring

lemma fullSlice_eval_integrable {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    Integrable (fun z : Euc k => fullSlice h π z b σ) := by
  classical
  choose K hK using fun i => (hπ i).1
  let K' : ℝ≥0 := Finset.univ.sup K
  have hK' i : LipschitzWith K' (π i) := (hK i).weaken (Finset.le_sup (Finset.mem_univ i))
  choose R hR using fun i => (hπ i).2
  let R' : ℝ := max 0 (∑ i, |R i|)
  have hR' i x : |π i x| ≤ R' := by
    apply (hR i x).trans
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i)).trans (le_max_right _ _))
  have hcost := (fullSlice_cost_integrable h hX π hK' hR').1
  obtain ⟨B₀,hB₀⟩ := hb.2
  let B : ℝ≥0 := ⟨max B₀ 0,le_max_right _ _⟩
  have hB x : |b x| ≤ B := (hB₀ x).trans (le_max_left _ _)
  apply (hcost.const_mul (B:ℝ)).mono' (measurable_fullSlice h π hπ b σ).aestronglyMeasurable
  filter_upwards [] with z
  have hd := (fullSlice_integral h π z).1.mass_bound_uniform (π := σ) hb (fun _ => (1:ℝ≥0))
    (fun i => Fin.elim0 i) hB
  simp only [Fin.prod_univ_zero,one_mul] at hd
  simpa only [Real.norm_eq_abs] using hd.trans
    (mul_le_mul_of_nonneg_left (fullSlice_approx h π z).mass_le_cost B.coe_nonneg)

lemma normalSlice_integral {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    Integrable (fun t : ℝ => normalSlice h u t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, normalSlice h u t b π := by
  have hcopy := h
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hcopy
  have ha := superlevelSlice_integral_of_bounded_weak_limit hTs h.normal.1 h.normal.2
    (C:ℝ≥0) (C:ℝ≥0) hM hN hlim hX hK hab
  have he : (fun t : ℝ => superlevelSlice h.normal.1 h.normal.2 u t b π) =ᵐ[volume]
      (fun t => normalSlice h u t b π) := by
    filter_upwards [ae_normalSlice_eq h hX hK] with t ht
    rw [ht]
  exact ⟨ha.1.congr he,ha.2.trans (integral_congr_ae he)⟩

theorem fullSlice_action_integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {b : X → ℝ} (hb : BoundedLip b) :
    T b π = ∫ z : Euc k, fullSlice h π z b (fun j => Fin.elim0 j) := by
  induction k with
  | zero =>
    have hp : π = fun j => Fin.elim0 j := by funext j; exact Fin.elim0 j
    simp only [fullSlice,volume_euclideanSpace_eq_dirac,integral_dirac,hp]
  | succ k ih =>
    have he : π = Matrix.vecCons (π 0) (Fin.tail π) := by ext i x; exact Fin.cases rfl (fun _ => rfl) i
    have ht : T b π = ∫ t : ℝ, normalSlice h (π 0) t b (Fin.tail π) := by
      conv_lhs => rw [he]
      exact (normalSlice_integral h hX (hπ 0).1.choose_spec ⟨hb,fun i => (hπ i.succ).1⟩).2
    rw [ht,Prism.integral_split]
    have hFi : Integrable (fun p : ℝ × Euc k =>
        fullSlice h π ((Prism.split k).symm p) b (fun j => Fin.elim0 j)) :=
      ((Prism.split_symm_measurePreserving k).integrable_comp_emb
        (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr
          (fullSlice_eval_integrable h hX π hπ hb _)
    rw [Measure.volume_eq_prod,integral_prod _ (by simpa only [Measure.volume_eq_prod] using hFi)]
    apply integral_congr_ae
    filter_upwards [] with t
    exact ih (normalSlice_approx h (π 0) t) (Fin.tail π) (fun i => hπ i.succ)

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_JointPoincare
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

noncomputable def parameterEquiv (k : ℕ) : (Fin k → ℝ) ≃L[ℝ] Euc k :=
  (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.toContinuousLinearEquiv

noncomputable def fullSliceControl {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (π : Fin (k+1) → X → ℝ) (K : ℝ≥0) : Measure (Euc (k+1)) :=
  (K^k) • Measure.map (coordinateMap π)
    (currentMassMeasure h.normal.1 + currentMassMeasure h.normal.2)

instance fullSliceControl_finite {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (π : Fin (k+1) → X → ℝ) (K : ℝ≥0) :
    IsFiniteMeasure (fullSliceControl h π K) := by unfold fullSliceControl; infer_instance

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Chord_NonnegativeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChordMeasure
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (ρ : α → ℝ)
noncomputable def probability : Measure α := μ.withDensity (fun x => ENNReal.ofReal (ρ x / total μ ρ))
end CAT0Fillings.ChordMeasure
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Pushforward
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u
namespace CurrentOperations
attribute [local instance] Classical.propDecidable
variable {X : Type u} {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

noncomputable def pushCurrent {k : ℕ} (f : X → Y) (T : Functional X k) : Functional Y k :=
  fun b π => if Admissible b π then T (b ∘ f) (fun i => π i ∘ f) else 0

end CurrentOperations
end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_AffineCalculus
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
noncomputable def boundedLipSubmodule : Submodule ℝ (X → ℝ) where
  carrier := {b | BoundedLip b}
  zero_mem' := BoundedLip.const 0
  add_mem' := fun hb hc => hb.add hc
  smul_mem' := fun a _ hb => hb.const_mul a

local notation "BL" => boundedLipSubmodule (X := X)

omit [MeasurableSpace X] [BorelSpace X] in
lemma bl_update_tail_zero {k : ℕ} (v : Fin (k+1) → BL) (f : BL) :
    (fun j : Fin k => ((Function.update v 0 f) j.succ : X → ℝ)) =
      fun j => (v j.succ : X → ℝ) := by
  funext j
  simp

omit [MeasurableSpace X] [BorelSpace X] in
lemma bl_update_tail_succ {k : ℕ} (v : Fin (k+1) → BL) (i : Fin k) (f : BL) :
    (fun j : Fin k => ((Function.update v i.succ f) j.succ : X → ℝ)) =
      Function.update (fun j => (v j.succ : X → ℝ)) i (f : X → ℝ) := by
  funext j
  by_cases h : j=i <;> simp [h]

noncomputable def IsMetricCurrent.fullMultilinear {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) : MultilinearMap ℝ (fun _ : Fin (k+1) => BL) ℝ :=
  MultilinearMap.mk' (fun v => T (v 0) (fun j => v j.succ)) (by
    intro v i f g
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Function.update_self,bl_update_tail_zero,Submodule.coe_add,Pi.add_def,
        one_mul] using hT.linearFirst f g (fun j => v j.succ) 1 1 f.property g.property
          (fun j => (v j.succ).property.1)
    · have h := hT.linearCoord (v 0 : X → ℝ)
        (Function.update (fun j => (v j.succ : X → ℝ)) j (f : X → ℝ)) j
        (g : X → ℝ) 1 1
        ⟨(v 0).property,fun l => by
          by_cases hl : l=j
          · simpa [hl] using f.property.1
          · simpa [hl] using (v l.succ).property.1⟩ g.property.1
      simpa only [Function.update_of_ne (Fin.succ_ne_zero j).symm,bl_update_tail_succ,
        Function.update_self,Submodule.coe_add,Pi.add_def,one_mul,Function.update_idem] using h)
    (by
      intro v i a f
      refine Fin.cases ?_ (fun j => ?_) i
      · have h := hT.linearFirst f f (fun j => v j.succ) a 0 f.property f.property
          (fun j => (v j.succ).property.1)
        simpa only [Function.update_self,bl_update_tail_zero,Submodule.coe_smul,Pi.smul_def,
          smul_eq_mul,zero_mul,add_zero] using h
      · have h := hT.linearCoord (v 0 : X → ℝ)
          (Function.update (fun j => (v j.succ : X → ℝ)) j (f : X → ℝ)) j
          (f : X → ℝ) a 0
          ⟨(v 0).property,fun l => by
            by_cases hl : l=j
            · simpa [hl] using f.property.1
            · simpa [hl] using (v l.succ).property.1⟩ f.property.1
        simpa only [Function.update_of_ne (Fin.succ_ne_zero j).symm,bl_update_tail_succ,
          Function.update_self,Submodule.coe_smul,Pi.smul_def,smul_eq_mul,
          zero_mul,add_zero,Function.update_idem] using h)

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_Chart
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
noncomputable def prismDomain : Set (Euc (k+1)) :=
  Prism.split k ⁻¹' (Icc (0:ℝ) 1 ×ˢ C.domain)

lemma measurableSet_prismDomain : MeasurableSet C.prismDomain :=
  (measurableSet_Icc.prod C.borel).preimage (Prism.split k).continuous.measurable

lemma bounded_prismDomain : Bornology.IsBounded C.prismDomain := by
  have h := (Prism.split k).symm.lipschitz.isBounded_image
    ((isCompact_Icc (a := (0:ℝ)) (b := 1)).isBounded.prod C.bounded)
  change Bornology.IsBounded ((Prism.split k).toEquiv.symm '' (Icc (0:ℝ) 1 ×ˢ C.domain)) at h
  rw [Equiv.image_symm_eq_preimage] at h
  exact h

noncomputable def prismParam (z : C.prismDomain) : ℝ × X :=
  ((Prism.split k z).1, C.param ⟨(Prism.split k z).2,z.2.2⟩)

lemma prismParam_bilipschitz : ∃ L U : ℝ≥0,
    LipschitzWith L C.prismParam ∧ AntilipschitzWith U C.prismParam := by
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  have hs := (Prism.split k).lipschitz.comp (LipschitzWith.subtype_val C.prismDomain)
  have ht := LipschitzWith.prod_fst.comp hs
  have hz := (LipschitzWith.prod_snd.comp hs).subtype_mk (fun z : C.prismDomain => z.2.2)
  refine ⟨_, ‖(Prism.split k).symm.toContinuousLinearMap‖₊ * max 1 U,
    ht.prodMk (hL.comp hz), ?_⟩
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have hu := hU.le_mul_dist
    ⟨(Prism.split k z).2,z.2.2⟩ ⟨(Prism.split k w).2,w.2.2⟩
  have hs' := (Prism.split k).antilipschitz.le_mul_dist z.val w.val
  change dist z.val w.val ≤ _
  calc
    _ ≤ _ := hs'
    _ ≤ ‖(Prism.split k).symm.toContinuousLinearMap‖₊ *
        ((max 1 U : ℝ≥0) * dist (C.prismParam z) (C.prismParam w)) := by
      apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
      rw [Prod.dist_eq]
      apply max_le
      · calc
          _ ≤ dist (C.prismParam z) (C.prismParam w) := le_max_left _ _
          _ ≤ _ := le_mul_of_one_le_left dist_nonneg (by exact_mod_cast le_max_left 1 U)
      · calc
          _ ≤ (U:ℝ) * dist (C.prismParam z).2 (C.prismParam w).2 := hu
          _ ≤ (U:ℝ) * dist (C.prismParam z) (C.prismParam w) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) U.coe_nonneg
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right 1 U) dist_nonneg
    _ = _ := by simp only [NNReal.coe_mul,mul_assoc]

lemma integrable_prismMultiplicity :
    Integrable (fun z => (C.multiplicity ((Prism.split k z).2) : ℝ))
      (volume.restrict C.prismDomain) := by
  have hi := C.integrable.comp_snd (volume.restrict (Icc (0:ℝ) 1))
  rw [Measure.prod_restrict] at hi
  exact ((Prism.split_measurePreserving k).restrict_preimage
    (measurableSet_Icc.prod C.borel)).integrable_comp_emb
      (Prism.split k).toHomeomorph.measurableEmbedding |>.mpr hi

noncomputable def prism : IntegerChart (ℝ × X) (k+1) where
  domain := C.prismDomain
  borel := C.measurableSet_prismDomain
  bounded := C.bounded_prismDomain
  param := C.prismParam
  bilipschitz := C.prismParam_bilipschitz
  multiplicity z := C.multiplicity ((Prism.split k z).2)
  integrable := C.integrable_prismMultiplicity

end CAT0Fillings.IntegerChart

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_Family
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
noncomputable def prismFamily (C : ℕ → IntegerChart X k) : Functional (ℝ × X) (k+1) :=
  fun b π => ∑' i, (C i).prism.action b π

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_TimeAction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory Measure Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] {k : ℕ}
noncomputable def timeAction {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]
    (hT : IsMetricCurrent T) (v : Fin (k+1) → ℝ × X → ℝ) (t : ℝ) : ℝ :=
  ∑ i, (-1:ℝ)^i.val * BorelCoefficients.borelAction μ hT
    (fun x => deriv (fun s => v i (s,x)) t) (fun j x => v (i.succAbove j) (t,x))

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_ClosedCylinder
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory CurrentOperations
open scoped NNReal ENNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma prism_clamp_bilipschitz : ∃ J : ℝ≥0,
    AntilipschitzWith J (cylinderClamp ∘ C.prism.param) := by
  obtain ⟨L,J,hL,hJ⟩ := C.prism.bilipschitz
  refine ⟨J,?_⟩
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have hx : cylinderEmbed (cylinderClamp (C.prism.param x)) = C.prism.param x :=
    cylinderEmbed_clamp _ x.2.1
  have hy : cylinderEmbed (cylinderClamp (C.prism.param y)) = C.prism.param y :=
    cylinderEmbed_clamp _ y.2.1
  have hd := cylinderEmbed_isometry.dist_eq (cylinderClamp (C.prism.param x))
    (cylinderClamp (C.prism.param y))
  simpa only [Function.comp_apply,←hd,hx,hy] using hJ.le_mul_dist x y

noncomputable def closedPrism : IntegerChart (ClosedCylinder X) (k+1) :=
  C.prism.postcompose cylinderClamp_lipschitz C.prism_clamp_bilipschitz.choose_spec

end IntegerChart

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_ClosedFamily
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory CurrentOperations
open scoped NNReal ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
noncomputable def closedPrismFamily (C : ℕ → IntegerChart X k) :
    Functional (ClosedCylinder X) (k+1) := pushCurrent cylinderClamp (prismFamily C)

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_ChartMass
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter Metric Matrix CurrentOperations
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] {k : ℕ} (C : IntegerChart X k)
noncomputable def radialJacobian (P : Euc k → Matrix (Fin k) (Fin k) ℝ)
    (o : X) (g : X → ℝ) (t : ℝ) (z : Euc k) : ℝ :=
  Real.sqrt (metricSpatialRadialForm (P z) (C.scalar g z)
    (C.scalar (dist o) z) t
    (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z))
    (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z))).det

end IntegerChart
end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_RadialChart
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
namespace Prism
noncomputable def tail (k : ℕ) : Euc (k+1) →L[ℝ] Euc k :=
  (ContinuousLinearMap.snd ℝ ℝ (Euc k)).comp (split k).toContinuousLinearMap
@[simp] lemma tail_apply (k : ℕ) (v : Euc (k+1)) :
    tail k v = WithLp.toLp 2 (fun j => v j.succ) := rfl
@[simp] lemma tail_single_zero (k : ℕ) : tail k (EuclideanSpace.single 0 1) = 0 := by
  ext j; simp
@[simp] lemma tail_single_succ (k : ℕ) (j : Fin k) :
    tail k (EuclideanSpace.single j.succ 1) = EuclideanSpace.single j 1 := by
  ext l; simp

@[simp] lemma zeroSumEquiv_symm_inl (k : ℕ) : (zeroSumEquiv k).symm (Sum.inl ()) = 0 := rfl
@[simp] lemma zeroSumEquiv_symm_inr (k : ℕ) (j : Fin k) :
    (zeroSumEquiv k).symm (Sum.inr j) = j.succ := rfl

noncomputable def radialForm {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ)
    (g r t : ℝ) (α γ : Fin k → ℝ) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  reindex (zeroSumEquiv k).symm (zeroSumEquiv k).symm
    (metricTotalRadialForm G g r t α γ)

end Prism

end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

noncomputable def sweptWeight (p : Euc k → Seminorm ℝ (Euc k))
    (o : X) (g : X → ℝ) (z : Euc k) : ℝ :=
  let G := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let α := differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z)
  (C.scalar (dist o) z)*C.scalar g z*Real.sqrt (1-α ⬝ᵥ G⁻¹.mulVec α)*Real.sqrt G.det

end IntegerChart
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_Current
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

namespace ChartGeometry
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def sweptMass (o : X) (g : X → ℝ) : ℝ :=
  ∑' i, ∫ z, |((q.chart i).multiplicity z : ℝ)| *(q.chart i).sweptWeight (q.field i) o g z
    ∂volume.restrict (q.chart i).domain

end ChartGeometry

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_AtomGraphs
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def UnitRepresentation {m : ℕ} (S : Functional X 0) (a : Fin m → ℤ) (x : Fin m → X) : Prop :=
  ∀ b : X → ℝ, LipschitzWith 1 b → (∀ z, |b z| ≤ 1) →
    S b (fun j => Fin.elim0 j) = ∑ j, (a j : ℝ) * b (x j)

variable {P : Type*} [MetricSpace P]

def atomDomain [SeparableSpace X] [Nonempty X]
    (S : P → Functional X 0) (E : Set P) (c : AtomCode) : Set P :=
  {t | t ∈ E ∧ c.Valid (X := X) ∧ ∃ x : Fin c.size → X,
    (∀ i, dist (x i) (TopologicalSpace.denseSeq X (c.centers i)) ≤ c.radius) ∧
    UnitRepresentation (S t) c.weights x}

noncomputable def selectedAtom [SeparableSpace X] [Nonempty X]
    (S : P → Functional X 0) (E : Set P) (c : AtomCode)
    (t : atomDomain S E c) : Fin c.size → X := Classical.choose t.property.2.2

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_GraphCharts
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] {k : ℕ}

noncomputable def jointGraphChart {D : Set (Euc k)} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ) : IntegerChart X k where
  domain := D
  borel := hD.measurableSet
  bounded := hD.isBounded
  param := γ
  bilipschitz := hγ
  multiplicity := fun _ => a
  integrable := integrableOn_const (C := (a : ℝ)) (hD.measure_lt_top (μ := volume)).ne

noncomputable def jointGraphFunction {D : Set (Euc k)} (γ : D → X) (b : X → ℝ) (z : Euc k) : ℝ :=
  if hz : z ∈ D then b (γ ⟨z,hz⟩) else 0

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_JointKernel
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

def TupleKernel (hT : IsMetricCurrent T) (π : Fin k → X → ℝ) : Prop :=
  ∀ (f : X → ℝ), Integrable f μ → borelAction μ hT f π = 0

end CAT0Fillings.SliceReconstruction
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Reconstruction_Uniqueness
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma fullSlice_cost_integrable_of_boundedLip {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) :
    Integrable (fun z : Euc k => ((fullSlice_approx h π z).cost : ℝ)) := by
  classical
  choose K hK using fun i => (hπ i).1
  let K' : ℝ≥0 := Finset.univ.sup K
  have hK' i : LipschitzWith K' (π i) := (hK i).weaken (Finset.le_sup (Finset.mem_univ i))
  choose R hR using fun i => (hπ i).2
  let R' : ℝ := max 0 (∑ i, |R i|)
  have hR' i x : |π i x| ≤ R' := by
    apply (hR i x).trans
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i)).trans (le_max_right _ _))
  exact (fullSlice_cost_integrable h hX π hK' hR').1

lemma fullSlice_borel_integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {f : X → ℝ} (hf : Measurable f) (B : ℝ≥0) (hfB : ∀ x, |f x| ≤ B) :
    ActionIntegralAgreement volume T π (fullSlice h π) (fun j => Fin.elim0 j) f := by
  apply ActionIntegralAgreement.bounded_measurable (fun i => (hπ i).1)
    (fun j => Fin.elim0 j) (Eventually.of_forall fun z => (fullSlice_approx h π z).metric)
    (fullSlice_cost_integrable_of_boundedLip h hX π hπ)
    (Eventually.of_forall fun z => Nat.cast_nonneg _)
    (Eventually.of_forall fun z => (fullSlice_approx h π z).mass_le_cost) ?_ hf B hfB
  intro b hb
  have he : (fun z => fullSlice h π z b (fun j => Fin.elim0 j)) =
      (fun z => currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)) := by
    funext z
    exact (currentBorelAction_eq_action (fullSlice_approx h π z).metric ⟨hb,fun j => Fin.elim0 j⟩).symm
  refine ⟨?_,?_⟩
  · rw [←he]
    exact fullSlice_eval_integrable h hX π hπ hb _
  · rw [currentBorelAction_eq_action h.metric ⟨hb,fun i => (hπ i).1⟩,←he]
    exact fullSlice_action_integral h hX π hπ hb

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Fillings_Attainment
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

noncomputable def fillingVolume {k : ℕ} (T : Functional X (k+1)) : ℝ :=
  sInf {r : ℝ | ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧
    boundarySucc S = T ∧ r = mass S}

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Fillings_WeightedCone
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open MassMeasure CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

omit [Nonempty X] in
lemma IsMetricCurrent.sub {T U : Functional X k} (hT : IsMetricCurrent T)
    (hU : IsMetricCurrent U) : IsMetricCurrent (T-U) := by
  simpa only [sub_eq_add_neg] using hT.add hU.neg

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

namespace CAT0Fillings

noncomputable def rawCovector {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (v : Euc n) : Fin n → ℝ :=
  (CFC.sqrt P⁻¹)⁻¹.mulVec (WithLp.ofLp v)

noncomputable def normalizedDet {n : ℕ} (P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (R : Fin n → Fin (n+1) → ℝ) (v : Euc (n+1)) : ℝ :=
  Matrix.det (Matrix.vecCons (rawCovector P v) R) / Real.sqrt P.det

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Pairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators MatrixOrder

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def testWeight (π : Fin k → X → ℝ) (L : ℕ × Euc (k+1) → Euc (k+1))
    (w : ℕ × Euc (k+1)) : ℝ :=
  let a : ℝ := (q.chart w.1).multiplicity w.2
  (a/abs a)*normalizedDet (q.gram w.1 w.2) (fun j => q.covector w.1 (π j) w.2) (L w)

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def pairing (π : Fin k → X → ℝ) (b : X → ℝ)
    (L : Lp (Euc (k+1)) 2 q.atlasMeasure) : ℝ :=
  ∫ w, q.testWeight π L w*b (q.atlasParam w) ∂q.atlasMeasure

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}

noncomputable def projectedL1 (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : Measurable b) (B : ℝ≥0) (hB : ∀ x, |b x| ≤ B) : Lp ℝ 1 (volume : Measure (Euc k)) :=
  (fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb B hB).1.toL1 _

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Slicing Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def isolatedL1 (h : NormalApprox n T) (hX : IsCAT0 X) (i : ℕ)
    (F : Fin n → X → ℝ) {K : ℝ≥0} (hF : ∀ a, LipschitzWith K (F a))
    {u : X → ℝ} (hu : Measurable u) (U : ℝ≥0) (hU : ∀ x, |u x| ≤ U) : Lp ℝ 1 (volume : Measure (Euc n)) :=
  projectedL1 h hX F hF (hu.indicator (q.chart i).measurableSet_image) U (q.indicator_bound i hU)

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Atlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings.ChartGeometry
open JointBV Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def value1 {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Lp ℝ 1 (MassMeasure.currentMassMeasure hT) :=
  ((boundedLip_of_lipschitz hu).memLp 1).toLp u

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Density_InverseCutoff
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def radialNormSq (o : X) (i : ℕ) (z : Euc k) : ℝ :=
  let α := differentialRow (fderivWithin ℝ ((q.chart i).scalar (dist o)) (q.chart i).domain z)
  α ⬝ᵥ (q.gram i z)⁻¹.mulVec α

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Constant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

instance sobolev_separable : SeparableSpace q.Sobolev := by
  let : Fact ((2:ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : Fact (1 ≤ (2:ℝ≥0∞)) := ⟨by norm_num⟩
  let : SecondCountableTopology X := inferInstance
  let : SecondCountableTopology (Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) := inferInstance
  let : SecondCountableTopology (Lp (Euc (k+1)) 2 q.atlasMeasure) := inferInstance
  let : SecondCountableTopology q.GraphAmbient := inferInstanceAs
    (SecondCountableTopology (WithLp 2 ((Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) ×
      (Lp (Euc (k+1)) 2 q.atlasMeasure))))
  let : SecondCountableTopology q.Sobolev := inferInstanceAs
    (SecondCountableTopology (q.closedGraph : Set q.GraphAmbient))
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_SpatialVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
namespace ChartGeometry
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def spatialMass (o : X) (g : X → ℝ) (t : ℝ) : ℝ :=
  ∑' i, ∫ z, |((q.chart i).multiplicity z : ℝ)| *
    (q.chart i).radialJacobian (q.gram i) o g t z ∂volume.restrict (q.chart i).domain

noncomputable def radialVariationChart (o : X) (g : X → ℝ) (i : ℕ) : ℝ :=
  ∫ z, q.density i z * ((k:ℝ)*(q.chart i).scalar g z + (q.chart i).scalar (dist o) z *
    (differentialRow (fderivWithin ℝ ((q.chart i).scalar (dist o)) (q.chart i).domain z) ⬝ᵥ
      (q.gram i z)⁻¹.mulVec
        (differentialRow (fderivWithin ℝ ((q.chart i).scalar g) (q.chart i).domain z))))
  ∂volume.restrict (q.chart i).domain

noncomputable def radialVariation (o : X) (g : X → ℝ) : ℝ := ∑' i, q.radialVariationChart o g i

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_ClosedInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def radialA (o : X) (w : ℕ × Euc (k+1)) : ℝ :=
  (k+1:ℝ)*(1-dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2))
noncomputable def radialB (o : X) (w : ℕ × Euc (k+1)) : Euc (k+1) :=
  dist o (q.atlasParam w) • q.gradient (LipschitzWith.dist_right o) w
lemma memLp_radialA (o : X) : MemLp (q.radialA o) 2 q.atlasMeasure := by
  have hr : AEStronglyMeasurable (fun w => dist o (q.atlasParam w)) q.atlasMeasure :=
    ((LipschitzWith.dist_right o).continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable
  have hd := (Lp.aestronglyMeasurable (q.gradient (LipschitzWith.dist_right o))).norm
  apply MemLp.of_bound (aestronglyMeasurable_const.mul
    (aestronglyMeasurable_const.sub (hr.mul (Real.continuous_sqrt.comp_aestronglyMeasurable (aestronglyMeasurable_const.sub (hd.pow 2))))))
    ((k+1:ℝ)*(1+Metric.diam (univ : Set X)))
  filter_upwards [q.ae_gradient_bound (LipschitzWith.dist_right o)] with w hw
  have hs : Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    nlinarith [sq_nonneg ‖q.gradient (LipschitzWith.dist_right o) w‖]
  have hh := mul_le_mul (radius_bound o (q.atlasParam w)) hs (Real.sqrt_nonneg _)
    (Metric.diam_nonneg (s := (univ : Set X)))
  change ‖(k+1:ℝ)*(1-dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2))‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ k+1 by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (abs_sub (1:ℝ) _).trans
  rw [abs_one,abs_of_nonneg (mul_nonneg dist_nonneg (Real.sqrt_nonneg _))]
  linarith

lemma memLp_radialB (o : X) : MemLp (q.radialB o) 2 q.atlasMeasure := by
  have hr : AEStronglyMeasurable (fun w => dist o (q.atlasParam w)) q.atlasMeasure :=
    ((LipschitzWith.dist_right o).continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable
  apply MemLp.of_bound (hr.smul (Lp.aestronglyMeasurable (q.gradient (LipschitzWith.dist_right o))))
    (Metric.diam (univ : Set X))
  filter_upwards [q.ae_gradient_bound (LipschitzWith.dist_right o)] with w hw
  change ‖dist o (q.atlasParam w) • q.gradient (LipschitzWith.dist_right o) w‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
  exact (mul_le_mul_of_nonneg_left hw dist_nonneg).trans (by simpa using radius_bound o (q.atlasParam w))

noncomputable def radialDefect (o : X) (P : q.Sobolev) : ℝ :=
  inner ℝ ((q.memLp_radialA o).toLp (q.radialA o))
    (Lp.compMeasurePreserving q.atlasParam q.atlas_preserving (q.inclusion P)) +
  inner ℝ ((q.memLp_radialB o).toLp (q.radialB o)) (q.closedGradient P)
end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Euler_OppositePointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def radialPowerIntegrand (o : X) (v : q.Sobolev) (β : ℝ) (w : ℕ × Euc (k+1)) : ℝ :=
  dist o (q.atlasParam w)*((q.inclusion v (q.atlasParam w))^(2+4*β)*
    Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)-
    2*β*(q.inclusion v (q.atlasParam w))^(1+4*β)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.closedGradient v w))

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Variational_Extremizer
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations Slicing CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

noncomputable def fillingDeficit {k : ℕ} (c p : ℝ) (T : Functional X (k+1)) : ℝ :=
  fillingVolume T-c*(mass T)^p

end CAT0Fillings
end

end OAI
end


