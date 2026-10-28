-- Prove2me | Definitions.Def_OAIQ070A006
-- name    : OAIQ070A006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:20:09.787028+00:00
-- url     : https://prove2.me/theorems/b1c15820-f43d-473c-bec1-c7da8ef38e6e
-- title:
--   Definitions bundle OAIQ070A006 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 55 definitions, 3 instances and 41 theorems. The definitions and types are `OAI.YauCounterexamples.CompactMetricAtlas.transfer`, `OAI.YauCounterexamples.CompactMetricAtlas.transferAcross`, `OAI.YauCounterexamples.MetricIntegralAtlas.positiveIntegral`, `OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure`, `OAI.YauCounterexamples.PhaseMatrixValid`, `OAI.YauCounterexamples.PositivePairing.eigenpairDerivative`, `OAI.YauCounterexamples.PositivePairing.eigenpairLinearization`, `OAI.YauCounterexamples.PositivePairing.eigenpairMap`, `OAI.YauCounterexamples.PositivePairing.perpendicular`, `OAI.YauCounterexamples.SphericalLargeWitness`, `OAI.YauCounterexamples.SphericalMetricGood`, `OAI.YauCounterexamples.SphericalPositiveTensor`, `OAI.YauCounterexamples.SphericalSimple`, `OAI.YauCounterexamples.SphericalTensor`, `OAI.YauCounterexamples.ThreeAnnulus`, `OAI.YauCounterexamples.ThreeCleanBall`, `OAI.YauCounterexamples.ThreeExterior`, `OAI.YauCounterexamples.ThreeLargeWitness`, `OAI.YauCounterexamples.ThreePhaseData`, `OAI.YauCounterexamples.ThreePositiveTensor`, `OAI.YauCounterexamples.ThreeSignAbove`, `OAI.YauCounterexamples.ThreeSimple`, `OAI.YauCounterexamples.ThreeTensor`, `OAI.YauCounterexamples.actualCoordinateNorm`, `OAI.YauCounterexamples.actualHessianForm`, `OAI.YauCounterexamples.actualProfileTraceForm`, `OAI.YauCounterexamples.chartFormTrivialization`, `OAI.YauCounterexamples.chartTensorPositive`, `OAI.YauCounterexamples.chartTrivMetricForm`, `OAI.YauCounterexamples.completePhaseColumns`, `OAI.YauCounterexamples.coordinateMetricGradient`, `OAI.YauCounterexamples.ellipticCommutator`, `OAI.YauCounterexamples.inducedMetric`, `OAI.YauCounterexamples.instNormedSpaceRealMetricForm`, `OAI.YauCounterexamples.metricFormNorm`, `OAI.YauCounterexamples.metricProfileTraceForm`, `OAI.YauCounterexamples.phaseCriticalCorrection`, `OAI.YauCounterexamples.phaseCriticalProjection`, `OAI.YauCounterexamples.phaseFormMatrix`, `OAI.YauCounterexamples.shiftedPhaseImag` and 15 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_DifferentialEq_SphericalOpenFormNorm`, `SmoothYau_DifferentialEq_TransferAcross`, `SmoothYau_Estimates_PartialBilinearExtension`, `SmoothYau_Estimates_PhaseFormMatrix`, `SmoothYau_Estimates_RadialSpeedPositiveAnnulus`, `SmoothYau_Estimates_RealPhaseLinear`, `SmoothYau_Estimates_SphericalPinFormNorm`, `SmoothYau_Geometry_ActualHessianForm`, `SmoothYau_Geometry_ProfilePeriodizeFirst`, `SmoothYau_Geometry_RadialFiniteDualNorm`, `SmoothYau_Geometry_RealForm`, `SmoothYau_Geometry_RoundMetricExists`, `SmoothYau_Geometry_SymmLChartTrivialization`, `SmoothYau_Limits_CoordinateForm`, `SmoothYau_NodalMeasure_PositiveIntegral`, `SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer`, `SmoothYau_Smoothness_ChartTensorCoordLocal1`, `SmoothYau_Smoothness_ExistsFinitePatchPartition`, `SmoothYau_Smoothness_GlobalPrepDualNorm`, `SmoothYau_Smoothness_PulledGradient`, `SmoothYau_Smoothness_SobolevRepresentativeOrderCongr`, `SmoothYau_Smoothness_SourceSignBox`, `SmoothYau_Smoothness_SphericalBaseProfileRadius`, `SmoothYau_Spectrum_ContinuousEigenpairLinearization`, `SmoothYau_Spectrum_ScalarCompDirectional`, `SmoothYau_SphereMetric_FourThree`, `SmoothYau_SphereMetric_ThreeCutoffControlBounds`, `SmoothYau_SphereMetric_ThreeFixedFormNorm`, `SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`; the bundles `OAIQ070A000`, `OAIQ070A001`, `OAIQ070A002` and `OAIQ070A003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A009`, `OAIQ070A010` and `OAIQ070A012`; the statements `OAI_YauCounterexamples_CompactMetricAtlas_shiftedInverse_eigenfunction`, `OAI_YauCounterexamples_MetricIntegralAtlas_green`, `OAI.YauCounterexamples.canonical_phase_triple_smallBall`, `OAI.YauCounterexamples.compact_profile_three_phase_data`, `OAI.YauCounterexamples.exists_spherical_chart_quasimodes`, `OAI.YauCounterexamples.exists_spherical_exact_stage`, `OAI.YauCounterexamples.exists_spherical_fixed_witnesses`, `OAI.YauCounterexamples.exists_spherical_global_quasimodes`, `OAI.YauCounterexamples.exists_spherical_scalar_producer`, `OAI.YauCounterexamples.exists_three_fixed_witnesses`, `OAI.YauCounterexamples.normalFamilyWave_at_zero`, `OAI.YauCounterexamples.sphericalBaseProfile_chart_margins`, `OAI.YauCounterexamples.sphericalMetricGood_neighborhood`, `OAI.YauCounterexamples.spherical_global_jet_lower`, `OAI.YauCounterexamples.spherical_largeWitness_eventually` and `OAI.YauCounterexamples.spherical_wave_background_chart_bounds`; the proofs of `OAI.YauCounterexamples.CompactMetricAtlas.eventually_product_scalar_exactification`, `OAI.YauCounterexamples.CompactMetricAtlas.eventually_scalar_exactification`, `OAI.YauCounterexamples.actual_radialCorrugation_strict_shift`, `OAI.YauCounterexamples.annular_orthogonal_transverse_nonzero`, `OAI.YauCounterexamples.cutoff_exactification_in_smooth_neighborhood`, `OAI.YauCounterexamples.exists_spherical_exact_stage`, `OAI.YauCounterexamples.exists_spherical_global_quasimodes`, `OAI.YauCounterexamples.exists_spherical_scalar_producer`, `OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ`, `OAI.YauCounterexamples.normalFamilyWave_at_zero`, `OAI.YauCounterexamples.sphere_three`, `OAI.YauCounterexamples.spherical_global_jet_lower` and `OAI.YauCounterexamples.three_rank_separating_tensor`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A000
import Definitions.Def_OAIQ070A001
import Definitions.Def_OAIQ070A002
import Definitions.Def_OAIQ070A003

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CoordinateForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def metricProfileTraceForm (B H : CoordinateForm E) (a : E) : CoordinateForm E :=
  (H a a) • B + (1+B a a) • H

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ProfilePeriodizeFirst
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma profileLattice_separated {k l : ProfileLattice} (hkl : k ≠ l) :
    1 ≤ ‖profileLatticePoint k - profileLatticePoint l‖ := by
  have hne : k.1 ≠ l.1 ∨ k.2 ≠ l.2 := by
    by_contra h
    push Not at h
    exact hkl (Prod.ext h.1 h.2)
  rw [Prod.norm_def]
  rcases hne with h | h
  · have hh : (1:ℝ) ≤ |(k.1:ℝ)-(l.1:ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h)
    exact hh.trans (le_max_left _ _)
  · have hh : (1:ℝ) ≤ |(k.2:ℝ)-(l.2:ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h)
    exact hh.trans (le_max_right _ _)


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RadialSpeedPositiveAnnulus
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma periodicRadialOffset_eq {R : ℝ} (hR : 2*R < 1) (k : ProfileLattice)
    {x : ProfilePlane} (hx : ‖x-profileLatticePoint k‖ < R) :
    periodicRadialOffset R x = x-profileLatticePoint k := by
  classical
  have he : ∃ l, ‖x-profileLatticePoint l‖ < R := ⟨k,hx⟩
  have hh : he.choose = k := by
    by_contra hn
    have hsep := profileLattice_separated hn
    have htri : ‖profileLatticePoint he.choose-profileLatticePoint k‖ ≤
        ‖x-profileLatticePoint he.choose‖+‖x-profileLatticePoint k‖ := by
      calc
        _ = ‖(profileLatticePoint he.choose-x)+(x-profileLatticePoint k)‖ := by congr 1; abel
        _ ≤ ‖profileLatticePoint he.choose-x‖+‖x-profileLatticePoint k‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev (profileLatticePoint he.choose) x]
    linarith only [hsep,htri,he.choose_spec,hx,hR]
  simp only [periodicRadialOffset,dite_eq_left he,hh]



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.YauCounterexamples.metricDualNorm
attribute [local instance] OAI.YauCounterexamples.metricDualSpace
local instance metricFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def coordinateMetricGradient (g : SmoothMetric E E) (ψ : E → ℝ) (x : E) : E :=
  (selfMetricFlat g x).inverse (fderiv ℝ ψ x)

def actualProfileTraceForm (g : SmoothMetric E E) (u : E → ℝ) (x : E) : CoordinateForm E :=
  metricProfileTraceForm (selfMetricFlat g x) (actualCoordinateHessian g u x)
    (coordinateMetricGradient g u x)


end

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma periodicRadialOffset_norm_le {R : ℝ} (hR : 0 ≤ R) (x : ProfilePlane) :
    ‖periodicRadialOffset R x‖ ≤ R := by
  classical
  unfold periodicRadialOffset
  split_ifs with h
  · exact h.choose_spec.le
  · simpa using hR

lemma periodicRadialOffset_radius_sq_le {R : ℝ} (hR : 0 ≤ R) (x : ProfilePlane) :
    (periodicRadialOffset R x).1^2+(periodicRadialOffset R x).2^2 ≤ 2*R^2 := by
  have hn := periodicRadialOffset_norm_le hR x
  have h1 := (norm_fst_le (periodicRadialOffset R x)).trans hn
  have h2 := (norm_snd_le (periodicRadialOffset R x)).trans hn
  rw [Real.norm_eq_abs] at h1 h2
  have hsq1 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hsq2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  simpa only [sq_abs] using (show
    |(periodicRadialOffset R x).1|^2+|(periodicRadialOffset R x).2|^2 ≤ 2*R^2 by
      linarith only [hsq1,hsq2])


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SphericalBaseProfileRadius
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [local instance] OAI.YauCounterexamples.chartFormDualNorm
attribute [local instance] OAI.YauCounterexamples.chartFormDualSpace
attribute [local instance] OAI.YauCounterexamples.chartFormFormNorm
attribute [local instance] OAI.YauCounterexamples.chartFormFormSpace
lemma chartMetricForm_contDiffOn (g : SmoothMetric E M) (p : M) :
    ContDiffOn ℝ ∞ (chartMetricForm g p) (chartAt E p).target :=
  metricMatrixForm_contDiffOn (contDiffOn_metricCoefficient g p)

lemma chartMetricForm_pos (g : SmoothMetric E M) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target) {v : E} (hv : v ≠ 0) :
    0 < chartMetricForm g p y v v :=
  metricMatrixForm_pos (metricCoefficients_posDef g p hy) hv

end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
variable {n : ℕ}

def sphereChartMetric (g : SmoothMetric (Euclidean n) (Sphere n)) (p : Sphere n) :
    SmoothMetric (Euclidean n) (Euclidean n) :=
  flatMetricOfForm (chartMetricForm g p)
    (contDiffOn_univ.mp (by simpa only [sphere_chart_target] using chartMetricForm_contDiffOn g p))
    (chartMetricForm_symm g p)
    (fun y v hv => chartMetricForm_pos g p (by rw [sphere_chart_target]; trivial) hv)


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold BoxIntegral
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_SymmLChartTrivialization
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]

attribute [local instance] OAI.YauCounterexamples.tensorDualNorm
attribute [local instance] OAI.YauCounterexamples.tensorDualSpace
local instance tensorFormSpace_r9b3c0c_1 : NormedSpace ℝ (MetricForm E) := inferInstanceAs
  (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
attribute [local instance] OAI.YauCounterexamples.tensorTangentDualAdd
attribute [local instance] OAI.YauCounterexamples.tensorTangentDualSmul
local instance tensorTangentFormAdd_r9b3c0c_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) :=
  inferInstance
local instance tensorTangentFormSmul_r9b3c0c_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
def chartFormTrivialization (p : M) := trivializationAt (MetricForm E) (TangentForm (E:=E)) p

def symmetrizeMetricForm : MetricForm E →L[ℝ] MetricForm E :=
  (1/2:ℝ) • (ContinuousLinearMap.id ℝ (MetricForm E) +
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap)
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTensorCoordLocal1
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.YauCounterexamples.instNormedSpaceRealContinuousLinearMapId_solutions
local instance instNormedSpaceRealMetricForm : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))

attribute [local instance] OAI.YauCounterexamples.instIsTopologicalAddGroupContinuousLinearMapRealIdTangentSpaceModelWithCornersSelf_solutions
local instance instContinuousSMulRealContinuousLinearMapIdTangentSpaceModelWithCornersSelf_solutions_r9b3c0c_1 (x : M) : ContinuousSMul ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) := inferInstance
def chartTrivMetricForm (g : SmoothMetric E M) (p : M) (y : E) : MetricForm E :=
  (chartFormTrivialization (E:=E) p ⟨(chartAt E p).symm y,g.inner ((chartAt E p).symm y)⟩).2

variable (g : SmoothMetric E M) (p : M) (K : Compacts E)

attribute [local instance] OAI.YauCounterexamples.instNormedAddCommGroupMetricForm
local instance instIsTopologicalAddGroupTangentForm_r9b3c0c_1 (x : M) : IsTopologicalAddGroup (TangentForm (E:=E) x) := inferInstance
local instance instContinuousSMulRealTangentForm_r9b3c0c_1 (x : M) : ContinuousSMul ℝ (TangentForm (E:=E) x) := inferInstance
def chartTensorPositive (H : 𝓓_{K}(E,MetricForm E)) : Prop :=
  ∀ y ∈ (K : Set E), positiveFormOn (⊤ : Submodule ℝ E)
    (chartTrivMetricForm g p y + symmetrizeMetricForm (H y))

end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RealForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def completePhaseColumns (U : RealForm V) (a b : V) : RealForm V :=
  let l := innerForm a
  let m := innerForm b
  let A := inner ℝ a a
  let B := inner ℝ b b
  show RealForm V from
  -(A⁻¹ • (l.smulRight (U b) + (U b).smulRight l)) +
    B⁻¹ • (m.smulRight (U a) + (U a).smulRight m) +
    (U a b / A ^ 2) • l.smulRight l -
    (U a b / B ^ 2) • m.smulRight m -
    (U a a / (A * B)) • (l.smulRight m + m.smulRight l)

@[simp] theorem completePhaseColumns_apply (U : RealForm V) (a b x y : V) :
    completePhaseColumns U a b x y =
      -(inner ℝ a a)⁻¹ * (inner ℝ a x * U b y + U b x * inner ℝ a y) +
      (inner ℝ b b)⁻¹ * (inner ℝ b x * U a y + U a x * inner ℝ b y) +
      U a b / (inner ℝ a a) ^ 2 * (inner ℝ a x * inner ℝ a y) -
      U a b / (inner ℝ b b) ^ 2 * (inner ℝ b x * inner ℝ b y) -
      U a a / (inner ℝ a a * inner ℝ b b) *
        (inner ℝ a x * inner ℝ b y + inner ℝ b x * inner ℝ a y) := by
  simp only [completePhaseColumns, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    innerForm_apply, smul_eq_mul]
  ring

def phaseCriticalProjection (H : RealForm V) (b : V) : V →ₗ[ℝ] V :=
  LinearMap.id - (H b b)⁻¹ • (H b).smulRight b

@[simp] theorem phaseCriticalProjection_apply (H : RealForm V) (b x : V) :
    phaseCriticalProjection H b x = x - ((H b b)⁻¹ * H b x) • b := by
  simp [phaseCriticalProjection, smul_smul]

def phaseCriticalCorrection (H : RealForm V) (b : V) : RealForm V :=
  (H b b)⁻¹ • (H b).smulRight (H b) +
    innerForm.compl₁₂ (phaseCriticalProjection H b) (phaseCriticalProjection H b)

@[simp] theorem phaseCriticalCorrection_apply (H : RealForm V) (b x y : V) :
    phaseCriticalCorrection H b x y = (H b b)⁻¹ * (H b x * H b y) +
      inner ℝ (phaseCriticalProjection H b x) (phaseCriticalProjection H b y) := rfl

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PhaseFormMatrix
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
open Matrix Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def phaseFormMatrix (U : RealForm (EuclideanSpace ℝ ι)) : Matrix ι ι ℝ :=
  fun i j => U (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealPhaseLinear
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise

def shiftedPhaseImag (a ν b : PhaseSpace) (δ : ℝ) : PhaseSpace :=
  (Real.sqrt (1 + ‖a + δ • ν‖^2) / Real.sqrt (1 + ‖a‖^2)) • b

def transverseAngleSq (b c : PhaseSpace) : ℝ :=
  (‖b‖^2 * ‖c‖^2 - (inner ℝ b c)^2) / (‖b‖^2 * ‖c‖^2)

def PhaseMatrixValid (H : RealForm PhaseSpace) (z : Fin 3 → ℂ)
    (κ C : ℝ) (Q : ComplexPhaseMatrix) : Prop :=
  Qᵀ = Q ∧ Q *ᵥ z = 0 ∧ ‖Q‖ ≤ C ∧
    ∀ v, 4 * κ * squareSum v ≤ realQuadratic (phaseFormMatrix H - Q.map Complex.re) v

def ThreePhaseData (H : RealForm PhaseSpace) (a ν : PhaseSpace)
    (δ κ η C : ℝ) : Prop :=
  ∃ b c : PhaseSpace, inner ℝ ν b = 0 ∧ inner ℝ ν c = 0 ∧
    ‖b‖^2 = 1 + ‖a‖^2 ∧ ‖c‖^2 = 1 + ‖a‖^2 ∧
    η ≤ transverseAngleSq b c ∧
    (∃ Q, PhaseMatrixValid H (complexPhaseVector a b) κ C Q) ∧
    (∃ Q, PhaseMatrixValid H (complexPhaseVector a c) κ C Q) ∧
    (∃ Q, PhaseMatrixValid H
      (complexPhaseVector (a + δ • ν) (shiftedPhaseImag a ν b δ)) κ C Q)


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualHessianForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples

def actualHessianForm (f : PhaseSpace → ℝ) : RealForm PhaseSpace where
  toFun v := (fderiv ℝ (fderiv ℝ f) 0 v).toLinearMap
  map_add' v w := by ext y; simp
  map_smul' c v := by ext y; simp

@[simp] lemma actualHessianForm_apply (f : PhaseSpace → ℝ) (v w : PhaseSpace) :
    actualHessianForm f v w = fderiv ℝ (fderiv ℝ f) 0 v w := rfl

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_GlobalPrepDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def actualCoordinateNorm (g : SmoothMetric E E) (x : E) (v : E) : ℝ :=
  Real.sqrt (selfMetricFlat g x v v)

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RadialFiniteDualNorm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section


section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff

lemma profileTorus_ball_lift {q z : ProfilePlane} {ρ : ℝ}
    (hz : profileTorusQuotient z ∈
      (ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ)) :
    ∃ k : ProfileLattice, dist (z-profileLatticePoint k) q < ρ := by
  refine ⟨(round (z.1-q.1),round (z.2-q.2)),?_⟩
  have h₁ := circle_ball_round hz.1
  have h₂ := circle_ball_round hz.2
  simp only [dist_eq_norm,Prod.norm_def,Real.norm_eq_abs,Prod.fst_sub,Prod.snd_sub,
    profileLatticePoint, max_lt_iff]
  constructor
  · convert h₁ using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  · convert h₂ using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring

theorem exists_radial_phase_window {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b < R^2) (hR : 0 < R)
    (hsmall : 2*R < 1) (hmid : β ((a+b)/2) = 1) :
    ∃ (q : ProfilePlane) (ρ c : ℝ), 0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < c ∧
      ∀ z, profileTorusQuotient z ∈
        (ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ) →
        c ≤ periodicRadialSpeed β R z := by
  let s := Real.sqrt ((a+b)/2)
  have ht : 0 < (a+b)/2 := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr ht
  have hs2 : s^2 = (a+b)/2 := Real.sq_sqrt ht.le
  have hsR : s < R := by nlinarith
  let q : ProfilePlane := (s,0)
  have hqn : ‖q‖ = s := by simp [q,Prod.norm_def,Real.norm_eq_abs,abs_of_pos hs,hs.le]
  let f : ProfilePlane → ℝ := fun z => 2*Real.sqrt (z.1^2+z.2^2)*β (z.1^2+z.2^2)
  have hf : Continuous f := (continuous_const.mul
    (Real.continuous_sqrt.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2)))).mul
    (hβ.continuous.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2)))
  have hq : s < f q := by
    dsimp [f,q]
    rw [zero_pow (by norm_num : 2 ≠ 0),add_zero,hs2,hmid,mul_one]
    change s < 2*s
    linarith
  obtain ⟨η,hη,hηsub⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hf) q hq
  let ρ := min η (min ((R-s)/2) (1/4))
  have hρ : 0 < ρ := lt_min hη (lt_min (by linarith) (by norm_num))
  refine ⟨q,ρ,s,hρ,(min_le_right _ _).trans (min_le_right _ _),hs,?_⟩
  intro z hz
  obtain ⟨k,hk⟩ := profileTorus_ball_lift hz
  have hnk : ‖z-profileLatticePoint k‖ < R := by
    have htri := norm_le_norm_add_norm_sub' (z-profileLatticePoint k) q
    have hks : ‖z-profileLatticePoint k-q‖ < ρ := by simpa [dist_eq_norm] using hk
    have hr : ρ ≤ (R-s)/2 := (min_le_right _ _).trans (min_le_left _ _)
    rw [hqn] at htri
    linarith
  have hh : s < f (z-profileLatticePoint k) := hηsub (hk.trans_le (min_le_left _ _))
  rw [periodicRadialSpeed,periodicRadialOffset_eq hsmall k hnk]
  exact hh.le

end


open Set Function Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ENNReal InnerProductSpace ContDiff

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SourceSignBox
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.threeChartedSpace _root_.OAI.YauCounterexamples.threeIsManifold _root_.OAI.YauCounterexamples.threeProductChartedSpace _root_.OAI.YauCounterexamples.threeProductIsManifold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold MeasureTheory BoxIntegral
open scoped Topology ContDiff
namespace YauCounterexamples

def sphericalProfileMetricNeighborhood : Set (SmoothMetric (Euclidean 3) (Sphere 3)) :=
  {g | ∀ t : ℝ, ∀ y ∈ sourceProfileCoverage,
    hessianMargins (selfMetricFlat (sphereChartMetric g sourcePole) y)
      (actualCoordinateHessian (sphereChartMetric g sourcePole)
        (sphericalBaseProfile sourceAxisOne sourceAxisTwo t ∘
          (chartAt (Euclidean 3) sourcePole).symm) y)}

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ExistsFinitePatchPartition
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Function Filter
open scoped Topology Manifold ContDiff
namespace YauCounterexamples
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma complexUnitBump_eq_one {x : E} (hx : ‖x‖ ≤ 1) : complexUnitBump E x = 1 := by
  have hh : x ∈ Metric.closedBall (0 : E) (unitBump E).rIn := by
    simpa only [Metric.mem_closedBall, dist_zero_right, unitBump] using hx
  simp only [complexUnitBump, (unitBump E).one_of_mem_closedBall hh, Complex.ofReal_one]

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PartialBilinearExtension
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
namespace YauCounterexamples
variable {𝕜 P E F : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup P] [Module 𝕜 P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  (B : P →ₗ[𝕜] P →ₗ[𝕜] F) (e : P →ₗ[𝕜] E) (hd : DenseRange e)
  (C : ℝ) (hb : ∀ p q, ‖B p q‖ ≤ C * ‖e p‖ * ‖e q‖)

lemma partialBilinearExtension_apply (p q : P) :
    partialBilinearExtension B e hd C hb p (e q) = B p q :=
  LinearMap.extendOfNorm_eq hd ⟨C * ‖e p‖, hb p⟩ q

lemma norm_partialBilinearExtension_le (hC : 0 ≤ C) (p : P) :
    ‖partialBilinearExtension B e hd C hb p‖ ≤ C * ‖e p‖ :=
  LinearMap.opNorm_extendOfNorm_le hd (mul_nonneg hC (norm_nonneg _)) (hb p)

lemma bilinearExtension_apply (hC : 0 ≤ C) (p q : P) :
    bilinearExtension B e hd C hb (e p) (e q) = B p q := by
  rw [bilinearExtension, LinearMap.extendOfNorm_eq hd
    ⟨C, norm_partialBilinearExtension_le B e hd C hb hC⟩]
  exact partialBilinearExtension_apply B e hd C hb p q

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SobolevRepresentativeOrderCongr
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.manifoldSobolev_completeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open Set Function Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma euclideanElliptic_mul (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    {χ u : E → ℂ} (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x : E) :
    euclideanElliptic b a c (fun y => χ y * u y) x =
      χ x * euclideanElliptic b a c u x + euclideanElliptic b a c χ x * u x +
      ∑ i, ∑ j, (a i j x : ℂ) *
        (fderiv ℝ χ x (b i) * fderiv ℝ u x (b j) +
          fderiv ℝ χ x (b j) * fderiv ℝ u x (b i)) := by
  simp only [euclideanElliptic, second_fderiv_mul hχ hu,
    fderiv_fun_mul (hχ.differentiable (by norm_num) x) (hu.differentiable (by norm_num) x),
    _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm, mul_comm]
  ring

lemma euclideanElliptic_scalarAffine (b : ι → E)
    (a : ι → ι → E → ℝ) (c : ι → E → ℝ) (p : E) (r : ℝ)
    {u : E → ℂ} (hu : ContDiff ℝ 2 u) (x : E) :
    euclideanElliptic b (fun i j y => a i j (p + r • y))
      (fun i y => r * c i (p + r • y)) (fun y => u (p + r • y)) x =
      (r : ℂ) ^ 2 * euclideanElliptic b a c u (p + r • x) := by
  simp only [euclideanElliptic, second_fderiv_scalarAffine p r hu,
    fderiv_scalarAffine p r u x _ (hu.differentiable (by norm_num) _), Complex.ofReal_mul,
    mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma euclideanElliptic_congr (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    {u v : E → ℂ} {x : E} (h : u =ᶠ[𝓝 x] v) :
    euclideanElliptic b a c u x = euclideanElliptic b a c v x := by
  have hh (w : E) : (fun y => fderiv ℝ u y w) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ v y w) :=
    h.fderiv.mono (fun _ hy => congrArg (fun L : E →L[ℝ] ℂ => L w) hy)
  simp only [euclideanElliptic, h.fderiv_eq, (hh _).fderiv_eq]

lemma euclideanElliptic_add_at (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    {u v : E → ℂ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    euclideanElliptic b a c (fun y => u y + v y) x =
      euclideanElliptic b a c u x + euclideanElliptic b a c v x := by
  simp only [euclideanElliptic, second_fderiv_add_at hu hv,
    fderiv_fun_add (hu.differentiableAt (by norm_num)) (hv.differentiableAt (by norm_num)),
    _root_.add_apply, mul_add, Finset.sum_add_distrib]
  ring

lemma euclideanElliptic_zero (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ) (x : E) :
    euclideanElliptic b a c 0 x = 0 := by
  simp [euclideanElliptic]


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma unscale_local_equation (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (p : E) {r : ℝ} (hr : r ≠ 0) (α : ℝ) {w : E → ℂ}
    (hw : ContDiff ℝ 2 w) (f : E → ℂ) (x : E)
    (he : ((α * r ^ 2 : ℝ) : ℂ) * w (r⁻¹ • (x - p)) -
      euclideanElliptic b (fun i j y => a i j (p + r • y))
        (fun i y => r * c i (p + r • y)) w (r⁻¹ • (x - p)) =
      (r : ℂ) ^ 2 * f x) :
    (α : ℂ) * w (r⁻¹ • (x - p)) -
      euclideanElliptic b a c (fun y => w (r⁻¹ • (y - p))) x = f x := by
  have hu : ContDiff ℝ 2 (fun y => w (r⁻¹ • (y - p))) := hw.comp (by fun_prop)
  have hh := euclideanElliptic_scalarAffine b a c p r hu (r⁻¹ • (x - p))
  simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, mul_inv_cancel₀ hr, one_smul, add_sub_cancel] at hh
  rw [hh] at he
  apply mul_left_cancel₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr))
  calc
    (r : ℂ) ^ 2 * ((α : ℂ) * w (r⁻¹ • (x - p)) -
        euclideanElliptic b a c (fun y => w (r⁻¹ • (y - p))) x) =
      ((α * r ^ 2 : ℝ) : ℂ) * w (r⁻¹ • (x - p)) -
        (r : ℂ) ^ 2 * euclideanElliptic b a c (fun y => w (r⁻¹ • (y - p))) x := by
          push_cast
          ring
    _ = _ := he

def ellipticCommutator (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (χ u : E → ℂ) (x : E) : ℂ :=
  euclideanElliptic b a c χ x * u x + ∑ i, ∑ j, (a i j x : ℂ) *
    (fderiv ℝ χ x (b i) * fderiv ℝ u x (b j) +
      fderiv ℝ χ x (b j) * fderiv ℝ u x (b i))

lemma cutoff_parametrix_equation (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    {χ u : E → ℂ} (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u)
    (α : ℝ) (f : E → ℂ)
    (he : ∀ x ∈ support χ, (α : ℂ) * u x - euclideanElliptic b a c u x = f x)
    (x : E) :
    (α : ℂ) * (χ x * u x) - euclideanElliptic b a c (fun y => χ y * u y) x =
      χ x * f x - ellipticCommutator b a c χ u x := by
  rw [euclideanElliptic_mul b a c hχ hu]
  have hh : χ x * ((α : ℂ) * u x - euclideanElliptic b a c u x) = χ x * f x := by
    by_cases hx : χ x = 0
    · simp only [hx, zero_mul]
    · rw [he x hx]
  dsimp only [ellipticCommutator]
  linear_combination hh

lemma support_ellipticCommutator (b : ι → E) (a : ι → ι → E → ℝ)
    (c : ι → E → ℝ) (χ u : E → ℂ) :
    support (ellipticCommutator b a c χ u) ⊆ tsupport χ := by
  intro x hx
  by_contra hn
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hn
  have he : euclideanElliptic b a c χ x = 0 := by
    rw [euclideanElliptic_congr b a c (notMem_tsupport_iff_eventuallyEq.mp hn)]
    exact euclideanElliptic_zero b a c x
  exact hx (by simp only [ellipticCommutator, he, hd, zero_apply,
    zero_mul, add_zero, mul_zero, Finset.sum_const_zero])
lemma ellipticCommutator_congr_coeff (b : ι → E)
    (a a' : ι → ι → E → ℝ) (c c' : ι → E → ℝ) (χ u : E → ℂ)
    (ha : ∀ x ∈ tsupport χ, ∀ i j, a i j x = a' i j x)
    (hc : ∀ x ∈ tsupport χ, ∀ i, c i x = c' i x) (x : E) :
    ellipticCommutator b a c χ u x = ellipticCommutator b a' c' χ u x := by
  by_cases hx : x ∈ tsupport χ
  · simp only [ellipticCommutator, euclideanElliptic, ha x hx, hc x hx]
  · have h1 := mt (fun h => support_ellipticCommutator b a c χ u h) hx
    have h2 := mt (fun h => support_ellipticCommutator b a' c' χ u h) hx
    exact (notMem_support.mp h1).trans (notMem_support.mp h2).symm


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped SchwartzMap BoundedContinuousFunction
section FirstOrderSobolev
open scoped SchwartzMap BoundedContinuousFunction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma sobolevRepresentative_order_congr {s t : ℝ} (h : s = t)
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * t)
    (u : FourierSobolevSpace E ℂ s) : sobolevRepresentative hs u = sobolevRepresentative ht u := by
  subst t
  rfl

end FirstOrderSobolev



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ScalarCompDirectional
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma fderiv_inChart_change_C2 {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (p q : M) {y : E} (hy : y ∈ (chartAt E q).target)
    (hp : (chartAt E q).symm y ∈ (chartAt E p).source) (i : CoordIndex E) :
    fderiv ℝ (u ∘ (chartAt E q).symm) y (Module.finBasis ℝ E i) =
      ∑ k, fderiv ℝ (u ∘ (chartAt E p).symm) (chartTransition p q y)
        (Module.finBasis ℝ E k) * coordinateTransitionMatrix p q y k i := by
  have he : (u ∘ (chartAt E q).symm) =ᶠ[𝓝 y]
      ((u ∘ (chartAt E p).symm) ∘ chartTransition p q) := by
    filter_upwards [chart_overlap_nhds p q hy hp] with z hz
    simp only [Function.comp_apply, chartTransition, (chartAt E p).left_inv hz.2]
  rw [he.fderiv_eq]
  have hf := (contDiffAt_chartTransition p q hy hp).differentiableAt (by simp)
  have hu' := (contDiffAt_inChart_C2 hu p ((chartAt E p).map_source hp)).differentiableAt (by simp)
  rw [fderiv_comp y hu' hf, ContinuousLinearMap.comp_apply,
    ← (Module.finBasis ℝ E).sum_repr (fderiv ℝ (chartTransition p q) y (Module.finBasis ℝ E i))]
  simp only [map_sum, map_smul, smul_eq_mul, coordinateTransitionMatrix,
    LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma metricFlux_change_C2 {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (g : SmoothMetric E M) (p q : M) {y : E} (hy : y ∈ (chartAt E q).target)
    (hp : (chartAt E q).symm y ∈ (chartAt E p).source) (i : CoordIndex E) :
    metricFlux g u q y i = ∑ k, |(coordinateTransitionMatrix p q y).det| *
      (coordinateTransitionMatrix p q y)⁻¹ i k * metricFlux g u p (chartTransition p q y) k := by
  classical
  let d : CoordIndex E → ℝ := fun j =>
    fderiv ℝ (u ∘ (chartAt E p).symm) (chartTransition p q y) (Module.finBasis ℝ E j)
  have hh := congrArg (fun A : Matrix (CoordIndex E) (CoordIndex E) ℝ => A.mulVec d i)
    (metricInverse_change_left g p q hy hp)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hh
  simp only [metricFlux, fderiv_inChart_change_C2 hu p q hy hp,
    metricDensity_change g p q hy hp]
  have hs : (∑ j, (metricCoefficients g q y)⁻¹ i j *
      ∑ k, d k * coordinateTransitionMatrix p q y k j) =
      ∑ k, (coordinateTransitionMatrix p q y)⁻¹ i k *
        ∑ j, (metricCoefficients g p (chartTransition p q y))⁻¹ k j * d j := by
    simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using hh
  change (_ * _) * (∑ j, (metricCoefficients g q y)⁻¹ i j *
    ∑ k, d k * coordinateTransitionMatrix p q y k j) = _
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [d]
  ring

lemma differentiableAt_metricFlux_C2 {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    DifferentiableAt ℝ (metricFlux g u p) y := by
  apply differentiableAt_pi.mpr
  intro i
  have hd := ((contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  apply hd.mul
  apply DifferentiableAt.fun_sum
  intro j _
  have ha := ((contDiffOn_metricInverse g p i j).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hu' := ((contDiffAt_inChart_C2 hu p hy).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact ha.mul (hu'.clm_apply (differentiableAt_const _))

lemma localLaplacian_expansion_C2 {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) (g : SmoothMetric E M)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    localLaplacian g u p y =
      (∑ i, ∑ j, (metricCoefficients g p y)⁻¹ i j *
        fderiv ℝ (fun z => fderiv ℝ (u ∘ (chartAt E p).symm) z (Module.finBasis ℝ E j)) y
          (Module.finBasis ℝ E i)) +
      ∑ j, metricFirstCoefficient g p j y *
        fderiv ℝ (u ∘ (chartAt E p).symm) y (Module.finBasis ℝ E j) := by
  classical
  let ρ := fun z => Real.sqrt (metricCoefficients g p z).det
  let A := metricCoefficients g p
  let v := u ∘ (chartAt E p).symm
  let b := Module.finBasis ℝ E
  have hρ : DifferentiableAt ℝ ρ y := ((contDiffOn_metricDensity g p).contDiffAt
    ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hA (i j : CoordIndex E) : DifferentiableAt ℝ (fun z => (A z)⁻¹ i j) y :=
    ((contDiffOn_metricInverse g p i j).contDiffAt
      ((chartAt E p).open_target.mem_nhds hy)).differentiableAt (by simp)
  have hv : DifferentiableAt ℝ (fderiv ℝ v) y :=
    ((contDiffAt_inChart_C2 hu p hy).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (i : CoordIndex E) : (fun z => metricFlux g u p z i) =
      fun z => ∑ j, (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j) := by
    funext z
    simp only [metricFlux, ρ, A, v, b, Finset.mul_sum, mul_assoc]
  have hder (i : CoordIndex E) : fderiv ℝ (fun z => metricFlux g u p z i) y (b i) =
      ∑ j, ((ρ y * (A y)⁻¹ i j) * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) +
        fderiv ℝ v y (b j) * fderiv ℝ (fun z => ρ z * (A z)⁻¹ i j) y (b i)) := by
    rw [he]
    erw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j z => (ρ z * (A z)⁻¹ i j) * fderiv ℝ v z (b j))
      (fun j _ => (hρ.mul (hA i j)).mul (hv.clm_apply (differentiableAt_const _)))]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    erw [fderiv_mul (c := fun z => ρ z * (A z)⁻¹ i j)
      (d := fun z => fderiv ℝ v z (b j)) (hρ.mul (hA i j))
      (hv.clm_apply (differentiableAt_const _))]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  change (ρ y)⁻¹ * ∑ i, fderiv ℝ (fun z => metricFlux g u p z i) y (b i) = _
  simp_rw [hder, Finset.sum_add_distrib]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have hn : ρ y ≠ 0 := (Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy)).ne'
  have hmain : (∑ i, (ρ y)⁻¹ * ∑ j, ρ y * (A y)⁻¹ i j *
      fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i)) =
      ∑ i, ∑ j, (A y)⁻¹ i j * fderiv ℝ (fun z => fderiv ℝ v z (b j)) y (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hmain]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [metricFirstCoefficient, ρ, A, b, v, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem laplaceBeltrami_nonpos_at_localMax_C2 (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) {x : M} (hm : IsLocalMax u x) :
    laplaceBeltrami g u x ≤ 0 := by
  classical
  let c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hInv : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  let f := u ∘ c.symm
  have hf : ContDiffAt ℝ 2 f (c x) := contDiffAt_inChart_C2 hu x hx
  have hm' : IsLocalMax f (c x) := by
    have h : IsLocalMax u (c.symm (c x)) := by rw [hInv]; exact hm
    exact h.comp_continuous (c.symm.continuousAt hx)
  change localLaplacian g u x (c x) ≤ 0
  rw [localLaplacian_expansion_C2 hu g x hx]
  change (∑ i, ∑ j, (metricCoefficients g x (c x))⁻¹ i j *
    fderiv ℝ (fun y => fderiv ℝ f y (Module.finBasis ℝ E j)) (c x) (Module.finBasis ℝ E i)) +
      ∑ j, metricFirstCoefficient g x j (c x) * fderiv ℝ f (c x) (Module.finBasis ℝ E j) ≤ 0
  simp only [hm'.fderiv_eq_zero, _root_.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]
  exact localMax_hessian_contraction
    hf hm'
    (Module.finBasis ℝ E) (metricCoefficients_posDef g x hx).inv.posSemidef

theorem laplaceBeltrami_nonneg_at_localMin_C2 (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u) {x : M} (hm : IsLocalMin u x) :
    0 ≤ laplaceBeltrami g u x := by
  have h := laplaceBeltrami_nonpos_at_localMax_C2 g hu.neg hm.neg
  change laplaceBeltrami g (-u) x ≤ 0 at h
  rw [laplaceBeltrami_neg] at h
  linarith

theorem positive_shift_kernel_eq_zero_C2 [CompactSpace M] (g : SmoothMetric E M)
    {α : ℝ} (hα : 0 < α) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (he : ∀ x, α * u x - laplaceBeltrami g u x = 0) : u = 0 := by
  ext y
  obtain ⟨x, _, hmax⟩ := isCompact_univ.exists_isMaxOn (show (univ : Set M).Nonempty from ⟨y, mem_univ _⟩)
    hu.continuous.continuousOn
  have hl := laplaceBeltrami_nonpos_at_localMax_C2 g hu (hmax.isLocalMax (univ_mem))
  have hx : u x ≤ 0 := by nlinarith [he x]
  obtain ⟨z, _, hmin⟩ := isCompact_univ.exists_isMinOn (show (univ : Set M).Nonempty from ⟨y, mem_univ _⟩)
    hu.continuous.continuousOn
  have hl' := laplaceBeltrami_nonneg_at_localMin_C2 g hu (hmin.isLocalMin (univ_mem))
  have hz : 0 ≤ u z := (mul_nonneg_iff_of_pos_left hα).mp (by linarith [he z])
  exact le_antisymm ((hmax (mem_univ y)).trans hx) (hz.trans (hmin (mem_univ y)))


open Set Function Filter
open scoped Topology ContDiff

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma contMDiff_chartLift_order (q : M) (ξ : M → ℂ)
    (hξs : tsupport ξ ⊆ (chartAt E q).source)
    (hξ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ ξ) (N : ℕ)
    {f : E → ℂ} (hf : ContDiff ℝ N f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) N (chartLift (E := E) q ξ f) := by
  have hN : (N : ℕ∞ω) ≤ (∞ : ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl N
  apply contMDiff_of_tsupport
  intro x hx
  have hxs : x ∈ (chartAt E q).source := hξs (tsupport_mul_subset_left hx)
  exact ((ContinuousLinearMap.mul ℝ ℂ).contMDiff.contMDiffAt.comp x
    (hξ.of_le hN).contMDiffAt).clm_apply
    ((contMDiff_iff_contDiff.mpr hf).contMDiffAt.comp x
      ((contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hxs).of_le hN))


end

open Set Filter Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] [CompactSpace M] in
lemma ψ_mul_χ (i : A.t) (x : M) : A.ψ i x * A.χ i x = A.χ i x := by
  by_cases hx : A.χ i x = 0
  · simp only [hx, mul_zero]
  · rw [(A.one_ψ i).self_of_nhdsSet (subset_tsupport _ hx), Pi.one_apply, one_mul]

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] in
lemma χcoord_support (i : A.t) : tsupport (A.χcoord i) ⊆
    Metric.closedBall ((chartAt E (A.p i)) (A.p i)) (A.localInverse i).radius := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := tsupport_chartLocalize_image (A.p i) (A.χ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_χ i) hx
  exact Metric.closedBall_subset_closedBall (by linarith [(A.localInverse i).radius_pos])
    (Metric.ball_subset_closedBall (A.support_χ i hy).2)

omit [T2Space M] in
lemma χcoord_unit_support (i : A.t) {x : E} (hx : x ∈ tsupport (A.χcoord i)) :
    ‖(A.localInverse i).radius⁻¹ • (x - (chartAt E (A.p i)) (A.p i))‖ ≤ 1 := by
  have hh := A.χcoord_support i hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (A.localInverse i).radius_pos),
    inv_mul_le_iff₀ (A.localInverse i).radius_pos, mul_one]
  exact hh

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

omit [T2Space M] [CompactSpace M] in
lemma χ_mul_η (i : A.t) (x : M) : A.χ i x * A.η i x = A.η i x := by
  by_cases hx : A.η i x = 0
  · simp only [hx, mul_zero]
  · rw [(A.one_χ i).self_of_nhdsSet (subset_tsupport _ hx), Pi.one_apply, one_mul]

omit [T2Space M] in
lemma ψ_one_on_χcoord (i : A.t) {x : M} (hx : x ∈ (chartAt E (A.p i)).source)
    (hc : (chartAt E (A.p i)) x ∈ tsupport (A.χcoord i)) : A.ψ i x = 1 := by
  obtain ⟨y, hy, he⟩ := tsupport_chartLocalize_image (A.p i) (A.χ i) 1
    (HasCompactSupport.of_compactSpace _) (A.chart_χ i) hc
  have hxy : y = x := (chartAt E (A.p i)).injOn (A.chart_χ i hy) hx he
  subst y
  exact (A.one_ψ i).self_of_nhdsSet hy

end CompactMetricAtlas


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def transfer {l : ℕ} {ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))}
    (B : CompactMetricAtlas g l ht) (n : ℕ) :
    A.H (2 * (n : ℝ)) →L[ℝ] B.H (2 * (n : ℝ)) :=
  ∑ i, B.lift (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) n ∘L
    A.localize (2 * (n : ℝ)) i

end CompactMetricAtlas


end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RoundMetricExists
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
section Pullback
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def inducedMetric (f : M → F) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hDf : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    SmoothMetric E M where
  inner x := pullbackInner (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)
  symm x v w := real_inner_comm _ _
  pos x v hv := real_inner_self_pos.mpr (by
    intro h
    apply hv
    apply hDf x
    rw [map_zero]
    exact h)
  isVonNBounded x := pullbackInner_bounded (E := E) _ (hDf x)
  contMDiff := contMDiff_pullbackInner f hf

end Pullback


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_TransferAcross
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def transferAcross {g' : SmoothMetric E M} {l : ℕ}
    {ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))} (B : CompactMetricAtlas g' l ht) (n : ℕ) :
    A.H (2 * (n : ℝ)) →L[ℝ] B.H (2 * (n : ℝ)) :=
  ∑ i, B.lift (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) n ∘L
    A.localize (2 * (n : ℝ)) i

end CompactMetricAtlas
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ContinuousEigenpairLinearization
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace PositivePairing
variable (B : PositivePairing (X := X))

def perpendicular (u : X) : Submodule ℝ X := (B.form u).ker

instance perpendicular_complete (u : X) : CompleteSpace (B.perpendicular u) :=
  (B.form u).isClosed_ker.completeSpace_coe

omit [CompleteSpace X] in
lemma perpendicular_invariant (T : X →L[ℝ] X)
    (hsym : ∀ x y, B.form (T x) y = B.form x (T y))
    {μ : ℝ} {u : X} (hu : T u = μ • u) :
    ∀ v ∈ B.perpendicular u, T v ∈ B.perpendicular u := by
  intro v hv
  change B.form u (T v) = 0
  change B.form u v = 0 at hv
  rw [← hsym, hu, map_smul, _root_.smul_apply, hv, smul_zero]

end PositivePairing

end

section
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
namespace PositivePairing
variable (B : PositivePairing (X := X))

def eigenpairLinearization (T : X →L[ℝ] X) (μ : ℝ) (u : X) :
    (ℝ × X) →L[ℝ] (ℝ × X) :=
  ((B.form u).comp (ContinuousLinearMap.snd ℝ ℝ X)).prod
    (((T - μ • 1).comp (ContinuousLinearMap.snd ℝ ℝ X)) -
      (ContinuousLinearMap.toSpanSingleton ℝ u).comp (ContinuousLinearMap.fst ℝ ℝ X))

def eigenpairMap (u : X) (p : EigenpairParameters (X := X)) : EigenpairParameters (X := X) :=
  (p.1, (B.form u p.2.2, p.1 p.2.2 - p.2.1 • p.2.2))

def eigenpairDerivative (T : X →L[ℝ] X) (μ : ℝ) (u : X) :
    EigenpairParameters (X := X) →L[ℝ] EigenpairParameters (X := X) :=
  let F := ContinuousLinearMap.fst ℝ (X →L[ℝ] X) (ℝ × X)
  let S := ContinuousLinearMap.snd ℝ (X →L[ℝ] X) (ℝ × X)
  F.prod (((B.eigenpairLinearization T μ u).comp S) +
    (0 : EigenpairParameters (X := X) →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.apply ℝ X u).comp F))

end PositivePairing

end

open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_PositiveIntegral
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff BoundedContinuousFunction CompactlySupported
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
namespace MetricIntegralAtlas
variable (I : MetricIntegralAtlas (E := E) (M := M)) (g : SmoothMetric E M)

def positiveIntegral : C_c(M,ℝ) →ₚ[ℝ] ℝ where
  toFun f := I.integral g f.toBoundedContinuousFunction
  map_add' f h := by
    change I.integral g (f.toBoundedContinuousFunction+h.toBoundedContinuousFunction) = _
    exact I.integral_add g _ _
  map_smul' c f := by
    change I.integral g (c • f.toBoundedContinuousFunction) = _
    exact I.integral_smul g c _
  monotone' f h hfh := I.integral_mono g hfh

def volumeMeasure : Measure M := RealRMK.rieszMeasure (I.positiveIntegral g)

instance volumeMeasure_finite : IsFiniteMeasure (I.volumeMeasure g) := by
  unfold volumeMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance volumeMeasure_openPos : Measure.IsOpenPosMeasure (I.volumeMeasure g) := by
  constructor
  intro O hO hne
  obtain ⟨x,hx⟩ := hne
  obtain ⟨V,hV,hxV,hVO⟩ := normal_exists_closure_subset isClosed_singleton hO
    (singleton_subset_iff.mpr hx)
  obtain ⟨χ,hχ1,hχ0,hχb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ,E)) (n := ⊤) isClosed_singleton (t := V)
    (by simpa only [hV.interior_eq] using hxV)
  have hs : tsupport (fun y => χ y) ⊆ O := by
    apply (closure_mono (show support (fun y => χ y) ⊆ V from ?_)).trans hVO
    intro y hy
    by_contra hn
    exact hy (hχ0 y hn)
  have hx1 : χ x = 1 := hχ1.self_of_nhdsSet x (mem_singleton x)
  let f : C_c(M,ℝ) := ⟨⟨χ,χ.property.continuous⟩,HasCompactSupport.of_compactSpace _⟩
  have hp : 0 < I.positiveIntegral g f := I.integral_pos g
    (fun y => (hχb y).1) ⟨x,by change 0 < χ x; rw [hx1]; norm_num⟩
  exact ((ENNReal.ofReal_pos.mpr hp).trans_le
    (RealRMK.le_rieszMeasure_tsupport_subset (I.positiveIntegral g) (f := f) (fun y => hχb y) hs)).ne'

end MetricIntegralAtlas
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_FourThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

def threeBackgroundMetric : SmoothMetric ThreeModel ThreeManifold :=
  inducedMetric threeImmersion threeImmersion_smooth threeImmersion_injective

end


open Set Filter Manifold Bundle Function
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_SphericalPinFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
local instance sphericalAmbientFormNorm : NormedAddCommGroup (MetricForm (Euclidean 3)) := inferInstanceAs (NormedAddCommGroup (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
local instance sphericalAmbientFormSpace : NormedSpace ℝ (MetricForm (Euclidean 3)) := inferInstanceAs (NormedSpace ℝ (Euclidean 3 →L[ℝ] Euclidean 3 →L[ℝ] ℝ))
def sphericalTensorSupport : Compacts (Euclidean 3) :=
  ⟨sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
    sphericalCoverage_compact sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole (by norm_num)⟩
abbrev SphericalTensor := 𝓓_{sphericalTensorSupport}(Euclidean 3,MetricForm (Euclidean 3))
end


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
def SphericalSimple (g : SmoothMetric (Euclidean 3) (Sphere 3)) (u : Sphere 3 → ℝ) (lam : ℝ) : Prop :=
  ∀ v, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v →
    (∀ x, -laplaceBeltrami g v x=lam*v x) → ∃ c : ℝ, v=fun x => c*u x

def SphericalLargeWitness (g : SmoothMetric (Euclidean 3) (Sphere 3)) (A B : ℝ) : Prop :=
  ∃ k : ℕ, 3 ≤ k ∧ ∃ e : ℝ, ∃ u : Sphere 3 → ℝ,
    B < e ∧ e < 2*(k:ℝ)^2 ∧ ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
      (∀ x, -laplaceBeltrami g u x=e*u x) ∧ SphericalRegular u ∧ SphericalSignAbove u (A*(k:ℝ))
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_SphericalOpenFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions
namespace YauCounterexamples
def sphericalPositiveSet (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) : Set SphericalTensor :=
  {H | chartTensorPositive g₀ sourcePole sphericalTensorSupport H}
abbrev SphericalPositiveTensor (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) := sphericalPositiveSet g₀

def SphericalMetricGood (g : SmoothMetric (Euclidean 3) (Sphere 3)) : Prop :=
  g ∈ sphericalProfileMetricNeighborhood ∧
    ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
        ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2
end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

local instance threeTransportNormedSpace_r9b3c0c_1 : NormedSpace ℝ ThreeModel := inferInstance
attribute [local instance] OAI.YauCounterexamples.threeTransportContinuousSMul
def threeNormalEquiv : NormalWaveSpace ≃L[ℝ] ThreeModel := by
  letI : ContinuousSMul ℝ NormalWaveSpace := IsBoundedSMul.continuousSMul
  exact ContinuousLinearEquiv.ofFinrankEq (by simpa [NormalWaveSpace] using threeModel_finrank.symm)
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

def threeNormalInv : NormalWaveSpace → ThreeManifold :=
  (chartAt ThreeModel threeProfileCenter).symm ∘ threeNormalEquiv
end


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

def ThreeCleanBall (R : ℝ) : Prop := ∀ y∈closedBall (0:NormalWaveSpace) R,
  1/2≤‖productA (threeNormalInv y).1‖ ∧ ‖productA (threeNormalInv y).1‖≤3/4
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeCutoffControlBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
def ThreeAnnulus (d e : ℝ) : Set ThreeManifold :=
  (threeNormalInv '' closedBall 0 e) \ (threeNormalInv '' ball 0 d)
end


open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeFixedFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions
local instance threeAmbientFormNorm : NormedAddCommGroup (MetricForm ThreeModel) := inferInstanceAs (NormedAddCommGroup (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
local instance threeAmbientFormSpace : NormedSpace ℝ (MetricForm ThreeModel) := inferInstanceAs (NormedSpace ℝ (ThreeModel →L[ℝ] ThreeModel →L[ℝ] ℝ))
def threeTensorSupport (R : ℝ) : Compacts ThreeModel :=
  ⟨threeNormalEquiv '' closedBall 0 (R/2), (isCompact_closedBall _ _).image threeNormalEquiv.continuous⟩
abbrev ThreeTensor (R : ℝ) := 𝓓_{threeTensorSupport R}(ThreeModel,MetricForm ThreeModel)
def ThreeExterior (g : SmoothMetric ThreeModel ThreeManifold) (r : ℝ) : Prop :=
  ∀ q∉threeNormalInv '' closedBall 0 r, g.inner q=threeBackgroundMetric.inner q
lemma ThreeExterior.mono {g : SmoothMetric ThreeModel ThreeManifold} {r s : ℝ}
    (he : ThreeExterior g r) (hrs : r ≤ s) : ThreeExterior g s := by
  intro q hq
  exact he q (fun hh => hq (image_mono (closedBall_subset_closedBall hrs) hh))
def threePositiveSet (R : ℝ) : Set (ThreeTensor R) :=
  {H | chartTensorPositive threeBackgroundMetric threeProfileCenter (threeTensorSupport R) H}
abbrev ThreePositiveTensor (R : ℝ) := threePositiveSet R
end


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral Metric
open scoped Topology ContDiff Distributions ENNReal NNReal
def ThreeSimple (g : SmoothMetric ThreeModel ThreeManifold) (u : ThreeManifold → ℝ) (lam : ℝ) : Prop :=
  ∀ v, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v →
    (∀ x, -laplaceBeltrami g v x=lam*v x) → ∃ c : ℝ, v=fun x => c*u x
end


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
def ThreeSignAbove (R : ℝ) (u : ThreeManifold → ℝ) (L : ℝ) : Prop :=
  ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I⊆Metric.closedBall 0 (R/2) ∧
  ∃ partition : TaggedPrepartition I, partition.IsPartition ∧
    ∃ d : {J : Box (Fin 3) // J ∈ partition.boxes} → ℝ, (∀ j, 0 < d j) ∧
      ENNReal.ofReal L < SignTests.signCertificate (fun j => Box.Ioo j.val) d
        ((u ∘ threeNormalInv) ∘ normalWaveEquiv)
def ThreeLargeWitness (R : ℝ) (g : SmoothMetric ThreeModel ThreeManifold) (A B : ℝ) : Prop :=
  ∃ k : ℕ, 3  ≤  k ∧ ∃ e : ℝ, ∃ u : ThreeManifold → ℝ,
    B < e ∧ e < 4*(k:ℝ)^2 ∧ ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
      (∀ x, -laplaceBeltrami g u x=e*u x) ∧ ThreeRegular u ∧ ThreeSignAbove R u (A*(k:ℝ))
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end


