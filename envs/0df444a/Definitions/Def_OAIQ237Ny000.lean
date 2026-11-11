-- Prove2me | Definitions.Def_OAIQ237Ny000
-- name    : OAIQ237Ny000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:23.349788+00:00
-- url     : https://prove2.me/theorems/68876e12-bbce-419e-9d96-63b9f61b4acd
-- title:
--   Definitions bundle OAIQ237Ny000 of the split of OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 275 declarations of OpenAI's Lean: 205 definitions, 6 inductive types or structures, 2 instances and 62 theorems. The definitions and types are `OAI.Yau.Analysis.InUnitCube`, `OAI.Yau.Analysis.cubeControl`, `OAI.Yau.Analysis.partialDirs`, `OAI.Yau.Analysis.partialJet`, `OAI.Yau.Coord`, `OAI.Yau.Geometry.AdmissibleFrameTriple`, `OAI.Yau.Geometry.AdmissibleFrameTriple.alpha`, `OAI.Yau.Geometry.AdmissibleFrameTriple.beta`, `OAI.Yau.Geometry.AdmissibleFrameTriple.frame`, `OAI.Yau.Geometry.AdmissibleFrameTriple.pullback`, `OAI.Yau.Geometry.CoefficientDerivative`, `OAI.Yau.Geometry.CoefficientFirstJet`, `OAI.Yau.Geometry.CoefficientPoint`, `OAI.Yau.Geometry.CompactFrameCover`, `OAI.Yau.Geometry.CompactFrameCover.Parameter`, `OAI.Yau.Geometry.CompactFrameCover.center`, `OAI.Yau.Geometry.CompactFrameCover.triple`, `OAI.Yau.Geometry.JetAdmissible`, `OAI.Yau.Geometry.JetSpace`, `OAI.Yau.Geometry.LiteralNodalCertificate`, `OAI.Yau.Geometry.LocalCompactWaveData`, `OAI.Yau.Geometry.LocalCompactWaveData.latticeAlpha`, `OAI.Yau.Geometry.LocalCompactWaveData.latticeEnergy`, `OAI.Yau.Geometry.LocalCompactWaveData.latticeEta`, `OAI.Yau.Geometry.LocalCompactWaveData.latticeGoodEvent`, `OAI.Yau.Geometry.LocalCompactWaveData.latticePlaneWaveCoefficient`, `OAI.Yau.Geometry.LocalCompactWaveData.latticeRandomDual`, `OAI.Yau.Geometry.LocalCompactWaveData.latticeSeededJet`, `OAI.Yau.Geometry.LocalCompactWaveData.latticeSeededRandomDual`, `OAI.Yau.Geometry.LocalCompactWaveData.latticeSigma`, `OAI.Yau.Geometry.LocalCompactWaveData.latticeVariance`, `OAI.Yau.Geometry.LocalCompactWaveData.originalEta`, `OAI.Yau.Geometry.LocalCompactWaveData.withEnvelope`, `OAI.Yau.Geometry.MetricJet`, `OAI.Yau.Geometry.MetricWaveJetFamily`, `OAI.Yau.Geometry.NormalOperatorFamily`, `OAI.Yau.Geometry.QuadParam`, `OAI.Yau.Geometry.SourceCompactFrameCover`, `OAI.Yau.Geometry.SourceFrameTriple`, `OAI.Yau.Geometry.SourceGrid` and 171 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `NodalSets_Charts_AbsolutePiola`, `NodalSets_Charts_AdaptedChartFamilyLemmas`, `NodalSets_Charts_ChartHessianLemmas`, `NodalSets_Charts_ChartMetric`, `NodalSets_Charts_ChartPushforward`, `NodalSets_Charts_ChartedEnvelope`, `NodalSets_Charts_CompactFrameCover`, `NodalSets_Charts_ComplexMetricFlux`, `NodalSets_Charts_CorrugationFrozenFrame`, `NodalSets_Charts_CorrugationMetricError`, `NodalSets_Charts_CorrugationRotatingFrame`, `NodalSets_Charts_FiniteChartDerivativeSize`, `NodalSets_Charts_FrameCotangent`, `NodalSets_Charts_FrameMapFamily`, `NodalSets_Charts_ImmersionMetric`, `NodalSets_Charts_InvariantFrameInverse`, `NodalSets_Charts_InverseChartJets`, `NodalSets_Charts_InverseMetricJet`, `NodalSets_Charts_LocalFrameTriple`, `NodalSets_Charts_LocalMetricJetContinuityLemmas`, `NodalSets_Charts_LocalMetricJets`, `NodalSets_Charts_ManifoldMatrixSmooth`, `NodalSets_Charts_MetricConnectionFamilyLemmas`, `NodalSets_Charts_MetricFluxPullback`, `NodalSets_Charts_MetricFrameOps`, `NodalSets_Charts_MetricJetAdmissibility`, `NodalSets_Charts_NormalFramePhase`, `NodalSets_Charts_PiolaFlux`, `NodalSets_Charts_PositiveMetric`, `NodalSets_Charts_QuadraticChart`, `NodalSets_Charts_SmoothInverseChart`, `NodalSets_Charts_TangentGramDeterminant`, `NodalSets_Charts_TransformedDensity`, `NodalSets_Coefficients_CoefficientLocality`, `NodalSets_Coefficients_CoefficientMetricJets`, `NodalSets_Coefficients_CommonCoefficientExtension`, `NodalSets_Coefficients_ComplexChartCoefficient`, `NodalSets_Coefficients_CoordinateCorrection`, `NodalSets_Coefficients_DualWaveCoefficient`, `NodalSets_Coefficients_GaussianCoefficientTail`, `NodalSets_Coefficients_GaussianCoefficientVariance`, `NodalSets_Coefficients_MetricWaveJets`, `NodalSets_Elliptic_AnchoredCubeBound`, `NodalSets_Elliptic_BallPacking`, `NodalSets_Elliptic_BasisLaplacian`, `NodalSets_Elliptic_CompactNormalOperator`, `NodalSets_Elliptic_CompactSmoothExtension`, `NodalSets_Elliptic_ContinuousPolynomialFamily`, `NodalSets_Elliptic_CoordinateMatrixEllipticity`, `NodalSets_Elliptic_CoordinateNorm`, `NodalSets_Elliptic_CoordinatePartialJets`, `NodalSets_Elliptic_CoordinateTransverseDisk`, `NodalSets_Elliptic_CorrugationAnnulusBoxes`, `NodalSets_Elliptic_CorrugationAnnulusPacking`, `NodalSets_Elliptic_CorrugationAssembly`, `NodalSets_Elliptic_CorrugationCubePartition`, `NodalSets_Elliptic_CorrugationCutoff`, `NodalSets_Elliptic_CorrugationDiskWell`, `NodalSets_Elliptic_CorrugationFixedAmplitude`, `NodalSets_Elliptic_CorrugationFixedCutoff`, `NodalSets_Elliptic_CorrugationFrequencyScale`, `NodalSets_Elliptic_CorrugationGlobalJets`, `NodalSets_Elliptic_CorrugationGridAssembly`, `NodalSets_Elliptic_CorrugationGridNonvanishing`, `NodalSets_Elliptic_CorrugationHighRegime`, `NodalSets_Elliptic_CorrugationLeadingVector`, `NodalSets_Elliptic_CorrugationNormalizedGradient`, `NodalSets_Elliptic_CorrugationOldData`, `NodalSets_Elliptic_CorrugationPeriodicWell`, `NodalSets_Elliptic_CorrugationRadialJetsLemmas`, `NodalSets_Elliptic_CorrugationRegimeBounds`, `NodalSets_Elliptic_CorrugationWellBound`, `NodalSets_Elliptic_CorrugationWellChoice`, `NodalSets_Elliptic_CorrugationWellSlope`, `NodalSets_Elliptic_EnvelopeContactJet`, `NodalSets_Elliptic_EnvelopeRegion`, `NodalSets_Elliptic_FiniteAmplitude`, `NodalSets_Elliptic_FirstJetGoodEvent`, `NodalSets_Elliptic_FirstJetNonvanishing`, `NodalSets_Elliptic_FirstJetSize`, `NodalSets_Elliptic_FrozenPhaseLemmas`, `NodalSets_Elliptic_IndependentWeightedMatrix`, `NodalSets_Elliptic_InitialPhasePolynomial`, `NodalSets_Elliptic_JacobianCalculus`, `NodalSets_Elliptic_LocalLogJetBounds`, `NodalSets_Elliptic_LocalMatrixSmooth`, `NodalSets_Elliptic_LocalSpatialJet`, `NodalSets_Elliptic_LocalizedCorrugation`, `NodalSets_Elliptic_OperatorLocality`, `NodalSets_Elliptic_PhaseJet`, `NodalSets_Elliptic_PolynomialEvaluation`, `NodalSets_Elliptic_PositiveBilinearBound`, `NodalSets_Elliptic_QuadraticFamily`, `NodalSets_Elliptic_RadialVolumeMatrix`, `NodalSets_Elliptic_RealPhaseJet`, `NodalSets_Elliptic_RecursiveJet`, `NodalSets_Elliptic_SeedJetLowerBound`, `NodalSets_Elliptic_SignScaleSeed`, `NodalSets_Elliptic_SmoothBeamJet`, `NodalSets_Elliptic_SmoothBilinearPullback`, `NodalSets_Elliptic_SmoothCutoff`, `NodalSets_Elliptic_SmoothJet`, `NodalSets_Elliptic_SmoothTransportJet`, `NodalSets_Elliptic_TransformedDrift`, `NodalSets_Elliptic_TransportedOperator`, `NodalSets_Elliptic_UniformContact`, `NodalSets_Elliptic_UniformPolynomial`, `NodalSets_Elliptic_UniformSmoothBounds`, `NodalSets_Elliptic_UniformTripleBounds`, `NodalSets_Elliptic_WeightedDivergenceInvariance`, `NodalSets_Hausdorff_LiteralNodalCertificate`, `NodalSets_Hausdorff_PhysicalNodalCylinder`, `NodalSets_Spectral_NormalOrthonormalChart`, `NodalSets_Waves_CompactSourceWaves`, `NodalSets_Waves_ConstructedCoordinateWaves`, `NodalSets_Waves_GaussianCompactSections`, `NodalSets_Waves_GaussianGradientSupremum`, `NodalSets_Waves_GaussianJet`, `NodalSets_Waves_GaussianWaveJet`, `NodalSets_Waves_LatticeCovariance`, `NodalSets_Waves_LatticeCovariance2`, `NodalSets_Waves_LatticeDirectionalCenters`, `NodalSets_Waves_LatticeEnergyLowerBound`, `NodalSets_Waves_LatticeFullPlaneWaveApprox`, `NodalSets_Waves_LatticeGaussianSmallBall`, `NodalSets_Waves_LatticeGeometry`, `NodalSets_Waves_LatticeGoodEvent`, `NodalSets_Waves_LatticeLogJets`, `NodalSets_Waves_LatticeNormalizedWeights`, `NodalSets_Waves_LatticeSourceWaves`, `NodalSets_Waves_LatticeVarianceUpper`, `NodalSets_Waves_LocalCompactWaves`, `NodalSets_Waves_LocalSourceWaveTransfer`, `NodalSets_Waves_LocalWaveEnvelopeTransfer`, `NodalSets_Waves_NormalizedWaveRatio`, `NodalSets_Waves_SmoothWaveOperator`, `NodalSets_Waves_TripleSourceWaves`, `NodalSets_Waves_TripleWaveParameters`, `NodalSets_Waves_UniformActualWaveSize`, `NodalSets_Waves_WaveCenterJets`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ237Ny002` and `OAIQ237Ny003`; the statements `OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball`, `OAI.Yau.Geometry.LocalCompactWaveData.lattice_good_event_probability`, `OAI.Yau.Geometry.NormalOperatorFamily.solve_jets`, `OAI.Yau.Geometry.TripleSourceWaveData.real_defect_second`, `OAI.Yau.Geometry.compact_actual_metric_wave_jets`, `OAI.Yau.Geometry.construct_triple_source_waves`, `OAI.Yau.Geometry.constructed_coordinate_wave_estimates`, `OAI.Yau.Geometry.corrugation_actual_low_gradient`, `OAI.Yau.Geometry.corrugation_actual_metric_unit_errors`, `OAI.Yau.Geometry.corrugation_grid_admissibility`, `OAI.Yau.Geometry.corrugation_grid_integrated_gain`, `OAI.Yau.Geometry.corrugation_speed_freezing` and `OAI.Yau.Geometry.lattice_physical_sign_subballs_fixed_domain`; the proof of `OAI.Yau.Geometry.LocalCompactWaveData.lattice_good_event_probability`.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor

section
-- module Solutions.OAIQ237_NY.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_QuadraticChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def quadraticChartMap (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (x : E) : E :=
  y + e x - (1/2:ℝ) • B x x

lemma quadraticChartMap_smooth (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    ContDiff ℝ ∞ (quadraticChartMap y e B) := by
  exact (contDiff_const.add e.contDiff).sub
    (B.contDiff.clm_apply contDiff_id |>.const_smul (1/2:ℝ))

lemma quadraticChartMap_hasFDerivAt (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) (x : E) :
    HasFDerivAt (quadraticChartMap y e B)
      (e.toContinuousLinearMap - (1/2:ℝ) • (B.flip x + B x)) x := by
  have h := (B.hasFDerivAt.clm_apply (hasFDerivAt_id x))
  convert ((hasFDerivAt_const y x).add e.hasFDerivAt).sub (h.const_smul (1/2:ℝ)) using 1 <;>
    simp [add_comm]
  funext z
  simp [quadraticChartMap, add_comm]

lemma quadraticChartMap_deriv_zero (y : E) (e : E ≃L[ℝ] E)
    (B : E →L[ℝ] E →L[ℝ] E) :
    HasFDerivAt (quadraticChartMap y e B) e.toContinuousLinearMap 0 := by
  simpa using quadraticChartMap_hasFDerivAt y e B 0

variable [CompleteSpace E]

def quadraticChart (y : E) (e : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    OpenPartialHomeomorph E E :=
  (quadraticChartMap_smooth y e B).contDiffAt.toOpenPartialHomeomorph
    (quadraticChartMap y e B) (quadraticChartMap_deriv_zero y e B) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance clmTopology {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    TopologicalSpace (E →L[ℝ] F) :=
  (ContinuousLinearMap.toNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] F)).toUniformSpace.toTopologicalSpace
local instance clmAdd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    AddCommGroup (E →L[ℝ] F) :=
  (ContinuousLinearMap.toNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] F)).toAddCommGroup
local instance clmModule {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Module ℝ (E →L[ℝ] F) :=
  (ContinuousLinearMap.toNormedSpace : NormedSpace ℝ (E →L[ℝ] F)).toModule

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartHessianLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def christoffelCovector (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1/2:ℝ) • (D + D.flip -
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp D.flip)

def christoffelTensor (m : E ≃L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E m.symm.toContinuousLinearMap).comp
    (christoffelCovector D)

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_PositiveMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

lemma dual_continuous_finrank : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).finrank_eq]
  exact Subspace.dual_finrank_eq

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricConnectionFamilyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

def metricConnection (g : E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (ContinuousLinearMap.inverse g)).comp
    (christoffelCovector D)

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RecursiveJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
abbrev CPoly := MvPolynomial (Fin 4) ℂ
abbrev Jet := ℕ → CPoly

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PolynomialEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section
abbrev Coord := Fin 4 → ℝ

def reval (p : CPoly) : Coord → ℂ := fun x ↦ eval (fun i ↦ (x i : ℂ)) p

def coordPartial (i : Fin 4) (f : Coord → ℂ) (x : Coord) : ℂ :=
  fderiv ℝ f x (Pi.single i 1)

def smoothSecondOrder (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (f : Coord → ℂ) (x : Coord) : ℂ :=
  (∑ i, ∑ j, g i j x * coordPartial i (coordPartial j f) x) + ∑ i, b i x * coordPartial i f x

def smoothEikonal (g : Fin 4 → Fin 4 → Coord → ℂ) (f : Coord → ℂ) (x : Coord) : ℂ :=
  (∑ i, ∑ j, g i j x * coordPartial i f x * coordPartial j f x) + 4

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def FlatAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Coord → F) (x : Coord) : Prop :=
  ∀ k, k ≤ n → iteratedFDeriv ℝ k f x = 0

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Spectral_NormalOrthonormalChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def frameConnection (B : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) :
    _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord :=
  (((ContinuousLinearMap.compL ℝ _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord).flip e.toContinuousLinearMap).comp B).comp
    e.toContinuousLinearMap

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricFrameOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def metricNormalize (g : E →L[ℝ] E →L[ℝ] ℝ) (v : E) : E :=
  (Real.sqrt (g v v))⁻¹ • v

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FrameMapFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def frameMap (e : Fin 4 → _root_.OAI.Yau.Jets.Coord) : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord :=
  ∑ i : Fin 4, (ContinuousLinearMap.proj i).smulRight (e i)

lemma frameMap_apply (e : Fin 4 → _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) : frameMap e x = ∑ i, x i • e i := by
  simp [frameMap]

lemma frameMap_pair (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (e : Fin 4 → _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e i) (e j) = if i = j then 1 else 0) (x : _root_.OAI.Yau.Jets.Coord) (i : Fin 4) :
    g (e i) (frameMap e x) = x i := by
  simp [frameMap_apply, map_sum, he, mul_ite]

lemma frameMap_injective (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (e : Fin 4 → _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e i) (e j) = if i = j then 1 else 0) : Function.Injective (frameMap e) := by
  intro x y hxy
  ext i
  rw [← frameMap_pair g e he x i, ← frameMap_pair g e he y i, hxy]

def frameEquiv (g : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (e : Fin 4 → _root_.OAI.Yau.Jets.Coord)
    (he : ∀ i j, g (e i) (e j) = if i = j then 1 else 0) : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord :=
  ((frameMap e).toLinearMap.linearEquivOfInjective (frameMap_injective g e he) rfl).toContinuousLinearEquiv

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_QuadraticFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev QuadParam (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E × ((E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E))

def rawQuadratic (p : QuadParam E) (x : E) : E :=
  p.1 + p.2.1 x - (1/2:ℝ) • p.2.2 x x

def pulledForm (g : E → E →L[ℝ] E →L[ℝ] ℝ) (p : QuadParam E) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  let J := fderiv ℝ (rawQuadratic p) x
  (((ContinuousLinearMap.compL ℝ E E ℝ).flip J).comp (g (rawQuadratic p x))).comp J

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_AdaptedChartFamilyLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open Filter
open scoped ContDiff Topology
open Yau.Jets
attribute [local instance] clmTopology clmAdd clmModule

def actualFrameConnection (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (y : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord :=
  frameConnection (metricConnection (g y) (fderiv ℝ g y)) e

def actualMetricChart (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (y : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord :=
  quadraticChart y e (actualFrameConnection g y e)

end

open Set Filter
open scoped ContDiff Topology
variable {T E F : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E]
  [TopologicalSpace F]

lemma compact_family_common_radius {s : Set T} (hs : IsCompact s)
    (f : T × E → F) (hf : Continuous f) {V : Set F} (hV : IsOpen V)
    (h0 : ∀ t ∈ s, f (t,0) ∈ V) :
    ∃ r > 0, ∀ t ∈ s, ∀ x : E, ‖x‖ < r → f (t,x) ∈ V := by
  obtain ⟨U,W,_,hW,hsU,h0W,hUW⟩ := generalized_tube_lemma hs (isCompact_singleton (x := (0:E)))
    (hV.preimage hf) (by rintro ⟨t,x⟩ ⟨ht,hx⟩; obtain rfl := mem_singleton_iff.mp hx; exact h0 t ht)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds (h0W (mem_singleton 0)))
  refine ⟨r,hr,fun t ht x hx ↦ hUW ⟨hsU ht, hball ?_⟩⟩
  simpa only [Metric.mem_ball, dist_zero_right] using hx

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PhaseJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section

def contactEta (a b h00 h11 : ℝ) : ℝ :=
  (a ^ 2 * h00 + b ^ 2 * h11) / (a ^ 2 + b ^ 2)

def imaginaryHessian (a b : ℝ) (H : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j ↦
  if i = 0 then -(b / a) * H 1 j
  else if i = 1 then (a / b) * H 0 j
  else if j = 0 then -(b / a) * H 1 i
  else if j = 1 then (a / b) * H 0 i
  else 0

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section
variable {T ι : Type*} [TopologicalSpace T] [Fintype ι]

def polynomialFamily (p : ι → CPoly) (c : T → ι → ℂ) (t : T) : Coord → ℂ :=
  fun x ↦ ∑ i, c t i • reval (p i) x

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ContinuousPolynomialFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

def ContinuousPolyFamily (P : T → CPoly) : Prop :=
  (∀ d, Continuous (fun t ↦ (P t).coeff d)) ∧
    ∃ s : Finset (Fin 4 →₀ ℕ), ∀ t, (P t).support ⊆ s

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_InitialPhasePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def linearPhase (v : Fin 4 → ℂ) : CPoly := ∑ i, C (v i) * X i

def quadraticPhase (H : Fin 4 → Fin 4 → ℂ) : CPoly :=
  C (1/2 : ℂ) * ∑ i, ∑ j, C (H i j) * X i * X j

def initialPhaseJet (S : ℝ) (v : Fin 4 → ℂ) (H : Fin 4 → Fin 4 → ℂ) : Jet :=
  fun k ↦ if k = 0 then C (S : ℂ) else if k = 1 then linearPhase v
    else if k = 2 then quadraticPhase H else 0

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_NormalFramePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

def normalFrameVector (a b : ℝ) : Fin 4 → ℂ := ![(a:ℂ), (b:ℂ)*Complex.I, 0, 0]

def normalRealHessian (a b : ℝ) (H : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j ↦ H i j - if i = j then Yau.contactEta a b (H 0 0) (H 1 1) else 0

def normalComplexHessian (a b : ℝ) (H : Fin 4 → Fin 4 → ℝ) : Fin 4 → Fin 4 → ℂ :=
  fun i j ↦ (normalRealHessian a b H i j : ℂ) +
    (Yau.imaginaryHessian a b (normalRealHessian a b H) i j : ℂ) * Complex.I

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Set Filter
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma compact_positive_bounds {s : Set T} (hs : IsCompact s) (f : T → ℝ)
    (hf : ContinuousOn f s) (hpos : ∀ t ∈ s, 0 < f t) :
    ∃ c > 0, ∃ C > 0, ∀ t ∈ s, c ≤ f t ∧ f t ≤ C := by
  by_cases hn : s.Nonempty
  · obtain ⟨u, hu, hmin⟩ := hs.exists_isMinOn hn hf
    obtain ⟨v, hv, hmax⟩ := hs.exists_isMaxOn hn hf
    exact ⟨f u, hpos u hu, f v, hpos v hv, fun t ht ↦ ⟨hmin ht, hmax ht⟩⟩
  · refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
    intro t ht
    exact (hn ⟨t, ht⟩).elim

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothTransportJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def smoothTransport (W : Fin 4 → Coord → ℂ) (c f a : Coord → ℂ) : Coord → ℂ :=
  fun x ↦ (∑ i, W i x * coordPartial i a x) + c x * a x - f x

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothBeamJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def smoothBeamVector (g : Fin 4 → Fin 4 → Coord → ℂ) (phi : Coord → ℂ)
    (i : Fin 4) : Coord → ℂ := fun x ↦ 2 * ∑ j, g i j x * coordPartial j phi x

def smoothBeamScalar (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (phi : Coord → ℂ) : Coord → ℂ := fun x ↦ smoothSecondOrder g b phi x + 6

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def finiteAmplitude (A : ℕ → CPoly) (J : ℕ) (N : ℝ) : Coord → ℂ :=
  polynomialFamily (fun j : Fin (J + 1) ↦ A j.val)
    (fun t : ℝ ↦ fun j : Fin (J + 1) ↦ (t : ℂ) ^ j.val) N⁻¹

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EnvelopeContactJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

def envelopeHessian (S : Coord → ℝ) (i j : Fin 4) : ℝ :=
  fderiv ℝ (fderiv ℝ S) 0 (Pi.single j 1) (Pi.single i 1)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_InverseMetricJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def inverseChartCoeff (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (y : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (i j : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  (ContinuousLinearMap.inverse
    (pulledForm g (y,e.toContinuousLinearMap,actualFrameConnection g y e) x)
    (ContinuousLinearMap.proj j)) i

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalSpatialJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [CompleteSpace E]

def inversePulledForm (g : E → E →L[ℝ] E →L[ℝ] ℝ) (p : QuadParam E) (x : E) :
    (E →L[ℝ] ℝ) →L[ℝ] E := ContinuousLinearMap.inverse (pulledForm g p x)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TransformedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def coordDet (J : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord) : ℝ :=
  Matrix.det (fun i j : Fin 4 ↦ (J (Pi.single j 1)) i)

def chartDensity (w : _root_.OAI.Yau.Jets.Coord → ℝ) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  w (rawQuadratic p x) * |coordDet (fderiv ℝ (rawQuadratic p) x)|

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CommonCoefficientExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
noncomputable section
variable {P E F T : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace T]

def cutoffCoefficient (beta : E → ℝ) (f : P → E → F) (p : P) (x : E) : F :=
  beta x • f p x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransformedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def chartPrincipal (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (i j : Fin 4) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  (inversePulledForm g p x (ContinuousLinearMap.proj j)) i

def chartFlux (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (i j : Fin 4) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  chartDensity w p x * chartPrincipal g i j p x

def chartDrift (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (j : Fin 4) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  (chartDensity w p x)⁻¹ * ∑ i, fderiv ℝ (chartFlux g w i j p) x (Pi.single i 1)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_ComplexChartCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def complexPrincipal (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (i j : Fin 4) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) : ℂ := chartPrincipal g i j p x

def complexDrift (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (j : Fin 4) (p : QuadParam _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) : ℂ := chartDrift g w j p x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_SmoothWaveOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def waveExp (phi : Coord → ℂ) (N : ℝ) : Coord → ℂ :=
  fun x ↦ Complex.exp ((N : ℂ) * phi x)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_JacobianCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

def jacobian (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ (fderiv ℝ F x (Pi.single j 1)) i

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_PiolaFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

def complexDivergence (V : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  ∑ i, coordPartial i (V i) x

def signedPiola (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (V : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ)
    (i : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  ∑ a, ((jacobian F x).adjugate i a : ℂ) * V a (F x)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_AbsolutePiola
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section

def absolutePiola (F : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) (V : Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ)
    (i : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  (|(jacobian F x).det| / (jacobian F x).det : ℝ) * signedPiola F V i x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartPushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def chartPushforward (F : OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord) (u : _root_.OAI.Yau.Jets.Coord → ℂ)
    (z : _root_.OAI.Yau.Jets.Coord) : ℂ := by
  classical
  exact if z ∈ F.target then u (F.symm z) else 0

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ChartedEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def metricGradient (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (y : _root_.OAI.Yau.Jets.Coord) : _root_.OAI.Yau.Jets.Coord :=
  ContinuousLinearMap.inverse (g y) (fderiv ℝ S y)

def sourceHessian (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : _root_.OAI.Yau.Jets.Coord) : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ S) y -
    (ContinuousLinearMap.compL ℝ _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord ℝ (fderiv ℝ S y)).comp
      (metricConnection (g y) (fderiv ℝ g y))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalFrameTriple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

structure AdmissibleFrameTriple
    (g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (p : T → _root_.OAI.Yau.Jets.Coord) where
  q : T → Fin 3 → _root_.OAI.Yau.Jets.Coord
  continuous_q : Continuous q
  independent : ∀ t, LinearIndependent ℝ (q t)
  perpendicular : ∀ t j, g t (p t) (q t j) = 0
  length : ∀ t j, g t (q t j) (q t j) = g t (p t) (p t)+4
  strict : ∀ t j, 0 < H t (p t) (p t)+H t (q t j) (q t j)
  e : T → Fin 3 → Fin 4 → _root_.OAI.Yau.Jets.Coord
  continuous_e : ∀ j i, Continuous (fun t ↦ e t j i)
  orthonormal : ∀ t j i k, g t (e t j i) (e t j k) = if i=k then 1 else 0
  first : ∀ t j, e t j 0 = metricNormalize (g t) (p t)
  second : ∀ t j, e t j 1 = metricNormalize (g t) (q t j)

def AdmissibleFrameTriple.pullback {R : Type*} [TopologicalSpace R]
    {g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {p : T → _root_.OAI.Yau.Jets.Coord}
    (d : AdmissibleFrameTriple g H p) (f : R → T) (hf : Continuous f) :
    AdmissibleFrameTriple (g ∘ f) (H ∘ f) (p ∘ f) where
  q := d.q ∘ f
  continuous_q := d.continuous_q.comp hf
  independent r := d.independent (f r)
  perpendicular r := d.perpendicular (f r)
  length r := d.length (f r)
  strict r := d.strict (f r)
  e := d.e ∘ f
  continuous_e j i := (d.continuous_e j i).comp hf
  orthonormal r := d.orthonormal (f r)
  first r := d.first (f r)
  second r := d.second (f r)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CompactFrameCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

structure CompactFrameCover
    (g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (p : T → _root_.OAI.Yau.Jets.Coord) where
  indices : Finset T
  patch : T → Set T
  compact_patch : ∀ i, IsCompact (patch i)
  covers : ∀ t, ∃ i ∈ indices, t ∈ patch i
  data : ∀ i, AdmissibleFrameTriple (fun t : patch i ↦ g t)
    (fun t : patch i ↦ H t) (fun t : patch i ↦ p t)

namespace CompactFrameCover
variable {g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {p : T → _root_.OAI.Yau.Jets.Coord}
variable (d : CompactFrameCover g H p)
def Parameter := Σ i : d.indices, d.patch i
instance instTopologicalSpaceParameter : TopologicalSpace d.Parameter := inferInstanceAs (TopologicalSpace (Σ i : d.indices, d.patch i))
instance instCompactSpaceParameter : CompactSpace d.Parameter := by
  let (i : d.indices) : CompactSpace (d.patch i) := isCompact_iff_compactSpace.mp (d.compact_patch i)
  exact inferInstanceAs (CompactSpace (Σ i : d.indices, d.patch i))
def center (t : d.Parameter) : T := t.2.val
lemma continuous_center : Continuous d.center := by
  apply continuous_sigma
  intro i
  exact continuous_subtype_val
lemma surjective_center : Function.Surjective d.center := by
  intro t
  obtain ⟨i,hi,ht⟩ := d.covers t
  exact ⟨⟨⟨i,hi⟩,⟨t,ht⟩⟩,rfl⟩

def triple : AdmissibleFrameTriple (g ∘ d.center) (H ∘ d.center) (p ∘ d.center) where
  q t := (d.data t.1).q t.2
  continuous_q := continuous_sigma (fun i ↦ (d.data i).continuous_q)
  independent t := (d.data t.1).independent t.2
  perpendicular t := (d.data t.1).perpendicular t.2
  length t := (d.data t.1).length t.2
  strict t := (d.data t.1).strict t.2
  e t := (d.data t.1).e t.2
  continuous_e j k := continuous_sigma (fun i ↦ (d.data i).continuous_e j k)
  orthonormal t := (d.data t.1).orthonormal t.2
  first t := (d.data t.1).first t.2
  second t := (d.data t.1).second t.2
end CompactFrameCover

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricFluxPullback
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def sourcePrincipal (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (i j : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  (ContinuousLinearMap.inverse (g x) (ContinuousLinearMap.proj j)) i

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ComplexMetricFlux
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def sourceFlux (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (i : Fin 4) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  ∑ j, ((w x : ℂ) * (sourcePrincipal g i j x : ℂ)) * coordPartial j u x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PositiveBilinearBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set Bornology Yau.Jets
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma positive_bilinear_coercive (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) :
    ∃ c > 0, ∀ v, c * ‖v‖^2 ≤ g v v := by
  obtain ⟨c,hc,_,_,hb⟩ := compact_positive_bounds
    (isCompact_sphere (0:E) 1) (fun v ↦ g v v)
    ((g.continuous.clm_apply continuous_id).continuousOn)
    (fun v hv ↦ hp v (by intro he; simp [he] at hv))
  refine ⟨c,hc,fun v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hh := (hb ((‖v‖⁻¹:ℝ) • v) (by simpa using hu)).1
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
  have he : ‖v‖^2*(‖v‖⁻¹*(‖v‖⁻¹*g v v)) = g v v := by field_simp
  rw [he] at hmul
  nlinarith

lemma positive_bilinear_bounded (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) :
    IsVonNBounded ℝ {v | g v v < 1} := by
  obtain ⟨c,hc,hb⟩ := positive_bilinear_coercive g hp
  apply (NormedSpace.isVonNBounded_iff ℝ).mpr
  apply (Metric.isBounded_closedBall (x := (0:E)) (r := 1+c⁻¹)).subset
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  have hh := hb v
  have hi : c*c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  have hp' : 0 < c⁻¹ := inv_pos.mpr hc
  dsimp at hv
  nlinarith [sq_nonneg (‖v‖-1),norm_nonneg v]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationFrozenFrame
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
noncomputable section

def frozenFrameCovector (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (i : Fin 4) : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp e.symm.toContinuousLinearMap

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactSmoothExtension
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Manifold
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem compact_smooth_cutoff {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ beta : _root_.OAI.Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
      tsupport beta ⊆ U ∧ (∀ x, 0 ≤ beta x ∧ beta x ≤ 1) ∧
      ∀ x ∈ K, beta =ᶠ[𝓝 x] (fun _ ↦ 1) := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨b,hb1,hb0,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, _root_.OAI.Yau.Jets.Coord)) hK.isClosed hKL (n := (⊤ : ℕ∞))
  have hsupp : tsupport (b : _root_.OAI.Yau.Jets.Coord → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra h
    exact hx (hb0 x h)
  refine ⟨b,b.contMDiff.contDiff,hL.of_isClosed_subset isClosed_closure hsupp,
    hsupp.trans hLU,hb,?_⟩
  intro x hx
  exact Filter.Eventually.filter_mono (nhds_le_nhdsSet hx) hb1

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationCutoff
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

theorem compact_fractional_cutoff {K U : Set _root_.OAI.Yau.Jets.Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (C : ℝ), 0 < C ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
      ∀ x, ‖fderiv ℝ χ x‖ ≤ C * (χ x)^((7:ℝ)/8) := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  obtain ⟨M,hM⟩ := (hb.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    ((hbc.fderiv (𝕜 := ℝ)).norm)
  let C := 8*(max M 0+1)
  have hC : 0 < C := by dsimp [C] <;> positivity
  let χ : _root_.OAI.Yau.Jets.Coord → ℝ := fun x ↦ (b x)^8
  have hsupp : tsupport χ ⊆ tsupport b := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [χ,hz])
  refine ⟨χ,C,hC,hb.pow 8,hbc.of_isClosed_subset isClosed_closure hsupp,hsupp.trans hbU,?_,?_,?_⟩
  · intro x
    exact ⟨pow_nonneg (hbr x).1 _,pow_le_one₀ (hbr x).1 (hbr x).2⟩
  · intro x hx
    filter_upwards [hb1 x hx] with y hy
    simp [χ,hy]
  · intro x
    have hD : ‖fderiv ℝ b x‖ ≤ max M 0+1 := by
      have hm := hM ⟨x,rfl⟩
      have hm' := le_max_left M 0
      linarith
    have hpow : (χ x)^((7:ℝ)/8) = (b x)^7 := by
      change ((b x)^8)^((7:ℝ)/8) = _
      rw [← Real.rpow_natCast (b x) 8,← Real.rpow_mul (hbr x).1]
      norm_num
    rw [hpow]
    change ‖fderiv ℝ (b^8) x‖ ≤ _
    rw [fderiv_pow 8 (hb.differentiable (by simp) x),norm_smul]
    simp only [Nat.cast_ofNat,nsmul_eq_mul,Nat.reduceSub,Real.norm_eq_abs,
      abs_mul,abs_of_nonneg (pow_nonneg (hbr x).1 7)]
    norm_num
    calc
      8* b x^7 * ‖fderiv ℝ b x‖ ≤ 8*b x^7*(max M 0+1) :=
        mul_le_mul_of_nonneg_left hD (mul_nonneg (by norm_num) (pow_nonneg (hbr x).1 7))
      _ = C*b x^7 := by dsimp [C] <;> ring

theorem exists_corrugation_cutoff : ∃ (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (C : ℝ),
    0 < C ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
    tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2) ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
    (∀ x ∈ closedBall (0:_root_.OAI.Yau.Jets.Coord) (1/4), χ =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
    ∀ x, ‖fderiv ℝ χ x‖ ≤ C*(χ x)^((7:ℝ)/8) := by
  apply compact_fractional_cutoff (isCompact_closedBall _ _) isOpen_ball
  intro x hx
  exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by norm_num))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationWellSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set
open scoped ContDiff
noncomputable section

def corrugationSlope (a R r : ℝ) : ℝ := a*r*expNegInvGlue (R^2-r^2)

lemma corrugationSlope_smooth (a R : ℝ) : ContDiff ℝ ∞ (corrugationSlope a R) :=
  (contDiff_const.mul contDiff_id).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2)))

lemma corrugationSlope_nonneg {a R r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    0 ≤ corrugationSlope a R r := mul_nonneg (mul_nonneg ha hr) (expNegInvGlue.nonneg _)

lemma corrugationSlope_zero {a R r : ℝ} (hR : 0 ≤ R) (hr : R ≤ r) :
    corrugationSlope a R r = 0 := by
  unfold corrugationSlope
  rw [expNegInvGlue.zero_of_nonpos (by nlinarith),mul_zero]

lemma expNegInvGlue_hasDerivAt (t : ℝ) :
    HasDerivAt expNegInvGlue ((t⁻¹)^2 * expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 t

lemma corrugationSlope_hasDerivAt (a R r : ℝ) :
    HasDerivAt (corrugationSlope a R)
      (a * expNegInvGlue (R^2-r^2) * (1-2*r^2*((R^2-r^2)⁻¹)^2)) r := by
  have h := ((hasDerivAt_id r).const_mul a).mul
    ((expNegInvGlue_hasDerivAt (R^2-r^2)).comp r
      ((hasDerivAt_const r (R^2)).sub ((hasDerivAt_id r).pow 2)))
  change HasDerivAt (corrugationSlope a R) _ r at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  ring

lemma corrugationSlope_deriv (a R r : ℝ) :
    deriv (corrugationSlope a R) r =
      a * expNegInvGlue (R^2-r^2) * (1-2*r^2*((R^2-r^2)⁻¹)^2) :=
  (corrugationSlope_hasDerivAt a R r).deriv

lemma corrugationSlope_negative_deriv_le {a R r : ℝ} (ha : 0 ≤ a) :
    max (-(deriv (corrugationSlope a R) r)) 0 ≤
      2*a*r^2*((R^2-r^2)⁻¹)^2*expNegInvGlue (R^2-r^2) := by
  rw [corrugationSlope_deriv]
  apply max_le
  · have h := mul_nonneg ha (expNegInvGlue.nonneg (R^2-r^2))
    nlinarith
  · have h := expNegInvGlue.nonneg (R^2-r^2)
    positivity

lemma expNegInvGlue_le_one (t : ℝ) : expNegInvGlue t ≤ 1 := by
  by_cases ht : t ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos ht]; norm_num
  · have ht' : 0 < t := lt_of_not_ge ht
    simp only [expNegInvGlue,ite_eq_right ht]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr ht'.le))

lemma corrugationSlope_le_one {a R r : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hR0 : 0 ≤ R) (hR : R ≤ 1) (hr : 0 ≤ r) : corrugationSlope a R r ≤ 1 := by
  by_cases hrR : r < R
  · have hr1 : r ≤ 1 := hrR.le.trans hR
    calc
      corrugationSlope a R r ≤ a*r*1 :=
        mul_le_mul_of_nonneg_left (expNegInvGlue_le_one _) (mul_nonneg ha hr)
      _ ≤ 1 := by nlinarith
  · rw [corrugationSlope_zero hR0 (le_of_not_gt hrR)]
    norm_num

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationWellBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set
open scoped ContDiff
noncomputable section

def flatRimWeight (t : ℝ) : ℝ := (t⁻¹)^2 * expNegInvGlue (8*t)

lemma flatRimWeight_continuous : Continuous flatRimWeight := by
  have h := (expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X^2)).comp
    (continuous_const.mul continuous_id : Continuous (fun t : ℝ ↦ 8*t))
  have he : flatRimWeight = fun t ↦ 64 * ((Polynomial.X^2 : Polynomial ℝ).eval (8*t)⁻¹ * expNegInvGlue (8*t)) := by
    funext t
    simp [flatRimWeight,mul_inv_rev,mul_pow]
    ring
  rw [he]
  exact continuous_const.mul h

lemma flatRimWeight_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0:ℝ) 1, flatRimWeight t ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image flatRimWeight_continuous.continuousOn
  exact ⟨max M 0,le_max_right _ _,fun t ht ↦ (hM ⟨t,ht,rfl⟩).trans (le_max_left _ _)⟩

lemma flatExponential_split {t : ℝ} (ht : 0 < t) :
    expNegInvGlue t = expNegInvGlue (8*t) * (expNegInvGlue t)^((7:ℝ)/8) := by
  have ht8 : 0 < 8*t := by positivity
  simp only [expNegInvGlue,ite_eq_right (not_le.mpr ht),ite_eq_right (not_le.mpr ht8)]
  rw [← Real.exp_mul,← Real.exp_add]
  congr 1
  simp [mul_inv_rev]
  ring

theorem corrugationSlope_fractional_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (a R r : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ R → R ≤ 1 → 0 ≤ r →
      max (-(deriv (corrugationSlope a R) r)) 0 ≤ C * (corrugationSlope a R r)^((7:ℝ)/8) := by
  obtain ⟨M,hM,hbound⟩ := flatRimWeight_bounded
  refine ⟨2*M+1,by linarith,?_⟩
  intro a R r ha ha1 hR hR1 hr
  by_cases ht : 0 < R^2-r^2
  · have hr1 : r ≤ 1 := by nlinarith
    have ht1 : R^2-r^2 ≤ 1 := by nlinarith [sq_nonneg r]
    have hw := hbound (R^2-r^2) ⟨ht.le,ht1⟩
    have har : 0 ≤ a*r := mul_nonneg ha hr
    have har1 : a*r ≤ 1 := by nlinarith
    have hpow : a*r ≤ (a*r)^((7:ℝ)/8) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' har har1
        (show 0 ≤ (7:ℝ)/8 by norm_num) (show (7:ℝ)/8 ≤ 1 by norm_num)
    have har2 : a*r^2 ≤ (a*r)^((7:ℝ)/8) :=
      (show a*r^2 ≤ a*r by nlinarith).trans hpow
    have hg := expNegInvGlue.nonneg (R^2-r^2)
    have hgp := Real.rpow_nonneg hg ((7:ℝ)/8)
    have hw0 : 0 ≤ flatRimWeight (R^2-r^2) := by
      unfold flatRimWeight
      exact mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _)
    calc
      max (-(deriv (corrugationSlope a R) r)) 0 ≤
          2*a*r^2*((R^2-r^2)⁻¹)^2*expNegInvGlue (R^2-r^2) :=
        corrugationSlope_negative_deriv_le ha
      _ = 2*(a*r^2)*flatRimWeight (R^2-r^2)*(expNegInvGlue (R^2-r^2))^((7:ℝ)/8) := by
        conv_lhs => rw [flatExponential_split ht]
        unfold flatRimWeight
        ring
      _ ≤ 2*(a*r)^((7:ℝ)/8)*M*(expNegInvGlue (R^2-r^2))^((7:ℝ)/8) := by
        gcongr
      _ ≤ (2*M+1)*(corrugationSlope a R r)^((7:ℝ)/8) := by
        rw [corrugationSlope,Real.mul_rpow har hg]
        nlinarith [mul_nonneg (Real.rpow_nonneg har ((7:ℝ)/8)) hgp]
  · have hz : expNegInvGlue (R^2-r^2) = 0 := expNegInvGlue.zero_of_nonpos (le_of_not_gt ht)
    simp [corrugationSlope_deriv,corrugationSlope,hz]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationWellChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set
open scoped ContDiff
noncomputable section

lemma corrugationSlope_le_amplitude {a R r : ℝ} (ha : 0 ≤ a)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hr : 0 ≤ r) : corrugationSlope a R r ≤ a := by
  by_cases hrR : r < R
  · calc
      corrugationSlope a R r ≤ a*r*1 :=
        mul_le_mul_of_nonneg_left (expNegInvGlue_le_one _) (mul_nonneg ha hr)
      _ ≤ a := by nlinarith
  · rw [corrugationSlope_zero hR0 (le_of_not_gt hrR)]
    exact ha

theorem exists_fixed_corrugation_slope : ∃ a C l₀ : ℝ,
    0 < a ∧ a ≤ 1 ∧ 0 < C ∧ 0 < l₀ ∧
    ContDiff ℝ ∞ (corrugationSlope a (1/4)) ∧
    (∀ r : ℝ, 0 ≤ r → 0 ≤ corrugationSlope a (1/4) r ∧ corrugationSlope a (1/4) r ≤ 1 ∧
      max (-(deriv (corrugationSlope a (1/4)) r)) 0 ≤ C*(corrugationSlope a (1/4) r)^((7:ℝ)/8) ∧
      corrugationSlope a (1/4) r * max (-(deriv (corrugationSlope a (1/4)) r)) 0 ≤ 1/(64*(1/4:ℝ))) ∧
    (∀ r ∈ Icc (1/16:ℝ) (1/8), l₀ ≤ corrugationSlope a (1/4) r) ∧
    (∀ r : ℝ, 1/4 ≤ r → corrugationSlope a (1/4) r = 0) := by
  obtain ⟨C,hC,hbound⟩ := corrugationSlope_fractional_bound
  let a := min 1 (1/(16*(C+1)))
  have ha : 0 < a := lt_min zero_lt_one (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  have haC : a*C ≤ 1/16 := by
    have ha' := min_le_right 1 (1/(16*(C+1)))
    have hm : a*(16*(C+1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp ha'
    nlinarith
  let l₀ := a*(1/16)*expNegInvGlue ((1/4:ℝ)^2-(1/8:ℝ)^2)
  have hl₀ : 0 < l₀ := mul_pos (mul_pos ha (by norm_num))
    (expNegInvGlue.pos_of_pos (by norm_num))
  refine ⟨a,C,l₀,ha,ha1,hC,hl₀,corrugationSlope_smooth _ _,?_,?_,?_⟩
  · intro r hr
    have hl := corrugationSlope_nonneg (R := (1/4:ℝ)) ha.le hr
    have hlu := corrugationSlope_le_one ha.le ha1 (by norm_num : 0 ≤ (1/4:ℝ)) (by norm_num) hr
    have hla := corrugationSlope_le_amplitude ha.le (by norm_num : 0 ≤ (1/4:ℝ)) (by norm_num) hr
    have hd := hbound a (1/4) r ha.le ha1 (by norm_num) (by norm_num) hr
    have hlq : (corrugationSlope a (1/4) r)^((7:ℝ)/8) ≤ 1 := Real.rpow_le_one hl hlu (by norm_num)
    have hdC : max (-(deriv (corrugationSlope a (1/4)) r)) 0 ≤ C := by nlinarith
    refine ⟨hl,hlu,hd,?_⟩
    calc
      corrugationSlope a (1/4) r * max (-(deriv (corrugationSlope a (1/4)) r)) 0 ≤ a*C := by gcongr
      _ ≤ 1/(64*(1/4:ℝ)) := by norm_num; exact haC
  · intro r hr
    have he : expNegInvGlue ((1/4:ℝ)^2-(1/8:ℝ)^2) ≤ expNegInvGlue ((1/4:ℝ)^2-r^2) :=
      expNegInvGlue.monotone (by nlinarith [hr.1,hr.2])
    have hn := expNegInvGlue.nonneg ((1/4:ℝ)^2-(1/8:ℝ)^2)
    change a*(1/16)*_ ≤ a*r*_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hr.1 ha.le) he hn
      (mul_nonneg ha.le (le_trans (by norm_num) hr.1))
  · intro r hr
    exact corrugationSlope_zero (by norm_num) hr

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationDiskWell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set MeasureTheory
open scoped ContDiff
noncomputable section

def flatPrimitive (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, expNegInvGlue s

def corrugationDiskWell (a R : ℝ) (z : ℝ × ℝ) : ℝ :=
  -(a/2)*flatPrimitive (R^2-z.1^2-z.2^2)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationPeriodicWell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Set Filter
open scoped ContDiff Topology
noncomputable section

def corrugationPeriodicWell (a : ℝ) (z : ℝ × ℝ) : ℝ :=
  ∑' k : ℤ × ℤ, corrugationDiskWell a (1/4) (z.1-(k.1:ℝ),z.2-(k.2:ℝ))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationRadialJetsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Real

def angularComponent (z v : ℝ × ℝ) (r : ℝ) : ℝ := (-z.2*v.1+z.1*v.2)/r

open Real Set
open scoped ContDiff

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalizedCorrugation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

def corrugationSlowMap (R : ℝ) : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord :=
  R⁻¹ • ContinuousLinearMap.id ℝ _root_.OAI.Yau.Jets.Coord

def corrugationFastMap (J : ℝ) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) : _root_.OAI.Yau.Jets.Coord →L[ℝ] (ℝ × ℝ) :=
  J • a.prod b

def localizedCorrugation (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (s J R : ℝ) (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  (s/J)*χ (corrugationSlowMap R (x-y))*f (corrugationFastMap J a b (x-y))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationMetricError
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

def corrugationMetricError (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (f : (ℝ × ℝ) → ℝ) (s J R : ℝ)
    (a b : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (y x u v : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  s/R*(fderiv ℝ χ (R⁻¹ • (x-y)) v*
    fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b u) +
    fderiv ℝ χ (R⁻¹ • (x-y)) u*
    fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b v)) +
  s/(J*R^2)*f (corrugationFastMap J a b (x-y))*
    fderiv ℝ (fderiv ℝ χ) (R⁻¹ • (x-y)) u v -
  s*χ (R⁻¹ • (x-y))*fderiv ℝ f (corrugationFastMap J a b (x-y))
    (a.prod b (metricConnection (g x) (fderiv ℝ g x) u v)) -
  s/(J*R)*f (corrugationFastMap J a b (x-y))*
    fderiv ℝ χ (R⁻¹ • (x-y)) (metricConnection (g x) (fderiv ℝ g x) u v)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGlobalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real
noncomputable section

def corrugationCellIndex (z : ℝ × ℝ) : ℤ × ℤ :=
  (⌊z.1+(1/2:ℝ)⌋,⌊z.2+(1/2:ℝ)⌋)

def corrugationCellPoint (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1-(corrugationCellIndex z).1,z.2-(corrugationCellIndex z).2)

def corrugationCellRadius (z : ℝ × ℝ) : ℝ :=
  Real.sqrt ((corrugationCellPoint z).1^2+(corrugationCellPoint z).2^2)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationLeadingVector
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def corrugationFastVector (amp : ℝ) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (z : ℝ × ℝ) : _root_.OAI.Yau.Jets.Coord :=
  fderiv ℝ (corrugationPeriodicWell amp) z (1,0) • e (Pi.single 2 1) +
  fderiv ℝ (corrugationPeriodicWell amp) z (0,1) • e (Pi.single 3 1)

def corrugationLeadingVector (amp t : ℝ) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (z : ℝ × ℝ) : _root_.OAI.Yau.Jets.Coord :=
  e (Pi.single 0 1)+t • corrugationFastVector amp e z

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_CorrugationRotatingFrame
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def frozenPlaneVector (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (α β : ℝ) : _root_.OAI.Yau.Jets.Coord :=
  α • e (Pi.single 2 1)+β • e (Pi.single 3 1)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FiniteChartDerivativeSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set
open scoped ContDiff
noncomputable section
variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def finiteChartDerivativeValues (P : Finset I) (Q : Set E) (J : ℕ) (f : I → E → F) : Set ℝ :=
  {0} ∪ {t | ∃ p ∈ P, ∃ i, i ≤ J ∧ ∃ x ∈ Q, t = ‖iteratedFDeriv ℝ i (f p) x‖}

def finiteChartDerivativeSize (P : Finset I) (Q : Set E) (J : ℕ) (f : I → E → F) : ℝ :=
  sSup (finiteChartDerivativeValues P Q J f)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_IndependentWeightedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

def weightedBaseMatrix (A : Matrix n n ℝ) (rho : ℝ) : Matrix n n ℝ := rho • A⁻¹

lemma weightedBaseMatrix_posDef {A : Matrix n n ℝ} (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) : (weightedBaseMatrix A rho).PosDef := hA.inv.smul hr

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_InvariantFrameInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def frameContravariant (A : Matrix m m ℝ) (J : Matrix m n ℝ) : Matrix n n ℝ :=
  (J.transpose * J)⁻¹ * (J.transpose * A * J) * (J.transpose * J)⁻¹

lemma invariant_frame_inverse (A : Matrix m m ℝ) (hA : A.PosDef)
    (J : Matrix m n ℝ) (hJ : Function.Injective J.mulVec)
    (T : Matrix n n ℝ) (hT : A * J = J * T)
    {rho : ℝ} (hr : 0 < rho) :
    frameContravariant A J = rho • (J.transpose * weightedBaseMatrix A rho * J)⁻¹ := by
  have hg : (J.transpose * J).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (PosDef.one : (1 : Matrix m m ℝ).PosDef).conjTranspose_mul_mul_same hJ
  have hh : (J.transpose * weightedBaseMatrix A rho * J).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (weightedBaseMatrix_posDef hA hr).conjTranspose_mul_mul_same hJ
  have ht : J.transpose * A = T.transpose * J.transpose := by
    have h := congrArg Matrix.transpose hT
    simpa only [transpose_mul,show A.transpose = A from by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.1.eq] using h
  have hcore : (J.transpose * A * J) * (J.transpose * J)⁻¹ *
      (J.transpose * A⁻¹ * J) = J.transpose * J := by
    calc
      _ = T.transpose * ((J.transpose * J) * (J.transpose * J)⁻¹) *
          (J.transpose * A⁻¹ * J) := by simp only [ht,Matrix.mul_assoc]
      _ = T.transpose * (J.transpose * A⁻¹ * J) := by
        rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne')]; simp
      _ = J.transpose * (A * A⁻¹) * J := by simp only [← Matrix.mul_assoc,← ht]
      _ = J.transpose * J := by
        rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne')]; simp
  have hmul : frameContravariant A J * (J.transpose * weightedBaseMatrix A rho * J) =
      rho • (1 : Matrix n n ℝ) := by
    unfold frameContravariant weightedBaseMatrix
    rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_smul]
    congr 1
    calc
      _ = (J.transpose * J)⁻¹ * ((J.transpose * A * J) * (J.transpose * J)⁻¹ *
          (J.transpose * A⁻¹ * J)) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hcore,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne')]
  calc
    frameContravariant A J = frameContravariant A J *
        ((J.transpose * weightedBaseMatrix A rho * J) * (J.transpose * weightedBaseMatrix A rho * J)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hh.det_pos.ne'),mul_one]
    _ = rho • (J.transpose * weightedBaseMatrix A rho * J)⁻¹ := by
      rw [← Matrix.mul_assoc,hmul,Matrix.smul_mul,one_mul]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_FrameCotangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

def frameLeftInverse (J : Matrix m n ℝ) : Matrix n m ℝ :=
  (J.transpose * J)⁻¹ * J.transpose

lemma frameLeftInverse_mul (J : Matrix m n ℝ) (hJ : Function.Injective J.mulVec) :
    frameLeftInverse J * J = 1 := by
  have hg : (J.transpose * J).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      (PosDef.one : (1 : Matrix m m ℝ).PosDef).conjTranspose_mul_mul_same hJ
  exact (Matrix.mul_assoc _ _ _).trans
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne'))

lemma frameLeftInverse_covector (J : Matrix m n ℝ) (hJ : Function.Injective J.mulVec)
    (v : n → ℝ) : J.transpose *ᵥ ((frameLeftInverse J).transpose *ᵥ v) = v := by
  rw [mulVec_mulVec,← transpose_mul,frameLeftInverse_mul J hJ,transpose_one,one_mulVec]

omit [DecidableEq m] in
lemma frameContravariant_pullback (A : Matrix m m ℝ) (J : Matrix m n ℝ) :
    frameContravariant A J = frameLeftInverse J * A * (frameLeftInverse J).transpose := by
  have ht : ((J.transpose * J)⁻¹).transpose = (J.transpose * J)⁻¹ := by
    rw [transpose_nonsing_inv,transpose_mul,transpose_transpose]
  simp only [frameContravariant,frameLeftInverse,transpose_mul,transpose_transpose,ht,Matrix.mul_assoc]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothBilinearPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def bilinearPullback (B : W →L[ℝ] W →L[ℝ] ℝ) (T : F →L[ℝ] W) :
    F →L[ℝ] F →L[ℝ] ℝ := (T.precomp ℝ).comp (B.comp T)

lemma smooth_bilinear_pullback (B : M → W →L[ℝ] W →L[ℝ] ℝ)
    (T : ∀ x, V x →L[ℝ] W)
    (hB : ContMDiff I 𝓘(ℝ,W →L[ℝ] W →L[ℝ] ℝ) ∞ B)
    (hT : ContMDiff I (I.prod 𝓘(ℝ,F →L[ℝ] W)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] W)
        (E := fun x ↦ V x →L[ℝ] Bundle.Trivial M W x) x (T x))) :
    ContMDiff I (I.prod 𝓘(ℝ,F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) x
        (bilinearPullback (B x) (T x))) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id,?_⟩
  have ht := ((contMDiffAt_hom_bundle _).mp (hT x)).2
  let t : M → F →L[ℝ] W := fun y ↦
    (T y).comp ((trivializationAt F V x).symmL ℝ y)
  have ht' : ContMDiffAt I 𝓘(ℝ,F →L[ℝ] W) ∞ t x := by
    simpa [inCoordinates, t] using ht
  have hBT : ContMDiffAt I 𝓘(ℝ,F →L[ℝ] W →L[ℝ] ℝ) ∞
      (fun y ↦ (B y).comp (t y)) x :=
    (hB x).clm_comp ht'
  have hpre : ContMDiffAt I 𝓘(ℝ,(W →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] ℝ) ∞
      (fun y ↦ (t y).precomp ℝ) x :=
    ht'.clm_precomp
  have hh : ContMDiffAt I 𝓘(ℝ,F →L[ℝ] F →L[ℝ] ℝ) ∞
      (fun y ↦ ((t y).precomp ℝ).comp ((B y).comp (t y))) x :=
    hpre.clm_comp hBT
  apply hh.congr_of_eventuallyEq
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F V x)] with y hy
  ext v w
  rw [inCoordinates_apply_eq₂ hy hy (Set.mem_univ _)]
  simp [bilinearPullback,t,Trivialization.symmL_apply,hy]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ImmersionMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

local instance instNormedAddCommGroupTangentSpaceReal_solutions (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)
local instance instNormedSpaceRealTangentSpace_solutions (x : M) : NormedSpace ℝ (TangentSpace I x) :=
  inferInstanceAs (NormedSpace ℝ E)
local instance instFiniteDimensionalRealTangentSpace_solutions (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

omit [FiniteDimensional ℝ E] in
lemma smooth_ambient_derivative (f : M → W) (hf : ContMDiff I 𝓘(ℝ,W) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ,E →L[ℝ] W)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] W)
        (E := fun x ↦ TangentSpace I x →L[ℝ] Bundle.Trivial M W x)
        x (mfderiv I 𝓘(ℝ,W) f x)) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id,?_⟩
  have hd := (hf x).mfderiv_const (m := ∞) (by simp)
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with y
  ext v
  simp [inTangentCoordinates, inCoordinates, ContinuousLinearMap.one_def]
  rfl

def immersionMetric (f : M → W) (hf : ContMDiff I 𝓘(ℝ,W) ∞ f)
    (hi : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ,W) f x))
    (B : M → W →L[ℝ] W →L[ℝ] ℝ)
    (hB : ContMDiff I 𝓘(ℝ,W →L[ℝ] W →L[ℝ] ℝ) ∞ B)
    (hs : ∀ x v w, B x v w = B x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < B x v v) :
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) where
  inner x := bilinearPullback (B x) (mfderiv I 𝓘(ℝ,W) f x)
  symm x _ _ := hs x _ _
  pos x _ hv := hp x _ (fun he ↦ hv (hi x (he.trans (map_zero _).symm)))
  isVonNBounded x := positive_bilinear_bounded _
    (fun _ hv ↦ hp x _ (fun he ↦ hv (hi x (he.trans (map_zero _).symm))))
  contMDiff := @smooth_bilinear_pullback E _ _ H _ I M _ _ E _ _
    (fun x : M ↦ TangentSpace I x) _ _ _
    (TangentSpace.fiberBundle (I := I) (M := M))
    (TangentSpace.vectorBundle (I := I) (M := M)) W _ _ B
    (fun x ↦ mfderiv I 𝓘(ℝ,W) f x) hB (smooth_ambient_derivative f hf)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_InverseChartJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def inverseSpatialJet (p : QuadParam _root_.OAI.Yau.Jets.Coord) : (k : ℕ) → _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord [×k]→L[ℝ] _root_.OAI.Yau.Jets.Coord
  | 0, x => (continuousMultilinearCurryFin0 ℝ _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord).symm x
  | k+1, x => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ _root_.OAI.Yau.Jets.Coord) _root_.OAI.Yau.Jets.Coord).symm
      ((fderiv ℝ (inverseSpatialJet p k) x).comp
        (ContinuousLinearMap.inverse (fderiv ℝ (rawQuadratic p) x)))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalMetricJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def localMetricGradient (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : E) : E :=
  ContinuousLinearMap.inverse (g x) (fderiv ℝ f x)

def localMetricHessian (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x -
    (ContinuousLinearMap.compL ℝ E E ℝ (fderiv ℝ f x)).comp
      (metricConnection (g x) (fderiv ℝ g x))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_LocalMetricJetContinuityLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def linearCovectorPull (e : F ≃L[ℝ] E) : (E →L[ℝ] ℝ) ≃L[ℝ] (F →L[ℝ] ℝ) :=
  e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

def linearMetricPull (e : F ≃L[ℝ] E) :
    (E →L[ℝ] E →L[ℝ] ℝ) ≃L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ) :=
  e.symm.arrowCongr (linearCovectorPull e)

def linearMetricField (e : F ≃L[ℝ] E) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x : F) : F →L[ℝ] F →L[ℝ] ℝ := linearMetricPull e (g (e x))

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_ManifoldMatrixSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Manifold Matrix
open scoped ContDiff
noncomputable section
local instance instContMDiffMulRealModelWithCornersSelfSomeENatTop_solutions : ContMDiffMul 𝓘(ℝ,ℝ) ∞ ℝ := by
  constructor
  rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod]
  exact contDiff_mul.contMDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : Type*} [Fintype n] [DecidableEq n]

lemma manifold_matrix_det_smooth (A : M → Matrix n n ℝ)
    (hA : ∀ i j, ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j)) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ (A x).det) := by
  simp only [Matrix.det_apply']
  apply ContMDiff.sum
  intro σ _
  apply contMDiff_const.mul
  apply ContMDiff.prod
  intro i _
  exact hA (σ i) i

lemma manifold_matrix_adjugate_smooth (A : M → Matrix n n ℝ)
    (hA : ∀ i j, ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j)) (i j : n) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ (A x).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply manifold_matrix_det_smooth
  intro k l
  by_cases hk : k = j
  · subst k
    simpa using (contMDiff_const (I := I) (c := (Pi.single i (1:ℝ) : n → ℝ) l))
  · simpa only [Matrix.updateRow_ne hk] using hA k l

lemma manifold_matrix_inverse_smooth (A : M → Matrix n n ℝ)
    (hA : ∀ i j, ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hdet : ∀ x, (A x).det ≠ 0) (i j : n) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ (A x)⁻¹ i j) := by
  have heq : (fun x ↦ (A x)⁻¹ i j) =
      (fun x ↦ ((A x).det)⁻¹ * (A x).adjugate i j) := by
    funext x
    rw [Matrix.inv_def,Ring.inverse_eq_inv]
    rfl
  rw [heq]
  exact ((manifold_matrix_det_smooth A hA).inv₀ hdet).mul
    (manifold_matrix_adjugate_smooth A hA i j)

lemma manifold_positive_sqrt_smooth (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ,ℝ) ∞ f) (hp : ∀ x, 0 < f x) :
    ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun x ↦ Real.sqrt (f x)) := by
  intro x
  exact (ContDiffAt.contMDiffAt (contDiffAt_id.sqrt (hp x).ne')).comp x (hf x)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_MetricJetAdmissibility
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

abbrev MetricJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)

def jetGradient (f : E → ℝ) (j : MetricJet E) (x : E) : E :=
  ContinuousLinearMap.inverse j.1 (fderiv ℝ f x)

def jetHessian (f : E → ℝ) (j : MetricJet E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x -
    (ContinuousLinearMap.compL ℝ E E ℝ (fderiv ℝ f x)).comp (metricConnection j.1 j.2)

def JetAdmissible (f : E → ℝ) (j : MetricJet E) (x : E) : Prop :=
  let p := jetGradient f j x
  let H := jetHessian f j x
  p ≠ 0 ∧ ∃ t : E, j.1 p t = 0 ∧ j.1 t t = 1 ∧
    0 < H p p + (j.1 p p+4)*H t t

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_SmoothInverseChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Manifold
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma inverse_chart_smooth_at (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    ContMDiffAt 𝓘(ℝ,E) I ∞ (extChartAt I p).symm y := by
  exact (contMDiffOn_extChartAt_symm p y hy).contMDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hy)

lemma inverse_chart_comp_derivative (f : M → F) (hf : ContMDiff I 𝓘(ℝ,F) ∞ f)
    (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    fderiv ℝ (f ∘ (extChartAt I p).symm) y =
      (mfderiv I 𝓘(ℝ,F) f ((extChartAt I p).symm y)).comp
        (mfderiv 𝓘(ℝ,E) I (extChartAt I p).symm y) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp y ((hf _).mdifferentiableAt (by simp))
    ((inverse_chart_smooth_at p hy).mdifferentiableAt (by simp))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RadialVolumeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
local instance instDecidableEqFinOfNatNat_solutions_r55ecd8_1 : DecidableEq (Fin 1) := fun a b ↦ decidableEq_of_subsingleton a b
local instance instFintypeFinOfNatNat_solutions : Fintype (Fin 1) := Unique.fintype

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TangentGramDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section

local instance instDecidableEqFinOfNatNat_solutions_1 : DecidableEq (Fin 1) := fun a b ↦ decidableEq_of_subsingleton a b
local instance instFintypeFinOfNatNat_solutions_1 : Fintype (Fin 1) := Unique.fintype

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_WeightedDivergenceInvariance
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def sourceWeightedOperator (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (u : _root_.OAI.Yau.Jets.Coord → ℂ) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  (w x : ℂ)⁻¹ * complexDivergence (sourceFlux g w u) x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransportedOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section

lemma coordPartial_eventuallyEq {f u : _root_.OAI.Yau.Jets.Coord → ℂ} {x : _root_.OAI.Yau.Jets.Coord}
    (he : f =ᶠ[𝓝 x] u) (i : Fin 4) : coordPartial i f =ᶠ[𝓝 x] coordPartial i u := by
  exact (he.fderiv (𝕜 := ℝ)).mono (fun _ h ↦ congrArg (fun L : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℂ ↦ L (Pi.single i 1)) h)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_OperatorLocality
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped ContDiff Topology
noncomputable section

lemma sourceOperator_eventuallyEq
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    {f u : _root_.OAI.Yau.Jets.Coord → ℂ} {x : _root_.OAI.Yau.Jets.Coord} (he : f =ᶠ[𝓝 x] u) :
    sourceWeightedOperator g w f =ᶠ[𝓝 x] sourceWeightedOperator g w u := by
  have hf (i : Fin 4) : sourceFlux g w f i =ᶠ[𝓝 x] sourceFlux g w u i := by
    filter_upwards [Filter.eventually_all.mpr (fun j ↦ coordPartial_eventuallyEq he j)] with z hz
    simp only [sourceFlux,hz]
  filter_upwards [Filter.eventually_all.mpr (fun i ↦ coordPartial_eventuallyEq (hf i) i)] with z hz
  simp only [sourceWeightedOperator,complexDivergence,hz]

lemma sourceWeightedOperator_zero
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ) :
    sourceWeightedOperator g w (fun _ ↦ 0) = 0 := by
  have he : sourceFlux g w (fun _ ↦ 0) = fun _ _ ↦ 0 := by
    funext i z
    simp [sourceFlux,coordPartial]
  funext x
  simp [sourceWeightedOperator,complexDivergence,he,coordPartial]

theorem source_residual_derivative_zero
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (u : _root_.OAI.Yau.Jets.Coord → ℂ) (lam : ℂ) (x : _root_.OAI.Yau.Jets.Coord) (hx : x ∉ tsupport u) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w u z + lam*u z) x = 0 := by
  have he : u =ᶠ[𝓝 x] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hx
  have hr : (fun z ↦ sourceWeightedOperator g w u z + lam*u z) =ᶠ[𝓝 x] (fun _ ↦ 0) := by
    filter_upwards [sourceOperator_eventuallyEq g w he,he] with z hz hu
    simp only [hz,hu,sourceWeightedOperator_zero,Pi.zero_apply,mul_zero,add_zero]
  rw [(hr.iteratedFDeriv ℝ k).self_of_nhds]
  simp

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientLocality
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sourceOperator_coefficients_eventuallyEq
    {g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {w W : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (hg : g =ᶠ[𝓝 x] G) (hw : w =ᶠ[𝓝 x] W) (u : _root_.OAI.Yau.Jets.Coord → ℂ) :
    sourceWeightedOperator g w u =ᶠ[𝓝 x] sourceWeightedOperator G W u := by
  have he (i : Fin 4) : sourceFlux g w u i =ᶠ[𝓝 x] sourceFlux G W u i := by
    filter_upwards [hg,hw] with z hz hwz
    simp only [sourceFlux,sourcePrincipal,hz,hwz]
  filter_upwards [hw,Filter.eventually_all.mpr (fun i ↦ coordPartial_eventuallyEq (he i) i)] with z hwz hz
  simp only [sourceWeightedOperator,complexDivergence,hwz,hz]

lemma sourceResidual_coefficients_derivative_eq
    {g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ} {w W : _root_.OAI.Yau.Jets.Coord → ℝ} {x : _root_.OAI.Yau.Jets.Coord}
    (hg : g =ᶠ[𝓝 x] G) (hw : w =ᶠ[𝓝 x] W) (u : _root_.OAI.Yau.Jets.Coord → ℂ) (lam : ℂ) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator g w u z+lam*u z) x =
      iteratedFDeriv ℝ k (fun z ↦ sourceWeightedOperator G W u z+lam*u z) x := by
  have he := sourceOperator_coefficients_eventuallyEq hg hw u
  have hr : (fun z ↦ sourceWeightedOperator g w u z+lam*u z) =ᶠ[𝓝 x]
      (fun z ↦ sourceWeightedOperator G W u z+lam*u z) := by
    filter_upwards [he] with z hz
    rw [hz]
  exact (hr.iteratedFDeriv ℝ k).self_of_nhds

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientMetricJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev CoefficientPoint (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ((E →L[ℝ] ℝ) →L[ℝ] E) × ℝ

abbrev CoefficientDerivative (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  letI : TopologicalSpace (CoefficientPoint E) :=
    (inferInstance : NormedAddCommGroup (CoefficientPoint E)).toUniformSpace.toTopologicalSpace
  letI : AddCommMonoid (CoefficientPoint E) :=
    (inferInstance : NormedAddCommGroup (CoefficientPoint E)).toAddCommMonoid
  letI : Module ℝ (CoefficientPoint E) :=
    (inferInstance : NormedSpace ℝ (CoefficientPoint E)).toModule
  E →L[ℝ] CoefficientPoint E

abbrev CoefficientFirstJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  CoefficientPoint E × CoefficientDerivative E

def coefficientMetricValue (c : CoefficientPoint E) : E →L[ℝ] E →L[ℝ] ℝ :=
  c.2 • ContinuousLinearMap.inverse c.1

def coefficientMetricJet (j : CoefficientFirstJet E) : MetricJet E :=
  (coefficientMetricValue j.1,(fderiv ℝ coefficientMetricValue j.1).comp j.2)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoordinateCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section
variable {n : ℕ}
abbrev Coord (n : ℕ) := Fin n → ℝ

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_TripleWaveParameters
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]
variable {g H : T → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {p : T → _root_.OAI.Yau.Jets.Coord}
namespace AdmissibleFrameTriple
variable (d : AdmissibleFrameTriple g H p)
def frame (z : T × Fin 3) : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord :=
  frameEquiv (g z.1) (d.e z.1 z.2) (d.orthonormal z.1 z.2)
def alpha (t : T) : ℝ := Real.sqrt (g t (p t) (p t))
def beta (t : T) : ℝ := Real.sqrt (g t (p t) (p t)+4)

end AdmissibleFrameTriple

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinateNorm
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def sourceEuclideanNorm (x : _root_.OAI.Yau.Jets.Coord) : ℝ := Real.sqrt (∑ i, (x i)^2)

lemma sourceEuclideanNorm_nonneg (x : _root_.OAI.Yau.Jets.Coord) : 0 ≤ sourceEuclideanNorm x := Real.sqrt_nonneg _

lemma norm_le_sourceEuclideanNorm (x : _root_.OAI.Yau.Jets.Coord) : ‖x‖ ≤ sourceEuclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg (sourceEuclideanNorm_nonneg x)).mpr
  intro i
  have hi : (x i)^2 ≤ ∑ j : Fin 4, (x j)^2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
  have hs := Real.sq_sqrt (Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) ↦ sq_nonneg (x j)))
  change |x i| ≤ sourceEuclideanNorm x
  have hpos := sourceEuclideanNorm_nonneg x
  dsimp [sourceEuclideanNorm] at *
  nlinarith [sq_abs (x i)]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Waves
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E]

def baseCutoff : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

def scaledCutoff (N : ℝ) (y : E) : E → ℝ :=
  fun x ↦ (baseCutoff (E := E)) (N ^ (1 / 3 : ℝ) • (x - y))

end
end Yau.Waves

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformSmoothBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

def DerivativeBound (k : ℕ) (f : Coord → ℂ) (x : Coord) (C : ℝ) : Prop :=
  ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ C

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactNormalOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

def metricChartParameter (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (y : _root_.OAI.Yau.Jets.Coord) (e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) : QuadParam _root_.OAI.Yau.Jets.Coord :=
  (y,e.toContinuousLinearMap,actualFrameConnection g y e)

def extendedPrincipal (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (y : T → _root_.OAI.Yau.Jets.Coord) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (beta : _root_.OAI.Yau.Jets.Coord → ℝ)
    (t : T) (i j : Fin 4) : _root_.OAI.Yau.Jets.Coord → ℂ :=
  cutoffCoefficient beta (complexPrincipal g i j) (metricChartParameter g (y t) (e t))

def extendedDrift (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : T → _root_.OAI.Yau.Jets.Coord) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (beta : _root_.OAI.Yau.Jets.Coord → ℝ)
    (t : T) (j : Fin 4) : _root_.OAI.Yau.Jets.Coord → ℂ :=
  cutoffCoefficient beta (complexDrift g w j) (metricChartParameter g (y t) (e t))

structure NormalOperatorFamily
    (a : T → Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (b : T → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) : Prop where
  principal_smooth : ∀ t i j, ContDiff ℝ ∞ (a t i j)
  drift_smooth : ∀ t j, ContDiff ℝ ∞ (b t j)
  principal_jets : ∀ k i j, Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ iteratedFDeriv ℝ k (a z.1 i j) z.2)
  drift_jets : ∀ k j, Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ iteratedFDeriv ℝ k (b z.1 j) z.2)
  principal_symm : ∀ t i j x, a t i j x = a t j i x
  normal_value : ∀ t i j, a t i j 0 = if i=j then 1 else 0
  normal_first : ∀ t i j, fderiv ℝ (a t i j) 0 = 0

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MetricWaveJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set MvPolynomial
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

structure MetricWaveJetFamily
    (G : T → Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ) (b : T → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ)
    (s a bb : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ) (m J : ℕ)
    (phi : T → CPoly) (A : ℕ → T → CPoly) : Prop where
  phase_continuous : ContinuousPolyFamily phi
  amplitude_continuous : ∀ j, ContinuousPolyFamily (A j)
  phase_retained : ∀ t k, k ≤ 2 → homogeneousComponent k (phi t) =
    initialPhaseJet (s t) (normalFrameVector (a t) (bb t)) (normalComplexHessian (a t) (bb t) (H t)) k
  phase_degree : ∀ t d, m+2*J+3 < d → homogeneousComponent d (phi t) = 0
  amplitude_value : ∀ j t, homogeneousComponent 0 (A j t) = if j=0 then 1 else 0
  amplitude_degree : ∀ j t k, m+1+2*(J-j) < k → homogeneousComponent k (A j t) = 0
  eikonal_flat : ∀ t, FlatAt m (smoothEikonal (G t) (reval (phi t))) 0
  transport_zero : ∀ t, FlatAt m (smoothTransport (smoothBeamVector (G t) (reval (phi t)))
    (smoothBeamScalar (G t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))) 0
  transport_next : ∀ j, j < J → ∀ t, FlatAt m
    (smoothTransport (smoothBeamVector (G t) (reval (phi t)))
      (smoothBeamScalar (G t) (b t) (reval (phi t)))
      (fun x ↦ -smoothSecondOrder (G t) (b t) (reval (A j t)) x) (reval (A (j+1) t))) 0

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_UniformActualWaveSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Filter Set
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem eventually_nat_frequency {P : ℝ → Prop} (h : ∀ᶠ N : ℝ in atTop, P N) :
    ∀ᶠ n : ℕ in atTop, P (n:ℝ) :=
  tendsto_natCast_atTop_atTop.eventually h

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_ConstructedCoordinateWaves
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set MvPolynomial
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

def coordinateWave (phi : T → CPoly) (A : ℕ → T → CPoly) (J : ℕ) (N : ℝ)
    (t : T) (x : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  Yau.Waves.scaledCutoff N (0:_root_.OAI.Yau.Jets.Coord) x •
    (finiteAmplitude (fun j ↦ A j t) J N x * waveExp (reval (phi t)) N x)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_TripleSourceWaves
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

abbrev SourceFrameTriple (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : T → _root_.OAI.Yau.Jets.Coord) := AdmissibleFrameTriple (g ∘ y) (sourceHessian g S ∘ y) (metricGradient g S ∘ y)

def sourceTripleAlpha (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : T → _root_.OAI.Yau.Jets.Coord) (z : T × Fin 3) : ℝ :=
  Real.sqrt (g (y z.1) (metricGradient g S (y z.1)) (metricGradient g S (y z.1)))

def sourceTripleBeta (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : T → _root_.OAI.Yau.Jets.Coord) (z : T × Fin 3) : ℝ :=
  Real.sqrt (g (y z.1) (metricGradient g S (y z.1)) (metricGradient g S (y z.1))+4)

structure TripleSourceWaveData
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : T → _root_.OAI.Yau.Jets.Coord) (d : SourceFrameTriple g S y) (m J K k0 : ℕ) where
  beta : ContDiffBump (0:_root_.OAI.Yau.Jets.Coord)
  phi : T × Fin 3 → CPoly
  A : ℕ → T × Fin 3 → CPoly
  F : T × Fin 3 → OpenPartialHomeomorph _root_.OAI.Yau.Jets.Coord _root_.OAI.Yau.Jets.Coord
  c : ℝ
  Cw : ℝ
  Cr : ℝ
  R : ℝ
  c_pos : 0 < c
  Cw_pos : 0 < Cw
  Cr_pos : 0 < Cr
  R_pos : 0 < R
  sourceRadius : ℝ
  targetRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  targetRadius_pos : 0 < targetRadius
  jets : MetricWaveJetFamily (extendedPrincipal g (fun z ↦ y z.1) d.frame beta)
    (extendedDrift g w (fun z ↦ y z.1) d.frame beta)
    (fun z ↦ S (y z.1)) (sourceTripleAlpha g S y) (sourceTripleBeta g S y)
    (fun z ↦ envelopeHessian (S ∘ actualMetricChart g (y z.1) (d.frame z))) m J phi A
  chart_eq : ∀ z, (F z : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord) = actualMetricChart g (y z.1) (d.frame z)
  chart_domain : ∀ z, (F z).source = Metric.ball 0 sourceRadius ∧
    Metric.closedBall (y z.1) targetRadius ⊆ (F z).target ∧
    ContDiffOn ℝ ∞ (F z).symm (F z).target
  estimates : ∀ᶠ n : ℕ in atTop, ∀ t,
    let V := chartPushforward (F t) (coordinateWave phi A J (n:ℝ) t)
    ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
    tsupport V ⊆ {z | sourceEuclideanNorm (z-y t.1) ≤ R*(n:ℝ)^(-1/3:ℝ)} ∧
    ∀ z : _root_.OAI.Yau.Jets.Coord,
      (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val V z‖ ≤
        Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c*(n:ℝ)*(sourceEuclideanNorm (z-y t.1))^2)) ∧
      DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w V z +
        ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*V z) z
          (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveCenterJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

def phase (t : T × Fin 3) : _root_.OAI.Yau.Jets.Coord → ℂ := reval (b.phi t) ∘ (b.F t).symm

def amplitude (N : ℝ) (t : T × Fin 3) : _root_.OAI.Yau.Jets.Coord → ℂ :=
  finiteAmplitude (fun j ↦ b.A j t) J N ∘ (b.F t).symm

def wave (N : ℝ) (t : T × Fin 3) : _root_.OAI.Yau.Jets.Coord → ℂ :=
  chartPushforward (b.F t) (coordinateWave b.phi b.A J N t)

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_DualWaveCoefficient
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def dualWaveCoefficient (N : ℝ) (V : _root_.OAI.Yau.Jets.Coord → ℂ) (S : ℝ) (x : _root_.OAI.Yau.Jets.Coord) (b : ℝ) (v : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  (Real.exp (-N*S):ℂ)*((b:ℂ)*V x+(N:ℂ)⁻¹*fderiv ℝ V x v)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GaussianCoefficientVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

def pairLinearSum (z : ι → ℂ) (a : ι × Fin 2 → ℝ) : ℝ :=
  ∑ p, (if p.2 = 0 then (z p.1).re else -(z p.1).im)*a p

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GaussianCoefficientTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

variable {ι : Type*} [Fintype ι]

def coefficientEvent (r : ℝ) : Set (ι × Fin 2 → ℝ) :=
  {a | ∀ i, ‖(a (i,0) : ℂ)+Complex.I*(a (i,1):ℂ)‖ ≤ r}

end
end Yau.Probability

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_AnchoredCubeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open MeasureTheory Set Function
open scoped ENNReal ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def InUnitCube (x : ι → ℝ) : Prop := ∀ i, |x i| ≤ 1

def cubeControl (f : List ι → (ι → ℝ) → ℝ) :
    List ι → List ι → (ι → ℝ) → ℝ≥0∞
  | [], ds, x => ‖f ds x‖ₑ
  | i :: is, ds, x => cubeControl f is ds (update x i 0) +
      ∫⁻ t in Icc (-1 : ℝ) 1, cubeControl f is (i :: ds) (update x i t)

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformTripleBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

def sourceDirectionEta (g H : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (p q : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  (H p p+H q q)/(g p p+g q q)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealPhaseJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

variable {T : Type*} [TopologicalSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

def realDefect (t : T × Fin 3) (x : _root_.OAI.Yau.Jets.Coord) : ℝ := (b.phase t x).re-S x

def eta (_b : TripleSourceWaveData g w S y d m J K k0) (t : T × Fin 3) : ℝ := sourceDirectionEta (g (y t.1))
  (sourceHessian g S (y t.1)) (metricGradient g S (y t.1)) (d.q t.1 t.2)

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianWaveJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

def gaussianCoefficient (a : ι × Fin 2 → ℝ) (i : ι) : ℂ :=
  (a (i,0):ℂ)+Complex.I*(a (i,1):ℂ)

def gaussianWaveField (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (a : ι × Fin 2 → ℝ) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  (∑ i, gaussianCoefficient a i*V i x).re

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι]

abbrev JetSpace := EuclideanSpace ℝ (Fin 5)

def normalizedRealJet (f : _root_.OAI.Yau.Jets.Coord → ℝ) (N S : ℝ) (x : _root_.OAI.Yau.Jets.Coord) : JetSpace :=
  WithLp.toLp 2 (Fin.cons (Real.exp (-N*S)*f x)
    (fun i : Fin 4 ↦ Real.exp (-N*S)*N⁻¹*fderiv ℝ f x (Pi.single i 1)))

def jetWaveCoefficients (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (N S : ℝ) (x : _root_.OAI.Yau.Jets.Coord) : Fin 5 → ι → ℂ :=
  Fin.cons (fun i ↦ dualWaveCoefficient N (V i) S x 1 0)
    (fun j i ↦ dualWaveCoefficient N (V i) S x 0 (Pi.single j 1))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EnvelopeRegion
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section

def highEnvelopeRegion (Ω : Set _root_.OAI.Yau.Jets.Coord) (S S0 : _root_.OAI.Yau.Jets.Coord → ℝ) (n : ℕ) : Set _root_.OAI.Yau.Jets.Coord :=
  {x | x ∈ Ω ∧ -8*Real.log (n:ℝ)/(n:ℝ) ≤ S x-S0 x}

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_CompactSourceWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

abbrev SourceCompactFrameCover (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (K : Set _root_.OAI.Yau.Jets.Coord) :=
  CompactFrameCover (fun t : K ↦ g t) (fun t : K ↦ sourceHessian g S t)
    (fun t : K ↦ metricGradient g S t)

def coverSourceCenter {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {S : _root_.OAI.Yau.Jets.Coord → ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} (d : SourceCompactFrameCover g S K)
    (t : d.Parameter) : _root_.OAI.Yau.Jets.Coord := (d.center t).val

lemma continuous_coverSourceCenter {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
    {S : _root_.OAI.Yau.Jets.Coord → ℝ} {K : Set _root_.OAI.Yau.Jets.Coord} (d : SourceCompactFrameCover g S K) :
    Continuous (coverSourceCenter d) := continuous_subtype_val.comp d.continuous_center

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeSourceWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def scaledLatticePoint (n : ℕ) (z : Fin 4 → ℤ) : _root_.OAI.Yau.Jets.Coord :=
  (n:ℝ)^(-1/2:ℝ) • (fun i ↦ (z i:ℝ))

abbrev SourceGrid (U : Set _root_.OAI.Yau.Jets.Coord) (n : ℕ) := {z : Fin 4 → ℤ // scaledLatticePoint n z ∈ U}

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

def selectFrame (d : SourceCompactFrameCover g S D) (x : D) : d.Parameter :=
  Classical.choose (d.surjective_center x)

def latticeFrame (d : SourceCompactFrameCover g S D) (hUD : U ⊆ D)
    (n : ℕ) (z : SourceGrid U n) : d.Parameter :=
  selectFrame d ⟨scaledLatticePoint n z,hUD z.property⟩

def latticeWave (d : SourceCompactFrameCover g S D)
    (b : TripleSourceWaveData g w S (coverSourceCenter d) d.triple m J K k0)
    (hUD : U ⊆ D) (n : ℕ) (z : SourceGrid U n) (j : Fin 3) : _root_.OAI.Yau.Jets.Coord → ℂ :=
  chartPushforward (b.F (latticeFrame d hUD n z,j))
    (coordinateWave b.phi b.A J (n:ℝ) (latticeFrame d hUD n z,j))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

def roundedLatticeIndex (n : ℕ) (x : _root_.OAI.Yau.Jets.Coord) : Fin 4 → ℤ :=
  fun i ↦ ⌊x i / (n:ℝ)^(-1/2:ℝ)⌋

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeDirectionalCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
noncomputable section

def unitDirection (v : _root_.OAI.Yau.Jets.Coord) : _root_.OAI.Yau.Jets.Coord := (‖v‖⁻¹:ℝ) • v

def directionalLatticeIndex (n : ℕ) (x : _root_.OAI.Yau.Jets.Coord) (K : ℝ) (v : _root_.OAI.Yau.Jets.Coord) : Fin 4 → ℤ :=
  roundedLatticeIndex n (x+(K*(n:ℝ)^(-1/2:ℝ)) • unitDirection v)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LocalSourceWaveTransfer
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem local_source_wave_transfer
    (g G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w W S A : _root_.OAI.Yau.Jets.Coord → ℝ)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) {E : Set _root_.OAI.Yau.Jets.Coord} (hE : IsOpen E) (hyE : ∀ t, y t ∈ E)
    (he : ∀ x ∈ E, (G =ᶠ[𝓝 x] g) ∧ (W =ᶠ[𝓝 x] w) ∧ A x = S x)
    (u : ℕ → T → _root_.OAI.Yau.Jets.Coord → ℂ) (k0 K : ℕ) (c Cw Cr R : ℝ)
    (hCw : 0 < Cw) (hCr : 0 < Cr)
    (hest : ∀ᶠ n : ℕ in atTop, ∀ t,
      ContDiff ℝ ∞ (u n t) ∧ HasCompactSupport (u n t) ∧
      tsupport (u n t) ⊆ {z | sourceEuclideanNorm (z-y t) ≤ R*(n:ℝ)^(-1/3:ℝ)} ∧
      ∀ z : _root_.OAI.Yau.Jets.Coord,
        (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (u n t) z‖ ≤
          Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*A z-c*(n:ℝ)*(sourceEuclideanNorm (z-y t))^2)) ∧
        DerivativeBound k0 (fun z ↦ sourceWeightedOperator G W (u n t) z +
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*u n t z) z
            (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*A z))) :
    ∀ᶠ n : ℕ in atTop, ∀ t,
      ContDiff ℝ ∞ (u n t) ∧ HasCompactSupport (u n t) ∧ tsupport (u n t) ⊆ E ∧
      tsupport (u n t) ⊆ {z | sourceEuclideanNorm (z-y t) ≤ R*(n:ℝ)^(-1/3:ℝ)} ∧
      ∀ z : _root_.OAI.Yau.Jets.Coord,
        (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (u n t) z‖ ≤
          Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c*(n:ℝ)*(sourceEuclideanNorm (z-y t))^2)) ∧
        DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w (u n t) z +
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*u n t z) z
            (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z)) := by
  obtain ⟨r,hr,hball⟩ := compact_family_common_radius isCompact_univ
    (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ y z.1+z.2) ((hy.comp continuous_fst).add continuous_snd)
    hE (fun t _ ↦ by simpa using hyE t)
  have hsmall : ∀ᶠ n : ℕ in atTop, R*(n:ℝ)^(-1/3:ℝ) < r := by
    apply eventually_nat_frequency (P := fun N : ℝ ↦ R*N^(-1/3:ℝ) < r)
    have ht : Tendsto (fun N : ℝ ↦ R*N^(-1/3:ℝ)) atTop (𝓝 0) := by
      simpa only [neg_div,mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul R
    exact ht.eventually (gt_mem_nhds hr)
  filter_upwards [hest,hsmall] with n hn hnr
  intro t
  obtain ⟨hsm,hcomp,hsup,hb⟩ := hn t
  have hsE : tsupport (u n t) ⊆ E := by
    intro z hz
    have hd := (norm_le_sourceEuclideanNorm (z-y t)).trans (hsup hz)
    have hh := hball t (mem_univ t) (z-y t) (hd.trans_lt hnr)
    simpa only [add_sub_cancel] using hh
  refine ⟨hsm,hcomp,hsE,hsup,?_⟩
  intro z
  by_cases hz : z ∈ E
  · have hsame := he z hz
    refine ⟨?_,?_⟩
    · simpa only [hsame.2.2] using (hb z).1
    · intro k hk
      rw [← sourceResidual_coefficients_derivative_eq hsame.1 hsame.2.1]
      simpa only [hsame.2.2] using (hb z).2 k hk
  · have hnot : z ∉ tsupport (u n t) := fun hh ↦ hz (hsE hh)
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hnot
    constructor
    · intro k
      rw [(hzero.iteratedFDeriv ℝ k.val).self_of_nhds]
      simp only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
      positivity
    · intro k hk
      rw [source_residual_derivative_zero g w (u n t) _ z hnot k,norm_zero]
      positivity

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LocalCompactWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

structure LocalCompactWaveData
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (w S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (D : Set _root_.OAI.Yau.Jets.Coord) (m J K k0 : ℕ) where
  G : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ
  W : _root_.OAI.Yau.Jets.Coord → ℝ
  A : _root_.OAI.Yau.Jets.Coord → ℝ
  E : Set _root_.OAI.Yau.Jets.Coord
  smooth_G : ContDiff ℝ ∞ G
  smooth_W : ContDiff ℝ ∞ W
  smooth_A : ContDiff ℝ ∞ A
  symmetric_G : ∀ x u v, G x u v = G x v u
  positive_G : ∀ x v, v ≠ 0 → 0 < G x v v
  open_E : IsOpen E
  centers_E : D ⊆ E
  germ : ∀ x ∈ E, (G =ᶠ[𝓝 x] g) ∧ (W =ᶠ[𝓝 x] w) ∧ (A =ᶠ[𝓝 x] S)
  nonzero_gradient : ∀ x ∈ D, metricGradient G A x ≠ 0
  cover : SourceCompactFrameCover G A D
  beams : TripleSourceWaveData G W A (coverSourceCenter cover) cover.triple m J K k0
  estimates : ∀ᶠ n : ℕ in atTop, ∀ t : cover.Parameter × Fin 3,
    ContDiff ℝ ∞ (beams.wave (n:ℝ) t) ∧ HasCompactSupport (beams.wave (n:ℝ) t) ∧
    tsupport (beams.wave (n:ℝ) t) ⊆ E ∧
    tsupport (beams.wave (n:ℝ) t) ⊆
      {z | sourceEuclideanNorm (z-coverSourceCenter cover t.1) ≤ beams.R*(n:ℝ)^(-1/3:ℝ)} ∧
    ∀ z : _root_.OAI.Yau.Jets.Coord,
      (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (beams.wave (n:ℝ) t) z‖ ≤
        beams.Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-beams.c*(n:ℝ)*(sourceEuclideanNorm (z-coverSourceCenter cover t.1))^2)) ∧
      DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w (beams.wave (n:ℝ) t) z +
        ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*beams.wave (n:ℝ) t z) z
          (beams.Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FrozenPhaseLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Jets Set Metric
open scoped ContDiff

def frozenPhaseCovector (l k : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp l + Complex.I • Complex.ofRealCLM.comp k

end Yau.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalLogJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def originalEta (t : a.cover.Parameter × Fin 3) : ℝ :=
  sourceDirectionEta (g (coverSourceCenter a.cover t.1))
    (sourceHessian g S (coverSourceCenter a.cover t.1))
    (metricGradient g S (coverSourceCenter a.cover t.1)) (a.cover.triple.q t.1 t.2)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeLogJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeEta (hUD : U ⊆ D) (n : ℕ) (z : SourceGrid U n) (j : Fin 3) : ℝ :=
  a.originalEta (latticeFrame a.cover hUD n z,j)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeEnergyLowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeEnergy (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (x : _root_.OAI.Yau.Jets.Coord) (b : ℝ) (v : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  letI := hfin
  ∑ i : SourceGrid U n × Fin 3,
    ‖dualWaveCoefficient n (latticeWave a.cover a.beams hUD n i.1 i.2) (S x) x b v‖^2

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeCovariance2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeRandomDual (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (x : _root_.OAI.Yau.Jets.Coord) (b : ℝ) (v : _root_.OAI.Yau.Jets.Coord) : (((SourceGrid U n × Fin 3) × Fin 2) → ℝ) → ℝ :=
  letI := hfin
  pairLinearSum (fun i : SourceGrid U n × Fin 3 ↦
    dualWaveCoefficient n (latticeWave a.cover a.beams hUD n i.1 i.2) (S x) x b v)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeSeededRandomDual (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (seed : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord) (b : ℝ) (v : _root_.OAI.Yau.Jets.Coord)
    (coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ) : ℝ :=
  letI := hfin
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  Real.exp (-(n:ℝ)*S x)*(b*(seed x+gaussianWaveField V coeff x)+
    (n:ℝ)⁻¹*fderiv ℝ (fun z ↦ seed z+gaussianWaveField V coeff z) x v)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeGaussianSmallBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal RealInnerProductSpace
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeSeededJet (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (seed : _root_.OAI.Yau.Jets.Coord → ℝ) (x : _root_.OAI.Yau.Jets.Coord)
    (coeff : ((SourceGrid U n × Fin 3) × Fin 2) → ℝ) : JetSpace :=
  letI := hfin
  let V := fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2
  normalizedRealJet (fun z ↦ seed z+gaussianWaveField V coeff z) (n:ℝ) (S x) x

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SeedJetLowerBound
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Set
open scoped ContDiff
noncomputable section

def oscillatorySeed (S T : Coord → ℝ) (N : ℝ) (x : Coord) : ℝ :=
  Real.exp (N*S x)*Real.cos (N*T x)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FirstJetSize
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability
noncomputable section

def firstJetSize (f : _root_.OAI.Yau.Jets.Coord → ℝ) (N : ℝ) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  |f x|+N⁻¹*‖fderiv ℝ f x‖

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FirstJetNonvanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology ENNReal
noncomputable section

def sourceFirstJetSize (f : _root_.OAI.Yau.Jets.Coord → ℝ) (N : ℝ) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  |f x|+N⁻¹*sourceEuclideanNorm (fun i ↦ fderiv ℝ f x (Pi.single i 1))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_BallPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric MeasureTheory
noncomputable section

def sourceClosedBall (x : _root_.OAI.Yau.Jets.Coord) (r : ℝ) : Set _root_.OAI.Yau.Jets.Coord :=
  {y | sourceEuclideanNorm (y-x) ≤ r}

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_BasisLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]

def basisMetricMatrix (b : Module.Basis n ℝ E) (B : LinearMap.BilinForm ℝ E) : Matrix n n ℝ :=
  LinearMap.toMatrix₂ b b B

def basisMetricFlux (b : Module.Basis n ℝ E) (B : E → LinearMap.BilinForm ℝ E)
    (f : E → ℝ) (i : n) (y : E) : ℝ :=
  Real.sqrt (basisMetricMatrix b (B y)).det *
    ∑ j, (basisMetricMatrix b (B y))⁻¹ i j * fderiv ℝ f y (b j)

def basisMetricLaplacian (b : Module.Basis n ℝ E) (B : E → LinearMap.BilinForm ℝ E)
    (f : E → ℝ) (y : E) : ℝ :=
  (Real.sqrt (basisMetricMatrix b (B y)).det)⁻¹ *
    ∑ i, fderiv ℝ (basisMetricFlux b B f i) y (b i)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinateMatrixEllipticity
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Matrix
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def coordMatrixForm (B : Matrix (Fin 4) (Fin 4) ℝ) : _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ :=
  ∑ i, ∑ j, B i j • ((ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj j))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinatePartialJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Analysis
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def partialDirs : (ds : List ι) → Fin ds.length → (ι → ℝ)
  | [] => Fin.elim0
  | i::ds => Fin.cons (Pi.single i 1) (partialDirs ds)

def partialJet (f : (ι → ℝ) → ℝ) : List ι → (ι → ℝ) → ℝ
  | [] => f
  | i::ds => fun x ↦ fderiv ℝ (partialJet f ds) x (Pi.single i 1)

end
end Yau.Analysis

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CoordinateTransverseDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

abbrev TransverseCoord := Fin 3 → ℝ

def transverseProjection (j : Fin 4) : _root_.OAI.Yau.Jets.Coord →L[ℝ] TransverseCoord :=
  ContinuousLinearMap.pi (fun k ↦ ContinuousLinearMap.proj (j.succAbove k))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFixedAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Set
noncomputable section

def corrugationFixedAmplitude : ℝ := Classical.choose exists_fixed_corrugation_slope

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAnnulusBoxes
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

def corrugationAnnulusBox (r J : ℝ) (j k : ℕ) : Set _root_.OAI.Yau.Jets.Coord :=
  Icc ![-r,-r,((j:ℝ)+1/16)/J,(k:ℝ)/J]
      ![r,r,((j:ℝ)+3/32)/J,((k:ℝ)+1/32)/J]

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAnnulusPacking
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

def corrugationAnnulusPacking (r J : ℝ) (n : ℕ) : Set _root_.OAI.Yau.Jets.Coord :=
  ⋃ p ∈ (Finset.univ : Finset (Fin n × Fin n)), corrugationAnnulusBox r J p.1 p.2

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationAssembly
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section
variable {ι : Type*}

def corrugationSum (I : Finset ι) (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (amp J R : ℝ)
    (s : ι → ℝ) (e : ι → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) (y : ι → _root_.OAI.Yau.Jets.Coord) (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  ∑ i ∈ I, localizedCorrugation χ (corrugationPeriodicWell amp) (s i) J R
    (frozenFrameCovector (e i) 2) (frozenFrameCovector (e i) 3) (y i) x

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationCubePartition
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
noncomputable section

def corrugationCubeCenter (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ) (n : ℕ) (k : Fin 4 → Fin n) : _root_.OAI.Yau.Jets.Coord :=
  fun i ↦ o i + (L/(n:ℝ))*((k i:ℝ)+1/2)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFixedCutoff
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

def corrugationFixedCutoff : _root_.OAI.Yau.Jets.Coord → ℝ := Classical.choose exists_corrugation_cutoff

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationFrequencyScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Real
open scoped Topology
noncomputable section

def corrugationFrequency (k : ℕ) : ℝ := ((k:ℝ)+1)^8

def corrugationSubdivision (k : ℕ) : ℕ := (k+1)^2

def corrugationScale (L : ℝ) (k : ℕ) : ℝ := L/(corrugationSubdivision k:ℝ)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGridAssembly
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

def corrugationGridSum (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ) (n : ℕ) (χ : _root_.OAI.Yau.Jets.Coord → ℝ) (amp J : ℝ)
    (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) : _root_.OAI.Yau.Jets.Coord → ℝ :=
  corrugationSum Finset.univ χ amp J (L/(n:ℝ)) s e (corrugationCubeCenter o L n)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationOldData
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

def corrugationOldSlope (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ)
    (S : _root_.OAI.Yau.Jets.Coord → ℝ) (y : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  Real.sqrt (g y (metricGradient g S y) (metricGradient g S y))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationGridNonvanishing
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

def corrugationEnvelopePerturbation (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ) (k : ℕ)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ) (amp : ℝ)
    (e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord) : _root_.OAI.Yau.Jets.Coord → ℝ :=
  corrugationGridSum o L (corrugationSubdivision k) χ amp (corrugationFrequency k)
    (fun i ↦ corrugationOldSlope g S (corrugationCubeCenter o L (corrugationSubdivision k) i)) e

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationRegimeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Filter
open scoped Topology
noncomputable section

def corrugationLowErrorRate (L T : ℝ) (k : ℕ) : ℝ :=
  (corrugationScale L k)⁻¹*(T/corrugationFrequency k)^((7:ℝ)/8) +
    (corrugationFrequency k*(corrugationScale L k)^2)⁻¹ + T/corrugationFrequency k +
    (corrugationFrequency k*corrugationScale L k)⁻¹

def corrugationLowRadialRate (L T : ℝ) (k : ℕ) : ℝ :=
  (corrugationScale L k)^2*corrugationFrequency k*(T/corrugationFrequency k)^((7:ℝ)/8)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationHighRegime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Real Filter
open scoped Topology
noncomputable section

def corrugationHighErrorRate (L T : ℝ) (k : ℕ) : ℝ :=
  (corrugationFrequency k*corrugationScale L k)⁻¹*(T/corrugationFrequency k)^(-(1:ℝ)/8) +
    (corrugationFrequency k*(corrugationScale L k)^2)⁻¹/T + (corrugationFrequency k)⁻¹ +
    (corrugationFrequency k*corrugationScale L k)⁻¹/T

def corrugationHighRadialRate (L T : ℝ) (k : ℕ) : ℝ :=
  (corrugationScale L k)^2*(T/corrugationFrequency k)^(-(1:ℝ)/8)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CorrugationNormalizedGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def corrugationGradientRate (L : ℝ) (k : ℕ) : ℝ :=
  corrugationScale L k+1/(corrugationFrequency k*corrugationScale L k)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeVarianceUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeVariance (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)] (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  ∑ i : SourceGrid U n × Fin 3, ‖latticeWave a.cover a.beams hUD n i.1 i.2 x‖^2

def latticeSigma (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)] (x : _root_.OAI.Yau.Jets.Coord) : ℝ :=
  Real.sqrt (a.latticeVariance hUD n x)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeNormalizedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeAlpha (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (x : _root_.OAI.Yau.Jets.Coord) (i : SourceGrid U n × Fin 3) : ℂ :=
  latticeWave a.cover a.beams hUD n i.1 i.2 x / (a.latticeSigma hUD n x:ℂ)

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FirstJetGoodEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Analysis Yau.Probability Set MeasureTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

def firstJetGoodEvent (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N : ℝ) (Ω : Set _root_.OAI.Yau.Jets.Coord) (b : _root_.OAI.Yau.Jets.Coord → ℝ) : Set (ι × Fin 2 → ℝ) :=
  {a | ∀ x ∈ Ω, b x ≤ sourceFirstJetSize (fun y ↦ seed y+gaussianWaveField V a y) N x}

def coefficientJetGoodEvent (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ) (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
    (N : ℝ) (Ω : Set _root_.OAI.Yau.Jets.Coord) (b : _root_.OAI.Yau.Jets.Coord → ℝ) : Set (ι × Fin 2 → ℝ) :=
  coefficientEvent N ∩ firstJetGoodEvent V seed N Ω b

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_LocalMatrixSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma matrix_det_smooth_at (A : E → Matrix n n ℝ) {x : E}
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun z ↦ A z i j) x) :
    ContDiffAt ℝ ∞ (fun z ↦ (A z).det) x := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i _
  exact hA (σ i) i

lemma matrix_adjugate_smooth_at (A : E → Matrix n n ℝ) {x : E}
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun z ↦ A z i j) x) (i j : n) :
    ContDiffAt ℝ ∞ (fun z ↦ (A z).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  apply matrix_det_smooth_at
  intro k l
  by_cases hk : k = j
  · subst k; simpa using (contDiffAt_const (c := (Pi.single i (1:ℝ) : n → ℝ) l) : ContDiffAt ℝ ∞ (fun _ : E ↦ _) x)
  · simpa only [Matrix.updateRow_ne hk] using hA k l

lemma matrix_inverse_smooth_at (A : E → Matrix n n ℝ) {x : E}
    (hA : ∀ i j, ContDiffAt ℝ ∞ (fun z ↦ A z i j) x)
    (hdet : (A x).det ≠ 0) (i j : n) :
    ContDiffAt ℝ ∞ (fun z ↦ (A z)⁻¹ i j) x := by
  have heq : (fun z ↦ (A z)⁻¹ i j) =
      (fun z ↦ ((A z).det)⁻¹ * (A z).adjugate i j) := by
    funext z
    rw [Matrix.inv_def,Ring.inverse_eq_inv]
    rfl
  rw [heq]
  exact ((matrix_det_smooth_at A hA).inv hdet).mul (matrix_adjugate_smooth_at A hA i j)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SignScaleSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def sourceSignScale (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (x : _root_.OAI.Yau.Jets.Coord) : ℝ := Real.sqrt (g x (metricGradient g S x) (metricGradient g S x)+4)

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_PhysicalNodalCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

def cylinderProjection (x : _root_.OAI.Yau.Jets.Coord) (j : Fin 4) (y : _root_.OAI.Yau.Jets.Coord × ℝ) : _root_.OAI.Yau.Jets.Coord :=
  Fin.cons y.2 (transverseProjection j (y.1-x))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Hausdorff_LiteralNodalCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

def LiteralNodalCertificate
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
    (Q U : Set _root_.OAI.Yau.Jets.Coord) (n : ℕ) (f : _root_.OAI.Yau.Jets.Coord → ℝ) (M : ℝ) : Prop :=
  ∃ tau rf : ℝ, 0 < tau ∧ tau < 1/4 ∧ 0 < rf ∧ rf < tau/4 ∧ rf < (1-tau)/2 ∧
    ∃ t : Finset _root_.OAI.Yau.Jets.Coord, ∃ j : t → Fin 4, ∃ u : Finset t,
      let R := fun x ↦ ((n:ℝ)*sourceSignScale g S x)⁻¹
      (↑t : Set _root_.OAI.Yau.Jets.Coord) ⊆ Q ∧
      (↑t : Set _root_.OAI.Yau.Jets.Coord).PairwiseDisjoint (fun x ↦ sourceClosedBall x (R x)) ∧
      (∀ x ∈ t, 0 < R x ∧ sourceClosedBall x (5*R x) ⊆ U) ∧
      M ≤ 2*rf^3*∑ x ∈ u, (R x)^3 ∧
      ∃ mu > 0,
        (∀ x ∈ u,
          (∀ y ∈ sourceClosedBall x (rf*R x), mu ≤ f y) ∧
          (∀ y ∈ sourceClosedBall ((x:_root_.OAI.Yau.Jets.Coord)+R x • (tau • Pi.single (j x) 1))
            (rf*R x), f y ≤ -mu)) ∧
        ∀ v : _root_.OAI.Yau.Jets.Coord → ℝ, Continuous v →
          (∀ x ∈ u, ∀ y ∈ sourceClosedBall x (rf*R x) ∪
            sourceClosedBall ((x:_root_.OAI.Yau.Jets.Coord)+R x • (tau • Pi.single (j x) 1)) (rf*R x),
            |v y-f y| < mu) →
          ENNReal.ofReal M ≤ Measure.hausdorffMeasure (4:ℝ)
            ((U ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | v y.1 = 0})

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianCompactSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι X : Type*} [Fintype ι] [TopologicalSpace X] [CompactSpace X]

def derivativeSection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : _root_.OAI.Yau.Jets.Coord → F) (hf : ContDiff ℝ ∞ f) (K : Set _root_.OAI.Yau.Jets.Coord)
    (k : ℕ) (dirs : Fin k → _root_.OAI.Yau.Jets.Coord) : C(K,F) :=
  ⟨fun x ↦ iteratedFDeriv ℝ k f x dirs,
    ((hf.continuous_iteratedFDeriv
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).comp continuous_subtype_val).eval
        continuous_const⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_GaussianGradientSupremum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι X : Type*} [Fintype ι] [TopologicalSpace X]

def vectorMeanSection (M : Fin 4 → C(X,ℝ)) : C(X,EuclideanSpace ℝ (Fin 4)) :=
  ⟨fun x ↦ WithLp.toLp 2 (fun j ↦ M j x),
    (PiLp.continuous_toLp 2 (fun _ : Fin 4 ↦ ℝ)).comp (continuous_pi (fun j ↦ (M j).continuous))⟩

def vectorCoeffSection (Z : Fin 4 → ι → C(X,ℂ)) (p : ι × Fin 2) :
    C(X,EuclideanSpace ℝ (Fin 4)) :=
  vectorMeanSection (fun j ↦ if p.2 = 0 then
    ⟨fun x ↦ (Z j p.1 x).re, Complex.continuous_re.comp (Z j p.1).continuous⟩ else
    ⟨fun x ↦ -(Z j p.1 x).im, (Complex.continuous_im.comp (Z j p.1).continuous).neg⟩)

def pairVectorSection (M : Fin 4 → C(X,ℝ)) (Z : Fin 4 → ι → C(X,ℂ))
    (a : ι × Fin 2 → ℝ) : C(X,EuclideanSpace ℝ (Fin 4)) :=
  vectorMeanSection M + ∑ p : ι × Fin 2, a p • vectorCoeffSection Z p

variable [CompactSpace X]

variable (V : ι → _root_.OAI.Yau.Jets.Coord → ℂ)
  (seed : _root_.OAI.Yau.Jets.Coord → ℝ)
  (hV : ∀ i, ContDiff ℝ ∞ (V i))
  (hs : ContDiff ℝ ∞ seed)
  (K : Set _root_.OAI.Yau.Jets.Coord)
  [CompactSpace K]

def gaussianGradientSection (a : ι × Fin 2 → ℝ) : C(K,EuclideanSpace ℝ (Fin 4)) :=
  pairVectorSection (fun j ↦ derivativeSection seed hs K 1 (fun _ ↦ Pi.single j 1))
    (fun j i ↦ derivativeSection (V i) (hV i) K 1 (fun _ ↦ Pi.single j 1)) a

def gaussianGradientSup (a : ι × Fin 2 → ℝ) : ℝ :=
  ‖gaussianGradientSection V seed hV hs K a‖

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_NormalizedWaveRatio
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

def planeWave (k : _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (s : ℝ) (v : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  Complex.exp (Complex.I*(k v/s:ℝ))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeFullPlaneWaveApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticePlaneWaveCoefficient (hUD : U ⊆ D) (n : ℕ) [Fintype (SourceGrid U n)]
    (x : _root_.OAI.Yau.Jets.Coord) (s : ℝ) (i : SourceGrid U n × Fin 3) (v : _root_.OAI.Yau.Jets.Coord) : ℂ :=
  if sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ) then
    a.latticeAlpha hUD n x i *
      planeWave (g (scaledLatticePoint n i.1) (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2)) s v
  else 0

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LatticeGoodEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
  {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeGoodEvent (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (S0 T0 : _root_.OAI.Yau.Jets.Coord → ℝ) (Ω : Set _root_.OAI.Yau.Jets.Coord) : Set (((SourceGrid U n × Fin 3) × Fin 2) → ℝ) :=
  letI := hfin
  coefficientJetGoodEvent
    (fun i : SourceGrid U n × Fin 3 ↦ latticeWave a.cover a.beams hUD n i.1 i.2)
    (oscillatorySeed S0 T0 n) n Ω
    (fun x ↦ ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*S x)) (Real.exp ((n:ℝ)*S0 x)))

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_LocalWaveEnvelopeTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}

def LocalCompactWaveData.withEnvelope (b : LocalCompactWaveData g w S D m J K k0)
    (S' : _root_.OAI.Yau.Jets.Coord → ℝ) {O : Set _root_.OAI.Yau.Jets.Coord} (hO : IsOpen O) (hDO : D ⊆ O)
    (he : ∀ x ∈ O, S' =ᶠ[𝓝 x] S) : LocalCompactWaveData g w S' D m J K k0 where
  G := b.G
  W := b.W
  A := b.A
  E := b.E ∩ O
  smooth_G := b.smooth_G
  smooth_W := b.smooth_W
  smooth_A := b.smooth_A
  symmetric_G := b.symmetric_G
  positive_G := b.positive_G
  open_E := b.open_E.inter hO
  centers_E := fun _ hx ↦ ⟨b.centers_E hx,hDO hx⟩
  germ := fun x hx ↦ ⟨(b.germ x hx.1).1,(b.germ x hx.1).2.1,
    (b.germ x hx.1).2.2.trans (he x hx.2).symm⟩
  nonzero_gradient := b.nonzero_gradient
  cover := b.cover
  beams := b.beams
  estimates := local_source_wave_transfer g b.G w b.W S' b.A
    (fun t : b.cover.Parameter × Fin 3 ↦ coverSourceCenter b.cover t.1)
    ((continuous_coverSourceCenter b.cover).comp continuous_fst)
    (b.open_E.inter hO)
    (fun t ↦ ⟨b.centers_E (b.cover.center t.1).property,hDO (b.cover.center t.1).property⟩)
    (fun x hx ↦ ⟨(b.germ x hx.1).1,(b.germ x hx.1).2.1,
      (b.germ x hx.1).2.2.eq_of_nhds.trans (he x hx.2).eq_of_nhds.symm⟩)
    (fun n t ↦ b.beams.wave (n:ℝ) t) k0 K b.beams.c b.beams.Cw b.beams.Cr b.beams.R
    b.beams.Cw_pos b.beams.Cr_pos b.beams.estimates

lemma envelope_germ_open (S S' : _root_.OAI.Yau.Jets.Coord → ℝ) :
    IsOpen {x | S' =ᶠ[𝓝 x] S} := by
  change IsOpen {x | {z | S' z = S z} ∈ 𝓝 x}
  simpa only [← mem_interior_iff_mem_nhds, ofPred_mem_eq] using
    (isOpen_interior : IsOpen (interior {z | S' z = S z}))

end
end Yau.Geometry

end OAI
end


