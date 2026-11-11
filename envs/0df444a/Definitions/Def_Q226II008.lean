-- Prove2me | Definitions.Def_Q226II008
-- name    : Q226II008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:42:33.203116+00:00
-- url     : https://prove2.me/theorems/0e926d37-3eec-4783-82dc-2b99812b904f
-- title:
--   Definitions bundle Q226II008 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 158 declarations of OpenAI's Lean: 30 definitions and 128 theorems. The definitions and types are `OAI.SmoothLocal.Geometry.BoundedAdmissibleHeight`, `OAI.SmoothLocal.Geometry.PatchAdmissibleHeight`, `OAI.SmoothLocal.Geometry.affinePatchProfile`, `OAI.SmoothLocal.Geometry.assembledPatchMetric`, `OAI.SmoothLocal.Geometry.assembledPatchTensor`, `OAI.SmoothLocal.Geometry.assemblyProfile`, `OAI.SmoothLocal.Geometry.enumeratedAssemblyProfile`, `OAI.SmoothLocal.Geometry.enumeratedPatchTensor`, `OAI.SmoothLocal.Geometry.initialAssemblyMetric`, `OAI.SmoothLocal.Geometry.initialCurvature`, `OAI.SmoothLocal.Geometry.initialCurvatureAmplitudes`, `OAI.SmoothLocal.Geometry.initialCurvatureTerm`, `OAI.SmoothLocal.Geometry.initialPatchAmplitude`, `OAI.SmoothLocal.Geometry.orientedPatchProfile`, `OAI.SmoothLocal.Geometry.patchAddressAmplitude`, `OAI.SmoothLocal.Geometry.patchAddressInitialMetric`, `OAI.SmoothLocal.Geometry.patchAddressProfile`, `OAI.SmoothLocal.Geometry.patchAddressTensor`, `OAI.SmoothLocal.ODE.globalPrescribedScalar`, `OAI.SmoothLocal.ODE.globalPrescribedState`, `OAI.SmoothLocal.ODE.prescribedCurvatureMetric`, `OAI.SmoothLocal.ODE.prescribedFactor`, `OAI.SmoothLocal.ODE.prescribedLocalState`, `OAI.SmoothLocal.ODE.prescribedVelocityFamily`, `OAI.SmoothLocal.ODE.prescribedVolterraFamily`, `OAI.SmoothLocal.Perturbation.SymmetricPerturbation`, `OAI.SmoothLocal.Perturbation.perturbationTensor`, `OAI.SmoothLocal.Perturbation.symmetricSupportedSubmodule`, `OAI.SmoothLocal.Pulse.qMetricDensityFactor`, `OAI.SmoothLocal.Pulse.qMetricFirstLower`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Assembly_AssemblyProfiles`, `IsometricImmersion_Assembly_EnumeratedPatchTensors`, `IsometricImmersion_Assembly_InitialAssemblyMetric`, `IsometricImmersion_Assembly_SupportedPerturbations`, `IsometricImmersion_Calculus_CoordinateJetNorm`, `IsometricImmersion_Calculus_MetricTwoJet`, `IsometricImmersion_Calculus_MixedCoordinateCalculus`, `IsometricImmersion_Calculus_VerticalSliceJets`, `IsometricImmersion_Caps_BoundedClassReflection`, `IsometricImmersion_Caps_CapInteriorEnergy`, `IsometricImmersion_Caps_CapL2Basics`, `IsometricImmersion_Coordinates_CoordinateSwap`, `IsometricImmersion_Coordinates_OrientedPatchSquares`, `IsometricImmersion_Coordinates_PatchAddressModel`, `IsometricImmersion_Coordinates_PatchGeometry`, `IsometricImmersion_Curvature_CurvatureParameter`, `IsometricImmersion_Curvature_CurvatureParameterJets`, `IsometricImmersion_Curvature_InitialCurvature`, `IsometricImmersion_Curvature_MetricCurvatureJet`, `IsometricImmersion_Curvature_PatchCurvatureProfiles`, `IsometricImmersion_Curvature_PrescribedCurvature`, `IsometricImmersion_Darboux_MixedDarbouxElimination`, `IsometricImmersion_Darboux_QMetricDensityDecomposition`, `IsometricImmersion_Darboux_QPositiveFloor`, `IsometricImmersion_Darboux_SixVariableDarboux`, `IsometricImmersion_Energy_ActualRemainderL2`, `IsometricImmersion_Energy_DirectedBounds`, `IsometricImmersion_Energy_DirectedCoercivity`, `IsometricImmersion_Energy_DirectedFarNegative`, `IsometricImmersion_Energy_MixedDerivativeL2`, `IsometricImmersion_Energy_MixedRemainderL2`, `IsometricImmersion_Energy_WeightPrimitive`, `IsometricImmersion_Energy_WeightPrimitiveParameter`, `IsometricImmersion_Energy_WeightedMultiplier`, `IsometricImmersion_Estimates_ActualHighEquation`, `IsometricImmersion_Estimates_ActualRemainderFactors`, `IsometricImmersion_Estimates_MixedRemainderFactors`, `IsometricImmersion_Flows_PatchFlowCoercivity`, `IsometricImmersion_Immersions_BoundedHeightClasses`, `IsometricImmersion_Metrics_LocalMetricPCoefficients`, `IsometricImmersion_Metrics_MetricPBundleBounds`, `IsometricImmersion_Metrics_PatchTensorRestriction`, `IsometricImmersion_Metrics_SmoothMetricRestriction`, `IsometricImmersion_Metrics_UniversalMetricP`, `IsometricImmersion_Obstructions_PatchAdmissibility`, `IsometricImmersion_Taylor_ScalarChainExpansion`, `IsometricImmersion_Volterra_VolterraGlue`, `IsometricImmersion_Volterra_VolterraJointSmooth`, `IsometricImmersion_Volterra_VolterraParameterJets`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II003`, `Q226II004` and `Q226II005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II011`, `Q226II012` and `Q226II013`.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 334; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Encodable.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Set.Pi
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II003
import Definitions.Def_Q226II004
import Definitions.Def_Q226II005

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_WeightedMultiplier
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {I : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem directedWeight_partial_s_factored
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (hd : edgeDistance b p ≠ 0) :
    coordPartial 1 (directedWeight b lambda I) p =
      directedWeight b lambda I p * (-weightH0 b lambda p + coordPartial 1 I p) := by
  rw [directedWeight_partial_s b lambda hI]
  unfold directedWeight weightH0
  field_simp [hd]
  ring

theorem directed_coefficients
    (A B C : Coord → ℝ) (b lambda epsilon : ℝ)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p)
    (hd : edgeDistance b p ≠ 0) :
    multiplierT B (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        ((weightH0 b lambda p - coordPartial 1 I p - epsilon +
          epsilon * p 0 * (2 * B p - coordPartial 0 I p)) / 2) ∧
    multiplierS A C (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        (coordPartial 1 A p / 2 - weightH0 b lambda p * A p / 2 +
          epsilon * p 0 * coordPartial 0 A p / 2 - C p +
          A p * (coordPartial 1 I p + epsilon + epsilon * p 0 * coordPartial 0 I p) / 2) ∧
    multiplierJ A B C (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        (coordPartial 0 I p - B p + epsilon * p 0 *
          (C p - coordPartial 1 A p + A p * (weightH0 b lambda p - coordPartial 1 I p))) := by
  have hm := directedM_differentiableAt b lambda hI
  have hn := directedN_differentiableAt b lambda epsilon hI
  have hwt := directedWeight_partial_t b lambda hI
  have hws := directedWeight_partial_s_factored b lambda hI hd
  constructor
  · unfold multiplierT
    rw [directedM_partial, directedN_partial b lambda epsilon hI]
    simp only [Fin.isValue, ↓reduceIte, mul_one, hwt, hws, directedN]
    ring
  constructor
  · unfold multiplierS
    rw [HessianCalculus.coordPartial_mul_at hA hm 1,
      HessianCalculus.coordPartial_mul_at hA hn 0,
      directedM_partial, directedN_partial b lambda epsilon hI]
    simp only [Fin.isValue, ↓reduceIte, mul_one, hwt, hws, directedM, directedN]
    ring
  · unfold multiplierJ
    rw [HessianCalculus.coordPartial_mul_at hA hn 1,
      directedM_partial, directedN_partial b lambda epsilon hI]
    have h01 : ¬((0 : Fin 2) = 1) := by decide
    simp only [Fin.isValue, h01, ↓reduceIte, mul_zero, zero_mul, zero_add,
      hwt, hws, directedM, directedN]
    ring

theorem directedS_transverse_expansion
    (A B C : Coord → ℝ) (b lambda epsilon : ℝ) (ell : ℕ) (r : ℝ)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p)
    (hd : edgeDistance b p ≠ 0)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r) :
    multiplierS A C (directedM b lambda I) (directedN b lambda epsilon I) p =
      directedWeight b lambda I p *
        (-((ell : ℝ) + 1 / 2) * coordPartial 1 A p +
          epsilon * p 0 * coordPartial 0 A p / 2 - weightH0 b lambda p * A p / 2 +
          A p * ((coordPartial 1 I p + epsilon + epsilon * p 0 * coordPartial 0 I p) / 2 - r)) := by
  rw [(directed_coefficients A B C b lambda epsilon hA hI hd).2.1, hC]
  ring

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_OrientedPatchSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

theorem orientedClosedPatch_subset_square (n k : ℕ) (R : OrientationLabel)
    {c : Coord} (hc : c ∈ orientedExteriorCenters n k R) :
    orientedClosedPatch n k R c ⊆ square :=
  (orientedClosedPatch_subset_enlarged n k R hc).trans (enlargedAccumulatingDisk_subset_square n)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_PatchCurvatureProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter Metric

namespace SmoothLocal.Geometry
open SmoothLocal.Weighted SmoothLocal.Model

theorem openPatchBox_subset_closedPatchBox : openPatchBox ⊆ closedPatchBox := by
  intro x hx i
  exact ⟨(hx i).1.le, (hx i).2.le⟩

def affinePatchProfile (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) : Coord → ℝ :=
  localPatchProfile ∘ affineInverseCoordinates c R

theorem affinePatchProfile_contDiff (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ ∞ (affinePatchProfile c R) :=
  localPatchProfile_contDiff.comp (affineInverseCoordinates_contDiff c R)

theorem affinePatchProfile_support (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : IsUnit R) : Function.support (affinePatchProfile c R) =
      affineCoordinates c R '' Function.support localPatchProfile := by
  ext p
  constructor
  · intro hp
    exact ⟨affineInverseCoordinates c R p, hp,
      affineCoordinates_affineInverseCoordinates c R hR p⟩
  · rintro ⟨q, hq, rfl⟩
    simpa only [Function.mem_support, affinePatchProfile, Function.comp_apply,
      affineInverseCoordinates_affineCoordinates c R hR] using hq

theorem affinePatchProfile_tsupport (c : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : IsUnit R) : tsupport (affinePatchProfile c R) =
      affineCoordinates c R '' tsupport localPatchProfile := by
  rw [tsupport, affinePatchProfile_support c R hR]
  exact ((affineCoordinateHomeomorph c R hR).image_closure
    (Function.support localPatchProfile)).symm

theorem affinePatchProfile_hasCompactSupport (c : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    HasCompactSupport (affinePatchProfile c R) := by
  change IsCompact (tsupport (affinePatchProfile c R))
  rw [affinePatchProfile_tsupport c R hR]
  exact localPatchProfile_hasCompactSupport.image (affineCoordinates_contDiff c R).continuous

theorem affinePatchProfile_tsupport_strictly_inside (c : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    tsupport (affinePatchProfile c R) ⊆ affineCoordinates c R '' openPatchBox := by
  rw [affinePatchProfile_tsupport c R hR]
  exact Set.image_mono localPatchProfile_tsupport_strictly_inside

def orientedPatchProfile (n k : ℕ) (R : OrientationLabel) (c : Coord) : Coord → ℝ :=
  affinePatchProfile c (orientedPatchScale n k R • R.val)

theorem orientedPatchProfile_contDiff (n k : ℕ) (R : OrientationLabel) (c : Coord) :
    ContDiff ℝ ∞ (orientedPatchProfile n k R c) := affinePatchProfile_contDiff _ _

theorem orientedPatchProfile_hasCompactSupport (n k : ℕ) (R : OrientationLabel) (c : Coord) :
    HasCompactSupport (orientedPatchProfile n k R c) :=
  affinePatchProfile_hasCompactSupport _ _ (orientedPatchMatrix_isUnit n k R)

theorem orientedPatchProfile_tsupport_subset_patch (n k : ℕ) (R : OrientationLabel) (c : Coord) :
    tsupport (orientedPatchProfile n k R c) ⊆ orientedClosedPatch n k R c :=
  (affinePatchProfile_tsupport_strictly_inside c _ (orientedPatchMatrix_isUnit n k R)).trans
    (Set.image_mono openPatchBox_subset_closedPatchBox)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_AssemblyProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.Geometry

def patchAddressProfile (a : PatchAddress) : Coord → ℝ :=
  orientedPatchProfile a.1 a.2.1 a.2.2.1 a.2.2.2.val

theorem patchAddressCarriers_pairwise_disjoint :
    Pairwise (fun a b => Disjoint (patchAddressCarrier a) (patchAddressCarrier b)) := by
  intro a b hab
  rcases a with ⟨n, k, R, c, hc⟩
  rcases b with ⟨m, l, S, d, hd⟩
  by_cases hnm : n = m
  · subst m
    by_cases hkl : k = l
    · subst l
      by_cases hRS : R = S
      · subst S
        apply orientedClosedPatches_disjoint_same_layer n k R hc hd
        intro hcd
        subst d
        exact hab rfl
      · apply orientedClosedPatches_disjoint_different_layers n
          (a := (k, R)) (b := (k, S)) _ hc hd
        exact fun h => hRS (congrArg Prod.snd h)
    · apply orientedClosedPatches_disjoint_different_layers n
        (a := (k, R)) (b := (l, S)) _ hc hd
      exact fun h => hkl (congrArg Prod.fst h)
  · exact orientedClosedPatches_disjoint_different_disks hnm k l R S hc hd

def assemblyProfile : AssemblyProfileIndex → Coord → ℝ
  | .inl n => accumulatingDiskProfile n
  | .inr a => patchAddressProfile a

theorem assemblyProfile_contDiff (i : AssemblyProfileIndex) : ContDiff ℝ ∞ (assemblyProfile i) := by
  cases i with
  | inl n => exact accumulatingDiskProfile_contDiff n
  | inr a => exact orientedPatchProfile_contDiff _ _ _ _

theorem assemblyProfile_hasCompactSupport (i : AssemblyProfileIndex) :
    HasCompactSupport (assemblyProfile i) := by
  cases i with
  | inl n => exact accumulatingDiskProfile_hasCompactSupport n
  | inr a => exact orientedPatchProfile_hasCompactSupport _ _ _ _

theorem assemblyProfile_tsupport_subset (i : AssemblyProfileIndex) :
    tsupport (assemblyProfile i) ⊆ assemblyCarrier i := by
  cases i with
  | inl n => exact accumulatingDiskProfile_tsupport_subset n
  | inr a => exact orientedPatchProfile_tsupport_subset_patch _ _ _ _

theorem assemblyCarriers_pairwise_disjoint :
    Pairwise (fun i j => Disjoint (assemblyCarrier i) (assemblyCarrier j)) := by
  intro i j hij
  cases i with
  | inl n =>
    cases j with
    | inl m => exact accumulatingDisks_pairwise_disjoint (fun h => hij (congrArg Sum.inl h))
    | inr a =>
      exact (orientedClosedPatch_disjoint_every_disk a.1 a.2.1 a.2.2.1 a.2.2.2.property n).symm
  | inr a =>
    cases j with
    | inl n => exact orientedClosedPatch_disjoint_every_disk a.1 a.2.1 a.2.2.1 a.2.2.2.property n
    | inr b => exact patchAddressCarriers_pairwise_disjoint (fun h => hij (congrArg Sum.inr h))

def enumeratedAssemblyProfile (j : ℕ) : Coord → ℝ :=
  match Encodable.decode₂ AssemblyProfileIndex j with
  | none => 0
  | some i => assemblyProfile i

theorem enumeratedAssemblyProfile_contDiff (j : ℕ) :
    ContDiff ℝ ∞ (enumeratedAssemblyProfile j) := by
  cases h : Encodable.decode₂ AssemblyProfileIndex j with
  | none =>
      simp only [enumeratedAssemblyProfile, h]
      change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ))
      exact contDiff_const
  | some i => simpa only [enumeratedAssemblyProfile, h] using assemblyProfile_contDiff i

theorem enumeratedAssemblyProfile_hasCompactSupport (j : ℕ) :
    HasCompactSupport (enumeratedAssemblyProfile j) := by
  cases h : Encodable.decode₂ AssemblyProfileIndex j with
  | none => simpa only [enumeratedAssemblyProfile, h] using
      (HasCompactSupport.zero : HasCompactSupport (0 : Coord → ℝ))
  | some i => simpa only [enumeratedAssemblyProfile, h] using assemblyProfile_hasCompactSupport i

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_CoordinateJetNorm
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

theorem coordinateBound_five_of_frechet_eight {f : Coord → ℝ} {U S : Set Coord} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : S ⊆ U)
    (hB : ∀ k ≤ 8, ∀ p ∈ S, ‖iteratedFDeriv ℝ k f p‖ ≤ M) :
    CoordinateBound f S 5 M :=
  (coordinateBound_of_frechet_bounds hf hU hSU hB).mono (by norm_num) le_rfl

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MetricTwoJet
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

theorem metric_inverse_derivative_identity {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d i j : Fin 2) :
    (∑ a, (coordPartial d (fun q => g q i a) p * inverseMetric g p a j +
      g p i a * coordPartial d (fun q => inverseMetric g q a j) p)) = 0 := by
  have hproduct : (fun q => ∑ a, g q i a * inverseMetric g q a j) =ᶠ[𝓝 p]
      (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact congrFun (congrFun
      (Matrix.mul_nonsing_inv (g q) ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 q hq).isUnit)) i) j
  have hdg (a : Fin 2) : DifferentiableAt ℝ (fun q => g q i a) p :=
    (((hg.1 i a) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdi (a : Fin 2) : DifferentiableAt ℝ (fun q => inverseMetric g q a j) p :=
    (((inverseMetric_contDiffOn hg a j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hzero : coordPartial d (fun q => ∑ a, g q i a * inverseMetric g q a j) p = 0 := by
    unfold coordPartial
    rw [hproduct.fderiv_eq]
    simp
  have hmul (a : Fin 2) : DifferentiableAt ℝ
      (fun q => g q i a * inverseMetric g q a j) p := (hdg a).mul (hdi a)
  rw [HessianCalculus.coordPartial_sum_two _ hmul d] at hzero
  simpa only [HessianCalculus.coordPartial_mul_at (hdg _) (hdi _) d] using hzero

theorem christoffel_coordPartial_formula {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d k i j : Fin 2) :
    coordPartial d (christoffel g k i j) p = (1 / 2 : ℝ) * ∑ l,
      (coordPartial d (fun q => inverseMetric g q k l) p *
        (coordPartial i (fun q => g q j l) p + coordPartial j (fun q => g q i l) p -
          coordPartial l (fun q => g q i j) p) +
        inverseMetric g p k l *
          (coordPartial d (coordPartial i (fun q => g q j l)) p +
            coordPartial d (coordPartial j (fun q => g q i l)) p -
            coordPartial d (coordPartial l (fun q => g q i j)) p)) := by
  have hdg (a b c : Fin 2) : DifferentiableAt ℝ (coordPartial a (fun q => g q b c)) p :=
    (((partial_contDiffOn (hg.1 b c) hU a) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdi (l : Fin 2) : DifferentiableAt ℝ (fun q => inverseMetric g q k l) p :=
    (((inverseMetric_contDiffOn hg k l) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let B : Fin 2 → Coord → ℝ := fun l q =>
    coordPartial i (fun q => g q j l) q + coordPartial j (fun q => g q i l) q -
      coordPartial l (fun q => g q i j) q
  have hB (l : Fin 2) : DifferentiableAt ℝ (B l) p :=
    ((hdg i j l).add (hdg j i l)).sub (hdg l i j)
  have hDB (l : Fin 2) : coordPartial d (B l) p =
      coordPartial d (coordPartial i (fun q => g q j l)) p +
        coordPartial d (coordPartial j (fun q => g q i l)) p -
        coordPartial d (coordPartial l (fun q => g q i j)) p := by
    change coordPartial d (fun q =>
      (coordPartial i (fun q => g q j l) q + coordPartial j (fun q => g q i l) q) -
        coordPartial l (fun q => g q i j) q) p = _
    have hadd : DifferentiableAt ℝ
        (fun q => coordPartial i (fun q => g q j l) q + coordPartial j (fun q => g q i l) q) p :=
      (hdg i j l).add (hdg j i l)
    rw [HessianCalculus.coordPartial_sub_at hadd (hdg l i j) d,
      HessianCalculus.coordPartial_add_at (hdg i j l) (hdg j i l) d]
  have hsum : DifferentiableAt ℝ (fun q => ∑ l, inverseMetric g q k l * B l q) p :=
    DifferentiableAt.fun_sum fun l _ => (hdi l).mul (hB l)
  change coordPartial d (fun q => (1 / 2 : ℝ) * ∑ l, inverseMetric g q k l * B l q) p = _
  have hterm (l : Fin 2) : DifferentiableAt ℝ
      (fun q => inverseMetric g q k l * B l q) p := (hdi l).mul (hB l)
  rw [MetricJetCalculus.coordPartial_const_mul_at hsum _ d,
    HessianCalculus.coordPartial_sum_two _ hterm d]
  simp only [HessianCalculus.coordPartial_mul_at (hdi _) (hB _) d, hDB, B]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_PatchGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Model

theorem gaussianCurvature_eventuallyEq_of_metric_eventuallyEq
    {g h : MetricField} {p : Coord} (heq : g =ᶠ[𝓝 p] h) :
    gaussianCurvature g =ᶠ[𝓝 p] gaussianCurvature h := by
  filter_upwards [heq.eventuallyEq_nhds] with q hq
  exact gaussianCurvature_eq_of_eventuallyEq hq

theorem patch_smallCurvature_eventually_model
    {g0 eta : MetricField} {kappa : ℝ} {U : Set Coord}
    (hk : 0 < kappa) (hU : IsOpen U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    {p : Coord} (hp : p ∈ U)
    (hsmall : |gaussianCurvature (g0 + eta) p| ≤ kappa / 8) :
    gaussianCurvature (g0 + eta) =ᶠ[𝓝 p] modelCurvature kappa := by
  have hout : p ∉ patchBox := by
    intro hin
    have hneg := hcentral p (patchBox_subset_centralBox hin)
    have hlo := (abs_le.mp hsmall).1
    linarith
  have hts : p ∉ tsupport eta := fun hin => hout (hsupport hin)
  have hsame := gaussianCurvature_eventuallyEq_of_metric_eventuallyEq
    (metric_add_eventuallyEq_of_not_mem_tsupport g0 eta hts)
  have hmodel : gaussianCurvature g0 =ᶠ[𝓝 p] modelCurvature kappa := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hbackground q hq
  exact hsame.trans hmodel

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureParameter
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem curvatureYDerivative_smooth {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square) :
    ∀ n, ContDiffOn ℝ ∞ (curvatureYDerivative K n) square := by
  intro n
  induction n with
  | zero => exact hK
  | succ n hn => exact partial_contDiffOn hn coordinate_square_isOpen 1

theorem coordinateCurvatureFamily_apply {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square) (r : ℝ) (hr1 : r < 1)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) (x : Icc (-r) r) :
    coordinateCurvatureFamily K r y x = K (coordinatePoint x y) := by
  have hc : Continuous (fun z : Icc (-r) r => K (coordinatePoint z y)) :=
    hK.continuousOn.comp_continuous (by unfold coordinatePoint; fun_prop)
      (fun z => coordinatePoint_mem_square (compact_x_mem_square_interval hr1 z) hy)
  unfold coordinateCurvatureFamily
  rw [ContinuousMap.mkD_of_continuous hc]
  rfl

theorem coordinateCurvatureFamily_contDiffOn {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square) (r : ℝ) (hr1 : r < 1) :
    ContDiffOn ℝ ∞ (coordinateCurvatureFamily K r) (Ioo (-1 : ℝ) 1) := by
  let H : ℕ → ℝ → Icc (-r) r → ℝ :=
    fun n y x => curvatureYDerivative K n (coordinatePoint x y)
  have hpointMem (y : ℝ) (hy : y ∈ Ioo (-1 : ℝ) 1) (x : Icc (-r) r) :
      coordinatePoint x y ∈ square :=
    coordinatePoint_mem_square (compact_x_mem_square_interval hr1 x) hy
  have hjoint (n : ℕ) : ContinuousOn (Function.uncurry (H n))
      ((Ioo (-1 : ℝ) 1) ×ˢ (Set.univ : Set (Icc (-r) r))) := by
    have hmap : Continuous (fun p : ℝ × Icc (-r) r => coordinatePoint p.2 p.1) := by
      unfold coordinatePoint
      fun_prop
    exact (curvatureYDerivative_smooth hK n).continuousOn.comp hmap.continuousOn
      (fun p hp => hpointMem p.1 hp.1 p.2)
  have hderiv (n : ℕ) (y : ℝ) (hy : y ∈ Ioo (-1 : ℝ) 1) (x : Icc (-r) r) :
      HasDerivAt (fun s => H n s x) (H (n + 1) y x) y := by
    have hd : DifferentiableAt ℝ (curvatureYDerivative K n) (coordinatePoint x y) :=
      ((curvatureYDerivative_smooth hK n).contDiffAt
        (coordinate_square_isOpen.mem_nhds (hpointMem y hy x))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    change HasDerivAt (fun s => curvatureYDerivative K n (coordinatePoint x s))
      (coordPartial 1 (curvatureYDerivative K n) (coordinatePoint x y)) y
    exact hd.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y x y)
  have hs := smooth_curry_of_joint_derivative_sequence H hjoint hderiv 0
  change ContDiffOn ℝ ∞
    (fun y => ContinuousMap.mkD (fun x : Icc (-r) r => K (coordinatePoint x y)) 0)
    (Ioo (-1 : ℝ) 1)
  exact hs

theorem coordinateCurvatureFamily_norm_le {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr1 : r < 1) {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    ‖coordinateCurvatureFamily K r y‖ ≤ (1 : ℝ) / 1000 := by
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1 / 1000)).mpr
  intro x
  rw [coordinateCurvatureFamily_apply hK r hr1 hy x, Real.norm_eq_abs]
  exact hbound _ (coordinatePoint_mem_square (compact_x_mem_square_interval hr1 x) hy)

def prescribedVolterraFamily (K : Coord → ℝ) (r : ℝ) (hr : 0 < r) (y : ℝ) :
    IntervalFunctions r :=
  volterraSolution r hr (coordinateCurvatureFamily K r y)

theorem prescribedVolterraFamily_contDiffOn {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ContDiffOn ℝ ∞ (prescribedVolterraFamily K r hr) (Ioo (-1 : ℝ) 1) :=
  volterraSolution_family_contDiffOn r hr hr1.le
    (coordinateCurvatureFamily_contDiffOn hK r hr1)
    (fun _ hy => coordinateCurvatureFamily_norm_le hK hbound r hr1 hy)

theorem prescribedVolterraFamily_equation {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    prescribedVolterraFamily K r hr y + volterraCLM r hr
      (coordinateCurvatureFamily K r y * prescribedVolterraFamily K r hr y) = 1 :=
  volterraSolution_equation r hr hr1.le (coordinateCurvatureFamily K r y)
    (coordinateCurvatureFamily_norm_le hK hbound r hr1 hy)

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraParameterJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

theorem intervalFamilyJet_mul (r : ℝ) (hr : 0 < r)
    {s : Set ℝ} (hs : IsOpen s) {K F : ℝ → IntervalFunctions r}
    (hK : ContDiffOn ℝ ∞ K s) (hF : ContDiffOn ℝ ∞ F s)
    (n : ℕ) (x : ℝ) {y : ℝ} (hy : y ∈ s) :
    intervalFamilyJet r hr (fun t => K t * F t) n (x, y) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        intervalFamilyJet r hr K i (x, y) *
        intervalFamilyJet r hr F (n - i) (x, y) := by
  have he := iteratedDeriv_fun_mul (f := K) (g := F) (n := n) (x := y)
    ((hK.contDiffAt (hs.mem_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top : (n : ℕ∞ω) ≤ ∞))
    ((hF.contDiffAt (hs.mem_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top : (n : ℕ∞ω) ≤ ∞))
  unfold intervalFamilyJet
  rw [he]
  simp [intervalExtension, ContinuousMap.IccExtendCM, ContinuousMap.projIccCM]

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureParameterJets
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem curvatureYDerivative_slice_hasDerivAt
    {K : Coord → ℝ} (hK : ContDiffOn ℝ ∞ K square)
    (n : ℕ) {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => curvatureYDerivative K n (coordinatePoint x t))
      (curvatureYDerivative K (n + 1) (coordinatePoint x y)) y := by
  have hd : DifferentiableAt ℝ (curvatureYDerivative K n) (coordinatePoint x y) :=
    ((curvatureYDerivative_smooth hK n).contDiffAt
      (coordinate_square_isOpen.mem_nhds (coordinatePoint_mem_square hx hy))).differentiableAt
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hd.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y x y)

theorem coordinateCurvatureFamily_jet_apply
    {K : Coord → ℝ} (hK : ContDiffOn ℝ ∞ K square)
    (r : ℝ) (hr1 : r < 1) (n : ℕ) (x : Icc (-r) r)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    iteratedDeriv n (coordinateCurvatureFamily K r) y x =
      curvatureYDerivative K n (coordinatePoint x y) := by
  have heval := iteratedDeriv_clm_comp (ContinuousMap.evalCLM ℝ x) n
    ((coordinateCurvatureFamily_contDiffOn hK r hr1).contDiffAt
      (isOpen_Ioo.mem_nhds hy))
  have hev : (fun t => coordinateCurvatureFamily K r t x) =ᶠ[𝓝 y]
      (fun t => K (coordinatePoint x t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact coordinateCurvatureFamily_apply hK r hr1 ht x
  have hs := iteratedDeriv_eq_of_derivative_sequence isOpen_Ioo
    (fun j t => curvatureYDerivative K j (coordinatePoint x t))
    (fun j t ht => curvatureYDerivative_slice_hasDerivAt hK j
      (compact_x_mem_square_interval hr1 x) ht) n y hy
  calc
    iteratedDeriv n (coordinateCurvatureFamily K r) y x =
        iteratedDeriv n (fun t => coordinateCurvatureFamily K r t x) y := heval.symm
    _ = iteratedDeriv n (fun t => K (coordinatePoint x t)) y := hev.iteratedDeriv_eq n
    _ = curvatureYDerivative K n (coordinatePoint x y) := hs

theorem coordinateCurvatureFamily_jet_contDiffOn
    {K : Coord → ℝ} (hK : ContDiffOn ℝ ∞ K square)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    ContDiffOn ℝ ∞ (intervalFamilyJet r hr (coordinateCurvatureFamily K r) n)
      (Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1) := by
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => coordinatePoint p.1 p.2) := by
    unfold coordinatePoint
    fun_prop
  have hmem : MapsTo (fun p : ℝ × ℝ => coordinatePoint p.1 p.2)
      (Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1) square := by
    intro p hp
    exact coordinatePoint_mem_square
      ⟨(neg_lt_neg hr1).trans hp.1.1, hp.1.2.trans hr1⟩ hp.2
  have hc := (curvatureYDerivative_smooth hK n).comp hmap.contDiffOn hmem
  apply hc.congr
  intro p hp
  unfold intervalFamilyJet
  rw [intervalExtension_apply_of_mem r hr _ ⟨hp.1.1.le, hp.1.2.le⟩]
  exact coordinateCurvatureFamily_jet_apply hK r hr1 n _ hp.2

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraJointSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

theorem volterra_family_joint_smooth
    (r : ℝ) (hr : 0 < r) {s : Set ℝ} (hs : IsOpen s)
    {K F P : ℝ → IntervalFunctions r}
    (hK : ContDiffOn ℝ ∞ K s) (hF : ContDiffOn ℝ ∞ F s)
    (hP : ContDiffOn ℝ ∞ P s)
    (hKjets : ∀ j, ContDiffOn ℝ ∞ (intervalFamilyJet r hr K j) (Ioo (-r) r ×ˢ s))
    (c : ℝ)
    (hFP : ∀ y ∈ s,
      F y = ContinuousMap.const (Icc (-r) r) c + primitiveCLM r hr (P y))
    (hPQ : ∀ y ∈ s, P y = primitiveCLM r hr (-(K y * F y))) :
    ∀ j, ContDiffOn ℝ ∞ (intervalFamilyJet r hr F j) (Ioo (-r) r ×ˢ s) ∧
      ContDiffOn ℝ ∞ (intervalFamilyJet r hr P j) (Ioo (-r) r ×ˢ s) := by
  let D : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ s
  let Q : ℝ → IntervalFunctions r := fun y => -(K y * F y)
  have hD : IsOpen D := isOpen_Ioo.prod hs
  have hQ : ContDiffOn ℝ ∞ Q s := (hK.mul hF).neg
  have hdxF (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => intervalFamilyJet r hr F j (x, p.2))
        (intervalFamilyJet r hr P j p) p.1 :=
    intervalFamilyJet_hasDerivAt_x_of_primitive r hr hs hP c hFP j hp.1 hp.2
  have hdxP (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => intervalFamilyJet r hr P j (x, p.2))
        (intervalFamilyJet r hr Q j p) p.1 := by
    apply intervalFamilyJet_hasDerivAt_x_of_primitive r hr hs hQ 0 _ j hp.1 hp.2
    intro y hy
    change P y = 0 + primitiveCLM r hr (Q y)
    rw [zero_add]
    exact hPQ y hy
  have hdyF (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => intervalFamilyJet r hr F j (p.1, y))
        (intervalFamilyJet r hr F (j + 1) p) p.2 :=
    intervalFamilyJet_hasDerivAt_y r hr hs hF j p.1 hp.2
  have hdyP (j : ℕ) (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => intervalFamilyJet r hr P j (p.1, y))
        (intervalFamilyJet r hr P (j + 1) p) p.2 :=
    intervalFamilyJet_hasDerivAt_y r hr hs hP j p.1 hp.2
  have hnat : ∀ n : ℕ, ∀ j,
      ContDiffOn ℝ n (intervalFamilyJet r hr F j) D ∧
      ContDiffOn ℝ n (intervalFamilyJet r hr P j) D := by
    intro n
    induction n with
    | zero =>
        intro j
        constructor
        · simpa only [Nat.cast_zero, contDiffOn_zero] using
            (intervalFamilyJet_continuousOn r hr hs hF j).mono
              (fun p hp => ⟨mem_univ p.1, hp.2⟩)
        · simpa only [Nat.cast_zero, contDiffOn_zero] using
            (intervalFamilyJet_continuousOn r hr hs hP j).mono
              (fun p hp => ⟨mem_univ p.1, hp.2⟩)
    | succ n hn =>
        intro j
        have hQj : ContDiffOn ℝ n (intervalFamilyJet r hr Q j) D := by
          have hsum : ContDiffOn ℝ n (fun p =>
              ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
                intervalFamilyJet r hr K i p * intervalFamilyJet r hr F (j - i) p) D :=
            ContDiffOn.sum (fun i hi =>
              (contDiffOn_const.mul (contDiffOn_infty.mp (hKjets i) n)).mul (hn (j - i)).1)
          apply hsum.neg.congr
          intro p hp
          have hneg : intervalFamilyJet r hr Q j p =
              -intervalFamilyJet r hr (fun y => K y * F y) j p := by
            simp only [intervalFamilyJet, Q, iteratedDeriv_fun_neg]
            rfl
          rw [hneg, intervalFamilyJet_mul r hr hs hK hF j p.1 hp.2]
        exact ⟨contDiffOn_succ_of_continuous_partials hD n (hn j).2 (hn (j + 1)).1
            (hdxF j) (hdyF j),
          contDiffOn_succ_of_continuous_partials hD n hQj (hn (j + 1)).2
            (hdxP j) (hdyP j)⟩
  intro j
  exact ⟨contDiffOn_infty.mpr (fun n => (hnat n j).1),
    contDiffOn_infty.mpr (fun n => (hnat n j).2)⟩

def prescribedVelocityFamily (K : SmoothLocal.Geometry.Coord → ℝ)
    (r : ℝ) (hr : 0 < r) (y : ℝ) : IntervalFunctions r :=
  primitiveCLM r hr (-(coordinateCurvatureFamily K r y * prescribedVolterraFamily K r hr y))

theorem prescribedVolterraFamily_joint_contDiffOn
    {K : SmoothLocal.Geometry.Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K SmoothLocal.Geometry.square)
    (hbound : ∀ p ∈ SmoothLocal.Geometry.square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      intervalExtension r hr (prescribedVolterraFamily K r hr p.2) p.1)
      (Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1) := by
  have hKB := coordinateCurvatureFamily_contDiffOn hK r hr1
  have hFB := prescribedVolterraFamily_contDiffOn hK hbound r hr hr1
  have hPB : ContDiffOn ℝ ∞ (prescribedVelocityFamily K r hr) (Ioo (-1 : ℝ) 1) :=
    contDiffOn_const.clm_apply (hKB.mul hFB).neg
  have hFP : ∀ y ∈ Ioo (-1 : ℝ) 1, prescribedVolterraFamily K r hr y =
      ContinuousMap.const (Icc (-r) r) 1 +
        primitiveCLM r hr (prescribedVelocityFamily K r hr y) := by
    intro y hy
    have he := prescribedVolterraFamily_equation hK hbound r hr hr1 hy
    change prescribedVolterraFamily K r hr y +
      primitiveCLM r hr (primitiveCLM r hr
        (coordinateCurvatureFamily K r y * prescribedVolterraFamily K r hr y)) = 1 at he
    change prescribedVolterraFamily K r hr y = 1 +
      primitiveCLM r hr (prescribedVelocityFamily K r hr y)
    simpa only [prescribedVelocityFamily, map_neg, sub_eq_add_neg] using eq_sub_of_add_eq he
  have hj := volterra_family_joint_smooth r hr isOpen_Ioo hKB hFB hPB
    (coordinateCurvatureFamily_jet_contDiffOn hK r hr hr1) 1 hFP
    (fun y hy => rfl) 0
  apply hj.1.congr
  intro p hp
  simp only [intervalFamilyJet, iteratedDeriv_zero]

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraGlue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric
open scoped ContDiff NNReal Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

def prescribedLocalState (K : Coord → ℝ) (r : ℝ) (hr : 0 < r)
    (y x : ℝ) : ℝ × ℝ :=
  (volterraScalar r hr (coordinateCurvatureFamily K r y) x,
    volterraVelocity r hr (coordinateCurvatureFamily K r y) x)

theorem prescribedLocalState_initial {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    prescribedLocalState K r hr y 0 = (1, 0) := by
  apply Prod.ext
  · exact volterraScalar_initial r hr hr1.le _
      (coordinateCurvatureFamily_norm_le hK hbound r hr1 hy)
  · exact volterraVelocity_initial r hr _

theorem prescribedLocalState_hasDerivAt {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    {y x : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (prescribedLocalState K r hr y)
      (curvatureField (fun t => K (coordinatePoint t y)) x
        (prescribedLocalState K r hr y x)) x := by
  have hkx : intervalExtension r hr (coordinateCurvatureFamily K r y) x =
      K (coordinatePoint x y) := by
    rw [intervalExtension_apply_of_mem r hr _ ⟨hx.1.le, hx.2.le⟩]
    exact coordinateCurvatureFamily_apply hK r hr1 hy _
  have hf := volterraScalar_hasDerivAt r hr hr1.le (coordinateCurvatureFamily K r y)
    (coordinateCurvatureFamily_norm_le hK hbound r hr1 hy) hx
  have hp := volterraVelocity_hasDerivAt r hr (coordinateCurvatureFamily K r y) x
  rw [hkx] at hp
  exact hf.prodMk hp

theorem prescribedLocalState_agree {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hr1 : r < 1) (hs1 : s < 1)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    EqOn (prescribedLocalState K r hr y) (prescribedLocalState K s hs y)
      (Ioo (-(min r s)) (min r s)) := by
  have hsubr : Ioo (-(min r s)) (min r s) ⊆ Ioo (-r) r := by
    intro t ht
    constructor <;> linarith [min_le_left r s, ht.1, ht.2]
  have hsubs : Ioo (-(min r s)) (min r s) ⊆ Ioo (-s) s := by
    intro t ht
    constructor <;> linarith [min_le_right r s, ht.1, ht.2]
  apply ODE_solution_unique_of_mem_Ioo
    (v := curvatureField (fun t => K (coordinatePoint t y)))
    (s := fun _ => Set.univ) (K := 1) (t₀ := 0)
  · intro t ht
    have htr := hsubr ht
    have htbig : t ∈ Ioo (-1 : ℝ) 1 :=
      ⟨(neg_lt_neg hr1).trans htr.1, htr.2.trans hr1⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro u _ v _
    exact (curvatureField_lipschitz
      (hbound _ (coordinatePoint_mem_square htbig hy))).dist_le_mul u v
  · have hm : 0 < min r s := lt_min hr hs
    exact ⟨by linarith, hm⟩
  · intro t ht
    exact ⟨prescribedLocalState_hasDerivAt hK hbound r hr hr1 hy (hsubr ht), mem_univ _⟩
  · intro t ht
    exact ⟨prescribedLocalState_hasDerivAt hK hbound s hs hs1 hy (hsubs ht), mem_univ _⟩
  · exact (prescribedLocalState_initial hK hbound r hr hr1 hy).trans
      (prescribedLocalState_initial hK hbound s hs hs1 hy).symm

def globalPrescribedState (K : Coord → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  prescribedLocalState K (interiorRadius p.1) (interiorRadius_pos p.1) p.2 p.1

def globalPrescribedScalar (K : Coord → ℝ) (p : ℝ × ℝ) : ℝ :=
  (globalPrescribedState K p).1

theorem globalPrescribedState_eq_local {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) {p : ℝ × ℝ}
    (hp : p ∈ Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1) :
    globalPrescribedState K p = prescribedLocalState K r hr p.2 p.1 := by
  have hxr : |p.1| < r := abs_lt.mpr hp.1
  have hx1 : |p.1| < 1 := hxr.trans hr1
  exact prescribedLocalState_agree hK hbound (interiorRadius p.1) r
    (interiorRadius_pos p.1) hr (interiorRadius_lt_one hx1) hr1 hp.2
    (abs_lt.mp (lt_min (abs_lt_interiorRadius hx1) hxr))

theorem globalPrescribedScalar_contDiffOn {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000) :
    ContDiffOn ℝ ∞ (globalPrescribedScalar K)
      (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) := by
  intro p hp
  let r := interiorRadius p.1
  have hr : 0 < r := interiorRadius_pos p.1
  have hr1 : r < 1 := interiorRadius_lt_one (abs_lt.mpr hp.1)
  have hpr : p ∈ Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1 :=
    ⟨abs_lt.mp (abs_lt_interiorRadius (abs_lt.mpr hp.1)), hp.2⟩
  have hlocal : ContDiffOn ℝ ∞ (globalPrescribedScalar K)
      (Ioo (-r) r ×ˢ Ioo (-1 : ℝ) 1) := by
    apply (prescribedVolterraFamily_joint_contDiffOn hK hbound r hr hr1).congr
    intro q hq
    exact congrArg Prod.fst (globalPrescribedState_eq_local hK hbound r hr hr1 hq)
  exact (hlocal.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hpr)).contDiffWithinAt

theorem globalPrescribedScalar_bounds {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {p : ℝ × ℝ} (hp : p ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) :
    (998 : ℝ) / 999 ≤ globalPrescribedScalar K p ∧
      globalPrescribedScalar K p ≤ (1000 : ℝ) / 999 ∧ 0 < globalPrescribedScalar K p := by
  exact volterraScalar_bounds (interiorRadius p.1) (interiorRadius_pos p.1)
    (interiorRadius_lt_one (abs_lt.mpr hp.1)).le _
    (coordinateCurvatureFamily_norm_le hK hbound (interiorRadius p.1)
      (interiorRadius_lt_one (abs_lt.mpr hp.1)) hp.2) p.1

def prescribedFactor (K : Coord → ℝ) (p : Coord) : ℝ :=
  globalPrescribedScalar K (p 0, p 1)

theorem prescribedFactor_contDiffOn {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000) :
    ContDiffOn ℝ ∞ (prescribedFactor K) square := by
  have hmap : ContDiff ℝ ∞ (fun p : Coord => (p 0, p 1)) := by fun_prop
  exact (globalPrescribedScalar_contDiffOn hK hbound).comp hmap.contDiffOn
    (fun p hp => ⟨hp 0, hp 1⟩)

theorem prescribedFactor_bounds {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {p : Coord} (hp : p ∈ square) :
    (998 : ℝ) / 999 ≤ prescribedFactor K p ∧
      prescribedFactor K p ≤ (1000 : ℝ) / 999 ∧ 0 < prescribedFactor K p :=
  globalPrescribedScalar_bounds hK hbound ⟨hp 0, hp 1⟩

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_PrescribedCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem globalPrescribedState_hasDerivAt {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => globalPrescribedState K (t, y))
      (curvatureField (fun t => K (coordinatePoint t y)) x
        (globalPrescribedState K (x, y))) x := by
  let r := interiorRadius x
  have hr : 0 < r := interiorRadius_pos x
  have hr1 : r < 1 := interiorRadius_lt_one (abs_lt.mpr hx)
  have hxr : x ∈ Ioo (-r) r := abs_lt.mp (abs_lt_interiorRadius (abs_lt.mpr hx))
  have hev : (fun t => globalPrescribedState K (t, y)) =ᶠ[𝓝 x]
      prescribedLocalState K r hr y := by
    filter_upwards [isOpen_Ioo.mem_nhds hxr] with t ht
    exact globalPrescribedState_eq_local hK hbound r hr hr1 ⟨ht, hy⟩
  have hd := (prescribedLocalState_hasDerivAt hK hbound r hr hr1 hy hxr).congr_of_eventuallyEq hev
  rw [globalPrescribedState_eq_local hK hbound r hr hr1 ⟨hxr, hy⟩]
  exact hd

def prescribedCurvatureMetric (K : Coord → ℝ) : MetricField := warpedMetric (prescribedFactor K)

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_SupportedPerturbations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

def symmetricSupportedSubmodule : Submodule ℝ SupportedTensor where
  carrier := {η | ∀ p i j, η p i j = η p j i}
  zero_mem' := by
    change ∀ p i j, (0 : SupportedTensor) p i j = (0 : SupportedTensor) p j i
    intros
    rfl
  add_mem' := by
    intro η θ hη hθ p i j
    change η p i j + θ p i j = η p j i + θ p j i
    rw [hη p i j, hθ p i j]
  smul_mem' := by
    intro a η hη p i j
    change a * η p i j = a * η p j i
    rw [hη p i j]

abbrev SymmetricPerturbation := symmetricSupportedSubmodule

def perturbationTensor (η : SymmetricPerturbation) : MetricField := η.val

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_EnumeratedPatchTensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

def patchAddressTensor (eta : PatchAddress → SymmetricPerturbation) (a : PatchAddress) : MetricField :=
  affinePushforwardMetric (perturbationTensor (eta a)) (patchAddressCenter a) (patchAddressMatrix a)

def enumeratedPatchTensor (eta : PatchAddress → SymmetricPerturbation) (j : ℕ) : MetricField :=
  match patchTensorAddress j with
  | none => 0
  | some a => patchAddressTensor eta a

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_InitialCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.Geometry
open SmoothLocal.Model

def initialCurvatureAmplitudes : ℕ → ℝ :=
  Classical.choose (exists_positive_diagonal_amplitudes enumeratedAssemblyProfile
    enumeratedAssemblyProfile_contDiff enumeratedAssemblyProfile_hasCompactSupport
    initialCurvatureBudget initialCurvatureBudget_pos)

theorem initialCurvatureAmplitudes_pos (j : ℕ) : 0 < initialCurvatureAmplitudes j :=
  (Classical.choose_spec (exists_positive_diagonal_amplitudes enumeratedAssemblyProfile
    enumeratedAssemblyProfile_contDiff enumeratedAssemblyProfile_hasCompactSupport
    initialCurvatureBudget initialCurvatureBudget_pos)).1 j

def initialCurvatureTerm (j : ℕ) (p : Coord) : ℝ :=
  initialCurvatureAmplitudes j • enumeratedAssemblyProfile j p

theorem initialCurvatureTerm_derivative_bound (j k : ℕ) (hkj : k ≤ j) (p : Coord) :
    ‖iteratedFDeriv ℝ k (initialCurvatureTerm j) p‖ ≤ patchSeriesWeight initialCurvatureBudget j :=
  (Classical.choose_spec (exists_positive_diagonal_amplitudes enumeratedAssemblyProfile
    enumeratedAssemblyProfile_contDiff enumeratedAssemblyProfile_hasCompactSupport
    initialCurvatureBudget initialCurvatureBudget_pos)).2 j k hkj p

theorem initialCurvatureTerm_contDiff (j : ℕ) : ContDiff ℝ ∞ (initialCurvatureTerm j) :=
  (enumeratedAssemblyProfile_contDiff j).const_smul (initialCurvatureAmplitudes j)

theorem initialCurvatureTerm_tsupport (j : ℕ) :
    tsupport (initialCurvatureTerm j) = tsupport (enumeratedAssemblyProfile j) :=
  tsupport_const_smul_eq_of_pos _ (initialCurvatureAmplitudes_pos j)

theorem initialCurvatureTerm_hasCompactSupport (j : ℕ) :
    HasCompactSupport (initialCurvatureTerm j) := by
  change IsCompact (tsupport (initialCurvatureTerm j))
  rw [initialCurvatureTerm_tsupport]
  exact enumeratedAssemblyProfile_hasCompactSupport j

def initialCurvature : Coord → ℝ := flatPatchSum initialCurvatureTerm

theorem initialCurvature_contDiff : ContDiff ℝ ∞ initialCurvature :=
  flatPatchSum_contDiff _ initialCurvatureBudget initialCurvatureTerm_contDiff
    initialCurvatureTerm_hasCompactSupport initialCurvatureTerm_derivative_bound

theorem initialCurvature_abs_le (p : Coord) : |initialCurvature p| ≤ 1 / 2000 := by
  simpa only [Real.norm_eq_abs, initialCurvature, initialCurvatureBudget] using
    flatPatchSum_norm_le initialCurvatureTerm
    initialCurvatureBudget initialCurvatureTerm_derivative_bound p

theorem initialCurvature_small (p : Coord) : |initialCurvature p| ≤ 1 / 1000 := by
  linarith [initialCurvature_abs_le p]

def initialPatchAmplitude (n k : ℕ) (R : OrientationLabel) (c : Coord)
    (hc : c ∈ orientedExteriorCenters n k R) : ℝ :=
  initialCurvatureAmplitudes (Encodable.encode (Sum.inr ⟨n, k, R, c, hc⟩ : AssemblyProfileIndex))

theorem initialPatchAmplitude_pos (n k : ℕ) (R : OrientationLabel) (c : Coord)
    (hc : c ∈ orientedExteriorCenters n k R) : 0 < initialPatchAmplitude n k R c hc :=
  initialCurvatureAmplitudes_pos _

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_InitialAssemblyMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.Geometry
open SmoothLocal.ODE SmoothLocal.Model

def initialAssemblyMetric : MetricField := prescribedCurvatureMetric initialCurvature

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SixVariableDarboux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord}

theorem stateConnection_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (stateConnection g i j) (stateBaseDomain U) := by
  unfold stateConnection jetConnection
  apply ContDiffOn.sum
  intro r hr
  exact ((christoffel_contDiffOn hg hU r i j).comp statePoint_contDiff.contDiffOn
    (fun w hw => hw)).mul (((contDiff_apply ℝ ℝ r).comp stateGradient_contDiff).contDiffOn)

theorem stateMixed_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateMixed g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 4 _).sub (stateConnection_contDiffOn hg hU 0 1)

theorem stateDenominator_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateDenominator g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 5 _).sub (stateConnection_contDiffOn hg hU 1 1)

theorem stateEnergy_contDiffOn (hg : SmoothPositiveOn g U) :
    ContDiffOn ℝ ∞ (stateEnergy g) (stateBaseDomain U) := by
  have hcoef (i j : Fin 2) : ContDiffOn ℝ ∞ (fun w => g (statePoint w) i j) (stateBaseDomain U) :=
    (hg.1 i j).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have hdet : ContDiffOn ℝ ∞ (fun w => (g (statePoint w)).det) (stateBaseDomain U) :=
    (metricDet_contDiffOn hg).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have hv (i : Fin 2) : ContDiffOn ℝ ∞ (fun w => stateGradient w i) (stateBaseDomain U) :=
    ((contDiff_apply ℝ ℝ i).comp stateGradient_contDiff).contDiffOn
  exact hdet.sub ((((hcoef 1 1).mul ((hv 0).pow 2)).sub
    ((((hcoef 0 1).add (hcoef 1 0)).mul (hv 0)).mul (hv 1))).add
      ((hcoef 0 0).mul ((hv 1).pow 2)))

theorem darbouxStateDomain_isOpen (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    IsOpen (darbouxStateDomain g U) := by
  exact (stateDenominator_contDiffOn hg hU).continuousOn.isOpen_inter_preimage
    (stateBaseDomain_isOpen hU) isClosed_singleton.isOpen_compl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_VerticalSliceJets
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem verticalJet_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ n, ContDiffOn ℝ ∞ (verticalJet f n) U := by
  intro n
  induction n with
  | zero => exact hf
  | succ n hn => exact normed_coordPartial_contDiffOn hn hU 1

theorem verticalJet_slice_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ)
    (hp : (![x, y] : Coord) ∈ U) :
    HasDerivAt (fun t => verticalJet f n ![x, t]) (verticalJet f (n + 1) ![x, y]) y := by
  have hd : DifferentiableAt ℝ (verticalJet f n) ![x, y] :=
    (((verticalJet_contDiffOn hU hf n).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  exact hd.hasFDerivAt.comp_hasDerivAt y (verticalPoint_hasDerivAt x y)

theorem verticalJet_slice
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (x : ℝ) : ∀ n y, (![x, y] : Coord) ∈ U →
      iteratedDeriv n (fun t => f ![x, t]) y = verticalJet f n ![x, y] := by
  intro n
  induction n with
  | zero => intro y hy; rfl
  | succ n hn =>
    intro y hy
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun t => f ![x, t]) =ᶠ[𝓝 y]
        (fun t => verticalJet f n ![x, t]) := by
      filter_upwards [(hU.preimage (verticalPoint_contDiff x).continuous).mem_nhds hy] with t ht
      exact hn t ht
    rw [heq.deriv_eq]
    exact (verticalJet_slice_hasDerivAt hU hf n hy).deriv

theorem verticalJet_coordPartial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (i : Fin 2) : ∀ n p, p ∈ U →
      verticalJet (coordPartial i f) n p = coordPartial i (verticalJet f n) p := by
  intro n
  induction n with
  | zero => intro p hp; rfl
  | succ n hn =>
    intro p hp
    have heq : verticalJet (coordPartial i f) n =ᶠ[𝓝 p] coordPartial i (verticalJet f n) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hn q hq
    have hd : coordPartial 1 (verticalJet (coordPartial i f) n) p =
        coordPartial 1 (coordPartial i (verticalJet f n)) p := by
      exact congrArg (fun L : Coord →L[ℝ] V => L (Pi.single 1 1)) heq.fderiv_eq
    change coordPartial 1 (verticalJet (coordPartial i f) n) p =
      coordPartial i (coordPartial 1 (verticalJet f n)) p
    rw [hd]
    exact coordPartial_comm (verticalJet_contDiffOn hU hf n) hU hp 1 i

theorem verticalJet_two_coordPartials
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hp : p ∈ U) (n : ℕ) (i j : Fin 2) :
    verticalJet (coordPartial i (coordPartial j f)) n p =
      coordPartial i (coordPartial j (verticalJet f n)) p := by
  rw [verticalJet_coordPartial hU (normed_coordPartial_contDiffOn hf hU j) i n p hp]
  have heq : verticalJet (coordPartial j f) n =ᶠ[𝓝 p] coordPartial j (verticalJet f n) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact verticalJet_coordPartial hU hf j n q hq
  exact congrArg (fun L : Coord →L[ℝ] V => L (Pi.single i 1)) heq.fderiv_eq

theorem solutionJetCurve_iteratedDeriv
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (n : ℕ) (hn : 2 ≤ n) :
    iteratedDeriv n (solutionJetCurve z x) y =
      ![0, 0, coordPartial 0 (verticalJet z n) ![x, y],
        coordPartial 1 (verticalJet z n) ![x, y],
        coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y],
        coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y]] := by
  have hc := solutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · change iteratedDeriv n (fun _ : ℝ => x) y = 0
    simp [iteratedDeriv_const, show n ≠ 0 by omega]
  · change iteratedDeriv n id y = 0
    simp [iteratedDeriv_id, show n ≠ 0 by omega, show n ≠ 1 by omega]
  · change iteratedDeriv n (fun t => coordPartial 0 z ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn hz hU 0) x n y hp,
      verticalJet_coordPartial hU hz 0 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn hz hU 1) x n y hp,
      verticalJet_coordPartial hU hz 1 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn (normed_coordPartial_contDiffOn hz hU 1) hU 0) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 0 1]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (normed_coordPartial_contDiffOn (normed_coordPartial_contDiffOn hz hU 1) hU 1) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 1 1]
    rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_WeightPrimitive
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry SmoothLocal.ODE

variable {B : Coord → ℝ} {R a b : ℝ}

theorem parameterDerivative_smooth_on_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) :
    ∀ n, ContDiffOn ℝ ∞ (curvatureYDerivative B n) (coordinateRectangle R a b) := by
  intro n
  induction n with
  | zero => exact hB
  | succ n hn => exact partial_contDiffOn hn (coordinateRectangle_isOpen R a b) 1

theorem coefficientFamily_contDiffOn_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hrR : r < R) :
    ContDiffOn ℝ ∞ (coordinateCurvatureFamily B r) (Ioo a b) := by
  let H : ℕ → ℝ → Icc (-r) r → ℝ :=
    fun n y x => curvatureYDerivative B n (coordinatePoint x y)
  have hmem (y : ℝ) (hy : y ∈ Ioo a b) (x : Icc (-r) r) :
      coordinatePoint x y ∈ coordinateRectangle R a b :=
    point_mem_rectangle (compact_t_mem_rectangle_interval hrR x) hy
  have hjoint (n : ℕ) : ContinuousOn (Function.uncurry (H n))
      (Ioo a b ×ˢ (Set.univ : Set (Icc (-r) r))) := by
    have hmap : Continuous (fun p : ℝ × Icc (-r) r => coordinatePoint p.2 p.1) := by
      unfold coordinatePoint
      fun_prop
    exact (parameterDerivative_smooth_on_rectangle hB n).continuousOn.comp
      hmap.continuousOn (fun p hp => hmem p.1 hp.1 p.2)
  have hderiv (n : ℕ) (y : ℝ) (hy : y ∈ Ioo a b) (x : Icc (-r) r) :
      HasDerivAt (fun t => H n t x) (H (n + 1) y x) y := by
    have hd : DifferentiableAt ℝ (curvatureYDerivative B n) (coordinatePoint x y) :=
      ((parameterDerivative_smooth_on_rectangle hB n).contDiffAt
        ((coordinateRectangle_isOpen R a b).mem_nhds (hmem y hy x))).differentiableAt
          (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact hd.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y x y)
  exact smooth_curry_of_joint_derivative_sequence H hjoint hderiv 0

theorem coefficientFamily_jet_apply_on_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hrR : r < R) (n : ℕ) (x : Icc (-r) r)
    {y : ℝ} (hy : y ∈ Ioo a b) :
    iteratedDeriv n (coordinateCurvatureFamily B r) y x =
      curvatureYDerivative B n (coordinatePoint x y) := by
  have heval := iteratedDeriv_clm_comp (ContinuousMap.evalCLM ℝ x) n
    ((coefficientFamily_contDiffOn_rectangle hB r hrR).contDiffAt
      (isOpen_Ioo.mem_nhds hy))
  have hev : (fun t => coordinateCurvatureFamily B r t x) =ᶠ[𝓝 y]
      (fun t => B (coordinatePoint x t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact coefficientFamily_apply_on_rectangle hB r hrR ht x
  have hdseq (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun v => curvatureYDerivative B j (coordinatePoint x v))
        (curvatureYDerivative B (j + 1) (coordinatePoint x t)) t := by
    have hmem : coordinatePoint x t ∈ coordinateRectangle R a b :=
      point_mem_rectangle (compact_t_mem_rectangle_interval hrR x) ht
    have hd : DifferentiableAt ℝ (curvatureYDerivative B j) (coordinatePoint x t) :=
      ((parameterDerivative_smooth_on_rectangle hB j).contDiffAt
        ((coordinateRectangle_isOpen R a b).mem_nhds hmem)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact hd.hasFDerivAt.comp_hasDerivAt t (coordinatePoint_hasDerivAt_y x t)
  have hseq := iteratedDeriv_eq_of_derivative_sequence isOpen_Ioo
    (fun j t => curvatureYDerivative B j (coordinatePoint x t)) hdseq n y hy
  calc
    iteratedDeriv n (coordinateCurvatureFamily B r) y x =
        iteratedDeriv n (fun t => coordinateCurvatureFamily B r t x) y := heval.symm
    _ = iteratedDeriv n (fun t => B (coordinatePoint x t)) y := hev.iteratedDeriv_eq n
    _ = curvatureYDerivative B n (coordinatePoint x y) := hseq

theorem coefficientFamily_jet_contDiffOn_rectangle
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R) (n : ℕ) :
    ContDiffOn ℝ ∞ (intervalFamilyJet r hr (coordinateCurvatureFamily B r) n)
      (Ioo (-r) r ×ˢ Ioo a b) := by
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × ℝ => coordinatePoint p.1 p.2) := by
    unfold coordinatePoint
    fun_prop
  have hmem : MapsTo (fun p : ℝ × ℝ => coordinatePoint p.1 p.2)
      (Ioo (-r) r ×ˢ Ioo a b) (coordinateRectangle R a b) := by
    intro p hp
    exact point_mem_rectangle
      ⟨(neg_lt_neg hrR).trans hp.1.1, hp.1.2.trans hrR⟩ hp.2
  have hc := (parameterDerivative_smooth_on_rectangle hB n).comp hmap.contDiffOn hmem
  apply hc.congr
  intro p hp
  unfold intervalFamilyJet
  rw [intervalExtension_apply_of_mem r hr _ ⟨hp.1.1.le, hp.1.2.le⟩]
  exact coefficientFamily_jet_apply_on_rectangle hB r hrR n _ hp.2

theorem clampedPrimitive_contDiffOn
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    ContDiffOn ℝ ∞ (clampedPrimitive B r hr) (Ioo (-r) r ×ˢ Ioo a b) := by
  have h := primitiveFamily_joint_smooth r hr
    (coefficientFamily_contDiffOn_rectangle hB r hrR)
    (coefficientFamily_jet_contDiffOn_rectangle hB r hr hrR) 0
  apply h.congr
  intro p hp
  simp only [intervalFamilyJet, iteratedDeriv_zero, clampedPrimitive]

theorem coordinatePrimitive_contDiffOn_inner
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    ContDiffOn ℝ ∞ (coordinatePrimitive B) (coordinateRectangle r a b) := by
  have hmap : ContDiff ℝ ∞ (fun p : Coord => (p 0, p 1)) := by fun_prop
  have hmem : MapsTo (fun p : Coord => (p 0, p 1)) (coordinateRectangle r a b)
      (Ioo (-r) r ×ˢ Ioo a b) := fun _ hp => hp
  have hc := (clampedPrimitive_contDiffOn hB r hr hrR).comp hmap.contDiffOn hmem
  apply hc.congr
  intro p hp
  exact (clampedPrimitive_eq_integral hB r hr hrR hp.1 hp.2).symm

theorem coordinatePrimitive_contDiffOn
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) :
    ContDiffOn ℝ ∞ (coordinatePrimitive B) (coordinateRectangle R a b) := by
  intro p hp
  obtain ⟨r, hpr, hrR⟩ := exists_between (abs_lt.mpr hp.1)
  have hr : 0 < r := (abs_nonneg (p 0)).trans_lt hpr
  have hpmem : p ∈ coordinateRectangle r a b := ⟨abs_lt.mp hpr, hp.2⟩
  exact ((coordinatePrimitive_contDiffOn_inner hB r hr hrR).contDiffAt
    ((coordinateRectangle_isOpen r a b).mem_nhds hpmem)).contDiffWithinAt

theorem coordinatePrimitive_partial_t
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b) :
    coordPartial 0 (coordinatePrimitive B) p = B p := by
  have hslice : ContinuousOn (fun t => B (coordinatePoint t (p 1))) (Ioo (-R) R) :=
    hB.continuousOn.comp (by unfold coordinatePoint; fun_prop)
      (fun t ht => point_mem_rectangle ht hp.2)
  have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  have hftc := intervalIntegral.integral_hasDerivAt_right
    (hslice.mono hseg).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hslice (p 0) hp.1)
    (hslice.continuousAt (isOpen_Ioo.mem_nhds hp.1))
  have hftc' : HasDerivAt (fun t => coordinatePrimitive B (coordinatePoint t (p 1)))
      (B p) (p 0) := by
    rw [point_eta] at hftc
    simpa [coordinatePrimitive, coordinatePoint] using hftc
  have hd : DifferentiableAt ℝ (coordinatePrimitive B) (coordinatePoint (p 0) (p 1)) := by
    rw [point_eta]
    exact ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hchain := hd.hasFDerivAt.comp_hasDerivAt (p 0) (point_hasDerivAt_t (p 0) (p 1))
  have hcoord : HasDerivAt (fun t => coordinatePrimitive B (coordinatePoint t (p 1)))
      (coordPartial 0 (coordinatePrimitive B) p) (p 0) := by
    simpa only [point_eta, Function.comp_def, coordPartial] using hchain
  exact hcoord.unique hftc'

theorem primitive_directedJ
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    {p : Coord} (hp : p ∈ coordinateRectangle R a b)
    (A C : Coord → ℝ) (hA : DifferentiableAt ℝ A p)
    (edge lambda epsilon : ℝ) (hd : edgeDistance edge p ≠ 0) :
    multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p =
      directedWeight edge lambda (coordinatePrimitive B) p *
        (epsilon * p 0 * (C p - coordPartial 1 A p +
          A p * (weightH0 edge lambda p - coordPartial 1 (coordinatePrimitive B) p))) := by
  have hI : DifferentiableAt ℝ (coordinatePrimitive B) p :=
    ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he := (directed_coefficients A B C edge lambda epsilon hA hI hd).2.2
  rw [coordinatePrimitive_partial_t hB hR hp] at he
  simpa only [sub_self, zero_add] using he

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff
namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

variable {B : Coord → ℝ} {R a b : ℝ} {p : Coord}

theorem primitive_directedT_lower_bound
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (edge lambda epsilon MI MB : ℝ)
    (heps : 0 ≤ epsilon) (hedge : p 1 < edge)
    (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hBp : |B p| ≤ MB)
    (hlambda : 2 * (MI + epsilon + epsilon * R * MB) ≤ lambda) :
    directedWeight edge lambda (coordinatePrimitive B) p * weightH0 edge lambda p / 4 ≤
      multiplierT B (directedM edge lambda (coordinatePrimitive B))
        (directedN edge lambda epsilon (coordinatePrimitive B)) p := by
  have hI : DifferentiableAt ℝ (coordinatePrimitive B) p :=
    ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : 0 < edgeDistance edge p := sub_pos.mpr hedge
  have hH : lambda ≤ weightH0 edge lambda p := by
    unfold weightH0
    exact le_add_of_nonneg_right (div_nonneg (by norm_num) hd.le)
  have hbound := normalized_T_lower_bound heps hR.le hIs
    (abs_lt.mpr hp.1).le hBp (hlambda.trans hH)
  have hW := (directedWeight_pos edge lambda (coordinatePrimitive B) p hedge).le
  have hcoeff := (directed_coefficients (fun _ => 0) B (fun _ => 0)
    edge lambda epsilon (differentiableAt_const (0 : ℝ)) hI hd.ne').1
  rw [coordinatePrimitive_partial_t hB hR hp] at hcoeff
  rw [hcoeff]
  have hm := mul_le_mul_of_nonneg_left hbound hW
  nlinarith only [hm]

theorem primitive_directedJ_bound
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon MCA MA MI : ℝ)
    (heps : 0 ≤ epsilon) (hedge : p 1 < edge) (hH : 0 ≤ weightH0 edge lambda p)
    (hCA : |C p - coordPartial 1 A p| ≤ MCA)
    (hAp : |A p| ≤ MA) (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI) :
    |multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p| ≤
      directedWeight edge lambda (coordinatePrimitive B) p * epsilon * R *
        (MCA + MA * MI + weightH0 edge lambda p * |A p|) := by
  have hd : 0 < edgeDistance edge p := sub_pos.mpr hedge
  have hW := (directedWeight_pos edge lambda (coordinatePrimitive B) p hedge).le
  have hMA : 0 ≤ MA := (abs_nonneg _).trans hAp
  have hMI : 0 ≤ MI := (abs_nonneg _).trans hIs
  have hprod : |A p * coordPartial 1 (coordinatePrimitive B) p| ≤ MA * MI := by
    rw [abs_mul]
    exact mul_le_mul hAp hIs (abs_nonneg _) hMA
  have hinner : |C p - coordPartial 1 A p +
      A p * (weightH0 edge lambda p - coordPartial 1 (coordinatePrimitive B) p)| ≤
      MCA + MA * MI + weightH0 edge lambda p * |A p| := by
    have he : C p - coordPartial 1 A p +
        A p * (weightH0 edge lambda p - coordPartial 1 (coordinatePrimitive B) p) =
        (C p - coordPartial 1 A p) - A p * coordPartial 1 (coordinatePrimitive B) p +
          weightH0 edge lambda p * A p := by ring
    rw [he]
    calc
      _ ≤ |(C p - coordPartial 1 A p) - A p * coordPartial 1 (coordinatePrimitive B) p| +
          |weightH0 edge lambda p * A p| := abs_add_le _ _
      _ ≤ (|C p - coordPartial 1 A p| +
          |A p * coordPartial 1 (coordinatePrimitive B) p|) +
          |weightH0 edge lambda p * A p| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ _ := by
        rw [abs_mul (weightH0 edge lambda p) (A p), abs_of_nonneg hH]
        exact add_le_add (add_le_add hCA hprod) le_rfl
  rw [primitive_directedJ hB hR hp A C hA edge lambda epsilon hd.ne']
  simp only [abs_mul, abs_of_nonneg hW, abs_of_nonneg heps]
  have ht : |p 0| ≤ R := (abs_lt.mpr hp.1).le
  have hm := mul_le_mul ht hinner (abs_nonneg _) hR.le
  have hm' := mul_le_mul_of_nonneg_left hm (mul_nonneg hW heps)
  nlinarith only [hm']

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedCoercivity
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem primitive_directedS_expansion
    {B : Coord → ℝ} {R a b : ℝ} {p : Coord}
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C r : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon : ℝ) (ell : ℕ)
    (hedge : p 1 < edge)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r p) :
    multiplierS A C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p =
      directedWeight edge lambda (coordinatePrimitive B) p *
        (directedPrincipal A ell epsilon p - weightH0 edge lambda p * A p / 2 +
          A p * directedSResidual B r ell epsilon p) := by
  have hI : DifferentiableAt ℝ (coordinatePrimitive B) p :=
    ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [directedS_transverse_expansion A B C edge lambda epsilon ell (r p) hA hI
    (sub_pos.mpr hedge).ne' hC, coordinatePrimitive_partial_t hB hR hp]
  rfl

theorem primitive_directed_near_coercivity
    {B : Coord → ℝ} {R a b : ℝ} {p : Coord}
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C r : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon : ℝ) (ell : ℕ)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r p)
    (MI MB Mr MA MAs mu : ℝ) (hmu : 0 < mu)
    (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hBp : |B p| ≤ MB) (hr : |r p| ≤ Mr)
    (hAp : |A p| ≤ MA) (hAs : |coordPartial 1 A p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * R * MB) ≤ lambda)
    (hEbudget : (MI + 1 + R * MB) / 2 + Mr ≤ lambda / 8)
    (hsmall : 4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2 * MA ≤ 1 / 8)
    (hloss : (4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2) / lambda ≤ mu / 4)
    (hprincipal : mu ≤ directedPrincipal A ell epsilon p)
    (hstrip : 0 < A p → weightH0 edge lambda p * A p ≤ mu / 3)
    (x y : ℝ) :
    min (lambda / 8) (mu / 2) * directedWeight edge lambda (coordinatePrimitive B) p *
      (x ^ 2 + y ^ 2) ≤
      multiplierT B (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * x ^ 2 +
        multiplierS A C (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * y ^ 2 +
        multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * x * y := by
  let W := directedWeight edge lambda (coordinatePrimitive B) p
  let H := weightH0 edge lambda p
  let Cj := R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)
  let L := 4 * Cj ^ 2 * epsilon ^ 2
  let E := (MI + 1 + R * MB) / 2 + Mr
  have hMI : 0 ≤ MI := (abs_nonneg _).trans hIs
  have hMB : 0 ≤ MB := (abs_nonneg _).trans hBp
  have hMr : 0 ≤ Mr := (abs_nonneg _).trans hr
  have hMA : 0 ≤ MA := (abs_nonneg _).trans hAp
  have hMAs : 0 ≤ MAs := (abs_nonneg _).trans hAs
  have hCj : 0 ≤ Cj := by dsimp [Cj] <;> positivity
  have hL : 0 ≤ L := by dsimp [L] <;> positivity
  have hW : 0 < W := directedWeight_pos _ _ _ _ hedge
  have hlH : lambda ≤ H := by
    dsimp [H, weightH0]
    exact le_add_of_nonneg_right (div_nonneg (by norm_num) (sub_pos.mpr hedge).le)
  have hH : 0 < H := hlambda.trans_le hlH
  have hCA : |C p - coordPartial 1 A p| ≤ (ell : ℝ) * MAs + MA * Mr := by
    have he : C p - coordPartial 1 A p =
        (ell : ℝ) * coordPartial 1 A p + A p * r p := by rw [hC]; ring
    rw [he]
    calc
      _ ≤ |(ell : ℝ) * coordPartial 1 A p| + |A p * r p| := abs_add_le _ _
      _ = (ell : ℝ) * |coordPartial 1 A p| + |A p| * |r p| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg ell)]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hAs (Nat.cast_nonneg ell))
        (mul_le_mul hAp hr (abs_nonneg _) hMA)
  have hT := primitive_directedT_lower_bound hB hR hp edge lambda epsilon MI MB
    heps hedge hIs hBp hTbudget
  have hJ0 := primitive_directedJ_bound hB hR hp A C hA edge lambda epsilon
    ((ell : ℝ) * MAs + MA * Mr) MA MI heps hedge hH.le hCA hAp hIs
  have hJ : |multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p| ≤
      W * Cj * epsilon * (1 + H * |A p|) := by
    refine hJ0.trans ?_
    have hD : 0 ≤ (ell : ℝ) * MAs + MA * Mr + MA * MI := by positivity
    have hh : 0 ≤ H * |A p| := mul_nonneg hH.le (abs_nonneg _)
    have hbase : (ell : ℝ) * MAs + MA * Mr + MA * MI + H * |A p| ≤
        ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1) * (1 + H * |A p|) := by
      nlinarith [mul_nonneg hD hh]
    have hm := mul_le_mul_of_nonneg_left hbase (mul_nonneg (mul_nonneg hW.le heps) hR.le)
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [W, H, Cj]
    ring
  have hcross := actual_normalized_cross_loss hW hH hCj heps hT hJ
  have he : |directedSResidual B r ell epsilon p| ≤ E :=
    directedSResidual_bound heps heps1 hR.le (abs_lt.mpr hp.1).le hIs hBp hr
  have hEH : E ≤ H / 8 := hEbudget.trans (by linarith)
  have hLH : L / H ≤ mu / 4 := by
    apply (div_le_iff₀ hH).2
    have hh : L ≤ (mu / 4) * lambda := (div_le_iff₀ hlambda).1 hloss
    exact hh.trans (mul_le_mul_of_nonneg_left hlH (by positivity))
  have hmargin : mu / 2 ≤ directedPrincipal A ell epsilon p - H * A p / 2 +
      A p * directedSResidual B r ell epsilon p - L * (H⁻¹ + H * (A p) ^ 2) := by
    by_cases hn : A p ≤ 0
    · have hh := normalized_negative_near_coercivity hH hL hmu hn hAp hsmall hLH he hEH hprincipal
      have hbonus : 0 ≤ H * |A p| / 4 := by positivity
      linarith
    · exact normalized_positive_strip_coercivity hH hL hmu (lt_of_not_ge hn).le hAp
        hsmall hLH he hEH hprincipal (hstrip (lt_of_not_ge hn))
  exact actual_quadratic_coercivity hW hH hlambda hmu hlH hT
    (primitive_directedS_expansion hB hR hp A C r hA edge lambda epsilon ell hedge hC)
    hcross hmargin

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualHighEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem chainTerm_eq_coordinateChainTerm
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (w : ChainWord) :
    chainTerm (sixVariableP g) (solutionJetCurve z x) w y =
      coordinateChainTerm g z w ![x, y] := by
  apply congrArg (iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z ![x, y]))
  funext i
  exact verticalJet_slice hU (solutionJet_contDiffOn hU hz) x (w.order i) y hp

theorem chainSum_eq_coordinateChainSum
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (ws : List ChainWord) :
    chainSum (sixVariableP g) (solutionJetCurve z x) ws y =
      coordinateChainSum g z ws ![x, y] := by
  unfold chainSum coordinateChainSum
  congr 1
  apply List.map_congr_left
  intro word _
  exact chainTerm_eq_coordinateChainTerm hU hz hp word

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ScalarChainExpansion
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem solutionJetCurve_iteratedDeriv_positive
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (solutionJetCurve z x) y =
      ![0, if n = 1 then 1 else 0,
        coordPartial 0 (verticalJet z n) ![x, y],
        coordPartial 1 (verticalJet z n) ![x, y],
        coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y],
        coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y]] := by
  have hc := solutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · change iteratedDeriv n (fun _ : ℝ => x) y = 0
    simp [iteratedDeriv_const, Nat.ne_of_gt hn]
  · change iteratedDeriv n id y = if n = 1 then 1 else 0
    simp [iteratedDeriv_id, Nat.ne_of_gt hn]
  · change iteratedDeriv n (fun t => coordPartial 0 z ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn hz hU 0) x n y hp,
      verticalJet_coordPartial hU hz 0 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn hz hU 1) x n y hp,
      verticalJet_coordPartial hU hz 1 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 0 1]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 1 1]
    rfl

theorem coordinate_solutionJet_vertical_positive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (n : ℕ) (hn : 0 < n) :
    verticalJet (solutionJet z) n p =
      ![0, if n = 1 then 1 else 0,
        coordPartial 0 (verticalJet z n) p,
        coordPartial 1 (verticalJet z n) p,
        coordPartial 0 (coordPartial 1 (verticalJet z n)) p,
        coordPartial 1 (coordPartial 1 (verticalJet z n)) p] := by
  have he : (![p 0, p 1] : Coord) = p := by
    ext i
    fin_cases i <;> rfl
  have h := solutionJetCurve_iteratedDeriv_positive hU hz
    (x := p 0) (y := p 1) (by simpa only [he] using hp) n hn
  have hv := verticalJet_slice hU (solutionJet_contDiffOn hU hz) (p 0) n (p 1)
    (by simpa only [he] using hp)
  change iteratedDeriv n (solutionJetCurve z (p 0)) (p 1) = _ at hv
  rw [hv] at h
  simpa only [he] using h

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MixedCoordinateCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem orderedPartial_perm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {ds es : List (Fin 2)} (hperm : ds.Perm es) :
    ∀ p ∈ U, iteratedCoordPartial ds f p = iteratedCoordPartial es f p := by
  induction hperm with
  | nil => intro p _; rfl
  | cons i _perm ih =>
      rename_i l1 l2
      intro p hp
      have he : iteratedCoordPartial l1 f =ᶠ[𝓝 p] iteratedCoordPartial l2 f := by
        filter_upwards [hU.mem_nhds hp] with q hq
        exact ih q hq
      exact coordPartial_eq_of_eventuallyEq he i
  | swap i j ds =>
      intro p hp
      exact normed_coordPartial_comm (orderedPartial_contDiffOn hf hU ds) hU hp j i
  | trans _ _ ih₁ ih₂ =>
      intro p hp
      exact (ih₁ p hp).trans (ih₂ p hp)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapInteriorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.Flow

theorem capInterior_gradient_le_directed_energy
    {L R bottom top b lambda MI : ℝ} {I u : Coord → ℝ}
    (hL : -2 < L) (hR : R < 2) (hbottom : -2 < bottom)
    (hLR : L ≤ R) (hbt : bottom ≤ top) (htop : top < b) (hb : b ≤ 0)
    (hlambda : 0 ≤ lambda) (hI : ContDiffOn ℝ ∞ I capChartDomain)
    (hu : ContDiffOn ℝ ∞ u capChartDomain)
    (hIv : ∀ p ∈ closedRectangle L R bottom top, |I p| ≤ MI) :
    rectangleIntegral L R bottom top (fun p => (coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
      (1/capInteriorWeightFloor top b lambda MI)*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
          (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) := by
  let F := fun p => (coordPartial 0 u p)^2+(coordPartial 1 u p)^2
  let E := directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda
  let S := closedRectangle L R bottom top
  let T := closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
  have hwpos := capInteriorWeightFloor_pos (lambda := lambda) (MI := MI) htop
  obtain ⟨htlo,htwidth,htone,hrone,hrwidth,htrhi,hsblo,hswidth,hsone,hlt,hrt⟩ :=
    capOuterRectangle_edges hL hR hbottom
  have ht : capOuterLeft L ≤ capOuterRight R := by linarith
  have hs : capOuterBottom bottom ≤ b := by linarith
  have hT : T ⊆ capChartDomain := capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hST : S ⊆ T := by
    intro p hp
    exact ⟨⟨hlt.le.trans hp.1.1,hp.1.2.trans hrt.le⟩,
      ⟨(by linarith [hp.2.1]),hp.2.2.trans htop.le⟩⟩
  have hgrad := ((partial_contDiffOn hu capChartDomain_isOpen 0).pow 2).add
    ((partial_contDiffOn hu capChartDomain_isOpen 1).pow 2)
  have hFc : ContinuousOn F T := hgrad.continuousOn.mono hT
  have hEc : ContinuousOn E T :=
    ((((capSpatialCutoff_contDiff L R bottom).contDiffOn.mul
      (directedWeight_contDiffOn b lambda hI)).mul hgrad).continuousOn.mono hT)
  have hEn (p : Coord) (hp : p ∈ T) : 0 ≤ E p := by
    have hchi := (capSpatialCutoff_range L R bottom p).1
    have hd : 0 ≤ edgeDistance b p := sub_nonneg.mpr hp.2.2
    unfold E directedGradientEnergy directedWeight
    positivity
  have hpoint (p : Coord) (hp : p ∈ S) : F p ≤ (1/capInteriorWeightFloor top b lambda MI)*E p := by
    have hW := directedWeight_interior_lower htop hlambda hp.2.2 (hIv p hp)
    have hchi := capSpatialCutoff_one hL hR hbottom p ⟨hp.1.1,hp.1.2,hp.2.1⟩
    have hgrad0 : 0 ≤ F p := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_right hW hgrad0
    have hscaled : capInteriorWeightFloor top b lambda MI*F p ≤ E p := by
      simpa only [E,directedGradientEnergy,hchi,one_mul] using hh
    have hdiv : F p ≤ E p/capInteriorWeightFloor top b lambda MI :=
      (le_div_iff₀ hwpos).mpr (by simpa only [mul_comm] using hscaled)
    convert hdiv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hcomp := restricted_gradient_from_energy ht hs (closedRectangle_measurable _ _ _ _)
    hST hFc hEc hEn (show 0 ≤ 1/capInteriorWeightFloor top b lambda MI by positivity) hpoint
  rw [coordinateSubsetIntegral_closedRectangle L R bottom top F hLR hbt (hFc.mono hST)] at hcomp
  exact hcomp

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_PatchAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

def PatchAdmissibleHeight (g : MetricField) (z : Coord → ℝ) : Prop :=
  ∃ U : Set Coord, IsOpen U ∧ modelSquare ⊆ U ∧ SmoothPositiveOn g U ∧
    ContDiffOn ℝ ∞ z U ∧
    (∀ p ∈ modelSquare,
      (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) ∧
    (∀ p ∈ modelSquare, 0 < heightEnergy g z p) ∧
    (∀ p ∈ modelSquare, covHessian g z p 1 1 ≠ 0) ∧
    (∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedFarNegative
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem primitive_directed_farnegative_coercivity
    {B : Coord → ℝ} {R a b : ℝ} {p : Coord}
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b)) (hR : 0 < R)
    (hp : p ∈ coordinateRectangle R a b) (A C r : Coord → ℝ)
    (hA : DifferentiableAt ℝ A p) (edge lambda epsilon : ℝ) (ell : ℕ)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hC : C p = ((ell : ℝ) + 1) * coordPartial 1 A p + A p * r p)
    (MI MB Mr MA MAs MAt mu alpha : ℝ) (hmu : 0 < mu)
    (hIs : |coordPartial 1 (coordinatePrimitive B) p| ≤ MI)
    (hBp : |B p| ≤ MB) (hr : |r p| ≤ Mr)
    (hAp : |A p| ≤ MA) (hAs : |coordPartial 1 A p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * R * MB) ≤ lambda)
    (hEbudget : (MI + 1 + R * MB) / 2 + Mr ≤ lambda / 8)
    (hsmall : 4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2 * MA ≤ 1 / 8)
    (hloss : (4 * (R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)) ^ 2 *
      epsilon ^ 2) / lambda ≤ mu / 4)
    (hAt : |coordPartial 0 A p| ≤ MAt)
    (halpha : 0 < alpha) (hAfar : A p ≤ -alpha)
    (hdominance : directedPrincipalBound ell epsilon R MAs MAt + mu ≤ lambda * alpha / 4)
    (x y : ℝ) :
    min (lambda / 8) (mu / 2) * directedWeight edge lambda (coordinatePrimitive B) p *
      (x ^ 2 + y ^ 2) ≤
      multiplierT B (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * x ^ 2 +
        multiplierS A C (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * y ^ 2 +
        multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
          (directedN edge lambda epsilon (coordinatePrimitive B)) p * x * y := by
  let W := directedWeight edge lambda (coordinatePrimitive B) p
  let H := weightH0 edge lambda p
  let Cj := R * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)
  let L := 4 * Cj ^ 2 * epsilon ^ 2
  let E := (MI + 1 + R * MB) / 2 + Mr
  have hMI : 0 ≤ MI := (abs_nonneg _).trans hIs
  have hMB : 0 ≤ MB := (abs_nonneg _).trans hBp
  have hMr : 0 ≤ Mr := (abs_nonneg _).trans hr
  have hMA : 0 ≤ MA := (abs_nonneg _).trans hAp
  have hMAs : 0 ≤ MAs := (abs_nonneg _).trans hAs
  have hCj : 0 ≤ Cj := by dsimp [Cj] <;> positivity
  have hL : 0 ≤ L := by dsimp [L] <;> positivity
  have hW : 0 < W := directedWeight_pos _ _ _ _ hedge
  have hlH : lambda ≤ H := by
    dsimp [H, weightH0]
    exact le_add_of_nonneg_right (div_nonneg (by norm_num) (sub_pos.mpr hedge).le)
  have hH : 0 < H := hlambda.trans_le hlH
  have hCA : |C p - coordPartial 1 A p| ≤ (ell : ℝ) * MAs + MA * Mr := by
    have he : C p - coordPartial 1 A p =
        (ell : ℝ) * coordPartial 1 A p + A p * r p := by rw [hC]; ring
    rw [he]
    calc
      _ ≤ |(ell : ℝ) * coordPartial 1 A p| + |A p * r p| := abs_add_le _ _
      _ = (ell : ℝ) * |coordPartial 1 A p| + |A p| * |r p| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg ell)]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hAs (Nat.cast_nonneg ell))
        (mul_le_mul hAp hr (abs_nonneg _) hMA)
  have hT := primitive_directedT_lower_bound hB hR hp edge lambda epsilon MI MB
    heps hedge hIs hBp hTbudget
  have hJ0 := primitive_directedJ_bound hB hR hp A C hA edge lambda epsilon
    ((ell : ℝ) * MAs + MA * Mr) MA MI heps hedge hH.le hCA hAp hIs
  have hJ : |multiplierJ A B C (directedM edge lambda (coordinatePrimitive B))
      (directedN edge lambda epsilon (coordinatePrimitive B)) p| ≤
      W * Cj * epsilon * (1 + H * |A p|) := by
    refine hJ0.trans ?_
    have hD : 0 ≤ (ell : ℝ) * MAs + MA * Mr + MA * MI := by positivity
    have hh : 0 ≤ H * |A p| := mul_nonneg hH.le (abs_nonneg _)
    have hbase : (ell : ℝ) * MAs + MA * Mr + MA * MI + H * |A p| ≤
        ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1) * (1 + H * |A p|) := by
      nlinarith [mul_nonneg hD hh]
    have hm := mul_le_mul_of_nonneg_left hbase (mul_nonneg (mul_nonneg hW.le heps) hR.le)
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [W, H, Cj]
    ring
  have hcross := actual_normalized_cross_loss hW hH hCj heps hT hJ
  have he : |directedSResidual B r ell epsilon p| ≤ E :=
    directedSResidual_bound heps heps1 hR.le (abs_lt.mpr hp.1).le hIs hBp hr
  have hEH : E ≤ H / 8 := hEbudget.trans (by linarith)
  have hLH : L / H ≤ mu / 4 := by
    apply (div_le_iff₀ hH).2
    have hh : L ≤ (mu / 4) * lambda := (div_le_iff₀ hlambda).1 hloss
    exact hh.trans (mul_le_mul_of_nonneg_left hlH (by positivity))
  have hmargin : mu / 2 ≤ directedPrincipal A ell epsilon p - H * A p / 2 +
      A p * directedSResidual B r ell epsilon p - L * (H⁻¹ + H * (A p) ^ 2) := by
    have hn : A p ≤ 0 := hAfar.trans (by linarith)
    have hAa : alpha ≤ |A p| := by rw [abs_of_nonpos hn]; linarith
    have hprincipal : -directedPrincipalBound ell epsilon R MAs MAt ≤
        directedPrincipal A ell epsilon p :=
      (abs_le.mp (directedPrincipal_abs_bound ell heps (abs_lt.mpr hp.1).le hAs hAt)).1
    have hbudget : directedPrincipalBound ell epsilon R MAs MAt + mu ≤ H * alpha / 4 :=
      hdominance.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlH halpha.le) (by norm_num))
    exact normalized_negative_far_coercivity hH hL hmu hn hAp hsmall hLH he hEH
      hprincipal hAa hbudget
  exact actual_quadratic_coercivity hW hH hlambda hmu hlH hT
    (primitive_directedS_expansion hB hR hp A C r hA edge lambda epsilon ell hedge hC)
    hcross hmargin

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_PatchFlowCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

variable {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord}
variable {Y : ℝ → ℝ → ℝ} {p : Coord} {kappa : ℝ}

theorem patch_capCurvature_eventually_model
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hk : 0 < kappa) (hU : IsOpen U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (himage : capChart Y p ∈ U)
    (hsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤ kappa / 8) :
    capPullback Y (gaussianCurvature (g0 + eta)) =ᶠ[𝓝 p] capModelCurvature kappa Y := by
  have heq := patch_smallCurvature_eventually_model hk hU hbackground hsupport hcentral himage hsmall
  have hc : ContinuousAt (capChart Y) p :=
    (capChart_contDiffOn hY).continuousOn.continuousAt (capChartDomain_isOpen.mem_nhds hp)
  exact heq.comp_tendsto hc.tendsto

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_WeightPrimitiveParameter
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Flow

variable {B : Coord → ℝ} {R a b : ℝ}

theorem coefficient_pairPartialY
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    {x y : ℝ} (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    pairPartialY (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (x, y) =
      coordPartial 1 B (coordinatePoint x y) := by
  have hdB : DifferentiableAt ℝ B (coordinatePoint x y) :=
    ((hB.contDiffAt ((coordinateRectangle_isOpen R a b).mem_nhds
      (point_mem_rectangle hx hy))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hdPair : DifferentiableAt ℝ (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (x, y) :=
    (((coefficient_pair_contDiffOn hB).contDiffAt
      ((pairRectangle_isOpen R a b).mem_nhds ⟨hx, hy⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hcoord : HasDerivAt (fun t => B (coordinatePoint x t))
      (coordPartial 1 B (coordinatePoint x y)) y :=
    hdB.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y x y)
  have hpair : HasDerivAt (fun t => B (coordinatePoint x t))
      (pairPartialY (fun p : ℝ × ℝ => B (coordinatePoint p.1 p.2)) (x, y)) y :=
    hdPair.hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  exact hpair.unique hcoord

theorem coordinatePrimitive_partial_s
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b) :
    coordPartial 1 (coordinatePrimitive B) p =
      ∫ t in 0..p 0, coordPartial 1 B (coordinatePoint t (p 1)) := by
  have hpairC1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => B (coordinatePoint q.1 q.2))
      (pairRectangle R a b) := (coefficient_pair_contDiffOn hB).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hftc := pairPrimitive_hasDerivAt_y hpairC1 hp.1 hp.2
  have hseg : uIcc 0 (p 0) ⊆ Ioo (-R) R := by
    have hz : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hz.1 hp.1.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hz.2 hp.1.2)⟩
  have he : pairPrimitive
      (pairPartialY (fun q : ℝ × ℝ => B (coordinatePoint q.1 q.2))) (p 0, p 1) =
      ∫ t in 0..p 0, coordPartial 1 B (coordinatePoint t (p 1)) := by
    unfold pairPrimitive
    apply intervalIntegral.integral_congr
    intro t ht
    exact coefficient_pairPartialY hB (hseg ht) hp.2
  rw [he] at hftc
  have hftc' : HasDerivAt (fun s => coordinatePrimitive B (coordinatePoint (p 0) s))
      (∫ t in 0..p 0, coordPartial 1 B (coordinatePoint t (p 1))) (p 1) := by
    simpa [pairPrimitive, coordinatePrimitive, coordinatePoint] using hftc
  have hdI : DifferentiableAt ℝ (coordinatePrimitive B) (coordinatePoint (p 0) (p 1)) := by
    rw [point_eta]
    exact ((coordinatePrimitive_contDiffOn hB).contDiffAt
      ((coordinateRectangle_isOpen R a b).mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hchain := hdI.hasFDerivAt.comp_hasDerivAt (p 1) (coordinatePoint_hasDerivAt_y (p 0) (p 1))
  have hcoord : HasDerivAt (fun s => coordinatePrimitive B (coordinatePoint (p 0) s))
      (coordPartial 1 (coordinatePrimitive B) p) (p 1) := by
    simpa only [point_eta, Function.comp_def, coordPartial] using hchain
  exact hcoord.unique hftc'

theorem coordinatePrimitive_partial_s_bound
    (hB : ContDiffOn ℝ ∞ B (coordinateRectangle R a b))
    (hR : 0 < R) {p : Coord} (hp : p ∈ coordinateRectangle R a b)
    {M : ℝ} (hBs : ∀ q ∈ coordinateRectangle R a b, |coordPartial 1 B q| ≤ M) :
    |coordPartial 1 (coordinatePrimitive B) p| ≤ R * M := by
  rw [coordinatePrimitive_partial_s hB hR hp]
  exact coordinatePrimitive_abs_bound
    (partial_contDiffOn hB (coordinateRectangle_isOpen R a b) 1).continuousOn hR hp hBs

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_CoordinateSwap
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem coordinateSwap_contDiff : ContDiff ℝ ∞ coordinateSwap :=
  affineCoordinates_contDiff 0 coordinateSwapMatrix

theorem coordinateSwap_preimage_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (coordinateSwap ⁻¹' U) :=
  hU.preimage coordinateSwap_contDiff.continuous

theorem christoffel_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (k i j : Fin 2) :
    christoffel (swappedMetric g) k i j p =
      christoffel g (swapCoordinateIndex k) (swapCoordinateIndex i)
        (swapCoordinateIndex j) (coordinateSwap p) := by
  have h := christoffel_affinePullback_push hg hU 0 coordinateSwapMatrix
    coordinateSwapMatrix_isUnit p hp (swapCoordinateIndex k) i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simpa [coordinateSwapMatrix, swapCoordinateIndex, Fin.sum_univ_two,
      swappedMetric, coordinateSwap] using h

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_MetricCurvatureJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem inverseMetric_coordPartial_eq_jet {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d i j : Fin 2) :
    coordPartial d (fun q => inverseMetric g q i j) p =
      inverseDerivativeJet (g p) (fun e a b => coordPartial e (fun q => g q a b) p)
        d i j := by
  let D : MetricMatrix := fun a b => coordPartial d (fun q => g q a b) p
  let I' : MetricMatrix := fun a b => coordPartial d (fun q => inverseMetric g q a b) p
  have hprod : D * (g p)⁻¹ + g p * I' = 0 := by
    ext a b
    change (∑ l, D a l * (g p)⁻¹ l b) + (∑ l, g p a l * I' l b) = 0
    simpa only [← Finset.sum_add_distrib, D, I', inverseMetric] using
      metric_inverse_derivative_identity hg hU hp d a b
  have hinv : (g p)⁻¹ * g p = 1 :=
    Matrix.nonsing_inv_mul (g p)
      ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit)
  have hz : ((g p)⁻¹ * D) * (g p)⁻¹ + I' = 0 := by
    calc
      _ = (g p)⁻¹ * (D * (g p)⁻¹ + g p * I') := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, hinv, one_mul]
      _ = 0 := by rw [hprod, mul_zero]
  have hentry : (((g p)⁻¹ * D) * (g p)⁻¹) i j =
      ∑ a, ∑ b, (g p)⁻¹ i a * D a b * (g p)⁻¹ b j := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have heq := congrFun (congrFun hz i) j
  simp only [Matrix.add_apply, Matrix.zero_apply, hentry] at heq
  change I' i j = -(∑ a, ∑ b, (g p)⁻¹ i a * D a b * (g p)⁻¹ b j)
  linarith only [heq]

theorem gaussianCurvature_eq_curvatureJet {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature g p = curvatureJet (g p)
      (fun d i j => coordPartial d (fun q => g q i j) p)
      (fun d e i j => coordPartial d (coordPartial e (fun q => g q i j)) p) := by
  have hΓ (k i j : Fin 2) : christoffel g k i j p =
      christoffelJet (g p) (fun d i j => coordPartial d (fun q => g q i j) p) k i j := rfl
  have hDΓ (d k i j : Fin 2) : coordPartial d (christoffel g k i j) p =
      christoffelDerivativeJet (g p)
        (fun d i j => coordPartial d (fun q => g q i j) p)
        (fun d e i j => coordPartial d (coordPartial e (fun q => g q i j)) p) d k i j := by
    rw [christoffel_coordPartial_formula hg hU hp]
    have hi := inverseMetric_coordPartial_eq_jet hg hU hp
    simp only [inverseMetric] at hi
    simp only [christoffelDerivativeJet, inverseMetric, hi]
  simp only [gaussianCurvature, curvatureJet, riemann, riemannJet, hΓ, hDΓ]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualRemainderFactors
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

theorem heightStateFactor_contDiffOn (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (n : ℕ) (j : Fin 4) : ContDiffOn ℝ ∞ (heightStateFactor z n j) U := by
  have hv := verticalJet_contDiffOn hU hz n
  fin_cases j
  · exact partial_contDiffOn hv hU 0
  · exact partial_contDiffOn hv hU 1
  · exact partial_contDiffOn (partial_contDiffOn hv hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hv hU 1) hU 1

theorem coordinateChainFactor_continuousOn (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) :
    ContinuousOn (coordinateChainFactor z w r i) U := by
  exact ((ContinuousLinearMap.proj (r i) : DarbouxState →L[ℝ] ℝ).continuous.comp_continuousOn
    (verticalJet_contDiffOn hU (solutionJet_contDiffOn hU hz) (w.order i)).continuousOn)

theorem vertical_state_height_ae (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (n : ℕ) (hn : 0 < n) (j : Fin 4) :
    (fun p => verticalJet (solutionJet z) n p (heightComponentIndex j)) =ᵐ[volume.restrict V]
      heightStateFactor z n j := by
  filter_upwards [ae_restrict_mem hV] with p hp
  rw [coordinate_solutionJet_vertical_positive hU hz (hVU hp) n hn]
  fin_cases j <;> rfl

theorem vertical_state_component_low_bound
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hVU : V ⊆ U)
    {m : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (n : ℕ) (hn : 0 < n) (k : Fin 6) (hk : n + stateBaseOrder k ≤ m + 1)
    {p : Coord} (hp : p ∈ V) :
    ‖verticalJet (solutionJet z) n p k‖ ≤ B := by
  rw [coordinate_solutionJet_vertical_positive hU hz (hVU hp) n hn]
  fin_cases k
  · simpa using le_trans (by norm_num : (0 : ℝ) ≤ 1) hB
  · by_cases he : n = 1
    · simpa [he] using hB
    · simpa [he] using le_trans (by norm_num : (0 : ℝ) ≤ 1) hB
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 0 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 1 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 2 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 3 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp

theorem vertical_state_component_high_eLpNorm
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} {H : ℝ≥0}
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (n : ℕ) (hn : 0 < n) (hnlow : n ≤ m + 1) (k : Fin 6)
    (hhigh : m + 2 ≤ n + stateBaseOrder k) (htop : n + stateBaseOrder k ≤ m + 3) :
    eLpNorm (fun p => verticalJet (solutionJet z) n p k) 2 (volume.restrict V) ≤
      (H : ℝ≥0∞) := by
  fin_cases k
  · norm_num [stateBaseOrder] at hhigh
    omega
  · norm_num [stateBaseOrder] at hhigh
    omega
  · calc
      _ = eLpNorm (heightStateFactor z n 0) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 0)
      _ ≤ _ := hheight n 0 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)
  · calc
      _ = eLpNorm (heightStateFactor z n 1) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 1)
      _ ≤ _ := hheight n 1 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)
  · calc
      _ = eLpNorm (heightStateFactor z n 2) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 2)
      _ ≤ _ := hheight n 2 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)
  · calc
      _ = eLpNorm (heightStateFactor z n 3) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 3)
      _ ≤ _ := hheight n 3 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_ActualRemainderL2
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

theorem residual_product_eLpNorm_two
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {B : ℝ} (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    {w : ChainWord} (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    eLpNorm (fun p => ∏ i, coordinateChainFactor z w r i p) 2 (volume.restrict V) ≤
      chainProductL2Budget B H V (m + 3) := by
  classical
  obtain ⟨hpos, -, horders⟩ := topResidualWords_properties m w hw
  obtain ⟨hfactorOrders, harity⟩ := residual_scalar_factor_orders hw r
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hmeas : AEStronglyMeasurable (fun p => ∏ i, coordinateChainFactor z w r i p)
      (volume.restrict V) :=
    Finset.univ.aestronglyMeasurable_fun_prod (fun index _ =>
      ((coordinateChainFactor_continuousOn hU hz w r index).mono hVU).aestronglyMeasurable
        (μ := volume) hV)
  by_cases hhigh : ∃ j, m + 2 ≤ chainFactorOrder w r j
  · obtain ⟨j, hj⟩ := hhigh
    have hlowOther : ∀ i ∈ (Finset.univ : Finset (Fin w.arity)).erase j,
        ∀ p ∈ V, ‖coordinateChainFactor z w r i p‖ ≤ B := by
      intro i hi p hp
      have hiorder : chainFactorOrder w r i ≤ m + 1 := by
        by_contra hiorder
        have hieq := residual_scalar_high_unique (i := i) (j := j) hm hw r (by omega) hj
        exact (Finset.mem_erase.mp hi).1 hieq
      exact vertical_state_component_low_bound hU hz hVU hB hlow
        (w.order i) (hpos i) (r i) hiorder hp
    have hjL2 : eLpNorm (coordinateChainFactor z w r j) 2 (volume.restrict V) ≤
        (H : ℝ≥0∞) :=
      vertical_state_component_high_eLpNorm hU hz hV hVU hheight
        (w.order j) (hpos j) (horders j) (r j) hj (hfactorOrders j)
    have hcard : ((Finset.univ : Finset (Fin w.arity)).erase j).card ≤ m + 3 := by
      have he := Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin w.arity)))
      have he' : ((Finset.univ : Finset (Fin w.arity)).erase j).card ≤ w.arity := by
        simpa only [Finset.card_univ, Fintype.card_fin] using he
      exact he'.trans harity
    have hp := finite_product_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (coordinateChainFactor z w r) (Finset.mem_univ j) hB0 hV hlowOther hmeas
    calc
      _ ≤ ‖B ^ ((Finset.univ : Finset (Fin w.arity)).erase j).card‖ₑ *
          eLpNorm (coordinateChainFactor z w r j) 2 (volume.restrict V) := hp
      _ ≤ ‖B ^ (m + 3)‖ₑ * ((H : ℝ≥0∞) + (volume V) ^ (1 / (2 : ℝ))) :=
        mul_le_mul' (enorm_pow_mono_of_one_le hB hcard)
          (hjL2.trans (le_add_of_nonneg_right (by positivity)))
      _ = _ := rfl
  · have hlowAll : ∀ i ∈ (Finset.univ : Finset (Fin w.arity)),
        ∀ p ∈ V, ‖coordinateChainFactor z w r i p‖ ≤ B := by
      intro i _ p hp
      have hiorder : chainFactorOrder w r i ≤ m + 1 := by
        have hni : ¬ m + 2 ≤ chainFactorOrder w r i := fun hi => hhigh ⟨i, hi⟩
        omega
      exact vertical_state_component_low_bound hU hz hVU hB hlow
        (w.order i) (hpos i) (r i) hiorder hp
    have hp := finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable
      (μ := volume) Finset.univ (coordinateChainFactor z w r) hB0 hV hlowAll hmeas
    calc
      _ ≤ ‖B ^ w.arity‖ₑ * (volume V) ^ (1 / (2 : ℝ)) := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hp
      _ ≤ ‖B ^ (m + 3)‖ₑ * ((H : ℝ≥0∞) + (volume V) ^ (1 / (2 : ℝ))) :=
        mul_le_mul' (enorm_pow_mono_of_one_le hB harity)
          (le_add_of_nonneg_left (by positivity))
      _ = _ := rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_BoundedHeightClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.HighEquation

def BoundedAdmissibleHeight (g : MetricField) (M : ℕ) (z : Coord → ℝ) : Prop :=
  0 < M ∧ PatchAdmissibleHeight g z ∧
  (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ (M : ℝ)) ∧
  (∀ p ∈ modelSquare, 1 / (M : ℝ) ≤ |covHessian g z p 1 1| ∧
    |covHessian g z p 1 1| ≤ (M : ℝ)) ∧
  (∀ p ∈ modelSquare, 1 / (M : ℝ) ≤ heightEnergy g z p)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_BoundedClassReflection
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.Flow.Reflection

theorem PatchAdmissibleHeight.reflected {g : MetricField} {z : Coord → ℝ}
    (h : PatchAdmissibleHeight g z) :
    PatchAdmissibleHeight (reflectedMetric g) (reflectedScalar z) := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := h
  have hmem {p : Coord} (hp : p ∈ modelSquare) : reflectPoint p ∈ U :=
    hSU ((reflectPoint_mem_modelSquare p).mpr hp)
  refine ⟨reflectPoint ⁻¹' U, reflectedDomain_isOpen hU,
    reflectedDomain_contains_modelSquare hSU, reflectedMetric_smoothPositive hg,
    reflectedScalar_contDiffOn hz, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [reflectedMetric_hessian_det hg hz hU (hmem hp),
      reflectedMetric_curvature hg hU (hmem hp), reflectedMetric_energy hz hU (hmem hp)]
    exact hD _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_energy hz hU (hmem hp)]
    exact hE _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_hessian_entry hg hz hU (hmem hp)]
    simpa only [ite_true, if_true] using hyy _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_quotient hg hz hU (hmem hp),abs_neg]
    exact hq _ ((reflectPoint_mem_modelSquare p).mpr hp)

theorem BoundedAdmissibleHeight.reflected {g : MetricField} {z : Coord → ℝ} {M : ℕ}
    (h : BoundedAdmissibleHeight g M z) :
    BoundedAdmissibleHeight (reflectedMetric g) M (reflectedScalar z) := by
  obtain ⟨hM,ha,hB,hyy,hE⟩ := h
  have har := ha.reflected
  obtain ⟨U,hU,hSU,hg,hz,hD,hpos,hne,hq⟩ := ha
  refine ⟨hM,har,reflectedScalar_C8 hB,?_,?_⟩
  · intro p hp
    have hpr := (reflectPoint_mem_modelSquare p).mpr hp
    rw [reflectedMetric_hessian_entry hg hz hU (hSU hpr)]
    simpa only [ite_true, if_true] using hyy _ hpr
  · intro p hp
    have hpr := (reflectPoint_mem_modelSquare p).mpr hp
    rw [reflectedMetric_energy hz hU (hSU hpr)]
    exact hE _ hpr

theorem bounded_class_reflected_center {g : MetricField} {z : Coord → ℝ} {M : ℕ}
    (h : BoundedAdmissibleHeight g M z) (q0 : ℝ) :
    |hessianQuotient (reflectedMetric g) (reflectedScalar z) 0-(-q0)| =
      |hessianQuotient g z 0-q0| := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := h.2.1
  have hzero : (0 : Coord) ∈ modelSquare := by constructor <;> intro i <;> norm_num
  have hrzero : reflectPoint (0 : Coord) = 0 := by ext i; fin_cases i <;> simp
  have hzeroU : reflectPoint (0 : Coord) ∈ U := by
    simpa only [hrzero] using hSU hzero
  rw [reflectedMetric_quotient hg hz hU (p := 0) hzeroU,hrzero]
  have he : -hessianQuotient g z 0-(-q0) = -(hessianQuotient g z 0-q0) := by ring
  rw [he,abs_neg]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_MixedDarbouxElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem mixed_coordinate_height_factor_eq_word
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (ds : List (Fin 2)) (c : OrderedFinpartition ds.length) (j : Fin c.length)
    (i : Fin 4) :
    (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i) =
      iteratedCoordPartial (mixedBlockWord ds c j ++ heightStateSuffix i) z p := by
  rw [mixedFaaFactor_height_slot hU hz hp]
  have hdir : (coordinateDirections ds ∘ c.emb j) =
      fun a => Pi.single (ds.get (c.emb j a)) (1 : ℝ) := by
    funext a
    exact coordinateDirections_apply ds (c.emb j a)
  rw [hdir, fullJet_coordinate_inputs_eq_ordered (heightStateFactor_contDiffOn hU hz 0 i) hU
    (c.partSize j) (fun a => ds.get (c.emb j a)) hp,
    heightStateFactor_zero_eq_suffix]
  exact (congrFun (orderedPartial_append (mixedBlockWord ds c j) (heightStateSuffix i) z) p).symm

theorem mixedFaaRemainder_coordinate_eq
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (ds : List (Fin 2)) (hds : 0 < ds.length) :
    mixedFaaRemainder g z hds (coordinateDirections ds) p =
      heightPFirst g z 0 p * iteratedCoordPartial (ds ++ [0]) z p +
      heightPFirst g z 1 p * iteratedCoordPartial (ds ++ [1]) z p +
      ∑ c ∈ (Finset.univ.erase (fullBlockPartition ds.length hds)),
        mixedFaaTerm g z (coordinateDirections ds) c p := by
  unfold mixedFaaRemainder
  rw [← iteratedCoordPartial_eq_jet (partial_contDiffOn hz hU 0) hU ds hp,
    ← iteratedCoordPartial_eq_jet (partial_contDiffOn hz hU 1) hU ds hp,
    orderedPartial_append ds [0], orderedPartial_append ds [1]]
  rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_MixedRemainderFactors
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem mixedBlock_low_norm_bound
    {z : Coord → ℝ} {U V : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hVU : V ⊆ U)
    (ds : List (Fin 2)) {B : ℝ} (hB : 1 ≤ B)
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (c : OrderedFinpartition ds.length) (j : Fin c.length) (a : Fin 6)
    (horder : c.partSize j + stateBaseOrder a ≤ ds.length - 1)
    {p : Coord} (hp : p ∈ V) :
    ‖(iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) a‖ ≤ B := by
  have hh (i : Fin 4) (hi : c.partSize j + heightStateBaseOrder i ≤ ds.length - 1) :
      |(iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
        (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i)| ≤ B := by
    rw [mixed_coordinate_height_factor_eq_word hU hz (hVU hp)]
    exact hlow _ (by simpa [mixedBlockWord, heightStateSuffix_length] using hi) p hp
  fin_cases a
  · simpa [Real.norm_eq_abs] using (mixedBlock_spatial_abs_le_one hU hz (hVU hp) ds c j 0).trans hB
  · simpa [Real.norm_eq_abs] using (mixedBlock_spatial_abs_le_one hU hz (hVU hp) ds c j 1).trans hB
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 0
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 1
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 2
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 3
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)

theorem mixedBlock_high_eLpNorm_bound
    {z : Coord → ℝ} {U V : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 0 < ds.length) {H : ℝ≥0}
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length hds)
    (j : Fin c.length) (a : Fin 6)
    (hhigh : ds.length ≤ c.partSize j + stateBaseOrder a) :
    eLpNorm (fun p => (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) a) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  have hn := ordered_nonfull_partSize_le hds c hc j
  have hh (i : Fin 4) : eLpNorm (fun p =>
      (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
        (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i)) 2 (volume.restrict V) ≤
      (H : ℝ≥0∞) := by
    have he : (fun p => (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
        (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i)) =ᵐ[volume.restrict V]
        iteratedCoordPartial (mixedBlockWord ds c j ++ heightStateSuffix i) z := by
      filter_upwards [ae_restrict_mem hV] with p hp
      exact mixed_coordinate_height_factor_eq_word hU hz (hVU hp) ds c j i
    rw [eLpNorm_congr_ae he]
    exact hheight _ (mixed_nonfull_height_word_length ds hds c hc j i)
  fin_cases a
  · norm_num [stateBaseOrder] at hhigh
    omega
  · norm_num [stateBaseOrder] at hhigh
    omega
  · simpa [heightComponentIndex] using hh 0
  · simpa [heightComponentIndex] using hh 1
  · simpa [heightComponentIndex] using hh 2
  · simpa [heightComponentIndex] using hh 3

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MixedRemainderL2
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem mixed_product_eLpNorm_two
    {z : Coord → ℝ} {U V : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 5 ≤ ds.length) {B : ℝ} (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length (by omega))
    (r : Fin c.length → Fin 6) :
    eLpNorm (fun p => ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p)
      2 (volume.restrict V) ≤ chainProductL2Budget B H V ds.length := by
  classical
  have hB0 : 0 ≤ B := by linarith
  have hprod : AEStronglyMeasurable
      (fun point => ∏ index, mixedFaaFactor z (coordinateDirections ds) c r index point)
      (volume.restrict V) :=
    ((continuousOn_finsetProd Finset.univ
      (fun index _ => mixedFaaFactor_continuousOn hU hz (coordinateDirections ds) c r index)).mono
        hVU).aestronglyMeasurable (μ := volume) hV
  by_cases hh : ∃ j, ds.length ≤ c.partSize j + stateBaseOrder (r j)
  · obtain ⟨j, hj⟩ := hh
    have hlo : ∀ i ∈ (Finset.univ : Finset (Fin c.length)).erase j,
        ∀ p ∈ V, ‖mixedFaaFactor z (coordinateDirections ds) c r i p‖ ≤ B := by
      intro i hi p hp
      have ho : c.partSize i + stateBaseOrder (r i) ≤ ds.length - 1 := by
        by_contra hn
        have he := mixed_high_factor_unique (i := i) (j := j) hds c r (by omega) hj
        exact (Finset.mem_erase.mp hi).1 he
      exact mixedBlock_low_norm_bound hU hz hVU ds hB hlow c i (r i) ho hp
    have hjL := mixedBlock_high_eLpNorm_bound hU hz hV hVU ds (by omega)
      hheight c hc j (r j) hj
    have hcard : ((Finset.univ : Finset (Fin c.length)).erase j).card ≤ ds.length := by
      have he : ((Finset.univ : Finset (Fin c.length)).erase j).card ≤ c.length := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin c.length)))
      exact he.trans c.length_le
    exact (finite_product_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (mixedFaaFactor z (coordinateDirections ds) c r) (Finset.mem_univ j) hB0 hV hlo hprod).trans
      (mul_le_mul' (enorm_pow_mono_of_one_le hB hcard)
        (hjL.trans (le_add_of_nonneg_right (by positivity))))
  · have hlo : ∀ i ∈ (Finset.univ : Finset (Fin c.length)),
        ∀ p ∈ V, ‖mixedFaaFactor z (coordinateDirections ds) c r i p‖ ≤ B := by
      intro i _ p hp
      have ho : c.partSize i + stateBaseOrder (r i) ≤ ds.length - 1 := by
        have hn : ¬ ds.length ≤ c.partSize i + stateBaseOrder (r i) := fun h => hh ⟨i, h⟩
        omega
      exact mixedBlock_low_norm_bound hU hz hVU ds hB hlow c i (r i) ho hp
    have hb := finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (mixedFaaFactor z (coordinateDirections ds) c r) hB0 hV hlo hprod
    have hb' : eLpNorm (fun p => ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p)
        2 (volume.restrict V) ≤ ‖B ^ c.length‖ₑ * (volume V) ^ (1 / (2 : ℝ)) := by
      simpa only [Finset.card_univ, Fintype.card_fin] using hb
    exact hb'.trans (mul_le_mul' (enorm_pow_mono_of_one_le hB c.length_le)
      (le_add_of_nonneg_left (by positivity)))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MixedDerivativeL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem orderedPartial_at_most_one_x_eLpNorm
    {z : Coord → ℝ} {U V : Set Coord} (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    {N : ℕ} {Htop : ℝ≥0}
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N - 1))) 2
      (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (ds : List (Fin 2)) (hlen : ds.length = N) (hx : ds.count 0 ≤ 1) :
    eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞) := by
  by_cases hzcount : ds.count 0 = 0
  · rw [word_no_x_eq_replicate ds hzcount, orderedPartial_replicate_y, hlen]
    exact hv
  · have hcount : ds.count 0 = 1 := by omega
    have hmem : (0 : Fin 2) ∈ ds := List.count_pos_iff.mp (by omega)
    have hperm := List.perm_cons_erase hmem
    have herase : (ds.erase 0).count 0 = 0 := by
      rw [List.count_erase_self, hcount]
    have heraseLen : (ds.erase 0).length = N - 1 := by
      have h := hperm.length_eq
      simp only [List.length_cons] at h
      omega
    have he : iteratedCoordPartial ds z =ᵐ[volume.restrict V]
        coordPartial 0 (verticalJet z (N - 1)) := by
      filter_upwards [ae_restrict_mem hV] with p hp
      have h := orderedPartial_perm hz hU hperm p (hVU hp)
      rw [word_no_x_eq_replicate (ds.erase 0) herase, heraseLen] at h
      simpa only [iteratedCoordPartial, orderedPartial_replicate_y] using h
    rw [eLpNorm_congr_ae he]
    exact hxv

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapL2Basics
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem CoordinateL2Bound.mono {z : Coord → ℝ} {V : Set Coord} {N n : ℕ} {H H' : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hn : n ≤ N) (hH : H ≤ H') :
    CoordinateL2Bound z V n H' := by
  intro ds hds
  exact (h ds (hds.trans hn)).trans (by exact_mod_cast hH)

theorem CoordinateL2Bound.restrict {z : Coord → ℝ} {V W : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hWV : W ⊆ V) : CoordinateL2Bound z W N H := by
  intro ds hds
  exact (eLpNorm'_mono_measure _ (Measure.restrict_mono_set volume hWV)
    (by norm_num)).trans (h ds hds)

theorem CoordinateL2Bound.heightFactors {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (n : ℕ) (j : Fin 4)
    (hn : n + heightStateBaseOrder j ≤ N) :
    eLpNorm' (heightStateFactor z n j) (2 : ℝ) (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  rw [heightStateFactor_eq_ordered]
  apply h
  simpa only [List.length_append, List.length_replicate, heightStateSuffix_length, Nat.add_comm] using hn

theorem CoordinateL2Bound.heightFactors_of_aestronglyMeasurable
    {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (hbound : CoordinateL2Bound z V N H) (order : ℕ) (component : Fin 4)
    (horder : order + heightStateBaseOrder component ≤ N)
    (hmeas : AEStronglyMeasurable (heightStateFactor z order component) (volume.restrict V)) :
    eLpNorm (heightStateFactor z order component) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  exact hbound.heightFactors order component horder

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_PatchAddressModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation SmoothLocal.Model

def patchAddressInitialMetric (a : PatchAddress) : MetricField :=
  affinePullbackMetric initialAssemblyMetric (patchAddressCenter a) (patchAddressMatrix a)

def patchAddressAmplitude (a : PatchAddress) : ℝ :=
  initialPatchAmplitude a.1 a.2.1 a.2.2.1 a.2.2.2.val a.2.2.2.property

theorem patchAddressAmplitude_pos (a : PatchAddress) : 0 < patchAddressAmplitude a :=
  initialPatchAmplitude_pos a.1 a.2.1 a.2.2.1 a.2.2.2.val a.2.2.2.property

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QMetricDensityDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qMetricDensityFactor (g : MetricField) (w : DarbouxState) : ℝ :=
  stateEnergy g w / ((g (statePoint w)).det*stateQDenominator g w)

def qMetricFirstLower (g : MetricField) (w : DarbouxState) : ℝ :=
  stateConnection g 1 1 w+(stateMixed g w)^2/stateQDenominator g w

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QPositiveFloor
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

theorem inverseMetric_value_bound {g : MetricField} {p : Coord} {G d : ℝ}
    (hG : 0 ≤ G) (hd : 0 < d) (hg0 : ∀ i j, |g p i j| ≤ G)
    (hdet : d ≤ |(g p).det|) (i j : Fin 2) : |inverseMetric g p i j| ≤ G / d := by
  have hadj : |(g p).adjugate i j| ≤ G := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hg0 1 1
    · simpa [Matrix.adjugate_fin_two] using hg0 0 1
    · simpa [Matrix.adjugate_fin_two] using hg0 1 0
    · simpa [Matrix.adjugate_fin_two] using hg0 0 0
  have he := congrFun (inverseMetric_eq_adjugate_div g i j) p
  rw [he, abs_div]
  exact (div_le_div_of_nonneg_right hadj (abs_nonneg _)).trans
    (div_le_div_of_nonneg_left hG hd hdet)

theorem christoffel_value_bound {g : MetricField} {p : Coord} {G d : ℝ}
    (hG : 0 ≤ G) (hd : 0 < d) (hg0 : ∀ i j, |g p i j| ≤ G)
    (hg1 : ∀ a i j, |coordPartial a (fun q => g q i j) p| ≤ G)
    (hdet : d ≤ |(g p).det|) (k i j : Fin 2) :
    |christoffel g k i j p| ≤ 3 * (G / d) * G := by
  have hB (l : Fin 2) : |coordPartial i (fun q => g q j l) p +
      coordPartial j (fun q => g q i l) p - coordPartial l (fun q => g q i j) p| ≤ 3 * G :=
    (abs_sub _ _).trans ((add_le_add
      ((abs_add_le _ _).trans (add_le_add (hg1 i j l) (hg1 j i l))) le_rfl).trans
      (by linarith [hg1 l i j]))
  have hprod (l : Fin 2) : |inverseMetric g p k l *
      (coordPartial i (fun q => g q j l) p + coordPartial j (fun q => g q i l) p -
        coordPartial l (fun q => g q i j) p)| ≤ (G / d) * (3 * G) := by
    rw [abs_mul]
    exact mul_le_mul (inverseMetric_value_bound hG hd hg0 hdet k l) (hB l)
      (abs_nonneg _) (div_nonneg hG hd.le)
  unfold christoffel
  rw [Fin.sum_univ_two, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (|inverseMetric g p k 0 *
        (coordPartial i (fun q => g q j 0) p + coordPartial j (fun q => g q i 0) p -
          coordPartial 0 (fun q => g q i j) p)| + |inverseMetric g p k 1 *
        (coordPartial i (fun q => g q j 1) p + coordPartial j (fun q => g q i 1) p -
          coordPartial 1 (fun q => g q i j) p)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ((G / d) * (3 * G) + (G / d) * (3 * G)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hprod 0) (hprod 1)) (by norm_num)
    _ = _ := by ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_UniversalMetricP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem sixVariableP_eq_universalMetricP {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    sixVariableP g w = universalMetricP (metricPBundle g w) := by
  have hK := gaussianCurvature_eq_curvatureJet hg hU hw
  unfold sixVariableP solvedDarboux jetNumerator jetMixed jetYY
  unfold universalMetricP
  rw [universalConnection_metricPBundle, universalConnection_metricPBundle,
    universalDenominator_metricPBundle, universalEnergy_metricPBundle]
  simp only [stateConnection, stateDenominator, stateEnergy, jetYY, metricPBundle, hK]

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricPBundleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem metricPBundle_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (metricPBundle g) (stateBaseDomain U) := by
  have h0 : ContDiffOn ℝ ∞ (fun w => g (statePoint w)) (stateBaseDomain U) := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (hg.1 i j).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have h1 : ContDiffOn ℝ ∞
      (fun w d i j => coordPartial d (fun p => g p i j) (statePoint w)) (stateBaseDomain U) := by
    apply contDiffOn_pi.mpr
    intro d
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (partial_contDiffOn (hg.1 i j) hU d).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have h2 : ContDiffOn ℝ ∞
      (fun w d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))
      (stateBaseDomain U) := by
    apply contDiffOn_pi.mpr
    intro d
    apply contDiffOn_pi.mpr
    intro e
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (partial_contDiffOn (partial_contDiffOn (hg.1 i j) hU e) hU d).comp
      statePoint_contDiff.contDiffOn (fun w hw => hw)
  exact h0.prodMk (h1.prodMk (h2.prodMk contDiffOn_id))

theorem metricPBundle_positive_jet_bound {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {N : ℕ} {G : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ N + 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n (metricPBundle g) w‖ ≤ max 1 G := by
  have hB := (metricPBundle_contDiffOn hg hU).contDiffAt
    ((stateBaseDomain_isOpen hU).mem_nhds hw)
  have h0 := hB.fst
  have h1 := hB.snd.fst
  have h2 := hB.snd.snd.fst
  have hId := hB.snd.snd.snd
  have hcon {f : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
      ‖iteratedFDeriv ℝ n (fun v => f (statePoint v)) w‖ ≤
        ‖iteratedFDeriv ℝ n f (statePoint w)‖ := by
    exact norm_iteratedFDeriv_comp_statePoint hf hU hw n
  have hb0 : ‖iteratedFDeriv ℝ n (fun v => g (statePoint v)) w‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h0 n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h0) i) n hG
    intro j
    exact (hcon (hg.1 i j)).trans (hgB i j n (by omega))
  have hb1 : ‖iteratedFDeriv ℝ n
      (fun v d i j => coordPartial d (fun p => g p i j) (statePoint v)) w‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h1 n hG
    intro d
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h1) d) n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp ((contDiffAt_pi.mp h1) d)) i) n hG
    intro j
    exact ((hcon (partial_contDiffOn (hg.1 i j) hU d)).trans
      (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw d n)).trans
        (hgB i j (n + 1) (by omega))
  have hb2 : ‖iteratedFDeriv ℝ n
      (fun v d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint v)) w‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h2 n hG
    intro d
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h2) d) n hG
    intro e
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp ((contDiffAt_pi.mp h2) d)) e) n hG
    intro i
    apply norm_iteratedFDeriv_pi_le
      ((contDiffAt_pi.mp ((contDiffAt_pi.mp ((contDiffAt_pi.mp h2) d)) e)) i) n hG
    intro j
    exact (((hcon (partial_contDiffOn (partial_contDiffOn (hg.1 i j) hU e) hU d)).trans
      (norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn (hg.1 i j) hU e) hU hw d n)).trans
      (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw e (n + 1))).trans
        (hgB i j (n + 1 + 1) (by omega))
  exact norm_iteratedFDeriv_prod_le h0 hB.snd n (hb0.trans (le_max_right _ _))
    (norm_iteratedFDeriv_prod_le h1 hB.snd.snd n (hb1.trans (le_max_right _ _))
      (norm_iteratedFDeriv_prod_le h2 hId n (hb2.trans (le_max_right _ _))
        ((norm_iteratedFDeriv_id_pos w hn).trans (le_max_left _ _))))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_LocalMetricPCoefficients
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem metricPBundle_norm_bound {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) : ‖metricPBundle g w‖ ≤ max G W := by
  have hb0 (i j : Fin 2) : |g (statePoint w) i j| ≤ G := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hgB i j 0 (by omega)
  have hb1 (d i j : Fin 2) : |coordPartial d (fun p => g p i j) (statePoint w)| ≤ G := by
    have hh := (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw d 0).trans
      (hgB i j 1 (by omega))
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hh
  have hb2 (d e i j : Fin 2) :
      |coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w)| ≤ G := by
    have hh := ((norm_iteratedFDeriv_coordPartial_le
      (partial_contDiffOn (hg.1 i j) hU e) hU hw d 0).trans
      (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw e 1)).trans (hgB i j 2 (by omega))
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hh
  have h0 : ‖g (statePoint w)‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hb0 i j))
  have h1 : ‖(fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hb1 d i j)))
  have h2 : ‖(fun d e i j =>
      coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun e =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
          (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hb2 d e i j))))
  change max ‖g (statePoint w)‖
    (max ‖(fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖
      (max ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖
        ‖w‖)) ≤ max G W
  exact max_le (h0.trans (le_max_left _ _))
    (max_le (h1.trans (le_max_left _ _))
      (max_le (h2.trans (le_max_left _ _)) (hwB.trans (le_max_right _ _))))

theorem metricPBundle_mapsTo_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    MapsTo (metricPBundle g) (darbouxStateDomain g U) universalMetricDomain := by
  intro w hw
  exact ⟨metricDet_ne_zero hg hw.1,
    by simpa only [universalDenominator_metricPBundle] using hw.2⟩

theorem metricPBundle_mem_universalTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W d c : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateDenominator g w|) :
    metricPBundle g w ∈ universalMetricTube (max G W) d c := by
  refine ⟨⟨?_, hdet⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using
      metricPBundle_norm_bound hg hU hw hG hgB hwB
  · simpa only [Set.mem_preimage, Set.mem_ofPred_eq, universalDenominator_metricPBundle] using hden

theorem actualP_jet_bound_from_universalTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxStateDomain g U) {N : ℕ} {G W d c C : ℝ}
    (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j k, k ≤ N + 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateDenominator g w|)
    (hC : ∀ k ≤ N, ∀ a ∈ universalMetricTube (max G W) d c,
      ‖iteratedFDeriv ℝ k universalMetricP a‖ ≤ C)
    {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (sixVariableP g) w‖ ≤ n.factorial * C * (max 1 G)^n := by
  have hD := darbouxStateDomain_isOpen hg hU
  have hsub : darbouxStateDomain g U ⊆ stateBaseDomain U := fun _ hv => hv.1
  have hf := (metricPBundle_contDiffOn hg hU).mono hsub
  have hmap := metricPBundle_mapsTo_domain hg
  have hmem := metricPBundle_mem_universalTube hg hU hw.1 hG
    (fun i j k hk => hgB i j k (by omega)) hwB hdet hden
  have hdomain := universalMetricTube_subset_domain (max G W) hd hc hmem
  have ho : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i universalMetricP universalMetricDomain (metricPBundle g w)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i universalMetricDomain_isOpen hdomain]
    exact hC i (hi.trans hn) (metricPBundle g w) hmem
  have hi : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (metricPBundle g) (darbouxStateDomain g U) w‖ ≤ (max 1 G)^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hD hw]
    exact (metricPBundle_positive_jet_bound hg hU hw.1 hG hgB hi (hin.trans hn)).trans
      (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le universalMetricP_contDiffOn hf
    (WithTop.coe_le_coe.mpr le_top) universalMetricDomain_isOpen.uniqueDiffOn hD.uniqueDiffOn
    hmap hw ho hi
  have heq : iteratedFDerivWithin ℝ n (sixVariableP g) (darbouxStateDomain g U) w =
      iteratedFDerivWithin ℝ n (universalMetricP ∘ metricPBundle g) (darbouxStateDomain g U) w :=
    iteratedFDerivWithin_congr (fun _ hv => sixVariableP_eq_universalMetricP hg hU hv.1) hw n
  rw [iteratedFDerivWithin_of_isOpen n hD hw] at heq
  rw [← heq] at hcomp
  exact hcomp

theorem exists_local_metric_P_jet_bound (G W : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ w : DarbouxState,
      statePoint w ∈ U →
      (∀ i j k, k ≤ N + 2 →
        ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G) →
      ‖w‖ ≤ W → d ≤ |(g (statePoint w)).det| → c ≤ |stateDenominator g w| →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (sixVariableP g) w‖ ≤ C := by
  classical
  obtain ⟨C0, hC0, hCP⟩ := universalMetricTube_finite_P_bounds (max G W) hd hc N
  let C : ℝ := ∑ k : Fin (N + 1), (k.val.factorial : ℝ) * C0 * (max 1 G)^k.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun index _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro g U hg hU w hw hgB hwB hdet hden n hn
  have hne : stateDenominator g w ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hden
    linarith
  have hb := actualP_jet_bound_from_universalTube hg hU ⟨hw, hne⟩ hG hd hc hgB hwB hdet hden hCP hn
  let j : Fin (N + 1) := ⟨n, by omega⟩
  have hsum : (j.val.factorial : ℝ) * C0 * (max 1 G)^j.val ≤
      ∑ i : Fin (N+1), (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val :=
    Finset.single_le_sum
      (f := fun i : Fin (N+1) => (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val)
      (fun index _ => by positivity) (Finset.mem_univ j)
  exact hb.trans hsum

theorem exists_same_region_solution_P_jet_bound (G Z : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → S ⊆ U → S ⊆ modelSquare →
      (∀ i j k, k ≤ N + 2 → ∀ p ∈ S, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      CoordinateBound z S 2 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 1 1|) →
      ∀ n ≤ N, ∀ p ∈ S, ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C := by
  obtain ⟨C, hC, hP⟩ := exists_local_metric_P_jet_bound G (max 3 Z) hG hd hc N
  refine ⟨C, hC, ?_⟩
  intro g z U S hg hU hSU hSS hgB hzB hdet hden n hn p hp
  have hwB : ‖solutionJet z p‖ ≤ max 3 Z := by
    apply (pi_norm_le_iff_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 3) (le_max_left _ _))).mpr
    intro i
    rw [Real.norm_eq_abs]
    fin_cases i
    · exact (abs_le.mpr ⟨(hSS hp).1 0, (hSS hp).2 0⟩).trans (le_max_left 3 Z)
    · exact (abs_le.mpr ⟨(hSS hp).1 1, (hSS hp).2 1⟩).trans (le_max_left 3 Z)
    · exact (hzB [0] (by norm_num) p hp).trans (le_max_right 3 Z)
    · exact (hzB [1] (by norm_num) p hp).trans (le_max_right 3 Z)
    · exact (hzB [0, 1] (by norm_num) p hp).trans (le_max_right 3 Z)
    · exact (hzB [1, 1] (by norm_num) p hp).trans (le_max_right 3 Z)
  exact hP g U hg hU (solutionJet z p)
    (by simpa only [statePoint_solutionJet] using hSU hp)
    (fun i j k hk => by simpa only [statePoint_solutionJet] using hgB i j k hk p hp)
    hwB (by simpa only [statePoint_solutionJet] using hdet p hp)
    (by simpa only [stateDenominator_solutionJet] using hden p hp) n hn

theorem exists_same_region_remainder_outer_bound (G Z : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → S ⊆ U → S ⊆ modelSquare →
      (∀ i j k, k ≤ m + 5 → ∀ p ∈ S, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      CoordinateBound z S 2 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 1 1|) →
      ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ S,
        |coordinateChainCoefficient g z w r p| ≤ C := by
  obtain ⟨C, hC, hP⟩ := exists_same_region_solution_P_jet_bound G Z hG hd hc (m + 3)
  refine ⟨C, hC, ?_⟩
  intro g z U S hg hU hSU hSS hgB hzB hdet hden w hw r p hp
  exact (coordinateChainCoefficient_abs_le_full_derivative g z w r p).trans
    (hP g z U S hg hU hSU hSS (fun i j k hk => hgB i j k (by omega)) hzB hdet hden
      w.arity (residual_scalar_factor_orders hw r).2 p hp)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_PatchTensorRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

def assembledPatchTensor (eta : PatchAddress → SymmetricPerturbation) : MetricField :=
  tensorPatchSum (enumeratedPatchTensor eta)

def assembledPatchMetric (g : MetricField) (eta : PatchAddress → SymmetricPerturbation) : MetricField :=
  g + assembledPatchTensor eta

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_SmoothMetricRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SmoothLocal.Geometry

theorem SmoothPositiveOn.mono {g : MetricField} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hVU : V ⊆ U) : SmoothPositiveOn g V :=
  ⟨fun i j => (hg.1 i j).mono hVU,fun p hp => hg.2 p (hVU hp)⟩

end SmoothLocal.Geometry

end

end OAI
end


