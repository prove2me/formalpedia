-- Prove2me | Definitions.Def_OAIQ237Ny003
-- name    : OAIQ237Ny003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:08:07.722844+00:00
-- url     : https://prove2.me/theorems/266c65ea-3504-4f05-a724-94e7a01e098b
-- title:
--   Definitions bundle OAIQ237Ny003 of the split of OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 18 definitions and 5 theorems. The definitions and types are `OAI.Yau.Target.coefficientAmbientEntry`, `OAI.Yau.Target.coefficientEntryLinear`, `OAI.Yau.Target.modelCoordinateEquiv`, `OAI.Yau.Target.productChart`, `OAI.Yau.Target.productChartDomain`, `OAI.Yau.Target.productChartInverse`, `OAI.Yau.Target.sphereRoundForm`, `OAI.Yau.realCenteredCube`, `OAI.Yau.realL2Convolution`, `OAI.Yau.realMollifierBump`, `OAI.Yau.realSmoothCompactL2`, `OAI.Yau.realSquareCutoff`, `OAI.Yau.realWeakFourJet`, `OAI.Yau.realWeakJetExpansion`, `OAI.Yau.realWeakJetFluxError`, `OAI.Yau.realWeakJetFluxErrorDerivative`, `OAI.Yau.realWeakJetProductSum`, `OAI.Yau.realWeakJetSuccessor`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `NodalSets_Charts_IndependentAmbientMetric`, `NodalSets_Charts_RoundCotangentTensor`, `NodalSets_Charts_TargetProductChart`, `NodalSets_Coefficients_CoefficientAmbientReconstruction`, `NodalSets_Coefficients_MatrixCoefficientBounds`, `NodalSets_Elliptic_RealCompactH1Approximation`, `NodalSets_Elliptic_RealDifferenceQuotientTest`, `NodalSets_Elliptic_RealFiniteWeakJetExtension`, `NodalSets_Elliptic_RealInteriorWeakRestrictionLemmas`, `NodalSets_Elliptic_RealL2Convolution`, `NodalSets_Elliptic_RealMollifierSupport`, `NodalSets_Elliptic_RealSquareCutoffWeakGradient`, `NodalSets_Elliptic_RealWeakJetForcingBounds`, `NodalSets_Elliptic_RealWeakJetLeibniz`, `NodalSets_Elliptic_RealWeakJetProducts`.
--
--   **Imports.** It imports the published bundle `Def_YauCounterexample`; the bundles `OAIQ237Ny000` and `OAIQ237Ny001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ237Ny004`.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
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
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny000
import Definitions.Def_OAIQ237Ny001

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_IndependentAmbientMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma ambientCircleWeight_smooth (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ ambientCircleWeight (A x) (rho x)) := by
  have hd := manifold_positive_sqrt_smooth _ (manifold_matrix_det_smooth A hA)
    (fun x ↦ (hp x).det_pos)
  convert hd.smul (hr.inv₀ (fun x ↦ (hrp x).ne')) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp [ambientCircleWeight,div_eq_mul_inv]

lemma ambientWeightedBase_smooth (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) :
    ContMDiff (𝓡 4) 𝓘(ℝ,AmbientBase →L[ℝ] AmbientBase →L[ℝ] ℝ) ∞
      (fun x ↦ ambientMatrixForm (weightedBaseMatrix (A x) (rho x))) := by
  apply ambientMatrixForm_smooth
  intro i j
  exact hr.smul (manifold_matrix_inverse_smooth A hA (fun x ↦ (hp x).det_pos.ne') i j)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_RoundCotangentTensor
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst1
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst2
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst3
attribute [local instance] OAI.Yau.Target.roundCotangentTensorLocalInst4
def sphereRoundForm (x : Base) : TangentSpace (𝓡 4) x →L[ℝ] TangentSpace (𝓡 4) x →L[ℝ] ℝ :=
  bilinearPullback (innerSL ℝ) (sphereAmbientDerivative x)

lemma sphereRoundForm_pos (x : Base) (v : TangentSpace (𝓡 4) x) (hv : v ≠ 0) :
    0 < sphereRoundForm x v v := by
  change 0 < ⟪sphereAmbientDerivative x v,sphereAmbientDerivative x v⟫
  apply real_inner_self_pos.mpr
  intro h
  exact hv ((injective_mvfderiv_subtypeVal_sphere (n := 4) x) (h.trans (map_zero _).symm))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_TargetProductChart
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Set Filter Yau.Jets
open scoped ContDiff Topology NNReal ENNReal
noncomputable section

def modelCoordinateEquiv : Model ≃L[ℝ] _root_.OAI.Yau.Jets.Coord × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).prodCongr
    (PiLp.equivOfUnique (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 1 ↦ ℝ))

def productChart (p : Manifold5) (a b : ℝ) (m : Manifold5) : _root_.OAI.Yau.Jets.Coord × ℝ :=
  let z := modelCoordinateEquiv (extChartAt modelWithCorners p m)
  (z.1, (z.2-a)/b)

def productChartInverse (p : Manifold5) (a b : ℝ) (z : _root_.OAI.Yau.Jets.Coord × ℝ) : Manifold5 :=
  (extChartAt modelWithCorners p).symm (modelCoordinateEquiv.symm (z.1,a+b*z.2))

def productChartDomain (p : Manifold5) (a b : ℝ) : Set (_root_.OAI.Yau.Jets.Coord × ℝ) :=
  {z | modelCoordinateEquiv.symm (z.1,a+b*z.2) ∈ (extChartAt modelWithCorners p).target}

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientAmbientReconstruction
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance coefficientReconstructionDimension_ref4716_1 : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
def coefficientAmbientEntry (p : Base) (c : BaseModel → CoefficientPoint BaseModel)
    (i j : Fin 5) (z : BaseModel) : ℝ :=
  sphereChartAmbientCovector p (EuclideanSpace.basisFun (Fin 5) ℝ i) z
    ((c z).1 (sphereChartAmbientCovector p (EuclideanSpace.basisFun (Fin 5) ℝ j) z)) +
      (((extChartAt (𝓡 4) p).symm z : AmbientBase) i) *
        (((extChartAt (𝓡 4) p).symm z : AmbientBase) j)

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MatrixCoefficientBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Matrix Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def coefficientEntryLinear (i j : Fin 4) :
    ℝ →L[ℝ] ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin 4) ℝ j)).smulRight
      (EuclideanSpace.basisFun (Fin 4) ℝ i))

end
end Yau.Target

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealDifferenceQuotientTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_compact_continuous_memLp {n : ℕ} (u : Coord n → ℝ)
    (hu : Continuous u) (hc : HasCompactSupport u) : MemLp u 2 volume :=
  (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mpr
    ((hu.pow 2).integrable_of_hasCompactSupport (by
      convert hc.mul_right (f' := u) using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | (ext x; simp [pow_two])))

def realCenteredCube (n : ℕ) (r : ℝ) : Set (Coord n) :=
  Set.univ.pi (fun _ ↦ Set.Icc (-r) r)

theorem realCenteredCube_mono {n : ℕ} {r R : ℝ} (h : r ≤ R) :
    realCenteredCube n r ⊆ realCenteredCube n R := by
  intro x hx j hj
  have hjx := hx j hj
  exact ⟨(neg_le_neg h).trans hjx.1,hjx.2.trans h⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealL2Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology
noncomputable section

def realL2Convolution {n : ℕ} (k : Coord n → ℝ) (U : RealEuclideanL2 n) :
    RealEuclideanL2 n := ∫ t, k t • realL2Translate (-t) U

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealMollifierSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution Topology Pointwise
noncomputable section

def realMollifierBump {n : ℕ} (r : ℝ) (hr : 0 < r) (m : ℕ) :
    ContDiffBump (0 : Coord n) :=
  ⟨(r * (1 / ((m:ℝ)+1)))/2, r * (1 / ((m:ℝ)+1)),
    by positivity, by
      have h : 0 < r * (1 / ((m:ℝ)+1)) := by positivity
      linarith⟩

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealCompactH1Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
noncomputable section

def realSmoothCompactL2 {n : ℕ} (v : Coord n → ℝ)
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) : RealEuclideanL2 n :=
  (real_compact_continuous_memLp v hv.continuous hc).toLp v

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealInteriorWeakRestrictionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set
open scoped ContDiff

def realWeakFourJet (w : Coord 4 → ℝ) (U : Fin 4 → Coord 4 → ℝ)
    (H : Fin 4 → Fin 4 → Coord 4 → ℝ) (J : Fin 4 → Fin 4 → Fin 4 → Coord 4 → ℝ)
    (L : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Coord 4 → ℝ) : List (Fin 4) → Coord 4 → ℝ
  | [] => w
  | [a] => U a
  | [k,a] => H a k
  | [l,k,a] => J a k l
  | [i,l,k,a] => L a k l i
  | _ => 0

end Yau

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealFiniteWeakJetExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

def realWeakJetSuccessor (U : List (Fin 4) → Coord 4 → ℝ)
    (H : List (Fin 4) → Fin 4 → Fin 4 → Coord 4 → ℝ) (N : ℕ) : List (Fin 4) → Coord 4 → ℝ
  | i::a::ds => if ds.length=N then H ds a i else U (i::a::ds)
  | es => U es

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealSquareCutoffWeakGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

def realSquareCutoff {n : ℕ} (eta u : Coord n → ℝ) : Coord n → ℝ :=
  fun x ↦ eta x^2*u x

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetProducts
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis
open scoped ContDiff
noncomputable section

def realWeakJetProductSum (A : Jets.Coord → ℝ) (U : List (Fin 4) → Jets.Coord → ℝ)
    (ts : List (List (Fin 4) × List (Fin 4))) (x : Jets.Coord) : ℝ :=
  (ts.map (fun t ↦ partialJet A t.1 x*U t.2 x)).sum

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetLeibniz
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

def realWeakJetExpansion (A : Jets.Coord → ℝ) (U : List (Fin 4) → Jets.Coord → ℝ)
    (extra ds : List (Fin 4)) (x : Jets.Coord) : ℝ :=
  A x*U (extra++ds) x+realWeakJetProductSum A U (realJetErrorTerms extra ds) x

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RealWeakJetForcingBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MeasureTheory Set Yau.Analysis Yau.Geometry
open scoped ContDiff
noncomputable section

def realWeakJetFluxError (C : Jets.Coord → Fin 4 → Fin 4 → ℝ)
    (U : List (Fin 4) → Jets.Coord → ℝ) (ds : List (Fin 4)) (j : Fin 4) (x : Jets.Coord) : ℝ :=
  ∑ a, realWeakJetProductSum (fun y ↦ C y a j) U (realJetErrorTerms [a] ds) x

def realWeakJetFluxErrorDerivative (C : Jets.Coord → Fin 4 → Fin 4 → ℝ)
    (U : List (Fin 4) → Jets.Coord → ℝ) (ds : List (Fin 4)) (j i : Fin 4) (x : Jets.Coord) : ℝ :=
  ∑ a, realWeakJetProductSum (fun y ↦ C y a j) U
    ((realJetErrorTerms [a] ds).map (fun t ↦ (i::t.1,t.2)) ++
      (realJetErrorTerms [a] ds).map (fun t ↦ (t.1,i::t.2))) x

end
end Yau

end OAI
end


