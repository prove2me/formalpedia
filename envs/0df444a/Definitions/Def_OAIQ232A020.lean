-- Prove2me | Definitions.Def_OAIQ232A020
-- name    : OAIQ232A020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:58:24.019211+00:00
-- url     : https://prove2.me/theorems/62ea7a3f-566c-4cd4-bced-776121887368
-- title:
--   Definitions bundle OAIQ232A020 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.WeakMTWTransport.middleSingularValue`, `OAI.WeakMTWTransport.normalizeDualPair`, `OAI.WeakMTWTransport.transformedDifferenceQuotient`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BiholderTransport_Duality_CompactDual`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Duality/CompactDual.lean), [`BiholderTransport_LinearAlgebra_MiddleScaling`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/MiddleScaling.lean), [`BiholderTransport_Regularity_CompactAE`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/CompactAE.lean).
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundle `OAIQ232A017` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.WeakMTWTransport.uniform_endpoint_middle_singular_comparison`; the proofs of `OAI.WeakMTWTransport.WeakMTW.exists_locally_uniform_test_det_bound`, `OAI.WeakMTWTransport.WeakMTW.exists_strict_test_det_bound`, `OAI.WeakMTWTransport.WeakMTW.test_det_bound_on_charts`, `OAI.WeakMTWTransport.WeakMTW.uniform_extended_spectral_comparison`, `OAI.WeakMTWTransport.WeakMTW.uniform_three_determinant_closure`, `OAI.WeakMTWTransport.uniform_biHolder_transport`, `OAI.WeakMTWTransport.uniform_endpoint_middle_singular_comparison`, `OAI.WeakMTWTransport.uniform_sheared_radial_quadratic_bounds` and `OAI.WeakMTWTransport.uniform_sheared_radial_spectrum`.
-- source:
--   OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A017

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_CompactDual
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

variable [MeasurableSpace M] [BorelSpace M]

def normalizeDualPair (x0 : M) (v : M →ᵇ ℝ) : (M →ᵇ ℝ) × (M →ᵇ ℝ) :=
  let a := boundedCTransform v
  (a + BoundedContinuousFunction.const M (-a x0),
    boundedCTransform a + BoundedContinuousFunction.const M (a x0))

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_MiddleScaling
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleSingular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def middleSingularValue (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ) (i : ℕ) : ℝ :=
  intrinsicBilinearSingular (sprayFlow h z).1 (middleHessian z h T) i

end MiddleSingular
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_CompactAE
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

namespace WeakMTWTransport

section CompactAE
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

def transformedDifferenceQuotient (v f : M →ᵇ ℝ) (t : ℝ) : M →ᵇ ℝ :=
  t⁻¹ • (boundedCTransform (v + t • f) - boundedCTransform v)

end CompactAE
end WeakMTWTransport

end

end

end

end OAI
end


