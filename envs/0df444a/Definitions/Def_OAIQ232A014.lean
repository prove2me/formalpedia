-- Prove2me | Definitions.Def_OAIQ232A014
-- name    : OAIQ232A014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:47:01.553036+00:00
-- url     : https://prove2.me/theorems/ad2fc169-1f9b-4bbe-90c8-f24f7333fcb7
-- title:
--   Definitions bundle OAIQ232A014 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BiholderTransport_Coordinates_NormalCoordinates2`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/NormalCoordinates2.lean).
--
--   **Imports.** It imports the bundle `OAIQ232A007` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ232A021`.
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
import Definitions.Def_OAIQ232A007

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalCoordinates2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma coordinate_geodesic_zero_velocity
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {γ V : ℝ → E} {a b : ℝ}
    (hg : ∀ t ∈ Ioo a b, DifferentiableAt ℝ g (γ t))
    (hi : ∀ t ∈ Ioo a b, (g (γ t)).IsInvertible)
    (hpos : ∀ t ∈ Ioo a b, ∀ w : E, w ≠ 0 → 0 < g (γ t) w w)
    (hsym : ∀ t ∈ Ioo a b, ∀ u v, g (γ t) u v = g (γ t) v u)
    (hode : ∀ t ∈ Ioo a b, HasDerivAt γ (V t) t ∧
      HasDerivAt V (-coordinateChristoffel g (γ t) (V t) (V t)) t)
    {s : ℝ} (hs : s ∈ Ioo a b) (hVs : V s = 0) {t : ℝ} (ht : t ∈ Ioo a b) :
    γ t = γ s ∧ V t = 0 := by
  have hVz : ∀ q ∈ Ioo a b, V q = 0 := by
    intro q hq
    have h := coordinate_geodesic_speed_constant hg hi hsym hode hq hs
    simp only [hVs,map_zero] at h
    by_contra hn
    exact (ne_of_gt (hpos q hq _ hn)) h
  refine ⟨?_,hVz t ht⟩
  apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun q hq => (hode q hq).1.differentiableAt.differentiableWithinAt) _ ht hs
  intro q hq
  exact (hode q hq).1.deriv.trans (hVz q hq)

end

end WeakMTWTransport

end

end OAI
end


