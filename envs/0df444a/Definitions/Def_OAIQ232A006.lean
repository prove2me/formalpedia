-- Prove2me | Definitions.Def_OAIQ232A006
-- name    : OAIQ232A006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:44:24.562467+00:00
-- url     : https://prove2.me/theorems/df10b68d-f4d3-4a03-9424-061f15bf6624
-- title:
--   Definitions bundle OAIQ232A006 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 3 definitions and 20 theorems. The definitions and types are `OAI.WeakMTWTransport.extendUnitPath`, `OAI.WeakMTWTransport.pathCalculusNormedAddCommGroupContinuousMap`, `OAI.WeakMTWTransport.tangentLiftNormedSpaceEndomorphism`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BiholderTransport_Calculus_PathCalculus`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/PathCalculus.lean), [`BiholderTransport_Calculus_SmoothDistance`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/SmoothDistance.lean), [`BiholderTransport_Coordinates_ChartTransition`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/ChartTransition.lean), [`BiholderTransport_Coordinates_Coordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/Coordinates.lean), [`BiholderTransport_Coordinates_TangentLift`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/TangentLift.lean), [`BiholderTransport_Geodesics_GeodesicSpray`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Geodesics/GeodesicSpray.lean), [`BiholderTransport_LocalFlow_MIntegralCurveUniformInvariant`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LocalFlow/MIntegralCurveUniformInvariant.lean), [`BiholderTransport_Regularity_UnitTime`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/UnitTime.lean).
--
--   **Imports.** It imports the bundles `OAIQ232A000` and `OAIQ232A001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A013` and `OAIQ232A016`.
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
import Definitions.Def_OAIQ232A000
import Definitions.Def_OAIQ232A001

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_PathCalculus
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

namespace WeakMTWTransport
universe u w
variable {K : Type w} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.WeakMTWTransport.pathCalculusNormedAddCommGroupContinuousLinearMap
attribute [local instance] OAI.WeakMTWTransport.pathCalculusNormedSpaceContinuousLinearMap
local instance pathCalculusNormedAddCommGroupContinuousMap :
    NormedAddCommGroup C(K,E →L[ℝ] F) := ContinuousMap.instNormedAddCommGroup

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_Coordinates
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance] OAI.WeakMTWTransport.instNormedSpaceReal_solutions
attribute [local instance] OAI.WeakMTWTransport.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.WeakMTWTransport.instNormedSpaceRealContinuousLinearMapId_solutions
attribute [local instance] OAI.WeakMTWTransport.instNormedAddCommGroupContinuousLinearMapRealId_solutions_1
attribute [local instance] OAI.WeakMTWTransport.instNormedSpaceRealContinuousLinearMapId_solutions_1
attribute [local instance] OAI.WeakMTWTransport.instNormedAddCommGroupContinuousLinearMapRealId_solutions_2
attribute [local instance] OAI.WeakMTWTransport.instNormedSpaceRealContinuousLinearMapId_solutions_2
lemma metricDual_isInvertible [FiniteDimensional ℝ E] (b : E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ v : E, v ≠ 0 → 0 < b v v) : b.IsInvertible := by
  have hinj : Function.Injective b := by
    intro u v huv
    have hz : b (u-v) = 0 := by rw [map_sub,huv,sub_self]
    by_contra huv'
    have hp := hb (u-v) (sub_ne_zero.mpr huv')
    simp only [hz,zero_apply] at hp
    exact (lt_irrefl 0) hp
  let A : E →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp b
  have hA : Function.Injective A := (InnerProductSpace.toDual ℝ E).symm.injective.comp hinj
  have hAsur : Function.Surjective A := LinearMap.injective_iff_surjective.mp hA
  have hsur : Function.Surjective b := by
    intro q
    obtain ⟨v,hv⟩ := hAsur ((InnerProductSpace.toDual ℝ E).symm q)
    refine ⟨v,(InnerProductSpace.toDual ℝ E).symm.injective hv⟩
  exact ⟨ContinuousLinearEquiv.ofBijective b (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsur),rfl⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_SmoothDistance
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance] OAI.WeakMTWTransport.smoothDistanceNormedSpace
local instance smoothDistanceNormedAddCommGroupEndomorphism_rc9ee8b_1 :
    NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance smoothDistanceNormedSpaceEndomorphism_rc9ee8b_1 :
    NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.WeakMTWTransport.smoothDistanceNormedAddCommGroupDual
attribute [local instance] OAI.WeakMTWTransport.smoothDistanceNormedSpaceDual
attribute [local instance] OAI.WeakMTWTransport.smoothDistanceNormedAddCommGroupBilinear
attribute [local instance] OAI.WeakMTWTransport.smoothDistanceNormedSpaceBilinear
lemma christoffel_pushforward_pairing
    {g h : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {x : E}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h (φ x))
    (hφ : ContDiffAt ℝ ∞ φ x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v, g y u v = h (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v))
    (hgi : (g x).IsInvertible) (hhi : (h (φ x)).IsInvertible)
    (hhs : ∀ u v, h (φ x) u v = h (φ x) v u) (u v w : E) :
    h (φ x) (fderiv ℝ φ x (coordinateChristoffel g x u v)) (fderiv ℝ φ x w) =
      h (φ x) (fderiv ℝ (fderiv ℝ φ) x u v +
        coordinateChristoffel h (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v))
        (fderiv ℝ φ x w) := by
  have hpd := hφ.differentiableAt (by simp)
  have hD := (hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hp := derivative_pullback_metric hg hh hpd hD hmetric
  have hm := hmetric.self_of_nhds
  have hb : ∀ u v, fderiv ℝ (fderiv ℝ φ) x u v = fderiv ℝ (fderiv ℝ φ) x v u := by
    intro u v
    exact (hφ.isSymmSndFDerivAt (by simp)).eq u v
  have h1 := coordinateChristoffel_metric g x u v w hgi
  have h2 := coordinateChristoffel_metric h (φ x) (fderiv ℝ φ x u)
    (fderiv ℝ φ x v) (fderiv ℝ φ x w) hhi
  rw [hm,hp u v w,hp v u w,hp w u v] at h1
  rw [hb v u,hb w u,hb w v] at h1
  rw [hhs (fderiv ℝ φ x v) _,hhs (fderiv ℝ φ x u) _] at h1
  simp only [map_add,add_apply]
  linarith

lemma christoffel_pushforward
    {g h : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {x : E}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h (φ x))
    (hφ : ContDiffAt ℝ ∞ φ x) (hφs : Function.Surjective (fderiv ℝ φ x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v, g y u v = h (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v))
    (hgi : (g x).IsInvertible) (hhi : (h (φ x)).IsInvertible)
    (hhs : ∀ u v, h (φ x) u v = h (φ x) v u) (u v : E) :
    fderiv ℝ φ x (coordinateChristoffel g x u v) =
      fderiv ℝ (fderiv ℝ φ) x u v +
        coordinateChristoffel h (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v) := by
  have heq : h (φ x) (fderiv ℝ φ x (coordinateChristoffel g x u v)) =
      h (φ x) (fderiv ℝ (fderiv ℝ φ) x u v +
        coordinateChristoffel h (φ x) (fderiv ℝ φ x u) (fderiv ℝ φ x v)) := by
    ext w
    obtain ⟨z,rfl⟩ := hφs w
    exact christoffel_pushforward_pairing hg hh hφ hmetric hgi hhi hhs u v z
  rcases hhi with ⟨A,hA⟩
  apply A.injective
  change A.toContinuousLinearMap _ = A.toContinuousLinearMap _
  rw [hA]
  exact heq
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartTransition
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma symmL_chart_transition {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source) (v : E) :
    (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) b).symmL ℝ x
      (fderiv ℝ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
        (extChartAt 𝓘(ℝ,E) a x) v) =
    (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ x v := by
  have ha' : x ∈ (chartAt E a).source := by simpa only [extChartAt_source] using ha
  have hb' : x ∈ (chartAt E b).source := by simpa only [extChartAt_source] using hb
  rw [(hasFDerivAt_chart_transition ha hb).fderiv,
    Trivialization.symmL_apply _ hb', Trivialization.symmL_apply _ ha']
  have hsA (u : E) : (trivializationAt E (TangentSpace 𝓘(ℝ,E)) a).symm x u =
      tangentCoordChange 𝓘(ℝ,E) a x x u :=
    (tangentBundleCore 𝓘(ℝ,E) M).localTriv_symm_apply (i := achart E a) ha' u
  have hsB (u : E) : (trivializationAt E (TangentSpace 𝓘(ℝ,E)) b).symm x u =
      tangentCoordChange 𝓘(ℝ,E) b x x u :=
    (tangentBundleCore 𝓘(ℝ,E) M).localTriv_symm_apply (i := achart E b) hb' u
  rw [hsA,hsB]
  have h := tangentCoordChange_comp (I := 𝓘(ℝ,E)) (w := a) (x := b) (y := x)
    (z := x) (v := v) ⟨⟨ha,hb⟩,mem_extChartAt_source x⟩
  exact h

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma chart_metric_transition {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source)
    {g h : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ∀ u v : E, g (extChartAt 𝓘(ℝ,E) a x) u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ x u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ x v))
    (hh : ∀ u v : E, h (extChartAt 𝓘(ℝ,E) b x) u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) b).symmL ℝ x u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) b).symmL ℝ x v))
    (u v : E) :
    g (extChartAt 𝓘(ℝ,E) a x) u v =
      h (extChartAt 𝓘(ℝ,E) b x)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
          (extChartAt 𝓘(ℝ,E) a x) u)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
          (extChartAt 𝓘(ℝ,E) a x) v) := by
  rw [hg,hh,symmL_chart_transition ha hb,symmL_chart_transition ha hb]

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_TangentLift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
attribute [local instance] OAI.WeakMTWTransport.tangentLiftNormedSpace
local instance tangentLiftNormedSpaceEndomorphism : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

attribute [local instance] OAI.WeakMTWTransport.tangentLiftNormedAddCommGroupEndomorphism
local instance tangentLiftNormedAddCommGroupDual_rc9ee8b_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance tangentLiftNormedSpaceDual_rc9ee8b_1 : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance tangentLiftNormedAddCommGroupBilinear_rc9ee8b_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance tangentLiftNormedSpaceBilinear_rc9ee8b_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
lemma fderiv_coordinateTangentLift {φ : E → E} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hDφ : DifferentiableAt ℝ (fderiv ℝ φ) x)
    (v u w : E) :
    fderiv ℝ (coordinateTangentLift φ) (x,v) (u,w) =
      (fderiv ℝ φ x u, fderiv ℝ (fderiv ℝ φ) x u v + fderiv ℝ φ x w) := by
  have h1 := hφ.hasFDerivAt.comp (x,v) (hasFDerivAt_fst (𝕜 := ℝ))
  have h2 := (hDφ.hasFDerivAt.comp (x,v) (hasFDerivAt_fst (𝕜 := ℝ))).clm_apply
    (hasFDerivAt_snd (𝕜 := ℝ))
  have he := congrArg (fun L : (E × E) →L[ℝ] (E × E) => L (u,w)) (h1.prodMk h2).fderiv
  change fderiv ℝ (fun y : E × E => (φ y.1, fderiv ℝ φ y.1 y.2)) (x,v) (u,w) = _
  convert he using 1 <;> first | (with_reducible_and_instances rfl) | (simp [add_comm])

lemma coordinateTangentLift_push_geodesicField
    {g h : E → E →L[ℝ] E →L[ℝ] ℝ} {φ : E → E} {x v : E}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h (φ x))
    (hφ : ContDiffAt ℝ ∞ φ x) (hφs : Function.Surjective (fderiv ℝ φ x))
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v,
      g y u v = h (φ y) (fderiv ℝ φ y u) (fderiv ℝ φ y v))
    (hgi : (g x).IsInvertible) (hhi : (h (φ x)).IsInvertible)
    (hhs : ∀ u v, h (φ x) u v = h (φ x) v u) :
    fderiv ℝ (coordinateTangentLift φ) (x,v) (coordinateGeodesicField g (x,v)) =
      coordinateGeodesicField h (coordinateTangentLift φ (x,v)) := by
  have hpd := hφ.differentiableAt (by simp)
  have hD := (hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have heq := christoffel_pushforward hg hh hφ hφs hmetric hgi hhi hhs v v
  change fderiv ℝ (coordinateTangentLift φ) (x,v) (v,-coordinateChristoffel g x v v) = _
  rw [fderiv_coordinateTangentLift hpd hD]
  apply Prod.ext
  · rfl
  · change fderiv ℝ (fderiv ℝ φ) x v v + fderiv ℝ φ x (-coordinateChristoffel g x v v) =
      -coordinateChristoffel h (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x v)
    rw [map_neg,heq]
    abel

end

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma riemannianCoordinateMetric_symm (a : M) (z u v : E) :
    riemannianCoordinateMetric a z u v = riemannianCoordinateMetric a z v u :=
by
  simp only [riemannianCoordinateMetric_apply]
  exact real_inner_comm _ _

lemma riemannianCoordinateMetric_positive {a : M} {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ,E) a).target) {v : E} (hv : v ≠ 0) :
    0 < riemannianCoordinateMetric a z v v := by
  rw [riemannianCoordinateMetric_apply,real_inner_self_pos]
  have hbase : (extChartAt 𝓘(ℝ,E) a).symm z ∈
      (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) a).map_target hz
  exact fun hzero => hv (((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).continuousLinearEquivAt ℝ _ hbase).symm.injective
        (by simpa only [Trivialization.symm_continuousLinearEquivAt_eq,map_zero] using hzero))

variable [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

local instance tangentLiftNormedAddCommGroupCotangent_rc9ee8b_1 (x : M) : NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance tangentLiftNormedSpaceCotangent_rc9ee8b_1 (x : M) : NormedSpace ℝ (TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
attribute [local instance] OAI.WeakMTWTransport.tangentLiftContinuousAddCotangent
attribute [local instance] OAI.WeakMTWTransport.tangentLiftContinuousSMulCotangent
lemma contDiffOn_riemannianCoordinateMetric (a : M) :
    ContDiffOn ℝ ∞ (riemannianCoordinateMetric a) (extChartAt 𝓘(ℝ,E) a).target := by
  let T := fun x : M => TangentSpace 𝓘(ℝ,E) x
  obtain ⟨b,hb,hinner⟩ := IsContMDiffRiemannianBundle.exists_contMDiff
    (IB := 𝓘(ℝ,E)) (n := ∞) (F := E) (E := T)
  let e := trivializationAt E T a
  let eB := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ) (fun x => T x →L[ℝ] T x →L[ℝ] ℝ) a
  let c : M → E →L[ℝ] E →L[ℝ] ℝ := fun x =>
    inCoordinates E T (E →L[ℝ] ℝ) (fun x => T x →L[ℝ] ℝ) a x a x (b x)
  have hc : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞ c e.baseSet := by
    intro x hx
    have hxB : x ∈ eB.baseSet := by
      change x ∈ e.baseSet ∩ (e.baseSet ∩ univ)
      exact ⟨hx,hx,mem_univ x⟩
    have hh := (eB.contMDiffAt_section_iff hxB).mp (hb x)
    exact hh.contMDiffWithinAt
  have hmaps : MapsTo (extChartAt 𝓘(ℝ,E) a).symm
      (extChartAt 𝓘(ℝ,E) a).target e.baseSet := by
    intro z hz
    change (extChartAt 𝓘(ℝ,E) a).symm z ∈ (chartAt E a).source
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,E) a).map_target hz
  have hs := hc.comp (contMDiffOn_extChartAt_symm a) hmaps
  apply (contMDiffOn_iff_contDiffOn.mp hs).congr
  intro z hz
  ext u v
  change riemannianCoordinateMetric a z u v = c ((extChartAt 𝓘(ℝ,E) a).symm z) u v
  simp only [c]
  rw [inCoordinates_apply_eq₂ (hmaps hz) (hmaps hz) (mem_univ _)]
  rw [riemannianCoordinateMetric_apply,hinner]
  simp only [Trivial.fiberBundle_trivializationAt',Trivial.linearMapAt_trivialization,
    LinearMap.id_coe,id_eq]
  change b _ (e.symmL ℝ _ u) (e.symmL ℝ _ v) = b _ (e.symm _ u) (e.symm _ v)
  rw [Trivialization.symmL_apply e (hmaps hz),Trivialization.symmL_apply e (hmaps hz)]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GeodesicSpray
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

namespace WeakMTWTransport
open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma tangent_chart_transition_eventually (a b : TangentBundle 𝓘(ℝ,E) M)
    {z : E × E} (ha : z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target)
    (hb : (extChartAt 𝓘(ℝ,E) a.1).symm z.1 ∈ (extChartAt 𝓘(ℝ,E) b.1).source) :
    (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) b ∘
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm) =ᶠ[𝓝 z]
      coordinateTangentLift (extChartAt 𝓘(ℝ,E) b.1 ∘ (extChartAt 𝓘(ℝ,E) a.1).symm) := by
  have h1 : ∀ᶠ y in 𝓝 z, y.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target :=
    continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_target a.1).mem_nhds ha)
  have h2 : ∀ᶠ y in 𝓝 z,
      (extChartAt 𝓘(ℝ,E) a.1).symm y.1 ∈ (extChartAt 𝓘(ℝ,E) b.1).source :=
    ((continuousAt_extChartAt_symm'' ha).comp continuousAt_fst).preimage_mem_nhds
      ((isOpen_extChartAt_source b.1).mem_nhds hb)
  filter_upwards [h1,h2] with y hy1 hy2
  exact tangent_chart_transition_apply a b y hy1 hy2

lemma tangent_tangentCoordChange_apply (a b z : TangentBundle 𝓘(ℝ,E) M)
    (ha : z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).source)
    (hb : z.1 ∈ (extChartAt 𝓘(ℝ,E) b.1).source) (w : E × E) :
    tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a b z w =
      fderiv ℝ (coordinateTangentLift
        (extChartAt 𝓘(ℝ,E) b.1 ∘ (extChartAt 𝓘(ℝ,E) a.1).symm))
        (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z) w := by
  have heq := tangent_chart_transition_eventually a b
    (z := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z)
    ((extChartAt 𝓘(ℝ,E) a.1).map_source ha)
    (by simpa only [tangent_chart_apply,(extChartAt 𝓘(ℝ,E) a.1).left_inv ha] using hb)
  simp only [tangentCoordChange_def,ModelWithCorners.range_eq_univ,fderivWithin_univ]
  exact congrArg (fun L : (E × E) →L[ℝ] (E × E) => L w) heq.fderiv_eq

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma riemannianCoordinateMetric_isInvertible [FiniteDimensional ℝ E] {a : M} {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ,E) a).target) :
    (riemannianCoordinateMetric a z).IsInvertible :=
  metricDual_isInvertible _ (fun _ hv => riemannianCoordinateMetric_positive hz hv)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma riemannianMetric_transition_eventually {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source) :
    ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ,E) a x), ∀ u v,
      riemannianCoordinateMetric a y u v =
        riemannianCoordinateMetric b
          ((extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm) y)
          (fderiv ℝ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm) y u)
          (fderiv ℝ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm) y v) := by
  have ht := (extChartAt 𝓘(ℝ,E) a).map_source ha
  have h1 := (isOpen_extChartAt_target a).mem_nhds ht
  have h2 : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ,E) a x),
      (extChartAt 𝓘(ℝ,E) a).symm y ∈ (extChartAt 𝓘(ℝ,E) b).source :=
    (continuousAt_extChartAt_symm'' ht).preimage_mem_nhds
      (by simpa only [(extChartAt 𝓘(ℝ,E) a).left_inv ha] using
        (isOpen_extChartAt_source b).mem_nhds hb)
  filter_upwards [h1,h2] with y hy1 hy2
  have hy0 := (extChartAt 𝓘(ℝ,E) a).map_target hy1
  intro u v
  have h := chart_metric_transition hy0 hy2
    (g := riemannianCoordinateMetric a) (h := riemannianCoordinateMetric b)
    (fun u v => by rw [riemannianCoordinateMetric_apply,(extChartAt 𝓘(ℝ,E) a).left_inv hy0])
    (fun u v => by rw [riemannianCoordinateMetric_apply,(extChartAt 𝓘(ℝ,E) b).left_inv hy2]) u v
  simpa only [(extChartAt 𝓘(ℝ,E) a).right_inv hy1,Function.comp_apply] using h

lemma geodesicSpray_coordinates [FiniteDimensional ℝ E] (a z : TangentBundle 𝓘(ℝ,E) M)
    (ha : z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).source) :
    tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z a z (geodesicSpray z) =
      coordinateGeodesicField (riemannianCoordinateMetric a.1)
        (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z) := by
  have hz := mem_extChartAt_source (I := 𝓘(ℝ,E)) z.1
  have htz := (extChartAt 𝓘(ℝ,E) z.1).map_source hz
  have hta := (extChartAt 𝓘(ℝ,E) a.1).map_source ha
  change tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z a z
    (coordinateGeodesicField (riemannianCoordinateMetric z.1)
      (extChartAt 𝓘(ℝ,E) z.1 z.1,z.2)) = _
  rw [tangent_tangentCoordChange_apply z a z hz ha]
  have hφ := contDiffAt_chart_transition hz ha
  have he := coordinateTangentLift_push_geodesicField (E := E)
    ((contDiffOn_riemannianCoordinateMetric z.1).contDiffAt
      ((isOpen_extChartAt_target z.1).mem_nhds htz) |>.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (g := riemannianCoordinateMetric z.1) (h := riemannianCoordinateMetric a.1)
    (φ := extChartAt 𝓘(ℝ,E) a.1 ∘ (extChartAt 𝓘(ℝ,E) z.1).symm)
    (v := z.2)
    (by simpa only [Function.comp_apply,(extChartAt 𝓘(ℝ,E) z.1).left_inv hz] using
      ((contDiffOn_riemannianCoordinateMetric a.1).contDiffAt
        ((isOpen_extChartAt_target a.1).mem_nhds hta) |>.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))
    hφ (chart_transition_derivative_surjective hz ha)
    (riemannianMetric_transition_eventually hz ha)
    (riemannianCoordinateMetric_isInvertible htz)
    (by simpa only [Function.comp_apply,(extChartAt 𝓘(ℝ,E) z.1).left_inv hz] using
      riemannianCoordinateMetric_isInvertible hta)
    (riemannianCoordinateMetric_symm a.1 _)
  have hcoord : extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z z =
      (extChartAt 𝓘(ℝ,E) z.1 z.1,z.2) := by
    rw [tangent_chart_apply]
    exact congrArg (fun v : E => (extChartAt 𝓘(ℝ,E) z.1 z.1,v))
      (tangentCoordChange_self (I := 𝓘(ℝ,E)) (v := z.2) hz)
  have hlift : coordinateTangentLift
      (extChartAt 𝓘(ℝ,E) a.1 ∘ (extChartAt 𝓘(ℝ,E) z.1).symm)
      (extChartAt 𝓘(ℝ,E) z.1 z.1,z.2) =
      extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z := by
    rw [tangent_chart_apply]
    simp only [coordinateTangentLift,Function.comp_apply,
      (extChartAt 𝓘(ℝ,E) z.1).left_inv hz,(hasFDerivAt_chart_transition hz ha).fderiv]
  rw [hcoord]
  rw [hlift] at he
  convert! he using 1
  all_goals try with_reducible_and_instances rfl

lemma contMDiff_geodesicSpray [FiniteDimensional ℝ E] :
    ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,E))
      ((𝓘(ℝ,E).prod 𝓘(ℝ,E)).prod 𝓘(ℝ,E × E)) ∞
      (fun z : TangentBundle 𝓘(ℝ,E) M =>
        (⟨z,geodesicSpray z⟩ : TangentBundle (𝓘(ℝ,E).prod 𝓘(ℝ,E)) _)) := by
  intro a
  apply (Bundle.contMDiffAt_section a).mpr
  have ha := mem_extChartAt_source (I := 𝓘(ℝ,E)) a.1
  have hat := (extChartAt 𝓘(ℝ,E) a.1).map_source ha
  have hg := (contDiffOn_riemannianCoordinateMetric a.1).contDiffAt
    ((isOpen_extChartAt_target a.1).mem_nhds hat)
  have hf := contDiffAt_coordinateGeodesicField (E := E) (v := a.2) hg
    (riemannianCoordinateMetric_isInvertible hat)
  have hself : extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a a =
      (extChartAt 𝓘(ℝ,E) a.1 a.1,a.2) := by
    rw [tangent_chart_apply]
    exact congrArg (fun v : E => (extChartAt 𝓘(ℝ,E) a.1 a.1,v))
      (tangentCoordChange_self (I := 𝓘(ℝ,E)) (v := a.2) ha)
  have hf' : ContMDiffAt 𝓘(ℝ,E × E) 𝓘(ℝ,E × E) ∞
      (coordinateGeodesicField (riemannianCoordinateMetric a.1))
      (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a a) := by
    rw [hself]
    exact hf.contMDiffAt
  have hc := (contMDiffOn_extChartAt (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E))
    (n := ∞) (x := a)).contMDiffAt
    (by simpa only [extChartAt_source] using
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).mem_nhds
        (mem_extChartAt_source (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a)))
  apply (hf'.comp a hc).congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).mem_nhds
        (mem_extChartAt_source (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a)] with z hz
  change tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z a z (geodesicSpray z) = _
  exact geodesicSpray_coordinates a z ((tangent_chart_source_iff a z).mp hz)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_UnitTime
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.WeakMTWTransport.instFactLeRealOfNat_solutions
def extendUnitPath (u : C(UnitTime,E)) : C(ℝ,E) :=
  u.comp (ContinuousMap.projIccCM (a := (0:ℝ)) (b := 1))

omit [NormedSpace ℝ E] in
@[simp] lemma extendUnitPath_coe (u : C(UnitTime,E)) (t : UnitTime) :
    extendUnitPath u t = u t := by
  change u (projIcc 0 1 (by positivity) t) = u t
  rw [projIcc_of_mem _ t.property]

omit [NormedSpace ℝ E] in
@[simp] lemma extendUnitPath_add (u v : C(UnitTime,E)) :
    extendUnitPath (u+v) = extendUnitPath u + extendUnitPath v := rfl

@[simp] lemma extendUnitPath_smul (c : ℝ) (u : C(UnitTime,E)) :
    extendUnitPath (c • u) = c • extendUnitPath u := rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_MIntegralCurveUniformInvariant
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

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

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set

section
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [T2Space M]

lemma exists_isMIntegralCurve_of_uniform_invariant_set [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x}
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {ε : ℝ} (hε : 0 < ε) {K : Set M}
    (h : ∀ x ∈ K, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε))
    (hinv : ∀ (a : ℝ) (γ : ℝ → M), γ 0 ∈ K →
      IsMIntegralCurveOn γ v (Ioo (-a) a) → MapsTo γ (Ioo (-a) a) K)
    (x : M) (hx : x ∈ K) : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  let s := { a | ∃ γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-a) a) }
  suffices hbdd : ¬BddAbove s by
    rw [not_bddAbove_iff] at hbdd
    rw [exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hv]
    intro a
    obtain ⟨y, ⟨γ, hγ1, hγ2⟩, hlt⟩ := hbdd a
    exact ⟨γ, hγ1, hγ2.mono <| Ioo_subset_Ioo (neg_le_neg hlt.le) hlt.le⟩
  intro hbdd
  set asup := sSup s with hasup

  obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup (⟨ε, h x hx⟩ : Set.Nonempty s) (ε := - (ε / 2))
    (by rw [neg_lt, neg_zero]; exact half_pos hε)
  rw [mem_ofPred] at ha
  rw [← hasup, ← sub_eq_add_neg] at hlt

  obtain ⟨γ, h0, hγ⟩ := ha
  have hεle : ε ≤ asup := le_csSup hbdd (h x hx)

  obtain ⟨γ1_aux, h1_aux, hγ1⟩ := h (γ (-(asup - ε / 2)))
    (hinv a γ (h0 ▸ hx) hγ ⟨by linarith, by linarith⟩)
  rw [← isMIntegralCurveOn_comp_add (dt := asup - ε / 2)] at hγ1
  set γ1 := γ1_aux ∘ (· + (asup - ε / 2)) with γ1_def
  have heq1 : γ1 (-(asup - ε / 2)) = γ (-(asup - ε / 2)) := by simp [γ1_def, h1_aux]

  obtain ⟨γ2_aux, h2_aux, hγ2⟩ := h (γ (asup - ε / 2))
    (hinv a γ (h0 ▸ hx) hγ ⟨by linarith, hlt⟩)
  rw [← isMIntegralCurveOn_comp_sub (dt := asup - ε / 2)] at hγ2
  set γ2 := γ2_aux ∘ (· - (asup - ε / 2)) with γ2_def
  have heq2 : γ2 (asup - ε / 2) = γ (asup - ε / 2) := by simp [γ2_def, h2_aux]

  simp_rw [Set.mem_Ioo, ← sub_lt_iff_lt_add, ← lt_sub_iff_add_lt, ← Set.mem_Ioo] at hγ1
  simp_rw [Set.mem_Ioo, lt_sub_iff_add_lt, sub_lt_iff_lt_add, ← Set.mem_Ioo] at hγ2

  set γ_ext : ℝ → M := piecewise (Ioo (-(asup + ε / 2)) a)
    (piecewise (Ioo (-a) a) γ γ1) γ2 with γ_ext_def
  have heq_ext : γ_ext 0 = x := by
    rw [γ_ext_def, piecewise, ite_eq_left ⟨by linarith, by linarith⟩, piecewise,
      ite_eq_left ⟨by linarith, by linarith⟩, h0]

  suffices hext : IsMIntegralCurveOn γ_ext v (Ioo (-(asup + ε / 2)) (asup + ε / 2)) from
    (not_lt.mpr <| le_csSup hbdd ⟨γ_ext, heq_ext, hext⟩) <| lt_add_of_pos_right asup (half_pos hε)
  apply (isMIntegralCurveOn_piecewise (t₀ := asup - ε / 2) hv _ hγ2
      ⟨⟨by linarith, hlt⟩, ⟨by linarith, by linarith⟩⟩
      (by rw [piecewise, ite_eq_left ⟨by linarith, hlt⟩, ← heq2])).mono
    (Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith))
  exact (isMIntegralCurveOn_piecewise (t₀ := -(asup - ε / 2)) hv hγ hγ1
      ⟨⟨neg_lt_neg hlt, by linarith⟩, ⟨by linarith, by linarith⟩⟩ heq1.symm).mono
    (union_comm _ _ ▸ Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl)

end
open Manifold Bundle
open scoped Manifold Bundle

end WeakMTWTransport

end

end OAI
end


