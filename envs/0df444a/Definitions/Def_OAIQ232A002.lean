-- Prove2me | Definitions.Def_OAIQ232A002
-- name    : OAIQ232A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:40:41.938177+00:00
-- url     : https://prove2.me/theorems/10f6e29a-5ea6-4bc5-8499-0b949e11b523
-- title:
--   Definitions bundle OAIQ232A002 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 3 definitions and 9 theorems. The definitions and types are `OAI.WeakMTWTransport.actionKernelDualNormedAddCommGroup`, `OAI.WeakMTWTransport.fiberwiseHomeomorph`, `OAI.WeakMTWTransport.tangentScale`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BiholderTransport_Coordinates_CoordinateMetricNorm`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/CoordinateMetricNorm.lean), [`BiholderTransport_Coordinates_FiberwiseHomeomorphism`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/FiberwiseHomeomorphism.lean), [`BiholderTransport_Geodesics_SprayScaling`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Geodesics/SprayScaling.lean), [`BiholderTransport_LinearAlgebra_LocalNormalChart`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/LinearAlgebra/LocalNormalChart.lean), [`BiholderTransport_Regularity_ActionKernel`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/ActionKernel.lean), [`BiholderTransport_Regularity_MetricDefinitions`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MetricDefinitions.lean), [`BiholderTransport_Volume_RadialCalibration`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Volume/RadialCalibration.lean).
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A007`, `OAIQ232A009` and `OAIQ232A012`.
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

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateMetricNorm
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_metric_norm {a : M} {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ,E) a).target)
    {g : E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ∀ u v : E, g u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) a).symm z) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) a).symm z) v)) (v : E) :
    Real.sqrt (g v v) = ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a).symm z v‖ := by
  have hsrc := (extChartAt 𝓘(ℝ,E) a).map_target hz
  have hsrc' : (extChartAt 𝓘(ℝ,E) a).symm z ∈ (chartAt E a).source := by
    simpa only [extChartAt_source] using hsrc
  have heq := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ,E)) hsrc'
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at heq
  have hinv : extChartAt 𝓘(ℝ,E) a ((extChartAt 𝓘(ℝ,E) a).symm z) = z :=
    (extChartAt 𝓘(ℝ,E) a).right_inv hz
  rw [hinv] at heq
  rw [hg,heq,real_inner_self_eq_norm_sq,Real.sqrt_sq_eq_abs,abs_norm]
  rfl

lemma inverse_coordinate_path_length {c : M} {η : ℝ → E} {a b : ℝ}
    (hη : ContDiffOn ℝ 1 η (Icc a b))
    (himg : MapsTo η (Icc a b) (extChartAt 𝓘(ℝ,E) c).target)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ t ∈ Icc a b, ∀ u v : E, g (η t) u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm (η t)) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm (η t)) v)) :
    pathELength 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g (η t) (deriv η t) (deriv η t))) := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo,←restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hηd := (hη.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero
  have hφd : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm (η t) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) c) _ (himg ht')).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds (himg ht')) |>.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hcomp := mfderiv_comp t hφd (mdifferentiableAt_iff_differentiableAt.mpr hηd)
  have hval := congrArg (fun L => L (1:ℝ)) hcomp
  rw [mfderiv_eq_fderiv] at hval
  have hn := coordinate_metric_norm (himg ht') (hg t ht') (deriv η t)
  have hnval : ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) t 1‖ =
      ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm (η t) (deriv η t)‖ :=
    congrArg (fun v : TangentSpace 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) c).symm (η t)) => ‖v‖) hval
  exact (ofReal_norm _).symm.trans (congrArg ENNReal.ofReal (hnval.trans hn.symm))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FiberwiseHomeomorphism
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

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle

namespace WeakMTWTransport
section FiberwiseHomeomorphism
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def fiberwiseHomeomorph (e : OpenPartialHomeomorph (X × Y) (X × Y))
    (he : ∀ z : X × Y, (e z).1 = z.1) (x : X) : OpenPartialHomeomorph Y Y where
  toFun y := (e (x,y)).2
  invFun y := (e.symm (x,y)).2
  source := {y | (x,y) ∈ e.source}
  target := {y | (x,y) ∈ e.target}
  map_source' := by
    intro y hy
    change (x,(e (x,y)).2) ∈ e.target
    have h : (x,(e (x,y)).2) = e (x,y) := Prod.ext (he (x,y)).symm rfl
    rw [h]
    exact e.map_source hy
  map_target' := by
    intro y hy
    have hx : (e.symm (x,y)).1 = x := (he _).symm.trans (congrArg Prod.fst (e.right_inv hy))
    change (x,(e.symm (x,y)).2) ∈ e.source
    have h : (x,(e.symm (x,y)).2) = e.symm (x,y) := Prod.ext hx.symm rfl
    rw [h]
    exact e.map_target hy
  left_inv' := by
    intro y hy
    have h : (x,(e (x,y)).2) = e (x,y) := Prod.ext (he (x,y)).symm rfl
    change (e.symm (x,(e (x,y)).2)).2 = y
    rw [h,e.left_inv hy]
  right_inv' := by
    intro y hy
    have hx : (e.symm (x,y)).1 = x := (he _).symm.trans (congrArg Prod.fst (e.right_inv hy))
    have h : (x,(e.symm (x,y)).2) = e.symm (x,y) := Prod.ext hx.symm rfl
    change (e (x,(e.symm (x,y)).2)).2 = y
    rw [h,e.right_inv hy]
  continuousOn_toFun := (e.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ h => h)).snd
  continuousOn_invFun := (e.symm.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ h => h)).snd
  open_source := e.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)

end FiberwiseHomeomorphism

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fiberwiseHomeomorph_contDiffOn
    {e : OpenPartialHomeomorph (E × F) (E × F)}
    (he : ∀ z : E × F, (e z).1 = z.1) (x : E)
    (hsm : ContDiffOn ℝ ∞ e e.source) :
    ContDiffOn ℝ ∞ (fiberwiseHomeomorph e he x) (fiberwiseHomeomorph e he x).source :=
  (hsm.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ h => h)).snd

lemma fiberwiseHomeomorph_symm_contDiffOn
    {e : OpenPartialHomeomorph (E × F) (E × F)}
    (he : ∀ z : E × F, (e z).1 = z.1) (x : E)
    (hsm : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (fiberwiseHomeomorph e he x).symm (fiberwiseHomeomorph e he x).target :=
  (hsm.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ h => h)).snd

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

lemma first_coordinate_preserving_derivative_invertible {f : E × F → F} {x : E} {v : F}
    (hf : DifferentiableAt ℝ f (x,v))
    (hi : (fderiv ℝ (fun w => f (x,w)) v).IsInvertible) :
    (fderiv ℝ (fun z : E × F => (z.1,f z)) (x,v)).IsInvertible := by
  let L := fderiv ℝ (fun z : E × F => (z.1,f z)) (x,v)
  have hL : L = (ContinuousLinearMap.fst ℝ E F).prod (fderiv ℝ f (x,v)) :=
    ((ContinuousLinearMap.fst ℝ E F).hasFDerivAt.prodMk hf.hasFDerivAt).fderiv
  have hpart : fderiv ℝ (fun w => f (x,w)) v =
      (fderiv ℝ f (x,v)).comp (ContinuousLinearMap.inr ℝ E F) :=
    (hf.hasFDerivAt.comp v ((hasFDerivAt_const x v).prodMk (hasFDerivAt_id v))).fderiv
  have hinj : Function.Injective L := by
    intro a b hab
    have hd : L (a-b) = 0 := by rw [map_sub,hab,sub_self]
    have hx : a.1-b.1 = 0 := by
      have h := congrArg Prod.fst hd
      rw [hL] at h
      exact h
    have hv : a.2-b.2 = 0 := by
      apply hi.injective
      have h := congrArg Prod.snd hd
      have hz : a-b = (0,a.2-b.2) := Prod.ext hx rfl
      change (fderiv ℝ (fun w => f (x,w)) v) (a.2-b.2) =
        (fderiv ℝ (fun w => f (x,w)) v) 0
      rw [map_zero,hpart]
      rw [hL,hz] at h
      exact h
    exact Prod.ext (sub_eq_zero.mp hx) (sub_eq_zero.mp hv)
  have hsur : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsur),rfl⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayScaling
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

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

def tangentScale (c : ℝ) (z : TangentBundle 𝓘(ℝ,E) M) : TangentBundle 𝓘(ℝ,E) M :=
  ⟨z.1,c • z.2⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_LocalNormalChart
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma positive_bilinear_nonneg (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ v : E, v ≠ 0 → 0 < g v v) (v : E) : 0 ≤ g v v := by
  by_cases hv : v = 0
  · simp only [hv,map_zero,le_refl]
  · exact (hg v hv).le

end WeakMTWTransport

open MeasureTheory
open scoped ContDiff ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActionKernel
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

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance actionKernelDualNormedAddCommGroup : NormedAddCommGroup (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
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

variable {M : Type*} [MetricSpace M]

lemma cost_symm (x y : M) : cost x y = cost y x := by
  simp only [cost, dist_comm]

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RadialCalibration
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasDerivAt_regularized_metric_radius (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hsym : ∀ u v, g u v = g v u) {ζ : ℝ → E} {ζ' : E} {t ε τ : ℝ}
    (hζ : HasDerivAt ζ ζ' t) (hpos : 0 < g (ζ t) (ζ t) + ε) :
    HasDerivAt (fun s => τ * Real.sqrt (g (ζ s) (ζ s) + ε))
      (τ * g (ζ t) ζ' / Real.sqrt (g (ζ t) (ζ t) + ε)) t := by
  have h := (((g.hasFDerivAt.comp_hasDerivAt t hζ).clm_apply hζ).add_const ε
    |>.sqrt (ne_of_gt hpos)).const_mul τ
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [Function.comp_apply,hsym ζ' (ζ t)]
  ring

lemma fderiv_partial_homeomorph_right_inverse
    (e : OpenPartialHomeomorph E E) {y : E} (hy : y ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm y)) (hi : DifferentiableAt ℝ e.symm y) :
    (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) = ContinuousLinearMap.id ℝ E := by
  have h := he.hasFDerivAt.comp y hi.hasFDerivAt
  exact h.unique ((hasFDerivAt_id y).congr_of_eventuallyEq (e.eventually_right_inverse hy))

end WeakMTWTransport

end

end OAI
end


