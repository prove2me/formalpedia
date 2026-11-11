-- Prove2me | Definitions.Def_OAIQ232A029
-- name    : OAIQ232A029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:31:30.543609+00:00
-- url     : https://prove2.me/theorems/362d2d6a-df09-43b5-8bfd-2881245b72b0
-- title:
--   Definitions bundle OAIQ232A029 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 22 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Contact_CenterSupport`, `BiholderTransport_Contact_HopfSupports`, `BiholderTransport_Convexity_EnvelopeData`, `BiholderTransport_Convexity_UniformEnvelope`, `BiholderTransport_Coordinates_JoinCoordinates`, `BiholderTransport_Coordinates_NormalCoordinates3`, `BiholderTransport_Coordinates_NormalEikonal`, `BiholderTransport_Coordinates_RadialFactor`, `BiholderTransport_CostGeometry_CrossingUniform`, `BiholderTransport_LinearAlgebra_CompactQuadratic`, `BiholderTransport_LinearAlgebra_CongruenceSpectrum`, `BiholderTransport_LinearAlgebra_JoinCongruence`, `BiholderTransport_LinearAlgebra_JoinOperator`, `BiholderTransport_LinearAlgebra_SpectralContinuity`, `BiholderTransport_Regularity_UniformMiddle`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A026` and `OAIQ232A027` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ232A030`; the statement `OAI.WeakMTWTransport.uniform_join_exp_ordered_comparison`; the proofs of `OAI.WeakMTWTransport.WeakMTW.uniform_extended_spectral_comparison`, `OAI.WeakMTWTransport.uniform_endpoint_middle_singular_comparison`, `OAI.WeakMTWTransport.uniform_family_short_mdifferentiable`, `OAI.WeakMTWTransport.uniform_join_exp_ordered_comparison`, `OAI.WeakMTWTransport.uniform_radial_Schur_background`, `OAI.WeakMTWTransport.uniform_sheared_radial_quadratic_bounds` and `OAI.WeakMTWTransport.uniform_sheared_radial_spectrum`.
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
import Definitions.Def_OAIQ232A026
import Definitions.Def_OAIQ232A027

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CenterSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma scalarCostSupport_lower {u v : M → ℝ} (hu : Continuous u)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hφ : Monotone φ) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    (hc : contactGap v u x (riemannianExp x p)=0) {s : ℝ} (hs : 0 < s) (hs1 : s<1)
    (y : M) : scalarCostSupport φ (v x) x p s y≤φ (v y) := by
  have ha : contactGap (cTransform u) u x (riemannianExp x p)=0 := by rwa [←hdual.2]
  have H := active_split_lower_support hu hp ha hs hs1 y
  rw [←hdual.2] at H
  apply hφ
  rw [neg_sub,sub_div] at H
  linarith only [H]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalCoordinates3
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma movingNormalCost_hasFDerivAt_zero {a : M} {b p : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    HasFDerivAt (movingNormalCost a b p)
      ((innerSL ℝ (-((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p))).comp
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b))) 0 := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  have he : movingNormalCost a b p = (fun h => normalCost x (L p) (L h)) := by
    funext h
    exact movingNormalCost_eq hb p h
  rw [he]
  exact (show HasFDerivAt (normalCost x (L p)) (innerSL ℝ (-L p)) (L 0) by
    simpa only [map_zero] using normalCost_hasFDerivAt_zero hp).comp 0 L.hasFDerivAt

lemma movingNormalCost_second {a : M} {b p : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) (v : Model n) :
    fderiv ℝ (fderiv ℝ (movingNormalCost a b p)) 0 v v =
      hessianValue ((extChartAt 𝓘(ℝ,Model n) a).symm b)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) v) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  have he : movingNormalCost a b p = (fun h => normalCost x (L p) (L h)) := by
    funext h
    exact movingNormalCost_eq hb p h
  rw [he, second_fderiv_comp_linear_zero
    ((normalCost_contDiffAt hp).of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)), hessianValue_eq_normalHessian hp]
  rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_EnvelopeData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {ι : Type*} [Fintype ι]

lemma scaledNormalEnvelope_first {a : M} {s : ℝ} (hs : s ≠ 0)
    {q : EnvelopeData (Model n) ι} (i : ι)
    (hb : q.1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
        (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) ∈
          injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))
    (hi : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) (s • q.1.2 i) ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) (v : Model n) :
    fderiv ℝ (scaledNormalEnvelope a s q i) 0 v =
      q.2.2 * inner ℝ
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
            (q.1.2 i - ∑ j, q.2.1 j • q.1.2 j))
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) v) := by
  have H := ((movingNormalCost_hasFDerivAt_zero hb hp).sub_const
      (movingNormalCost a q.1.1 (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) 0)).sub
    (((movingNormalCost_hasFDerivAt_zero hb hi).sub_const
      (movingNormalCost a q.1.1 (s • q.1.2 i) 0)).const_smul (q.2.2 / s))
  simp only [Pi.sub_def,Pi.smul_def,smul_eq_mul] at H
  unfold scaledNormalEnvelope
  rw [H.fderiv]
  simp only [_root_.sub_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,map_smul,map_sub,inner_neg_left,real_inner_smul_left,inner_sub_left,smul_eq_mul]
  field_simp
  ring

lemma scaledNormalEnvelope_second {a : M} {s : ℝ}
    {q : EnvelopeData (Model n) ι} (i : ι)
    (hb : q.1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
        (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) ∈
          injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))
    (hi : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) (s • q.1.2 i) ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) (v : Model n) :
    fderiv ℝ (fderiv ℝ (scaledNormalEnvelope a s q i)) 0 v v =
      hessianValue ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
            (q.2.2 • ∑ j, q.2.1 j • q.1.2 j))
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) v) -
      q.2.2 / s * hessianValue ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) (s • q.1.2 i))
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) v) := by
  have hl : ContDiffAt ℝ 2 (movingNormalCost a q.1.1 (q.2.2 • ∑ j, q.2.1 j • q.1.2 j)) 0 :=
    ((movingNormalCost_contDiffAt hb hp).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hr : ContDiffAt ℝ 2 (movingNormalCost a q.1.1 (s • q.1.2 i)) 0 :=
    ((movingNormalCost_contDiffAt hb hi).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have H := second_fderiv_scaled_differences hl hr 1 (q.2.2 / s) v
  unfold scaledNormalEnvelope
  simpa only [one_mul,movingNormalCost_second hb hp,movingNormalCost_second hb hi] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_UniformEnvelope
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma scaledNormalEnvelope_mean {ι : Type*} [Fintype ι]
    {a : M} {s : ℝ} (hs : s ≠ 0) {q : EnvelopeData (Model n) ι}
    (hb : q.1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : chartFiberInverse a q.1.1 (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) ∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))
    (hi : ∀ i, chartFiberInverse a q.1.1 (s • q.1.2 i) ∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))
    (hsum : ∑ i, q.2.1 i = 1) (v : Model n) :
    ∑ i, q.2.1 i * fderiv ℝ (scaledNormalEnvelope a s q i) 0 v = 0 := by
  let L := chartFiberInverse a q.1.1
  let r := ∑ j, q.2.1 j • q.1.2 j
  have he : (∑ i, q.2.1 i • L (q.1.2 i-r)) = 0 := by
    simp only [map_sub,smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,hsum,one_smul]
    rw [show (∑ i, q.2.1 i • L (q.1.2 i)) = L r by simp only [r,map_sum,map_smul]]
    exact sub_self _
  calc
    _ = q.2.2 * inner ℝ (∑ i, q.2.1 i • L (q.1.2 i-r)) (L v) := by
      simp only [scaledNormalEnvelope_first hs _ hb hp (hi _),sum_inner,
        real_inner_smul_left,Finset.mul_sum,L,r]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [he,inner_zero_left,mul_zero]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_HopfSupports
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma uniform_cTransform_chart_lower (a : M) :
    ∃ B>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ v : M → ℝ, Continuous v →
        ∀ x∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
          ∃ L : Model n →L[ℝ] ℝ,
            ∀ y∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
              cTransform v ((extChartAt 𝓘(ℝ,Model n) a).symm x)+L (y-x)-B*‖y-x‖^2 ≤
                cTransform v ((extChartAt 𝓘(ℝ,Model n) a).symm y) := by
  obtain ⟨B,hB,r,hr,hrT,hjet⟩ := uniform_half_cost_hessian (n := n) a
  refine ⟨2*B,by positivity,r,hr,hrT,?_⟩
  intro v hv x hx
  let χ := extChartAt 𝓘(ℝ,Model n) a
  obtain ⟨p,hp⟩ := nonempty_activeLogs (n := n) hv (χ.symm x)
  let f := chartCost (n := n) a (riemannianExp (χ.symm x) ((1/2:ℝ) • p))
  refine ⟨(-2:ℝ) • fderiv ℝ f x,?_⟩
  intro y hy
  have hrem := first_order_remainder_le_of_hessian_bound (convex_ball _ _) hB.le
    (fun w hw => (hjet x hx p hp.1 w hw).1)
    (fun w hw => (hjet x hx p hp.1 w hw).2) hx hy
  have hlow := active_split_lower_support hv hp.1 hp.2
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) (χ.symm y)
  change |f y-f x-fderiv ℝ f x (y-x)|≤B*‖y-x‖^2 at hrem
  change -(f y-f x)/(1/2:ℝ) ≤ cTransform v (χ.symm y)-cTransform v (χ.symm x) at hlow
  have hU := (abs_le.mp hrem).2
  simp only [_root_.smul_apply,smul_eq_mul]
  norm_num at hlow
  nlinarith

lemma uniform_hopfLax_chart_upper (a : M) :
    ∃ B>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ t : ℝ, 0<t → ∀ u : M → ℝ, Continuous u →
        ∀ x∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
          ∃ U : Model n →L[ℝ] ℝ,
            ∀ y∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
              hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm y) ≤
                hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm x)+U (y-x)+(B/t)*‖y-x‖^2 := by
  obtain ⟨B,hB,r,hr,hrT,H⟩ := uniform_cTransform_chart_lower (n := n) a
  refine ⟨B,hB,r,hr,hrT,?_⟩
  intro t ht u hu x hx
  obtain ⟨L,hL⟩ := H (fun x => t*u x) (continuous_const.mul hu) x hx
  refine ⟨(-t⁻¹) • L,?_⟩
  intro y hy
  rw [hopfLax_eq_neg_transform hu ht,hopfLax_eq_neg_transform hu ht]
  simp only [_root_.smul_apply,smul_eq_mul]
  have H' := mul_le_mul_of_nonpos_left (hL y hy) (neg_nonpos.mpr (inv_nonneg.mpr ht.le))
  convert H' using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (simp only [div_eq_mul_inv]; ring)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CompactQuadratic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleHessian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma middle_action_contact {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) 0/h+
      normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2) 0/(1-h)=
      cost z.1 (riemannianExp z.1 z.2) := by
  rw [middle_normal_prefix,middle_normal_suffix,riemannianExp_zero]
  have H := splitNormalAction_contact hz hh hh1
  simp only [splitNormalAction,normalCost,riemannianExp_zero] at H
  simpa only [riemannianExp_smul] using H

lemma middleCenteredAction_minimum {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    IsLocalMin (middleCenteredAction z h) 0 := by
  filter_upwards [] with b
  have H := squared_dist_divided_action_le z.1 (riemannianExp (sprayFlow h z).1 b)
    (riemannianExp z.1 z.2) hh hh1
  have H' : cost z.1 (riemannianExp z.1 z.2)≤
      normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) b/h+
      normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2) b/(1-h) := by
    rw [middle_normal_prefix,middle_normal_suffix]
    convert H using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [cost,div_div,mul_comm])
  rw [←middle_action_contact hz hh hh1] at H'
  dsimp only [middleCenteredAction]
  simp only [sub_self,mul_zero,neg_mul,sub_neg_eq_add,div_eq_mul_inv] at H' ⊢
  nlinarith

lemma middleHessian_one_nonneg {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1)
    (v : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    0 ≤ middleHessian z h 1 v v := by
  rw [←middleCenteredAction_hessian hz hh hh1]
  exact localMin_hessian_nonneg (middleCenteredAction_contDiffAt hz hh hh1)
    (middleCenteredAction_minimum hz hh hh1) v

end MiddleHessian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_JoinCoordinates
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
section JoinCoordinates
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma middle_action_in_join_coordinates {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {h : ℝ} (hp : p∈minimizingVectors x) (hh : 0<h) (hh1 : h<1)
    {q : TangentSpace 𝓘(ℝ,Model n) x →
        TangentSpace 𝓘(ℝ,Model n) (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1}
    (hqr : ∀ᶠ a in 𝓝 p, riemannianExp _ (q a)=riemannianExp x (h • a)) :
    (middleCenteredAction (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) h ∘ q) =ᶠ[𝓝 p]
      (fun a => diagonalSplitAction x h (p,a)-cost x (riemannianExp x p)) := by
  filter_upwards [hqr] with a ha
  have hc := middle_action_contact (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hp hh hh1
  dsimp only [Function.comp_apply,middleCenteredAction]
  rw [middle_normal_prefix,middle_normal_suffix,ha]
  dsimp only [diagonalSplitAction,splitNormalAction,normalCost]
  simp only [normalCost,riemannianExp_zero,div_eq_mul_inv] at hc ⊢
  nlinarith only [hc]

end JoinCoordinates
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalEikonal
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section NormalEikonal
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_normal_eikonal_log {x y : M} {r : TangentSpace 𝓘(ℝ,Model n) y}
    (hr : r∈injectivityDomain y) (he : riemannianExp y r=x) :
    ∃ q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y,
      q 0=r ∧ ContDiffAt ℝ ∞ q 0 ∧
      (∀ᶠ a in 𝓝 0, riemannianExp y (q a)=riemannianExp x a) ∧
      (∀ᶠ a in 𝓝 0,
        doubleNormalCost x y (a,0)=‖q a‖^2/2 ∧
        fderiv ℝ (fun b => doubleNormalCost x y (a,b)) 0=innerSL ℝ (-q a)) := by
  let : Nonempty M := ⟨x⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  obtain ⟨κ,hκ0,hκ,hκright⟩ := exists_normal_local_inverse_at hr
  rw [he] at hκ0 hκ hκright
  let q : X → Y := κ ∘ riemannianExp (n := n) x
  have hq0 : q 0=r := by simp only [q,Function.comp_apply,riemannianExp_zero,hκ0]
  have hq : ContDiffAt ℝ ∞ q 0 := by
    apply ContMDiffAt.contDiffAt
    exact (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Y) ∞ κ (riemannianExp x (0:X)) from
      by simpa only [riemannianExp_zero] using hκ).comp 0 (contMDiff_riemannianExp_fiber x 0)
  have hqright : ∀ᶠ a in 𝓝 0, riemannianExp y (q a)=riemannianExp x a :=
    (show ContinuousAt (riemannianExp (n := n) x) (0:X) from
      (continuous_riemannianExp x).continuousAt).eventually
        (by simpa only [riemannianExp_zero] using hκright)
  have hqI : ∀ᶠ a in 𝓝 0, q a∈injectivityDomain y :=
    hq.continuousAt.preimage_mem_nhds ((isOpen_injectivityDomain y).mem_nhds (hq0.symm ▸ hr))
  refine ⟨q,hq0,hq,hqright,?_⟩
  filter_upwards [hqright,hqI] with a ha haI
  change riemannianExp y (q a)=riemannianExp x a at ha
  change q a∈injectivityDomain y at haI
  constructor
  · have hm := injectivityDomain_subset_minimizingVectors y haI
    change dist y (riemannianExp y (q a))=‖q a‖ at hm
    simp only [doubleNormalCost,riemannianExp_zero,cost,←ha,dist_comm _ y,hm]
  · have heq : (fun b => doubleNormalCost x y (a,b))=normalCost y (q a) := by
      funext b
      dsimp [doubleNormalCost,normalCost,cost]
      rw [←ha,dist_comm]
    rw [heq]
    exact (normalCost_hasFDerivAt_zero haI).fderiv

end NormalEikonal
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_RadialFactor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section RadialFactor
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma normalHessian_radial_derivative_factor {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ L : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
        TangentSpace 𝓘(ℝ,Model n) (reverseRay (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      Function.Injective L ∧
      (∀ v, ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) (reverseRay (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
        𝓘(ℝ,Model n) (riemannianExp (reverseRay (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
        (reverseRay (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 (L v)‖=‖v‖) ∧ ∀ v,
      HasDerivAt (fun s : ℝ => normalHessian x (s • p) v v)
        (normalHessian x p v v-‖L v‖^2) 1 := by
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let y := (reverseRay z).1
  let r := (reverseRay z).2
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  have hr : r∈injectivityDomain y := reverseRay_injectivityDomain hp
  have he : riemannianExp y r=x := reverseRay_endpoint z
  obtain ⟨q,hq0,hq,hqr,hqeq⟩ := exists_normal_eikonal_log hr he
  let L := fderiv ℝ q 0
  refine ⟨L,normal_log_fderiv_injective (hq.differentiableAt (by simp)) hqr,?_,?_⟩
  · intro v
    have H := normal_log_fderiv_exp_norm (hq.differentiableAt (by simp)) hqr v
    rw [hq0] at H
    exact H
  intro v
  let B := doubleNormalCost (n := n) x y
  have hB : ContDiffAt ℝ 3 B (0,0) := (doubleNormalCost_contDiffAt hr he).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hq2 : ContDiffAt ℝ 2 q 0 := hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heik : (fun a : X => B (a,0))=ᶠ[𝓝 0] fun a => ‖-q a‖^2/2 := by
    filter_upwards [hqeq] with a ha
    simpa only [norm_neg] using ha.1
  have hgrad : ∀ᶠ a : X in 𝓝 0, ∀ w : Y,
      fderiv ℝ B (a,0) (0,w)=inner ℝ (-q a) w := by
    have hBa : ∀ᶠ a : X in 𝓝 0, ContDiffAt ℝ 3 B (a,0) :=
      (continuousAt_id.prodMk continuousAt_const).eventually (hB.eventually (by norm_num))
    filter_upwards [hqeq,hBa] with a ha hBa
    intro w
    have hd := (hBa.differentiableAt (by norm_num)).hasFDerivAt.comp 0
      ((hasFDerivAt_const a (0:Y)).prodMk (hasFDerivAt_id 0))
    have hv := congrArg (fun D : Y →L[ℝ] ℝ => D w) hd.fderiv
    change fderiv ℝ (fun b => doubleNormalCost x y (a,b)) 0 w=
      fderiv ℝ B (a,0) (0,w) at hv
    rw [ha.2] at hv
    exact hv.symm
  have heik3 := eikonal_third_derivative hB hq2.neg heik hgrad (v := v)
  have hS := second_derivative_source_slice (hB.of_le (by norm_num)) v v
  have hBzero : (fun a : X => B (a,0))=normalCost x p := by
    funext a
    simp only [B,doubleNormalCost,normalCost,riemannianExp_zero]
    rw [riemannianExp_eq_sprayFlow x p]
    rfl
  rw [hBzero] at hS
  change normalHessian x p v v=_ at hS
  have hneg : fderiv ℝ (fun a : X => -q a) 0 = -L := by
    exact fderiv_fun_neg
  rw [hq0,hneg] at heik3
  change fderiv ℝ (fderiv ℝ B) (0,0) (v,0) (v,0)=
    ‖-(L v)‖^2+fderiv ℝ (fderiv ℝ (fderiv ℝ B)) (0,0) (0,-r) (v,0) (v,0) at heik3
  rw [norm_neg,←hS] at heik3
  have hline := hasDerivAt_source_hessian_line (a := (0:X)) (b := (0:Y))
    (w := -r) (t := 1) (v := v) hB
  have hf : (fun s : ℝ => fderiv ℝ (fderiv ℝ
      (fun a : X => B (a,(0:Y)+(s-1) • (-r)))) 0 v v)=
        (fun s : ℝ => normalHessian x (s • p) v v) := by
    funext s
    congr 3
    funext a
    dsimp [B,doubleNormalCost,normalCost]
    have hs : (0:Y)+(s-1) • (-r)=(1-s) • r := by
      simp only [zero_add,smul_neg,←neg_smul]
      congr 1
      ring
    rw [hs,exp_reverseRay_line z s]
    rfl
  rw [hf] at hline
  convert hline using 1
  all_goals try with_reducible_and_instances rfl
  linarith

end RadialFactor
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_CrossingUniform
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
section CrossingUniform
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma compact_bundle_radialCrossingValue_bounds
    {K : Set (TangentBundle 𝓘(ℝ,Model n) M)} (hK : IsCompact K)
    (hI : ∀ z∈K, z.2∈injectivityDomain z.1) :
    ∃ c C : ℝ, 0 < c ∧ 0<C ∧ ∀ z∈K, ∀ v : TangentSpace 𝓘(ℝ,Model n) z.1,
      c*‖v‖^2 ≤ radialCrossingValue z.1 z.2 v ∧
      radialCrossingValue z.1 z.2 v≤C*‖v‖^2 := by
  have hR : IsCompact (reverseRay '' K) := hK.image continuous_reverseRay
  have hRI : ∀ r∈reverseRay '' K, r.2∈injectivityDomain r.1 := by
    rintro r ⟨z,hz,rfl⟩
    exact reverseRay_injectivityDomain (hI z hz)
  obtain ⟨l,u,hl,hu,H⟩ := compact_exp_differential_bounds hR hRI
  refine ⟨(u^2)⁻¹,(l^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hu),inv_pos.mpr (sq_pos_of_pos hl),?_⟩
  intro z hz v
  obtain ⟨L,hL,hN,hD⟩ := normalHessian_radial_derivative_factor (hI z hz)
  have heq : radialCrossingValue z.1 z.2 v=‖L v‖^2 := by
    have hd := (hD v).unique (normalHessian_radial_derivative_value (hI z hz) v)
    linarith
  have hb := H (reverseRay z) (mem_image_of_mem _ hz) (L v)
  rw [hN] at hb
  rw [heq]
  constructor
  · have hs : ‖v‖^2≤u^2*‖L v‖^2 := by
      nlinarith [sq_le_sq₀ (norm_nonneg v) (mul_nonneg hu.le (norm_nonneg (L v))) |>.mpr hb.2]
    rw [inv_mul_le_iff₀ (sq_pos_of_pos hu)]
    exact hs
  · have hs : l^2*‖L v‖^2≤‖v‖^2 := by
      nlinarith [sq_le_sq₀ (mul_nonneg hl.le (norm_nonneg (L v))) (norm_nonneg v) |>.mpr hb.1]
    rw [le_inv_mul_iff₀ (sq_pos_of_pos hl)]
    exact hs

end CrossingUniform
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_JoinCongruence
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
section JoinCongruence
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma split_join_hessian_congruence {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    ∃ P : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
        TangentSpace 𝓘(ℝ,Model n) (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      Function.Injective P ∧ ∀ a,
      fderiv ℝ (fderiv ℝ (diagonalSplitAction x h)) (p,p) (0,a) (0,a)=
        middleHessian (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) h 1 (P a) (P a) := by
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  have hleft := contracted_minimizer_mem_injectivityDomain hp hh hh1
  obtain ⟨q,hqp,hq,hqinj,hqr⟩ := exists_join_normal_coordinates hh.ne' hleft
  have hf := middleCenteredAction_contDiffAt (z := z) hp hh hh1
  have hf' : ContDiffAt ℝ 2 (middleCenteredAction z h) (q p) := by rwa [hqp]
  have hz : fderiv ℝ (middleCenteredAction z h) (q p)=0 := by
    rw [hqp]
    exact (middleCenteredAction_minimum (z := z) hp hh hh1).fderiv_eq_zero
  have hF : ContDiffAt ℝ 2 (diagonalSplitAction x h) (p,p) :=
    (diagonalSplitAction_contDiffAt hleft (proper_suffix_in_injectivityDomain
      (z := z) hp hh hh1 le_rfl)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := middle_action_in_join_coordinates hp hh hh1 hqr
  have heD := he.fderiv (𝕜 := ℝ)
  have heDD := heD.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (fderiv ℝ (middleCenteredAction z h ∘ q)) p =
    fderiv ℝ (fderiv ℝ (fun a => diagonalSplitAction x h (p,a)-cost x (riemannianExp x p))) p at heDD
  have hsub : fderiv ℝ (fun a => diagonalSplitAction x h (p,a)-cost x (riemannianExp x p))=
      fderiv ℝ (fun a => diagonalSplitAction x h (p,a)) := by
    funext a; exact fderiv_sub_const _
  rw [hsub] at heDD
  refine ⟨fderiv ℝ q p,hqinj,?_⟩
  intro a
  have H := second_fderiv_comp_at_critical hf' (hq.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hz a a
  rw [heDD,hqp,second_derivative_target_slice hF] at H
  exact H.trans (middleCenteredAction_hessian (z := z) hp hh hh1 _)

end JoinCongruence
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_JoinOperator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section JoinOperator
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma splitJoinHessianOperator_positive {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    (splitJoinHessianOperator x t p).toLinearMap.IsPositive := by
  have hleft := contracted_minimizer_mem_injectivityDomain hp ht ht1
  have hright := proper_suffix_in_injectivityDomain
    (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hp ht ht1 le_rfl
  have hB := diagonalSplitAction_contDiffAt hleft hright
  refine ⟨?_,?_⟩
  · intro a k
    change inner ℝ (splitJoinHessianOperator x t p a) k=
      inner ℝ a (splitJoinHessianOperator x t p k)
    rw [real_inner_comm (splitJoinHessianOperator x t p k) a,
      inner_splitJoinHessianOperator,inner_splitJoinHessianOperator]
    exact (hB.isSymmSndFDerivAt (by simp)).eq _ _
  · intro a
    change 0 ≤ inner ℝ (splitJoinHessianOperator x t p a) a
    rw [inner_splitJoinHessianOperator]
    obtain ⟨P,hP,HP⟩ := split_join_hessian_congruence hp ht ht1
    rw [HP]
    exact middleHessian_one_nonneg hp ht ht1 _

end JoinOperator
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_UniformMiddle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section UniformMiddle
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniform_suffix_crossing_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0<C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → ∀ s∈Icc (1/4:ℝ) (3/4), ∀ v,
      c*‖v‖^2≤ radialCrossingValue (sprayFlow (1/4) z).1
        (s • (sprayFlow (1/4) z).2) v/s^2 ∧
      radialCrossingValue (sprayFlow (1/4) z).1
        (s • (sprayFlow (1/4) z).2) v/s^2≤ C*‖v‖^2 := by
  let G := {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈minimizingVectors z.1}
  let F : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => tangentScale q.1 (sprayFlow (1/4) q.2)
  have hF : Continuous F := contMDiff_tangentScale.continuous.comp
    (continuous_fst.prodMk (contMDiff_sprayFlow.continuous.comp
      (continuous_const.prodMk continuous_snd)))
  have hK : IsCompact (F '' (Icc (1/4:ℝ) (3/4) ×ˢ G)) :=
    (isCompact_Icc.prod (isCompact_total_minimizingVectors (n := n) (M := M))).image hF
  have hI : ∀ z∈F '' (Icc (1/4:ℝ) (3/4) ×ˢ G), z.2∈injectivityDomain z.1 := by
    rintro _ ⟨⟨s,z⟩,hsz,rfl⟩
    have H := proper_suffix_in_injectivityDomain hsz.2 (show (0:ℝ)<1/4 by norm_num)
      (show (1/4:ℝ) < s+1/4 by linarith [hsz.1.1])
      (show s+1/4≤(1:ℝ) by linarith [hsz.1.2])
    change s • (sprayFlow (1/4) z).2∈injectivityDomain (sprayFlow (1/4) z).1
    simpa only [add_sub_cancel_right] using H
  obtain ⟨c,C,hc,hC,H⟩ := compact_bundle_radialCrossingValue_bounds hK hI
  refine ⟨c,16*C,hc,mul_pos (by norm_num) hC,?_⟩
  intro z hz s hs v
  have hb := H (F (s,z)) (mem_image_of_mem _ ⟨hs,hz⟩) v
  change c*‖v‖^2≤ radialCrossingValue (sprayFlow (1/4) z).1
      (s • (sprayFlow (1/4) z).2) v ∧
    radialCrossingValue (sprayFlow (1/4) z).1
      (s • (sprayFlow (1/4) z).2) v≤ C*‖v‖^2 at hb
  have hp : 0 < s := by linarith [hs.1]
  have hslo : (1/16:ℝ)≤ s^2 := by nlinarith [hs.1]
  have hshi : s^2≤(1:ℝ) := by nlinarith [hs.2]
  constructor
  · rw [le_div_iff₀ (sq_pos_of_pos hp)]
    exact (mul_le_of_le_one_right (mul_nonneg hc.le (sq_nonneg ‖v‖)) hshi).trans hb.1
  · rw [div_le_iff₀ (sq_pos_of_pos hp)]
    have hmul := mul_le_mul_of_nonneg_left hslo (mul_nonneg hC.le (sq_nonneg ‖v‖))
    nlinarith [hb.2]

lemma uniform_middleHessian_crossing :
    ∃ c C : ℝ, 0 < c ∧ 0<C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → ∀ δ : ℝ, 0≤δ → δ≤1/2 → ∀ v,
      c*δ*‖v‖^2≤ middleHessian z (1/4) (1-δ) v v-middleHessian z (1/4) 1 v v ∧
      middleHessian z (1/4) (1-δ) v v-middleHessian z (1/4) 1 v v≤ C*δ*‖v‖^2 := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_suffix_crossing_bounds (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro z hz δ hd hdhalf v
  let p := (sprayFlow (1/4) z).2
  let x := (sprayFlow (1/4) z).1
  let Q : ℝ → ℝ := fun r => radialCrossingValue x (r • p) v/r^2
  let f : ℝ → ℝ := fun r => normalHessian x (r • p) v v/r
  have hI (r) (hr : r∈Icc (1/4:ℝ) (3/4)) : r • p∈injectivityDomain x := by
    have HH := proper_suffix_in_injectivityDomain hz (show (0:ℝ)<1/4 by norm_num)
      (show (1/4:ℝ) < r+1/4 by linarith [hr.1])
      (show r+1/4≤(1:ℝ) by linarith [hr.2])
    simpa only [add_sub_cancel_right] using HH
  have hder (r) (hr : r∈Icc (1/4:ℝ) (3/4)) : HasDerivAt f (-Q r) r :=
    divided_normalHessian_derivative_value (by linarith [hr.1]) (hI r hr) v
  have hf : ContinuousOn f (Icc (1/4:ℝ) (3/4)) :=
    fun r hr => (hder r hr).continuousAt.continuousWithinAt
  have hdf : DifferentiableOn ℝ f (interior (Icc (1/4:ℝ) (3/4))) :=
    fun r hr => (hder r (interior_subset hr)).differentiableAt.differentiableWithinAt
  have hs : 1-δ-1/4∈Icc (1/4:ℝ) (3/4) := ⟨by linarith,by linarith⟩
  have ht : (3/4:ℝ)∈Icc (1/4:ℝ) (3/4) := ⟨by norm_num,le_rfl⟩
  have hst : 1-δ-1/4≤(3/4:ℝ) := by linarith
  have hlo := (convex_Icc (1/4:ℝ) (3/4)).image_sub_le_mul_sub_of_deriv_le hf hdf
    (C := -(c*‖v‖^2)) (fun r hr => by
      rw [(hder r (interior_subset hr)).deriv]
      exact neg_le_neg (H z hz r (interior_subset hr) v).1)
    (1-δ-1/4) hs (3/4) ht hst
  have hhi := (convex_Icc (1/4:ℝ) (3/4)).mul_sub_le_image_sub_of_le_deriv hf hdf
    (C := -(C*‖v‖^2)) (fun r hr => by
      rw [(hder r (interior_subset hr)).deriv]
      exact neg_le_neg (H z hz r (interior_subset hr) v).2)
    (1-δ-1/4) hs (3/4) ht hst
  rw [middleHessian_apply,middleHessian_apply]
  change _≤_ + f (1-δ-1/4)-(_+f (1-1/4)) ∧
    _+f (1-δ-1/4)-(_+f (1-1/4))≤_
  norm_num only [show (1:ℝ)-1/4=3/4 by norm_num]
  constructor <;> nlinarith

end UniformMiddle
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SpectralContinuity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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
section MiddleSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_5
lemma middleHessianOperator_symmetric {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2 ∈ minimizingVectors z.1) {h T : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hT : h < T) (hT1 : T ≤ 1) :
    (middleHessianOperator z h T).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (middleHessianOperator z h T v) w = inner ℝ v (middleHessianOperator z h T w)
  rw [real_inner_comm (middleHessianOperator z h T w) v,inner_middleHessianOperator,inner_middleHessianOperator,
    middleHessian_apply,middleHessian_apply,
    normalHessian_symm (proper_prefix_reverse_in_injectivityDomain hz hh hh1),
    normalHessian_symm (proper_suffix_in_injectivityDomain hz hh hT hT1)]

lemma shortened_middle_operator_positive {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2 ∈ minimizingVectors z.1) {δ : ℝ} (hd : 0 ≤ δ) (hdhalf : δ ≤ 1/2) :
    (middleHessianOperator z (1/4) (1-δ)).toLinearMap.IsPositive := by
  refine ⟨middleHessianOperator_symmetric hz (by norm_num) (by norm_num)
    (by linarith) (by linarith),?_⟩
  intro v
  change 0 ≤ inner ℝ (middleHessianOperator z (1/4) (1-δ) v) v
  rw [inner_middleHessianOperator]
  obtain ⟨c,C,hc,hC,H⟩ := uniform_middleHessian_crossing (n := n) (M := M)
  have H1 := (H z hz δ hd hdhalf v).1
  have H0 := middleHessian_one_nonneg hz (show (0:ℝ) < 1/4 by norm_num)
    (show (1/4:ℝ) < 1 by norm_num) v
  have Hpos := mul_nonneg (mul_nonneg hc.le hd) (sq_nonneg ‖v‖)
  linarith

end MiddleSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CongruenceSpectrum
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
section EndpointMiddle
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_7
lemma middleHessianOperator_positive_one {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2 ∈ minimizingVectors z.1) {h : ℝ} (hh : 0 < h) (hh1 : h < 1) :
    (middleHessianOperator z h 1).toLinearMap.IsPositive := by
  refine ⟨middleHessianOperator_symmetric hz hh hh1 hh1 le_rfl,?_⟩
  intro v
  change 0 ≤ inner ℝ (middleHessianOperator z h 1 v) v
  rw [inner_middleHessianOperator]
  exact middleHessian_one_nonneg hz hh hh1 v

end EndpointMiddle
end WeakMTWTransport

end

end

end

end OAI
end


