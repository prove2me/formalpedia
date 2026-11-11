-- Prove2me | Definitions.Def_OAIQ232A031
-- name    : OAIQ232A031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:40:51.288251+00:00
-- url     : https://prove2.me/theorems/c4e3a96a-c451-44c3-8c98-86179f50d440
-- title:
--   Definitions bundle OAIQ232A031 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 5 definitions and 9 theorems. The definitions and types are `OAI.WeakMTWTransport.MaximumDiagonal.center_sequence`, `OAI.WeakMTWTransport.MaximumDiagonal.comp`, `OAI.WeakMTWTransport.MaximumJensenFamily.OuterSampleGood`, `OAI.WeakMTWTransport.MaximumJensenFamily.comp`, `OAI.WeakMTWTransport.WeakMTW.center_sequence_of_graph`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`BiholderTransport_Calculus_HopfGradient`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Calculus/HopfGradient.lean), [`BiholderTransport_Contact_CenterSupportFamily`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Contact/CenterSupportFamily.lean), [`BiholderTransport_Contact_CoordinateSupportGradient`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Contact/CoordinateSupportGradient.lean), [`BiholderTransport_Convexity_JensenAtCenter`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/JensenAtCenter.lean), [`BiholderTransport_Convexity_ParametricShortLowerEnvelope`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Convexity/ParametricShortLowerEnvelope.lean), [`BiholderTransport_Coordinates_PoleCoordinates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Coordinates/PoleCoordinates.lean), [`BiholderTransport_Regularity_ActualCenterRay`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/ActualCenterRay.lean), [`BiholderTransport_Regularity_MaximumCenterSequence`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumCenterSequence.lean), [`BiholderTransport_Regularity_MaximumOuterSamples`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumOuterSamples.lean), [`BiholderTransport_Regularity_MaximumReindex`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/MaximumReindex.lean), [`BiholderTransport_Regularity_SampleCenterFamilies`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/BiholderTransport/Regularity/SampleCenterFamilies.lean).
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundle `OAIQ232A030` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.WeakMTWTransport.WeakMTW.exists_maximum_true_outer`; the proofs of `OAI.WeakMTWTransport.MaximumDiagonal.scalar_jets`, `OAI.WeakMTWTransport.MaximumJensenFamily.center_regular`, `OAI.WeakMTWTransport.MaximumJensenFamily.selected_pole_compact`, `OAI.WeakMTWTransport.MaximumRow.jensen_first_limit`, `OAI.WeakMTWTransport.WeakMTW.actualPole_kernel`, `OAI.WeakMTWTransport.WeakMTW.actualPole_taylor`, `OAI.WeakMTWTransport.WeakMTW.actual_sample_pole_matrix`, `OAI.WeakMTWTransport.WeakMTW.exists_maximum_simultaneous`, `OAI.WeakMTWTransport.WeakMTW.exists_maximum_true_outer`, `OAI.WeakMTWTransport.WeakMTW.family_comparison_local_data`, `OAI.WeakMTWTransport.WeakMTW.jensen_undo_short`, `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound`, `OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg`, `OAI.WeakMTWTransport.exists_maximum_center_gain` and `OAI.WeakMTWTransport.exists_maximum_true_center`.
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
import Definitions.Def_OAIQ232A030

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_HopfGradient
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

lemma WeakMTW.hopfLax_backward_flow (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : subgradientGraph (n := n) (cTransform v)) :
    sprayFlow (-t)
      (⟨graphProjection (cTransform v) t q,
        riemannianGradient (hopfLax t (cTransform v)) (graphProjection (cTransform v) t q)⟩ :
          TangentBundle 𝓘(ℝ,Model n) M) = q.1 := by
  have hdual : IsCostDualPair (cTransform v) (cTransform (cTransform v)) :=
    ⟨(cTransform_triple hv).symm,rfl⟩
  have hu := continuous_cTransform hv
  have hp := (hmtw.global_support hv q.2).1
  have hbase : graphProjection (cTransform v) t q=(sprayFlow t q.1).1 :=
    riemannianExp_smul _ _ _
  have hd := hmtw.mdifferentiable_hopfLax hu (continuous_cTransform hu) hdual ht ht1
  have hval := hmtw.hopfLax_graph_value hv ht ht1 q
  rw [hbase] at hval
  have hder := hopfLax_derivative_of_minimizer hu hp ht ht1.le hval (hd _)
  rw [hbase,riemannianGradient_eq_of_derivative hder]
  change sprayFlow (-t) (sprayFlow t q.1)=q.1
  rw [←sprayFlow_add,neg_add_cancel,sprayFlow_zero]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_PoleCoordinates
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

lemma WeakMTW.coordinateBackward_eq_pole (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (hdual : IsCostDualPair u v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) {a : M} {z : Model n}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    coordinateBackward a (t,z,
      fderiv ℝ (fun w => hopfLax t u ((extChartAt 𝓘(ℝ,Model n) a).symm w)) z) =
      hopfPole (n := n) t u ((extChartAt 𝓘(ℝ,Model n) a).symm z) := by
  have H := coordinateBackward_of_derivative
    (⟨(extChartAt 𝓘(ℝ,Model n) a).symm z,
      riemannianGradient (n := n) (hopfLax t u) ((extChartAt 𝓘(ℝ,Model n) a).symm z)⟩ :
      TangentBundle 𝓘(ℝ,Model n) M)
    ((extChartAt 𝓘(ℝ,Model n) a).map_target hz)
    (hasMFDerivAt_riemannianGradient (hmtw.mdifferentiable_hopfLax hu hv hdual ht ht1 _)) t
  simpa only [hopfPole, (extChartAt 𝓘(ℝ,Model n) a).right_inv hz] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_ParametricShortLowerEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Manifold Bundle Asymptotics
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.modified_short_contact (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} {y : M} {l τ : ℝ}
    (hφ : HasDerivAt φ l (v y)) (hl : 0<l) (hl1 : l<1) (hτ : τ≠0)
    {r : TangentSpace 𝓘(ℝ,Model n) y} (hr : τ • r∈injectivityDomain y)
    (hmin : IsLocalMin (fun a => φ (v a)+cost a (riemannianExp y (τ • r))/τ) y) :
    l⁻¹ • r∈minimizingVectors y ∧
      contactGap v u y (riemannianExp y (l⁻¹ • r))=0 ∧ r∈injectivityDomain y := by
  have hsub := scalar_normalSubdifferential_inv hv hφ hl
    (local_min_divided_cost_subgradient hτ hr hmin)
  have H := hmtw.subgradient_dual_contact hv.continuous hu ⟨hdual.2,hdual.1⟩ hsub
  refine ⟨H.1,H.2,?_⟩
  have HI := contracted_minimizer_mem_injectivityDomain H.1 hl hl1
  simpa only [smul_smul,mul_inv_cancel₀ hl.ne',one_smul] using HI

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CoordinateSupportGradient
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.exists_actual_center_support (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hmono : Monotone φ)
    {a : M} {b : Model n} (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {l τ : ℝ} (hφ : HasDerivAt φ l (v ((extChartAt 𝓘(ℝ,Model n) a).symm b)))
    (hl : 0<l) (hl1 : l<1) (hτ : τ≠0)
    {r : TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm b)}
    (hr : τ • r∈injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hmin : IsLocalMin (fun y => φ (v y)+
      cost y (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) (τ • r))/τ)
        ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    ∃ p : Model n,
      let y := (extChartAt 𝓘(ℝ,Model n) a).symm b
      let s := (1+l)/2
      let ψ := fun w => coordinateScalarSupport a φ ((((v y),s),(b,p)),w)
      0 < s ∧ s<1 ∧
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ y p=
        l⁻¹ • r ∧
      l⁻¹ • r∈minimizingVectors y ∧
      contactGap v u y (movingNormal a (b,p))=0 ∧
      (∀ w,ψ w≤φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm w))) ∧
      ψ b=φ (v y) ∧
      shortForward a ψ (τ,b)=extChartAt 𝓘(ℝ,Model n) a (riemannianExp y (τ • r)) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let y := χ.symm b
  let T := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  let p := T.continuousLinearMapAt ℝ y (l⁻¹ • r)
  have hy : y∈(chartAt (Model n) a).source := by
    simpa only [y,χ,extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hb
  have hp : T.symmL ℝ y p=l⁻¹ • r := Trivialization.symmL_continuousLinearMapAt _ hy _
  obtain ⟨hpm,hpc,hrreg⟩ := hmtw.modified_short_contact hu hv hdual hφ hl hl1 hτ hr hmin
  have hs : 0<(1+l)/2 := by linarith
  have hs1 : (1+l)/2<1 := by linarith
  have hpr : ((1+l)/2) • T.symmL ℝ y p∈injectivityDomain y := by
    rw [hp]
    exact contracted_minimizer_mem_injectivityDomain hpm hs hs1
  refine ⟨p,hs,hs1,hp,hpm,?_,?_,?_,?_⟩
  · rw [movingNormal_eq hb]
    change contactGap v u y (riemannianExp y (T.symmL ℝ y p))=0
    rw [hp]
    exact hpc
  · intro w
    dsimp only
    rw [coordinateScalarSupport_eq hb]
    change scalarCostSupport φ (v y) y (T.symmL ℝ y p) ((1+l)/2) (χ.symm w)≤φ (v (χ.symm w))
    rw [hp]
    exact scalarCostSupport_lower hu hdual hmono hpm hpc hs hs1 _
  · exact coordinateScalarSupport_self _ _ _ _ _ _
  · rw [coordinateScalarSupport_shortForward hb hs.ne' hpr hφ,movingNormal_eq hb,map_smul,hp,
      smul_smul]
    have he : τ*l*l⁻¹=τ := by field_simp
    rw [he]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ActualCenterRay
attribute [-simp] _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.exists_center_ray_of_minimizer (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hφc : Continuous φ)
    {y z : M} {l τ : ℝ} (hφ : HasDerivAt φ l (v y)) (hl : 0<l) (hl1 : l<1)
    (hτ : 0<τ) (hτ1 : τ<1)
    (hval : hopfLax τ (fun a=>φ (v a)) z=φ (v y)+cost y z/τ) :
    ∃ r : TangentSpace 𝓘(ℝ,Model n) y,
      τ • r∈injectivityDomain y ∧ riemannianExp y (τ • r)=z ∧
      l⁻¹ • r∈minimizingVectors y ∧
      contactGap v u y (riemannianExp y (l⁻¹ • r))=0 ∧ r∈injectivityDomain y := by
  obtain ⟨q,hq,hqz⟩ := exists_minimizing_vector (n := n) y z
  let r := τ⁻¹ • q
  have hsub : r∈normalSubdifferential (fun a=>φ (v a)) y := by
    apply global_min_divided_cost_subgradient hq hτ
    intro a
    rw [hqz,←hval]
    exact hopfLax_le (hφc.comp hv.continuous) τ z a
  have H := hmtw.subgradient_dual_contact hv.continuous hu ⟨hdual.2,hdual.1⟩
    (scalar_normalSubdifferential_inv hv hφ hl hsub)
  have hr : r∈injectivityDomain y := by
    have HR := contracted_minimizer_mem_injectivityDomain H.1 hl hl1
    simpa only [smul_smul,mul_inv_cancel₀ hl.ne',one_smul] using HR
  refine ⟨r,contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors y hr) hτ hτ1,?_,H.1,H.2,hr⟩
  simpa only [r,smul_smul,mul_inv_cancel₀ hτ.ne',one_smul] using hqz

lemma WeakMTW.exists_center_coordinate_support (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hφc : Continuous φ) (hmono : Monotone φ)
    {a : M} {b : Model n} (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {z : M} {l τ : ℝ} (hφ : HasDerivAt φ l (v ((extChartAt 𝓘(ℝ,Model n) a).symm b)))
    (hl : 0<l) (hl1 : l<1) (hτ : 0<τ) (hτ1 : τ<1)
    (hval : hopfLax τ (fun y=>φ (v y)) z=φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm b))+
      cost ((extChartAt 𝓘(ℝ,Model n) a).symm b) z/τ) :
    ∃ p : Model n,
      let y := (extChartAt 𝓘(ℝ,Model n) a).symm b
      let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ y
      let ψ := fun w=>coordinateScalarSupport a φ (((v y,(1+l)/2),(b,p)),w)
      A p∈minimizingVectors y ∧ contactGap v u y (movingNormal a (b,p))=0 ∧
      l • A p∈injectivityDomain y ∧ riemannianExp y ((τ*l) • A p)=z ∧
      (∀ w,ψ w≤φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm w))) ∧
      ψ b=φ (v y) ∧ shortForward a ψ (τ,b)=extChartAt 𝓘(ℝ,Model n) a z := by
  obtain ⟨r,hr,hrz,hpm,hpc,hrreg⟩ :=
    hmtw.exists_center_ray_of_minimizer hu hv hdual hφc hφ hl hl1 hτ hτ1 hval
  have hmin : IsLocalMin (fun y=>φ (v y)+cost y
      (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) (τ • r))/τ)
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    rw [hrz,←hval]
    exact hopfLax_le (hφc.comp hv.continuous) τ z y
  obtain ⟨p,hs,hs1,hp,hpm,hpc,hbelow,htouch,hZ⟩ :=
    hmtw.exists_actual_center_support hu hv hdual hmono hb hφ hl hl1 hτ.ne' hr hmin
  refine ⟨p,?_,hpc,?_,?_,hbelow,htouch,?_⟩
  · rwa [hp]
  · simpa only [hp,smul_smul,mul_inv_cancel₀ hl.ne',one_smul] using hrreg
  · rw [hp,smul_smul,show τ*l*l⁻¹=τ by field_simp]
    exact hrz
  · rwa [hrz] at hZ

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_CenterSupportFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.actual_center_row (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {Lv : ℝ≥0} (hv : LipschitzWith Lv v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hφc : Continuous φ) (hmono : Monotone φ)
    {c : M} {x : Model n} (hx : x∈(extChartAt 𝓘(ℝ,Model n) c).target)
    {z : M} {l τ : ℝ} (hφ : HasDerivAt φ l (v ((extChartAt 𝓘(ℝ,Model n) c).symm x)))
    (hl : 0<l) (hl1 : l<1) (hτ : 0<τ) (hτ1 : τ<1)
    (hval : hopfLax τ (fun y=>φ (v y)) z=φ (v ((extChartAt 𝓘(ℝ,Model n) c).symm x))+
      cost ((extChartAt 𝓘(ℝ,Model n) c).symm x) z/τ) :
    Nonempty (TrueCenterRow c u v φ x z τ l) := by
  obtain ⟨p,hm,hc,hr,he,hb,ht,hf⟩ := hmtw.exists_center_coordinate_support hu hv hdual hφc hmono hx hφ hl hl1 hτ hτ1 hval
  exact ⟨⟨p,hx,hm,hc,hr,he,hb,ht,hf⟩⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_JensenAtCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section JensenAtCenter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.jensen_at_center_row (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {Lv : ℝ≥0} (hv : LipschitzWith Lv v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hφ : Continuous φ) (hmono : Monotone φ)
    {w : M → ℝ} {t l : ℝ} (ht : 0<t) (ht1 : t<1) {a c : M} {N : Set (Model n)}
    (J : JensenSamplesAt w (fun y=>φ (v y)) t a c N) (k : ℕ)
    (hd : HasDerivAt φ l (v (J.Y (J.z k)))) (hl : 0<l) (hl1 : l<1) :
    Nonempty (TrueCenterRow a u v φ (extChartAt 𝓘(ℝ,Model n) a (J.Y (J.z k)))
      ((extChartAt 𝓘(ℝ,Model n) a).symm (J.z k)) (1-t) l) := by
  have hsource := (J.samples k).1
  have hleft := (extChartAt 𝓘(ℝ,Model n) a).left_inv hsource
  have hx := (extChartAt 𝓘(ℝ,Model n) a).map_source hsource
  apply hmtw.actual_center_row hu hv hdual hφ hmono hx
  · rwa [hleft]
  · exact hl
  · exact hl1
  · linarith
  · linarith
  · rw [hleft]
    exact ((J.samples k).2.2.1 (J.Y (J.z k))).mpr rfl

end JensenAtCenter
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumReindex
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

def MaximumJensenFamily.comp (J : MaximumJensenFamily hmtw hv ho F a c N)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) :
    MaximumJensenFamily hmtw hv ho (F.comp σ hσ) a c N where
  poleSource k := J.poleSource (σ k)
  endpointSource k := J.endpointSource (σ k)
  sample k := J.sample (σ k)
  first k := J.first (σ k)

def MaximumDiagonal.comp {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) :
    MaximumDiagonal (J.comp σ hσ) (ε ∘ σ) (fun k j=>P (σ k) j) where
  ν := S.ν ∘ σ
  poleSource k := S.poleSource (σ k)
  chart k := S.chart (σ k)
  baseClose k := S.baseClose (σ k)
  velocityClose k := S.velocityClose (σ k)
  centerClose k := S.centerClose (σ k)
  gradientClose k := S.gradientClose (σ k)
  HClose k := S.HClose (σ k)
  LClose k := S.LClose (σ k)
  activeClose k := S.activeClose (σ k)
  weightClose k := S.weightClose (σ k)
  extra k := S.extra (σ k)

end MaximumReindex
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SampleCenterFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section SampleCenterFamilies
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.coordinateBackward_graph_pole (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : subgradientGraph (n := n) (cTransform v)) {c : M}
    (hz : graphProjection (cTransform v) t q∈(extChartAt 𝓘(ℝ,Model n) c).source) :
    coordinateBackward c (t,extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform v) t q),
      fderiv ℝ (chartOuterEnvelope v t c)
        (extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform v) t q)))=q.1.1 := by
  have HH := hmtw.coordinateBackward_eq_pole (continuous_cTransform hv)
    (continuous_cTransform (continuous_cTransform hv)) ⟨(cTransform_triple hv).symm,rfl⟩ ht ht1
      ((extChartAt 𝓘(ℝ,Model n) c).map_source hz)
  rw [(extChartAt 𝓘(ℝ,Model n) c).left_inv hz] at HH
  have HP := congrArg Bundle.TotalSpace.proj (hmtw.hopfLax_backward_flow hv ht ht1 q)
  exact HH.trans HP

def WeakMTW.center_sequence_of_graph (hmtw : WeakMTW (n := n) (M := M))
    {a c : M} {u v : M → ℝ} {Φ : ℝ×ℝ → ℝ}
    {γj lj τj tj : ℕ → ℝ} {xj : ℕ → Model n} {wj : ℕ → M → ℝ}
    (hw : ∀ i,Continuous (wj i)) (ht : ∀ i,0<tj i) (ht1 : ∀ i,tj i<1)
    (q : ∀ i,subgradientGraph (n := n) (cTransform (wj i)))
    (ha : ∀ i,(q i).1.1∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (hc : ∀ i,graphProjection (cTransform (wj i)) (tj i) (q i)∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (R : ∀ i,TrueCenterRow c u v (fun s=>Φ (γj i,s)) (xj i)
      (graphProjection (cTransform (wj i)) (tj i) (q i)) (τj i) (lj i))
    (hd : ∀ᶠ i in atTop,
      (∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform (wj i)) (tj i) (q i))),
        DifferentiableAt ℝ (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y))
          ((extChartAt 𝓘(ℝ,Model n) c).symm z)) z) ∧
      DifferentiableAt ℝ (fderiv ℝ (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y))
        ((extChartAt 𝓘(ℝ,Model n) c).symm z)))
        (extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform (wj i)) (tj i) (q i))))
    (hg : Tendsto (fun i=>fderiv ℝ (chartOuterEnvelope (wj i) (tj i) c)
        (extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform (wj i)) (tj i) (q i)))+
      fderiv ℝ (fun z=>hopfLax (τj i) (fun y=>Φ (γj i,v y))
        ((extChartAt 𝓘(ℝ,Model n) c).symm z))
        (extChartAt 𝓘(ℝ,Model n) c (graphProjection (cTransform (wj i)) (tj i) (q i)))) atTop (𝓝 0)) :
    CenterSequenceData a c u v Φ γj lj τj tj xj
      (fun i=>graphBaseCoordinate a (q i).1) (fun i=>graphVelocityCoordinate a (q i).1)
      (fun i=>graphProjection (cTransform (wj i)) (tj i) (q i))
      (fun i=>chartOuterEnvelope (wj i) (tj i) c) where
  row := R
  endpoint i := movingPrefix_graph_coordinates (ha i) (tj i)
  derivative := hd
  gradient := hg
  backward := Eventually.of_forall (fun i=>by
    rw [hmtw.coordinateBackward_graph_pole (hw i) (ht i) (ht1 i) (q i) (hc i)]
    exact ((extChartAt 𝓘(ℝ,Model n) a).left_inv (ha i)).symm)

end SampleCenterFamilies
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumCenterSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
section MaximumCenterSequence
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

def MaximumDiagonal.center_sequence {J : MaximumJensenFamily hmtw hv ho F a c N}
    {ε : ℕ → ℝ} {P : ℕ → ℕ → Prop} (S : MaximumDiagonal J ε P)
    {u : M → ℝ} (hu : Continuous u) {Lv : ℝ≥0} (hLv : LipschitzWith Lv v)
    (hdual : IsCostDualPair u v) (hBc : ContDiff ℝ ∞ Bc)
    (hmono : ∀ b∈Icc bminus bplus,Monotone (fun s=>modifiedScalar α D Bc (b,s)))
    (hl : ∀ k,0<J.sampleSlope k (S.ν k) ∧ J.sampleSlope k (S.ν k)<1)
    (hg : Tendsto (fun k=>J.sampleGradient k (S.ν k)) atTop (𝓝 0)) :
    CenterSequenceData a c u v (modifiedScalar α D Bc) F.b
      (fun k=>J.sampleSlope k (S.ν k)) (fun k=>1-F.t k) F.t
      (fun k=>J.sampleCenter k (S.ν k))
      (fun k=>graphBaseCoordinate a (J.samplePoint k (S.ν k)).1)
      (fun k=>graphVelocityCoordinate a (J.samplePoint k (S.ν k)).1)
      (fun k=>graphProjection (cTransform (modifiedDatum v α D (F.b k) Bo)) (F.t k)
        (J.samplePoint k (S.ν k)))
      (fun k=>chartOuterEnvelope (modifiedDatum v α D (F.b k) Bo) (F.t k) c) := by
  have R (k:ℕ) : Nonempty (TrueCenterRow c u v
      (fun s=>modifiedScalar α D Bc (F.b k,s)) (J.sampleCenter k (S.ν k))
      (graphProjection (cTransform (modifiedDatum v α D (F.b k) Bo)) (F.t k)
        (J.samplePoint k (S.ν k))) (1-F.t k) (J.sampleSlope k (S.ν k))) := by
    rw [J.sampleProjection]
    exact hmtw.jensen_at_center_row hu hLv hdual
      ((modifiedScalar_contDiff hBc α D).continuous.comp (continuous_const.prodMk continuous_id))
      (hmono (F.b k) (Ioo_subset_Icc_self (F.parameter k)))
      (F.prefixTime k).1 (F.prefixTime k).2 (J.sample k) (J.sampleIndex k (S.ν k))
      (scalar_family_derivable (modifiedScalar_contDiff hBc α D)
        (F.b k,v ((J.sample k).Y ((J.sample k).z (J.sampleIndex k (S.ν k)))))) (hl k).1 (hl k).2
  apply hmtw.center_sequence_of_graph
    (fun k=>continuous_modifiedDatum hv α D (F.b k) ho)
    (fun k=>(F.prefixTime k).1) (fun k=>(F.prefixTime k).2)
    (fun k=>J.samplePoint k (S.ν k)) S.poleSource S.endpointSource
    (fun k=>Classical.choice (R k))
  · apply Eventually.of_forall
    intro k
    rw [S.endpointChart]
    obtain ⟨_,_,_,_,_,_,_,_,hC,_,_⟩ := (J.sample k).samples (J.sampleIndex k (S.ν k))
    refine ⟨?_,hC⟩
    filter_upwards [(J.sample k).openRegion.mem_nhds ((J.sample k).sampleInRegion
      (J.sampleIndex k (S.ν k)))] with z hz
    exact (J.sample k).centerDifferentiable z hz
  · convert hg using 1
    all_goals try with_reducible_and_instances rfl
    ext k
    rw [S.endpointChart]
    rfl

end MaximumCenterSequence
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MaximumOuterSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MaximumOuterSamples
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {v : M → ℝ} {α D bminus bplus : ℝ} {Bc Bo : ℝ → ℝ}
    {hmtw : WeakMTW (n := n) (M := M)} {hv : Continuous v} {ho : Continuous Bo}
    {F : MaximumFamily (n := n) v α D bminus bplus Bc Bo} {a c : M} {N : Set (Model n)}

def MaximumJensenFamily.OuterSampleGood (J:MaximumJensenFamily hmtw hv ho F a c N)
    (k j:ℕ):Prop :=
  let b:=graphBaseCoordinate a (J.samplePoint k j).1
  (∀d e,J.sampleL k j d e=J.sampleL k j e d) ∧
  (∀d,0 ≤ J.sampleL k j d d) ∧
  (∀i,0 ≤ (J.first k).w j i) ∧
  (∀i,chartFiberInverse a b ((J.first k).pj j i)∈
    activeLogs (modifiedDatum v α D (F.b k) Bo) ((extChartAt 𝓘(ℝ,Model n) a).symm b)) ∧
  (∀i,0 < (J.first k).w j i → HasLowerSecondTaylor
    (fun d=>modifiedDatum v α D (F.b k) Bo (movingNormal a (b,(J.first k).pj j i+d))+
      ‖chartFiberInverse a b ((J.first k).pj j i+d)‖^2/2) 0
    ((J.first k).w j i • J.sampleL k j))

end MaximumOuterSamples
end WeakMTWTransport

end
end

end OAI
end


