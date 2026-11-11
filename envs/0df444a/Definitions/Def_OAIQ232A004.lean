-- Prove2me | Definitions.Def_OAIQ232A004
-- name    : OAIQ232A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:41:58.893059+00:00
-- url     : https://prove2.me/theorems/e2ab5b26-a494-46af-8352-ce098d7babad
-- title:
--   Definitions bundle OAIQ232A004 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 66 declarations of OpenAI's Lean: 8 definitions and 58 theorems. The definitions and types are `OAI.WeakMTWTransport.chartCost`, `OAI.WeakMTWTransport.coordinatePairingDerivativeBilinearNormedAddCommGroup`, `OAI.WeakMTWTransport.coordinatePairingDerivativeBilinearNormedSpace`, `OAI.WeakMTWTransport.coordinatePairingDerivativeDualNormedAddCommGroup`, `OAI.WeakMTWTransport.coordinatePairingDerivativeDualNormedSpace`, `OAI.WeakMTWTransport.coordinatePairingDerivativeNormedSpace`, `OAI.WeakMTWTransport.dualObjective`, `OAI.WeakMTWTransport.modifiedScalar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_CompactSmoothGrowth`, `BiholderTransport_Calculus_FiniteSmoothTransverseGrowth`, `BiholderTransport_Calculus_ScalarFamily`, `BiholderTransport_Calculus_TaylorBound`, `BiholderTransport_Contact_MatchedSupports`, `BiholderTransport_Contact_UpperContactIteratedDeriv`, `BiholderTransport_Convexity_Fermat`, `BiholderTransport_Coordinates_ChartCostJets`, `BiholderTransport_Coordinates_CompactEventuallyFiberwise`, `BiholderTransport_Coordinates_CoordinatePairingDerivative`, `BiholderTransport_Coordinates_NormalSubdifferential`, `BiholderTransport_CostGeometry_CurvedQuadratic`, `BiholderTransport_CostGeometry_DividedAction`, `BiholderTransport_CostGeometry_FirstCutSegment`, `BiholderTransport_CostGeometry_PrecutExtension`, `BiholderTransport_Duality_CompactDual`, `BiholderTransport_Geodesics_GlobalGauss`, `BiholderTransport_Geodesics_NoCorner`, `BiholderTransport_LinearAlgebra_Calculus`, `BiholderTransport_LinearAlgebra_FinitePositiveWeight`, `BiholderTransport_LinearAlgebra_Hessian`, `BiholderTransport_LinearAlgebra_HessianSmooth`, `BiholderTransport_LinearAlgebra_JensenHessian`, `BiholderTransport_LinearAlgebra_SchurEnvelope`, `BiholderTransport_LinearAlgebra_SchurRatioTendstoBot`, `BiholderTransport_Regularity_ActionKernel`, `BiholderTransport_Regularity_ContDiffParametricSecant`, `BiholderTransport_Regularity_ContDiffQuadraticUpper`, `BiholderTransport_Regularity_ContDiffSecondOrder`, `BiholderTransport_Regularity_EuclideanUpper`, `BiholderTransport_Regularity_FiniteNonnegativeWeight`, `BiholderTransport_Regularity_FiniteNonnegativeWeightPos`, `BiholderTransport_Regularity_FiniteSimplexRepresentation`, `BiholderTransport_Regularity_GeneratingKernel`, `BiholderTransport_Regularity_InteriorCompactUniqueFiber`, `BiholderTransport_Regularity_LimitGeometry`, `BiholderTransport_Regularity_LocalMinSecondDeriv`, `BiholderTransport_Regularity_LocalMinStrictGrowth`, `BiholderTransport_Regularity_MetricDefinitions`, `BiholderTransport_Regularity_SecondFderivCompLinear`, `BiholderTransport_Regularity_SecondScaled`, `BiholderTransport_Regularity_UniformFiniteGrowth`, `BiholderTransport_Volume_DiagonalKernel`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A009` and `OAIQ232A011`; the proof of `OAI.WeakMTWTransport.parametric_short_pullback_semibound`.
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
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_TaylorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

section TaylorBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_order_remainder_bound_on_ball {f : E → ℝ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε)
    (hf : ∀ z ∈ Metric.ball (0:E) r, ContDiffAt ℝ 2 f z)
    (hB : ∀ z ∈ Metric.ball (0:E) r,
      ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f) 0‖ ≤ ε)
    {h : E} (hh : h ∈ Metric.ball (0:E) r) :
    |f h - f 0 - fderiv ℝ f 0 h - fderiv ℝ (fderiv ℝ f) 0 h h / 2| ≤ ε * ‖h‖^2 := by
  let D := fderiv ℝ f 0
  let B := fderiv ℝ (fderiv ℝ f) 0
  let R : E → ℝ := fun z => f z - f 0 - D z - B z z / 2
  let R' : E → E →L[ℝ] ℝ := fun z => fderiv ℝ f z - D - B z
  have h0 : (0:E) ∈ Metric.ball (0:E) r := Metric.mem_ball_self hr
  have hs : ∀ v w, B v w = B w v :=
    fun v w => ((hf 0 h0).isSymmSndFDerivAt (by norm_num)).eq v w
  have hdR' : ∀ z ∈ Metric.ball (0:E) r,
      HasFDerivAt R' (fderiv ℝ (fderiv ℝ f) z - B) z := by
    intro z hz
    exact ((((hf z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.sub_const D).sub B.hasFDerivAt
  have hR' : ∀ z ∈ Metric.ball (0:E) r, ‖R' z‖ ≤ ε * ‖z‖ := by
    intro z hz
    have H := (convex_ball (0:E) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hdR' z hz).hasFDerivWithinAt) hB h0 hz
    simpa only [R',D,B,map_zero,sub_self,sub_zero] using H
  have hdR : ∀ z ∈ Metric.ball (0:E) r, HasFDerivAt R (R' z) z := by
    intro z hz
    have hquad : HasFDerivAt (fun v : E => B v v / 2) (B z) z := by
      have H := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id z) (hasFDerivAt_id z)).const_smul (1/2:ℝ)
      have he : (fun v : E => B v v / 2) = ((1/2:ℝ) • fun v : E => B v v) := by
        ext v
        simp only [Pi.smul_apply,smul_eq_mul]
        ring
      rw [he]
      apply H.congr_fderiv
      ext v
      simp only [_root_.smul_apply,_root_.add_apply,ContinuousLinearMap.precompR_apply,
        ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,smul_eq_mul,id_eq]
      rw [hs v z]
      ring
    exact (((hf z hz).differentiableAt (by norm_num)).hasFDerivAt.sub_const (f 0)
      |>.sub D.hasFDerivAt |>.sub hquad)
  have hsub : Metric.closedBall (0:E) ‖h‖ ⊆ Metric.ball (0:E) r := by
    intro z hz
    simp only [Metric.mem_closedBall,Metric.mem_ball,dist_zero_right] at hz hh ⊢
    exact lt_of_le_of_lt hz hh
  have H := (convex_closedBall (0:E) ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hdR z (hsub hz)).hasFDerivWithinAt)
    (show ∀ z ∈ Metric.closedBall (0:E) ‖h‖, ‖R' z‖ ≤ ε * ‖h‖ from by
      intro z hz
      apply (hR' z (hsub hz)).trans
      exact mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz) hε)
    (Metric.mem_closedBall_self (norm_nonneg h))
    (show h ∈ Metric.closedBall (0:E) ‖h‖ by simp)
  simpa only [R,D,B,map_zero,_root_.zero_apply,zero_div,sub_self,sub_zero,Real.norm_eq_abs,
    pow_two,mul_assoc] using H

end TaylorBound

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace P] [CompactSpace P]

lemma compact_parametric_second_order_remainder
    (f : P → E → ℝ)
    (hf : ∀ a : P, ∀ᶠ q : E × P in 𝓝 (0,a), ContDiffAt ℝ 2 (f q.2) q.1)
    (hD : ∀ a : P, ContinuousAt (fun q : E × P => fderiv ℝ (fderiv ℝ (f q.2)) q.1) (0,a))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : E in 𝓝 0, ∀ a : P,
      |f a h - f a 0 - fderiv ℝ (f a) 0 h -
        fderiv ℝ (fderiv ℝ (f a)) 0 h h / 2| ≤ ε * ‖h‖^2 := by
  have hloc : ∀ a ∈ (univ : Set P), ∀ᶠ q : E × P in 𝓝 (0,a),
      ContDiffAt ℝ 2 (f q.2) q.1 ∧
      ‖fderiv ℝ (fderiv ℝ (f q.2)) q.1 - fderiv ℝ (fderiv ℝ (f q.2)) 0‖ ≤ ε := by
    intro a _
    have hc0 : ContinuousAt (fun q : E × P => ((0:E),q.2)) ((0:E),a) :=
      continuousAt_const.prodMk continuousAt_snd
    have hcB0 : ContinuousAt (fun q : E × P =>
        fderiv ℝ (fderiv ℝ (f q.2)) 0) (0,a) :=
      by
      simpa only [Function.comp_def] using (hD a).comp (x := ((0:E),a)) (f := fun q : E × P => ((0:E),q.2)) hc0
    have hc : ContinuousAt (fun q : E × P =>
        ‖fderiv ℝ (fderiv ℝ (f q.2)) q.1 - fderiv ℝ (fderiv ℝ (f q.2)) 0‖) (0,a) :=
      by
      have hh : ContinuousAt (fun q : E × P =>
        fderiv ℝ (fderiv ℝ (f q.2)) q.1 - fderiv ℝ (fderiv ℝ (f q.2)) (0:E)) ((0:E),a) :=
        (hD a).sub hcB0
      exact @ContinuousAt.norm (E × P) (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _ hh
    have he : ∀ᶠ q : E × P in 𝓝 (0,a),
        ‖fderiv ℝ (fderiv ℝ (f q.2)) q.1 - fderiv ℝ (fderiv ℝ (f q.2)) 0‖ < ε :=
      hc.eventually_lt continuousAt_const (by simpa only [sub_self, ContinuousLinearMap.opNorm_zero] using hε)
    exact (hf a).and (he.mono (fun _ h => h.le))
  have he : ∀ᶠ h : E in 𝓝 0, ∀ a ∈ (univ : Set P),
      ContDiffAt ℝ 2 (f a) h ∧
      ‖fderiv ℝ (fderiv ℝ (f a)) h - fderiv ℝ (fderiv ℝ (f a)) 0‖ ≤ ε :=
    isCompact_univ.eventually_forall_of_forall_eventually hloc
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with h hh
  intro a
  apply second_order_remainder_bound_on_ball hr hε.le
  · intro z hz
    exact (hball (y := z) hz a (mem_univ a)).1
  · intro z hz
    exact (hball (y := z) hz a (mem_univ a)).2
  · exact hh

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FiniteNonnegativeWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma finite_nonnegative_weight_exists_ge {ι : Type*} [Fintype ι] [Nonempty ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) {a : ℝ}
    (ha : a ≤ ∑ i, w i * f i) : ∃ i, a ≤ f i := by
  by_contra hn
  have hf : ∀ i, f i < a := by simpa only [not_exists,not_le] using hn
  have hpos : ∃ i, 0 < w i := by
    by_contra hp
    have hz : ∀ i, w i = 0 := by
      intro i
      exact le_antisymm (le_of_not_gt (fun h => hp ⟨i,h⟩)) (hw i)
    simp only [hz,Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨j,hj⟩ := hpos
  have hh : (∑ i, w i * f i) < ∑ i, w i * a := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (hf i).le (hw i)
    · exact ⟨j,Finset.mem_univ j,mul_lt_mul_of_pos_left (hf j) hj⟩
  rw [← Finset.sum_mul,hsum,one_mul] at hh
  exact (not_lt_of_ge ha) hh

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_UniformFiniteGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {P E : Type*} [TopologicalSpace P] [CompactSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [Nonempty ι]

lemma uniform_finite_transverse_quadratic_growth
    (w : P → ι → ℝ) (L : P → ι → E →L[ℝ] ℝ)
    (B : P → ι → E →L[ℝ] E →L[ℝ] ℝ)
    (hw : ∀ a i, 0 ≤ w a i) (hsum : ∀ a, ∑ i, w a i = 1)
    (hmean : ∀ a v, ∑ i, w a i * L a i v = 0)
    (hwc : ∀ i, Continuous (fun a => w a i))
    (hLc : ∀ i, Continuous (fun a => L a i))
    (hBc : ∀ i, Continuous (fun a => B a i))
    (hpos : ∀ a v, ‖v‖ = 1 → (∀ i, L a i v ≤ 0) →
      0 < ∑ i, w a i * B a i v v) :
    ∃ b > 0, ∀ᶠ h : E in 𝓝 0, ∀ a : P, ∃ i,
      b * ‖h‖ ^ 2 ≤ L a i h + B a i h h := by
  let Q : P × E → ℝ := fun z => ∑ i, w z.1 i * B z.1 i z.2 z.2
  have hQ : Continuous Q := by
    apply continuous_finsetSum
    intro i _
    exact ((hwc i).comp continuous_fst).mul
      (((hBc i).comp continuous_fst).clm_apply continuous_snd |>.clm_apply continuous_snd)
  have hL : ∀ i, Continuous (fun z : P × E => L z.1 i z.2) :=
    fun i => ((hLc i).comp continuous_fst).clm_apply continuous_snd
  let C : Set (P × E) := univ ×ˢ Metric.sphere (0:E) 1
  have hC : IsCompact C := isCompact_univ.prod (isCompact_sphere (0:E) 1)
  let K : Set (P × E) := C ∩ {z | ∀ i, L z.1 i z.2 ≤ 0}
  have hK : IsCompact K := by
    apply hC.inter_right
    simpa only [Set.ofPred_forall] using
      isClosed_iInter (fun i => isClosed_le (hL i) continuous_const)
  obtain ⟨b,hb,hbK⟩ : ∃ b > 0, ∀ z ∈ K, b < Q z := by
    by_cases hne : K.Nonempty
    · obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne hQ.continuousOn
      have hp : 0 < Q z := hpos z.1 z.2
        (by simpa only [Metric.mem_sphere,dist_zero_right] using hz.1.2) hz.2
      exact ⟨Q z / 2,half_pos hp,fun y hy => (half_lt_self hp).trans_le (hmin hy)⟩
    · exact ⟨1,zero_lt_one,fun z hz => (hne ⟨z,hz⟩).elim⟩
  have hloc : ∀ z ∈ C, ∀ᶠ q : ℝ × (P × E) in 𝓝 (0,z),
      0 ≤ q.1 → ∃ i, q.1 * b ≤ L q.2.1 i q.2.2 + q.1 * B q.2.1 i q.2.2 q.2.2 := by
    intro z hz
    by_cases hlin : ∃ i, 0 < L z.1 i z.2
    · obtain ⟨i,hi⟩ := hlin
      have hc : Continuous (fun q : ℝ × (P × E) =>
          L q.2.1 i q.2.2 + q.1 * (B q.2.1 i q.2.2 q.2.2 - b)) := by
        exact ((hL i).comp continuous_snd).add
          (continuous_fst.mul (((((hBc i).comp (continuous_fst.comp continuous_snd)).clm_apply
            (continuous_snd.comp continuous_snd)).clm_apply
              (continuous_snd.comp continuous_snd)).sub continuous_const))
      have he : ∀ᶠ q : ℝ × (P × E) in 𝓝 (0,z),
          0 < L q.2.1 i q.2.2 + q.1 * (B q.2.1 i q.2.2 q.2.2 - b) :=
        hc.continuousAt.eventually (Ioi_mem_nhds (by simpa using hi))
      filter_upwards [he] with q hq _
      exact ⟨i,by nlinarith⟩
    · have hzK : z ∈ K := ⟨hz,fun i => le_of_not_gt (fun h => hlin ⟨i,h⟩)⟩
      have he : ∀ᶠ q : ℝ × (P × E) in 𝓝 (0,z), b < Q q.2 :=
        (hQ.comp continuous_snd).continuousAt.eventually (Ioi_mem_nhds (hbK z hzK))
      filter_upwards [he] with q hq hr
      apply finite_nonnegative_weight_exists_ge (w q.2.1)
        (fun i => L q.2.1 i q.2.2 + q.1 * B q.2.1 i q.2.2 q.2.2)
        (hw q.2.1) (hsum q.2.1)
      have heq : (∑ i, w q.2.1 i *
          (L q.2.1 i q.2.2 + q.1 * B q.2.1 i q.2.2 q.2.2)) = q.1 * Q q.2 := by
        simp only [mul_add,Finset.sum_add_distrib,hmean,zero_add,Q]
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hq.le hr
  have he : ∀ᶠ r : ℝ in 𝓝 0, ∀ z ∈ C, 0 ≤ r → ∃ i,
      r * b ≤ L z.1 i z.2 + r * B z.1 i z.2 z.2 :=
    hC.eventually_forall_of_forall_eventually hloc
  have hnorm : Tendsto (fun h : E => ‖h‖) (𝓝 0) (𝓝 (0:ℝ)) := by
    simpa only [norm_zero] using continuous_norm.tendsto (0:E)
  refine ⟨b,hb,?_⟩
  filter_upwards [hnorm.eventually he] with h hh
  intro a
  by_cases hz : h = 0
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i,by simp [hz]⟩
  · let v := ‖h‖⁻¹ • h
    have hn : 0 < ‖h‖ := norm_pos_iff.mpr hz
    have hv : v ∈ Metric.sphere (0:E) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,v,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    obtain ⟨i,hi⟩ := hh (a,v) ⟨mem_univ _,hv⟩ hn.le
    have hv' : ‖h‖ • v = h := by simp [v,smul_smul,hn.ne']
    have hil := mul_le_mul_of_nonneg_left hi hn.le
    refine ⟨i,?_⟩
    have hL' : L a i h = ‖h‖ * L a i v := by
      calc _ = L a i (‖h‖ • v) := congrArg (L a i) hv'.symm
           _ = _ := by simp only [map_smul,smul_eq_mul]
    have hB' : B a i h h = ‖h‖ * (‖h‖ * B a i v v) := by
      calc _ = B a i (‖h‖ • v) (‖h‖ • v) := by rw [hv']
           _ = _ := by simp only [map_smul,_root_.smul_apply,smul_eq_mul]
    rw [hL',hB']
    nlinarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_CompactSmoothGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {P E : Type*} [TopologicalSpace P] [CompactSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [Nonempty ι]

lemma compact_finite_smooth_transverse_growth
    (f : P → ι → E → ℝ) (w : P → ι → ℝ)
    (hw : ∀ a i, 0 ≤ w a i) (hsum : ∀ a, ∑ i, w a i = 1)
    (hwc : ∀ i, Continuous (fun a => w a i))
    (hf : ∀ a i, ∀ᶠ q : E × P in 𝓝 (0,a), ContDiffAt ℝ 2 (f q.2 i) q.1)
    (hf0 : ∀ a i, f a i 0 = 0)
    (hLc : ∀ i, Continuous (fun a => fderiv ℝ (f a i) 0))
    (hBc : ∀ i, Continuous (fun a => fderiv ℝ (fderiv ℝ (f a i)) 0))
    (hD : ∀ a i, ContinuousAt (fun q : E × P =>
      fderiv ℝ (fderiv ℝ (f q.2 i)) q.1) (0,a))
    (hmean : ∀ a v, ∑ i, w a i * fderiv ℝ (f a i) 0 v = 0)
    (hpos : ∀ a v, ‖v‖ = 1 → (∀ i, fderiv ℝ (f a i) 0 v ≤ 0) →
      0 < ∑ i, w a i * fderiv ℝ (fderiv ℝ (f a i)) 0 v v) :
    ∃ b > 0, ∀ᶠ h : E in 𝓝 0, ∀ a : P, ∃ i, b * ‖h‖^2 ≤ f a i h := by
  let L := fun a i => fderiv ℝ (f a i) 0
  let B := fun a i => (1/2 : ℝ) • fderiv ℝ (fderiv ℝ (f a i)) 0
  have hB : ∀ i, Continuous (fun a => B a i) :=
    fun i => (continuous_const : Continuous (fun _ : P => (1/2 : ℝ))).smul (hBc i)
  have hpos' : ∀ a v, ‖v‖ = 1 → (∀ i, L a i v ≤ 0) →
      0 < ∑ i, w a i * B a i v v := by
    intro a v hv hl
    have he : (∑ i, w a i * B a i v v) = (1/2:ℝ) *
        ∑ i, w a i * fderiv ℝ (fderiv ℝ (f a i)) 0 v v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [B,_root_.smul_apply,smul_eq_mul]
      ring
    rw [he]
    exact mul_pos (by norm_num) (hpos a v hv hl)
  obtain ⟨b,hb,H⟩ := uniform_finite_transverse_quadratic_growth w L B hw hsum hmean
    hwc hLc hB hpos'
  have HT : ∀ᶠ h : E in 𝓝 0, ∀ i, ∀ a : P,
      |f a i h - L a i h - B a i h h| ≤ (b/2) * ‖h‖^2 := by
    apply Filter.eventually_all.mpr
    intro i
    have hi := compact_parametric_second_order_remainder (fun a => f a i)
      (fun a => hf a i) (fun a => hD a i) (half_pos hb)
    filter_upwards [hi] with h hh
    intro a
    simpa only [hf0,sub_zero,L,B,_root_.smul_apply,smul_eq_mul,one_div,div_eq_mul_inv,
      one_mul,mul_comm] using hh a
  refine ⟨b/2,half_pos hb,?_⟩
  filter_upwards [H,HT] with h hh ht
  intro a
  obtain ⟨i,hi⟩ := hh a
  have he := (abs_le.mp (ht i a)).1
  exact ⟨i,by nlinarith⟩

end

open Set Filter
open scoped Topology ContDiff

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_FinitePositiveWeight
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma finite_positive_weight_exists_ge {ι : Type*} [Fintype ι] [Nonempty ι]
    (w f : ι → ℝ) (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1) {a : ℝ}
    (ha : a≤∑ i, w i*f i) : ∃ i, a≤f i := by
  by_contra! h
  have hh : (∑ i, w i*f i)<∑ i, w i*a := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (mul_lt_mul_of_pos_left (h i) (hw i)).le
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact ⟨i,Finset.mem_univ i,mul_lt_mul_of_pos_left (h i) (hw i)⟩
  rw [←Finset.sum_mul,hsum,one_mul] at hh
  exact (not_lt_of_ge ha) hh

lemma finite_positive_weight_zero {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0<w i) (hf : ∀ i, f i≤0)
    (hsum : ∑ i, w i*f i=0) : ∀ i, f i=0 := by
  intro i
  apply le_antisymm (hf i)
  by_contra! hh
  have hs : (∑ j, w j*f j)<∑ j ∈ (Finset.univ : Finset ι), (0:ℝ) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_nonpos_of_nonneg_of_nonpos (hw j).le (hf j)
    · exact ⟨i,Finset.mem_univ i,mul_neg_of_pos_of_neg (hw i) hh⟩
  simp [hsum] at hs

lemma finite_transverse_quadratic_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → E →L[ℝ] ℝ) (B : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmean : ∀ v, ∑ i, w i*L i v=0)
    (hpos : ∀ v : E, v≠0 → (∀ i, L i v=0) → 0<∑ i, w i*B i v v) :
    ∃ b>0, ∀ᶠ h : E in 𝓝 0, ∃ i, b*‖h‖^2≤L i h+B i h h := by
  let Q : E → ℝ := fun v => ∑ i, w i*B i v v
  have hQ : Continuous Q := by
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul ((B i).continuous.clm_apply continuous_id))
  let K : Set E := {v | ‖v‖=1 ∧ ∀ i, L i v=0}
  have hK : IsCompact K := by
    have hc : IsClosed {v : E | ∀ i, L i v=0} := by
      simpa only [Set.ofPred_forall] using
        isClosed_iInter (fun i => isClosed_eq (L i).continuous (continuous_const (y := (0:ℝ))))
    exact (isCompact_sphere (0:E) 1).inter_right hc |>.of_isClosed_subset
      (isClosed_eq continuous_norm continuous_const |>.inter hc) (by
        intro v hv
        exact ⟨by simpa [Metric.mem_sphere,dist_zero_right] using hv.1,hv.2⟩)
  obtain ⟨b,hb,hbK⟩ : ∃ b>0, ∀ v ∈ K, b<Q v := by
    by_cases hne : K.Nonempty
    · obtain ⟨u,hu,hmin⟩ := hK.exists_isMinOn hne hQ.continuousOn
      have hp : 0<Q u := hpos u (by intro hz; simp [K,hz] at hu) hu.2
      refine ⟨Q u/2,by positivity,?_⟩
      intro v hv
      exact (half_lt_self hp).trans_le (hmin hv)
    · exact ⟨1,zero_lt_one,fun v hv => (hne ⟨v,hv⟩).elim⟩
  have hloc : ∀ u ∈ Metric.sphere (0:E) 1, ∀ᶠ z : ℝ × E in 𝓝 (0,u),
      0≤z.1 → ∃ i, z.1*b≤L i z.2+z.1*B i z.2 z.2 := by
    intro u hu
    by_cases hlin : ∃ i, 0<L i u
    · obtain ⟨i,hi⟩ := hlin
      have hc : Continuous (fun z : ℝ × E => L i z.2+z.1*(B i z.2 z.2-b)) := by
        exact ((L i).continuous.comp continuous_snd).add
          (continuous_fst.mul (((B i).continuous.comp continuous_snd).clm_apply continuous_snd |>.sub continuous_const))
      have he : ∀ᶠ z : ℝ × E in 𝓝 (0,u), 0<L i z.2+z.1*(B i z.2 z.2-b) :=
        hc.continuousAt.eventually (Ioi_mem_nhds (by simpa using hi))
      filter_upwards [he] with z hz _
      exact ⟨i,by nlinarith⟩
    · have hall : ∀ i, L i u=0 := finite_positive_weight_zero w (fun i => L i u) hw
        (by simpa only [not_exists,not_lt] using hlin) (hmean u)
      have huK : u ∈ K := ⟨by simpa [Metric.mem_sphere,dist_zero_right] using hu,hall⟩
      have he : ∀ᶠ z : ℝ × E in 𝓝 (0,u), b<Q z.2 :=
        (hQ.comp continuous_snd).continuousAt.eventually (Ioi_mem_nhds (hbK u huK))
      filter_upwards [he] with z hz hr
      apply finite_positive_weight_exists_ge w (fun i => L i z.2+z.1*B i z.2 z.2) hw hsum
      have heq : (∑ i, w i*(L i z.2+z.1*B i z.2 z.2))=z.1*Q z.2 := by
        simp only [mul_add,Finset.sum_add_distrib,hmean,zero_add,Q]
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hz.le hr
  have he : ∀ᶠ r : ℝ in 𝓝 0, ∀ u ∈ Metric.sphere (0:E) 1,
      0 ≤ r → ∃ i, r*b≤L i u+r*B i u u :=
    (isCompact_sphere (0:E) 1).eventually_forall_of_forall_eventually hloc
  have hnorm : Tendsto (fun h : E => ‖h‖) (𝓝 0) (𝓝 (0:ℝ)) := by simpa only [norm_zero] using (continuous_norm.tendsto (0:E))
  refine ⟨b,hb,?_⟩
  filter_upwards [hnorm.eventually he] with h hh
  by_cases hz : h=0
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i,by simp [hz]⟩
  · let u := ‖h‖⁻¹ • h
    have hn : 0<‖h‖ := norm_pos_iff.mpr hz
    have hu : u ∈ Metric.sphere (0:E) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,u,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    obtain ⟨i,hi⟩ := hh u hu hn.le
    have hv : ‖h‖ • u=h := by simp [u,smul_smul,hn.ne']
    have hil := mul_le_mul_of_nonneg_left hi hn.le
    refine ⟨i,?_⟩
    calc
      b*‖h‖^2≤‖h‖*(L i u+‖h‖*B i u u) := by nlinarith [hil]
      _ = L i h+B i h h := by
        have hL : L i h=‖h‖*L i u := by
          calc _ = L i (‖h‖ • u) := congrArg (L i) hv.symm
               _ = _ := by simp only [map_smul,smul_eq_mul]
        have hB : B i h h=‖h‖*(‖h‖*B i u u) := by
          calc _ = B i (‖h‖ • u) (‖h‖ • u) := by rw [hv]
               _ = _ := by simp only [map_smul,smul_apply,smul_eq_mul]
        rw [hL,hB]
        ring
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ContDiffSecondOrder
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
lemma contDiffAt_second_order_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    (fun h => f h-f 0-fderiv ℝ f 0 h-fderiv ℝ (fderiv ℝ f) 0 h h/2)
      =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  let D := fderiv ℝ f 0
  let B := fderiv ℝ (fderiv ℝ f) 0
  have hs : ∀ v w, B v w=B w v := fun v w => (hf.isSymmSndFDerivAt (by norm_num)).eq v w
  let R : E → ℝ := fun h => f h-f 0-D h-B h h/2
  let R' : E → E →L[ℝ] ℝ := fun h => fderiv ℝ f h-D-B h
  have hB : HasFDerivAt (fderiv ℝ f) B 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  obtain ⟨r,hr,hrdiff⟩ := Metric.mem_nhds_iff.mp ((hf.eventually (by norm_num)).mono fun h hh =>
    hh.differentiableAt (by norm_num))
  have hder : ∀ h ∈ Metric.ball (0:E) r, HasFDerivWithinAt R (R' h) (Metric.ball (0:E) r) h := by
    intro h hh
    have hquad : HasFDerivAt (fun z : E => B z z/2) (B h) h := by
      have H := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id h) (hasFDerivAt_id h)).const_smul (1/2:ℝ)
      have heq : (fun z : E => B z z/2) = ((1/2:ℝ) • fun z : E => B z z) := by ext z; simp only [Pi.smul_apply,smul_eq_mul] <;> ring
      rw [heq]
      apply H.congr_fderiv
      ext v
      simp only [smul_apply,add_apply,ContinuousLinearMap.precompR_apply,
        ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply,smul_eq_mul,id_eq]
      rw [hs v h]
      ring
    exact (((hrdiff hh).hasFDerivAt.sub_const (f 0)).sub D.hasFDerivAt |>.sub hquad).hasFDerivWithinAt
  have ho : R' =o[𝓝[Metric.ball (0:E) r] (0:E)] fun h => ‖h-(0:E)‖^1 := by
    simpa only [R',D,B,sub_zero,pow_one] using hB.isLittleO.norm_right.mono nhdsWithin_le_nhds
  have H := (convex_ball (0:E) r).isLittleO_pow_succ (Metric.mem_ball_self hr) hder ho
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds _ hr)] at H
  simpa only [R,D,B,map_zero,zero_apply,zero_div,sub_self,sub_zero] using H
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_FiniteSmoothTransverseGrowth
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
lemma finite_smooth_transverse_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → E → ℝ) (hf : ∀ i, ContDiffAt ℝ 2 (f i) 0) (hf0 : ∀ i, f i 0=0)
    (w : ι → ℝ) (hw : ∀ i, 0<w i) (hsum : ∑ i, w i=1)
    (hmean : ∀ v, ∑ i, w i*fderiv ℝ (f i) 0 v=0)
    (hpos : ∀ v : E, v≠0 → (∀ i, fderiv ℝ (f i) 0 v=0) →
      0<∑ i, w i*fderiv ℝ (fderiv ℝ (f i)) 0 v v) :
    ∃ b>0, ∀ᶠ h : E in 𝓝 0, ∃ i, b*‖h‖^2≤f i h := by
  let L := fun i => fderiv ℝ (f i) 0
  let B := fun i => (1/2:ℝ) • fderiv ℝ (fderiv ℝ (f i)) 0
  have hBpos : ∀ v : E, v≠0 → (∀ i, L i v=0) → 0<∑ i, w i*B i v v := by
    intro v hv hl
    have heq : (∑ i, w i*B i v v)=(1/2:ℝ)*(∑ i, w i*fderiv ℝ (fderiv ℝ (f i)) 0 v v) := by
      simp only [B,smul_apply,smul_eq_mul,Finset.mul_sum]
      congr 1
      ext i
      ring
    rw [heq]
    exact mul_pos (by norm_num) (hpos v hv hl)
  obtain ⟨b,hb,hgrowth⟩ := finite_transverse_quadratic_growth L B w hw hsum hmean hBpos
  have hrem : ∀ᶠ h : E in 𝓝 0, ∀ i,
      |f i h-L i h-B i h h|≤(b/2)*‖h‖^2 := by
    rw [Filter.eventually_all]
    intro i
    have H := (contDiffAt_second_order_remainder (hf i)).bound (half_pos hb)
    simpa only [hf0,L,B,smul_apply,smul_eq_mul,div_eq_mul_inv,one_mul,mul_comm,
      sub_zero,Real.norm_eq_abs,norm_pow,Real.norm_of_nonneg (norm_nonneg _)] using H
  refine ⟨b/2,half_pos hb,?_⟩
  filter_upwards [hgrowth,hrem] with h hh hr
  obtain ⟨i,hi⟩ := hh
  exact ⟨i,by linarith [(abs_le.mp (hr i)).1]⟩
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_ScalarFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

def modifiedScalar (α D : ℝ) (B : ℝ → ℝ) (p : ℝ×ℝ) : ℝ :=
  p.2+p.1*B ((p.2-α)/D)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_MatchedSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma linear_supports_match {f : E → ℝ} {x : E} {L U : E →L[ℝ] ℝ} {B : ℝ}
    (hnear : ∀ᶠ y in 𝓝 x,
      f x+L (y-x)-B*‖y-x‖^2≤f y ∧ f y≤f x+U (y-x)+B*‖y-x‖^2) : L=U := by
  have hmin : IsLocalMin (fun h : E => (U-L) h+(2*B)*‖h‖^2) 0 := by
    have hn := ((continuous_const.add continuous_id).tendsto (0:E)).eventually
      (show ∀ᶠ y in 𝓝 (x+(0:E)), _ from by simpa only [add_zero] using hnear)
    filter_upwards [hn] with h hh
    change f x + L (x+h-x) - B*‖x+h-x‖^2 ≤ f (x+h) ∧
      f (x+h) ≤ f x + U (x+h-x) + B*‖x+h-x‖^2 at hh
    simp only [add_sub_cancel_left] at hh
    simpa only [add_sub_cancel_left] using
      (show (U-L) 0+(2*B)*‖(0:E)‖^2≤(U-L) h+(2*B)*‖h‖^2 from by
        simp only [map_zero,norm_zero,zero_pow (by omega : 2≠0),mul_zero,zero_add,
          _root_.sub_apply]
        linarith [hh.1,hh.2])
  have hd : HasFDerivAt (fun h : E => (U-L) h+(2*B)*‖h‖^2) (U-L) 0 := by
    convert (U-L).hasFDerivAt.add ((hasStrictFDerivAt_norm_sq (0:E)).hasFDerivAt.const_mul (2*B)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (ext h; simp)
  exact (sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero hd)).symm

lemma hasFDerivAt_of_quadratic_remainder {f : E → ℝ} {x : E} {L : E →L[ℝ] ℝ}
    {B : ℝ} (hB : 0≤B)
    (hnear : ∀ᶠ y in 𝓝 x, |f y-f x-L (y-x)|≤B*‖y-x‖^2) :
    HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have hn : ∀ᶠ h : E in 𝓝 0, |f (x+h)-f x-L h|≤B*‖h‖^2 := by
    simpa only [add_zero,add_sub_cancel_left] using
      ((show Tendsto (fun h : E => x+h) (𝓝 0) (𝓝 x) from by
        convert (continuous_const.add continuous_id : Continuous (fun h : E => x+h)).tendsto 0 using 1
        all_goals try with_reducible_and_instances rfl
        all_goals first | rfl | simp).eventually hnear)
  have hr : ∀ᶠ h : E in 𝓝 0, ‖h‖<ε/(B+1) :=
    (continuous_norm.tendsto (0:E)).eventually (by
      simpa only [norm_zero] using eventually_lt_nhds (show (0:ℝ)<ε/(B+1) by positivity))
  filter_upwards [hn,hr] with h hh hr
  rw [Real.norm_eq_abs]
  apply hh.trans
  have hmul : (B+1)*‖h‖<ε := by
    have := (lt_div_iff₀ (show 0<B+1 by linarith)).mp hr
    nlinarith
  have hh0 := norm_nonneg h
  have : B*‖h‖≤ε := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hh0]

lemma quadratic_remainder_of_two_supports {f : E → ℝ} {S : Set E}
    (hS : IsOpen S) {B : ℝ} (hB : 0≤B)
    (hs : ∀ x∈S, ∃ L U : E →L[ℝ] ℝ, ∀ y∈S,
      f x+L (y-x)-B*‖y-x‖^2≤f y ∧ f y≤f x+U (y-x)+B*‖y-x‖^2) :
    ∀ x∈S, DifferentiableAt ℝ f x ∧
      ∀ y∈S, |f y-f x-fderiv ℝ f x (y-x)|≤B*‖y-x‖^2 := by
  intro x hx
  obtain ⟨L,U,hLU⟩ := hs x hx
  have hsame : L=U := linear_supports_match
    (by filter_upwards [hS.mem_nhds hx] with y hy; exact hLU y hy)
  subst U
  have hrem : ∀ y∈S, |f y-f x-L (y-x)|≤B*‖y-x‖^2 := by
    intro y hy
    exact abs_le.mpr ⟨by linarith [(hLU y hy).1],by linarith [(hLU y hy).2]⟩
  have hd := hasFDerivAt_of_quadratic_remainder hB
    (by filter_upwards [hS.mem_nhds hx] with y hy; exact hrem y hy)
  exact ⟨hd.differentiableAt,by simpa only [hd.fderiv] using hrem⟩

lemma derivative_lipschitz_of_quadratic_remainder {f : E → ℝ} {a : E} {r B : ℝ}
    (hr : 0 < r) (hB : 0≤B)
    (hrem : ∀ x∈ball a r, ∀ y∈ball a r,
      |f y-f x-fderiv ℝ f x (y-x)|≤B*‖y-x‖^2) :
    LipschitzOnWith ⟨6*B,by positivity⟩ (fderiv ℝ f) (ball a (r/4)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm,dist_eq_norm]
  change ‖fderiv ℝ f x-fderiv ℝ f y‖≤(6*B)*‖x-y‖
  by_cases hxy : x=y
  · simp only [hxy,sub_self,norm_zero,mul_zero,le_refl]
  let d := ‖x-y‖
  have hd : 0<d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hdR : d < r/2 := by
    have H := dist_triangle x a y
    rw [dist_comm a y] at H
    change dist x a < r/4 at hx
    change dist y a < r/4 at hy
    rw [dist_eq_norm] at H
    change d≤_ at H
    linarith
  have hxR : x∈ball a r := ball_subset_ball (by linarith only [hr]) hx
  have hyR : y∈ball a r := ball_subset_ball (by linarith) hy
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  let z := x+d • e
  have hzR : z∈ball a r := by
    have H := dist_triangle z x a
    have hzx : dist z x=d := by simp only [z,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hd,he,mul_one]
    rw [hzx] at H
    change dist x a < r/4 at hx
    exact lt_of_le_of_lt H (by linarith)
  have hzx : ‖z-x‖=d := by simp only [z,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hd,he,mul_one]
  have hzy : ‖z-y‖≤2*d := by
    have H := norm_add_le (z-x) (x-y)
    have he : (z-x)+(x-y)=z-y := by abel
    rw [he,hzx] at H
    change _≤d+d at H
    linarith
  have hxz := hrem x hxR z hzR
  have hyz := hrem y hyR z hzR
  have hyx := hrem y hyR x hxR
  have hlin : (fderiv ℝ f x-fderiv ℝ f y) (z-x) =
      (f z-f y-fderiv ℝ f y (z-y))-
      (f x-f y-fderiv ℝ f y (x-y))-
      (f z-f x-fderiv ℝ f x (z-x)) := by
    have he : z-y=(z-x)+(x-y) := by abel
    rw [he,map_add,_root_.sub_apply]
    ring
  have H := abs_sub ((f z-f y-fderiv ℝ f y (z-y))-
      (f x-f y-fderiv ℝ f y (x-y))) (f z-f x-fderiv ℝ f x (z-x))
  have H' := abs_sub (f z-f y-fderiv ℝ f y (z-y)) (f x-f y-fderiv ℝ f y (x-y))
  rw [←hlin] at H
  rw [hzx] at hxz
  have Hsq : ‖z-y‖^2≤4*d^2 := by nlinarith [norm_nonneg (z-y)]
  have Hb := mul_le_mul_of_nonneg_left Hsq hB
  have hbound : |(fderiv ℝ f x-fderiv ℝ f y) (z-x)|≤6*B*d^2 := by
    change _≤B*d^2 at hyx
    nlinarith
  have happly : (fderiv ℝ f x-fderiv ℝ f y) (z-x)=d*((fderiv ℝ f x-fderiv ℝ f y) e) := by
    simp only [z,add_sub_cancel_left,map_smul,smul_eq_mul]
  rw [happly,abs_mul,abs_of_pos hd] at hbound
  rw [Real.norm_eq_abs]
  nlinarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_LocalMinSecondDeriv
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

lemma localMin_second_deriv_nonneg {f : ℝ → ℝ} {a : ℝ}
    (h : IsLocalMin f a) (hc : ContinuousAt f a) : 0 ≤ deriv (deriv f) a := by
  by_contra hn
  have hm := isLocalMax_of_deriv_deriv_neg (lt_of_not_ge hn) h.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [h,hm] with x hx hy
    exact le_antisymm hy hx
  have hh := heq.deriv.deriv_eq
  simpa using (not_le_of_gt (lt_of_not_ge hn)) (show 0 ≤ deriv (deriv f) a by simpa using hh.ge)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_UpperContactIteratedDeriv
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma upper_contact_iteratedDeriv_two {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hle : ∀ᶠ y in 𝓝 x, f y≤g y) (heq : f x=g x) :
    iteratedDeriv 2 f x ≤ iteratedDeriv 2 g x := by
  have hmin : IsLocalMin (g-f) x := by
    filter_upwards [hle] with y hy
    change g x-f x≤g y-f y
    rw [heq,sub_self]
    exact sub_nonneg.mpr hy
  have H := localMin_second_deriv_nonneg hmin (hg.sub hf).continuousAt
  have htwo : iteratedDeriv 2 (g-f) x=deriv (deriv (g-f)) x := by
    rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]
  rw [←htwo] at H
  rw [iteratedDeriv_sub hg hf] at H
  exact sub_nonneg.mp H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_Fermat
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

lemma isLocalMin_hasMFDerivAt_eq_zero {f : M → ℝ} {x : M}
    {L : TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ}
    (h : IsLocalMin f x) (hD : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f x L) : L = 0 := by
  let c := extChartAt 𝓘(ℝ,E) x
  have hx : x ∈ c.source := mem_extChartAt_source x
  have hcx : c x ∈ c.target := c.map_source hx
  have hc : ContinuousAt c.symm (c x) :=
    ((continuousOn_extChartAt_symm x) _ hcx).continuousAt ((isOpen_extChartAt_target x).mem_nhds hcx)
  have hmin : IsLocalMin (fun w : E => f (c.symm w)) (c x) := by
    have hh : IsLocalMin f (c.symm (c x)) := by rw [c.left_inv hx]; exact h
    exact hh.comp_continuous hc
  have hDf : HasFDerivAt (fun w : E => f (c.symm w)) L (c x) := by
    convert! hD.2.hasFDerivAt (by simp only [mfld_simps,Filter.univ_mem])
  exact hmin.hasFDerivAt_eq_zero hDf

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CompactEventuallyFiberwise
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter
open scoped Topology

namespace WeakMTWTransport
lemma compact_eventually_fiberwise {A X T : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [T2Space X] [TopologicalSpace T]
    {K : Set A} (hK : IsCompact K) {f : A → X} (hf : Continuous f)
    {g : T → X} {t : T} (hg : ContinuousAt g t) {P : T → A → Prop}
    (hP : ∀ a∈K, f a=g t → ∀ᶠ q : T×A in 𝓝 (t,a), P q.1 q.2) :
    ∀ᶠ s in 𝓝 t, ∀ a∈K, f a=g s → P s a := by
  apply hK.eventually_forall_of_forall_eventually
  intro a ha
  by_cases he : f a=g t
  · filter_upwards [hP a ha he] with q hq using fun _ => hq
  · have hc1 : ContinuousAt (fun q : T×A => f q.2) (t,a) := hf.continuousAt.comp continuousAt_snd
    have hc2 : ContinuousAt (fun q : T×A => g q.1) (t,a) := hg.comp continuousAt_fst
    have hn : ∀ᶠ q : T×A in 𝓝 (t,a), f q.2≠g q.1 :=
      (hc1.prodMk hc2).preimage_mem_nhds (isClosed_diagonal.isOpen_compl.mem_nhds he)
    filter_upwards [hn] with q hq using fun heq => (hq heq).elim
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartCostJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

def chartCost (a y : M) (z : Model n) : ℝ :=
  cost ((extChartAt 𝓘(ℝ,Model n) a).symm z) y

end

open Set Filter
open scoped Topology

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinatePairingDerivative
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
local instance coordinatePairingDerivativeNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance coordinatePairingDerivativeDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance coordinatePairingDerivativeDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance coordinatePairingDerivativeBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance coordinatePairingDerivativeBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_NoCorner
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

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma cost_gradients_opposite {p y b : M}
    (htri : dist p b = dist p y + dist b y) (heq : dist p y = dist b y)
    (u v : TangentSpace 𝓘(ℝ,E) y)
    (hp : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun w => dist p w^2/2) y (innerSL ℝ u))
    (hb : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun w => dist b w^2/2) y (innerSL ℝ v)) :
    u + v = 0 := by
  have hmin : IsLocalMin (fun w => dist p w^2/2 + dist b w^2/2) y := by
    apply Filter.Eventually.of_forall
    intro w
    have h := dist_triangle p w b
    rw [htri,dist_comm w b] at h
    have h' : (dist p y+dist b y)^2 ≤ (dist p w+dist b w)^2 :=
      pow_le_pow_left₀ (add_nonneg dist_nonneg dist_nonneg) h 2
    nlinarith [sq_nonneg (dist p w-dist b w)]
  have hzero := isLocalMin_hasMFDerivAt_eq_zero hmin (hp.add hb)
  have hval := congrArg (fun L : TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ => L (u+v)) hzero
  have hsq : ‖u+v‖^2 = 0 := by
    simpa only [_root_.add_apply,_root_.zero_apply,
      innerSL_apply_apply,←inner_add_left,real_inner_self_eq_norm_sq] using hval
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_JensenHessian
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
include I

lemma riemannian_approximate_midpoint (x y : M) {eps : ℝ} (heps : 0 < eps) :
    ∃ z : M, dist x z = dist x y/2 ∧ dist z y < dist x y/2+eps := by
  have hdist : riemannianEDist I x y < ENNReal.ofReal (dist x y+eps) := by
    rw [← IsRiemannianManifold.out,edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by linarith)
  obtain ⟨γ,hγ0,hγ1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hdist
  have hc : ContinuousOn (fun t : ℝ => dist x (γ t)) (Icc 0 1) :=
    continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ.continuousOn)
  have hhalf : dist x y/2 ∈ Icc (dist x (γ 0)) (dist x (γ 1)) := by
    rw [hγ0,hγ1,dist_self]
    constructor <;> linarith [dist_nonneg (x := x) (y := y)]
  obtain ⟨t,ht,htt⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hc hhalf
  change dist x (γ t) = dist x y/2 at htt
  refine ⟨γ t,htt,?_⟩
  have hpre := riemannianEDist_le_pathELength (I := I)
    (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
  have hpost := riemannianEDist_le_pathELength (I := I)
    (hγ.mono (Icc_subset_Icc ht.1 le_rfl)) rfl hγ1 ht.2
  have hsum : ENNReal.ofReal (dist x (γ t)+dist (γ t) y) <
      ENNReal.ofReal (dist x y+eps) := by
    rw [ENNReal.ofReal_add dist_nonneg dist_nonneg]
    rw [← IsRiemannianManifold.out,edist_dist] at hpre hpost
    exact (add_le_add hpre hpost).trans_lt ((pathELength_add ht.1 ht.2).trans_lt hlen)
  have hsumR : dist x (γ t)+dist (γ t) y < dist x y+eps :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hsum
  rw [htt] at hsumR
  linarith

lemma riemannian_exists_midpoint [CompactSpace M] (x y : M) :
    ∃ z : M, dist x z = dist x y/2 ∧ dist z y = dist x y/2 := by
  let F : M → ℝ := fun z => max (dist x z) (dist z y)
  have hc : Continuous F := by fun_prop
  obtain ⟨z,_,hz⟩ := isCompact_univ.exists_isMinOn ⟨x,mem_univ x⟩ hc.continuousOn
  have hF : F z ≤ dist x y/2 := by
    by_contra hn
    have hp : 0 < F z-dist x y/2 := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨w,hwx,hwy⟩ := riemannian_approximate_midpoint (I := I) x y (half_pos hp)
    have hw : F w < F z := by
      dsimp [F]
      apply max_lt
      · rw [hwx]; linarith
      · linarith
    exact (not_lt_of_ge (hz (mem_univ w))) hw
  have hx := (le_max_left (dist x z) (dist z y)).trans hF
  have hy := (le_max_right (dist x z) (dist z y)).trans hF
  have htri := dist_triangle x z y
  exact ⟨z,by linarith,by linarith⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GlobalGauss
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

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma contMDiff_fiber_line (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) :
    ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun s : ℝ => (⟨x,v+s • w⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  intro s
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const,?_⟩
  let e := trivializationAt E (fun y : M => TangentSpace 𝓘(ℝ,E) y) x
  let L : TangentSpace 𝓘(ℝ,E) x →L[ℝ] E := e.continuousLinearMapAt ℝ x
  have heq : (fun r : ℝ => (e (⟨x,v+r • w⟩ : TangentBundle 𝓘(ℝ,E) M)).2) =
      (fun r : ℝ => L (v+r • w)) := by
    funext r
    exact (e.continuousLinearMapAt_apply_of_mem ℝ (mem_baseSet_trivializationAt E _ x) _).symm
  change ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun r : ℝ => (e ⟨x,v+r • w⟩).2) s
  rw [heq]
  exact (L.contDiff.comp (contDiff_const.add (contDiff_id.smul contDiff_const))).contDiffAt.contMDiffAt

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_Hessian
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma localMin_hessian_nonneg {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMin f x) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let L : ℝ → E := fun t => x+t • v
  have hL (t : ℝ) : HasDerivAt L v t := by
    convert! (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hL0 : L 0 = x := by simp [L]
  have hcont : ContinuousAt (fun t => f (L t)) 0 := by
    apply ContinuousAt.comp _ (hL 0).continuousAt
    simpa only [hL0] using hf.continuousAt
  have hmin : IsLocalMin (fun t => f (L t)) 0 :=
    (show IsLocalMin f (L 0) by rwa [hL0]).comp_continuous (hL 0).continuousAt
  have heq : deriv (fun t => f (L t)) =ᶠ[𝓝 (0:ℝ)]
      fun t => fderiv ℝ f (L t) v := by
    have hnear : ∀ᶠ t in 𝓝 (0:ℝ), ContDiffAt ℝ 2 f (L t) := by
      apply (show Tendsto L (𝓝 0) (𝓝 x) by simpa only [ContinuousAt,hL0] using (hL 0).continuousAt).eventually
      exact hf.eventually (by norm_num)
    filter_upwards [hnear] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hL t)).deriv
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd : HasDerivAt (fun t => fderiv ℝ f (L t) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (L 0) := by
      rw [hL0]; exact hdf.hasFDerivAt
    have hd0 := (hfd.comp_hasDerivAt 0 (hL 0)).clm_apply (hasDerivAt_const 0 v)
    convert! hd0 using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hh := localMin_second_deriv_nonneg hmin hcont
  rwa [heq.deriv_eq,hd.deriv] at hh

lemma symmetric_nonneg_bilinear_null {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hs : ∀ u v, B u v = B v u) (hp : ∀ u, 0 ≤ B u u)
    {v : E} (hv : B v v = 0) (w : E) : B v w = 0 := by
  let f : ℝ → ℝ := fun t => B (v+t • w) (v+t • w)
  have hmin : IsLocalMin f 0 := by
    filter_upwards [] with t
    simpa only [f,zero_smul,add_zero,hv] using hp (v+t • w)
  have heq : f = fun t => 2*t*(B v w)+t^2*(B w w) := by
    funext t
    simp only [f,map_add,map_smul,add_apply,smul_apply,smul_eq_mul,hv,hs w v]
    ring
  have hd : HasDerivAt f (2*B v w) 0 := by
    rw [heq]
    convert! (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const (B v w)).add
      (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (B w w)) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hh := hmin.hasDerivAt_eq_zero hd
  linarith

lemma localMin_hessian_null {f : E → ℝ} {x v : E}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMin f x)
    (hv : fderiv ℝ (fderiv ℝ f) x v v = 0) (w : E) :
    fderiv ℝ (fderiv ℝ f) x v w = 0 := by
  exact symmetric_nonneg_bilinear_null
    (hf.isSymmSndFDerivAt (by simp)).eq (localMin_hessian_nonneg hf hm) hv w

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_GeneratingKernel
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma localMin_generating_kernel {B : E×F → ℝ} {Q : E → F} {p w : E}
    (hB : ContDiffAt ℝ 2 B (p,Q p)) (hmin : IsLocalMin B (p,Q p))
    (hQ : DifferentiableAt ℝ Q p)
    (hstat : ∀ᶠ v in 𝓝 p, ∀ a : E, fderiv ℝ B (v,Q v) (a,0) = 0)
    (hker : fderiv ℝ Q p w = 0) :
    fderiv ℝ (fderiv ℝ B) (p,Q p) (w,0) = 0 := by
  let G : E → E×F := fun v => (v,Q v)
  let G' : E →L[ℝ] E×F := (ContinuousLinearMap.id ℝ E).prod (fderiv ℝ Q p)
  have hG : HasFDerivAt G G' p := (hasFDerivAt_id p).prodMk hQ.hasFDerivAt
  have hDB : HasFDerivAt (fderiv ℝ B) (fderiv ℝ (fderiv ℝ B) (p,Q p)) (G p) :=
    ((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hd := ((hDB.comp p hG).clm_apply (hasFDerivAt_const (w,(0:F)) p)).fderiv
  have heq : (fun v => fderiv ℝ B (G v) (w,0)) =ᶠ[𝓝 p] fun _ => (0:ℝ) :=
    hstat.mono (fun _ hv => hv w)
  have hzero : fderiv ℝ (fun v => fderiv ℝ B (G v) (w,0)) p = 0 := by
    rw [heq.fderiv_eq]; exact fderiv_const_apply (0:ℝ)
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L w) (hzero.symm.trans hd)
  have hdiag : fderiv ℝ (fderiv ℝ B) (p,Q p) (w,0) (w,0) = 0 := by
    simpa [G',hker] using hh.symm
  apply ContinuousLinearMap.ext
  intro u
  exact localMin_hessian_null hB hmin hdiag u

lemma localMin_generating_cotangent_kernel {B : E×F → ℝ} {Q : E → F} {p w : E}
    (hB : ContDiffAt ℝ 2 B (p,Q p)) (hmin : IsLocalMin B (p,Q p))
    (hQ : DifferentiableAt ℝ Q p)
    (hstat : ∀ᶠ v in 𝓝 p, ∀ a : E, fderiv ℝ B (v,Q v) (a,0) = 0)
    (hker : fderiv ℝ Q p w = 0) (u : F) :
    fderiv ℝ (fun v => fderiv ℝ B (v,Q v) (0,u)) p w = 0 := by
  have hdB : DifferentiableAt ℝ (fderiv ℝ B) (p,Q p) :=
    (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := ((hdB.hasFDerivAt.comp p
    ((hasFDerivAt_id p).prodMk hQ.hasFDerivAt)).clm_apply
      (hasFDerivAt_const ((0:E),u) p)).fderiv
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L w) hd
  simpa [hker,localMin_generating_kernel hB hmin hQ hstat hker] using hh

end WeakMTWTransport

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

lemma weighted_square_le (a b : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0<t) :
    (a+b)^2/(s+t) ≤ a^2/s+b^2/t := by
  rw [div_add_div _ _ hs.ne' ht.ne']
  apply (div_le_div_iff₀ (add_pos hs ht) (mul_pos hs ht)).mpr
  nlinarith [sq_nonneg (t*a-s*b)]

lemma three_leg_energy_le {M : Type*} [PseudoMetricSpace M]
    (x b q y : M) {L ε r : ℝ} (hL : 0<L) (hε : 0<ε)
    (hb : dist x b ≤ L*r) :
    dist x y^2/(2*(L+2*ε)) ≤ L*r^2/2 + dist b q^2/(2*ε) + dist q y^2/(2*ε) := by
  have htri : dist x y ≤ L*r+(dist b q+dist q y) :=
    (dist_triangle x b y).trans (add_le_add hb (dist_triangle b q y))
  have hsq : dist x y^2 ≤ (L*r+(dist b q+dist q y))^2 := by
    nlinarith [dist_nonneg (x := x) (y := y)]
  have h₁ := weighted_square_le (L*r) (dist b q+dist q y) hL (by linarith : 0<2*ε)
  have h₂ := weighted_square_le (dist b q) (dist q y) hε hε
  have he : (L*r)^2/L = L*r^2 := by field_simp
  rw [he] at h₁
  have h₂' : (dist b q+dist q y)^2/(2*ε) ≤ dist b q^2/ε+dist q y^2/ε := by
    simpa only [two_mul] using h₂
  have hh := (div_le_div_of_nonneg_right hsq (show 0≤L+2*ε by positivity)).trans
    (h₁.trans (add_le_add le_rfl h₂'))
  have hh' := div_le_div_of_nonneg_right hh (show (0:ℝ)≤2 by norm_num)
  calc
    dist x y^2/(2*(L+2*ε)) = (dist x y^2/(L+2*ε))/2 := by rw [div_div,mul_comm]
    _ ≤ (L*r^2+(dist b q^2/ε+dist q y^2/ε))/2 := hh'
    _ = _ := by field_simp <;> ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_InteriorCompactUniqueFiber
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport

lemma interior_of_compact_unique_fiber {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y} {C : Set X} {x : X}
    (hC : IsCompact C) (hf : Continuous f)
    (hs : ∀ y, ∃ q ∈ C, f q = y)
    (hu : ∀ q ∈ C, f q = f x → q = x)
    (hi : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U) : x ∈ interior C := by
  obtain ⟨U,hU,hxU,hUinj⟩ := hi
  have hclosed : IsClosed (f '' (C \ U)) := ((hC.diff hU).image hf).isClosed
  have hxnot : f x ∉ f '' (C \ U) := by
    rintro ⟨q,hq,hqx⟩
    exact hq.2 (hu q hq.1 hqx ▸ hxU)
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hU.mem_nhds hxU,
    hf.continuousAt.preimage_mem_nhds (hclosed.isOpen_compl.mem_nhds hxnot)] with v hv hvf
  obtain ⟨q,hq,hqv⟩ := hs (f v)
  have hqU : q ∈ U := by
    by_contra hqU
    exact hvf ⟨q,⟨hq,hqU⟩,hqv⟩
  exact hUinj hqU hv hqv ▸ hq

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_DividedAction
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
variable {M : Type*} [PseudoMetricSpace M]

lemma squared_dist_divided_action_le (x y z : M) {s : ℝ} (hs : 0 < s) (hs1 : s<1) :
    dist x z^2/2 ≤ dist x y^2/(2*s) + dist y z^2/(2*(1-s)) := by
  have hns : 1-s ≠ 0 := (sub_pos.mpr hs1).ne'
  have htri := dist_triangle x y z
  have hab := dist_nonneg (x := x) (y := y)
  have hbc := dist_nonneg (x := y) (y := z)
  have hac := dist_nonneg (x := x) (y := z)
  have ht : dist x z^2 ≤ (dist x y+dist y z)^2 := by nlinarith
  have hc : (dist x y+dist y z)^2 ≤ dist x y^2/s + dist y z^2/(1-s) := by
    rw [div_add_div _ _ hs.ne' hns]
    apply (le_div_iff₀ (mul_pos hs (sub_pos.mpr hs1))).mpr
    nlinarith [sq_nonneg ((1-s)*dist x y-s*dist y z)]
  calc
    dist x z^2/2 ≤ (dist x y+dist y z)^2/2 := div_le_div_of_nonneg_right ht (by norm_num)
    _ ≤ (dist x y^2/s+dist y z^2/(1-s))/2 := div_le_div_of_nonneg_right hc (by norm_num)
    _ = _ := by field_simp [hs.ne',hns]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_HessianSmooth
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
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma iteratedDeriv_two_affine_line {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v : E) :
    iteratedDeriv 2 (fun t : ℝ => f (x+t • v)) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  let L : ℝ → E := fun t => x+t • v
  have hL (t : ℝ) : HasDerivAt L v t := by
    convert! (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hL0 : L 0=x := by simp [L]
  have hLc : ContDiffAt ℝ 2 L 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hL2 : iteratedDeriv 2 L 0=0 := by
    rw [iteratedDeriv_succ,iteratedDeriv_one]
    have heq : deriv L=fun _ => v := funext (fun t => (hL t).deriv)
    rw [heq,deriv_const]
  have hf' : ContDiffAt ℝ 2 f (L 0) := by rwa [hL0]
  have H := iteratedDeriv_vcomp_two hf' hLc
  simpa only [Function.comp_def,hL0,(hL 0).deriv,hL2,map_zero,add_zero,
    iteratedFDeriv_two_apply] using H

lemma directional_fderiv_hasDerivAt {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x+t • v) w)
      (fderiv ℝ (fderiv ℝ f) x v w) 0 := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    convert! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x+(0:ℝ) • v) := by
    simpa only [zero_smul,add_zero] using hdf.hasFDerivAt
  have hd := (hd'.comp_hasDerivAt (f := fun t : ℝ => x+t • v) 0 hline).clm_apply (hasDerivAt_const 0 w)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp

lemma positive_schur_test {a b q A : ℝ} (hq : 0<q)
    (ht : ∀ t : ℝ, A ≤ a+2*t*b+t^2*q) : A ≤ a-b^2/q := by
  have H := ht (-b/q)
  have heq : a+2*(-b/q)*b+(-b/q)^2*q=a-b^2/q := by field_simp <;> ring
  rwa [heq] at H

lemma nonzero_pairing_positive_test {a b q A : ℝ} (hq : 0≤q) (hb : b≠0)
    (ht : ∀ t : ℝ, A≤a+2*t*b+t^2*q) : 0<q := by
  by_contra hn
  have h0 : q=0 := le_antisymm (le_of_not_gt hn) hq
  have H := ht ((A-a-1)/(2*b))
  rw [h0,mul_zero,add_zero] at H
  have he : a+2*((A-a-1)/(2*b))*b=A-1 := by field_simp <;> ring
  rw [he] at H
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SchurEnvelope
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma upper_contact_block_trial {f : E → ℝ} {B : E×F → ℝ} {x : E} {q : F}
    (hf : ContDiffAt ℝ 2 f x) (hB : ContDiffAt ℝ 2 B (x,q))
    (hle : ∀ᶠ z in 𝓝 (x,q), f z.1≤B z) (heq : f x=B (x,q))
    (v : E) (k : F) (t : ℝ) :
    fderiv ℝ (fderiv ℝ f) x v v ≤
      fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (v,0) +
      2*t*fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (0,k) +
      t^2*fderiv ℝ (fderiv ℝ B) (x,q) (0,k) (0,k) := by
  let L : ℝ → E×F := fun s => (x,q)+s • (v,t • k)
  have hLc : ContDiffAt ℝ 2 L 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hL0 : L 0=(x,q) := by simp [L]
  have hLlim : Tendsto L (𝓝 0) (𝓝 (x,q)) := by
    simpa only [hL0] using hLc.continuousAt.tendsto
  have hBc : ContDiffAt ℝ 2 (B ∘ L) 0 := by
    have hB' : ContDiffAt ℝ 2 B (L 0) := by rwa [hL0]
    exact hB'.comp 0 hLc
  have hfc : ContDiffAt ℝ 2 (fun s : ℝ => f (x+s • v)) 0 := by
    have hf' : ContDiffAt ℝ 2 f (x+(0:ℝ) • v) := by simpa only [zero_smul,add_zero] using hf
    exact hf'.comp 0 (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hle' : ∀ᶠ s : ℝ in 𝓝 0, f (x+s • v) ≤ (B ∘ L) s :=
    hLlim.eventually hle
  have heq' : f (x+(0:ℝ) • v)=(B ∘ L) 0 := by simpa only [Function.comp_apply,hL0,zero_smul,add_zero] using heq
  have H := upper_contact_iteratedDeriv_two hfc hBc hle' heq'
  change iteratedDeriv 2 (fun s : ℝ => f (x+s • v)) 0 ≤
    iteratedDeriv 2 (fun s : ℝ => B ((x,q)+s • (v,t • k))) 0 at H
  rw [iteratedDeriv_two_affine_line hf,iteratedDeriv_two_affine_line hB] at H
  have hv : (v,t • k)=(v,0)+t • ((0:E),k) := by ext <;> simp
  have hs := (hB.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eq ((0:E),k) (v,(0:F))
  rw [hv] at H
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul] at H
  rw [hs] at H
  nlinarith

lemma upper_contact_block_nonneg {f : E → ℝ} {B : E×F → ℝ} {x : E} {q : F}
    (hf : ContDiffAt ℝ 2 f x) (hB : ContDiffAt ℝ 2 B (x,q))
    (hle : ∀ᶠ z in 𝓝 (x,q), f z.1≤B z) (heq : f x=B (x,q)) (k : F) :
    0≤fderiv ℝ (fderiv ℝ B) (x,q) (0,k) (0,k) := by
  simpa only [show ((0:E),(0:F))=(0:E×F) from rfl, map_zero, zero_apply, one_mul,
    zero_add, one_pow, mul_zero] using upper_contact_block_trial hf hB hle heq 0 k 1

lemma upper_contact_block_positive {f : E → ℝ} {B : E×F → ℝ} {x : E} {q : F}
    (hf : ContDiffAt ℝ 2 f x) (hB : ContDiffAt ℝ 2 B (x,q))
    (hle : ∀ᶠ z in 𝓝 (x,q), f z.1≤B z) (heq : f x=B (x,q)) (v : E) (k : F)
    (hk : fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (0,k)≠0) :
    0<fderiv ℝ (fderiv ℝ B) (x,q) (0,k) (0,k) :=
  nonzero_pairing_positive_test (upper_contact_block_nonneg hf hB hle heq k) hk
    (upper_contact_block_trial hf hB hle heq v k)

lemma upper_contact_block_schur {f : E → ℝ} {B : E×F → ℝ} {x : E} {q : F}
    (hf : ContDiffAt ℝ 2 f x) (hB : ContDiffAt ℝ 2 B (x,q))
    (hle : ∀ᶠ z in 𝓝 (x,q), f z.1≤B z) (heq : f x=B (x,q)) (v : E) (k : F)
    (hk : fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (0,k)≠0) :
    fderiv ℝ (fderiv ℝ f) x v v ≤
      fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (v,0) -
      (fderiv ℝ (fderiv ℝ B) (x,q) (v,0) (0,k))^2/
        fderiv ℝ (fderiv ℝ B) (x,q) (0,k) (0,k) :=
  positive_schur_test (upper_contact_block_positive hf hB hle heq v k hk)
    (upper_contact_block_trial hf hB hle heq v k)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_DiagonalKernel
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
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma diagonal_stationary_hessian_null {F : E×E → ℝ} {p k : E}
    (hF : ContDiffAt ℝ 2 F (p,p))
    (hstat : ∀ᶠ v in 𝓝 p, fderiv ℝ F (v,v) (0,k)=0)
    (hker : ∀ᶠ v in 𝓝 p, fderiv ℝ F (p,v) (k,0)=0) :
    fderiv ℝ (fderiv ℝ F) (p,p) (0,k) (0,k)=0 := by
  have hdf := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let L : E →L[ℝ] E×E := (ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)
  have hD₁ := ((hdf.hasFDerivAt.comp (f := fun v : E => (v,v)) p L.hasFDerivAt).clm_apply
    (hasFDerivAt_const ((0:E),k) p)).fderiv
  have hz₁ : fderiv ℝ (fun v : E => fderiv ℝ F (v,v) (0,k)) p=0 := by
    have heq : (fun v : E => fderiv ℝ F (v,v) (0,k)) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := hstat
    rw [heq.fderiv_eq]
    exact (hasFDerivAt_const (0:ℝ) p).fderiv
  have hd₁ := congrArg (fun A : E →L[ℝ] ℝ => A k) (hD₁.symm.trans hz₁)
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply,L,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply] at hd₁
  have hL₂ : HasFDerivAt (fun v : E => (p,v))
      ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) p :=
    (hasFDerivAt_const p p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hD₂ := ((hdf.hasFDerivAt.comp (f := fun v : E => (p,v)) p hL₂).clm_apply
    (hasFDerivAt_const (k,(0:E)) p)).fderiv
  have hz₂ : fderiv ℝ (fun v : E => fderiv ℝ F (p,v) (k,0)) p=0 := by
    have heq : (fun v : E => fderiv ℝ F (p,v) (k,0)) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := hker
    rw [heq.fderiv_eq]
    exact (hasFDerivAt_const (0:ℝ) p).fderiv
  have hd₂ := congrArg (fun A : E →L[ℝ] ℝ => A k) (hD₂.symm.trans hz₂)
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply] at hd₂
  rw [(hF.isSymmSndFDerivAt (by simp)).eq] at hd₂
  have heq : (k,k)=(k,0)+((0:E),k) := by ext <;> simp
  rw [heq,map_add,add_apply,hd₂,zero_add] at hd₁
  exact hd₁
end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SecondScaled
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma second_fderiv_scaled_differences {f g : E → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) (a b : ℝ) (v : E) :
    fderiv ℝ (fderiv ℝ (fun h => a*(f h-f 0)-b*(g h-g 0))) 0 v v =
      a*fderiv ℝ (fderiv ℝ f) 0 v v-b*fderiv ℝ (fderiv ℝ g) 0 v v := by
  have hline : ContDiffAt ℝ 2 (fun t : ℝ => (0:E)+t • v) 0 := by fun_prop
  have hfl : ContDiffAt ℝ 2 (fun t : ℝ => f ((0:E)+t • v)) 0 :=
    (show ContDiffAt ℝ 2 f ((0:E)+(0:ℝ) • v) by simpa using hf).comp 0 hline
  have hgl : ContDiffAt ℝ 2 (fun t : ℝ => g ((0:E)+t • v)) 0 :=
    (show ContDiffAt ℝ 2 g ((0:E)+(0:ℝ) • v) by simpa using hg).comp 0 hline
  have hF : ContDiffAt ℝ 2 (fun h => a*(f h-f 0)-b*(g h-g 0)) 0 :=
    (contDiffAt_const.mul (hf.sub contDiffAt_const)).sub (contDiffAt_const.mul (hg.sub contDiffAt_const))
  rw [←iteratedDeriv_two_affine_line hF v,
    iteratedDeriv_fun_sub (contDiffAt_const.mul (hfl.sub contDiffAt_const))
      (contDiffAt_const.mul (hgl.sub contDiffAt_const)),
    iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sub hfl contDiffAt_const,iteratedDeriv_fun_sub hgl contDiffAt_const]
  simp only [iteratedDeriv_const,ite_false, if_false,show (2:ℕ)≠0 by norm_num,sub_zero,
    iteratedDeriv_two_affine_line hf v,iteratedDeriv_two_affine_line hg v]

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

lemma cost_lipschitz_of_distance_bound {D : ℝ}
    (hD : ∀ x y : M, dist x y ≤ D) (x x' y : M) :
    |cost x y - cost x' y| ≤ D * dist x x' := by
  have htri := abs_dist_sub_le x x' y
  have hsum : 0 ≤ dist x y + dist x' y := by positivity
  have hprod := mul_le_mul htri (show dist x y + dist x' y ≤ 2 * D by
      linarith [hD x y, hD x' y]) hsum (dist_nonneg : 0 ≤ dist x x')
  rw [cost, cost]
  have heq : dist x y ^ 2 / 2 - dist x' y ^ 2 / 2 =
      (dist x y - dist x' y) * (dist x y + dist x' y) / 2 := by ring
  rw [heq, abs_div, abs_mul, abs_of_nonneg hsum]
  norm_num
  linarith

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalSubdifferential
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport

lemma hasFDerivAt_affine_lower_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {D : E →L[ℝ] ℝ} (hD : HasFDerivAt f D 0) :
    ∀ ε>0, ∀ᶠ h : E in 𝓝 0, D h-ε*‖h‖≤f h-f 0 := by
  intro ε hε
  have H := hD.isLittleO.bound hε
  filter_upwards [H] with h hh
  simp only [sub_zero,Real.norm_eq_abs] at hh
  linarith [(abs_le.mp hh).1]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ContDiffQuadraticUpper
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma contDiffAt_quadratic_upper {f : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (hf0 : f 0=0) (hd0 : deriv f 0=0) :
    ∃ eps C : ℝ, 0<eps ∧ 0<C ∧ ∀ s ∈ Ioo 0 eps, f s≤C*s^2 := by
  obtain ⟨K,U,hU,hLip⟩ := (hf.derivWithin (m := 1) (by norm_num)).exists_lipschitzOnWith
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ f s :=
    (hf.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hnear)
  refine ⟨eps,(K:ℝ)+1,heps,by positivity,?_⟩
  intro s hs
  have hsub : Icc 0 s ⊆ Metric.ball (0:ℝ) eps := by
    intro r hr
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hr.1] using hr.2.trans_lt hs.2
  have hzero : (0:ℝ) ∈ U := (hball (Metric.mem_ball_self heps)).1
  have hbound : ∀ r ∈ Icc 0 s, ‖deriv f r‖ ≤ (K:ℝ)*s := by
    intro r hr
    have H := hLip.dist_le_mul r (hball (hsub hr)).1 0 hzero
    have H' : ‖deriv f r‖ ≤ (K:ℝ)*r := by
      simpa only [hd0,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hr.1] using H
    exact H'.trans (mul_le_mul_of_nonneg_left hr.2 K.coe_nonneg)
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun r hr => (hball (hsub hr)).2) hbound (convex_Icc (0:ℝ) s)
    (left_mem_Icc.mpr hs.1.le) (right_mem_Icc.mpr hs.1.le)
  have H' : |f s|≤(K:ℝ)*s^2 := by
    simpa only [hf0,sub_zero,Real.norm_eq_abs,abs_of_pos hs.1,pow_two,mul_assoc] using H
  exact (le_abs_self (f s)).trans (H'.trans (by nlinarith [sq_nonneg s]))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_CurvedQuadratic
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_curved_quadratic_upper {Q : E → ℝ} {p e : E}
    (hQ : ContDiffAt ℝ 2 Q p) (hQ0 : Q p=0)
    (hmin : ∀ᶠ s : ℝ in 𝓝 0, 0≤Q (p+s • e)) :
    ∃ eps C : ℝ, 0<eps ∧ 0<C ∧ ∀ s ∈ Ioo 0 eps,
      Q ((1-s^2) • (p+s • e))≤C*s^2 := by
  have hl : HasDerivAt (fun s : ℝ => p+s • e) e 0 := by
    convert! (hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const e) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hQ' : HasFDerivAt Q (fderiv ℝ Q p) (p+(0:ℝ) • e) := by
    simpa only [zero_smul,add_zero] using (hQ.differentiableAt (by norm_num)).hasFDerivAt
  have hlocal : IsLocalMin (fun s : ℝ => Q (p+s • e)) 0 := by
    change ∀ᶠ s : ℝ in 𝓝 0, Q (p+(0:ℝ) • e) ≤ Q (p+s • e)
    simpa only [zero_smul,add_zero,hQ0] using hmin
  have hderivzero : fderiv ℝ Q p e=0 :=
    hlocal.hasDerivAt_eq_zero (hQ'.comp_hasDerivAt (f := fun s : ℝ => p+s • e) 0 hl)
  let L : ℝ → E := fun s => (1-s^2) • (p+s • e)
  have hL0 : L 0=p := by simp [L]
  have hL : HasDerivAt L e 0 := by
    convert! ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub ((hasDerivAt_id (0:ℝ)).pow 2)).smul hl using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hLc : ContDiffAt ℝ 2 L 0 := by dsimp [L]; fun_prop
  have hQc : ContDiffAt ℝ 2 (Q ∘ L) 0 := by
    have hQ' : ContDiffAt ℝ 2 Q (L 0) := by rwa [hL0]
    exact hQ'.comp 0 hLc
  have hqd : HasDerivAt (Q ∘ L) 0 0 := by
    have hd : HasFDerivAt Q (fderiv ℝ Q p) (L 0) := by
      simpa only [hL0] using (hQ.differentiableAt (by norm_num)).hasFDerivAt
    simpa only [hderivzero,Function.comp_def] using hd.comp_hasDerivAt (f := L) 0 hL
  exact contDiffAt_quadratic_upper (f := Q ∘ L) hQc (by change Q (L 0)=0; rw [hL0,hQ0]) hqd.deriv
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SchurRatioTendstoBot
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

namespace WeakMTWTransport

lemma schur_ratio_tendsto_atBot {α : Type*} {l : Filter α} {f a Q : α → ℝ} {A c : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hQ : Tendsto Q l (𝓝 0)) (hc : 0 < c)
    (hpos : ∀ᶠ r in l, 0<Q r) (hupper : ∀ᶠ r in l, f r≤a r-c/Q r) :
    Tendsto f l atBot := by
  apply tendsto_atBot.mpr
  intro B
  let D := |A+1-B|+1
  have hD : 0<D := by dsimp [D] <;> positivity
  have hQB := hQ.eventually_lt_const (div_pos hc hD)
  have haB := ha.eventually_lt_const (show A<A+1 by linarith)
  filter_upwards [hQB,haB,hpos,hupper] with r hrQ hra hrp hru
  have hmul : D*Q r < c := by nlinarith [(lt_div_iff₀ hD).mp hrQ]
  have hdiv : D < c/Q r := (lt_div_iff₀ hrp).mpr hmul
  have hdom : A+1-B<D := by dsimp [D] <;> linarith [le_abs_self (A+1-B)]
  linarith
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_FirstCutSegment
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma kernel_parallel_of_transverse_orthogonal_ne_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e k : E} (he : e ≠ 0)
    (hk : ∀ xi : E, inner ℝ xi e=0 → inner ℝ xi k=0) :
    k=(inner ℝ k e / inner ℝ e e) • e := by
  have hee : inner ℝ e e ≠ 0 := inner_self_ne_zero.mpr he
  let xi := k-(inner ℝ k e / inner ℝ e e) • e
  have hxi : inner ℝ xi e=0 := by
    dsimp [xi]
    simp only [inner_sub_left,real_inner_smul_left,div_mul_cancel₀ _ hee,sub_self]
  have hxik := hk xi hxi
  have hxixi : inner ℝ xi xi=0 := by
    change inner ℝ xi (k-(inner ℝ k e / inner ℝ e e) • e)=0
    simp only [inner_sub_right,real_inner_smul_right,hxik,hxi,mul_zero,sub_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hxixi)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_LocalMinStrictGrowth
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport

lemma exists_local_min_of_strict_growth {X P : Type*} [MetricSpace X] [ProperSpace X]
    [TopologicalSpace P] {F : X → P → ℝ} (hF : Continuous (fun q : X×P => F q.1 q.2))
    {x : X} {p : P} (H : ∀ᶠ z in 𝓝 x, z≠x → F x p<F z p) :
    ∀ O ∈ 𝓝 x, ∀ᶠ q in 𝓝 p, ∃ z∈O, IsLocalMin (fun w => F w q) z := by
  intro O hO
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hO H)
  obtain ⟨s,hs,hsr⟩ := exists_between hr
  have Hs : ∀ z∈Metric.sphere x s, F x p<F z p := by
    intro z hz
    have hd : dist z x=s := hz
    exact (hball (by simpa only [Metric.mem_ball,hd] using hsr)).2
      (by intro he; subst z; simp only [dist_self] at hd <;> linarith)
  have He : ∀ᶠ q in 𝓝 p, ∀ z∈Metric.sphere x s, F x q<F z q := by
    apply (isCompact_sphere x s).eventually_forall_of_forall_eventually
    intro z hz
    have hopen : IsOpen {a : P×X | F x a.1<F a.2 a.1} :=
      isOpen_lt (hF.comp (continuous_const.prodMk continuous_fst))
        (hF.comp (continuous_snd.prodMk continuous_fst))
    exact hopen.mem_nhds (show (p,z) ∈ {a : P×X | F x a.1<F a.2 a.1} from Hs z hz)
  filter_upwards [He] with q hq
  obtain ⟨z,hz,hmin⟩ := Metric.exists_isLocalMin_mem_ball
    (a := x) (r := s) (z := x) (hF.comp (continuous_id.prodMk continuous_const)).continuousOn
    (by simpa using hs.le) hq
  exact ⟨z,(hball ((Metric.ball_subset_ball hsr.le) hz)).1,hmin⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ContDiffParametricSecant
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma contDiffAt_parametric_secant_lower {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E×ℝ → ℝ} {x : E}
    (hF : ContDiffAt ℝ 1 F (x,0)) {K : ℝ}
    (hK : K < fderiv ℝ F (x,0) (0,1)) :
    ∀ᶠ q : E×ℝ in 𝓝 (x,0), 0≤q.2 → K*q.2≤F q-F (q.1,0) := by
  have hd : ContinuousAt (fun q : E×ℝ => fderiv ℝ F q (0,1)) (x,0) :=
    (hF.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have H : ∀ᶠ q : E×ℝ in 𝓝 (x,0), ContDiffAt ℝ 1 F q ∧ K<fderiv ℝ F q (0,1) :=
    (hF.eventually (by norm_num)).and (hd.preimage_mem_nhds (Ioi_mem_nhds hK))
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp H
  obtain ⟨δ,hδ,hδV⟩ := Metric.mem_nhds_iff.mp hV
  have hnear : U ×ˢ Metric.ball (0:ℝ) δ ∈ 𝓝 (x,0) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hU (Metric.ball_mem_nhds (0:ℝ) hδ)
  filter_upwards [hnear] with q hq ht
  have hqt : q.2<δ := (le_abs_self q.2).trans_lt (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hq.2)
  have Hj : ∀ r∈Icc 0 q.2, ContDiffAt ℝ 1 F (q.1,r) ∧ K<fderiv ℝ F (q.1,r) (0,1) := by
    intro r hr
    exact hUV ⟨hq.1,hδV (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hr.1] using hr.2.trans_lt hqt)⟩
  have hD : ∀ r∈Icc 0 q.2, HasDerivAt (fun r => F (q.1,r))
      (fderiv ℝ F (q.1,r) (0,1)) r := by
    intro r hr
    exact ((Hj r hr).1.differentiableAt_one.hasFDerivAt).comp_hasDerivAt r
      ((hasDerivAt_const r q.1).prodMk (hasDerivAt_id r))
  rcases ht.eq_or_lt with he|ht
  · have hqeq : q = (q.1, 0) := by ext <;> simp [←he]
    rw [hqeq]
    simp
  obtain ⟨r,hr,he⟩ := exists_hasDerivAt_eq_slope (fun r => F (q.1,r))
    (fun r => fderiv ℝ F (q.1,r) (0,1)) ht
    (fun r hr => (hD r hr).continuousAt.continuousWithinAt)
    (fun r hr => hD r ⟨hr.1.le,hr.2.le⟩)
  have hk := (Hj r ⟨hr.1.le,hr.2.le⟩).2.le
  rw [he,sub_zero] at hk
  exact (le_div_iff₀ ht).mp hk

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_PrecutExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

lemma eventually_injective_of_uniform_local_injective
    {P X Y Z : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace X] [TopologicalSpace Y] [T2Space Y] [PseudoMetricSpace Z]
    (F : P → X → Y) (hF : Continuous (fun p : P × X => F p.1 p.2))
    (q : X → Z) (hq : Continuous q) {T : P} {δ : ℝ} (hδ : 0<δ)
    (hT : Function.Injective (F T))
    (hloc : ∀ᶠ t in 𝓝 T, ∀ x y, dist (q x) (q y)<δ → F t x=F t y → x=y) :
    ∀ᶠ t in 𝓝 T, Function.Injective (F t) := by
  have hopen : IsOpen {p : P × (X × X) |
      dist (q p.2.1) (q p.2.2)<δ ∨ F p.1 p.2.1 ≠ F p.1 p.2.2} :=
    (isOpen_lt ((hq.comp (continuous_fst.comp continuous_snd)).dist
      (hq.comp (continuous_snd.comp continuous_snd))) continuous_const).union
      (isOpen_ne_fun (hF.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
        (hF.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  have hfar : ∀ᶠ t in 𝓝 T, ∀ xy ∈ (univ : Set (X×X)),
      dist (q xy.1) (q xy.2)<δ ∨ F t xy.1 ≠ F t xy.2 := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro xy _
    apply hopen.mem_nhds
    by_cases hxy : xy.1=xy.2
    · exact Or.inl (by simpa only [hxy,dist_self] using hδ)
    · exact Or.inr (fun he => hxy (hT he))
  filter_upwards [hloc,hfar] with t ht hf x y he
  rcases hf (x,y) (mem_univ _) with hclose | hne
  · exact ht x y hclose he
  · exact (hne he).elim

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Duality_CompactDual
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

def dualObjective (mu nu : Measure M) (uv : (M →ᵇ ℝ) × (M →ᵇ ℝ)) : ℝ :=
  (∫ x, uv.1 x ∂mu) + ∫ y, uv.2 y ∂nu

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_Calculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma first_order_remainder_le_of_hessian_bound {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) {B : ℝ} (hB : 0≤B)
    (hf : ∀ z∈S, ContDiffAt ℝ 2 f z)
    (hbound : ∀ z∈S, ‖fderiv ℝ (fderiv ℝ f) z‖≤B)
    {x y : E} (hx : x∈S) (hy : y∈S) :
    |f y-f x-fderiv ℝ f x (y-x)|≤B*‖y-x‖^2 := by
  have hD : ∀ z∈S, HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z := by
    intro z hz
    exact ((hf z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hLip : ∀ z∈S, ‖fderiv ℝ f z-fderiv ℝ f x‖≤B*‖z-x‖ := by
    intro z hz
    exact hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun w hw => (hD w hw).hasFDerivWithinAt) hbound hx hz
  let R := fun z => f z-f x-fderiv ℝ f x (z-x)
  have hR : ∀ z∈S, HasFDerivAt R (fderiv ℝ f z-fderiv ℝ f x) z := by
    intro z hz
    exact ((hf z hz).differentiableAt (by norm_num)).hasFDerivAt.sub_const (f x) |>.sub
      ((fderiv ℝ f x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
  have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hn : ∀ z∈segment ℝ x y, ‖z-x‖≤‖y-x‖ := by
    intro z hz
    simpa only [Metric.mem_closedBall,dist_eq_norm] using
      (show segment ℝ x y ⊆ Metric.closedBall x ‖y-x‖ from
      (convex_closedBall x ‖y-x‖).segment_subset
        (Metric.mem_closedBall_self (norm_nonneg _)) (by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl])) hz
  have H := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hR z (hseg hz)).hasFDerivWithinAt)
    (show ∀ z∈segment ℝ x y, ‖fderiv ℝ f z-fderiv ℝ f x‖≤B*‖y-x‖ from by
      intro z hz
      exact (hLip z (hseg hz)).trans (mul_le_mul_of_nonneg_left (hn z hz) hB))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [R,sub_self,map_zero,sub_zero,Real.norm_eq_abs,pow_two,mul_assoc] using H

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_EuclideanUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
lemma divided_cost_triangle (x z y : M) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    cost x y ≤ cost x z/t+cost z y/(1-t) := by
  convert squared_dist_divided_action_le x z y ht ht1 using 1 <;>
    simp only [cost,div_div,mul_comm]

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FiniteNonnegativeWeightPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport

lemma finite_nonnegative_weight_zero_on_pos {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, f i ≤ 0)
    (hsum : ∑ i, w i * f i = 0) : ∀ i, 0 < w i → f i = 0 := by
  intro i hi
  apply le_antisymm (hf i)
  by_contra! hh
  have hs : (∑ j, w j * f j) < ∑ j ∈ (Finset.univ : Finset ι), (0:ℝ) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_nonpos_of_nonneg_of_nonpos (hw j) (hf j)
    · exact ⟨i,Finset.mem_univ i,mul_neg_of_pos_of_neg hi hh⟩
  simp [hsum] at hs

lemma sum_filter_positive_weights {ι E : Type*} [Fintype ι]
    [AddCommMonoid E] [Module ℝ E] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f : ι → E) :
    ∑ i ∈ (Finset.univ.filter (fun i => 0 < w i)), w i • f i = ∑ i, w i • f i := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < w i
  · simp only [h,ite_true, if_true]
  · have hz : w i = 0 := le_antisymm (le_of_not_gt h) (hw i)
    simp [hz]

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_FiniteSimplexRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set

namespace WeakMTWTransport

lemma finite_simplex_representation {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} {x : E} (hx : x ∈ convexHull ℝ S) :
    ∃ m : ℕ, 0 < m ∧ m ≤ Module.finrank ℝ E + 1 ∧
      ∃ z : Fin m → E, ∃ w : Fin m → ℝ,
        (∀ i, z i ∈ S) ∧ (∀ i, 0 ≤ w i) ∧
        (∑ i, w i = 1) ∧ (∑ i, w i • z i = x) := by
  classical
  obtain ⟨ι,inst,z,w,hz,hi,hw,hsum,heq⟩ := eq_pos_convex_span_of_mem_convexHull hx
  let : Fintype ι := inst
  have : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp at hsum
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι,Fintype.card_pos,
    hi.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1),
    fun i => z (e.symm i),fun i => w (e.symm i),?_,?_,?_,?_⟩
  · intro i
    exact hz (mem_range_self _)
  · intro i
    exact (hw _).le
  · simpa only [e.symm.sum_comp] using hsum
  · exact (e.symm.sum_comp (fun i => w i • z i)).trans heq

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_LimitGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set Filter
open scoped Topology

lemma isPreconnected_fiber_of_mem_closure_bijective
    {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [T2Space Y] [LocallyConnectedSpace Y]
    (F : P → X → Y) (hF : Continuous (fun q : P × X => F q.1 q.2))
    {a : P} (ha : a ∈ closure {p | Function.Bijective (F p)}) (y : Y) :
    IsPreconnected {x | F a x = y} := by
  have hFa : Continuous (F a) := hF.comp (continuous_const.prodMk continuous_id)
  have hs : IsClosed {x | F a x = y} := isClosed_eq hFa continuous_const
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hs).mpr
  intro A B hA hB hcover hAB
  by_contra hnot
  push Not at hnot
  obtain ⟨x,hx,hxA⟩ := Set.not_subset.mp hnot.1
  obtain ⟨z,hz,hzB⟩ := Set.not_subset.mp hnot.2
  have hxB : x ∈ B := (hcover hx).resolve_left hxA
  have hzA : z ∈ A := (hcover hz).resolve_right hzB
  obtain ⟨U,V,hU,hV,hAU,hBV,hUV⟩ := normal_separation hA hB hAB
  let K := (U ∪ V)ᶜ
  have hK : IsCompact K := (hU.union hV).isClosed_compl.isCompact
  have H : ∀ᶠ q : P × Y in 𝓝 (a,y), ∀ b ∈ K, F q.1 b ≠ q.2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro b hb
    have hbne : F a b ≠ y := by
      intro he
      exact hb ((hcover he).imp (fun h => hAU h) (fun h => hBV h))
    have hf : Continuous (fun q : (P × Y) × X => F q.1.1 q.2) :=
      hF.comp ((continuous_fst.fst).prodMk continuous_snd)
    exact (isOpen_ne_fun hf continuous_fst.snd).mem_nhds hbne
  obtain ⟨O,hO,W,hW,hOW⟩ := mem_nhds_prod_iff.mp H
  obtain ⟨N,hNW,hN,hyN,hNc⟩ :=
    (locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp (inferInstance : LocallyConnectedSpace Y)) y W hW
  have Hx : ∀ᶠ p in 𝓝 a, F p x ∈ N := by
    have hc : ContinuousAt (fun p => F p x) a :=
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact hc.preimage_mem_nhds (hx.symm ▸ hN.mem_nhds hyN)
  have Hz : ∀ᶠ p in 𝓝 a, F p z ∈ N := by
    have hc : ContinuousAt (fun p => F p z) a :=
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact hc.preimage_mem_nhds (hz.symm ▸ hN.mem_nhds hyN)
  have HO : ∀ᶠ p in 𝓝 a, p ∈ O := hO
  obtain ⟨p,hp,hpO,hpx,hpz⟩ :=
    ((mem_closure_iff_frequently.mp ha).and_eventually (HO.and (Hx.and Hz))).exists
  have hpC : Continuous (F p) := hF.comp (continuous_const.prodMk continuous_id)
  have hpconn : IsPreconnected (F p ⁻¹' N) :=
    hNc.isPreconnected.preimage_of_isClosedMap hp.1 hpC.isClosedMap
      (fun w _ => hp.2 w)
  have hsub : F p ⁻¹' N ⊆ U ∪ V := by
    intro b hb
    by_contra hn
    exact hOW (show (p,F p b) ∈ O ×ˢ W from ⟨hpO,hNW hb⟩) b hn rfl
  obtain ⟨b,hb,hbU,hbV⟩ := hpconn U V hU hV hsub
    ⟨z,hpz,hAU hzA⟩ ⟨x,hpx,hBV hxB⟩
  exact Set.disjoint_left.mp hUV hbU hbV

lemma fiber_subsingleton_of_preconnected_isolated
    {X : Type*} [TopologicalSpace X] [T1Space X] {s : Set X}
    (hs : IsPreconnected s)
    (hisol : ∀ x ∈ s, ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ s ⊆ {x}) :
    s.Subsingleton := by
  intro x hx y hy
  obtain ⟨U,hU,hxU,hUs⟩ := hisol x hx
  by_contra hxy
  have hcov : s ⊆ U ∪ ({x} : Set X)ᶜ := by
    intro z hz
    by_cases he : z=x
    · exact Or.inl (he.symm ▸ hxU)
    · exact Or.inr he
  obtain ⟨z,hzs,hzU,hzne⟩ := hs U ({x} : Set X)ᶜ hU isClosed_singleton.isOpen_compl hcov
    ⟨x,hx,hxU⟩ ⟨y,hy,Ne.symm hxy⟩
  exact hzne (hUs ⟨hzU,hzs⟩)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_SecondFderivCompLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma second_fderiv_comp_linear_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (hf : ContDiffAt ℝ 2 f 0) (L : E →L[ℝ] F) (v : E) :
    fderiv ℝ (fderiv ℝ (fun h => f (L h))) 0 v v =
      fderiv ℝ (fderiv ℝ f) 0 (L v) (L v) := by
  have hcomp : ContDiffAt ℝ 2 (fun h => f (L h)) 0 :=
    (show ContDiffAt ℝ 2 f (L 0) by simpa using hf).comp 0 L.contDiff.contDiffAt
  rw [← iteratedDeriv_two_affine_line hcomp v, ← iteratedDeriv_two_affine_line hf (L v)]
  congr 2
  ext t
  simp only [map_smul,zero_add]

end WeakMTWTransport
end

end OAI
end


