-- Prove2me | Definitions.Def_OAIQ232A027
-- name    : OAIQ232A027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:41.927043+00:00
-- url     : https://prove2.me/theorems/b1b31c94-4be6-43b8-8503-78bed5a03421
-- title:
--   Definitions bundle OAIQ232A027 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 1 definition and 20 theorems. The definitions and types are `OAI.WeakMTWTransport.trueCenterJetOfOriginal`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_TrueCenterJetBuild`, `BiholderTransport_Contact_CoordinateSupportGradient`, `BiholderTransport_Convexity_EnvelopeData`, `BiholderTransport_Coordinates_ActiveCompact`, `BiholderTransport_Coordinates_ChartGradientMap`, `BiholderTransport_Coordinates_JoinCoordinates`, `BiholderTransport_Coordinates_NormalCoordinates3`, `BiholderTransport_Coordinates_NormalEikonal`, `BiholderTransport_Coordinates_ProperPieces`, `BiholderTransport_LinearAlgebra_CompactQuadratic`, `BiholderTransport_LinearAlgebra_ContactDifferential`, `BiholderTransport_LinearAlgebra_DividedHessian`, `BiholderTransport_LinearAlgebra_HalfCostUniform`, `BiholderTransport_LinearAlgebra_PositiveSingular`, `BiholderTransport_Regularity_Reversal`, `BiholderTransport_Regularity_ReverseRegular`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A024` and `OAIQ232A025` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ232A029`; the proofs of `OAI.WeakMTWTransport.CenterSequenceData.regular_compact`, `OAI.WeakMTWTransport.CenterSequenceData.true_ray_compact`, `OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second`, `OAI.WeakMTWTransport.WeakMTW.exists_local_outer_chart_jet_bound`, `OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound`, `OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound`, `OAI.WeakMTWTransport.contact_selection_chart_differential_full`, `OAI.WeakMTWTransport.exists_actual_center_sequential_gain`, `OAI.WeakMTWTransport.exists_parametric_short_lower_sequence`, `OAI.WeakMTWTransport.exists_uniform_cost_upper_taylor`, `OAI.WeakMTWTransport.normal_test_to_chart`, `OAI.WeakMTWTransport.original_chart_good_null` and `OAI.WeakMTWTransport.parametric_short_center_pole_limit`.
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
import Definitions.Def_OAIQ232A024
import Definitions.Def_OAIQ232A025

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

lemma movingNormalCost_contDiffAt {a : M} {b p : Model n}
    (hb : b ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b)) :
    ContDiffAt ℝ ∞ (fun q : (Model n × Model n) × Model n =>
      movingNormalCost a q.1.1 q.1.2 q.2) ((b,p),0) := by
  let x := (extChartAt 𝓘(ℝ,Model n) a).symm b
  let L := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
  have hA : ContMDiffAt 𝓘(ℝ,(Model n × Model n) × Model n) 𝓘(ℝ,Model n) ∞
      (fun q : (Model n × Model n) × Model n => movingNormal a (q.1.1,q.2)) ((b,p),0) :=
    (movingNormal_contMDiffAt (q := (b,0)) hb).comp ((b,p),0)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd).contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ,(Model n × Model n) × Model n) 𝓘(ℝ,Model n) ∞
      (fun q : (Model n × Model n) × Model n => movingNormal a (q.1.1,q.1.2)) ((b,p),0) :=
    (movingNormal_contMDiffAt (q := (b,p)) hb).comp ((b,p),0) contDiffAt_fst.contMDiffAt
  have hC : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (movingNormal a (b,0),movingNormal a (b,p)) := by
    rw [movingNormal_zero hb,movingNormal_eq hb]
    exact cost_contMDiffAt_of_injectivityDomain ⟨x,L p⟩ hp
  exact ((hC.comp ((b,p),0) (hA.prodMk hB)).contDiffAt)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_EnvelopeData
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
  {ι : Type*} [Fintype ι]

lemma scaledNormalEnvelope_contDiffAt {a : M} {s : ℝ}
    {q : EnvelopeData (Model n) ι} (i : ι)
    (hb : q.1.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)
        (q.2.2 • ∑ j, q.2.1 j • q.1.2 j) ∈
          injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1))
    (hi : (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1) (s • q.1.2 i) ∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.1)) :
    ContDiffAt ℝ ∞ (fun z : EnvelopeData (Model n) ι × Model n =>
      scaledNormalEnvelope a s z.1 i z.2) (q,0) := by
  have hmean : ContDiff ℝ ∞ (fun z : EnvelopeData (Model n) ι × Model n =>
      z.1.2.2 • ∑ j, z.1.2.1 j • z.1.1.2 j) := by fun_prop
  have hpi : ContDiff ℝ ∞ (fun z : EnvelopeData (Model n) ι × Model n =>
      s • z.1.1.2 i) := by fun_prop
  have hleft := movingNormalCost_contDiffAt hb hp
  have hright := movingNormalCost_contDiffAt hb hi
  exact ((hleft.comp (q,0) ((contDiffAt_fst.fst.fst.prodMk hmean.contDiffAt).prodMk contDiffAt_snd)).sub
    (hleft.comp (q,0) ((contDiffAt_fst.fst.fst.prodMk hmean.contDiffAt).prodMk contDiffAt_const))).sub
      ((contDiffAt_fst.snd.snd.div_const s).mul
        ((hright.comp (q,0) ((contDiffAt_fst.fst.fst.prodMk hpi.contDiffAt).prodMk contDiffAt_snd)).sub
          (hright.comp (q,0) ((contDiffAt_fst.fst.fst.prodMk hpi.contDiffAt).prodMk contDiffAt_const))))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ActiveCompact
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_uniform_short_contraction_into_ID (D : ℝ) :
    ∃ τ>0, τ<1 ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      ‖p‖≤D → ∀ t : ℝ, 0≤t → t≤τ → t • p ∈ injectivityDomain x := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  have hK := isCompact_bundle_disk (F := Model n)
    (E := fun x : M => TangentSpace 𝓘(ℝ,Model n) x) D
  have H : ∀ᶠ t : ℝ in 𝓝 0, ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      ‖z.2‖≤D → t • z.2 ∈ injectivityDomain z.1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have ho := (isOpen_total_injectivityDomain (n := n) (M := M)).preimage
      (contMDiff_tangentScale (E := Model n) (M := M)).continuous
    apply ho.mem_nhds
    change (0:ℝ) • z.2 ∈ injectivityDomain z.1
    simpa only [zero_smul] using zero_mem_injectivityDomain (n := n) z.1
  obtain ⟨δ,hδ,Hδ⟩ := Metric.eventually_nhds_iff.mp H
  obtain ⟨τ,hτ,hτm⟩ := exists_between (lt_min hδ (show (0:ℝ)<1 by norm_num))
  refine ⟨τ,hτ,(lt_min_iff.mp hτm).2,?_⟩
  intro x p hp t ht htτ
  exact Hδ (by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ht] using
    htτ.trans_lt (lt_min_iff.mp hτm).1) ⟨x,p⟩ hp

lemma exists_uniform_short_active_hull_contraction :
    ∃ τ>0, τ<1 ∧ ∀ v : M → ℝ, ∀ x : M,
      ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
        ∀ t : ℝ, 0≤t → t≤τ → t • p ∈ injectivityDomain x := by
  obtain ⟨τ,hτ,hτ1,H⟩ := exists_uniform_short_contraction_into_ID (n := n) (M := M)
    (Metric.diam (univ : Set M))
  exact ⟨τ,hτ,hτ1,fun _ x p hp => H x p (active_hull_norm_le_diam hp)⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_HalfCostUniform
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniform_half_cost_hessian (a : M) :
    ∃ B>0, ∃ r>0,
      ball (extChartAt 𝓘(ℝ,Model n) a a) r ⊆ (extChartAt 𝓘(ℝ,Model n) a).target ∧
      ∀ x∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
      ∀ p : TangentSpace 𝓘(ℝ,Model n) ((extChartAt 𝓘(ℝ,Model n) a).symm x),
      p∈minimizingVectors ((extChartAt 𝓘(ℝ,Model n) a).symm x) →
      ∀ z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
        ContDiffAt ℝ 2 (chartCost a (riemannianExp _ ((1/2:ℝ) • p))) z ∧
        ‖fderiv ℝ (fderiv ℝ (chartCost a (riemannianExp _ ((1/2:ℝ) • p)))) z‖≤B := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let z₀ := χ a
  let Y : TangentBundle 𝓘(ℝ,Model n) M → M := fun V => riemannianExp V.1 ((1/2:ℝ) • V.2)
  have hY : Continuous Y := contMDiff_riemannianExp.continuous.comp
    (contMDiff_tangentScale.continuous.comp (continuous_const.prodMk continuous_id))
  have haT : z₀∈χ.target := χ.map_source (mem_extChartAt_source a)
  have hχ : ContinuousAt χ.symm z₀ :=
    (continuousOn_extChartAt_symm a z₀ haT).continuousAt ((isOpen_extChartAt_target a).mem_nhds haT)
  have hproj : Continuous (fun V : TangentBundle 𝓘(ℝ,Model n) M => V.1) :=
    FiberBundle.continuous_proj _ _
  have hg : ContinuousAt (fun q : Model n×Model n => χ.symm q.1) (z₀,z₀) :=
    hχ.comp (x := (z₀,z₀)) (f := fun q : Model n×Model n => q.1) continuousAt_fst
  have hloc : ∀ V : TangentBundle 𝓘(ℝ,Model n) M,
      V.2∈minimizingVectors V.1 → V.1=χ.symm z₀ →
      ContinuousAt (fun q : Model n×M => fderiv ℝ (fderiv ℝ (chartCost a q.2)) q.1) (z₀,Y V) ∧
      ∀ᶠ q : Model n×M in 𝓝 (z₀,Y V), ContDiffAt ℝ 2 (chartCost a q.2) q.1 := by
    intro V hV he
    apply chartCost_jet_continuous haT
    have hc := cost_contMDiffAt_of_injectivityDomain
      (⟨V.1,(1/2:ℝ) • V.2⟩ : TangentBundle 𝓘(ℝ,Model n) M)
      (contracted_minimizer_mem_injectivityDomain hV (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1))
    change ContMDiffAt _ _ ∞ (fun q : M×M => cost q.1 q.2) (χ.symm z₀,Y V)
    rw [←he]
    exact hc
  let H := fun q : (Model n×Model n)×TangentBundle 𝓘(ℝ,Model n) M =>
    fderiv ℝ (fderiv ℝ (chartCost a (Y q.2))) q.1.2
  have hc : Continuous (fun q : (Model n×Model n)×TangentBundle 𝓘(ℝ,Model n) M =>
      (q.1.2,Y q.2)) := continuous_fst.snd.prodMk (hY.comp continuous_snd)
  obtain ⟨B,hB,hBnear⟩ := compact_eventually_fiberwise_bound isCompact_total_minimizingVectors
    hproj hg (h := H) (fun V hV he => by
      convert (hloc V hV he).1.comp
        (x := ((z₀,z₀),V)) (f := fun q : (Model n×Model n)×TangentBundle 𝓘(ℝ,Model n) M => (q.1.2,Y q.2)) hc.continuousAt using 1
      all_goals try with_reducible_and_instances rfl
      rfl)
  have hSnear : ∀ᶠ q : Model n×Model n in 𝓝 (z₀,z₀),
      ∀ V : TangentBundle 𝓘(ℝ,Model n) M, V.2∈minimizingVectors V.1 → V.1=χ.symm q.1 →
      ContDiffAt ℝ 2 (chartCost a (Y V)) q.2 := by
    apply compact_eventually_fiberwise isCompact_total_minimizingVectors hproj hg
    intro V hV he
    exact (hc.continuousAt (x := ((z₀,z₀),V))).tendsto.eventually (hloc V hV he).2
  obtain ⟨r₁,hr₁,hr⟩ := Metric.eventually_nhds_iff.mp (hSnear.and hBnear)
  obtain ⟨r₂,hr₂,hrT⟩ := Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target a).mem_nhds haT)
  refine ⟨B,hB,min r₁ r₂,lt_min hr₁ hr₂,?_,?_⟩
  · exact fun x hx => hrT (ball_subset_ball (min_le_right _ _) hx)
  · intro x hx p hp z hz
    have hpair : dist (x,z) (z₀,z₀) < r₁ := by
      rw [Prod.dist_eq,max_lt_iff]
      exact ⟨lt_of_lt_of_le hx (min_le_left _ _),lt_of_lt_of_le hz (min_le_left _ _)⟩
    exact ⟨(hr hpair).1 ⟨χ.symm x,p⟩ hp rfl,(hr hpair).2 ⟨χ.symm x,p⟩ hp rfl⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ChartGradientMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma chartCost_gradient_at_contact {a : M} {z : Model n} {L : Model n →L[ℝ] ℝ}
    (hz : z∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hp : chartGradientVector a z L∈injectivityDomain
      ((extChartAt 𝓘(ℝ,Model n) a).symm z)) :
    HasFDerivAt (chartCost a (coordinateBackward a (-1,z,L))) (-L) z := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let x := χ.symm z
  let p := chartGradientVector a z L
  have hx : x∈χ.source := χ.map_target hz
  have hx' : x∈(chartAt (Model n) a).source := by simpa only [χ,extChartAt_source] using hx
  have H := coordinate_gradient_of_hasMFDerivAt (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)
    hx (fun w => cost w (riemannianExp x p)) (-1)
    (by simpa only [neg_one_smul] using cost_start_gradient_of_injectivityDomain hp)
  have hcoord : (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 =
      (riemannianCoordinateMetric a z).inverse L := by
    have hsame : (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 =
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p := by
      rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx']
      rfl
    rw [hsame]
    exact Trivialization.continuousLinearMapAt_symmL _ hx' _
  dsimp only [Bundle.TotalSpace.proj,Bundle.TotalSpace.snd] at H
  rw [hcoord] at H
  have he : χ x=z := χ.right_inv hz
  change HasFDerivAt (fun q => cost (χ.symm q) (riemannianExp x p))
    ((-1:ℝ) • riemannianCoordinateMetric a (χ x) ((riemannianCoordinateMetric a z).inverse L)) (χ x) at H
  rw [he,(riemannianCoordinateMetric_isInvertible hz).self_apply_inverse] at H
  rw [coordinateBackward_eq_exp_chartGradient hz]
  apply H.congr_fderiv
  ext w
  change (-1:ℝ)*L w= -L w
  ring

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

omit [Nonempty M] in
lemma coordinateScalarSupport_hasFDerivAt {a : M} {b p : Model n}
    {v s l : ℝ} {φ : ℝ → ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hs : s≠0)
    (hp : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hφ : HasDerivAt φ l v) :
    HasFDerivAt (fun w => coordinateScalarSupport a φ (((v,s),(b,p)),w))
      (l • riemannianCoordinateMetric a b p) b := by
  let L := riemannianCoordinateMetric a b p
  have hi := riemannianCoordinateMetric_isInvertible hb
  have hgrad : chartGradientVector a b (s • L)=
      s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm b) p := by
    simp only [chartGradientVector,map_smul,L,hi.inverse_apply_self]
  have he : coordinateBackward a (-1,b,s • L)=movingNormal a (b,s • p) := by
    simp only [coordinateBackward,neg_neg,one_smul,map_smul,L,hi.inverse_apply_self]
  have hC := chartCost_gradient_at_contact hb (hgrad.symm ▸ hp)
  rw [he] at hC
  let c := chartCost (n := n) a (movingNormal a (b,s • p))
  let f := fun w => v+c b/s+(-s⁻¹)*c w
  have hf : HasFDerivAt f L b := by
    apply ((hC.const_mul (-s⁻¹)).const_add (v+c b/s)).congr_fderiv
    ext d
    simp only [_root_.smul_apply,smul_eq_mul,neg_apply]
    field_simp
  have hf0 : f b=v := by dsimp only [f] <;> ring
  have h : HasDerivAt φ l (f b) := hf0.symm ▸ hφ
  have H := h.comp_hasFDerivAt b hf
  have heq : (fun w => coordinateScalarSupport a φ (((v,s),(b,p)),w))=
      fun w => φ (f w) := by
    funext w
    dsimp only [coordinateScalarSupport,f,c,chartCost]
    congr 1
    ring
  rw [heq]
  exact H

omit [Nonempty M] in
lemma coordinateScalarSupport_shortForward {a : M} {b p : Model n}
    {v s l t : ℝ} {φ : ℝ → ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hs : s≠0)
    (hp : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
      injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hφ : HasDerivAt φ l v) :
    shortForward a (fun w => coordinateScalarSupport a φ (((v,s),(b,p)),w)) (t,b)=
      extChartAt 𝓘(ℝ,Model n) a (movingNormal a (b,(t*l) • p)) := by
  rw [shortForward,(coordinateScalarSupport_hasFDerivAt hb hs hp hφ).fderiv]
  simp only [coordinateBackward,neg_neg,map_smul,
    (riemannianCoordinateMetric_isInvertible hb).inverse_apply_self,smul_smul,one_mul]

end WeakMTWTransport

end



end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_ReverseRegular
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

lemma reverseRay_regular {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈injectivityDomain z.1) :
    (reverseRay z).2∈injectivityDomain (reverseRay z).1 := by
  have hzi := interior_total_minimizingVectors z hz
  have H := continuous_reverseRay.continuousAt.eventually
    (show ∀ᶠ q in 𝓝 (reverseRay (reverseRay z)), q.2∈minimizingVectors q.1 from
      by rw [reverseRay_involutive z]; exact mem_interior_iff_mem_nhds.mp hzi)
  have HR : ∀ᶠ q in 𝓝 (reverseRay z), q.2∈minimizingVectors q.1 := by
    filter_upwards [H] with q hq
    exact (reverseRay_involutive q) ▸ (reverseRay_minimizing hq)
  have HI : reverseRay z∈interior {q : TangentBundle 𝓘(ℝ,Model n) M | q.2∈minimizingVectors q.1} :=
    mem_interior_iff_mem_nhds.mpr HR
  rwa [←total_injectivityDomain_eq_interior] at HI

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ContactDifferential
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
section ContactDifferential
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf
omit [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
lemma exists_normal_local_inverse_at {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ κ : M → TangentSpace 𝓘(ℝ,Model n) x,
      κ (riemannianExp x p)=p ∧
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ κ (riemannianExp x p) ∧
      ∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (κ y)=y := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  let d := extChartAt 𝓘(ℝ,Model n) y
  obtain ⟨e,he,hp',hc⟩ := exists_coordinate_exp_inverse hp
  let κ : M → V := fun z => e.symm (d z)
  have hep : e p=d y := congrFun he p
  have hκp : κ y=p := by change e.symm _=p; rw [←hep]; exact e.left_inv hp'
  have hκ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ κ y := by
    apply ContMDiffAt.comp y _ contMDiffAt_extChartAt
    rw [←hep]
    exact hc.contMDiffAt
  refine ⟨κ,hκp,hκ,?_⟩
  have hct : ∀ᶠ z in 𝓝 y, d z∈e.target :=
    (contMDiffAt_extChartAt (I := 𝓘(ℝ,Model n)) (n := ∞) (x := y)).continuousAt.preimage_mem_nhds
      (by rw [←hep]; exact e.open_target.mem_nhds (e.map_source hp'))
  have hcs : ∀ᶠ z in 𝓝 y, z∈d.source := extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y
  have hes : ∀ᶠ z in 𝓝 y, riemannianExp x (κ z)∈d.source :=
    (((contMDiff_riemannianExp_fiber x).continuous.continuousAt).comp hκ.continuousAt).preimage_mem_nhds
      (by simp only [Function.comp_apply,hκp]; exact extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y)
  filter_upwards [hct,hcs,hes] with z hzt hzs hzes
  apply d.injOn hzes hzs
  change (fun q => d (riemannianExp x q)) (κ z)=_
  rw [←he]
  exact e.right_inv hzt

end ContactDifferential
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Calculus_TrueCenterJetBuild
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
section TrueCenterJetBuild
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def trueCenterJetOfOriginal {u:M → ℝ} {a c y:M} {φ:ℝ → ℝ} {l:ℝ}
    {p:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A)
    (hp:∀d,d≠0 → 0 < inner ℝ ((normalHessianOperator y p+A) d) d)
    (hl:0<l) (hl1:l<1)
    (hy:y∈(extChartAt 𝓘(ℝ,Model n) c).source)
    (hz:(reverseRay (⟨y,l • p⟩:TangentBundle 𝓘(ℝ,Model n) M)).1∈
      (extChartAt 𝓘(ℝ,Model n) a).source)
    (hφ:ContDiffAt ℝ 2 φ (cTransform u y)) (hφd:deriv φ (cTransform u y)=l)
    {s:Model n} {S:Model n →L[ℝ] Model n}
    (hS:∀d e,inner ℝ (S d) e=inner ℝ d (S e))
    (hSe:HasQuadraticExpansion (fun h=>φ (cTransform u ((extChartAt 𝓘(ℝ,Model n) c).symm
      (extChartAt 𝓘(ℝ,Model n) c y+h)))) s S) :
    TrueCenterJet (n:=n) u a c φ l := by
  let z:=reverseRay (⟨y,l • p⟩:TangentBundle 𝓘(ℝ,Model n) M)
  have hrec:=graph_coordinate_reconstruction hz
  have hreg:z.2∈injectivityDomain z.1:=
    reverseRay_regular (contracted_minimizer_mem_injectivityDomain (injectivityDomain_subset_minimizingVectors _ hA.2.1) hl hl1)
  refine {
    y := y
    b := graphBaseCoordinate a z
    q := graphVelocityCoordinate a z
    chart := (extChartAt 𝓘(ℝ,Model n) a).map_source hz
    regular := ?_
    endpoint := ?_
    endChart := hy
    p := p
    A := A
    original := hA
    positive := hp
    pole := ?_
    smooth := hφ
    slope := hφd
    s := s
    S := S
    symmetric := hS
    expansion := hSe }
  · exact (congrArg (fun w:TangentBundle 𝓘(ℝ,Model n) M=>w.2∈injectivityDomain w.1) hrec).mpr hreg
  · rw [movingPrefix_graph_coordinates hz,one_smul]
    exact reverseRay_endpoint _
  · exact (reverseRay_base (⟨y,l • p⟩:TangentBundle 𝓘(ℝ,Model n) M)).symm.trans
      ((extChartAt 𝓘(ℝ,Model n) a).left_inv hz).symm
end TrueCenterJetBuild
end WeakMTWTransport

end
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_Reversal
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
section Reversal
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma reverseRay_injectivityDomain {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈injectivityDomain z.1) :
    (reverseRay z).2∈injectivityDomain (reverseRay z).1 := by
  have hi := interior_total_minimizingVectors z hz
  have H : ∀ᶠ w : TangentBundle 𝓘(ℝ,Model n) M in 𝓝 (reverseRay z),
      (reverseRay w).2∈minimizingVectors (reverseRay w).1 := by
    have hN := continuous_reverseRay.continuousAt.preimage_mem_nhds
      (show {q : TangentBundle 𝓘(ℝ,Model n) M | q.2∈minimizingVectors q.1} ∈
        𝓝 (reverseRay (reverseRay z)) from by
          rw [reverseRay_reverseRay]; exact mem_interior_iff_mem_nhds.mp hi)
    exact hN
  have hj : reverseRay z∈interior {q : TangentBundle 𝓘(ℝ,Model n) M |
      q.2∈minimizingVectors q.1} := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [H] with w hw
    have hh := reverseRay_minimizing hw
    change reverseRay (reverseRay w)∈{q : TangentBundle 𝓘(ℝ,Model n) M |
      q.2∈minimizingVectors q.1} at hh
    rwa [reverseRay_reverseRay] at hh
  rwa [←total_injectivityDomain_eq_interior] at hj

end Reversal
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ProperPieces
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
section ProperPieces
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

variable [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma proper_suffix_in_injectivityDomain {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h T : ℝ} (hh : 0<h) (hhT : h<T) (hT1 : T≤1) :
    (T-h) • (sprayFlow h z).2∈injectivityDomain (sprayFlow h z).1 := by
  have hT : 0<T := hh.trans hhT
  let w := tangentScale T z
  have hw : w.2∈minimizingVectors w.1 := minimizingVectors_smul hz hT.le hT1
  have hr := reverseRay_minimizing hw
  have hs : 0<(T-h)/T := div_pos (sub_pos.mpr hhT) hT
  have hs1 : (T-h)/T<1 := (div_lt_one hT).mpr (by linarith)
  have hi := contracted_minimizer_mem_injectivityDomain hr hs hs1
  change (tangentScale ((T-h)/T) (reverseRay (tangentScale T z))).2∈
    injectivityDomain (tangentScale ((T-h)/T) (reverseRay (tangentScale T z))).1 at hi
  rw [←reverseRay_segment z h T hT.ne'] at hi
  have H := reverseRay_injectivityDomain hi
  change (reverseRay (reverseRay (tangentScale (T-h) (sprayFlow h z)))).2∈
    injectivityDomain (reverseRay (reverseRay (tangentScale (T-h) (sprayFlow h z)))).1 at H
  rw [reverseRay_reverseRay] at H
  exact H

end ProperPieces
end WeakMTWTransport

end

end

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

lemma proper_prefix_reverse_in_injectivityDomain {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    (-h) • (sprayFlow h z).2∈injectivityDomain (sprayFlow h z).1 := by
  have H := reverseRay_injectivityDomain (z := tangentScale h z)
    (contracted_minimizer_mem_injectivityDomain hz hh hh1)
  rw [reverseRay_prefix] at H
  exact H

lemma middleCenteredAction_contDiffAt {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    ContDiffAt ℝ 2 (middleCenteredAction z h) 0 := by
  have hf : ContDiffAt ℝ 2 (normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2)) 0 :=
    (normalCost_contDiffAt (proper_prefix_reverse_in_injectivityDomain hz hh hh1)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hg : ContDiffAt ℝ 2 (normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2)) 0 :=
    (normalCost_contDiffAt (proper_suffix_in_injectivityDomain hz hh hh1 le_rfl)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact (contDiffAt_const.mul (hf.sub contDiffAt_const)).sub
      (contDiffAt_const.mul (hg.sub contDiffAt_const))

lemma middleCenteredAction_hessian {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1)
    (v : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    fderiv ℝ (fderiv ℝ (middleCenteredAction z h)) 0 v v=middleHessian z h 1 v v := by
  have hf : ContDiffAt ℝ 2 (normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2)) 0 :=
    (normalCost_contDiffAt (proper_prefix_reverse_in_injectivityDomain hz hh hh1)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hg : ContDiffAt ℝ 2 (normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2)) 0 :=
    (normalCost_contDiffAt (proper_suffix_in_injectivityDomain hz hh hh1 le_rfl)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  unfold middleCenteredAction
  rw [second_fderiv_scaled_differences hf hg,middleHessian_apply]
  simp only [normalHessian,neg_mul,sub_neg_eq_add,div_eq_mul_inv,mul_comm]

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
section JoinCoordinates
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_join_normal_coordinates {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {h : ℝ} (hh : h≠0) (hp : h • p∈injectivityDomain x) :
    ∃ q : TangentSpace 𝓘(ℝ,Model n) x →
        TangentSpace 𝓘(ℝ,Model n) (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      q p=0 ∧ ContDiffAt ℝ ∞ q p ∧ Function.Injective (fderiv ℝ q p) ∧
      ∀ᶠ a in 𝓝 p, riemannianExp _ (q a)=riemannianExp x (h • a) := by
  let : Nonempty M := ⟨x⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let z := sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Z := TangentSpace 𝓘(ℝ,Model n) z.1
  obtain ⟨κ,hκ0,hκ,hκr⟩ := exists_normal_local_inverse_at (zero_mem_injectivityDomain (n := n) z.1)
  rw [riemannianExp_zero] at hκ0 hκ hκr
  let q : X → Z := fun a => κ (riemannianExp x (h • a))
  have heq : riemannianExp x (h • p)=z.1 := riemannianExp_smul x p h
  have hE : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,Model n) ∞
      (fun a : X => riemannianExp x (h • a)) p :=
    (contMDiff_riemannianExp_fiber x _).comp p
      (show ContDiffAt ℝ ∞ (fun a : X => h • a) p from by fun_prop).contMDiffAt
  have hq : ContDiffAt ℝ ∞ q p := by
    apply ContMDiffAt.contDiffAt
    apply ContMDiffAt.comp p _ hE
    rwa [heq]
  have hqp : q p=0 := by change κ _=0; rw [heq,hκ0]
  have hqr : ∀ᶠ a in 𝓝 p, riemannianExp z.1 (q a)=riemannianExp x (h • a) :=
    hE.continuousAt.eventually (by simpa only [heq] using hκr)
  exact ⟨q,hqp,hq,prefix_log_fderiv_injective hh hp (hq.differentiableAt (by simp)) hqr,hqr⟩

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

lemma doubleNormalCost_contDiffAt {x y : M} {r : TangentSpace 𝓘(ℝ,Model n) y}
    (hr : r∈injectivityDomain y) (he : riemannianExp y r=x) :
    ContDiffAt ℝ ∞ (doubleNormalCost (n := n) x y) (0,0) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  have hu : ContMDiffAt 𝓘(ℝ,X×Y) 𝓘(ℝ,Model n) ∞
      (fun z : X×Y => riemannianExp y z.2) (0,0) :=
    (contMDiff_riemannianExp_fiber y _).comp (0,0) contDiffAt_snd.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,X×Y) 𝓘(ℝ,Model n) ∞
      (fun z : X×Y => riemannianExp x z.1) (0,0) :=
    (contMDiff_riemannianExp_fiber x _).comp (0,0) contDiffAt_fst.contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨y,r⟩ : TangentBundle 𝓘(ℝ,Model n) M) hr
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp y (0:Y),riemannianExp x (0:X)) := by
    simpa only [riemannianExp_zero,he] using hc
  have H := (hc'.comp (0,0) (hu.prodMk hv)).contDiffAt
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact congrArg (fun d : ℝ => d^2/2) (dist_comm _ _)

end NormalEikonal
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_DividedHessian
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
section CrossingValue
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma doubleNormalCost_self_contDiffAt {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈injectivityDomain x) :
    ContDiffAt ℝ ∞ (doubleNormalCost (n := n) x x) (0,p) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  have hu : ContMDiffAt 𝓘(ℝ,X×X) 𝓘(ℝ,Model n) ∞
      (fun z : X×X => riemannianExp x z.1) (0,p) :=
    (contMDiff_riemannianExp_fiber x _).comp (0,p) contDiffAt_fst.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,X×X) 𝓘(ℝ,Model n) ∞
      (fun z : X×X => riemannianExp x z.2) (0,p) :=
    (contMDiff_riemannianExp_fiber x _).comp (0,p) contDiffAt_snd.contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:X),riemannianExp x p) := by
    simpa only [riemannianExp_zero] using hc
  exact (hc'.comp (0,p) (hu.prodMk hv)).contDiffAt

end CrossingValue
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_PositiveSingular
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
section CrossingDerivative
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_4_rfc3d83_1 (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma normalHessian_radial_derivative_value {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈injectivityDomain x)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    HasDerivAt (fun s : ℝ => normalHessian x (s • p) v v)
      (normalHessian x p v v-radialCrossingValue x p v) 1 := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let B := doubleNormalCost (n := n) x x
  have hB : ContDiffAt ℝ 3 B (0,p) :=
    (doubleNormalCost_self_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hD := hasDerivAt_source_hessian_line (a := (0:X)) (b := p)
    (w := p) (t := 1) (v := v) hB
  have heq : (fun s : ℝ => fderiv ℝ (fderiv ℝ (fun a : X => B (a,p+(s-1) • p))) 0 v v)=
      (fun s : ℝ => normalHessian x (s • p) v v) := by
    funext s
    have hs : p+(s-1) • p=s • p := by module
    rw [hs]
    rfl
  rw [heq] at hD
  have hS := second_derivative_source_slice (a := (0:X)) (b := p)
    (hB.of_le (by norm_num)) v v
  change normalHessian x p v v = _ at hS
  convert hD using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [radialCrossingValue]
  rw [←hS]
  ring

lemma divided_normalHessian_derivative_value {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ} (ht : t≠0)
    (hp : t • p∈injectivityDomain x) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    HasDerivAt (fun s : ℝ => normalHessian x (s • p) v v / s)
      (-(radialCrossingValue x (t • p) v/t^2)) t := by
  have hlin : HasDerivAt (fun s : ℝ => s/t) (1/t) t := (hasDerivAt_id t).div_const t
  have hder' : HasDerivAt (fun r : ℝ => normalHessian x (r • (t • p)) v v)
      (normalHessian x (t • p) v v-radialCrossingValue x (t • p) v) (t/t) := by
    simpa only [div_self ht] using normalHessian_radial_derivative_value hp v
  have hcomp := hder'.comp (h := fun s : ℝ => s/t) t hlin
  have heq : (fun s : ℝ => normalHessian x ((s/t) • (t • p)) v v)=
      (fun s : ℝ => normalHessian x (s • p) v v) := by
    funext s
    rw [smul_smul,div_mul_cancel₀ s ht]
  simp only [Function.comp_def] at hcomp
  rw [heq] at hcomp
  have H := hcomp.div (hasDerivAt_id t) ht
  simp only [id_eq] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (field_simp [ht]; ring)
end CrossingDerivative
end WeakMTWTransport

end

end

end

end OAI
end


