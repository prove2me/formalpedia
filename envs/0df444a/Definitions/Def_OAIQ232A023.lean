-- Prove2me | Definitions.Def_OAIQ232A023
-- name    : OAIQ232A023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:06:20.888311+00:00
-- url     : https://prove2.me/theorems/ea30da87-c980-4f95-9dc7-c7976d577aab
-- title:
--   Definitions bundle OAIQ232A023 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 26 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Contact_GraphProjection`, `BiholderTransport_Coordinates_BranchInverse`, `BiholderTransport_Coordinates_CutCharacterization`, `BiholderTransport_Coordinates_ExpVertical`, `BiholderTransport_Coordinates_KernelRadial`, `BiholderTransport_Coordinates_NormalCoordinates3`, `BiholderTransport_Coordinates_PoleCoordinates`, `BiholderTransport_Coordinates_ProperPieces`, `BiholderTransport_Coordinates_RadialFactor`, `BiholderTransport_Coordinates_SplitLogInjective`, `BiholderTransport_CostGeometry_BranchCost2`, `BiholderTransport_CostGeometry_StrictDividedAction`, `BiholderTransport_Geodesics_BranchExtension`, `BiholderTransport_Geodesics_SplitMinimizingAction`, `BiholderTransport_LinearAlgebra_CompactQuadratic`, `BiholderTransport_LinearAlgebra_RadialHessian`, `BiholderTransport_Regularity_ReverseRegular`, `BiholderTransport_Volume_ExponentialJacobian`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundle `OAIQ232A021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A024` and `OAIQ232A025`.
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
import Definitions.Def_OAIQ232A021

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SplitMinimizingAction
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma minimizing_split_upper_support {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) {s : ℝ} (hs : 0 < s) (hs1 : s<1) (z : M) :
    cost z (riemannianExp x p) ≤ cost z (riemannianExp x (s • p))/s + (1-s)*‖p‖^2/2 := by
  have hseg : dist (riemannianExp x (s • p)) (riemannianExp x p) = (1-s)*‖p‖ := by
    rw [riemannianExp_smul,riemannianExp_eq_sprayFlow]
    have hh := sprayFlow_minimizing_subinterval (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)
      hs.le hs1.le (show dist x (sprayFlow 1 ⟨x,p⟩).1 = 1*‖p‖ by rw [one_mul,←riemannianExp_eq_sprayFlow]; exact hp)
    exact hh
  have hh := squared_dist_divided_action_le z (riemannianExp x (s • p)) (riemannianExp x p) hs hs1
  rw [hseg] at hh
  unfold cost
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hs.ne', (sub_pos.mpr hs1).ne']

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_StrictDividedAction
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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma shifted_injectivityDomain_of_injectivityDomain {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ injectivityDomain x)
    {t : ℝ} (ht : 0≤t) (ht1 : t<1) :
    (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  obtain ⟨a,ha,hmin⟩ := hp
  have hden : 0<1-t := sub_pos.mpr ht1
  let b := (a-t)/(1-t)
  have hb : 1<b := (lt_div_iff₀ hden).mpr (by linarith)
  have hbt : b*(1-t)=a-t := div_mul_cancel₀ _ hden.ne'
  refine ⟨b,hb,?_⟩
  rw [smul_smul,hbt,riemannianExp_eq_sprayFlow]
  change dist (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
    (sprayFlow 1 (tangentScale (a-t) (sprayFlow t ⟨x,p⟩))).1 = _
  rw [sprayFlow_scale,mul_one,←sprayFlow_add,sub_add_cancel]
  have hm : dist x (sprayFlow a (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1=a*‖p‖ := by
    rw [←riemannianExp_smul]
    exact hmin
  change dist (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
    (sprayFlow a (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 = _
  rw [sprayFlow_minimizing_subinterval _ ht (ht1.trans ha).le hm]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hden,sprayFlow_speed,←mul_assoc,hbt]

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_BranchInverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_joint_exp_inverse_of_nonconjugate (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
    let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
    ∃ e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n),
      (e : Model n × Model n → Model n × Model n) =
        (fun q => (q.1, d (riemannianExp (χ.symm q).1 (χ.symm q).2))) ∧
      χ z ∈ e.source ∧ e.source ⊆ χ.target ∧
      (∀ q ∈ e.source, riemannianExp (χ.symm q).1 (χ.symm q).2 ∈ d.source) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  let f : Model n × Model n → Model n := fun q =>
    d (riemannianExp (χ.symm q).1 (χ.symm q).2)
  let S := χ.target ∩ (fun q => riemannianExp (χ.symm q).1 (χ.symm q).2) ⁻¹' d.source
  have hχz : χ z ∈ χ.target := χ.map_source (mem_extChartAt_source z)
  have hχinv : χ.symm (χ z)=z := χ.left_inv (mem_extChartAt_source z)
  have hχ : ContMDiffOn 𝓘(ℝ,Model n × Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ χ.symm χ.target :=
    contMDiffOn_extChartAt_symm z
  have hE : ContMDiffOn 𝓘(ℝ,Model n × Model n) 𝓘(ℝ,Model n) ∞
      (fun q => riemannianExp (χ.symm q).1 (χ.symm q).2) χ.target :=
    contMDiff_riemannianExp.comp_contMDiffOn hχ
  have hS : IsOpen S :=
    hE.continuousOn.isOpen_inter_preimage (isOpen_extChartAt_target z) (isOpen_extChartAt_source _)
  have hzS : χ z ∈ S := ⟨hχz,by change riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2 ∈ d.source; rw [hχinv]; exact mem_extChartAt_source _⟩
  have hd : ContMDiffOn 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d d.source := by
    simpa only [d,extChartAt_source] using (contMDiffOn_extChartAt (I := 𝓘(ℝ,Model n)) (n := ∞) (x := riemannianExp z.1 z.2))
  have hf : ContDiffOn ℝ ∞ f S :=
    (hd.comp (hE.mono (inter_subset_left)) (fun q hq => hq.2)).contDiffOn
  let τ := trivializationAt (Model n) (fun b : M => TangentSpace 𝓘(ℝ,Model n) b) z.1
  let L : TangentSpace 𝓘(ℝ,Model n) z.1 ≃L[ℝ] Model n :=
    τ.continuousLinearEquivAt ℝ z.1 (mem_baseSet_trivializationAt (Model n) _ z.1)
  have hχsecond : (χ z).2=L z.2 := rfl
  have hχfiber (w : Model n) : χ.symm ((χ z).1,w) =
      (⟨z.1,L.symm w⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    have hforward : χ (⟨z.1,L.symm w⟩ : TangentBundle 𝓘(ℝ,Model n) M) = ((χ z).1,w) := by
      apply Prod.ext
      · rfl
      · change L (L.symm w)=w
        exact L.apply_symm_apply w
    rw [←hforward]
    apply χ.left_inv
    exact (tangent_chart_source_iff z _).mpr (mem_extChartAt_source z.1)
  let F : TangentSpace 𝓘(ℝ,Model n) z.1 → Model n :=
    fun v => d (riemannianExp z.1 v)
  have hF : ContDiffAt ℝ ∞ F z.2 :=
    ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d (riemannianExp z.1 z.2) from
      contMDiffAt_extChartAt).comp z.2 (contMDiff_riemannianExp_fiber z.1 z.2)).contDiffAt
  have hFi : Function.Injective (fderiv ℝ F z.2) := hz
  have hpart : (fun w => f ((χ z).1,w)) = F ∘ L.symm := by
    funext w
    dsimp [f]
    rw [hχfiber]
  have hpartder : fderiv ℝ (fun w => f ((χ z).1,w)) (χ z).2 =
      (fderiv ℝ F z.2).comp (L.symm : Model n →L[ℝ] TangentSpace 𝓘(ℝ,Model n) z.1) := by
    rw [hpart,hχsecond]
    have hF' : HasFDerivAt F (fderiv ℝ F z.2) (L.symm (L z.2)) := by
      simpa only [L.symm_apply_apply] using (hF.differentiableAt (by simp)).hasFDerivAt
    exact (hF'.comp (L z.2) L.symm.hasFDerivAt).fderiv
  have hpi : (fderiv ℝ (fun w => f ((χ z).1,w)) (χ z).2).IsInvertible := by
    have hi : Function.Injective (fderiv ℝ (fun w => f ((χ z).1,w)) (χ z).2) := by
      rw [hpartder]
      exact hFi.comp L.symm.injective
    have hs := LinearMap.injective_iff_surjective.mp hi
    exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hi)
      (LinearMap.range_eq_top.mpr hs),rfl⟩
  have hi := first_coordinate_preserving_derivative_invertible
    ((hf.contDiffAt (hS.mem_nhds hzS)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hpi
  obtain ⟨e,he,hz',heS,heD,heInv⟩ := exists_smooth_local_diffeomorphism hS
    (contDiffOn_fst.prodMk hf) hzS hi
  exact ⟨e,he,hz',fun q hq => (heS hq).1,fun q hq => (heS hq).2,heD,heInv⟩

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_exp_branch (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ P : M×M → TangentBundle 𝓘(ℝ,Model n) M,
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P
        (z.1,riemannianExp z.1 z.2) ∧
      P (z.1,riemannianExp z.1 z.2)=z ∧
      (∀ᶠ r in 𝓝 z, P (r.1,riemannianExp r.1 r.2)=r) ∧
      (∀ᶠ q in 𝓝 (z.1,riemannianExp z.1 z.2),
        (P q).1=q.1 ∧ riemannianExp (P q).1 (P q).2=q.2) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let c := extChartAt 𝓘(ℝ,Model n) z.1
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  let y : M×M := (z.1,riemannianExp z.1 z.2)
  let J : M×M → Model n × Model n := fun q => (c q.1,d q.2)
  obtain ⟨e,he,hze,_,hend,_,hei⟩ := exists_joint_exp_inverse_of_nonconjugate z hz
  have hχz := χ.map_source (mem_extChartAt_source z)
  have hχinv : χ.symm (χ z)=z := χ.left_inv (mem_extChartAt_source z)
  have hJy : J y = e (χ z) := by
    rw [he]
    change (c z.1,d (riemannianExp z.1 z.2)) =
      ((χ z).1,d (riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2))
    rw [hχinv]
    rfl
  have hyT : J y ∈ e.target := by
    simpa only [hJy] using e.map_source hze
  have hiy : e.symm (J y)=χ z := by rw [hJy,e.left_inv hze]
  have hJ : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,Model n × Model n) ∞ J y := by
    have hc₀ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ c y.1 := contMDiffAt_extChartAt
    have hd₀ : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y.2 := contMDiffAt_extChartAt
    exact (hc₀.comp y contMDiffAt_fst).prodMk_space (hd₀.comp y contMDiffAt_snd)
  have hi := (hei.contDiffAt (e.open_target.mem_nhds hyT)).contMDiffAt.comp y hJ
  have hc : ContMDiffAt 𝓘(ℝ,Model n × Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ χ.symm
      (e.symm (J y)) :=
    (contMDiffOn_extChartAt_symm z).contMDiffAt
      ((isOpen_extChartAt_target z).mem_nhds (by simpa only [hiy] using hχz))
  let P : M×M → TangentBundle 𝓘(ℝ,Model n) M := fun q => χ.symm (e.symm (J q))
  have hP : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P y :=
    hc.comp y hi
  have hPy : P y = z := by dsimp [P]; rw [hiy,hχinv]
  refine ⟨P,hP,hPy,?_,?_⟩
  · have hχnear : ∀ᶠ r in 𝓝 z, χ r ∈ e.source :=
      (show ContinuousAt χ z from continuousAt_extChartAt z).preimage_mem_nhds (e.open_source.mem_nhds hze)
    filter_upwards [hχnear,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z] with r hre hrs
    have hJr : J (r.1,riemannianExp r.1 r.2)=e (χ r) := by
      rw [he]
      change (c r.1,d (riemannianExp r.1 r.2)) =
        ((χ r).1,d (riemannianExp (χ.symm (χ r)).1 (χ.symm (χ r)).2))
      rw [χ.left_inv hrs]
      rfl
    dsimp only [P]
    rw [hJr,e.left_inv hre,χ.left_inv hrs]
  · have hJnear : ∀ᶠ q in 𝓝 y, J q ∈ e.target :=
      hJ.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hyT)
    have hcnear : ∀ᶠ q : M×M in 𝓝 y, q.1 ∈ c.source :=
      (continuous_fst : Continuous (fun q : M×M => q.1)).continuousAt.preimage_mem_nhds
        (show c.source ∈ 𝓝 y.1 from extChartAt_source_mem_nhds z.1)
    have hdnear : ∀ᶠ q : M×M in 𝓝 y, q.2 ∈ d.source :=
      (continuous_snd : Continuous (fun q : M×M => q.2)).continuousAt.preimage_mem_nhds
        (show d.source ∈ 𝓝 y.2 from extChartAt_source_mem_nhds (riemannianExp z.1 z.2))
    filter_upwards [hJnear,hcnear,hdnear] with q hqJ hqc hqd
    have his := e.map_target hqJ
    have hmap := e.right_inv hqJ
    rw [he] at hmap
    constructor
    · change (χ.symm (e.symm (J q))).1=q.1
      rw [tangent_chart_symm_base]
      have hf := congrArg Prod.fst hmap
      change (e.symm (J q)).1=c q.1 at hf
      rw [hf,c.left_inv hqc]
    · apply d.injOn (hend _ his) hqd
      exact congrArg Prod.snd hmap

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_GraphProjection
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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

section
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma continuous_graphProjection (u : M → ℝ) (t : ℝ) :
    Continuous (graphProjection (n := n) u t) :=
  (contMDiff_riemannianExp (n := n) (M := M)).continuous.comp
    ((contMDiff_tangentScale (E := Model n) (M := M)).continuous.comp
      (continuous_const.prodMk continuous_subtype_val))

end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CutCharacterization
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

lemma joint_exp_locally_injective_of_nonconjugate (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ U : Set (TangentBundle 𝓘(ℝ,Model n) M), IsOpen U ∧ z ∈ U ∧
      InjOn (fun q : TangentBundle 𝓘(ℝ,Model n) M => (q.1,riemannianExp q.1 q.2)) U := by
  obtain ⟨P,_,_,hleft,_⟩ := exists_smooth_exp_branch z hz
  obtain ⟨U,hUP,hU,hzU⟩ := mem_nhds_iff.mp hleft
  refine ⟨U,hU,hzU,?_⟩
  exact (show LeftInvOn P
    (fun point : TangentBundle 𝓘(ℝ,Model n) M =>
      (point.1,riemannianExp point.1 point.2)) U from hUP).injOn

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_KernelRadial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exp_kernel_radial_orthogonal {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0) :
    inner ℝ p k=0 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hline : HasDerivAt (fun s : ℝ => p+s • k) k 0 := by
    convert! (hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const k) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  let F : V → M := fun v => (sprayFlow 1 (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
  have hf : riemannianExp x=F := funext (fun v => riemannianExp_eq_sprayFlow x v)
  have hkF : mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) F p k=0 := by
    rw [←hf]
    exact hk
  have hs : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,Model n) ∞ F := by
    rw [←hf]
    exact contMDiff_riemannianExp_fiber x
  have he := ((hs (p+(0:ℝ) • k)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := he.comp 0 hline.hasFDerivAt.hasMFDerivAt
  have hz : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) (fun s : ℝ => F (p+s • k)) 0 1=0 := by
    have hc := hcomp.mfderiv
    simp only [Function.comp_def] at hc
    rw [hc]
    change (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) F (p+(0:ℝ) • k)) ((1:ℝ) • k)=0
    rw [one_smul]
    convert! hkF using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    exact mfderiv_congr_point (by simp only [zero_smul,add_zero])
  have H := sprayFlow_gauss x p k (1:ℝ)
  rw [hz] at H
  have H' : inner ℝ (sprayFlow 1 (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2
      (0 : TangentSpace 𝓘(ℝ,Model n) (sprayFlow 1 (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)=inner ℝ p k := by
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul]
  simpa only [inner_zero_right] using H'.symm
end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exp_mfderiv_apply_eq_coordinate (x : M) (p k : TangentSpace 𝓘(ℝ,Model n) x) :
    mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=
      (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp x p) (riemannianExp x v)) p :
        TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] Model n) k := by
  have H := ((contMDiff_riemannianExp_fiber x p).mdifferentiableAt (by simp)).mfderiv
  have HH := congrArg (fun L => L k) H
  simp only [mfld_simps,chartAt_self_eq,Function.comp_def,fderivWithin_univ] at HH ⊢
  convert! HH using 1
  all_goals try with_reducible_and_instances rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_SplitLogInjective
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
section ExpCoordinates
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma coordinateEndpoint_contDiffAt (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source)
    (hy : riemannianExp z.1 z.2∈(extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)).source) :
    ContDiffAt ℝ ∞ (coordinateEndpoint c)
      (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c z) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)
  have hχ : ContMDiffAt 𝓘(ℝ,Model n×Model n) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ χ.symm (χ z) :=
    (contMDiffOn_extChartAt_symm c).contMDiffAt ((isOpen_extChartAt_target c).mem_nhds (χ.map_source hz))
  have hE := contMDiff_riemannianExp.contMDiffAt.comp (χ z) hχ
  have hd : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d (riemannianExp z.1 z.2) :=
    (contMDiffOn_extChartAt (n := ∞) (x := riemannianExp c.1 c.2)).contMDiffAt
      (by simpa only [extChartAt_source] using (isOpen_extChartAt_source _).mem_nhds hy)
  have hd' : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d
      (riemannianExp (χ.symm (χ z)).1 (χ.symm (χ z)).2) := by rwa [χ.left_inv hz]
  exact (hd'.comp (χ z) hE).contDiffAt

lemma coordinateEndpointVertical_apply (c z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z∈(extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c).source)
    (hy : riemannianExp z.1 z.2∈(extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)).source)
    (v : TangentSpace 𝓘(ℝ,Model n) z.1) :
    coordinateEndpointVertical c z
      ((trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1).continuousLinearMapAt ℝ z.1 v)=
    (trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)
      (riemannianExp c.1 c.2)).continuousLinearMapAt ℝ (riemannianExp z.1 z.2)
        (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) z.1) 𝓘(ℝ,Model n) (riemannianExp z.1) z.2 v) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)
  let X := TangentSpace 𝓘(ℝ,Model n) z.1
  let τ := trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1
  let L := τ.continuousLinearEquivAt ℝ z.1 (by simpa only [τ,TangentBundle.trivializationAt_baseSet,extChartAt_source] using (tangent_chart_source_iff c z).mp hz)
  let F : X → Model n := fun a => d (riemannianExp z.1 a)
  have hd : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d (riemannianExp z.1 z.2) :=
    (contMDiffOn_extChartAt (n := ∞) (x := riemannianExp c.1 c.2)).contMDiffAt
      (by simpa only [extChartAt_source] using (isOpen_extChartAt_source _).mem_nhds hy)
  have hF : ContDiffAt ℝ ∞ F z.2 :=
    (hd.comp z.2 (contMDiff_riemannianExp_fiber z.1 z.2)).contDiffAt
  have hpart : (fun w => coordinateEndpoint c ((χ z).1,w))=F ∘ L.symm := by
    funext w
    dsimp only [coordinateEndpoint,F,Function.comp_apply]
    rw [tangent_chart_fiber_inverse c z hz w]
  have hG := (coordinateEndpoint_contDiffAt c z hz hy).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hpartD := (hG.hasFDerivAt.comp (χ z).2
    ((hasFDerivAt_const (χ z).1 (χ z).2).prodMk (hasFDerivAt_id (χ z).2))).fderiv
  have hLz : (χ z).2=L z.2 := rfl
  have hFD : HasFDerivAt F (fderiv ℝ F z.2) (L.symm (χ z).2) := by
    rw [hLz,L.symm_apply_apply]
    exact (hF.differentiableAt (by simp)).hasFDerivAt
  have hRD := (hFD.comp (χ z).2 L.symm.hasFDerivAt).fderiv
  change fderiv ℝ (fun w => coordinateEndpoint c ((χ z).1,w)) (χ z).2 =
    (fderiv ℝ (coordinateEndpoint c) (χ z)).comp (inr ℝ _ _) at hpartD
  rw [hpart] at hpartD
  have hA : coordinateEndpointVertical c z=(fderiv ℝ F z.2).comp (L.symm : Model n →L[ℝ] X) :=
    hpartD.symm.trans hRD
  have hD := (hd.mdifferentiableAt (by simp)).hasMFDerivAt.comp z.2
    ((contMDiff_riemannianExp_fiber z.1 z.2).mdifferentiableAt (by simp)).hasMFDerivAt
  have hDE : fderiv ℝ F z.2=(mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d (riemannianExp z.1 z.2)).comp
      (mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp z.1) z.2) := by
    have hm := hD.mfderiv
    rw [mfderiv_eq_fderiv] at hm
    exact hm
  have hLv : τ.continuousLinearMapAt ℝ z.1 v=L v := by
    simp only [L,Trivialization.coe_continuousLinearEquivAt_eq]
  rw [hLv]
  rw [hA,ContinuousLinearMap.comp_apply]
  change fderiv ℝ F z.2 (L.symm (L v))=_
  rw [L.symm_apply_apply,hDE]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (by simpa only [extChartAt_source] using hy)]
  rfl

end ExpCoordinates
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_ExponentialJacobian
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
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExponentialJacobian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteExponentialJacobian_r7267b5_1 (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
lemma mfderiv_exp_zero_norm (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
      (riemannianExp (n := n) x) 0 v‖=‖v‖ := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,v⟩
  have hline : HasFDerivAt (fun t : ℝ => t • v)
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) 0 := (hasFDerivAt_id 0).smul_const v
  have he := ((contMDiff_riemannianExp_fiber x ((0:ℝ) • v)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hc := he.comp 0 hline.hasMFDerivAt
  have hs := hasMFDerivAt_spray_projection ((sprayFlow_curve z).isMIntegralCurveAt 0)
  have hfun : (fun t : ℝ => riemannianExp (n := n) x (t • v))=(fun t : ℝ => (sprayFlow t z).1) :=
    funext (riemannianExp_smul x v)
  have hsN : ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n)
      (fun t : ℝ => (sprayFlow t z).1) 0 1‖=‖v‖ := by
    rw [hs.mfderiv]
    change ‖(1 : ℝ) • (sprayFlow 0 z).2‖ = ‖v‖
    simpa only [one_smul] using sprayFlow_speed 0 z
  have hnorm := (congrArg (fun f : ℝ → M =>
    ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) f 0 1‖) hfun).trans hsN
  have hcm := hc.mfderiv
  simp only [Function.comp_def] at hcm
  rw [hcm] at hnorm
  change ‖mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) (riemannianExp (n := n) x)
    ((0:ℝ) • v) ((1:ℝ) • v)‖=‖v‖ at hnorm
  simp only [one_smul] at hnorm
  exact (congrArg (fun w : V => ‖mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n)
    (riemannianExp (n := n) x) w v‖) (zero_smul ℝ v)).symm.trans hnorm

end ExponentialJacobian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_ExpVertical
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
section ExpVertical
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma coordinateEndpointVertical_continuousAt (c : TangentBundle 𝓘(ℝ,Model n) M) :
    ContinuousAt (coordinateEndpointVertical c) c := by
  have hG := coordinateEndpoint_contDiffAt c c (mem_extChartAt_source c)
    (mem_extChartAt_source (riemannianExp c.1 c.2))
  have hG2 : ContDiffAt ℝ 2 (coordinateEndpoint c)
      (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c c) :=
    hG.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hD := (hG2.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hχ := (contMDiffAt_extChartAt (I := 𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (n := ∞) (x := c)).continuousAt
  exact (hD.comp hχ).clm_comp continuousAt_const

end ExpVertical
end WeakMTWTransport

end

end

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

lemma movingNormal_contMDiffAt {a : M} {q : Model n × Model n}
    (hq : q.1 ∈ (extChartAt 𝓘(ℝ,Model n) a).target) :
    ContMDiffAt 𝓘(ℝ,Model n × Model n) 𝓘(ℝ,Model n) ∞ (movingNormal a) q := by
  have hT : q ∈ (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).target :=
    (tangent_chart_target_iff _ q).mpr hq
  exact (contMDiff_riemannianExp (n := n) (M := M) _).comp q ((contMDiffOn_extChartAt_symm _).contMDiffAt ((isOpen_extChartAt_target _).mem_nhds hT))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_BranchExtension
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

lemma smooth_branch_normal_family {x : M} {r : TangentSpace 𝓘(ℝ,Model n) x}
    {T : ℝ} {G : M × M → ℝ}
    (hG : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (x,riemannianExp x (T • r))) :
    ContDiffAt ℝ ∞ (fun q : ℝ × TangentSpace 𝓘(ℝ,Model n) x =>
      G (riemannianExp x q.2,riemannianExp x (q.1 • r))) (T,0) := by
  have hG' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (riemannianExp (n := n) x 0,riemannianExp x (T • r)) := by simpa only [riemannianExp_zero] using hG
  have hL : ContMDiffAt 𝓘(ℝ,ℝ × TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ × TangentSpace 𝓘(ℝ,Model n) x => riemannianExp x q.2) (T,0) :=
    (contMDiff_riemannianExp_fiber x _).comp (T,0) contDiffAt_snd.contMDiffAt
  have hR : ContMDiffAt 𝓘(ℝ,ℝ × TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) ∞
      (fun q : ℝ × TangentSpace 𝓘(ℝ,Model n) x => riemannianExp x (q.1 • r)) (T,0) :=
    (contMDiff_riemannianExp_fiber x _).comp (T,0)
      (contDiffAt_fst.smul contDiffAt_const).contMDiffAt
  exact (hG'.comp (T,0) (hL.prodMk hR)).contDiffAt

lemma cost_branch_normal_eventuallyEq {x : M} {r : TangentSpace 𝓘(ℝ,Model n) x}
    {T : ℝ} {G : M × M → ℝ}
    (hagree : ∀ᶠ z in 𝓝 (⟨x,T • r⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      z.2 ∈ injectivityDomain z.1 →
        (fun q : M × M => cost q.1 q.2) =ᶠ[𝓝 (z.1,riemannianExp z.1 z.2)] G) :
    ∀ᶠ t in 𝓝 T, t • r ∈ injectivityDomain x →
      normalCost x (t • r) =ᶠ[𝓝 0] (fun h => G (riemannianExp x h,riemannianExp x (t • r))) := by
  have hi : Continuous (fun t : ℝ => (⟨x,t • r⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    (FiberBundle.continuous_totalSpaceMk (Model n) _ x).comp (continuous_id.smul continuous_const)
  filter_upwards [hi.continuousAt.eventually hagree] with t ht htID
  have hc : Tendsto (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      (riemannianExp x h,riemannianExp x (t • r))) (𝓝 0) (𝓝 (x,riemannianExp x (t • r))) := by
    have hcurve : ContinuousAt (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
        (riemannianExp x h,riemannianExp x (t • r))) 0 :=
      (contMDiff_riemannianExp_fiber x).continuous.continuousAt.prodMk continuousAt_const
    simpa only [riemannianExp_zero] using hcurve.tendsto
  exact (ht htID).comp_tendsto hc

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_PoleCoordinates
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
lemma coordinateBackward_of_derivative {a : M} (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z.1∈(extChartAt 𝓘(ℝ,Model n) a).source) {f : M → ℝ}
    (hf : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z.1 (innerSL ℝ z.2)) (t : ℝ) :
    coordinateBackward a (t,extChartAt 𝓘(ℝ,Model n) a z.1,
      fderiv ℝ (fun w => f ((extChartAt 𝓘(ℝ,Model n) a).symm w))
        (extChartAt 𝓘(ℝ,Model n) a z.1)) = (sprayFlow (-t) z).1 := by
  have hd := coordinate_gradient_of_hasMFDerivAt z hz f 1 (by simpa using hf)
  simp only [one_smul] at hd
  rw [coordinateBackward,hd.fderiv]
  have hT := (extChartAt 𝓘(ℝ,Model n) a).map_source hz
  have hi := riemannianCoordinateMetric_isInvertible hT
  rw [hi.inverse_apply_self]
  rw [movingNormal_eq hT, (extChartAt 𝓘(ℝ,Model n) a).left_inv hz,map_smul]
  have hbase : z.1∈(chartAt (Model n) a).source := by simpa only [extChartAt_source] using hz
  have hcoord : (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) z).2 =
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ z.1 z.2 := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hbase]
    rfl
  rw [hcoord]
  change riemannianExp z.1 ((-t) •
    ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ z.1
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ z.1 z.2))) = _
  rw [Trivialization.symmL_continuousLinearMapAt _ hbase,riemannianExp_smul]

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

lemma reverseRay_minimizing {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) :
    (reverseRay z).2∈minimizingVectors (reverseRay z).1 := by
  change dist (reverseRay z).1 (riemannianExp (reverseRay z).1 (reverseRay z).2)=‖(reverseRay z).2‖
  rw [riemannianExp_eq_sprayFlow]
  change dist (sprayFlow 1 z).1 (sprayFlow 1 (tangentScale (-1) (sprayFlow 1 z))).1=
    ‖(-1:ℝ) • (sprayFlow 1 z).2‖
  rw [sprayFlow_reverse,neg_one_smul,norm_neg,sprayFlow_speed]
  change dist (sprayFlow 1 z).1 z.1=‖z.2‖
  rw [dist_comm,←riemannianExp_eq_sprayFlow]
  exact hz

end WeakMTWTransport

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

lemma proper_suffix_endpoint (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ) :
    riemannianExp (sprayFlow h z).1 ((T-h) • (sprayFlow h z).2)=
      riemannianExp z.1 (T • z.2) := by
  rw [riemannianExp_smul,riemannianExp_smul,←sprayFlow_add,sub_add_cancel]

end ProperPieces
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_BranchCost2
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

lemma reverseRay_base (z : TangentBundle 𝓘(ℝ,Model n) M) :
    (reverseRay z).1=riemannianExp z.1 z.2 := by
  rw [riemannianExp_eq_sprayFlow]
  rfl

lemma reverseRay_endpoint (z : TangentBundle 𝓘(ℝ,Model n) M) :
    riemannianExp (reverseRay z).1 (reverseRay z).2=z.1 := by
  rw [←reverseRay_base,reverseRay_involutive]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_RadialHessian
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
section RadialHessian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exp_reverseRay_line (z : TangentBundle 𝓘(ℝ,Model n) M) (s : ℝ) :
    riemannianExp (reverseRay z).1 ((1-s) • (reverseRay z).2)=
      riemannianExp z.1 (s • z.2) := by
  rw [riemannianExp_smul,riemannianExp_smul]
  change (sprayFlow (1-s) (tangentScale (-1) (sprayFlow 1 z))).1=(sprayFlow s z).1
  rw [sprayFlow_scale,←sprayFlow_add]
  change (sprayFlow ((-1)*(1-s)+1) z).1=(sprayFlow s z).1
  congr 2
  ring

lemma normal_log_fderiv_injective {x y : M}
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hq : DifferentiableAt ℝ q 0)
    (hqr : ∀ᶠ a in 𝓝 0, riemannianExp y (q a)=riemannianExp x a) :
    Function.Injective (fderiv ℝ q 0) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  apply (injective_iff_map_eq_zero (fderiv ℝ q 0)).mpr
  intro v hv
  have he := (contMDiff_riemannianExp_fiber y (q 0)).mdifferentiableAt (by simp)
  have hD := (he.hasMFDerivAt.comp 0 hq.hasFDerivAt.hasMFDerivAt)
  have hqr' : (riemannianExp y ∘ q) =ᶠ[𝓝 0] riemannianExp x := hqr
  have hD' := hD.congr_of_eventuallyEq hqr'.symm
  have hE := hD'.mfderiv
  have hV : mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) 0 v=0 := by
    rw [hE]
    change mfderiv 𝓘(ℝ,Y) 𝓘(ℝ,Model n) (riemannianExp (n := n) y)
      (q 0) (fderiv ℝ q 0 v)=0
    rw [hv]
    exact (mfderiv 𝓘(ℝ,Y) 𝓘(ℝ,Model n) (riemannianExp (n := n) y) (q 0)).map_zero
  have hN : ‖mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp (n := n) x) 0 v‖=0 := by
    rw [hV,norm_zero]
  rw [mfderiv_exp_zero_norm] at hN
  exact norm_eq_zero.mp hN
end RadialHessian
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

lemma normal_log_fderiv_exp_norm {x y : M}
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (hq : DifferentiableAt ℝ q 0)
    (hqr : ∀ᶠ a in 𝓝 0, riemannianExp y (q a)=riemannianExp x a)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    ‖mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) y) 𝓘(ℝ,Model n)
      (riemannianExp y) (q 0) (fderiv ℝ q 0 v)‖=‖v‖ := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Y := TangentSpace 𝓘(ℝ,Model n) y
  have he := (contMDiff_riemannianExp_fiber y (q 0)).mdifferentiableAt (by simp)
  have hD := (he.hasMFDerivAt.comp 0 hq.hasFDerivAt.hasMFDerivAt)
  have hqr' : (riemannianExp y ∘ q) =ᶠ[𝓝 0] riemannianExp x := hqr
  have hD' := hD.congr_of_eventuallyEq hqr'.symm
  have hE := hD'.mfderiv
  have hN := mfderiv_exp_zero_norm x v
  rw [hE] at hN
  have he0 := hqr.self_of_nhds
  convert! hN using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [he0]

end RadialFactor
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

lemma proper_prefix_reverse_endpoint (z : TangentBundle 𝓘(ℝ,Model n) M) (h : ℝ) :
    riemannianExp (sprayFlow h z).1 ((-h) • (sprayFlow h z).2)=z.1 := by
  have H := reverseRay_endpoint (tangentScale h z)
  rw [reverseRay_prefix] at H
  exact H

lemma middle_normal_prefix (z : TangentBundle 𝓘(ℝ,Model n) M) (h : ℝ)
    (b : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) b=
      cost z.1 (riemannianExp (sprayFlow h z).1 b) := by
  unfold normalCost
  rw [proper_prefix_reverse_endpoint,cost_symm]

lemma middle_normal_suffix (z : TangentBundle 𝓘(ℝ,Model n) M) (h : ℝ)
    (b : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2) b=
      cost (riemannianExp (sprayFlow h z).1 b) (riemannianExp z.1 z.2) := by
  unfold normalCost
  rw [proper_suffix_endpoint,one_smul]

end MiddleHessian
end WeakMTWTransport

end

end

end

end OAI
end


