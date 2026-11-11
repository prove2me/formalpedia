-- Prove2me | Definitions.Def_OAIQ232A026
-- name    : OAIQ232A026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:21.475139+00:00
-- url     : https://prove2.me/theorems/afb1e78f-349d-4806-a338-b74c4b8f61f3
-- title:
--   Definitions bundle OAIQ232A026 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 31 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Contact_ActiveLocalGrowth`, `BiholderTransport_Convexity_FirstCutConvex`, `BiholderTransport_Coordinates_FiniteActiveGrowth`, `BiholderTransport_Coordinates_RadialIdentity`, `BiholderTransport_Coordinates_SplitAction`, `BiholderTransport_Coordinates_SplitPairing`, `BiholderTransport_CostGeometry_FirstCutLower`, `BiholderTransport_CostGeometry_FirstCutSegment`, `BiholderTransport_CostGeometry_SplitTrial`, `BiholderTransport_CostGeometry_StrictDividedAction`, `BiholderTransport_LinearAlgebra_ActualRadial`, `BiholderTransport_LinearAlgebra_CurvedBlowup`, `BiholderTransport_Regularity_LimitGeometry`, `BiholderTransport_Regularity_TrialBlowup`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundle `OAIQ232A024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A028` and `OAIQ232A029`; the proofs of `OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound`, `OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood`, `OAI.WeakMTWTransport.cTransform_ae_active_before_cut`, `OAI.WeakMTWTransport.cTransform_ae_normal_quadraticExpansion`, `OAI.WeakMTWTransport.chartJetMatrix_normal_identity`, `OAI.WeakMTWTransport.contact_selection_chart_differential_full`, `OAI.WeakMTWTransport.exists_actual_center_sequential_gain`, `OAI.WeakMTWTransport.exists_density_original_center_good`, `OAI.WeakMTWTransport.exists_fixedJoinMiddle_lower_crossing`, `OAI.WeakMTWTransport.exists_reverse_exp_divided_isotropic_gain`, `OAI.WeakMTWTransport.exists_reverse_exp_rescaled_fixedJoin_factor`, `OAI.WeakMTWTransport.exists_true_center_jet_gain`, `OAI.WeakMTWTransport.exists_uniform_center_support_pullback`, `OAI.WeakMTWTransport.exists_uniform_cost_upper_taylor`, `OAI.WeakMTWTransport.exists_uniform_divided_hessian_gap`, `OAI.WeakMTWTransport.exists_uniform_intrinsic_contact_bounds`, `OAI.WeakMTWTransport.exists_uniform_true_center_gain`, `OAI.WeakMTWTransport.mixed_intrinsic_det`, `OAI.WeakMTWTransport.normal_test_to_chart`, `OAI.WeakMTWTransport.original_chart_good_null` and `OAI.WeakMTWTransport.prefixDefect_taylor`.
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

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_RadialIdentity
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma shifted_injectivityDomain_near_zero {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) : ∀ᶠ t : ℝ in 𝓝 0,
    (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  let Z : ℝ → TangentBundle 𝓘(ℝ,Model n) M := fun t => tangentScale (1-t) (sprayFlow t ⟨x,p⟩)
  have hZ : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Z :=
    contMDiff_tangentScale.comp ((contMDiff_const.sub contMDiff_id).prodMk
      (contMDiff_sprayFlow.comp (contMDiff_id.prodMk contMDiff_const)))
  have hZ0 : Z 0=⟨x,p⟩ := by
    dsimp [Z]
    rw [sprayFlow_zero]
    simp [tangentScale]
  have hh : Z 0 ∈ {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ injectivityDomain z.1} := by
    rw [hZ0]; exact hp
  exact hZ.continuous.continuousAt.preimage_mem_nhds (isOpen_total_injectivityDomain.mem_nhds hh)

lemma normalCost_radial_fderiv_of_shift {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (xi : TangentSpace 𝓘(ℝ,Model n) x) {t : ℝ} (ht : t ≠ 0) (ht1 : t ≠ 1)
    (hp : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hf : DifferentiableAt ℝ (normalCost x p) (t • p)) :
    fderiv ℝ (normalCost x p) (t • p) xi = (t-1)*inner ℝ p xi := by
  have hD := cost_start_gradient_of_injectivityDomain hp
  rw [shifted_exp_endpoint] at hD
  have hD' : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (fun b => dist b (riemannianExp x p)^2/2)
      (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
      (innerSL ℝ ((-(1-t)) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2)) := by
    simpa only [cost,neg_smul] using hD
  have he : 1-t ≠ 0 := sub_ne_zero.mpr ht1.symm
  have H := spray_action_line_stationary x p xi t (1-t) he (riemannianExp x p) hD'
  have hv : HasDerivAt (fun s : ℝ => t • (p+s • xi)) (t • xi) 0 := by
    convert! (((hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const xi)).const_smul t) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hf' : HasFDerivAt (normalCost x p) (fderiv ℝ (normalCost x p) (t • p)) (t • (p+(0:ℝ) • xi)) := by
    simpa only [zero_smul,add_zero] using hf.hasFDerivAt
  have hfc := hf'.comp_hasDerivAt 0 hv
  have hn : HasDerivAt (fun s : ℝ => t*‖p+s • xi‖^2/2) (t*inner ℝ p xi) 0 := by
    convert! (((hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const xi)).norm_sq.const_mul t).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    simp
    ring
  have HH := hn.add (hfc.div_const (1-t))
  have hh : (t*inner ℝ p xi)+fderiv ℝ (normalCost x p) (t • p) (t • xi)/(1-t)=0 := by
    apply HH.unique
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    funext s
    simp only [normalCost,cost,riemannianExp_smul,Function.comp_def]
    rfl
  rw [map_smul,smul_eq_mul] at hh
  field_simp at hh
  have hh' : t * (fderiv ℝ (normalCost x p) (t • p) xi - (t-1)*inner ℝ p xi)=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh').resolve_left ht)

lemma normalCost_radial_fderiv_near_zero {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    (fun t : ℝ => fderiv ℝ (normalCost x p) (t • p) xi) =ᶠ[𝓝 0]
      (fun t : ℝ => (t-1)*inner ℝ p xi) := by
  have hf := normalCost_contDiffAt hp
  have hline : ContDiffAt ℝ ∞ (fun t : ℝ => t • p) 0 := contDiffAt_id.smul contDiffAt_const
  have hline0 : (0:ℝ) • p=0 := zero_smul ℝ p
  have hfnear : ∀ᶠ t : ℝ in 𝓝 0, DifferentiableAt ℝ (normalCost x p) (t • p) := by
    have hh : ∀ᶠ u in 𝓝 (0 : TangentSpace 𝓘(ℝ,Model n) x), ContDiffAt ℝ 1 (normalCost x p) u :=
      (hf.of_le (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num)
    have ht : Tendsto (fun t : ℝ => t • p) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt,hline0] using hline.continuousAt
    exact (ht.eventually hh).mono (fun _ h => h.differentiableAt (by norm_num))
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, t≠0 →
      fderiv ℝ (normalCost x p) (t • p) xi=(t-1)*inner ℝ p xi := by
    filter_upwards [shifted_injectivityDomain_near_zero hp,hfnear,
      eventually_ne_nhds (show (0:ℝ)≠1 by norm_num)] with t ht hft ht1
    exact fun htn => normalCost_radial_fderiv_of_shift xi htn ht1 ht hft
  have hleft : ContinuousAt (fun t : ℝ => fderiv ℝ (normalCost x p) (t • p) xi) 0 := by
    have hdf := (hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
    have hdf' : ContinuousAt (fderiv ℝ (normalCost x p)) ((0:ℝ) • p) := by rwa [hline0]
    exact (ContinuousAt.comp (f := fun t : ℝ => t • p) hdf' hline.continuousAt).clm_apply continuousAt_const
  have hright : ContinuousAt (fun t : ℝ => (t-1)*inner ℝ p xi) 0 := by fun_prop
  have heqpunct : (fun t : ℝ => fderiv ℝ (normalCost x p) (t • p) xi) =ᶠ[𝓝[≠] 0]
      (fun t : ℝ => (t-1)*inner ℝ p xi) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htn
    exact ht htn
  have heq0 := tendsto_nhds_unique_of_eventuallyEq
    (hleft.mono_left nhdsWithin_le_nhds) (hright.mono_left nhdsWithin_le_nhds) heqpunct
  filter_upwards [hnear] with t ht
  by_cases ht0 : t=0
  · simpa only [ht0] using heq0
  · exact ht ht0

lemma normalCost_radial_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (normalCost x p)) 0 p xi = inner ℝ p xi := by
  have hf := (normalCost_contDiffAt hp).of_le (m := 2)
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hd0 : HasDerivAt (fun t : ℝ => fderiv ℝ (normalCost x p) (t • p) xi)
      (fderiv ℝ (fderiv ℝ (normalCost x p)) 0 p xi) 0 := by
    simpa only [zero_add] using directional_fderiv_hasDerivAt hf p xi
  have heq := normalCost_radial_fderiv_near_zero hp xi
  have hright : HasDerivAt (fun t : ℝ => (t-1)*inner ℝ p xi) (inner ℝ p xi) 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).sub_const 1).mul_const (inner ℝ p xi) using 1; simp only [one_mul]
  exact hd0.unique (hright.congr_of_eventuallyEq heq)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_SplitAction
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma splitNormalAction_contact {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    splitNormalAction x t p (0,p)=normalCost x p 0 := by
  have hseg : dist (riemannianExp x (t • p)) (riemannianExp x p)=(1-t)*‖p‖ := by
    rw [riemannianExp_smul,riemannianExp_eq_sprayFlow]
    exact sprayFlow_minimizing_subinterval (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)
      ht.le ht1.le (by rw [one_mul,←riemannianExp_eq_sprayFlow]; exact hp)
  have H := minimizing_split_contact hp ht ht1
  unfold splitNormalAction normalCost
  rw [riemannianExp_zero]
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  unfold cost
  rw [hseg]
  field_simp

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_SplitPairing
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma normalCost_fderiv_zero {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (normalCost x p) 0 xi = -inner ℝ p xi := by
  have H := (normalCost_radial_fderiv_near_zero hp xi).self_of_nhds
  simpa only [zero_smul,zero_sub,neg_mul,one_mul] using H

lemma splitNormalAction_source_gradient {x : M} {p v : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hv : t • v ∈ injectivityDomain x)
    (hB : DifferentiableAt ℝ (splitNormalAction x t p) (0,v))
    (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (splitNormalAction x t p) (0,v) (xi,0) = -inner ℝ v xi := by
  have hnc := ((normalCost_contDiffAt hv).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have H := (hnc.mul_const t⁻¹).add_const
    (cost (riemannianExp x (t • v)) (riemannianExp x p)/(1-t))
  have hp₀ := (hasFDerivAt_id (𝕜 := ℝ) (0 : TangentSpace 𝓘(ℝ,Model n) x)).prodMk
    (hasFDerivAt_const v (0 : TangentSpace 𝓘(ℝ,Model n) x))
  have H' : HasFDerivAt (fun u => splitNormalAction x t p (u,v))
      (t⁻¹ • fderiv ℝ (normalCost x (t • v)) 0) 0 := by
    simpa only [splitNormalAction,normalCost,div_eq_mul_inv] using H
  have heq := (hB.hasFDerivAt.comp (f := fun u => (u,v)) 0 hp₀).unique H'
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A xi) heq
  change fderiv ℝ (splitNormalAction x t p) (0,v) (xi,0) =
    t⁻¹ * fderiv ℝ (normalCost x (t • v)) 0 xi at hh
  rw [normalCost_fderiv_zero hv,real_inner_smul_left] at hh
  rw [hh]
  field_simp

lemma splitNormalAction_mixed_pairing {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (xi k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (xi,0) (0,k) = -inner ℝ k xi := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let B := splitNormalAction x t p
  have hBc : ContDiffAt ℝ ∞ B (0,p) :=
    (splitNormalAction_contDiffAt hleft hright).comp (f := fun q : V×V => (p,q)) (0,p) (contDiffAt_const.prodMk contDiffAt_id)
  have hB₂ := hBc.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hdf := (hB₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hL : HasFDerivAt (fun v : V => ((0:V),v))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) p :=
    (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := ((hdf.hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).clm_apply
    (hasFDerivAt_const (xi,(0:V)) p)).fderiv
  have hnB : ∀ᶠ v : V in 𝓝 p, DifferentiableAt ℝ B (0,v) := by
    have hn := (hBc.of_le (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num)
    exact (hL.continuousAt.eventually hn).mono (fun _ h => h.differentiableAt (by norm_num))
  have hscale : Continuous (fun v : V => t • v) := by fun_prop
  have hnleft : ∀ᶠ v : V in 𝓝 p, t • v ∈ injectivityDomain x :=
    hscale.continuousAt.preimage_mem_nhds
      ((isOpen_injectivityDomain x).mem_nhds hleft)
  have heq : (fun v : V => fderiv ℝ B (0,v) (xi,0)) =ᶠ[𝓝 p]
      (fun v : V => -inner ℝ v xi) := by
    filter_upwards [hnB,hnleft] with v hv hvleft
    exact splitNormalAction_source_gradient ht hvleft hv xi
  have hinner : HasFDerivAt (fun v : V => -inner ℝ v xi) (-(innerSL ℝ xi)) p := by
    convert! ((innerSL ℝ xi).hasFDerivAt (x := p)).neg using 1
    all_goals try with_reducible_and_instances rfl
    funext v
    exact congrArg Neg.neg (real_inner_comm xi v)
  have H := congrArg (fun A : V →L[ℝ] ℝ => A k) (hd.symm.trans (heq.fderiv_eq.trans hinner.fderiv))
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,neg_apply] at H
  change fderiv ℝ (fderiv ℝ B) (0,p) (0,k) (xi,0) = -inner ℝ xi k at H
  rw [real_inner_comm] at H
  rwa [(hB₂.isSymmSndFDerivAt (by simp)).eq] at H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_ActualRadial
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma normalHessian_symm {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (v w : TangentSpace 𝓘(ℝ,Model n) x) :
    normalHessian x p v w = normalHessian x p w v :=
  ((normalCost_contDiffAt hp).isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eq v w

lemma hessianValue_eq_normalHessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    hessianValue x p v=normalHessian x p v v := by
  have H := iteratedDeriv_two_affine_line
    ((normalCost_contDiffAt hp).of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v
  simpa only [zero_add,normalCost,hessianValue,normalHessian] using H

lemma normalHessian_radial {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    normalHessian x p p v=inner ℝ p v := normalCost_radial_hessian hp v

lemma normalHessian_contracted_radial {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {r : ℝ} (hr : r≠0) (hp : r • p ∈ injectivityDomain x)
    (v : TangentSpace 𝓘(ℝ,Model n) x) : normalHessian x (r • p) p v=inner ℝ p v := by
  have H := normalHessian_radial hp v
  simp only [map_smul,smul_apply,real_inner_smul_left,smul_eq_mul] at H
  exact (mul_left_cancel₀ hr H)

lemma hessianValue_contracted_radial {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {r : ℝ} (hr : r≠0) (hp : r • p ∈ injectivityDomain x) :
    hessianValue x (r • p) p=‖p‖^2 := by
  rw [hessianValue_eq_normalHessian hp,normalHessian_contracted_radial hr hp,real_inner_self_eq_norm_sq]

lemma hessianValue_transverse_radial_identity {x : M} {p e : TangentSpace 𝓘(ℝ,Model n) x}
    {r s : ℝ} (hr : r≠0) (hp : r • (p+s • e) ∈ injectivityDomain x)
    (hortho : inner ℝ p e=0) :
    hessianValue x (r • (p+s • e)) p = ‖p‖^2+s^2*(hessianValue x (r • (p+s • e)) e-‖e‖^2) := by
  rw [hessianValue_eq_normalHessian hp,hessianValue_eq_normalHessian hp]
  have H1 := normalHessian_contracted_radial hr hp p
  have H2 := normalHessian_contracted_radial hr hp e
  have hep : inner ℝ e p=0 := by rw [real_inner_comm,hortho]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul,
    inner_add_left,real_inner_smul_left,hortho,hep,real_inner_self_eq_norm_sq,mul_zero,zero_add,add_zero] at H1 H2
  rw [normalHessian_symm hp e p] at H1
  nlinarith [congrArg (fun a : ℝ => s*a) H2]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_SplitTrial
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma splitTrialValue_eq_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (xi k : TangentSpace 𝓘(ℝ,Model n) x) :
    splitTrialValue x t xi k p =
      fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (xi,k) (xi,k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hc := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun q : V×V => (p,q)) (0,p) (contDiffAt_const.prodMk contDiffAt_id)
  simpa only [Function.comp_def,splitTrialValue,Prod.mk_add_mk,Prod.smul_mk,Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd,zero_add] using
    iteratedDeriv_two_affine_line (hc.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (xi,k)

lemma splitTrialValue_nonneg {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hp : p ∈ minimizingVectors x)
    (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    0 ≤ splitTrialValue x t 0 k p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let f : ℝ → ℝ := fun s => splitNormalAction x t p (0,p+s • k)
  have hmin : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro s
    change splitNormalAction x t p (0,p+(0:ℝ) • k) ≤ splitNormalAction x t p (0,p+s • k)
    simp only [zero_smul,add_zero,splitNormalAction_contact hp ht ht1]
    exact normalCost_le_splitNormalAction x p 0 (p+s • k) ht ht1
  have hp' : ContDiffAt ℝ ∞ (fun z : V×(V×V) => splitNormalAction x t z.1 z.2)
      (p,((0:V),p+(0:ℝ) • k)) := by simpa using splitNormalAction_contDiffAt hleft hright
  have hBc := hp'.comp
    (f := fun s : ℝ => (p,((0:V),p+s • k))) 0 (by fun_prop)
  have hfc : ContinuousAt f 0 := by exact hBc.continuousAt
  have H := localMin_second_deriv_nonneg hmin hfc
  simpa only [splitTrialValue,smul_zero,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero,f] using H

lemma splitTrialValue_schur {x : M} {p xi k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hp : p ∈ injectivityDomain x)
    (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hpair : inner ℝ k xi≠0) :
    0 < splitTrialValue x t 0 k p ∧
      hessianValue x p xi ≤ splitTrialValue x t xi 0 p-(inner ℝ k xi)^2/splitTrialValue x t 0 k p := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hf := (normalCost_contDiffAt hp).of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hBc := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun q : V×V => (p,q)) (0,p) (contDiffAt_const.prodMk contDiffAt_id)
  have hB := hBc.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hle : ∀ᶠ z : V×V in 𝓝 (0,p), normalCost x p z.1 ≤ splitNormalAction x t p z :=
    Filter.Eventually.of_forall (fun z => normalCost_le_splitNormalAction x p z.1 z.2 ht ht1)
  have heq := (splitNormalAction_contact (injectivityDomain_subset_minimizingVectors x hp) ht ht1).symm
  have hmix := splitNormalAction_mixed_pairing ht.ne' hleft hright xi k
  have hmixne : fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (xi,0) (0,k)≠0 := by
    rw [hmix]; exact neg_ne_zero.mpr hpair
  constructor
  · rw [splitTrialValue_eq_hessian hleft hright]
    exact upper_contact_block_positive hf hB hle heq xi k hmixne
  · rw [hessianValue_eq_normalHessian hp,splitTrialValue_eq_hessian hleft hright,
      splitTrialValue_eq_hessian hleft hright]
    have H := upper_contact_block_schur hf hB hle heq xi k hmixne
    dsimp only [Function.comp_def] at H
    rw [hmix,neg_sq] at H
    exact H
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_StrictDividedAction
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

lemma hessianValue_strict_radial_decrease {x : M} {p xi : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) {t : ℝ} (ht : 0<t) (ht1 : t<1) (hxi : xi≠0) :
    hessianValue x p xi<hessianValue x (t • p) xi/t := by
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  have hpair : inner ℝ xi xi≠0 := inner_self_ne_zero.mpr hxi
  obtain ⟨hpos,hSchur⟩ := splitTrialValue_schur ht ht1 hp hleft hright hpair
  rw [splitTrialValue_source] at hSchur
  exact lt_of_le_of_lt hSchur (sub_lt_self _ (div_pos (sq_pos_of_ne_zero hpair) hpos))

lemma divided_hessian_strict_decrease {x : M} {p xi : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) {t s : ℝ} (ht : 0<t) (hts : t < s) (hs : s<1)
    (hxi : xi≠0) : hessianValue x (s • p) xi/s<hessianValue x (t • p) xi/t := by
  have hs0 := ht.trans hts
  have hsp := contracted_minimizer_mem_injectivityDomain hp hs0 hs
  have hts0 : 0<t/s := div_pos ht hs0
  have hts1 : t/s<1 := (div_lt_one hs0).mpr hts
  have H := hessianValue_strict_radial_decrease hsp hts0 hts1 hxi
  rw [smul_smul,div_mul_cancel₀ _ hs0.ne'] at H
  have H' := div_lt_div_of_pos_right H hs0
  simpa only [div_div,div_mul_cancel₀ _ hs0.ne'] using H'
end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.contracted_transverse_concaveOn_set (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {xi : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    {C : Set (TangentSpace 𝓘(ℝ,Model n) x)} (hC : Convex ℝ C)
    (hID : ∀ p ∈ C, t • p ∈ injectivityDomain x)
    (hortho : ∀ p ∈ C, ∀ q ∈ C, inner ℝ xi (q-p)=0) :
    ConcaveOn ℝ C (fun p => hessianValue x (t • p) xi) := by
  refine ⟨hC,?_⟩
  intro p hp q hq a b ha hb hab
  have hline : ∀ s ∈ Icc (0:ℝ) 1, t • p+s • (t • (q-p)) ∈ injectivityDomain x := by
    intro s hs
    have heq : t • p+s • (t • (q-p))=t • ((1-s) • p+s • q) := by module
    rw [heq]
    exact hID _ (hC hp hq (sub_nonneg.mpr hs.2) hs.1 (by ring))
  have H := hmtw.transverse_concaveOn_injectivityDomain x (t • p) xi (t • (q-p))
    (convex_Icc 0 1) hline (by simp only [real_inner_smul_right,hortho p hp q hq,mul_zero])
  have hh := H.2 (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num) ha hb hab
  have heq : t • p+b • (t • (q-p))=t • (a • p+b • q) := by
    rw [show a=1-b by linarith]
    module
  have heq1 : t • p+t • (q-p)=t • q := by module
  simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,zero_smul,add_zero,one_smul,heq1,heq] using hh

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_FiniteActiveGrowth
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma normalCost_hasFDerivAt_zero {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) :
    HasFDerivAt (normalCost x p) (innerSL ℝ (-p)) 0 := by
  apply ((normalCost_contDiffAt hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.congr_fderiv
  ext v
  have H := (normalCost_radial_fderiv_near_zero hp v).self_of_nhds
  simpa only [zero_smul,zero_sub,neg_one_mul,innerSL_apply_apply,inner_neg_left] using H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Contact_ActiveLocalGrowth
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma active_split_lower_support {v : M → ℝ} (hv : Continuous v) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ minimizingVectors x)
    (hactive : contactGap (cTransform v) v x (riemannianExp x p)=0)
    {s : ℝ} (hs : 0 < s) (hs1 : s<1) (z : M) :
    -(cost z (riemannianExp x (s • p))-cost x (riemannianExp x (s • p)))/s ≤
      cTransform v z-cTransform v x := by
  let : Nonempty M := ⟨x⟩
  have hgap := cTransform_gap_nonneg hv z (riemannianExp x p)
  have hsplit := minimizing_split_upper_support hp hs hs1 z
  have hsame := minimizing_split_contact hp hs hs1
  dsimp only [contactGap] at hgap hactive
  rw [neg_sub,sub_div]
  linarith

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_TrialBlowup
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma split_regular_legs_eventually {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∀ᶠ w in 𝓝 p, t • w ∈ injectivityDomain x ∧
      (1-t) • (sprayFlow t (⟨x,w⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
        injectivityDomain (sprayFlow t (⟨x,w⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hL : ∀ᶠ w in 𝓝 p, t • w ∈ injectivityDomain x :=
    (show ContinuousAt (fun w : V => t • w) p from by fun_prop).preimage_mem_nhds
      ((isOpen_injectivityDomain x).mem_nhds hleft)
  let Z : V → TangentBundle 𝓘(ℝ,Model n) M :=
    fun w => tangentScale (1-t) (sprayFlow t ⟨x,w⟩)
  have hZ : ContMDiff 𝓘(ℝ,V) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Z :=
    contMDiff_tangentScale.comp (contMDiff_const.prodMk (contMDiff_spray_fiber x t))
  have hR : ∀ᶠ w in 𝓝 p, Z w ∈ {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ injectivityDomain z.1} :=
    hZ.continuous.continuousAt.preimage_mem_nhds (isOpen_total_injectivityDomain.mem_nhds hright)
  exact hL.and hR

lemma conjugate_radial_hessian_tendsto_atBot {x : M} {p xi k : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x)
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0)
    (hpair : inner ℝ k xi≠0) :
    Tendsto (fun r : ℝ => hessianValue x (r • p) xi) (𝓝[<] 1) atBot := by
  obtain ⟨t,ht,ht1,hleft,hright⟩ := exists_minimizing_two_regular_legs hp
  have hline : Tendsto (fun r : ℝ => r • p) (𝓝[<] 1) (𝓝 p) := by
    simpa only [one_smul] using
      (show ContinuousAt (fun r : ℝ => r • p) 1 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  have ha := ((splitTrialValue_contDiffAt hleft hright xi 0).continuousAt.tendsto).comp hline
  have hQ := ((splitTrialValue_contDiffAt hleft hright 0 k).continuousAt.tendsto).comp hline
  rw [splitTrialValue_conjugate_null ht ht1 hleft hright hk] at hQ
  have hnear : ∀ᶠ r : ℝ in 𝓝[<] 1,
      0 < splitTrialValue x t 0 k (r • p) ∧ hessianValue x (r • p) xi ≤
        splitTrialValue x t xi 0 (r • p)-(inner ℝ k xi)^2/splitTrialValue x t 0 k (r • p) := by
    filter_upwards [hline.eventually (split_regular_legs_eventually hleft hright),
      (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hr hr0 hr1
    exact splitTrialValue_schur ht ht1 (contracted_minimizer_mem_injectivityDomain hp hr0 hr1)
      hr.1 hr.2 hpair
  exact schur_ratio_tendsto_atBot ha hQ (sq_pos_of_ne_zero hpair) (hnear.mono (fun _ h => h.1))
    (hnear.mono (fun _ h => h.2))
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_FirstCutLower
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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.firstcut_kernel_transverse_orthogonal (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {p e k : TangentSpace 𝓘(ℝ,Model n) x} {a b : ℝ}
    (ha : a<0) (hb : 0<b)
    (hseg : ∀ s ∈ Icc a b, p+s • e ∈ minimizingVectors x)
    (hleft : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+a • e)) (riemannianExp x v)) (p+a • e)))
    (hright : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+b • e)) (riemannianExp x v)) (p+b • e)))
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0)
    (xi : TangentSpace 𝓘(ℝ,Model n) x) (hortho : inner ℝ xi e=0) : inner ℝ xi k=0 := by
  by_contra hpair
  have hp : p ∈ minimizingVectors x := by simpa using hseg 0 ⟨ha.le,hb.le⟩
  have hneg := conjugate_radial_hessian_tendsto_atBot hp hk
    (by rwa [real_inner_comm] : inner ℝ k xi≠0)
  obtain ⟨L,hL⟩ := hmtw.firstcut_transverse_lower ha hb hseg hleft hright hortho
  have hlo : ∀ᶠ r : ℝ in 𝓝[<] 1, L≤hessianValue x (r • p) xi :=
    hL.mono (fun r hr => by simpa using hr 0 ⟨ha.le,hb.le⟩)
  obtain ⟨r,hr,hrr⟩ := (hlo.and (hneg.eventually (eventually_lt_atBot L))).exists
  exact (not_lt_of_ge hr) hrr
end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.firstcut_radial_lower (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {p e : TangentSpace 𝓘(ℝ,Model n) x} {b : ℝ}
    (hb : 0<b) (hseg : ∀ s ∈ Icc 0 b, p+s • e ∈ minimizingVectors x)
    (hright : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+b • e)) (riemannianExp x v)) (p+b • e)))
    (hortho : inner ℝ p e=0) :
    ∃ D : ℝ, ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ s ∈ Icc 0 b,
      -D * s ≤ s^2 * hessianValue x (r • (p+s • e)) e := by
  have hp : p ∈ minimizingVectors x := by simpa using hseg 0 ⟨le_rfl,hb.le⟩
  obtain ⟨C,hC⟩ := nonconjugate_inward_hessian_bounded (hseg b ⟨hb.le,le_rfl⟩) hright p
  let D := (C+‖p‖^2)/b
  refine ⟨D,?_⟩
  filter_upwards [hC,
    (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hrC hr0 hr1
  have hconc := hmtw.contracted_segment_concaveOn hseg hr0 hr1 hortho
  have hconv := hconc.neg.add_const (‖p‖^2)
  have hrad0 := hessianValue_contracted_radial hr0.ne'
    (contracted_minimizer_mem_injectivityDomain hp hr0 hr1)
  have hz : -hessianValue x (r • (p+(0:ℝ) • e)) p+‖p‖^2=0 := by
    simp only [zero_smul,add_zero,hrad0,neg_add_cancel]
  have hend : -hessianValue x (r • (p+b • e)) p+‖p‖^2≤D*b := by
    have hd : D*b=C+‖p‖^2 := div_mul_cancel₀ _ hb.ne'
    rw [hd]
    linarith [neg_le_of_abs_le hrC]
  intro s hs
  have hlin := convex_linear_bound hb hconv hz hend hs
  have hrad := hessianValue_transverse_radial_identity hr0.ne'
    (contracted_minimizer_mem_injectivityDomain (hseg s hs) hr0 hr1) hortho
  dsimp only [Pi.neg_apply,Pi.add_apply] at hlin
  nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg ‖e‖)]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_CurvedBlowup
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma conjugate_curved_hessian_upper {x : M} {p e xi k : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x)
    (hseg : ∀ᶠ s : ℝ in 𝓝 0, p+s • e ∈ minimizingVectors x)
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0)
    (hpair : inner ℝ k xi≠0) :
    ∃ eps B c : ℝ, 0<eps ∧ 0 < c ∧ ∀ s ∈ Ioo 0 eps,
      hessianValue x ((1-s^2) • (p+s • e)) xi ≤ B-c/s^2 := by
  obtain ⟨t,ht,ht1,hleft,hright⟩ := exists_minimizing_two_regular_legs hp
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let Q := splitTrialValue x t 0 k
  let a := splitTrialValue x t xi 0
  have hQ0 : Q p=0 := splitTrialValue_conjugate_null ht ht1 hleft hright hk
  have hQ : ContDiffAt ℝ 2 Q p := (splitTrialValue_contDiffAt hleft hright 0 k).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hlinear : Tendsto (fun s : ℝ => p+s • e) (𝓝 0) (𝓝 p) := by
    simpa only [zero_smul,add_zero] using
      (show ContinuousAt (fun s : ℝ => p+s • e) 0 from by fun_prop).tendsto
  have hQmin : ∀ᶠ s : ℝ in 𝓝 0, 0≤Q (p+s • e) := by
    filter_upwards [hseg,hlinear.eventually (split_regular_legs_eventually hleft hright)] with s hs hh
    exact splitTrialValue_nonneg ht ht1 hs hh.1 hh.2
  obtain ⟨eps,C,heps,hC,hquad⟩ := contDiffAt_curved_quadratic_upper hQ hQ0 hQmin
  let W : ℝ → V := fun s => (1-s^2) • (p+s • e)
  have hW0 : W 0=p := by simp [W]
  have hW : Tendsto W (𝓝 0) (𝓝 p) := by
    simpa only [hW0] using (show ContinuousAt W 0 from by dsimp [W]; fun_prop).tendsto
  have ha : ∀ᶠ s : ℝ in 𝓝 0, a (W s)<a p+1 :=
    ((splitTrialValue_contDiffAt hleft hright xi 0).continuousAt.tendsto.comp hW).eventually_lt_const
      (show a p<a p+1 by linarith)
  have hnear := ha.and (hseg.and (hW.eventually (split_regular_legs_eventually hleft hright)))
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min eps (min d 1),a p+1,(inner ℝ k xi)^2/C,
    lt_min heps (lt_min hd zero_lt_one),div_pos (sq_pos_of_ne_zero hpair) hC,?_⟩
  intro s hs
  have hseps := hs.2.trans_le (min_le_left eps (min d 1))
  have hsd := hs.2.trans_le ((min_le_right eps (min d 1)).trans (min_le_left d 1))
  have hs1 := hs.2.trans_le ((min_le_right eps (min d 1)).trans (min_le_right d 1))
  have hh := hball (show s ∈ Metric.ball (0:ℝ) d by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hs.1] using hsd)
  have hr : 0<1-s^2 := by nlinarith [mul_pos hs.1 (sub_pos.mpr hs1)]
  have hr1 : 1-s^2<1 := by nlinarith [sq_pos_of_pos hs.1]
  have hID : W s ∈ injectivityDomain x := contracted_minimizer_mem_injectivityDomain hh.2.1 hr hr1
  obtain ⟨hpos,hSchur⟩ := splitTrialValue_schur ht ht1 hID hh.2.2.1 hh.2.2.2 hpair
  have hq := hquad s ⟨hs.1,hseps⟩
  have hdiv : (inner ℝ k xi)^2/(C*s^2) ≤ (inner ℝ k xi)^2/Q (W s) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hpos hq
  have hid : (inner ℝ k xi)^2/(C*s^2)=((inner ℝ k xi)^2/C)/s^2 := by rw [div_div]
  rw [hid] at hdiv
  exact hSchur.trans (by change a (W s)-(inner ℝ k xi)^2/Q (W s)≤a p+1-_; linarith [hh.1])
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_CostGeometry_FirstCutSegment
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.firstcut_segment_kernel_zero (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {p e k : TangentSpace 𝓘(ℝ,Model n) x} {a b : ℝ}
    (ha : a<0) (hb : 0<b) (he : e≠0)
    (hseg : ∀ s ∈ Icc a b, p+s • e ∈ minimizingVectors x)
    (hleft : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+a • e)) (riemannianExp x v)) (p+a • e)))
    (hright : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+b • e)) (riemannianExp x v)) (p+b • e)))
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0) :
    k=0 := by
  by_contra hk0
  have hpar := kernel_parallel_of_transverse_orthogonal_ne_zero he
    (hmtw.firstcut_kernel_transverse_orthogonal ha hb hseg hleft hright hk)
  have hpair : inner ℝ k e≠0 := by
    intro hh
    rw [hh,zero_div,zero_smul] at hpar
    exact hk0 hpar
  have hortho : inner ℝ p e=0 := by
    have hh := exp_kernel_radial_orthogonal hk
    rw [hpar,real_inner_smul_right] at hh
    exact (mul_eq_zero.mp hh).resolve_left (div_ne_zero hpair (inner_self_ne_zero.mpr he))
  have hp : p ∈ minimizingVectors x := by simpa using hseg 0 ⟨ha.le,hb.le⟩
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, p+s • e ∈ minimizingVectors x := by
    filter_upwards [Ioo_mem_nhds ha hb] with s hs
    exact hseg s ⟨hs.1.le,hs.2.le⟩
  obtain ⟨eps,B,c,heps,hc,hupper⟩ := conjugate_curved_hessian_upper hp hnear hk hpair
  obtain ⟨D,hD⟩ := hmtw.firstcut_radial_lower hb
    (fun s hs => hseg s ⟨ha.le.trans hs.1,hs.2⟩) hright hortho
  have hcurve : Tendsto (fun s : ℝ => 1-s^2) (𝓝[>] 0) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (show ContinuousAt (fun s : ℝ => 1-s^2) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 1-s^2<1
      have hs0 : 0 < s := hs
      nlinarith [sq_pos_of_pos hs0]
  have hpoly : ∀ᶠ s : ℝ in 𝓝[>] 0, c≤D*s+B*s^2 := by
    filter_upwards [hcurve.eventually hD,self_mem_nhdsWithin,
      (eventually_lt_nhds heps).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with s hs hs0 hseps hsb
    have hspos : 0 < s := hs0
    have hlo := hs s ⟨hspos.le,hsb.le⟩
    have hhi := hupper s ⟨hspos,hseps⟩
    have hdiv : c/s^2≤B-hessianValue x ((1-s^2) • (p+s • e)) e := by linarith
    have hmul := (div_le_iff₀ (sq_pos_of_pos hspos)).mp hdiv
    nlinarith
  have htend : Tendsto (fun s : ℝ => D*s+B*s^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (show ContinuousAt (fun s : ℝ => D*s+B*s^2) 0 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  have hc0 : c≤0 := le_of_tendsto_of_tendsto tendsto_const_nhds htend hpoly
  exact (not_le_of_gt hc) hc0
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_FirstCutConvex
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.convex_nonconjugate_subset (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {C : Set (TangentSpace 𝓘(ℝ,Model n) x)}
    (hC : Convex ℝ C) (hmin : C ⊆ minimizingVectors x) :
    Convex ℝ {p | p ∈ C ∧ Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p)} := by
  intro u hu v hv a b ha hb hab
  refine ⟨hC hu.1 hv.1 ha hb hab,?_⟩
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa only [ha0,hb1,zero_smul,zero_add,one_smul] using hv.2
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    simpa only [hb0,ha1,zero_smul,add_zero,one_smul] using hu.2
  by_cases huv : u=v
  · have heq : a • u+b • v=v := by rw [huv,←add_smul,hab,one_smul]
    rw [heq]
    exact hv.2
  let p := a • u+b • v
  let e := v-u
  have he : e≠0 := sub_ne_zero.mpr (Ne.symm huv)
  have hleftEq : p+(-b) • e=u := by
    dsimp [p,e]
    rw [show a=1-b by linarith]
    module
  have hrightEq : p+a • e=v := by
    dsimp [p,e]
    rw [show b=1-a by linarith]
    module
  have hseg : ∀ s ∈ Icc (-b) a, p+s • e ∈ minimizingVectors x := by
    intro s hs
    have hq : p+s • e=(a-s) • u+(b+s) • v := by dsimp [p,e]; module
    rw [hq]
    exact hmin (hC hu.1 hv.1 (sub_nonneg.mpr hs.2) (by linarith [hs.1]) (by linarith))
  have hleft : Function.Injective (fderiv ℝ (fun w => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+(-b) • e)) (riemannianExp x w)) (p+(-b) • e)) := by
    rw [hleftEq]
    exact hu.2
  have hright : Function.Injective (fderiv ℝ (fun w => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+a • e)) (riemannianExp x w)) (p+a • e)) := by
    rw [hrightEq]
    exact hv.2
  let D := fderiv ℝ (fun w => extChartAt 𝓘(ℝ,Model n) (riemannianExp x p) (riemannianExp x w)) p
  have hzero (k) (hk : D k=0) : k=0 := by
    apply hmtw.firstcut_segment_kernel_zero (neg_neg_iff_pos.mpr (lt_of_le_of_ne hb (Ne.symm hb0)))
      (lt_of_le_of_ne ha (Ne.symm ha0)) he hseg hleft hright
    rw [exp_mfderiv_apply_eq_coordinate]
    exact hk
  intro k l hkl
  apply sub_eq_zero.mp
  apply hzero (k-l)
  rw [map_sub,hkl,sub_self]

lemma WeakMTW.convexHull_nonconjugate (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {S : Set (TangentSpace 𝓘(ℝ,Model n) x)}
    (hmin : convexHull ℝ S ⊆ minimizingVectors x)
    (hreg : ∀ p ∈ S, Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p))
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ convexHull ℝ S) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p) := by
  have hsub : S ⊆ {q | q ∈ convexHull ℝ S ∧ Function.Injective (fderiv ℝ (fun v =>
      extChartAt 𝓘(ℝ,Model n) (riemannianExp x q) (riemannianExp x v)) q)} :=
    fun q hq => ⟨subset_convexHull ℝ S hq,hreg q hq⟩
  exact (convexHull_min hsub (hmtw.convex_nonconjugate_subset (convex_convexHull ℝ S) hmin) hp).2
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

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff Pointwise

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.active_hull_nonconjugate_of_minimizing
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} {x : M}
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hmin : ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), T • p ∈ minimizingVectors x)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x)) :
    Function.Injective (fderiv ℝ (fun q => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (T • p)) (riemannianExp x q)) (T • p)) := by
  apply hmtw.convexHull_nonconjugate (S := T • activeLogs (n := n) v x)
  · rw [convexHull_smul]
    rintro _ ⟨q,hq,rfl⟩
    exact hmin q hq
  · rintro _ ⟨q,hq,rfl⟩
    exact riemannianExp_interior_nonconjugate
      (contracted_minimizer_mem_injectivityDomain hq.1 hT hT1)
  · rw [convexHull_smul]
    exact ⟨p,hp,rfl⟩

end

open Set Filter
open scoped Topology

end WeakMTWTransport

end

end OAI
end


