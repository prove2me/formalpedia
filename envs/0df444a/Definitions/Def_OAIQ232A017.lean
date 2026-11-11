-- Prove2me | Definitions.Def_OAIQ232A017
-- name    : OAIQ232A017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:56:53.128694+00:00
-- url     : https://prove2.me/theorems/453130ee-d162-45ef-b429-578d32b60286
-- title:
--   Definitions bundle OAIQ232A017 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 10 definitions and 32 theorems. The definitions and types are `OAI.WeakMTWTransport.boundedCTransform`, `OAI.WeakMTWTransport.classOscillation`, `OAI.WeakMTWTransport.classSectionOscillations`, `OAI.WeakMTWTransport.coordinatePhaseFlow`, `OAI.WeakMTWTransport.densityDualClass`, `OAI.WeakMTWTransport.middleCenteredAction`, `OAI.WeakMTWTransport.middleHessian`, `OAI.WeakMTWTransport.middleHessianOperator`, `OAI.WeakMTWTransport.normalizedDualPairs`, `OAI.WeakMTWTransport.reverseRay`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Coordinates_ProperPieces`, `BiholderTransport_Coordinates_UniformShort`, `BiholderTransport_Duality_CompactDual`, `BiholderTransport_Geodesics_EndpointIdentity`, `BiholderTransport_Geodesics_GeodesicExistence`, `BiholderTransport_Geodesics_GlobalGauss`, `BiholderTransport_Geodesics_IntegratedGauss`, `BiholderTransport_Geodesics_MinimizingSubinterval`, `BiholderTransport_Geodesics_NoCorner`, `BiholderTransport_Geodesics_ShortGradient`, `BiholderTransport_Geodesics_SprayActionMinimum`, `BiholderTransport_Geodesics_SprayDistanceBound`, `BiholderTransport_Geodesics_SprayMinimizerUnique`, `BiholderTransport_Geodesics_SprayScaling`, `BiholderTransport_LinearAlgebra_CompactQuadratic`, `BiholderTransport_LinearAlgebra_SpectralContinuity`, `BiholderTransport_LocalFlow_CotangentFlow`, `BiholderTransport_Oscillation_SectionOscillation`, `BiholderTransport_Regularity_MetricDefinitions`, `BiholderTransport_Regularity_Reversal`, `BiholderTransport_Regularity_ReverseRegular`, `BiholderTransport_Volume_RadialCalibration`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A013` and `OAIQ232A016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A019` and `OAIQ232A020`; the statements `OAI.WeakMTWTransport.CenterSequenceData.true_ray_compact`, `OAI.WeakMTWTransport.WeakMTW.class_power`, `OAI.WeakMTWTransport.WeakMTW.exists_local_branch_jet_bound_second`, `OAI.WeakMTWTransport.WeakMTW.exists_local_outer_chart_jet_bound`, `OAI.WeakMTWTransport.WeakMTW.exists_locally_uniform_test_det_bound`, `OAI.WeakMTWTransport.WeakMTW.exists_normal_relative_hessian_bound`, `OAI.WeakMTWTransport.WeakMTW.exists_original_outer_limit`, `OAI.WeakMTWTransport.WeakMTW.exists_strict_test_det_bound`, `OAI.WeakMTWTransport.WeakMTW.exists_uniform_active_outer_matrix`, `OAI.WeakMTWTransport.WeakMTW.exists_uniform_chart_outer_matrix`, `OAI.WeakMTWTransport.WeakMTW.exists_uniform_intrinsic_test_det_bound`, `OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_normal_det_bound_second`, `OAI.WeakMTWTransport.WeakMTW.exists_uniform_outer_true_matrix`, `OAI.WeakMTWTransport.WeakMTW.maximum_template_bound`, `OAI.WeakMTWTransport.WeakMTW.modified_outer_neighborhood`, `OAI.WeakMTWTransport.WeakMTW.test_det_bound_on_charts`, `OAI.WeakMTWTransport.WeakMTW.uniform_three_determinant_closure` and `OAI.WeakMTWTransport.exists_density_original_center_good`.
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
import Definitions.Def_OAIQ232A013
import Definitions.Def_OAIQ232A016

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_RadialCalibration
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normal_chart_radial_path_bound
    (e : OpenPartialHomeomorph E E) (he : ContDiffOn ℝ 1 e e.source)
    (hi : ContDiffOn ℝ 1 e.symm e.target) (h0 : (0:E) ∈ e.source)
    (g₀ : E →L[ℝ] E →L[ℝ] ℝ) (hg₀ : ∀ v, 0 ≤ g₀ v v)
    (hsym₀ : ∀ u v, g₀ u v = g₀ v u)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ y ∈ e.target, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ e.target, ∀ u v, g y u v = g y v u)
    (V : E → E) {τ : ℝ} (hτ : 0 ≤ τ)
    (henergy : ∀ y ∈ e.target, g y (V y) (V y) = g₀ (e.symm y) (e.symm y))
    (hgauss : ∀ y ∈ e.target, ∀ w,
      g y (V y) ((fderiv ℝ e (e.symm y)) w) = τ * g₀ (e.symm y) w)
    {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (himg : MapsTo γ (Icc a b) e.target)
    (ha : γ a = e 0) :
    ENNReal.ofReal (τ * Real.sqrt (g₀ (e.symm (γ b)) (e.symm (γ b)))) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g (γ t) (deriv γ t) (deriv γ t))) := by
  let ζ : ℝ → E := e.symm ∘ γ
  have hζ : ContDiffOn ℝ 1 ζ (Icc a b) := hi.comp hγ himg
  have hζa : ζ a = 0 := by simp only [ζ,Function.comp_apply,ha,e.left_inv h0]
  apply radial_calibration_length_lower_bound g₀ hg₀ hsym₀ hab hτ hζ hζa _
    (fun _ _ => Real.sqrt_nonneg _) ?_
  intro t ht
  have hmem := himg (Ioo_subset_Icc_self ht)
  have hγd := (hγ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero
  have hid := (hi.contDiffAt (e.open_target.mem_nhds hmem)).differentiableAt one_ne_zero
  have hed := (he.contDiffAt (e.open_source.mem_nhds (e.map_target hmem))).differentiableAt one_ne_zero
  have hζd := hid.hasFDerivAt.comp_hasDerivAt t hγd.hasDerivAt
  change |τ * g₀ (e.symm (γ t)) (deriv ζ t)| ≤ _
  rw [hζd.deriv]
  exact normal_chart_gauss_dual_bound e hmem hed hid g₀ (g (γ t))
    (hg _ hmem) (hsym _ hmem) (V (γ t)) (henergy _ hmem) (hgauss _ hmem) _

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayScaling
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

variable [T2Space M] [CompactSpace M]

lemma sprayFlow_scale (z : TangentBundle 𝓘(ℝ,E) M) (c t : ℝ) :
    sprayFlow t (tangentScale c z) = tangentScale c (sprayFlow (c*t) z) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (contMDiff_geodesicSpray.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (sprayFlow_curve (tangentScale c z))
    (isMIntegralCurve_spray_scaled (sprayFlow_curve z) c)
    (by simp only [sprayFlow_zero,mul_zero])
  exact congrFun he t

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_EndpointIdentity
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
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma hasDerivAt_spray_coordinate_zero (a : M) (v : TangentSpace 𝓘(ℝ,E) a) :
    HasDerivAt (fun t => extChartAt 𝓘(ℝ,E) a (sprayFlow t ⟨a,v⟩).1) v 0 := by
  have hd := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt 0
    (spray_chart_hasDerivAt ((sprayFlow_curve (⟨a,v⟩ : TangentBundle 𝓘(ℝ,E) M)).isMIntegralCurveAt 0))
  simp only [sprayFlow_zero,tangent_chart_apply,coordinateGeodesicField,
    Function.comp_def,ContinuousLinearMap.coe_fst'] at hd
  have he : tangentCoordChange 𝓘(ℝ,E) a a a v = v :=
    tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ,E)) a)
  rw [he] at hd
  exact hd

lemma coordinate_flow_endpoint_derivative_zero (a : M) {r τ : ℝ} (hr : 0 < r)
    {Φ : ℝ × (E × E) → E × E}
    (hΦ : ContDiffOn ℝ ∞ Φ
      (Ioo (-r) r ×ˢ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r))
    (hΦ0 : ∀ z ∈ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r, Φ (0,z) = z)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r,
      (Φ (t,z)).1 ∈ (extChartAt 𝓘(ℝ,E) a).target ∧
      HasDerivAt (fun s => Φ (s,z)) (coordinateGeodesicField (riemannianCoordinateMetric a) (Φ (t,z))) t)
    (hτ : τ ∈ Ioo (-r) r) :
    fderiv ℝ (fun v : E => (Φ (τ,extChartAt 𝓘(ℝ,E) a a,v)).1) 0 =
      τ • ContinuousLinearMap.id ℝ E := by
  let x := extChartAt 𝓘(ℝ,E) a a
  let ψ : E → E := fun v => (Φ (τ,x,v)).1
  have hψ : DifferentiableAt ℝ ψ 0 :=
    (((hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds
      ⟨hτ,Metric.mem_ball_self hr⟩)).comp 0
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).fst).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq : ∀ v ∈ Metric.ball (0:E) r,
      ψ v = extChartAt 𝓘(ℝ,E) a (sprayFlow τ ⟨a,v⟩).1 := by
    intro v hv
    have hz : (x,v) ∈ Metric.ball (x,0) r := by
      simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_lt_iff] using And.intro hr hv
    let z : TangentBundle 𝓘(ℝ,E) M := ⟨a,0⟩
    have H := sprayFlow_eq_coordinate_curve z hr
      (fun t ht => (hode t ht (x,v) hz).1)
      (fun t ht => (hode t ht (x,v) hz).2)
      (show (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z).symm (Φ (0,x,v)) = ⟨a,v⟩ by
        rw [hΦ0 (x,v) hz]; exact tangent_chart_at_self_base_symm z v) hτ
    have Hc := congrArg (fun p : TangentBundle 𝓘(ℝ,E) M => extChartAt 𝓘(ℝ,E) a p.1) H
    rw [tangent_chart_symm_base,(extChartAt 𝓘(ℝ,E) a).right_inv (hode τ hτ (x,v) hz).1] at Hc
    exact Hc.symm
  ext w
  have hn : ∀ᶠ s : ℝ in 𝓝 0, s • w ∈ Metric.ball (0:E) r :=
    ((continuousAt_id.smul continuousAt_const) :
      ContinuousAt (fun s : ℝ => s • w) 0).preimage_mem_nhds
      (by
        change Metric.ball (0:E) r ∈ 𝓝 ((0:ℝ) • w)
        simpa only [zero_smul] using Metric.ball_mem_nhds (0:E) hr)
  have he : (fun s : ℝ => ψ (s • w)) =ᶠ[𝓝 0]
      (fun s => extChartAt 𝓘(ℝ,E) a (sprayFlow (s*τ) ⟨a,w⟩).1) := by
    filter_upwards [hn] with s hs
    rw [heq (s • w) hs,show (⟨a,s • w⟩ : TangentBundle 𝓘(ℝ,E) M) = tangentScale s ⟨a,w⟩ from rfl,
      sprayFlow_scale]
    rfl
  have hL := (show HasFDerivAt ψ (fderiv ℝ ψ 0) ((0:ℝ) • w) by
    simpa only [zero_smul] using hψ.hasFDerivAt).comp_hasDerivAt 0
    (show HasDerivAt (fun s : ℝ => s • w) w 0 by
      simpa only [one_smul,id_eq] using (hasDerivAt_id (0:ℝ)).smul_const w)
  have hR := (show HasDerivAt (fun t => extChartAt 𝓘(ℝ,E) a
      (sprayFlow t ⟨a,w⟩).1) w ((id (0:ℝ))*τ) by
    simpa only [id_eq,zero_mul] using hasDerivAt_spray_coordinate_zero a w).scomp 0
      ((hasDerivAt_id (0:ℝ)).mul_const τ)
  have H := (hL.congr_of_eventuallyEq he.symm).unique
    (show HasDerivAt (fun s => extChartAt 𝓘(ℝ,E) a (sprayFlow (s*τ) ⟨a,w⟩).1) (τ • w) 0 by
      simpa only [zero_mul,one_mul,id_eq,Function.comp_def,smul_eq_mul] using hR)
  exact H

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GeodesicExistence
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
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_endpoint_radial (a : M) {r : ℝ} (hr : 0 < r)
    {Ψ W : ℝ × E → E}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (hinit : ∀ v ∈ Metric.ball (0:E) r,
      Ψ (0,v) = extChartAt 𝓘(ℝ,E) a a ∧ W (0,v) = v)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball (0:E) r,
      Ψ (t,v) ∈ (extChartAt 𝓘(ℝ,E) a).target ∧
      HasDerivAt (fun s => Ψ (s,v)) (W (t,v)) t ∧
      HasDerivAt (fun s => W (s,v))
        (-coordinateChristoffel (riemannianCoordinateMetric a) (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {v : E} (hv : v ∈ Metric.ball (0:E) r) {τ : ℝ} (hτ : τ ∈ Ioo (-r) r) :
    fderiv ℝ (fun w => Ψ (τ,w)) v v = τ • W (τ,v) := by
  have hn1 : ∀ᶠ s : ℝ in 𝓝 1, s • v ∈ Metric.ball (0:E) r :=
    ((continuousAt_id.smul continuousAt_const) : ContinuousAt (fun s : ℝ => s • v) 1)
      (by change Metric.ball (0:E) r ∈ 𝓝 ((1:ℝ) • v)
          simpa only [one_smul] using Metric.isOpen_ball.mem_nhds hv)
  have hn2 : ∀ᶠ s : ℝ in 𝓝 1, s*τ ∈ Ioo (-r) r :=
    ((continuousAt_id.mul continuousAt_const) :
      ContinuousAt (fun scalar : ℝ => scalar * τ) 1).preimage_mem_nhds
      (by change Ioo (-r) r ∈ 𝓝 ((1:ℝ)*τ)
          simpa only [one_mul] using isOpen_Ioo.mem_nhds hτ)
  have heq : (fun s : ℝ => Ψ (τ,s • v)) =ᶠ[𝓝 1] (fun s => Ψ (s*τ,v)) := by
    filter_upwards [hn1,hn2] with s hs ht
    rw [coordinate_flow_eq_spray a hr hinit hode hs hτ,
      coordinate_flow_eq_spray a hr hinit hode hv ht]
    rw [show (⟨a,s • v⟩ : TangentBundle 𝓘(ℝ,E) M) = tangentScale s ⟨a,v⟩ from rfl,
      sprayFlow_scale]
    rfl
  have hD : DifferentiableAt ℝ (fun w => Ψ (τ,w)) v :=
    ((hΨ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds ⟨hτ,hv⟩)).comp v
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hleft : HasDerivAt (fun s : ℝ => Ψ (τ,s • v))
      (fderiv ℝ (fun w => Ψ (τ,w)) v v) 1 := by
    have hs : HasDerivAt (fun s : ℝ => s • v) v 1 := by
      simpa only [one_smul] using (hasDerivAt_id' (1:ℝ)).smul_const v
    have hD' : HasFDerivAt (fun w => Ψ (τ,w))
        (fderiv ℝ (fun w => Ψ (τ,w)) v) ((1:ℝ) • v) := by
      simpa only [one_smul] using hD.hasFDerivAt
    exact hD'.comp_hasDerivAt 1 hs
  have hright : HasDerivAt (fun s : ℝ => Ψ (s*τ,v)) (τ • W (τ,v)) 1 := by
    have hs : HasDerivAt (fun s : ℝ => s*τ) τ 1 := hasDerivAt_mul_const τ
    have hW : HasDerivAt (fun s => Ψ (s,v)) (W (τ,v)) ((1:ℝ)*τ) := by
      simpa only [one_mul] using (hode τ hτ v hv).2.1
    exact hW.scomp 1 hs
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayDistanceBound
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
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma sprayFlow_pathELength (z : TangentBundle 𝓘(ℝ,E) M) (s t : ℝ) :
    pathELength 𝓘(ℝ,E) (fun u => (sprayFlow u z).1) s t =
      ENNReal.ofReal ((t-s)*‖z.2‖) := by
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  calc
    _ = ∫⁻ _ in Icc s t, ENNReal.ofReal ‖z.2‖ := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u _
      have H := congrArg (fun v : TangentSpace 𝓘(ℝ,E) (sprayFlow u z).1 => ENNReal.ofReal ‖v‖)
        (spray_velocity_eq_mfderiv ((sprayFlow_curve z).isMIntegralCurveAt u))
      have H' := H.trans (congrArg ENNReal.ofReal (sprayFlow_speed u z))
      convert! H' using 1
      all_goals try with_reducible_and_instances rfl
      exact (ofReal_norm _).symm
    _ = _ := by
      rw [setLIntegral_const,Real.volume_Icc,ENNReal.ofReal_mul' (norm_nonneg _),mul_comm]

lemma dist_sprayFlow_le (z : TangentBundle 𝓘(ℝ,E) M) (s t : ℝ) :
    dist (sprayFlow s z).1 (sprayFlow t z).1 ≤ |s-t| * ‖z.2‖ := by
  have hsm : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun u => (sprayFlow u z).1) :=
    (Bundle.contMDiff_proj (fun x : M => TangentSpace 𝓘(ℝ,E) x)).comp
      (contMDiff_sprayFlow.comp (contMDiff_id.prodMk contMDiff_const))
  have H : ∀ s t : ℝ, s ≤ t → dist (sprayFlow s z).1 (sprayFlow t z).1 ≤ (t-s)*‖z.2‖ := by
    intro s t hst
    have he := riemannianEDist_le_pathELength (I := 𝓘(ℝ,E))
      (hsm.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contMDiffOn rfl rfl hst
    rw [←IsRiemannianManifold.out,sprayFlow_pathELength,edist_dist] at he
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sub_nonneg.mpr hst) (norm_nonneg _))).mp he
  rcases le_total s t with hst | hts
  · rw [abs_of_nonpos (sub_nonpos.mpr hst)]
    simpa only [neg_sub] using H s t hst
  · rw [dist_comm,abs_of_nonneg (sub_nonneg.mpr hts)]
    exact H t s hts

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_NoCorner
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

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_minimizing_prefix (z : TangentBundle 𝓘(ℝ,E) M) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hmin : dist z.1 (sprayFlow t z).1 = t * ‖z.2‖) :
    dist z.1 (sprayFlow s z).1 = s * ‖z.2‖ := by
  have h0 := dist_sprayFlow_le z 0 s
  rw [sprayFlow_zero,zero_sub,abs_neg,abs_of_nonneg hs] at h0
  apply le_antisymm h0
  have h1 := dist_sprayFlow_le z s t
  rw [abs_of_nonpos (sub_nonpos.mpr hst)] at h1
  have h2 := dist_triangle z.1 (sprayFlow s z).1 (sprayFlow t z).1
  rw [hmin] at h2
  nlinarith

lemma sprayFlow_minimizer_gradient (z : TangentBundle 𝓘(ℝ,E) M) {t : ℝ} (ht : 0 < t)
    (hmin : dist z.1 (sprayFlow t z).1 = t * ‖z.2‖)
    (W : TangentSpace 𝓘(ℝ,E) (sprayFlow t z).1)
    (hW : ‖W‖ = dist z.1 (sprayFlow t z).1)
    (hD : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun x => dist z.1 x ^ 2 / 2) (sprayFlow t z).1 (innerSL ℝ W)) :
    W = t • (sprayFlow t z).2 := by
  have hcomp := hD.comp t (hasMFDerivAt_spray_projection ((sprayFlow_curve z).isMIntegralCurveAt t))
  have hd : HasDerivAt (fun s => dist z.1 (sprayFlow s z).1 ^ 2 / 2)
      (inner ℝ W (sprayFlow t z).2) t := by
    have hh : HasFDerivAt (fun s => dist z.1 (sprayFlow s z).1 ^ 2 / 2)
        ((innerSL ℝ W).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (sprayFlow t z).2)) t := by
      convert! hcomp.hasFDerivAt
    convert! hh.hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self,one_smul,innerSL_apply_apply]
  have hp : HasDerivAt (fun s : ℝ => s^2 * (‖z.2‖^2 / 2)) (t * ‖z.2‖^2) t := by
    convert! ((hasDerivAt_id t).pow 2).mul_const (‖z.2‖^2/2) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq]
    ring
  have heq : ∀ s ∈ Icc 0 t,
      dist z.1 (sprayFlow s z).1 ^ 2 / 2 = s^2 * (‖z.2‖^2 / 2) := by
    intro s hs
    rw [sprayFlow_minimizing_prefix z hs.1 hs.2 hmin,mul_pow]
    ring
  have hdin : HasDerivWithinAt (fun s => dist z.1 (sprayFlow s z).1 ^ 2 / 2)
      (t * ‖z.2‖^2) (Icc 0 t) t :=
    hp.hasDerivWithinAt.congr_of_mem heq ⟨ht.le,le_rfl⟩
  have hi : inner ℝ W (sprayFlow t z).2 = t*‖z.2‖^2 := by
    exact (hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc ht t ⟨ht.le,le_rfl⟩)).symm.trans
      (hdin.derivWithin (uniqueDiffOn_Icc ht t ⟨ht.le,le_rfl⟩))
  have hn := norm_sub_sq_real W (t • (sprayFlow t z).2)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,sprayFlow_speed,real_inner_smul_right,hi,hW,hmin] at hn
  have hzero : ‖W - t • (sprayFlow t z).2‖ = 0 := by nlinarith [sq_nonneg ‖W - t • (sprayFlow t z).2‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MinimizingSubinterval
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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_minimizing_subinterval (z : TangentBundle 𝓘(ℝ,E) M) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hmin : dist z.1 (sprayFlow t z).1 = t * ‖z.2‖) :
    dist (sprayFlow s z).1 (sprayFlow t z).1 = (t-s) * ‖z.2‖ := by
  have hle := dist_sprayFlow_le z s t
  rw [abs_of_nonpos (sub_nonpos.mpr hst),neg_sub] at hle
  apply le_antisymm hle
  have hlow := dist_triangle z.1 (sprayFlow s z).1 (sprayFlow t z).1
  rw [hmin,sprayFlow_minimizing_prefix z hs hst hmin] at hlow
  nlinarith

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GlobalGauss
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

lemma sprayFlow_chart_hasDerivAt (a z : TangentBundle 𝓘(ℝ,E) M) {t : ℝ}
    (hz : (sprayFlow t z).1 ∈ (extChartAt 𝓘(ℝ,E) a.1).source) :
    HasDerivAt (fun r => extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a (sprayFlow r z))
      (coordinateGeodesicField (riemannianCoordinateMetric a.1)
        (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a (sprayFlow t z))) t := by
  have hsrc : sprayFlow t z ∈ (chartAt (ModelProd E E) a).source := by
    simpa only [extChartAt_source] using (tangent_chart_source_iff a (sprayFlow t z)).mpr hz
  have hD := (hasMFDerivAt_extChartAt (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) hsrc).comp t
    (sprayFlow_curve z t)
  rw [hasMFDerivAt_iff_hasFDerivAt] at hD
  let L : ℝ →L[ℝ] E×E :=
    (tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (sprayFlow t z) a (sprayFlow t z)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (geodesicSpray (sprayFlow t z)))
  have hD' : HasFDerivAt (fun r => extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a (sprayFlow r z)) L t := by
    convert! hD using 1
    all_goals try with_reducible_and_instances rfl
    rw [mfderiv_chartAt_eq_tangentCoordChange hsrc]
    rfl
  have hd := hD'.hasDerivAt
  apply hd.congr_deriv
  change tangentCoordChange (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (sprayFlow t z) a (sprayFlow t z)
    ((1:ℝ) • geodesicSpray (sprayFlow t z)) = _
  rw [one_smul]
  exact geodesicSpray_coordinates a (sprayFlow t z) hz

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

attribute [local instance] OAI.WeakMTWTransport.globalPairingNormedSpace
lemma spray_variation_pairing_hasDerivAt
    {ν : ℝ → TangentBundle 𝓘(ℝ,E) M}
    (hν : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ ν)
    {s e : ℝ} (he : HasDerivAt (fun r => ‖(ν r).2‖^2) e s) (t : ℝ) :
    HasDerivAt (fun r => inner ℝ (sprayFlow r (ν s)).2
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (sprayFlow r (ν k)).1) s 1)) (e/2) t := by
  let F : ℝ×ℝ → TangentBundle 𝓘(ℝ,E) M := fun z => sprayFlow z.1 (ν z.2)
  let a := F (t,s)
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a
  let c := extChartAt 𝓘(ℝ,E) a.1
  let g := riemannianCoordinateMetric (E := E) a.1
  let U := F ⁻¹' χ.source
  let A : ℝ×ℝ → E := fun z => (χ (F z)).1
  let V : ℝ×ℝ → E := fun z => (χ (F z)).2
  have hF : ContMDiff 𝓘(ℝ,ℝ×ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ F :=
    contMDiff_sprayFlow.comp (contDiff_fst.contMDiff.prodMk (hν.comp contDiff_snd.contMDiff))
  have hU : IsOpen U := (isOpen_extChartAt_source (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).preimage hF.continuous
  have hts : (t,s) ∈ U := mem_extChartAt_source a
  have hχ : ContMDiffOn (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E×E) ∞ χ χ.source := by
    simpa only [χ,extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) (n := ∞) (x := a))
  have hq : ContDiffOn ℝ ∞ (fun z => χ (F z)) U :=
    (hχ.comp hF.contMDiffOn (fun _ h => h)).contDiffOn
  have hbase (z : ℝ×ℝ) (hz : z ∈ U) : (F z).1 ∈ c.source :=
    (tangent_chart_source_iff a (F z)).mp hz
  have himg (z : ℝ×ℝ) (hz : z ∈ U) : A z ∈ c.target := c.map_source (hbase z hz)
  have hode (z : ℝ×ℝ) (hz : z ∈ U) :
      HasDerivAt (fun q => A (q,z.2)) (V z) z.1 ∧
      HasDerivAt (fun q => V (q,z.2)) (-coordinateChristoffel g (A z) (V z) (V z)) z.1 := by
    have hd := sprayFlow_chart_hasDerivAt a (ν z.2) (hbase z hz)
    exact ⟨(ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt z.1 hd,
      (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt z.1 hd⟩
  have henergy : HasDerivAt (fun r => g (A (t,r)) (V (t,r)) (V (t,r))) e s := by
    apply he.congr_of_eventuallyEq
    have hnear : ∀ᶠ r in 𝓝 s, (t,r) ∈ U :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hts)
    filter_upwards [hnear] with r hr
    exact (coordinate_spray_energy a (F (t,r)) (hbase _ hr)).trans
      (congrArg (fun a : ℝ => a^2) (sprayFlow_speed t (ν r)))
  have hG := coordinate_pairing_hasDerivAt (isOpen_extChartAt_target a.1)
    (contDiffOn_riemannianCoordinateMetric a.1)
    (fun _ hz => riemannianCoordinateMetric_isInvertible hz)
    (fun _ _ => riemannianCoordinateMetric_symm _ _)
    hU hq.fst hq.snd himg hode hts henergy
  apply hG.congr_of_eventuallyEq
  have hnear : ∀ᶠ r in 𝓝 t, (r,s) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds hts)
  filter_upwards [hnear] with r hr
  have hp : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun k => (F (r,k)).1) :=
    (Bundle.contMDiff_proj (fun x : M => TangentSpace 𝓘(ℝ,E) x)).comp
      (hF.comp (contMDiff_const.prodMk_space contMDiff_id))
  have hsrc : (F (r,s)).1 ∈ (chartAt E a.1).source := by
    simpa only [c,extChartAt_source] using hbase _ hr
  have hDc := (hasMFDerivAt_extChartAt (I := 𝓘(ℝ,E)) hsrc).comp s
    (hp.mdifferentiable (by simp) s).hasMFDerivAt
  rw [hasMFDerivAt_iff_hasFDerivAt] at hDc
  have hAr := hasDerivAt_slice_right ((hq.fst.contDiffAt (hU.mem_nhds hr)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  let L : ℝ →L[ℝ] E := (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c (F (r,s)).1).comp
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (F (r,k)).1) s)
  have hDc' : HasFDerivAt (fun k => c (F (r,k)).1) L s := by convert! hDc using 1
  have hJ := hAr.unique hDc'.hasDerivAt
  change directionalDerivative A (0,1) (r,s) =
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c (F (r,s)).1)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (F (r,k)).1) s 1) at hJ
  have hvel : V (r,s) = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c (F (r,s)).1 (F (r,s)).2 := by
    rw [mfderiv_extChartAt_eq_tangentCoordChange (hbase _ hr)]
    rfl
  change inner ℝ (F (r,s)).2
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (F (r,k)).1) s 1) =
      g (A (r,s)) (V (r,s)) (directionalDerivative A (0,1) (r,s))
  apply (coordinate_metric_chart_pairing (hbase _ hr) _ _).symm.trans
  convert! congrArg₂ (fun u v : E => g (A (r,s)) u v) hvel.symm hJ.symm using 1
  all_goals try with_reducible_and_instances rfl

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_IntegratedGauss
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
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma spray_variation_pairing_affine
    {ν : ℝ → TangentBundle 𝓘(ℝ,E) M}
    (hν : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ ν)
    {s e : ℝ} (he : HasDerivAt (fun r => ‖(ν r).2‖^2) e s) (t : ℝ) :
    inner ℝ (sprayFlow t (ν s)).2
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (sprayFlow t (ν k)).1) s 1) =
    inner ℝ (ν s).2 (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (ν k).1) s 1) + t*(e/2) := by
  let P : ℝ → ℝ := fun r => inner ℝ (sprayFlow r (ν s)).2
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (sprayFlow r (ν k)).1) s 1)
  have hP (r : ℝ) : HasDerivAt P (e/2) r := spray_variation_pairing_hasDerivAt hν he r
  have hd (r : ℝ) : HasDerivAt (fun q => P q-q*(e/2)) 0 r := by
    convert! (hP r).sub ((hasDerivAt_id r).mul_const (e/2)) using 1; simp
  have hc := is_const_of_deriv_eq_zero
    (fun point => (hd point).differentiableAt)
    (fun point => (hd point).deriv) t (0 : ℝ)
  have hP0 : P 0 = inner ℝ (ν s).2
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (ν k).1) s 1) := by
    have hflow0 : (fun k => sprayFlow 0 (ν k)) = ν := funext (fun k => sprayFlow_zero (ν k))
    exact congrArg (fun γ : ℝ → TangentBundle 𝓘(ℝ,E) M =>
      inner ℝ (γ s).2 (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun k => (γ k).1) s 1)) hflow0
  simp only [zero_mul,sub_zero,hP0] at hc
  dsimp [P] at hc
  linarith

lemma sprayFlow_gauss (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) (t : ℝ) :
    inner ℝ (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).2
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
        (fun s : ℝ => (sprayFlow t (⟨x,v+s • w⟩ : TangentBundle 𝓘(ℝ,E) M)).1) 0 1) =
    t*inner ℝ v w := by
  let ν : ℝ → TangentBundle 𝓘(ℝ,E) M := fun s => ⟨x,v+s • w⟩
  have he : HasDerivAt (fun s : ℝ => ‖(ν s).2‖^2) (2*inner ℝ v w) 0 := by
    have hh := ((hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const w)).norm_sq
    simpa [ν] using hh
  have hh := spray_variation_pairing_affine (ν := ν) (contMDiff_fiber_line x v w) he t
  have hν0 : ν 0 = (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M) := by
    dsimp [ν]; rw [zero_smul,add_zero]
  rw [hν0] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp [ν]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_ShortGradient
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma sprayFlow_reverse (z : TangentBundle 𝓘(ℝ,E) M) (t : ℝ) :
    sprayFlow t (tangentScale (-1) (sprayFlow t z)) = tangentScale (-1) z := by
  rw [sprayFlow_scale,neg_one_mul,←sprayFlow_add,neg_add_cancel,sprayFlow_zero]

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma spray_action_line_stationary (x : M) (p w : TangentSpace 𝓘(ℝ,E) x)
    (L ε : ℝ) (hε : ε ≠ 0) (y : M)
    (hD : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun b => dist b y^2/2)
      (sprayFlow L (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1
      (innerSL ℝ ((-ε) • (sprayFlow L (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).2))) :
    HasDerivAt (fun s : ℝ => L*‖p+s • w‖^2/2 +
      (dist (sprayFlow L (⟨x,p+s • w⟩ : TangentBundle 𝓘(ℝ,E) M)).1 y^2/2)/ε) 0 0 := by
  let ν : ℝ → TangentBundle 𝓘(ℝ,E) M := fun s => sprayFlow L ⟨x,p+s • w⟩
  let ψ : ℝ → M := fun s => (ν s).1
  have hψ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ ψ :=
    (Bundle.contMDiff_proj (fun b : M => TangentSpace 𝓘(ℝ,E) b)).comp
      (contMDiff_sprayFlow.comp (contMDiff_const.prodMk (contMDiff_fiber_line x p w)))
  have hν0 : ν 0 = sprayFlow L (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M) := by simp [ν]
  have hD₀ : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun b => dist b y^2/2) (ν 0).1
      (innerSL ℝ ((-ε) • (ν 0).2)) := by rw [hν0]; exact hD
  have hDc := hD₀.comp 0 (hψ.mdifferentiable (by simp) 0).hasMFDerivAt
  let J := mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ψ 0 (1:ℝ)
  have hd : HasDerivAt (fun s => dist (ψ s) y^2/2)
      ((-ε) * inner ℝ (ν 0).2 J) 0 := by
    have hf : HasFDerivAt (fun s => dist (ψ s) y^2/2)
        ((innerSL ℝ ((-ε) • (ν 0).2)).comp (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ψ 0)) 0 := by
      convert! hDc.hasFDerivAt using 1
      all_goals try with_reducible_and_instances rfl
    convert! hf.hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    change (-ε) * inner ℝ (ν 0).2 J = inner ℝ ((-ε) • (ν 0).2) J
    rw [real_inner_smul_left]
  have hg : inner ℝ (ν 0).2 J = L*inner ℝ p w := by
    have he : HasDerivAt (fun s : ℝ => ‖p+s • w‖^2) (2*inner ℝ p w) 0 := by
      convert! ((hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const w)).norm_sq using 1
      all_goals try with_reducible_and_instances rfl
      simp
    have H := spray_variation_pairing_affine (ν := fun s => (⟨x,p+s • w⟩ : TangentBundle 𝓘(ℝ,E) M))
      (contMDiff_fiber_line x p w) he L
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hn := ((hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const w)).norm_sq
  have he : HasDerivAt (fun s : ℝ => L*‖p+s • w‖^2/2) (L*inner ℝ p w) 0 := by
    convert! (hn.const_mul L).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    simp
    ring
  have H := he.add (hd.div_const ε)
  apply H.congr_deriv
  rw [hg]
  field_simp
  ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayActionMinimum
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma spray_split_action_contact (x : M) (p : TangentSpace 𝓘(ℝ,E) x)
    {L ε : ℝ} (hL : 0<L) (hε : 0<ε)
    (hmin : dist x (sprayFlow (L+2*ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 = (L+2*ε)*‖p‖) :
    L*‖p‖^2/2 +
      dist (sprayFlow L (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 (sprayFlow (L+ε) ⟨x,p⟩).1^2/(2*ε) +
      dist (sprayFlow (L+ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 (sprayFlow (L+2*ε) ⟨x,p⟩).1^2/(2*ε) =
      (L+2*ε)*‖p‖^2/2 := by
  have hpre := sprayFlow_minimizing_prefix (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
    (s := L+ε) (by positivity) (by linarith) hmin
  have h₁ := sprayFlow_minimizing_subinterval (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
    (s := L) hL.le (by linarith : L≤L+ε) hpre
  have h₂ := sprayFlow_minimizing_subinterval (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
    (s := L+ε) (by positivity) (by linarith : L+ε≤L+2*ε) hmin
  rw [h₁,h₂]
  dsimp
  field_simp
  ring

lemma spray_split_action_minimum (x : M) (p : TangentSpace 𝓘(ℝ,E) x)
    {L ε : ℝ} (hL : 0<L) (hε : 0<ε)
    (hmin : dist x (sprayFlow (L+2*ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 = (L+2*ε)*‖p‖)
    (v : TangentSpace 𝓘(ℝ,E) x) (q : M) :
    (L+2*ε)*‖p‖^2/2 ≤ L*‖v‖^2/2 +
      dist (sprayFlow L (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 q^2/(2*ε) +
      dist q (sprayFlow (L+2*ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1^2/(2*ε) := by
  have hb : dist x (sprayFlow L (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ≤ L*‖v‖ := by
    simpa only [sprayFlow_zero,zero_sub,abs_neg,abs_of_pos hL] using
      dist_sprayFlow_le (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M) 0 L
  have hh := three_leg_energy_le x (sprayFlow L (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 q
    (sprayFlow (L+2*ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 hL hε hb
  rw [hmin] at hh
  have he : ((L+2*ε)*‖p‖)^2/(2*(L+2*ε)) = (L+2*ε)*‖p‖^2/2 := by
    have hn : L+2*ε ≠ 0 := (show 0<L+2*ε by positivity).ne'
    field_simp
  rwa [he] at hh

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_spray_fiber_immersion (x : M) (p : TangentSpace 𝓘(ℝ,E) x) (t : ℝ) :
    Function.Injective (fderiv ℝ
      (fun v : TangentSpace 𝓘(ℝ,E) x =>
        extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (sprayFlow t ⟨x,p⟩) (sprayFlow t ⟨x,v⟩)) p) := by
  let z : TangentBundle 𝓘(ℝ,E) M := ⟨x,p⟩
  let a := sprayFlow t z
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a
  let χ₀ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z
  let Φ : TangentSpace 𝓘(ℝ,E) x → E×E := fun v => χ (sprayFlow t ⟨x,v⟩)
  let K : E×E → E×E := fun y => χ₀ (sprayFlow (-t) (χ.symm y))
  let R : E×E → E := fun y => (K y).2
  have hΦp : Φ p = χ a := rfl
  have hχinv : χ.symm (Φ p) = a := χ.left_inv (mem_extChartAt_source a)
  have hback : sprayFlow (-t) (χ.symm (Φ p)) = z := by
    rw [hχinv]
    exact (sprayFlow_add (-t) t z).symm.trans (by rw [neg_add_cancel,sprayFlow_zero])
  have hΦ : ContDiffAt ℝ ∞ Φ p :=
    ((show ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E×E) ∞ χ a from
      contMDiffAt_extChartAt).comp p (contMDiff_spray_fiber x t p)).contDiffAt
  have hχ : ContMDiffAt 𝓘(ℝ,E×E) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ χ.symm (Φ p) :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds (χ.map_source (mem_extChartAt_source a)))
  have hf : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (sprayFlow (-t) : TangentBundle 𝓘(ℝ,E) M → TangentBundle 𝓘(ℝ,E) M) :=
    contMDiff_sprayFlow.comp (contMDiff_const.prodMk contMDiff_id)
  have hχ₀ : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E×E) ∞ χ₀
      (sprayFlow (-t) (χ.symm (Φ p))) := by
    rw [hback]; exact contMDiffAt_extChartAt
  have hK : ContDiffAt ℝ ∞ K (Φ p) :=
    (hχ₀.comp (Φ p) ((hf (χ.symm (Φ p))).comp (Φ p) hχ)).contDiffAt
  have hR : DifferentiableAt ℝ R (Φ p) := hK.snd.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let e := trivializationAt E (fun b : M => TangentSpace 𝓘(ℝ,E) b) x
  let L : TangentSpace 𝓘(ℝ,E) x ≃L[ℝ] E :=
    e.continuousLinearEquivAt ℝ x (mem_baseSet_trivializationAt E _ x)
  have hnear : ∀ᶠ v : TangentSpace 𝓘(ℝ,E) x in 𝓝 p, sprayFlow t ⟨x,v⟩ ∈ χ.source :=
    (contMDiff_spray_fiber x t p).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source a).mem_nhds (mem_extChartAt_source a))
  have heq : (fun v => R (Φ v)) =ᶠ[𝓝 p] L := by
    filter_upwards [hnear] with v hv
    dsimp [R,K,Φ]
    rw [χ.left_inv hv,←sprayFlow_add,neg_add_cancel,sprayFlow_zero]
    rfl
  have hd := (hR.hasFDerivAt.comp p (hΦ.differentiableAt (by simp)).hasFDerivAt).fderiv
  change fderiv ℝ (fun v => R (Φ v)) p = _ at hd
  rw [heq.fderiv_eq,L.hasFDerivAt.fderiv] at hd
  intro u v huv
  change fderiv ℝ Φ p u = fderiv ℝ Φ p v at huv
  apply L.injective
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,E) x →L[ℝ] E => A u-A v) hd
  simp only [ContinuousLinearMap.comp_apply,huv,sub_self,sub_eq_zero] at hh
  convert! hh

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_UniformShort
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_zero_velocity_base (a : M) (t : ℝ) :
    (sprayFlow t (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)).1 = a := by
  have hh := dist_sprayFlow_le (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) 0 t
  exact (show a = (sprayFlow t ⟨a,0⟩).1 by
    simpa only [sprayFlow_zero,norm_zero,mul_zero,dist_le_zero] using hh).symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayMinimizerUnique
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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_minimizer_terminal_eq (z G : TangentBundle 𝓘(ℝ,E) M)
    (hG : G.1 = (sprayFlow 1 z).1)
    (hmin : dist z.1 (sprayFlow 1 z).1 = ‖z.2‖)
    (hGn : ‖G.2‖ = dist z.1 G.1)
    (hD : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun x => dist z.1 x^2/2) G.1 (innerSL ℝ G.2)) : sprayFlow 1 z = G := by
  rcases G with ⟨b,W⟩
  change b = (sprayFlow 1 z).1 at hG
  subst b
  have hmin' : dist z.1 (sprayFlow 1 z).1 = 1 * ‖z.2‖ := by rw [one_mul]; exact hmin
  have hh := sprayFlow_minimizer_gradient z zero_lt_one hmin' W hGn hD
  rw [one_smul] at hh
  rw [hh]

lemma sprayFlow_minimizer_unique_of_gradient (z w G : TangentBundle 𝓘(ℝ,E) M)
    (hbase : z.1=w.1)
    (hGz : G.1=(sprayFlow 1 z).1) (hGw : G.1=(sprayFlow 1 w).1)
    (hz : dist z.1 (sprayFlow 1 z).1 = ‖z.2‖)
    (hw : dist w.1 (sprayFlow 1 w).1 = ‖w.2‖)
    (hGn : ‖G.2‖ = dist z.1 G.1)
    (hD : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun x => dist z.1 x^2/2) G.1 (innerSL ℝ G.2)) : z=w := by
  have hez := sprayFlow_minimizer_terminal_eq z G hGz hz hGn hD
  have hDw : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun x => dist w.1 x^2/2) G.1 (innerSL ℝ G.2) := by rwa [←hbase]
  have hnw : ‖G.2‖ = dist w.1 G.1 := by rw [←hbase]; exact hGn
  have hew := sprayFlow_minimizer_terminal_eq w G hGw hw hnw hDw
  have hh := congrArg (sprayFlow (-1)) (hez.trans hew.symm)
  simpa only [←sprayFlow_add,neg_add_cancel,sprayFlow_zero] using hh

end

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

def reverseRay (z : TangentBundle 𝓘(ℝ,Model n) M) := tangentScale (-1) (sprayFlow 1 z)

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma reverseRay_involutive : Function.Involutive (reverseRay (n := n) (M := M)) := by
  intro z
  dsimp only [reverseRay]
  rw [sprayFlow_reverse]
  rcases z with ⟨x,p⟩
  change (⟨x,(-1:ℝ) • ((-1:ℝ) • p)⟩ : TangentBundle 𝓘(ℝ,Model n) M)=⟨x,p⟩
  rw [neg_one_smul,neg_one_smul,neg_neg]

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma continuous_reverseRay : Continuous (reverseRay (n := n) (M := M)) := by
  exact contMDiff_tangentScale.continuous.comp
    (continuous_const.prodMk (contMDiff_sprayFlow.continuous.comp
      (continuous_const.prodMk continuous_id)))

end WeakMTWTransport

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

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma reverseRay_reverseRay (z : TangentBundle 𝓘(ℝ,Model n) M) :
    reverseRay (reverseRay z)=z := by
  unfold reverseRay
  rw [sprayFlow_reverse]
  rcases z with ⟨x,v⟩
  change (⟨x,(-1:ℝ) • ((-1:ℝ) • v)⟩ : TangentBundle 𝓘(ℝ,Model n) M)=⟨x,v⟩
  rw [neg_one_smul,neg_one_smul,neg_neg]

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
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.WeakMTWTransport.fixedJoinMiddle_apply _root_.OAI.WeakMTWTransport.normalEndpointMixedOperator_inner
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

lemma reverseRay_segment (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ) (hT : T≠0) :
    reverseRay (tangentScale (T-h) (sprayFlow h z))=
      tangentScale ((T-h)/T) (reverseRay (tangentScale T z)) := by
  unfold reverseRay
  rw [sprayFlow_scale,mul_one,←sprayFlow_add,sub_add_cancel,
    sprayFlow_scale,mul_one]
  rw [tangentScale_mul,tangentScale_mul,tangentScale_mul]
  congr 1
  field_simp

end ProperPieces
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_MetricDefinitions
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

variable {M : Type*} [MetricSpace M]

variable [CompactSpace M] [Nonempty M]

lemma continuous_cTransform {v : M → ℝ} (hv : Continuous v) :
    Continuous (cTransform v) := by
  apply (cTransform_lipschitz hv (D := ⟨Metric.diam (univ : Set M),
    Metric.diam_nonneg⟩) _).continuous
  intro x y
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)

end WeakMTWTransport
end

end OAI
end

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

lemma cTransform_cTransform_le {v : M → ℝ} (hv : Continuous v) (x : M) :
    cTransform (cTransform v) x ≤ v x := by
  rw [cTransform_le_iff (continuous_cTransform hv)]
  intro y
  have hh := cTransform_gap_nonneg hv y x
  rw [contactGap, cost_symm y x] at hh
  linarith

lemma cTransform_triple {v : M → ℝ} (hv : Continuous v) :
    cTransform (cTransform (cTransform v)) = cTransform v := by
  funext x
  exact le_antisymm (cTransform_cTransform_le (continuous_cTransform hv) x)
    (cTransform_antitone (continuous_cTransform (continuous_cTransform hv)) hv
      (cTransform_cTransform_le hv) x)

def boundedCTransform (v : M →ᵇ ℝ) : M →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨cTransform v, continuous_cTransform v.continuous⟩

def normalizedDualPairs (x0 : M) : Set ((M →ᵇ ℝ) × (M →ᵇ ℝ)) :=
  {uv | uv.1 x0 = 0 ∧ boundedCTransform uv.2 = uv.1 ∧ boundedCTransform uv.1 = uv.2}

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

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma reverseRay_prefix (z : TangentBundle 𝓘(ℝ,Model n) M) (h : ℝ) :
    reverseRay (tangentScale h z)=tangentScale (-h) (sprayFlow h z) := by
  rw [reverseRay,sprayFlow_scale,mul_one,tangentScale_mul,neg_one_mul]

def middleHessian (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ) :
    TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1 →L[ℝ]
      TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1 →L[ℝ] ℝ :=
  h⁻¹ • normalHessian (sprayFlow h z).1 ((-h) • (sprayFlow h z).2)+
    (T-h)⁻¹ • normalHessian (sprayFlow h z).1 ((T-h) • (sprayFlow h z).2)

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleHessian_apply (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ)
    (v w : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    middleHessian z h T v w=
      normalHessian (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) v w/h+
      normalHessian (sprayFlow h z).1 ((T-h) • (sprayFlow h z).2) v w/(T-h) := by
  simp only [middleHessian,add_apply,smul_apply,
    smul_eq_mul,div_eq_mul_inv]
  ring

def middleCenteredAction (z : TangentBundle 𝓘(ℝ,Model n) M) (h : ℝ)
    (b : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) : ℝ :=
  h⁻¹*(normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) b-
    normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) 0)-
  (-(1-h)⁻¹)*(normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2) b-
    normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2) 0)

end MiddleHessian
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LinearAlgebra_SpectralContinuity
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
section MiddleSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] OAI.WeakMTWTransport.instFiniteDimensionalRealTangentSpaceModelModelWithCornersSelf_5
def middleHessianOperator (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ) :
    TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1 →L[ℝ]
      TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1 :=
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (middleHessian z h T)

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma inner_middleHessianOperator (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ)
    (v w : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    inner ℝ (middleHessianOperator z h T v) w = middleHessian z h T v w :=
  InnerProductSpace.toDual_symm_apply

end MiddleSpectrum
end WeakMTWTransport

end

end

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_CotangentFlow
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

def coordinatePhaseFlow (a:M) (q:ℝ×Phase n) : Phase n :=
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩:TangentBundle 𝓘(ℝ,Model n) M)
  phaseLower a (χ (sprayFlow (-q.1) (χ.symm (phaseRaise a q.2))))

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Oscillation_SectionOscillation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section SectionOscillation
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

variable [MeasurableSpace M] [BorelSpace M]

def densityDualClass (vol : Measure M) (lam cap : ℝ) (x0 : M) :
    Set ((M →ᵇ ℝ) × (M →ᵇ ℝ)) :=
  {uv | uv ∈ normalizedDualPairs x0 ∧
    ∃ rho0 rho1 : M → ℝ, AdmissibleDensity vol lam cap rho0 ∧
      AdmissibleDensity vol lam cap rho1 ∧
      ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
        dualObjective (densityMeasure vol rho0) (densityMeasure vol rho1) uv ≤
          dualObjective (densityMeasure vol rho0) (densityMeasure vol rho1) (a,b)}

def classSectionOscillations (vol : Measure M) (lam cap : ℝ) (x0 : M) (r : ℝ) : Set ℝ :=
  {a | ∃ uv ∈ densityDualClass vol lam cap x0, ∃ x : M,
    a = sectionOscillation uv.1 uv.2 x r}

def classOscillation (vol : Measure M) (lam cap : ℝ) (x0 : M) (r : ℝ) : ℝ :=
  sSup (classSectionOscillations vol lam cap x0 r)

end SectionOscillation

open Filter

end WeakMTWTransport
end
end
end

end OAI
end


