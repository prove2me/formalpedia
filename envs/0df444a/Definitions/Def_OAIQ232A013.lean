-- Prove2me | Definitions.Def_OAIQ232A013
-- name    : OAIQ232A013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:48:52.091218+00:00
-- url     : https://prove2.me/theorems/6f0d99bf-1851-4ab2-aa19-520ab45d10ab
-- title:
--   Definitions bundle OAIQ232A013 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 6 definitions, 1 inductive type or structure and 45 theorems. The definitions and types are `OAI.WeakMTWTransport.JensenSamplesAt`, `OAI.WeakMTWTransport.chartActualPole`, `OAI.WeakMTWTransport.hopfPole`, `OAI.WeakMTWTransport.rescaledIntegralCurve`, `OAI.WeakMTWTransport.sprayFlow`, `OAI.WeakMTWTransport.unitPathIntegral`, `OAI.WeakMTWTransport.unitPathPrimitive`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Calculus_PathCalculus`, `BiholderTransport_Convexity_JensenAt`, `BiholderTransport_Convexity_JensenPackage`, `BiholderTransport_Coordinates_JointNormalChart`, `BiholderTransport_Coordinates_NormalCoordinates`, `BiholderTransport_Coordinates_NormalRigidity`, `BiholderTransport_Coordinates_PoleCoordinates`, `BiholderTransport_Geodesics_CompleteSpray`, `BiholderTransport_Geodesics_GeodesicExistence`, `BiholderTransport_Geodesics_ShortGradient`, `BiholderTransport_Geodesics_SprayEnergy`, `BiholderTransport_Geodesics_SprayProjection`, `BiholderTransport_Geodesics_SprayScaling`, `BiholderTransport_LocalFlow_CompactFlow`, `BiholderTransport_LocalFlow_ImplicitODE`, `BiholderTransport_LocalFlow_LocalDomainFlow`, `BiholderTransport_LocalFlow_LocalMetricNormal`, `BiholderTransport_LocalFlow_MIntegralCurveUniformInvariant`, `BiholderTransport_LocalFlow_SmoothCoordinateFlow`, `BiholderTransport_LocalFlow_SmoothFlowEndpoint`, `BiholderTransport_LocalFlow_SmoothIntegralCurve`, `BiholderTransport_Regularity_MetricDefinitions`, `BiholderTransport_Regularity_UnitTime`, `BiholderTransport_Volume_RadialCalibration`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A006`, `OAIQ232A007`, `OAIQ232A008` and `OAIQ232A009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ232A017` and `OAIQ232A018`; the statements `OAI.WeakMTWTransport.WeakMTW.actualPole_kernel`, `OAI.WeakMTWTransport.WeakMTW.actualPole_residual_taylor`, `OAI.WeakMTWTransport.WeakMTW.actualPole_taylor`, `OAI.WeakMTWTransport.WeakMTW.actual_sample_pole_matrix`, `OAI.WeakMTWTransport.WeakMTW.coordinate_sample_pole_matrix`, `OAI.WeakMTWTransport.WeakMTW.family_comparison_local_data`, `OAI.WeakMTWTransport.WeakMTW.jensen_undo_short`, `OAI.WeakMTWTransport.WeakMTW.modified_active_lower_jet_nonneg`, `OAI.WeakMTWTransport.exists_fixedJoinMiddle_lower_crossing`, `OAI.WeakMTWTransport.fixedJoinMiddle_uniform_interval_crossing` and `OAI.WeakMTWTransport.movingFixedJoinMiddle_strict_crossing`; the proof of `OAI.WeakMTWTransport.WeakMTW.actualPole_residual_taylor`.
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
import Definitions.Def_OAIQ232A006
import Definitions.Def_OAIQ232A007
import Definitions.Def_OAIQ232A008
import Definitions.Def_OAIQ232A009

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
attribute [local instance] OAI.WeakMTWTransport.pathCalculusNormedAddCommGroupContinuousMap
lemma contDiff_path_comp_nat (m : ℕ) (f : C(E,F)) (hf : ContDiff ℝ m f) :
    ContDiff ℝ m (fun v : C(K,E) => f.comp v) := by
  induction m generalizing F with
  | zero => exact contDiff_zero.mpr f.continuous_postcomp
  | succ m ih =>
    obtain ⟨f',hf',hder⟩ := contDiff_succ_iff_hasFDerivAt.mp hf
    let F' : C(E,E →L[ℝ] F) := ⟨f',hf'.continuous⟩
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun v => pathLinearApply (F'.comp v),?_,?_⟩
    · exact (pathLinearApplyL (K := K) (E := E) (F := F)).contDiff.comp
        (ih F' hf')
    · intro u; exact hasFDerivAt_path_comp f F' hder u

lemma contDiff_path_comp (f : C(E,F)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun v : C(K,E) => f.comp v) :=
  contDiff_infty.mpr fun m => contDiff_path_comp_nat m f (contDiff_infty.mp hf m)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalCoordinates
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.WeakMTWTransport.normalCoordinatesNormedSpace
attribute [local instance] OAI.WeakMTWTransport.normalCoordinatesDualNormedAddCommGroup
attribute [local instance] OAI.WeakMTWTransport.normalCoordinatesDualNormedSpace
attribute [local instance] OAI.WeakMTWTransport.normalCoordinatesBilinearNormedAddCommGroup
attribute [local instance] OAI.WeakMTWTransport.normalCoordinatesBilinearNormedSpace
local instance normalCoordinatesTrilinearNormedAddCommGroup_rf01306_1 :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance normalCoordinatesTrilinearNormedSpace_rf01306_1 :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
lemma coordinate_endpoint_isInvertible
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {Ψ W : ℝ × E → E} {a b R : ℝ} (hR : 0 < R)
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo a b ×ˢ Metric.ball 0 R))
    (hW : ContDiffOn ℝ ∞ W (Ioo a b ×ˢ Metric.ball 0 R))
    (himg : ∀ t ∈ Ioo a b, ∀ v ∈ Metric.ball 0 R, Ψ (t,v) ∈ S)
    (hode : ∀ t ∈ Ioo a b, ∀ v ∈ Metric.ball 0 R,
      HasDerivAt (fun q => Ψ (q,v)) (W (t,v)) t ∧
      HasDerivAt (fun q => W (q,v))
        (-coordinateChristoffel g (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {x : E} (h0 : 0 ∈ Ioo a b)
    (hΨ0 : ∀ v ∈ Metric.ball 0 R, Ψ (0,v) = x)
    (hW0 : ∀ v ∈ Metric.ball 0 R, W (0,v) = v)
    {τ : ℝ} (hτ : τ ∈ Ioo a b) (hτne : τ ≠ 0) :
    (fderiv ℝ (fun v => Ψ (τ,v)) 0).IsInvertible := by
  have hz : (0:E) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
  have hx : x ∈ S := hΨ0 0 hz ▸ himg 0 h0 0 hz
  have hi : ∀ y ∈ S, (g y).IsInvertible :=
    fun y hy => metricDual_isInvertible (g y) (hpos y hy)
  have hgd : ∀ t ∈ Ioo a b, ∀ v ∈ Metric.ball 0 R,
      DifferentiableAt ℝ g (Ψ (t,v)) := fun t ht v hv =>
    (hg.contDiffAt (hS.mem_nhds (himg t ht v hv))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hWτ0 : W (τ,0) = 0 := by
    have he := coordinate_geodesic_speed_constant
      (fun t ht => hgd t ht 0 hz) (fun t ht => hi _ (himg t ht 0 hz))
      (fun t ht => hsym _ (himg t ht 0 hz)) (fun t ht => hode t ht 0 hz) hτ h0
    simp only [hΨ0 0 hz,hW0 0 hz,map_zero] at he
    by_contra hn
    exact (ne_of_gt (hpos _ (himg τ hτ 0 hz) _ hn)) he
  have hopen : IsOpen (Ioo a b ×ˢ Metric.ball (0:E) R) :=
    isOpen_Ioo.prod Metric.isOpen_ball
  have hψ : ContDiffAt ℝ ∞ (fun v => Ψ (τ,v)) 0 :=
    (hΨ.contDiffAt (hopen.mem_nhds ⟨hτ,hz⟩)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)
  let L := fderiv ℝ (fun v => Ψ (τ,v)) 0
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro w hw
    let δ := R / (‖w‖+1)
    have hd : 0 < δ := div_pos hR (by positivity)
    have hsw : ∀ s ∈ Ioo (-δ) δ, s • w ∈ Metric.ball 0 R := by
      intro s hs
      rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
      have hsa := abs_lt.mpr hs
      have hmul : |s| * (‖w‖+1) < R := (lt_div_iff₀ (by positivity)).mp hsa
      nlinarith [abs_nonneg s]
    let A : ℝ × ℝ → E := fun z => Ψ (z.1,z.2 • w)
    let V : ℝ × ℝ → E := fun z => W (z.1,z.2 • w)
    have hA : ContDiffOn ℝ ∞ A (Ioo a b ×ˢ Ioo (-δ) δ) :=
      hΨ.comp (contDiffOn_fst.prodMk (contDiffOn_snd.smul contDiffOn_const))
        (fun z hz => ⟨hz.1,hsw z.2 hz.2⟩)
    have hV : ContDiffOn ℝ ∞ V (Ioo a b ×ˢ Ioo (-δ) δ) :=
      hW.comp (contDiffOn_fst.prodMk (contDiffOn_snd.smul contDiffOn_const))
        (fun z hz => ⟨hz.1,hsw z.2 hz.2⟩)
    have hs0 : (0:ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hd,hd⟩
    have hrect : IsOpen (Ioo a b ×ˢ Ioo (-δ) δ) := isOpen_Ioo.prod isOpen_Ioo
    have hAat : ContDiffAt ℝ ∞ A (τ,0) := hA.contDiffAt (hrect.mem_nhds ⟨hτ,hs0⟩)
    have hVat : ContDiffAt ℝ ∞ V (τ,0) := hV.contDiffAt (hrect.mem_nhds ⟨hτ,hs0⟩)
    have hJat := contDiffAt_directionalDerivative hAat (0,1)
    have hAr := hasDerivAt_slice_right (hAat.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have hVr := hasDerivAt_slice_right (hVat.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have hJr := hasDerivAt_slice_right (hJat.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have hswder : HasDerivAt (fun s : ℝ => s • w) w 0 := by
      convert (hasDerivAt_id (0:ℝ)).smul_const w using 1 <;> first | rfl | simp only [one_smul]
    have hψder := (show HasFDerivAt (fun v => Ψ (τ,v)) L ((0:ℝ) • w) by
      simpa only [zero_smul] using (hψ.differentiableAt (by simp)).hasFDerivAt
      ).comp_hasDerivAt 0 hswder
    have hJ0 : directionalDerivative A (0,1) (τ,0) = 0 := by
      have he : directionalDerivative A (0,1) (τ,0) = L w := hAr.unique hψder
      exact he.trans hw
    have hV0' : V (τ,0) = 0 := by simpa only [V,zero_smul] using hWτ0
    have hgdA : DifferentiableAt ℝ g (A (τ,0)) := by
      simpa only [A,zero_smul] using hgd τ hτ 0 hz
    have hAg : HasDerivAt (fun s => g (A (τ,s)))
        ((fderiv ℝ g (A (τ,0))) (directionalDerivative A (0,1) (τ,0))) 0 :=
      hgdA.hasFDerivAt.comp_hasDerivAt 0 hAr
    have hH := (hAg.clm_apply hVr).clm_apply hJr
    have hH0 : HasDerivAt (fun s => g (A (τ,s)) (V (τ,s))
        (directionalDerivative A (0,1) (τ,s))) 0 0 := by
      convert hH using 1
      all_goals try with_reducible_and_instances rfl
      simp only [hJ0,hV0',map_zero,zero_apply,add_zero,zero_add]
    have hHeq : (fun s => g (A (τ,s)) (V (τ,s))
        (directionalDerivative A (0,1) (τ,s))) =ᶠ[𝓝 0]
          (fun s => (τ * g x w w) * s) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs0] with s hs
      have hν : HasDerivAt (fun s : ℝ => s • w) w s := by
        convert (hasDerivAt_id s).smul_const w using 1 <;> first | rfl | simp only [one_smul]
      have hG := coordinate_gauss_variation hS hg hi hsym hA hV
        (fun t ht r hr => himg t ht (r • w) (hsw r hr))
        (fun t ht r hr => hode t ht (r • w) (hsw r hr))
        h0 (fun r hr => hΨ0 (r • w) (hsw r hr))
        (fun r hr => hW0 (r • w) (hsw r hr)) hτ hs hν
      dsimp only [A,V] at hG ⊢
      rw [hG]
      simp only [map_smul,smul_apply,smul_eq_mul]
      ring
    have hderRight : HasDerivAt (fun s => (τ * g x w w) * s) (τ * g x w w) 0 := by
      convert (hasDerivAt_id (0:ℝ)).const_mul (τ * g x w w) using 1 <;> first | rfl | simp only [mul_one]
    have he := (hH0.congr_of_eventuallyEq hHeq.symm).unique hderRight
    have hgww : g x w w = 0 := (mul_eq_zero.mp he.symm).resolve_left hτne
    by_contra hn
    exact (ne_of_gt (hpos x hx w hn)) hgww
  have hsur : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsur),rfl⟩

end WeakMTWTransport

end

end OAI
end

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

lemma normal_chart_gauss_dual_bound
    (e : OpenPartialHomeomorph E E) {y : E} (hy : y ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm y)) (hi : DifferentiableAt ℝ e.symm y)
    (g₀ g₁ : E →L[ℝ] E →L[ℝ] ℝ)
    (hg₁ : ∀ v, v ≠ 0 → 0 < g₁ v v) (hsym : ∀ u v, g₁ u v = g₁ v u)
    (V : E) {τ : ℝ}
    (henergy : g₁ V V = g₀ (e.symm y) (e.symm y))
    (hgauss : ∀ w, g₁ V ((fderiv ℝ e (e.symm y)) w) = τ * g₀ (e.symm y) w)
    (u : E) :
    |τ * g₀ (e.symm y) ((fderiv ℝ e.symm y) u)| ≤
      Real.sqrt (g₀ (e.symm y) (e.symm y)) * Real.sqrt (g₁ u u) := by
  have hd := congrArg (fun L : E →L[ℝ] E => L u)
    (fderiv_partial_homeomorph_right_inverse e hy he hi)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hd
  have hG := hgauss ((fderiv ℝ e.symm y) u)
  rw [hd] at hG
  rw [←hG,←henergy]
  exact positive_bilinear_abs_le g₁ hg₁ hsym V u

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_LocalMetricNormal
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
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma coordinate_flow_path_length
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {c : M} (hSto : S ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hmetric : ∀ z ∈ S, ∀ u v : E, g z u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) v))
    {η V : ℝ → E} {r : ℝ} (hη : ContDiffOn ℝ ∞ η (Ioo (-r) r))
    (himg : MapsTo η (Ioo (-r) r) S)
    (hode : ∀ t ∈ Ioo (-r) r, HasDerivAt η (V t) t ∧
      HasDerivAt V (-coordinateChristoffel g (η t) (V t) (V t)) t)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτr : τ < r) :
    pathELength 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) 0 τ =
      ENNReal.ofReal (τ * Real.sqrt (g (η 0) (V 0) (V 0))) := by
  have hr : 0 < r := hτ.trans_lt hτr
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  have hsub : Icc 0 τ ⊆ Ioo (-r) r := fun t ht => ⟨by linarith [ht.1],ht.2.trans_lt hτr⟩
  rw [inverse_coordinate_path_length ((hη.mono hsub).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (fun t ht => hSto (himg (hsub ht))) g (fun t ht => hmetric _ (himg (hsub ht)))]
  have hi : ∀ y ∈ S, (g y).IsInvertible := fun y hy => metricDual_isInvertible (g y) (hpos y hy)
  have hc : ∀ t ∈ Icc 0 τ, g (η t) (deriv η t) (deriv η t) = g (η 0) (V 0) (V 0) := by
    intro t ht
    rw [(hode t (hsub ht)).1.deriv]
    exact coordinate_geodesic_speed_constant
      (fun s hs => (hg.contDiffAt (hS.mem_nhds (himg hs))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (fun s hs => hi _ (himg hs)) (fun s hs => hsym _ (himg hs)) hode (hsub ht) h0
  calc
    _ = ∫⁻ t in Icc (0:ℝ) τ, ENNReal.ofReal (Real.sqrt (g (η 0) (V 0) (V 0))) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      rw [hc t ht]
    _ = _ := by rw [setLIntegral_const,Real.volume_Icc,sub_zero,ENNReal.ofReal_mul hτ,mul_comm]

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

def unitPathPrimitive (u : C(UnitTime,E)) : C(UnitTime,E) :=
  ⟨fun t => ∫ s in (0:ℝ)..t.val, extendUnitPath u s,
   (intervalIntegral.continuous_primitive
      (fun a b => (extendUnitPath u).continuous.intervalIntegrable a b) 0).comp
      continuous_subtype_val⟩

lemma unitPathPrimitive_bound (u : C(UnitTime,E)) : ‖unitPathPrimitive u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  change ‖∫ s in (0:ℝ)..t.val, extendUnitPath u s‖ ≤ ‖u‖
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := t.val) (f := extendUnitPath u)
    (C := ‖u‖) (fun s _ => u.norm_coe_le_norm (projIcc 0 1 (by positivity) s))
  apply h.trans
  rw [sub_zero,abs_of_nonneg t.property.1]
  exact mul_le_of_le_one_right (norm_nonneg u) t.property.2

def unitPathIntegral : C(UnitTime,E) →L[ℝ] C(UnitTime,E) := by
  let L : C(UnitTime,E) →ₗ[ℝ] C(UnitTime,E) :=
    { toFun := unitPathPrimitive
      map_add' := by
        intro u v; ext t
        change (∫ s in (0:ℝ)..t.val, extendUnitPath (u+v) s) =
          (∫ s in (0:ℝ)..t.val, extendUnitPath u s) +
          (∫ s in (0:ℝ)..t.val, extendUnitPath v s)
        rw [extendUnitPath_add]
        exact intervalIntegral.integral_add
          ((extendUnitPath u).continuous.intervalIntegrable _ _)
          ((extendUnitPath v).continuous.intervalIntegrable _ _)
      map_smul' := by
        intro c u; ext t
        change (∫ s in (0:ℝ)..t.val, extendUnitPath (c • u) s) =
          c • (∫ s in (0:ℝ)..t.val, extendUnitPath u s)
        rw [extendUnitPath_smul]
        exact intervalIntegral.integral_smul c (extendUnitPath u) }
  exact L.mkContinuous 1 (by
    intro u
    change ‖unitPathPrimitive (u : C(UnitTime,E))‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using unitPathPrimitive_bound u)

@[simp] lemma unitPathIntegral_apply (u : C(UnitTime,E)) (t : UnitTime) :
    unitPathIntegral u t = ∫ s in (0:ℝ)..t.val, extendUnitPath u s := rfl

lemma hasDerivAt_unitPathPrimitive [CompleteSpace E] (u : C(UnitTime,E)) (t : ℝ) :
    HasDerivAt (fun s => ∫ r in (0:ℝ)..s, extendUnitPath u r) (extendUnitPath u t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((extendUnitPath u).continuous.intervalIntegrable 0 t)
    (extendUnitPath u).continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    (extendUnitPath u).continuous.continuousAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_ImplicitODE
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

section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma exists_smooth_rescaled_ode_family_on (f : E → E) (hf : ContDiff ℝ ∞ f) (a : E) :
    ∃ U : (ℝ × E) → C(UnitTime,E), ∃ S : Set (ℝ × E), IsOpen S ∧ (0,a) ∈ S ∧
      ContDiffOn ℝ ∞ U S ∧ U (0,a) = ContinuousMap.const UnitTime a ∧
      ∀ z ∈ S, U z = ContinuousMap.const UnitTime z.2 +
        z.1 • unitPathIntegral ((⟨f,hf.continuous⟩ : C(E,E)).comp (U z)) := by
  let fC : C(E,E) := ⟨f,hf.continuous⟩
  exact exists_smooth_rescaled_equation_on (fun p => fC.comp p) (contDiff_path_comp fC hf)
    (ContinuousLinearMap.const ℝ UnitTime) unitPathIntegral a

end

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def rescaledIntegralCurve (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E)) (s : ℝ) : E :=
  x + t • ∫ r in (0:ℝ)..s, extendUnitPath (f.comp u) r

omit [CompleteSpace E] in
@[simp] lemma rescaledIntegralCurve_zero (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E)) :
    rescaledIntegralCurve f t x u 0 = x := by simp [rescaledIntegralCurve]

omit [CompleteSpace E] in
lemma rescaledIntegralCurve_eq (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E))
    (hu : u = ContinuousMap.const UnitTime x + t • unitPathIntegral (f.comp u)) (s : UnitTime) :
    rescaledIntegralCurve f t x u s = u s := by
  have h := congrArg (fun v : C(UnitTime,E) => v s) hu
  exact h.symm

lemma hasDerivAt_rescaledIntegralCurve (f : C(E,E)) (t : ℝ) (x : E) (u : C(UnitTime,E))
    (hu : u = ContinuousMap.const UnitTime x + t • unitPathIntegral (f.comp u))
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    HasDerivAt (rescaledIntegralCurve f t x u) (t • f (rescaledIntegralCurve f t x u s)) s := by
  have hd := ((hasDerivAt_unitPathPrimitive (f.comp u) s).const_smul t).const_add x
  have hc := rescaledIntegralCurve_eq f t x u hu ⟨s,hs⟩
  have he : extendUnitPath (f.comp u) s = f (rescaledIntegralCurve f t x u s) := by
    rw [hc]
    exact extendUnitPath_coe (f.comp u) ⟨s,hs⟩
  change HasDerivAt (rescaledIntegralCurve f t x u)
    (t • extendUnitPath (f.comp u) s) s at hd
  rw [he] at hd
  exact hd

lemma rescaled_ode_path_time_scaling (f : C(E,E)) (t : ℝ) (x : E)
    (u v : C(UnitTime,E)) (s : UnitTime) (K : ℝ≥0) (B : Set E)
    (hf : LipschitzOnWith K f B)
    (hu : u = ContinuousMap.const UnitTime x + t • unitPathIntegral (f.comp u))
    (hv : v = ContinuousMap.const UnitTime x + (t * s.val) • unitPathIntegral (f.comp v))
    (huB : ∀ r, u r ∈ B) (hvB : ∀ r, v r ∈ B) :
    u s = v ⟨1,by simp⟩ := by
  let U := rescaledIntegralCurve f t x u
  let V := rescaledIntegralCurve f (t*s.val) x v
  have hsr : ∀ r ∈ Icc (0:ℝ) 1, s.val * r ∈ Icc (0:ℝ) 1 := by
    intro r hr
    exact ⟨mul_nonneg s.property.1 hr.1,
      (mul_le_of_le_one_left hr.1 s.property.2).trans hr.2⟩
  have hU : ∀ r ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun q => U (s.val*q)) ((t*s.val) • f (U (s.val*r))) r := by
    intro r hr
    have h := (hasDerivAt_rescaledIntegralCurve f t x u hu (s.val*r) (hsr r hr)).scomp r
      ((hasDerivAt_id r).const_mul s.val)
    simpa only [mul_one,smul_smul,mul_comm,Function.comp_def,U] using h
  have hV : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt V ((t*s.val) • f (V r)) r :=
    hasDerivAt_rescaledIntegralCurve f (t*s.val) x v hv
  have hEq : EqOn (fun q => U (s.val*q)) V (Icc (0:ℝ) 1) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun (_ : ℝ) z => (t*s.val) • f z) (s := fun _ => B) (K := ‖t*s.val‖₊ * K)
    · intro r hr; exact lipschitzOnWith_const_smul hf (t*s.val)
    · exact HasDerivAt.continuousOn hU
    · intro r hr; exact (hU r (Ico_subset_Icc_self hr)).hasDerivWithinAt
    · intro r hr
      dsimp only [U]
      rw [rescaledIntegralCurve_eq f t x u hu ⟨s.val*r,hsr r (Ico_subset_Icc_self hr)⟩]
      exact huB _
    · exact HasDerivAt.continuousOn hV
    · intro r hr; exact (hV r (Ico_subset_Icc_self hr)).hasDerivWithinAt
    · intro r hr
      dsimp only [V]
      rw [rescaledIntegralCurve_eq f (t*s.val) x v hv ⟨r,Ico_subset_Icc_self hr⟩]
      exact hvB _
    · simp only [U,V,mul_zero,rescaledIntegralCurve_zero]
  have h := hEq (by simp : (1:ℝ) ∈ Icc (0:ℝ) 1)
  change U (s.val*1) = V 1 at h
  simpa only [mul_one,U,V,rescaledIntegralCurve_eq f t x u hu s,
    rescaledIntegralCurve_eq f (t*s.val) x v hv ⟨1,by simp⟩] using h

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_SmoothFlowEndpoint
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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma ode_family_initial {f : C(E,E)} {U : (ℝ × E) → C(UnitTime,E)} {x : E}
    (h : U (0,x) = ContinuousMap.const UnitTime x +
      (0:ℝ) • unitPathIntegral (f.comp (U (0,x)))) :
    U (0,x) = ContinuousMap.const UnitTime x := by simpa using h

lemma ode_family_endpoint_deriv_zero (f : C(E,E)) (hf : ContDiff ℝ ∞ f)
    (U : (ℝ × E) → C(UnitTime,E)) (x : E)
    (hU : ContDiffAt ℝ ∞ U (0,x))
    (hEq : ∀ᶠ z in 𝓝 ((0:ℝ),x), U z = ContinuousMap.const UnitTime z.2 +
      z.1 • unitPathIntegral (f.comp (U z))) :
    HasDerivAt (fun t => U (t,x) ⟨1,by simp⟩) (f x) 0 := by
  let e : UnitTime := ⟨1,by simp⟩
  let W : ℝ → E := fun t => unitPathIntegral (f.comp (U (t,x))) e
  have hW : ContDiffAt ℝ ∞ W 0 :=
    (ContinuousMap.evalCLM ℝ e).contDiff.contDiffAt.comp 0
      (unitPathIntegral.contDiff.contDiffAt.comp 0
        ((contDiff_path_comp f hf).contDiffAt.comp 0
          (hU.comp 0 (contDiffAt_id.prodMk contDiffAt_const))))
  have hUx : U (0,x) = ContinuousMap.const UnitTime x := ode_family_initial hEq.self_of_nhds
  have hW0 : W 0 = f x := by
    simp [W,unitPathIntegral_apply,hUx,extendUnitPath,ContinuousMap.comp_apply,e]
  have heq : (fun t : ℝ => U (t,x) e) =ᶠ[𝓝 0] (fun t => x + t • W t) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hEq] with t ht
    exact congrArg (fun u : C(UnitTime,E) => u e) ht
  have hd := ((hasDerivAt_id (0:ℝ)).smul (hW.differentiableAt (by simp)).hasDerivAt).const_add x
  change HasDerivAt (fun t => x + t • W t)
    ((0:ℝ) • deriv W 0 + (1:ℝ) • W 0) 0 at hd
  have hd' : HasDerivAt (fun t => x + t • W t) (f x) 0 := by
    simpa only [id_eq,Pi.smul_apply,one_smul,zero_smul,add_zero,zero_add,hW0] using hd
  exact hd'.congr_of_eventuallyEq heq

lemma ode_family_endpoint_deriv_ne_zero (f : C(E,E))
    (U : (ℝ × E) → C(UnitTime,E)) (S : Set (ℝ × E)) (hS : IsOpen S)
    (hEq : ∀ z ∈ S, U z = ContinuousMap.const UnitTime z.2 +
      z.1 • unitPathIntegral (f.comp (U z)))
    (K : ℝ≥0) (B : Set E) (hf : LipschitzOnWith K f B)
    (hB : ∀ z ∈ S, ∀ s, U z s ∈ B)
    (t : ℝ) (x : E) (ht : t ≠ 0) (htS : (t,x) ∈ S) (h2tS : (2*t,x) ∈ S) :
    HasDerivAt (fun q => U (q,x) ⟨1,by simp⟩)
      (f (U (t,x) ⟨1,by simp⟩)) t := by
  let a : ℝ := 2*t
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) ht
  have hratio : t/a = 1/2 := by dsimp [a]; field_simp
  have hmem : t/a ∈ Ioo (0:ℝ) 1 := by rw [hratio]; norm_num
  have hnear : ∀ᶠ q in 𝓝 t, (q,x) ∈ S ∧ q/a ∈ Ioo (0:ℝ) 1 :=
    ((continuousAt_id.prodMk continuousAt_const).eventually (hS.mem_nhds htS)).and
      ((continuousAt_id.div_const a).eventually (isOpen_Ioo.mem_nhds hmem))
  let γ := rescaledIntegralCurve f a x (U (a,x))
  have heq : (fun q => U (q,x) ⟨1,by simp⟩) =ᶠ[𝓝 t] (fun q => γ (q/a)) := by
    filter_upwards [hnear] with q hq
    have hqa : a * (q/a) = q := by field_simp
    have hs := rescaled_ode_path_time_scaling f a x (U (a,x)) (U (q,x))
      ⟨q/a,Ioo_subset_Icc_self hq.2⟩ K B hf (hEq (a,x) h2tS)
      (by simpa only [hqa] using hEq (q,x) hq.1)
      (hB (a,x) h2tS) (hB (q,x) hq.1)
    exact hs.symm.trans (rescaledIntegralCurve_eq f a x (U (a,x))
      (hEq (a,x) h2tS) ⟨q/a,Ioo_subset_Icc_self hq.2⟩).symm
  have hd := (hasDerivAt_rescaledIntegralCurve f a x (U (a,x))
    (hEq (a,x) h2tS) (t/a) (Ioo_subset_Icc_self hmem)).scomp t
      ((hasDerivAt_id t).div_const a)
  have hd' : HasDerivAt (fun q => γ (q/a)) (f (γ (t/a))) t := by
    simpa only [one_div,smul_smul,inv_mul_cancel₀ ha,one_smul,Function.comp_def,id_eq,γ] using hd
  have hpoint : U (t,x) ⟨1,by simp⟩ = γ (t/a) := heq.self_of_nhds
  rw [←hpoint] at hd'
  exact hd'.congr_of_eventuallyEq heq

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma exists_smooth_local_flow (f : E → E) (hf : ContDiff ℝ ∞ f) (a : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : (ℝ × E) → E,
      ContDiffOn ℝ ∞ Φ (Ioo (-r) r ×ˢ Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, Φ (0,x) = x) ∧
      ∀ t ∈ Ioo (-r) r, ∀ x ∈ Metric.ball a r,
        HasDerivAt (fun s => Φ (s,x)) (f (Φ (t,x))) t := by
  obtain ⟨U,S,hS,ha,hU,hUa,hEq⟩ := exists_smooth_rescaled_ode_family_on f hf a
  let fC : C(E,E) := ⟨f,hf.continuous⟩
  obtain ⟨K,B,hBa,hLip⟩ := (hf.contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1:ℕ∞ω) ≤ (∞:ℕ∞ω))).exists_lipschitzOnWith
  obtain ⟨b,hb,hbB⟩ := Metric.mem_nhds_iff.mp hBa
  have hcont : ContinuousAt U (0,a) := (hU.contDiffAt (hS.mem_nhds ha)).continuousAt
  have hn : ∀ᶠ z in 𝓝 ((0:ℝ),a), z ∈ S ∧ dist (U z) (ContinuousMap.const UnitTime a) < b := by
    have h := hcont.eventually (Metric.ball_mem_nhds (U (0,a)) hb)
    rw [hUa] at h
    exact (show ∀ᶠ z in 𝓝 ((0:ℝ),a), z ∈ S from hS.mem_nhds ha).and h
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hn
  let R := Metric.ball ((0:ℝ),a) ε
  have hRS : R ⊆ S := fun z hz => (hεsub hz).1
  have hRB : ∀ z ∈ R, ∀ s, U z s ∈ B := by
    intro z hz s
    apply hbB
    exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := U z)
      (g := ContinuousMap.const UnitTime a) s) (hεsub hz).2
  let r := ε/3
  have hr : 0 < r := div_pos hε (by norm_num)
  have htr : ∀ t ∈ Ioo (-r) r, ∀ x ∈ Metric.ball a r, (t,x) ∈ R ∧ (2*t,x) ∈ R := by
    intro t ht x hx
    have habs : |t| < r := abs_lt.mpr ht
    have hx' : dist x a < r := hx
    have hre : r < ε := by dsimp [r] <;> linarith
    have ht2 : |2*t| < ε := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]; dsimp [r] at habs; linarith
    constructor
    · change dist (t,x) (0,a) < ε
      rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
      exact ⟨habs.trans hre,hx'.trans hre⟩
    · change dist (2*t,x) (0,a) < ε
      rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
      exact ⟨ht2,hx'.trans hre⟩
  let Φ : (ℝ × E) → E := fun z => U z ⟨1,by simp⟩
  refine ⟨r,hr,Φ,?_,?_,?_⟩
  · have hUSub : ContDiffOn ℝ ∞ U (Ioo (-r) r ×ˢ Metric.ball a r) :=
      hU.mono (fun z hz => hRS (htr z.1 hz.1 z.2 hz.2).1)
    exact (ContinuousMap.evalCLM ℝ (⟨1,by simp⟩ : UnitTime)).contDiff.comp_contDiffOn hUSub
  · intro x hx
    have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨neg_neg_of_pos hr,hr⟩
    have hi := ode_family_initial (hEq (0,x) (hRS (htr 0 h0 x hx).1))
    exact congrArg (fun u : C(UnitTime,E) => u ⟨1,by simp⟩) hi
  · intro t ht x hx
    by_cases ht0 : t = 0
    · subst t
      have hi : Φ (0,x) = x := congrArg (fun u : C(UnitTime,E) => u ⟨1,by simp⟩)
        (ode_family_initial (hEq (0,x) (hRS (htr 0 ht x hx).1)))
      rw [hi]
      exact ode_family_endpoint_deriv_zero fC hf U x
        (hU.contDiffAt (hS.mem_nhds (hRS (htr 0 ht x hx).1)))
        (Filter.eventually_of_mem (hS.mem_nhds (hRS (htr 0 ht x hx).1)) hEq)
    · exact ode_family_endpoint_deriv_ne_zero fC U R Metric.isOpen_ball
        (fun z hz => hEq z (hRS hz)) K B hLip hRB t x ht0
        (htr t ht x hx).1 (htr t ht x hx).2

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_LocalDomainFlow
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]

lemma exists_smooth_local_flow_on {f : E → E} {S : Set E}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) {a : E} (ha : a ∈ S) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ S ∧ ∃ Φ : (ℝ × E) → E,
      ContDiffOn ℝ ∞ Φ (Ioo (-r) r ×ˢ Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, Φ (0,x) = x) ∧
      ∀ t ∈ Ioo (-r) r, ∀ x ∈ Metric.ball a r,
        Φ (t,x) ∈ S ∧ HasDerivAt (fun s => Φ (s,x)) (f (Φ (t,x))) t := by
  obtain ⟨g,hg,hgf⟩ := exists_smooth_extension_near hS hf ha
  obtain ⟨r,hr,Φ,hΦ,hΦ0,hΦder⟩ := exists_smooth_local_flow g hg a
  have hcenter : ((0:ℝ),a) ∈ Ioo (-r) r ×ˢ Metric.ball a r :=
    ⟨⟨neg_neg_of_pos hr,hr⟩,Metric.mem_ball_self hr⟩
  have hcont : ContinuousAt Φ (0,a) :=
    (hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds hcenter)).continuousAt
  have hΦa : Φ (0,a) = a := hΦ0 a (Metric.mem_ball_self hr)
  have hnear : ∀ᶠ z in 𝓝 ((0:ℝ),a), Φ z ∈ S ∧ g (Φ z) = f (Φ z) := by
    have h := hcont.eventually (show ∀ᶠ y in 𝓝 (Φ (0,a)), y ∈ S ∧ g y = f y from by
      rw [hΦa]
      exact (show ∀ᶠ y in 𝓝 a, y ∈ S from hS.mem_nhds ha).and hgf)
    exact h
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min (r/2) (ε/2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
  have hdom : Ioo (-δ) δ ×ˢ Metric.ball a δ ⊆ Ioo (-r) r ×ˢ Metric.ball a r := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1],hz.1.2.trans hδr⟩,lt_trans hz.2 hδr⟩
  have himg : ∀ t ∈ Ioo (-δ) δ, ∀ x ∈ Metric.ball a δ,
      Φ (t,x) ∈ S ∧ g (Φ (t,x)) = f (Φ (t,x)) := by
    intro t ht x hx
    apply hεsub
    change dist (t,x) (0,a) < ε
    rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
    exact ⟨(abs_lt.mpr ht).trans hδε,lt_trans hx hδε⟩
  refine ⟨δ,hδ,?_,Φ,hΦ.mono hdom,?_,?_⟩
  · intro x hx
    have h0 : Φ (0,x) = x := hΦ0 x (lt_trans hx hδr)
    exact h0 ▸ (himg 0 ⟨neg_neg_of_pos hδ,hδ⟩ x hx).1
  · intro x hx
    exact hΦ0 x (lt_trans hx hδr)
  · intro t ht x hx
    refine ⟨(himg t ht x hx).1,?_⟩
    rw [←(himg t ht x hx).2]
    have hz := hdom (show (t,x) ∈ Ioo (-δ) δ ×ˢ Metric.ball a δ from ⟨ht,hx⟩)
    exact hΦder t hz.1 x hz.2

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_SmoothCoordinateFlow
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_smooth_coordinate_flow
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hi : ∀ x ∈ S, (g x).IsInvertible)
    (x v : E) (hx : x ∈ S) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : (ℝ × (E × E)) → E × E,
      ContDiffOn ℝ ∞ Φ (Ioo (-r) r ×ˢ Metric.ball (x,v) r) ∧
      (∀ z ∈ Metric.ball (x,v) r, Φ (0,z) = z) ∧
      ∀ t ∈ Ioo (-r) r, ∀ z ∈ Metric.ball (x,v) r,
        (Φ (t,z)).1 ∈ S ∧
        HasDerivAt (fun q => (Φ (q,z)).1) (Φ (t,z)).2 t ∧
        HasDerivAt (fun q => (Φ (q,z)).2)
          (-coordinateChristoffel g (Φ (t,z)).1 (Φ (t,z)).2 (Φ (t,z)).2) t := by
  have hf : ContDiffOn ℝ ∞ (coordinateGeodesicField g) (S ×ˢ (univ : Set E)) := by
    intro z hz
    exact (contDiffAt_coordinateGeodesicField ((hg z.1 hz.1).contDiffAt
      (hS.mem_nhds hz.1)) (hi z.1 hz.1)).contDiffWithinAt
  obtain ⟨r,hr,_,Φ,hΦ,hΦ0,hder⟩ := exists_smooth_local_flow_on
    (hS.prod isOpen_univ) hf (a := (x,v)) ⟨hx,mem_univ _⟩
  refine ⟨r,hr,Φ,hΦ,hΦ0,?_⟩
  intro t ht z hz
  have h := hder t ht z hz
  exact ⟨h.1.1,h.2.fst,h.2.snd⟩

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_JointNormalChart
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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_joint_smooth_normal_chart
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {x : E} (hx : x ∈ S) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : ℝ × (E × E) → E × E,
      ContDiffOn ℝ ∞ Φ (Ioo (-r) r ×ˢ Metric.ball (x,0) r) ∧
      (∀ z ∈ Metric.ball (x,0) r, Φ (0,z) = z) ∧
      (∀ t ∈ Ioo (-r) r, ∀ z ∈ Metric.ball (x,0) r,
        (Φ (t,z)).1 ∈ S ∧
        HasDerivAt (fun q => (Φ (q,z)).1) (Φ (t,z)).2 t ∧
        HasDerivAt (fun q => (Φ (q,z)).2)
          (-coordinateChristoffel g (Φ (t,z)).1 (Φ (t,z)).2 (Φ (t,z)).2) t) ∧
      ∃ τ : ℝ, 0 < τ ∧ τ < r ∧ ∃ e : OpenPartialHomeomorph (E × E) (E × E),
        (e : (E × E) → (E × E)) = (fun z => (z.1,(Φ (τ,z)).1)) ∧
        (x,0) ∈ e.source ∧
        e.source ⊆ Metric.ball (x,0) r ∧
        ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hi : ∀ y ∈ S, (g y).IsInvertible :=
    fun y hy => metricDual_isInvertible (g y) (hpos y hy)
  obtain ⟨r,hr,Φ,hΦ,hΦ0,hΦode⟩ := exists_smooth_coordinate_flow hS hg hi x 0 hx
  have hball : ∀ v ∈ Metric.ball (0:E) r, (x,v) ∈ Metric.ball (x,0) r := by
    intro v hv
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_lt_iff] using And.intro hr hv
  have hΦc : ContDiffOn ℝ ∞ (fun z : ℝ × E => Φ (z.1,(x,z.2)))
      (Ioo (-r) r ×ˢ Metric.ball 0 r) :=
    hΦ.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
      (fun z hz => ⟨hz.1,hball z.2 hz.2⟩)
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨neg_neg_of_pos hr,hr⟩
  have hτ : r/2 ∈ Ioo (-r) r := ⟨by linarith,by linarith⟩
  have hinv := coordinate_endpoint_isInvertible (x := x) hS hg hpos hsym hr hΦc.fst hΦc.snd
    (fun t ht v hv => (hΦode t ht (x,v) (hball v hv)).1)
    (fun t ht v hv => (hΦode t ht (x,v) (hball v hv)).2)
    h0 (fun v hv => congrArg Prod.fst (hΦ0 (x,v) (hball v hv)))
    (fun v hv => congrArg Prod.snd (hΦ0 (x,v) (hball v hv)))
    hτ (by linarith : r/2 ≠ 0)
  have hψ : ContDiffOn ℝ ∞ (fun z => (Φ (r/2,z)).1) (Metric.ball (x,0) r) :=
    (hΦ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun z hz => ⟨hτ,hz⟩)).fst
  have hψa := (hψ.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hinv' := first_coordinate_preserving_derivative_invertible hψa hinv
  obtain ⟨e,he,hes,hesub,hed,hei⟩ := exists_smooth_local_diffeomorphism
    Metric.isOpen_ball (contDiffOn_fst.prodMk hψ) (Metric.mem_ball_self hr) hinv'
  exact ⟨r,hr,Φ,hΦ,hΦ0,hΦode,r/2,by positivity,hτ.2,e,he,hes,hesub,hed,hei⟩

end

end WeakMTWTransport
open Set

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayEnergy
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

variable [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma spray_chart_hasDerivAt {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (geodesicSpray (E := E)) t) :
    HasDerivAt (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) ∘ γ)
      (coordinateGeodesicField (riemannianCoordinateMetric (γ t).1)
        (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) (γ t))) t := by
  have hd := Filter.Eventually.self_of_nhds hγ.eventually_hasDerivAt
  rw [geodesicSpray_coordinates (γ t) (γ t)
    (mem_extChartAt_source (I := 𝓘(ℝ,E)) (γ t).1)] at hd
  exact hd

lemma spray_coordinate_energy_hasDerivAt {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (geodesicSpray (E := E)) t) :
    let q := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) ∘ γ
    HasDerivAt (fun s => riemannianCoordinateMetric (γ t).1 (q s).1 (q s).2 (q s).2) 0 t := by
  let q := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) ∘ γ
  have hd := spray_chart_hasDerivAt hγ
  have hqt : (q t).1 ∈ (extChartAt 𝓘(ℝ,E) (γ t).1).target :=
    (extChartAt 𝓘(ℝ,E) (γ t).1).map_source (mem_extChartAt_source (γ t).1)
  have hg : DifferentiableAt ℝ (riemannianCoordinateMetric (γ t).1) (q t).1 :=
    ((contDiffOn_riemannianCoordinateMetric (γ t).1).contDiffAt
      ((isOpen_extChartAt_target (γ t).1).mem_nhds hqt)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hpos : HasDerivAt (fun s => (q s).1) (q t).2 t :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t hd
  have hvel : HasDerivAt (fun s => (q s).2)
      (-coordinateChristoffel (riemannianCoordinateMetric (γ t).1) (q t).1 (q t).2 (q t).2) t :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t hd
  exact metric_speed_derivative (E := E) hg
    (riemannianCoordinateMetric_isInvertible hqt)
    (riemannianCoordinateMetric_symm _ _) hpos hvel

lemma hasDerivAt_spray_energy {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (geodesicSpray (E := E)) t) :
    HasDerivAt (fun s => ‖(γ s).2‖ ^ 2) 0 t := by
  apply (spray_coordinate_energy_hasDerivAt hγ).congr_of_eventuallyEq
  have hnear : ∀ᶠ s in 𝓝 t, (γ s).1 ∈ (extChartAt 𝓘(ℝ,E) (γ t).1).source := by
    have h := hγ.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t))
    filter_upwards [h] with s hs
    exact (tangent_chart_source_iff (γ t) (γ s)).mp hs
  filter_upwards [hnear] with s hs
  exact (coordinate_spray_energy (γ t) (γ s) hs).symm

lemma spray_speed_constant {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {a b s t : ℝ}
    (hγ : IsMIntegralCurveOn γ (geodesicSpray (E := E)) (Ioo a b))
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) : ‖(γ s).2‖ = ‖(γ t).2‖ := by
  have hd (r : ℝ) (hr : r ∈ Ioo a b) := hasDerivAt_spray_energy
    (hγ.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hr))
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht
  nlinarith [norm_nonneg (γ s).2,norm_nonneg (γ t).2]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_MIntegralCurveUniformInvariant
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

lemma exists_uniform_local_manifold_curves [CompleteSpace E] [HasContDiffBump E]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞
      (fun x => (⟨x,v x⟩ : TangentBundle I M))) (a : M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set M, U ∈ 𝓝 a ∧
      ∀ x ∈ U, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  let c := extChartAt I a
  obtain ⟨r,hr,_,Φ,_,hΦ0,hΦder⟩ := exists_smooth_local_flow_on
    (isOpen_extChartAt_target a) (contDiffOn_coordinate_vectorField hv a)
      (c.map_source (mem_extChartAt_source a))
  let U := c.source ∩ c ⁻¹' Metric.ball (c a) r
  have hUa : U ∈ 𝓝 a := inter_mem (extChartAt_source_mem_nhds a)
    ((continuousAt_extChartAt (I := I) (x := a)).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  refine ⟨r,hr,U,hUa,?_⟩
  intro x hx
  refine ⟨c.symm ∘ (fun t => Φ (t,c x)),?_,?_⟩
  · simp only [Function.comp_apply,hΦ0 _ hx.2,c.left_inv hx.1]
  · intro t ht
    exact (hasMFDerivAt_of_chart_ode a (hΦder t ht (c x) hx.2).1
      (hΦder t ht (c x) hx.2).2).hasMFDerivWithinAt

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_CompactFlow
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

lemma exists_uniform_time_on_compact {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (fun x => (⟨x,v x⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K,
      ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) := by
  classical
  choose r hr U hU hflow using exists_uniform_local_manifold_curves hv
  obtain ⟨t,_,ht⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  have hfin : ∀ t : Finset M, ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ t, ε ≤ r a := by
    intro s
    induction s using Finset.induction with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨ε,hε,hle⟩ := ih
      refine ⟨min ε (r a),lt_min hε (hr a),?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle b hb)
  obtain ⟨ε,hε,hle⟩ := hfin t
  refine ⟨ε,hε,?_⟩
  intro x hx
  obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (ht hx)
  obtain ⟨γ,hγ0,hγ⟩ := hflow a x hxa
  exact ⟨γ,hγ0,hγ.mono (Ioo_subset_Ioo (neg_le_neg (hle a ha)) (hle a ha))⟩

lemma exists_complete_curve_of_compact_invariant [T2Space M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (fun x => (⟨x,v x⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K)
    (hinv : ∀ (a : ℝ) (γ : ℝ → M), γ 0 ∈ K →
      IsMIntegralCurveOn γ v (Ioo (-a) a) → MapsTo γ (Ioo (-a) a) K)
    (x : M) (hx : x ∈ K) : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε,hε,hflow⟩ := exists_uniform_time_on_compact hv hK
  exact exists_isMIntegralCurve_of_uniform_invariant_set (hv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    hε hflow hinv x hx

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_CompleteSpray
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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma exists_complete_spray_curve (z : TangentBundle 𝓘(ℝ,E) M) :
    ∃ γ : ℝ → TangentBundle 𝓘(ℝ,E) M, γ 0 = z ∧
      IsMIntegralCurve γ (geodesicSpray (E := E)) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  have : IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,E))
  apply exists_complete_curve_of_compact_invariant contMDiff_geodesicSpray
    (isCompact_bundle_disk (F := E) (E := fun x : M => TangentSpace 𝓘(ℝ,E) x) ‖z.2‖)
    _ z (Set.mem_ofPred.mpr le_rfl)
  intro a γ hγ0 hγ t ht
  have ha : 0 < a := by obtain ⟨h₁,h₂⟩ := ht; linarith
  change ‖(γ t).2‖ ≤ ‖z.2‖
  rw [spray_speed_constant hγ ht ⟨neg_lt_zero.mpr ha,ha⟩]
  exact hγ0

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_LocalFlow_SmoothIntegralCurve
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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

lemma exists_smooth_local_manifold_flow {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞
      (fun x => (⟨x,v x⟩ : TangentBundle I M))) (a : M) :
    ∃ r : ℝ, 0 < r ∧ ∃ U : Set M, IsOpen U ∧ a ∈ U ∧
      ∃ Φ : ℝ × M → M,
        ContMDiffOn (𝓘(ℝ,ℝ).prod I) I ∞ Φ (Ioo (-r) r ×ˢ U) ∧
        (∀ x ∈ U, Φ (0,x) = x) ∧
        (∀ x ∈ U, IsMIntegralCurveOn (fun t => Φ (t,x)) v (Ioo (-r) r)) := by
  let c := extChartAt I a
  obtain ⟨r,hr,_,Ψ,hΨ,hΨ0,hΨder⟩ := exists_smooth_local_flow_on
    (isOpen_extChartAt_target a) (contDiffOn_coordinate_vectorField hv a)
      (c.map_source (mem_extChartAt_source a))
  let U := c.source ∩ c ⁻¹' Metric.ball (c a) r
  have hU : IsOpen U := isOpen_extChartAt_preimage' a Metric.isOpen_ball
  have ha : a ∈ U := ⟨mem_extChartAt_source a,Metric.mem_ball_self hr⟩
  let Φ : ℝ × M → M := fun z => c.symm (Ψ (z.1,c z.2))
  refine ⟨r,hr,U,hU,ha,Φ,?_,?_,?_⟩
  · intro z hz
    have hc : ContMDiffAt I 𝓘(ℝ,E) ∞ c z.2 :=
      (contMDiffOn_extChartAt (I := I) (n := ∞) (x := a)).contMDiffAt
        (by simpa only [extChartAt_source] using
          (isOpen_extChartAt_source (I := I) a).mem_nhds hz.2.1)
    have hg : ContDiffAt ℝ ∞ Ψ (z.1,c z.2) :=
      hΨ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds ⟨hz.1,hz.2.2⟩)
    have hsym : ContMDiffAt 𝓘(ℝ,E) I ∞ c.symm (Ψ (z.1,c z.2)) :=
      (contMDiffOn_extChartAt_symm a).contMDiffAt
        ((isOpen_extChartAt_target a).mem_nhds (hΨder z.1 hz.1 (c z.2) hz.2.2).1)
    have hpair : ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ × E) ∞
        (fun w : ℝ × M => (w.1,c w.2)) z :=
      contMDiffAt_prod_module_iff _ |>.mpr ⟨contMDiffAt_fst,hc.comp z contMDiffAt_snd⟩
    exact (hsym.comp z (hg.contMDiffAt.comp z hpair)).contMDiffWithinAt
  · intro x hx
    simp only [Φ,hΨ0 _ hx.2,c.left_inv hx.1]
  · intro x hx t ht
    exact (hasMFDerivAt_of_chart_ode a (hΨder t ht (c x) hx.2).1
      (hΨder t ht (c x) hx.2).2).hasMFDerivWithinAt

end
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]
  {v : (x : M) → TangentSpace I x}

variable (hc : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v)

variable (hv : ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (fun x => (⟨x,v x⟩ : TangentBundle I M)))
include hv

lemma contMDiff_completeFlow_time_slice (t : ℝ) : ContMDiff I I ∞ (completeFlow hc t) := by
  intro a
  let T : Set ℝ := {s | ContMDiffAt I I ∞ (completeFlow hc s) a}
  have hT0 : 0 ∈ T := by
    change ContMDiffAt I I ∞ (completeFlow hc 0) a
    have hzero : completeFlow hc 0 = id := funext (completeFlow_zero hc)
    rw [hzero]
    exact contMDiffAt_id
  have hopen : IsOpen T := by
    apply Metric.isOpen_iff.mpr
    intro s hs
    obtain ⟨r,hr,U,hU,hUa,Φ,hΦ,hΦ0,hΦode⟩ :=
      exists_smooth_local_manifold_flow hv (completeFlow hc s a)
    refine ⟨r,hr,?_⟩
    intro t ht
    exact completeFlow_smooth_step hc hv hr hU hΦ hΦ0 hΦode hs hUa
      (by simpa only [Metric.mem_ball,Real.dist_eq,abs_lt,mem_Ioo] using ht)
  have hcompl : IsOpen Tᶜ := by
    apply Metric.isOpen_iff.mpr
    intro t ht
    obtain ⟨r,hr,U,hU,hUa,Φ,hΦ,hΦ0,hΦode⟩ :=
      exists_smooth_local_manifold_flow hv (completeFlow hc t a)
    have hnear := (completeFlow_curve hc a).continuous.continuousAt.preimage_mem_nhds
      (hU.mem_nhds hUa)
    obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hnear
    refine ⟨min r δ,lt_min hr hδ,?_⟩
    intro s hs hsm
    have hsr : dist s t < r := lt_of_lt_of_le hs (min_le_left _ _)
    have hsδ : dist s t < δ := lt_of_lt_of_le hs (min_le_right _ _)
    apply ht
    exact completeFlow_smooth_step hc hv hr hU hΦ hΦ0 hΦode hsm (hδU hsδ)
      (by simpa only [Real.dist_eq,abs_sub_comm,abs_lt,mem_Ioo] using hsr)
  have hTuniv : T = univ := (IsClopen.eq_univ ⟨isOpen_compl_iff.mp hcompl,hopen⟩ ⟨0,hT0⟩)
  change t ∈ T
  rw [hTuniv]
  exact mem_univ t

lemma contMDiff_completeFlow :
    ContMDiff (𝓘(ℝ,ℝ).prod I) I ∞ (fun z : ℝ × M => completeFlow hc z.1 z.2) := by
  intro z
  obtain ⟨r,hr,U,hU,hUa,Φ,hΦ,hΦ0,hΦode⟩ :=
    exists_smooth_local_manifold_flow hv (completeFlow hc z.1 z.2)
  have hs := (contMDiff_completeFlow_time_slice hc hv z.1) z.2
  have hpair : ContMDiffAt (𝓘(ℝ,ℝ).prod I) (𝓘(ℝ,ℝ).prod I) ∞
      (fun w : ℝ × M => (w.1-z.1,completeFlow hc z.1 w.2)) z :=
    (contMDiffAt_fst.sub contMDiffAt_const).prodMk (hs.comp z contMDiffAt_snd)
  have hsm := (hΦ.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
    (show (z.1-z.1,completeFlow hc z.1 z.2) ∈ Ioo (-r) r ×ˢ U from
      ⟨by simp only [sub_self,mem_Ioo]; exact ⟨neg_lt_zero.mpr hr,hr⟩,hUa⟩))).comp z hpair
  apply hsm.congr_of_eventuallyEq
  have hnear := hpair.continuousAt.preimage_mem_nhds
    ((isOpen_Ioo.prod hU).mem_nhds
      (show (z.1-z.1,completeFlow hc z.1 z.2) ∈ Ioo (-r) r ×ˢ U from
        ⟨by simp only [sub_self,mem_Ioo]; exact ⟨neg_lt_zero.mpr hr,hr⟩,hUa⟩))
  filter_upwards [hnear] with w hw
  change completeFlow hc w.1 w.2 = Φ (w.1-z.1,completeFlow hc z.1 w.2)
  rw [← completeFlow_eq_local hc hv hr hΦ0 hΦode hw.2 hw.1,
    ← completeFlow_add hc hv,sub_add_cancel]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayProjection
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

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma hasMFDerivAt_spray_projection {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (geodesicSpray (E := E)) t) :
    HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun s => (γ s).1) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (γ t).2) := by
  have hd := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t
    (spray_chart_hasDerivAt hγ)
  have ht := mem_extChartAt_source (I := 𝓘(ℝ,E)) (γ t).1
  have hself : (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) (γ t)).2 =
      (γ t).2 := by
    rw [tangent_chart_apply]
    exact tangentCoordChange_self ht
  change HasDerivAt (fun s => (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) (γ s)).1)
    (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (γ t) (γ t)).2 t at hd
  rw [hself] at hd
  have hd' : HasDerivAt (extChartAt 𝓘(ℝ,E) (γ t).1 ∘ (fun s => (γ s).1))
      (γ t).2 t := by
    simpa only [Function.comp_def,tangent_chart_apply] using hd
  refine ⟨(FiberBundle.continuous_proj E (fun x : M => TangentSpace 𝓘(ℝ,E) x)).continuousAt.comp
    hγ.continuousAt,?_⟩
  rw [writtenInExtChartAt,extChartAt_model_space_eq_id,ModelWithCorners.range_eq_univ]
  change HasFDerivWithinAt (extChartAt 𝓘(ℝ,E) (γ t).1 ∘ (fun s => (γ s).1))
    ((1 : ℝ →L[ℝ] ℝ).smulRight (γ t).2) univ t
  rw [hasFDerivWithinAt_univ]
  convert! hd'.hasFDerivAt using 1
  all_goals try with_reducible_and_instances rfl

lemma spray_velocity_eq_mfderiv {γ : ℝ → TangentBundle 𝓘(ℝ,E) M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (geodesicSpray (E := E)) t) :
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun s => (γ s).1) t (1 : ℝ) = (γ t).2 := by
  have h := congrArg (fun f : TangentSpace 𝓘(ℝ,ℝ) t →L[ℝ]
    TangentSpace 𝓘(ℝ,E) (γ t).1 => f (1 : ℝ)) (hasMFDerivAt_spray_projection hγ).mfderiv
  change mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun s => (γ s).1) t (1 : ℝ) =
    (1 : ℝ) • (γ t).2 at h
  simpa only [one_smul] using h

variable [T2Space M] [CompactSpace M]

def sprayFlow (t : ℝ) (z : TangentBundle 𝓘(ℝ,E) M) : TangentBundle 𝓘(ℝ,E) M :=
  completeFlow exists_complete_spray_curve t z

lemma sprayFlow_zero (z : TangentBundle 𝓘(ℝ,E) M) : sprayFlow 0 z = z :=
  completeFlow_zero exists_complete_spray_curve z

lemma sprayFlow_curve (z : TangentBundle 𝓘(ℝ,E) M) :
    IsMIntegralCurve (fun t => sprayFlow t z) (geodesicSpray (E := E)) :=
  completeFlow_curve exists_complete_spray_curve z

lemma sprayFlow_add (s t : ℝ) (z : TangentBundle 𝓘(ℝ,E) M) :
    sprayFlow (s+t) z = sprayFlow s (sprayFlow t z) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  exact completeFlow_add exists_complete_spray_curve contMDiff_geodesicSpray s t z

lemma contMDiff_sprayFlow :
    ContMDiff (𝓘(ℝ,ℝ).prod (𝓘(ℝ,E).prod 𝓘(ℝ,E))) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun z : ℝ × TangentBundle 𝓘(ℝ,E) M => sprayFlow z.1 z.2) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  exact contMDiff_completeFlow exists_complete_spray_curve contMDiff_geodesicSpray

lemma sprayFlow_speed (t : ℝ) (z : TangentBundle 𝓘(ℝ,E) M) :
    ‖(sprayFlow t z).2‖ = ‖z.2‖ := by
  have he := spray_speed_constant ((sprayFlow_curve z).isMIntegralCurveOn (Ioo (min t 0-1) (max t 0+1)))
    (show t ∈ Ioo (min t 0-1) (max t 0+1) from
      ⟨by linarith [min_le_left t 0],by linarith [le_max_left t 0]⟩)
    (show (0:ℝ) ∈ Ioo (min t 0-1) (max t 0+1) from
      ⟨by linarith [min_le_right t 0],by linarith [le_max_right t 0]⟩)
  exact he.trans (congrArg (fun w : TangentBundle 𝓘(ℝ,E) M => ‖w.2‖) (sprayFlow_zero z))

end
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma hasMFDerivAt_of_coordinate_spray (a : TangentBundle 𝓘(ℝ,E) M)
    {q : ℝ → E × E} {t : ℝ} (hq : (q t).1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target)
    (hd : HasDerivAt q (coordinateGeodesicField (riemannianCoordinateMetric a.1) (q t)) t) :
    HasMFDerivAt 𝓘(ℝ,ℝ) (𝓘(ℝ,E).prod 𝓘(ℝ,E))
      ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm ∘ q) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicSpray ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm (q t)))) := by
  have hqt := (tangent_chart_target_iff a (q t)).mpr hq
  apply hasMFDerivAt_of_chart_ode a hqt
  rw [geodesicSpray_coordinates a _ ((tangent_chart_source_iff a _).mp
    ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).map_target hqt)),
    (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).right_inv hqt]
  exact hd

variable [T2Space M] [CompactSpace M]

lemma sprayFlow_eq_coordinate_curve (a : TangentBundle 𝓘(ℝ,E) M)
    {q : ℝ → E × E} {r : ℝ} (hr : 0 < r)
    (himg : ∀ t ∈ Ioo (-r) r, (q t).1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target)
    (hode : ∀ t ∈ Ioo (-r) r,
      HasDerivAt q (coordinateGeodesicField (riemannianCoordinateMetric a.1) (q t)) t)
    {z : TangentBundle 𝓘(ℝ,E) M}
    (hq0 : (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm (q 0) = z)
    {t : ℝ} (ht : t ∈ Ioo (-r) r) :
    sprayFlow t z = (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm (q t) := by
  have : T2Space (TangentBundle 𝓘(ℝ,E) M) := bundle_totalSpace_t2
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨neg_lt_zero.mpr hr,hr⟩ (contMDiff_geodesicSpray.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((sprayFlow_curve z).isMIntegralCurveOn _) _ _ ht
  · intro s hs
    exact (hasMFDerivAt_of_coordinate_spray a (himg s hs) (hode s hs)).hasMFDerivWithinAt
  · exact (sprayFlow_zero z).trans hq0.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayScaling
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
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma isMIntegralCurve_spray_scaled {γ : ℝ → TangentBundle 𝓘(ℝ,E) M}
    (hγ : IsMIntegralCurve γ (geodesicSpray (E := E))) (c : ℝ) :
    IsMIntegralCurve (fun t => tangentScale c (γ (c*t))) (geodesicSpray (E := E)) := by
  intro t
  let a := γ (c*t)
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a
  let P : ℝ → E × E := fun s => ((χ (γ (c*s))).1,c • (χ (γ (c*s))).2)
  have hd := coordinate_geodesic_scale (spray_chart_hasDerivAt (hγ.isMIntegralCurveAt (c*t)))
    (c := c)
  have hPt : (P t).1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target := by
    change (χ a).1 ∈ _
    rw [tangent_chart_apply]
    exact mem_extChartAt_target a.1
  have hδ : (χ.symm ∘ P) =ᶠ[𝓝 t] (fun s => tangentScale c (γ (c*s))) := by
    have hc : ContinuousAt (fun s => γ (c*s)) t :=
      (hγ.isMIntegralCurveAt (c*t)).continuousAt.comp (continuousAt_const.mul continuousAt_id)
    have hn : ∀ᶠ s in 𝓝 t, γ (c*s) ∈ χ.source :=
      hc.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) a)
    filter_upwards [hn] with s hs
    have hss : tangentScale c (γ (c*s)) ∈ χ.source :=
      (tangent_chart_source_iff a _).mpr ((tangent_chart_source_iff a _).mp hs)
    change χ.symm (P s) = _
    rw [show P s = χ (tangentScale c (γ (c*s))) from (tangent_chart_scale a _ c).symm]
    exact χ.left_inv hss
  have scaledDeriv :=
    (hasMFDerivAt_of_coordinate_spray a hPt hd).congr_of_eventuallyEq hδ.symm
  have scaledPoint : (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm (P t) =
      tangentScale c (γ (c*t)) := hδ.self_of_nhds
  apply scaledDeriv.congr_mfderiv
  exact congrArg (fun point : TangentBundle 𝓘(ℝ,E) M =>
    (1 : ℝ →L[ℝ] ℝ).smulRight (show E × E from geodesicSpray point)) scaledPoint

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalRigidity
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
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma coordinate_curve_speed_square {γ : ℝ → M} {t : ℝ} {a : M}
    (hγ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t)
    (ha : γ t ∈ (extChartAt 𝓘(ℝ,E) a).source) :
    riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a (γ t))
      (deriv (extChartAt 𝓘(ℝ,E) a ∘ γ) t) (deriv (extChartAt 𝓘(ℝ,E) a ∘ γ) t) =
      ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)‖^2 := by
  let c := extChartAt 𝓘(ℝ,E) a
  let g := riemannianCoordinateMetric a (c (γ t))
  have hm := mfderiv_comp t (mdifferentiableAt_extChartAt
    (I := 𝓘(ℝ,E)) (x := a) (by simpa only [extChartAt_source] using ha)) hγ
  rw [mfderiv_eq_fderiv] at hm
  have hval : deriv (c ∘ γ) t = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c (γ t)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1) :=
    congrArg (fun L : ℝ →L[ℝ] E => L 1) hm
  have hnorm := coordinate_metric_chart_derivative_norm ha
    (g := g) (by
      intro u v
      change riemannianCoordinateMetric a (c (γ t)) u v = _
      rw [riemannianCoordinateMetric_apply,c.left_inv ha])
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1)
  rw [←hval] at hnorm
  calc
    _ = (Real.sqrt (g (deriv (c ∘ γ) t) (deriv (c ∘ γ) t)))^2 :=
      (Real.sq_sqrt (positive_bilinear_nonneg g
        (fun v hv => riemannianCoordinateMetric_positive (c.map_source ha) hv) _)).symm
    _ = _ := congrArg (fun x : ℝ => x^2) hnorm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_GeodesicExistence
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
  {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_flow_eq_spray (a : M) {r : ℝ} (hr : 0 < r)
    {Ψ W : ℝ × E → E}
    (hinit : ∀ v ∈ Metric.ball (0:E) r,
      Ψ (0,v) = extChartAt 𝓘(ℝ,E) a a ∧ W (0,v) = v)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball (0:E) r,
      Ψ (t,v) ∈ (extChartAt 𝓘(ℝ,E) a).target ∧
      HasDerivAt (fun s => Ψ (s,v)) (W (t,v)) t ∧
      HasDerivAt (fun s => W (s,v))
        (-coordinateChristoffel (riemannianCoordinateMetric a) (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {v : E} (hv : v ∈ Metric.ball (0:E) r) {t : ℝ} (ht : t ∈ Ioo (-r) r) :
    Ψ (t,v) = extChartAt 𝓘(ℝ,E) a (sprayFlow t ⟨a,v⟩).1 := by
  let z : TangentBundle 𝓘(ℝ,E) M := ⟨a,0⟩
  have H := sprayFlow_eq_coordinate_curve z hr
    (fun s hs => (hode s hs v hv).1)
    (fun s hs => (hode s hs v hv).2.1.prodMk (hode s hs v hv).2.2)
    (show (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z).symm (Ψ (0,v), W (0,v)) = ⟨a,v⟩ by
      rw [(hinit v hv).1,(hinit v hv).2]
      exact tangent_chart_at_self_base_symm z v) ht
  have Hc := congrArg (fun p : TangentBundle 𝓘(ℝ,E) M => extChartAt 𝓘(ℝ,E) a p.1) H
  rw [tangent_chart_symm_base,(extChartAt 𝓘(ℝ,E) a).right_inv (hode t ht v hv).1] at Hc
  exact Hc.symm

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_ShortGradient
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

omit [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma contMDiff_spray_fiber (x : M) (t : ℝ) :
    ContMDiff 𝓘(ℝ,TangentSpace 𝓘(ℝ,E) x) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun v : TangentSpace 𝓘(ℝ,E) x => sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)) :=
  contMDiff_sprayFlow.comp (contMDiff_const.prodMk (contMDiff_fiber_embedding x))

end WeakMTWTransport

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

lemma cTransform_lipschitz {v : M → ℝ} (hv : Continuous v) {D : ℝ≥0}
    (hD : ∀ x y : M, dist x y ≤ D) : LipschitzWith D (cTransform v) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x x'
  rw [Real.dist_eq, abs_le]
  obtain ⟨y, hy, hmax⟩ := exists_cTransform_contact hv x
  obtain ⟨y', hy', hmax'⟩ := exists_cTransform_contact hv x'
  have hcost := cost_lipschitz_of_distance_bound hD x x' y
  have hcost' := cost_lipschitz_of_distance_bound hD x x' y'
  constructor
  · have hh := hmax y'
    rw [hy']
    linarith [(abs_le.mp hcost').2]
  · have hh := hmax' y
    rw [hy]
    linarith [(abs_le.mp hcost).1]

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

def hopfPole (t : ℝ) (u : M → ℝ) (z : M) : M :=
  (sprayFlow (-t) (⟨z,riemannianGradient (n := n) (hopfLax t u) z⟩ :
    TangentBundle 𝓘(ℝ,Model n) M)).1

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_JensenPackage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

abbrev chartActualPole (v : M → ℝ) (t : ℝ) (a : M) : Model n → M :=
  fun z=>hopfPole (n := n) t (cTransform v) ((extChartAt 𝓘(ℝ,Model n) a).symm z)
end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Convexity_JensenAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

structure JensenSamplesAt (v g : M → ℝ) (t : ℝ) (a c : M) (N : Set (Model n)) where
  z : ℕ → Model n
  Y : Model n → M
  Af : Model n →L[ℝ] Model n →L[ℝ] ℝ
  Ac : Model n →L[ℝ] Model n →L[ℝ] ℝ
  points : Tendsto z atTop (𝓝 (extChartAt 𝓘(ℝ,Model n) a c))
  outerHessians : Tendsto (fun i=>fderiv ℝ (fderiv ℝ (chartOuterEnvelope v t a)) (z i)) atTop (𝓝 Af)
  centerHessians : Tendsto (fun i=>fderiv ℝ (fderiv ℝ (chartCenterEnvelope g t a)) (z i)) atTop (𝓝 Ac)
  gradients : Tendsto (fun i=>fderiv ℝ (chartOuterEnvelope v t a) (z i)+
    fderiv ℝ (chartCenterEnvelope g t a) (z i)) atTop (𝓝 0)
  upper : ∀ d:Model n,Af d d+Ac d d≤0
  region : Set (Model n)
  openRegion : IsOpen region
  centerInRegion : extChartAt 𝓘(ℝ,Model n) a c∈region
  sampleInRegion : ∀ i,z i∈region
  outerDifferentiable : ∀ z∈region,DifferentiableAt ℝ (chartOuterEnvelope v t a) z
  centerDifferentiable : ∀ z∈region,DifferentiableAt ℝ (chartCenterEnvelope g t a) z
  outerGradientContinuous : ContinuousOn (fderiv ℝ (chartOuterEnvelope v t a)) region
  centerGradientContinuous : ContinuousOn (fderiv ℝ (chartCenterEnvelope g t a)) region
  selectorContinuous : ContinuousOn (fun z=>extChartAt 𝓘(ℝ,Model n) a (Y z)) region
  actual : ∀ z∈region,
    let χ := extChartAt 𝓘(ℝ,Model n) a
    let P : Model n → M := chartActualPole v t a
    let χP := extChartAt 𝓘(ℝ,Model n) (P (χ c))
    Y z∈χ.source ∧ P z∈χP.source ∧
    (∀ y:M,chartCenterEnvelope g t a z=g y+cost y (χ.symm z)/(1-t) ↔ y=Y z) ∧
    chartOuterEnvelope v t a z=cTransform v (P z)+cost (P z) (χ.symm z)/t
  samples : ∀ i,
    let χ := extChartAt 𝓘(ℝ,Model n) a
    let P : Model n → M := chartActualPole v t a
    let χP := extChartAt 𝓘(ℝ,Model n) (P (χ c))
    let F : Model n → ℝ := chartOuterEnvelope v t a
    let C := chartCenterEnvelope g t a
    Y (z i)∈χ.source ∧ P (z i)∈χP.source ∧
    (∀ y:M,C (z i)=g y+cost y (χ.symm (z i))/(1-t) ↔ y=Y (z i)) ∧
    F (z i)=cTransform v (P (z i))+cost (P (z i)) (χ.symm (z i))/t ∧
    HasFDerivAt (fun w=>χ (Y w)) (fderiv ℝ (fun w=>χ (Y w)) (z i)) (z i) ∧
    HasFDerivAt (fun w=>χP (P w)) (fderiv ℝ (fun w=>χP (P w)) (z i)) (z i) ∧
    ((fderiv ℝ (fun w=>χ (Y w)) (z i)).det≠0 → χ (Y (z i))∉N) ∧
    DifferentiableAt ℝ (fderiv ℝ F) (z i) ∧ DifferentiableAt ℝ (fderiv ℝ C) (z i) ∧
    HasSecondTaylor (fun h=>F (z i+h)) (fderiv ℝ F (z i)) (fderiv ℝ (fderiv ℝ F) (z i)) ∧
    HasSecondTaylor (fun h=>C (z i+h)) (fderiv ℝ C (z i)) (fderiv ℝ (fderiv ℝ C) (z i))

end WeakMTWTransport

end

end OAI
end


