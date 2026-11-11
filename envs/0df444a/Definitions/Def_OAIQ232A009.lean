-- Prove2me | Definitions.Def_OAIQ232A009
-- name    : OAIQ232A009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:44:54.444044+00:00
-- url     : https://prove2.me/theorems/1908ab50-7279-446c-bb75-876cf874ed46
-- title:
--   Definitions bundle OAIQ232A009 of the split of OpenAI, Uniform Bi-Holder Transport from Weak MTW (result family 360)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWTransport.uniform_biHolder_transport`, carved from OpenAI's openai/math development (OpenAI, *Uniform Bi-Holder Transport from Weak MTW (result family 360)*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 3 definitions and 16 theorems. The definitions and types are `OAI.WeakMTWTransport.contactImage`, `OAI.WeakMTWTransport.gapSection`, `OAI.WeakMTWTransport.splitNormalAction`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BiholderTransport_Coordinates_CoordinateGradient`, `BiholderTransport_Coordinates_IntrinsicGradient`, `BiholderTransport_Coordinates_NormalGradient`, `BiholderTransport_Coordinates_NormalRigidity`, `BiholderTransport_Coordinates_SplitAction`, `BiholderTransport_Coordinates_UniformShort`, `BiholderTransport_Geodesics_MetricSegments`, `BiholderTransport_Geodesics_SprayDistanceBound`, `BiholderTransport_Geodesics_SprayMinimizerUnique`, `BiholderTransport_Geodesics_SprayScaling`, `BiholderTransport_Regularity_MetricDefinitions`, `BiholderTransport_Regularity_RiemannianMetricSegment`, `BiholderTransport_Volume_MeasureContacts`, `BiholderTransport_Volume_RadialCalibration`.
--
--   **Imports.** It imports the published bundle `Def_BiholderTransport`; the bundles `OAIQ232A000`, `OAIQ232A001`, `OAIQ232A002` and `OAIQ232A004` of this split.
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
import Definitions.Def_BiholderTransport
import Definitions.Def_OAIQ232A000
import Definitions.Def_OAIQ232A001
import Definitions.Def_OAIQ232A002
import Definitions.Def_OAIQ232A004

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_IntrinsicGradient
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
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_metric_chart_pairing {a y : M}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (u v : TangentSpace 𝓘(ℝ,E) y) :
    riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a y)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y u)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) y v) = inner ℝ u v := by
  let c := extChartAt 𝓘(ℝ,E) a
  let e := trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a
  have hy' : y ∈ (chartAt E a).source := by simpa only [extChartAt_source] using hy
  have hbase : y ∈ e.baseSet := hy'
  have hInv : ∀ w : TangentSpace 𝓘(ℝ,E) y,
      e.symmL ℝ y (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c y w) = w := by
    intro w
    have hh := e.symmL_continuousLinearMapAt (R := ℝ) hbase w
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hy'] at hh
    exact hh
  erw [riemannianCoordinateMetric_apply,c.left_inv hy,hInv u,hInv v]

lemma hasMFDerivAt_of_coordinate_gradient {a : M} (z : TangentBundle 𝓘(ℝ,E) M)
    (hz : z.1 ∈ (extChartAt 𝓘(ℝ,E) a).source) (f : M → ℝ) (τ : ℝ)
    (hD : HasFDerivAt (fun w : E => f ((extChartAt 𝓘(ℝ,E) a).symm w))
      (τ • riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a z.1)
        ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E))
          (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) z).2))
      (extChartAt 𝓘(ℝ,E) a z.1)) :
    HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f z.1 (τ • innerSL ℝ z.2) := by
  let c := extChartAt 𝓘(ℝ,E) a
  have hz' : z.1 ∈ (chartAt E a).source := by simpa only [extChartAt_source] using hz
  have hDc := (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) hz').hasMFDerivAt
  have H := hD.hasMFDerivAt.comp z.1 hDc
  have heq : f =ᶠ[𝓝 z.1] (fun x : M => f (c.symm (c x))) := by
    filter_upwards [(isOpen_extChartAt_source a).mem_nhds hz] with x hx
    rw [c.left_inv hx]
  have H' := H.congr_of_eventuallyEq heq
  apply H'.congr_mfderiv
  ext w
  change τ * riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a z.1)
    ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) z).2)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) a) z.1 w) = τ * inner ℝ z.2 w
  congr 1
  rw [tangent_chart_apply]
  rw [←mfderiv_extChartAt_eq_tangentCoordChange hz]
  exact coordinate_metric_chart_pairing hz z.2 w

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_CoordinateGradient
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
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_gradient_of_hasMFDerivAt {a : M} (z : TangentBundle 𝓘(ℝ,E) M)
    (hz : z.1 ∈ (extChartAt 𝓘(ℝ,E) a).source) (f : M → ℝ) (τ : ℝ)
    (hM : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f z.1 (innerSL ℝ (τ • z.2))) :
    HasFDerivAt (fun q : E => f ((extChartAt 𝓘(ℝ,E) a).symm q))
      (τ • riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a z.1)
        ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) z).2))
      (extChartAt 𝓘(ℝ,E) a z.1) := by
  let c := extChartAt 𝓘(ℝ,E) a
  let F : E → ℝ := fun q => f (c.symm q)
  have hc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c.symm (c z.1) :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds (c.map_source hz))
  have hm : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f (c.symm (c z.1)) := by
    rw [c.left_inv hz]; exact hM.mdifferentiableAt
  have hF : DifferentiableAt ℝ F (c z.1) :=
    (hm.comp (c z.1) (hc.mdifferentiableAt (by simp))).differentiableAt
  have hz' : z.1 ∈ (chartAt E a).source := by simpa only [extChartAt_source] using hz
  have hDc := (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) hz').hasMFDerivAt
  have H := hF.hasFDerivAt.hasMFDerivAt.comp z.1 hDc
  have heq : f =ᶠ[𝓝 z.1] (fun y : M => F (c y)) := by
    filter_upwards [(isOpen_extChartAt_source a).mem_nhds hz] with y hy
    dsimp [F]; rw [c.left_inv hy]
  have H' := H.congr_of_eventuallyEq heq
  have hEq := H'.mfderiv.symm.trans hM.mfderiv
  have hsur : Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c z.1) := by
    obtain ⟨A,hA⟩ := isInvertible_mfderiv_extChartAt hz
    rw [←hA]
    exact A.surjective
  apply hF.hasFDerivAt.congr_fderiv
  ext u
  obtain ⟨v,rfl⟩ := hsur u
  have hh := congrArg (fun D : TangentSpace 𝓘(ℝ,E) z.1 →L[ℝ] ℝ => D v) hEq
  change fderiv ℝ F (c z.1) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c z.1 v) =
    τ * riemannianCoordinateMetric a (c z.1)
      ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) z).2)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c z.1 v)
  rw [tangent_chart_apply,←mfderiv_extChartAt_eq_tangentCoordChange hz]
  dsimp only [Prod.snd]
  erw [coordinate_metric_chart_pairing hz z.2 v]
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [innerSL_apply_apply,real_inner_smul_left]

end

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

lemma radial_calibration_length_lower_bound
    (g : E →L[ℝ] E →L[ℝ] ℝ) (hg : ∀ v : E, 0 ≤ g v v)
    (hsym : ∀ u v, g u v = g v u) {ζ : ℝ → E} {a b τ : ℝ}
    (hab : a ≤ b) (hτ : 0 ≤ τ) (hζ : ContDiffOn ℝ 1 ζ (Icc a b)) (hζa : ζ a = 0)
    (B : ℝ → ℝ) (hB : ∀ t ∈ Ioo a b, 0 ≤ B t)
    (hbound : ∀ t ∈ Ioo a b,
      |τ * g (ζ t) (deriv ζ t)| ≤ Real.sqrt (g (ζ t) (ζ t)) * B t) :
    ENNReal.ofReal (τ * Real.sqrt (g (ζ b) (ζ b))) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (B t) := by
  by_cases heq : a = b
  · subst b
    simp only [hζa,map_zero,Real.sqrt_zero,mul_zero,ENNReal.ofReal_zero,zero_le]
  have hεbound : ∀ ε : ℝ, 0 < ε →
      ‖τ * Real.sqrt (g (ζ b) (ζ b)+ε) - τ * Real.sqrt ε‖ₑ ≤
        ∫⁻ t in Icc a b, ENNReal.ofReal (B t) := by
    intro ε hε
    let F : ℝ → ℝ := fun t => τ * Real.sqrt (g (ζ t) (ζ t)+ε)
    have hF : ContDiffOn ℝ 1 F (Icc a b) :=
      contDiffOn_const.mul (((g.contDiff.comp_contDiffOn hζ).clm_apply hζ).add
        contDiffOn_const |>.sqrt (fun t _ => ne_of_gt (by change 0 < g (ζ t) (ζ t) + ε; linarith [hg (ζ t)])))
    have hlen := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hF hab
    have hFa : F a = τ * Real.sqrt ε := by simp only [F,hζa,map_zero,zero_add]
    rw [hFa] at hlen
    apply hlen.trans
    rw [←restrict_Ioo_eq_restrict_Icc]
    apply setLIntegral_mono' measurableSet_Ioo
    intro t ht
    have hζt : HasDerivAt ζ (deriv ζ t) t :=
      ((hζ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt one_ne_zero).hasDerivAt
    have hFt := hasDerivAt_regularized_metric_radius g hsym hζt
      (τ := τ) (ε := ε) (by linarith [hg (ζ t)])
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),hFt.deriv,
      Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    have hs : 0 < Real.sqrt (g (ζ t) (ζ t)+ε) := Real.sqrt_pos.2 (by linarith [hg (ζ t)])
    rw [abs_div,abs_of_pos hs,div_le_iff₀ hs]
    refine (hbound t ht).trans ?_
    rw [mul_comm (B t)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (hB t ht)
  have hc : Continuous (fun ε : ℝ =>
      ‖τ * Real.sqrt (g (ζ b) (ζ b)+ε) - τ * Real.sqrt ε‖ₑ) := by fun_prop
  have hlim : Tendsto (fun ε : ℝ =>
      ‖τ * Real.sqrt (g (ζ b) (ζ b)+ε) - τ * Real.sqrt ε‖ₑ) (𝓝[>] 0)
      (𝓝 (‖τ * Real.sqrt (g (ζ b) (ζ b)+(0:ℝ)) - τ * Real.sqrt (0:ℝ)‖ₑ)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hfinal := le_of_tendsto hlim (show ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ‖τ * Real.sqrt (g (ζ b) (ζ b)+ε) - τ * Real.sqrt ε‖ₑ ≤
        ∫⁻ t in Icc a b, ENNReal.ofReal (B t) from by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hεbound ε hε)
  simpa only [add_zero,Real.sqrt_zero,mul_zero,sub_zero,
    Real.enorm_of_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _))] using hfinal

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalGradient
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normal_action_hasFDerivAt
    (e : OpenPartialHomeomorph E E) {y : E} (hy : y ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm y)) (hi : DifferentiableAt ℝ e.symm y)
    (g₀ g₁ : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ u v, g₀ u v = g₀ v u)
    (V : E) (τ : ℝ)
    (hgauss : ∀ w, g₁ V ((fderiv ℝ e (e.symm y)) w) = τ * g₀ (e.symm y) w) :
    HasFDerivAt (fun z => (τ^2/2) * g₀ (e.symm z) (e.symm z))
      (τ • g₁ V) y := by
  have hg := (((g₀.hasFDerivAt.comp y hi.hasFDerivAt).clm_apply hi.hasFDerivAt).const_mul (τ^2/2))
  convert! hg using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  have hd := congrArg (fun L : E →L[ℝ] E => L w)
    (fderiv_partial_homeomorph_right_inverse e hy he hi)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hd
  have hG := hgauss ((fderiv ℝ e.symm y) w)
  rw [hd] at hG
  simp only [smul_apply,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,smul_eq_mul,Function.comp_apply]
  rw [hsym ((fderiv ℝ e.symm y) w) (e.symm y)]
  rw [hG]
  ring

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_NormalRigidity
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma normal_chart_radial_rigidity
    (e : OpenPartialHomeomorph E E)
    (hed : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (g₀ : E →L[ℝ] E →L[ℝ] ℝ) (hs₀ : ∀ u v, g₀ u v = g₀ v u)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (V : E → E) (τ k : ℝ)
    (hp : ∀ v ∈ e.source, ∀ w : E, w ≠ 0 → 0 < g (e v) w w)
    (hs : ∀ v ∈ e.source, ∀ u w, g (e v) u w = g (e v) w u)
    (henergy : ∀ v ∈ e.source, g (e v) (V v) (V v) = g₀ v v)
    (hgauss : ∀ v ∈ e.source, ∀ w,
      g (e v) (V v) (fderiv ℝ e v w) = τ*g₀ v w)
    (hradial : ∀ v ∈ e.source, fderiv ℝ e v v = τ • V v)
    {f : ℝ → E} {l r a : ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo l r))
    (ha : a ∈ Ioo l r) (himg : MapsTo f (Ioo l r) e.source)
    (hspeed : ∀ s ∈ Ioo l r,
      g (e (f s)) (deriv (e ∘ f) s) (deriv (e ∘ f) s) = k^2)
    (hdist : ∀ s ∈ Ioo l r, τ^2*g₀ (f s) (f s) = (s-a)^2*k^2) :
    ∀ s ∈ Ioo l r, f s = (s-a) • deriv f a := by
  apply linear_of_radial_derivative hf ha
  intro s hs'
  have hfs := himg hs'
  have hfD := (hf.contDiffAt (isOpen_Ioo.mem_nhds hs')).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heD := (hed.contDiffAt (e.open_source.mem_nhds hfs)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hiD := (hei.contDiffAt (e.open_target.mem_nhds (e.map_source hfs))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hqder : deriv (e ∘ f) s = fderiv ℝ e (f s) (deriv f s) :=
    (heD.hasFDerivAt.comp_hasDerivAt s hfD.hasDerivAt).deriv
  have heq : (fun t => τ^2*g₀ (f t) (f t)) =ᶠ[𝓝 s] (fun t => (t-a)^2*k^2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs'] with t ht
    exact hdist t ht
  have hpair := bilinear_metric_radial_derivative hs₀ hfD heq
  have hvelocity : (s-a) • deriv (e ∘ f) s = τ • V (f s) := by
    apply radial_velocity_of_metric_equalities (hp _ hfs) (hs _ hfs) (hspeed s hs')
    · rw [henergy _ hfs]; exact hdist s hs'
    · rw [hqder,hgauss _ hfs]
      nlinarith [hpair]
  have hL : (fderiv ℝ e.symm (e (f s))).comp (fderiv ℝ e (f s)) =
      ContinuousLinearMap.id ℝ E := by
    have H := fderiv_partial_homeomorph_right_inverse e.symm hfs
      (by simpa only [OpenPartialHomeomorph.symm_symm] using hiD) heD
    simpa only [OpenPartialHomeomorph.symm_symm,e.left_inv hfs] using H
  have hinj : Function.Injective (fderiv ℝ e (f s)) := by
    intro u v huv
    have H := congrArg (fderiv ℝ e.symm (e (f s))) huv
    simpa only [←ContinuousLinearMap.comp_apply,hL,ContinuousLinearMap.id_apply] using H
  apply hinj
  rw [map_smul,←hqder,hradial _ hfs]
  exact hvelocity
end

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

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma tangent_chart_scale (a z : TangentBundle 𝓘(ℝ,E) M) (c : ℝ) :
    extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a (tangentScale c z) =
      ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z).1,
        c • (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a z).2) := by
  simp only [tangent_chart_apply,tangentScale]
  congr 1
  exact (tangentCoordChange 𝓘(ℝ,E) z.1 a.1 z.1).map_smul c z.2

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_SprayDistanceBound
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

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma contracted_minimizer_mem_injectivityDomain {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ minimizingVectors x)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : t • p ∈ injectivityDomain x := by
  refine ⟨t⁻¹,(one_lt_inv₀ ht0).mpr ht1,?_⟩
  rw [smul_smul,inv_mul_cancel₀ ht0.ne',one_smul]
  rw [hp,norm_smul,Real.norm_eq_abs,abs_of_pos ht0,←mul_assoc,inv_mul_cancel₀ ht0.ne',one_mul]

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Geodesics_MetricSegments
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

namespace WeakMTWTransport
variable {M : Type*} [MetricSpace M]

lemma isMetricChain_initial (x y : M) :
    IsMetricChain x y {(0,x),(dist x y,y)} := by
  refine ⟨by simp,by simp,?_,?_⟩
  · intro u hu
    rcases hu with hu|hu
    · subst u; exact ⟨⟨le_rfl,dist_nonneg⟩,mem_univ _⟩
    · rcases hu with rfl
      exact ⟨⟨dist_nonneg,le_rfl⟩,mem_univ _⟩
  · intro u hu v hv
    rcases hu with rfl|hu <;> rcases hv with rfl|hv
    · simp
    · rcases hv with rfl
      simp [abs_of_nonneg dist_nonneg]
    · rcases hu with rfl
      simp [dist_comm,abs_of_nonneg dist_nonneg]
    · rcases hu with rfl; rcases hv with rfl
      simp

lemma exists_maximal_metricChain (x y : M) :
    ∃ A : Set (ℝ × M), Maximal (IsMetricChain x y) A := by
  let S : Set (Set (ℝ × M)) := {A | IsMetricChain x y A}
  have hchains : ∀ c ⊆ S, IsChain (fun a b => a ⊆ b) c → c.Nonempty →
      ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain hne
    obtain ⟨B,hB⟩ := hne
    refine ⟨⋃₀ c,?_,fun s hs => subset_sUnion_of_mem hs⟩
    refine ⟨mem_sUnion.mpr ⟨B,hB,(hc hB).1⟩,
      mem_sUnion.mpr ⟨B,hB,(hc hB).2.1⟩,?_,?_⟩
    · intro u hu
      obtain ⟨C,hC,huC⟩ := mem_sUnion.mp hu
      exact (hc hC).2.2.1 huC
    · intro u hu v hv
      obtain ⟨C,hC,huC⟩ := mem_sUnion.mp hu
      obtain ⟨D,hD,hvD⟩ := mem_sUnion.mp hv
      obtain ⟨F,hF,hCF,hDF⟩ := hchain.directedOn C hC D hD
      exact (hc hF).2.2.2 u (hCF huC) v (hDF hvD)
  obtain ⟨A,_,hA⟩ := zorn_subset_nonempty S hchains
    {(0,x),(dist x y,y)} (isMetricChain_initial x y)
  exact ⟨A,hA⟩

lemma insert_midpoint_metricChain {x y : M} {A : Set (ℝ × M)}
    (hA : IsMetricChain x y A) {u v : ℝ × M} (hu : u ∈ A) (hv : v ∈ A)
    (huv : u.1 < v.1)
    (hgap : ∀ w ∈ A, w.1 ≤ u.1 ∨ v.1 ≤ w.1) {z : M}
    (huz : dist u.2 z = dist u.2 v.2/2)
    (hzv : dist z v.2 = dist u.2 v.2/2) :
    IsMetricChain x y (insert ((u.1+v.1)/2,z) A) := by
  let m : ℝ := (u.1+v.1)/2
  have hadist : dist u.2 v.2 = v.1-u.1 := by
    rw [hA.2.2.2 u hu v hv,abs_of_neg (sub_neg.mpr huv)]
    ring
  rw [hadist] at huz hzv
  have hwm (w : ℝ × M) (hw : w ∈ A) : dist w.2 z = |w.1-m| := by
    have hwu := hA.2.2.2 w hw u hu
    have hwv := hA.2.2.2 w hw v hv
    rcases hgap w hw with hleft|hright
    · have habs1 : |w.1-u.1| = u.1-w.1 := by rw [abs_of_nonpos (sub_nonpos.mpr hleft)]; ring
      have habs2 : |w.1-v.1| = v.1-w.1 := by rw [abs_of_nonpos (by linarith)]; ring
      rw [habs1] at hwu
      rw [habs2] at hwv
      have hwmle : w.1 ≤ m := by dsimp [m] <;> linarith
      rw [abs_of_nonpos (sub_nonpos.mpr hwmle)]
      have hubound := dist_triangle w.2 u.2 z
      have hlbound := dist_triangle w.2 z v.2
      dsimp [m]
      linarith
    · have habs1 : |w.1-u.1| = w.1-u.1 := abs_of_nonneg (by linarith)
      have habs2 : |w.1-v.1| = w.1-v.1 := abs_of_nonneg (sub_nonneg.mpr hright)
      rw [habs1] at hwu
      rw [habs2] at hwv
      have hwmle : m ≤ w.1 := by dsimp [m] <;> linarith
      rw [abs_of_nonneg (sub_nonneg.mpr hwmle)]
      have hubound := dist_triangle w.2 v.2 z
      have hlbound := dist_triangle w.2 z u.2
      rw [dist_comm v.2 z] at hubound
      rw [dist_comm z u.2] at hlbound
      dsimp [m]
      linarith
  refine ⟨mem_insert_of_mem _ hA.1,mem_insert_of_mem _ hA.2.1,?_,?_⟩
  · intro w hw
    rcases hw with rfl|hw
    · have hux := (hA.2.2.1 hu).1
      have hvx := (hA.2.2.1 hv).1
      exact ⟨⟨by dsimp <;> linarith [hux.1,hvx.1],by dsimp <;> linarith [hux.2,hvx.2]⟩,mem_univ _⟩
    · exact hA.2.2.1 hw
  · intro w hw q hq
    rcases hw with rfl|hw <;> rcases hq with rfl|hq
    · simp
    · simpa only [dist_comm z q.2,abs_sub_comm] using hwm q hq
    · exact hwm w hw
    · exact hA.2.2.2 w hw q hq

lemma maximal_metricChain_full_projection [CompactSpace M] (x y : M)
    (hmid : ∀ u v : M, ∃ z, dist u z = dist u v/2 ∧ dist z v = dist u v/2)
    {A : Set (ℝ × M)} (hA : Maximal (IsMetricChain x y) A) :
    Prod.fst '' A = Icc 0 (dist x y) := by
  have hAc : IsClosed A := by
    have heq : closure A = A := subset_antisymm (hA.2 hA.1.closure subset_closure) subset_closure
    rw [← heq]
    exact isClosed_closure
  have hAk : IsCompact A := (isCompact_Icc.prod isCompact_univ).of_isClosed_subset hAc hA.1.2.2.1
  let K : Set ℝ := Prod.fst '' A
  have hK : IsCompact K := hAk.image continuous_fst
  apply Subset.antisymm
  · rintro t ⟨w,hw,rfl⟩
    exact (hA.1.2.2.1 hw).1
  · intro t ht
    by_contra htn
    have hK0 : 0 ∈ K := ⟨(0,x),hA.1.1,rfl⟩
    have hKL : dist x y ∈ K := ⟨(dist x y,y),hA.1.2.1,rfl⟩
    obtain ⟨a,ha,hamax⟩ := (hK.inter_right isClosed_Iic).exists_isMaxOn
      ⟨0,hK0,ht.1⟩ continuousOn_id
    obtain ⟨b,hb,hbmin⟩ := (hK.inter_right isClosed_Ici).exists_isMinOn
      ⟨dist x y,hKL,ht.2⟩ continuousOn_id
    have hat : a < t := lt_of_le_of_ne ha.2 (by intro heq; exact htn (heq ▸ ha.1))
    have htb : t < b := lt_of_le_of_ne hb.2 (by intro heq; exact htn (heq.symm ▸ hb.1))
    obtain ⟨u,hu,hua⟩ := ha.1
    obtain ⟨v,hv,hvb⟩ := hb.1
    have huv : u.1 < v.1 := by rw [hua,hvb]; exact hat.trans htb
    have hgap : ∀ w ∈ A, w.1 ≤ u.1 ∨ v.1 ≤ w.1 := by
      intro w hw
      have hwK : w.1 ∈ K := ⟨w,hw,rfl⟩
      by_cases hwt : w.1 ≤ t
      · exact Or.inl (by rw [hua]; exact hamax ⟨hwK,hwt⟩)
      · exact Or.inr (by rw [hvb]; exact hbmin ⟨hwK,(lt_of_not_ge hwt).le⟩)
    obtain ⟨z,huz,hzv⟩ := hmid u.2 v.2
    have hi := insert_midpoint_metricChain hA.1 hu hv huv hgap huz hzv
    have himem : ((u.1+v.1)/2,z) ∈ A := hA.2 hi (subset_insert _ _) (mem_insert _ _)
    rcases hgap _ himem with hl|hr
    · dsimp at hl <;> linarith
    · dsimp at hr <;> linarith

lemma exists_metric_segment [CompactSpace M] (x y : M)
    (hmid : ∀ u v : M, ∃ z, dist u z = dist u v/2 ∧ dist z v = dist u v/2) :
    ∃ γ : Icc (0:ℝ) (dist x y) → M, Isometry γ ∧
      γ ⟨0,⟨le_rfl,dist_nonneg⟩⟩ = x ∧
      γ ⟨dist x y,⟨dist_nonneg,le_rfl⟩⟩ = y := by
  obtain ⟨A,hA⟩ := exists_maximal_metricChain x y
  have hfull := maximal_metricChain_full_projection x y hmid hA
  have hex (t : Icc (0:ℝ) (dist x y)) : ∃ z : M, (t.1,z) ∈ A := by
    have hm : t.1 ∈ Prod.fst '' A := by rw [hfull]; exact t.2
    obtain ⟨w,hw,hwf⟩ := hm
    exact ⟨w.2,by simpa only [← hwf] using hw⟩
  choose γ hγ using hex
  refine ⟨γ,?_,?_,?_⟩
  · apply Isometry.of_dist_eq
    intro s t
    simpa only [Subtype.dist_eq,Real.dist_eq] using hA.1.2.2.2 (s.1,γ s) (hγ s) (t.1,γ t) (hγ t)
  · have hh := hA.1.2.2.2 _ (hγ ⟨0,⟨le_rfl,dist_nonneg⟩⟩) _ hA.1.1
    exact dist_eq_zero.mp (by simpa only [sub_self,abs_zero] using hh)
  · have hh := hA.1.2.2.2 _ (hγ ⟨dist x y,⟨dist_nonneg,le_rfl⟩⟩) _ hA.1.2.1
    exact dist_eq_zero.mp (by simpa only [sub_self,abs_zero] using hh)

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Regularity_RiemannianMetricSegment
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

namespace WeakMTWTransport
open Set Manifold Bundle
open scoped ContDiff

lemma riemannian_exists_metric_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (x y : M) :
    ∃ γ : Icc (0:ℝ) (dist x y) → M, Isometry γ ∧
      γ ⟨0,⟨le_rfl,dist_nonneg⟩⟩ = x ∧
      γ ⟨dist x y,⟨dist_nonneg,le_rfl⟩⟩ = y :=
  exists_metric_segment x y (riemannian_exists_midpoint (I := I))
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

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma contMDiff_tangentScale :
    ContMDiff (𝓘(ℝ,ℝ).prod (𝓘(ℝ,E).prod 𝓘(ℝ,E))) (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞
      (fun p : ℝ × TangentBundle 𝓘(ℝ,E) M => tangentScale p.1 p.2) := by
  intro p
  have hpr : ContMDiffAt (𝓘(ℝ,ℝ).prod (𝓘(ℝ,E).prod 𝓘(ℝ,E)))
      (𝓘(ℝ,E).prod 𝓘(ℝ,E)) ∞ (fun q : ℝ × TangentBundle 𝓘(ℝ,E) M => q.2) p :=
    contMDiffAt_snd
  rw [Bundle.contMDiffAt_totalSpace] at hpr ⊢
  refine ⟨hpr.1,?_⟩
  let e := trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) p.2.1
  have hnear : ∀ᶠ q : ℝ × TangentBundle 𝓘(ℝ,E) M in 𝓝 p, q.2.1 ∈ e.baseSet :=
    hpr.1.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ p.2.1))
  apply (contMDiffAt_fst.smul hpr.2).congr_of_eventuallyEq
  filter_upwards [hnear] with q hq
  exact (e.linear ℝ hq).map_smul q.1 q.2.2

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

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [CompactSpace M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma tangentScale_injective {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (tangentScale (M := M) (E := E) c) := by
  have hinv : Function.LeftInverse (tangentScale (M := M) (E := E) c⁻¹)
      (tangentScale c) := by
    rintro ⟨base,velocity⟩
    dsimp only [tangentScale]
    congr 1
    exact inv_smul_smul₀ hc velocity
  exact hinv.injective

end

end WeakMTWTransport

end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Coordinates_SplitAction
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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def splitNormalAction (x : M) (t : ℝ) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost (riemannianExp x q.1) (riemannianExp x (t • q.2))/t +
    cost (riemannianExp x (t • q.2)) (riemannianExp x p)/(1-t)

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

def gapSection (u v : M → ℝ) (x : M) (r : ℝ) : Set M :=
  {y | contactGap u v x y ≤ r}

end WeakMTWTransport
end

end OAI
end

section
-- module Solutions.OAIQ232_BH.BiholderTransport_Volume_MeasureContacts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology BoundedContinuousFunction

namespace WeakMTWTransport

section MeasureContacts
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

def contactImage (u v : M → ℝ) (A : Set M) : Set M :=
  {y | ∃ x ∈ A, contactGap u v x y = 0}

end MeasureContacts

end WeakMTWTransport
end
end
end

end OAI
end


