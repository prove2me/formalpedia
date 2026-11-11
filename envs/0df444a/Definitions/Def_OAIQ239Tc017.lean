-- Prove2me | Definitions.Def_OAIQ239Tc017
-- name    : OAIQ239Tc017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:36:16.033734+00:00
-- url     : https://prove2.me/theorems/e89b8423-ee0d-4ed1-ae8b-46c8b9549d14
-- title:
--   Definitions bundle OAIQ239Tc017 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 63 declarations of OpenAI's Lean: 17 definitions and 46 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricChart.data`, `OAI.TamingCompatibility.GeometricChart.deltaB`, `OAI.TamingCompatibility.GeometricChart.deltaComplexB`, `OAI.TamingCompatibility.GeometricChart.hermitianCenterExtension`, `OAI.TamingCompatibility.GeometricChart.localDelta`, `OAI.TamingCompatibility.GeometricChart.normalOperator`, `OAI.TamingCompatibility.GeometricChart.patchA`, `OAI.TamingCompatibility.GeometricChart.patchB`, `OAI.TamingCompatibility.GeometricChart.radialPairSource`, `OAI.TamingCompatibility.GeometricChart.radialScalarSource`, `OAI.TamingCompatibility.GeometricChart.radialSourceExtension`, `OAI.TamingCompatibility.GeometricChart.rawPair`, `OAI.TamingCompatibility.GeometricChart.realPairSchwartz`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.FrameSpace`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedAddCommGroup`, `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.regularMetrics`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_ChartEnergyIntegral`, `TamingCompatibility_Charts_ChartMetricBounds`, `TamingCompatibility_Charts_ChartMetricComparison`, `TamingCompatibility_Charts_ChartScalarBound`, `TamingCompatibility_Charts_ChartUnitaryData`, `TamingCompatibility_Charts_GeometricCutoff`, `TamingCompatibility_DifferentialForms_AntiEnergy`, `TamingCompatibility_DifferentialForms_ClosedLiftData`, `TamingCompatibility_DifferentialForms_ConstantGeometricEnergy`, `TamingCompatibility_DifferentialForms_Dpos`, `TamingCompatibility_DifferentialForms_FirstMatrixJoint`, `TamingCompatibility_DifferentialForms_GeometricFrameTest`, `TamingCompatibility_DifferentialForms_HermitianGeometricCenter`, `TamingCompatibility_DifferentialForms_RadialGeometricCoefficient`, `TamingCompatibility_DifferentialForms_RadialScalarOff`, `TamingCompatibility_DifferentialForms_RawJetEstimate`, `TamingCompatibility_DifferentialForms_RawTest`, `TamingCompatibility_DifferentialForms_TestLinear`, `TamingCompatibility_Elliptic_DirectionH1`, `TamingCompatibility_Elliptic_LocalMatrixGarding`, `TamingCompatibility_Elliptic_MatrixGarding`, `TamingCompatibility_Elliptic_UnitaryLocalGarding`, `TamingCompatibility_Functional_NormalMap`, `TamingCompatibility_Functional_NormalPatch`, `TamingCompatibility_Functional_RawNormal`, `TamingCompatibility_Hodge_HodgeCompactExtension`, `TamingCompatibility_Hodge_HodgeFiniteFrameResolution`, `TamingCompatibility_Hodge_HodgeParametrixWeakEquation`.
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc014` and `OAIQ239Tc015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc021`, `OAIQ239Tc022`, `OAIQ239Tc023` and `OAIQ239Tc024`; the statements `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedFirst_center`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_unitary` and `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity_pos`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.gaugedFirst_center`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDensity_smooth`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_unitary` and `OAI.TamingCompatibility.GeometricHilbert.NormalMetricCalculus.volumeDensity_pos`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc014
import Definitions.Def_OAIQ239Tc015

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ConstantGeometricEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy MetricForms ExteriorForms MetricHodge AntiInvariantFrame
open MatrixEnergy

lemma frozen_geometric_energy (g : MetricModel.Metric V)
    (b : Module.Basis (Fin 4) ℝ V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (J : V →L[ℝ] V) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
    (F : MetricForms.Form V 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (A B : S) :
    (∫ x, gradientEnergy A B x) ≤
      (DirectionalEnergy.coordinateConstant b * evaluationConstant b) *
      ∫ x, ‖constantSystem (principal g F (realPart g b) (imagPart g b)) A B x‖^2 := by
  let c := principal g F (realPart g b) (imagPart g b)
  have he (x : V) : oneVector (starThree g F
      (wedgeOne (fderiv ℝ A x) (realPart g b) +
        wedgeOne (fderiv ℝ B x) (imagPart g b))) = constantSystem c A B x := by
    simpa only [constantSystem,coordinateDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv]
      using principal_covectors g F (realPart g b) (imagPart g b) (fderiv ℝ A x) (fderiv ℝ B x)
  have hp (x : V) : ‖DirectionalEnergy.codifferential b A B x‖^2 ≤
      evaluationConstant b * ‖constantSystem c A B x‖^2 := by
    rw [← oneCoordinates_star_covectors g b hb J h0 h1 h2 h3 F hF A B x]
    simpa only [he] using oneCoordinates_bound b (starThree g F
      (wedgeOne (fderiv ℝ A x) (realPart g b) + wedgeOne (fderiv ℝ B x) (imagPart g b)))
  have hI := integral_mono (DirectionalEnergy.codifferential_integrable_sq b A B)
    ((constantSystem_integrable c A B).const_mul (evaluationConstant b)) hp
  rw [integral_const_mul,DirectionalEnergy.codifferential_energy] at hI
  have hG := integral_mono (gradientEnergy_integrable A B)
    ((DirectionalEnergy.gradientEnergy_integrable b A B).const_mul
      (DirectionalEnergy.coordinateConstant b)) (DirectionalEnergy.gradient_control b A B)
  rw [integral_const_mul] at hG
  calc
    _ ≤ DirectionalEnergy.coordinateConstant b * (∫ x, DirectionalEnergy.gradientEnergy b A B x) := hG
    _ ≤ DirectionalEnergy.coordinateConstant b *
        (evaluationConstant b * (∫ x, ‖constantSystem c A B x‖^2)) :=
      mul_le_mul_of_nonneg_left hI (DirectionalEnergy.coordinateConstant_pos b).le
    _ = _ := by rw [mul_assoc]

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_MatrixGarding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy

theorem garding (c : Fin 4 → Pair →L[ℝ] V) {K δ C : ℝ} (hK : 0 < K)
    (hsmall : 16*K*δ^2 ≤ 1/2)
    (henergy : ∀ A B : S, (∫ x, gradientEnergy A B x) ≤
      K * (∫ x, ‖constantSystem c A B x‖^2))
    (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    (hac : ∀ i, Continuous (a i)) (hbc : Continuous b)
    (ha : ∀ x i, ‖a i x-c i‖ ≤ δ) (hb : ∀ x, ‖b x‖ ≤ C) (A B : S) :
    (∫ x, gradientEnergy A B x) ≤ 4*K * (∫ x, ‖system a b A B x‖^2) +
      8*K*C^2 * (∫ x, (A x)^2+(B x)^2) := by
  have ha' (x : V) (i : Fin 4) : ‖a i x‖ ≤ δ + ∑ j, ‖c j‖ := by
    calc
      ‖a i x‖ ≤ ‖a i x-c i‖ + ‖c i‖ := norm_le_norm_sub_add _ _
      _ ≤ δ + ∑ j, ‖c j‖ := add_le_add (ha x i)
        (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  have hS := system_integrable a b A B hac hbc ha' hb
  have hG := gradientEnergy_integrable A B
  have hF := (schwartz_sq_integrable A).add (schwartz_sq_integrable B)
  have hcomp := integral_mono (constantSystem_integrable c A B)
    (((hS.const_mul 2).add (hG.const_mul (16*δ^2))).add (hF.const_mul (4*C^2)))
    (fun x => comparison_pointwise c a b A B x (ha x) (hb x))
  dsimp only [Pi.add_apply] at hcomp
  erw [integral_add ((hS.const_mul 2).add (hG.const_mul (16*δ^2))) (hF.const_mul (4*C^2)),
    integral_add (hS.const_mul 2) (hG.const_mul (16*δ^2)),
    integral_const_mul,integral_const_mul,integral_const_mul] at hcomp
  simp only [Pi.add_apply] at hcomp
  have hcompK := mul_le_mul_of_nonneg_left hcomp hK.le
  have hcoerce := henergy A B
  have hG0 : 0 ≤ ∫ x, gradientEnergy A B x := integral_nonneg fun x =>
    Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsmallG := mul_le_mul_of_nonneg_right hsmall hG0
  nlinarith

end TamingCompatibility.MatrixEnergy

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_LocalMatrixGarding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy
open Filter Topology

theorem local_garding (c : Fin 4 → Pair →L[ℝ] V) {K : ℝ} (hK : 0 < K)
    (henergy : ∀ A B : S, (∫ x, gradientEnergy A B x) ≤
      K * (∫ x, ‖constantSystem c A B x‖^2))
    {U : Set V} (hU : IsOpen U) {x₀ : V} (hx₀ : x₀ ∈ U)
    (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    (ha : ∀ i, ContinuousOn (a i) U) (hb : ContinuousOn b U)
    (ha₀ : ∀ i, a i x₀ = c i) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ Metric.closedBall x₀ (2*r) ⊆ U ∧
      ∀ A B : S, tsupport A ⊆ Metric.closedBall x₀ r →
        tsupport B ⊆ Metric.closedBall x₀ r →
        (∫ x, gradientEnergy A B x) ≤ 4*K * (∫ x, ‖system a b A B x‖^2) +
          8*K*C^2 * (∫ x, (A x)^2+(B x)^2) := by
  obtain ⟨δ,hδ,hsmall⟩ := exists_small_error hK
  let C := ‖b x₀‖ + 1
  have hC : 0 < C := by dsimp only [C] <;> positivity
  have hae : ∀ᶠ x in 𝓝 x₀, ∀ i, ‖a i x-c i‖ ≤ δ := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun x => ‖a i x-c i‖) x₀ :=
      (((ha i).continuousAt (hU.mem_nhds hx₀)).sub continuousAt_const).norm
    have hz : ‖a i x₀-c i‖ < δ := by simpa only [ha₀ i,sub_self,norm_zero] using hδ
    exact (hc.eventually (gt_mem_nhds hz)).mono (fun _ h => h.le)
  have hbe : ∀ᶠ x in 𝓝 x₀, ‖b x‖ ≤ C := by
    have hz : ‖b x₀‖ < C := by dsimp only [C] <;> linarith
    exact (((hb.continuousAt (hU.mem_nhds hx₀)).norm).eventually
      (gt_mem_nhds hz)).mono (fun _ h => h.le)
  have he : ∀ᶠ x in 𝓝 x₀, x ∈ U ∧ (∀ i, ‖a i x-c i‖ ≤ δ) ∧ ‖b x‖ ≤ C :=
    (show ∀ᶠ x in 𝓝 x₀, x ∈ U from hU.mem_nhds hx₀).and (hae.and hbe)
  obtain ⟨ε,hε,hεgood⟩ := Metric.mem_nhds_iff.mp he
  let φ : ContDiffBump x₀ := {
    rIn := ε/4
    rOut := ε/2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hgood (x : V) (hx : x ∈ tsupport φ) :
      x ∈ U ∧ (∀ i, ‖a i x-c i‖ ≤ δ) ∧ ‖b x‖ ≤ C := by
    rw [φ.tsupport_eq] at hx
    apply hεgood
    have hh := Metric.mem_closedBall.mp hx
    change dist x x₀ ≤ ε/2 at hh
    exact Metric.mem_ball.mpr (by linarith)
  have hφU : tsupport φ ⊆ U := fun x hx => (hgood x hx).1
  have ha' := patchPrincipal_continuous hU c a ha φ hφU
  have hb' : Continuous (patchLower b φ) := continuous_cutoff hU hb φ hφU
  have hap (x : V) (i : Fin 4) : ‖patchPrincipal c a φ i x-c i‖ ≤ δ :=
    patchPrincipal_bound c a hδ.le (fun x hx => (hgood x hx).2.1) φ (Set.Subset.refl _) x i
  have hbp (x : V) : ‖patchLower b φ x‖ ≤ C :=
    cutoff_bound hC.le (fun x hx => (hgood x hx).2.2) φ (Set.Subset.refl _) x
  refine ⟨ε/4,C,by positivity,hC,?_,?_⟩
  · intro x hx
    apply hφU
    rw [φ.tsupport_eq]
    simpa only [φ,show (2:ℝ)*(ε/4) = ε/2 by ring] using hx
  · intro A B hA hB
    have h := garding c hK hsmall henergy (patchPrincipal c a φ) (patchLower b φ)
      ha' hb' hap hbp A B
    simpa only [system_patch_eq c a b φ A B hA hB] using h

end TamingCompatibility.MatrixEnergy

end
end

section

noncomputable section
open _root_.MeasureTheory Filter Topology
open scoped ContDiff SchwartzMap
namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy MetricModel MetricForms MetricHodge ExteriorForms AntiInvariantFrame

theorem geometric_local_garding {U : Set V} (hU : IsOpen U) {x₀ : V} (hx₀ : x₀ ∈ U)
    (g : V → Metric V) (F ψ χ : V → MetricForms.Form V 2)
    (hstar : ContDiffOn ℝ ∞ (fun x => starThreeCLM (g x) (F x)) U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hχ : ContDiffOn ℝ ∞ χ U)
    (b : Module.Basis (Fin 4) ℝ V)
    (hb : ∀ i j, (g x₀).bilinear (b i) (b j) = if i = j then 1 else 0)
    (J : V →L[ℝ] V) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
    (hF : ∀ u v, F x₀ ![u,v] = (g x₀).bilinear (J u) v)
    (hψ₀ : ψ x₀ = realPart (g x₀) b) (hχ₀ : χ x₀ = imagPart (g x₀) b) :
    ∃ r K C : ℝ, 0 < r ∧ 0 < K ∧ 0 < C ∧ Metric.closedBall x₀ (2*r) ⊆ U ∧
      ∀ A B : S, tsupport A ⊆ Metric.closedBall x₀ r →
        tsupport B ⊆ Metric.closedBall x₀ r →
        (∫ x, gradientEnergy A B x) ≤ K * (∫ x,
          ‖oneVector (starThree (g x) (F x)
            (extDeriv (fun y => A y • ψ y + B y • χ y) x))‖^2) +
          C * (∫ x, (A x)^2+(B x)^2) := by
  let K := DirectionalEnergy.coordinateConstant b * evaluationConstant b
  have hK : 0 < K := mul_pos (DirectionalEnergy.coordinateConstant_pos b)
    (evaluationConstant_pos b)
  let c := principal (g x₀) (F x₀) (realPart (g x₀) b) (imagPart (g x₀) b)
  have henergy := frozen_geometric_energy (g x₀) b hb J h0 h1 h2 h3 (F x₀) hF
  obtain ⟨r,C,hr,hC,hrU,he⟩ := MatrixEnergy.local_garding c hK henergy hU hx₀
    (fun i x => principal (g x) (F x) (ψ x) (χ x) i)
    (fun x => lower (g x) (F x) ψ χ x)
    (fun i => (principal_smooth hstar hψ hχ i).continuousOn)
    (lower_smooth hU hstar hψ hχ).continuousOn (fun _ => by simp only [hψ₀,hχ₀,c])
  refine ⟨r,4*K,8*K*C^2,hr,by positivity,by positivity,hrU,?_⟩
  intro A B hA hB
  have hrU' : Metric.closedBall x₀ r ⊆ U :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hrU
  simpa only [supported_operator_eq hU g F ψ χ hψ hχ A B (hA.trans hrU') (hB.trans hrU')]
    using he A B hA hB

end TamingCompatibility.LocalMatrixOperator

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_UnitaryLocalGarding
attribute [-simp] _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped ContDiff SchwartzMap

namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy MetricModel MetricForms MetricHodge ExteriorForms AntiInvariantFrame
open _root_.MeasureTheory

theorem exists_unitary_local_garding {U : Set V} (hU : IsOpen U) {x₀ : V} (hx₀ : x₀ ∈ U)
    (g : V → Metric V) (J : V → V →L[ℝ] V) (F : V → MetricForms.Form V 2)
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U) (hJ : ContDiffOn ℝ ∞ J U)
    (hJs : ∀ x ∈ U, ∀ u, J x (J x u) = -u)
    (hgJ : ∀ x ∈ U, ∀ u v, (g x).bilinear (J x u) (J x v) = (g x).bilinear u v)
    (hFs : ContDiffOn ℝ ∞ F U)
    (hF : ∀ x ∈ U, ∀ u v, F x ![u,v] = (g x).bilinear (J x u) v) :
    ∃ r K C : ℝ, 0 < r ∧ 0 < K ∧ 0 < C ∧ Metric.closedBall x₀ (2*r) ⊆ U ∧
      ∃ W : Set V, IsOpen W ∧ Metric.closedBall x₀ (2*r) ⊆ W ∧ W ⊆ U ∧
        ∃ b : Fin 4 → V → V,
          (∀ i, ContDiffOn ℝ ∞ (b i) W) ∧
          (∀ x ∈ W, ∀ i j, (g x).bilinear (b i x) (b j x) = if i = j then 1 else 0) ∧
          (∀ x ∈ W, J x (b 0 x) = b 1 x ∧ J x (b 1 x) = -b 0 x ∧
            J x (b 2 x) = b 3 x ∧ J x (b 3 x) = -b 2 x) ∧
          ∀ A B : S, tsupport A ⊆ Metric.closedBall x₀ r →
            tsupport B ⊆ Metric.closedBall x₀ r →
            (∫ x, gradientEnergy A B x) ≤ K * (∫ x,
              ‖oneVector (starThree (g x) (F x)
                (extDeriv (fun y => A y • realPart (g y) (fun i => b i y) +
                  B y • imagPart (g y) (fun i => b i y)) x))‖^2) +
                C * (∫ x, (A x)^2+(B x)^2) := by
  obtain ⟨W,hW,hxW,hWU,b,hbs,hb,hJb,B₀,hB₀⟩ :=
    SmoothMetric.exists_unitaryFrame_near g J (by simp [V]) hU hg hJ hJs hgJ hx₀
  have hψ := realPart_smooth (hg.mono hWU) hbs
  have hχ := imagPart_smooth (hg.mono hWU) hbs
  have he : (fun i => b i x₀) = B₀ := funext hB₀
  obtain ⟨h0,h1,h2,h3⟩ := hJb x₀ hxW
  have hstar := SmoothHodge.starThreeCLM_contDiffOn g J (by simp [V]) hW
    (hg.mono hWU) (hJ.mono hWU) (fun x hx => hJs x (hWU hx))
    (fun x hx => hgJ x (hWU hx)) (hFs.mono hWU)
  obtain ⟨r,K,C,hr,hK,hC,hrW,hgard⟩ := geometric_local_garding hW hxW g F
    (fun x => realPart (g x) (fun i => b i x))
    (fun x => imagPart (g x) (fun i => b i x)) hstar hψ hχ B₀
    (fun i j => by simpa only [hB₀] using hb x₀ hxW i j) (J x₀)
    (by simpa only [hB₀] using h0) (by simpa only [hB₀] using h1)
    (by simpa only [hB₀] using h2) (by simpa only [hB₀] using h3)
    (hF x₀ hx₀) (by rw [he]) (by rw [he])
  exact ⟨r,K,C,hr,hK,hC,hrW.trans hWU,W,hW,hrW,hWU,b,hbs,hb,hJb,hgard⟩
end TamingCompatibility.LocalMatrixOperator

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartUnitaryData
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
open scoped Manifold ContDiff SchwartzMap
namespace TamingCompatibility.GeometricChart
open ManifoldHodge ManifoldVolume ManifoldForms
open MetricModel MetricForms MetricHodge AntiInvariantFrame EuclideanEnergy LocalMatrixOperator
open _root_.MeasureTheory Set
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

theorem data_nonempty (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (p : X) : Nonempty (Data J α ht p) := by
  obtain ⟨r,K,C,hr,hK,hC,_,W,hW,hrW,hWU,b,hbs,hb,hJb,hgard⟩ :=
    exists_unitary_local_garding (isOpen_extChartAt_target p)
      (mem_extChartAt_target p) (coordinateMetric J α ht p) (coordinateJ J p)
      (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p).symm)
      (coordinateMetric_smooth J α hs ht p) (coordinateJ_smooth J p)
      (fun x hx => coordinateJ_square J p hx)
      (fun x hx => coordinateMetric_hermitian J α ht p hx)
      (smooth_chart _ (hs.invariantPart J) p)
      (fun x hx => ManifoldTop.coordinateFundamental J α ht p hx)
  exact ⟨⟨r,K,C,hr,hK,hC,W,hW,hrW,hWU,b,hbs,hb,hJb,hgard⟩⟩

def data (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (p : X) : Data J α ht p := Classical.choice (data_nonempty J α hs ht p)

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartEnergyIntegral
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open Bundle ManifoldForms ManifoldLocalization ManifoldVolume ManifoldHodge
open Set _root_.MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

lemma pairing_chart (p : X) {k : ℕ} (hk : k=1 ∨ k=2) (a b : ManifoldForms.Form X k)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    MetricForms.pairing (coordinateMetric J α ht p z)
      (ManifoldForms.pullback a (extChartAt Model p).symm z)
      (ManifoldForms.pullback b (extChartAt Model p).symm z) =
      GeometricAdjoint.pairing J α ht a b ((extChartAt Model p).symm z) := by
  let L : Space ≃L[ℝ] Space := inverseChartEquiv p z hz
  have hL : L.toContinuousLinearMap = mfderiv Model Model (extChartAt Model p).symm z :=
    inverseChartEquiv_coe p z hz
  rcases hk with rfl | rfl
  · have h := MetricForms.pairing_one_comp (E := Space) (D := Space)
      (coordinateMetric J α ht p z) (GeometricAdjoint.pointMetric J α ht ((extChartAt Model p).symm z))
      L (coordinateMetric_pullback J α ht p hz) (by simp [Space])
      (a ((extChartAt Model p).symm z)) (b ((extChartAt Model p).symm z))
    rw [hL] at h
    exact h
  · have h := MetricForms.pairing_two_comp (E := Space) (D := Space)
      (coordinateMetric J α ht p z) (GeometricAdjoint.pointMetric J α ht ((extChartAt Model p).symm z))
      L (coordinateMetric_pullback J α ht p hz) (by simp [Space])
      (a ((extChartAt Model p).symm z)) (b ((extChartAt Model p).symm z))
    rw [hL] at h
    exact h

lemma localizedPairing_eq_coordinateIntegrand (p : A.centers) {k : ℕ} (hk : k=1 ∨ k=2)
    (a : ManifoldForms.Form X k) :
    (fun z => chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
      (localizedFunction A p a z) (localizedFunction A p a z)) =
    coordinateIntegrand J α p.val (fun x => (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a a x) := by
  funext z
  by_cases hz : z ∈ (extChartAt Model p.val).target
  · unfold localizedFunction coordinateIntegrand
    rw [indicator_of_mem hz,indicator_of_mem hz,MetricForms.pairing_smul_left,
      MetricForms.pairing_smul_right,pairing_chart J α ht p.val hk a a hz]
    ring
  · unfold localizedFunction coordinateIntegrand
    rw [indicator_of_notMem hz,indicator_of_notMem hz]
    simp only [MetricForms.pairing_self_eq_zero _ _ |>.mpr rfl,mul_zero]

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (hs : IsSmooth α)

include hs in
omit [MeasurableSpace X] [BorelSpace X] in
lemma localizedPairing_integrable (p : A.centers) {k : ℕ} (hk : k=1 ∨ k=2)
    {a : ManifoldForms.Form X k} (ha : Smooth a) :
    Integrable (fun z => chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
      (localizedFunction A p a z) (localizedFunction A p a z)) := by
  rw [localizedPairing_eq_coordinateIntegrand A J α ht p hk a]
  apply coordinateIntegrand_integrable J α hs ht p.val
  · apply ((A.partition p).contMDiff.continuous.pow 2).mul
    rcases hk with rfl|rfl
    · exact (GeometricAdjoint.pairing_one_smooth J α hs ht ha ha).continuous
    · exact (GeometricAdjoint.pairing_two_smooth J α hs ht ha ha).continuous
  · apply (tsupport_mul_subset_left).trans
    exact (cutoff_square_tsupport A p).trans (A.subordinate p)

include hs in

lemma integral_localizedPairing (p : A.centers) {k : ℕ} (hk : k=1 ∨ k=2)
    {a : ManifoldForms.Form X k} (ha : Smooth a) :
    (∫ z, chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
      (localizedFunction A p a z) (localizedFunction A p a z)) =
    ∫ x, (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a a x ∂geometricVolume A J α := by
  rw [localizedPairing_eq_coordinateIntegrand A J α ht p hk a]
  have hc : Continuous (fun x => (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a a x) := by
    apply ((A.partition p).contMDiff.continuous.pow 2).mul
    rcases hk with rfl|rfl
    · exact (GeometricAdjoint.pairing_one_smooth J α hs ht ha ha).continuous
    · exact (GeometricAdjoint.pairing_two_smooth J α hs ht ha ha).continuous
  have hp : tsupport (fun x => (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a a x) ⊆
      (extChartAt Model p.val).source :=
    tsupport_mul_subset_left.trans ((cutoff_square_tsupport A p).trans (A.subordinate p))
  rw [integral_geometricVolume_coordinate A J α hs ht p.val _ hc hp,
    ← integral_indicator (isOpen_extChartAt_target p.val).measurableSet]
  rfl
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_AntiEnergy
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace ManifoldHodge
lemma codifferential_anti (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {a : TwoForm X} (ha : antiInvariantPart J a = a) :
    codifferential J α ht a = -starThree J α ht (ManifoldForms.exteriorDerivative a) := by
  have he : starTwo J α ht a = a := by
    conv_lhs => rw [← ha]
    exact (starTwo_antiInvariant J α ht a).trans ha
  rw [codifferential,he]
end ManifoldHodge

end TamingCompatibility

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_GeometricCutoff
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section

namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge GeometricAdjoint
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma codifferential_fun_smul_anti (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {a : TwoForm X} (ha : Smooth a) (hanti : antiInvariantPart J a = a)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    codifferential J α ht (fun x => f x • a x) =
      (fun x => f x • codifferential J α ht a x) -
        starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) a) := by
  rw [codifferential_anti J α ht (antiInvariant_fun_smul J hanti f),
    exteriorDerivative_fun_smul hf ha,ManifoldHodge.starThree_add]
  funext x
  have he := congrFun (codifferential_anti J α ht hanti) x
  let d : MetricForms.Form Space 3 := exteriorDerivative a x
  let q : MetricForms.Form Space 1 := codifferential J α ht a x
  let s : MetricForms.Form Space 1 := starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) a) x
  let F : MetricForms.Form Space 2 := invariantPart J α x
  let g := pointMetric J α ht x
  change -(MetricHodge.starThree g F (f x • d) + s) = f x • q - s
  change q = -MetricHodge.starThree g F d at he
  rw [MetricHodge.starThree_smul,he]
  module

lemma pairing_star_wedge_anti (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {a : TwoForm X} (ha : antiInvariantPart J a = a) (ξ : ManifoldForms.Form X 1) (x : X) :
    pairing J α ht (starThree J α ht (ManifoldForms.wedgeOne ξ a))
      (starThree J α ht (ManifoldForms.wedgeOne ξ a)) x =
      (1/2:ℝ) * pairing J α ht ξ ξ x * pairing J α ht a a x := by
  let g := pointMetric J α ht x
  let Jx : Space →L[ℝ] Space := J.endomorphism x
  obtain ⟨b,hb,h0,h1,h2,h3⟩ := VolumeNormalization.exists_metric_unitary_basis g Jx (J.square x)
    ((invariantPart_isInvariant J α).associatedBilinear_hermitian x) (by simp [Space])
  have hanti : (a x).compContinuousLinearMap Jx = -a x := by
    ext v
    have h := congrArg (fun b => b x v) ha
    change (1/2:ℝ) * (a x v - (a x).compContinuousLinearMap Jx v) = a x v at h
    change (a x).compContinuousLinearMap Jx v = -a x v
    linarith
  have he := AntiInvariantFrame.star_wedge_anti g (by simp [Space]) b hb Jx h0 h1 h2 h3
    (invariantPart J α x) (fun u v => (associatedBilinear_invariantPart_fundamental J α x u v).symm)
    (ExteriorForms.oneLinear (E := Space) (ξ x)) (a x) hanti
  have hx : ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1)
      (ExteriorForms.oneLinear (E := Space) (ξ x)) = ξ x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).apply_symm_apply _
  rw [hx] at he
  exact he

lemma cutoff_delta_pointwise (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    {a : TwoForm X} (ha : Smooth a) (hanti : antiInvariantPart J a = a)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (x : X) :
    pairing J α ht (codifferential J α ht (fun x => f x • a x))
      (codifferential J α ht (fun x => f x • a x)) x ≤
      2*(f x)^2*pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x +
        pairing J α ht (scalarDifferential f) (scalarDifferential f) x * pairing J α ht a a x := by
  rw [codifferential_fun_smul_anti J α ht ha hanti hf]
  let d : MetricForms.Form Space 1 := codifferential J α ht a x
  let s : MetricForms.Form Space 1 := starThree J α ht (ManifoldForms.wedgeOne (scalarDifferential f) a) x
  have hb := MetricForms.pairing_sub_self_le (pointMetric J α ht x) (f x • d) s
  rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right] at hb
  have he := pairing_star_wedge_anti J α ht hanti (scalarDifferential f) x
  change MetricForms.pairing (pointMetric J α ht x) s s = _ at he
  rw [he] at hb
  convert hb using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [GeometricAdjoint.pairing, d] <;> (first | rfl | ring))
end TamingCompatibility

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume ContinuousAlternatingMap
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

def localDelta (p : A.centers) (a : TwoForm X) : Space → MetricForms.Form Space 1 := fun x =>
  MetricHodge.starThree (coordinateMetric J α ht p.val x)
    (ManifoldForms.pullback (invariantPart J α) (extChartAt Model p.val).symm x)
    (extDeriv (localizedFunction A p a) x)

lemma localizedFunction_eq_cutoff (p : A.centers) (a : TwoForm X) {z : Space}
    (hz : z ∈ (extChartAt Model p.val).target) : localizedFunction A p a z =
      ManifoldForms.pullback (cutoffForm A p a) (extChartAt Model p.val).symm z := by
  unfold localizedFunction
  rw [indicator_of_mem hz]
  ext v
  rfl

lemma localDelta_eq (p : A.centers) {a : TwoForm X} (ha : Smooth a)
    (hanti : antiInvariantPart J a = a) {z : Space} (hz : z ∈ (extChartAt Model p.val).target) :
    localDelta A J α ht p a z = -ManifoldForms.pullback
      (codifferential J α ht (cutoffForm A p a)) (extChartAt Model p.val).symm z := by
  have he : localizedFunction A p a =ᶠ[𝓝 z]
      ManifoldForms.pullback (cutoffForm A p a) (extChartAt Model p.val).symm := by
    filter_upwards [(isOpen_extChartAt_target p.val).mem_nhds hz] with y hy
    exact localizedFunction_eq_cutoff A p a hy
  unfold localDelta
  rw [he.extDeriv_eq,pullback_codifferential_antiInvariant J α ht
    (cutoffForm_smooth A p ha) (cutoffForm_anti A J p hanti) p.val hz,neg_neg]
  rfl

lemma cutoffDelta_zero_off (p : A.centers) {a : TwoForm X}
    (hanti : antiInvariantPart J a = a) {x : X} (hx : x ∉ tsupport (A.partition p)) :
    codifferential J α ht (cutoffForm A p a) x = 0 := by
  rw [codifferential_anti J α ht (cutoffForm_anti A J p hanti)]
  let F : MetricForms.Form Space 2 := invariantPart J α x
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) F
    (exteriorDerivative (fun y => A.partition p y • a y) x) = 0
  rw [exteriorDerivative_fun_smul_vanishes a hx]
  change -MetricHodge.starThree (GeometricAdjoint.pointMetric J α ht x) F (0 : MetricForms.Form Space 3) = 0
  rw [MetricHodge.starThree_zero,neg_zero]

variable [CompactSpace X]
lemma localDelta_zero_off (p : A.centers) (a : TwoForm X) {z : Space}
    (hz : z ∉ coordinateSupport A p) : localDelta A J α ht p a z = 0 := by
  have he : localizedFunction A p a =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(coordinateSupport_compact A p).isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact localizedFunction_zero_off A p a hy
  unfold localDelta
  rw [he.extDeriv_eq]
  have hz : extDeriv (fun _ => (0 : MetricForms.Form Space 2)) z = 0 := by
    simp [extDeriv,← alternatizeUncurryFinCLM_apply]
  rw [hz,MetricHodge.starThree_zero]

omit [CompactSpace X] in
lemma cutoffDelta_pairing_tsupport (p : A.centers) {a : TwoForm X}
    (hanti : antiInvariantPart J a = a) :
    tsupport (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
      (codifferential J α ht (cutoffForm A p a))) ⊆ tsupport (A.partition p) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  apply hx
  change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
    (codifferential J α ht (cutoffForm A p a) x) (codifferential J α ht (cutoffForm A p a) x) = 0
  rw [cutoffDelta_zero_off A J α ht p hanti hn]
  exact (MetricForms.pairing_self_eq_zero _ _).mpr rfl

variable (hs : IsSmooth α)
include hs in
lemma localDelta_density_integrable (p : A.centers) {a : TwoForm X} (ha : Smooth a)
    (hanti : antiInvariantPart J a = a) :
    Integrable (coordinateIntegrand J α p.val
      (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a)))) := by
  apply coordinateIntegrand_integrable J α hs ht p.val
  · have hd := GeometricAdjoint.codifferential_smooth J α hs ht (cutoffForm_smooth A p ha)
    exact (GeometricAdjoint.pairing_one_smooth J α hs ht hd hd).continuous
  · exact (cutoffDelta_pairing_tsupport A J α ht p hanti).trans (A.subordinate p)

variable [MeasurableSpace X] [BorelSpace X]
include hs in
lemma integral_localDelta_density (p : A.centers) {a : TwoForm X} (ha : Smooth a)
    (hanti : antiInvariantPart J a = a) :
    (∫ z, coordinateIntegrand J α p.val
      (GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a))) z) =
    ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
        (codifferential J α ht (cutoffForm A p a)) x ∂geometricVolume A J α := by
  have hd := GeometricAdjoint.codifferential_smooth J α hs ht (cutoffForm_smooth A p ha)
  rw [integral_geometricVolume_coordinate A J α hs ht p.val _
    (GeometricAdjoint.pairing_one_smooth J α hs ht hd hd).continuous
    ((cutoffDelta_pairing_tsupport A J α ht p hanti).trans (A.subordinate p)),
    ← integral_indicator (isOpen_extChartAt_target p.val).measurableSet]
  rfl
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartMetricBounds
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume LocalMatrixOperator
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)

lemma localDelta_pairing (p : A.centers) {a : TwoForm X} (ha : Smooth a)
    (hanti : antiInvariantPart J a = a) {z : Space} (hz : z ∈ (extChartAt Model p.val).target) :
    chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
      (localDelta A J α ht p a z) (localDelta A J α ht p a z) =
    coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
      (codifferential J α ht (cutoffForm A p a)) (codifferential J α ht (cutoffForm A p a))) z := by
  rw [localDelta_eq A J α ht p ha hanti hz,MetricForms.pairing_neg_self,
    pairing_chart J α ht p.val (Or.inl rfl) _ _ hz]
  unfold coordinateIntegrand
  rw [indicator_of_mem hz]

variable [CompactSpace X] (hs : IsSmooth α)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include hs hD in
lemma localDelta_norm_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a → antiInvariantPart J a = a → ∀ z,
      ‖oneVector (localDelta A J α ht p a z)‖^2 ≤
        C * coordinateIntegrand J α p.val (GeometricAdjoint.pairing J α ht
          (codifferential J α ht (cutoffForm A p a)) (codifferential J α ht (cutoffForm A p a))) z := by
  obtain ⟨C,hC,hbound⟩ := coordinate_metric_one_bounds A J α hs ht D hD p
  refine ⟨(‖oneVector‖^2+1)*C,mul_pos (by positivity) hC,?_⟩
  intro a ha hanti z
  by_cases hz : z ∈ coordinateSupport A p
  · have hh := (hbound z hz (localDelta A J α ht p a z)).1
    have hchart := (coordinateSupport_domain A J α ht D hD p).trans (D p).domain_subset hz
    rw [localDelta_pairing A J α ht p ha hanti hchart] at hh
    have ho := pow_le_pow_left₀ (norm_nonneg _) (oneVector.le_opNorm (localDelta A J α ht p a z)) 2
    rw [mul_pow] at ho
    have hi := coordinateIntegrand_self_nonneg J α ht p.val (codifferential J α ht (cutoffForm A p a)) z
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖oneVector‖)
    nlinarith
  · rw [localDelta_zero_off A J α ht p a hz,map_zero,norm_zero,zero_pow (by decide : 2≠0)]
    exact mul_nonneg (mul_nonneg (by positivity) hC.le)
      (coordinateIntegrand_self_nonneg J α ht p.val (codifferential J α ht (cutoffForm A p a)) z)

variable [MeasurableSpace X] [BorelSpace X]
include hs hD in
lemma integral_localDelta_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a → antiInvariantPart J a = a →
      (∫ z, ‖oneVector (localDelta A J α ht p a z)‖^2) ≤
        C * ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
          (codifferential J α ht (cutoffForm A p a)) x ∂geometricVolume A J α := by
  obtain ⟨C,hC,hbound⟩ := localDelta_norm_bound A J α ht hs D hD p
  refine ⟨C,hC,?_⟩
  intro a ha hanti
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => sq_nonneg
    ‖oneVector (localDelta A J α ht p a z)‖))
    ((localDelta_density_integrable A J α ht hs p ha hanti).const_mul C)
    (Filter.Eventually.of_forall (hbound a ha hanti))
  rwa [integral_const_mul,integral_localDelta_density A J α ht hs p ha hanti] at h
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartScalarBound
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hs hD in
lemma density_lower_on_support (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ coordinateSupport A p, 1 ≤ C * chartDensity J α p.val z := by
  have hd : ∀ z ∈ coordinateSupport A p, 0 < chartDensity J α p.val z := fun z hz =>
    chartDensity_pos J α ht p.val ((coordinateSupport_domain A J α ht D hD p).trans (D p).domain_subset hz)
  have hc := (chartDensity_smooth J α hs ht p.val).continuousOn.mono
    ((coordinateSupport_domain A J α ht D hD p).trans (D p).domain_subset)
  obtain ⟨B,hB⟩ := (coordinateSupport_compact A p).exists_bound_of_continuousOn
    (f := fun z => (chartDensity J α p.val z)⁻¹) (hc.inv₀ (fun z hz => ne_of_gt (hd z hz)))
  refine ⟨max 1 B,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro z hz
  have h := (le_abs_self ((chartDensity J α p.val z)⁻¹)).trans ((hB z hz).trans (le_max_right 1 B))
  have hmul := mul_le_mul_of_nonneg_right h (hd z hz).le
  simpa only [inv_mul_cancel₀ (ne_of_gt (hd z hz))] using hmul

include hs hD in
lemma scalar_norm_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, antiInvariantPart J a = a → ∀ z,
      (scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2 ≤
        C * (chartDensity J α p.val z * MetricForms.pairing (coordinateMetric J α ht p.val z)
          (localizedFunction A p a z) (localizedFunction A p a z)) := by
  obtain ⟨C,hC,hbound⟩ := density_lower_on_support A J α hs ht D hD p
  refine ⟨C,hC,?_⟩
  intro a hanti z
  by_cases hz : z ∈ coordinateSupport A p
  · rw [localizedPairing_scalars A J α ht D hD p hanti]
    have hb := hbound z hz
    have hn := add_nonneg (sq_nonneg (scalar A J α ht D p a 2 z)) (sq_nonneg (scalar A J α ht D p a 3 z))
    have hm := mul_le_mul_of_nonneg_right hb hn
    nlinarith
  · rw [scalar_zero_off A J α ht D p a 2 hz,scalar_zero_off A J α ht D p a 3 hz,
      localizedFunction_zero_off A p a hz]
    simp only [zero_pow (by decide : 2≠0),add_zero,(MetricForms.pairing_self_eq_zero _ _).mpr rfl,mul_zero,le_refl]

omit [CompactSpace X] in
lemma pairing_cutoff (p : A.centers) (a : TwoForm X) (x : X) :
    GeometricAdjoint.pairing J α ht (cutoffForm A p a) (cutoffForm A p a) x =
      (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a a x := by
  let v : MetricForms.Form Space 2 := a x
  change MetricForms.pairing (GeometricAdjoint.pointMetric J α ht x)
    (A.partition p x • v) (A.partition p x • v) = (A.partition p x)^2 * MetricForms.pairing _ v v
  rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right]
  ring

variable [MeasurableSpace X] [BorelSpace X]
include hs hD in
lemma integral_scalar_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a → antiInvariantPart J a = a →
      (∫ z, (scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2) ≤
        C * ∫ x, GeometricAdjoint.pairing J α ht (cutoffForm A p a)
          (cutoffForm A p a) x ∂geometricVolume A J α := by
  obtain ⟨C,hC,hbound⟩ := scalar_norm_bound A J α hs ht D hD p
  refine ⟨C,hC,?_⟩
  intro a ha hanti
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => add_nonneg
    (sq_nonneg (scalar A J α ht D p a 2 z)) (sq_nonneg (scalar A J α ht D p a 3 z))))
    ((localizedPairing_integrable A J α ht hs p (Or.inr rfl) ha).const_mul C)
    (Filter.Eventually.of_forall (hbound a hanti))
  rw [integral_const_mul,integral_localizedPairing A J α ht hs p (Or.inr rfl) ha] at h
  simpa only [pairing_cutoff A J α ht p a] using h
end TamingCompatibility.GeometricChart

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization GeometricAdjoint
open _root_.MeasureTheory Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

include hs in
lemma cutoff_energy_bound {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, Smooth a → antiInvariantPart J a = a →
      (∫ x, pairing J α ht (fun y => f y • a y) (fun y => f y • a y) x ∂geometricVolume A J α) +
      (∫ x, pairing J α ht (codifferential J α ht (fun y => f y • a y))
        (codifferential J α ht (fun y => f y • a y)) x ∂geometricVolume A J α) ≤
      C * ((∫ x, pairing J α ht a a x ∂geometricVolume A J α) +
        (∫ x, pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x ∂geometricVolume A J α)) := by
  let := geometricVolume_finite A J α hs ht
  have hdf := scalarDifferential_smooth hf
  have hc := (pairing_one_smooth J α hs ht hdf hdf).continuous
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun x => (f x)^2 + pairing J α ht (scalarDifferential f) (scalarDifferential f) x)
    ((hf.continuous.pow 2).add hc).continuousOn
  obtain ⟨D,hD⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun x => 2*(f x)^2) ((hf.continuous.pow 2).const_mul 2).continuousOn
  let C := max 1 (max B D)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro a ha hanti
  have hb₁ (x : X) : (f x)^2 + pairing J α ht (scalarDifferential f) (scalarDifferential f) x ≤ C :=
    (le_abs_self _).trans ((hB x (mem_univ x)).trans ((le_max_left B D).trans (le_max_right 1 (max B D))))
  have hb₂ (x : X) : 2*(f x)^2 ≤ C :=
    (le_abs_self _).trans ((hD x (mem_univ x)).trans ((le_max_right B D).trans (le_max_right 1 (max B D))))
  have hal := (pairing_two_smooth J α hs ht ha ha).continuous.integrable_of_hasCompactSupport (μ := geometricVolume A J α)
    (HasCompactSupport.of_compactSpace _)
  have had := codifferential_smooth J α hs ht ha
  have hadl := (pairing_one_smooth J α hs ht had had).continuous.integrable_of_hasCompactSupport (μ := geometricVolume A J α)
    (HasCompactSupport.of_compactSpace _)
  have hfa := Smooth.fun_smul hf ha
  have hfal := (pairing_two_smooth J α hs ht hfa hfa).continuous.integrable_of_hasCompactSupport (μ := geometricVolume A J α)
    (HasCompactSupport.of_compactSpace _)
  have hfad := codifferential_smooth J α hs ht (b := (fun y => f y • a y : TwoForm X)) hfa
  have hfadl := (pairing_one_smooth J α hs ht hfad hfad).continuous.integrable_of_hasCompactSupport (μ := geometricVolume A J α)
    (HasCompactSupport.of_compactSpace _)
  rw [← integral_add hfal hfadl,← integral_add hal hadl,← integral_const_mul]
  apply integral_mono (hfal.add hfadl) ((hal.add hadl).const_mul C)
  intro x
  have hx := cutoff_delta_pointwise J α ht ha hanti hf x
  have he : pairing J α ht (fun y => f y • a y) (fun y => f y • a y) x =
      (f x)^2 * pairing J α ht a a x := by
    let v : MetricForms.Form Space 2 := a x
    change MetricForms.pairing (pointMetric J α ht x) (f x • v) (f x • v) = _
    rw [MetricForms.pairing_smul_left,MetricForms.pairing_smul_right]
    change f x * (f x * MetricForms.pairing (pointMetric J α ht x) v v) =
      (f x)^2 * MetricForms.pairing (pointMetric J α ht x) v v
    ring
  simp only [Pi.add_apply]
  rw [he]
  have h₁ := mul_le_mul_of_nonneg_right (hb₁ x) (MetricForms.pairing_self_nonneg (pointMetric J α ht x) (a x))
  have h₂ := mul_le_mul_of_nonneg_right (hb₂ x) (MetricForms.pairing_self_nonneg (pointMetric J α ht x) (codifferential J α ht a x))
  change ((f x)^2 + pairing J α ht (scalarDifferential f) (scalarDifferential f) x) *
    pairing J α ht a a x ≤ C * pairing J α ht a a x at h₁
  change 2*(f x)^2 * pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x ≤
    C * pairing J α ht (codifferential J α ht a) (codifferential J α ht a) x at h₂
  nlinarith
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_DirectionH1
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume LocalMatrixOperator EuclideanEnergy
open Set _root_.MeasureTheory AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma localizedLinear_support (p : A.centers) (a : smoothForms X 2) :
    tsupport (localizedLinear A 2 p a) ⊆ coordinateSupport A p := by
  apply closure_minimal _ (coordinateSupport_compact A p).isClosed
  intro x hx
  by_contra hn
  apply hx
  change formCoordinates 2 (localizedFunction A p a.val x) = 0
  rw [localizedFunction_zero_off A p a.val hn,map_zero]

section L2Norm
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
lemma schwartz_l2_norm_sq (u : 𝓢(Space,F)) :
    ‖u.toLp 2 (volume : Measure Space)‖^2 = ∫ x, ‖u x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u.coeFn_toLp 2 (volume : Measure Space)] with x hx
  rw [hx,real_inner_self_eq_norm_sq]
end L2Norm

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ChartMetricComparison
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume GeometricHilbert
open Set _root_.MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

local instance instFiniteDimensionalRealContinuousMultilinearMapFinOfNatNatSpace : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective
local instance instFiniteDimensionalRealFormSpaceOfNatNat : FiniteDimensional ℝ (MetricForms.Form Space 2) :=
  FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

lemma formCoordinates_lower : ∃ C : ℝ, 0 < C ∧ ∀ v : MetricForms.Form Space 2,
    ‖v‖^2 ≤ C * ‖formCoordinates 2 v‖^2 := by
  obtain ⟨K,hK,hb⟩ := (formCoordinates 2).toLinearMap.injective_iff_antilipschitz.mp
    (FiberCoordinates.complexCoordinates_injective (stdOrthonormalBasis ℝ Space).toBasis 2)
  refine ⟨(K:ℝ)^2,by exact sq_pos_of_pos (by exact_mod_cast hK),?_⟩
  intro v
  have h : ‖v‖ ≤ (K:ℝ)*‖formCoordinates 2 v‖ := by
    simpa only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] using hb.le_mul_dist v 0
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg v) h 2

include hs hD in
lemma localized_metric_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : smoothForms X 2,
      (∫ x, (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a.val a.val x ∂geometricVolume A J α) ≤
        C * ‖localizeL2 A 2 a p‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coordinate_metric_two_bounds A J α hs ht D hD p
  obtain ⟨K,hK,hform⟩ := formCoordinates_lower
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro a
  rw [localizeL2_apply,schwartz_l2_norm_sq,← integral_localizedPairing A J α ht hs p (Or.inr rfl) a.property]
  have hint : Integrable (fun x => ‖localizedLinear A 2 p a x‖^2) := by
    exact (memLp_two_iff_integrable_sq_norm (localizedLinear A 2 p a).continuous.aestronglyMeasurable).mp
      ((localizedLinear A 2 p a).memLp 2 volume)
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (show 0 ≤ chartDensity J α p.val x from Real.sqrt_nonneg _)
        (MetricForms.pairing_self_nonneg (coordinateMetric J α ht p.val x) (localizedFunction A p a.val x))))
    (hint.const_mul (C*K)) (Filter.Eventually.of_forall (fun x => ?_))
  · simpa only [integral_const_mul] using h
  · by_cases hx : x ∈ coordinateSupport A p
    · exact ((hbound x hx (localizedFunction A p a.val x)).2).trans
        ((mul_le_mul_of_nonneg_left (hform (localizedFunction A p a.val x)) hC.le).trans_eq (mul_assoc _ _ _).symm)
    · change _ ≤ C*K*‖formCoordinates 2 (localizedFunction A p a.val x)‖^2
      have hz : localizedFunction A p a.val x = 0 := localizedFunction_zero_off A p a.val hx
      have hp : MetricForms.pairing (coordinateMetric J α ht p.val x)
          (localizedFunction A p a.val x) (localizedFunction A p a.val x) = 0 :=
        (MetricForms.pairing_self_eq_zero _ _).mpr hz
      dsimp only
      rw [hp,hz,map_zero,norm_zero]
      simp

include hs hD in

theorem metric_norm_le_chart : ∃ C : ℝ, 0 < C ∧ ∀ a : PreL2 A J α hs ht true,
    ‖a‖^2 ≤ C * ‖localizeL2 A 2 a‖^2 := by
  classical
  have hi := geometricVolume_finite A J α hs ht
  let := hi
  choose C hC hbound using localized_metric_bound A J α hs ht D hD
  let B := 1 + ∑ p : A.centers, C p
  have hB : 0 < B := by
    have hsum : 0 ≤ ∑ p : A.centers, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hCB (p : A.centers) : C p ≤ B := by
    exact (Finset.single_le_sum (fun q _ => (hC q).le) (Finset.mem_univ p)).trans (by change (∑ p : A.centers, C p) ≤ 1 + (∑ p : A.centers, C p); linarith)
  let N : ℝ := Fintype.card A.centers
  refine ⟨(N+1)*B,mul_pos (by dsimp [N] <;> positivity) hB,?_⟩
  intro a
  let f : X → ℝ := GeometricAdjoint.pairing J α ht a.val a.val
  have hf : Integrable f (geometricVolume A J α) :=
    (GeometricAdjoint.pairing_two_smooth J α hs ht a.property a.property).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hρ (p : A.centers) : Integrable (fun x => (A.partition p x)^2 * f x) (geometricVolume A J α) :=
    (((A.partition p).contMDiff.continuous.pow 2).mul
      (GeometricAdjoint.pairing_two_smooth J α hs ht a.property a.property).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum (x : X) : f x ≤ N * (∑ p : A.centers, (A.partition p x)^2*f x) := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun p : A.centers => A.partition p x)
    rw [partition_sum A x,one_pow] at h
    have hm := mul_le_mul_of_nonneg_right h (MetricForms.pairing_self_nonneg (GeometricAdjoint.pointMetric J α ht x) (a.val x))
    simpa only [N,f,GeometricAdjoint.pairing,one_mul,Finset.card_univ,Finset.sum_mul,mul_assoc] using hm
  have hI := integral_mono hf
    ((integrable_finsetSum Finset.univ (fun p _ => hρ p)).const_mul N) hsum
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun p _ => hρ p)] at hI
  have hc : (∑ p : A.centers, ∫ x, (A.partition p x)^2*f x ∂geometricVolume A J α) ≤
      B * ‖localizeL2 A 2 a‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    exact (hbound p a).trans (mul_le_mul_of_nonneg_right (hCB p) (sq_nonneg _))
  rw [preL2_norm_sq]
  change (∫ x, f x ∂geometricVolume A J α) ≤ _
  have hm := mul_le_mul_of_nonneg_left hc (by dsimp [N]; positivity : 0 ≤ N)
  have hn := mul_nonneg hB.le (sq_nonneg ‖localizeL2 A 2 a‖)
  nlinarith
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GeometricFrameTest
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
  (ht : Tames α J) (p : X) (D : Data J α ht p)

include hs in
lemma manifoldTest_smooth {q : Space → EuclideanEnergy.Pair} (hq : ContDiff ℝ ∞ q)
    (hc : HasCompactSupport q) (hqD : tsupport q ⊆ D.domain) :
    IsSmooth (manifoldTest J α ht p D q) :=
  IsSmooth.antiInvariantPart (chartLift_smooth p (coordinateTest_smooth J α hs ht p D hq hqD)
    (frameTest_compact _ _ hc) ((coordinateTest_support J α ht p D q).trans
      (hqD.trans D.domain_subset))) J

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_RawNormal
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

def rawPair (a : TwoForm X) (z : Space) : EuclideanEnergy.Pair :=
  EuclideanEnergy.pair (rawScalar J α ht p D a 2 z) (rawScalar J α ht p D a 3 z)

end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator ManifoldLocalization ManifoldVolume
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)

def normalOperator (q : Space → EuclideanEnergy.Pair) (z : Space) : Space :=
  (∑ i, normalA J α ht p D i z (fderiv ℝ q z (EuclideanEnergy.e i))) +
    normalB J α ht p D z (q z)

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalPatch
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge LocalMatrixOperator Set Filter LocalFormalAdjoint LineDeriv
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

def patchA (i : Fin 4) : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space) :=
  SchwartzCutoff.schwartz D.domain_open (normalA_smooth J α ht p D i) hφ hc hφD

def patchB : 𝓢(Space,EuclideanEnergy.Pair →L[ℝ] Space) :=
  SchwartzCutoff.schwartz D.domain_open (normalB_smooth J α hs ht p D) hφ hc hφD

end TamingCompatibility.GeometricChart

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawTest
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def realPairSchwartz (p : A.centers) (a : smoothForms X 2) : 𝓢(Space,EuclideanEnergy.Pair) :=
  SchwartzMap.postcompCLM (retract 2) (pairLinear A J α ht D hD p a)

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TestLinear
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set
open scoped Manifold
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] {k : ℕ}
lemma chartLift_add (p : X) (a b : Space → Space [⋀^Fin k]→L[ℝ] ℝ) :
    chartLift p (a+b) = chartLift p a + chartLift p b := by
  classical
  funext x
  simp only [chartLift,Pi.add_apply]
  split_ifs
  · rfl
  · simp
end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge LocalMatrixOperator
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J) (p : X) (D : Data J α ht p)
lemma manifoldTest_add (q r : Space → EuclideanEnergy.Pair) :
    manifoldTest J α ht p D (q+r) = manifoldTest J α ht p D q + manifoldTest J α ht p D r := by
  rw [manifoldTest,coordinateTest_add,chartLift_add,antiInvariantPart_add]
  rfl
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ClosedLiftData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

def deltaB (z : Space) : EuclideanEnergy.Pair →L[ℝ] MetricForms.Form Space 1 :=
  -(frameRecover (coordinateMetric J α ht p z) (fun j => D.frame j z)).comp (normalB J α ht p D z)

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge _root_.MeasureTheory Set Filter NormalJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma frameMap_metric (g : MetricModel.Metric Space) (b : Fin 4 → Space)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (u v : Space) :
    g.bilinear (frameMap b u) (frameMap b v) = ⟪u,v⟫ := by
  classical
  simp only [frameMap_apply,map_sum,map_smul,_root_.sum_apply,
    _root_.smul_apply,smul_eq_mul]
  simp only [hb]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace
local instance instNormedAddCommGroupMetricDerivativeSpace_r9ee472_1 : NormedAddCommGroup (NormalJets.MetricDerivative (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricDerivativeSpace_r9ee472_1 : NormedSpace ℝ (NormalJets.MetricDerivative (V := ManifoldForms.Space)) := ContinuousLinearMap.toNormedSpace
lemma normalMetric_zero (g : Space → MetricTensor (V := Space))
    (B : Space → Space →L[ℝ] Space) (p : Space) :
    normalMetric g B (p,0) = (g p).bilinearComp (B p) (B p) := by
  simp [normalMetric,affineMetric]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_NormalMap
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

local instance instNormedAddCommGroupMetricTensorSpace_2_r9ee472_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_2_r9ee472_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
def ActualData (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
    (p : X) (D : GeometricChart.Data J α ht p) (q : Space)
    (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space) : Prop :=
  ∃ O : Set Space, IsOpen O ∧ q ∈ O ∧ O ⊆ D.domain ∧
    (∀ y ∈ O, g y = (coordinateMetric J α ht p y).bilinear) ∧
    (∀ y ∈ O, B y = frameMap (fun i => D.frame i y)) ∧
    (∀ y v w, g y v w = g y w v)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.NormalMetricCalculus
open NormalJets MetricDensity Filter Set
open scoped ContDiff Topology
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

local instance instNormedAddCommGroupMetricTensorV_1_r9ee472_1 : NormedAddCommGroup (MetricTensor (V := V)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorV_1_r9ee472_1 : NormedSpace ℝ (MetricTensor (V := V)) := ContinuousLinearMap.toNormedSpace
def regularMetrics : Set (MetricTensor (V := V)) :=
  {M | 0 < (gram (stdOrthonormalBasis ℝ V).toBasis M).det ∧ (metricOperator M).IsInvertible}

lemma euclidean_mem_regularMetrics : EMetric ∈ regularMetrics := by
  constructor
  · simp [gram_euclidean]
  · rw [metricOperator_euclidean]
    exact ⟨ContinuousLinearEquiv.refl ℝ V,rfl⟩

end TamingCompatibility.GeometricHilbert.NormalMetricCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianGeometricCenter
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X)
variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

def hermitianCenterExtension {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain) :
    SchwartzMap Space (Space →L[ℝ] Space) :=
  SchwartzCutoff.schwartz D.domain_open
    ((coordinateJ_smooth J p).mono D.domain_subset) hφ hc hφD

end TamingCompatibility.GeometricChart

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialGeometricCoefficient
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X)

variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

lemma radialSourceVector_smooth (j : Fin 2) :
    ContDiffOn ℝ ∞ (radialSourceVector J p D j) D.domain :=
  antiDdcVector_smooth J p D.domain_open D.domain_subset
    (D.frame_smooth 0) (D.frame_smooth _)

def radialSourceExtension {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain) (j : Fin 2) :
    SchwartzMap Space Space :=
  SchwartzCutoff.schwartz D.domain_open (radialSourceVector_smooth J p D j) hφ hc hφD

end TamingCompatibility.GeometricChart

end
end

section

noncomputable section

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X) {α : TwoForm X} {ht : Tames α J}
  (D : Data J α ht p)
variable {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)
variable {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)

def radialScalarSource (j : Fin 2) : 𝓢(Space,ℝ) := by
  have hc' : HasCompactSupport
      (RadialPotential.firstOrderSource (radialSourceExtension J p D hφ hc hφD j) f) :=
    hfc.of_isClosed_subset (isClosed_tsupport _) (RadialPotential.firstOrderSource_tsupport _ _)
  exact hc'.toSchwartzMap (RadialPotential.firstOrderSource_smooth _
    ((radialSourceExtension J p D hφ hc hφD j).smooth ⊤) f hf)

def radialPairSource : 𝓢(Space,EuclideanEnergy.Pair) :=
  componentTest 0 (radialScalarSource J p D hφ hc hφD hf hfc 0) +
  componentTest 1 (radialScalarSource J p D hφ hc hφD hf hfc 1)

end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RawJetEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge AntiInvariantFrame LocalMatrixOperator GeometricAdjoint Set Filter ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

def deltaComplexB (z : Space) : C 2 →L[ℝ] MetricForms.Form Space 1 :=
  (deltaB J α ht p D z).comp (retract 2)

end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RadialScalarOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
omit [IsManifold Model ∞ X] in
lemma chartLift_smul {k : ℕ} (p : X) (c : ℝ) (f : Space → MetricForms.Form Space k) :
    chartLift p (c • f) = c • chartLift p f := by
  funext x
  simp only [chartLift,Pi.smul_apply]
  split_ifs
  · rfl
  · simp
end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge LocalMatrixOperator
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : Data J α ht p)
lemma manifoldTest_smul (c : ℝ) (q : Space → EuclideanEnergy.Pair) :
    manifoldTest J α ht p D (c • q) = c • manifoldTest J α ht p D q := by
  rw [manifoldTest,coordinateTest_smul,chartLift_smul,antiInvariantPart_smul]
  rfl
end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

local instance instNormedAddCommGroupMetricTensorSpace_4_r9ee472_1 : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealMetricTensorSpace_4_r9ee472_1 : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
lemma ActualData.metric_zero {q : Space} (hactual : ActualData J α ht p D q g B) :
    normalMetric g B (q,0) = EMetric := by
  obtain ⟨O,hO,hqO,hOD,hgact,hBact,hsym⟩ := hactual
  rw [normalMetric_zero,hgact q hqO,hBact q hqO]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact frameMap_metric _ _ (D.frame_gram q (hOD hqO)) v w

attribute [local irreducible] normalFirst

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixDataMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeFiniteFrameResolution
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X)
  (α : TwoForm X)
  (ht : Tames α J)
  (A : FiniteCharts X)

abbrev FrameSpace := (A.centers × Fin 6) → ℝ

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end


