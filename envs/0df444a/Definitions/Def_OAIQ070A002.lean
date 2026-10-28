-- Prove2me | Definitions.Def_OAIQ070A002
-- name    : OAIQ070A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T11:16:29.131711+00:00
-- url     : https://prove2.me/theorems/5a9b2c23-4f74-4c1a-8dd3-7e800e456370
-- title:
--   Definitions bundle OAIQ070A002 of the split of OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 132 declarations of OpenAI's Lean: 82 definitions, 2 inductive types or structures, 4 instances and 44 theorems. The definitions and types are `OAI.YauCounterexamples.ComplexPhaseMatrix`, `OAI.YauCounterexamples.ContinuousSmoothFamilyOn`, `OAI.YauCounterexamples.CoordinateForm`, `OAI.YauCounterexamples.EllipticTest`, `OAI.YauCounterexamples.FixedRadialChoice`, `OAI.YauCounterexamples.FixedRadialChoice.fraction`, `OAI.YauCounterexamples.FlowParameters`, `OAI.YauCounterexamples.HessianJetData`, `OAI.YauCounterexamples.MetricForm`, `OAI.YauCounterexamples.MetricJet`, `OAI.YauCounterexamples.NormalWaveParameter`, `OAI.YauCounterexamples.NormalWaveSpace`, `OAI.YauCounterexamples.PhaseSpace`, `OAI.YauCounterexamples.PositivePairing.EigenpairParameters`, `OAI.YauCounterexamples.ProfileForm`, `OAI.YauCounterexamples.ProfileLattice`, `OAI.YauCounterexamples.ProfilePlane`, `OAI.YauCounterexamples.ProfileTorus`, `OAI.YauCounterexamples.QuadraticInnerSpace`, `OAI.YauCounterexamples.RealSmoothFunctions`, `OAI.YauCounterexamples.SignTests.extrudeSet`, `OAI.YauCounterexamples.SignTests.extrusionEquiv`, `OAI.YauCounterexamples.SignTests.oppositeSet`, `OAI.YauCounterexamples.SignTests.signCertificate`, `OAI.YauCounterexamples.SignTests.signMass`, `OAI.YauCounterexamples.SignTests.swept`, `OAI.YauCounterexamples.SignTests.sweptVolume`, `OAI.YauCounterexamples.SmoothJetZero`, `OAI.YauCounterexamples.SmoothScalar`, `OAI.YauCounterexamples.SmoothScalar.directional`, `OAI.YauCounterexamples.SphericalRegular`, `OAI.YauCounterexamples.SphericalSignAbove`, `OAI.YauCounterexamples.TangentForm`, `OAI.YauCounterexamples.actualCoordinateHessian`, `OAI.YauCounterexamples.boundedDivergence`, `OAI.YauCounterexamples.chartFormDualNorm`, `OAI.YauCounterexamples.chartFormDualSpace`, `OAI.YauCounterexamples.chartFormFormNorm`, `OAI.YauCounterexamples.chartFormFormSpace`, `OAI.YauCounterexamples.chartMetricForm` and 44 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `SmoothYau_DifferentialEq_HmoDualNorm`, `SmoothYau_Estimates_AnisotropicCompositionSmall`, `SmoothYau_Estimates_ExistsBoxIccSubsetOpen`, `SmoothYau_Estimates_FixedRadialChoice`, `SmoothYau_Estimates_PhaseFormMatrix`, `SmoothYau_Estimates_PiolaCancellation`, `SmoothYau_Estimates_PreconditionedInverse`, `SmoothYau_Estimates_QuadraticInnerSpace`, `SmoothYau_Estimates_RadialSpeedPositiveAnnulus`, `SmoothYau_Estimates_RealPhaseLinear`, `SmoothYau_Estimates_ScalarAffineDetNeZero`, `SmoothYau_Estimates_SphericalPinFormNorm`, `SmoothYau_Geometry_RadialFiniteDualNorm`, `SmoothYau_Geometry_SymmLChartTrivialization`, `SmoothYau_Limits_CompactFullProfileMargin`, `SmoothYau_Limits_CoordinateForm`, `SmoothYau_NodalMeasure_ExtrusionEquiv`, `SmoothYau_Smoothness_BoundedDegreeMonomials`, `SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer`, `SmoothYau_Smoothness_ChartTensorCoordLocal1`, `SmoothYau_Smoothness_ContDiffSmoothFiniteWave`, `SmoothYau_Smoothness_ContinuousCompactSmoothJets`, `SmoothYau_Smoothness_FlowParameters`, `SmoothYau_Smoothness_PinningTensorSpace`, `SmoothYau_Smoothness_ProfilePeriodizeEventuallyZero`, `SmoothYau_Smoothness_PulledGradient`, `SmoothYau_Smoothness_SecondDerivNonposLocalMax`, `SmoothYau_Smoothness_SmDualNorm`, `SmoothYau_Smoothness_SobolevRepresentativeOrderCongr`, `SmoothYau_Smoothness_SourceSignBox`, `SmoothYau_Smoothness_SphericalBaseProfileRadius`, `SmoothYau_Smoothness_TestDerivativeComm`, `SmoothYau_Spectrum_BilinearCoordinateMatrixPosDef`, `SmoothYau_Spectrum_ContinuousEigenpairLinearization`, `SmoothYau_Spectrum_ScalarCompDirectional`, `SmoothYau_Spectrum_SphereProjection`.
--
--   **Imports.** It imports the published bundle `Def_SmoothYau`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ070A005`, `OAIQ070A006`, `OAIQ070A007` and `OAIQ070A008`; the statements `OAI_YauCounterexamples_actual_metric_superposition_complete_supported`, `OAI.YauCounterexamples.contDiff_complexLaplaceBeltrami_self`, `OAI_YauCounterexamples_exists_box_amplified_profile`, `OAI.YauCounterexamples.finiteWaveSuperposition_residual`, `OAI_YauCounterexamples_finite_packet_variance_lower`, `OAI.YauCounterexamples.laplaceBeltrami_any_basis_univ`, `OAI_YauCounterexamples_laplaceBeltrami_self_any_basis` and `OAI_YauCounterexamples_spherical_simple_eigenpair_open`; the proofs of `OAI_YauCounterexamples_actual_metric_superposition_complete_supported`, `OAI_YauCounterexamples_exists_box_amplified_profile` and `OAI_YauCounterexamples_finite_packet_variance_lower`.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib
import Definitions.Def_SmoothYau

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CoordinateForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev CoordinateForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E →L[ℝ] ℝ

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_DifferentialEq_HmoDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def positiveFormOn (P : Submodule ℝ E) (T : CoordinateForm E) : Prop :=
  ∀ v ∈ P, v ≠ 0 → 0 < T v v

def hessianMargins (B H : CoordinateForm E) : Prop :=
  positiveFormOn ⊤ ((1/2 : ℝ) • B + H) ∧
  ∃ P : Submodule ℝ E, Module.finrank ℝ P = 2 ∧ positiveFormOn P (H-B)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_AnisotropicCompositionSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
section Neumann
variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

def neumannCorrectedInverse (R : Y →L[𝕜] X) (P : X →L[𝕜] Y) (h : ‖R ∘L P‖ < 1) :
    Y →L[𝕜] X :=
  let hb := ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_sub_of_norm_lt_one h)
  (ContinuousLinearEquiv.ofBijective (1 - R ∘L P)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)).symm.toContinuousLinearMap ∘L R

lemma neumannCorrectedInverse_fixed (R : Y →L[𝕜] X) (P : X →L[𝕜] Y)
    (h : ‖R ∘L P‖ < 1) (f : Y) :
    neumannCorrectedInverse R P h f = R (f + P (neumannCorrectedInverse R P h f)) := by
  let hb := ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_sub_of_norm_lt_one h)
  let e := ContinuousLinearEquiv.ofBijective (1 - R ∘L P)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have he := e.apply_symm_apply (R f)
  change neumannCorrectedInverse R P h f - R (P (neumannCorrectedInverse R P h f)) = R f at he
  rw [map_add]
  exact sub_eq_iff_eq_add.mp he

end Neumann

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_SphereProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}
local instance instFactEqNatFinrankRealEuclideanHAddOfNat : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) := ⟨by simp [Euclidean]⟩

lemma sphere_chart_target (p : Sphere n) : (chartAt (Euclidean n) p).target = univ := by
  change (stereographic' n (-p)).target = _
  simp


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold BoxIntegral Metric
open scoped Topology ContDiff InnerProductSpace

def sphericalRadius (a b : Euclidean 4) (q : Sphere 3) : ℝ :=
  Real.sqrt ((inner ℝ a (q : Euclidean 4))^2+(inner ℝ b (q : Euclidean 4))^2)

lemma sphericalRadius_continuous (a b : Euclidean 4) : Continuous (sphericalRadius a b) :=
  (((continuous_const.inner continuous_subtype_val).pow 2).add
    ((continuous_const.inner continuous_subtype_val).pow 2)).sqrt

lemma sphere_chart_source (p : Sphere 3) : (chartAt (Euclidean 3) p).source = {-p}ᶜ := by
  let : Fact (Module.finrank ℝ (Euclidean 4) = 3+1) := ⟨by simp [Euclidean]⟩
  change (stereographic' 3 (-p)).source = _
  simp

abbrev sourceAxisOne : Euclidean 4 := EuclideanSpace.single 0 1
abbrev sourceAxisTwo : Euclidean 4 := EuclideanSpace.single 1 1

def sourcePole : Sphere 3 := ⟨sourceAxisOne,by simp [sourceAxisOne]⟩

lemma sphericalRadius_neg_sourcePole : sphericalRadius sourceAxisOne sourceAxisTwo (-sourcePole) = 1 := by
  norm_num [sphericalRadius,sourcePole,sourceAxisOne,sourceAxisTwo,
    EuclideanSpace.inner_single_left,PiLp.single_apply]

def sourceSignPoint : Sphere 3 :=
  ⟨EuclideanSpace.single 0 (40/401)+EuclideanSpace.single (2 : Fin 4) (399/401),by
    rw [Metric.mem_sphere,dist_zero_right]
    have hi : inner ℝ
        (EuclideanSpace.single (0 : Fin 4) (40/401 : ℝ)+EuclideanSpace.single (2 : Fin 4) (399/401))
        (EuclideanSpace.single (0 : Fin 4) (40/401 : ℝ)+EuclideanSpace.single (2 : Fin 4) (399/401)) = 1 := by
      simp only [inner_add_left,inner_add_right,EuclideanSpace.inner_single_left,PiLp.single_apply]
      norm_num [Fin.ext_iff]
    rw [real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg (EuclideanSpace.single (0 : Fin 4) (40/401 : ℝ)+EuclideanSpace.single (2 : Fin 4) (399/401))]⟩

lemma sphericalRadius_sourceSignPoint :
    sphericalRadius sourceAxisOne sourceAxisTwo sourceSignPoint = 40/401 := by
  unfold sphericalRadius
  have he : (inner ℝ sourceAxisOne (sourceSignPoint : Euclidean 4))^2+
      (inner ℝ sourceAxisTwo (sourceSignPoint : Euclidean 4))^2 = (40/401 : ℝ)^2 := by
    simp only [sourceAxisOne,sourceAxisTwo,sourceSignPoint,inner_add_right,
      EuclideanSpace.inner_single_left,PiLp.single_apply]
    norm_num [Fin.ext_iff]
  rw [he,Real.sqrt_sq_eq_abs]
  norm_num

lemma sphericalRadius_sublevel_in_source (p : Sphere 3) (a b : Euclidean 4)
    (hp : sphericalRadius a b (-p) = 1) {R : ℝ} (hR : R < 1) :
    {q | sphericalRadius a b q ≤ R} ⊆ (chartAt (Euclidean 3) p).source := by
  intro q hq
  rw [sphere_chart_source]
  intro hneg
  have he : q = -p := hneg
  change sphericalRadius a b q ≤ R at hq
  rw [he,hp] at hq
  exact (not_le_of_gt hR) hq

def sphericalCoverage (p : Sphere 3) (a b : Euclidean 4) (R : ℝ) : Set (Euclidean 3) :=
  chartAt (Euclidean 3) p '' {q | sphericalRadius a b q ≤ R}

lemma sphericalCoverage_compact (p : Sphere 3) (a b : Euclidean 4)
    (hp : sphericalRadius a b (-p) = 1) {R : ℝ} (hR : R < 1) :
    IsCompact (sphericalCoverage p a b R) := by
  have hc : IsCompact {q : Sphere 3 | sphericalRadius a b q ≤ R} :=
    (isClosed_le (sphericalRadius_continuous a b) continuous_const).isCompact
  exact hc.image_of_continuousOn ((chartAt (Euclidean 3) p).continuousOn.mono
    (sphericalRadius_sublevel_in_source p a b hp hR))

lemma sphere_chart_symm_continuous (p : Sphere 3) : Continuous (chartAt (Euclidean 3) p).symm := by
  exact continuousOn_univ.mp (by simpa only [sphere_chart_target] using
    (chartAt (Euclidean 3) p).continuousOn_symm)


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ExistsBoxIccSubsetOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold BoxIntegral Metric
open scoped Topology ContDiff
namespace YauCounterexamples

lemma exists_box_Icc_subset_open {ι : Type*} [Fintype ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ I : Box ι, Box.Icc I ⊆ U := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hx
  let I : Box ι := ⟨fun i => x i-ε/2,fun i => x i+ε/2,fun i => by linarith⟩
  refine ⟨I,?_⟩
  intro y hy
  have hd : dist y x ≤ ε/2 := by
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [Real.norm_eq_abs]
    have h₁ : x i-ε/2 ≤ y i := hy.1 i
    have h₂ : y i ≤ x i+ε/2 := hy.2 i
    exact abs_le.mpr ⟨by dsimp; linarith,by dsimp; linarith⟩
  exact hball (hd.trans_lt (by linarith))

theorem exists_spherical_sign_box :
    ∃ I : Box (Fin 3), ∀ y ∈
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm '' Box.Icc I,
      (1/20 : ℝ) < sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) ∧
      sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < 1/8 := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let f : (Fin 3 → ℝ) → ℝ := fun x =>
    sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) sourcePole).symm (e x))
  have hf : Continuous f := (sphericalRadius_continuous _ _).comp
    ((sphere_chart_symm_continuous sourcePole).comp e.continuous)
  have hsrc : sourceSignPoint ∈ (chartAt (Euclidean 3) sourcePole).source := by
    apply sphericalRadius_sublevel_in_source sourcePole sourceAxisOne sourceAxisTwo
      sphericalRadius_neg_sourcePole (R := 1/8) (by norm_num)
    change sphericalRadius sourceAxisOne sourceAxisTwo sourceSignPoint ≤ 1/8
    rw [sphericalRadius_sourceSignPoint]
    norm_num
  have hn : (f ⁻¹' Set.Ioo (1/20 : ℝ) (1/8)).Nonempty := by
    refine ⟨e.symm ((chartAt (Euclidean 3) sourcePole) sourceSignPoint),?_⟩
    change 1/20 < f _ ∧ f _ < 1/8
    dsimp [f]
    rw [e.apply_symm_apply,(chartAt (Euclidean 3) sourcePole).left_inv hsrc,
      sphericalRadius_sourceSignPoint]
    norm_num
  obtain ⟨I,hI⟩ := exists_box_Icc_subset_open (isOpen_Ioo.preimage hf) hn
  refine ⟨I,?_⟩
  rintro y ⟨x,hx,rfl⟩
  exact hI hx

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactFullProfileMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
section ProfileForms
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev ProfileForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E →L[ℝ] ℝ

end ProfileForms

end

open Set Filter Function Metric
open scoped Topology
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProfilePeriodizeEventuallyZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
abbrev ProfilePlane := ℝ × ℝ
abbrev ProfileLattice := ℤ × ℤ

def profileLatticePoint (k : ProfileLattice) : ProfilePlane := (k.1,k.2)


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RadialSpeedPositiveAnnulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

def periodicRadialOffset (R : ℝ) (x : ProfilePlane) : ProfilePlane := by
  classical
  exact if h : ∃ k, ‖x-profileLatticePoint k‖ < R then x-profileLatticePoint h.choose else 0

def periodicRadialSpeed (β : ℝ → ℝ) (R : ℝ) (x : ProfilePlane) : ℝ :=
  let z := periodicRadialOffset R x
  2*Real.sqrt (z.1^2+z.2^2)*β (z.1^2+z.2^2)

def periodicAngularSecond (β : ℝ → ℝ) (R : ℝ) (x : ProfilePlane) : ℝ :=
  let z := periodicRadialOffset R x
  2*β (z.1^2+z.2^2)

def periodicRadialSecond (β : ℝ → ℝ) (R : ℝ) (x : ProfilePlane) : ℝ :=
  let z := periodicRadialOffset R x
  2*β (z.1^2+z.2^2)+4*(z.1^2+z.2^2)*deriv β (z.1^2+z.2^2)


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PulledGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Manifold Bundle
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance metricDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance metricDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

def selfMetricFlat (g : SmoothMetric E E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (g.inner x).bilinearComp (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm.toContinuousLinearMap
    (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm.toContinuousLinearMap

local instance metricFormNorm_r3c601d_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricFormSpace_r3c601d_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricTriNorm_r3c601d_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance metricTriSpace_r3c601d_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
def coordinateKoszul (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (1/2 : ℝ) • (D+D.flip-(ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.comp D.flip)

def metricChristoffel (g : SmoothMetric E E) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E) (selfMetricFlat g x).inverse).comp
    (coordinateKoszul (fderiv ℝ (selfMetricFlat g) x))

theorem compact_positive_bilinear_lower {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (B : X → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : Continuous B) (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v : E, m*‖v‖^2 ≤ B x v v := by
  let S := K ×ˢ Metric.sphere (0:E) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hc : Continuous (fun p : X × E => B p.1 p.2 p.2) :=
    ((hB.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  have hm : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ v : E, ‖v‖ = 1 → m ≤ B x v v := by
    by_cases hne : S.Nonempty
    · obtain ⟨p,hp,hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
      have hv : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hp.2
      refine ⟨B p.1 p.2 p.2,hpos p.1 hp.1 p.2 (norm_ne_zero_iff.mp (by rw [hv]; norm_num)),?_⟩
      intro x hx v hv
      exact hmin (show (x,v) ∈ S from ⟨hx,mem_sphere_zero_iff_norm.mpr hv⟩)
    · exact ⟨1,zero_lt_one,fun x hx v hv => (hne ⟨(x,v),hx,mem_sphere_zero_iff_norm.mpr hv⟩).elim⟩
  obtain ⟨m,hm,hmB⟩ := hm
  refine ⟨m,hm,?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,hvn]
  have hvw : ‖v‖ • w = v := by simp [w,smul_smul,hvn]
  have heq : B x v v = ‖v‖^2 * B x w w := by
    conv_lhs => rw [←hvw]
    simp only [map_smul,smul_apply,smul_eq_mul]
    ring
  rw [heq,mul_comm m]
  exact mul_le_mul_of_nonneg_left (hmB x hx w hw) (sq_nonneg _)


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
section GenericCoordinateHessian
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
def coordinateCovariantSecond (Γ : E → E →L[ℝ] E →L[ℝ] E) (f : E → V) (x : E) :
    E →L[ℝ] E →L[ℝ] V :=
  fderiv ℝ (fderiv ℝ f) x -
    (ContinuousLinearMap.compL ℝ E E V (fderiv ℝ f x)).comp (Γ x)

end GenericCoordinateHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def actualCoordinateHessian (g : SmoothMetric E E) (u : E → ℝ) : E → CoordinateForm E :=
  coordinateCovariantSecond (metricChristoffel g) u


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_FlowParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

abbrev FlowParameters (E : Type u) [TopologicalSpace E] := (ℝ × E) × C(unitInterval, E)


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SphericalBaseProfileRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
lemma positive_bilinear_bounded (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : E | B v v < 1} := by
  obtain ⟨m, hm, hml⟩ := compact_positive_bilinear_lower (isCompact_singleton (x := ()))
    (fun _ : Unit => B) continuous_const (fun _ _ => hpos)
  rw [NormedSpace.isVonNBounded_iff ℝ]
  apply (Metric.isBounded_ball (x := (0 : E)) (r := Real.sqrt m⁻¹)).subset
  intro v hv
  change dist v 0 < Real.sqrt m⁻¹
  rw [dist_zero_right]
  apply (Real.lt_sqrt (norm_nonneg _)).mpr
  rw [← one_div m]
  apply (lt_div_iff₀ hm).mpr
  simpa only [mul_comm] using (hml () (mem_singleton ()) v).trans_lt hv

def flatMetricOfForm (B : E → E →L[ℝ] E →L[ℝ] ℝ) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v) : SmoothMetric E E where
  inner x := B x
  symm := hsym
  pos := hpos
  isVonNBounded x := positive_bilinear_bounded (B x) (hpos x)
  contMDiff := by
    intro x
    erw [contMDiffAt_section x]
    have h := contMDiffAt_iff_contDiffAt.mpr (hB.contDiffAt (x := x))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext y v w
    have hy : y ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun z => TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ) x).baseSet := by
      simp [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet, chartAt_self_eq]
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      Trivialization.coe_linearMapAt_of_mem _ hy]
    rfl

end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

local instance chartFormDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartFormDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartFormFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartFormFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def metricBasisCoordinate (i : CoordIndex E) : E →L[ℝ] ℝ :=
  ((Module.finBasis ℝ E).coord i).toContinuousLinearMap

def metricMatrixForm (A : Matrix (CoordIndex E) (CoordIndex E) ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • (metricBasisCoordinate i).smulRight (metricBasisCoordinate j)

lemma metricMatrixForm_apply (A : Matrix (CoordIndex E) (CoordIndex E) ℝ) (v w : E) :
    metricMatrixForm A v w =
      ∑ i, ∑ j, A i j * (Module.finBasis ℝ E).coord i v * (Module.finBasis ℝ E).coord j w := by
  simp [metricMatrixForm, metricBasisCoordinate, mul_assoc]

lemma metricMatrixForm_pos {A : Matrix (CoordIndex E) (CoordIndex E) ℝ}
    (hA : A.PosDef) {v : E} (hv : v ≠ 0) : 0 < metricMatrixForm A v v := by
  have hne : (Module.finBasis ℝ E).equivFun v ≠ 0 := by
    simpa only [ne_eq, (Module.finBasis ℝ E).equivFun.map_eq_zero_iff] using hv
  have h := hA.dotProduct_mulVec_pos hne
  simpa [metricMatrixForm_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Module.Basis.equivFun_apply, mul_comm, mul_left_comm, mul_assoc] using h

lemma metricMatrixForm_contDiffOn {A : E → Matrix (CoordIndex E) (CoordIndex E) ℝ}
    {O : Set E} (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O) :
    ContDiffOn ℝ ∞ (fun x => metricMatrixForm (A x)) O := by
  unfold metricMatrixForm
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hA i j).smul contDiffOn_const))

def chartMetricForm (g : SmoothMetric E M) (p : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  metricMatrixForm (metricCoefficients g p y)

lemma chartMetricForm_pairing (g : SmoothMetric E M) (p : M) (y v w : E) :
    chartMetricForm g p y v w = g.inner ((chartAt E p).symm y)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y w) := by
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm y
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner ((chartAt E p).symm y)
  change metricMatrixForm (metricCoefficients g p y) v w = B (D v) (D w)
  rw [metricMatrixForm_apply]
  have hv : v = ∑ i, (Module.finBasis ℝ E).equivFun v i • Module.finBasis ℝ E i := by
    simpa only [Module.Basis.equivFun_symm_apply] using
      ((Module.finBasis ℝ E).equivFun.symm_apply_apply v).symm
  have hw : w = ∑ i, (Module.finBasis ℝ E).equivFun w i • Module.finBasis ℝ E i := by
    simpa only [Module.Basis.equivFun_symm_apply] using
      ((Module.finBasis ℝ E).equivFun.symm_apply_apply w).symm
  conv_rhs => rw [hv, hw]
  unfold metricCoefficients
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  simp only [coordinateVector, D, Module.Basis.equivFun_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  simp [B, Module.Basis.coord_apply, mul_comm, mul_left_comm]
  ring_nf
  rfl

lemma chartMetricForm_symm (g : SmoothMetric E M) (p : M) (y v w : E) :
    chartMetricForm g p y v w = chartMetricForm g p y w v := by
  rw [chartMetricForm_pairing, chartMetricForm_pairing, g.symm]

end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
variable {n : ℕ}

def sphericalBaseProfile (a b : Euclidean 4) (t : ℝ) (q : Sphere 3) : ℝ :=
  Real.log t + (inner ℝ a (q : Euclidean 4))^2 +
    (inner ℝ b (q : Euclidean 4))^2 - t^2


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold BoxIntegral
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_SymmLChartTrivialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
abbrev MetricForm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E →L[ℝ] ℝ
abbrev TangentForm (x : M) := TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ

local instance tensorDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance tensorDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
end


open Set Filter Function Manifold Bundle
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartTensorCoordLocal1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff
variable {P E F G : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure ContinuousSmoothFamilyOn (f : P → E → F) (U : Set E) : Prop where
  smooth : ∀ p x, x ∈ U → ContDiffAt ℝ ∞ (f p) x
  jets : ∀ n, ContinuousOn (fun z : P × E => iteratedFDeriv ℝ n (f z.1) z.2) (univ ×ˢ U)

end


section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapId_solutions : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance instNormedAddCommGroupMetricForm : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContinuousCompactSmoothJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local instance mcfDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance mcfDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance mcfFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance mcfFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance
local instance mcfMatrixMapNorm {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (Matrix ι κ ℝ →L[ℝ] CoordinateForm (E)) :=
  inferInstanceAs (NormedAddCommGroup ((ι → κ → ℝ) →L[ℝ] CoordinateForm (E)))


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev HessianJetData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (CoordinateForm E × (E →L[ℝ] CoordinateForm E)) × ((E →L[ℝ] ℝ) × CoordinateForm E)


end


open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev MetricJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E × (CoordinateForm E × (E →L[ℝ] ℝ))


end

open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_RadialFiniteDualNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section


section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff
abbrev ProfileTorus := UnitAddCircle × UnitAddCircle

def profileTorusQuotient (z : ProfilePlane) : ProfileTorus := (z.1,z.2)

end


open Set Function Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ENNReal InnerProductSpace ContDiff

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_FixedRadialChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff

structure FixedRadialChoice where
  β : ℝ → ℝ
  smooth : ContDiff ℝ ∞ β
  zero_at_zero : β 0 = 0
  range_bound : ∀ t, β t ∈ Icc 0 1
  zero_above : ∀ t, (1:ℝ)/256 ≤ t → β t = 0
  Fmax : ℝ
  S : ℝ
  K : ℝ
  Fmax_pos : 0 < Fmax
  S_pos : 0 < S
  K_pos : 0 < K
  coefficients : ∀ z, 0 ≤ periodicRadialSpeed β (1/4) z ∧
    periodicRadialSpeed β (1/4) z ≤ Fmax ∧
    0 ≤ periodicAngularSecond β (1/4) z ∧
    (periodicRadialSpeed β (1/4) z)^2 ≤ S*periodicAngularSecond β (1/4) z ∧
    |periodicRadialSecond β (1/4) z| ≤ K
  q : ProfilePlane
  ρ : ℝ
  c : ℝ
  δ : ℝ
  g₀ : ℝ
  radius_pos : 0 < ρ
  radius_le : ρ ≤ 1/4
  speed_pos : 0 < c
  delta_pos : 0 < δ
  gain_pos : 0 < g₀
  gain_le : g₀ ≤ 1
  gain_eq : g₀ = Real.sqrt (1+δ^2*c^2/16)-1
  smallness : 9216*K*S*δ^2 ≤ 1
  window : ∀ z, profileTorusQuotient z ∈
    ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ →
    c ≤ periodicRadialSpeed β (1/4) z

def FixedRadialChoice.fraction (D : FixedRadialChoice) : ℝ := (2*D.ρ)^2

end
end YauCounterexamples

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PhaseFormMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]

def realQuadratic (a : ι → ι → ℝ) (v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * v i * v j

def squareSum (v : ι → ℝ) : ℝ := ∑ i, v i * v i


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
open Matrix Set Filter
open scoped Topology Matrix Matrix.Norms.Elementwise




end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PiolaCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι]
lemma piola_cancellation (B : Matrix ι ι ℝ) (D : ι → Matrix ι ι ℝ)
    (hD : ∀ i l m, D i l m = D m l i) (k : ι) :
    ∑ i, (Matrix.trace (D i * B) * B i k - (B * D i * B) i k) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  calc
    (∑ i, ∑ l, ∑ m, D i l m * B m l * B i k) =
        ∑ i, ∑ l, ∑ m, B m l * D m l i * B i k := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      rw [hD i l m]
      ring
    _ = ∑ m, ∑ i, ∑ l, B m l * D m l i * B i k := by
      calc
        _ = ∑ i, ∑ m, ∑ l, B m l * D m l i * B i k := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by rfl
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_PreconditionedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
namespace YauCounterexamples
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def preconditionedInverse (R : X →L[ℝ] Y) (L : Y →L[ℝ] X) : X →L[ℝ] Y :=
  R ∘L Ring.inverse (L ∘L R)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_QuadraticInnerSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction Real ENNReal ContDiff
open MeasureTheory
open scoped ENNReal
open Set Filter
open scoped SchwartzMap ContDiff Topology
open Matrix ContinuousLinearMap
open scoped InnerProductSpace
namespace YauCounterexamples

def QuadraticInnerSpace {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (_hA : A.PosDef) := ι → ℝ

namespace QuadraticInnerSpace
variable {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (hA : A.PosDef)
instance instNormedAddCommGroup : NormedAddCommGroup (QuadraticInnerSpace A hA) := Matrix.toNormedAddCommGroup A hA
instance instInnerProductSpaceReal : InnerProductSpace ℝ (QuadraticInnerSpace A hA) := Matrix.toInnerProductSpace A hA.posSemidef
instance instFiniteDimensionalReal : FiniteDimensional ℝ (QuadraticInnerSpace A hA) :=
  inferInstanceAs (FiniteDimensional ℝ (ι → ℝ))

end QuadraticInnerSpace

end YauCounterexamples

open FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Real

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealPhaseLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise
abbrev PhaseSpace := EuclideanSpace ℝ (Fin 3)
abbrev ComplexPhaseMatrix := Matrix (Fin 3) (Fin 3) ℂ


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_ScalarAffineDetNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma scalarAffine_det_ne_zero (p : E) {r : ℝ} (hr : r ≠ 0) (x : E) :
    (fderiv ℝ (fun y : E => p + r • y) x).det ≠ 0 := by
  have hd : HasFDerivAt (fun y : E => p + r • y) (r • ContinuousLinearMap.id ℝ E) x := by
    simpa only [Pi.smul_apply, id_eq] using ((hasFDerivAt_id x).const_smul r).const_add p
  rw [hd.fderiv]
  change LinearMap.det (r • (LinearMap.id : E →ₗ[ℝ] E)) ≠ 0
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  exact pow_ne_zero _ hr

end YauCounterexamples


end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BoundedDegreeMonomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def SmoothJetZero (f : E → F) (N : ℕ) : Prop :=
  ∀ k < N, iteratedFDeriv ℝ k f 0 = 0

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ContDiffSmoothFiniteWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
abbrev NormalWaveSpace := EuclideanSpace ℝ (Fin 3)
abbrev NormalWaveParameter := NormalWaveSpace × (NormalWaveSpace →L[ℝ] NormalWaveSpace)


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

abbrev normalWaveEquiv : (Fin 3 → ℝ) ≃L[ℝ] NormalWaveSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_NodalMeasure_ExtrusionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace YauCounterexamples.SignTests

def oppositeSet {X M : Type*} (D : Set X) (a b : X → M) (f : M → ℝ) : Set X :=
  {x | x ∈ D ∧ f (a x) * f (b x) < 0}

def signMass {X M : Type*} [MeasurableSpace X] (μ : Measure X)
    (D : Set X) (a b : X → M) (f : M → ℝ) : ℝ≥0∞ :=
  μ (oppositeSet D a b f)

def swept {ι : Type*} [DecidableEq ι] (i : ι) (d : ℝ) (s : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {x | ∃ z ∈ s, ∃ t ∈ Icc 0 d, x = z - Pi.single i t}

@[simp] theorem swept_empty {ι : Type*} [DecidableEq ι] (i : ι) (d : ℝ) :
    swept i d (∅ : Set (ι → ℝ)) = ∅ := by ext x; simp [swept]

theorem swept_mono {ι : Type*} [DecidableEq ι] (i : ι) (d : ℝ) :
    Monotone (swept i d) := by
  rintro s t h x ⟨z, hz, r, hr, hx⟩
  exact ⟨z, h hz, r, hr, hx⟩

theorem swept_iUnion {ι J : Type*} [DecidableEq ι] (i : ι) (d : ℝ)
    (s : J → Set (ι → ℝ)) : swept i d (⋃ j, s j) = ⋃ j, swept i d (s j) := by
  ext x
  simp only [swept, mem_ofPred_eq, mem_iUnion]
  aesop

def sweptVolume {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (d : ℝ) :
    OuterMeasure (ι → ℝ) where
  measureOf s := volume (swept i d s)
  empty := by simp
  mono := fun h => measure_mono (swept_mono i d h)
  iUnion_nat := fun s _ => by rw [swept_iUnion]; exact measure_iUnion_le _

def signCertificate {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (P : J → Set (ι → ℝ)) (d : J → ℝ) (f : (ι → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ p, ∑ i, (ENNReal.ofReal (d p))⁻¹ *
    signMass volume {x | x ∈ P p ∧ x + Pi.single i (d p) ∈ P p}
      id (fun x => x + Pi.single i (d p)) f

end YauCounterexamples.SignTests
end

open Set Function MeasureTheory
open scoped ENNReal
namespace YauCounterexamples.SignTests
abbrev extrusionEquiv (n : ℕ) : (Fin (n+1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
def extrudeSet {n : ℕ} (P : Set (Fin n → ℝ)) : Set (Fin (n+1) → ℝ) :=
  extrusionEquiv n ⁻¹' (Ioo 0 1 ×ˢ P)
end YauCounterexamples.SignTests
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_TestDerivativeComm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev smoothScalarAlgebra (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Subalgebra ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  algebraMap_mem' c := by change ContDiff ℝ ∞ (fun _ : E => c); exact contDiff_const
  zero_mem' := by change ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    exact hf.add hg
  one_mem' := by change ContDiff ℝ ∞ (fun _ : E => (1 : ℝ)); exact contDiff_const
  mul_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    exact hf.mul hg

abbrev SmoothScalar (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  smoothScalarAlgebra E

namespace SmoothScalar
instance instCoeFunSubtypeForallRealMemSubalgebra : CoeFun (SmoothScalar E) (fun _ => E → ℝ) := ⟨Subtype.val⟩
lemma contDiff (f : SmoothScalar E) : ContDiff ℝ ∞ (f : E → ℝ) := f.property
variable (v : E)
def directional : SmoothScalar E →ₗ[ℝ] SmoothScalar E where
  toFun f := ⟨fun x => fderiv ℝ (f : E → ℝ) x v,
    by
      change ContDiff ℝ ∞ (fun x => fderiv ℝ (f : E → ℝ) x v)
      exact ((SmoothScalar.contDiff f).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const⟩
  map_add' f g := by
    apply Subtype.ext
    ext x
    simp only [Subalgebra.coe_add, Pi.add_apply,
      fderiv_add ((SmoothScalar.contDiff f).differentiable (by simp)).differentiableAt
        ((SmoothScalar.contDiff g).differentiable (by simp)).differentiableAt,
      add_apply]
  map_smul' c f := by
    apply Subtype.ext
    ext x
    simp only [Subalgebra.coe_smul, Pi.smul_apply,
      fderiv_const_smul ((SmoothScalar.contDiff f).differentiable (by simp)).differentiableAt,
      smul_apply, RingHom.id_apply]

@[simp] lemma directional_apply (f : SmoothScalar E) (x : E) :
    directional v f x = fderiv ℝ (f : E → ℝ) x v := rfl
end SmoothScalar

variable (K : Compacts E)
abbrev EllipticTest := 𝓓_{K}(E, ℝ)

end

open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_BilinearCoordinateMatrixPosDef
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix Manifold
open scoped Topology ContDiff Matrix.Norms.Elementwise
section ComplexProjection
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma clm_fderiv_apply (L : ℂ →L[ℝ] F) {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ (fun y => L (f y)) x v = L (fderiv ℝ f x v) := by
  erw [(L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv]
  rfl

lemma clm_second_fderiv (L : ℂ →L[ℝ] F) {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => L (f z)) y w) x v =
      L (fderiv ℝ (fun y => fderiv ℝ f y w) x v) := by
  have he : (fun y => fderiv ℝ (fun z => L (f z)) y w) =ᶠ[𝓝 x]
      (fun y => L (fderiv ℝ f y w)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact clm_fderiv_apply L (hy.differentiableAt (by norm_num)) w
  rw [he.fderiv_eq]
  apply clm_fderiv_apply
  exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
    (differentiableAt_const w)
end ComplexProjection
section ComplexMetric
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def complexLaplaceBeltrami (g : SmoothMetric E M) (u : M → ℂ) (x : M) : ℂ :=
  ⟨laplaceBeltrami g (Complex.re ∘ u) x, laplaceBeltrami g (Complex.im ∘ u) x⟩
end ComplexMetric
end


open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SourceSignBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter Manifold MeasureTheory BoxIntegral
open scoped Topology ContDiff
namespace YauCounterexamples

def sourceSignBox : Box (Fin 3) := Classical.choose exists_spherical_sign_box

def sourceProfileCoverage : Set NormalWaveSpace :=
  sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SobolevRepresentativeOrderCongr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open Set Function Filter
open scoped Topology ContDiff
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scalarAffine_hasFDerivAt (p : E) (r : ℝ) (x : E) :
    HasFDerivAt (fun y : E => p + r • y) (r • ContinuousLinearMap.id ℝ E) x := by
  simpa only [Pi.smul_apply, id_eq] using
    ((hasFDerivAt_id x).const_smul r).const_add p

lemma fderiv_scalarAffine (p : E) (r : ℝ) (u : E → ℂ) (x v : E)
    (hu : DifferentiableAt ℝ u (p + r • x)) :
    fderiv ℝ (fun y => u (p + r • y)) x v =
      (r : ℂ) * fderiv ℝ u (p + r • x) v := by
  change fderiv ℝ (u ∘ (fun y => p + r • y)) x v = _
  rw [(hu.hasFDerivAt.comp x (scalarAffine_hasFDerivAt p r x)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, Complex.real_smul]

lemma differentiable_directional {u : E → ℂ} (hu : ContDiff ℝ 2 u) (v : E) :
    Differentiable ℝ (fun x => fderiv ℝ u x v) :=
  (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero |>.clm_apply
    (differentiable_const v)

lemma second_fderiv_scalarAffine (p : E) (r : ℝ) {u : E → ℂ}
    (hu : ContDiff ℝ 2 u) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u (p + r • z)) y w) x v =
      (r : ℂ) ^ 2 * fderiv ℝ (fun y => fderiv ℝ u y w) (p + r • x) v := by
  have he : (fun y => fderiv ℝ (fun z => u (p + r • z)) y w) =
      fun y => (r : ℂ) * fderiv ℝ u (p + r • y) w := by
    funext y
    exact fderiv_scalarAffine p r u y w (hu.differentiable (by norm_num) _)
  rw [he]
  have hd := (differentiable_directional hu w) (p + r • x)
  have ha := scalarAffine_hasFDerivAt p r x
  erw [fderiv_const_mul (hd.comp x ha.differentiableAt) (r : ℂ),
    _root_.smul_apply, smul_eq_mul, fderiv_scalarAffine p r _ x v hd]
  ring

lemma second_fderiv_mul {u v : E → ℂ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (x a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u z * v z) y b) x a =
      u x * fderiv ℝ (fun y => fderiv ℝ v y b) x a +
      v x * fderiv ℝ (fun y => fderiv ℝ u y b) x a +
      fderiv ℝ u x a * fderiv ℝ v x b +
      fderiv ℝ u x b * fderiv ℝ v x a := by
  have hdu := hu.differentiable (by norm_num)
  have hdv := hv.differentiable (by norm_num)
  have hdu' := differentiable_directional hu b
  have hdv' := differentiable_directional hv b
  have he : (fun y => fderiv ℝ (fun z => u z * v z) y b) =
      fun y => u y * fderiv ℝ v y b + v y * fderiv ℝ u y b := by
    funext y
    rw [fderiv_fun_mul (hdu y) (hdv y)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [he]
  erw [fderiv_fun_add ((hdu x).mul (hdv' x)) ((hdv x).mul (hdu' x)),
    fderiv_fun_mul (hdu x) (hdv' x), fderiv_fun_mul (hdv x) (hdu' x)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

end Calculus


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma second_fderiv_add_at {u v : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) (a b : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => u z + v z) y b) x a =
      fderiv ℝ (fun y => fderiv ℝ u y b) x a +
        fderiv ℝ (fun y => fderiv ℝ v y b) x a := by
  have he : (fun y => fderiv ℝ (fun z => u z + v z) y b) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y b + fderiv ℝ v y b) := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y huy hvy
    rw [fderiv_fun_add (huy.differentiableAt (by norm_num)) (hvy.differentiableAt (by norm_num))]
    rfl
  rw [he.fderiv_eq]
  have hdu := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
    (differentiableAt_const b)
  have hdv := ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
    (differentiableAt_const b)
  rw [fderiv_fun_add hdu hdv]
  rfl


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma fderiv_inverseScalarAffine (p : E) (r : ℝ) {u : E → ℂ} (x v : E)
    (hu : DifferentiableAt ℝ u (r⁻¹ • (x - p))) :
    fderiv ℝ (fun y => u (r⁻¹ • (y - p))) x v =
      (r⁻¹ : ℝ) * fderiv ℝ u (r⁻¹ • (x - p)) v := by
  have ha : HasFDerivAt (fun y : E => r⁻¹ • (y - p))
      (r⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    ((hasFDerivAt_id x).sub_const p).const_smul r⁻¹
  change fderiv ℝ (u ∘ (fun y : E => r⁻¹ • (y - p))) x v = _
  rw [(hu.hasFDerivAt.comp x ha).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, Complex.real_smul]


end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped SchwartzMap BoundedContinuousFunction



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SecondDerivNonposLocalMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
namespace YauCounterexamples

lemma second_deriv_nonpos_of_localMax {f : ℝ → ℝ} {x : ℝ}
    (hf : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hp hf.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hf, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hz : deriv (deriv f) x = 0 := by
    simpa only [deriv_const', deriv_const] using he.deriv.deriv_eq
  linarith

lemma matrix_contraction_nonpos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (H : Matrix ι ι ℝ)
    (hH : ∀ v : ι → ℝ, ∑ i, ∑ j, H i j * v i * v j ≤ 0) :
    ∑ i, ∑ j, A i j * H i j ≤ 0 := by
  let U : Matrix ι ι ℝ := hA.isHermitian.eigenvectorUnitary
  have hspec (i j : ι) : A i j =
      ∑ k, hA.isHermitian.eigenvalues k * U i k * U j k := by
    conv_lhs => rw [hA.isHermitian.spectral_theorem]
    rw [conjStarAlgAut_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
    change (∑ k, U i k * hA.isHermitian.eigenvalues k * U j k) = _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [U]
    ring
  simp_rw [hspec, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ k, ∑ j, hA.isHermitian.eigenvalues k * U i k * U j k * H i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, hA.isHermitian.eigenvalues k * U i k * U j k * H i j :=
      Finset.sum_comm
    _ = ∑ k, hA.isHermitian.eigenvalues k *
        (∑ i, ∑ j, H i j * U i k * U j k) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 0 := Finset.sum_nonpos fun k _ =>
      mul_nonpos_of_nonneg_of_nonpos (hA.eigenvalues_nonneg k) (hH (fun i => U i k))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_fderiv_diag_nonpos {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) (v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x v ≤ 0 := by
  let line : ℝ → E := fun t => x + t • v
  have hl (t : ℝ) : HasDerivAt line v t := by
    simpa [line] using (hasDerivAt_id t).smul_const v |>.const_add x
  have h0 : line 0 = x := by simp [line]
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he : (fun t => deriv (f ∘ line) t) =ᶠ[𝓝 0]
      fun t => fderiv ℝ f (line t) v := by
    have hfd := hf.eventually (by norm_num)
    have hline : Tendsto line (𝓝 0) (𝓝 x) := by
      have hc := (hl 0).continuousAt
      rwa [ContinuousAt, h0] at hc
    filter_upwards [hline.eventually hfd] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  have h2 : deriv (deriv (f ∘ line)) 0 =
      fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
    rw [he.deriv_eq]
    have hd : HasFDerivAt (fun y => fderiv ℝ f y v)
        (fderiv ℝ (fun y => fderiv ℝ f y v) x) (line 0) := by
      rw [h0]
      exact (hf'.clm_apply (differentiableAt_const v)).hasFDerivAt
    exact (hd.comp_hasDerivAt 0 (hl 0)).deriv
  rw [← h2]
  apply second_deriv_nonpos_of_localMax
  · have hm' : IsLocalMax f (line 0) := by simpa [line] using hm
    exact hm'.comp_continuous (hl 0).continuousAt
  · have hc : ContinuousAt f (line 0) := by rw [h0]; exact hf.continuousAt
    exact hc.comp (hl 0).continuousAt

lemma localMax_hessian_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x)
    (b : ι → E) {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fun y => fderiv ℝ f y (b j)) x (b i) ≤ 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  apply matrix_contraction_nonpos hA
  intro v
  have hq := second_fderiv_diag_nonpos hf hm (∑ i, v i • b i)
  simp only [fderiv_clm_apply hd (differentiableAt_const _), fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] at hq ⊢
  convert hq using 1
  all_goals try with_reducible_and_instances rfl
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ScalarCompDirectional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_neg (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    laplaceBeltrami g (-u) x = -laplaceBeltrami g u x := by
  unfold laplaceBeltrami
  simp only [Function.comp_def, Pi.neg_apply, fderiv_fun_neg, _root_.neg_apply,
    mul_neg, Finset.sum_neg_distrib]


end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
omit [FiniteDimensional ℝ E] in
lemma contDiffAt_inChart_C2 {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (p : M) {y : E} (hy : y ∈ (chartAt E p).target) :
    ContDiffAt ℝ 2 (u ∘ (chartAt E p).symm) y :=
  contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp y
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hy))


open Set Function Filter
open scoped Topology ContDiff

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_complex_inChart {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u) (p : M) {x : M}
    (hx : x ∈ (chartAt E p).source) :
    ContDiffAt ℝ 2 (u ∘ (chartAt E p).symm) ((chartAt E p) x) :=
  contMDiffAt_iff_contDiffAt.mp (hu.contMDiffAt.comp _
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)
      ((chartAt E p).map_source hx)))


end

open Set Filter Manifold
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ChartDerivativeNeZeroTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
section SubspaceBilinear
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local instance subspace_smulCommClass (S : Submodule ℝ X) : SMulCommClass ℝ ℝ S :=
  ⟨fun a b c => by simp only [smul_smul, mul_comm]⟩
local instance subspace_isScalarTower_r3c601d_1 (S : Submodule ℝ X) : IsScalarTower ℝ ℝ S :=
  ⟨fun a b c => mul_smul a b c⟩
def restrictBilinear (p : X →L[ℝ] X →L[ℝ] X) (S : Submodule ℝ X)
    (hp : ∀ u v : S, p u v ∈ S) : S →L[ℝ] S →L[ℝ] S :=
  (LinearMap.mk₂ ℝ (fun (u v : S) => (⟨p u v, hp u v⟩ : S))
    (fun u v w => by apply Subtype.ext; exact congrArg (fun f : X →L[ℝ] X => f (w : X)) (map_add p (u : X) (v : X)))
    (fun c u v => by apply Subtype.ext; exact congrArg (fun f : X →L[ℝ] X => f (v : X)) (map_smul p c (u : X)))
    (fun u v w => by apply Subtype.ext; exact map_add (p (u : X)) (v : X) (w : X))
    (fun c u v => by apply Subtype.ext; exact map_smul (p (u : X)) c (v : X))).mkContinuous₂
      ‖p‖ (fun u v => p.le_opNorm₂ u v)
end SubspaceBilinear
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [CompactSpace M] in
lemma laplaceBeltrami_zero (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun _ => 0) x = 0 := by
  simp [laplaceBeltrami, Function.comp_def]

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def boundedDivergence (p : X →L[ℝ] X →L[ℝ] X) (q : Y →L[ℝ] Y →L[ℝ] Y)
    (I L : X →L[ℝ] Y) (b : X) : X →L[ℝ] Y :=
  (1 / 2 : ℝ) • (L.comp (p b) + (q (I b)).comp L - (q (L b)).comp I)

end

open Set Filter Function Manifold
open scoped Topology ContDiff BoundedContinuousFunction

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PinningTensorSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

abbrev RealSmoothFunctions (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] := C^∞⟮𝓘(ℝ,E),M;𝓘(ℝ,ℝ),ℝ⟯

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Spectrum_ContinuousEigenpairLinearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
namespace PositivePairing

abbrev EigenpairParameters := (X →L[ℝ] X) × (ℝ × X)

end PositivePairing

end

open Set Filter Module
open scoped Topology
open Set Filter Function
open scoped Topology


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_SphericalPinFormNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal
def SphericalSignAbove (u : Sphere 3 → ℝ) (L : ℝ) : Prop :=
  ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧
    ∃ d : {J : Box (Fin 3) // J ∈ partition.boxes} → ℝ, (∀ j, 0 < d j) ∧
      ENNReal.ofReal L < SignTests.signCertificate (fun j => Box.Ioo j.val) d
        ((u ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv)
def SphericalRegular (u : Sphere 3 → ℝ) : Prop :=
  ∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt (Euclidean 3) q).symm)
    ((chartAt (Euclidean 3) q) q) ≠ 0
end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral
open scoped Topology ContDiff Distributions ENNReal NNReal

end YauCounterexamples
end

end OAI
end


