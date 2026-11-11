-- Prove2me | Definitions.Def_Q227CKS002
-- name    : Q227CKS002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:47:49.512335+00:00
-- url     : https://prove2.me/theorems/2ceaa425-9575-4777-bb0b-1ea678ad29a6
-- title:
--   Definitions bundle Q227CKS002 of the split of OpenAI, Area-controlled end replacement and the Bondi Penrose inequality in the CKS class
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CKSMain.schwarzschild_equality_examples`, carved from OpenAI's openai/math development (OpenAI, *Area-controlled end replacement and the Bondi Penrose inequality in the CKS class*, OpenAI Math Release, September 27, 2026, result family 260, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 159 declarations of OpenAI's Lean: 46 definitions, 3 inductive types or structures and 110 theorems. The definitions and types are `OAI.CKSMain.SchwarzschildAttainment`, `OAI.CKSMain.horizonNormal`, `OAI.CKSMain.schwarzschildBoundary`, `OAI.CKSMixedGeometry.FiniteLogDecay`, `OAI.CKSMixedGeometry.LogJetBound`, `OAI.CKSMixedGeometry.inverseChartDerivative`, `OAI.CKSRealizedRound.lapseJet`, `OAI.CKSRealizedRound.massJet`, `OAI.CKSRealizedRound.metric`, `OAI.CKSRealizedRound.metricJet`, `OAI.CKSRealizedRound.outerMetric`, `OAI.CKSRealizedRound.roundTensor`, `OAI.CKSRealizedRound.tensor`, `OAI.CKSRealizedRound.tensorJet`, `OAI.CKSSchwarzschild.InteriorImmersion`, `OAI.CKSSchwarzschild.IntrinsicInteriorImmersion.coordinateImmersion`, `OAI.CKSSchwarzschild.SchwarzschildEqualityExample`, `OAI.CKSSchwarzschild.boundaryScaledMetric`, `OAI.CKSSchwarzschild.boundarySphere`, `OAI.CKSSchwarzschild.cksData`, `OAI.CKSSchwarzschild.euclideanMetric`, `OAI.CKSSchwarzschild.intrinsicCoordinateMap`, `OAI.CKSSchwarzschild.intrinsicCoordinateNormal`, `OAI.CKSSchwarzschild.intrinsicSurfaceMeanCurvature`, `OAI.CKSSchwarzschild.intrinsicSurfaceTensorTrace`, `OAI.CKSSchwarzschild.logRadius`, `OAI.CKSSchwarzschild.parameterMeanCurvature`, `OAI.CKSSchwarzschild.parameterSecondForm`, `OAI.CKSSchwarzschild.parameterTensorTrace`, `OAI.CKSSchwarzschild.positionTangentEquiv`, `OAI.CKSSchwarzschild.radialNormal`, `OAI.CKSSchwarzschild.schwarzschildEqualityCotangentTopology`, `OAI.CKSSchwarzschild.sphereCone`, `OAI.CKSSchwarzschild.sphereConeDeriv`, `OAI.CKSSchwarzschild.sphereDerivative`, `OAI.CKSSchwarzschild.sphereMeanCurvature`, `OAI.CKSSchwarzschild.sphereMetric`, `OAI.CKSSchwarzschild.sphereParam`, `OAI.CKSSchwarzschild.sphereParamDeriv`, `OAI.CKSSchwarzschild.sphereTensorTrace` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Relativity_CKS_BoundaryBridge`, `Relativity_CKS_ConstructedOuterMetric`, `Relativity_CKS_LogPhysicalCoefficients`, `Relativity_CKS_LogRadiusJets`, `Relativity_CKS_MainDefinitions`, `Relativity_CKS_ScaledPullback`, `Relativity_CKS_SchwarzschildAreaDefinitions`, `Relativity_CKS_SchwarzschildBoundary`, `Relativity_CKS_SchwarzschildCKS`, `Relativity_CKS_SchwarzschildCKSAlgebra`, `Relativity_CKS_SchwarzschildCKSDecay`, `Relativity_CKS_SchwarzschildCharts`, `Relativity_CKS_SchwarzschildCompleteness`, `Relativity_CKS_SchwarzschildConnection`, `Relativity_CKS_SchwarzschildConnectionDefinitions`, `Relativity_CKS_SchwarzschildEqualityDefinitions`, `Relativity_CKS_SchwarzschildHorizon`, `Relativity_CKS_SchwarzschildHorizonExclusionDefinitions`, `Relativity_CKS_SchwarzschildIntrinsicEquality`, `Relativity_CKS_SchwarzschildIntrinsicHorizonDefinitions`, `Relativity_CKS_SchwarzschildOrientability`, `Relativity_CKS_SchwarzschildProfile`, `Relativity_CKS_SchwarzschildRadialDecay`, `Relativity_CKS_SchwarzschildRoundMetric`, `Relativity_CKS_SmoothOuterDEC`, `Relativity_CKS_SphereConeChart`, `Relativity_CKS_SphereConeMeasure`, `Relativity_CKS_SurfaceScaling`.
--
--   **Imports.** It imports the published bundles `Def_CKSBondiPenrose` and `Def_CKSBondiPenrose_002`; the bundles `Q227CKS000` and `Q227CKS001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q227CKS005` and `Q227CKS006`; the statements `OAI.CKSSchwarzschild.numerical_equality`, `OAI.CKSSchwarzschild.radial_round_vacuum` and `OAI_CKSSchwarzschild_schwarzschild_equality_example`; the proofs of `OAI.CKSMain.schwarzschild_equality_examples`, `OAI_CKSSchwarzschild_horizon_regular_graph`, `OAI.CKSSchwarzschild.numerical_equality`, `OAI.CKSSchwarzschild.physical_DEC`, `OAI.CKSSchwarzschild.radial_round_vacuum`, `OAI.CKSSchwarzschild.source_minimum_area` and `OAI_CKSSchwarzschild_spherical_vacuum_regular`.
-- source:
--   OpenAI, Area-controlled end replacement and the Bondi Penrose inequality in the CKS class, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 260; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSBondiPenrose_002
import Definitions.Def_Q227CKS000
import Definitions.Def_Q227CKS001

section
-- module Solutions.Q227_CKS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SmoothOuterDEC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound
open scoped Topology ContDiff

def lapseJet (u : Point → ℝ) (x : Point) : LapseJet where
  u := u x
  ur := D (basis 0) u x
  ut := D (basis 1) u x
  up := D (basis 2) u x
  urr := D (basis 0) (D (basis 0) u) x
  urt := D (basis 1) (D (basis 0) u) x
  urp := D (basis 2) (D (basis 0) u) x
  utt := D (basis 1) (D (basis 1) u) x
  utp := D (basis 2) (D (basis 1) u) x
  upp := D (basis 2) (D (basis 2) u) x

def metric (u : Point → ℝ) (x : Point) : Mat :=
  Matrix.diagonal ![1 / u x ^ 2, x 0 ^ 2, x 0 ^ 2 * Real.sin (x 1) ^ 2]

def metricJet (u : Point → ℝ) (x : Point) : MetricJet where
  inv := (metric u x)⁻¹
  d := fun a i j => D (basis a) (fun y => metric u y i j) x
  dd := fun a b i j => D (basis a) (D (basis b) (fun y => metric u y i j)) x

end
end CKSRealizedRound

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound Filter
open scoped Topology ContDiff

def massJet (F : Point → ℝ) (x : Point) : MassJet where
  F := F x
  Fr := D (basis 0) F x
  Ft := D (basis 1) F x
  Fp := D (basis 2) F x
  Frr := D (basis 0) (D (basis 0) F) x
  Frt := D (basis 1) (D (basis 0) F) x
  Frp := D (basis 2) (D (basis 0) F) x
  Ftt := D (basis 1) (D (basis 1) F) x
  Ftp := D (basis 2) (D (basis 1) F) x
  Fpp := D (basis 2) (D (basis 2) F) x

end
end CKSRealizedRound

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound
open scoped Topology ContDiff

def tensor (u : Point → ℝ) (v : ℝ → ℝ) (L a b : Point → ℝ) (x : Point) : Mat :=
  !![L x / u x ^ 2, 0, 0;
    0, radial v x * x 0 + a x, b x;
    0, b x, (radial v x * x 0 - a x) * Real.sin (x 1) ^ 2]

def tensorJet (u : Point → ℝ) (v : ℝ → ℝ) (L a b : Point → ℝ) (x : Point) : TensorJet where
  val := tensor u v L a b x
  d := fun d i j => D (basis d) (fun y => tensor u v L a b y i j) x

def roundTensor (v : ℝ → ℝ) (L a b : Point → ℝ) (x : Point) : RoundTensor where
  v := v (x 0)
  vp := deriv v (x 0)
  L := L x
  Lr := D (basis 0) L x
  Lt := D (basis 1) L x
  Lp := D (basis 2) L x
  a := a x
  ar := D (basis 0) a x
  aθ := D (basis 1) a x
  ap := D (basis 2) a x
  b := b x
  br := D (basis 0) b x
  bt := D (basis 1) b x
  bp := D (basis 2) b x

end
end CKSRealizedRound

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound CKSLocalBending
open scoped Topology ContDiff

def outerMetric (F : Point → ℝ) (v : ℝ → ℝ) := metric (lapse F v)

end
end CKSRealizedRound

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_LogRadiusJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_pos (n : ℝ) (x : Point) : 0 < radiusPower n x := Real.exp_pos _
lemma radiusPower_smooth (n : ℝ) : ContDiff ℝ ∞ (radiusPower n) := by unfold radiusPower; fun_prop
lemma radiusPower_diff (n : ℝ) (m : ℕ) (x : Point) : ContDiffAt ℝ m (radiusPower n) x :=
  ((radiusPower_smooth n).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt
lemma D_radiusPower (n : ℝ) (a : I) :
    D (basis a) (radiusPower n) = fun x => (n*basis a 0)*radiusPower n x := by
  funext x
  have hc : DifferentiableAt ℝ (fun y : Point => y 0) x := by fun_prop
  unfold radiusPower
  rw [D_comp_real (basis a) (Real.differentiableAt_exp) (hc.const_mul n),
    Real.deriv_exp,D_const_mul (basis a) n hc]
  change Real.exp (n*x 0) * (n*D (basis a) (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ) x) = _
  rw [D_clm]
  simp only [ContinuousLinearMap.proj_apply]
  ring

end
end CKSMixedGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_LogPhysicalCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_neg_nat (n : ℕ) (x : Point) : radiusPower (-(n:ℝ)) x = 1/Real.exp (x 0)^n := by
  rw [radiusPower,neg_mul,Real.exp_neg,Real.exp_nat_mul,one_div]

end
end CKSMixedGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_ScaledPullback
attribute [-simp] _root_.OAI.CKSAngularSlice.injection_succ _root_.OAI.CKSAngularSlice.injection_zero _root_.OAI.CKSAngularSlice.slice_zero _root_.OAI.CKSLorentz.angularProjection_inverseLogRadiusChart _root_.OAI.CKSLorentz.angularProjection_logRadiusChart _root_.OAI.CKSLorentz.polarCartesianChart_coe _root_.OAI.CKSMixedGeometry.angularProjection_radialLogChart _root_.OAI.CKSMixedGeometry.backwardScaledIter_cons _root_.OAI.CKSMixedGeometry.backwardScaledIter_nil _root_.OAI.CKSMixedGeometry.logRadiusChart_slice _root_.OAI.CKSMixedGeometry.radialEigenvalue_cons _root_.OAI.CKSMixedGeometry.radialEigenvalue_nil _root_.OAI.CKSMixedGeometry.radialLogChart_logRadiusChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal

lemma logRadiusChart_smooth : ContDiff ℝ ∞ logRadiusChart := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 0
  · simp only [logRadiusChart,hi,ite_eq_left]; fun_prop
  · simp only [logRadiusChart,hi,ite_false, if_false]; fun_prop

lemma logRadiusChart_hasFDerivAt (x : Point) : HasFDerivAt logRadiusChart (chartDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [logRadiusChart,chartDerivative,Function.comp_def] using
      (Real.hasDerivAt_exp (x 0)).comp_hasFDerivAt x (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).hasFDerivAt
  · simp only [logRadiusChart,hi,ite_false, if_false]
    change HasFDerivAt (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) (ContinuousLinearMap.proj i) x
    exact (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt

lemma chartDerivative_basis (a : I) (x : Point) :
    chartDerivative x (basis a) = radialFactor a (logRadiusChart x) • basis a := by
  ext i
  by_cases ha : a = 0 <;> by_cases hi : i = 0
  · subst a; subst i; simp [chartDerivative,radialFactor,logRadiusChart,basis]
  · subst a; simp [chartDerivative,radialFactor,logRadiusChart,basis,hi]
  · subst i; simp [chartDerivative,radialFactor,basis,ha,Ne.symm ha]
  · simp [chartDerivative,radialFactor,basis,ha,hi]

lemma D_pullback (a : I) {f : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (logRadiusChart x)) :
    D (basis a) (fun y => f (logRadiusChart y)) x = scaledD a f (logRadiusChart x) := by
  unfold D
  change (fderiv ℝ (f ∘ logRadiusChart) x) (basis a) = _
  rw [fderiv_comp x hf (logRadiusChart_hasFDerivAt x).differentiableAt,
    (logRadiusChart_hasFDerivAt x).fderiv]
  simp only [ContinuousLinearMap.comp_apply,chartDerivative_basis,map_smul,smul_eq_mul,scaledD,D]

lemma scaledIter_contDiffAt (l : List I) (m : ℕ) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ (↑(m+l.length) : ℕ∞ω) f x) : ContDiffAt ℝ m (scaledIter l f) x := by
  induction l generalizing m with
  | nil => simpa only [List.length_nil,add_zero,scaledIter] using hf
  | cons a l ih =>
    have heq : m+(a::l).length = (m+1)+l.length := by simp; omega
    rw [heq] at hf
    exact ((radialFactor_smooth a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt.mul
      (contDiffAt_D (ih (m+1) hf) (m := m) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (basis a))

lemma coordinateIter_pullback (l : List I) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ l.length f (logRadiusChart x)) :
    coordinateIter l (fun y => f (logRadiusChart y)) x = scaledIter l f (logRadiusChart x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    have heq : coordinateIter l (fun y => f (logRadiusChart y)) =ᶠ[𝓝 x]
        (fun y => scaledIter l f (logRadiusChart y)) := by
      have hf' : ContDiffAt ℝ l.length f (logRadiusChart x) := hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      have he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ l.length f (logRadiusChart y) :=
        (logRadiusChart_smooth.continuous.continuousAt.tendsto).eventually (hf'.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      filter_upwards [he] with y hy
      exact ih hy
    change D (basis a) (coordinateIter l (fun y => f (logRadiusChart y))) x = _
    rw [D_congr heq]
    have hf' : ContDiffAt ℝ (↑(1+l.length) : ℕ∞ω) f (logRadiusChart x) := by
      simpa only [List.length_cons,Nat.add_comm] using hf
    exact D_pullback a ((scaledIter_contDiffAt l 1 hf').differentiableAt (by norm_num))

end
end CKSMixedGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_ConstructedOuterMetric
attribute [-simp] _root_.OAI.CKSLorentz.polarCartesianChart_coe _root_.OAI.CKSMixedGeometry.logRadiusChart_slice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSSphericalHarmonics CKSInducedSphere
open scoped Topology Matrix

 def sphericalAngularMetric (x : CKSRealizedRound.Point) : CKSAngularGeometry.Mat :=
  Matrix.diagonal ![1, Real.sin (x 1)^2]

end
end CKSSphericalChart

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma sum_coordinate_basis (v : Point) : ∑ k : I, v k • basis k = v := by
  ext k
  simp [basis, Finset.sum_apply, Pi.single_apply]

lemma multilinear_norm_of_components {n : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Point) ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ a : Fin n → I, ‖M (fun i => basis (a i))‖ ≤ C) :
    ‖M‖ ≤ 3^n * C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he : M v = ∑ a : Fin n → I, (∏ i, v i (a i)) * M (fun i => basis (a i)) := by
    calc M v = M (fun i => ∑ k : I, v i k • basis k) := by
          congr 1; funext i; exact (sum_coordinate_basis _).symm
         _ = ∑ a : Fin n → I, M (fun i => v i (a i) • basis (a i)) := M.map_sum _
         _ = _ := by simp only [M.map_smul_univ, smul_eq_mul]
  rw [he]
  calc ‖∑ a : Fin n → I, (∏ i, v i (a i)) * M (fun i => basis (a i))‖
      ≤ ∑ a : Fin n → I, ‖(∏ i, v i (a i)) * M (fun i => basis (a i))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin n → I, (∏ i, ‖v i‖) * C := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, norm_prod]
      apply mul_le_mul
      · apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
        intro i _
        exact norm_le_pi_norm (v i) (a i)
      · exact hb a
      · exact norm_nonneg _
      · positivity
    _ = 3^n * C * ∏ i, ‖v i‖ := by simp [mul_comm, mul_left_comm, mul_assoc]

lemma iteratedFDeriv_basis_ofFn (n : ℕ) (a : Fin n → I)
    {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ n f x) :
    iteratedFDeriv ℝ n f x (fun i => basis (a i)) = coordinateIter (List.ofFn a) f x := by
  induction n generalizing x with
  | zero => simp [coordinateIter]
  | succ n ih =>
    have hd := hf.differentiableAt_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n)
    rw [hd.iteratedFDeriv_succ_apply_left']
    have he : (fun y => iteratedFDeriv ℝ n f y (Fin.tail (fun i => basis (a i)))) =ᶠ[𝓝 x]
        coordinateIter (List.ofFn (Fin.tail a)) f := by
      have hfn : ContDiffAt ℝ n f x := hf.of_le (by exact_mod_cast Nat.le_succ n)
      filter_upwards [hfn.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)] with y hy
      exact ih (Fin.tail a) hy
    have hlist : List.ofFn a = a 0 :: List.ofFn (Fin.tail a) := by
      conv_lhs => rw [← Fin.cons_self_tail a]
      exact List.ofFn_cons _ _
    rw [hlist]
    change D (basis (a 0)) (fun y => iteratedFDeriv ℝ n f y (Fin.tail (fun i => basis (a i)))) x = _
    exact D_congr he _

lemma coordinateIter_le_iteratedFDeriv (l : List I)
    {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ l.length f x) :
    |coordinateIter l f x| ≤ ‖iteratedFDeriv ℝ l.length f x‖ := by
  have he := iteratedFDeriv_basis_ofFn l.length l.get hf
  rw [List.ofFn_get] at he
  rw [← he, ← Real.norm_eq_abs]
  have h := (iteratedFDeriv ℝ l.length f x).le_opNorm (fun i => basis (l.get i))
  have hn (i : Fin l.length) : ‖basis (l.get i)‖ = 1 := by simp [basis, Pi.norm_single]
  simpa only [hn, Finset.prod_const_one, mul_one] using h

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma inverseLogRadiusChart_smooth : ContDiff ℝ ∞ inverseLogRadiusChart := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i=0 <;> simp only [inverseLogRadiusChart,hi,ite_true, if_true,ite_false, if_false] <;> fun_prop

lemma backwardFactor_smooth (a : I) : ContDiff ℝ ∞ (backwardFactor a) := by
  change ContDiff ℝ ∞ (fun y : Point => if a=0 then -y 0 else 1)
  split_ifs <;> fun_prop

def inverseChartDerivative (x : Point) : Point →L[ℝ] Point :=
  letI := pointDimension_neZero
  letI := coordinate_smulCommClass
  letI := coordinate_continuousConstSMul
  ContinuousLinearMap.pi (fun i => if i=0 then (-Real.exp (-x 0)) • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma inverseLogRadiusChart_hasFDerivAt (x : Point) :
    HasFDerivAt inverseLogRadiusChart (inverseChartDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i
    have h := (Real.hasDerivAt_exp (-x 0)).comp_hasFDerivAt x
      ((ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).hasFDerivAt.neg)
    change HasFDerivAt (fun y : Point => Real.exp (-y 0))
      ((-Real.exp (-x 0)) • ContinuousLinearMap.proj 0) x
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (ext y <;> simp)
  · simp only [inverseLogRadiusChart,hi,ite_false, if_false]
    change HasFDerivAt (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) (ContinuousLinearMap.proj i) x
    exact (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt

lemma inverseChartDerivative_basis (a : I) (x : Point) :
    inverseChartDerivative x (basis a) = backwardFactor a (inverseLogRadiusChart x) • basis a := by
  ext i
  by_cases ha : a=0 <;> by_cases hi : i=0
  · subst a; subst i; simp [inverseChartDerivative,backwardFactor,inverseLogRadiusChart,basis]
  · subst a; simp [inverseChartDerivative,backwardFactor,inverseLogRadiusChart,basis,hi]
  · subst i; simp [inverseChartDerivative,backwardFactor,basis,ha,Ne.symm ha]
  · simp [inverseChartDerivative,backwardFactor,basis,ha,hi]

lemma D_inverse_pullback (a : I) {f : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (inverseLogRadiusChart x)) :
    D (basis a) (fun y => f (inverseLogRadiusChart y)) x =
      backwardScaledD a f (inverseLogRadiusChart x) := by
  unfold D
  change (fderiv ℝ (f ∘ inverseLogRadiusChart) x) (basis a) = _
  rw [fderiv_comp x hf (inverseLogRadiusChart_hasFDerivAt x).differentiableAt,
    (inverseLogRadiusChart_hasFDerivAt x).fderiv]
  simp only [ContinuousLinearMap.comp_apply,inverseChartDerivative_basis,map_smul,
    smul_eq_mul,backwardScaledD,D]

lemma backwardScaledIter_contDiffAt (l : List I) (m : ℕ) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ (↑(m+l.length) : ℕ∞ω) f x) :
    ContDiffAt ℝ m (backwardScaledIter l f) x := by
  induction l generalizing m with
  | nil => simpa only [List.length_nil,add_zero,backwardScaledIter_nil] using hf
  | cons a l ih =>
    have heq : m+(a::l).length = (m+1)+l.length := by simp; omega
    rw [heq] at hf
    exact ((backwardFactor_smooth a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt.mul
      (contDiffAt_D (ih (m+1) hf) (m := m) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (basis a))

lemma coordinateIter_inverse_pullback (l : List I) {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ l.length f (inverseLogRadiusChart x)) :
    coordinateIter l (fun y => f (inverseLogRadiusChart y)) x =
      backwardScaledIter l f (inverseLogRadiusChart x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    have heq : coordinateIter l (fun y => f (inverseLogRadiusChart y)) =ᶠ[𝓝 x]
        (fun y => backwardScaledIter l f (inverseLogRadiusChart y)) := by
      have hf' : ContDiffAt ℝ l.length f (inverseLogRadiusChart x) := hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      have he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ l.length f (inverseLogRadiusChart y) :=
        inverseLogRadiusChart_smooth.continuous.continuousAt.eventually (hf'.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      filter_upwards [he] with y hy
      exact ih hy
    change D (basis a) (coordinateIter l (fun y => f (inverseLogRadiusChart y))) x = _
    rw [D_congr heq]
    have hf' : ContDiffAt ℝ (↑(1+l.length) : ℕ∞ω) f (inverseLogRadiusChart x) := by
      simpa only [List.length_cons,Nat.add_comm] using hf
    exact D_inverse_pullback a ((backwardScaledIter_contDiffAt l 1 hf').differentiableAt (by norm_num))

theorem compactified_scalar_uniform_jets (n : ℕ) {K : Set Point} (hK : IsCompact K)
    {f : Point → ℝ} (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      ‖iteratedFDeriv ℝ n (fun y => f (inverseLogRadiusChart y)) x‖ ≤ C := by
  let Q : Point → (Fin n → I) → ℝ := fun z a => backwardScaledIter (List.ofFn a) f z
  have hQ : ContinuousOn Q K := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro a
    exact (backwardScaledIter_contDiffAt (List.ofFn a) 0
      ((hf z hz).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).continuousAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hQ
  refine ⟨3^n * max 0 C,by positivity,?_⟩
  intro x hx
  apply multilinear_norm_of_components _ (le_max_left _ _)
  intro a
  have hfn : ContDiffAt ℝ n f (inverseLogRadiusChart x) :=
    (hf _ hx).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hcomp : ContDiffAt ℝ n (fun y => f (inverseLogRadiusChart y)) x :=
    hfn.comp x (inverseLogRadiusChart_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  rw [iteratedFDeriv_basis_ofFn n a hcomp]
  rw [coordinateIter_inverse_pullback (f := f) (x := x) (List.ofFn a) (by simpa using hfn)]
  exact (norm_le_pi_norm (Q (inverseLogRadiusChart x)) a).trans ((hC _ hx).trans (le_max_right _ _))

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

def LogJetBound (f : Point → ℝ) (j : ℕ) (q C : ℝ) (x : Point) : Prop :=
  ∀ n : ℕ, n ≤ j → ‖iteratedFDeriv ℝ n f x‖ ≤ C * radiusPower (-q) x

lemma local_norm_iteratedFDeriv_mul {f g : Point → ℝ} {n : ℕ} {x : Point}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by
  obtain ⟨s,hs,hsopen,hxs⟩ := mem_nhds_iff.mp
    ((hf.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).and (hg.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))
  have hfs : ContDiffOn ℝ n f s := fun y hy => (hs hy).1.contDiffWithinAt
  have hgs : ContDiffOn ℝ n g s := fun y hy => (hs hy).2.contDiffWithinAt
  have h := norm_iteratedFDerivWithin_mul_le hfs hgs hsopen.uniqueDiffOn hxs (le_refl (n : ℕ∞ω))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn (hf.mul hg) hxs] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn
      (hf.of_le (by exact_mod_cast hi')) hxs,
    iteratedFDerivWithin_eq_iteratedFDeriv hsopen.uniqueDiffOn
      (hg.of_le (by exact_mod_cast Nat.sub_le n i)) hxs]

lemma LogJetBound.mul {f g : Point → ℝ} {x : Point} {j : ℕ} {q r C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hf : ContDiffAt ℝ j f x) (hg : ContDiffAt ℝ j g x)
    (hb : LogJetBound f j q C x) (hc : LogJetBound g j r D x) :
    LogJetBound (fun y => f y * g y) j (q+r) (2^j*C*D) x := by
  intro n hn
  have hfn : ContDiffAt ℝ n f x := hf.of_le (by exact_mod_cast hn)
  have hgn : ContDiffAt ℝ n g x := hg.of_le (by exact_mod_cast hn)
  calc
    ‖iteratedFDeriv ℝ n (fun y => f y*g y) x‖ ≤
        ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ :=
      local_norm_iteratedFDeriv_mul hfn hgn
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
          (C * radiusPower (-q) x)*(D * radiusPower (-r) x) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i (hi'.trans hn)) (by positivity))
        (hc (n-i) ((Nat.sub_le n i).trans hn)) (norm_nonneg _)
        (mul_nonneg (by positivity) (mul_nonneg hC (radiusPower_pos _ _).le))
    _ = 2^n*C*D * radiusPower (-(q+r)) x := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hsum : ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) = 2^n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [hsum]
      have he : radiusPower (-(q+r)) x = radiusPower (-q) x * radiusPower (-r) x := by
        simp only [radiusPower,neg_add,add_mul,Real.exp_add]
      rw [he]
      ring
    _ ≤ 2^j*C*D * radiusPower (-(q+r)) x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn) hC) hD)
        (radiusPower_pos _ _).le

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma coordinateIter_radiusPower (t : ℝ) (l : List I) :
    coordinateIter l (radiusPower t) = fun x => radialEigenvalue t l * radiusPower t x := by
  induction l with
  | nil => simp [coordinateIter,radialEigenvalue]
  | cons a l ih =>
    funext x
    simp only [coordinateIter,ih]
    rw [D_const_mul (basis a) _ ((radiusPower_smooth t).contDiffAt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
    simp only [D_radiusPower,radialEigenvalue_cons]
    ring

lemma abs_radialEigenvalue (t : ℝ) (l : List I) :
    |radialEigenvalue t l| ≤ |t|^l.length := by
  induction l with
  | nil => simp [radialEigenvalue]
  | cons a l ih =>
    simp only [radialEigenvalue_cons,abs_mul,List.length_cons,pow_succ]
    calc |t| * |basis a 0| * |radialEigenvalue t l|
        ≤ (|t| *1) * |t|^l.length :=
          mul_le_mul (mul_le_mul_of_nonneg_left (basis_rad_abs a) (abs_nonneg t)) ih
            (abs_nonneg _) (by positivity)
      _ = |t|^l.length * |t| := by ring

lemma radiusPower_logJet (j : ℕ) (q : ℝ) (x : Point) :
    LogJetBound (radiusPower (-q)) j q (3^j * (max 1 |q|)^j) x := by
  intro n hn
  have hc : 0 ≤ |q|^n * radiusPower (-q) x :=
    mul_nonneg (pow_nonneg (abs_nonneg q) _) (radiusPower_pos _ _).le
  have hb := multilinear_norm_of_components (iteratedFDeriv ℝ n (radiusPower (-q)) x) hc
    (fun a => by
      rw [iteratedFDeriv_basis_ofFn n a (radiusPower_diff (-q) n x),
        coordinateIter_radiusPower,Real.norm_eq_abs,abs_mul,
        abs_of_pos (radiusPower_pos (-q) x)]
      have he : |radialEigenvalue (-q) (List.ofFn a)| ≤ |q|^n := by
        simpa only [abs_neg,List.length_ofFn] using abs_radialEigenvalue (-q) (List.ofFn a)
      exact mul_le_mul_of_nonneg_right he (radiusPower_pos _ _).le)
  have hpow : |q|^n ≤ (max 1 |q|)^j :=
    (pow_le_pow_left₀ (abs_nonneg q) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hn)
  calc _ ≤ 3^n * (|q|^n * radiusPower (-q) x) := hb
    _ ≤ 3^j * ((max 1 |q|)^j * radiusPower (-q) x) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hn)
        (mul_le_mul_of_nonneg_right hpow (radiusPower_pos _ _).le) hc (by positivity)
    _ = _ := by ring

lemma compactified_uniform_logJet (j : ℕ) {K : Set Point} (hK : IsCompact K)
    {f : Point → ℝ} (hf : ∀ z ∈ K, ContDiffAt ℝ ∞ f z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point, inverseLogRadiusChart x ∈ K →
      LogJetBound (fun y => f (inverseLogRadiusChart y)) j 0 C x := by
  classical
  choose C hC hb using (fun n : Fin (j+1) => compactified_scalar_uniform_jets n.val hK hf)
  refine ⟨∑ n, C n, Finset.sum_nonneg (fun n _ => hC n), ?_⟩
  intro x hx n hn
  have hc : C ⟨n,by omega⟩ ≤ ∑ k, C k :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ _)
  simpa [radiusPower] using (hb ⟨n,by omega⟩ x hx).trans hc

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

structure FiniteLogDecay (j : ℕ) (q : ℝ) (U : Set Point) (f : Point → ℝ) : Prop where
  regular : ∀ x ∈ U, ContDiffAt ℝ j f x
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, LogJetBound f j q C x

namespace FiniteLogDecay
variable {j : ℕ} {q r : ℝ} {U : Set Point} {f g : Point → ℝ}

lemma congr (hf : FiniteLogDecay j q U f) (he : f = g) : FiniteLogDecay j q U g := he ▸ hf

lemma mul (hf : FiniteLogDecay j q U f) (hg : FiniteLogDecay j r U g) :
    FiniteLogDecay j (q+r) U (fun x => f x*g x) := by
  obtain ⟨C,hC,hb⟩ := hf.bound
  obtain ⟨D,hD,hc⟩ := hg.bound
  exact ⟨fun x hx => (hf.regular x hx).mul (hg.regular x hx),2^j*C*D,by positivity,
    fun x hx => LogJetBound.mul hC hD (hf.regular x hx) (hg.regular x hx) (hb x hx) (hc x hx)⟩

lemma radiusPower (j : ℕ) (q : ℝ) (U : Set Point) :
    FiniteLogDecay j q U (CKSMixedGeometry.radiusPower (-q)) :=
  ⟨fun x _ => radiusPower_diff (-q) j x,
    3^j*(max 1 |q|)^j,by positivity,fun x _ => radiusPower_logJet j q x⟩

lemma compactified (j : ℕ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z) :
    FiniteLogDecay j 0 (inverseLogRadiusChart ⁻¹' K)
      (fun x => F (inverseLogRadiusChart x)) := by
  refine ⟨fun x hx => ?_,compactified_uniform_logJet j hK hF⟩
  exact ((hF _ hx).comp x inverseLogRadiusChart_smooth.contDiffAt).of_le
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))

end FiniteLogDecay
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff
namespace FiniteLogDecay

lemma weighted_compactified (j : ℕ) (q : ℝ) {K : Set Point} (hK : IsCompact K)
    {F : Point → ℝ} (hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z) :
    FiniteLogDecay j q (inverseLogRadiusChart ⁻¹' K)
      (fun x => CKSMixedGeometry.radiusPower (-q) x * F (inverseLogRadiusChart x)) := by
  simpa only [add_zero] using (radiusPower j q _).mul (compactified j hK hF)

end FiniteLogDecay
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus CKSAngularSlice
open scoped ContDiff Topology

lemma logRadiusChart_radialLogChart {y : Point} (hy : 0 < y 0) :
    logRadiusChart (radialLogChart y) = y := by
  ext i
  by_cases hi : i=0 <;> simp [radialLogChart,logRadiusChart,hi,Real.exp_log hy]

lemma radialLogChart_contDiffAt {y : Point} (hy : 0 < y 0) :
    ContDiffAt ℝ ∞ radialLogChart y := by
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i=0
  · simp only [radialLogChart,hi,ite_true, if_true]
    exact (show ContDiffAt ℝ ∞ (fun z : Point => z 0) y by fun_prop).log (ne_of_gt hy)
  · simp only [radialLogChart,hi,ite_false, if_false]
    fun_prop

theorem FiniteLogDecay.to_source {j q : ℕ} {U : Set Point} {f : Point → ℝ}
    (hf : FiniteLogDecay j q U f) :
    SourceRemainderOn j q (logRadiusChart '' U) (fun y => f (radialLogChart y)) := by
  have hr (x : Point) (hx : x ∈ U) : ContDiffAt ℝ j
      (fun y => f (radialLogChart y)) (logRadiusChart x) := by
    have hl := (radialLogChart_contDiffAt (show 0 < (logRadiusChart x) 0 by
      simpa only [logRadiusChart,ite_true, if_true] using Real.exp_pos (x 0))).of_le
        (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    have hfx : ContDiffAt ℝ j f (radialLogChart (logRadiusChart x)) := by
      simpa only [radialLogChart_logRadiusChart] using hf.regular x hx
    exact hfx.comp _ hl
  refine ⟨?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    exact hr x hx
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨C,hC,?_⟩
  rintro y ⟨x,hx,rfl⟩ l hl
  have he := coordinateIter_pullback l ((hr x hx).of_le (by exact_mod_cast hl))
  have hi : (fun z => f (radialLogChart (logRadiusChart z))) = f := by
    funext z
    rw [radialLogChart_logRadiusChart]
  rw [hi] at he
  rw [← he]
  calc |coordinateIter l f x| ≤ ‖iteratedFDeriv ℝ l.length f x‖ :=
        coordinateIter_le_iteratedFDeriv l ((hf.regular x hx).of_le (by exact_mod_cast hl))
    _ ≤ C*CKSMixedGeometry.radiusPower (-(q:ℝ)) x := hb x hx _ hl
    _ = C/(logRadiusChart x 0)^q := by rw [radiusPower_neg_nat]; simp [logRadiusChart,div_eq_mul_inv]

theorem FiniteLogDecay.source_of_log {j q : ℕ} {U : Set Point} {g : Point → ℝ}
    (hf : FiniteLogDecay j q U (fun x => g (logRadiusChart x))) :
    SourceRemainderOn j q (logRadiusChart '' U) g := by
  have hr (x : Point) (hx : x ∈ U) : ContDiffAt ℝ j g (logRadiusChart x) := by
    have h := hf.to_source.regular (logRadiusChart x) ⟨x,hx,rfl⟩
    have he : g =ᶠ[𝓝 (logRadiusChart x)]
        (fun y => g (logRadiusChart (radialLogChart y))) := by
      have hp : ∀ᶠ y in 𝓝 (logRadiusChart x), 0 < y 0 :=
        (isOpen_lt continuous_const (continuous_apply (0:I))).mem_nhds
          (by change 0 < (logRadiusChart x) 0
              simpa only [logRadiusChart,ite_true, if_true] using Real.exp_pos (x 0))
      filter_upwards [hp] with y hy
      rw [logRadiusChart_radialLogChart hy]
    exact h.congr_of_eventuallyEq he
  refine ⟨?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    exact hr x hx
  obtain ⟨C,hC,hb⟩ := hf.bound
  refine ⟨C,hC,?_⟩
  rintro y ⟨x,hx,rfl⟩ l hl
  rw [← coordinateIter_pullback l ((hr x hx).of_le (by exact_mod_cast hl))]
  calc _ ≤ ‖iteratedFDeriv ℝ l.length (fun z => g (logRadiusChart z)) x‖ :=
        coordinateIter_le_iteratedFDeriv l ((hf.regular x hx).of_le (by exact_mod_cast hl))
    _ ≤ C*CKSMixedGeometry.radiusPower (-(q:ℝ)) x := hb x hx _ hl
    _ = C/(logRadiusChart x 0)^q := by rw [radiusPower_neg_nat]; simp [logRadiusChart,div_eq_mul_inv]

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularSlice Set
open scoped ContDiff Topology

lemma SourceRemainderOn.mono {j q : ℕ} {U V : Set Point} {f : Point → ℝ}
    (hf : SourceRemainderOn j q V f) (hUV : U ⊆ V) : SourceRemainderOn j q U f := by
  obtain ⟨B,hB,hb⟩ := hf.bound
  exact ⟨fun y hy => hf.regular y (hUV hy),B,hB,fun y hy => hb y (hUV hy)⟩

end
end CKSMixedGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCharts
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

attribute [local instance] halfSpaceDimension_neZero

lemma boundary_iff (p : Exterior) : p ∈ I3.boundary Exterior ↔ p.1.val = 0 := by
  rw [CKSBoundarySurface.boundary_iff_zero p p (mem_chart_source H3 p)]
  rfl
lemma interior_iff (p : Exterior) : p ∈ I3.interior Exterior ↔ 0 < p.1.val := by
  have h := (I3.isBoundaryPoint_iff_not_isInteriorPoint p)
  change p ∈ I3.boundary Exterior ↔ p ∉ I3.interior Exterior at h
  rw [boundary_iff] at h
  have hp := p.1.property
  constructor
  · intro hi
    by_contra hn
    have hz : p.1.val = 0 := le_antisymm (le_of_not_gt hn) hp
    exact h.mp hz hi
  · intro hp0
    by_contra hi
    have hz := h.mpr hi
    linarith

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildBoundary
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma boundary_height (p : Boundary Exterior) : height p.val = 0 :=
  (boundary_iff p.val).mp p.property

def boundarySphere : Boundary Exterior ≃ₜ Sphere where
  toFun p := p.val.2
  invFun n := ⟨(⟨0,le_rfl⟩,n),(boundary_iff _).mpr rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact (boundary_height p).symm
    · rfl
  right_inv n := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _

lemma boundary_compact : IsCompact (I3.boundary Exterior) := by
  have : CompactSpace (Boundary Exterior) := boundarySphere.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma lapseSquared_horizon {m : ℝ} (hm : 0 < m) : lapseSquared m (2*m) = 1 := by
  rw [lapseSquared,velocity_near m (2*m) (by linarith)]
  have hm0 : m ≠ 0 := ne_of_gt hm
  field_simp
  ring
lemma lapse_horizon {m : ℝ} (hm : 0 < m) : lapse m (2*m) = 1 := by
  rw [lapse,lapseSquared_horizon hm,Real.sqrt_one]
lemma lapse_pos {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) : 0 < lapse m r :=
  Real.sqrt_pos.mpr (lapseSquared_pos hm hr)
lemma lapse_sq {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) : (lapse m r)^2 = lapseSquared m r :=
  Real.sq_sqrt (lapseSquared_pos hm hr).le

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildConnectionDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Manifold Bundle Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def radialNormal (m : ℝ) (x : E3) : E3 := lapse m ‖x‖ • radialUnit x
def tangentProjection (x a : E3) : E3 := a - ⟪radialUnit x,a⟫_ℝ • radialUnit x

def sphereMeanCurvature (m : ℝ) (x : E3) : ℝ :=
  ∑ i : Fin 3, covariantPair (cartMetric m) (radialNormal m) x
    (tangentProjection x (EuclideanSpace.single i 1))
    (tangentProjection x (EuclideanSpace.single i 1))
def sphereTensorTrace (m : ℝ) (x : E3) : ℝ :=
  ∑ i : Fin 3, cartTensor m x
    (tangentProjection x (EuclideanSpace.single i 1))
    (tangentProjection x (EuclideanSpace.single i 1))
def sphereThetaPlus (m : ℝ) (x : E3) : ℝ := sphereMeanCurvature m x + sphereTensorTrace m x
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma radialUnit_inner_self {x : E3} (hx : x ≠ 0) : ⟪radialUnit x,radialUnit x⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq,norm_radialUnit hx,one_pow]
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildHorizon
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma radialNormal_unit {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖) :
    cartMetric m x (radialNormal m x) (radialNormal m x) = 1 := by
  have hn : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hx)
  rw [cartMetric_apply]
  simp only [radialNormal,inner_smul_right,real_inner_smul_left,radialUnit_inner_self hn,mul_one]
  rw [← lapse_sq hm hx]
  have hu := ne_of_gt (lapse_pos hm hx)
  field_simp
  ring
lemma radialNormal_orthogonal (m : ℝ) {x a : E3} (ha : ⟪radialUnit x,a⟫_ℝ = 0) :
    cartMetric m x (radialNormal m x) a = 0 := by
  rw [cartMetric_apply]
  simp only [radialNormal,real_inner_smul_left,ha,mul_zero,zero_add]
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildRadialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSMixedGeometry CKSAngularSlice
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma compactified_radial_source (j q : ℕ) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hδR : 1/δ ≤ R) (θ : Angle) {F : ℝ → ℝ}
    (hF : ∀ s ∈ Icc 0 δ, ContDiffAt ℝ ∞ F s) :
    SourceRemainderOn j q (angularRadialTail R (Metric.ball θ 1))
      (fun y => F ((y 0)⁻¹) / (y 0)^q) := by
  let K : Set Point := (fun p : ℝ × Angle => slice p.1 p.2) '' (Icc 0 δ ×ˢ Metric.closedBall θ 1)
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall θ 1)).image (by apply continuous_pi; intro i; fin_cases i <;> simp [slice,injection] <;> fun_prop)
  have hFc : ∀ z ∈ K, ContDiffAt ℝ ∞ (fun z : Point => F (z 0)) z := by
    rintro z ⟨p,hp,rfl⟩
    have hh : ContDiffAt ℝ ∞ F (slice p.1 p.2 0) := by simpa [slice] using hF p.1 hp.1
    exact hh.comp (slice p.1 p.2)
      (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).contDiff.contDiffAt
  have h := FiniteLogDecay.weighted_compactified j (q : ℝ) hK hFc
  have he (x : Point) : radiusPower (-(q:ℝ)) x * F ((inverseLogRadiusChart x) 0) =
      F ((logRadiusChart x 0)⁻¹) / (logRadiusChart x 0)^q := by
    rw [radiusPower_neg_nat]
    simp only [inverseLogRadiusChart,logRadiusChart,ite_true, if_true,Real.exp_neg]
    ring
  have h' : FiniteLogDecay j (q : ℝ) (inverseLogRadiusChart ⁻¹' K)
      (fun x => F ((logRadiusChart x 0)⁻¹) / (logRadiusChart x 0)^q) :=
    h.congr (funext he)
  apply h'.source_of_log.mono
  intro y hy
  have hr : 0 < y 0 := lt_trans hR hy.1
  refine ⟨radialLogChart y,?_,logRadiusChart_radialLogChart hr⟩
  have hinv : (y 0)⁻¹ ≤ δ := by
    have hh : 1/δ < y 0 := lt_of_le_of_lt hδR hy.1
    exact (inv_le_comm₀ hr hδ).mpr (by simpa using hh.le)
  refine ⟨((y 0)⁻¹,angularProjection y),⟨⟨inv_nonneg.mpr hr.le,hinv⟩,Metric.mem_closedBall.mpr
    (Metric.mem_ball.mp hy.2).le⟩,?_⟩
  ext i
  cases i using Fin.cases <;> simp [slice,inverseLogRadiusChart,radialLogChart,
    angularProjection,Real.exp_neg,Real.exp_log hr]

lemma source_zero (j q : ℕ) (R : ℝ) (θ : Angle) (hR : 0 < R) :
    SourceRemainderOn j q (angularRadialTail R (Metric.ball θ 1)) (fun _ => 0) := by
  simpa only [zero_div] using compactified_radial_source j q (δ := 1/R)
    (one_div_pos.mpr hR) hR (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) θ (F := fun _ => 0) (fun _ _ => contDiffAt_const)

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildRoundMetric
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Manifold Bundle Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance schwarzschildRoundMetricFinrank : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩

def euclideanMetric : ContMDiffRiemannianMetric 𝓘(ℝ,E3) ∞ E3 (fun x : E3 => TangentSpace 𝓘(ℝ,E3) x) :=
  { riemannianMetricVectorSpace E3 with contMDiff := (riemannianMetricVectorSpace E3).contMDiff.of_le le_top }

def sphereMetric : ContMDiffRiemannianMetric I2 ∞ E2 (fun x : Sphere => TangentSpace I2 x) :=
  CKSInducedArea.inducedMetric euclideanMetric (Subtype.val : Sphere → E3)
    (contMDiff_coe_sphere (n := 2)) (by
      intro point
      convert! injective_mvfderiv_subtypeVal_sphere (n := 2) point)

def sphereDerivative (n : Sphere) : E2 →L[ℝ] E3 := by
  exact mfderiv I2 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) n

lemma radialUnit_position {m : ℝ} (hm : 0 < m) (p : Exterior) :
    radialUnit (position m p) = directionAmbient p := by
  rw [radialUnit,norm_position hm,position,smul_smul,inv_mul_cancel₀ (ne_of_gt (radius_pos hm p)),one_smul]
lemma position_radial_inner {m : ℝ} (hm : 0 < m) (p : Exterior) (v : E3) :
    ⟪radialUnit (position m p),ambientDerivative (position m) p v⟫_ℝ = v 0 := by
  have ho : ⟪directionAmbient p,ambientDerivative directionAmbient p v⟫_ℝ = 0 := directionAmbient_orthogonal p v
  rw [radialUnit_position hm,mfderiv_position,inner_add_right,inner_smul_right,inner_smul_right,ho,
    real_inner_self_eq_norm_sq,norm_direction]
  ring

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildHorizonExclusionDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

attribute [local instance] CKSInducedArea.real_continuousAdd CKSInducedArea.real_smulCommClass
  CKSInducedArea.real_continuousConstSMul CKSBoundarySurface.two_atLeastTwo

attribute [local instance] OAI.CKSSchwarzschild.frameCovectorModule

def parameterSecondForm (m : ℝ) (f : E2 → E3) (y : E2) (N : E3) (a b : E2) : ℝ :=
  -(cartMetric m (f y) N (fderiv ℝ (fun z => fderiv ℝ f z b) y a) +
    christoffelPair (cartMetric m) (f y) (fderiv ℝ f y a) (fderiv ℝ f y b) N)

def parameterMeanCurvature (m : ℝ) (f : E2 → E3) (y : E2) (N : E3) : ℝ :=
  let a := firstFrame (cartMetric m (f y)) (fderiv ℝ f y)
  let b := secondFrame (cartMetric m (f y)) (fderiv ℝ f y)
  parameterSecondForm m f y N a a + parameterSecondForm m f y N b b

def parameterTensorTrace (m : ℝ) (f : E2 → E3) (y : E2) : ℝ :=
  let a := fderiv ℝ f y (firstFrame (cartMetric m (f y)) (fderiv ℝ f y))
  let b := fderiv ℝ f y (secondFrame (cartMetric m (f y)) (fderiv ℝ f y))
  cartTensor m (f y) a a + cartTensor m (f y) b b

universe u
variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T]

def surfaceParameter (F : T → E3) (p : T) : E2 → E3 := F ∘ (extChartAt I2 p).symm

def surfaceMeanCurvature (m : ℝ) (F N : T → E3) (p : T) : ℝ :=
  parameterMeanCurvature m (surfaceParameter F p) ((extChartAt I2 p) p) (N p)

def surfaceTensorTrace (m : ℝ) (F : T → E3) (p : T) : ℝ :=
  parameterTensorTrace m (surfaceParameter F p) ((extChartAt I2 p) p)

structure InteriorImmersion (m : ℝ) (T : Type u) [TopologicalSpace T] [ChartedSpace E2 T] where
  map : T → E3
  smooth : ContMDiff I2 𝓘(ℝ,E3) ∞ map
  immersion : ∀ p, Function.Injective (mfderiv I2 𝓘(ℝ,E3) map p)
  interior : ∀ p, 2*m < ‖map p‖
  normal : T → E3
  normal_unit : ∀ p, cartMetric m (map p) (normal p) (normal p) = 1
  normal_orthogonal : ∀ p a, cartMetric m (map p) (normal p) (mfderiv I2 𝓘(ℝ,E3) map p a) = 0

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BoundaryBridge
attribute [-simp] _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology InnerProductSpace
namespace CKSMain
open CKSSchwarzschild
attribute [local instance] manifold_regular
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero
attribute [local instance] CKSSpatialManifold.real_id_isometric
  CKSLorentz.real_smulCommClass CKSLorentz.spatialDual_smulCommClass

def horizonNormal (p : Boundary Exterior) : TangentSpace I3 p.val :=
  EuclideanSpace.single 0 1

lemma horizon_radius {m : ℝ} (hm : 0 < m) (p : Boundary Exterior) :
    ‖position m p.val‖ = 2*m := by simp [norm_position hm,radius,boundary_height p]

lemma horizonNormal_coordinate {m : ℝ} (hm : 0 < m) (p : Boundary Exterior) :
    mfderiv I3 𝓘(ℝ,E3) (position m) p.val (horizonNormal p) =
      radialNormal m (position m p.val) := by
  have hd : dropPlane (EuclideanSpace.single 0 1) = 0 := by
    ext i
    simp [dropPlane_apply]
  have hz : ambientDerivative directionAmbient p.val (EuclideanSpace.single 0 1) = 0 := by
    change mfderiv I3 𝓘(ℝ,E3) directionAmbient p.val (EuclideanSpace.single 0 1) = 0
    rw [mfderiv_directionAmbient]
    change mfderiv I2 𝓘(ℝ,E3) (Subtype.val : CKSSchwarzschild.Sphere → E3) p.val.2
      (dropPlane (EuclideanSpace.single 0 1)) = 0
    rw [hd]
    change (mfderiv I2 𝓘(ℝ,E3) (Subtype.val : CKSSchwarzschild.Sphere → E3) p.val.2)
      (0 : TangentSpace I2 p.val.2) = 0
    exact map_zero _
  change ambientDerivative (position m) p.val (EuclideanSpace.single 0 1) = _
  rw [mfderiv_position,hz]
  simp [radialNormal,horizon_radius hm p,lapse_horizon hm,radialUnit_position hm]

def schwarzschildBoundary {m : ℝ} (hm : 0 < m) :
    BoundaryGeometry (smoothMetric hm) (tensorInner m) where
  normal := horizonNormal
  unit p := by
    change cartMetric m (position m p.val)
      (mfderiv I3 𝓘(ℝ,E3) (position m) p.val (horizonNormal p))
      (mfderiv I3 𝓘(ℝ,E3) (position m) p.val (horizonNormal p)) = 1
    rw [horizonNormal_coordinate hm p]
    exact radialNormal_unit hm (by rw [horizon_radius hm p])
  orthogonal p a := by
    change cartMetric m (position m p.val)
      (mfderiv I3 𝓘(ℝ,E3) (position m) p.val (horizonNormal p))
      (mfderiv I3 𝓘(ℝ,E3) (position m) p.val
        (mfderiv I2 I3 (Subtype.val : Boundary Exterior → Exterior) p a)) = 0
    rw [horizonNormal_coordinate hm p,(CKSBoundarySurface.inclusion_hasMFDeriv p).mfderiv]
    apply radialNormal_orthogonal
    exact (position_radial_inner hm p.val (liftPlane a)).trans (liftPlane_zero a)
  inward p := by change 0 < (EuclideanSpace.single 0 1 : E3) 0; simp
  chart p := schwarzschildAtlas hm p.val
  normal_smooth p := by
    change ContMDiffAt I2 𝓘(ℝ,E3) ∞
      (fun z : Boundary Exterior =>
        mfderiv I3 𝓘(ℝ,E3) (position m) z.val (horizonNormal z)) p
    have he : (fun z : Boundary Exterior =>
        mfderiv I3 𝓘(ℝ,E3) (position m) z.val (horizonNormal z)) =
        directionAmbient ∘ (Subtype.val : Boundary Exterior → Exterior) := by
      funext z
      rw [horizonNormal_coordinate hm z]
      simp [radialNormal,horizon_radius hm z,lapse_horizon hm,radialUnit_position hm]
      rfl
    rw [he]
    exact (directionAmbient_smooth.comp CKSBoundarySurface.inclusion_smooth) p

end CKSMain

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [local instance] OAI.CKSSurfaceVolume.instNormedAddCommGroupContinuousLinearMapRealIdE
attribute [local instance] OAI.CKSSurfaceVolume.instNormedSpaceRealContinuousLinearMapIdE
local instance instNormedAddCommGroupContinuousLinearMapRealIdE_1_rdf0426_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance instNormedSpaceRealContinuousLinearMapIdE_1_rdf0426_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
def scaledMetric (g : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (c : ℝ) (hc : 0 < c) : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x) where
  inner x := c • g.inner x
  symm x v w := congrArg (c * ·) (g.symm x v w)
  pos x v hv := mul_pos hc (g.pos x v hv)
  isVonNBounded x := CKSInducedArea.positive_bilinear_bounded (c • g.inner x)
    (fun v hv => mul_pos hc (g.pos x v hv))
  contMDiff := by
    let (x : M) : NormedAddCommGroup (TangentSpace I x) := by unfold TangentSpace; infer_instance
    let (x : M) : NormedSpace ℝ (TangentSpace I x) := by unfold TangentSpace; infer_instance
    let (x : M) : ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) := by
      change ContinuousAdd (E →L[ℝ] ℝ); infer_instance
    let (x : M) : ContinuousAdd (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
      change ContinuousAdd (E →L[ℝ] E →L[ℝ] ℝ); infer_instance
    exact g.contMDiff.const_smul_section

@[simp] lemma scaledMetric_apply (g : ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x))
    (c : ℝ) (hc : 0 < c) (x : M) (v w : E) : (scaledMetric g c hc).inner x v w = c * g.inner x v w := rfl

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildAreaDefinitions
attribute [-simp] _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace CKSSchwarzschild
open CKSBoundarySurface CKSFullCutArea CKSSurfaceVolume
def boundaryScaledMetric {m : ℝ} (hm : 0 < m) :=
  scaledMetric sphereMetric ((2*m)^2) (sq_pos_of_pos (mul_pos (by norm_num) hm))

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCKSAlgebra
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMixedGeometry CKSAngularSlice
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma cartTensor_far (m : ℝ) {x : E3} (hx : 2*m+2 < ‖x‖) (hp : 0 < ‖x‖) :
    cartTensor m x = cartMetric m x := by
  rw [cartTensor,cartMetric,velocity_far m ‖x‖ hx.le,velocity_deriv_far m ‖x‖ hx,
    div_self hp.ne',one_smul,one_div]
lemma hyperbolic_radial (x : E3) (hx : x ≠ 0) :
    hyperbolicField x = euclideanForm + ((1+‖x‖^2)⁻¹-1) • radialForm x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hd : 1+‖x‖^2 ≠ 0 := by positivity
  change ⟪v,w⟫_ℝ - 1/(1+‖x‖^2)*(⟪x,v⟫_ℝ * ⟪x,w⟫_ℝ) =
    ⟪v,w⟫_ℝ + ((1+‖x‖^2)⁻¹-1)*(⟪‖x‖⁻¹ • x,v⟫_ℝ * ⟪‖x‖⁻¹ • x,w⟫_ℝ)
  simp only [real_inner_smul_left]
  field_simp
  ring
lemma metricPerturbation_far (m : ℝ) {x : E3} (hx : 2*m+2 ≤ ‖x‖) (hp : 0 < ‖x‖) :
    metricPerturbation m x = radialCoefficient m ‖x‖ • radialForm x := by
  rw [metricPerturbation,hyperbolic_radial x (norm_ne_zero_iff.mp hp.ne')]
  unfold cartMetric lapseSquared radialCoefficient
  rw [velocity_far m ‖x‖ hx]
  have he : 1-2*m/‖x‖+‖x‖^2 = 1+‖x‖^2-2*m/‖x‖ := by ring
  rw [he]
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [add_apply,sub_apply,smul_apply,smul_eq_mul]
  ring

lemma radialUnit_polar (P : SmoothAngularPatch) {y : Point} (hr : 0 < y 0) :
    radialUnit (polarParam P y) = P.param (angularProjection y) := by
  rw [radialUnit,polarParam_norm P hr.le,polarParam,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
lemma radial_dot_polar (P : SmoothAngularPatch) {y : Point} (hr : 0 < y 0)
    (hy : angularProjection y ∈ P.chart.target) (i : I) :
    ⟪radialUnit (polarParam P y), fderiv ℝ (polarParam P) y (basis i)⟫_ℝ =
      if i=0 then 1 else 0 := by
  rw [radialUnit_polar P hr]
  cases i using Fin.cases
  · rw [polarParam_fderiv_radial P hy,real_inner_self_eq_norm_sq]
    have hn : ‖P.param (angularProjection y)‖ = 1 := P.param_norm (angularProjection y)
    simp [hn]
  · rw [polarParam_fderiv_angular P hy,inner_smul_right,P.param_tangent hy]
    simp
lemma perturbation_polar (m : ℝ) (P : SmoothAngularPatch) {y : Point}
    (hr : 2*m+2 < y 0) (hp : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (i k : I) :
    polarTensorComponents P (metricPerturbation m) i k y =
      (if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0) ∧
    polarTensorComponents P (tensorPerturbation m) i k y =
      if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0 := by
  have hn := polarParam_norm P hp.le
  have hM := metricPerturbation_far m (x := polarParam P y) (by rw [hn]; exact hr.le)
    (by rwa [hn])
  have hK : tensorPerturbation m (polarParam P y) = metricPerturbation m (polarParam P y) := by
    rw [tensorPerturbation,metricPerturbation,cartTensor_far m (by rwa [hn]) (by rwa [hn])]
  have he : polarTensorComponents P (metricPerturbation m) i k y =
      if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0 := by
    unfold polarTensorComponents
    rw [hM,hn]
    change radialCoefficient m (y 0) *
      (⟪radialUnit (polarParam P y),fderiv ℝ (polarParam P) y (basis i)⟫_ℝ *
      ⟪radialUnit (polarParam P y),fderiv ℝ (polarParam P) y (basis k)⟫_ℝ) = _
    rw [radial_dot_polar P hp hy,radial_dot_polar P hp hy]
    split_ifs <;> simp_all
  exact ⟨he,by unfold polarTensorComponents; rw [hK]; exact he⟩
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCKSDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSMixedGeometry CKSAngularSlice
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma compactDenominator_pos {m s : ℝ} (hm : 0 < m) (hs : s ∈ Icc 0 (1/(4*m+4))) :
    0 < compactDenominator m s := by
  have hD : 0 < 4*m+4 := by positivity
  have hms := (le_div_iff₀ hD).mp hs.2
  have hmss : 0 ≤ 1-2*m*s := by nlinarith
  have hp : 0 < 1+s^2-2*m*s^3 := by nlinarith [mul_nonneg (sq_nonneg s) hmss]
  exact mul_pos hp (by positivity)
lemma compactCoefficient_smooth {m s : ℝ} (hm : 0 < m) (hs : s ∈ Icc 0 (1/(4*m+4))) :
    ContDiffAt ℝ ∞ (compactCoefficient m) s := by
  exact contDiffAt_const.div (by unfold compactDenominator; fun_prop)
    (compactDenominator_pos hm hs).ne'
lemma compactRemainder_smooth {m s : ℝ} (hm : 0 < m) (hs : s ∈ Icc 0 (1/(4*m+4))) :
    ContDiffAt ℝ ∞ (compactRemainder m) s := by
  unfold compactRemainder
  apply ContDiffAt.div
  · fun_prop
  · unfold compactDenominator; fun_prop
  · exact (compactDenominator_pos hm hs).ne'
lemma radialCoefficient_id {m r : ℝ} (hm : 0 < m) (hr : 4*m+4 ≤ r) :
    radialCoefficient m r = compactCoefficient m r⁻¹/r^5 ∧
    radialCoefficient m r - 2*m/r^5 = compactRemainder m r⁻¹/r^6 := by
  have hrp : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hd : 0 < 1+r^2-2*m/r := by
    have hmr : 2*m < r := by linarith
    have h := (div_lt_one hrp).mpr hmr
    nlinarith [sq_nonneg r]
  have hs := tail_inverse_small hm hr
  have hc : compactDenominator m r⁻¹ ≠ 0 := (compactDenominator_pos hm hs).ne'
  have h1 : 1+r^2 ≠ 0 := by positivity
  have hpoly : r+r^3-2*m ≠ 0 := by
    have : 0 < (1+r^2-2*m/r)*r := mul_pos hd hrp
    have he : (1+r^2-2*m/r)*r = r+r^3-2*m := by field_simp
    rw [he] at this
    exact this.ne'
  have hpoly' : r+r^3-m*2 ≠ 0 := by simpa only [mul_comm m 2] using hpoly
  constructor
  · unfold radialCoefficient compactCoefficient compactDenominator
    field_simp (disch := first | assumption | positivity | (convert hpoly using 1; ring))
    ring
  · unfold radialCoefficient compactRemainder compactDenominator
    field_simp (disch := first | assumption | positivity | (convert hpoly using 1; ring))
    ring

lemma radial_decay {m : ℝ} (hm : 0 < m) (θ : Angle) :
    SourceRemainderOn 3 6 (angularRadialTail (4*m+4) (Metric.ball θ 1))
      (fun y => radialCoefficient m (y 0)-2*m/(y 0)^5) ∧
    SourceRemainderOn 2 5 (angularRadialTail (4*m+4) (Metric.ball θ 1))
      (fun y => radialCoefficient m (y 0)) := by
  have hR : 0 < 4*m+4 := by positivity
  have hδ : 0 < 1/(4*m+4) := one_div_pos.mpr hR
  have hδR : 1/(1/(4*m+4)) ≤ 4*m+4 := by simp
  constructor
  · apply (compactified_radial_source 3 6 hδ hR hδR θ (fun s hs => compactRemainder_smooth hm hs)).congrOn
      (angularRadialTail_open _ Metric.isOpen_ball)
    intro y hy
    exact (radialCoefficient_id hm hy.1.le).2.symm
  · apply (compactified_radial_source 2 5 hδ hR hδR θ (fun s hs => compactCoefficient_smooth hm hs)).congrOn
      (angularRadialTail_open _ Metric.isOpen_ball)
    intro y hy
    exact (radialCoefficient_id hm hy.1.le).1.symm
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCKS
attribute [-simp] _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMixedGeometry CKSAngularSlice
open CKSSourceExterior
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

attribute [local instance] four_atLeastTwo
attribute [local instance] CKSMixedGeometry.pointDimension_neZero CKSBoundarySurface.two_atLeastTwo

lemma tensorPatch_zero_smooth (n : Sphere) :
    ∀ i k : CKSMixedGeometry.I, i≠0 → k≠0 →
      ContDiffOn ℝ ∞ (fun _ : Angle => (0 : ℝ))
        (Metric.ball ((stereoSmoothPatch (-n)).chart n) 1) :=
  fun _ _ _ _ => contDiffOn_const

lemma tensorPatch_metric_CKS {m : ℝ} (hm : 0 < m) (n : Sphere) :
    SourceCKSComponents 3 6 (angularRadialTail (4*m+4) (Metric.ball ((stereoSmoothPatch (-n)).chart n) 1))
      (fun i k y => if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0) (fun _ => 2*m) (fun _ _ _ => 0) := by
  constructor
  · simpa [ordinaryLeadingComponent,div_eq_mul_inv,mul_comm] using
      (radial_decay hm ((stereoSmoothPatch (-n)).chart n)).1
  · intro i k h
    have hn : ¬(i=0 ∧ k=0) := by tauto
    simpa only [ite_eq_right hn] using source_zero 3 3 (4*m+4)
      ((stereoSmoothPatch (-n)).chart n) (by positivity)
  · intro i k hi hk
    have hn : ¬(i=0 ∧ k=0) := by tauto
    simpa [ite_eq_right hn,ordinaryLeadingComponent] using source_zero 3 2 (4*m+4)
      ((stereoSmoothPatch (-n)).chart n) (by positivity)

lemma tensorPatch_second_CKS {m : ℝ} (hm : 0 < m) (n : Sphere) :
    SourceCKSComponents 2 5 (angularRadialTail (4*m+4) (Metric.ball ((stereoSmoothPatch (-n)).chart n) 1))
      (fun i k y => if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0) (fun _ => 0) (fun _ _ _ => 0) := by
  constructor
  · simpa [ordinaryLeadingComponent] using
      (radial_decay hm ((stereoSmoothPatch (-n)).chart n)).2
  · intro i k h
    have hn : ¬(i=0 ∧ k=0) := by tauto
    simpa only [ite_eq_right hn] using source_zero 2 3 (4*m+4)
      ((stereoSmoothPatch (-n)).chart n) (by positivity)
  · intro i k hi hk
    have hn : ¬(i=0 ∧ k=0) := by tauto
    simpa [ite_eq_right hn,ordinaryLeadingComponent] using source_zero 2 2 (4*m+4)
      ((stereoSmoothPatch (-n)).chart n) (by positivity)

def tensorPatch {m : ℝ} (hm : 0 < m) (n : Sphere) : CKSTensorPatch where
  patch := stereoSmoothPatch (-n)
  region := Metric.ball ((stereoSmoothPatch (-n)).chart n) 1
  open_region := Metric.isOpen_ball
  region_target := by simp [stereoSmoothPatch]
  radius := 4*m+4
  metric := fun i k y => if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0
  second := fun i k y => if i=0 ∧ k=0 then radialCoefficient m (y 0) else 0
  mr := fun _ => 2*m
  mg := fun _ _ _ => 0
  mK := fun _ _ _ => 0
  mr_smooth := contDiffOn_const
  mg_smooth := tensorPatch_zero_smooth n
  mK_smooth := tensorPatch_zero_smooth n
  metric_CKS := tensorPatch_metric_CKS hm n
  second_CKS := tensorPatch_second_CKS hm n
lemma tensorPatch_covers {m : ℝ} (hm : 0 < m) (n : Sphere) :
    n ∈ (tensorPatch hm n).patch.sphereRegion (tensorPatch hm n).region := by
  constructor
  · change n ∈ (stereoAngularChart (-n)).source
    simpa only [stereoAngularChart_source,mem_compl_iff,mem_singleton_iff] using
      ne_neg_of_mem_unit_sphere ℝ n
  · exact Metric.mem_ball_self (by norm_num)
lemma tensorPatch_realizes {m : ℝ} (hm : 0 < m) (n : Sphere) :
    (tensorPatch hm n).Realizes (metricPerturbation m) (tensorPerturbation m) := by
  intro y hy i k
  have hr : 4*m+4 < y 0 := hy.1
  have h := perturbation_polar m (stereoSmoothPatch (-n))
    (by linarith : 2*m+2 < y 0) (by linarith : 0 < y 0)
    (by simp [stereoSmoothPatch]) i k
  exact ⟨h.1.symm,h.2.symm⟩
lemma tensorPatch_aspect {m : ℝ} (hm : 0 < m) (n : Sphere) :
    (tensorPatch hm n).RepresentsMassAspect (fun _ => 4*m) := by
  intro p hp
  change cksChartMassAspect _ (fun _ => 2*m) (fun _ _ _ => 0) (fun _ _ _ => 0) _ = _
  rw [cksChartMassAspect_split]
  have hz (σ : AngularMatrix) : angularMetricTrace σ (fun _ _ => 0) = 0 := by
    change (σ⁻¹ * (0 : AngularMatrix)).trace = 0
    simp
  rw [hz]
  ring

def cksData {m : ℝ} (hm : 0 < m) : CKSData (smoothMetric hm) (tensorInner m) where
  chart := coordinateEnd hm
  metricPerturbation := metricPerturbation m
  tensorPerturbation := tensorPerturbation m
  metric_smooth := cksData_metric_smooth hm
  tensor_smooth := cksData_tensor_smooth hm
  represents := cksData_represents hm
  massAspect := fun _ => 4*m
  aspect_smooth := cksData_aspect_smooth m
  patches := tensorPatch hm
  covers := tensorPatch_covers hm
  realizes := tensorPatch_realizes hm
  aspect_eq := tensorPatch_aspect hm
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildEqualityDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSSpatialManifold CKSMetricGluing CKSLorentz
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance schwarzschildEqualityCotangentTopology : TopologicalSpace (TotalSpace (E3 →L[ℝ] ℝ)
    (fun x : Exterior => TangentSpace I3 x →L[ℝ] ℝ)) := inferInstance

structure SchwarzschildEqualityExample (m : ℝ) (hm : 0 < m) : Prop where
  connected : ConnectedSpace Exterior
  orientable : CKSSourceExterior.Orientable (N := Exterior)
  boundary_nonempty : (I3.boundary Exterior).Nonempty
  boundary_compact : IsCompact (I3.boundary Exterior)
  boundary_connected : ConnectedSpace (Boundary Exterior)
  smooth_tensor : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞
    (innerSection I3 (tensorInner m))
  symmetric_tensor : ∀ p v w, tensorInner m p v w = tensorInner m p w v
  complete : CKSReplacementCompleteness.IsComplete I3 (smoothMetric hm).toContinuousRiemannianMetric
  dec : PhysicalDEC I3 (smoothMetric hm).inner (tensorInner m)
  exterior_CKS : Nonempty (CKSSourceExterior.CKSData (smoothMetric hm) (tensorInner m))
  bondi : CKSLorentz.bondiCharge (cksData hm).massAspect = (m,0)
  timelike : ‖(CKSLorentz.bondiCharge (cksData hm).massAspect).2‖ <
    (CKSLorentz.bondiCharge (cksData hm).massAspect).1
  horizon_regular : HorizonRegularGraph m
  boundary_normal_unit : ∀ x : E3, 2*m ≤ ‖x‖ →
    cartMetric m x (radialNormal m x) (radialNormal m x) = 1
  boundary_normal_orthogonal : ∀ x a : E3, ⟪radialUnit x,a⟫_ℝ = 0 →
    cartMetric m x (radialNormal m x) a = 0
  boundary_normal_points_into_end : ∀ x : E3, 2*m ≤ ‖x‖ →
    0 < fderiv ℝ (fun y : E3 => ‖y‖) x (radialNormal m x)
  boundary_theta_plus : ∀ p ∈ I3.boundary Exterior, sphereThetaPlus m (position m p) = 0
  full_cut_area : CKSSourceExterior.minimumEnclosingArea (smoothMetric hm) = 16*Real.pi*m^2
  positive_area : 0 < CKSSourceExterior.minimumEnclosingArea (smoothMetric hm)
  equality : Real.sqrt ((CKSLorentz.bondiCharge (cksData hm).massAspect).1^2 -
    ‖(CKSLorentz.bondiCharge (cksData hm).massAspect).2‖^2) =
    Real.sqrt (CKSSourceExterior.minimumEnclosingArea (smoothMetric hm) / (16*Real.pi))
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_MainDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
namespace CKSMain
universe u v
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

attribute [local instance] sixteen_atLeastTwo

def SchwarzschildAttainment (m : ℝ) (hm : 0 < m) : Prop :=
  MainHypotheses.{0,v} (CKSSchwarzschild.smoothMetric hm) (CKSSchwarzschild.tensorInner m)
    (CKSSchwarzschild.cksData hm) (schwarzschildAtlas hm) ∧
  CKSSchwarzschild.HorizonRegularGraph m ∧
  bondiMass (CKSSchwarzschild.cksData hm) = m ∧
  minimumEnclosingArea (CKSSchwarzschild.smoothMetric hm) = 16*Real.pi*m^2 ∧
  bondiMass (CKSSchwarzschild.cksData hm) =
    Real.sqrt (minimumEnclosingArea (CKSSchwarzschild.smoothMetric hm) / (16*Real.pi))

end CKSMain

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSReplacementCompleteness
open scoped ContDiff Topology ENNReal
namespace CKSSchwarzschild
open CKSBoundarySurface

def logRadius (m : ℝ) (p : Exterior) : ℝ := Real.log (radius m p+2)
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SphereConeChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

local instance sphereConeChartFinrank_rdf0426_1 : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩
def sphereParam (p : Sphere) (y : E2) : E3 := ((extChartAt I2 p).symm y).val
def sphereParamDeriv (p : Sphere) (y : E2) : E2 →L[ℝ] E3 :=
  (sphereDerivative ((extChartAt I2 p).symm y)).comp (CKSSurfaceVolume.chartFrame p y)

def sphereCone (p : Sphere) (z : E3) : E3 := (z 0) • sphereParam p (dropPlane z)
def sphereConeDeriv (p : Sphere) (z : E3) : E3 →L[ℝ] E3 :=
  coneLinear (z 0) (sphereParam p (dropPlane z)) (sphereParamDeriv p (dropPlane z))

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SphereConeMeasure
attribute [-simp] _root_.OAI.CKSBoundarySurface.boundaryChart_apply _root_.OAI.CKSBoundarySurface.boundaryChart_source _root_.OAI.CKSBoundarySurface.boundaryChart_target _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace CKSSchwarzschild
open CKSBoundarySurface

def splitEuclidean : E3 ≃ₜ ℝ × E2 where
  toFun z := (z 0,dropPlane z)
  invFun := join
  left_inv := join_drop
  right_inv z := by cases z; simp
  continuous_toFun := firstCoordinate.continuous.prodMk dropPlane.continuous
  continuous_invFun := join.continuous

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildOrientability
attribute [-simp] _root_.OAI.CKSSchwarzschild.coneLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

def positionTangentEquiv (p : Exterior) : TangentSpace I3 p ≃L[ℝ] E3 := by
  exact (LinearEquiv.ofBijective (ambientDerivative (position 1) p).toLinearMap
    ⟨position_derivative_injective (by norm_num) p,
      LinearMap.injective_iff_surjective.mp (position_derivative_injective (by norm_num) p)⟩).toContinuousLinearEquiv

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildIntrinsicHorizonDefinitions
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff
namespace CKSSchwarzschild
open CKSBoundarySurface
universe u

variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T]
def intrinsicCoordinateMap {m : ℝ} (D : IntrinsicInteriorImmersion m T) : T → E3 :=
  position m ∘ D.map
def intrinsicCoordinateNormal {m : ℝ} (D : IntrinsicInteriorImmersion m T) : T → E3 :=
  fun p => mfderiv I3 𝓘(ℝ,E3) (position m) (D.map p) (D.normal p)
def intrinsicSurfaceMeanCurvature {m : ℝ} (D : IntrinsicInteriorImmersion m T) (p : T) : ℝ :=
  surfaceMeanCurvature m (intrinsicCoordinateMap D) (intrinsicCoordinateNormal D) p
def intrinsicSurfaceTensorTrace {m : ℝ} (D : IntrinsicInteriorImmersion m T) (p : T) : ℝ :=
  surfaceTensorTrace m (intrinsicCoordinateMap D) p
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildIntrinsicEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff
namespace CKSSchwarzschild
open CKSBoundarySurface
universe u
variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]

omit [IsManifold I2 ∞ T] in
lemma intrinsicCoordinateMap_derivative [IsManifold I2 ∞ T] {m : ℝ}
    (D : IntrinsicInteriorImmersion m T) (p : T) :
    mfderiv I2 𝓘(ℝ,E3) (intrinsicCoordinateMap D) p =
      (mfderiv I3 𝓘(ℝ,E3) (position m) (D.map p)).comp (mfderiv I2 I3 D.map p) := by
  exact mfderiv_comp p ((position_smooth m).mdifferentiable (by simp) _)
    (D.smooth.mdifferentiable (by simp) _)

def IntrinsicInteriorImmersion.coordinateImmersion {m : ℝ} (hm : 0 < m)
    (D : IntrinsicInteriorImmersion m T) : InteriorImmersion m T where
  map := intrinsicCoordinateMap D
  smooth := (position_smooth m).comp D.smooth
  immersion p := by
    rw [intrinsicCoordinateMap_derivative]
    exact (position_derivative_injective hm _).comp (D.immersion p)
  interior p := by
    rw [intrinsicCoordinateMap,Function.comp_apply,norm_position hm]
    have hp := (interior_iff _).mp (D.interior p)
    change 2*m < 2*m + (D.map p).1.val
    linarith
  normal := intrinsicCoordinateNormal D
  normal_unit p := D.normal_unit p
  normal_orthogonal p a := by
    rw [intrinsicCoordinateMap_derivative]
    exact D.normal_orthogonal p a

end CKSSchwarzschild

end

end OAI
end


