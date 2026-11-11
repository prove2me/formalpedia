-- Prove2me | Definitions.Def_OAIQ240Bp006
-- name    : OAIQ240Bp006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:45:34.755585+00:00
-- url     : https://prove2.me/theorems/6b22378f-e90f-4d67-9c4f-d6eeb43ff79c
-- title:
--   Definitions bundle OAIQ240Bp006 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 117 declarations of OpenAI's Lean: 40 definitions, 2 inductive types or structures and 75 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.planeTestCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.IsolatingStabilization`, `OAI.HigherDimensionalBallPacking.Rigidity.SmoothZeroAtlas`, `OAI.HigherDimensionalBallPacking.Rigidity.SmoothZeroAtlas.chartedSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.SmoothZeroAtlas.localChart`, `OAI.HigherDimensionalBallPacking.Rigidity.SmoothZeroAtlas.prescribe`, `OAI.HigherDimensionalBallPacking.Rigidity.StabilizedKernelFrame.orientedZeroAtlas`, `OAI.HigherDimensionalBallPacking.Rigidity.StabilizedKernelFrame.physicalProjection`, `OAI.HigherDimensionalBallPacking.Rigidity.ZeroGraphChart.inverse`, `OAI.HigherDimensionalBallPacking.Rigidity.ZeroGraphChart.partialHomeomorph`, `OAI.HigherDimensionalBallPacking.Rigidity.ZeroGraphChart.rebase`, `OAI.HigherDimensionalBallPacking.Rigidity.ZeroGraphChart.reparam`, `OAI.HigherDimensionalBallPacking.Rigidity.ZeroGraphChart.restrict`, `OAI.HigherDimensionalBallPacking.Rigidity.ZeroGraphChart.spatialDerivative`, `OAI.HigherDimensionalBallPacking.Rigidity.blowupPrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.chartCorrection`, `OAI.HigherDimensionalBallPacking.Rigidity.framedChartJacobian`, `OAI.HigherDimensionalBallPacking.Rigidity.frozenInitialChart`, `OAI.HigherDimensionalBallPacking.Rigidity.imageJ`, `OAI.HigherDimensionalBallPacking.Rigidity.infinityGerm`, `OAI.HigherDimensionalBallPacking.Rigidity.inversePullback`, `OAI.HigherDimensionalBallPacking.Rigidity.localizeJ`, `OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.parametricBase`, `OAI.HigherDimensionalBallPacking.Rigidity.parametricEssential`, `OAI.HigherDimensionalBallPacking.Rigidity.radialForm`, `OAI.HigherDimensionalBallPacking.Rigidity.radialPrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.radialPrimitiveCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.stdOmega`, `OAI.HigherDimensionalBallPacking.Rigidity.stdPrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.weightedPrimitive`, `OAI.HigherDimensionalBallPacking.Rigidity.weightedTwoForm`, `OAI.PackingSufficiencySupport.Comparison.fixedIntervalValue`, `OAI.PackingSufficiencySupport.Comparison.intervalEndpoint`, `OAI.PackingSufficiencySupport.Comparison.intervalMinimum`, `OAI.PackingSufficiencySupport.Comparison.intervalValue`, `OAI.PackingSufficiencySupport.Comparison.rearrange`, `OAI.PackingSufficiencySupport.Comparison.unitIntervalValue`, `OAI.PackingSufficiencySupport.Comparison.unitRearrange` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `BallPacking_Cauchy_GreenFormula`, `BallPacking_Compactness_JetCauchy`, `BallPacking_Continuation_ProperPaths`, `BallPacking_Fredholm_FreeLinearization`, `BallPacking_Fredholm_NonlinearReduction`, `BallPacking_Hamiltonian_ScaledPlanarMotion`, `BallPacking_Holder_BanachSpace`, `BallPacking_Holder_MarkedJets`, `BallPacking_Holder_NonlinearCR`, `BallPacking_Moduli_SmoothZeroCharts`, `BallPacking_Moduli_ZeroCharts`, `BallPacking_Moments_ConvexRearrangement`, `BallPacking_Rigidity_Adapted`, `BallPacking_Rigidity_CompatibleStructures`, `BallPacking_Rigidity_Correction`, `BallPacking_Rigidity_CurveArea`, `BallPacking_Rigidity_RadialForm`, `BallPacking_Surfaces_DiagonalQuadric`.
--
--   **Imports.** It imports the published bundle `Def_BallPacking`; the bundles `OAIQ240Bp000`, `OAIQ240Bp001`, `OAIQ240Bp002` and `OAIQ240Bp003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp008`, `OAIQ240Bp009` and `OAIQ240Bp010`; the statement `OAI.HigherDimensionalBallPacking.Rigidity.equicontinuous_CR_derivative_bound_bp240`; the proof of `OAI_HigherDimensionalBallPacking_Rigidity_packing_two_line_reduction`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp000
import Definitions.Def_OAIQ240Bp001
import Definitions.Def_OAIQ240Bp002
import Definitions.Def_OAIQ240Bp003

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_BanachSpace
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped BoundedContinuousFunction Topology ContDiff
open Set Filter
section

variable (X E : Type*) [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {X E}

variable {α : ℝ}

section LinearOperations
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma const_norm_le (e : E) : ‖(const (X := X) α e)‖ ≤ ‖e‖ := by
  change max ‖BoundedContinuousFunction.const X e‖ ‖(0 : Pairs X →ᵇ E)‖ ≤ ‖e‖
  rw [norm_zero]
  exact max_le (BoundedContinuousFunction.norm_const_le e) (norm_nonneg e)

end LinearOperations

end
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1_rb9f788_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.instNormedSpaceRealContinuousLinearMapId_solutions_1
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_2_rb9f788_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapId_solutions_2_rb9f788_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
lemma BoundedCThree.add_const {f : E → F} (hf : BoundedCThree f) (c : F) :
    BoundedCThree (fun x => f x + c) := by
  obtain ⟨M,hM,h0,h1,h2,h3⟩ := hf.bounded
  have he : fderiv ℝ (fun x => f x + c) = fderiv ℝ f := by
    ext x v
    simp only [fderiv_add_const]
  refine ⟨hf.smooth.add contDiff_const, M + ‖c‖, by positivity, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (norm_add_le _ _).trans (add_le_add_left (h0 x) _)
  · intro x; rw [he]; exact (h1 x).trans (le_add_of_nonneg_right (norm_nonneg c))
  · intro x; rw [he]; exact (h2 x).trans (le_add_of_nonneg_right (norm_nonneg c))
  · intro x; rw [he]; exact (h3 x).trans (le_add_of_nonneg_right (norm_nonneg c))

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_NonlinearCR
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma ofBoundedDeriv_norm_le (f : D → F) (hf : Differentiable ℝ f) (M L : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hval : ∀ x, ‖f x‖ ≤ M)
    (hder : ∀ x, ‖fderiv ℝ f x‖ ≤ L) :
    ‖ofBoundedDeriv f hf M L hM hL hval hder‖ ≤ 2*M+L := by
  unfold ofBoundedDeriv
  apply (ofBound_norm_le _ _ _ _ hM _ _ _).trans
  exact max_le (by linarith) le_rfl

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CompatibleStructures
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

theorem compatible_standardJ (n : ℕ) : Compatible (standardJ n) :=
  ⟨standardJ_sq n, standardForm_J_J, fun _ hv => standardForm_J_pos hv⟩

def imageJ {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n) (y : Phase n) : End n :=
  let D := fderiv ℝ f (invFunOn f U y)
  D.comp ((standardJ n).comp D.inverse)

end Rigidity
end
end HigherDimensionalBallPacking

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

theorem contDiffAt_interpolateJ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {J : E → End n} {t : E → ℝ} {x : E}
    (hJs : ContDiffAt ℝ ∞ J x) (hts : ContDiffAt ℝ ∞ t x)
    (hJ : Compatible (J x)) (ht : t x ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y => interpolateJ (J y) (t y)) x := by
  have hA : ContDiffAt ℝ ∞ (fun y => relativeOperator (J y)) x :=
    (contDiffAt_const.clm_comp hJs).neg
  have ha : ContDiffAt ℝ ∞ (fun y => 1 + t y) x := contDiffAt_const.add hts
  have hb : ContDiffAt ℝ ∞ (fun y => 1 - t y) x := contDiffAt_const.sub hts
  have hP : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1+t y) (1-t y)) x :=
    (ha.smul hA).add (hb.smul contDiffAt_const)
  have hQ : ContDiffAt ℝ ∞ (fun y => cayleyP (J y) (1-t y) (1+t y)) x :=
    (hb.smul hA).add (ha.smul contDiffAt_const)
  have hQi := cayleyP_invertible hJ (show 0 < 1 + t x by linarith [ht.1])
    (show 0 ≤ 1 - t x by linarith [ht.2])
  have hI : ContDiffAt ℝ ∞ (fun y => (cayleyP (J y) (1-t y) (1+t y)).inverse) x :=
    ContDiffAt.comp x (g := ContinuousLinearMap.inverse)
      (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (n := ∞) hQi) hQ
  exact contDiffAt_const.clm_comp (hP.clm_comp hI)

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Adapted
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology Manifold
open Set Function Filter


def localizeJ {n : ℕ} (V : Set (Phase n)) (J : Phase n → End n)
    (χ : Phase n → ℝ) (x : Phase n) : End n := by
  classical
  exact if x ∈ V then interpolateJ (J x) (χ x) else standardJ n


end

section
open scoped ContDiff Topology
open Set Function Filter

theorem interpolateJ_standard {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    interpolateJ (standardJ n) t = standardJ n := by
  have ha : 0 < 1+t := by linarith [ht.1]
  have hb : 0 ≤ 1-t := by linarith [ht.2]
  obtain ⟨e,he⟩ := cayleyP_invertible (compatible_standardJ n) ha hb
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator (standardJ n) (1+t) (1-t) ((e : End n) x)) =
    standardJ n ((e : End n) x)
  rw [he,cayleyOperator_on_denominator ⟨e,he⟩]
  congr 1
  simp only [cayleyP_apply,relativeOperator_apply,standardJ_sq,neg_neg]
  module

@[simp] theorem lineHomotopy_zero {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 0 x = standardJ n :=
  interpolateJ_zero (hJ x)

@[simp] theorem lineHomotopy_one {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 1 x = J x :=
  interpolateJ_one (hJ x)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

@[simp] theorem stdDot_J_right {n : ℕ} (v w : Phase n) :
    stdDot n v (standardJ n w) = -standardForm v w := by
  rw [←standardForm_J_right,standardJ_sq,standardForm_neg_right]

@[simp] theorem capacity_eq_stdDot {n : ℕ} (x : Phase n) :
    capacity x = Real.pi * stdDot n x x := by
  rw [←standardForm_J_right,standardForm_J_self]
  rfl

def radialForm {n : ℕ} (σ τ : ℝ) (x v w : Phase n) : ℝ :=
  radialCoefficient σ τ (capacity x) * standardForm v w +
    Real.pi * radialSlope σ τ (capacity x) *
      (stdDot n x v * standardForm x w - stdDot n x w * standardForm x v)

def stdOmega (n : ℕ) : Phase n →L[ℝ] Phase n →L[ℝ] ℝ :=
  -((stdDot n).flip.comp (standardJ n)).flip

@[simp] theorem stdOmega_apply {n : ℕ} (v w : Phase n) :
    stdOmega n v w = standardForm v w := by
  change -(stdDot n v (standardJ n w)) = standardForm v w
  rw [stdDot_J_right,neg_neg]

def radialPrimitiveCLM {n : ℕ} (σ τ : ℝ) (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (radialCoefficient σ τ (capacity x) / 2) • stdOmega n x

def radialPrimitive {n : ℕ} (σ τ : ℝ) (x : Phase n) : Phase n [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (Phase n) ℝ 0 (radialPrimitiveCLM σ τ x)

def infinityGerm {n : ℕ} (u : ℂ → Phase n) (v : Phase n) (w : ℂ) : Phase n :=
  if w = 0 then v else w • u w⁻¹

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Cauchy_GreenFormula
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma smoothCauchyKernel_zero (z : ℂ) : smoothCauchyKernel 0 z = z⁻¹ := by
  rw [smoothCauchyKernel, add_zero, Complex.inv_def,Complex.normSq_eq_norm_sq]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  exact mul_comm _ _

lemma regularizedCauchyJet_zero_fderiv {z : ℂ} (hz : z ≠ 0) :
    regularizedCauchyJet 0 z = fderiv ℝ (fun w : ℂ => w⁻¹) z := by
  have hd := ((hasDerivAt_inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))).comp_hasFDerivAt z
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt).smul
      (starL ℝ : ℂ ≃L[ℝ] ℂ).hasFDerivAt
  have he : (fun w : ℂ => (‖w‖^2)⁻¹ • star w) = fun w : ℂ => w⁻¹ := by
    funext w
    simpa only [smoothCauchyKernel, add_zero] using smoothCauchyKernel_zero w
  change HasFDerivAt (fun w : ℂ => (‖w‖^2)⁻¹ • star w) _ z at hd
  rw [he] at hd
  rw [hd.fderiv]
  ext v
  simp only [regularizedCauchyJet, add_zero, sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,starL'_apply,
    ContinuousLinearEquiv.coe_coe,add_apply,smul_smul,two_smul,Function.comp_apply]
  change (‖z‖^2)⁻¹ • star v - ((2/(‖z‖^2)^2)*(inner ℝ z v)) • star z =
    (‖z‖^2)⁻¹ • star v + (-((‖z‖^2)^2)⁻¹*(inner ℝ z v+inner ℝ z v)) • star z
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2
  simp only [div_eq_mul_inv]
  ring

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma affine_hasFDerivAt (p : E) (a : ℂ →L[ℝ] E) (z : ℂ) :
    HasFDerivAt (affine p a) a z := by
  convert! (hasFDerivAt_const p z).add a.hasFDerivAt using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_add]

lemma affine_differentiable (p : E) (a : ℂ →L[ℝ] E) : Differentiable ℝ (affine p a) :=
  fun z => (affine_hasFDerivAt p a z).differentiableAt

lemma affine_fderiv_bound (p : E) (a : ℂ →L[ℝ] E) (z : ℂ) :
    ‖fderiv ℝ (affine p a) z‖ ≤ ‖a‖ := by rw [(affine_hasFDerivAt p a z).fderiv]


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_JetCauchy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}

def compatibleFrame (J : End n) : End n := cayleyP J 1 1

@[simp] lemma compatibleFrame_apply (J : End n) (v : Phase n) :
    compatibleFrame J v = -standardJ n (J v)+v := by
  simp only [compatibleFrame,cayleyP_apply,one_smul,relativeOperator_apply]

lemma compatibleFrame_invertible {J : End n} (hJ : Compatible J) :
    (compatibleFrame J).IsInvertible := cayleyP_invertible hJ zero_lt_one zero_le_one

lemma compatibleFrame_standard :
    compatibleFrame (standardJ n) = (2:ℝ) • ContinuousLinearMap.id ℝ (Phase n) := by
  ext v i
  simp only [compatibleFrame_apply,standardJ_sq,neg_neg,Pi.add_apply,
    smul_apply,ContinuousLinearMap.id_apply,Pi.smul_apply]
  exact (two_smul ℝ (v i)).symm

lemma compatibleFrame_smooth {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {A : D → End n} (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (fun z => compatibleFrame (A z)) := by
  have hI : ContDiff ℝ ∞ (fun _ : D => standardJ n) := contDiff_const
  simpa only [compatibleFrame,cayleyP,one_smul,relativeOperator] using
    ((hI.clm_comp hA).neg.add (contDiff_const (c := ContinuousLinearMap.id ℝ (Phase n))))

lemma compatibleFrame_inverse_smooth {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {A : D → End n} (hA : ContDiff ℝ ∞ A) (hc : ∀ z, Compatible (A z)) :
    ContDiff ℝ ∞ (fun z => (compatibleFrame (A z)).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (compatibleFrame_invertible (hc z)).contDiffAt_map_inverse.comp z
    (compatibleFrame_smooth hA).contDiffAt

lemma compatibleFrame_inverse_right {J : End n} (hJ : Compatible J) (v : Phase n) :
    compatibleFrame J ((compatibleFrame J).inverse v) = v := by
  obtain ⟨e,he⟩ := compatibleFrame_invertible hJ
  rw [←he]
  simp only [ContinuousLinearMap.inverse_equiv,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

lemma compatibleFrame_inverse_standard :
    (compatibleFrame (standardJ n)).inverse = (1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n) := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨e,he⟩ := compatibleFrame_invertible (compatible_standardJ n)
  apply (show Function.Injective (compatibleFrame (standardJ n)) by rw [←he]; exact e.injective)
  rw [compatibleFrame_inverse_right (compatible_standardJ n)]
  change v = compatibleFrame (standardJ n) ((1/2:ℝ) • v)
  rw [compatibleFrame_standard]
  simp only [smul_apply,ContinuousLinearMap.id_apply,smul_smul]
  norm_num

variable {K : Set ℂ} (hK : IsCompact K) {A : ℂ → End n}
    (hA : ContDiff ℝ ∞ A) (hc : ∀ z, Compatible (A z))
    (hstd : ∀ z ∉ K, A z = standardJ n)

include hK hstd in
lemma compatibleFrame_compactPerturbation :
    HasCompactSupport (fun z => compatibleFrame (A z) - (2:ℝ) • ContinuousLinearMap.id ℝ (Phase n)) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hzK
  apply hz
  change compatibleFrame (A z) - (2:ℝ) • ContinuousLinearMap.id ℝ (Phase n) = 0
  rw [hstd z hzK,compatibleFrame_standard,sub_self]

include hK hstd in
lemma compatibleFrame_inverse_compactPerturbation :
    HasCompactSupport (fun z => (compatibleFrame (A z)).inverse - (1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n)) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hzK
  apply hz
  change (compatibleFrame (A z)).inverse - (1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n) = 0
  rw [hstd z hzK,compatibleFrame_inverse_standard,sub_self]



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CurveArea
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def weightedTwoForm {n : ℕ} (g dg : ℝ) (x v w : Phase n) : ℝ :=
  g * standardForm v w + Real.pi * dg *
    (stdDot n x v * standardForm x w - stdDot n x w * standardForm x v)



open SymplecticBallPacking.Hamiltonian (Plane )

def normalizedPrimitive {n : ℕ} (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (1 / (2 * capacity x)) • stdOmega n x

@[simp] theorem normalizedPrimitive_apply {n : ℕ} (x v : Phase n) :
    normalizedPrimitive x v = standardForm x v / (2 * capacity x) := by
  simp only [normalizedPrimitive,smul_apply,smul_eq_mul,stdOmega_apply]
  ring


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def weightedPrimitive {n : ℕ} (g : ℝ → ℝ) (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (g (capacity x) / 2) • stdOmega n x

def blowupPrimitive {n : ℕ} (σ τ : ℝ) : Phase n → Phase n →L[ℝ] ℝ :=
  weightedPrimitive (blowupCoefficient σ τ)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Correction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def stdPrimitive {n : ℕ} (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (1/2 : ℝ) • stdOmega n x

def inversePullback {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n)
    (α : Phase n → Phase n →L[ℝ] ℝ) (y : Phase n) : Phase n →L[ℝ] ℝ :=
  (α (invFunOn f U y)).comp (fderiv ℝ (invFunOn f U) y)

def chartCorrection {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n)
    (σ τ : ℝ) (y : Phase n) : Phase n →L[ℝ] ℝ := by
  classical
  exact if y ∈ f '' U then inversePullback U f (fun x => blowupPrimitive σ τ x - stdPrimitive x) y
    else 0



open SymplecticBallPacking.Hamiltonian (Plane )


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter MeasureTheory
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma planeTest_norm_bound (g : PlaneTest) (v : ℂ →ᵇ E) :
    ‖∫ z, g.val z • v z‖ ≤ (∫ z, ‖g.val z‖)*‖v‖ := by
  have hi : Integrable g.val := g.property.1.continuous.integrable_of_hasCompactSupport g.property.2
  calc
    _ ≤ ∫ z, ‖g.val z • v z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖g.val z‖*‖v‖ := by
      apply integral_mono (planeTest_integrable g v).norm (hi.norm.mul_const _)
      intro z
      change ‖g.val z • v z‖ ≤ ‖g.val z‖*‖v‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm v z) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

def planeTestCLM (g : PlaneTest) : (ℂ →ᵇ E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ z, g.val z • v z
      map_add' := fun u v => by
        simp only [BoundedContinuousFunction.add_apply,smul_add]
        exact integral_add (planeTest_integrable g u) (planeTest_integrable g v)
      map_smul' := fun c v => by
        simp only [BoundedContinuousFunction.smul_apply]
        simp_rw [smul_comm (g.val _) c]
        exact integral_smul c _ }
    (∫ z, ‖g.val z‖) (planeTest_norm_bound g)

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)

def parametricEssential (F : ℝ × X → Y) (v : (ℝ × pkg.decDom.X₀) × pkg.decDom.X₁) : pkg.decCodom.X₁ :=
  ((codCoords pkg) (F (v.1.1,(domCoords pkg).symm (v.2,v.1.2)))).1

def parametricBase (t : ℝ) (x : X) : (ℝ × pkg.decDom.X₀) × pkg.decDom.X₁ :=
  ((t,((domCoords pkg) x).2),((domCoords pkg) x).1)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma parametricEssential_smooth [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parametricEssential pkg F) :=
  ((codCoords pkg).contDiff.comp (hF.comp (contDiff_fst.fst.prodMk
    ((domCoords pkg).symm.contDiff.comp (contDiff_snd.prodMk contDiff_fst.snd))))).fst

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moduli_ZeroCharts
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ZeroGraphChart
variable {F : ℝ × X → Y} (c : ZeroGraphChart F E)

def inverse (q : ℝ × E) : {v : ℝ × X // F v=0} := by
  classical
  exact if hq : q∈c.domain then ⟨(q.1,c.reconstruct q),c.zero q hq⟩ else ⟨c.base,c.zero_base⟩

omit [NormedSpace ℝ Y] in
lemma inverse_val [NormedSpace ℝ Y] {q : ℝ × E} (hq : q∈c.domain) : (c.inverse q).val=(q.1,c.reconstruct q) := by
  rw [inverse,dite_eq_left hq]

lemma inverse_continuousOn : ContinuousOn c.inverse c.domain := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_induced_rng.mpr
  have hc : Continuous (fun q : c.domain => (q.val.1,c.reconstruct q.val)) :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (continuousOn_iff_continuous_domRestrict.mp c.smooth.continuousOn)
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  exact c.inverse_val q.property

def partialHomeomorph : OpenPartialHomeomorph {v : ℝ × X // F v=0} (ℝ × E) where
  toFun v := (v.val.1,c.coordinate v.val.2)
  invFun := c.inverse
  source := {v | v.val∈c.ambient ∧ (v.val.1,c.coordinate v.val.2)∈c.domain}
  target := c.domain
  map_source' v hv := hv.2
  map_target' q hq := by
    change (c.inverse q).val∈c.ambient ∧ ((c.inverse q).val.1,c.coordinate (c.inverse q).val.2)∈c.domain
    rw [c.inverse_val hq]
    exact ⟨c.image_ambient q hq,by simpa only [c.left_inv,Prod.mk.eta] using hq⟩
  left_inv' v hv := by
    apply Subtype.ext
    rw [c.inverse_val hv.2]
    exact Prod.ext rfl (c.complete v.val hv.1 v.property)
  right_inv' q hq := by
    rw [c.inverse_val hq]
    exact Prod.ext rfl (c.left_inv q)
  continuousOn_toFun :=
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (c.coordinate.continuous.comp (continuous_snd.comp continuous_subtype_val))).continuousOn
  continuousOn_invFun := c.inverse_continuousOn
  open_source := (c.ambient_open.preimage continuous_subtype_val).inter
    (c.domain_open.preimage ((continuous_fst.comp continuous_subtype_val).prodMk
      (c.coordinate.continuous.comp (continuous_snd.comp continuous_subtype_val))))
  open_target := c.domain_open

lemma base_mem_source : (⟨c.base,c.zero_base⟩ : {v : ℝ × X // F v=0})∈c.partialHomeomorph.source :=
  ⟨c.base_ambient,c.base_domain⟩

lemma partialHomeomorph_symm_val {q : ℝ × E} (hq : q∈c.partialHomeomorph.target) :
    (c.partialHomeomorph.symm q).val=(q.1,c.reconstruct q) := c.inverse_val hq

end ZeroGraphChart

end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E E' : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {F : ℝ × X → Y}

def ZeroGraphChart.reparam (c : ZeroGraphChart F E) (e : E ≃L[ℝ] E') : ZeroGraphChart F E' where
  base := c.base
  zero_base := c.zero_base
  coordinate := e.toContinuousLinearMap.comp c.coordinate
  reconstruct := fun q => c.reconstruct (q.1,e.symm q.2)
  domain := (fun q : ℝ × E' => (q.1,e.symm q.2)) ⁻¹' c.domain
  ambient := c.ambient
  domain_open := c.domain_open.preimage (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
  ambient_open := c.ambient_open
  base_domain := by
    change (c.base.1,e.symm (e (c.coordinate c.base.2)))∈c.domain
    simpa only [e.symm_apply_apply] using c.base_domain
  base_ambient := c.base_ambient
  smooth := c.smooth.comp (contDiffOn_fst.prodMk (e.symm.contDiff.contDiffOn.comp contDiffOn_snd (mapsTo_univ _ _)))
    (fun _ h => h)
  left_inv := by
    intro q
    change e (c.coordinate (c.reconstruct (q.1,e.symm q.2)))=q.2
    rw [c.left_inv,e.apply_symm_apply]
  zero := by
    intro q hq
    exact c.zero (q.1,e.symm q.2) hq
  image_ambient := fun q hq => c.image_ambient (q.1,e.symm q.2) hq
  complete := by
    intro v hv hz
    change c.reconstruct (v.1,e.symm (e (c.coordinate v.2)))=v.2
    rw [e.symm_apply_apply]
    exact c.complete v hv hz


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y} (c : ZeroGraphChart F E)

def ZeroGraphChart.spatialDerivative (q : ℝ × E) : E →L[ℝ] X :=
  (fderiv ℝ c.reconstruct q).comp (ContinuousLinearMap.inr ℝ ℝ E)

omit [NormedSpace ℝ Y] in
lemma ZeroGraphChart.spatialDerivative_continuous [NormedSpace ℝ Y] : ContinuousOn c.spatialDerivative c.domain := by
  exact (c.smooth.continuousOn_fderiv_of_isOpen c.domain_open (by norm_num)).clm_comp continuousOn_const

omit [NormedSpace ℝ Y] in
lemma ZeroGraphChart.hasSpatialDerivative [NormedSpace ℝ Y] {q : ℝ × E} (hq : q∈c.domain) :
    HasFDerivAt (fun e => c.reconstruct (q.1,e)) (c.spatialDerivative q) q.2 := by
  have hd : DifferentiableAt ℝ c.reconstruct q :=
    (c.smooth.contDiffAt (c.domain_open.mem_nhds hq)).differentiableAt (by norm_num)
  exact hd.hasFDerivAt.comp q.2 ((hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2))

lemma ZeroGraphChart.spatialDerivative_coordinate {q : ℝ × E} (hq : q∈c.domain) (e : E) :
    c.coordinate (c.spatialDerivative q e)=e := by
  have hd := c.coordinate.hasFDerivAt.comp q.2 (c.hasSpatialDerivative hq)
  have he : (fun z => c.coordinate (c.reconstruct (q.1,z)))=id := funext (fun z => c.left_inv _)
  simp only [Function.comp_def] at hd
  rw [he] at hd
  have hh := hd.unique (hasFDerivAt_id q.2)
  exact congrArg (fun A : E →L[ℝ] E => A e) hh

lemma ZeroGraphChart.spatialDerivative_injective {q : ℝ × E} (hq : q∈c.domain) :
    Injective (c.spatialDerivative q) := by
  intro e f he
  have hh := congrArg c.coordinate he
  simpa only [c.spatialDerivative_coordinate hq] using hh

variable [CompleteSpace X] [CompleteSpace Y]

lemma ZeroGraphChart.spatialDerivative_kernel (hF : ContDiff ℝ ∞ F)
    {q : ℝ × E} (hq : q∈c.domain) (e : E) :
    pathSpatialDerivative F (q.1,c.reconstruct q) (c.spatialDerivative q e)=0 := by
  have hsl : ContDiff ℝ ∞ (fun x => F (q.1,x)) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hd := (hsl.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (c.reconstruct q)).hasFDerivAt.comp q.2
    (c.hasSpatialDerivative hq)
  have he : (fun z => F (q.1,c.reconstruct (q.1,z))) =ᶠ[𝓝 q.2] (fun _ => 0) := by
    have hm : ∀ᶠ z in 𝓝 q.2,(q.1,z)∈c.domain :=
      (continuousAt_const.prodMk continuousAt_id) (c.domain_open.mem_nhds hq)
    filter_upwards [hm] with z hz
    exact c.zero (q.1,z) hz
  have hz := hd.fderiv.symm.trans (he.fderiv_eq)
  simp only [fderiv_fun_const] at hz
  rw [pathSpatialDerivative_eq hF]
  exact congrArg (fun A : E →L[ℝ] Y => A e) hz


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)
  (c : ZeroGraphChart (finiteTargetAugment F E) E)

def framedChartJacobian (q : ℝ × E) : E →L[ℝ] E :=
  (fr.coordinate (q.1,(c.reconstruct q).1)).comp (c.spatialDerivative q)

lemma framedChartJacobian_injective (hF : ContDiff ℝ ∞ F) {q : ℝ × E}
    (hq : q∈c.domain) (hv : (q.1,(c.reconstruct q).1)∈V) :
    Injective (framedChartJacobian fr c q) := by
  have hk (e : E) : ((pathSpatialDerivative F (q.1,(c.reconstruct q).1)).coprod E.subtypeL)
      (c.spatialDerivative q e)=0 := by
    have hh := c.spatialDerivative_kernel (finiteTargetAugment_smooth hF E) hq e
    rw [pathSpatialDerivative_eq (finiteTargetAugment_smooth hF E),finiteTargetAugment_spatial_derivative hF] at hh
    exact hh
  intro e f he
  apply c.spatialDerivative_injective hq
  have hh := congrArg (fr.frame (q.1,(c.reconstruct q).1)) he
  exact (fr.right_inv _ hv _ (hk e)).symm.trans (hh.trans (fr.right_inv _ hv _ (hk f)))

lemma framedChartJacobian_bijective (hF : ContDiff ℝ ∞ F) {q : ℝ × E}
    (hq : q∈c.domain) (hv : (q.1,(c.reconstruct q).1)∈V) :
    Bijective (framedChartJacobian fr c q) :=
  ⟨framedChartJacobian_injective fr c hF hq hv,
    (LinearMap.injective_iff_surjective).mp (framedChartJacobian_injective fr c hF hq hv)⟩

lemma framedChartJacobian_det_ne_zero (hF : ContDiff ℝ ∞ F) {q : ℝ × E}
    (hq : q∈c.domain) (hv : (q.1,(c.reconstruct q).1)∈V) :
    (framedChartJacobian fr c q).det≠0 := by
  let A := LinearEquiv.ofBijective (framedChartJacobian fr c q).toLinearMap
    (framedChartJacobian_bijective fr c hF hq hv)
  exact A.isUnit_det'.ne_zero

omit [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma framedChartJacobian_continuous [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E] :
    ContinuousOn (framedChartJacobian fr c) (c.domain ∩ {q | (q.1,(c.reconstruct q).1)∈V}) := by
  apply ContinuousOn.clm_comp
  · exact fr.coordinate_continuous.comp
      ((continuousOn_fst.mono inter_subset_left).prodMk
        (continuous_fst.continuousOn.comp (c.smooth.continuousOn.mono inter_subset_left)
          (mapsTo_univ _ _))) (fun _ h => h.2)
  · exact c.spatialDerivative_continuous.mono inter_subset_left

lemma framedChart_orientation_neighborhood (hF : ContDiff ℝ ∞ F) (hV : IsOpen V)
    {q : ℝ × E} (hq : q∈c.domain) (hv : (q.1,(c.reconstruct q).1)∈V) :
    ∃ O : Set (ℝ × E),IsOpen O ∧ q∈O ∧ O⊆c.domain ∧
      ∀ r∈O,0<(framedChartJacobian fr c r).det*(framedChartJacobian fr c q).det := by
  have hn := framedChartJacobian_det_ne_zero fr c hF hq hv
  have hm : c.domain ∩ {r | (r.1,(c.reconstruct r).1)∈V}∈𝓝 q := by
    apply inter_mem (c.domain_open.mem_nhds hq)
    exact (continuousAt_fst.prodMk
      (continuous_fst.continuousAt.comp (c.smooth.contDiffAt (c.domain_open.mem_nhds hq)).continuousAt))
        (hV.mem_nhds hv)
  have hc : ContinuousAt (fun r => (framedChartJacobian fr c r).det) q :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      ((framedChartJacobian_continuous fr c q ⟨hq,hv⟩).continuousAt hm)
  have hp : ∀ᶠ r in 𝓝 q,0<(framedChartJacobian fr c r).det*(framedChartJacobian fr c q).det :=
    (hc.mul_const _).eventually (lt_mem_nhds (mul_self_pos.mpr hn))
  obtain ⟨O,hO,hOo,hOq⟩ := mem_nhds_iff.mp (inter_mem (c.domain_open.mem_nhds hq) hp)
  exact ⟨O,hOo,hOq,fun _ h => (hO h).1,fun _ h => (hO h).2⟩


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y} (c d : ZeroGraphChart F E)

lemma zeroChart_transition_derivative {q : ℝ × E} (hq : q∈c.domain)
    (ha : (q.1,c.reconstruct q)∈d.ambient)
    (hr : (q.1,d.coordinate (c.reconstruct q))∈d.domain) :
    (d.spatialDerivative (q.1,d.coordinate (c.reconstruct q))).comp
      (d.coordinate.comp (c.spatialDerivative q))=c.spatialDerivative q := by
  have hc := c.hasSpatialDerivative hq
  have hd := (d.hasSpatialDerivative hr).comp q.2 (d.coordinate.hasFDerivAt.comp q.2 hc)
  have he : (fun z => d.reconstruct (q.1,d.coordinate (c.reconstruct (q.1,z)))) =ᶠ[𝓝 q.2]
      (fun z => c.reconstruct (q.1,z)) := by
    have hm : ∀ᶠ z in 𝓝 q.2,(q.1,z)∈c.domain :=
      (continuousAt_const.prodMk continuousAt_id) (c.domain_open.mem_nhds hq)
    have hn : ∀ᶠ z in 𝓝 q.2,(q.1,c.reconstruct (q.1,z))∈d.ambient :=
      (continuousAt_const.prodMk hc.continuousAt) (d.ambient_open.mem_nhds ha)
    filter_upwards [hm,hn] with z hz hza
    exact d.complete (q.1,c.reconstruct (q.1,z)) hza (c.zero (q.1,z) hz)
  exact hd.fderiv.symm.trans (he.fderiv_eq.trans hc.fderiv)


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)
  (c d : ZeroGraphChart (finiteTargetAugment F E) E)

omit [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma framedChart_transition_identity [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E]
    {q : ℝ × E} (hq : q∈c.domain)
    (ha : (q.1,c.reconstruct q)∈d.ambient)
    (hr : (q.1,d.coordinate (c.reconstruct q))∈d.domain) :
    (framedChartJacobian fr d (q.1,d.coordinate (c.reconstruct q))).comp
      (d.coordinate.comp (c.spatialDerivative q))=framedChartJacobian fr c q := by
  have he := d.complete (q.1,c.reconstruct q) ha (c.zero q hq)
  change ((fr.coordinate (q.1,(d.reconstruct (q.1,d.coordinate (c.reconstruct q))).1)).comp
    (d.spatialDerivative (q.1,d.coordinate (c.reconstruct q)))).comp _=_
  rw [he,ContinuousLinearMap.comp_assoc,zeroChart_transition_derivative c d hq ha hr]
  rfl

lemma framedChart_transition_det {q : ℝ × E} (hq : q∈c.domain)
    (ha : (q.1,c.reconstruct q)∈d.ambient)
    (hr : (q.1,d.coordinate (c.reconstruct q))∈d.domain) :
    (framedChartJacobian fr d (q.1,d.coordinate (c.reconstruct q))).det *
      (d.coordinate.comp (c.spatialDerivative q)).det=(framedChartJacobian fr c q).det := by
  have he := congrArg (fun A : E →L[ℝ] E => A.det) (framedChart_transition_identity fr c d hq ha hr)
  change LinearMap.det ((framedChartJacobian fr d (q.1,d.coordinate (c.reconstruct q))).toLinearMap.comp
    (d.coordinate.comp (c.spatialDerivative q)).toLinearMap)=_ at he
  simpa only [LinearMap.det_comp] using he

lemma framedChart_transition_signed_det (hF : ContDiff ℝ ∞ F)
    {q : ℝ × E} (hq : q∈c.domain) (hv : (q.1,(c.reconstruct q).1)∈V)
    (ha : (q.1,c.reconstruct q)∈d.ambient)
    (hr : (q.1,d.coordinate (c.reconstruct q))∈d.domain) :
    Real.sign (framedChartJacobian fr c q).det * (d.coordinate.comp (c.spatialDerivative q)).det =
      Real.sign (framedChartJacobian fr d (q.1,d.coordinate (c.reconstruct q))).det *
        |(d.coordinate.comp (c.spatialDerivative q)).det| := by
  have he := framedChart_transition_det fr c d hq ha hr
  have hn := framedChartJacobian_det_ne_zero fr c hF hq hv
  have hn' : (framedChartJacobian fr d (q.1,d.coordinate (c.reconstruct q))).det≠0 := by
    intro hz
    rw [hz,zero_mul] at he
    exact hn he.symm
  have htn : (d.coordinate.comp (c.spatialDerivative q)).det≠0 := by
    intro hz
    rw [hz,mul_zero] at he
    exact hn he.symm
  rw [←he]
  rcases lt_or_gt_of_ne hn' with hd | hd <;> rcases lt_or_gt_of_ne htn with ht | ht
  · rw [Real.sign_of_pos (mul_pos_of_neg_of_neg hd ht),Real.sign_of_neg hd,abs_of_neg ht]
    ring
  · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos hd ht),Real.sign_of_neg hd,abs_of_pos ht]
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hd ht),Real.sign_of_pos hd,abs_of_neg ht]
    ring
  · rw [Real.sign_of_pos (mul_pos hd ht),Real.sign_of_pos hd,abs_of_pos ht]


end
open scoped ContDiff Topology
open Set Function Filter
variable {P Q Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma implicitFunction_smooth_neighborhood {f : P × Q → Y} (hf : ContDiff ℝ ∞ f)
    {u : P × Q} (hi : ((fderiv ℝ f u).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible) :
    ∃ D : Set P,IsOpen D ∧ u.1∈D ∧
      ContDiffOn ℝ ∞ (hf.contDiffAt.implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi) D := by
  let ψ := hf.contDiffAt.implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi
  have hs : ContDiffAt ℝ ∞ ψ u.1 := hf.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi
  have hb : ψ u.1=u.2 := hf.contDiffAt.implicitFunction_apply_self (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi
  obtain ⟨S,hSn,hSs⟩ := hs.contDiffOn (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hψf : ∀ᶠ p in 𝓝 u.1,f (p,ψ p)=f u := hf.contDiffAt.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi
  have hder : Continuous (fun v : P × Q => (fderiv ℝ f v).comp (ContinuousLinearMap.inr ℝ P Q)) :=
    (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp continuous_const
  have hival : ((fderiv ℝ f (u.1,ψ u.1)).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible := by
    simpa only [hb,Prod.mk.eta] using hi
  have hin : ∀ᶠ p in 𝓝 u.1,((fderiv ℝ f (p,ψ p)).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible :=
    (hder.continuousAt.comp (continuousAt_id.prodMk hs.continuousAt))
      (ContinuousLinearEquiv.isOpen.mem_nhds hival)
  obtain ⟨D,hD,hDo,hDu⟩ := mem_nhds_iff.mp (inter_mem hSn (inter_mem hψf hin))
  refine ⟨D,hDo,hDu,smooth_actual_implicit_branch hf hDo (hSs.continuousOn.mono (fun _ h => (hD h).1))
    (f u) (fun _ h => (hD h).2.1) (fun _ h => (hD h).2.2)⟩



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moduli_SmoothZeroCharts
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y}

def ZeroGraphChart.restrict (c : ZeroGraphChart F E)
    (D : Set (ℝ × E)) (hD : IsOpen D) (hDc : D⊆c.domain)
    (hb : (c.base.1,c.coordinate c.base.2)∈D) : ZeroGraphChart F E where
  base := c.base
  zero_base := c.zero_base
  coordinate := c.coordinate
  reconstruct := c.reconstruct
  domain := D
  ambient := c.ambient
  domain_open := hD
  ambient_open := c.ambient_open
  base_domain := hb
  base_ambient := c.base_ambient
  smooth := c.smooth.mono hDc
  left_inv := c.left_inv
  zero := fun q hq => c.zero q (hDc hq)
  image_ambient := fun q hq => c.image_ambient q (hDc hq)
  complete := c.complete

omit [NormedSpace ℝ Y] in
lemma ZeroGraphChart.reparam_smooth [NormedSpace ℝ Y] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (c : ZeroGraphChart F E) (hc : ContDiffOn ℝ ∞ c.reconstruct c.domain) (e : E ≃L[ℝ] E') :
    ContDiffOn ℝ ∞ (c.reparam e).reconstruct (c.reparam e).domain :=
  hc.comp ((contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)).contDiffOn) (fun _ h => h)


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : ℝ × X → Y}

structure SmoothZeroAtlas (F : ℝ × X → Y) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : TopologicalSpace.Opens {v : ℝ × X // F v=0}) where
  chart : s → ZeroGraphChart F E
  base : ∀ x,(chart x).base=x.val.val
  smooth : ∀ x,ContDiffOn ℝ ∞ (chart x).reconstruct (chart x).domain

namespace SmoothZeroAtlas
variable {s : TopologicalSpace.Opens {v : ℝ × X // F v=0}}
  (a : SmoothZeroAtlas F E s)

def localChart (x : s) : OpenPartialHomeomorph s (ℝ × E) :=
  (a.chart x).partialHomeomorph.subtypeRestr ⟨x⟩

lemma localChart_apply (x z : s) : a.localChart x z=(z.val.val.1,(a.chart x).coordinate z.val.val.2) := rfl

lemma localChart_target (x : s) : (a.localChart x).target⊆(a.chart x).domain :=
  (a.chart x).partialHomeomorph.subtypeRestr_target_subset ⟨x⟩

lemma localChart_symm_val (x : s) {q : ℝ × E} (hq : q∈(a.localChart x).target) :
    ((a.localChart x).symm q).val.val=(q.1,(a.chart x).reconstruct q) := by
  have he := (a.chart x).partialHomeomorph.subtypeRestr_symm_apply ⟨x⟩ hq
  change ((a.localChart x).symm q).val=(a.chart x).partialHomeomorph.symm q at he
  rw [he]
  exact (a.chart x).partialHomeomorph_symm_val (a.localChart_target x hq)

@[instance_reducible]
def chartedSpace : ChartedSpace (ℝ × E) s where
  atlas := range a.localChart
  chartAt := a.localChart
  mem_chart_source x := by
    rw [localChart,OpenPartialHomeomorph.subtypeRestr_source]
    change x.val∈(a.chart x).partialHomeomorph.source
    have hb := (a.chart x).base_mem_source
    have he : (⟨(a.chart x).base,(a.chart x).zero_base⟩ : {v : ℝ × X // F v=0})=x.val :=
      Subtype.ext (a.base x)
    rwa [he] at hb
  chart_mem_atlas x := mem_range_self x

lemma transition_smooth (x y : s) :
    ContDiffOn ℝ ∞ ((a.localChart x).symm ≫ₕ a.localChart y)
      ((a.localChart x).symm ≫ₕ a.localChart y).source := by
  have hc : ContDiffOn ℝ ∞ (fun q : ℝ × E => (q.1,(a.chart y).coordinate ((a.chart x).reconstruct q)))
      (a.chart x).domain :=
    contDiffOn_fst.prodMk ((a.chart y).coordinate.contDiff.comp_contDiffOn (a.smooth x))
  apply (hc.mono (fun q hq => a.localChart_target x hq.1)).congr
  intro q hq
  change a.localChart y ((a.localChart x).symm q)=
    (q.1,(a.chart y).coordinate ((a.chart x).reconstruct q))
  rw [a.localChart_apply,a.localChart_symm_val x hq.1]

end SmoothZeroAtlas

end
section
open scoped ContDiff Topology
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {F : ℝ × X → Y}

omit [NormedSpace ℝ Y] in
lemma zeroChart_time_transition_det [NormedSpace ℝ Y] (c d : ZeroGraphChart F E) {q : ℝ × E}
    (hq : q∈c.domain) :
    (fderiv ℝ (fun r : ℝ × E => (r.1,d.coordinate (c.reconstruct r))) q).det =
      (d.coordinate.comp (c.spatialDerivative q)).det := by
  have hc := (c.smooth.contDiffAt (c.domain_open.mem_nhds hq)).differentiableAt (by norm_num)
  have hd := (hasFDerivAt_fst (p := q)).prodMk (d.coordinate.hasFDerivAt.comp q hc.hasFDerivAt)
  simp only [Function.comp_def] at hd
  rw [hd.fderiv,timePreserving_linear_det]
  rfl


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)
  (hF : ContDiff ℝ ∞ F) (hV : IsOpen V)
  (a : SmoothZeroAtlas (finiteTargetAugment F E) E (framedZeroOpen F E V hV))

omit [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma framedLocalChart_V [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E]
    (x : framedZeroOpen F E V hV) {q : ℝ × E}
    (hq : q∈(a.localChart x).target) : (q.1,((a.chart x).reconstruct q).1)∈V := by
  have hv := ((a.localChart x).symm q).property
  change (((a.localChart x).symm q).val.val.1,((a.localChart x).symm q).val.val.2.1)∈V at hv
  rwa [a.localChart_symm_val x hq] at hv

include hF in
lemma framedLocalChart_signed_transition (x y : framedZeroOpen F E V hV)
    {q : ℝ × E} (hq : q∈((a.localChart x).symm ≫ₕ a.localChart y).source) :
    Real.sign (framedChartJacobian fr (a.chart x) q).det *
      (fderiv ℝ (a.localChart y ∘ (a.localChart x).symm) q).det =
    Real.sign (framedChartJacobian fr (a.chart y) (a.localChart y ((a.localChart x).symm q))).det *
      |(fderiv ℝ (a.localChart y ∘ (a.localChart x).symm) q).det| := by
  have hqx := a.localChart_target x hq.1
  have hh : ((a.localChart x).symm q).val∈(a.chart y).partialHomeomorph.source := by
    simpa only [OpenPartialHomeomorph.symm_symm,Set.mem_preimage,SmoothZeroAtlas.localChart,
      OpenPartialHomeomorph.subtypeRestr_source] using hq.2
  change ((a.localChart x).symm q).val.val∈(a.chart y).ambient ∧
    (((a.localChart x).symm q).val.val.1,(a.chart y).coordinate ((a.localChart x).symm q).val.val.2)∈
      (a.chart y).domain at hh
  rw [a.localChart_symm_val x hq.1] at hh
  have he : (a.localChart y ∘ (a.localChart x).symm) =ᶠ[𝓝 q]
      (fun r => (r.1,(a.chart y).coordinate ((a.chart x).reconstruct r))) := by
    filter_upwards [((a.localChart x).symm ≫ₕ a.localChart y).open_source.mem_nhds hq] with r hr
    change a.localChart y ((a.localChart x).symm r)=_
    rw [a.localChart_apply,a.localChart_symm_val x hr.1]
  rw [he.fderiv_eq,zeroChart_time_transition_det _ _ hqx]
  rw [a.localChart_apply,a.localChart_symm_val x hq.1]
  exact framedChart_transition_signed_det fr (a.chart x) (a.chart y) hF hqx
    (framedLocalChart_V hV a x hq.1) hh.1 hh.2

omit [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma framedLocalChart_base_target [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ E]
    (x : framedZeroOpen F E V hV) :
    a.localChart x x∈(a.localChart x).target :=
  (a.localChart x).map_source (a.chartedSpace.mem_chart_source x)

def StabilizedKernelFrame.orientedZeroAtlas :
    Degree.SignedModelAtlas (framedZeroOpen F E V hV) (framedZeroOpen F E V hV) (ℝ × E) := by
  classical
  have ho (x : framedZeroOpen F E V hV) := framedChart_orientation_neighborhood fr (a.chart x) hF hV
    (a.localChart_target x (framedLocalChart_base_target hV a x))
    (framedLocalChart_V hV a x (framedLocalChart_base_target hV a x))
  let O := fun x => (ho x).choose
  have hO (x) := (ho x).choose_spec
  let c := fun x => ((a.localChart x).symm.restrOpen (O x) (hO x).1).symm
  refine {
    chart := c
    cover := ?_
    sign := fun x => Real.sign (framedChartJacobian fr (a.chart x) (a.localChart x x)).det
    sign_sq := ?_
    transition_smooth := ?_
    orientation := ?_ }
  · intro x
    refine ⟨x,?_⟩
    exact ⟨a.chartedSpace.mem_chart_source x,(hO x).2.1⟩
  · intro x
    have hn := framedChartJacobian_det_ne_zero fr (a.chart x) hF
      (a.localChart_target x (framedLocalChart_base_target hV a x))
      (framedLocalChart_V hV a x (framedLocalChart_base_target hV a x))
    rcases Real.sign_apply_eq_of_ne_zero _ hn with h|h <;> rw [h] <;> norm_num
  · intro x y
    apply (a.transition_smooth x y).mono
    intro q hq
    exact ⟨hq.1.1,hq.2.1⟩
  · intro x y q hq
    have hq' : q∈((a.localChart x).symm ≫ₕ a.localChart y).source := ⟨hq.1.1,hq.2.1⟩
    have hx := sign_eq_of_mul_pos ((hO x).2.2.2 q hq.1.2)
    have hy := sign_eq_of_mul_pos ((hO y).2.2.2 (a.localChart y ((a.localChart x).symm q)) hq.2.2)
    change Real.sign (framedChartJacobian fr (a.chart x) (a.localChart x x)).det *
        (fderiv ℝ (a.localChart y ∘ (a.localChart x).symm) q).det =
      Real.sign (framedChartJacobian fr (a.chart y) (a.localChart y y)).det *
        |(fderiv ℝ (a.localChart y ∘ (a.localChart x).symm) q).det|
    rw [←hx,←hy]
    exact framedLocalChart_signed_transition fr hF hV a x y hq'


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)
  (hF : ContDiff ℝ ∞ F) (hV : IsOpen V)
  (a : SmoothZeroAtlas (finiteTargetAugment F E) E (framedZeroOpen F E V hV))

lemma orientedZeroAtlas_target (x : framedZeroOpen F E V hV) :
    ((fr.orientedZeroAtlas hF hV a).chart x).target⊆(a.localChart x).target := by
  intro q hq
  exact hq.1

 def StabilizedKernelFrame.physicalProjection :
    Degree.ModelAtlasSmoothMap (fr.orientedZeroAtlas hF hV a) (ℝ × E) where
  map z := (z.val.val.1,z.val.val.2.2)
  smooth x := by
    have hs : ContDiffOn ℝ ∞ (fun q : ℝ × E => (q.1,((a.chart x).reconstruct q).2))
        (a.chart x).domain := contDiffOn_fst.prodMk (contDiff_snd.comp_contDiffOn (a.smooth x))
    apply (hs.mono (fun q hq => a.localChart_target x (orientedZeroAtlas_target fr hF hV a x hq))).congr
    intro q hq
    change (((a.localChart x).symm q).val.val.1,((a.localChart x).symm q).val.val.2.2)=_
    rw [a.localChart_symm_val x (orientedZeroAtlas_target fr hF hV a x hq)]


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

structure IsolatingStabilization (F : ℝ × X → Y) (U : Set X)
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (N : Set (ℝ × (X × E))) : Prop where
  isOpen : IsOpen N
  contains : ∀ t∈Icc (0:ℝ) 1,∀ x∈U,F (t,x)=0 →(t,(x,0))∈N
  compact : IsCompact (closure N ∩ {v | finiteTargetAugment F E v=0})
  domain : ∀ v∈closure N,finiteTargetAugment F E v=0 →v.2.1∈U
  germs : ∀ v∈closure N,v.1∈Icc (0:ℝ) 1 →finiteTargetAugment F E v=0 →
    Nonempty (FiniteZeroGerm (finiteTargetAugment F E) v.1 v.2 (Module.finrank ℝ E))


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_ProperPaths
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  (L : X ≃L[ℝ] Y) (hL : ∀ x,F (0,x)=L x)

def frozenInitialChart : ZeroGraphChart (finiteTargetAugment (frozenPath F) E) E where
  base := (0,(0,0))
  zero_base := by
    change F (freezeTime 0,0)+(0:Y)=0
    rw [freezeTime_initial (by norm_num),hL,map_zero,add_zero]
  coordinate := ContinuousLinearMap.snd ℝ X E
  reconstruct q := initialKernelGraph L E q.2
  domain := {q | q.1<1/4}
  ambient := {v | v.1<1/4}
  domain_open := isOpen_lt continuous_fst continuous_const
  ambient_open := isOpen_lt continuous_fst continuous_const
  base_domain := by norm_num
  base_ambient := by norm_num
  smooth := ((initialKernelGraph L E).contDiff.comp contDiff_snd).contDiffOn
  left_inv q := rfl
  zero q hq := by
    change F (freezeTime q.1,-L.symm (q.2:Y))+(q.2:Y)=0
    rw [freezeTime_initial (le_of_lt hq),hL,map_neg,L.apply_symm_apply,neg_add_cancel]
  image_ambient q hq := hq
  complete v hv hz := by
    change initialKernelGraph L E v.2.2=v.2
    apply (initialKernelGraph_kernel v.2).mp
    change F (freezeTime v.1,v.2.1)+(v.2.2:Y)=0 at hz
    rwa [freezeTime_initial (le_of_lt hv),hL] at hz


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ × X → Y}

 def ZeroGraphChart.rebase (c : ZeroGraphChart F E) (p : {v : ℝ × X // F v=0})
    (hp : p∈c.partialHomeomorph.source) : ZeroGraphChart F E :=
  {c with base := p.val,zero_base := p.property,base_domain := hp.2,base_ambient := hp.1}

 def SmoothZeroAtlas.prescribe {s : TopologicalSpace.Opens {v : ℝ × X // F v=0}}
    (a : SmoothZeroAtlas F E s) (p : s) (c : ZeroGraphChart F E)
    (hp : p.val∈c.partialHomeomorph.source) (hc : ContDiffOn ℝ ∞ c.reconstruct c.domain) :
    SmoothZeroAtlas F E s := by
  classical
  refine {chart := fun x => if x=p then c.rebase p.val hp else a.chart x,base := ?_,smooth := ?_}
  · intro x
    by_cases hx : x=p
    · subst x; simp only; rfl
    · simp only [ite_eq_right hx]; exact a.base x
  · intro x
    by_cases hx : x=p
    · simp only [ite_eq_left hx]; exact hc
    · simp only [ite_eq_right hx]; exact a.smooth x

@[simp] lemma SmoothZeroAtlas.prescribe_at {s : TopologicalSpace.Opens {v : ℝ × X // F v=0}}
    (a : SmoothZeroAtlas F E s) (p : s) (c : ZeroGraphChart F E)
    (hp : p.val∈c.partialHomeomorph.source) (hc : ContDiffOn ℝ ∞ c.reconstruct c.domain) :
    (a.prescribe p c hp hc).chart p=c.rebase p.val hp := by
  classical
  simp [SmoothZeroAtlas.prescribe]


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_DiagonalQuadric
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function

variable {m : ℕ}

theorem branch_augmented_regular_bijective {z : Affine m} (ht : z.1≠0)
    (i : Fin m) (hw : ∀ j,j≠i → z.2 j≠0) :
    Bijective (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))).prod
      (jacobian z)) := by
  classical
  constructor
  · intro v w h
    have hwi : v.2 i=w.2 i := congrArg (fun x : Affine m => x.1) h
    have he j := congrArg (fun x : Affine m => x.2 j) h
    have hti := he i
    change 2*z.2 i*v.2 i-2*z.1*v.1=2*z.2 i*w.2 i-2*z.1*w.1 at hti
    have hm : 2*z.1*v.1=2*z.1*w.1 := by rw [hwi] at hti; linear_combination -hti
    have htv : v.1=w.1 := mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) ht) hm
    apply Prod.ext htv
    funext j
    by_cases hji : j=i
    · subst j; exact hwi
    · have hej := he j
      change 2*z.2 j*v.2 j-2*z.1*v.1=2*z.2 j*w.2 j-2*z.1*w.1 at hej
      rw [htv] at hej
      have hm : (2*z.2 j)*v.2 j=(2*z.2 j)*w.2 j := by linear_combination hej
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) (hw j hji)) hm
  · rintro ⟨t,y⟩
    let v : ℂ := (2*z.2 i*t-y i)/(2*z.1)
    have hv : 2*z.1*v=2*z.2 i*t-y i :=
      mul_div_cancel₀ _ (mul_ne_zero (by norm_num : (2:ℂ)≠0) ht)
    refine ⟨(v,fun j => if j=i then t else (y j+2*z.1*v)/(2*z.2 j)),?_⟩
    apply Prod.ext
    · change (if i=i then t else (y i+2*z.1*v)/(2*z.2 i))=t
      simp only [ite_true, if_true]
    · funext j
      change 2*z.2 j*(if j=i then t else (y j+2*z.1*v)/(2*z.2 j))-2*z.1*v=y j
      by_cases hji : j=i
      · subst j
        rw [ite_eq_left rfl,hv]
        ring
      · rw [ite_eq_right hji,mul_div_cancel₀ _ (mul_ne_zero (by norm_num) (hw j hji)),add_sub_cancel_right]

theorem regularCoordinate_bijective (c : Option (Fin m)) {z : Affine m}
    (hz : z∈regularCoordinate c) : Bijective ((curveCoordinate c).prod (jacobian z)) := by
  cases c with
  | none => exact ordinary_augmented_bijective hz
  | some i => exact branch_augmented_regular_bijective hz.1 i hz.2

theorem exists_normal_straightening (a : Fin m → ℂ) (c : Option (Fin m))
    {z : Affine m} (hz : z∈regularCoordinate c) :
    ∃ e : OpenPartialHomeomorph (Affine m) (Affine m),
      z∈e.source ∧ e.source⊆regularCoordinate c ∧
      (e : Affine m → Affine m)=normalCoordinates a c ∧
      ContDiff ℂ ∞ (e : Affine m → Affine m) ∧
      ContDiffOn ℂ ∞ (e.symm : Affine m → Affine m) e.target := by
  let A := (curveCoordinate c).prod (jacobian z)
  have hb := regularCoordinate_bijective c hz
  let L : Affine m ≃L[ℂ] Affine m := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hd : HasFDerivAt (normalCoordinates a c) (L : Affine m →L[ℂ] Affine m) z :=
    normalCoordinates_hasFDerivAt a c z
  let e₀ := (normalCoordinates_contDiff a c).contDiffAt.toOpenPartialHomeomorph
    (normalCoordinates a c) hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let e := e₀.restrOpen (regularCoordinate c) (regularCoordinate_isOpen c)
  have he : (e : Affine m → Affine m)=normalCoordinates a c := rfl
  have heSub : e.source⊆regularCoordinate c := inter_subset_right
  refine ⟨e,⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),hz⟩,
    heSub,he,normalCoordinates_contDiff a c,?_⟩
  intro y hy
  have hreg := heSub (e.map_target hy)
  have hb' := regularCoordinate_bijective c hreg
  let B := (curveCoordinate c).prod (jacobian (e.symm y))
  let K : Affine m ≃L[ℂ] Affine m := ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr hb'.1) (LinearMap.range_eq_top.mpr hb'.2)
  exact (e.contDiffAt_symm (𝕜 := ℂ) (f₀' := K) hy
    (normalCoordinates_hasFDerivAt a c (e.symm y))
      (normalCoordinates_contDiff a c).contDiffAt).contDiffWithinAt

theorem exists_normalChart_at {a : Fin m → ℂ} (ha : Injective a) (ha0 : ∀ j,a j≠0)
    (x : locus a) : ∃ e : NormalChart a,(x : Affine m)∈e.ambient.source := by
  obtain ⟨c,hc⟩ := exists_regularCoordinate ha ha0 x.property
  obtain ⟨e,he,_hreg,heq,_hf,hg⟩ := exists_normal_straightening a c hc
  exact ⟨⟨c,e,heq,hg⟩,he⟩

namespace NormalChart
variable {a : Fin m → ℂ} (e : NormalChart a)

theorem sliceInverse_eq (x : locus a) {t : ℂ} (ht : (t,0)∈e.ambient.target) :
    (e.sliceInverse x t : Affine m)=e.ambient.symm (t,0) := by
  simp only [sliceInverse,dite_eq_left ht]

def sliceChart (x : locus a) : OpenPartialHomeomorph (locus a) ℂ where
  toFun y := curveCoordinate e.coordinate y.val
  invFun := e.sliceInverse x
  source := Subtype.val ⁻¹' e.ambient.source
  target := (fun t : ℂ => (t,(0 : Fin m → ℂ))) ⁻¹' e.ambient.target
  map_source' := by
    intro y hy
    have he := e.ambient.map_source hy
    rw [e.ambient_apply] at he
    have hy0 : equations a y.val=0 := y.property
    change (curveCoordinate e.coordinate y.val,(0 : Fin m → ℂ))∈e.ambient.target
    simpa only [hy0] using he
  map_target' := by
    intro t ht
    change (e.sliceInverse x t : Affine m)∈e.ambient.source
    rw [e.sliceInverse_eq x ht]
    exact e.ambient.map_target ht
  left_inv' := by
    intro y hy
    have hy0 : equations a y.val=0 := y.property
    have hyt : (curveCoordinate e.coordinate y.val,0)∈e.ambient.target := by
      simpa only [e.ambient_apply,hy0] using e.ambient.map_source hy
    apply Subtype.ext
    rw [e.sliceInverse_eq x hyt]
    have he : (curveCoordinate e.coordinate y.val,0)=e.ambient y.val := by
      rw [e.ambient_apply,hy0]
    rw [he]
    exact e.ambient.left_inv hy
  right_inv' := by
    intro t ht
    rw [e.sliceInverse_eq x ht]
    simpa only [e.ambient_apply] using congrArg Prod.fst (e.ambient.right_inv ht)
  open_source := e.ambient.open_source.preimage continuous_subtype_val
  open_target := e.ambient.open_target.preimage (continuous_id.prodMk continuous_const)
  continuousOn_toFun := ((curveCoordinate e.coordinate).continuous.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_induced_rng.mpr
    have hc := e.ambient.continuousOn_symm.comp
      (show Continuous (fun t : ℂ => (t,(0 : Fin m → ℂ))) from
        continuous_id.prodMk continuous_const).continuousOn (mapsTo_preimage _ _)
    rw [continuousOn_iff_continuous_domRestrict] at hc
    exact hc.congr (fun t => (e.sliceInverse_eq x t.property).symm)

@[simp] theorem sliceChart_apply (x y : locus a) :
    e.sliceChart x y=curveCoordinate e.coordinate y.val := rfl

@[simp] theorem sliceChart_source (x : locus a) :
    (e.sliceChart x).source=Subtype.val ⁻¹' e.ambient.source := rfl

@[simp] theorem sliceChart_target (x : locus a) :
    (e.sliceChart x).target=(fun t : ℂ => (t,(0 : Fin m → ℂ))) ⁻¹' e.ambient.target := rfl

end NormalChart

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ConvexRearrangement
attribute [-instance] _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff ENNReal Pointwise Classical
namespace PackingSufficiencySupport
open MeasureTheory
namespace Comparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Minimum
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

theorem minimum_attained (F : C(X, ℝ)) : ∃ x, F x = minimum F :=
  (isCompact_range F.continuous).sInf_mem (Set.range_nonempty F)

omit [Nonempty X] in
theorem minimum_le (F : C(X, ℝ)) (x : X) : minimum F ≤ F x :=
  csInf_le (isCompact_range F.continuous).bddBelow ⟨x, rfl⟩

theorem minimum_lipschitz : LipschitzWith 1 (minimum : C(X, ℝ) → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro F G
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  apply abs_sub_le_iff.mpr
  constructor
  · obtain ⟨x, hx⟩ := minimum_attained G
    have h := (abs_sub_le_iff.mp (ContinuousMap.dist_apply_le_dist (f := F) (g := G) x)).1
    have hf := minimum_le F x
    rw [hx] at h
    linarith
  · obtain ⟨x, hx⟩ := minimum_attained F
    have h := (abs_sub_le_iff.mp (ContinuousMap.dist_apply_le_dist (f := F) (g := G) x)).2
    have hg := minimum_le G x
    rw [hx] at h
    linarith

end Minimum

section SlicedDomain
variable (Y : Set E) (L : E → ℝ)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem intervalEndpoint_mem (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1)
    (xt : Slice Y L × UnitInterval) :
    (xt.1.val.1, xt.2.val * (L xt.1.val.1 - xt.1.val.2) + δ * xt.1.val.2)
      ∈ sliceDomain Y L := by
  refine ⟨xt.1.property.1, ?_, ?_⟩
  · have ht := xt.2.property.1
    have hx := xt.1.property.2
    change 0 ≤ xt.2.val * (L xt.1.val.1 - xt.1.val.2) + δ * xt.1.val.2
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hx.2), mul_nonneg hδ.1 hx.1]
  · have ht := xt.2.property.2
    have hx := xt.1.property.2
    change xt.2.val * (L xt.1.val.1 - xt.1.val.2) + δ * xt.1.val.2 ≤ L xt.1.val.1
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hx.2),
      mul_nonneg (sub_nonneg.mpr hδ.2) hx.1]

def intervalEndpoint (hL : ContinuousOn L Y) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    C(Slice Y L × UnitInterval, Slice Y L) := by
  refine ⟨fun xt => ⟨(xt.1.val.1, xt.2.val * (L xt.1.val.1 - xt.1.val.2) +
    δ * xt.1.val.2), intervalEndpoint_mem Y L δ hδ xt⟩, ?_⟩
  apply Continuous.subtype_mk
  apply Continuous.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
  exact ((continuous_subtype_val.comp continuous_snd).mul
    (((sliceLength Y L hL).continuous.comp continuous_fst).sub
      ((sliceHeight Y L).continuous.comp continuous_fst))).add
      (((sliceHeight Y L).continuous.comp continuous_fst).const_mul δ)

def intervalValue (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ)) :
    C(Slice Y L × UnitInterval, ℝ) :=
  F.comp (intervalEndpoint Y L hL 0 (by norm_num)) ⊔
    F.comp (intervalEndpoint Y L hL 1 (by norm_num))

def rearrange (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ)) : C(Slice Y L, ℝ) :=
  ⟨fun x => minimum ((intervalValue Y L hL F).curry x),
    minimum_lipschitz.continuous.comp (intervalValue Y L hL F).curry.continuous⟩

omit [NormedSpace ℝ E] in
theorem intervalValue_eq_candidate (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ))
    (x : Slice Y L) (t : UnitInterval) :
    intervalValue Y L hL F (x, t) =
      intervalCandidate Y L F x (t.val * (L x.val.1 - x.val.2))
        (mul_nonneg t.property.1 (sub_nonneg.mpr x.property.2.2))
        (by
          nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2)
            (sub_nonneg.mpr x.property.2.2)]) := by
  simp [intervalValue, intervalEndpoint, intervalCandidate, pointAtHeight]

theorem exists_unitInterval_mul {D a : ℝ} (hD : 0 ≤ D) (ha : 0 ≤ a) (haD : a ≤ D) :
    ∃ t : UnitInterval, t.val * D = a := by
  by_cases h : D = 0
  · have ha0 : a = 0 := le_antisymm (haD.trans_eq h) ha
    exact ⟨⟨0, by norm_num⟩, by simp [ha0]⟩
  · have hpos : 0 < D := lt_of_le_of_ne hD (Ne.symm h)
    exact ⟨⟨a / D, div_nonneg ha hD, (div_le_one hpos).mpr haD⟩,
      div_mul_cancel₀ a h⟩

omit [NormedSpace ℝ E] in
theorem rearrange_le_candidate (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ))
    (x : Slice Y L) (a : ℝ) (ha : 0 ≤ a) (hax : a + x.val.2 ≤ L x.val.1) :
    rearrange Y L hL F x ≤ intervalCandidate Y L F x a ha hax := by
  obtain ⟨t, ht⟩ := exists_unitInterval_mul (sub_nonneg.mpr x.property.2.2) ha
    (show a ≤ L x.val.1 - x.val.2 by linarith)
  change minimum ((intervalValue Y L hL F).curry x) ≤ _
  calc
    _ ≤ (intervalValue Y L hL F).curry x t := minimum_le _ t
    _ = _ := by
      change intervalValue Y L hL F (x, t) = _
      rw [intervalValue_eq_candidate]
      simp only [ht]

omit [NormedSpace ℝ E] in
theorem rearrange_attained (hL : ContinuousOn L Y) (F : C(Slice Y L, ℝ))
    (x : Slice Y L) :
    ∃ (a : ℝ) (ha : 0 ≤ a) (hax : a + x.val.2 ≤ L x.val.1),
      rearrange Y L hL F x = intervalCandidate Y L F x a ha hax := by
  obtain ⟨t, ht⟩ := minimum_attained ((intervalValue Y L hL F).curry x)
  have ha := mul_nonneg t.property.1 (sub_nonneg.mpr x.property.2.2)
  have hax : t.val * (L x.val.1 - x.val.2) + x.val.2 ≤ L x.val.1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr x.property.2.2)]
  refine ⟨_, ha, hax, ?_⟩
  change minimum ((intervalValue Y L hL F).curry x) = _
  rw [← ht]
  exact intervalValue_eq_candidate Y L hL F x t

theorem rearrange_convex (hL : ContinuousOn L Y) (hc : ConcaveOn ℝ Y L)
    (F : ConvexMaps (sliceDomain Y L) (convex_sliceDomain Y L hc)) :
    rearrange Y L hL F.val ∈ convexFunctionSet (sliceDomain Y L)
      (convex_sliceDomain Y L hc) := by
  intro x y a b ha hb hab
  let z : Slice Y L := ⟨a • x.val + b • y.val, (convex_sliceDomain Y L hc) x.property y.property ha hb hab⟩
  obtain ⟨A, hA, hAx, hFx⟩ := rearrange_attained Y L hL F.val x
  obtain ⟨B, hB, hBy, hFy⟩ := rearrange_attained Y L hL F.val y
  have hC : 0 ≤ a * A + b * B := add_nonneg (mul_nonneg ha hA) (mul_nonneg hb hB)
  have hCz : a * A + b * B + z.val.2 ≤ L z.val.1 := by
    change a * A + b * B + (a * x.val.2 + b * y.val.2) ≤ L (a • x.val.1 + b • y.val.1)
    calc
      _ = a * (A + x.val.2) + b * (B + y.val.2) := by ring
      _ ≤ a * L x.val.1 + b * L y.val.1 :=
        add_le_add (mul_le_mul_of_nonneg_left hAx ha) (mul_le_mul_of_nonneg_left hBy hb)
      _ ≤ _ := hc.2 x.property.1 y.property.1 ha hb hab
  have hz := rearrange_le_candidate Y L hL F.val z (a * A + b * B) hC hCz
  apply hz.trans
  apply max_le
  · have hf := F.property
      (pointAtHeight Y L x A ⟨hA, by linarith [x.property.2.1]⟩)
      (pointAtHeight Y L y B ⟨hB, by linarith [y.property.2.1]⟩) a b ha hb hab
    have hx : F.val (pointAtHeight Y L x A ⟨hA, by linarith [x.property.2.1]⟩) ≤
        rearrange Y L hL F.val x := by
      rw [hFx]; exact le_max_left _ _
    have hy : F.val (pointAtHeight Y L y B ⟨hB, by linarith [y.property.2.1]⟩) ≤
        rearrange Y L hL F.val y := by
      rw [hFy]; exact le_max_left _ _
    have hf' := hf.trans (add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb))
    simpa [pointAtHeight, z, smul_eq_mul] using hf'
  · have hf := F.property
      (pointAtHeight Y L x (A + x.val.2) ⟨by linarith [x.property.2.1], hAx⟩)
      (pointAtHeight Y L y (B + y.val.2) ⟨by linarith [y.property.2.1], hBy⟩) a b ha hb hab
    have hx : F.val (pointAtHeight Y L x (A + x.val.2) ⟨by linarith [x.property.2.1], hAx⟩) ≤
        rearrange Y L hL F.val x := by
      rw [hFx]; exact le_max_right _ _
    have hy : F.val (pointAtHeight Y L y (B + y.val.2) ⟨by linarith [y.property.2.1], hBy⟩) ≤
        rearrange Y L hL F.val y := by
      rw [hFy]; exact le_max_right _ _
    have hf' := hf.trans (add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb))
    convert hf' using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ext <;> simp [pointAtHeight, z, smul_eq_mul]
    ring

end SlicedDomain

end Comparison
end PackingSufficiencySupport

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Hamiltonian_ScaledPlanarMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Comparison
open scoped Topology
open Set Function Filter
section

variable {P : Type*} [TopologicalSpace P] {m : ℕ}

def unitIntervalValue (F : C(P × ℝ,ℝ)) : C((P × ℝ) × UnitInterval,ℝ) where
  toFun p := max (F (p.1.1,p.2.val*(1-clampUnit p.1.2)))
    (F (p.1.1,p.2.val*(1-clampUnit p.1.2)+clampUnit p.1.2))
  continuous_toFun := by
    have hc : Continuous (fun p : (P × ℝ) × UnitInterval => clampUnit p.1.2) :=
      continuous_clampUnit.comp (continuous_snd.comp continuous_fst)
    have ht : Continuous (fun p : (P × ℝ) × UnitInterval => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have hy : Continuous (fun p : (P × ℝ) × UnitInterval => p.1.1) :=
      continuous_fst.comp continuous_fst
    exact (F.continuous.comp (hy.prodMk (ht.mul (continuous_const.sub hc)))).max
      (F.continuous.comp (hy.prodMk ((ht.mul (continuous_const.sub hc)).add hc)))

def unitRearrange (F : C(P × ℝ,ℝ)) : C(P × ℝ,ℝ) where
  toFun p := minimum ((unitIntervalValue F).curry p)
  continuous_toFun := minimum_lipschitz.continuous.comp (unitIntervalValue F).curry.continuous

def unitSublevel (F : C(P × ℝ,ℝ)) (h ε : ℝ) (y : P) : Set ℝ :=
  {v | v ∈ Ioo 0 1 ∧ F (y,v) < unitRearrange F (y,h)+ε}

end

def fixedIntervalValue (f : C(ℝ,ℝ)) (L h : ℝ) : C(UnitInterval,ℝ) where
  toFun t := max (f (t.val*(L-h))) (f (t.val*(L-h)+h))
  continuous_toFun := (f.continuous.comp (continuous_subtype_val.mul continuous_const)).max
    (f.continuous.comp ((continuous_subtype_val.mul continuous_const).add continuous_const))

def intervalMinimum (f : C(ℝ,ℝ)) (L h : ℝ) : ℝ := minimum (fixedIntervalValue f L h)

end PackingSufficiencySupport.Comparison
end

end OAI
end


