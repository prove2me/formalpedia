-- Prove2me | Definitions.Def_OAIQ240Bp002
-- name    : OAIQ240Bp002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:41:18.236565+00:00
-- url     : https://prove2.me/theorems/490eec3b-aaa3-46e7-ae1a-b6d0446aa2de
-- title:
--   Definitions bundle OAIQ240Bp002 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 50 declarations of OpenAI's Lean: 29 definitions, 1 inductive type or structure and 20 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ctInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffCommute`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cutoffTransport`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.djcInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frameFredInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.largerDiskBump`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ljcInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ljcInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.lsoInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.lsoInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ptCRInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.scsInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smallDiskBump`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.tcInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.StabilizedKernelFrame`, `OAI.HigherDimensionalBallPacking.Rigidity.StabilizedKernelFrame.kernelEquiv`, `OAI.HigherDimensionalBallPacking.Rigidity.bumpCurlKernel`, `OAI.HigherDimensionalBallPacking.Rigidity.cauchyCurl`, `OAI.HigherDimensionalBallPacking.Rigidity.cauchyInnerBump`, `OAI.HigherDimensionalBallPacking.Rigidity.cauchyPuncture`, `OAI.HigherDimensionalBallPacking.Rigidity.finiteTargetAugment`, `OAI.HigherDimensionalBallPacking.Rigidity.framedZeroOpen`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_4`, `OAI.HigherDimensionalBallPacking.Rigidity.instNormedSpaceRealContinuousLinearMapIdComplex_solutions_4`, `OAI.HigherDimensionalBallPacking.Rigidity.pathSpatialDerivative`, `OAI.PackingSufficiencySupport.Comparison.minimum`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Cauchy_GreenFormula`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Cauchy/GreenFormula.lean), [`BallPacking_Compactness_GradientBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/GradientBounds.lean), [`BallPacking_Compactness_JetCauchy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/JetCauchy.lean), [`BallPacking_Fredholm_FrameFredholm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/FrameFredholm.lean), [`BallPacking_Fredholm_NonlinearReduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/NonlinearReduction.lean), [`BallPacking_Fredholm_PointwiseMarkedCR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/PointwiseMarkedCR.lean), [`BallPacking_Fredholm_ProjectionTimeGrid`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/ProjectionTimeGrid.lean), [`BallPacking_Fredholm_TranslationContinuity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Fredholm/TranslationContinuity.lean), [`BallPacking_Moduli_SmoothZeroCharts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Moduli/SmoothZeroCharts.lean), [`BallPacking_Moduli_ZeroCharts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Moduli/ZeroCharts.lean), [`BallPacking_Moments_ConvexRearrangement`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Moments/ConvexRearrangement.lean), [`BallPacking_Rigidity_RadialForm`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Rigidity/RadialForm.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp006` and `OAIQ240Bp007`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ240_BP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 theorem HasCompactSupport.left_slice {F : Type*} [Zero F] {f : ℝ × ℝ → F}
    (hf : HasCompactSupport f) (y : ℝ) : HasCompactSupport (fun x => f (x,y)) := by
  apply HasCompactSupport.intro (hf.image continuous_fst)
  intro x hx
  by_contra hn
  exact hx ⟨(x,y),subset_tsupport f hn,rfl⟩

 theorem HasCompactSupport.right_slice {F : Type*} [Zero F] {f : ℝ × ℝ → F}
    (hf : HasCompactSupport f) (x : ℝ) : HasCompactSupport (fun y => f (x,y)) := by
  apply HasCompactSupport.intro (hf.image continuous_snd)
  intro y hy
  by_contra hn
  exact hy ⟨(x,y),subset_tsupport f hn,rfl⟩

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Cauchy_GreenFormula
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

 def cauchyCurl (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * fderiv ℝ f z 1 - fderiv ℝ f z Complex.I

 def cauchyInnerBump (R : ℝ) (hR : 0<R) : ContDiffBump (0:ℂ) where
  rIn := R/4
  rOut := R/2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

 def cauchyPuncture (b : ContDiffBump (0:ℂ)) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1-b z) • (f z/z)

 theorem cauchyPuncture_compact (b : ContDiffBump (0:ℂ)) {f : ℂ → ℂ}
    (hc : HasCompactSupport f) : HasCompactSupport (cauchyPuncture b f) := by
  apply HasCompactSupport.intro hc
  intro z hz
  simp only [cauchyPuncture,image_eq_zero_of_notMem_tsupport hz,zero_div,smul_zero]

 theorem cauchyPuncture_smooth (b : ContDiffBump (0:ℂ)) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cauchyPuncture b f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z=0
  · subst z
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [b.eventuallyEq_one] with z hz
    simp only [cauchyPuncture,hz,Pi.one_apply,sub_self,zero_smul]
  · apply (contDiffAt_const.sub b.contDiff.contDiffAt).smul
    simpa only [div_eq_mul_inv] using hf.contDiffAt.mul (contDiffAt_inv (𝕜 := ℝ) hz)

 theorem cauchyPuncture_eventuallyEq (b : ContDiffBump (0:ℂ)) (f : ℂ → ℂ)
    {z : ℂ} (hz : b.rOut<‖z‖) :
    cauchyPuncture b f =ᶠ[𝓝 z] (fun w => f w/w) := by
  have hh : ∀ᶠ w in 𝓝 z, b.rOut<‖w‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  filter_upwards [hh] with w hw
  have hb : b w=0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using hw.le)
  simp only [cauchyPuncture,hb,sub_zero,one_smul]

 theorem cauchyCurl_div {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hz : z≠0) : cauchyCurl (fun w => f w/w) z = cauchyCurl f z/z := by
  have hd := hf.hasFDerivAt.mul ((hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ)
  have he : (fun w => f w/w) = (fun w => f w*w⁻¹) := by
    funext w
    exact div_eq_mul_inv _ _
  change HasFDerivAt (fun w => f w*w⁻¹) _ z at hd
  rw [he,cauchyCurl,hd.fderiv]
  change Complex.I * (f z * (1 * (-(z^2)⁻¹)) + z⁻¹ * fderiv ℝ f z 1) -
    (f z * (Complex.I * (-(z^2)⁻¹)) + z⁻¹ * fderiv ℝ f z Complex.I) =
      (Complex.I * fderiv ℝ f z 1 - fderiv ℝ f z Complex.I) / z
  rw [div_eq_mul_inv]
  ring

 theorem circle_mean_integral_limit {f : ℂ → ℂ} (hf : Continuous f) :
    Tendsto (fun R : ℝ => ∫ t in -Real.pi..Real.pi, f (circleMap 0 R t))
      (𝓝 (0:ℝ)) (𝓝 ((2*Real.pi : ℝ) • f 0)) := by
  have hh : Continuous (fun p : ℝ×ℝ => f (circleMap 0 p.1 p.2)) := by
    apply hf.comp
    unfold circleMap
    fun_prop
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun R t : ℝ => f (circleMap 0 R t)) hh (-Real.pi) Real.pi
  convert (hi.continuousAt (x := (0:ℝ))).tendsto using 1
  all_goals try with_reducible_and_instances rfl
  simp only [circleMap,Complex.ofReal_zero,zero_mul,zero_add,intervalIntegral.integral_const]
  congr 1
  congr 1
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_4 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdComplex_solutions_4 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

def bumpCurlKernel (b : ContDiffBump (0:ℂ)) (w : ℂ) : ℂ :=
  cauchyCurl (fun z : ℂ => (b z : ℂ)) w / w

lemma bump_complex_smooth (b : ContDiffBump (0:ℂ)) :
    ContDiff ℝ ∞ (fun z : ℂ => (b z : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_GradientBounds
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance scsInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance scsInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance ctInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
variable (b : ContDiffBump (0:ℂ))

def cutoffTransport (h z : ℂ) : E →L[ℝ] E :=
  (fderiv ℝ b z h) • ContinuousLinearMap.id ℝ E

def cutoffCommute (z : ℂ) : E →L[ℝ] E :=
  cutoffTransport b Complex.I z-(ContinuousLinearMap.lsmul ℝ ℂ (E := E) Complex.I).comp (cutoffTransport b 1 z)


end
open scoped Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_JetCauchy
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance ljcInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance ljcInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance lsoInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance lsoInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance djcInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup

def smallDiskBump : ContDiffBump (0:ℂ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
def largerDiskBump : ContDiffBump (0:ℂ) := ⟨1,3/2,by norm_num,by norm_num⟩


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FrameFredholm
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [ProperSpace E]
local instance frameFredInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance frameFredInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_PointwiseMarkedCR
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance ptCRInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance ptCRInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance tcInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance tcInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

def pathSpatialDerivative (F : ℝ × X → Y) (v : ℝ × X) : X →L[ℝ] Y :=
  (fderiv ℝ F v).comp (ContinuousLinearMap.inr ℝ ℝ X)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma pathSpatialDerivative_eq [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) (v : ℝ × X) :
    pathSpatialDerivative F v=fderiv ℝ (fun y => F (v.1,y)) v.2 := by
  have hD := (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) v).hasFDerivAt
  have hi : HasFDerivAt (fun y : X => (v.1,y)) (ContinuousLinearMap.inr ℝ ℝ X) v.2 :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have hh := hD.comp v.2 hi
  exact hh.fderiv.symm

def finiteTargetAugment (F : ℝ × X → Y) (E : Submodule ℝ Y) (v : ℝ × (X × E)) : Y :=
  F (v.1,v.2.1)+(v.2.2:Y)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma finiteTargetAugment_smooth [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) (E : Submodule ℝ Y) :
    ContDiff ℝ ∞ (finiteTargetAugment F E) :=
  (hF.comp (contDiff_fst.prodMk contDiff_snd.fst)).add
    (E.subtypeL.contDiff.comp contDiff_snd.snd)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma finiteTargetAugment_spatial_derivative [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F)
    (E : Submodule ℝ Y) (t : ℝ) (x : X) (e : E) :
    fderiv ℝ (fun v : X × E => finiteTargetAugment F E (t,v)) (x,e)=
      (pathSpatialDerivative F (t,x)).coprod E.subtypeL := by
  have hi : HasFDerivAt (fun v : X × E => (t,v.1))
      ((0 : X × E →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ X E)) (x,e) :=
    (hasFDerivAt_const _ _).prodMk hasFDerivAt_fst
  have hD := ((hF.differentiable (by simp) (t,x)).hasFDerivAt.comp (x,e) hi).add
      (E.subtypeL.hasFDerivAt.comp (x,e) hasFDerivAt_snd)
  change fderiv ℝ ((F ∘ fun v : X × E => (t,v.1)) + E.subtypeL ∘ Prod.snd) (x,e)=_
  rw [hD.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_ProjectionTimeGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

structure StabilizedKernelFrame (F : ℝ × X → Y) (E : Submodule ℝ Y)
    (V : Set (ℝ × X)) where
  frame : (ℝ × X) → E →L[ℝ] (X × E)
  coordinate : (ℝ × X) → (X × E) →L[ℝ] E
  frame_continuous : ContinuousOn frame V
  coordinate_continuous : ContinuousOn coordinate V
  kernel : ∀ v∈V,∀ e : E,((pathSpatialDerivative F v).coprod E.subtypeL) (frame v e)=0
  left_inv : ∀ v∈V,∀ e : E,coordinate v (frame v e)=e
  right_inv : ∀ v∈V,∀ w : X × E,((pathSpatialDerivative F v).coprod E.subtypeL) w=0 →
    frame v (coordinate v w)=w



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moduli_ZeroCharts
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
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)

def StabilizedKernelFrame.kernelEquiv {v : ℝ × X} (hv : v∈V) :
    E ≃ₗ[ℝ] ((pathSpatialDerivative F v).coprod E.subtypeL).ker := by
  let A := (pathSpatialDerivative F v).coprod E.subtypeL
  let B : E →ₗ[ℝ] A.ker := (fr.frame v).toLinearMap.codRestrict A.ker (fr.kernel v hv)
  refine LinearEquiv.ofBijective B ⟨?_,?_⟩
  · intro e f he
    have hh := congrArg (fun z : A.ker => fr.coordinate v z.val) he
    change fr.coordinate v (fr.frame v e)=fr.coordinate v (fr.frame v f) at hh
    simpa only [fr.left_inv v hv] using hh
  · intro w
    refine ⟨fr.coordinate v w.val,?_⟩
    apply Subtype.ext
    exact fr.right_inv v hv w.val w.property

include fr in
lemma StabilizedKernelFrame.fredholm {v : ℝ × X} (hv : v∈V)
    (hs : Surjective ((pathSpatialDerivative F v).coprod E.subtypeL)) :
    ((pathSpatialDerivative F v).coprod E.subtypeL).IsFredholm := by
  let A := (pathSpatialDerivative F v).coprod E.subtypeL
  let e := fr.kernelEquiv hv
  let : FiniteDimensional ℝ A.ker := Module.Finite.equiv e
  have htop : A.range=⊤ := LinearMap.range_eq_top.mpr hs
  refine ⟨(A.isOpenMap hs).isStrictMap A.continuous,?_,inferInstance,?_,?_⟩
  · rw [htop]
    exact isClosed_univ
  · rw [htop]
    infer_instance
  · exact Submodule.ClosedComplemented.of_finiteDimensional _


end
open scoped ContDiff Topology
open Set Function Filter
variable {P Q Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma smooth_actual_implicit_branch {f : P × Q → Y} (hf : ContDiff ℝ ∞ f)
    {ψ : P → Q} {D : Set P} (hD : IsOpen D) (hψ : ContinuousOn ψ D) (z : Y)
    (hz : ∀ p∈D,f (p,ψ p)=z)
    (hi : ∀ p∈D,((fderiv ℝ f (p,ψ p)).comp (ContinuousLinearMap.inr ℝ P Q)).IsInvertible) :
    ContDiffOn ℝ ∞ ψ D := by
  intro p hp
  let g := hf.contDiffAt.implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (hi p hp)
  have hg : ContDiffAt ℝ ∞ g p := hf.contDiffAt.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (hi p hp)
  have he : ψ =ᶠ[𝓝 p] g := by
    have hh := hf.contDiffAt.eventually_apply_eq_iff_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (hi p hp)
    have hc : ContinuousAt (fun r => (r,ψ r)) p :=
      continuousAt_id.prodMk ((hψ p hp).continuousAt (hD.mem_nhds hp))
    have hm := hc hh
    filter_upwards [hm,hD.mem_nhds hp] with r hr hrD
    exact ((hr).mp ((hz r hrD).trans (hz p hp).symm)).symm
  exact (hg.congr_of_eventuallyEq he).contDiffWithinAt



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moduli_SmoothZeroCharts
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
variable {F : ℝ × X → Y}

variable [CompleteSpace X] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)
local instance szcK : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
local instance szcX : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.completeSpace_coe


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma timePreserving_linear_det (A : ℝ × E →L[ℝ] E) :
    ((ContinuousLinearMap.fst ℝ ℝ E).prod A).det =
      (A.comp (ContinuousLinearMap.inr ℝ ℝ E)).det := by
  classical
  let b := Module.Free.chooseBasis ℝ ℝ
  let c := Module.Free.chooseBasis ℝ E
  have hm : LinearMap.toMatrix (b.prod c) (b.prod c)
      ((ContinuousLinearMap.fst ℝ ℝ E).prod A).toLinearMap =
      Matrix.fromBlocks (1 : Matrix _ _ ℝ) 0
        (LinearMap.toMatrix b c (A.comp (ContinuousLinearMap.inl ℝ ℝ E)).toLinearMap)
        (LinearMap.toMatrix c c (A.comp (ContinuousLinearMap.inr ℝ ℝ E)).toLinearMap) := by
    ext (i|i) (j|j) <;> simp [LinearMap.toMatrix_apply,Matrix.one_apply,Finsupp.single_apply,eq_comm]
  change LinearMap.det _ = LinearMap.det _
  rw [←LinearMap.det_toMatrix (b.prod c),hm,Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one,one_mul,LinearMap.det_toMatrix]


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)}

def framedZeroOpen (F : ℝ × X → Y) (E : Submodule ℝ Y)
    (V : Set (ℝ × X)) (hV : IsOpen V) :
    TopologicalSpace.Opens {v : ℝ × (X × E) // finiteTargetAugment F E v=0} :=
  ⟨{v | (v.val.1,v.val.2.1)∈V},hV.preimage
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_fst.comp (continuous_snd.comp continuous_subtype_val)))⟩


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y}
  {E : Submodule ℝ Y}
  [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)}
  (fr : StabilizedKernelFrame F E V)
  (hF : ContDiff ℝ ∞ F)
  (hV : IsOpen V)

lemma sign_eq_of_mul_pos {r s : ℝ} (h : 0 < r*s) : Real.sign r=Real.sign s := by
  rcases mul_pos_iff.mp h with h|h
  · rw [Real.sign_of_pos h.1,Real.sign_of_pos h.2]
  · rw [Real.sign_of_neg h.1,Real.sign_of_neg h.2]


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moments_ConvexRearrangement
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

def minimum (F : C(X, ℝ)) : ℝ := sInf (Set.range F)

end Minimum

end Comparison
end PackingSufficiencySupport

end

end OAI
end


