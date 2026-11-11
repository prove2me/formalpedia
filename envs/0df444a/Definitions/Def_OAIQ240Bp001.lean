-- Prove2me | Definitions.Def_OAIQ240Bp001
-- name    : OAIQ240Bp001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:41:59.35309+00:00
-- url     : https://prove2.me/theorems/a2f623b3-2e2f-4986-8f4c-5fd0a784949a
-- title:
--   Definitions bundle OAIQ240Bp001 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 136 declarations of OpenAI's Lean: 65 definitions, 1 inductive type or structure and 70 theorems. The definitions and types are `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.PlaneTest`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.affineCutInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ccInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.complexI`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.complexSlope`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.complexSlopeCLM`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.crSectInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst10`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.csInst9`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.ctInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeChartInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.freeFredInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmChartInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc7`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gmc8`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetSuperInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetSuperInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetSuperInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.jetSuperInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.linCRInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markFiniteInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markFiniteInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst5`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedChartInst6`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFrameInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedFrameInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.markedJetInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst1`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothSuperInst2`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.zeroOrderInst1` and 26 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `BallPacking_Cauchy_GreenFormula`, `BallPacking_Compactness_GradientBounds`, `BallPacking_Continuation_CompatibleHomotopy`, `BallPacking_Continuation_ParameterizedImplicit`, `BallPacking_Fredholm_CompactFredholmAlternative`, `BallPacking_Fredholm_FiniteExtensions`, `BallPacking_Fredholm_FrameFredholm`, `BallPacking_Fredholm_FreeLinearization`, `BallPacking_Fredholm_PointwiseMarkedCR`, `BallPacking_Holder_HolderTaylor`, `BallPacking_Holder_KernelSchauder`, `BallPacking_Holder_MarkedFrame`, `BallPacking_Holder_MarkedJets`, `BallPacking_Holder_NonlinearCR`, `BallPacking_Holder_SchauderSplit`, `BallPacking_Moments_ConvexRearrangement`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ240Bp005` and `OAIQ240Bp006`; the statement `OAI_HigherDimensionalBallPacking_Rigidity_equicontinuous_CR_derivative_bound`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_NonlinearCR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology RealInnerProductSpace
open Set Filter MeasureTheory

 def smoothCauchyKernel (δ : ℝ) (z : ℂ) : ℂ := (‖z‖^2+δ)⁻¹ • star z

 theorem smoothCauchyKernel_smooth {δ : ℝ} (hδ : 0<δ) :
    ContDiff ℝ ∞ (smoothCauchyKernel δ) := by
  exact (((contDiff_id.norm_sq ℂ).add contDiff_const).inv
    (fun z => (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ).ne')).smul
      (starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff

 theorem smoothCauchyKernel_fderiv {δ : ℝ} (hδ : 0<δ) (z v : ℂ) :
    fderiv ℝ (smoothCauchyKernel δ) z v =
      (‖z‖^2+δ)⁻¹ • star v -
        (2*inner ℝ z v/(‖z‖^2+δ)^2) • star z := by
  have hd := ((hasDerivAt_inv (add_pos_of_nonneg_of_pos (sq_nonneg ‖z‖) hδ).ne').comp_hasFDerivAt z
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const δ)).smul
      (starL ℝ : ℂ ≃L[ℝ] ℂ).hasFDerivAt
  rw [show fderiv ℝ (smoothCauchyKernel δ) z = _ from hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,two_smul,smul_eq_mul,Function.comp_apply]
  change (‖z‖^2+δ)⁻¹ • star v + (-((‖z‖^2+δ)^2)⁻¹*(inner ℝ z v+inner ℝ z v)) • star z = _
  rw [sub_eq_add_neg,←neg_smul]
  congr 2
  rw [div_eq_mul_inv]
  ring

 theorem smoothCauchyKernel_tendsto (z : ℂ) :
    Tendsto (fun δ : ℝ => smoothCauchyKernel δ z) (𝓝[>] 0) (𝓝 z⁻¹) := by
  by_cases hz : z=0
  · simp only [hz,smoothCauchyKernel,norm_zero,zero_pow (by decide : (2:ℕ)≠0),
      zero_add,star_zero,smul_zero,inv_zero]
    exact tendsto_const_nhds
  have hn : ‖z‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hh : ContinuousAt (fun δ : ℝ => (‖z‖^2+δ)⁻¹ • star z) 0 := by
    exact (((continuous_const.add continuous_id).continuousAt.inv₀
      (by simpa only [Pi.add_apply,id_eq,add_zero] using hn)).smul continuousAt_const)
  have h := hh.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have he : (‖z‖^2)⁻¹ • star z=z⁻¹ := by
    rw [Complex.inv_def,Complex.normSq_eq_norm_sq]
    simp only [Complex.real_smul,Complex.ofReal_inv]
    exact mul_comm _ _
  simpa only [smoothCauchyKernel,add_zero,he] using h


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_KernelSchauder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Filter MeasureTheory

lemma smoothCauchyKernel_second_directional {δ : ℝ} (hδ : 0 < δ) (z v w : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ (smoothCauchyKernel δ) y v) z w =
      (-(2 * inner ℝ z w) / (‖z‖ ^ 2 + δ) ^ 2) • star v -
      (2 * inner ℝ w v / (‖z‖ ^ 2 + δ) ^ 2 -
        8 * inner ℝ z v * inner ℝ z w / (‖z‖ ^ 2 + δ) ^ 3) • star z -
      (2 * inner ℝ z v / (‖z‖ ^ 2 + δ) ^ 2) • star w := by
  have hq : 0 < ‖z‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  have hqi := (hasDerivAt_inv hq.ne').comp_hasFDerivAt z
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const δ)
  have hi : HasFDerivAt (fun y : ℂ => inner ℝ y v) (innerSL ℝ v) z := by
    convert! (innerSL ℝ v).hasFDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simpa only [innerSL_apply_apply] using (real_inner_comm y v).symm
  have ht := (hi.const_mul 2).mul (hqi.pow 2)
  have hd := (hqi.smul_const (star v)).sub
    (ht.smul (starL ℝ : ℂ ≃L[ℝ] ℂ).hasFDerivAt)
  have he : (fun y => fderiv ℝ (smoothCauchyKernel δ) y v) =
      (fun y => (‖y‖ ^ 2 + δ)⁻¹ • star v -
        (2 * inner ℝ y v * ((‖y‖ ^ 2 + δ)⁻¹) ^ 2) • star y) := by
    funext y
    rw [smoothCauchyKernel_fderiv hδ, div_eq_mul_inv, inv_pow]
  rw [he]
  change HasFDerivAt (fun y : ℂ => (‖y‖ ^ 2 + δ)⁻¹ • star v -
      (2 * inner ℝ y v * ((‖y‖ ^ 2 + δ)⁻¹) ^ 2) • star y) _ z at hd
  rw [hd.fderiv]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, two_smul, smul_eq_mul, Function.comp_apply]
  simp only [Pi.mul_apply, Nat.reduceSub, pow_one, div_eq_mul_inv, inv_pow, ContinuousLinearEquiv.coe_coe]
  rw [real_inner_comm v w]
  change (-((‖z‖ ^ 2 + δ) ^ 2)⁻¹ * (inner ℝ z w + inner ℝ z w)) • star v -
      ((2 * inner ℝ z v * ((‖z‖ ^ 2 + δ) ^ 2)⁻¹) • star w +
        (2 * inner ℝ z v *
              (((‖z‖ ^ 2 + δ)⁻¹ + (‖z‖ ^ 2 + δ)⁻¹) *
                (-((‖z‖ ^ 2 + δ) ^ 2)⁻¹ * (inner ℝ z w + inner ℝ z w))) +
            ((‖z‖ ^ 2 + δ) ^ 2)⁻¹ * (inner ℝ v w + inner ℝ v w)) • star z) = _
  simp only [← inv_pow]
  module

lemma smoothCauchyKernel_second_norm {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : z ≠ 0) (v w : ℂ) :
    ‖fderiv ℝ (fun y => fderiv ℝ (smoothCauchyKernel δ) y v) z w‖ ≤
      (14 / ‖z‖^3) * ‖v‖ * ‖w‖ := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hq : 0 < ‖z‖^2+δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  have hq2 : ‖z‖^4 ≤ (‖z‖^2+δ)^2 := by
    calc
      _ = (‖z‖^2)^2 := by ring
      _ ≤ _ := by gcongr; linarith
  have hq3 : ‖z‖^6 ≤ (‖z‖^2+δ)^3 := by
    calc
      _ = (‖z‖^2)^3 := by ring
      _ ≤ _ := by gcongr; linarith
  rw [smoothCauchyKernel_second_directional hδ]
  calc
    _ ≤ ‖(-(2*inner ℝ z w)/(‖z‖^2+δ)^2) • star v‖ +
        ‖(2*inner ℝ w v/(‖z‖^2+δ)^2 -
          8*inner ℝ z v*inner ℝ z w/(‖z‖^2+δ)^3) • star z‖ +
        ‖(2*inner ℝ z v/(‖z‖^2+δ)^2) • star w‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (2*|inner ℝ z w|/(‖z‖^2+δ)^2)*‖v‖ +
        ((2*|inner ℝ w v|/(‖z‖^2+δ)^2) +
          (8*|inner ℝ z v| *|inner ℝ z w|/(‖z‖^2+δ)^3))*‖z‖ +
        (2*|inner ℝ z v|/(‖z‖^2+δ)^2)*‖w‖ := by
      simp only [norm_smul, norm_star, Real.norm_eq_abs, abs_div, abs_neg, abs_mul,
        abs_pow, abs_of_pos hq, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      gcongr
      apply (abs_sub _ _).trans_eq
      simp only [abs_div, abs_mul, abs_pow, abs_of_pos hq,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 8)]
    _ ≤ (2*(‖z‖*‖w‖)/‖z‖^4)*‖v‖ +
        ((2*(‖w‖*‖v‖)/‖z‖^4) +
          (8*(‖z‖*‖v‖)*(‖z‖*‖w‖)/‖z‖^6))*‖z‖ +
        (2*(‖z‖*‖v‖)/‖z‖^4)*‖w‖ := by
      gcongr <;> exact abs_real_inner_le_norm _ _
    _ = _ := by field_simp <;> ring


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_directional_eq {f : ℂ → E} (hf : ContDiff ℝ ∞ f) (z v w : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ f y v) z w = fderiv ℝ (fderiv ℝ f) z w v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)
    (differentiableAt_const v)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]

lemma norm_second_jet (f : ℂ → E) (z : ℂ) :
    ‖iteratedFDeriv ℝ 2 f z‖ = ‖fderiv ℝ (fderiv ℝ f) z‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

lemma second_directional_norm_le {f : ℂ → E} (hf : ContDiff ℝ ∞ f) (z v w : ℂ) :
    ‖fderiv ℝ (fun y => fderiv ℝ f y v) z w‖ ≤
      ‖iteratedFDeriv ℝ 2 f z‖ * ‖v‖ * ‖w‖ := by
  rw [second_directional_eq hf, norm_second_jet]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  calc
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) z‖ * ‖w‖)*‖v‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = _ := by ring

lemma norm_first_smul_le {b : ℂ → ℝ} {K : ℂ → E}
    (hb : ContDiff ℝ ∞ b) (hK : ContDiff ℝ ∞ K) (z : ℂ) :
    ‖fderiv ℝ (fun w => b w • K w) z‖ ≤
      ‖b z‖*‖fderiv ℝ K z‖ + ‖fderiv ℝ b z‖*‖K z‖ := by
  have he := norm_iteratedFDeriv_smul_le hb hK z (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1:ℕ) ≤ (∞ : ℕ∞ω))
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.sub_zero, Nat.sub_self, Nat.reduceSub, norm_iteratedFDeriv_one, norm_iteratedFDeriv_zero] using he

lemma norm_second_smul_le {b : ℂ → ℝ} {K : ℂ → E}
    (hb : ContDiff ℝ ∞ b) (hK : ContDiff ℝ ∞ K) (z : ℂ) :
    ‖iteratedFDeriv ℝ 2 (fun w => b w • K w) z‖ ≤
      ‖b z‖*‖iteratedFDeriv ℝ 2 K z‖ +
        2*‖fderiv ℝ b z‖*‖fderiv ℝ K z‖ +
        ‖iteratedFDeriv ℝ 2 b z‖*‖K z‖ := by
  have he := norm_iteratedFDeriv_smul_le hb hK z (show (2:ℕ) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.cast_one, one_mul,
    Nat.sub_zero, Nat.sub_self, Nat.reduceSub, Nat.cast_ofNat,
    norm_iteratedFDeriv_one, norm_iteratedFDeriv_zero] using he

lemma norm_first_rescale {f : ℂ → E} (hf : ContDiff ℝ ∞ f) {r : ℝ} (hr : 0 < r)
    (z : ℂ) : ‖fderiv ℝ (fun w => f (r⁻¹ • w)) z‖ =
      r⁻¹ * ‖fderiv ℝ f (r⁻¹ • z)‖ := by
  have he := congrArg (fun g => ‖g z‖)
    (iteratedFDeriv_comp_const_smul r⁻¹ (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1:ℕ∞ω) ≤ ∞)))
  simpa only [norm_iteratedFDeriv_one, pow_one, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] using he

lemma norm_second_rescale {f : ℂ → E} (hf : ContDiff ℝ ∞ f) {r : ℝ} (_hr : 0 < r)
    (z : ℂ) : ‖iteratedFDeriv ℝ 2 (fun w => f (r⁻¹ • w)) z‖ =
      (r^2)⁻¹ * ‖iteratedFDeriv ℝ 2 f (r⁻¹ • z)‖ := by
  have he := congrArg (fun g => ‖g z‖)
    (iteratedFDeriv_comp_const_smul r⁻¹ (hf.of_le (show (2:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)))
  simpa only [norm_smul, inv_pow, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg r))] using he


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory

def schauderBump : ContDiffBump (0:ℂ) where
  rIn := 3/2
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def scaledSchauderBump (r : ℝ) (z : ℂ) : ℝ := schauderBump (r⁻¹ • z)

lemma scaledSchauderBump_smooth (r : ℝ) : ContDiff ℝ ∞ (scaledSchauderBump r) :=
  schauderBump.contDiff.comp (contDiff_id.const_smul r⁻¹)

lemma scaledSchauderBump_range (r : ℝ) (z : ℂ) :
    scaledSchauderBump r z ∈ Icc (0:ℝ) 1 := ⟨schauderBump.nonneg, schauderBump.le_one⟩

lemma scaledSchauderBump_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (scaledSchauderBump r) ⊆ Metric.closedBall (0:ℂ) (2*r) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  have hz' : r⁻¹ • z ∈ Function.support schauderBump := hz
  rw [schauderBump.support_eq] at hz'
  simp only [Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at hz'
  change r⁻¹ * ‖z‖ < 2 at hz'
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [inv_mul_eq_div, div_lt_iff₀ hr] at hz'
  exact hz'.le

lemma scaledSchauderBump_eventually_one {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ ≤ r) : scaledSchauderBump r =ᶠ[𝓝 z] (fun _ => 1) := by
  have ht : r⁻¹ • z ∈ Metric.ball (0:ℂ) schauderBump.rIn := by
    simp only [Metric.mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    change r⁻¹ * ‖z‖ < 3/2
    have : r⁻¹ * ‖z‖ ≤ 1 := by rwa [inv_mul_eq_div, div_le_one hr]
    linarith
  exact (schauderBump.eventuallyEq_one_of_mem_ball ht).comp_tendsto
    ((continuous_id.const_smul r⁻¹).tendsto z)

lemma smoothCauchyKernel_second_opNorm {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ≠ 0) :
    ‖iteratedFDeriv ℝ 2 (smoothCauchyKernel δ) z‖ ≤ 14/‖z‖^3 := by
  rw [norm_second_jet]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [← second_directional_eq (smoothCauchyKernel_smooth hδ)]
  convert! smoothCauchyKernel_second_norm hδ hz v w using 1; ring


end
section
open scoped Topology
open Set Filter MeasureTheory

def schauderNearWeight (z : ℂ) : ℝ :=
  (Metric.closedBall (0:ℂ) 2).indicator (fun w => ‖w‖ ^ (-(5:ℝ)/3)) z

def schauderFarWeight (z : ℂ) : ℝ :=
  (Ioi (1:ℝ)).indicator (fun r => r ^ (-(8:ℝ)/3)) ‖z‖

lemma schauderNearWeight_nonneg (z : ℂ) : 0 ≤ schauderNearWeight z := by
  exact indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg w) _) z

lemma schauderFarWeight_nonneg (z : ℂ) : 0 ≤ schauderFarWeight z := by
  apply indicator_nonneg _ ‖z‖
  intro r hr
  exact Real.rpow_nonneg (zero_le_one.trans hr.le) _

lemma schauderNearWeight_integrable : Integrable schauderNearWeight := by
  apply IntegrableOn.integrable_indicator _ measurableSet_closedBall
  apply LocallyIntegrable.integrableOn_isCompact _ (isCompact_closedBall _ _)
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := (5:ℝ)/3) (by simp) (by norm_num)
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
      norm_num
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

lemma schauderFarWeight_integrable : Integrable schauderFarWeight := by
  unfold schauderFarWeight
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ)]
  have h : Integrable ((Ioi (1:ℝ)).indicator (fun r => r ^ (-(5:ℝ)/3))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(5:ℝ)/3 < -1) zero_lt_one).integrable_indicator
      measurableSet_Ioi
  apply h.integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
  by_cases h1 : 1 < r
  · rw [indicator_of_mem (show r ∈ Ioi (1:ℝ) from h1),
      indicator_of_mem (show r ∈ Ioi (1:ℝ) from h1)]
    have he := Real.rpow_add (show 0 < r from hr) (1:ℝ) (-(8:ℝ)/3)
    norm_num at he
    simpa only [neg_div] using he
  · simp only [indicator_of_notMem (show r ∉ Ioi (1:ℝ) from h1), mul_zero]

def scaledSchauderWeight (β : ℝ) (W : ℂ → ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  r ^ β * W (r⁻¹ • z)

lemma scaledSchauderWeight_integrable {W : ℂ → ℝ} (hW : Integrable W)
    (β : ℝ) {r : ℝ} (hr : 0 < r) : Integrable (scaledSchauderWeight β W r) :=
  (hW.comp_smul (inv_ne_zero hr.ne')).const_mul _

lemma integral_scaledSchauderWeight (β : ℝ) (W : ℂ → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ z, scaledSchauderWeight β W r z) = r ^ (β+2) * ∫ z, W z := by
  unfold scaledSchauderWeight
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume W hr.le]
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_two, ← Real.rpow_add hr]

lemma scaledNearWeight_value {r : ℝ} (hr : 0 < r) (z : ℂ) :
    scaledSchauderWeight (-(5:ℝ)/3) schauderNearWeight r z =
      (Metric.closedBall (0:ℂ) (2*r)).indicator (fun w => ‖w‖^(-(5:ℝ)/3)) z := by
  have hn : ‖r⁻¹ • z‖ = r⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hm : r⁻¹ • z ∈ Metric.closedBall (0:ℂ) 2 ↔ z ∈ Metric.closedBall (0:ℂ) (2*r) := by
    simp only [Metric.mem_closedBall, dist_zero_right, hn]
    rw [inv_mul_eq_div, div_le_iff₀ hr]
  simp only [scaledSchauderWeight, schauderNearWeight]
  by_cases hz : z ∈ Metric.closedBall (0:ℂ) (2*r)
  · rw [indicator_of_mem (hm.mpr hz), indicator_of_mem hz, hn,
      Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg z), Real.inv_rpow hr.le,
      ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne', one_mul]
  · rw [indicator_of_notMem (fun h => hz (hm.mp h)), indicator_of_notMem hz, mul_zero]

lemma scaledFarWeight_value {r : ℝ} (hr : 0 < r) (z : ℂ) :
    scaledSchauderWeight (-(8:ℝ)/3) schauderFarWeight r z =
      (Ioi r).indicator (fun t => t^(-(8:ℝ)/3)) ‖z‖ := by
  have hn : ‖r⁻¹ • z‖ = r⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hm : 1 < ‖r⁻¹ • z‖ ↔ r < ‖z‖ := by
    rw [hn, inv_mul_eq_div, lt_div_iff₀ hr, one_mul]
  simp only [scaledSchauderWeight, schauderFarWeight]
  by_cases hz : r < ‖z‖
  · rw [indicator_of_mem (show ‖r⁻¹ • z‖ ∈ Ioi (1:ℝ) from hm.mpr hz),
      indicator_of_mem (show ‖z‖ ∈ Ioi r from hz), hn,
      Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg z), Real.inv_rpow hr.le,
      ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne', one_mul]
  · rw [indicator_of_notMem (show ‖r⁻¹ • z‖ ∉ Ioi (1:ℝ) from fun h => hz (hm.mp h)),
      indicator_of_notMem (show ‖z‖ ∉ Ioi r from hz), mul_zero]


end
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma compact_convolution_split_fderiv {K N F : ℂ → ℂ}
    (hN : ContDiff ℝ ∞ N) (hcN : HasCompactSupport N)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hKF : ∀ w, K w = N w + F w) {g : ℂ → E} (hg : Continuous g) (x : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x =
      fderiv ℝ (convolution N g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x +
      fderiv ℝ (convolution F g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x := by
  have he : convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume =
      convolution N g (ContinuousLinearMap.lsmul ℝ ℂ) volume +
      convolution F g (ContinuousLinearMap.lsmul ℝ ℂ) volume := by
    funext z
    simp only [convolution, hKF, ContinuousLinearMap.map_add, add_apply, Pi.add_apply]
    exact integral_add
      (hcN.convolutionExists_left _ hN.continuous hg.locallyIntegrable z)
      (hcF.convolutionExists_left _ hF.continuous hg.locallyIntegrable z)
  rw [he]
  exact fderiv_add
    (hcN.hasFDerivAt_convolution_left _ (hN.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hg.locallyIntegrable x).differentiableAt
    (hcF.hasFDerivAt_convolution_left _ (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hg.locallyIntegrable x).differentiableAt



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_SchauderSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Filter MeasureTheory

structure SchauderSplit (K : ℂ → ℂ) (r A B : ℝ) where
  near : ℂ → ℂ
  far : ℂ → ℂ
  smooth_near : ContDiff ℝ ∞ near
  smooth_far : ContDiff ℝ ∞ far
  compact_near : HasCompactSupport near
  compact_far : HasCompactSupport far
  sum_eq : ∀ w, K w = near w + far w
  support_near : tsupport near ⊆ Metric.closedBall (0:ℂ) (2*r)
  support_far : ∀ w, ‖w‖ ≤ r → w ∉ tsupport far
  bound_near : ∀ w, w ≠ 0 → ‖fderiv ℝ near w‖ ≤ A / ‖w‖^2
  bound_far : ∀ w, w ≠ 0 → ‖iteratedFDeriv ℝ 2 far w‖ ≤ B / ‖w‖^3

local instance instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_r95f9f8_1 : NormedAddCommGroup (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdComplex_solutions_r95f9f8_1 : NormedSpace ℝ (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace
local instance instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_1_r95f9f8_1 : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
lemma norm_second_const_sub {b : ℂ → ℝ} (w : ℂ) :
    ‖iteratedFDeriv ℝ 2 (fun z => 1-b z) w‖ = ‖iteratedFDeriv ℝ 2 b w‖ := by
  rw [norm_second_jet]
  have he : fderiv ℝ (fun z => 1-b z) = fun z => -fderiv ℝ b z := funext fun z => fderiv_const_sub 1
  rw [he, fderiv_fun_neg]
  exact (norm_neg (fderiv ℝ (fderiv ℝ b) w)).trans (norm_second_jet b w).symm

lemma first_near_bound {K : ℂ → ℂ} {b : ℂ → ℝ} (hK : ContDiff ℝ ∞ K)
    (hb : ContDiff ℝ ∞ b) {M C₁ : ℝ} (hM : 0 ≤ M) (_hC₁ : 0 ≤ C₁)
    {w : ℂ} (hw : w ≠ 0) (hbn : ‖b w‖ ≤ 1)
    (hb1 : ‖fderiv ℝ b w‖ ≤ 2*M/‖w‖)
    (hK0 : ‖K w‖ ≤ ‖w‖⁻¹) (hK1 : ‖fderiv ℝ K w‖ ≤ C₁/‖w‖^2) :
    ‖fderiv ℝ (fun z => b z • K z) w‖ ≤ (C₁+2*M)/‖w‖^2 := by
  have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  calc
    _ ≤ ‖b w‖*‖fderiv ℝ K w‖ + ‖fderiv ℝ b w‖*‖K w‖ := norm_first_smul_le hb hK w
    _ ≤ 1*(C₁/‖w‖^2) + (2*M/‖w‖)*‖w‖⁻¹ := by
      exact add_le_add (mul_le_mul hbn hK1 (norm_nonneg _) zero_le_one)
        (mul_le_mul hb1 hK0 (norm_nonneg _) (by positivity))
    _ = _ := by field_simp

lemma second_far_bound {K : ℂ → ℂ} {b : ℂ → ℝ} (hK : ContDiff ℝ ∞ K)
    (hb : ContDiff ℝ ∞ b) {M C₁ C₂ : ℝ} (hM : 0 ≤ M) (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    {w : ℂ} (hw : w ≠ 0) (hbn : ‖1-b w‖ ≤ 1)
    (hb1 : ‖fderiv ℝ b w‖ ≤ 2*M/‖w‖)
    (hb2 : ‖iteratedFDeriv ℝ 2 b w‖ ≤ 4*M/‖w‖^2)
    (hK0 : ‖K w‖ ≤ ‖w‖⁻¹) (hK1 : ‖fderiv ℝ K w‖ ≤ C₁/‖w‖^2)
    (hK2 : ‖iteratedFDeriv ℝ 2 K w‖ ≤ C₂/‖w‖^3) :
    ‖iteratedFDeriv ℝ 2 (fun z => (1-b z) • K z) w‖ ≤
      (C₂+4*M*C₁+4*M)/‖w‖^3 := by
  have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  calc
    _ ≤ ‖1-b w‖*‖iteratedFDeriv ℝ 2 K w‖ +
        2*‖fderiv ℝ (fun z => 1-b z) w‖*‖fderiv ℝ K w‖ +
        ‖iteratedFDeriv ℝ 2 (fun z => 1-b z) w‖*‖K w‖ :=
      norm_second_smul_le (contDiff_const.sub hb) hK w
    _ = ‖1-b w‖*‖iteratedFDeriv ℝ 2 K w‖ +
        2*‖fderiv ℝ b w‖*‖fderiv ℝ K w‖ + ‖iteratedFDeriv ℝ 2 b w‖*‖K w‖ := by
      rw [fderiv_const_sub, norm_neg, norm_second_const_sub]
    _ ≤ 1*(C₂/‖w‖^3) + 2*(2*M/‖w‖)*(C₁/‖w‖^2) + (4*M/‖w‖^2)*‖w‖⁻¹ := by
      apply add_le_add _ (mul_le_mul hb2 hK0 (norm_nonneg _) (by positivity))
      exact add_le_add (mul_le_mul hbn hK2 (norm_nonneg _) zero_le_one)
        (mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by norm_num))
          hK1 (norm_nonneg _) (by positivity))
    _ = _ := by field_simp <;> ring


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

lemma inv_sq_mul_third {t : ℝ} (ht : 0 < t) :
    (t^2)⁻¹*t^((1:ℝ)/3) = t^(-(5:ℝ)/3) := by
  rw [← Real.rpow_two, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
  norm_num

lemma inv_cube_mul_third {t : ℝ} (ht : 0 < t) :
    (t^3)⁻¹*t^((1:ℝ)/3) = t^(-(8:ℝ)/3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
  norm_num

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma SchauderSplit.near_weight_bound {K : ℂ → ℂ} {r A B H : ℝ}
    (s : SchauderSplit K r A B) (hr : 0 < r) (hA : 0 ≤ A) (hH : 0 ≤ H)
    {g : ℂ → E} (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x w v : ℂ) :
    ‖fderiv ℝ s.near w v‖*‖g (x-w)-g x‖ ≤
      (A*H*scaledSchauderWeight (-(5:ℝ)/3) schauderNearWeight r w)*‖v‖ := by
  rw [scaledNearWeight_value hr]
  by_cases hw2 : w ∈ Metric.closedBall (0:ℂ) (2*r)
  · rw [indicator_of_mem hw2]
    by_cases hw : w = 0
    · subst w
      simp only [sub_zero, sub_self, norm_zero, mul_zero]
      positivity
    have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hd : ‖fderiv ℝ s.near w v‖ ≤ (A/‖w‖^2)*‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (s.bound_near w hw) (norm_nonneg _))
    have hg' : ‖g (x-w)-g x‖ ≤ H*‖w‖^((1:ℝ)/3) := by
      simpa only [sub_sub_cancel_left, norm_neg] using hg (x-w) x
    calc
      _ ≤ ((A/‖w‖^2)*‖v‖)*(H*‖w‖^((1:ℝ)/3)) :=
        mul_le_mul hd hg' (norm_nonneg _) (by positivity)
      _ = A*H*((‖w‖^2)⁻¹*‖w‖^((1:ℝ)/3))*‖v‖ := by ring
      _ = _ := by rw [inv_sq_mul_third hp]
  · have ht : w ∉ tsupport s.near := fun h => hw2 (s.support_near h)
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) ht, zero_apply, norm_zero, zero_mul,
      indicator_of_notMem hw2, mul_zero, zero_mul]

omit [NormedSpace ℂ E] [CompleteSpace E] in
lemma SchauderSplit.far_weight_bound {K : ℂ → ℂ} {r A B H : ℝ}
    (s : SchauderSplit K r A B) (hr : 0 < r) (hB : 0 ≤ B) (_hH : 0 ≤ H)
    {g : ℂ → E} (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3)) (x w v t : ℂ) :
    ‖fderiv ℝ (fun y => fderiv ℝ s.far y v) w t‖*‖g (x-w)-g x‖ ≤
      (B*H*scaledSchauderWeight (-(8:ℝ)/3) schauderFarWeight r w)*‖v‖*‖t‖ := by
  rw [scaledFarWeight_value hr]
  by_cases hw2 : r < ‖w‖
  · rw [indicator_of_mem (show ‖w‖ ∈ Ioi r from hw2)]
    have hp : 0 < ‖w‖ := hr.trans hw2
    have hw : w ≠ 0 := norm_pos_iff.mp hp
    have hd : ‖fderiv ℝ (fun y => fderiv ℝ s.far y v) w t‖ ≤
        (B/‖w‖^3)*‖v‖*‖t‖ :=
      (second_directional_norm_le s.smooth_far w v t).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (s.bound_far w hw)
          (norm_nonneg _)) (norm_nonneg _))
    have hg' : ‖g (x-w)-g x‖ ≤ H*‖w‖^((1:ℝ)/3) := by
      simpa only [sub_sub_cancel_left, norm_neg] using hg (x-w) x
    calc
      _ ≤ ((B/‖w‖^3)*‖v‖*‖t‖)*(H*‖w‖^((1:ℝ)/3)) :=
        mul_le_mul hd hg' (norm_nonneg _) (by positivity)
      _ = B*H*((‖w‖^3)⁻¹*‖w‖^((1:ℝ)/3))*‖v‖*‖t‖ := by ring
      _ = _ := by rw [inv_cube_mul_third hp]
  · have ht : w ∉ tsupport s.far := s.support_far w (le_of_not_gt hw2)
    have hd2 : iteratedFDeriv ℝ 2 s.far w = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => ht (tsupport_iteratedFDeriv_subset 2 h)
    have hd := second_directional_norm_le s.smooth_far w v t
    rw [hd2, norm_zero, zero_mul, zero_mul] at hd
    rw [indicator_of_notMem (show ‖w‖ ∉ Ioi r from hw2), mul_zero, zero_mul, zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg hd (norm_nonneg _)


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory

 def cauchySchauderWeight (R : ℝ) : ℂ → ℝ :=
  (Metric.closedBall (0:ℂ) R).indicator
    (fun z => ‖z‖^(-(2:ℝ)/3)+‖z‖^(-(5:ℝ)/3))

 theorem cauchy_holder_power_locallyIntegrable {α : ℝ} (hα : α<2) :
    LocallyIntegrable (fun z : ℂ => ‖z‖^(-α)) := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := α) (by simp) (by simpa using hα)
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),one_mul]
  · exact (measurable_norm.pow_const (-α)).aestronglyMeasurable

 theorem cauchySchauderWeight_integrable (R : ℝ) : Integrable (cauchySchauderWeight R) := by
  apply IntegrableOn.integrable_indicator
    (s := Metric.closedBall (0:ℂ) R) _ measurableSet_closedBall
  apply LocallyIntegrable.integrableOn_isCompact _ (isCompact_closedBall _ _)
  have h := (cauchy_holder_power_locallyIntegrable (α := (2:ℝ)/3) (by norm_num)).add
    (cauchy_holder_power_locallyIntegrable (α := (5:ℝ)/3) (by norm_num))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Pi.add_apply, neg_div]

 theorem cutoff_smoothCauchyKernel_schauder_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (b : ContDiffBump (0:ℂ)) {C : ℝ} (hC : 0≤C)
    (hCbound : ∀ δ : ℝ, 0<δ → ∀ z v : ℂ, z≠0 →
      ‖fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z v‖ ≤
        (C*‖z‖⁻¹+3/‖z‖^2)*‖v‖)
    {g : ℂ → E} {H : ℝ} (hH : 0≤H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3))
    {δ : ℝ} (hδ : 0<δ) (x w v : ℂ) :
    ‖fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) w v‖*‖g (x-w)-g x‖ ≤
      ((C+3)*H*cauchySchauderWeight b.rOut w)*‖v‖ := by
  by_cases hwb : w ∈ Metric.closedBall (0:ℂ) b.rOut
  · rw [cauchySchauderWeight,indicator_of_mem hwb]
    by_cases hw : w=0
    · subst w
      simp only [sub_zero,sub_self,norm_zero,mul_zero]
      positivity
    have hp : 0<‖w‖ := norm_pos_iff.mpr hw
    have hh : ‖g (x-w)-g x‖ ≤ H*‖w‖^((1:ℝ)/3) := by
      simpa only [sub_sub_cancel_left,norm_neg] using hg (x-w) x
    have hb := mul_le_mul (hCbound δ hδ w v hw) hh (norm_nonneg _) (by positivity)
    have he1 : ‖w‖⁻¹*‖w‖^((1:ℝ)/3)=‖w‖^(-(2:ℝ)/3) := by
      rw [←Real.rpow_neg_one,←Real.rpow_add hp]
      norm_num
    have he2 : (‖w‖^2)⁻¹*‖w‖^((1:ℝ)/3)=‖w‖^(-(5:ℝ)/3) := by
      rw [←Real.rpow_two,←Real.rpow_neg (norm_nonneg w),←Real.rpow_add hp]
      norm_num
    calc
      _ ≤ _ := hb
      _ = (C*‖w‖^(-(2:ℝ)/3)+3*‖w‖^(-(5:ℝ)/3))*H*‖v‖ := by
        rw [show (C*‖w‖⁻¹+3/‖w‖^2)*‖v‖*(H*‖w‖^((1:ℝ)/3)) =
          (C*(‖w‖⁻¹*‖w‖^((1:ℝ)/3))+3*((‖w‖^2)⁻¹*‖w‖^((1:ℝ)/3)))*H*‖v‖ from by ring,
          he1,he2]
      _ ≤ _ := by
        have h1 := Real.rpow_nonneg (norm_nonneg w) (-(2:ℝ)/3)
        have h2 := Real.rpow_nonneg (norm_nonneg w) (-(5:ℝ)/3)
        have hb0 : C*‖w‖^(-(2:ℝ)/3)+3*‖w‖^(-(5:ℝ)/3) ≤
            (C+3)*(‖w‖^(-(2:ℝ)/3)+‖w‖^(-(5:ℝ)/3)) := by nlinarith
        have hh0 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb0 hH) (norm_nonneg v)
        convert hh0 using 1 <;> first | rfl | ring
  · have ht : w ∉ tsupport (fun z => b z • smoothCauchyKernel δ z) := by
      intro hh
      exact hwb ((b.tsupport_eq ▸ tsupport_smul_subset_left _ _ hh))
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) ht,zero_apply,norm_zero,zero_mul,
      cauchySchauderWeight,indicator_of_notMem hwb,mul_zero,zero_mul]


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

 theorem locallyIntegrable_complex_inv : LocallyIntegrable (fun z : ℂ => z⁻¹) := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by norm_num)
  · exact ae_of_all _ fun z => by simp only [norm_inv,Real.rpow_neg_one,one_mul,le_refl]
  · exact measurable_inv.aestronglyMeasurable

 variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 def cauchyTransform (h : ℂ → E) : ℂ → E :=
  (Real.pi : ℂ)⁻¹ • convolution (fun z : ℂ => z⁻¹) h (ContinuousLinearMap.lsmul ℝ ℂ) volume

 theorem cauchyTransform_apply (h : ℂ → E) (z : ℂ) :
    cauchyTransform h z = (Real.pi : ℂ)⁻¹ • ∫ w : ℂ, w⁻¹ • h (z-w) := rfl


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory

def regularizedCauchyJet (δ : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (‖z‖^2+δ)⁻¹ • (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap -
    (2/(‖z‖^2+δ)^2) • ((innerSL ℝ z).smulRight (star z))

lemma regularizedCauchyJet_eq {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    fderiv ℝ (smoothCauchyKernel δ) z = regularizedCauchyJet δ z := by
  ext v
  rw [smoothCauchyKernel_fderiv hδ]
  simp only [regularizedCauchyJet, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, starL'_apply, ContinuousLinearEquiv.coe_coe, smul_smul]
  congr 1
  congr 1
  ring

lemma regularizedCauchyJet_continuousAt {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun δ : ℝ => regularizedCauchyJet δ z) 0 := by
  have hq : ‖z‖^2+(0:ℝ) ≠ 0 := by simpa using pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hi : ContinuousAt (fun δ : ℝ => (‖z‖^2+δ)⁻¹) 0 :=
    (continuousAt_const.add continuousAt_id).inv₀ hq
  have hcoeff : ContinuousAt (fun δ : ℝ => 2/(‖z‖^2+δ)^2) 0 :=
    continuousAt_const.div ((continuousAt_const.add continuousAt_id).pow 2) (pow_ne_zero 2 hq)
  exact (hi.smul continuousAt_const).sub
    (hcoeff.smul continuousAt_const)

def cutoffCauchyJet (b : ContDiffBump (0:ℂ)) (δ : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  b z • regularizedCauchyJet δ z + (fderiv ℝ b z).smulRight (smoothCauchyKernel δ z)

lemma cutoffCauchyJet_eq (b : ContDiffBump (0:ℂ)) {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z = cutoffCauchyJet b δ z := by
  rw [fderiv_fun_smul ((b.contDiff : ContDiff ℝ ∞ b).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)
    ((smoothCauchyKernel_smooth hδ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z), regularizedCauchyJet_eq hδ]
  rfl

lemma cutoffCauchyJet_continuousAt (b : ContDiffBump (0:ℂ)) {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun δ : ℝ => cutoffCauchyJet b δ z) 0 := by
  have hq : ‖z‖^2+(0:ℝ) ≠ 0 := by simpa using pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hi : ContinuousAt (fun δ : ℝ => (‖z‖^2+δ)⁻¹) 0 :=
    (continuousAt_const.add continuousAt_id).inv₀ hq
  have hv : ContinuousAt (fun δ : ℝ => smoothCauchyKernel δ z) 0 :=
    hi.smul (show ContinuousAt (fun _ : ℝ => star z) 0 from continuousAt_const)
  have hs : ContinuousAt (fun δ : ℝ => (fderiv ℝ b z).smulRight (smoothCauchyKernel δ z)) 0 :=
    (ContinuousLinearMap.smulRightL ℝ ℂ ℂ (fderiv ℝ b z)).continuous.continuousAt.comp hv
  have hb : ContinuousAt (fun δ : ℝ => b z • regularizedCauchyJet δ z) 0 :=
    (show ContinuousAt (fun _ : ℝ => b z) 0 from continuousAt_const).smul
      (regularizedCauchyJet_continuousAt hz)
  exact hb.add hs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def cancellationJetIntegrand (b : ContDiffBump (0:ℂ)) (δ : ℝ) (g : ℂ → E)
    (x w : ℂ) : ℂ →L[ℝ] E :=
  ((ContinuousLinearMap.lsmul ℝ ℂ).flip (g (x-w)-g x)).comp (cutoffCauchyJet b δ w)

def cutoffCauchyDerivative (b : ContDiffBump (0:ℂ)) (g : ℂ → E) (x : ℂ) : ℂ →L[ℝ] E :=
  ∫ w : ℂ, cancellationJetIntegrand b 0 g x w

omit [CompleteSpace E] in
lemma cancellationJetIntegrand_apply (b : ContDiffBump (0:ℂ)) (δ : ℝ)
    (g : ℂ → E) (x w v : ℂ) :
    cancellationJetIntegrand b δ g x w v = cutoffCauchyJet b δ w v • (g (x-w)-g x) := rfl

omit [CompleteSpace E] in
lemma cancellationJetIntegrand_continuous (b : ContDiffBump (0:ℂ)) {δ : ℝ} (hδ : 0 < δ)
    {g : ℂ → E} (hg : Continuous g) (x : ℂ) :
    Continuous (cancellationJetIntegrand b δ g x) := by
  have hK : ContDiff ℝ ∞ (fun w => b w • smoothCauchyKernel δ w) :=
    b.contDiff.smul (smoothCauchyKernel_smooth hδ)
  have hD : Continuous (fun w => cutoffCauchyJet b δ w) := by
    simp_rw [← cutoffCauchyJet_eq b hδ]
    exact hK.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (((ContinuousLinearMap.lsmul ℝ ℂ).flip).continuous.comp
    ((hg.comp (continuous_const.sub continuous_id)).sub continuous_const)).clm_comp hD

omit [CompleteSpace E] in
lemma cancellationJetIntegrand_bound (b : ContDiffBump (0:ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (hCb : ∀ δ : ℝ, 0 < δ → ∀ z v : ℂ, z ≠ 0 →
      ‖fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z v‖ ≤
        (C*‖z‖⁻¹+3/‖z‖^2)*‖v‖)
    {g : ℂ → E} {H : ℝ} (hH : 0 ≤ H)
    (hg : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖^((1:ℝ)/3))
    {δ : ℝ} (hδ : 0 < δ) (x w : ℂ) :
    ‖cancellationJetIntegrand b δ g x w‖ ≤ (C+3)*H*cauchySchauderWeight b.rOut w := by
  have hw0 : 0 ≤ cauchySchauderWeight b.rOut w := by
    apply indicator_nonneg _ w
    intro z _
    exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [cancellationJetIntegrand_apply, norm_smul, ← cutoffCauchyJet_eq b hδ]
  exact cutoff_smoothCauchyKernel_schauder_bound b hC hCb hH hg hδ x w v

omit [CompleteSpace E] in
lemma cancellationJetIntegrand_tendsto (b : ContDiffBump (0:ℂ))
    (g : ℂ → E) (x w : ℂ) :
    Tendsto (fun δ : ℝ => cancellationJetIntegrand b δ g x w) (𝓝[>] 0)
      (𝓝 (cancellationJetIntegrand b 0 g x w)) := by
  by_cases hw : w = 0
  · subst w
    simp only [cancellationJetIntegrand, sub_zero, sub_self, map_zero, ContinuousLinearMap.zero_comp]
    exact tendsto_const_nhds
  · have h : ContinuousAt (fun δ : ℝ => cancellationJetIntegrand b δ g x w) 0 :=
      (show ContinuousAt (fun _ : ℝ => (ContinuousLinearMap.lsmul ℝ ℂ).flip (g (x-w)-g x)) 0
        from continuousAt_const).clm_comp (cutoffCauchyJet_continuousAt b hw)
    exact h.tendsto.mono_left nhdsWithin_le_nhds


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_HolderTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped Topology
open Set Filter
open scoped ContDiff
open MeasureTheory
section
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
 [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma holder_taylor_remainder {f : D → E} (hf : Differentiable ℝ f)
    {M α : ℝ} (hM : 0 ≤ M) (hα : 0 ≤ α)
    (hdf : ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ M*‖x-y‖^α) (x h : D) :
    ‖f (x+h)-f x-fderiv ℝ f x h‖ ≤ (M*‖h‖^α)*‖h‖ := by
  have hball : x+h ∈ Metric.closedBall x ‖h‖ := by
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, le_refl]
  have hb (z : D) (hz : z ∈ Metric.closedBall x ‖h‖) :
      ‖fderiv ℝ f z-fderiv ℝ f x‖ ≤ M*‖h‖^α := by
    apply (hdf z x).trans
    apply mul_le_mul_of_nonneg_left _ hM
    apply Real.rpow_le_rpow (norm_nonneg _) _ hα
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have he := (convex_closedBall x ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt) hb
    (Metric.mem_closedBall_self (norm_nonneg h)) hball
  simpa only [add_sub_cancel_left] using he

lemma hasFDerivAt_of_holder_remainder {f : D → E} (L : D →L[ℝ] E) (x : D)
    {C α : ℝ} (hα : 0 < α)
    (hb : ∀ h, ‖f (x+h)-f x-L h‖ ≤ (C*‖h‖^α)*‖h‖) : HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have ht : Tendsto (fun h : D => C*‖h‖^α) (𝓝 0) (𝓝 (0:ℝ)) := by
    simpa only [norm_zero, Real.zero_rpow hα.ne', mul_zero] using
      (show Tendsto (fun h : D => C*‖h‖^α) (𝓝 0) (𝓝 (C*‖(0:D)‖^α)) from
        (continuous_const.mul (continuous_norm.rpow_const (fun _ => Or.inr hα.le))).tendsto 0)
  filter_upwards [(tendsto_order.mp ht).2 c hc] with h hh
  exact (hb h).trans (mul_le_mul_of_nonneg_right hh.le (norm_nonneg _))

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
lemma holder_continuous {f : D → E} {C α : ℝ} (hα : 0 < α)
    (hb : ∀ x y, ‖f x-f y‖ ≤ C*‖x-y‖^α) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change Tendsto f (𝓝 x) (𝓝 (f x))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun y : D => C*‖y-x‖^α) (𝓝 x) (𝓝 (0:ℝ)) := by
    have hcont : Continuous (fun y : D => C*‖y-x‖^α) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        (fun _ => Or.inr hα.le))
    simpa only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] using hcont.tendsto x
  exact squeeze_zero (fun _ => norm_nonneg _) (fun y => hb y x) ht

lemma hasFDerivAt_limit_of_holder_derivative {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → D → E} {L : ι → D → (D →L[ℝ] E)} {f₀ : D → E} {L₀ : D → D →L[ℝ] E}
    {M α : ℝ} (hM : 0 ≤ M) (hα : 0 < α)
    (hd : ∀ᶠ i in l, ∀ x, HasFDerivAt (f i) (L i x) x)
    (hH : ∀ᶠ i in l, ∀ x y, ‖L i x-L i y‖ ≤ M*‖x-y‖^α)
    (hf : ∀ x, Tendsto (fun i => f i x) l (𝓝 (f₀ x)))
    (hL : ∀ x, Tendsto (fun i => L i x) l (𝓝 (L₀ x))) (x : D) :
    HasFDerivAt f₀ (L₀ x) x := by
  apply hasFDerivAt_of_holder_remainder _ x hα
  intro v
  have htL := (ContinuousLinearMap.apply ℝ E v).continuous.tendsto (L₀ x) |>.comp (hL x)
  apply le_of_tendsto (((hf (x+v)).sub (hf x)).sub htL).norm
  filter_upwards [hd, hH] with i hi hh
  have hEq : fderiv ℝ (f i) = L i := funext fun z => (hi z).fderiv
  have he := holder_taylor_remainder (fun z => (hi z).differentiableAt) hM hα.le
    (fun z w => by rw [hEq]; exact hh z w) x v
  change ‖f i (x+v)-f i x-L i x v‖ ≤ _
  simpa only [hEq] using he

end
section

local instance instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_2 : NormedAddCommGroup (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdComplex_solutions_2 : NormedSpace ℝ (ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace

def tailCauchyKernel (δ : ℝ) (z : ℂ) : ℂ :=
  (1 - scaledSchauderBump 1 z) • smoothCauchyKernel δ z

def tailCauchyJet (δ : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (1-scaledSchauderBump 1 z) • regularizedCauchyJet δ z -
    (fderiv ℝ (scaledSchauderBump 1) z).smulRight (smoothCauchyKernel δ z)

lemma tailCauchyKernel_smooth {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (tailCauchyKernel δ) :=
  (contDiff_const.sub (scaledSchauderBump_smooth 1)).smul (smoothCauchyKernel_smooth hδ)

lemma tailCauchyKernel_eventually_zero (δ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    tailCauchyKernel δ =ᶠ[𝓝 z] (fun _ => 0) := by
  filter_upwards [scaledSchauderBump_eventually_one (by norm_num : (0:ℝ) < 1) hz] with w hw
  simp only [tailCauchyKernel, hw, sub_self, zero_smul]

lemma tailCauchyJet_eq {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    fderiv ℝ (tailCauchyKernel δ) z = tailCauchyJet δ z := by
  change fderiv ℝ (fun w => (1-scaledSchauderBump 1 w) • smoothCauchyKernel δ w) z = _
  rw [fderiv_fun_smul
    ((contDiff_const.sub (scaledSchauderBump_smooth 1)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)
    ((smoothCauchyKernel_smooth hδ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z),
    regularizedCauchyJet_eq hδ, fderiv_const_sub]
  ext v
  simp only [tailCauchyJet, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, neg_apply, neg_smul, sub_eq_add_neg]

lemma tailCauchyKernel_zero (z : ℂ) : tailCauchyKernel 0 z = (1-schauderBump z) • z⁻¹ := by
  have he : (‖z‖^2)⁻¹ • star z = z⁻¹ := by
    rw [Complex.inv_def,Complex.normSq_eq_norm_sq]
    simp only [Complex.real_smul,Complex.ofReal_inv]
    exact mul_comm _ _
  simpa only [tailCauchyKernel, scaledSchauderBump, smoothCauchyKernel,
    inv_one, one_smul, add_zero] using congrArg ((1-schauderBump z) • ·) he

lemma tailCauchyKernel_tendsto (z : ℂ) :
    Tendsto (fun δ : ℝ => tailCauchyKernel δ z) (𝓝[>] 0) (𝓝 (tailCauchyKernel 0 z)) := by
  rw [tailCauchyKernel_zero]
  simpa only [tailCauchyKernel, scaledSchauderBump, inv_one, one_smul] using
    (tendsto_const_nhds.smul (smoothCauchyKernel_tendsto z) :
      Tendsto (fun δ : ℝ => (1-schauderBump z) • smoothCauchyKernel δ z) _ _)

local instance instNormedAddCommGroupContinuousLinearMapRealIdComplex_solutions_3_r95f9f8_1 : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
local instance instNormedSpaceRealContinuousLinearMapIdComplex_solutions_3_r95f9f8_1 : NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℂ) := ContinuousLinearMap.toNormedSpace
lemma tailCauchyJet_tendsto (z : ℂ) :
    Tendsto (fun δ : ℝ => tailCauchyJet δ z) (𝓝[>] 0) (𝓝 (tailCauchyJet 0 z)) := by
  by_cases hz : z = 0
  · subst z
    have he := scaledSchauderBump_eventually_one (by norm_num : (0:ℝ) < 1)
      (by simp : ‖(0:ℂ)‖ ≤ (1:ℝ))
    have hd : fderiv ℝ (scaledSchauderBump 1) 0 = 0 := he.fderiv_eq.trans (by simp)
    simp only [tailCauchyJet, he.eq_of_nhds, sub_self, zero_smul, hd,
      ContinuousLinearMap.zero_smulRight]
    exact tendsto_const_nhds
  · have hv : ContinuousAt (fun δ : ℝ => smoothCauchyKernel δ z) 0 := by
      have hn : ‖z‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
      have hi : ContinuousAt (fun δ : ℝ => (‖z‖^2+δ)⁻¹) 0 :=
        (continuousAt_const.add continuousAt_id).inv₀ (by simpa using hn)
      exact hi.smul (show ContinuousAt (fun _ : ℝ => star z) 0 from continuousAt_const)
    have hA : ContinuousAt (fun δ : ℝ => (1-scaledSchauderBump 1 z) • regularizedCauchyJet δ z) 0 :=
      (show ContinuousAt (fun _ : ℝ => 1-scaledSchauderBump 1 z) 0 from continuousAt_const).smul
        (regularizedCauchyJet_continuousAt hz)
    have hB : ContinuousAt (fun δ : ℝ => (fderiv ℝ (scaledSchauderBump 1) z).smulRight
        (smoothCauchyKernel δ z)) 0 :=
      (ContinuousLinearMap.smulRightL ℝ ℂ ℂ (fderiv ℝ (scaledSchauderBump 1) z)).continuous.continuousAt.comp hv
    have ht : ContinuousAt (fun δ : ℝ => tailCauchyJet δ z) 0 := hA.sub hB
    exact ht.tendsto.mono_left nhdsWithin_le_nhds

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def tailCauchyTransform (g : ℂ → E) : ℂ → E :=
  convolution (tailCauchyKernel 0) g (ContinuousLinearMap.lsmul ℝ ℂ) volume

def tailIntegralJet (g : ℂ → E) (x w : ℂ) : ℂ →L[ℝ] E :=
  ((ContinuousLinearMap.lsmul ℝ ℂ).flip (g w)).comp (tailCauchyJet 0 (x-w))

def tailCauchyDerivative (g : ℂ → E) (x : ℂ) : ℂ →L[ℝ] E :=
  ∫ w : ℂ, tailIntegralJet g x w

omit [CompleteSpace E] in
lemma tailCauchyTransform_eq (g : ℂ → E) (x : ℂ) :
    tailCauchyTransform g x = ∫ w : ℂ, tailCauchyKernel 0 (x-w) • g w :=
  convolution_eq_swap _

omit [CompleteSpace E] in
lemma tailIntegralJet_bound {A : ℝ} (hA : 0 ≤ A) (hJ : ∀ z, ‖tailCauchyJet 0 z‖ ≤ A)
    (g : ℂ → E) (x w : ℂ) : ‖tailIntegralJet g x w‖ ≤ A*‖g w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hA (norm_nonneg _))
  intro v
  change ‖tailCauchyJet 0 (x-w) v • g w‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ (A*‖v‖)*‖g w‖ := mul_le_mul_of_nonneg_right
      ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hJ _) (norm_nonneg _)))
      (norm_nonneg _)
    _ = _ := by ring

lemma cutoffCauchyKernel_integrable (b : ContDiffBump (0:ℂ)) :
    Integrable (fun w : ℂ => b w • w⁻¹) :=
  locallyIntegrable_complex_inv.integrable_smul_left_of_hasCompactSupport b.continuous b.hasCompactSupport

omit [CompleteSpace E] in
lemma cutoffCauchy_convolution_integrable (b : ContDiffBump (0:ℂ)) {g : ℂ → E}
    (hg : Continuous g) (x : ℂ) : Integrable (fun w : ℂ => (b w • w⁻¹) • g (x-w)) := by
  have h := locallyIntegrable_complex_inv.integrable_smul_right_of_hasCompactSupport
    (b.continuous.smul (hg.comp (continuous_const.sub continuous_id)))
    (b.hasCompactSupport.smul_right (f' := fun w => g (x-w)))
  have he : (fun w : ℂ => (b w • w⁻¹) • g (x-w)) =
      (fun w : ℂ => w⁻¹ • (b w • g (x-w))) := by
    funext w
    rw [smul_assoc, smul_comm (b w) (w⁻¹)]
  rw [he]
  exact h

omit [CompleteSpace E] in
lemma cutoffCauchy_value_bound (b : ContDiffBump (0:ℂ)) {g : ℂ → E} {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (x : ℂ) :
    ‖convolution (fun w => b w • w⁻¹) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x‖ ≤
      (∫ w : ℂ, ‖b w • w⁻¹‖)*M := by
  apply (norm_integral_le_of_norm_le ((cutoffCauchyKernel_integrable b).norm.mul_const M) ?_).trans_eq
    (integral_mul_const M _)
  apply Eventually.of_forall
  intro w
  change ‖(b w • w⁻¹) • g (x-w)‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)

def globalCauchyDerivative (g : ℂ → E) (x : ℂ) : ℂ →L[ℝ] E :=
  (Real.pi : ℂ)⁻¹ • (cutoffCauchyDerivative schauderBump g x + tailCauchyDerivative g x)

end HigherDimensionalBallPacking.Rigidity

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def curlJet : (ℂ →L[ℝ] E) →L[ℝ] E :=
  Complex.I • ContinuousLinearMap.apply ℝ E (1:ℂ) - ContinuousLinearMap.apply ℝ E Complex.I

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance markedJetInst1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedJetInst2 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
universe u v
variable {D : Type v} {E F : Type u}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance smoothSuperInst1 : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance smoothSuperInst2 : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

lemma compactSupport_fderiv_of_perturbation {f : E → F} (c : F)
    (hc : HasCompactSupport (fun x => f x-c)) : HasCompactSupport (fderiv ℝ f) := by
  have he : fderiv ℝ (fun x => f x-c) = fderiv ℝ f := funext fun x => fderiv_sub_const c
  rw [← he]
  exact hc.fderiv ℝ


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance crSectInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance crSectInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {K : Set ℂ} (hK : IsCompact K)

def complexSlope (a : E) : ℂ →L[ℝ] E :=
  (ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedFrame
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
local instance markedFrameInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedFrameInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance affineCutInst5 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance affineCutInst6 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

def complexSlopeCLM : E →L[ℝ] (ℂ →L[ℝ] E) :=
  (ContinuousLinearMap.lsmul ℝ ℂ (E := E)).flip

variable (b : ContDiffBump (0:ℂ))

lemma cutoffCoordinate_smooth : ContDiff ℝ ∞ (fun z : ℂ => b z • z) :=
  b.contDiff.smul contDiff_id
lemma cutoffCoordinate_compact : HasCompactSupport (fun z : ℂ => b z • z) :=
  b.hasCompactSupport.smul_right


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
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
local instance csInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance csInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance csInst9 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance csInst10 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance ccInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance ccInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance ctInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
open scoped Topology BoundedContinuousFunction
open Set Filter



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FiniteExtensions
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance jetSuperInst1 : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetSuperInst2 : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance jetSuperInst3_r95f9f8_1 : NormedAddCommGroup (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetSuperInst5 : NormedAddCommGroup (ℂ →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetSuperInst4_r95f9f8_1 : NormedSpace ℝ (ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance jetSuperInst6 : NormedSpace ℝ (ℂ →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [completeSpaceE : CompleteSpace E]
local instance zeroOrderInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance zeroOrderInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_CompactFredholmAlternative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance linCRInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance linCRInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

abbrev complexI : E →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I

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

lemma compactPerturbation_of_outside_constant {D F : Type*} [NormedAddCommGroup D]
    [ProperSpace D] [NormedAddCommGroup F] {P : D → F} (c : F) {B : ℝ}
    (hP : ∀ x, B < ‖x‖ → P x=c) : HasCompactSupport (fun x => P x-c) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:D) B)
  intro x hx
  by_contra hxB
  apply hx
  change P x-c=0
  rw [hP x (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hxB),sub_self]


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance markFiniteInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markFiniteInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance markedChartInst5 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance markedChartInst6 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace



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
open Set Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance freeFredInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance freeFredInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance freeChartInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance freeChartInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
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

abbrev PlaneTest := {g : ℂ → ℝ // ContDiff ℝ ∞ g ∧ HasCompactSupport g}

omit [CompleteSpace E] in
lemma planeTest_integrable [CompleteSpace E] (g : PlaneTest) (v : ℂ →ᵇ E) :
    Integrable (fun z => g.val z • v z) :=
  v.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    g.property.1.continuous g.property.2

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_CompatibleHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter

variable {n : ℕ}

def fullTime : ℝ → ℝ := Real.smoothTransition
lemma fullTime_range (t : ℝ) : fullTime t∈Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
lemma fullTime_smooth : ContDiff ℝ ∞ fullTime := by
  apply contDiff_infty.mpr
  intro m
  exact Real.smoothTransition.contDiff
@[simp] lemma fullTime_zero : fullTime 0=0 := Real.smoothTransition.zero
@[simp] lemma fullTime_one : fullTime 1=1 := Real.smoothTransition.one

def fullTimeBump : ContDiffBump (0:ℝ) := ⟨2,3,by norm_num,by norm_num⟩

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance gmc7 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance gmc8 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_ParameterizedImplicit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology
open Filter
open scoped BoundedContinuousFunction
open Set Function
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance gmChartInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance gmChartInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

end

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

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

section SlicedDomain
variable (Y : Set E) (L : E → ℝ)

abbrev UnitInterval := ↥(Set.Icc (0 : ℝ) 1)

end SlicedDomain

end Comparison
end PackingSufficiencySupport

end

end OAI
end


