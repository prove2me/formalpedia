-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8AnalyticGerm
-- name    : CK_GeneralCK_PureGapE8AnalyticGerm
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:46:35.106009+00:00
-- url     : https://prove2.me/theorems/ea71912a-f6d0-44da-af7a-57174731a151
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8AnalyticGerm` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8AnalyticGerm` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8AnalyticGerm` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8AnalyticGerm (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8AnalyticGerm.lean)

import Definitions.Def_CK_GeneralCK_ReflectionComplexContactGerm
import Definitions.Def_CK_GeneralCK_ReflectionComplexContactFactor
import Definitions.Def_CK_GeneralCK_Certificates_E8InverseJet
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.PureGapE8AnalyticGerm =====
section

/-!
# An analytic E8 inverse germ at slope zero

This is deliberately separate from the zero-filled real `e8Q`.  The stable
hyperbolic parametrization is written in the bias coordinate `c = tanh α` and
inverted over `ℂ` near `c = 0`.
-/

namespace GeneralCK.E8AnalyticGerm

open Set Filter Function
open Reflection.ComplexEntropy

























/-- The hyperbolic coordinate is odd, as an identity of principal logarithms. -/
theorem atanhExt_neg (c : ℂ) : atanhExt (-c) = -atanhExt c := by
  unfold atanhExt
  rw [show 1 + -c = 1 - c by ring, show 1 - -c = 1 + c by ring]
  ring

/-- The second hyperbolic denominator is even. -/
theorem biasBExt_neg (c : ℂ) : biasBExt (-c) = biasBExt c := by
  simp only [biasBExt, neg_sq]

/-- Exact odd symmetry of the analytic slope parametrization. -/
theorem thetaParam_neg (c : ℂ) : thetaParam (-c) = -thetaParam c := by
  simp only [thetaParam, atanhExt_neg, neg_sq, biasBExt_neg,
    Reflection.ComplexContactFactor.entropyExt_neg]
  ring

/-- Exact odd symmetry of the analytic contact-coordinate parametrization. -/
theorem xParam_neg (c : ℂ) : xParam (-c) = -xParam c := by
  simp only [xParam, Reflection.ComplexContactFactor.entropyExt_neg]
  ring

private theorem logTwo_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

private theorem one_mem_slit : (1 : ℂ) ∈ Complex.slitPlane := by
  simpa using (Complex.mem_slitPlane_of_norm_lt_one (z := (0 : ℂ)) (by norm_num))
























theorem analyticAt_xParam : AnalyticAt ℂ xParam 0 := by
  unfold xParam
  exact (analyticAt_const.mul analyticAt_id).div
    (analyticAt_const.mul
      (Reflection.ComplexContactGerm.analyticAt_entropyExt (c := (0 : ℂ)) (by norm_num)))
    (by
      rw [Reflection.ComplexContactGerm.entropyExt_zero]
      exact mul_ne_zero (by norm_num) logTwo_ne)

theorem hasDerivAt_xParam_zero : CDeriv xParam (1 / 2) 0 := by
  have hE : CDeriv entropyExt 0 0 := by
    simpa [entropyDeriv] using hasDerivAt_entropyExt (c := (0 : ℂ)) (by norm_num)
  have h := ((hasDerivAt_const (𝕜 := ℂ) 0 (Real.log 2 : ℂ)).mul
    (hasDerivAt_id 0)).div
      ((hasDerivAt_const (𝕜 := ℂ) 0 2).mul hE) (by
        simp only [Pi.mul_apply, Reflection.ComplexContactGerm.entropyExt_zero]
        exact mul_ne_zero (by norm_num) logTwo_ne)
  convert! h using 1
  · simp only [Reflection.ComplexContactGerm.entropyExt_zero, id_eq,
      zero_mul, mul_zero, add_zero, sub_zero, Pi.mul_apply]
    field_simp [logTwo_ne]
    simpa using (div_self logTwo_ne).symm

















































private theorem deriv_thetaParam_zero :
    deriv thetaParam 0 = 4 / (Real.log 2 : ℂ) :=
  hasDerivAt_thetaParam_zero.deriv

private theorem deriv_thetaParam_ne : deriv thetaParam 0 ≠ 0 := by
  rw [deriv_thetaParam_zero]
  exact div_ne_zero (by norm_num) logTwo_ne















theorem analyticAt_biasGerm : AnalyticAt ℂ biasGerm 0 := by
  simpa [biasGerm] using
    analyticAt_thetaParam.analyticAt_localInverse deriv_thetaParam_ne

theorem hasDerivAt_biasGerm_zero :
    CDeriv biasGerm ((Real.log 2 : ℂ) / 4) 0 := by
  have h := analyticAt_thetaParam.hasStrictDerivAt.to_localInverse deriv_thetaParam_ne
  have hk : ((4 / (Real.log 2 : ℂ))⁻¹) = (Real.log 2 : ℂ) / 4 := by
    field_simp [logTwo_ne]
  simpa [biasGerm, deriv_thetaParam_zero, hk] using h.hasDerivAt

theorem analyticAt_qGerm : AnalyticAt ℂ qGerm 0 := by
  exact analyticAt_xParam.comp_of_eq analyticAt_biasGerm biasGerm_zero

/-- The analytic germ has the manuscript's exact linear coefficient. -/
theorem hasDerivAt_qGerm_zero :
    CDeriv qGerm ((Real.log 2 : ℂ) / 8) 0 := by
  have hx : CDeriv xParam (1 / 2) (biasGerm 0) := by
    simpa using hasDerivAt_xParam_zero
  have h := hx.comp (0 : ℂ) hasDerivAt_biasGerm_zero
  convert! h using 1
  · ring









/-- Concrete order-one connection between the analytic germ and the
factorial-normalized inverse jet. -/
theorem qTaylorCoeff_one :
    qTaylorCoeff 1 = (Real.log 2 : ℂ) / 8 := by
  rw [qTaylorCoeff, iteratedDeriv_one, hasDerivAt_qGerm_zero.deriv]
  norm_num

theorem eventually_thetaParam_biasGerm :
    ∀ᶠ y in nhds (0 : ℂ), thetaParam (biasGerm y) = y := by
  simpa [biasGerm, thetaParam_zero] using
    analyticAt_thetaParam.hasStrictDerivAt.eventually_right_inverse deriv_thetaParam_ne

/-- The locally chosen inverse bias coordinate inherits the exact odd symmetry. -/
theorem eventually_biasGerm_neg :
    ∀ᶠ y in nhds (0 : ℂ), biasGerm (-y) = -biasGerm y := by
  let g : ℂ → ℂ := fun y => -biasGerm (-y)
  have hleft := analyticAt_thetaParam.hasStrictDerivAt.eventually_left_inverse
    deriv_thetaParam_ne
  change ∀ᶠ x in nhds (0 : ℂ), biasGerm (thetaParam x) = x at hleft
  have hneg : ∀ᶠ x in nhds (0 : ℂ),
      biasGerm (thetaParam (-x)) = -x := by
    have ht : Tendsto (fun z : ℂ => -z) (nhds 0) (nhds 0) := by
      simpa only [neg_zero] using continuous_neg.tendsto (0 : ℂ)
    exact ht hleft
  have hg : ∀ᶠ x in nhds (0 : ℂ), g (thetaParam x) = x := by
    filter_upwards [hneg] with x hx
    simp only [g, ← thetaParam_neg]
    rw [hx]
    simp
  have hu : ∀ᶠ y in nhds (0 : ℂ), g y = biasGerm y := by
    simpa [biasGerm] using
      (analyticAt_thetaParam.hasStrictDerivAt.hasStrictFDerivAt_equiv
        deriv_thetaParam_ne).localInverse_unique hg
  filter_upwards [hu] with y hy
  dsimp [g] at hy
  linear_combination -hy

/-- Consequently the analytic inverse contact germ is locally odd. -/
theorem eventually_qGerm_neg :
    ∀ᶠ y in nhds (0 : ℂ), qGerm (-y) = -qGerm y := by
  filter_upwards [eventually_biasGerm_neg] with y hy
  simp only [qGerm, hy, xParam_neg]

/-- Every even factorial-normalized Taylor coefficient of the odd analytic
germ vanishes.  In particular this supplies all even entries through the
order-17 inverse-jet ledger at once. -/
theorem qTaylorCoeff_eq_zero_of_even {n : ℕ} (hn : Even n) :
    qTaylorCoeff n = 0 := by
  have heq : (fun y : ℂ => qGerm (-y)) =ᶠ[nhds 0]
      (fun y : ℂ => -qGerm y) := eventually_qGerm_neg
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at hd
  simp only [neg_zero] at hd
  have hp : (-1 : ℂ) ^ n = 1 := Even.neg_one_pow hn
  rw [hp, one_smul] at hd
  have hz : iteratedDeriv n qGerm 0 = 0 := by
    have htwo : (2 : ℂ) * iteratedDeriv n qGerm 0 = 0 := by
      linear_combination hd
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  unfold qTaylorCoeff
  rw [hz]
  simp

end GeneralCK.E8AnalyticGerm

end


