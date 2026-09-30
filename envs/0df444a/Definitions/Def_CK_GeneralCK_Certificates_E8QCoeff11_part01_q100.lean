-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8QCoeff11_part01_q100
-- name    : CK_GeneralCK_Certificates_E8QCoeff11_part01_q100
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T17:36:19.715447+00:00
-- url     : https://prove2.me/theorems/07a3c40b-6d6d-4814-a473-3b6f149b0896
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8QCoeff11 (part 2 of 3) (piece 1 of 2)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8QCoeff11 (part 2 of 3) (piece 1 of 2)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8QCoeff11 (part 2 of 3) (piece 1 of 2)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8QCoeff11 (part 2 of 3) (piece 1 of 2) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8QCoeff11 (part 2 of 3) (piece 1 of 2).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QCoeff11_part01_q00


namespace GeneralCK.Certificates.E8QCoeff11
open Filter
open E8AnalyticGerm E8AnalyticInverseRecurrence E8NormalizedCoeff5
open E8ParamCoeff9 E8ThetaParamCoeff5 E8ThetaParamCoeff7 E8ThetaParamCoeff9
open E8ThetaParamCoeff11 E8ComposeCoeff11 E8LowOrderThetaCoefficients
open E8HigherRationalTrace E8HigherSourceBoxBridge E8AnalyticCoefficientBoxes
theorem logTwo_ne_priv : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

theorem thetaTaylorCoeff_even_priv (n : ℕ) (hn : Even n) :
    thetaTaylorCoeff n = 0 := by
  have heq : (fun z : ℂ => thetaGerm (-z)) =ᶠ[nhds 0]
      (fun z => -thetaGerm z) := by
    filter_upwards [eventually_xBiasGerm_neg] with z hz
    simp only [thetaGerm, hz, thetaParam_neg]
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_comp_neg, iteratedDeriv_fun_neg] at hd
  simp only [neg_zero, Even.neg_one_pow hn, one_smul] at hd
  unfold thetaTaylorCoeff
  have hz : iteratedDeriv n thetaGerm 0 = 0 := by
    linear_combination (1 / 2 : ℂ) * hd
  simp [hz]

theorem clogTwo_eq_priv : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
  (Complex.natCast_log (n := 2)).symm

theorem clogTwo_ne_priv : Complex.log (2 : ℂ) ≠ 0 := by
  rw [clogTwo_eq_priv]
  exact logTwo_ne_priv

end GeneralCK.Certificates.E8QCoeff11


