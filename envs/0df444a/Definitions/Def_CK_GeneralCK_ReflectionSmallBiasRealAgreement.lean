-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasRealAgreement
-- name    : CK_GeneralCK_ReflectionSmallBiasRealAgreement
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:32:02.290364+00:00
-- url     : https://prove2.me/theorems/fff95caa-dfb1-4591-88fe-92aaaba458cc
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasRealAgreement` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasRealAgreement` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasRealAgreement` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasRealAgreement (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasRealAgreement.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasCurvatureAssembly
import Definitions.Def_CK_GeneralCK_ReflectionRegularDifference_v2

-- ===== source module GeneralCK.ReflectionSmallBiasRealAgreement =====
section

/-! Agreement of the quantitative complex difference with the original real curvature. -/

namespace GeneralCK.Reflection.SmallBiasRealAgreement

open ComplexEntropy ComplexFixedPoint ComplexGlobalAnalytic SmallBiasComplexDomain
open Filter
open scoped Topology

/- The elementary real-axis log identity, as in ReflectionComplexRealBridge. -/
theorem entropyExt_ofReal {c : ℝ} (hc₀ : -1 < c) (hc₁ : c < 1) :
    entropyExt (c : ℂ) = (Certificates.Reflection.biasE c : ℂ) := by
  have hp : 0 ≤ 1 + c := (by linarith : 0 ≤ 1 + c)
  have hm : 0 ≤ 1 - c := (by linarith : 0 ≤ 1 - c)
  have hpLog : Complex.log (1 + (c : ℂ)) = (Real.log (1 + c) : ℂ) := by
    calc
      Complex.log (1 + (c : ℂ)) = Complex.log ((1 + c : ℝ) : ℂ) := by norm_num
      _ = (Real.log (1 + c) : ℂ) := (Complex.ofReal_log hp).symm
  have hmLog : Complex.log (1 - (c : ℂ)) = (Real.log (1 - c) : ℂ) := by
    calc
      Complex.log (1 - (c : ℂ)) = Complex.log ((1 - c : ℝ) : ℂ) := by norm_num
      _ = (Real.log (1 - c) : ℂ) := (Complex.ofReal_log hm).symm
  unfold entropyExt Certificates.Reflection.biasE
  rw [hpLog, hmLog]
  norm_num

theorem atanhExt_ofReal {c : ℝ} (hc : -1<c) (hc1 : c<1) :
    atanhExt (c:ℂ) = (SmallMean.A c:ℂ) := by
  have hp : 0 < 1+c := by linarith
  have hm : 0 < 1-c := by linarith
  have hplus : Complex.log (1+(c:ℂ)) = (Real.log (1+c):ℂ) := by
    rw [show 1+(c:ℂ) = ((1+c:ℝ):ℂ) by norm_num,← Complex.ofReal_log hp.le]
  have hminus : Complex.log (1-(c:ℂ)) = (Real.log (1-c):ℂ) := by
    rw [show 1-(c:ℂ) = ((1-c:ℝ):ℂ) by norm_num,← Complex.ofReal_log hm.le]
  unfold atanhExt SmallMean.A
  rw [hplus,hminus,Real.log_div hp.ne' hm.ne']
  norm_num

theorem fixedPointOnDisc_ofReal {t : ℝ} (ht : |t| < 7/10) :
    fixedPointOnDisc (t:ℂ) = (regularContact t:ℂ) := by
  have htn : ‖(t:ℂ)‖ < (7/10:ℝ) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using ht
  have hc := regularContact_mem t
  have hcBound : ‖(regularContact t:ℂ)‖ ≤ (4/5:ℝ) := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    have hlog : Real.log 2 ≤ (7/10:ℝ) := by linarith [Real.log_two_lt_d9]
    calc
      |regularContact t| ≤ |t| * Real.log 2 := abs_regularContact_le t
      _ ≤ (7/10:ℝ)*(7/10:ℝ) :=
        mul_le_mul ht.le hlog (Real.log_pos (by norm_num)).le (by norm_num)
      _ ≤ 4/5 := by norm_num
  have hfix : Function.IsFixedPt (ComplexDiscElementary.contactMap entropyExt (t:ℂ))
      (regularContact t:ℂ) := by
    unfold Function.IsFixedPt ComplexDiscElementary.contactMap
    rw [entropyExt_ofReal hc.1 hc.2]
    exact_mod_cast (regularContact_equation t).symm
  rw [fixedPointOnDisc_eq htn]
  exact (eq_fixedPoint htn.le
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hcBound) hfix).symm

theorem meanEntropy_ofReal {a b : ℝ} (ha : -1<a) (ha1 : a<1) (hb : -1<b) (hb1 : b<1) :
    SmallBiasComplexDomain.meanEntropy (a:ℂ) (b:ℂ) = (RegularDifference.entropy a b:ℂ) := by
  unfold SmallBiasComplexDomain.meanEntropy RegularDifference.entropy
  rw [entropyExt_ofReal ha ha1,entropyExt_ofReal hb hb1]
  norm_num

theorem contactValue_ofReal {s e : ℝ} (ht : ‖(s:ℂ)/(e:ℂ)‖ < (7/10:ℝ)) :
    contactValue (s:ℂ) (e:ℂ) = (RegularDifference.FNat s e:ℂ) := by
  have ht' : |s/e| < (7/10:ℝ) := by
    simpa only [← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs] using ht
  have hc := regularContact_mem (s/e)
  unfold contactValue RegularDifference.FNat
  rw [← Complex.ofReal_div,fixedPointOnDisc_ofReal ht',atanhExt_ofReal hc.1 hc.2]
  norm_num

theorem difference_ofReal {a b : ℝ} (ha : |a| ≤ (21/50:ℝ)) (hb : |b| ≤ (21/50:ℝ)) :
    difference (a:ℂ) (b:ℂ) = (RegularDifference.Dreg a b:ℂ) := by
  have ha0 : -1<a := by have := (abs_le.mp ha).1; linarith
  have ha1 : a<1 := by have := (abs_le.mp ha).2; linarith
  have hb0 : -1<b := by have := (abs_le.mp hb).1; linarith
  have hb1 : b<1 := by have := (abs_le.mp hb).2; linarith
  have han : ‖(a:ℂ)‖ ≤ (21/50:ℝ) := by simpa only [Complex.norm_real,Real.norm_eq_abs] using ha
  have hbn : ‖(b:ℂ)‖ ≤ (21/50:ℝ) := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hb
  have he := meanEntropy_ofReal ha0 ha1 hb0 hb1
  have htp : ‖((((a+b)/2:ℝ):ℂ)/(RegularDifference.entropy a b:ℂ))‖ < (7/10:ℝ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_ofNat,← he] using
      norm_parameter_lt han hbn (norm_half_add_le han hbn)
  have htm : ‖((((a-b)/2:ℝ):ℂ)/(RegularDifference.entropy a b:ℂ))‖ < (7/10:ℝ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_ofNat,← he] using
      norm_parameter_lt han hbn (norm_half_sub_le han hbn)
  have hp := contactValue_ofReal htp
  have hm := contactValue_ofReal htm
  simp only [Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_ofNat] at hp hm
  unfold difference RegularDifference.Dreg
  rw [atanhExt_ofReal ha0 ha1,atanhExt_ofReal hb0 hb1,he,hp,hm]
  norm_num

theorem deriv2_difference_eq_curvature {a b : ℝ} (hb : 0<b) (hba : b<a) (ha1 : a≤3/20) :
    deriv (deriv (fun x : ℝ => (SmallBiasCurvatureAssembly.complexDifference ((x:ℂ),(b:ℂ))).re)) a =
      GeneralCK.Reflection.curvature a b := by
  have haR : a < (21/50:ℝ) := by linarith
  have hbR : |b| ≤ (21/50:ℝ) := by rw [abs_of_pos hb]; linarith
  have he : (fun x : ℝ => (SmallBiasCurvatureAssembly.complexDifference ((x:ℂ),(b:ℂ))).re) =ᶠ[𝓝 a]
      (fun x => GeneralCK.Reflection.D x b) := by
    filter_upwards [Ioo_mem_nhds hba haR] with x hx
    have hxp : 0<x := hb.trans hx.1
    have hxR : |x| ≤ (21/50:ℝ) := by rw [abs_of_pos hxp]; exact hx.2.le
    change (difference (x:ℂ) (b:ℂ)).re = _
    rw [difference_ofReal hxR hbR,Complex.ofReal_re,RegularDifference.Dreg_eq_D hb.le hx.1.le (by linarith [hx.2])]
  exact he.deriv.deriv_eq.trans (GeneralCK.Reflection.deriv2_D hb.le hba (by linarith))

end GeneralCK.Reflection.SmallBiasRealAgreement


end


