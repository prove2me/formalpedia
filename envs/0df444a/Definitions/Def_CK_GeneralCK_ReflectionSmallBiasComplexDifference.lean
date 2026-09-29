-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasComplexDifference
-- name    : CK_GeneralCK_ReflectionSmallBiasComplexDifference
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T12:56:29.477977+00:00
-- url     : https://prove2.me/theorems/e6b97a80-3dca-4d0a-b159-f5cd4f0e8a28
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasComplexDifference` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasComplexDifference` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasComplexDifference` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasComplexDifference (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasComplexDifference.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasComplexDomain

-- ===== source module GeneralCK.ReflectionSmallBiasComplexDifference =====
section

/-! # The holomorphic reflection difference on the quantitative bidisc -/

namespace GeneralCK.Reflection.SmallBiasComplexDomain

open ComplexEntropy ComplexGlobalAnalytic

noncomputable def atanhExt (c : ℂ) : ℂ :=
  (Complex.log (1 + c) - Complex.log (1 - c)) / 2

theorem atanhExt_eq_neg_entropyDeriv (c : ℂ) : atanhExt c = -entropyDeriv c := by
  unfold atanhExt entropyDeriv
  ring

theorem analyticAt_atanhExt {c : ℂ} (hc : ‖c‖ < 1) : AnalyticAt ℂ atanhExt c := by
  have hp : AnalyticAt ℂ (fun z : ℂ => 1 + z) c := analyticAt_const.add analyticAt_id
  have hm : AnalyticAt ℂ (fun z : ℂ => 1 - z) c := analyticAt_const.sub analyticAt_id
  have hpSlit : 1 + c ∈ Complex.slitPlane := Complex.mem_slitPlane_of_norm_lt_one hc
  have hmSlit : 1 - c ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg, norm_neg] using
      (Complex.mem_slitPlane_of_norm_lt_one (z := -c) (by simpa using hc))
  exact ((hp.clog hpSlit).sub (hm.clog hmSlit)).div analyticAt_const (by norm_num : (2 : ℂ) ≠ 0)

theorem norm_atanhExt_le_source {c : ℂ} (hc : ‖c‖ ≤ (21 / 50 : ℝ)) :
    ‖atanhExt c‖ ≤ (1 / 2 : ℝ) := by
  rw [atanhExt_eq_neg_entropyDeriv, norm_neg]
  have hc1 : ‖c‖ < 1 := hc.trans_lt (by norm_num)
  have hinv : (1 - ‖c‖)⁻¹ ≤ (50 / 29 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos.mpr hc1) (by norm_num : (0 : ℝ) < 50 / 29)]
    linarith
  calc
    _ ≤ ‖c‖ + ‖c‖ ^ 3 / 3 + ‖c‖ ^ 5 * (1 - ‖c‖)⁻¹ / 5 := norm_entropyDeriv_le hc1
    _ ≤ (21 / 50 : ℝ) + (21 / 50 : ℝ) ^ 3 / 3 +
        (21 / 50 : ℝ) ^ 5 * (50 / 29 : ℝ) / 5 := by gcongr
    _ ≤ (1 / 2 : ℝ) := by norm_num

theorem norm_atanhExt_le_contact {c : ℂ} (hc : ‖c‖ ≤ (4 / 5 : ℝ)) :
    ‖atanhExt c‖ ≤ (7 / 5 : ℝ) := by
  rw [atanhExt_eq_neg_entropyDeriv, norm_neg]
  exact norm_entropyDeriv_le_seven_fifths hc

noncomputable def contactValue (s e : ℂ) : ℂ :=
  2 * s * atanhExt (fixedPointOnDisc (s / e))

noncomputable def difference (a b : ℂ) : ℂ :=
  a * atanhExt b + b * atanhExt a -
    contactValue ((a + b) / 2) (meanEntropy a b) +
    contactValue ((a - b) / 2) (meanEntropy a b)

theorem norm_half_add_le {a b : ℂ}
    (ha : ‖a‖ ≤ (21 / 50 : ℝ)) (hb : ‖b‖ ≤ (21 / 50 : ℝ)) :
    ‖(a + b) / 2‖ ≤ (21 / 50 : ℝ) := by
  rw [norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  have hh := norm_add_le a b
  linarith

theorem norm_half_sub_le {a b : ℂ}
    (ha : ‖a‖ ≤ (21 / 50 : ℝ)) (hb : ‖b‖ ≤ (21 / 50 : ℝ)) :
    ‖(a - b) / 2‖ ≤ (21 / 50 : ℝ) := by
  rw [norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  have hh := norm_sub_le a b
  linarith

theorem analyticAt_meanEntropy {p : ℂ × ℂ}
    (ha : ‖p.1‖ < 1) (hb : ‖p.2‖ < 1) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => meanEntropy q.1 q.2) p :=
  (((ComplexContactGerm.analyticAt_entropyExt ha).comp analyticAt_fst).add
    ((ComplexContactGerm.analyticAt_entropyExt hb).comp analyticAt_snd)).div
      analyticAt_const (by norm_num : (2 : ℂ) ≠ 0)

theorem analyticAt_contactValue {p : ℂ × ℂ}
    (he : p.2 ≠ 0) (hparam : ‖p.1 / p.2‖ < (7 / 10 : ℝ)) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => contactValue q.1 q.2) p := by
  have hratio : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1 / q.2) p :=
    analyticAt_fst.div analyticAt_snd he
  have hc := (analyticAt_fixedPointOnDisc hparam).comp_of_eq hratio rfl
  have hmem : ‖fixedPointOnDisc (p.1 / p.2)‖ < (4 / 5 : ℝ) := by
    simpa only [Metric.mem_ball, dist_zero_right] using fixedPointOnDisc_mem_ball hparam
  have hA := (analyticAt_atanhExt (hmem.trans (by norm_num))).comp_of_eq hc rfl
  exact (analyticAt_const.mul analyticAt_fst).mul hA

/-- Joint holomorphy holds on a neighborhood of every point of the closed bidisc. -/
theorem analyticAt_difference {p : ℂ × ℂ}
    (ha : ‖p.1‖ ≤ (21 / 50 : ℝ)) (hb : ‖p.2‖ ≤ (21 / 50 : ℝ)) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => difference q.1 q.2) p := by
  have he := meanEntropy_ne_zero ha hb
  have hE := analyticAt_meanEntropy (ha.trans_lt (by norm_num)) (hb.trans_lt (by norm_num))
  have hs : AnalyticAt ℂ (fun q : ℂ × ℂ => (q.1 + q.2) / 2) p :=
    (analyticAt_fst.add analyticAt_snd).div analyticAt_const (by norm_num : (2 : ℂ) ≠ 0)
  have hd : AnalyticAt ℂ (fun q : ℂ × ℂ => (q.1 - q.2) / 2) p :=
    (analyticAt_fst.sub analyticAt_snd).div analyticAt_const (by norm_num : (2 : ℂ) ≠ 0)
  have hplus := (analyticAt_contactValue (p := ((p.1 + p.2) / 2, meanEntropy p.1 p.2)) he
    (norm_parameter_lt ha hb (norm_half_add_le ha hb))).comp_of_eq (hs.prod hE) rfl
  have hminus := (analyticAt_contactValue (p := ((p.1 - p.2) / 2, meanEntropy p.1 p.2)) he
    (norm_parameter_lt ha hb (norm_half_sub_le ha hb))).comp_of_eq (hd.prod hE) rfl
  have hA := (analyticAt_atanhExt (ha.trans_lt (by norm_num))).comp
    (analyticAt_fst : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1) p)
  have hB := (analyticAt_atanhExt (hb.trans_lt (by norm_num))).comp
    (analyticAt_snd : AnalyticAt ℂ (fun q : ℂ × ℂ => q.2) p)
  exact ((analyticAt_fst.mul hB).add (analyticAt_snd.mul hA)).sub hplus |>.add hminus

theorem norm_contactValue_le {a b s : ℂ}
    (ha : ‖a‖ ≤ (21 / 50 : ℝ)) (hb : ‖b‖ ≤ (21 / 50 : ℝ))
    (hs : ‖s‖ ≤ (21 / 50 : ℝ)) :
    ‖contactValue s (meanEntropy a b)‖ ≤ (147 / 125 : ℝ) := by
  have ht := norm_parameter_lt ha hb hs
  have hc : ‖fixedPointOnDisc (s / meanEntropy a b)‖ ≤ (4 / 5 : ℝ) := by
    exact (show ‖fixedPointOnDisc (s / meanEntropy a b)‖ < (4 / 5 : ℝ) by
      simpa only [Metric.mem_ball, dist_zero_right] using fixedPointOnDisc_mem_ball ht).le
  have hA := norm_atanhExt_le_contact hc
  unfold contactValue
  rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  calc
    _ ≤ 2 * (21 / 50 : ℝ) * (7 / 5 : ℝ) := by gcongr
    _ = (147 / 125 : ℝ) := by norm_num

/-- A uniform rational bound for the Cauchy remainder argument. -/
theorem norm_difference_le {a b : ℂ}
    (ha : ‖a‖ ≤ (21 / 50 : ℝ)) (hb : ‖b‖ ≤ (21 / 50 : ℝ)) :
    ‖difference a b‖ ≤ (3 : ℝ) := by
  have hab : ‖a * atanhExt b‖ ≤ (21 / 100 : ℝ) := by
    rw [norm_mul]
    calc
      _ ≤ (21 / 50 : ℝ) * (1 / 2 : ℝ) :=
        mul_le_mul ha (norm_atanhExt_le_source hb) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hba : ‖b * atanhExt a‖ ≤ (21 / 100 : ℝ) := by
    rw [norm_mul]
    calc
      _ ≤ (21 / 50 : ℝ) * (1 / 2 : ℝ) :=
        mul_le_mul hb (norm_atanhExt_le_source ha) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hp := norm_contactValue_le ha hb (norm_half_add_le ha hb)
  have hm := norm_contactValue_le ha hb (norm_half_sub_le ha hb)
  unfold difference
  calc
    _ ≤ ‖a * atanhExt b + b * atanhExt a - contactValue ((a + b) / 2) (meanEntropy a b)‖ +
        ‖contactValue ((a - b) / 2) (meanEntropy a b)‖ := norm_add_le _ _
    _ ≤ (‖a * atanhExt b‖ + ‖b * atanhExt a‖) +
        ‖contactValue ((a + b) / 2) (meanEntropy a b)‖ +
        ‖contactValue ((a - b) / 2) (meanEntropy a b)‖ := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 3 := by linarith

end GeneralCK.Reflection.SmallBiasComplexDomain

end


