-- Prove2me | Definitions.Def_CK_GeneralCK_FCConst
-- name    : CK_GeneralCK_FCConst
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:45:40.690254+00:00
-- url     : https://prove2.me/theorems/ca48d8b5-9bf5-4beb-8ab8-e01b1c5ad29c
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCConst` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCConst` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCConst` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCConst (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCConst.lean)

import Definitions.Def_CK_GeneralCK_FCSharp

-- ===== source module GeneralCK.FCConst =====
section

/-!
# Lane F-C: the three constants the capped assembly still needs

Priced at the worst admissible point (`zm = 1e-4`) before being written down:

* `H_ge_mul_J_sharp`      — `q·J q + q/log 2 ≤ H q`.  The discarded
  `log2 (1/(1-q))` term is worth `2.885·zm` in the assembly, which is the
  difference between failing by 0.6% and holding by 6.7%.
* `neg_deriv_eta_sharp`   — `−eta' h ≤ (17/10)/h` on `(0, 1/500]`; the chain
  yields 1.6685, so 2% of headroom.
* `entropyInverse_ge_half_a` — under the capped hypothesis, `a/2 ≤ entropyInverse E`,
  which is what converts `eta E` into `J a + 1.0002` and hence into `H a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCConst

open GeneralCK

/-- `H q ≥ q·J q + q / log 2`: the sharp form of `H_ge_mul_J`. -/
theorem H_ge_mul_J_sharp {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    q * J q + q / Real.log 2 ≤ H q := by
  have hqc : (0 : ℝ) < 1 - q := by linarith
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hid : H q * Real.log 2 - (q * J q) * Real.log 2 = -Real.log (1 - q) := by
    unfold H Real.binEntropy J
    rw [Real.log_div hqc.ne' hq.ne']
    simp only [Real.log_inv]
    field_simp
    ring
  have hlog : q ≤ -Real.log (1 - q) := by
    have h := Real.log_le_sub_one_of_pos hqc
    linarith
  have hdiv : (q / Real.log 2) * Real.log 2 = q := by field_simp
  nlinarith only [hid, hlog, hdiv, hLpos]

/-- `−eta' h ≤ (17/10)/h` on `(0, 1/500]`.  Chain value 1.6685. -/
theorem neg_deriv_eta_sharp {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 500) :
    -deriv eta h ≤ (17 / 10) / h := by
  have hh1 : h < 1 := by linarith
  set v := entropyInverse h with hvdef
  set l := Real.log ((1 - v) / v) with hldef
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hv1 : v < 1 := by linarith
  have hvle : v ≤ 1 / 1000 := FCAnalytic.entropyInverse_small hh hhi
  have hl : (68 / 10 : ℝ) ≤ l := FCAnalytic.logit_large hh hhi
  have hvc : 0 < 1 - v := by linarith
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL := FCAnalytic.log_two_lb
  have he : H v = h := (entropyInverse_spec hh.le hh1.le).2.2
  have hup := FCAnalytic.entropy_natural_upper hv hv1
  rw [he] at hup
  have hinv : 1 / (1 - v) ≤ 101 / 100 := by
    rw [div_le_div_iff₀ hvc (by norm_num)]
    linarith
  have hkey : h * Real.log 2 ≤ v * (l + 101 / 100) := by
    have hstep : v * (l + 1 / (1 - v)) ≤ v * (l + 101 / 100) := by
      nlinarith only [hinv, hv]
    linarith
  have hlne : Real.log ((1 - v) / v) ≠ 0 := by
    simp only [← hldef]; intro hz; rw [hz] at hl; norm_num at hl
  have hd : deriv eta h = -2 - (1 - 2 * v) / (v * (1 - v) * l) := by
    rw [deriv_eta hh hh1]
    change -2 - (1 - 2 * v) / (Real.log 2 * v * (1 - v) * J v) = _
    unfold J
    field_simp [hlne]
    ring
  have hden : 0 < v * (1 - v) * l := by
    have hlpos : (0 : ℝ) < l := by linarith
    positivity
  rw [hd, le_div_iff₀ hh]
  have hfrac : (1 - 2 * v) / (v * (1 - v) * l) * h ≤ 167 / 100 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have hhb : h ≤ (100 / 69) * (v * (l + 101 / 100)) := by
      rw [show (100 : ℝ) / 69 * (v * (l + 101 / 100))
        = v * (l + 101 / 100) / (69 / 100) by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 69 / 100)]
      nlinarith only [hkey, hL, hh]
    have hpos : (0 : ℝ) ≤ 1 - 2 * v := by linarith
    have hstep1 : (1 - 2 * v) * h ≤ (1 - 2 * v) * ((100 / 69) * (v * (l + 101 / 100))) :=
      mul_le_mul_of_nonneg_left hhb hpos
    have hlpos : (0 : ℝ) < l := by linarith
    have hA : (1 - 2 * v) * ((100 / 69) * (l + 101 / 100))
        ≤ (100 / 69) * (l + 101 / 100) := by
      nlinarith only [hv, hlpos]
    have hC : (100 / 69) * (l + 101 / 100) ≤ (167 / 100) * ((999 / 1000) * l) := by
      nlinarith only [hl]
    have hB : (167 / 100) * ((999 / 1000) * l) ≤ (167 / 100) * ((1 - v) * l) := by
      nlinarith only [hvle, hlpos]
    have hchain : (1 - 2 * v) * ((100 / 69) * (l + 101 / 100))
        ≤ (167 / 100) * ((1 - v) * l) := by linarith [hA, hC, hB]
    have hmul := mul_le_mul_of_nonneg_left hchain hv.le
    have he1 : (1 - 2 * v) * ((100 / 69) * (v * (l + 101 / 100)))
        = v * ((1 - 2 * v) * ((100 / 69) * (l + 101 / 100))) := by ring
    have he2 : v * ((167 / 100) * ((1 - v) * l)) = (167 / 100) * (v * (1 - v) * l) := by ring
    linarith [hstep1, hmul, he1, he2]
  have h2h : 2 * h ≤ 1 / 250 := by linarith
  nlinarith only [hfrac, h2h, hh]

/-- Under the capped hypothesis the entropy inverse of `E` is at least `a/2`.
This is what turns `eta E` into `J a + O(1)` and hence into `H a`. -/
theorem entropyInverse_ge_half_a {a E : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 10000)
    (hE : 0 < E) (hE1 : E < 1) (hJa : (13 : ℝ) ≤ J a) (hcap : (9998 / 10000) * H a ≤ E) :
    a / 2 ≤ entropyInverse E := by
  have hpos : (0 : ℝ) < 1 - a / 2 := by linarith
  have haq : (0 : ℝ) < a / 2 := by linarith
  have haq2 : a / 2 < 1 / 2 := by linarith
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL := FCAnalytic.log_two_lb
  -- J (a/2) ≤ J a + 101/100
  have hJhalf : J (a / 2) ≤ J a + 101 / 100 := by
    have hratio : ((1 : ℝ) - a / 2) / (a / 2) ≤ ((1 - a) / a) * (201 / 100) := by
      rw [div_le_iff₀ haq]
      have hd : ((1 : ℝ) - a) / a * (201 / 100) * (a / 2) = (1 - a) * (201 / 200) := by
        field_simp; ring
      rw [hd]
      nlinarith only [ha, ha1]
    have hlog := Real.log_le_log (div_pos hpos haq) hratio
    have hne : ((1 : ℝ) - a) / a ≠ 0 :=
      ne_of_gt (div_pos (by linarith : (0 : ℝ) < 1 - a) ha)
    rw [Real.log_mul hne (by norm_num : (201 : ℝ) / 100 ≠ 0)] at hlog
    have h201 : Real.log ((201 : ℝ) / 100) ≤ Real.log 2 + 1 / 200 := by
      have hsplit : ((201 : ℝ) / 100) = 2 * (201 / 200) := by norm_num
      rw [hsplit, Real.log_mul (by norm_num) (by norm_num)]
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 201 / 200)
      linarith
    unfold J
    rw [div_le_iff₀ hLpos, add_mul, div_mul_cancel₀ _ hLpos.ne']
    nlinarith only [hlog, h201, hL, hLpos]
  -- H (a/2) ≤ (a/2) J (a/2) + (3/2) a
  have hHhalf : H (a / 2) ≤ (a / 2) * J (a / 2) + (3 / 2) * a := by
    have hid : H (a / 2) * Real.log 2 - ((a / 2) * J (a / 2)) * Real.log 2
        = -Real.log (1 - a / 2) := by
      unfold H Real.binEntropy J
      rw [Real.log_div (by linarith : (1 : ℝ) - a / 2 ≠ 0) (by linarith : a / 2 ≠ 0)]
      simp only [Real.log_inv]
      field_simp
      ring
    have hlog : -Real.log (1 - a / 2) ≤ a := by
      have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
      rw [Real.log_inv] at hl
      have hb : ((1 : ℝ) - a / 2)⁻¹ ≤ 1 + a := by
        rw [show ((1 : ℝ) - a / 2)⁻¹ = 1 / (1 - a / 2) by rw [one_div],
          div_le_iff₀ hpos]
        nlinarith only [ha, ha1]
      linarith
    have hkey : (H (a / 2) - (a / 2) * J (a / 2)) * Real.log 2 ≤ a := by
      nlinarith only [hid, hlog]
    have hgoal : H (a / 2) - (a / 2) * J (a / 2) ≤ (3 / 2) * a := by
      by_contra hc
      push_neg at hc
      nlinarith only [hkey, hL, hLpos, ha, hc]
    linarith
  have hHa : a * J a ≤ H a := FCContact.H_ge_mul_J ha (by linarith)
  have hle : H (a / 2) ≤ E := by
    have hstep : (a / 2) * J (a / 2) + (3 / 2) * a ≤ (9998 / 10000) * (a * J a) := by
      nlinarith only [hJhalf, hJa, ha]
    have hmul : (9998 / 10000 : ℝ) * (a * J a) ≤ (9998 / 10000) * H a :=
      mul_le_mul_of_nonneg_left hHa (by norm_num)
    linarith [hHhalf, hstep, hmul, hcap]
  by_contra hcon
  push_neg at hcon
  have hv : 0 < entropyInverse E := entropyInverse_pos hE hE1.le
  have hvhalf : entropyInverse E < 1 / 2 := entropyInverse_lt_half hE.le hE1
  have hHv : H (entropyInverse E) = E := (entropyInverse_spec hE.le hE1.le).2.2
  have hmono := H_strictMonoOn
    (show entropyInverse E ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨hv.le, hvhalf.le⟩)
    (show (a / 2) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨haq.le, haq2.le⟩) hcon
  rw [hHv] at hmono
  linarith

#check @H_ge_mul_J_sharp
#check @neg_deriv_eta_sharp
#check @entropyInverse_ge_half_a
#print axioms H_ge_mul_J_sharp
#print axioms neg_deriv_eta_sharp
#print axioms entropyInverse_ge_half_a

end GeneralCK.FCConst

end


