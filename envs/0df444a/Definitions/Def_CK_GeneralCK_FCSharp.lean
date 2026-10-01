-- Prove2me | Definitions.Def_CK_GeneralCK_FCSharp
-- name    : CK_GeneralCK_FCSharp
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:52:41.071344+00:00
-- url     : https://prove2.me/theorems/89b92a3e-ab8a-491f-b936-9850fdb56d4d
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCSharp` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCSharp` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCSharp` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCSharp (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCSharp.lean)

import Definitions.Def_CK_GeneralCK_FCEtaPoints

-- ===== source module GeneralCK.FCSharp =====
section

/-!
# Lane F-C: sharpened constants for the capped assembly

Every constant here was evaluated at the WORST point of its own range before
being written down, not at its asymptote.

* `entropyInverse_le_of_J`      — `entropyInverse h ≤ p` from `h ≤ p · J p`
                                   (sharper than the parabola route for moderate `p`);
* `neg_deriv_eta_upper_sharp`   — `−eta' h ≤ (17/10)/h` on `(0, 1/500]`
                                   (chain yields 1.6666; 2% headroom);
* `neg_deriv_eta_upper_tenth`   — `−eta' h ≤ (21/10)/h` on `(0, 1/10]`
                                   (chain yields 2.032; 3.2% headroom);
* `eta_decrement_tenth`         — the integrated form on `(0, 1/10]`;
* `eta_tenth_upper_sharp`       — `eta (1/10) ≤ 63/10` (true 6.134);
* `eta_half_lower_sharp`        — `21/10 ≤ eta (1/2)` (true 2.352);
* `eta_gap_sharp`               — gap `≤ 21/5`, replacing the `49/10` that left
                                   only 0.3% at the worst admissible `zm`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCSharp

open GeneralCK

/-- `H p ≥ p · J p` transfers to an upper bound on the entropy inverse. -/
theorem entropyInverse_le_of_J {h p : ℝ} (hh : 0 < h) (hp : 0 < p) (hp2 : p < 1 / 2)
    (hle : h ≤ p * J p) : entropyInverse h ≤ p := by
  have hHp : p * J p ≤ H p := FCContact.H_ge_mul_J hp (by linarith)
  have hhc : h ≤ H p := le_trans hle hHp
  have hmono := entropyInverse_mono hh.le (H_le_one p) hhc
  rwa [entropyInverse_H_lower hp.le hp2.le] at hmono

theorem log_49_lower : (28 / 5 : ℝ) * Real.log 2 ≤ Real.log 49 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (28 : ℕ))
    (by norm_num : (2 : ℝ) ^ (28 : ℕ) ≤ 49 ^ (5 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

/-- On `(0, 1/10]` the entropy inverse is at most `1/50`. -/
theorem entropyInverse_small_tenth {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 10) :
    entropyInverse h ≤ 1 / 50 := by
  apply entropyInverse_le_of_J hh (by norm_num) (by norm_num)
  have hJ : (5 : ℝ) ≤ J (1 / 50) := by
    unfold J
    rw [show ((1 : ℝ) - 1 / 50) / (1 / 50) = 49 by norm_num]
    rw [le_div_iff₀ log_two_pos]
    linarith [log_49_lower, FCAnalytic.log_two_lb]
  nlinarith only [hJ, hhi]

theorem logit_large_tenth {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 10) :
    (193 / 50 : ℝ) ≤ Real.log ((1 - entropyInverse h) / entropyInverse h) := by
  have hh1 : h < 1 := by linarith
  have hv : 0 < entropyInverse h := entropyInverse_pos hh hh1.le
  have hvle := entropyInverse_small_tenth hh hhi
  have hratio : (49 : ℝ) ≤ (1 - entropyInverse h) / entropyInverse h :=
    (le_div_iff₀ hv).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 49) hratio
  linarith [log_49_lower, FCAnalytic.log_two_lb]

/-- `−eta' h ≤ (21/10)/h` on `(0, 1/10]`. -/
theorem neg_deriv_eta_upper_tenth {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 10) :
    -deriv eta h ≤ (21 / 10) / h := by
  have hh1 : h < 1 := by linarith
  set v := entropyInverse h with hvdef
  set l := Real.log ((1 - v) / v) with hldef
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hv1 : v < 1 := by linarith
  have hvle : v ≤ 1 / 50 := entropyInverse_small_tenth hh hhi
  have hl : (193 / 50 : ℝ) ≤ l := logit_large_tenth hh hhi
  have hvc : 0 < 1 - v := by linarith
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL := FCAnalytic.log_two_lb
  have he : H v = h := (entropyInverse_spec hh.le hh1.le).2.2
  have hup := FCAnalytic.entropy_natural_upper hv hv1
  rw [he] at hup
  have hinv : 1 / (1 - v) ≤ 50 / 49 := by
    rw [div_le_div_iff₀ hvc (by norm_num)]
    linarith
  have hkey : h * Real.log 2 ≤ v * (l + 50 / 49) := by
    have hstep : v * (l + 1 / (1 - v)) ≤ v * (l + 50 / 49) := by
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
  have hfrac : (1 - 2 * v) / (v * (1 - v) * l) * h ≤ 19 / 10 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have hhb : h ≤ (100 / 69) * (v * (l + 50 / 49)) := by
      rw [show (100 : ℝ) / 69 * (v * (l + 50 / 49))
        = v * (l + 50 / 49) / (69 / 100) by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 69 / 100)]
      nlinarith only [hkey, hL, hh]
    have hpos : (0 : ℝ) ≤ 1 - 2 * v := by linarith
    have hstep1 : (1 - 2 * v) * h ≤ (1 - 2 * v) * ((100 / 69) * (v * (l + 50 / 49))) :=
      mul_le_mul_of_nonneg_left hhb hpos
    have hlpos : (0 : ℝ) < l := by linarith
    have hA : (1 - 2 * v) * ((100 / 69) * (l + 50 / 49))
        ≤ (100 / 69) * (l + 50 / 49) := by
      nlinarith only [hv, hlpos]
    have hC : (100 / 69) * (l + 50 / 49) ≤ (19 / 10) * ((49 / 50) * l) := by
      nlinarith only [hl]
    have hB : (19 / 10) * ((49 / 50) * l) ≤ (19 / 10) * ((1 - v) * l) := by
      nlinarith only [hvle, hlpos]
    have hchain : (1 - 2 * v) * ((100 / 69) * (l + 50 / 49))
        ≤ (19 / 10) * ((1 - v) * l) := by linarith [hA, hC, hB]
    have hmul := mul_le_mul_of_nonneg_left hchain hv.le
    have he1 : (1 - 2 * v) * ((100 / 69) * (v * (l + 50 / 49)))
        = v * ((1 - 2 * v) * ((100 / 69) * (l + 50 / 49))) := by ring
    have he2 : v * ((19 / 10) * ((1 - v) * l)) = (19 / 10) * (v * (1 - v) * l) := by ring
    linarith [hstep1, hmul, he1, he2]
  have h2h : 2 * h ≤ 1 / 5 := by linarith
  nlinarith only [hfrac, h2h, hh]

/-- `eta x − eta y ≤ (21/10)·(log y − log x)` on `(0, 1/10]`. -/
theorem eta_decrement_tenth {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 10) :
    eta x - eta y ≤ (21 / 10) * (Real.log y - Real.log x) := by
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]; simp
  · have hmono : MonotoneOn (fun t => eta t + (21 / 10) * Real.log t) (Set.Icc x y) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y)
        (f' := fun t => deriv eta t + (21 / 10) * t⁻¹)
      · intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
        have ht1 : t < 1 := by have := ht.2; linarith
        have hda := hasDerivAt_eta ht0 ht1
        have h1 : HasDerivAt eta (deriv eta t) t := by rwa [hda.deriv]
        have h2 : HasDerivAt (fun u : ℝ => (21 / 10) * Real.log u) ((21 / 10) * t⁻¹) t :=
          (Real.hasDerivAt_log ht0.ne').const_mul (21 / 10 : ℝ)
        exact (h1.add h2).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht0 : 0 < t := lt_trans hx ht.1
        have ht1 : t < 1 := by have := ht.2; linarith
        have hda := hasDerivAt_eta ht0 ht1
        have h1 : HasDerivAt eta (deriv eta t) t := by rwa [hda.deriv]
        have h2 : HasDerivAt (fun u : ℝ => (21 / 10) * Real.log u) ((21 / 10) * t⁻¹) t :=
          (Real.hasDerivAt_log ht0.ne').const_mul (21 / 10 : ℝ)
        exact (h1.add h2).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht0 : 0 < t := lt_trans hx ht.1
        have htle : t ≤ 1 / 10 := by have := ht.2; linarith
        have hb := neg_deriv_eta_upper_tenth ht0 htle
        have hinv : (21 / 10 : ℝ) * t⁻¹ = (21 / 10) / t := by field_simp
        linarith [hb, hinv]
    have hres := hmono (Set.left_mem_Icc.2 hxy) (Set.right_mem_Icc.2 hxy) hxy
    simp only at hres
    linarith

theorem log_78_upper : Real.log 78 ≤ (63 / 10 : ℝ) * Real.log 2 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 78 ^ (10 : ℕ))
    (by norm_num : (78 : ℝ) ^ (10 : ℕ) ≤ 2 ^ (63 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem log_77_upper : Real.log 77 ≤ (63 / 10 : ℝ) * Real.log 2 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 77 ^ (10 : ℕ))
    (by norm_num : (77 : ℝ) ^ (10 : ℕ) ≤ 2 ^ (63 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem H_seventyeighth_upper : H (1 / 78 : ℝ) ≤ 1 / 10 := by
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL := FCAnalytic.log_two_lb
  have hLu := FCAnalytic.log_two_ub
  have htail : Real.log ((78 : ℝ) / 77) ≤ 1 / 77 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 78 / 77)
    linarith
  have hHid : H (1 / 78 : ℝ) * Real.log 2
      = (1 / 78) * Real.log 78 + (77 / 78) * Real.log (78 / 77) := by
    unfold H Real.binEntropy
    rw [div_mul_cancel₀ _ hLpos.ne']
    rw [show (1 : ℝ) - 1 / 78 = 77 / 78 by norm_num]
    rw [show ((1 : ℝ) / 78)⁻¹ = 78 by norm_num,
      show ((77 : ℝ) / 78)⁻¹ = 78 / 77 by norm_num]
  have hbound : H (1 / 78 : ℝ) * Real.log 2 ≤ (1 / 10 : ℝ) * Real.log 2 := by
    rw [hHid]
    nlinarith only [log_78_upper, htail, hL, hLu, hLpos]
  exact le_of_mul_le_mul_right hbound hLpos

theorem eta_tenth_upper_sharp : eta (1 / 10 : ℝ) ≤ 63 / 10 := by
  have hv : 0 < entropyInverse (1 / 10 : ℝ) :=
    entropyInverse_pos (by norm_num) (by norm_num)
  have hvhalf : entropyInverse (1 / 10 : ℝ) < 1 / 2 :=
    entropyInverse_lt_half (by norm_num) (by norm_num)
  have hlow : (1 / 78 : ℝ) ≤ entropyInverse (1 / 10) := by
    by_contra hcon
    push_neg at hcon
    have hHv : H (entropyInverse (1 / 10 : ℝ)) = 1 / 10 :=
      (entropyInverse_spec (by norm_num) (by norm_num)).2.2
    have hmono := H_strictMonoOn
      (show entropyInverse (1 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨hv.le, hvhalf.le⟩)
      (show (1 / 78 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) by constructor <;> norm_num) hcon
    rw [hHv] at hmono
    linarith [H_seventyeighth_upper]
  have hJ : J (entropyInverse (1 / 10 : ℝ)) ≤ J (1 / 78 : ℝ) :=
    J_antitone (by norm_num) hvhalf.le hlow
  have hJval : J (1 / 78 : ℝ) ≤ 63 / 10 := by
    unfold J
    rw [show ((1 : ℝ) - 1 / 78) / (1 / 78) = 77 by norm_num]
    rw [div_le_iff₀ log_two_pos]
    linarith [log_77_upper]
  have hJnn : 0 ≤ J (entropyInverse (1 / 10 : ℝ)) := J_nonneg hv hvhalf.le
  rw [eta_eq_profile (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num : (1 / 10 : ℝ) ≤ 1)]
  nlinarith only [hJ, hJval, hJnn, hv]

theorem log_7_lower : (14 / 5 : ℝ) * Real.log 2 ≤ Real.log 7 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (14 : ℕ))
    (by norm_num : (2 : ℝ) ^ (14 : ℕ) ≤ 7 ^ (5 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem H_eighth_lower : (1 / 2 : ℝ) ≤ H (1 / 8) := by
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL := FCAnalytic.log_two_lb
  have hLu := FCAnalytic.log_two_ub
  have htail : (1 : ℝ) / 8 ≤ Real.log (8 / 7) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7 / 8)
    have hinv : Real.log ((7 : ℝ) / 8) = -Real.log ((8 : ℝ) / 7) := by
      rw [show (7 : ℝ) / 8 = ((8 : ℝ) / 7)⁻¹ by norm_num, Real.log_inv]
    rw [hinv] at h
    linarith
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hHid : H (1 / 8 : ℝ) * Real.log 2
      = (1 / 8) * Real.log 8 + (7 / 8) * Real.log (8 / 7) := by
    unfold H Real.binEntropy
    rw [div_mul_cancel₀ _ hLpos.ne']
    rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num]
    rw [show ((1 : ℝ) / 8)⁻¹ = 8 by norm_num,
      show ((7 : ℝ) / 8)⁻¹ = 8 / 7 by norm_num]
  have hbound : (1 / 2 : ℝ) * Real.log 2 ≤ H (1 / 8 : ℝ) * Real.log 2 := by
    rw [hHid, hlog8]
    nlinarith only [htail, hL, hLu, hLpos]
  exact le_of_mul_le_mul_right hbound hLpos

theorem eta_half_lower_sharp : (21 / 10 : ℝ) ≤ eta (1 / 2) := by
  have hv : 0 < entropyInverse (1 / 2 : ℝ) :=
    entropyInverse_pos (by norm_num) (by norm_num)
  have hvhalf : entropyInverse (1 / 2 : ℝ) < 1 / 2 :=
    entropyInverse_lt_half (by norm_num) (by norm_num)
  have hup : entropyInverse (1 / 2 : ℝ) ≤ 1 / 8 := by
    have hmono := entropyInverse_mono (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (H_le_one (1 / 8 : ℝ)) (le_trans (by norm_num) H_eighth_lower)
    rwa [entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 : ℝ) / 8 ≤ 1 / 2)] at hmono
  have hJ : J (1 / 8 : ℝ) ≤ J (entropyInverse (1 / 2 : ℝ)) :=
    J_antitone hv (by norm_num) hup
  have hJval : (14 / 5 : ℝ) ≤ J (1 / 8 : ℝ) := by
    unfold J
    rw [show ((1 : ℝ) - 1 / 8) / (1 / 8) = 7 by norm_num]
    rw [le_div_iff₀ log_two_pos]
    linarith [log_7_lower]
  rw [eta_eq_profile (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  nlinarith only [hJ, hJval, hup, hv]

/-- `eta (1/10) − eta (1/2) ≤ 21/5`.  True value 3.782. -/
theorem eta_gap_sharp : eta (1 / 10 : ℝ) - eta (1 / 2) ≤ 21 / 5 := by
  linarith [eta_tenth_upper_sharp, eta_half_lower_sharp]

#check @neg_deriv_eta_upper_tenth
#check @eta_decrement_tenth
#check @eta_tenth_upper_sharp
#check @eta_half_lower_sharp
#check @eta_gap_sharp
#print axioms entropyInverse_le_of_J
#print axioms neg_deriv_eta_upper_tenth
#print axioms eta_decrement_tenth
#print axioms eta_tenth_upper_sharp
#print axioms eta_half_lower_sharp
#print axioms eta_gap_sharp

end GeneralCK.FCSharp

end


