-- Prove2me | Definitions.Def_CK_GeneralCK_FCDecrement
-- name    : CK_GeneralCK_FCDecrement
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:22:15.927384+00:00
-- url     : https://prove2.me/theorems/2da9f872-823a-4dd9-a560-577c0425e237
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCDecrement` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCDecrement` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCDecrement` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCDecrement (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCDecrement.lean)

import Definitions.Def_CK_GeneralCK_FCContact

-- ===== source module GeneralCK.FCDecrement =====
section

/-!
# Lane F-C: the integrated eta decrement

The last obligation needs `eta x − eta y ≤ 2·log (y/x)` on a range reaching well
past `1/500`.  Two pieces:

* `neg_deriv_eta_upper_twentieth` — `−eta' h ≤ 2/h` on `(0, 1/20]`.  The measured
  value of `h·(−eta' h)` at `h = 1/20` is 1.813, and the proof chain yields 1.905,
  so the constant `2` has 5% headroom at the worst point of the range.
* `eta_decrement` — `eta x − eta y ≤ 2·(Real.log y − Real.log x)` for
  `0 < x ≤ y ≤ 1/20`, by monotonicity of `t ↦ eta t + 2·log t`.

The point of pushing the range from `1/500` to `1/20` is that the single-constant
chain over `(0, 1/2]` charges the whole integration at the `t → 1/2` rate (2.906)
when 99.9% of the range runs at 1.45.  Splitting at `1/20` is what recovers the
margin.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCDecrement

open GeneralCK

/-- On `(0, 1/20]` the entropy inverse is at most `1/64`. -/
theorem entropyInverse_small_twentieth {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 20) :
    entropyInverse h ≤ 1 / 64 :=
  FCAnalytic.entropyInverse_le_of_parabola hh (by norm_num) (by norm_num)
    (by norm_num; linarith)

theorem log_63_lower : (59 / 10 : ℝ) * Real.log 2 ≤ Real.log 63 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (59 : ℕ))
    (by norm_num : (2 : ℝ) ^ (59 : ℕ) ≤ 63 ^ (10 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

/-- On `(0, 1/20]` the logit of the entropy inverse is at least `69/20`. -/
theorem logit_large_twentieth {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 20) :
    (4 : ℝ) ≤ Real.log ((1 - entropyInverse h) / entropyInverse h) := by
  have hh1 : h < 1 := by linarith
  have hv : 0 < entropyInverse h := entropyInverse_pos hh hh1.le
  have hvle := entropyInverse_small_twentieth hh hhi
  have hratio : (63 : ℝ) ≤ (1 - entropyInverse h) / entropyInverse h :=
    (le_div_iff₀ hv).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 63) hratio
  linarith [log_63_lower, FCAnalytic.log_two_lb]

/-- `−eta' h ≤ 2/h` on `(0, 1/20]`. -/
theorem neg_deriv_eta_upper_twentieth {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 20) :
    -deriv eta h ≤ 2 / h := by
  have hh1 : h < 1 := by linarith
  set v := entropyInverse h with hvdef
  set l := Real.log ((1 - v) / v) with hldef
  have hv : 0 < v := entropyInverse_pos hh hh1.le
  have hvhalf : v < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hv1 : v < 1 := by linarith
  have hvle : v ≤ 1 / 64 := entropyInverse_small_twentieth hh hhi
  have hl : (4 : ℝ) ≤ l := logit_large_twentieth hh hhi
  have hvc : 0 < 1 - v := by linarith
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL := FCAnalytic.log_two_lb
  have he : H v = h := (entropyInverse_spec hh.le hh1.le).2.2
  have hup := FCAnalytic.entropy_natural_upper hv hv1
  rw [he] at hup
  have hinv : 1 / (1 - v) ≤ 64 / 63 := by
    rw [div_le_div_iff₀ hvc (by norm_num)]
    linarith
  have hkey : h * Real.log 2 ≤ v * (l + 64 / 63) := by
    have hstep : v * (l + 1 / (1 - v)) ≤ v * (l + 64 / 63) := by
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
    have hhb : h ≤ (100 / 69) * (v * (l + 64 / 63)) := by
      rw [show (100 : ℝ) / 69 * (v * (l + 64 / 63))
        = v * (l + 64 / 63) / (69 / 100) by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 69 / 100)]
      nlinarith only [hkey, hL, hh]
    have hpos : (0 : ℝ) ≤ 1 - 2 * v := by linarith
    have hstep1 : (1 - 2 * v) * h ≤ (1 - 2 * v) * ((100 / 69) * (v * (l + 64 / 63))) :=
      mul_le_mul_of_nonneg_left hhb hpos
    have hlpos : (0 : ℝ) < l := by linarith
    have hA : (1 - 2 * v) * ((100 / 69) * (l + 64 / 63))
        ≤ (100 / 69) * (l + 64 / 63) := by
      nlinarith only [hv, hlpos]
    have hC : (100 / 69) * (l + 64 / 63) ≤ (19 / 10) * ((63 / 64) * l) := by
      nlinarith only [hl]
    have hB : (19 / 10) * ((63 / 64) * l) ≤ (19 / 10) * ((1 - v) * l) := by
      nlinarith only [hvle, hlpos]
    have hchain : (1 - 2 * v) * ((100 / 69) * (l + 64 / 63))
        ≤ (19 / 10) * ((1 - v) * l) := by linarith [hA, hC, hB]
    have hmul := mul_le_mul_of_nonneg_left hchain hv.le
    have he1 : (1 - 2 * v) * ((100 / 69) * (v * (l + 64 / 63)))
        = v * ((1 - 2 * v) * ((100 / 69) * (l + 64 / 63))) := by ring
    have he2 : v * ((19 / 10) * ((1 - v) * l)) = (19 / 10) * (v * (1 - v) * l) := by ring
    linarith [hstep1, hmul, he1, he2]
  have h2h : 2 * h ≤ 1 / 10 := by linarith
  nlinarith only [hfrac, h2h, hh]

/-- `eta x − eta y ≤ 2·(log y − log x)` on `(0, 1/20]`. -/
theorem eta_decrement {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 20) :
    eta x - eta y ≤ 2 * (Real.log y - Real.log x) := by
  rcases eq_or_lt_of_le hxy with heq | hlt
  · rw [heq]; simp
  · have hmono : MonotoneOn (fun t => eta t + 2 * Real.log t) (Set.Icc x y) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x y)
        (f' := fun t => deriv eta t + 2 * t⁻¹)
      · intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
        have ht1 : t < 1 := by have := ht.2; linarith
        have hda := hasDerivAt_eta ht0 ht1
        have h1 : HasDerivAt eta (deriv eta t) t := by rwa [hda.deriv]
        have h2 : HasDerivAt (fun u : ℝ => 2 * Real.log u) (2 * t⁻¹) t :=
          (Real.hasDerivAt_log ht0.ne').const_mul (2 : ℝ)
        exact (h1.add h2).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht0 : 0 < t := lt_trans hx ht.1
        have ht1 : t < 1 := by have := ht.2; linarith
        have hda := hasDerivAt_eta ht0 ht1
        have h1 : HasDerivAt eta (deriv eta t) t := by rwa [hda.deriv]
        have h2 : HasDerivAt (fun u : ℝ => 2 * Real.log u) (2 * t⁻¹) t :=
          (Real.hasDerivAt_log ht0.ne').const_mul (2 : ℝ)
        exact (h1.add h2).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht0 : 0 < t := lt_trans hx ht.1
        have htle : t ≤ 1 / 20 := by have := ht.2; linarith
        have hb := neg_deriv_eta_upper_twentieth ht0 htle
        have hinv : (2 : ℝ) * t⁻¹ = 2 / t := by field_simp
        linarith [hb, hinv]
    have hres := hmono (Set.left_mem_Icc.2 hxy) (Set.right_mem_Icc.2 hxy) hxy
    simp only at hres
    linarith

#check @neg_deriv_eta_upper_twentieth
#check @eta_decrement
#print axioms neg_deriv_eta_upper_twentieth
#print axioms eta_decrement

end GeneralCK.FCDecrement

end


