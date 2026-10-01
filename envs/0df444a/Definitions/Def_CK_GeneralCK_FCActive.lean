-- Prove2me | Definitions.Def_CK_GeneralCK_FCActive
-- name    : CK_GeneralCK_FCActive
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T19:55:34.000471+00:00
-- url     : https://prove2.me/theorems/3d8f77b5-a6cd-4834-9c38-d124f170d529
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCActive` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCActive` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCActive` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCActive (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCActive.lean)

import Definitions.Def_CK_GeneralCK_FCAnalytic
import Definitions.Def_CK_GeneralCK_FCAnalytic2

-- ===== source module GeneralCK.FCActive =====
section

/-!
# Lane F-C: what the certificate hypothesis `psi ≤ phi` buys

On the opposite-corner domain the hypothesis `psi m E ≤ phi m E` is not free
information: it forces the radial displacement `zm = 1 - a - b` to dominate the
mean entropy `E`, and hence forces a linear-in-`zm` lower bound on `F zm E`.

`active_forces_F_lower` is that statement.  Chain:
  psi ≤ phi                    ⟹ F zm E ≤ eta E − eta (E + 1 − H m)
  convexity of eta             ⟹ eta E − eta (E + δ) ≤ (−eta' E)·δ
  neg_deriv_eta_upper          ⟹ (−eta' E) ≤ 2/E
  one_sub_H_near_half          ⟹ δ = 1 − H m ≤ (3/4)·zm²
  homogeneity                  ⟹ F X 1 ≤ (3/2)X²,  X = zm/E
  antitoneOn_F_div_sq + anchor ⟹ X > 2
  F_slope_mono + anchor        ⟹ F zm E ≥ (16/5)·zm
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCActive

open GeneralCK

/-- `-eta' h ≤ 2/h` on `(0, 1/500]`.  Measured value of `h·(-eta' h)` ≈ 1.66. -/
theorem neg_deriv_eta_upper {h : ℝ} (hh : 0 < h) (hhi : h ≤ 1 / 500) :
    -deriv eta h ≤ 2 / h := by
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
    have : (0 : ℝ) < l := by linarith
    positivity
  rw [hd, le_div_iff₀ hh]
  -- goal : -(-2 - (1 - 2v)/(v(1-v)l)) * h ≤ 2
  have hfrac : (1 - 2 * v) / (v * (1 - v) * l) * h ≤ 17 / 10 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    -- (1-2v) * h ≤ (166/100) * (v (1-v) l)
    have hhb : h ≤ (100 / 69) * (v * (l + 101 / 100)) := by
      rw [show (100 : ℝ) / 69 * (v * (l + 101 / 100))
        = v * (l + 101 / 100) / (69 / 100) by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 69 / 100)]
      nlinarith only [hkey, hL, hh]
    have hpos : (0 : ℝ) ≤ 1 - 2 * v := by linarith
    have hstep1 : (1 - 2 * v) * h ≤ (1 - 2 * v) * ((100 / 69) * (v * (l + 101 / 100))) :=
      mul_le_mul_of_nonneg_left hhb hpos
    have hstep2 : (1 - 2 * v) * ((100 / 69) * (v * (l + 101 / 100)))
        ≤ 17 / 10 * (v * (1 - v) * l) := by
      have hlpos : (0 : ℝ) < l := by linarith
      have hA : (1 - 2 * v) * ((100 / 69) * (l + 101 / 100))
          ≤ (100 / 69) * (l + 101 / 100) := by
        nlinarith only [hv, hlpos]
      have hC : (100 / 69) * (l + 101 / 100) ≤ (17 / 10) * ((999 / 1000) * l) := by
        nlinarith only [hl]
      have hB : (17 / 10) * ((999 / 1000) * l) ≤ (17 / 10) * ((1 - v) * l) := by
        nlinarith only [hvle, hlpos]
      have hchain : (1 - 2 * v) * ((100 / 69) * (l + 101 / 100))
          ≤ (17 / 10) * ((1 - v) * l) := by linarith [hA, hC, hB]
      have hmul := mul_le_mul_of_nonneg_left hchain hv.le
      nlinarith only [hmul]
    linarith [hstep1, hstep2]
  have h2h : 2 * h ≤ 4 / 1000 := by linarith
  nlinarith only [hfrac, h2h, hh]

/-- The certificate hypothesis forces `2E < zm`.  Exposed separately because the
capped sub-case needs it to know that the psi tangent at `2E` is in range. -/
theorem active_forces_two_E_lt {a b E : ℝ}
    (ha : 0 < a) (hb : 1 / 2 < b) (hsum : a + b < 1)
    (hcut : a + (1 - b) < 1 / 10000)
    (hE : 0 < E) (hEsmall : E ≤ 1 / 500)
    (hactive : psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E) :
    2 * E < 1 - a - b := by
  have hzmpos : 0 < 1 - a - b := by linarith
  by_contra hcon
  push_neg at hcon
  -- if zm ≤ 2E then F zm E ≤ F (2E) E = 2E·F 2 1 ... contradicts the derived bound
  have hXle : (1 - a - b) / E ≤ 2 := by
    rw [div_le_iff₀ hE]; linarith
  have hXpos : 0 < (1 - a - b) / E := div_pos hzmpos hE
  have hFX : F (1 - a - b) E = E * F ((1 - a - b) / E) 1 := FCAnalytic2.F_scale_one hE
  -- the bound F zm E ≥ (16/5) zm rules out X ≤ 2 only together with the
  -- quadratic bound, which is what `active_forces_F_lower` already used; we
  -- re-derive the strict inequality directly from the same quadratic step.
  have hquad : F ((1 - a - b) / E) 1 ≤ (3 / 2) * ((1 - a - b) / E) ^ 2 := by
    have hzmsmall : 1 - a - b ≤ 1 / 1000 := by linarith
    have hm : (a + b) / 2 = (1 - (1 - a - b)) / 2 := by ring
    have hrad : |1 - 2 * ((a + b) / 2)| = 1 - a - b := by
      rw [hm, show (1 : ℝ) - 2 * ((1 - (1 - a - b)) / 2) = 1 - a - b by ring]
      exact abs_of_pos hzmpos
    have hδ : 0 ≤ 1 - H ((a + b) / 2) := by linarith [H_le_one ((a + b) / 2)]
    have hstep1 : F (1 - a - b) E ≤ eta E - eta (E + 1 - H ((a + b) / 2)) := by
      have hp : phi ((a + b) / 2) E = eta E - F (1 - a - b) E := by
        unfold phi; rw [hrad]
      have hq : psi ((a + b) / 2) E = eta (E + 1 - H ((a + b) / 2)) := rfl
      rw [hp, hq] at hactive
      linarith
    have hHm : 1 - H ((a + b) / 2) ≤ (3 / 4) * (1 - a - b) ^ 2 := by
      rw [hm]
      exact FCAnalytic2.one_sub_H_near_half hzmpos.le hzmsmall
    have hE1 : E < 1 := by linarith
    have hEd1 : E + (1 - H ((a + b) / 2)) ≤ 1 := by
      have hz : (3 : ℝ) / 4 * (1 - a - b) ^ 2 ≤ 1 / 1000000 := by
        nlinarith only [hzmsmall, hzmpos]
      linarith [hHm, hEsmall]
    have hconv : eta E - eta (E + (1 - H ((a + b) / 2)))
        ≤ (2 / E) * (1 - H ((a + b) / 2)) := by
      rcases eq_or_lt_of_le hδ with hz | hdpos
      · rw [← hz]
        simp
      · have hDA := hasDerivAt_eta hE hE1
        have hdd : deriv eta E = -2 - (1 - 2 * entropyInverse E) /
            (Real.log 2 * entropyInverse E * (1 - entropyInverse E) * J (entropyInverse E)) :=
          deriv_eta hE hE1
        have hslope := Scalar.eta_convexOn_Ioc.le_slope_of_hasDerivAt
          (show E ∈ Set.Ioc (0 : ℝ) 1 from ⟨hE, hE1.le⟩)
          (show E + (1 - H ((a + b) / 2)) ∈ Set.Ioc (0 : ℝ) 1 from ⟨by linarith, hEd1⟩)
          (by linarith) hDA
        rw [slope_def_field, ← hdd] at hslope
        have hdiv := (le_div_iff₀
          (show (0 : ℝ) < E + (1 - H ((a + b) / 2)) - E by linarith)).mp hslope
        have hneg := neg_deriv_eta_upper hE hEsmall
        nlinarith only [hdiv, hneg, hδ]
    have hrw : E + (1 - H ((a + b) / 2)) = E + 1 - H ((a + b) / 2) := by ring
    rw [hrw] at hconv
    have hmono : (2 / E) * (1 - H ((a + b) / 2))
        ≤ (2 / E) * ((3 / 4) * (1 - a - b) ^ 2) := by
      have hEinv : (0 : ℝ) ≤ 2 / E := by positivity
      nlinarith only [hHm, hEinv]
    have hchain : E * F ((1 - a - b) / E) 1 ≤ (2 / E) * ((3 / 4) * (1 - a - b) ^ 2) := by
      rw [← hFX]; linarith [hstep1, hconv, hmono]
    have hrw2 : (2 / E) * ((3 / 4) * (1 - a - b) ^ 2)
        = E * ((3 / 2) * ((1 - a - b) / E) ^ 2) := by field_simp; ring
    rw [hrw2] at hchain
    exact le_of_mul_le_mul_left hchain hE
  have hanti := antitoneOn_F_div_sq (h := 1) (by norm_num)
    (show (1 - a - b) / E ∈ Set.Ioi (0 : ℝ) from hXpos)
    (show (2 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num) hXle
  have hF2 := FCAnalytic2.F_two_one_lower
  have hXsq : (0 : ℝ) < ((1 - a - b) / E) ^ 2 := by positivity
  have hle : F ((1 - a - b) / E) 1 / ((1 - a - b) / E) ^ 2 ≤ (3 / 2 : ℝ) := by
    rw [div_le_iff₀ hXsq]; linarith [hquad]
  have hge : (8 / 5 : ℝ) ≤ F 2 1 / 2 ^ 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 2)]; linarith [hF2]
  simp only at hanti
  linarith [hanti, hle, hge]

/-- The certificate hypothesis forces `F zm E ≥ (16/5)·zm`. -/
theorem active_forces_F_lower {a b E : ℝ}
    (ha : 0 < a) (hb : 1 / 2 < b) (hsum : a + b < 1)
    (hcut : a + (1 - b) < 1 / 10000)
    (hE : 0 < E) (hEsmall : E ≤ 1 / 500)
    (hactive : psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E) :
    (16 / 5 : ℝ) * (1 - a - b) ≤ F (1 - a - b) E := by
  set zm := 1 - a - b with hzmdef
  have hzmpos : 0 < zm := by simp only [hzmdef]; linarith
  have hzmsmall : zm ≤ 1 / 1000 := by simp only [hzmdef]; linarith
  have hm : (a + b) / 2 = (1 - zm) / 2 := by simp only [hzmdef]; ring
  have hrad : |1 - 2 * ((a + b) / 2)| = zm := by
    rw [hm]
    rw [show (1 : ℝ) - 2 * ((1 - zm) / 2) = zm by ring]
    exact abs_of_pos hzmpos
  -- step 1: unfold the hypothesis
  have hδ : 0 ≤ 1 - H ((a + b) / 2) := by linarith [H_le_one ((a + b) / 2)]
  have hstep1 : F zm E ≤ eta E - eta (E + 1 - H ((a + b) / 2)) := by
    have hp : phi ((a + b) / 2) E = eta E - F zm E := by
      unfold phi; rw [hrad]
    have hq : psi ((a + b) / 2) E = eta (E + 1 - H ((a + b) / 2)) := rfl
    rw [hp, hq] at hactive
    linarith
  -- step 2/3: convexity plus the derivative bound
  have hHm : 1 - H ((a + b) / 2) ≤ (3 / 4) * zm ^ 2 := by
    rw [hm]
    exact FCAnalytic2.one_sub_H_near_half hzmpos.le hzmsmall
  have hE1 : E < 1 := by linarith
  have hconv : ∀ d : ℝ, 0 ≤ d → E + d ≤ 1 → eta E - eta (E + d) ≤ (2 / E) * d := by
    intro d hd hd1
    rcases eq_or_lt_of_le hd with hz | hdpos
    · rw [← hz]
      simp
    · have hDA := hasDerivAt_eta hE hE1
      have hdd : deriv eta E = -2 - (1 - 2 * entropyInverse E) /
          (Real.log 2 * entropyInverse E * (1 - entropyInverse E) * J (entropyInverse E)) :=
        deriv_eta hE hE1
      have hslope := Scalar.eta_convexOn_Ioc.le_slope_of_hasDerivAt
        (show E ∈ Set.Ioc (0 : ℝ) 1 from ⟨hE, hE1.le⟩)
        (show E + d ∈ Set.Ioc (0 : ℝ) 1 from ⟨by linarith, hd1⟩)
        (by linarith) hDA
      rw [slope_def_field, ← hdd] at hslope
      have hdiv := (le_div_iff₀ (show (0 : ℝ) < E + d - E by linarith)).mp hslope
      have hneg := neg_deriv_eta_upper hE hEsmall
      nlinarith only [hdiv, hneg, hd]
  have hEd1 : E + (1 - H ((a + b) / 2)) ≤ 1 := by
    have hz : (3 : ℝ) / 4 * zm ^ 2 ≤ 1 / 1000000 := by nlinarith only [hzmsmall, hzmpos]
    linarith [hHm, hEsmall]
  have hstep2 : eta E - eta (E + 1 - H ((a + b) / 2)) ≤ (2 / E) * ((3 / 4) * zm ^ 2) := by
    have hbase := hconv (1 - H ((a + b) / 2)) hδ hEd1
    have hrw : E + (1 - H ((a + b) / 2)) = E + 1 - H ((a + b) / 2) := by ring
    rw [hrw] at hbase
    have hmono : (2 / E) * (1 - H ((a + b) / 2)) ≤ (2 / E) * ((3 / 4) * zm ^ 2) := by
      have hEinv : (0 : ℝ) ≤ 2 / E := by positivity
      nlinarith only [hHm, hEinv]
    linarith [hbase, hmono]
  -- step 5/6: normalise by homogeneity
  set X := zm / E with hXdef
  have hXpos : 0 < X := div_pos hzmpos hE
  have hFX : F zm E = E * F X 1 := FCAnalytic2.F_scale_one hE
  have hquad : F X 1 ≤ (3 / 2) * X ^ 2 := by
    have hchain : E * F X 1 ≤ (2 / E) * ((3 / 4) * zm ^ 2) := by
      rw [← hFX]; linarith [hstep1, hstep2]
    have hzmE : zm = X * E := by
      simp only [hXdef]; field_simp
    rw [hzmE] at hchain
    have hrw : (2 / E) * ((3 / 4) * (X * E) ^ 2) = E * ((3 / 2) * X ^ 2) := by
      field_simp; ring
    rw [hrw] at hchain
    exact le_of_mul_le_mul_left hchain hE
  -- step 7: the anchor forces X > 2
  have hXgt : 2 < X := by
    by_contra hcon
    push_neg at hcon
    have hanti := antitoneOn_F_div_sq (h := 1) (by norm_num)
      (show X ∈ Set.Ioi (0 : ℝ) from hXpos)
      (show (2 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num) hcon
    have hF2 := FCAnalytic2.F_two_one_lower
    have hXsq : (0 : ℝ) < X ^ 2 := by positivity
    have hle : F X 1 / X ^ 2 ≤ (3 / 2 : ℝ) := by
      rw [div_le_iff₀ hXsq]; linarith [hquad]
    have hge : (8 / 5 : ℝ) ≤ F 2 1 / 2 ^ 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 2)]; linarith [hF2]
    simp only at hanti
    linarith [hanti, hle, hge]
  -- step 8: slope monotonicity plus the anchor
  have hslope := FCAnalytic2.F_slope_mono (by norm_num : (0 : ℝ) < 2) hXgt.le
  have hF2 := FCAnalytic2.F_two_one_lower
  have hlow : (16 / 5 : ℝ) ≤ F X 1 / X := by
    have : (16 / 5 : ℝ) ≤ F 2 1 / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]; linarith
    linarith [hslope]
  have hfin : (16 / 5 : ℝ) * X ≤ F X 1 := by
    rw [le_div_iff₀ hXpos] at hlow
    linarith
  have hzmE : zm = X * E := by simp only [hXdef]; field_simp
  rw [hFX, hzmE]
  nlinarith only [hfin, hE]

#check @neg_deriv_eta_upper
#check @active_forces_two_E_lt
#check @active_forces_F_lower
#print axioms neg_deriv_eta_upper
#print axioms active_forces_two_E_lt
#print axioms active_forces_F_lower

end GeneralCK.FCActive

end


