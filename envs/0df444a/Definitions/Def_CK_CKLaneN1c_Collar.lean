-- Prove2me | Definitions.Def_CK_CKLaneN1c_Collar
-- name    : CK_CKLaneN1c_Collar
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T10:21:45.933017+00:00
-- url     : https://prove2.me/theorems/f9d1ed20-db39-4b2a-808c-89931e327955
-- title:
--   Courtade–Kumar proof module `CKLaneN1c.Collar` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1c.Collar` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1c.Collar` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1c.Collar (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1c/Collar.lean)

import Definitions.Def_CK_CKLaneN1c_FiveGain
import Definitions.Def_CK_CKLaneN1c_NormAnalytic
import Definitions.Def_CK_CKLaneN1c_Normalized
import Definitions.Def_CK_GeneralCK_LowInformationMeans

-- ===== source module CKLaneN1c.Collar =====
section

/-!
# Lane N1c-c: the three explicit collars of SHARPER_COLLARS.md (the transition `prior_collar` delegate)

Archive: `CK_NO_SEPARATION_EXTENSION/prior_inputs/SHARPER_COLLARS.md` (dependency of
`CK_OPPOSITE_EXTENSION.zip`), invoked by `transition/PROOF.md` §4 for the `prior_collar` owner.

**Theorem (canonical orientation `a ≤ b`, `a + b ≤ 1`).** Assume positive feasible entropies and the
shared-entropy cap `E ≤ min{H(a), H(b)}`.  In each row

| row | region | margin coefficient of `q²/E` |
|---|---|---|
| 1 | `q ≤ E`,  `d ≥ 5E` | `50/49 − 69/100 − 1183/3600 = 317/176400` |
| 2 | `q ≤ 2E`, `d ≥ 6E` | `1 − 3/5 − 1183/4320 = 109/864` |
| 3 | `q ≤ 4E`, `d ≥ 8E` | `5/28 + 1600/2891 − 1/2 − 1183/5760 > 0` |

the psi-active branch satisfies `gap ≤ cost` (`sharper_collars`).  Proof exactly as in SHARPER_COLLARS:

* (2) endpoint gain `B_end ≥ F(d,E) + (d/(2L)) 𝒥(τ)` for `d ≥ 5E`: `FiveGain.law_endpoint_logarithmic_lower`
  (corpus source `PsiEndpointFiveGain.lean`, namespace-renamed copy);
* (5) `0 ≤ A ≤ 13q/(3E)`: `PsiLowEntropyRedesign.child_slope_bounds` (global `zF_zz ≤ 13/6`);
* §3 the two convex supporting lines at `E` (valid on the whole feasible split interval by the cap):
  `childAverage_lower_feasible`; split loss `169 L q²/(72 d) ≤ 1183 q²/(720 d)` (`NA.split_loss`, `L ≤ 7/10`);
* (7) `f'(5)/10 < 69/100`, `f'(6)/12 < 3/5`, `f'(8)/16 < 1/2` (`W5`, `W6`, `W8`, kernel-certified with
  `CKLaneE.FP` at a lower contact bracket) and radial concavity (`NA.radialLoss_le`);
* (8) `(E/q²)[η(E) − η(E+C(q))] ≥ 10E/7 + 50/(49(1 + C(q)/(2E)))` (`parent_correction`, from the corpus
  `eta_increment_ge_linear_log` and `log(1+x) ≥ 2x/(2+x)`), with the row bounds
  `C(q)/E ≤ 27E/35, 16E/5, 27E/2` (`C_row1/2/3`, from `LowInformation.Cn_upper_sharp`).
-/

set_option autoImplicit false


namespace CKLaneN1c.Collar

open GeneralCK CKLaneE.FP CKLaneN1 PsiChildEntropyCoupling PsiSignedSplit

/-! ## Constants -/

theorem log_two_le_seven_tenths : Real.log 2 ≤ 7 / 10 := by
  have h := log_two_mem.2
  have h2 : CKLaneE.FP.LqHi ≤ (7 / 10 : ℚ) := by decide +kernel
  have h3 : ((CKLaneE.FP.LqHi : ℚ) : ℝ) ≤ ((7 / 10 : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  linarith

theorem log_two_ge_69 : (69 / 100 : ℝ) ≤ Real.log 2 := by
  have h := log_two_mem.1
  have h2 : (69 / 100 : ℚ) ≤ CKLaneE.FP.LqLo := by decide +kernel
  have h3 : ((69 / 100 : ℚ) : ℝ) ≤ ((CKLaneE.FP.LqLo : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  linarith

/-- `log(1+x) ≥ 2x/(2+x)` for `x ≥ 0` (first atanh term at `w = x/(2+x)`). -/
theorem log_one_add_ge {x : ℝ} (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ Real.log (1 + x) := by
  have hw0 : 0 ≤ x / (2 + x) := by positivity
  have hw1 : x / (2 + x) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h := Real.sum_range_le_log_div hw0 hw1 1
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add, pow_one, div_one] at h
  have e : (1 + x / (2 + x)) / (1 - x / (2 + x)) = 1 + x := by
    have h2 : (2 + x) ≠ 0 := by positivity
    (first | (field_simp; ring) | field_simp | ring)
  rw [e] at h
  have e2 : 2 * x / (2 + x) = 2 * (x / (2 + x)) := by ring
  rw [e2]
  linarith

/-! ## Upper bounds of `C(q) = 1 − H((1−q)/2)` in the three rows -/

theorem C_upper {q qm : ℝ} (hq : 0 ≤ q) (hqm : q ≤ qm) (hqm1 : qm < 1) :
    1 - H ((1 - q) / 2) ≤ q ^ 2 * (1 / 2 + qm ^ 2 / (12 * (1 - qm ^ 2))) / (69 / 100) := by
  have hq1 : q < 1 := lt_of_le_of_lt hqm hqm1
  have h := LowInformation.Cn_upper_sharp hq hq1
  unfold SmallMean.Cn at h
  have hL := log_two_ge_69
  have hLpos := log_two_pos
  have hqq : q ^ 2 ≤ qm ^ 2 := pow_le_pow_left₀ hq hqm 2
  have hqm2 : 0 < 1 - qm ^ 2 := by nlinarith
  have hq2 : 0 < 1 - q ^ 2 := by nlinarith
  have h4 : q ^ 4 / (12 * (1 - q ^ 2)) ≤ q ^ 2 * (qm ^ 2 / (12 * (1 - qm ^ 2))) := by
    rw [div_le_iff₀ (by positivity)]
    have e : q ^ 2 * (qm ^ 2 / (12 * (1 - qm ^ 2))) * (12 * (1 - q ^ 2)) =
        q ^ 2 * qm ^ 2 * ((1 - q ^ 2) / (1 - qm ^ 2)) := by (first | (field_simp; ring) | field_simp | ring)
    rw [e]
    have hr : 1 ≤ (1 - q ^ 2) / (1 - qm ^ 2) := by rw [le_div_iff₀ hqm2]; linarith
    have hq2' : 0 ≤ q ^ 2 * qm ^ 2 := by positivity
    have : q ^ 4 = q ^ 2 * q ^ 2 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hqq (sq_nonneg q)]
  have hnum : 0 ≤ q ^ 2 * (1 / 2 + qm ^ 2 / (12 * (1 - qm ^ 2))) := by positivity
  have hC : 1 - H ((1 - q) / 2) ≤ q ^ 2 * (1 / 2 + qm ^ 2 / (12 * (1 - qm ^ 2))) / Real.log 2 := by
    rw [le_div_iff₀ hLpos]
    nlinarith
  exact hC.trans (div_le_div_of_nonneg_left hnum (by norm_num) hL)

theorem C_row1 {q : ℝ} (hq : 0 ≤ q) (hq6 : q ≤ 1 / 6) : 1 - H ((1 - q) / 2) ≤ 27 / 35 * q ^ 2 := by
  have h := C_upper hq hq6 (by norm_num)
  have e : q ^ 2 * (1 / 2 + (1 / 6 : ℝ) ^ 2 / (12 * (1 - (1 / 6) ^ 2))) / (69 / 100) =
      2110 / 2898 * q ^ 2 := by ring
  rw [e] at h
  nlinarith [sq_nonneg q]

theorem C_row2 {q : ℝ} (hq : 0 ≤ q) (hq4 : q ≤ 1 / 4) : 1 - H ((1 - q) / 2) ≤ 4 / 5 * q ^ 2 := by
  have h := C_upper hq hq4 (by norm_num)
  have e : q ^ 2 * (1 / 2 + (1 / 4 : ℝ) ^ 2 / (12 * (1 - (1 / 4) ^ 2))) / (69 / 100) =
      910 / 1242 * q ^ 2 := by ring
  rw [e] at h
  nlinarith [sq_nonneg q]

theorem C_row3 {q : ℝ} (hq : 0 ≤ q) (hq3 : q ≤ 1 / 3) : 1 - H ((1 - q) / 2) ≤ 27 / 32 * q ^ 2 := by
  have h := C_upper hq hq3 (by norm_num)
  have e : q ^ 2 * (1 / 2 + (1 / 3 : ℝ) ^ 2 / (12 * (1 - (1 / 3) ^ 2))) / (69 / 100) =
      4900 / 6624 * q ^ 2 := by ring
  rw [e] at h
  nlinarith [sq_nonneg q]

/-! ## Radial scalar certificates (SHARPER_COLLARS (7)) -/

/-- Kernel test: `v_l` is a lower bracket of the contact at `x₀` and `radialSlope(v_l)/(2x₀) ≤ w`. -/
def radCheck (x0 vl w : ℚ) : Bool :=
  decide (0 < x0) && ptOk vl &&
  decide (vl < 1 / 2 ∧ x0 * Hhi vl ≤ 1 - 2 * vl ∧ 0 < nKl vl ∧ 0 ≤ HnumHi vl ∧
    nRs vl / (2 * x0) ≤ w)

theorem radCheck_sound {x0 vl w : ℚ} (h : radCheck x0 vl w = true) {x : ℝ} (hx : (x0 : ℝ) ≤ x) :
    deriv (fun r => F r 1) x / (2 * x) ≤ (w : ℝ) := by
  simp only [radCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hx0, hpt⟩, hvlh, hvlH, hkl0, hhn0, hw⟩ := h
  have hx0R : (0 : ℝ) < (x0 : ℝ) := by exact_mod_cast hx0
  have hvl0 : (0 : ℝ) < (vl : ℝ) := by exact_mod_cast (ptOk_pos hpt).1
  have hvlhR : (vl : ℝ) < 1 / 2 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr hvlh
    push_cast at h'
    linarith
  have hvlHR : (x0 : ℝ) * ((Hhi vl : ℚ) : ℝ) ≤ 1 - 2 * (vl : ℝ) := by exact_mod_cast hvlH
  have hvlcR : (x0 : ℝ) * H (vl : ℝ) ≤ 1 - 2 * (vl : ℝ) :=
    (mul_le_mul_of_nonneg_left (H_bounds hpt).2 hx0R.le).trans hvlHR
  have hslope := NA.radial_ratio_le_slope hx0R hx hvl0 hvlhR hvlcR
  obtain ⟨hl1, hl2, hl3, hl4⟩ := ptOk_sound hpt
  have hvl1 : (0 : ℝ) < 1 - (vl : ℝ) := by linarith
  have hhnle : Certificates.Mixed.hn (vl : ℝ) ≤ ((HnumHi vl : ℚ) : ℝ) := by
    unfold Certificates.Mixed.hn
    simp only [HnumHi]
    push_cast
    have a1 := mul_le_mul_of_nonneg_left hl1 hvl0.le
    have a2 := mul_le_mul_of_nonneg_left hl3 hvl1.le
    linarith
  have hklR : (0 : ℝ) < ((nKl vl : ℚ) : ℝ) := by exact_mod_cast hkl0
  have hklle : ((nKl vl : ℚ) : ℝ) ≤ Certificates.Mixed.kap (vl : ℝ) := by
    unfold Certificates.Mixed.kap
    rw [Real.log_mul hvl0.ne' hvl1.ne']
    simp only [nKl]
    push_cast
    linarith
  have hrs := NA.radialSlope_le hvl0 hvlhR (J_bounds hpt).2 hhnle hklR hklle LqLo_pos
    log_two_mem.1
  have hRsQ : ((nRs vl : ℚ) : ℝ) = ((JhiQ vl : ℚ) : ℝ) + (1 - 2 * (vl : ℝ)) *
      ((HnumHi vl : ℚ) : ℝ) / (2 * (LqLo : ℝ) * (vl : ℝ) * (1 - (vl : ℝ)) * ((nKl vl : ℚ) : ℝ)) := by
    simp only [nRs]; push_cast; ring
  have hwR : ((nRs vl : ℚ) : ℝ) / (2 * (x0 : ℝ)) ≤ (w : ℝ) := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hw
    push_cast at h'
    exact h'
  refine hslope.trans ?_
  rw [← hRsQ] at hrs
  exact (div_le_div_of_nonneg_right hrs (by positivity)).trans hwR

theorem W5 {x : ℝ} (hx : 5 ≤ x) : deriv (fun r => F r 1) x / (2 * x) ≤ 69 / 100 := by
  have h := radCheck_sound (x0 := 5) (vl := dy 129820680520939 52) (w := 69 / 100)
    (by decide +kernel) (x := x) (by push_cast; linarith)
  push_cast at h
  linarith

theorem W6 {x : ℝ} (hx : 6 ≤ x) : deriv (fun r => F r 1) x / (2 * x) ≤ 3 / 5 := by
  have h := radCheck_sound (x0 := 6) (vl := dy 104392600756079 52) (w := 3 / 5)
    (by decide +kernel) (x := x) (by push_cast; linarith)
  push_cast at h
  linarith

theorem W8 {x : ℝ} (hx : 8 ≤ x) : deriv (fun r => F r 1) x / (2 * x) ≤ 1 / 2 := by
  have h := radCheck_sound (x0 := 8) (vl := dy 73990925584681 52) (w := 1 / 2)
    (by decide +kernel) (x := x) (by push_cast; linarith)
  push_cast at h
  linarith

/-! ## Supporting lines on the feasible interval -/

theorem child_tangent_feasible {z E h : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) (hE : 0 < E) (hE1 : E < 1)
    (hEc : E ≤ H ((1 - z) / 2)) (hh : 0 < h) (hhc : h ≤ H ((1 - z) / 2)) :
    radialPhi z E + deriv (radialPhi z) E * (h - E) ≤ radialPhi z h := by
  have hc := radialPhi_entropy_convexOn hz hz1
  have hd := NA.radialPhi_hasDerivAt hz hE hE1
  have hEm : E ∈ Set.Ioc 0 (H ((1 - z) / 2)) := ⟨hE, hEc⟩
  have hhm : h ∈ Set.Ioc 0 (H ((1 - z) / 2)) := ⟨hh, hhc⟩
  rcases lt_trichotomy E h with hlt | he | hgt
  · have hs := hc.le_slope_of_hasDerivAt hEm hhm hlt hd
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    linarith
  · rw [← he]; simp
  · have hs := hc.slope_le_of_hasDerivAt hhm hEm hgt hd
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr hgt)).mp hs
    nlinarith

/-- SHARPER_COLLARS §3: the two convex supporting lines at `E` (the shared-entropy cap puts `E` in
both feasible intervals; feasibility puts `e`, `f` there). -/
theorem childAverage_lower_feasible {d q E t : ℝ} (hq : 0 ≤ q) (hqd : q ≤ d) (hdq : d + q < 1)
    (hE : 0 < E) (hE1 : E < 1) (ht : |t| < 1)
    (hEa : E ≤ H ((1 - d - q) / 2)) (hEb : E ≤ H ((1 + d - q) / 2))
    (hea : E * (1 + t) ≤ H ((1 - d - q) / 2)) (hfb : E * (1 - t) ≤ H ((1 + d - q) / 2)) :
    (radialPhi (d + q) E + radialPhi (d - q) E) / 2 + E * t * slopeDifference d q E / 2 ≤
      childAverage d q E t := by
  have hti := abs_lt.mp ht
  have hep : 0 < E * (1 + t) := mul_pos hE (by linarith)
  have hem : 0 < E * (1 - t) := mul_pos hE (by linarith)
  have e1 : (1 - (d + q)) / 2 = (1 - d - q) / 2 := by ring
  have e2 : H ((1 - (d - q)) / 2) = H ((1 + d - q) / 2) := by
    rw [← H_complement ((1 + d - q) / 2)]
    congr 1
    ring
  have hp := child_tangent_feasible (z := d + q) (by linarith) hdq hE hE1 (by rw [e1]; exact hEa) hep
    (by rw [e1]; exact hea)
  have hm := child_tangent_feasible (z := d - q) (by linarith) (by linarith) hE hE1
    (by rw [e2]; exact hEb) hem (by rw [e2]; exact hfb)
  have hpr : E * (1 + t) - E = E * t := by ring
  have hmr : E * (1 - t) - E = -(E * t) := by ring
  rw [hpr] at hp
  rw [hmr] at hm
  unfold childAverage slopeDifference
  linear_combination hp / 2 + hm / 2

/-! ## Parent correction (SHARPER_COLLARS (8)) -/

theorem parent_correction {E C q Cm : ℝ} (hE : 0 < E) (hC0 : 0 ≤ C)
    (hCq : q ^ 2 / (2 * Real.log 2) ≤ C) (hEC : E + C ≤ 1) (hCm : C ≤ Cm) :
    q ^ 2 / E * (10 * E / 7 + 50 / (49 * (1 + Cm / (2 * E)))) ≤ eta E - eta (E + C) := by
  have hL := log_two_pos
  have hL7 := log_two_le_seven_tenths
  have hinc := eta_increment_ge_linear_log hE hC0 hEC
  have hx : 0 ≤ C / E := div_nonneg hC0 hE.le
  have hlog := log_one_add_ge hx
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hCm0 : 0 ≤ Cm := hC0.trans hCm
  have hC2 : q ^ 2 / Real.log 2 ≤ 2 * C := by
    have e : q ^ 2 / Real.log 2 = 2 * (q ^ 2 / (2 * Real.log 2)) := by (first | (field_simp; ring) | field_simp | ring)
    linarith
  have h1 : 10 * q ^ 2 / 7 ≤ 2 * C := by
    have h2 : 10 * q ^ 2 / 7 ≤ q ^ 2 / Real.log 2 := by
      rw [le_div_iff₀ hL]
      nlinarith
    linarith
  have hden : 0 < 2 * E + Cm := by positivity
  have hA : 2 * (C / E) / (2 + C / E) = 2 * C / (2 * E + C) := by
    (first | (field_simp; ring) | field_simp | ring)
  rw [hA] at hlog
  have hB : 2 * C / (2 * E + Cm) ≤ 2 * C / (2 * E + C) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hB2 : q ^ 2 / Real.log 2 / (2 * E + Cm) ≤ 2 * C / (2 * E + Cm) :=
    div_le_div_of_nonneg_right hC2 hden.le
  have hlog2 : q ^ 2 / Real.log 2 / (2 * E + Cm) ≤ Real.log (1 + C / E) := by linarith
  have h3 : q ^ 2 / Real.log 2 / (2 * E + Cm) / Real.log 2 ≤ Real.log (1 + C / E) / Real.log 2 :=
    div_le_div_of_nonneg_right hlog2 hL.le
  have hL2 : Real.log 2 ^ 2 ≤ 49 / 100 := by nlinarith
  have h4 : 50 * q ^ 2 / (49 * (E + Cm / 2)) ≤ q ^ 2 / Real.log 2 / (2 * E + Cm) / Real.log 2 := by
    have e1 : q ^ 2 / Real.log 2 / (2 * E + Cm) / Real.log 2 =
        q ^ 2 / (Real.log 2 ^ 2 * (2 * E + Cm)) := by (first | (field_simp; ring) | field_simp | ring)
    have e2 : 50 * q ^ 2 / (49 * (E + Cm / 2)) = q ^ 2 / (49 / 100 * (2 * E + Cm)) := by
      (first | (field_simp; ring) | field_simp | ring)
    rw [e1, e2]
    apply div_le_div_of_nonneg_left hq2 (by positivity)
    exact mul_le_mul_of_nonneg_right hL2 hden.le
  have e : q ^ 2 / E * (10 * E / 7 + 50 / (49 * (1 + Cm / (2 * E)))) =
      10 * q ^ 2 / 7 + 50 * q ^ 2 / (49 * (E + Cm / 2)) := by
    (first | (field_simp; ring) | field_simp | ring)
  rw [e]
  linarith

/-! ## The collar comparison -/

/-- SHARPER_COLLARS §3–§5 assembled with the endpoint gain `d/(2L) 𝒥(τ)`. -/
theorem collar_core {d q E t C P W K : ℝ} (hq : 0 ≤ q) (hqd : q ≤ d) (hd : 0 < d) (hE : 0 < E)
    (hE1 : E < 1) (ht : |t| < 1)
    (hchild : (radialPhi (d + q) E + radialPhi (d - q) E) / 2 + E * t * slopeDifference d q E / 2 ≤
      childAverage d q E t)
    (hpar : q ^ 2 / E * P ≤ eta E - eta (E + C))
    (hrad : radialLoss d q E ≤ q ^ 2 / E * W)
    (hK : 169 * Real.log 2 * q ^ 2 / (72 * d) ≤ q ^ 2 / E * K)
    (hval : 0 ≤ P - W - K) :
    eta (E + C) - childAverage d q E t ≤ F d E + d / (2 * Real.log 2) * barrier t := by
  obtain ⟨hA0, hA⟩ := PsiLowEntropyRedesign.child_slope_bounds hE hE1 hq hqd
  have hL := log_two_pos
  have hc : 0 < d / (2 * Real.log 2) := by positivity
  have hsplit := NA.split_loss hc hE hA0 hA ht
  have hsp : 169 * q ^ 2 / (144 * (d / (2 * Real.log 2))) = 169 * Real.log 2 * q ^ 2 / (72 * d) := by
    (first | (field_simp; ring) | field_simp | ring)
  rw [hsp] at hsplit
  have hphi : (radialPhi (d + q) E + radialPhi (d - q) E) / 2 = eta E - F d E - radialLoss d q E := by
    unfold radialPhi radialLoss
    ring
  have hqE : 0 ≤ q ^ 2 / E := by positivity
  have hfin := mul_nonneg hqE hval
  have hfin' : q ^ 2 / E * K ≤ q ^ 2 / E * P - q ^ 2 / E * W := by
    have e : q ^ 2 / E * (P - W - K) = q ^ 2 / E * P - q ^ 2 / E * W - q ^ 2 / E * K := by ring
    linarith
  linarith

/-- Law-level collar step, common to the three rows. -/
theorem collar_of_bounds {k : ℕ} (μ : InteriorLaw (Fin k)) (hsum : μ.a + μ.b ≤ 1)
    (hcap : μ.meanEntropy ≤ min (H μ.a) (H μ.b)) (h5 : 5 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqd : 1 - μ.a - μ.b ≤ μ.b - μ.a) (hact : PsiActive μ) {P W K : ℝ}
    (hpar : (1 - μ.a - μ.b) ^ 2 / μ.meanEntropy * P ≤
      eta μ.meanEntropy - eta (μ.meanEntropy + (1 - H ((1 - (1 - μ.a - μ.b)) / 2))))
    (hW : deriv (fun r => F r 1) ((μ.b - μ.a) / μ.meanEntropy) /
      (2 * ((μ.b - μ.a) / μ.meanEntropy)) ≤ W)
    (hK : 169 * Real.log 2 * (1 - μ.a - μ.b) ^ 2 / (72 * (μ.b - μ.a)) ≤
      (1 - μ.a - μ.b) ^ 2 / μ.meanEntropy * K)
    (hval : 0 ≤ P - W - K) : μ.gap ≤ μ.cost := by
  have hEpos := CKLaneD.law_meanEntropy_pos μ
  have haI := μ.a_interior
  have hbI := μ.b_interior
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  have hd : 0 < μ.b - μ.a := by linarith
  have hdq : (μ.b - μ.a) + (1 - μ.a - μ.b) < 1 := by linarith
  have hE1 : μ.meanEntropy < 1 := by linarith
  obtain ⟨ht, hce, hcf⟩ := PsiRetainedChildBridge.positive_entropy_split μ.e_pos μ.f_pos
  change μ.meanEntropy * (1 + (μ.e - μ.f) / (μ.e + μ.f)) = μ.e at hce
  change μ.meanEntropy * (1 - (μ.e - μ.f) / (μ.e + μ.f)) = μ.f at hcf
  have hca : (1 - (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.a := by ring
  have hcb : (1 + (μ.b - μ.a) - (1 - μ.a - μ.b)) / 2 = μ.b := by ring
  have hEa : μ.meanEntropy ≤ H μ.a := hcap.trans (min_le_left _ _)
  have hEb : μ.meanEntropy ≤ H μ.b := hcap.trans (min_le_right _ _)
  have hchild := childAverage_lower_feasible (d := μ.b - μ.a) (q := 1 - μ.a - μ.b)
    (E := μ.meanEntropy) (t := (μ.e - μ.f) / (μ.e + μ.f)) hq0 hqd hdq hEpos hE1 ht
    (by rw [hca]; exact hEa) (by rw [hcb]; exact hEb)
    (by rw [hca, hce]; exact μ.e_le_cap) (by rw [hcb, hcf]; exact μ.f_le_cap)
  have hrad := (NA.radialLoss_le hd hEpos hq0 hqd).trans
    (mul_le_mul_of_nonneg_left hW (by positivity))
  have hcore := collar_core hq0 hqd hd hEpos hE1 ht hchild hpar hrad hK hval
  have hmean : (1 - (1 - μ.a - μ.b)) / 2 = μ.midpoint := by
    unfold InteriorLaw.midpoint
    ring
  have hc := PsiRetainedChildBridge.canonical_hybrid_gap_le_childAverage
    (d := μ.b - μ.a) (q := 1 - μ.a - μ.b) (E := μ.meanEntropy)
    (t := (μ.e - μ.f) / (μ.e + μ.f)) hq0 hqd (by rw [hmean]; exact hact.le)
  rw [hca, hcb, hce, hcf] at hc
  change μ.gap ≤ _ at hc
  have hcost := FiveGain.law_endpoint_logarithmic_lower μ h5
  linarith

/-- The split-loss coefficient of row `k₀` (`d ≥ k₀ E`): `169 L q²/(72 d) ≤ (q²/E) · 1183/(720 k₀)`. -/
theorem split_coeff {d q E k0 : ℝ} (hE : 0 < E) (hk0 : 0 < k0) (hd : k0 * E ≤ d) :
    169 * Real.log 2 * q ^ 2 / (72 * d) ≤ q ^ 2 / E * (1183 / (720 * k0)) := by
  have hL7 := log_two_le_seven_tenths
  have hL := log_two_pos
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd
  have h1 : 169 * Real.log 2 * q ^ 2 / (72 * d) ≤ 169 * (7 / 10) * q ^ 2 / (72 * d) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := sq_nonneg q
    nlinarith
  have h2 : 169 * (7 / 10) * q ^ 2 / (72 * d) ≤ 169 * (7 / 10) * q ^ 2 / (72 * (k0 * E)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have e : 169 * (7 / 10) * q ^ 2 / (72 * (k0 * E)) = q ^ 2 / E * (1183 / (720 * k0)) := by
    (first | (field_simp; ring) | field_simp | ring)
  linarith

/-! ## The three row inequalities (SHARPER_COLLARS §4–§5) -/

/-- Row 1: `10E/7 + 50/(49(1 + 27E/70)) ≥ 50/49` and `50/49 − 69/100 − 1183/3600 = 317/176400 > 0`. -/
theorem row1_val {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ 10 * E / 7 + 50 / (49 * (1 + 27 * E / 70)) - 69 / 100 - 1183 / (720 * 5) := by
  have hs : 50 / 49 - 50 / 49 * (27 * E / 70) ≤ 50 / (49 * (1 + 27 * E / 70)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg E]
  norm_num at hs ⊢
  linarith

/-- Row 2: `10E/7 + 50/(49(1 + 8E/5)) ≥ 1` (i.e. `(16/7)E² − (6/35)E + 1/49 > 0`) and
`1 − 3/5 − 1183/4320 = 109/864 > 0`. -/
theorem row2_val {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ 10 * E / 7 + 50 / (49 * (1 + 8 * E / 5)) - 3 / 5 - 1183 / (720 * 6) := by
  have hs : 1 - 10 * E / 7 ≤ 50 / (49 * (1 + 8 * E / 5)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (E - 3 / 80)]
  norm_num at hs ⊢
  linarith

/-- Row 3: `10E/7 + 50/(49(1 + 27E/4)) ≥ 1/2 + 1183/5760` (a quadratic with negative discriminant). -/
theorem row3_val {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ 10 * E / 7 + 50 / (49 * (1 + 27 * E / 4)) - 1 / 2 - 1183 / (720 * 8) := by
  have hs : 4063 / 5760 - 10 * E / 7 ≤ 50 / (49 * (1 + 27 * E / 4)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (E - 173 / 1000)]
  norm_num at hs ⊢
  linarith

/-! ## The collar theorem -/

set_option maxHeartbeats 1000000 in
/-- **SHARPER_COLLARS.md, three explicit collars** (canonical orientation, psi-active branch): under
the shared-entropy cap `E ≤ min(H a, H b)`, each row `q ≤ E ∧ 5E ≤ d`, `q ≤ 2E ∧ 6E ≤ d`,
`q ≤ 4E ∧ 8E ≤ d` gives `gap ≤ cost`. -/
theorem sharper_collars : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    μ.meanEntropy ≤ min (H μ.a) (H μ.b) →
    ((1 - μ.a - μ.b ≤ μ.meanEntropy ∧ 5 * μ.meanEntropy ≤ μ.b - μ.a) ∨
      (1 - μ.a - μ.b ≤ 2 * μ.meanEntropy ∧ 6 * μ.meanEntropy ≤ μ.b - μ.a) ∨
      (1 - μ.a - μ.b ≤ 4 * μ.meanEntropy ∧ 8 * μ.meanEntropy ≤ μ.b - μ.a)) →
    PsiActive μ → μ.gap ≤ μ.cost := by
  intro k μ _hab hsum hcap hrow hact
  have hEpos := CKLaneD.law_meanEntropy_pos μ
  have haI := μ.a_interior
  have hbI := μ.b_interior
  have hL := log_two_pos
  have hq0 : 0 ≤ 1 - μ.a - μ.b := by linarith
  -- physical parent cap `E + C(q) ≤ 1`
  have hpc := PsiRetainedChildBridge.entropy_mean_le_parent_cap
    ⟨haI.1.le, haI.2.le⟩ ⟨hbI.1.le, hbI.2.le⟩ μ.e_le_cap μ.f_le_cap
  have hmid : (1 - (1 - μ.a - μ.b)) / 2 = (μ.a + μ.b) / 2 := by ring
  have hEC : μ.meanEntropy + (1 - H ((1 - (1 - μ.a - μ.b)) / 2)) ≤ 1 := by
    rw [hmid]
    change (μ.e + μ.f) / 2 + (1 - H ((μ.a + μ.b) / 2)) ≤ 1
    linarith
  have hC0 : 0 ≤ 1 - H ((1 - (1 - μ.a - μ.b)) / 2) := by
    linarith [H_le_one ((1 - (1 - μ.a - μ.b)) / 2)]
  have hCq := NA.C_ge_half_sq hq0 (by linarith : 1 - μ.a - μ.b ≤ 1)
  have hxE : (μ.b - μ.a) / μ.meanEntropy * μ.meanEntropy = μ.b - μ.a := by (first | (field_simp; ring) | field_simp | ring)
  have hx_of : ∀ c : ℝ, c * μ.meanEntropy ≤ μ.b - μ.a → c ≤ (μ.b - μ.a) / μ.meanEntropy := by
    intro c hc
    rw [le_div_iff₀ hEpos]
    exact hc
  rcases hrow with ⟨hq, hdk⟩ | ⟨hq, hdk⟩ | ⟨hq, hdk⟩
  · -- row 1: `q ≤ E`, `d ≥ 5E`
    have hq6 : 1 - μ.a - μ.b ≤ 1 / 6 := by linarith
    have hC := C_row1 hq0 hq6
    have hCm : 1 - H ((1 - (1 - μ.a - μ.b)) / 2) ≤ 27 / 35 * μ.meanEntropy ^ 2 := by
      have : (1 - μ.a - μ.b) ^ 2 ≤ μ.meanEntropy ^ 2 := pow_le_pow_left₀ hq0 hq 2
      linarith
    have hpar := parent_correction hEpos hC0 hCq hEC hCm
    have hW := W5 (hx_of 5 hdk)
    have hK := split_coeff (q := 1 - μ.a - μ.b) hEpos (by norm_num : (0 : ℝ) < 5) hdk
    refine collar_of_bounds μ hsum hcap hdk (by linarith) hact hpar hW hK ?_
    have e : 27 / 35 * μ.meanEntropy ^ 2 / (2 * μ.meanEntropy) = 27 * μ.meanEntropy / 70 := by
      (first | (field_simp; ring) | field_simp | ring)
    rw [e]
    exact row1_val hEpos.le
  · -- row 2: `q ≤ 2E`, `d ≥ 6E`
    have hq4 : 1 - μ.a - μ.b ≤ 1 / 4 := by linarith
    have hC := C_row2 hq0 hq4
    have hCm : 1 - H ((1 - (1 - μ.a - μ.b)) / 2) ≤ 16 / 5 * μ.meanEntropy ^ 2 := by
      have : (1 - μ.a - μ.b) ^ 2 ≤ (2 * μ.meanEntropy) ^ 2 := pow_le_pow_left₀ hq0 hq 2
      have e2 : (2 * μ.meanEntropy) ^ 2 = 4 * μ.meanEntropy ^ 2 := by ring
      linarith
    have hpar := parent_correction hEpos hC0 hCq hEC hCm
    have hW := W6 (hx_of 6 hdk)
    have hK := split_coeff (q := 1 - μ.a - μ.b) hEpos (by norm_num : (0 : ℝ) < 6) hdk
    refine collar_of_bounds μ hsum hcap (by linarith) (by linarith) hact hpar hW hK ?_
    have e : 16 / 5 * μ.meanEntropy ^ 2 / (2 * μ.meanEntropy) = 8 * μ.meanEntropy / 5 := by
      (first | (field_simp; ring) | field_simp | ring)
    rw [e]
    exact row2_val hEpos.le
  · -- row 3: `q ≤ 4E`, `d ≥ 8E`
    have hq3 : 1 - μ.a - μ.b ≤ 1 / 3 := by linarith
    have hC := C_row3 hq0 hq3
    have hCm : 1 - H ((1 - (1 - μ.a - μ.b)) / 2) ≤ 27 / 2 * μ.meanEntropy ^ 2 := by
      have : (1 - μ.a - μ.b) ^ 2 ≤ (4 * μ.meanEntropy) ^ 2 := pow_le_pow_left₀ hq0 hq 2
      have e2 : (4 * μ.meanEntropy) ^ 2 = 16 * μ.meanEntropy ^ 2 := by ring
      linarith
    have hpar := parent_correction hEpos hC0 hCq hEC hCm
    have hW := W8 (hx_of 8 hdk)
    have hK := split_coeff (q := 1 - μ.a - μ.b) hEpos (by norm_num : (0 : ℝ) < 8) hdk
    refine collar_of_bounds μ hsum hcap (by linarith) (by linarith) hact hpar hW hK ?_
    have e : 27 / 2 * μ.meanEntropy ^ 2 / (2 * μ.meanEntropy) = 27 * μ.meanEntropy / 4 := by
      (first | (field_simp; ring) | field_simp | ring)
    rw [e]
    exact row3_val hEpos.le

end CKLaneN1c.Collar

end


