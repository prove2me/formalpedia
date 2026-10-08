-- Prove2me | Definitions.Def_CK_CKLaneN4_RadialSharp
-- name    : CK_CKLaneN4_RadialSharp
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T20:20:19.315965+00:00
-- url     : https://prove2.me/theorems/9bde201f-ef78-4abd-aca8-a3e7b1347615
-- title:
--   Courtade–Kumar proof module `CKLaneN4.RadialSharp` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.RadialSharp` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.RadialSharp` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.RadialSharp (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/RadialSharp.lean)

import Definitions.Def_CK_CKLaneN4_ParentKernel
import Definitions.Def_CK_GeneralCK_PsiRadialDeficit

-- ===== source module CKLaneN4.RadialSharp =====
section

/-!
# Lane N4: the archive's radial constant `479/1000` (GLOBAL_EIGHT_PROOF.md (11))

`(F(d+q,E) + F(d-q,E))/2 - F(d,E) ≤ (479/1000) q²/E` for `d ≥ 8E`, via `f'(8)/16 < 479/1000`,
`f(x) = F(x, 1)` (archive: EIGHT_RATIO_FIXED, certified upper enclosure `< 0.478601724750980`).

`f'(8) = radialSlope(v8)`, `v8 = radialContact 8 1` (corpus `deriv_F_radius_slope`).  `radialSlope`
decreases on `(0, 1/2)` (its derivative `-hn(2 kap - (1-2v)²)/(…) ≤ 0` since `2 kap ≥ 2 log 2 > 1`), so a
rational lower contact bracket `vR ≤ v8` (`8 H(vR) ≤ 1 - 2 vR`) gives `f'(8) ≤ radialSlope(vR)`, which
is bounded by log certificates at the single point `vR`: `f'(8) ≤ 7.6577 < 7.664 = 16·479/1000`.
-/

namespace CKLaneN4

open GeneralCK CKLaneD Set Certificates.Mixed

theorem two_kap_ge {x : ℝ} (hx : 0 < x) (hx' : x < 1 / 2) : (1 - 2 * x) ^ 2 ≤ 2 * kap x := by
  unfold kap
  have hp : 0 < x * (1 - x) := by nlinarith
  have hq : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hl : Real.log (x * (1 - x)) ≤ Real.log (1 / 4) := Real.log_le_log hp hq
  have h4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hL : (69 / 100 : ℝ) < Real.log 2 := by
    have h1 := Certificates.PilotData.log_two.1
    norm_num at h1
    linarith
  have hsq : (1 - 2 * x) ^ 2 ≤ 1 := by nlinarith
  linarith

theorem hn_nonneg_of {x : ℝ} (hx : 0 < x) (hx1 : x < 1) : 0 ≤ hn x := by
  rw [hn_eq_H_mul_log]
  exact mul_nonneg (H_nonneg hx.le hx1.le) log_two_pos.le

theorem radialSlope_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1 / 2) :
    radialSlope v ≤ radialSlope u := by
  have hanti : AntitoneOn radialSlope (Icc u v) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc u v)
      (f' := fun x => -hn x * (2 * kap x - (1 - 2 * x) ^ 2) /
        (4 * Real.log 2 * x ^ 2 * (1 - x) ^ 2 * (kap x) ^ 2))
    · intro x hx
      exact (hasDerivAt_radialSlope (hu.trans_le hx.1) (hx.2.trans_lt hv)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_radialSlope (hu.trans hx.1) (hx.2.trans hv)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := hu.trans hx.1
      have hx1 : x < 1 / 2 := hx.2.trans hv
      have hk := kap_pos hx0 hx1
      have h2 := two_kap_ge hx0 hx1
      have hh := hn_nonneg_of hx0 (by linarith)
      have hD : 0 < 4 * Real.log 2 * x ^ 2 * (1 - x) ^ 2 * (kap x) ^ 2 := by
        have : 0 < 1 - x := by linarith
        have := log_two_pos
        positivity
      have hN : 0 ≤ hn x * (2 * kap x - (1 - 2 * x) ^ 2) := mul_nonneg hh (by linarith)
      have e : -hn x * (2 * kap x - (1 - 2 * x) ^ 2) /
          (4 * Real.log 2 * x ^ 2 * (1 - x) ^ 2 * (kap x) ^ 2) =
          -(hn x * (2 * kap x - (1 - 2 * x) ^ 2) /
            (4 * Real.log 2 * x ^ 2 * (1 - x) ^ 2 * (kap x) ^ 2)) := by ring
      rw [e]
      exact neg_nonpos.mpr (div_nonneg hN hD.le)
  exact hanti ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv

/-- The rational lower contact bracket at ratio 8. -/
def vR : ℚ := 303066831195102469 / 18446744073709551616

/-- Log certificates for `vR` and `1 - vR`. -/
def pR : PtCert :=
  ⟨⟨6, 6, (-4850684767405464296063 / 1180591620717411303424 : ℚ),
      (-4850684767405464296059 / 1180591620717411303424 : ℚ)⟩,
    ⟨0, 5, (-9778688817464095079 / 590295810358705651712 : ℚ),
      (-78229510539712760631 / 4722366482869645213696 : ℚ)⟩⟩

/-- Upper bound of `hn vR`. -/
def hnHiR : ℚ := -vR * pR.cx.lo - (1 - vR) * pR.cy.lo

/-- Lower bound of `kap vR`. -/
def kapLoR : ℚ := -(pR.cx.hi + pR.cy.hi) / 2

theorem pR_ok : checkPt vR pR = true := by decide +kernel

theorem radial_rat : 8 * Hhi vR pR ≤ 1 - 2 * vR ∧ 2 * vR ≤ 1 ∧ 0 < kapLoR ∧ 0 ≤ hnHiR ∧
    Jhi vR pR + (1 - 2 * vR) * hnHiR / (2 * L0 * vR * (1 - vR) * kapLoR) ≤ 7664 / 1000 := by
  decide +kernel

theorem deriv_F_eight_le : deriv (fun r => F r 1) 8 ≤ 7664 / 1000 := by
  rw [deriv_F_radius_slope (by norm_num) (by norm_num)]
  obtain ⟨hc, hv2, hk, hhn, hval⟩ := radial_rat
  obtain ⟨hv0, hv1, _, hHu, _, hJu⟩ := checkPt_bounds pR_ok
  have hlx := checkLogCert_sound (show checkLogCert vR pR.cx = true by
    have h := pR_ok; unfold checkPt at h; rw [Bool.and_eq_true] at h; exact h.1)
  have hly := checkLogCert_sound (show checkLogCert (1 - vR) pR.cy = true by
    have h := pR_ok; unfold checkPt at h; rw [Bool.and_eq_true] at h; exact h.2)
  push_cast at hly
  have rv0 : (0 : ℝ) < (vR : ℝ) := by exact_mod_cast hv0
  have rv2 : 2 * (vR : ℝ) ≤ 1 := by exact_mod_cast hv2
  have rc : 8 * (Hhi vR pR : ℝ) ≤ 1 - 2 * (vR : ℝ) := by exact_mod_cast hc
  have hHv : 0 ≤ H (vR : ℝ) := H_nonneg rv0.le (by linarith)
  have hcont : (8 : ℝ) * H (vR : ℝ) ≤ 1 * (1 - 2 * (vR : ℝ)) := by linarith
  have hvle : (vR : ℝ) ≤ radialContact 8 1 :=
    (le_radialContact_iff (by norm_num) (by norm_num) rv0.le (by linarith)).2 hcont
  have hlt : radialContact 8 1 < 1 / 2 := radialContact_lt_half (by norm_num) (by norm_num)
  refine (radialSlope_antitone rv0 hvle hlt).trans ?_
  -- bound radialSlope vR by the rational expression
  have hvc : (0 : ℝ) < 1 - (vR : ℝ) := by linarith
  have rk : (0 : ℝ) < (kapLoR : ℝ) := by exact_mod_cast hk
  have ekap : (kapLoR : ℝ) = -((pR.cx.hi : ℝ) + (pR.cy.hi : ℝ)) / 2 := by
    unfold kapLoR; push_cast; ring
  have hkap : (kapLoR : ℝ) ≤ kap (vR : ℝ) := by
    unfold kap
    rw [Real.log_mul rv0.ne' hvc.ne', ekap]
    linarith [hlx.2, hly.2]
  have ehn : (hnHiR : ℝ) = -(vR : ℝ) * (pR.cx.lo : ℝ) - (1 - (vR : ℝ)) * (pR.cy.lo : ℝ) := by
    unfold hnHiR; push_cast; ring
  have hhn' : hn (vR : ℝ) ≤ (hnHiR : ℝ) := by
    unfold hn
    rw [ehn]
    have a1 := mul_le_mul_of_nonneg_left hlx.1 rv0.le
    have a2 := mul_le_mul_of_nonneg_left hly.1 hvc.le
    linarith
  have hL := log2_bounds
  have hLpos : 0 < Real.log 2 := log_two_pos
  have hL0 : (0 : ℝ) < (L0 : ℝ) := L0_pos_real
  have hden : 2 * (L0 : ℝ) * (vR : ℝ) * (1 - (vR : ℝ)) * (kapLoR : ℝ) ≤
      2 * Real.log 2 * (vR : ℝ) * (1 - (vR : ℝ)) * kap (vR : ℝ) := by
    have h1 : 2 * (L0 : ℝ) * (vR : ℝ) * (1 - (vR : ℝ)) ≤ 2 * Real.log 2 * (vR : ℝ) * (1 - (vR : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hL.1 (show (0 : ℝ) ≤ 2 * (vR : ℝ) * (1 - (vR : ℝ)) by positivity)
      nlinarith
    exact mul_le_mul h1 hkap rk.le (by positivity)
  have hdpos : 0 < 2 * (L0 : ℝ) * (vR : ℝ) * (1 - (vR : ℝ)) * (kapLoR : ℝ) := by positivity
  have hnum0 : 0 ≤ (1 - 2 * (vR : ℝ)) * hn (vR : ℝ) :=
    mul_nonneg (by linarith) (hn_nonneg_of rv0 (by linarith))
  have hfrac : (1 - 2 * (vR : ℝ)) * hn (vR : ℝ) /
      (2 * Real.log 2 * (vR : ℝ) * (1 - (vR : ℝ)) * kap (vR : ℝ)) ≤
      (1 - 2 * (vR : ℝ)) * (hnHiR : ℝ) / (2 * (L0 : ℝ) * (vR : ℝ) * (1 - (vR : ℝ)) * (kapLoR : ℝ)) := by
    calc (1 - 2 * (vR : ℝ)) * hn (vR : ℝ) / (2 * Real.log 2 * (vR : ℝ) * (1 - (vR : ℝ)) * kap (vR : ℝ))
        ≤ (1 - 2 * (vR : ℝ)) * hn (vR : ℝ) /
            (2 * (L0 : ℝ) * (vR : ℝ) * (1 - (vR : ℝ)) * (kapLoR : ℝ)) :=
          div_le_div_of_nonneg_left hnum0 hdpos hden
      _ ≤ (1 - 2 * (vR : ℝ)) * (hnHiR : ℝ) /
            (2 * (L0 : ℝ) * (vR : ℝ) * (1 - (vR : ℝ)) * (kapLoR : ℝ)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhn' (by linarith)) hdpos.le
  have rval : ((Jhi vR pR + (1 - 2 * vR) * hnHiR / (2 * L0 * vR * (1 - vR) * kapLoR) : ℚ) : ℝ) ≤
      ((7664 / 1000 : ℚ) : ℝ) := Rat.cast_le.mpr hval
  push_cast at rval
  unfold radialSlope
  linarith

theorem radial_ratio_le_479 {x : ℝ} (hx : 8 ≤ x) :
    deriv (fun r => F r 1) x / (2 * x) ≤ 479 / 1000 := by
  have hm := antitoneOn_F_radius_ratio (by norm_num : (0 : ℝ) < 1)
    (show (8 : ℝ) ∈ Ioi 0 by norm_num) (show x ∈ Ioi 0 by change 0 < x; linarith) hx
  have he : deriv (fun r => F r 1) 8 / (2 * 8) ≤ 479 / 1000 := by
    have hd := deriv_F_eight_le
    rw [div_le_iff₀ (by norm_num)]
    linarith
  exact hm.trans he

/-- The archive's radial estimate (11): `radial loss ≤ (479/1000) q²/E` for `d ≥ 8E`. -/
theorem radial_average_loss_le_479 {d E : ℝ} (hE : 0 < E) (hd : 8 * E ≤ d) (q : ℝ) :
    (F |d - q| E + F |d + q| E) / 2 - F d E ≤ (479 / 1000) * (q ^ 2 / E) := by
  have hd0 : 0 < d := by linarith
  have hx : 8 ≤ d / E := (le_div_iff₀ hE).2 hd
  have hb := radial_ratio_le_479 hx
  have hh := F_average_difference_le hd0 hE q
  have heq : q ^ 2 / (2 * d) * deriv (fun r => F r E) d =
      (q ^ 2 / E) * (deriv (fun r => F r 1) (d / E) / (2 * (d / E))) := by
    rw [deriv_F_radius_normalize hd0 hE]
    field_simp
  have hp := mul_le_mul_of_nonneg_left hb (show 0 ≤ q ^ 2 / E by positivity)
  rw [heq] at hh
  calc
    _ ≤ (q ^ 2 / E) * (deriv (fun r => F r 1) (d / E) / (2 * (d / E))) := hh
    _ ≤ (q ^ 2 / E) * (479 / 1000) := hp
    _ = (479 / 1000) * (q ^ 2 / E) := by ring

end CKLaneN4

end


