-- Prove2me | solution 1 for ArbEcon.Off.checkCoreG_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:58:23.468176+00:00
-- url     : https://prove2.me/submissions/9036c732-25a7-4a50-a6c0-70742d834d14

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ArbEcon_Off_corr_eqG
import Theorems.Thm_ArbEcon_Off_zeta_ballG
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh

/-  EMZetaOfflineCheck.lean -- lane offline: the KERNEL-ONLY assembly of an order-(2K+1)
    Euler-Maclaurin enclosure of ζ(σ + i t) at a rational `σ = (a - b)/q` (any sign, `σ > -2K`) and a
    dyadic `t = tn / 2^tq > 0`.

      * `gpochG`, `pochRI_eq_gpochG`  -- the Gaussian-integer rising factorial
                                         `(q u)^k (σ + i t)_k` (`u = 2^tq`);
      * `corrDataG`, `corr_eqG`       -- the exact correction factor `emCorr K (σ + i t) N` as
                                         `(BreN + i BimN) / BD` in integers;
      * `pnG`, `pochNormSq_eq_pnG`    -- the remainder numerator `Π_{j<k} ((sN + j q)² u² + tn² q²)`;
      * `rpow_neg_le_of_pow`          -- `N^(-σ) ≤ Rn/Rd` from `Rd^q N^b ≤ Rn^q N^a`;
      * `remOddG`, `remOddG_sound`    -- the odd-saw remainder of `EMOff.em_zeta_orderK_enclosure_odd_ext`
                                         (valid off the line, `σ > -2K`) as `EN/ED`;
      * `zeta_ballG`                  -- the evaluator balls after `N-1` and `N` terms plus any remainder
                                         bound give balls for `Re ζ(s)`, `Im ζ(s)`;
      * `checkG`, `checkG_sound`      -- ONE Boolean checker (run by `decide +kernel`) and its
                                         soundness: `lo/D ≤ Re ζ(σ + i t) ≤ hi/D`, same for `Im`.

    conjecture1_proved = False.  Finite interval arithmetic at one point; nothing about RH.
-/




open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.Off
end ArbEcon.Off
open ArbEcon.Off

open ArbEcon.OrderK (betaN Lbeta  )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/















/-! ## B. The remainder numerator and `N^(-σ)`. -/







/-! ## C. The odd-saw remainder certificate, off the line. -/





/-! ## D. The ball: evaluator invariants + remainder + correction factor. -/







/-! ## E. The kernel checker and its soundness. -/






set_option maxHeartbeats 1000000
theorem solution (P tq tn K : ℕ) (a b q N : ℕ) (σ t : ℝ) (hσ : σ = ((a : ℝ) - b) / q)
    (ht : t = (tn : ℝ) / 2 ^ tq) (x1 x2 : Acc)
    (h1 : AccOK P (psumK σ t 0 (N - 1)) x1) (h2 : AccOK P (psumK σ t 0 N) x2) (D : ℕ)
    (reLo reHi imLo imHi EN ED : ℤ)
    (hE : ‖riemannZeta (sOfG σ t) - emFinite K (sOfG σ t) N‖ ≤ (EN : ℝ) / (ED : ℝ))
    (hc : checkCoreG P tq tn K ((a : ℤ) - b) q N x1 x2 D reLo reHi imLo imHi EN ED = true) :
    ((reLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).re ∧ (riemannZeta (sOfG σ t)).re ≤ (reHi : ℝ) / D) ∧
    ((imLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).im ∧ (riemannZeta (sOfG σ t)).im ≤ (imHi : ℝ) / D) := by
  simp only [checkCoreG, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hK1, hK6⟩, hN2⟩, hD1⟩, hEDpos⟩, hq1⟩, htn1⟩, hreLo⟩, hreHi⟩, himLo⟩, himHi⟩ := hc
  set u : ℕ := 2 ^ tq with hudef
  have hu : 0 < u := Nat.two_pow_pos _
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have ht' : t = (tn : ℝ) / u := by rw [ht, hudef]; push_cast; ring
  have hσ' : σ = (((a : ℤ) - b : ℤ) : ℝ) / q := by rw [hσ]; push_cast; ring
  obtain ⟨hcre, hcim⟩ := corr_eqG K ((a : ℤ) - b) q u tn N hK1 hK6 (by omega) hu (by omega)
    (by omega) σ t hσ' ht'
  set cd := corrDataG K ((a : ℤ) - b) q u tn N with hcd
  set BreN := cd.1 with hBreN
  set BimN := cd.2.1 with hBimN
  set BD := cd.2.2 with hBD
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have htnR : (0 : ℝ) < tn := by exact_mod_cast (show 0 < tn by omega)
  have hBDpos : (0 : ℝ) < (BD : ℝ) := by
    have e : (BD : ℝ) = 2 * (((((a : ℤ) - b : ℤ) : ℝ) - q) ^ 2 * (u : ℝ) ^ 2 + (tn : ℝ) ^ 2 * (q : ℝ) ^ 2)
        * ((Lbeta : ℝ) * ((q : ℝ) * u * N) ^ (2 * K - 1)) := by
      simp only [hBD, hcd, corrDataG]; push_cast; ring
    rw [e]
    have hL : (0 : ℝ) < (Lbeta : ℝ) := by norm_num [Lbeta]
    positivity
  have hEDR : (0 : ℝ) < (ED : ℝ) := by exact_mod_cast hEDpos
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD1
  have hP : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have haRe : |(BreN : ℝ) / BD| ≤ ((BreN.natAbs : ℤ) : ℝ) / BD := by
    rw [abs_div, abs_of_pos hBDpos, Int.natCast_natAbs, Int.cast_abs]
  have haIm : |(BimN : ℝ) / BD| ≤ ((BimN.natAbs : ℤ) : ℝ) / BD := by
    rw [abs_div, abs_of_pos hBDpos, Int.natCast_natAbs, Int.cast_abs]
  have hball := zeta_ballG P σ t K N hN2 x1 x2 h1 h2 _ hE _ _ hcre hcim
  simp only at hball
  obtain ⟨hbre, hbim⟩ := hball
  have hBabs : |(BreN : ℝ) / BD| = |(BreN : ℝ)| / BD := by rw [abs_div, abs_of_pos hBDpos]
  have hCabs : |(BimN : ℝ) / BD| = |(BimN : ℝ)| / BD := by rw [abs_div, abs_of_pos hBDpos]
  rw [hBabs, hCabs] at hbre hbim
  rw [abs_le] at hbre hbim
  have hc3 : (0 : ℝ) < (D : ℝ) * BD * ED := by positivity
  have hk : (0 : ℝ) < 2 ^ P * BD * ED := by positivity
  have cast1 := (Int.cast_le (R := ℝ)).mpr hreLo
  have cast2 := (Int.cast_le (R := ℝ)).mpr hreHi
  have cast3 := (Int.cast_le (R := ℝ)).mpr himLo
  have cast4 := (Int.cast_le (R := ℝ)).mpr himHi
  push_cast at cast1 cast2 cast3 cast4
  have hBDne : (BD : ℝ) ≠ 0 := ne_of_gt hBDpos
  have hEDne : (ED : ℝ) ≠ 0 := ne_of_gt hEDR
  have id_re_lo : (D : ℝ) * ED * ((((x1.reP : ℝ) - x1.reN) * BD + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * BreN - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * BimN) - ((x1.reR : ℝ) * BD + ((x2.reR : ℝ) + x1.reR) * |(BreN : ℝ)| + ((x2.imR : ℝ) + x1.imR) * |(BimN : ℝ)|)) - D * BD * EN * 2 ^ P
      = (D * BD * ED) * ((((x1.reP : ℝ) - x1.reN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BreN : ℝ) / BD) - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BimN : ℝ) / BD)) - ((x1.reR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BreN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BimN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P))) := by
    field_simp; ring
  have id_re_hi : (D : ℝ) * ED * ((((x1.reP : ℝ) - x1.reN) * BD + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * BreN - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * BimN) + ((x1.reR : ℝ) * BD + ((x2.reR : ℝ) + x1.reR) * |(BreN : ℝ)| + ((x2.imR : ℝ) + x1.imR) * |(BimN : ℝ)|)) + D * BD * EN * 2 ^ P
      = (D * BD * ED) * ((((x1.reP : ℝ) - x1.reN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BreN : ℝ) / BD) - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BimN : ℝ) / BD)) + ((x1.reR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BreN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BimN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P))) := by
    field_simp; ring
  have id_im_lo : (D : ℝ) * ED * ((((x1.imP : ℝ) - x1.imN) * BD + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * BimN + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * BreN) - ((x1.imR : ℝ) * BD + ((x2.reR : ℝ) + x1.reR) * |(BimN : ℝ)| + ((x2.imR : ℝ) + x1.imR) * |(BreN : ℝ)|)) - D * BD * EN * 2 ^ P
      = (D * BD * ED) * ((((x1.imP : ℝ) - x1.imN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BimN : ℝ) / BD) + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BreN : ℝ) / BD)) - ((x1.imR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BimN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BreN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P))) := by
    field_simp; ring
  have id_im_hi : (D : ℝ) * ED * ((((x1.imP : ℝ) - x1.imN) * BD + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * BimN + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * BreN) + ((x1.imR : ℝ) * BD + ((x2.reR : ℝ) + x1.reR) * |(BimN : ℝ)| + ((x2.imR : ℝ) + x1.imR) * |(BreN : ℝ)|)) + D * BD * EN * 2 ^ P
      = (D * BD * ED) * ((((x1.imP : ℝ) - x1.imN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BimN : ℝ) / BD) + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BreN : ℝ) / BD)) + ((x1.imR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BimN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BreN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P))) := by
    field_simp; ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [div_le_iff₀ hDR]
    have hlow : (((x1.reP : ℝ) - x1.reN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BreN : ℝ) / BD) - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BimN : ℝ) / BD)) - ((x1.reR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BreN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BimN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P)) ≤ (riemannZeta (sOfG σ t)).re * 2 ^ P := by linarith [hbre.1]
    have hm := mul_le_mul_of_nonneg_left hlow hc3.le
    have : (reLo : ℝ) * (2 ^ P * BD * ED) ≤ (riemannZeta (sOfG σ t)).re * D * (2 ^ P * BD * ED) := by
      linarith [cast1, id_re_lo, hm]
    exact le_of_mul_le_mul_right this hk
  · rw [le_div_iff₀ hDR]
    have hup : (riemannZeta (sOfG σ t)).re * 2 ^ P ≤ (((x1.reP : ℝ) - x1.reN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BreN : ℝ) / BD) - (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BimN : ℝ) / BD)) + ((x1.reR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BreN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BimN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P)) := by linarith [hbre.2]
    have hm := mul_le_mul_of_nonneg_left hup hc3.le
    have : (riemannZeta (sOfG σ t)).re * D * (2 ^ P * BD * ED) ≤ (reHi : ℝ) * (2 ^ P * BD * ED) := by
      linarith [cast2, id_re_hi, hm]
    exact le_of_mul_le_mul_right this hk
  · rw [div_le_iff₀ hDR]
    have hlow : (((x1.imP : ℝ) - x1.imN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BimN : ℝ) / BD) + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BreN : ℝ) / BD)) - ((x1.imR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BimN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BreN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P)) ≤ (riemannZeta (sOfG σ t)).im * 2 ^ P := by linarith [hbim.1]
    have hm := mul_le_mul_of_nonneg_left hlow hc3.le
    have : (imLo : ℝ) * (2 ^ P * BD * ED) ≤ (riemannZeta (sOfG σ t)).im * D * (2 ^ P * BD * ED) := by
      linarith [cast3, id_im_lo, hm]
    exact le_of_mul_le_mul_right this hk
  · rw [le_div_iff₀ hDR]
    have hup : (riemannZeta (sOfG σ t)).im * 2 ^ P ≤ (((x1.imP : ℝ) - x1.imN) + (((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)) * ((BimN : ℝ) / BD) + (((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)) * ((BreN : ℝ) / BD)) + ((x1.imR : ℝ) + ((x2.reR : ℝ) + x1.reR) * (|(BimN : ℝ)| / BD) + ((x2.imR : ℝ) + x1.imR) * (|(BreN : ℝ)| / BD) + ((EN : ℝ) / ED * 2 ^ P)) := by linarith [hbim.2]
    have hm := mul_le_mul_of_nonneg_left hup hc3.le
    have : (riemannZeta (sOfG σ t)).im * D * (2 ^ P * BD * ED) ≤ (imHi : ℝ) * (2 ^ P * BD * ED) := by
      linarith [cast4, id_im_hi, hm]
    exact le_of_mul_le_mul_right this hk
