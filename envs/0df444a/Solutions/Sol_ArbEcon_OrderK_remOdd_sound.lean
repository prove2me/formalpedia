-- Prove2me | solution 1 for ArbEcon.OrderK.remOdd_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:14:13.587975+00:00
-- url     : https://prove2.me/submissions/2561207f-6735-4592-bd28-814c7577642c

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
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
import Theorems.Thm_ZetaReflection_EMHigh_em_line_remainder_odd_le
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  EMZetaHighCheck.lean -- a KERNEL-ONLY assembly for the order-(2K+1) Euler-Maclaurin enclosure
    of ζ(1/2 + i t) (lane emhigh, production format).

    `EMZetaHighEval.zetaK_re_bounds` turns the evaluator invariants into Re/Im ζ bounds, but an
    instance then discharges its rational side conditions (the correction factor `B_K(t, N)`, the
    remainder constant, the final inequalities) with `norm_num` on 60-digit rationals: about 3 s of
    tactic interpretation and 1.3 MB of proof term per evaluation.  At the h280000 scale (445,947
    sign evaluations) that is about 400 core-hours of elaboration and 0.6 TB of oleans.

    This file replaces all of it by ONE Boolean checker `checkK`, run by `decide +kernel`, over plain
    `Nat`/`Int` arithmetic, and ONE soundness theorem `checkK_sound`, proved once:
      * `valid64`                  -- the P = 64 evaluator configuration `EMZetaHighCfg64.cfg64`
                                      (lnbig = sqbig = 256) as a function of the height `t = tn / 2^tq`,
                                      validated ONCE for all heights (no per-instance `norm_num`).
      * `betaN`, `Lbeta`, `betaN_spec` -- `B_{i+2}/(i+2)! = betaN i / Lβ`, `Lβ = 2730·12!`, `i ≤ 10`.
      * `gpoch`, `pochRI_eq_gpoch`  -- the Gaussian-integer rising factorial `(2u)^k (1/2 + i tn/u)_k`.
      * `corrData`, `corr_eq`       -- the exact correction factor `emCorr K (1/2 + i t) N` as
                                      `(BreN + i BimN) / BD` with integers computed in the kernel.
      * `pnK`, `pochNormSq_eq_pnK`  -- the remainder numerator `Π_{j<k} ((2j+1)² u² + 4 tn²)`.
      * `remEven`, `remOdd` (+ `_sound`) -- the remainder as `EN/ED` in integers, even-saw
                                      (`em_line_remainder_le`) or odd-saw (`em_line_remainder_odd_le`,
                                      π replaced by `3.141592 < π < 3.141593`, about 7 percent fewer terms).
      * `checkCore`, `checkCore_sound` -- the four final inequalities for ANY remainder `EN/ED`.
      * `checkK`, `checkK_sound`    -- the checker (`odd` flag) and its soundness: `checkK … = true`
                                      gives `reLo/D ≤ Re ζ(1/2+it) ≤ reHi/D` and the same for Im.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace OrderK

/-! ## A. The P = 64 configuration (`EMZetaHighCfg64.cfg64`), validated once for every height. -/



/-! ## B. Bernoulli data over one common denominator. -/







/-! ## C. The correction factor in exact integer arithmetic. -/















/-! ## D. The remainder numerator. -/



theorem pochNormSq_eq_pnK (u tn : ℕ) (hu : 0 < u) (t : ℝ) (ht : t = (tn : ℝ) / u) (k : ℕ) :
    pochNormSq (1 / 2) t k = (pnK u tn k : ℝ) / (2 * u) ^ (2 * k) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  induction k with
  | zero => simp [pochNormSq, pnK]
  | succ k ih =>
    rw [pochNormSq, ih, pnK]
    push_cast
    subst ht
    have hne : (2 * (u : ℝ)) ^ (2 * k) ≠ 0 := by positivity
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    field_simp
    ring

/-! ## E. The remainder certificates (even and odd saw forms). -/









/-! ## F. The checker and its soundness. -/











end OrderK

end ArbEcon


/-  EMZetaHighCheck.lean -- a KERNEL-ONLY assembly for the order-(2K+1) Euler-Maclaurin enclosure
    of ζ(1/2 + i t) (lane emhigh, production format).

    `EMZetaHighEval.zetaK_re_bounds` turns the evaluator invariants into Re/Im ζ bounds, but an
    instance then discharges its rational side conditions (the correction factor `B_K(t, N)`, the
    remainder constant, the final inequalities) with `norm_num` on 60-digit rationals: about 3 s of
    tactic interpretation and 1.3 MB of proof term per evaluation.  At the h280000 scale (445,947
    sign evaluations) that is about 400 core-hours of elaboration and 0.6 TB of oleans.

    This file replaces all of it by ONE Boolean checker `checkK`, run by `decide +kernel`, over plain
    `Nat`/`Int` arithmetic, and ONE soundness theorem `checkK_sound`, proved once:
      * `valid64`                  -- the P = 64 evaluator configuration `EMZetaHighCfg64.cfg64`
                                      (lnbig = sqbig = 256) as a function of the height `t = tn / 2^tq`,
                                      validated ONCE for all heights (no per-instance `norm_num`).
      * `betaN`, `Lbeta`, `betaN_spec` -- `B_{i+2}/(i+2)! = betaN i / Lβ`, `Lβ = 2730·12!`, `i ≤ 10`.
      * `gpoch`, `pochRI_eq_gpoch`  -- the Gaussian-integer rising factorial `(2u)^k (1/2 + i tn/u)_k`.
      * `corrData`, `corr_eq`       -- the exact correction factor `emCorr K (1/2 + i t) N` as
                                      `(BreN + i BimN) / BD` with integers computed in the kernel.
      * `pnK`, `pochNormSq_eq_pnK`  -- the remainder numerator `Π_{j<k} ((2j+1)² u² + 4 tn²)`.
      * `remEven`, `remOdd` (+ `_sound`) -- the remainder as `EN/ED` in integers, even-saw
                                      (`em_line_remainder_le`) or odd-saw (`em_line_remainder_odd_le`,
                                      π replaced by `3.141592 < π < 3.141593`, about 7 percent fewer terms).
      * `checkCore`, `checkCore_sound` -- the four final inequalities for ANY remainder `EN/ED`.
      * `checkK`, `checkK_sound`    -- the checker (`odd` flag) and its soundness: `checkK … = true`
                                      gives `reLo/D ≤ Re ζ(1/2+it) ≤ reHi/D` and the same for Im.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.OrderK
end ArbEcon.OrderK
open ArbEcon.OrderK

/-! ## A. The P = 64 configuration (`EMZetaHighCfg64.cfg64`), validated once for every height. -/



/-! ## B. Bernoulli data over one common denominator. -/







/-! ## C. The correction factor in exact integer arithmetic. -/















/-! ## D. The remainder numerator. -/





/-! ## E. The remainder certificates (even and odd saw forms). -/







theorem solution (K N : ℕ) (hK1 : 1 ≤ K) (hN : 1 ≤ N) (u tn : ℕ) (hu : 0 < u)
    (t : ℝ) (ht : t = (tn : ℝ) / u) (Q r : ℕ) (hok : (remOdd K u tn N Q r).1 = true) :
    ‖riemannZeta (sOf t) - emFinite K (sOf t) N‖
      ≤ ((remOdd K u tn N Q r).2.1 : ℝ) / ((remOdd K u tn N Q r).2.2 : ℝ) := by
  simp only [remOdd, Bool.and_eq_true, Nat.ble_eq] at hok ⊢
  obtain ⟨⟨hr1, hrN⟩, hQ⟩ := hok
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
  set Qr : ℝ := (Q : ℝ) / (2 * u) ^ (2 * K + 1) with hQr
  have hQr0 : 0 ≤ Qr := by positivity
  have hpn := pochNormSq_eq_pnK u tn hu t ht (2 * K + 1)
  have hQsq : pochNormSq (1 / 2) t (2 * K + 1) ≤ Qr ^ 2 := by
    rw [hpn, hQr, div_pow, ← pow_mul]
    have h2 : (0 : ℝ) < (2 * (u : ℝ)) ^ ((2 * K + 1) * 2) := by positivity
    rw [show 2 * (2 * K + 1) = (2 * K + 1) * 2 by ring]
    apply div_le_div_of_nonneg_right _ h2.le
    have : (pnK u tn (2 * K + 1) : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by exact_mod_cast hQ
    push_cast at this; nlinarith [this]
  have hrem := em_line_remainder_odd_le K hK1 t (N := N) hN Qr hQr0 hQsq r hr1
    (by rw [pow_two]; exact hrN)
  have hsOf : sOf t = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := rfl
  rw [hsOf]
  refine le_trans hrem ?_
  -- replace π by the rational brackets 6283184/10^6 < 2π, π < 3141593/10^6
  have hlo : (6283184 : ℝ) / 1000000 ≤ 2 * π := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hhi : π ≤ (3141593 : ℝ) / 1000000 := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have hpipos : (0 : ℝ) < π := Real.pi_pos
  have hK2 : ((2 * K + 1 : ℕ) : ℝ) - 1 / 2 = (4 * (K : ℝ) + 1) / 2 := by push_cast; ring
  rw [hK2]
  have h4K : (0 : ℝ) < 4 * (K : ℝ) + 1 := by positivity
  have hden0 : (0 : ℝ) < (N : ℝ) ^ (2 * K) * r := by positivity
  have h2k : (0 : ℝ) < (2 : ℝ) ^ (2 * K - 1) := by positivity
  have hpi2 : π ^ 2 ≤ ((3141593 : ℝ) / 1000000) ^ 2 := by
    exact pow_le_pow_left₀ hpipos.le hhi 2
  have hnum0 : 0 ≤ 1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1) := by
    have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
    positivity
  calc 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) * Qr
        / ((N : ℝ) ^ (2 * K) * r) / ((4 * (K : ℝ) + 1) / 2)
      ≤ 2 * (1 + (((3141593 : ℝ) / 1000000) ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
          / ((6283184 : ℝ) ^ (2 * K + 1) / 1000000 ^ (2 * K + 1)) * Qr
          / ((N : ℝ) ^ (2 * K) * r) / ((4 * (K : ℝ) + 1) / 2) := by
        rw [← div_pow]
        gcongr
    _ = _ := by
        rw [hQr]
        push_cast
        field_simp
        ring
