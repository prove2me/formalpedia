-- Prove2me | solution 1 for ArbEcon.OrderK.valid64
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:38:47.084304+00:00
-- url     : https://prove2.me/submissions/7abfbab9-d7d9-47bf-8210-ca1efcbca29e

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
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

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.OrderK
end ArbEcon.OrderK
open ArbEcon.OrderK

/-! ## A. The P = 64 configuration (`EMZetaHighCfg64.cfg64`), validated once for every height. -/


theorem solution (tn tq : ℕ) (t : ℝ) (ht : t = (tn : ℝ) / 2 ^ tq) : Valid (cfg64 tn tq) t 9 where
  one_eq := by show (18446744073709551616 : ℕ) = 2 ^ 64; norm_num
  two1_eq := by show (36893488147419103232 : ℕ) = 2 ^ (64 + 1); norm_num
  oneSq_eq := by show (340282366920938463463374607431768211456 : ℕ) = 2 ^ (2 * 64); norm_num
  t_eq := ht
  pi_ball := by
    show |Real.pi / 2 * 2 ^ (64 : ℕ) - ((28976077832308491369 : ℕ) : ℝ)| ≤ ((2 : ℕ) : ℝ)
    have h1 := Real.pi_gt_d20
    have h2 := Real.pi_lt_d20
    rw [abs_le]; constructor <;> norm_num <;> linarith
  umax_le := by show (14987979559889010688 : ℕ) * 16 ≤ 13 * 2 ^ 64; norm_num
  dcos_eq := by
    show [5644703686555122794496, 4427218577690292387840, 3357307421415138394112,
      2434970217729660813312, 1660206966633859645440, 1033017668127734890496, 553402322211286548480,
      221360928884514619392, 36893488147419103232] = (divList fcos 9).map (fun d : ℕ => 18446744073709551616 * d)
    decide
  dsin_eq := by
    show [6308786473208666652672, 5017514388048998039552, 3873816255479005839360,
      2877692075498690052096, 2029141848108050677760, 1328165573307087716352, 774763251095801167872,
      368934881474191032320, 110680464442257309696] = (divList fsin 9).map (fun d : ℕ => 18446744073709551616 * d)
    decide
  tau_ok := by
    show (2 : ℝ) ^ (64 : ℕ) * ArbEcon.taylorBnd 9 ≤ ((1 : ℕ) : ℝ)
    unfold ArbEcon.taylorBnd; norm_num [Nat.factorial]
  hc_eq := fun _ => rfl
  hs_eq := fun _ => rfl
  lnf_eq := fun _ => rfl
