-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
-- name    : ArdaRH65K_Turing121_EMZetaHighCheck
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:06:00.531772+00:00
-- url     : https://prove2.me/theorems/a72ca223-2e6d-44f0-b58c-0eadc9306c9c
-- title:
--   EMZetaHighCheck certificate definitions
-- statement:
--   This bundle defines fixed-point data and checks for higher-order zeta enclosures. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ArbEcon.OrderK.Lbeta},\;\mathtt{ArbEcon.OrderK.betaN},\;\mathtt{ArbEcon.OrderK.gpoch},\;\mathtt{ArbEcon.OrderK.gsum}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaHighCheck.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
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

/-- `Lβ = 2730 · 12!`, a common denominator of `B_{i+2}/(i+2)!` for `i ≤ 10`. -/
def Lbeta : ℕ := 1307674368000

/-- `B_{i+2}/(i+2)! = betaN i / Lβ` (`i ≤ 10`); odd Bernoulli numbers past `B_1` vanish. -/
def betaN : ℕ → ℤ
  | 0 => 108972864000
  | 2 => -1816214400
  | 4 => 43243200
  | 6 => -1081080
  | 8 => 27300
  | 10 => -691
  | _ => 0



/-! ## C. The correction factor in exact integer arithmetic. -/

/-- Gaussian-integer rising factorial: `G_k = (2u)^k (1/2 + i tn/u)_k` with `U = u`, `T2 = 2 tn`
    (`G_{k+1} = G_k · ((2k+1)U + i T2)`). -/
def gpoch (U T2 : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 =>
    match gpoch U T2 k with
    | (x, y) => (x * ((2 * k + 1) * U) - y * T2, x * T2 + y * ((2 * k + 1) * U))





/-- `Σ_{i<j} βN_i · G_{i+1} · W^(M-1-i)` (real and imaginary parts). -/
def gsum (U T2 W : ℤ) (M : ℕ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | j + 1 => ((gsum U T2 W M j).1 + betaN j * (gpoch U T2 (j + 1)).1 * W ^ (M - 1 - j),
              (gsum U T2 W M j).2 + betaN j * (gpoch U T2 (j + 1)).2 * W ^ (M - 1 - j))



/-- The exact correction factor `emCorr K (1/2 + i tn/u) N = (BreN + i BimN) / BD`:
    returns `(BreN, BimN, BD)`. -/
def corrData (K u tn N : ℕ) : ℤ × ℤ × ℤ :=
  let U : ℤ := u
  let T2 : ℤ := 2 * tn
  let M := 2 * K - 1
  let W : ℤ := 2 * u * N
  let q : ℤ := U * U + T2 * T2
  let base : ℤ := Lbeta * W ^ M
  let S := gsum U T2 W M M
  (-(4 * u * N) * U * base + q * base + 2 * q * S.1,
   -(4 * u * N) * T2 * base + 2 * q * S.2,
   2 * q * base)



/-! ## D. The remainder numerator. -/

/-- `Π_{j<k} ((2j+1)² u² + 4 tn²)`. -/
def pnK (u tn : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => pnK u tn k * ((2 * k + 1) ^ 2 * u ^ 2 + 4 * tn ^ 2)



/-! ## E. The remainder certificates (even and odd saw forms). -/



/-- Odd-saw remainder certificate, with `6.283184 < 2π` and `π < 3.141593` (Mathlib
    `pi_gt_d6`/`pi_lt_d6`): `E ≤ 4 A 1000000^(2K+1) Q / (6·10^12 2^(2K−1) 6283184^(2K+1) (2u)^(2K+1) N^(2K)
    r (4K+1))`, `A = 6·10^12 2^(2K−1) + 3141593² − 6·10^12` (`ok`: `0 < r`, `r² ≤ N`,
    `pnK(2K+1) ≤ Q²`). -/
def remOdd (K u tn N Q r : ℕ) : Bool × ℤ × ℤ :=
  (Nat.ble 1 r && Nat.ble (r * r) N && Nat.ble (pnK u tn (2 * K + 1)) (Q * Q),
   4 * (6000000000000 * 2 ^ (2 * K - 1) + 9869606577649 - 6000000000000) * 1000000 ^ (2 * K + 1) * Q,
   6000000000000 * 2 ^ (2 * K - 1) * 6283184 ^ (2 * K + 1) * (2 * u) ^ (2 * K + 1) * N ^ (2 * K)
     * r * (4 * K + 1))





/-! ## F. The checker and its soundness. -/











end OrderK

end ArbEcon


def ArdaRH65K_Turing121_EMZetaHighCheck : Nat := 0


