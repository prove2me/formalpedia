-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
-- name    : ArdaRH65K_Turing121_EMZetaOfflineCheck
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:06:20.741079+00:00
-- url     : https://prove2.me/theorems/30c6737e-9e26-4e31-b3d5-6613a07aac8a
-- title:
--   EMZetaOfflineCheck certificate definitions
-- statement:
--   This bundle defines offline correction and remainder checks for zeta enclosures. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ArbEcon.Off.gpochG},\;\mathtt{ArbEcon.Off.gsumG},\;\mathtt{ArbEcon.Off.corrDataG},\;\mathtt{ArbEcon.Off.pnG}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineCheck.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
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

namespace ArbEcon

namespace Off

open ArbEcon.OrderK (betaN Lbeta  )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/

/-- `G_k = (q u)^k (σ + i t)_k`, `G_{k+1} = G_k · ((sN + k q) u + i tn q)`. -/
def gpochG (sN : ℤ) (q u tn : ℕ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 =>
    match gpochG sN q u tn k with
    | (x, y) => (x * ((sN + k * q) * u) - y * (tn * q), x * (tn * q) + y * ((sN + k * q) * u))





/-- `Σ_{i<j} βN_i · G_{i+1} · W^(M-1-i)`. -/
def gsumG (sN : ℤ) (q u tn : ℕ) (W : ℤ) (M : ℕ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | j + 1 => ((gsumG sN q u tn W M j).1 + betaN j * (gpochG sN q u tn (j + 1)).1 * W ^ (M - 1 - j),
              (gsumG sN q u tn W M j).2 + betaN j * (gpochG sN q u tn (j + 1)).2 * W ^ (M - 1 - j))



/-- The exact correction factor `emCorr K (σ + i t) N = (BreN + i BimN) / BD`, `σ = sN/q`,
    `t = tn/u`: returns `(BreN, BimN, BD)`. -/
def corrDataG (K : ℕ) (sN : ℤ) (q u tn N : ℕ) : ℤ × ℤ × ℤ :=
  let M := 2 * K - 1
  let W : ℤ := (q : ℤ) * u * N
  let q2 : ℤ := (sN - q) ^ 2 * (u : ℤ) ^ 2 + (tn : ℤ) ^ 2 * (q : ℤ) ^ 2
  let base : ℤ := Lbeta * W ^ M
  let S := gsumG sN q u tn W M M
  (2 * N * q * (u : ℤ) ^ 2 * (sN - q) * base + q2 * base + 2 * q2 * S.1,
   -(2 * N * (q : ℤ) ^ 2 * u * tn * base) + 2 * q2 * S.2,
   2 * q2 * base)



/-! ## B. The remainder numerator and `N^(-σ)`. -/

/-- `Π_{j<k} ((sN + j q)² u² + tn² q²)` (the `(q u)^(2k)`-scaled `‖(σ + i t)_k‖²`). -/
def pnG (sN : ℤ) (q u tn : ℕ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => pnG sN q u tn k * ((sN + k * q) ^ 2 * (u : ℤ) ^ 2 + (tn : ℤ) ^ 2 * (q : ℤ) ^ 2)





/-! ## C. The odd-saw remainder certificate, off the line. -/

/-- `(ok, EN, ED)`: `ok` checks `1 ≤ Rd`, `1 ≤ K`, `pnG(2K+1) ≤ Qp²`, `Rd^q N^b ≤ Rn^q N^a`,
    `0 < sN + 2Kq`; then `‖ζ(s) − emFinite K s N‖ ≤ EN/ED` (with `6.283184 < 2π`, `π < 3.141593`). -/
def remOddG (K a b q u tn N Qp Rn Rd : ℕ) : Bool × ℤ × ℤ :=
  let sN : ℤ := (a : ℤ) - b
  (Nat.ble 1 Rd && Nat.ble 1 K && decide (pnG sN q u tn (2 * K + 1) ≤ (Qp : ℤ) * Qp) &&
     Nat.ble (Rd ^ q * N ^ b) (Rn ^ q * N ^ a) && decide (0 < sN + 2 * K * q),
   2 * (6000000000000 * 2 ^ (2 * K - 1) + 9869606577649 - 6000000000000) * 1000000 ^ (2 * K + 1)
     * Qp * Rn * q,
   6000000000000 * 2 ^ (2 * K - 1) * 6283184 ^ (2 * K + 1) * ((q : ℤ) * u) ^ (2 * K + 1) * Rd
     * (N : ℤ) ^ (2 * K) * (sN + 2 * K * q))



/-! ## D. The ball: evaluator invariants + remainder + correction factor. -/







/-! ## E. The kernel checker and its soundness. -/

/-- The final-inequality core for ANY remainder bound `EN/ED` (multiplied through by `D·BD·ED`). -/
def checkCoreG (P tq tn K : ℕ) (sN : ℤ) (q N : ℕ) (x1 x2 : Acc) (D : ℕ)
    (reLo reHi imLo imHi EN ED : ℤ) : Bool :=
  let u := 2 ^ tq
  let cd := corrDataG K sN q u tn N
  let BreN := cd.1
  let BimN := cd.2.1
  let BD := cd.2.2
  let two : ℤ := 2 ^ P
  let a1 : ℤ := (x1.reP : ℤ) - x1.reN
  let b1 : ℤ := (x1.imP : ℤ) - x1.imN
  let za : ℤ := ((x2.reP : ℤ) - x2.reN) - a1
  let zb : ℤ := ((x2.imP : ℤ) - x2.imN) - b1
  let zra : ℤ := (x2.reR : ℤ) + x1.reR
  let zrb : ℤ := (x2.imR : ℤ) + x1.imR
  let aB : ℤ := BreN.natAbs
  let aC : ℤ := BimN.natAbs
  let CreN := a1 * BD + za * BreN - zb * BimN
  let RreN := (x1.reR : ℤ) * BD + zra * aB + zrb * aC
  let CimN := b1 * BD + za * BimN + zb * BreN
  let RimN := (x1.imR : ℤ) * BD + zra * aC + zrb * aB
  let DD : ℤ := D
  Nat.ble 1 K && Nat.ble K 6 && Nat.ble 2 N && Nat.ble 1 D && decide (0 < ED) && Nat.ble 1 q &&
    Nat.ble 1 tn &&
    decide (reLo * two * BD * ED ≤ DD * ED * (CreN - RreN) - DD * BD * EN * two) &&
    decide (DD * ED * (CreN + RreN) + DD * BD * EN * two ≤ reHi * two * BD * ED) &&
    decide (imLo * two * BD * ED ≤ DD * ED * (CimN - RimN) - DD * BD * EN * two) &&
    decide (DD * ED * (CimN + RimN) + DD * BD * EN * two ≤ imHi * two * BD * ED)

/-- **The off-line kernel checker**: the odd-saw remainder certificate `remOddG` and the core. -/
def checkG (c : Cfg) (o : OCfg) (K N : ℕ) (x1 x2 : Acc) (D : ℕ) (reLo reHi imLo imHi : ℤ)
    (Qp Rn Rd : ℕ) : Bool :=
  let R := remOddG K o.a o.b o.q (2 ^ c.tq) c.tn N Qp Rn Rd
  R.1 && checkCoreG c.P c.tq c.tn K ((o.a : ℤ) - o.b) o.q N x1 x2 D reLo reHi imLo imHi R.2.1 R.2.2







end Off

end ArbEcon


def ArdaRH65K_Turing121_EMZetaOfflineCheck : Nat := 0


