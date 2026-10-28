-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
-- name    : ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:07:53.652888+00:00
-- url     : https://prove2.me/theorems/20cfc7cb-5626-4fb1-8ec5-2f548907d0d5
-- title:
--   EMZetaOfflineSlabCheck certificate definitions
-- statement:
--   This bundle defines finite arithmetic checks for the rectangular-cell error budgets. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ArbEcon.Off.wData},\;\mathtt{ArbEcon.Off.wUpper},\;\mathtt{ArbEcon.Off.sumM},\;\mathtt{ArbEcon.Off.cellRHS}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineSlabCheck.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
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
/-  EMZetaOfflineSlabCheck.lean -- lane offline: the KERNEL checker of a zero-free cell.

    The off-line evaluator run at a center `c = σc + i tc` with `p + 1` accumulators gives, after
    `N - 1` and `N` terms, balls of `S_k = Σ_{n<N} (log n)^k n^(-c)` and of `S_k + (log N)^k N^(-c)`.
    With the exact correction factor `emCorr K c N = (BreN + i BimN)/BD` (`corrDataG`) they give balls
    of the Taylor weights `W_k = S_k + (log N)^k N^(-c) emCorr K c N` of `EMZetaOfflineSlab`.

      * `wData`, `wball_sound`  -- the ball of `W_k`, scaled by `2^P BD`;
      * `sumM`, `sumM_sound`    -- `Σ_{k≥1} ‖W_k‖ rn^k rd^(p-k) (p!/k!)` from above;
      * `checkCell`, `checkCell_sound` -- ONE Boolean check (run by `decide +kernel`) proving
                                   `Σ_{k=1}^p ‖W_k‖ r^k/k! + FN/FD < ‖W_0‖`, `r = rn/rd`, the
                                   hypothesis `hmain` of `zeta_ne_zero_of_cell`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing about RH.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

/-! ## A. The Taylor weights from the evaluator's partial sums. -/



/-! ## B. The ball of a weight. -/

/-- `(CreN, CimN, RreN, RimN)`: the ball of `A1 + (A2 - A1)(BreN + i BimN)/BD`, scaled by `2^P BD`,
    from the balls `x1 ∋ A1`, `x2 ∋ A2`. -/
def wData (BreN BimN BD : ℤ) (x1 x2 : Acc) : ℤ × ℤ × ℤ × ℤ :=
  (((x1.reP : ℤ) - x1.reN) * BD + ((((x2.reP : ℤ) - x2.reN) - ((x1.reP : ℤ) - x1.reN))) * BreN
      - ((((x2.imP : ℤ) - x2.imN) - ((x1.imP : ℤ) - x1.imN))) * BimN,
   ((x1.imP : ℤ) - x1.imN) * BD + ((((x2.reP : ℤ) - x2.reN) - ((x1.reP : ℤ) - x1.reN))) * BimN
      + ((((x2.imP : ℤ) - x2.imN) - ((x1.imP : ℤ) - x1.imN))) * BreN,
   (x1.reR : ℤ) * BD + ((x2.reR : ℤ) + x1.reR) * (BreN.natAbs : ℤ) + ((x2.imR : ℤ) + x1.imR) * (BimN.natAbs : ℤ),
   (x1.imR : ℤ) * BD + ((x2.reR : ℤ) + x1.reR) * (BimN.natAbs : ℤ) + ((x2.imR : ℤ) + x1.imR) * (BreN.natAbs : ℤ))

/-- The upper bound `|CreN| + RreN + |CimN| + RimN` of `‖W‖ 2^P BD`. -/
def wUpper (d : ℤ × ℤ × ℤ × ℤ) : ℤ := (d.1.natAbs : ℤ) + d.2.2.1 + (d.2.1.natAbs : ℤ) + d.2.2.2





/-! ## C. The weighted sum over `k ≥ 1`. -/

/-- `Σ_{j ≥ k} wUpper(W_j) rn^j rd^(p-j) (p!/j!)` over the paired accumulator lists. -/
def sumM (BreN BimN BD : ℤ) (rn rd p : ℕ) : ℕ → List Acc → List Acc → ℤ
  | k, x1 :: xs1, x2 :: xs2 =>
    wUpper (wData BreN BimN BD x1 x2) * (rn : ℤ) ^ k * (rd : ℤ) ^ (p - k) * ((p ! / k ! : ℕ) : ℤ)
      + sumM BreN BimN BD rn rd p (k + 1) xs1 xs2
  | _, _, _ => 0



/-! ## D. The cell checker. -/

/-- The right side `(R0re + R0im) T + (Σ_{k≥1} …) FD + FN 2^P BD rd^p p!` of the cell check,
    `T = rd^p p! FD` (all scaled by `2^P BD rd^p p! FD`). -/
def cellRHS (c : Cfg) (o : OCfg) (K N p : ℕ) (x1 x2 : Acc) (ys1 ys2 : List Acc) (rn rd FN FD : ℕ) : ℤ :=
  (((wData (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 x1 x2).2.2.1
    + (wData (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 x1 x2).2.2.2)
    * ((rd : ℤ) ^ p * ((p ! : ℕ) : ℤ) * FD))
  + sumM (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 rn rd p 1 ys1 ys2 * FD
  + FN * 2 ^ c.P * (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 * (rd : ℤ) ^ p * ((p ! : ℕ) : ℤ)

/-- The left side `(C0re² + C0im²) T²` of the cell check. -/
def cellLHS (c : Cfg) (o : OCfg) (K N p : ℕ) (x1 x2 : Acc) (rd FD : ℕ) : ℤ :=
  ((wData (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 x1 x2).1 ^ 2
    + (wData (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 x1 x2).2.1 ^ 2)
  * ((rd : ℤ) ^ p * ((p ! : ℕ) : ℤ) * FD) ^ 2

/-- **The kernel cell check.**  `xs1`, `xs2`: the `p + 1` accumulators after `N - 1` and `N` terms at
    `c = σ + i t`; `r = rn/rd`; `F = FN/FD`.  Checks `Σ_{k=1}^p ‖W_k‖ r^k/k! + F < ‖W_0‖` by comparing
    squares, everything multiplied through by `2^P BD rd^p p! FD`. -/
def checkCell (c : Cfg) (o : OCfg) (K N p : ℕ) (xs1 xs2 : List Acc) (rn rd FN FD : ℕ) : Bool :=
  match xs1, xs2 with
  | x1 :: ys1, x2 :: ys2 =>
    Nat.ble 1 K && Nat.ble K 6 && Nat.ble 2 N && Nat.ble 1 rd && Nat.ble 1 FD && Nat.ble 1 o.q &&
      Nat.ble 1 c.tn && Nat.beq ys1.length p && Nat.beq ys2.length p &&
      decide (0 ≤ cellRHS c o K N p x1 x2 ys1 ys2 rn rd FN FD) &&
      decide (cellRHS c o K N p x1 x2 ys1 ys2 rn rd FN FD * cellRHS c o K N p x1 x2 ys1 ys2 rn rd FN FD
        < cellLHS c o K N p x1 x2 rd FD)
  | _, _ => false



end Off

end ArbEcon


def ArdaRH65K_Turing121_EMZetaOfflineSlabCheck : Nat := 0


