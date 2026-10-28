-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_H1000Octant
-- name    : ArdaRH65K_Turing121_H1000Octant
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:10:58.998969+00:00
-- url     : https://prove2.me/theorems/dd3622bf-3406-48f3-a2b6-ecdf1ff5c91a
-- title:
--   H1000Octant certificate definitions
-- statement:
--   This bundle defines octant evaluations and finite checks for horizontal boundary pieces. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{H1000Oct.octXv},\;\mathtt{H1000Oct.octLo},\;\mathtt{H1000Oct.octUp},\;\mathtt{H1000Oct.sumOct}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H1000Octant.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
/-  H1000Octant.lean -- lane h1000-integrate: the kernel-checked OCTANT PIECE, the evaluator side of
    brick K6c (`ArgHoriz`) for the horizontal edges `[2, -1] + i T` of the RvM rectangles.

    `ArgHoriz.hAH_of_octCert_boxes` reduces `argChangeHoriz ζ T 2 (-1) ∈ [L, H]` to an octant
    certificate: breakpoints `2 = p 0 > p 1 > … > p m = -1`, one octant label `k j` per piece, and
    the no-crossing facts `0 < octX (k j) ζ(x + i T)` for every `x` of piece `j`, plus two point
    enclosures at `x = 2` and `x = -1`.  This file proves the no-crossing fact of ONE piece from ONE
    run of the off-line evaluator (`EMZetaOfflineEval`, `p + 1` accumulators) at the piece center
    `c = σc + i tc` and ONE Boolean check run by `decide +kernel`:

      A1. `emCorr_sub_le_norm`, `norm_emCorr_le_norm` -- the correction-factor bounds of
          `EMZetaOfflineSlab` with `a ≤ ‖c - 1‖` in place of `a ≤ Im c` (so they hold near `s = 1`
          at small heights);
      A2. `emFinite_taylor_le_G` -- the Taylor model of the EM finite part for ANY real part of the
          center: `‖n^(-c)‖ ≤ G` for `n ≤ N` (`G = 1` for `σc ≥ 0`, `N^(-σc)` for `σc < 0`);
      B.  `pochNormSq_mono_abs`, `em_remainder_horiz` -- the order-(2K+1) remainder uniformly on a
          horizontal segment `xlo ≤ x ≤ xhi` (negative `x` allowed, `x > -2K`);
          `natCpow_norm_le_of_pow` -- the `G` certificate `Gd^q N^b ≤ Gn^q N^a`;
      C.  `octLo`, `octUp`, `sumOct`, `checkOct`, `checkOct_sound` -- the kernel check
          `Σ_{k=1}^p |octX (W_k)| r^k/k! + (|α| + |β|) F < octX (W_0)` on the evaluator balls;
      D.  `piece_octX_pos` -- THE PIECE: for every real `x` with `|x - σc| ≤ r`,
          `0 < ArgHoriz.octX kk (ζ(x + i tc))`.  Along a horizontal piece `h = x - σc` is REAL, so
          the octant projection of the Taylor polynomial is a real polynomial in `h` and only the
          projections `octX (W_k)` enter;
      E.  `abs_sub_le_of_mem_uIcc`, `budget_mono` -- small helpers for the generated certificates.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (AxiomGuardAllZerosKernel_h1000).  No `sorry`.
    conjecture1_proved = False.  Finite interval arithmetic along finitely many segments; nothing
    here bears on the Riemann Hypothesis.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace H1000Oct

open ArbEcon ArbEcon.Off

/-! ## A1. The correction factor, with `a ≤ ‖c - 1‖`. -/





/-! ## A2. The Taylor model for any real part of the center. -/



/-! ## B. The remainder along a horizontal segment, and the `G` certificate. -/









/-! ## C. The kernel check of a piece. -/

/-- The octant projection `α Re w + β Im w`. -/
noncomputable def octXv (α β : ℤ) (w : ℂ) : ℝ := (α : ℝ) * w.re + (β : ℝ) * w.im











/-- Lower bound, scaled, of the projection over a ball `d = (C_re, C_im, R_re, R_im)`. -/
def octLo (α β : ℤ) (d : ℤ × ℤ × ℤ × ℤ) : ℤ :=
  α * d.1 + β * d.2.1 - ((α.natAbs : ℤ) * d.2.2.1 + (β.natAbs : ℤ) * d.2.2.2)

/-- Upper bound, scaled, of the absolute projection over a ball. -/
def octUp (α β : ℤ) (d : ℤ × ℤ × ℤ × ℤ) : ℤ :=
  ((α * d.1 + β * d.2.1).natAbs : ℤ) + (α.natAbs : ℤ) * d.2.2.1 + (β.natAbs : ℤ) * d.2.2.2





/-- `Σ_{j ≥ k} octUp(W_j) rn^j rd^(p-j) (p!/j!)` over the paired accumulator lists. -/
def sumOct (α β BreN BimN BD : ℤ) (rn rd p : ℕ) : ℕ → List Acc → List Acc → ℤ
  | k, x1 :: xs1, x2 :: xs2 =>
    octUp α β (wData BreN BimN BD x1 x2) * (rn : ℤ) ^ k * (rd : ℤ) ^ (p - k) * ((p ! / k ! : ℕ) : ℤ)
      + sumOct α β BreN BimN BD rn rd p (k + 1) xs1 xs2
  | _, _, _ => 0



/-- The right side of the piece check (scaled by `2^P BD rd^p p! FD`). -/
def octRHS (c : Cfg) (o : OCfg) (K N p : ℕ) (kk : ℤ) (ys1 ys2 : List Acc) (rn rd FN FD : ℕ) : ℤ :=
  sumOct (ArgHoriz.octA kk) (ArgHoriz.octB kk)
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
      (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 rn rd p 1 ys1 ys2 * FD
    + (((ArgHoriz.octA kk).natAbs : ℤ) + ((ArgHoriz.octB kk).natAbs : ℤ)) * FN * 2 ^ c.P
      * (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 * (rd : ℤ) ^ p * ((p ! : ℕ) : ℤ)

/-- The left side of the piece check. -/
def octLHS (c : Cfg) (o : OCfg) (K N p : ℕ) (kk : ℤ) (x1 x2 : Acc) (rd FD : ℕ) : ℤ :=
  octLo (ArgHoriz.octA kk) (ArgHoriz.octB kk)
      (wData (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).1
        (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.1
        (corrDataG K ((o.a : ℤ) - o.b) o.q (2 ^ c.tq) c.tn N).2.2 x1 x2)
    * ((rd : ℤ) ^ p * ((p ! : ℕ) : ℤ) * FD)

/-- **The kernel piece check.**  `xs1`, `xs2`: the `p + 1` accumulators after `N - 1` and `N` terms
    at `c = σ + i t`; octant `kk` (integer vector `(α, β) = (octA kk, octB kk)`); `r = rn/rd`;
    `F = FN/FD`.  Checks `Σ_{k=1}^p |octX (W_k)| r^k/k! + (|α| + |β|) F < octX (W_0)`, everything
    multiplied through by `2^P BD rd^p p! FD`. -/
def checkOct (c : Cfg) (o : OCfg) (K N p : ℕ) (xs1 xs2 : List Acc) (rn rd FN FD : ℕ) (kk : ℤ) : Bool :=
  match xs1, xs2 with
  | x1 :: ys1, x2 :: ys2 =>
    Nat.ble 1 K && Nat.ble K 6 && Nat.ble 2 N && Nat.ble 1 rd && Nat.ble 1 FD && Nat.ble 1 o.q &&
      Nat.ble 1 c.tn && Nat.beq ys1.length p && Nat.beq ys2.length p &&
      decide (octRHS c o K N p kk ys1 ys2 rn rd FN FD < octLHS c o K N p kk x1 x2 rd FD)
  | _, _ => false



/-! ## D. The piece. -/





/-! ## E. Helpers for the generated certificates. -/







/-! ## F. Closed forms for the generated budgets (K ≤ 6), and the slab-cell wrapper. -/











/-! ## G. Generated-certificate adapters. -/









end H1000Oct


def ArdaRH65K_Turing121_H1000Octant : Nat := 0


