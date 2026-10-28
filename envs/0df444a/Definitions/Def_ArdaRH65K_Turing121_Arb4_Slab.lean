-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
-- name    : ArdaRH65K_Turing121_Arb4_Slab
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:14:08.860765+00:00
-- url     : https://prove2.me/theorems/a698a9ee-209a-43d9-b28b-5392b8c185df
-- title:
--   Arb4 Slab certificate definitions
-- statement:
--   This bundle defines cell and slab certificates with their finite rational checks. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{Arb4.slabBudgetQ},\;\mathtt{Arb4.CellD},\;\mathtt{Arb4.CellD.rn},\;\mathtt{Arb4.CellD.a}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Slab.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
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
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
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
/-  Arb4_Slab.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per zero-free
    edge-clearance slab `EdgeClearGlue.SlabClear a b` (brick K1's numerical input).

    The generated slab modules `H1000Slab_*` of lane h1000-integrate cover `[1/2, 1] × [a, b]` by
    cells (one off-line evaluator run and one `ArbEcon.Off.checkCell` each), assembled by
    `H1000Oct.cell_zeta_ne_zero_R`, and close the slab budget, the Pochhammer bound and about
    fifteen scalar conditions per cell by `norm_num`.  Here the WHOLE slab is one Boolean `slabOK`:

      * `slabBudgetQ`, `slabBudget_le` -- the slab error budget as a rational (with
                           `C_6 ≤ 84107 · 10^-15`, `H1000Oct.CK_six_le`);
      * `CellD`, `SlabD` -- the certificate data: the slab `[lo, hi]`, its shared budget, the
                           breakpoints `1/2 = xs 0 < … < xs m = 1` and one cell per column
                           `[xs j, xs (j+1)] × [lo, hi]` (center, radius, half-widths);
      * `cellOK`, `cellOK_sound` -- one cell (evaluator run recomputed, `checkCell`, geometry);
      * `slabOK`, `slabOK_sound` -- THE SLAB: `slabOK S = true` gives `SlabClear lo hi`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  A finite zero-free
    slab; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. The slab budget -/

/-- `C_5 (R L)^6 ((N - 1) + emcB) + 3 corrVar + C_6' Qr / (N^12 r0) / (25/2)`, `C_6' = 84107·10^-15`. -/
def slabBudgetQ (N : ℕ) (R L a U : Q) (Qr r0 : ℕ) : Q :=
  add (add (mul (mul (CpQ 5) (npow (mul R L) (5 + 1))) (add (sub (ofNat N) (ofNat 1)) (emcBQ 6 N a U)))
      (mul (ofNat 3) (corrVarQ 6 N R a U)))
    (div (div (mul (frac 84107 (10 ^ 15)) (ofNat Qr)) (ofNat (N ^ 12 * r0))) (frac 25 2))



/-! ## B. The certificate data -/

/-- One cell `[xs j, xs (j+1)] × [lo, hi]` of a slab: center `σ = (a - b)/q ≥ 0`, `tc = tn / 2^tq`,
    radius `rn / rd`, half-widths `w`, `hh` of the rectangle around the center. -/
structure CellD where
  a : ℕ
  b : ℕ
  q : ℕ
  tn : ℕ
  rn : ℕ
  rd : ℕ
  w : Q
  hh : Q

/-- The certificate data of one slab `[1/2, 1] × [lo, hi]` (the reflection covers `(0, 1/2)`). -/
structure SlabD where
  /-- dyadic exponent of every cell center height -/
  tq : ℕ
  /-- EM cut, log bound, budget radius `R` (at least every cell radius) -/
  N : ℕ
  L : Q
  R : Q
  /-- the slab `[lo, hi]`; `lo` is also the lower bound `a ≤ Im s` of the budget -/
  lo : Q
  hi : Q
  /-- `‖c + j‖ ≤ U`, `pochNormSq 1 hi 13 ≤ Qr²`, `r0² ≤ N`, the budget `FN / FD` -/
  U : Q
  Qr : ℕ
  r0 : ℕ
  FN : ℕ
  FD : ℕ
  /-- `m` columns `[xs j, xs (j+1)]`, `xs 0 = 1/2`, `xs m = 1` -/
  m : ℕ
  xs : ℕ → Q
  cell : ℕ → CellD

namespace CellD

noncomputable def σ (C : CellD) : ℝ := ((C.a : ℝ) - C.b) / C.q

def σQ (C : CellD) : Q := frac ((C.a : ℤ) - C.b) C.q

def oc (C : CellD) : ArbEcon.Off.OCfg := ⟨C.a, C.b, C.q, 2 ^ (C.q * 64), 256⟩



end CellD

/-! ## C. One cell -/

/-- **The cell checker** (cell `j` of slab `S`): the evaluator run at the center (recomputed), the
    kernel check `checkCell`, and the cell's side conditions and rectangle geometry. -/
noncomputable def cellOK (S : SlabD) (j : ℕ) : Bool :=
  let C := S.cell j
  let c := ArbEcon.OrderK.cfg64 C.tn S.tq
  let s1 := ArbEcon.Off.runO c C.oc (S.N - 2) (ArbEcon.Off.StO.init c 5)
  let sN := ArbEcon.Off.runO c C.oc 1 s1
  Nat.ble 2 S.N && Nat.ble 1 C.q && Nat.ble 1 C.rd && Nat.ble C.b C.a &&
    ArbEcon.Off.checkCell c C.oc 6 S.N 5 s1.acc sN.acc C.rn C.rd S.FN S.FD &&
    le (frac (C.rn : ℤ) C.rd) S.R && le (ofNat sN.lhi) (mul S.L (ofNat (2 ^ 64))) &&
    le S.lo (tQ C.tn S.tq) &&
    le (add (npow (add C.σQ (ofNat 11)) 2) (npow (tQ C.tn S.tq) 2)) (npow S.U 2) &&
    le (qabs (sub (S.xs j) C.σQ)) C.w && le (qabs (sub (S.xs (j + 1)) C.σQ)) C.w &&
    le (qabs (sub S.lo (tQ C.tn S.tq))) C.hh && le (qabs (sub S.hi (tQ C.tn S.tq))) C.hh &&
    le (add (npow C.w 2) (npow C.hh 2)) (npow (frac (C.rn : ℤ) C.rd) 2)

/-- The slab-level facts every cell uses. -/
def slabHeadOK (S : SlabD) : Bool :=
  Nat.ble 1 S.m && Nat.ble 1 S.FD && eqB (S.xs 0) (frac 1 2) && eqB (S.xs S.m) (ofNat 1) &&
    le (mul S.R S.L) (ofNat 1) && decide (0 < S.lo.n) && decide (0 ≤ S.U.n) &&
    le (pochQ (ofNat 1) S.hi 13) (ofNat (S.Qr * S.Qr)) && Nat.ble 1 S.r0 &&
    Nat.ble (S.r0 * S.r0) S.N && Nat.ble 1 S.N &&
    le (slabBudgetQ S.N S.R S.L S.lo S.U S.Qr S.r0) (frac (S.FN : ℤ) S.FD)





/-! ## D. THE SLAB -/



/-- **The slab checker**: the slab-level facts and every cell. -/
noncomputable def slabOK (S : SlabD) : Bool :=
  slabHeadOK S && (List.range S.m).all (cellOK S)



end Arb4


def ArdaRH65K_Turing121_Arb4_Slab : Nat := 0


