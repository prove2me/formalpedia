-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
-- name    : ArdaRH65K_Turing121_Arb4_Side
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:11:56.159329+00:00
-- url     : https://prove2.me/theorems/c0597c57-2288-43b8-9ae1-ffe40d06b125
-- title:
--   Arb4 Side certificate definitions
-- statement:
--   This bundle defines rational side-segment data and interval-checking operations. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{Arb4.CpQ},\;\mathtt{Arb4.betaQ},\;\mathtt{Arb4.emcBQ},\;\mathtt{Arb4.corrVarQ}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Side.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
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
/-  Arb4_Side.lean -- lane Arb4 (h1000 compaction): Boolean kernel checkers, with soundness proved
    once, for the per-piece side conditions of an octant certificate (brick K6c, `H1000Octant`).

    The generated edge modules `H1000Edge_*` of lane h1000-integrate close, per octant piece, an error
    budget, a horizontal remainder bound, a `G` certificate and six scalar conditions by `norm_num`
    (about 400 KB of olean per piece).  Here all of them are ONE Boolean `pieceOK`, run by
    `decide +kernel` on exact rationals (`Arb4_Q`), together with the off-line evaluator run itself
    (the states after `N - 1` and `N` terms are recomputed in the kernel, not stored):

      * `CpQ betaQ emcBQ corrVarQ budgetQ` (+ `val_*`) -- the error budget of
                           `H1000Oct.piece_octX_pos` as a rational, EQUAL to the real one;
      * `pochQ`, `val_pochQ` -- `pochNormSq` as a rational;
      * `PieceD`         -- the certificate data of one piece (center `(a - b)/q`, radius `rn/rd`,
                           octant `kk`, budget `FN/FD`, and the rationals of the side conditions);
      * `gOK remOK geomOK budgetOK` and their soundness -- the `G` bound, the order-13 remainder on the
                           piece, the scalar geometry, the budget;
      * `pieceOK`, `pieceOK_sound` -- THE PIECE: `pieceOK tn tq N L P = true` gives
                           `0 < octX kk (ζ(x + i t))` for every `x` with `|x - σ| ≤ r`, `t = tn / 2^tq`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  Finite interval
    arithmetic along finitely many segments; nothing here bears on the Riemann Hypothesis.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. The error budget as a rational -/

/-- `C_p = (p + 2) / ((p + 1)! (p + 1))`. -/
def CpQ (p : ℕ) : Q := frac ((p + 2 : ℕ) : ℤ) ((p + 1)! * (p + 1))



/-- `|B_{i+2}| / (i+2)! = |betaN i| / Lβ` as a rational. -/
def betaQ (i : ℕ) : Q := frac ((ArbEcon.OrderK.betaN i).natAbs : ℤ) ArbEcon.OrderK.Lbeta



/-- `N / a + 1/2 + Σ_{i < 2K-1} |B_{i+2}|/(i+2)! U^(i+1) / N^(i+1)` (the bound `emcB`). -/
def emcBQ (K N : ℕ) (a U : Q) : Q :=
  add (add (div (ofNat N) a) (frac 1 2))
    (sumQ (fun i => mul (betaQ i) (div (npow U (i + 1)) (ofNat (N ^ (i + 1))))) (2 * K - 1))



/-- `N r / a² + Σ_{i < 2K-1} |B_{i+2}|/(i+2)! ((U + r)^(i+1) - U^(i+1)) / N^(i+1)` (`corrVar`). -/
def corrVarQ (K N : ℕ) (r a U : Q) : Q :=
  add (div (mul (ofNat N) r) (npow a 2))
    (sumQ (fun i => mul (betaQ i) (div (sub (npow (add U r) (i + 1)) (npow U (i + 1)))
      (ofNat (N ^ (i + 1))))) (2 * K - 1))





/-- The error budget of `H1000Oct.piece_octX_pos` (order `2K + 1`, Taylor order `p`):
    `G (C_p (R L)^(p+1) ((N - 1) + emcB) + 3 corrVar) + E`. -/
def budgetQ (K N p : ℕ) (G R L a U E : Q) : Q :=
  add (mul G (add (mul (mul (CpQ p) (npow (mul R L) (p + 1)))
      (add (sub (ofNat N) (ofNat 1)) (emcBQ K N a U)))
    (mul (ofNat 3) (corrVarQ K N R a U)))) E



/-! ## B. `pochNormSq` as a rational -/

/-- `Π_{j < k} ((σ + j)² + t²)`. -/
def pochQ (σ t : Q) : ℕ → Q
  | 0 => ofNat 1
  | k + 1 => mul (pochQ σ t k) (add (npow (add σ (ofNat k)) 2) (npow t 2))



/-! ## C. The certificate data of one octant piece -/

/-- The height `t = tn / 2^tq` as a rational. -/
def tQ (tn tq : ℕ) : Q := frac (tn : ℤ) (2 ^ tq)



/-- The certificate data of ONE octant piece `[σ - r, σ + r]` of a horizontal edge.  Every field is
    an exact integer or rational; nothing is trusted: `pieceOK` re-checks every relation. -/
structure PieceD where
  /-- center `σ = (a - b) / q` -/
  a : ℕ
  b : ℕ
  q : ℕ
  /-- radius `r = rn / rd` -/
  rn : ℕ
  rd : ℕ
  /-- octant label (a continuous lift of the argument, in units of `π/4`) -/
  kk : ℤ
  /-- error budget `F = FN / FD` of the kernel check `checkOct` -/
  FN : ℕ
  FD : ℕ
  /-- distance parameter: `a + r ≤ ‖c - 1‖` -/
  aQ : Q
  /-- `‖c + j‖ ≤ U` for `j < 12` -/
  U : Q
  /-- `G = Gn / Gd ≥ ‖n^(-c)‖`: `Gd^gq N^gb ≤ Gn^gq N^ga`, `ga ≤ gb`, `(ga - gb)/gq ≤ σ` -/
  ga : ℕ
  gb : ℕ
  gq : ℕ
  Gn : ℕ
  Gd : ℕ
  /-- remainder range `[xlo, xhi]`, `xlo = (ea - eb)/eqd`, `|x| ≤ sigs` on it,
      `N^(-xlo) ≤ Rn/Rd` from `Rd^eqd N^eb ≤ Rn^eqd N^ea`, `pochNormSq sigs t 13 ≤ Qr²`,
      and the resulting remainder bound `E` -/
  ea : ℕ
  eb : ℕ
  eqd : ℕ
  Rn : ℕ
  Rd : ℕ
  xhi : Q
  sigs : Q
  Qr : ℕ
  E : Q

namespace PieceD

/-- The center `σ = (a - b) / q`. -/
noncomputable def σ (P : PieceD) : ℝ := ((P.a : ℝ) - P.b) / P.q

def σQ (P : PieceD) : Q := frac ((P.a : ℤ) - P.b) P.q

def rQ (P : PieceD) : Q := frac (P.rn : ℤ) P.rd

def GQ (P : PieceD) : Q := frac (P.Gn : ℤ) P.Gd

def FQ (P : PieceD) : Q := frac (P.FN : ℤ) P.FD

def xloQ (P : PieceD) : Q := frac ((P.ea : ℤ) - P.eb) P.eqd

/-- The off-line evaluator configuration of the piece center (`oneQ = 2^(q P)`, `P = 64`; Newton fuel
    256: `rootLoop` stops at convergence, and centers with `q = 64` need about 66 steps at `m = 2`). -/
def oc (P : PieceD) : ArbEcon.Off.OCfg := ⟨P.a, P.b, P.q, 2 ^ (P.q * 64), 256⟩











end PieceD

/-! ## D. The side conditions as Booleans -/

/-- The `G` certificate: `Gd^gq N^gb ≤ Gn^gq N^ga`, `ga ≤ gb`, `(ga - gb)/gq ≤ σ`. -/
def gOK (N : ℕ) (P : PieceD) : Bool :=
  Nat.ble 1 P.gq && Nat.ble 1 P.Gd && Nat.ble P.ga P.gb &&
    Nat.ble (P.Gd ^ P.gq * N ^ P.gb) (P.Gn ^ P.gq * N ^ P.ga) &&
    Q.le (frac ((P.ga : ℤ) - P.gb) P.gq) P.σQ



/-- The order-13 remainder on the piece: `[σ - r, σ + r] ⊆ [xlo, xhi]`, `xlo > -12`, `|x| ≤ sigs`,
    `pochNormSq sigs t 13 ≤ Qr²`, `N^(-xlo) ≤ Rn/Rd`, and `C_6 Qr (Rn/Rd) / N^12 / (xlo + 12) ≤ E`
    (with `C_6 ≤ 84107 · 10^-15`, `H1000Oct.CK_six_le`). -/
def remOK (tn tq N : ℕ) (P : PieceD) : Bool :=
  Nat.ble 1 P.eqd && Nat.ble 1 P.Rd && Nat.ble 1 tn &&
    Q.le P.xloQ (sub P.σQ P.rQ) && Q.le (add P.σQ P.rQ) P.xhi &&
    decide (0 < (add P.xloQ (ofNat 12)).n) &&
    Q.le P.xhi P.sigs && Q.le (neg P.xloQ) P.sigs &&
    Q.le (pochQ P.sigs (tQ tn tq) 13) (ofNat (P.Qr * P.Qr)) &&
    Nat.ble (P.Rd ^ P.eqd * N ^ P.eb) (P.Rn ^ P.eqd * N ^ P.ea) &&
    Q.le (div (div (mul (mul (frac 84107 (10 ^ 15)) (ofNat P.Qr)) (frac (P.Rn : ℤ) P.Rd))
      (ofNat (N ^ 12))) (add P.xloQ (ofNat 12))) P.E



/-- The scalar geometry of the piece: the log bracket `lhi ≤ L 2^64`, `r L ≤ 1`, `0 < a`,
    `(a + r)² ≤ (σ - 1)² + t²`, `0 ≤ U`, `(|σ| + 11)² + t² ≤ U²`. -/
def geomOK (tn tq : ℕ) (L : Q) (lhi : ℕ) (P : PieceD) : Bool :=
  Q.le (ofNat lhi) (mul L (ofNat (2 ^ 64))) && Q.le (mul P.rQ L) (ofNat 1) &&
    decide (0 < P.aQ.n) &&
    Q.le (npow (add P.aQ P.rQ) 2) (add (npow (sub P.σQ (ofNat 1)) 2) (npow (tQ tn tq) 2)) &&
    decide (0 ≤ P.U.n) &&
    Q.le (add (npow (add (qabs P.σQ) (ofNat 11)) 2) (npow (tQ tn tq) 2)) (npow P.U 2)

/-- The error budget of the piece. -/
def budgetOK (N : ℕ) (L : Q) (P : PieceD) : Bool :=
  Q.le (budgetQ 6 N 5 P.GQ P.rQ L P.aQ P.U P.E) P.FQ

/-! ## E. THE PIECE -/

/-- **The piece checker**: the off-line evaluator run at the center (states after `N - 1` and `N`
    terms, 6 accumulators, recomputed here), the kernel check `H1000Oct.checkOct`, and every side
    condition of `H1000Oct.piece_octX_pos`. -/
noncomputable def pieceOK (tn tq N : ℕ) (L : Q) (P : PieceD) : Bool :=
  let c := ArbEcon.OrderK.cfg64 tn tq
  let s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5)
  let sN := ArbEcon.Off.runO c P.oc 1 s1
  Nat.ble 2 N && Nat.ble 1 P.q && Nat.ble 1 P.rd && Nat.ble 1 P.FD &&
    H1000Oct.checkOct c P.oc 6 N 5 s1.acc sN.acc P.rn P.rd P.FN P.FD P.kk &&
    geomOK tn tq L sN.lhi P && gOK N P && remOK tn tq N P && budgetOK N L P



end Arb4


def ArdaRH65K_Turing121_Arb4_Side : Nat := 0


