-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_H1000Point
-- name    : ArdaRH65K_Turing121_H1000Point
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:09:23.063565+00:00
-- url     : https://prove2.me/theorems/552a52df-bef4-43f9-86a1-c5e7bc16769c
-- title:
--   H1000Point certificate definitions
-- statement:
--   This bundle defines individual critical-line sample data and its integer interval checks. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{H1000Line.LinePt.Q},\;\mathtt{H1000Line.LinePt.nl},\;\mathtt{H1000Line.LinePt.mk},\;\mathtt{H1000Line.LinePt.tq}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H1000Point.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_H1000Phase
import Definitions.Def_ArdaRH65K_Turing121_KernelGammaEnvelope
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
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
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
/-  H1000Point.lean -- the point record and the pieces of the on-line sign certificate (lane
    h1000-prep; consumed by `H1000Line`).

    `LinePt` (height `t = tn / 2^tq`, EM cut, evaluator states, remainder and phase hints, claimed
    sign) and the kernel-evaluable pieces of `ptCheck`: the Dirichlet chunks `dirOk`
    (`ArbEcon.chunk_sound`), the integer zeta ball `zcX, zrX, zcY, zrY` at scale `zW`
    (`zball_sound`, from `EMZetaHighEval.zeta_ballK`, `EMZetaHighCheck.corr_eq`, `remOdd_sound`), the
    shifted phase interval `thLo, thHi` and its `trig` (`trig_phase`, from `H1000Phase.phase_sound` and
    `ArbEcon.trig_sound`), the product ball `sCtr ± sRad` of `S · 2^64 · W` (`s_ball`), and the
    positive magnitude factor of `gLine` (`gLine_eq_mag_mul`).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.
-/



open Real Filter Topology
open ArbEcon ArbEcon.OrderK

namespace H1000Line

noncomputable section

/-! ## E. The point record, the Dirichlet chunks and the integer zeta ball. -/

/-- A kernel-checked on-line point: height `t = tn / 2^tq`, EM cut `N` (order 13, `K = 6`), the
    evaluator states `s1` (after `N - 1` terms) and `s2` (after `N`), the odd-saw remainder
    certificate `Q, r`, the phase hints `k` (`2^k ≤ A < 2^(k+1)`), `nl` (log series length), `m`
    (the `2π m` shift making the phase nonnegative), and the CLAIMED sign `pos` of `gLine t`. -/
structure LinePt where
  tn : ℕ
  tq : ℕ
  N : ℕ
  s1 : St
  s2 : St
  Q : ℕ
  r : ℕ
  k : ℕ
  nl : ℕ
  m : ℕ
  pos : Bool

/-- The height of a point. -/
def tOf (p : LinePt) : ℝ := (p.tn : ℝ) / 2 ^ p.tq





/-- The remainder certificate `(ok, EN, ED)` of the point (order 13, odd saw). -/
def remP (p : LinePt) : Bool × ℤ × ℤ := remOdd 6 (2 ^ p.tq) p.tn p.N p.Q p.r

/-- The exact correction factor `(BreN, BimN, BD)` of the point. -/
def corP (p : LinePt) : ℤ × ℤ × ℤ := corrData 6 (2 ^ p.tq) p.tn p.N

/-- `W = 2^64 · BD · ED`, the common scale of the zeta ball. -/
def zW (p : LinePt) : ℤ := 2 ^ 64 * (corP p).2.2 * (remP p).2.2

/-- Centre of the `Re ζ` ball at scale `W` (the `checkCore` numerator `CreN`, times `ED`). -/
def zcX (p : LinePt) : ℤ :=
  (remP p).2.2 * ((((p.s1.reP : ℤ) - p.s1.reN)) * (corP p).2.2
    + (((p.s2.reP : ℤ) - p.s2.reN) - ((p.s1.reP : ℤ) - p.s1.reN)) * (corP p).1
    - (((p.s2.imP : ℤ) - p.s2.imN) - ((p.s1.imP : ℤ) - p.s1.imN)) * (corP p).2.1)

/-- Radius of the `Re ζ` ball at scale `W`. -/
def zrX (p : LinePt) : ℤ :=
  (remP p).2.2 * ((p.s1.reR : ℤ) * (corP p).2.2 + ((p.s2.reR : ℤ) + p.s1.reR) * ((corP p).1.natAbs : ℤ)
    + ((p.s2.imR : ℤ) + p.s1.imR) * ((corP p).2.1.natAbs : ℤ))
    + (corP p).2.2 * (remP p).2.1 * 2 ^ 64

/-- Centre of the `Im ζ` ball at scale `W`. -/
def zcY (p : LinePt) : ℤ :=
  (remP p).2.2 * ((((p.s1.imP : ℤ) - p.s1.imN)) * (corP p).2.2
    + (((p.s2.reP : ℤ) - p.s2.reN) - ((p.s1.reP : ℤ) - p.s1.reN)) * (corP p).2.1
    + (((p.s2.imP : ℤ) - p.s2.imN) - ((p.s1.imP : ℤ) - p.s1.imN)) * (corP p).1)

/-- Radius of the `Im ζ` ball at scale `W`. -/
def zrY (p : LinePt) : ℤ :=
  (remP p).2.2 * ((p.s1.imR : ℤ) * (corP p).2.2 + ((p.s2.reR : ℤ) + p.s1.reR) * ((corP p).2.1.natAbs : ℤ)
    + ((p.s2.imR : ℤ) + p.s1.imR) * ((corP p).1.natAbs : ℤ))
    + (corP p).2.2 * (remP p).2.1 * 2 ^ 64





/-! ## F. The product ball and the sign test. -/



/-- Integer sign `±1` of a Bool (`true` = `+1`), the integer form of `ArbEcon.sgn`. -/
def sgnI (b : Bool) : ℤ := Bool.rec (-1) 1 b



/-- The shifted phase interval (scale `2^64`) fed to `trig`: lower end. -/
def thLo (p : LinePt) : ℤ := phaseLo p.tn p.tq p.k p.nl + (p.m : ℤ) * (TPLO : ℤ)

/-- The shifted phase interval: upper end. -/
def thHi (p : LinePt) : ℤ := phaseHi p.tn p.tq p.k p.nl + (p.m : ℤ) * (TPHI : ℤ)

/-- cos / sin of the (shifted) phase, by the evaluator's `trig`. -/
def trigP (p : LinePt) : Trig := trig (cfg64 p.tn p.tq) (thLo p).toNat (thHi p).toNat

/-- Centre of `S · 2^64 · W` (`S = cos φ Re ζ - sin φ Im ζ`). -/
def sCtr (p : LinePt) : ℤ :=
  sgnI (trigP p).cs * ((trigP p).cm : ℤ) * zcX p - sgnI (trigP p).ss * ((trigP p).sm : ℤ) * zcY p

/-- Radius of `S · 2^64 · W`. -/
def sRad (p : LinePt) : ℤ :=
  ((trigP p).cr : ℤ) * (((zcX p).natAbs : ℤ) + zrX p) + ((trigP p).cm : ℤ) * zrX p
    + ((trigP p).sr : ℤ) * (((zcY p).natAbs : ℤ) + zrY p) + ((trigP p).sm : ℤ) * zrY p



/-- The phase of the point, `φ = Λ - (t/2) log π`. -/
def phiOf (p : LinePt) (Λ : ℝ) : ℝ := Λ - tOf p / 2 * Real.log π







end

end H1000Line


def ArdaRH65K_Turing121_H1000Point : Nat := 0


