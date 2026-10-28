-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_H1000Phase
-- name    : ArdaRH65K_Turing121_H1000Phase
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:08:14.738788+00:00
-- url     : https://prove2.me/theorems/d4976f6b-93d8-46a6-b0d6-a2b50d6a8b25
-- title:
--   H1000Phase certificate definitions
-- statement:
--   This bundle defines fixed-point logarithm, angle, and phase evaluation data. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{H1000Line.fdiv},\;\mathtt{H1000Line.cdiv},\;\mathtt{H1000Line.ONE},\;\mathtt{H1000Line.lser}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/H1000Phase.lean

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
/-  H1000Phase.lean -- the Riemann-Siegel phase at a rational height, as kernel-checkable integer
    bounds (lane h1000-prep; consumed by `H1000Line`).

    For `t = tn / 2^tq` and the branch limit `Λ = lim imLnVal (1/4) (t/2)` (the one
    `KernelGammaEnvelope.gLine_decomp_explicit` exposes), `phase_sound` gives

        phaseLo tn tq k nl ≤ (Λ - (t/2) log π) · 2^64 ≤ phaseHi tn tq k nl,

    where `phaseLo`, `phaseHi` are plain `Int`/`Nat` computations (the kernel evaluates them) of the
    height-uniform bracket `RSTheta.theta_bracket`:
        thetaS t - 1/(2t) ≤ Λ - (t/2) log π ≤ thetaS t,
        thetaS t = (t/4) log (1/16 + t²/4) - (1/4) arctan (2t) - t/2 - (t/2) log π.
    Ingredients: `log (1/16 + t²/4) = (k - 2tq - 4) log 2 - log (1 - (A - 2^k)/A)`, `A = 4^tq + 4 tn²`
    (`log_inner_eq`); the fixed-point series of `-log (1 - x)` with Mathlib's geometric remainder
    `Real.abs_log_sub_add_sum_range_le` (`lnBox_sound`); `log 2`, `log π` from `RSTheta.log2_box`,
    `logpi_box`; `π` from `Real.pi_gt_d20`, `pi_lt_d20`; `arctan (2t) = π/2 - arctan w` with
    `w - w³/3 ≤ arctan w ≤ w` (`ArctanTaylor`).  Every rounding is outward (`fdiv`, `cdiv`).

    Trust: axioms [propext, Classical.choice, Quot.sound] (AxiomGuardH1000Line.lean); no `sorry`.
    conjecture1_proved = False.  Elementary enclosures of one special-function value; nothing here
    bears on the Riemann Hypothesis.
-/






open Real Filter Topology
open ArbEcon ArbEcon.OrderK

namespace H1000Line

noncomputable section

/-! ## A. Floor and ceiling division of an integer by a positive natural. -/

/-- `⌊a / b⌋` for `b > 0` (`Int.ediv`). -/
def fdiv (a : ℤ) (b : ℕ) : ℤ := a / (b : ℤ)

/-- `⌈a / b⌉` for `b > 0`. -/
def cdiv (a : ℤ) (b : ℕ) : ℤ := -((-a) / (b : ℤ))





/-! ## B. The series `-log (1 - a/b) = Σ_j (a/b)^(j+1)/(j+1)` in fixed point (scale `2^64`). -/

/-- The fixed-point scale of the phase, `2^64` (the evaluator's `one`). -/
def ONE : ℕ := 18446744073709551616



/-- `lser one a b n i pa pb acc`: `n` more floored series terms from index `i` (with `pa = a^(i+1)`,
    `pb = b^(i+1)`); returns `(acc', a^(i+n+1), b^(i+n+1))`.  The scale `one` is a parameter (it is
    `ONE = 2^64` in `lnBox`), so the generic lemmas never unfold a large literal. -/
def lser (one a b : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ)
    (fun _ pa pb acc => (acc, pa, pb))
    (fun _ ih i pa pb acc => ih (i + 1) (pa * a) (pb * b) (acc + pa * one / (pb * (i + 1))))

/-- The `j`-th floored term `⌊a^(j+1) one / (b^(j+1) (j+1))⌋`. -/
def lterm (one a b j : ℕ) : ℕ := a ^ (j + 1) * one / (b ^ (j + 1) * (j + 1))









/-- `(lo, hi)` with `lo ≤ -log (1 - a/b) · 2^64 ≤ hi` (for `0 < b`, `2a < b`): `nl` floored series
    terms plus the geometric tail `(a/b)^(nl+1) / (1 - a/b)`. -/
def lnBox (a b nl : ℕ) : ℤ × ℤ :=
  let r := lser ONE a b nl 0 a b 0
  let EU : ℕ := r.2.1 * ONE * b / (r.2.2 * (b - a)) + 1
  ((r.1 : ℤ) - (EU : ℤ), ((r.1 + nl + EU : ℕ) : ℤ))



/-! ## C. Scaled constants: `log 2`, `log π`, `π/8`, `2π` at scale `2^64`. -/

def L2LO : ℕ := 12786308645202588812
def L2HI : ℕ := 12786308645202719885
def LPLO : ℕ := 21116539237789363774
def LPHI : ℕ := 21116539237791978907
def P8LO : ℕ := 7244019458077122842
def P8HI : ℕ := 7244019458077122843
def TPLO : ℕ := 115904311329233965478
def TPHI : ℕ := 115904311329233965479









/-! ## D. The Riemann-Siegel phase `φ = Λ - (t/2) log π` at `t = tn / 2^tq`. -/

/-- `A = 4^tq + 4 tn²`, so that `1/16 + t²/4 = A / 2^(2 tq + 4)` at `t = tn / 2^tq`. -/
def AA (tn tq : ℕ) : ℕ := 2 ^ tq * 2 ^ tq + 4 * tn * tn

/-- Side conditions of the phase evaluation: `2^k ≤ A < 2^(k+1)`, `2 tq + 4 ≤ k`, `1 ≤ tn`,
    `2^tq ≤ 2 tn` (so `t ≥ 1/2`). -/
def phaseOk (tn tq k : ℕ) : Bool :=
  decide (2 ^ k ≤ AA tn tq) && decide (AA tn tq < 2 * 2 ^ k) && decide (2 * tq + 4 ≤ k) &&
    decide (1 ≤ tn) && decide (2 ^ tq ≤ 2 * tn)

/-- Bounds for `log (1/16 + t²/4) · 2^64`: `(k - 2 tq - 4) log 2 - log (1 - (A - 2^k)/A)`. -/
def innerBox (tn tq k nl : ℕ) : ℤ × ℤ :=
  let j : ℤ := ((k - (2 * tq + 4) : ℕ) : ℤ)
  let lb := lnBox (AA tn tq - 2 ^ k) (AA tn tq) nl
  (j * (L2LO : ℤ) + lb.1, j * (L2HI : ℤ) + lb.2)

/-- Lower bound of `φ · 2^64` (theta bracket lower edge `thetaS t - 1/(2t)`). -/
def phaseLo (tn tq k nl : ℕ) : ℤ :=
  fdiv ((innerBox tn tq k nl).1 * (tn : ℤ)) (4 * 2 ^ tq)
    + (fdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn)
        - cdiv ((2 ^ tq * 2 ^ tq * 2 ^ tq * ONE : ℕ) : ℤ) (96 * tn * tn * tn) - (P8HI : ℤ))
    + fdiv (-((tn * ONE : ℕ) : ℤ)) (2 * 2 ^ tq)
    + fdiv (-((tn * LPHI : ℕ) : ℤ)) (2 * 2 ^ tq)
    - cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (2 * tn)

/-- Upper bound of `φ · 2^64` (theta bracket upper edge `thetaS t`). -/
def phaseHi (tn tq k nl : ℕ) : ℤ :=
  cdiv ((innerBox tn tq k nl).2 * (tn : ℤ)) (4 * 2 ^ tq)
    + (cdiv ((2 ^ tq * ONE : ℕ) : ℤ) (8 * tn) - (P8LO : ℤ))
    + cdiv (-((tn * ONE : ℕ) : ℤ)) (2 * 2 ^ tq)
    + cdiv (-((tn * LPLO : ℕ) : ℤ)) (2 * 2 ^ tq)











end

end H1000Line


def ArdaRH65K_Turing121_H1000Phase : Nat := 0


