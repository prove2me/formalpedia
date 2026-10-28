-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_Arb4_Gamma
-- name    : ArdaRH65K_Turing121_Arb4_Gamma
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:14:58.151736+00:00
-- url     : https://prove2.me/theorems/bdddc413-703a-42f8-aa3a-e52bd613cd41
-- title:
--   Arb4 Gamma certificate definitions
-- statement:
--   This bundle defines rational gamma-factor and arctangent enclosures and their checks. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{Arb4.l2lo},\;\mathtt{Arb4.l2hi},\;\mathtt{Arb4.lplo},\;\mathtt{Arb4.lphi}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Gamma.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgGammaR
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
import Mathlib.Analysis.PSeries
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
/-  Arb4_Gamma.lean -- lane Arb4 (h1000 compaction): the Γℝ argument-change side conditions of a
    Turing band (brick K6b, `ArgGammaR`) as ONE Boolean kernel check.

    `ArgChangeGlue.K6Side` compares the band's enclosures `[L4, H4]`, `[L5, H5]` with the closed-form
    brackets `Sm1`, `S2` of `ArgGammaR` at the two edge heights.  The generated module
    `ArgChangeH1000` proves one `log` box, one `arctan` box and one `S2`/`Sm1` box per height by
    `norm_num` over truncated series (about 1 MB of olean per height).  Here:

      * `logOK logLo logHi`, `log_mem`  -- `log v = k log 2 + log (1 - x)`, `v = 2^k (1 - x)`,
                             `0 ≤ x < 1`, with `RSDesignTheta.log2_box` and the Taylor bracket
                             `ArgGammaR.log_one_sub_mem` (n terms);
      * `atanOK arctanLo arctanHi`, `arctan_mem` -- `arctan y` by the Taylor bracket
                             `ArctanTaylor.arctan_bracket` (mode 0, `0 ≤ y ≤ 1`), by
                             `arctan y = π/2 - arctan (1/y)` (mode 1, `y > 0`), or `π/4` (`y = 1`);
      * `GamD`, `gamOK`, `S2_mem`, `Sm1_mem` -- the brackets at one height (`ArgGammaR.S2_mem_of`,
                             `Sm1_mem_of`, `RSDesignTheta.logpi_box`, `π` to 20 digits);
      * `k6B`, `k6B_sound` -- the four K6b comparisons of a band from two heights.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/



open scoped Real

namespace Arb4

open Q

/-! ## A. Constants -/

/-- `log 2` bracket (`RSDesignTheta.log2_box`). -/
def l2lo : Q := frac 3465735902799708427977 5000000000000000000000
def l2hi : Q := frac 6931471805599487910229 10000000000000000000000

/-- `log π` bracket (`RSDesignTheta.logpi_box`). -/
def lplo : Q := frac 11447298858493313056567 10000000000000000000000
def lphi : Q := frac 5723649429247365361409 5000000000000000000000

/-- `π` bracket (`Real.pi_gt_d20`, `Real.pi_lt_d20`). -/
def pilo : Q := frac 314159265358979323846 100000000000000000000
def pihi : Q := frac 314159265358979323847 100000000000000000000







/-! ## B. Logarithms -/

/-- `2^k` for an integer `k`. -/
def pow2Q (k : ℤ) : Q := if 0 ≤ k then ofNat (2 ^ k.toNat) else frac 1 (2 ^ (-k).toNat)





/-- `Σ_{i<n} x^(i+1)/(i+1)`. -/
def lserQ (x : Q) (n : ℕ) : Q := sumQ (fun i => div (npow x (i + 1)) (ofNat (i + 1))) n



/-- `x = 1 - v / 2^k`. -/
def lx (v : Q) (k : ℤ) : Q := sub (ofNat 1) (div v (pow2Q k))

/-- The certificate `(k, n)` of `log v` is admissible: `v > 0`, `0 ≤ x < 1`. -/
def logOK (v : Q) (k : ℤ) : Bool := lt (ofNat 0) v && decide (0 ≤ (lx v k).n) && lt (lx v k) (ofNat 1)

/-- `k log 2`, bracketed. -/
def kl2lo (k : ℤ) : Q := if 0 ≤ k then mul (ofInt k) l2lo else mul (ofInt k) l2hi
def kl2hi (k : ℤ) : Q := if 0 ≤ k then mul (ofInt k) l2hi else mul (ofInt k) l2lo



/-- `1 - x` (the divisor of the Taylor remainder). -/
def omx (x : Q) : Q := sub (ofNat 1) x



/-- Lower and upper bounds of `log v` from the certificate `(k, n)`. -/
def logLo (v : Q) (k : ℤ) (n : ℕ) : Q :=
  sub (sub (kl2lo k) (lserQ (lx v k) n)) (div (npow (lx v k) (n + 1)) (omx (lx v k)))

def logHi (v : Q) (k : ℤ) (n : ℕ) : Q :=
  add (sub (kl2hi k) (lserQ (lx v k) n)) (div (npow (lx v k) (n + 1)) (omx (lx v k)))



/-! ## C. Arctangents -/

/-- `atanPS u N = Σ_{j<N} (-1)^j u^(2j+1)/(2j+1)`. -/
def atanPSQ (u : Q) (N : ℕ) : Q :=
  sumQ (fun j => mul (ofInt ((-1) ^ j)) (div (npow u (2 * j + 1)) (ofNat (2 * j + 1)))) N

/-- The Taylor remainder `u^(2N+1)/(2N+1)`. -/
def atanErrQ (u : Q) (N : ℕ) : Q := div (npow u (2 * N + 1)) (ofNat (2 * N + 1))







/-- The reciprocal `1 / y`. -/
def inv (y : Q) : Q := div (ofNat 1) y

/-- Admissibility of an arctangent certificate: mode 0 needs `0 ≤ y ≤ 1`, mode 1 `y > 0`, mode 2
    `y = 1`. -/
def atanOK (y : Q) : ℕ → Bool
  | 0 => le (ofNat 0) y && le y (ofNat 1)
  | 1 => lt (ofNat 0) y
  | _ => eqB y (ofNat 1)

/-- Lower bound of `arctan y`. -/
def arctanLo (y : Q) (N : ℕ) : ℕ → Q
  | 0 => sub (atanPSQ y N) (atanErrQ y N)
  | 1 => sub (div pilo (ofNat 2)) (add (atanPSQ (inv y) N) (atanErrQ (inv y) N))
  | _ => div pilo (ofNat 4)

/-- Upper bound of `arctan y`. -/
def arctanHi (y : Q) (N : ℕ) : ℕ → Q
  | 0 => add (atanPSQ y N) (atanErrQ y N)
  | 1 => sub (div pihi (ofNat 2)) (sub (atanPSQ (inv y) N) (atanErrQ (inv y) N))
  | _ => div pihi (ofNat 4)






/-! ## D. The closed-form Γℝ brackets at one height -/

/-- The certificate of the brackets at one height `T`: `log (1 + T²/4)` (`k2`, `n2`),
    `log (1/4 + T²/4)` (`km`, `nm`), `arctan (T/2)` (mode `md2`, `N2` terms), `arctan T` (`mdm`, `Nm`). -/
structure GamD where
  T : Q
  k2 : ℤ
  n2 : ℕ
  km : ℤ
  nm : ℕ
  md2 : ℕ
  N2 : ℕ
  mdm : ℕ
  Nm : ℕ

namespace GamD

/-- `1 + T²/4`. -/
def v2 (G : GamD) : Q := add (ofNat 1) (div (npow G.T 2) (ofNat 4))

/-- `1/4 + T²/4`. -/
def vm (G : GamD) : Q := add (frac 1 4) (div (npow G.T 2) (ofNat 4))

/-- `T / 2`. -/
def half (G : GamD) : Q := div G.T (ofNat 2)







end GamD

/-- Admissibility of the height certificate. -/
def gamOK (G : GamD) : Bool :=
  le (ofNat 0) G.T && logOK G.v2 G.k2 && logOK G.vm G.km && atanOK G.half G.md2 && atanOK G.T G.mdm

/-- `S2 T ≥ 1/2 atanLo(T/2) + T/4 logLo(1 + T²/4) - T/2 - T/2 log π⁺`. -/
def S2lo (G : GamD) : Q :=
  sub (sub (add (mul (frac 1 2) (arctanLo G.half G.N2 G.md2)) (mul (div G.T (ofNat 4))
    (logLo G.v2 G.k2 G.n2))) (div G.T (ofNat 2))) (mul (div G.T (ofNat 2)) lphi)

def S2hi (G : GamD) : Q :=
  sub (sub (add (mul (frac 1 2) (arctanHi G.half G.N2 G.md2)) (mul (div G.T (ofNat 4))
    (logHi G.v2 G.k2 G.n2))) (div G.T (ofNat 2))) (mul (div G.T (ofNat 2)) lplo)

/-- `Sm1 T ≥ T/4 logLo(1/4 + T²/4) + atanLo T - T/2 - T/2 log π⁺`. -/
def Sm1lo (G : GamD) : Q :=
  sub (sub (add (mul (div G.T (ofNat 4)) (logLo G.vm G.km G.nm)) (arctanLo G.T G.Nm G.mdm))
    (div G.T (ofNat 2))) (mul (div G.T (ofNat 2)) lphi)

def Sm1hi (G : GamD) : Q :=
  sub (sub (add (mul (div G.T (ofNat 4)) (logHi G.vm G.km G.nm)) (arctanHi G.T G.Nm G.mdm))
    (div G.T (ofNat 2))) (mul (div G.T (ofNat 2)) lplo)





/-! ## E. The K6b comparisons of a band -/

/-- `em1 T = T / (2 (1 + T²))`. -/
def em1Q (T : Q) : Q := div T (mul (ofNat 2) (add (ofNat 1) (npow T 2)))

/-- `e2 T = T / (2 (4 + T²))`. -/
def e2Q (T : Q) : Q := div T (mul (ofNat 2) (add (ofNat 4) (npow T 2)))







/-- **The K6b check of a band** with edge heights `G0.T ≤ G1.T`: `[L4, H4] ⊇` the `σ = -1` bracket,
    `[L5, H5] ⊇` the `σ = 2` bracket. -/
def k6B (G0 G1 : GamD) (L4 H4 L5 H5 : Q) : Bool :=
  gamOK G0 && gamOK G1 &&
    le L4 (sub (sub (Sm1lo G1) (Sm1hi G0)) (em1Q G1.T)) &&
    le (add (sub (Sm1hi G1) (Sm1lo G0)) (em1Q G0.T)) H4 &&
    le L5 (sub (sub (S2lo G1) (S2hi G0)) (e2Q G1.T)) &&
    le (add (sub (S2hi G1) (S2lo G0)) (e2Q G0.T)) H5



end Arb4


def ArdaRH65K_Turing121_Arb4_Gamma : Nat := 0


