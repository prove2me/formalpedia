-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
-- name    : ArdaRH65K_Turing121_ArgHoriz
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:07:18.426149+00:00
-- url     : https://prove2.me/theorems/43d5ca07-2246-4807-a670-7bedab9cbf72
-- title:
--   ArgHoriz certificate definitions
-- statement:
--   This bundle defines rotated-octant data and checks for horizontal argument changes. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ArgHoriz.rot},\;\mathtt{ArgHoriz.chartAngle},\;\mathtt{ArgHoriz.octIdx},\;\mathtt{ArgHoriz.octAN}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/ArgHoriz.lean

import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
/-  ArgHoriz.lean -- brick K6c of the ANDURIL Arb discharge: piecewise half-plane tracking of the
    horizontal argument change (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row
    H2e, brick K6c).

    THE BINDERS IT REDUCES.  Conjuncts 6 and 7 of the `hArbT` binder of every emitted Turing band
    (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) are

        hAHt : DiffractionCore.argChangeHoriz riemannZeta T1 2 (-1) ∈ Set.Icc L2 H2,
        hAHb : DiffractionCore.argChangeHoriz riemannZeta T0 2 (-1) ∈ Set.Icc L3 H3,

    the argument change of ζ along the horizontal edges `[2, -1] + i T` of the RvM rectangle
    (20,758 binders at h280000, 13,235 distinct heights).  Unlike K6a/K6b these are NOT generic:
    they need values of ζ off the line.  This file proves the reduction theorem that turns them
    into a finite, kernel-checkable certificate, so that only ENCLOSURES remain.

    THE CERTIFICATE (`OctCert`).  Breakpoints `2 = p 0, p 1, ..., p m = -1` and one integer label
    `k j` per piece `[p j, p (j+1)]`, the octant direction `k j · π/4`.  It is valid when
      * `StepOK`   : consecutive labels differ by at most 3 (a decidable check on integers);
      * `NoCross`  : on piece `j`, ζ never crosses the line through 0 orthogonal to the octant
                     direction: `0 < α Re ζ(x + i T) + β Im ζ(x + i T)` for all `x` in the piece,
                     `(α, β) ∈ {(1,0),(1,1),(0,1),(-1,1),(-1,0),(-1,-1),(0,-1),(1,-1)}` the integer
                     octant vector (`octX`).  One strict sign condition per piece: a range
                     enclosure of ζ over the piece that avoids the octant boundary discharges it
                     (`octX_pos_of_box`, bundled per certificate as `OctCert.noCross_of_boxes`).
    Then (`argChangeHoriz_eq_of_octCert`, EXACT, no approximation):

        argChangeHoriz ζ T 2 (-1) = octAngle (k (m-1)) ζ(-1 + i T) - octAngle (k 0) ζ(2 + i T),
        octAngle k w = k π/4 + arctan ((α Im w - β Re w)/(α Re w + β Im w)).

    Every interior breakpoint cancels exactly: the chart angles of the two pieces meeting there
    agree (`chartAngle_eq`), because both charts contain the point and their directions differ by
    less than π.  So the only numerics left are TWO POINT ENCLOSURES, of ζ(2 + i T) and ζ(-1 + i T),
    turned into an arctan interval by `octAngle_mem_of_box` and the rational arctan brackets
    `atanLo ≤ arctan ≤ atanHi` (the emitter may use the sharper `ArctanTaylor.arctan_bracket`).
    `hAH_of_octCert_boxes` is the end-to-end binder-form statement.

    THE GENERAL THEOREM behind it (`argChangeHoriz_chain`): for any `f` analytic along the segment
    and any real chart directions `θ j` with `|θ (j+1) - θ j| < π` and `0 < Re (e^{-i θ j} f)` on
    piece `j`, the horizontal argument change is `chartAngle (θ (m-1)) f(end) - chartAngle (θ 0)
    f(start)`, `chartAngle θ w = θ + arg (e^{-i θ} w)` (FTC for `log (e^{-i θ} f)` on each piece).

    WHAT IS NOT HERE.  The off-line ζ evaluator (memo brick B6) that produces the `NoCross` range
    enclosures and the two endpoint point enclosures, and the functional-equation fold K6d.

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  A reduction of one edge of a finite zero count to finitely many
    enclosures; nothing here bears on the Riemann Hypothesis. -/





open Complex

namespace ArgHoriz

/-! ## 1. Charts: rotated principal arguments -/

/-- The value `w` seen in the chart of direction `θ`: `e^{-iθ} w`. -/
noncomputable def rot (θ : ℝ) (w : ℂ) : ℂ := Complex.exp (((-θ : ℝ) : ℂ) * I) * w

/-- The chart angle of `w` in direction `θ`: `θ + arg (e^{-iθ} w)`, an argument of `w`. -/
noncomputable def chartAngle (θ : ℝ) (w : ℂ) : ℝ := θ + Complex.arg (rot θ w)











/-! ## 2. One piece: FTC for `log (e^{-iθ} f)` -/



/-! ## 3. The chain of pieces -/



/-! ## 4. Octant charts: integer directions -/

/-- The octant index `k mod 8 ∈ {0, ..., 7}`. -/
def octIdx (k : ℤ) : ℕ := (k % 8).toNat

/-- First coordinate of the integer octant vector, by residue `r = k mod 8`. -/
def octAN : ℕ → ℤ
  | 0 => 1 | 1 => 1 | 2 => 0 | 3 => -1 | 4 => -1 | 5 => -1 | 6 => 0 | _ => 1

/-- Second coordinate of the integer octant vector, by residue `r = k mod 8`. -/
def octBN : ℕ → ℤ
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 0 | 5 => -1 | 6 => -1 | _ => -1

/-- First coordinate of the integer octant vector of direction `k π/4`. -/
def octA (k : ℤ) : ℤ := octAN (octIdx k)

/-- Second coordinate of the integer octant vector of direction `k π/4`. -/
def octB (k : ℤ) : ℤ := octBN (octIdx k)









/-- The chart-`k` real part in integer form: `α Re w + β Im w` (a positive multiple of
    `Re (e^{-i k π/4} w)`). -/
noncomputable def octX (k : ℤ) (w : ℂ) : ℝ := (octA k : ℝ) * w.re + (octB k : ℝ) * w.im

/-- The chart-`k` imaginary part in integer form: `α Im w - β Re w`. -/
noncomputable def octY (k : ℤ) (w : ℂ) : ℝ := (octA k : ℝ) * w.im - (octB k : ℝ) * w.re

/-- The octant angle `k π/4 + arctan (octY/octX)`: the chart angle of `w` in octant `k`. -/
noncomputable def octAngle (k : ℤ) (w : ℂ) : ℝ :=
  k * Real.pi / 4 + Real.arctan (octY k w / octX k w)







/-! ## 5. The octant certificate -/

/-- **An octant certificate** for a horizontal segment: `m` pieces with breakpoints `p 0 .. p m`
    and one octant label `k j` per piece. -/
structure OctCert where
  m : ℕ
  p : ℕ → ℝ
  k : ℕ → ℤ

namespace OctCert

/-- Consecutive octant labels differ by at most 3 (so the directions differ by less than π). -/
def StepOK (c : OctCert) : Prop := ∀ j, j + 1 < c.m → |c.k (j + 1) - c.k j| ≤ 3

/-- **No zero crossing**: on piece `j`, `f(x + i T)` stays strictly on the positive side of the
    octant line: `0 < α Re f + β Im f`. -/
def NoCross (c : OctCert) (f : ℂ → ℂ) (T : ℝ) : Prop :=
  ∀ j < c.m, ∀ x ∈ Set.uIcc (c.p j) (c.p (j + 1)), 0 < octX (c.k j) (f ((x : ℂ) + (T : ℂ) * I))

end OctCert





/-! ## 6. Endpoint enclosures -/





/-- A complex box `[a0, a1] x [b0, b1]`. -/
def InBox (w : ℂ) (a0 a1 b0 b1 : ℝ) : Prop := a0 ≤ w.re ∧ w.re ≤ a1 ∧ b0 ≤ w.im ∧ w.im ≤ b1





/-- Rational lower bound for `arctan q`: `q - q³/3` for `q ≥ 0`, `q` for `q < 0`. -/
noncomputable def atanLo (q : ℝ) : ℝ := if 0 ≤ q then q - q ^ 3 / 3 else q

/-- Rational upper bound for `arctan q`: `q` for `q ≥ 0`, `q - q³/3` for `q < 0`. -/
noncomputable def atanHi (q : ℝ) : ℝ := if 0 ≤ q then q else q - q ^ 3 / 3







/-! ## 7. The ζ edge in binder form -/







/-! ## 8. Non-vacuity: the certificate on `f = id` -/





end ArgHoriz


def ArdaRH65K_Turing121_ArgHoriz : Nat := 0


