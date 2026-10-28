-- Prove2me | solution 1 for ArgHoriz.hAH_of_octCert_boxes
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:01:26.579545+00:00
-- url     : https://prove2.me/submissions/5933475a-4c88-448c-bd28-e458a22076a7

import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
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
import Theorems.Thm_ArgHoriz_argChangeHoriz_eq_of_octCert
import Theorems.Thm_ArgHoriz_octAngle_mem_of_box
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















/-! ## 2. One piece: FTC for `log (e^{-iθ} f)` -/



/-! ## 3. The chain of pieces -/



/-! ## 4. Octant charts: integer directions -/































/-! ## 5. The octant certificate -/



namespace OctCert





end OctCert





/-! ## 6. Endpoint enclosures -/





















/-! ## 7. The ζ edge in binder form -/

/-- ζ is analytic along every horizontal line off the real axis. -/
theorem zeta_analyticAt_horiz {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    AnalyticAt ℂ riemannZeta ((x : ℂ) + (T : ℂ) * I) := by
  apply analyticOn_riemannZeta
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hT this

/-- **K6c, exact form for the RvM edge `[2, -1] + i T`.**  For `T ≠ 0` and a valid octant
    certificate from `2` to `-1`:
        `argChangeHoriz ζ T 2 (-1) = octAngle (k (m-1)) ζ(-1 + i T) - octAngle (k 0) ζ(2 + i T)`. -/
theorem argChangeHoriz_zeta_eq_of_octCert {T : ℝ} (hT : T ≠ 0) (c : OctCert) (hm : 1 ≤ c.m)
    (hp0 : c.p 0 = 2) (hpm : c.p c.m = -1) (hstep : c.StepOK) (hnc : c.NoCross riemannZeta T) :
    DiffractionCore.argChangeHoriz riemannZeta T 2 (-1)
      = octAngle (c.k (c.m - 1)) (riemannZeta (((-1 : ℝ) : ℂ) + (T : ℂ) * I))
        - octAngle (c.k 0) (riemannZeta (((2 : ℝ) : ℂ) + (T : ℂ) * I)) := by
  have h := argChangeHoriz_eq_of_octCert riemannZeta T c hm
    (fun _ _ x _ => zeta_analyticAt_horiz hT x) hstep hnc
  rw [hp0, hpm] at h
  exact h



/-! ## 8. Non-vacuity: the certificate on `f = id` -/





end ArgHoriz


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

section
namespace ArgHoriz
end ArgHoriz
open ArgHoriz

/-! ## 1. Charts: rotated principal arguments -/















/-! ## 2. One piece: FTC for `log (e^{-iθ} f)` -/



/-! ## 3. The chain of pieces -/



/-! ## 4. Octant charts: integer directions -/































/-! ## 5. The octant certificate -/



section
namespace ArgHoriz.OctCert
end ArgHoriz.OctCert
open ArgHoriz.OctCert





end





/-! ## 6. Endpoint enclosures -/





















/-! ## 7. The ζ edge in binder form -/






theorem solution {T L H : ℝ} (hT : T ≠ 0) (c : OctCert) (hm : 1 ≤ c.m)
    (hp0 : c.p 0 = 2) (hpm : c.p c.m = -1) (hstep : c.StepOK) (hnc : c.NoCross riemannZeta T)
    {a0 a1 b0 b1 qlo0 qhi0 : ℝ}
    (hw0 : InBox (riemannZeta (((2 : ℝ) : ℂ) + (T : ℂ) * I)) a0 a1 b0 b1)
    (hS0 : ∀ a ∈ ({a0, a1} : Set ℝ), ∀ b ∈ ({b0, b1} : Set ℝ),
      0 < (octA (c.k 0) : ℝ) * a + octB (c.k 0) * b ∧
      qlo0 * ((octA (c.k 0) : ℝ) * a + octB (c.k 0) * b) ≤ (octA (c.k 0) : ℝ) * b - octB (c.k 0) * a ∧
      (octA (c.k 0) : ℝ) * b - octB (c.k 0) * a ≤ qhi0 * ((octA (c.k 0) : ℝ) * a + octB (c.k 0) * b))
    {c0 c1 d0 d1 qlo1 qhi1 : ℝ}
    (hw1 : InBox (riemannZeta (((-1 : ℝ) : ℂ) + (T : ℂ) * I)) c0 c1 d0 d1)
    (hS1 : ∀ a ∈ ({c0, c1} : Set ℝ), ∀ b ∈ ({d0, d1} : Set ℝ),
      0 < (octA (c.k (c.m - 1)) : ℝ) * a + octB (c.k (c.m - 1)) * b ∧
      qlo1 * ((octA (c.k (c.m - 1)) : ℝ) * a + octB (c.k (c.m - 1)) * b)
        ≤ (octA (c.k (c.m - 1)) : ℝ) * b - octB (c.k (c.m - 1)) * a ∧
      (octA (c.k (c.m - 1)) : ℝ) * b - octB (c.k (c.m - 1)) * a
        ≤ qhi1 * ((octA (c.k (c.m - 1)) : ℝ) * a + octB (c.k (c.m - 1)) * b))
    (hL : L ≤ ((c.k (c.m - 1) : ℝ) - c.k 0) * Real.pi / 4 + Real.arctan qlo1 - Real.arctan qhi0)
    (hH : ((c.k (c.m - 1) : ℝ) - c.k 0) * Real.pi / 4 + Real.arctan qhi1 - Real.arctan qlo0 ≤ H) :
    DiffractionCore.argChangeHoriz riemannZeta T 2 (-1) ∈ Set.Icc L H := by
  rw [argChangeHoriz_zeta_eq_of_octCert hT c hm hp0 hpm hstep hnc]
  have m00 := hS0 a0 (by simp) b0 (by simp)
  have m01 := hS0 a0 (by simp) b1 (by simp)
  have m10 := hS0 a1 (by simp) b0 (by simp)
  have m11 := hS0 a1 (by simp) b1 (by simp)
  have n00 := hS1 c0 (by simp) d0 (by simp)
  have n01 := hS1 c0 (by simp) d1 (by simp)
  have n10 := hS1 c1 (by simp) d0 (by simp)
  have n11 := hS1 c1 (by simp) d1 (by simp)
  obtain ⟨_, h0lo, h0hi⟩ := octAngle_mem_of_box hw0 m00.1 m01.1 m10.1 m11.1
    m00.2.1 m01.2.1 m10.2.1 m11.2.1 m00.2.2 m01.2.2 m10.2.2 m11.2.2
  obtain ⟨_, h1lo, h1hi⟩ := octAngle_mem_of_box hw1 n00.1 n01.1 n10.1 n11.1
    n00.2.1 n01.2.1 n10.2.1 n11.2.1 n00.2.2 n01.2.2 n10.2.2 n11.2.2
  constructor
  · have e : ((c.k (c.m - 1) : ℝ) - c.k 0) * Real.pi / 4
        = (c.k (c.m - 1) : ℝ) * Real.pi / 4 - (c.k 0 : ℝ) * Real.pi / 4 := by ring
    rw [e] at hL
    linarith
  · have e : ((c.k (c.m - 1) : ℝ) - c.k 0) * Real.pi / 4
        = (c.k (c.m - 1) : ℝ) * Real.pi / 4 - (c.k 0 : ℝ) * Real.pi / 4 := by ring
    rw [e] at hH
    linarith
