-- Prove2me | solution 1 for ArgHoriz.argChangeHoriz_eq_of_octCert
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:41.664011+00:00
-- url     : https://prove2.me/submissions/08a6fddd-930f-4e2a-911e-19301fbf4605

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
import Theorems.Thm_ArgHoriz_argChangeHoriz_chain
import Theorems.Thm_ArgHoriz_octant_trig
import Theorems.Thm_ThetaValue_arg_eq_arctan_of_re_pos
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





theorem rot_re (θ : ℝ) (w : ℂ) : (rot θ w).re = Real.cos θ * w.re + Real.sin θ * w.im := by
  unfold rot
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
    Real.sin_neg]
  ring

theorem rot_im (θ : ℝ) (w : ℂ) : (rot θ w).im = Real.cos θ * w.im - Real.sin θ * w.re := by
  unfold rot
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
    Real.sin_neg]
  ring







/-! ## 2. One piece: FTC for `log (e^{-iθ} f)` -/



/-! ## 3. The chain of pieces -/



/-! ## 4. Octant charts: integer directions -/

























theorem rot_oct (k : ℤ) (w : ℂ) : ∃ c : ℝ, 0 < c ∧
    (rot (k * Real.pi / 4) w).re = c * octX k w ∧ (rot (k * Real.pi / 4) w).im = c * octY k w := by
  obtain ⟨c, hc, hcos, hsin⟩ := octant_trig k
  refine ⟨c, hc, ?_, ?_⟩
  · rw [rot_re, hcos, hsin]; unfold octX; ring
  · rw [rot_im, hcos, hsin]; unfold octY; ring

theorem rot_oct_re_pos {k : ℤ} {w : ℂ} (h : 0 < octX k w) : 0 < (rot (k * Real.pi / 4) w).re := by
  obtain ⟨c, hc, hre, _⟩ := rot_oct k w
  rw [hre]; exact mul_pos hc h

/-- In octant `k`, the chart angle is the octant angle. -/
theorem chartAngle_oct {k : ℤ} {w : ℂ} (h : 0 < octX k w) :
    chartAngle (k * Real.pi / 4) w = octAngle k w := by
  obtain ⟨c, hc, hre, him⟩ := rot_oct k w
  have hpos : 0 < (rot (k * Real.pi / 4) w).re := by rw [hre]; exact mul_pos hc h
  unfold chartAngle octAngle
  rw [ThetaValue.arg_eq_arctan_of_re_pos hpos, hre, him, mul_div_mul_left _ _ hc.ne']

/-! ## 5. The octant certificate -/



namespace OctCert





end OctCert

theorem theta_step_lt {k k' : ℤ} (h : |k' - k| ≤ 3) :
    |(k' : ℝ) * Real.pi / 4 - k * Real.pi / 4| < Real.pi := by
  have hR : |((k' - k : ℤ) : ℝ)| ≤ 3 := by exact_mod_cast h
  have e : (k' : ℝ) * Real.pi / 4 - k * Real.pi / 4 = ((k' - k : ℤ) : ℝ) * (Real.pi / 4) := by
    push_cast; ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 4)]
  have hpi := Real.pi_pos
  nlinarith



/-! ## 6. Endpoint enclosures -/





















/-! ## 7. The ζ edge in binder form -/







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




theorem solution (f : ℂ → ℂ) (T : ℝ) (c : OctCert) (hm : 1 ≤ c.m)
    (han : ∀ j < c.m, ∀ x ∈ Set.uIcc (c.p j) (c.p (j + 1)), AnalyticAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hstep : c.StepOK) (hnc : c.NoCross f T) :
    DiffractionCore.argChangeHoriz f T (c.p 0) (c.p c.m)
      = octAngle (c.k (c.m - 1)) (f ((c.p c.m : ℂ) + (T : ℂ) * I))
        - octAngle (c.k 0) (f ((c.p 0 : ℂ) + (T : ℂ) * I)) := by
  have hchain := argChangeHoriz_chain f T c.p (fun j => (c.k j : ℝ) * Real.pi / 4) c.m hm han
    (fun j hj x hx => rot_oct_re_pos (hnc j hj x hx))
    (fun j hj => theta_step_lt (hstep j hj))
  unfold DiffractionCore.argChangeHoriz
  rw [hchain.2]
  have hlast : 0 < octX (c.k (c.m - 1)) (f ((c.p c.m : ℂ) + (T : ℂ) * I)) := by
    have := hnc (c.m - 1) (by omega) (c.p c.m)
      (by rw [show c.m - 1 + 1 = c.m by omega]; exact Set.right_mem_uIcc)
    exact this
  have hfirst : 0 < octX (c.k 0) (f ((c.p 0 : ℂ) + (T : ℂ) * I)) :=
    hnc 0 (by omega) (c.p 0) Set.left_mem_uIcc
  rw [chartAngle_oct hlast, chartAngle_oct hfirst]
