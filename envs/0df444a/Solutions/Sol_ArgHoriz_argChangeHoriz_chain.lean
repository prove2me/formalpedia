-- Prove2me | solution 1 for ArgHoriz.argChangeHoriz_chain
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:57.487005+00:00
-- url     : https://prove2.me/submissions/31a9f762-0848-41ce-957d-a509377ff620

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
import Theorems.Thm_ArgHoriz_chartAngle_eq
import Theorems.Thm_ArgHoriz_piece_eq

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


theorem solution (f : ℂ → ℂ) (T : ℝ) (p θ : ℕ → ℝ) :
    ∀ m : ℕ, 1 ≤ m →
      (∀ j < m, ∀ x ∈ Set.uIcc (p j) (p (j + 1)), AnalyticAt ℂ f ((x : ℂ) + (T : ℂ) * I)) →
      (∀ j < m, ∀ x ∈ Set.uIcc (p j) (p (j + 1)), 0 < (rot (θ j) (f ((x : ℂ) + (T : ℂ) * I))).re) →
      (∀ j, j + 1 < m → |θ (j + 1) - θ j| < Real.pi) →
      IntervalIntegrable (fun x : ℝ => logDeriv f ((x : ℂ) + (T : ℂ) * I)) MeasureTheory.volume
          (p 0) (p m) ∧
        (∫ x in p 0..p m, logDeriv f ((x : ℂ) + (T : ℂ) * I)).im
          = chartAngle (θ (m - 1)) (f ((p m : ℂ) + (T : ℂ) * I))
            - chartAngle (θ 0) (f ((p 0 : ℂ) + (T : ℂ) * I)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro han hin _
    exact piece_eq f T (p 0) (p 1) (θ 0) (han 0 (by norm_num)) (hin 0 (by norm_num))
  | succ m hm ih =>
    intro han hin hstep
    obtain ⟨hint, heq⟩ := ih (fun j hj => han j (by omega)) (fun j hj => hin j (by omega))
      (fun j hj => hstep j (by omega))
    obtain ⟨hint', heq'⟩ := piece_eq f T (p m) (p (m + 1)) (θ m) (han m (by omega))
      (hin m (by omega))
    refine ⟨hint.trans hint', ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hint hint', Complex.add_im, heq, heq']
    -- the breakpoint `p m` is in both charts
    have hjoin : chartAngle (θ (m - 1)) (f ((p m : ℂ) + (T : ℂ) * I))
        = chartAngle (θ m) (f ((p m : ℂ) + (T : ℂ) * I)) := by
      have hm1 : m - 1 + 1 = m := by omega
      apply chartAngle_eq
      · have := hin (m - 1) (by omega) (p m) (by rw [hm1]; exact Set.right_mem_uIcc)
        exact this
      · exact hin m (by omega) (p m) Set.left_mem_uIcc
      · have := hstep (m - 1) (by omega)
        rw [hm1] at this
        rw [abs_sub_comm]
        exact this
    rw [hjoin, show m + 1 - 1 = m by omega]
    ring
