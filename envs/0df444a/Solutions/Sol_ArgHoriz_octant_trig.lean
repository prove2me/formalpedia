-- Prove2me | solution 1 for ArgHoriz.octant_trig
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:47:07.759979+00:00
-- url     : https://prove2.me/submissions/39ce289b-db38-440e-b9a7-cbf56416cab7

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
import Theorems.Thm_ArgHoriz_octant_trig_residue
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











theorem octIdx_lt (k : ℤ) : octIdx k < 8 := by
  unfold octIdx
  have h0 : 0 ≤ k % 8 := Int.emod_nonneg k (by norm_num)
  have h8 : k % 8 < 8 := Int.emod_lt_of_pos k (by norm_num)
  omega

theorem octIdx_cast (k : ℤ) : ((octIdx k : ℕ) : ℤ) = k % 8 := by
  unfold octIdx
  exact Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))

















/-! ## 5. The octant certificate -/



namespace OctCert





end OctCert





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


















theorem solution (k : ℤ) :
    ∃ c : ℝ, 0 < c ∧ Real.cos (k * Real.pi / 4) = c * octA k ∧
      Real.sin (k * Real.pi / 4) = c * octB k := by
  have hk : (k : ℝ) * Real.pi / 4 = (octIdx k : ℝ) * Real.pi / 4 + ((k / 8 : ℤ) : ℝ) * (2 * Real.pi) := by
    have h : k = k % 8 + 8 * (k / 8) := by omega
    have hc : ((octIdx k : ℕ) : ℝ) = ((k % 8 : ℤ) : ℝ) := by
      rw [← octIdx_cast]; push_cast; ring
    rw [hc]
    have h' : (k : ℝ) = ((k % 8 : ℤ) : ℝ) + 8 * ((k / 8 : ℤ) : ℝ) := by exact_mod_cast h
    rw [h']
    ring
  obtain ⟨c, hc, hcos, hsin⟩ := octant_trig_residue (octIdx k) (octIdx_lt k)
  refine ⟨c, hc, ?_, ?_⟩
  · rw [hk, Real.cos_add_int_mul_two_pi, hcos]; rfl
  · rw [hk, Real.sin_add_int_mul_two_pi, hsin]; rfl
