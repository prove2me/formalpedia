-- Prove2me | solution 1 for ArgHoriz.octAngle_mem_of_box
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:29:45.538763+00:00
-- url     : https://prove2.me/submissions/b5991514-7140-4321-aecb-55f9e4c42e0e

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

/-- An affine form nonnegative at the four corners of a box is nonnegative on the box. -/
theorem affine_nonneg_of_corners {u v a0 a1 b0 b1 a b : ℝ} (ha : a0 ≤ a ∧ a ≤ a1)
    (hb : b0 ≤ b ∧ b ≤ b1) (h00 : 0 ≤ u * a0 + v * b0) (h01 : 0 ≤ u * a0 + v * b1)
    (h10 : 0 ≤ u * a1 + v * b0) (h11 : 0 ≤ u * a1 + v * b1) : 0 ≤ u * a + v * b := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 hu, mul_le_mul_of_nonneg_left hb.1 hv]
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 hu, mul_le_mul_of_nonpos_left hb.2 hv]
  · nlinarith [mul_le_mul_of_nonpos_left ha.2 hu, mul_le_mul_of_nonneg_left hb.1 hv]
  · nlinarith [mul_le_mul_of_nonpos_left ha.2 hu, mul_le_mul_of_nonpos_left hb.2 hv]

/-- An affine form positive at the four corners of a box is positive on the box. -/
theorem affine_pos_of_corners {u v a0 a1 b0 b1 a b : ℝ} (ha : a0 ≤ a ∧ a ≤ a1)
    (hb : b0 ≤ b ∧ b ≤ b1) (h00 : 0 < u * a0 + v * b0) (h01 : 0 < u * a0 + v * b1)
    (h10 : 0 < u * a1 + v * b0) (h11 : 0 < u * a1 + v * b1) : 0 < u * a + v * b := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 hu, mul_le_mul_of_nonneg_left hb.1 hv]
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 hu, mul_le_mul_of_nonpos_left hb.2 hv]
  · nlinarith [mul_le_mul_of_nonpos_left ha.2 hu, mul_le_mul_of_nonneg_left hb.1 hv]
  · nlinarith [mul_le_mul_of_nonpos_left ha.2 hu, mul_le_mul_of_nonpos_left hb.2 hv]

















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





/-! ## 6. Endpoint enclosures -/










theorem solution {k : ℤ} {w : ℂ} {a0 a1 b0 b1 qlo qhi : ℝ}
    (hw : InBox w a0 a1 b0 b1)
    (hX00 : 0 < (octA k : ℝ) * a0 + octB k * b0) (hX01 : 0 < (octA k : ℝ) * a0 + octB k * b1)
    (hX10 : 0 < (octA k : ℝ) * a1 + octB k * b0) (hX11 : 0 < (octA k : ℝ) * a1 + octB k * b1)
    (hL00 : qlo * ((octA k : ℝ) * a0 + octB k * b0) ≤ (octA k : ℝ) * b0 - octB k * a0)
    (hL01 : qlo * ((octA k : ℝ) * a0 + octB k * b1) ≤ (octA k : ℝ) * b1 - octB k * a0)
    (hL10 : qlo * ((octA k : ℝ) * a1 + octB k * b0) ≤ (octA k : ℝ) * b0 - octB k * a1)
    (hL11 : qlo * ((octA k : ℝ) * a1 + octB k * b1) ≤ (octA k : ℝ) * b1 - octB k * a1)
    (hH00 : (octA k : ℝ) * b0 - octB k * a0 ≤ qhi * ((octA k : ℝ) * a0 + octB k * b0))
    (hH01 : (octA k : ℝ) * b1 - octB k * a0 ≤ qhi * ((octA k : ℝ) * a0 + octB k * b1))
    (hH10 : (octA k : ℝ) * b0 - octB k * a1 ≤ qhi * ((octA k : ℝ) * a1 + octB k * b0))
    (hH11 : (octA k : ℝ) * b1 - octB k * a1 ≤ qhi * ((octA k : ℝ) * a1 + octB k * b1)) :
    0 < octX k w ∧ k * Real.pi / 4 + Real.arctan qlo ≤ octAngle k w ∧
      octAngle k w ≤ k * Real.pi / 4 + Real.arctan qhi := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ := hw
  set α : ℝ := (octA k : ℝ)
  set β : ℝ := (octB k : ℝ)
  have hX : 0 < octX k w :=
    affine_pos_of_corners (u := α) (v := β) ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ hX00 hX01 hX10 hX11
  -- `Y - qlo X = (-β - qlo α) a + (α - qlo β) b`, affine in `(a, b)`
  have hlo : qlo * octX k w ≤ octY k w := by
    have h := affine_nonneg_of_corners (u := -β - qlo * α) (v := α - qlo * β)
      (a := w.re) (b := w.im) ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
      (by nlinarith [hL00]) (by nlinarith [hL01]) (by nlinarith [hL10]) (by nlinarith [hL11])
    unfold octX octY
    nlinarith [h]
  have hhi : octY k w ≤ qhi * octX k w := by
    have h := affine_nonneg_of_corners (u := qhi * α + β) (v := qhi * β - α)
      (a := w.re) (b := w.im) ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
      (by nlinarith [hH00]) (by nlinarith [hH01]) (by nlinarith [hH10]) (by nlinarith [hH11])
    unfold octX octY
    nlinarith [h]
  refine ⟨hX, ?_, ?_⟩
  · unfold octAngle
    have : qlo ≤ octY k w / octX k w := by rw [le_div_iff₀ hX]; linarith
    have := Real.arctan_le_arctan_iff.mpr this
    linarith
  · unfold octAngle
    have : octY k w / octX k w ≤ qhi := by rw [div_le_iff₀ hX]; linarith
    have := Real.arctan_le_arctan_iff.mpr this
    linarith
