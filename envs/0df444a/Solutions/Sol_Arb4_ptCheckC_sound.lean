-- Prove2me | solution 1 for Arb4.ptCheckC_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:19:45.509616+00:00
-- url     : https://prove2.me/submissions/e6b91ab8-fe66-47ad-a35e-6ba9e33968c9

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Line
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_H1000Line
import Definitions.Def_ArdaRH65K_Turing121_H1000Phase
import Definitions.Def_ArdaRH65K_Turing121_H1000Point
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
import Theorems.Thm_Arb4_ptCheckC_spec
import Theorems.Thm_ArbEcon_OrderK_valid64
import Theorems.Thm_ArbEcon_step_sound
import Theorems.Thm_H1000Line_s_ball
import Theorems.Thm_H1000Line_trig_phase
import Theorems.Thm_H1000Line_zball_sound
import Theorems.Thm_KernelGammaEnvelope_gLine_decomp_explicit
import Theorems.Thm_KernelGammaEnvelope_gammaRMag_bounds
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
/-  Probes/ArbEconomics_Sound.lean -- soundness of the Nat-only zeta evaluator (ArbEconomics_Eval).

    Every function of `ArbEconomics_Eval` is shown to produce a TRUE enclosure:
      * `logInc`   : `S <= (log m - log (m-1)) 2^P <= S + K + T`
                     (Mathlib `Real.hasSum_pow_div_log_of_abs_lt_one`, `abs_log_sub_add_sum_range_le`);
      * `termOf`   : `Rlo <= 2^P / sqrt m <= Rhi` for ANY Newton iterate (two-sided validation);
      * `trig`     : cos/sin balls of `theta` from the (pi/2)-reduction, the Horner scheme
                     (Mathlib `Complex.exp_bound`) and the quadrant rotation;
      * `step`/`run` : the loop invariant `Inv` (log bracket + Re/Im balls of the partial zeta sum).

    The main theorem `run_sound` turns a kernel-checked chunk equation
    `St.beq (run cfg L s) s' = true` into `Inv n s -> Inv (n + L) s'`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/










open Real Finset

namespace ArbEcon

/-! ## A. floor division / shifts, cast to ℝ -/











/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























/-! ## H. the zeta term, the term product, one step, the run -/











theorem inv_init (c : Cfg) (t : ℝ) (hone : c.one = 2 ^ c.P) : Inv c t 1 (St.init c) := by
  have hps : psum t 1 = 1 := by simp [psum]
  refine ⟨rfl, le_rfl, ?_, ?_, ?_, ?_⟩ <;> simp [St.init, hps, hone]





theorem run_sound (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) :
    ∀ (L n : ℕ) (s : St), Inv c t n s → Inv c t (n + L) (run c L s) := by
  intro L
  induction L with
  | zero => intro n s h; exact h
  | succ L ih =>
    intro n s h
    have := ih (n + 1) (step c s) (step_sound c t K hv n s h)
    rw [show n + (L + 1) = n + 1 + L by ring]
    exact this





end ArbEcon


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









/-! ## B. The series `-log (1 - a/b) = Σ_j (a/b)^(j+1)/(j+1)` in fixed point (scale `2^64`). -/





















/-! ## C. Scaled constants: `log 2`, `log π`, `π/8`, `2π` at scale `2^64`. -/


















/-! ## D. The Riemann-Siegel phase `φ = Λ - (t/2) log π` at `t = tn / 2^tq`. -/











theorem phaseOk_spec {tn tq k : ℕ} (h : phaseOk tn tq k = true) :
    2 ^ k ≤ AA tn tq ∧ AA tn tq < 2 * 2 ^ k ∧ 2 * tq + 4 ≤ k ∧ 1 ≤ tn ∧ 2 ^ tq ≤ 2 * tn := by
  simp only [phaseOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩









end

end H1000Line


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



























/-! ## F. The product ball and the sign test. -/

























/-- The sign of `gLine t` is the sign of `S = cos φ Re ζ - sin φ Im ζ` (`M(t) > 0`). -/
theorem gLine_eq_mag_mul (p : LinePt) (htpos : 0 < tOf p) :
    ∃ Λ : ℝ, Tendsto (ThetaGap.imLnVal (1 / 4) (tOf p / 2)) atTop (𝓝 Λ) ∧
      0 < KernelGammaEnvelope.gammaRMag (tOf p) ∧
      XiLineZeros.gLine (tOf p) = KernelGammaEnvelope.gammaRMag (tOf p)
        * (Real.cos (phiOf p Λ) * (riemannZeta (sOf (tOf p))).re
          - Real.sin (phiOf p Λ) * (riemannZeta (sOf (tOf p))).im) := by
  obtain ⟨Λ, hΛ, hdec⟩ := KernelGammaEnvelope.gLine_decomp_explicit (tOf p) (ne_of_gt htpos)
  have hMpos : 0 < KernelGammaEnvelope.gammaRMag (tOf p) :=
    lt_of_lt_of_le (by positivity) (KernelGammaEnvelope.gammaRMag_bounds (tOf p)).1
  exact ⟨Λ, hΛ, hMpos, hdec⟩

end

end H1000Line


/-  Arb4_Line.lean -- lane Arb4 (h1000 compaction): the on-line sign certificate of a Turing band
    with the evaluator states recomputed in the kernel (brick K4 in EM form, `H1000Line`).

    The band modules `H1000Line_Bxx` of lane h1000-prep store, per grid point, the two evaluator
    states after `N - 1` and `N` Dirichlet terms as computable definitions (compiled to IR: about
    20 KB of olean per point).  Here a point is `mkPt tn tq N Q r k nl m pos`, whose states ARE the
    evaluator runs (`ArbEcon.run`), so `H1000Line.ptCheck (mkPt …)` recomputes them, and a whole band
    is ONE Boolean `bandB` run by ONE `decide +kernel`:

      * `mkPt`            -- a point record with recomputed states;
      * `allB`, `allB_sound` -- every point of a list passes `H1000Line.ptCheck`;
      * `bandB`, `bandB_sound` -- the band: `allB` and `H1000Line.bandOk` give the band's verbatim
                             `hLine` (`n` increasing zeros of `completedRiemannZeta` on the critical
                             line in `[T0, T1]`) through `H1000Line.band_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  Finite interval
    arithmetic and the intermediate value theorem; nothing here bears on the Riemann Hypothesis.
-/


namespace Arb4











/-! ## Points with the states computed ONCE (no `dirOk` comparison) -/









/-- The evaluator invariants of a point's states (they are the runs, `ArbEcon.run_sound`). -/
theorem pt_inv (d : PtD) (hN : 2 ≤ d.N) :
    ArbEcon.Inv (ArbEcon.OrderK.cfg64 d.pt.tn d.pt.tq) (H1000Line.tOf d.pt) (d.pt.N - 1) d.pt.s1 ∧
      ArbEcon.Inv (ArbEcon.OrderK.cfg64 d.pt.tn d.pt.tq) (H1000Line.tOf d.pt) d.pt.N d.pt.s2 := by
  have hv := ArbEcon.OrderK.valid64 d.tn d.tq (H1000Line.tOf d.pt) rfl
  have i0 := ArbEcon.inv_init (ArbEcon.OrderK.cfg64 d.tn d.tq) (H1000Line.tOf d.pt) hv.one_eq
  have i1 := ArbEcon.run_sound _ _ 9 hv (d.N - 2) 1 _ i0
  rw [show 1 + (d.N - 2) = d.N - 1 by omega] at i1
  have i2 := ArbEcon.run_sound _ _ 9 hv 1 (d.N - 1) _ i1
  rw [show d.N - 1 + 1 = d.N by omega] at i2
  exact ⟨i1, i2⟩











end Arb4


/-  Arb4_Line.lean -- lane Arb4 (h1000 compaction): the on-line sign certificate of a Turing band
    with the evaluator states recomputed in the kernel (brick K4 in EM form, `H1000Line`).

    The band modules `H1000Line_Bxx` of lane h1000-prep store, per grid point, the two evaluator
    states after `N - 1` and `N` Dirichlet terms as computable definitions (compiled to IR: about
    20 KB of olean per point).  Here a point is `mkPt tn tq N Q r k nl m pos`, whose states ARE the
    evaluator runs (`ArbEcon.run`), so `H1000Line.ptCheck (mkPt …)` recomputes them, and a whole band
    is ONE Boolean `bandB` run by ONE `decide +kernel`:

      * `mkPt`            -- a point record with recomputed states;
      * `allB`, `allB_sound` -- every point of a list passes `H1000Line.ptCheck`;
      * `bandB`, `bandB_sound` -- the band: `allB` and `H1000Line.bandOk` give the band's verbatim
                             `hLine` (`n` increasing zeros of `completedRiemannZeta` on the critical
                             line in `[T0, T1]`) through `H1000Line.band_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  Finite interval
    arithmetic and the intermediate value theorem; nothing here bears on the Riemann Hypothesis.
-/


section
namespace Arb4
end Arb4
open Arb4











/-! ## Points with the states computed ONCE (no `dirOk` comparison) -/












open H1000Line Filter Topology

theorem solution (d : PtD) (h : ptCheckC d.pt = true) :
    (d.pt.pos = true → 0 < XiLineZeros.gLine (tOf d.pt)) ∧
      (d.pt.pos = false → XiLineZeros.gLine (tOf d.pt) < 0) := by
  obtain ⟨hN, hR, hED, hph, hlo0, hpos, hneg⟩ := ptCheckC_spec h
  obtain ⟨h1, h2⟩ := pt_inv d hN
  obtain ⟨hW, hX, hY⟩ := zball_sound d.pt hN h1 h2 hR hED
  obtain ⟨_, _, _, htn, _⟩ := phaseOk_spec hph
  have htpos : 0 < tOf d.pt := by
    have : (0 : ℝ) < d.pt.tn := by exact_mod_cast htn
    unfold tOf; positivity
  obtain ⟨Λ, hΛ, hMpos, hgl⟩ := gLine_eq_mag_mul d.pt htpos
  obtain ⟨hc, hsn⟩ := trig_phase d.pt hph hlo0 Λ hΛ
  have hSW := s_ball d.pt Λ hc hsn hX hY
  set S := Real.cos (phiOf d.pt Λ) * (riemannZeta (ArbEcon.sOf (tOf d.pt))).re
    - Real.sin (phiOf d.pt Λ) * (riemannZeta (ArbEcon.sOf (tOf d.pt))).im with hS
  have hKpos : (0 : ℝ) < 2 ^ 64 * (zW d.pt : ℝ) := by positivity
  have eK : S * 2 ^ 64 * (zW d.pt : ℝ) = S * (2 ^ 64 * (zW d.pt : ℝ)) := by ring
  rw [abs_le] at hSW
  constructor
  · intro hp
    have hs' : ((sRad d.pt : ℤ) : ℝ) < ((sCtr d.pt : ℤ) : ℝ) := by exact_mod_cast hpos hp
    have hSpos : 0 * (2 ^ 64 * (zW d.pt : ℝ)) < S * (2 ^ 64 * (zW d.pt : ℝ)) := by
      rw [zero_mul, ← eK]; linarith [hSW.1]
    have : 0 < S := lt_of_mul_lt_mul_right hSpos hKpos.le
    rw [hgl]; exact mul_pos hMpos this
  · intro hp
    have hs' : ((sCtr d.pt : ℤ) : ℝ) + ((sRad d.pt : ℤ) : ℝ) < 0 := by exact_mod_cast hneg hp
    have hSneg : S * (2 ^ 64 * (zW d.pt : ℝ)) < 0 * (2 ^ 64 * (zW d.pt : ℝ)) := by
      rw [zero_mul, ← eK]; linarith [hSW.2]
    have : S < 0 := lt_of_mul_lt_mul_right hSneg hKpos.le
    rw [hgl]; exact mul_neg_of_pos_of_neg hMpos this
