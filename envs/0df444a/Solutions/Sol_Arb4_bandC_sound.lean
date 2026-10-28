-- Prove2me | solution 1 for Arb4.bandC_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:23:07.978255+00:00
-- url     : https://prove2.me/submissions/825cb0ee-c65c-4c0f-abc7-52b1bbd1e01f

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
import Theorems.Thm_Arb4_ptCheckC_sound
import Theorems.Thm_H1000Line_chainOk_get
import Theorems.Thm_H1000Line_lastLe_sound
import Theorems.Thm_ZetaReflection_alternating_signs_chain
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
/-  H1000Line.lean -- the on-line sign certificate of the height-1000 ladder segment (lane
    h1000-prep, memo ANDURIL_ARB_DISCHARGE_2026-09-23, input H1 `hLine`, brick K4 in EM form).

    THE TWO THEOREMS, PROVED ONCE.  For the Boolean checker `ptCheck p` of `H1000Point` on a point
    record `p : LinePt` (height `t = tn / 2^tq`, EM cut `N`, the two evaluator states, remainder and
    phase hints, and a CLAIMED sign):

        ptCheck_sound : ptCheck p = true →
          (p.pos = true → 0 < gLine t) ∧ (p.pos = false → gLine t < 0),

    and the band assembly `band_sound`: a list of kernel-checked points with alternating signs inside
    `[T0, T1]` (`bandOk`) gives the VERBATIM `hLine` shape of `TuringBand.BandStatement` (`n` strictly
    increasing zeros of `completedRiemannZeta` on the critical line in `[T0, T1]`), through
    `SignChain.alternating_signs_chain`.

    HOW THE SIGN IS CERTIFIED (all kernel arithmetic on `Nat`/`Int`, no hypotheses):
      * `gLine t = M(t) * S(t)`, `S = cos φ · Re ζ(1/2+it) - sin φ · Im ζ(1/2+it)`,
        `M(t) ≥ (3/4) e^{-π|t|/2} > 0`             (`KernelGammaEnvelope.gLine_decomp_explicit`,
                                                      `gammaRMag_bounds`), so sign gLine = sign S;
      * Re ζ, Im ζ : the order-13 Euler-Maclaurin ball (`EMZetaHighEval.zeta_ballK`,
        `EMZetaHighCheck.corr_eq`, `remOdd_sound`), the Dirichlet sum by the ArbEconomics Nat
        evaluator (`ArbEcon.chunk_sound`, `EMZetaHighCheck.valid64`)       [H1000Point.zball_sound];
      * φ = Λ - (t/2) log π : the height-uniform bracket `RSTheta.theta_bracket` evaluated in integers
                                                                        [H1000Phase.phase_sound];
      * cos φ, sin φ : the evaluator's own `ArbEcon.trig` after a `2π m` shift [H1000Point.trig_phase];
      * the product ball `|S · 2^64 · W - sCtr| ≤ sRad` and the sign test   [H1000Point.s_ball].

    Because |ζ(1/2+it)| = |Z(t)| on the line, the φ uncertainty (half-width about 1/(4t)) enters
    only relatively: the certified interval is about Z(t)(1 ± √2/(4t)), plus the absolute EM error.

    The 25 band instances of `BandGlue_h1000.seg` are generated by
    `telperion/examples/zeta_reflection/emit_h1000_line.py` (modules `H1000Line_B00 … B24`,
    assembled in `H1000Line_All`).

    KERNEL FOOTGUN (see `ptCheck_spec`): never make the kernel decide a definitional equality between
    `cond`/`decide` forms on a symbolic point; extract conjuncts by rewriting with lemmas.

    Trust: axioms [propext, Classical.choice, Quot.sound] (see AxiomGuardH1000Line.lean); no
    `sorry`, no `native_decide`, every numeric fact is decided by the kernel (`decide +kernel`).

    conjecture1_proved = False.  Finite interval arithmetic and the intermediate value theorem at
    finitely many heights; nothing here bears on the Riemann Hypothesis.
-/


open Real Filter Topology
open ArbEcon ArbEcon.OrderK

namespace H1000Line

noncomputable section







/-! ## H. Bands: a list of kernel-checked points gives the `hLine` shape. -/



theorem tlt_sound {a b : LinePt} (h : tlt a b = true) : tOf a < tOf b := by
  have h' : decide (a.tn * 2 ^ b.tq < b.tn * 2 ^ a.tq) = true := h
  have hlt := of_decide_eq_true h'
  have hR : ((a.tn * 2 ^ b.tq : ℕ) : ℝ) < ((b.tn * 2 ^ a.tq : ℕ) : ℝ) := by exact_mod_cast hlt
  push_cast at hR
  unfold tOf
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  exact hR

















theorem firstGe_sound (T0n T0d : ℕ) (hd : 0 < T0d) : ∀ (ps : List LinePt) (h : 0 < ps.length),
    firstGe T0n T0d ps = true → (T0n : ℝ) / T0d ≤ tOf (ps[0]'h)
  | [], h, _ => by simp at h
  | a :: _, _, hf => by
    have hf' : decide (T0n * 2 ^ a.tq ≤ a.tn * T0d) = true := hf
    have hle := of_decide_eq_true hf'
    have hR : ((T0n * 2 ^ a.tq : ℕ) : ℝ) ≤ ((a.tn * T0d : ℕ) : ℝ) := by exact_mod_cast hle
    push_cast at hR
    show (T0n : ℝ) / T0d ≤ (a.tn : ℝ) / 2 ^ a.tq
    have hdR : (0 : ℝ) < T0d := by exact_mod_cast hd
    rw [div_le_div_iff₀ hdR (by positivity)]
    linarith







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


section
namespace Arb4
end Arb4
open Arb4











/-! ## Points with the states computed ONCE (no `dirOk` comparison) -/




















open H1000Line

theorem solution (T0 T1 : ℝ) (T0n T0d T1n T1d n : ℕ) (hT0 : T0 = (T0n : ℝ) / T0d)
    (hT1 : T1 = (T1n : ℝ) / T1d) (ds : List PtD) (h : bandC T0n T0d T1n T1d n ds = true) :
    ∃ xs : List ℝ, xs.length = n ∧ xs.IsChain (· < ·) ∧ (∀ t ∈ xs, T0 ≤ t ∧ t ≤ T1) ∧
      (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) := by
  have h' : (ds.all (fun d => ptCheckC d.pt) && bandOk T0n T0d T1n T1d n (ds.map PtD.pt)) = true := h
  rw [Bool.and_eq_true] at h'
  obtain ⟨hall, hb⟩ := h'
  set ps := ds.map PtD.pt with hps
  have hsgn : ∀ (i : ℕ) (hi : i < ps.length),
      ((ps[i]'hi).pos = true → 0 < XiLineZeros.gLine (tOf (ps[i]'hi))) ∧
        ((ps[i]'hi).pos = false → XiLineZeros.gLine (tOf (ps[i]'hi)) < 0) := by
    intro i hi
    have hi' : i < ds.length := by rw [hps, List.length_map] at hi; exact hi
    have hd := List.all_eq_true.mp hall (ds[i]'hi') (List.getElem_mem hi')
    have e : ps[i]'hi = (ds[i]'hi').pt := by simp [hps]
    rw [e]
    exact ptCheckC_sound (ds[i]'hi') hd
  have hb' : (((((decide (ps.length = n + 1) && chainOk ps) && decide (0 < T0d)) && decide (0 < T1d))
      && firstGe T0n T0d ps) && lastLe T1n T1d ps) = true := hb
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hb'
  obtain ⟨⟨⟨⟨⟨hlen, hch⟩, hd0⟩, hd1⟩, hfirst⟩, hlast⟩ := hb'
  have hlen' : decide (ps.length = n + 1) = true := hlen
  have hd0' : decide (0 < T0d) = true := hd0
  have hd1' : decide (0 < T1d) = true := hd1
  have hL := of_decide_eq_true hlen'
  have hD0 := of_decide_eq_true hd0'
  have hD1 := of_decide_eq_true hd1'
  let pt : Fin (n + 1) → ℝ := fun i => tOf (ps[i.1]'(by rw [hL]; exact i.2))
  apply ZetaReflection.alternating_signs_chain T0 T1 n pt
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    have h := chainOk_get ps hch i.1 (by rw [hL]; omega)
    exact tlt_sound h.1
  · rw [hT0]
    exact firstGe_sound T0n T0d hD0 ps (by rw [hL]; omega) hfirst
  · rw [hT1]
    exact lastLe_sound T1n T1d hD1 ps hlast n hL.symm
  · intro i
    have hc := chainOk_get ps hch i.1 (by rw [hL]; omega)
    have hA := hsgn i.1 (by rw [hL]; omega)
    have hB := hsgn (i.1 + 1) (by rw [hL]; omega)
    show XiLineZeros.gLine (tOf (ps[i.1]'(by rw [hL]; omega)))
        * XiLineZeros.gLine (tOf (ps[i.1 + 1]'(by rw [hL]; omega))) < 0
    rcases Bool.eq_false_or_eq_true (ps[i.1]'(by rw [hL]; omega)).pos with ha | ha
    · have hb2 : (ps[i.1 + 1]'(by rw [hL]; omega)).pos = false := by
        have := hc.2; rw [ha] at this; cases h2 : (ps[i.1 + 1]'(by rw [hL]; omega)).pos
        · rfl
        · rw [h2] at this; exact absurd rfl this
      exact mul_neg_of_pos_of_neg (hA.1 ha) (hB.2 hb2)
    · have hb2 : (ps[i.1 + 1]'(by rw [hL]; omega)).pos = true := by
        have := hc.2; rw [ha] at this; cases h2 : (ps[i.1 + 1]'(by rw [hL]; omega)).pos
        · rw [h2] at this; exact absurd rfl this
        · rfl
      exact mul_neg_of_neg_of_pos (hA.2 ha) (hB.1 hb2)
