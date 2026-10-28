-- Prove2me | solution 1 for Arb4.k6side_of_B
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:05:01.261994+00:00
-- url     : https://prove2.me/submissions/8249d836-0ca2-4ee8-98f9-ed43b7316aeb

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Gamma
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Line
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Seg
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgChangeGlue
import Definitions.Def_ArdaRH65K_Turing121_ArgGammaR
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_ArgZetaTwo
import Definitions.Def_ArdaRH65K_Turing121_BandGlue
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
import Definitions.Def_ArdaRH65K_Turing121_H1000Line
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_H1000Phase
import Definitions.Def_ArdaRH65K_Turing121_H1000Point
import Definitions.Def_ArdaRH65K_Turing121_HeightFloorCheck
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
import Theorems.Thm_Arb4_k6B_sound
namespace Arb4.Q
end Arb4.Q
namespace BandGlue
end BandGlue
namespace BandGlue.BandData
end BandGlue.BandData
/-  Arb4_Q.lean -- lane Arb4 (h1000 compaction): exact rational arithmetic for Boolean kernel
    checkers.

    A certificate side condition such as the error budget of an octant piece is a polynomial
    inequality between explicit rationals.  Closing it by `norm_num` stores the whole normalisation
    trace in the olean (about 300 KB per budget at height 1000).  Here the same inequality is
    computed by `decide +kernel` over plain `Int`/`Nat` arithmetic (GMP-accelerated literals) and
    transported to `ℝ` by ONE soundness theorem per operation, proved once:

      * `Q`             -- an UNNORMALISED rational `n / (dm + 1)` (`n : ℤ`, `dm : ℕ`): the
                           denominator is positive by construction, so no positivity bookkeeping;
                           `val` is its real value, `frac n d` the rational `n / d` (`d ≥ 1`);
      * `add sub mul neg qabs npow div sumQ` -- the operations, `val_*` their homomorphism laws;
      * `le lt`         -- the Boolean comparisons, `le_sound`, `lt_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


namespace Arb4



namespace Q





























/-! ## The value homomorphism -/

theorem den_pos (a : Q) : (0 : ℝ) < (a.dm : ℝ) + 1 := by positivity



theorem val_frac (n : ℤ) {d : ℕ} (hd : 1 ≤ d) : (frac n d).val = (n : ℝ) / (d : ℝ) := by
  simp only [val, frac]
  rw [Nat.cast_sub hd]
  push_cast
  ring_nf























/-! ## The comparisons -/

theorem le_sound {a b : Q} (h : le a b = true) : a.val ≤ b.val := by
  have hz : a.n * ((b.dm : ℤ) + 1) ≤ b.n * ((a.dm : ℤ) + 1) := of_decide_eq_true h
  have hr : (a.n : ℝ) * ((b.dm : ℝ) + 1) ≤ (b.n : ℝ) * ((a.dm : ℝ) + 1) := by exact_mod_cast hz
  simp only [val]
  rw [div_le_div_iff₀ (den_pos a) (den_pos b)]
  exact hr









/-! ## Literal conversions (small proof terms for the generated certificates) -/











end Q

end Arb4


/-  Arb4_Seg.lean -- lane Arb4: the band-level glue of a COMPACT hypothesis-free ladder segment.

    For a Turing band `d : BandGlue.BandData` of a ladder segment (its edges, count and Blaschke ball
    from the zeta_zero_localization band plan), the certificate route of `BandGlue` needs: the
    decidable side conditions `Valid` for the band with OUR enclosures, the K1 cap geometry, the
    on-line zeros, two zero-free slabs, the K6 side conditions and the two horizontal edges.  Here:

      * `EnclQ`, `withEncl`  -- the five enclosures as rationals, and the band with them swapped in;
      * `validB`, `valid_of_B` -- `Valid` (ball cover of the RvM rectangle, the two pins) from ONE
                               Boolean over the band's rational table values;
      * `k6sideB`, `k6side_of_B` -- `ArgChangeGlue.K6Side` (K6a range, K6b brackets) from ONE Boolean;
      * `boxCert_of_parts`   -- the band's `BandGlue.BoxCert` from the parts (K0 + K1 + K6).

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/






open Complex

section
namespace Arb4
end Arb4
open Arb4

open Q BandGlue BandGlue.BandData















theorem solution (d : BandData) (G0 G1 : GamD) (E : EnclQ) (hT0 : d.T0 = G0.T.val)
    (hT1 : d.T1 = G1.T.val) (h : k6sideB G0 G1 E = true) : ArgChangeGlue.K6Side (withEncl d E) := by
  simp only [k6sideB, Bool.and_eq_true] at h
  obtain ⟨⟨hL1, hH1⟩, hk⟩ := h
  obtain ⟨a0, a1, l4, h4, l5, h5⟩ := k6B_sound G0 G1 E.L4 E.H4 E.L5 E.H5 hk
  have hL1' := le_sound hL1
  have hH1' := le_sound hH1
  rw [val_frac _ (by norm_num)] at hL1' hH1'
  have hT0' : (withEncl d E).T0 = G0.T.val := hT0
  have hT1' : (withEncl d E).T1 = G1.T.val := hT1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hT0']; exact a0
  · rw [hT1']; exact a1
  · show E.L1.val ≤ -(249 / 250); push_cast at hL1'; linarith
  · show 249 / 250 ≤ E.H1.val; push_cast at hH1'; linarith
  · rw [hT0', hT1']; exact l4
  · rw [hT0', hT1']; exact h4
  · rw [hT0', hT1']; exact l5
  · rw [hT0', hT1']; exact h5
