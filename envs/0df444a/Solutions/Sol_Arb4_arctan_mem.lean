-- Prove2me | solution 1 for Arb4.arctan_mem
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:17.623803+00:00
-- url     : https://prove2.me/submissions/88b0ea47-4c24-431f-9aef-4fc066107c24

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Gamma
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
import Theorems.Thm_Arb4_Q_val_div
import Theorems.Thm_ArctanTaylor_arctan_eq_ps_add_rem
import Theorems.Thm_ArctanTaylor_rem_abs_le
namespace Arb4.Q
end Arb4.Q
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
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

theorem den_ne (a : Q) : (a.dm : ℝ) + 1 ≠ 0 := ne_of_gt (den_pos a)

theorem val_frac (n : ℤ) {d : ℕ} (hd : 1 ≤ d) : (frac n d).val = (n : ℝ) / (d : ℝ) := by
  simp only [val, frac]
  rw [Nat.cast_sub hd]
  push_cast
  ring_nf

@[simp] theorem val_ofNat (m : ℕ) : (ofNat m).val = (m : ℝ) := by
  simp [val, ofNat]

@[simp] theorem val_ofInt (m : ℤ) : (ofInt m).val = (m : ℝ) := by
  simp [val, ofInt]

theorem cast_den_mul (a b : Q) :
    (((a.dm * b.dm + a.dm + b.dm : ℕ) : ℝ) + 1) = ((a.dm : ℝ) + 1) * ((b.dm : ℝ) + 1) := by
  push_cast; ring

theorem val_add (a b : Q) : (add a b).val = a.val + b.val := by
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, add]
  rw [cast_den_mul]
  push_cast
  field_simp

theorem val_sub (a b : Q) : (sub a b).val = a.val - b.val := by
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, sub]
  rw [cast_den_mul]
  push_cast
  field_simp

theorem val_mul (a b : Q) : (mul a b).val = a.val * b.val := by
  simp only [val, mul]
  rw [cast_den_mul]
  push_cast
  rw [mul_div_mul_comm]





theorem val_npow (a : Q) : ∀ k, (npow a k).val = a.val ^ k
  | 0 => by simp [npow, val]
  | k + 1 => by rw [npow, val_mul, val_npow a k, pow_succ]



theorem val_sumQ (f : ℕ → Q) : ∀ k, (sumQ f k).val = ∑ i ∈ Finset.range k, (f i).val
  | 0 => by simp [sumQ, val]
  | k + 1 => by rw [sumQ, val_add, val_sumQ f k, Finset.sum_range_succ]

/-! ## The comparisons -/

theorem le_sound {a b : Q} (h : le a b = true) : a.val ≤ b.val := by
  have hz : a.n * ((b.dm : ℤ) + 1) ≤ b.n * ((a.dm : ℤ) + 1) := of_decide_eq_true h
  have hr : (a.n : ℝ) * ((b.dm : ℝ) + 1) ≤ (b.n : ℝ) * ((a.dm : ℝ) + 1) := by exact_mod_cast hz
  simp only [val]
  rw [div_le_div_iff₀ (den_pos a) (den_pos b)]
  exact hr

theorem lt_sound {a b : Q} (h : lt a b = true) : a.val < b.val := by
  have hz : a.n * ((b.dm : ℤ) + 1) < b.n * ((a.dm : ℤ) + 1) := of_decide_eq_true h
  have hr : (a.n : ℝ) * ((b.dm : ℝ) + 1) < (b.n : ℝ) * ((a.dm : ℝ) + 1) := by exact_mod_cast hz
  simp only [val]
  rw [div_lt_div_iff₀ (den_pos a) (den_pos b)]
  exact hr







/-! ## Literal conversions (small proof terms for the generated certificates) -/











end Q

end Arb4


/-  ArctanTaylor.lean -- ANDÚRIL A4 θ-value instrument: the reusable arctan Taylor bracket.

    The θ-value route (`ThetaValue.lean`) needs, for the Euler/Weierstrass series
    `Im log Γ(x+iy) = y·log n − Σ_k arctan(y/(x+k))` (limit form), a KERNEL box for each
    `arctan(y/(x+k))`.  This file is the reusable arctan instrument that produces those boxes,
    with NO numeric hypotheses and NO special-function anchors (no ψ, no Γ).

    ## The instrument.

    For `u ≥ 0` and any truncation order `N`,

        |arctan u − atanPS u N| ≤ u^(2N+1)/(2N+1),        atanPS u N = Σ_{j<N} (−1)^j u^(2j+1)/(2j+1).

    This is the alternating Taylor bracket, proved RIGOROUSLY from the integral representation
    `arctan u = ∫₀ᵘ (1+t²)⁻¹` (Mathlib `integral_inv_one_add_sq`) via the finite geometric
    identity `(1+t²)⁻¹ = Σ_{j<N}(−t²)^j + (−t²)^N/(1+t²)` and the elementary remainder bound
    `|∫₀ᵘ (−t²)^N/(1+t²)| ≤ ∫₀ᵘ t^(2N) = u^(2N+1)/(2N+1)`.

    Two cheap corollaries used by the tail machinery (elementary, no integral):
      * `arctan_le_self`        : `arctan u ≤ u`               (0 ≤ u)
      * `self_sub_cube_le_arctan`: `u − u³/3 ≤ arctan u`       (0 ≤ u)

    All lemmas are GENERAL in `(u, N)` — the ThetaValue driver instantiates them per term.
    Guarded: `#print axioms arctan_bracket` = {propext, Classical.choice, Quot.sound}.

    conjecture1_proved = False.  A rigorous elementary arctan enclosure, a building block, NOT a
    proof of anything about ζ.
-/





open Real intervalIntegral MeasureTheory

namespace ArctanTaylor



/-! ### The integral representation split. -/





/-! ### The remainder bound. -/



/-! ### THE INSTRUMENT: the two-sided arctan Taylor bracket. -/

/-- **Arctan Taylor bracket.**  For `0 ≤ u` and any `N`, `arctan u` is within
    `u^(2N+1)/(2N+1)` of its `N`-term Taylor partial sum. -/
theorem arctan_bracket (u : ℝ) (hu : 0 ≤ u) (N : ℕ) :
    |arctan u - atanPS u N| ≤ u^(2*N+1)/(2*N+1) := by
  rw [arctan_eq_ps_add_rem u N,
    show atanPS u N + (∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2)) - atanPS u N
      = (∫ t in (0:ℝ)..u, (-(t^2))^N / (1+t^2)) from by ring]
  exact rem_abs_le u hu N

/-! ### Elementary corollaries (no integral) for the far-tail machinery. -/





end ArctanTaylor


/-  Arb4_Edge.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per horizontal edge.

    `ArgHoriz.hAH_of_octCert_boxes` (brick K6c) reduces `argChangeHoriz ζ T 2 (-1) ∈ [Lo, Hi]` to an
    octant certificate (breakpoints `2 = x 0 > … > x m = -1`, labels, no crossing on every piece),
    two endpoint point enclosures with their corner slopes, and two final inequalities with `π` and
    `arctan`.  The generated edge modules `H1000Edge_*` prove these by `norm_num` per piece and per
    edge.  Here the WHOLE edge is one Boolean `edgeOK`, run by ONE `decide +kernel`:

      * `EdgeD`         -- the certificate data of an edge: height `t = tn / 2^tq`, EM cut `N`, log
                           bound `L`, breakpoints `x`, pieces `pc` (`Arb4_Side.PieceD`), endpoint
                           boxes (`ArbEcon.Off.checkG` data), corner slopes, the final `[Lo, Hi]`;
      * `boxOK`, `boxOK_sound` -- an endpoint enclosure (evaluator run at the piece center, recomputed)
                           and its four corner conditions;
      * `atanLoQ atanHiQ piL piH`, `finalLo_sound`, `finalHi_sound` -- the two final inequalities
                           (`3.141592 < π < 3.141593`, `ArgHoriz.atanLo_le`, `ArgHoriz.le_atanHi`);
      * `edgeOK`, `edgeOK_sound` -- THE EDGE: `edgeOK E = true` gives
                           `argChangeHoriz riemannZeta (tn / 2^tq) 2 (-1) ∈ [Lo, Hi]`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  One edge of a finite
    zero count; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. Small Boolean helpers -/



theorem eqB_sound {a b : Q} (h : eqB a b = true) : a.val = b.val := by
  simp only [eqB, Bool.and_eq_true] at h
  exact le_antisymm (le_sound h.1) (le_sound h.2)





/-! ## B. The evaluator invariants of a piece center -/



/-! ## C. Endpoint enclosures and their corner slopes -/









/-! ## D. The two final inequalities -/



























/-! ## E. THE EDGE -/



namespace EdgeD





end EdgeD





end Arb4


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














theorem pi_mem : pilo.val ≤ π ∧ π ≤ pihi.val := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  rw [pilo, pihi, val_frac _ (by norm_num), val_frac _ (by norm_num)]
  push_cast
  norm_num at h1 h2 ⊢
  exact ⟨h1.le, h2.le⟩

/-! ## B. Logarithms -/






























/-! ## C. Arctangents -/





theorem odd_n_pos (j : ℕ) : 0 < (ofNat (2 * j + 1)).n := by
  show (0 : ℤ) < ((2 * j + 1 : ℕ) : ℤ); exact_mod_cast Nat.succ_pos _

theorem val_atanPSQ (u : Q) (N : ℕ) : (atanPSQ u N).val = ArctanTaylor.atanPS u.val N := by
  rw [atanPSQ, val_sumQ, ArctanTaylor.atanPS]
  apply Finset.sum_congr rfl
  intro j _
  rw [val_mul, val_ofInt, val_div _ (odd_n_pos j), val_npow, val_ofNat]
  push_cast; ring

theorem val_atanErrQ (u : Q) (N : ℕ) : (atanErrQ u N).val = u.val ^ (2 * N + 1) / (2 * N + 1) := by
  rw [atanErrQ, val_div _ (odd_n_pos N), val_npow, val_ofNat]
  push_cast; ring









theorem two_n_pos : 0 < (ofNat 2).n := by show (0 : ℤ) < ((2 : ℕ) : ℤ); norm_num
theorem four_n_pos : 0 < (ofNat 4).n := by show (0 : ℤ) < ((4 : ℕ) : ℤ); norm_num



/-! ## D. The closed-form Γℝ brackets at one height -/



namespace GamD













end GamD















/-! ## E. The K6b comparisons of a band -/















end Arb4


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

section
namespace Arb4
end Arb4
open Arb4

open Q

/-! ## A. Constants -/
















/-! ## B. Logarithms -/






























/-! ## C. Arctangents -/






















theorem solution (y : Q) (N mode : ℕ) (h : atanOK y mode = true) :
    (arctanLo y N mode).val ≤ Real.arctan y.val ∧ Real.arctan y.val ≤ (arctanHi y N mode).val := by
  obtain ⟨hpl, hph⟩ := pi_mem
  match mode, h with
  | 0, h =>
    simp only [atanOK, Bool.and_eq_true] at h
    have h0 := le_sound h.1
    rw [val_ofNat, Nat.cast_zero] at h0
    have hb := ArctanTaylor.arctan_bracket y.val h0 N
    rw [abs_le] at hb
    simp only [arctanLo, arctanHi]
    rw [val_sub, val_add, val_atanPSQ, val_atanErrQ]
    constructor <;> linarith [hb.1, hb.2]
  | 1, h =>
    simp only [atanOK] at h
    have hy := lt_sound h
    rw [val_ofNat, Nat.cast_zero] at hy
    have hyn : 0 < y.n := by
      by_contra hn
      push Not at hn
      have : y.val ≤ 0 := by
        have : (y.n : ℝ) ≤ 0 := by exact_mod_cast hn
        exact div_nonpos_of_nonpos_of_nonneg this (den_pos y).le
      linarith
    have hinv : (inv y).val = y.val⁻¹ := by
      rw [inv, val_div _ hyn, val_ofNat, Nat.cast_one, one_div]
    have hu : 0 ≤ (inv y).val := by rw [hinv]; exact inv_nonneg.mpr hy.le
    have hb := ArctanTaylor.arctan_bracket (inv y).val hu N
    rw [abs_le] at hb
    have hr := Real.arctan_inv_of_pos hy
    rw [← hinv] at hr
    simp only [arctanLo, arctanHi]
    rw [val_sub, val_div _ two_n_pos, val_add, val_atanPSQ, val_atanErrQ, val_sub,
      val_div _ two_n_pos, val_sub, val_atanPSQ, val_atanErrQ, val_ofNat]
    push_cast
    constructor <;> linarith [hb.1, hb.2]
  | m + 2, h =>
    simp only [atanOK] at h
    have hy := eqB_sound h
    rw [val_ofNat, Nat.cast_one] at hy
    simp only [arctanLo, arctanHi]
    rw [val_div _ four_n_pos, val_div _ four_n_pos, val_ofNat, hy, Real.arctan_one]
    push_cast
    constructor <;> linarith
