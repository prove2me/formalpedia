-- Prove2me | solution 1 for Arb4.slabOK_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:34:59.922495+00:00
-- url     : https://prove2.me/submissions/c0e572c0-cb34-453f-a074-78eadf384109

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
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
import Theorems.Thm_Arb4_cellOK_sound
import Theorems.Thm_ArbEcon_Off_slabClear_of_right_half
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



theorem val_frac (n : ℤ) {d : ℕ} (hd : 1 ≤ d) : (frac n d).val = (n : ℝ) / (d : ℝ) := by
  simp only [val, frac]
  rw [Nat.cast_sub hd]
  push_cast
  ring_nf

@[simp] theorem val_ofNat (m : ℕ) : (ofNat m).val = (m : ℝ) := by
  simp [val, ofNat]





















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


/-  Arb4_Slab.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per zero-free
    edge-clearance slab `EdgeClearGlue.SlabClear a b` (brick K1's numerical input).

    The generated slab modules `H1000Slab_*` of lane h1000-integrate cover `[1/2, 1] × [a, b]` by
    cells (one off-line evaluator run and one `ArbEcon.Off.checkCell` each), assembled by
    `H1000Oct.cell_zeta_ne_zero_R`, and close the slab budget, the Pochhammer bound and about
    fifteen scalar conditions per cell by `norm_num`.  Here the WHOLE slab is one Boolean `slabOK`:

      * `slabBudgetQ`, `slabBudget_le` -- the slab error budget as a rational (with
                           `C_6 ≤ 84107 · 10^-15`, `H1000Oct.CK_six_le`);
      * `CellD`, `SlabD` -- the certificate data: the slab `[lo, hi]`, its shared budget, the
                           breakpoints `1/2 = xs 0 < … < xs m = 1` and one cell per column
                           `[xs j, xs (j+1)] × [lo, hi]` (center, radius, half-widths);
      * `cellOK`, `cellOK_sound` -- one cell (evaluator run recomputed, `checkCell`, geometry);
      * `slabOK`, `slabOK_sound` -- THE SLAB: `slabOK S = true` gives `SlabClear lo hi`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  A finite zero-free
    slab; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. The slab budget -/





/-! ## B. The certificate data -/





namespace CellD









end CellD

/-! ## C. One cell -/









/-! ## D. THE SLAB -/

/-- Any `x ∈ [f 0, f m]` (`m ≥ 1`) lies in some `[f j, f (j+1)]`, `j < m` (no monotonicity needed). -/
theorem exists_col (f : ℕ → ℝ) (x : ℝ) : ∀ m : ℕ, 1 ≤ m → f 0 ≤ x → x ≤ f m →
    ∃ j, j < m ∧ f j ≤ x ∧ x ≤ f (j + 1)
  | 0, hm, _, _ => absurd hm (by norm_num)
  | m + 1, _, h0, hm => by
    by_cases hx : x ≤ f m
    · rcases Nat.eq_zero_or_pos m with h | h
      · subst h; exact ⟨0, by norm_num, h0, hm⟩
      · obtain ⟨j, hj, h1, h2⟩ := exists_col f x m h h0 hx
        exact ⟨j, by omega, h1, h2⟩
    · push Not at hx
      exact ⟨m, by omega, hx.le, hm⟩





end Arb4


/-  Arb4_Slab.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per zero-free
    edge-clearance slab `EdgeClearGlue.SlabClear a b` (brick K1's numerical input).

    The generated slab modules `H1000Slab_*` of lane h1000-integrate cover `[1/2, 1] × [a, b]` by
    cells (one off-line evaluator run and one `ArbEcon.Off.checkCell` each), assembled by
    `H1000Oct.cell_zeta_ne_zero_R`, and close the slab budget, the Pochhammer bound and about
    fifteen scalar conditions per cell by `norm_num`.  Here the WHOLE slab is one Boolean `slabOK`:

      * `slabBudgetQ`, `slabBudget_le` -- the slab error budget as a rational (with
                           `C_6 ≤ 84107 · 10^-15`, `H1000Oct.CK_six_le`);
      * `CellD`, `SlabD` -- the certificate data: the slab `[lo, hi]`, its shared budget, the
                           breakpoints `1/2 = xs 0 < … < xs m = 1` and one cell per column
                           `[xs j, xs (j+1)] × [lo, hi]` (center, radius, half-widths);
      * `cellOK`, `cellOK_sound` -- one cell (evaluator run recomputed, `checkCell`, geometry);
      * `slabOK`, `slabOK_sound` -- THE SLAB: `slabOK S = true` gives `SlabClear lo hi`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  A finite zero-free
    slab; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace Arb4
end Arb4
open Arb4

open Q

/-! ## A. The slab budget -/





/-! ## B. The certificate data -/





section
namespace Arb4.CellD
end Arb4.CellD
open Arb4.CellD









end

/-! ## C. One cell -/









/-! ## D. THE SLAB -/






theorem solution (S : SlabD) (h : slabOK S = true) : EdgeClearGlue.SlabClear S.lo.val S.hi.val := by
  simp only [slabOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hS, hcells⟩ := h
  have hS' := hS
  simp only [slabHeadOK, Bool.and_eq_true, Nat.ble_eq] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, _⟩, hx0⟩, hxm⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hS'
  have hx0' : (S.xs 0).val = 1 / 2 := by rw [eqB_sound hx0, val_frac _ (by norm_num)]; norm_num
  have hxm' : (S.xs S.m).val = 1 := by rw [eqB_sound hxm, val_ofNat]; norm_num
  apply ArbEcon.Off.slabClear_of_right_half
  intro x y hx0'' hx1 hy0 hy1
  obtain ⟨j, hj, h1, h2⟩ := exists_col (fun j => (S.xs j).val) x S.m hm (by rw [hx0']; exact hx0'')
    (by rw [hxm']; exact hx1.le)
  exact cellOK_sound S hS j (hcells j hj) x y (Set.mem_uIcc.mpr (Or.inl ⟨h1, h2⟩)) hy0 hy1 hx0''
    hx1.le
