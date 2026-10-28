-- Prove2me | solution 1 for Arb4.Q.val_div
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:32:17.072658+00:00
-- url     : https://prove2.me/submissions/de98489b-7753-4537-92af-fcdbf1a5cc8c

import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Mathlib
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

























/-! ## The comparisons -/











/-! ## Literal conversions (small proof terms for the generated certificates) -/











end Q

end Arb4


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


section
namespace Arb4
end Arb4
open Arb4



section
namespace Arb4.Q
end Arb4.Q
open Arb4.Q





























/-! ## The value homomorphism -/

























theorem solution (a : Q) {b : Q} (hb : 0 < b.n) : (div a b).val = a.val / b.val := by
  have hb1 : 1 ≤ b.n.toNat := by omega
  have hb' : ((b.n.toNat : ℕ) : ℝ) = (b.n : ℝ) := by
    have : ((b.n.toNat : ℕ) : ℤ) = b.n := Int.toNat_of_nonneg hb.le
    exact_mod_cast this
  have hbpos : (0 : ℝ) < (b.n : ℝ) := by exact_mod_cast hb
  have hge : 1 ≤ (a.dm + 1) * b.n.toNat := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e : ((((a.dm + 1) * b.n.toNat - 1 : ℕ)) : ℝ) + 1 = ((a.dm : ℝ) + 1) * (b.n : ℝ) := by
    rw [Nat.cast_sub hge]
    push_cast
    rw [hb']
    ring
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, div]
  rw [e]
  push_cast
  field_simp
