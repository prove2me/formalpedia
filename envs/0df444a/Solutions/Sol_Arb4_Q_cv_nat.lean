-- Prove2me | solution 1 for Arb4.Q.cv_nat
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:30:40.104897+00:00
-- url     : https://prove2.me/submissions/a141ce07-ce78-48d5-b767-1351d5702c3e

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







@[simp] theorem val_ofNat (m : ℕ) : (ofNat m).val = (m : ℝ) := by
  simp [val, ofNat]





















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





























/-! ## The comparisons -/











/-! ## Literal conversions (small proof terms for the generated certificates) -/

theorem solution (m : ℕ) [m.AtLeastTwo] : (ofNat (OfNat.ofNat m)).val = (OfNat.ofNat m : ℝ) := by
  rw [val_ofNat]; exact Nat.cast_ofNat
