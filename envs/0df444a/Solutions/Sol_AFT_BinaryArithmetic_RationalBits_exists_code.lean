-- Prove2me | solution 1 for AFT.BinaryArithmetic.RationalBits.exists_code
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T04:20:42.215839+00:00
-- url     : https://prove2.me/submissions/d7d6d19a-28ab-48f3-a7a4-37a110250a3b

import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalLiterals
import Mathlib


/-! Finite stored literals and explicit copying. `exists_code` is a semantic
encoding theorem; it is not a runtime rational-to-bits oracle. Programs store
its finite Boolean literals before execution. -/
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
section AFT
section BinaryArithmetic
open AFT
open AFT.BinaryArithmetic







theorem _root_.AFT.BinaryArithmetic.bits_value (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec with
  | zero => simp [value]
  | bit b n ih =>
    by_cases hn : n=0
    · subst n
      cases b <;> simp [Nat.bit_val,value]
    · rw [Nat.bits_append_bit n b (fun hh => False.elim (hn hh))]
      simp only [value,ih,Nat.bit_val]
      omega

namespace AFT.BinaryArithmetic.RationalBits
end AFT.BinaryArithmetic.RationalBits
section RationalBits
open AFT
open AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits







/-- Existence of a finite literal encoding, used when constructing a fixed
program. The result is stored data, not an invocation of a real oracle. -/
theorem solution (q : ℚ) : ∃ code : RationalBits,code.decode=q := by
  let negative := decide (q.num < 0)
  have hsign : signedValue negative q.num.natAbs.bits=q.num := by
    simp only [signedValue,bits_value,negative]
    by_cases hn : q.num < 0
    · simp [hn,abs_of_neg hn]
    · simp [hn,abs_of_nonneg (by omega : 0 ≤ q.num)]
  let code : RationalBits :=
    ⟨negative,q.num.natAbs.bits,q.den.bits,
      by rw [bits_value,Nat.size_eq_bits_len],
      by rw [bits_value,Nat.size_eq_bits_len],
      by simpa only [bits_value] using q.den_pos,
      by simpa only [bits_value] using q.reduced⟩
  refine ⟨code,?_⟩
  rw [decode_fraction]
  change (signedValue negative q.num.natAbs.bits : ℚ)/(value q.den.bits : ℚ)=q
  rw [hsign,bits_value,Rat.num_div_den]

end RationalBits
end BinaryArithmetic
end AFT
