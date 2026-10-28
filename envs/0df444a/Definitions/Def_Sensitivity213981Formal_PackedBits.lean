-- Prove2me | Definitions.Def_Sensitivity213981Formal_PackedBits
-- name    : Sensitivity213981Formal_PackedBits
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:06:24.127196+00:00
-- url     : https://prove2.me/theorems/efc1a679-646d-49d8-a655-54f323d4b704
-- title:
--   Packed Bits — sensitivity certificate definitions
-- statement:
--   The definitions for Packed Bits in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundPackedBits.mask_mod`, `ThreeBoundPackedBits.mask_div`, `ThreeBoundPackedBits.masked_split`, `ThreeBoundPackedBits.bitSum_eq_mod`, `ThreeBoundPackedBits.mask`, `ThreeBoundPackedBits.bitSum`, `ThreeBoundPackedBits.bitSum_le`, `ThreeBoundPackedBits.bitSum_succ`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; PackedBits.lean, lines 1–70.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Init.Data.Nat.Bitwise.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section
/- Sparse binary encoding: a 0/1 digit in each 16-bit lane can be counted
   by a single remainder modulo 65535. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ThreeBoundPackedBits
open scoped BigOperators

def mask : ℕ→ℕ
  | 0=>0
  | n+1=>1+65536*mask n

def bitSum(n x:ℕ):ℕ:=∑i∈Finset.range n,(x.testBit (16*i)).toNat

theorem bitSum_le(n x:ℕ):bitSum n x≤ n := by
  have h:bitSum n x≤ ∑_i∈Finset.range n,1 := by
    apply Finset.sum_le_sum
    intro i _
    cases x.testBit (16*i) <;> decide
  simpa using h

theorem bitSum_succ(n x:ℕ):bitSum (n+1) x=x%2+bitSum n (x/65536) := by
  unfold bitSum
  rw [Finset.sum_range_succ']
  simp only [Nat.mul_zero,Nat.toNat_testBit,Nat.pow_zero,Nat.div_one]
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.div_div_eq_div_mul]
  congr 2
  rw [show 65536=2^16 by decide,←pow_add]
  congr 1
  omega

theorem mask_mod(n:ℕ):mask (n+1)%65536=1 := by simp [mask,Nat.add_mod]
theorem mask_div(n:ℕ):mask (n+1)/65536=mask n := by simp [mask,Nat.add_div]

theorem masked_split(n x:ℕ)(h:x&&&mask (n+1)=x):
    x%65536≤ 1 ∧ (x/65536)&&&mask n=x/65536 := by
  have hlo:=congrArg (fun z:ℕ=>z%65536) h
  have hhi:=congrArg (fun z:ℕ=>z/65536) h
  have hb:65536=2^16:=by decide
  rw [hb,Nat.and_mod_two_pow,←hb,mask_mod] at hlo
  rw [hb,Nat.and_div_two_pow,←hb,mask_div] at hhi
  exact ⟨hlo.symm ▸ Nat.and_le_right,hhi⟩

theorem bitSum_eq_mod(n x:ℕ)(hn:n< 65535)(h:x&&&mask n=x):bitSum n x=x%65535 := by
  induction n generalizing x with
  | zero =>
    have hx:x=0:=by simpa only [mask,Nat.and_zero] using h.symm
    simp [bitSum,hx]
  | succ n ih =>
    obtain ⟨hlo,hhi⟩:=masked_split n x h
    have hb:=bitSum_le n (x/65536)
    have hi:=ih (x/65536) (by omega) hhi
    rw [bitSum_succ,hi]
    have hlo2:x%2=x%65536 := by
      have hh:=Nat.mod_mod_of_dvd x (by decide:2∣65536)
      rw [Nat.mod_eq_of_lt (by omega: x%65536< 2)] at hh
      exact hh.symm
    rw [hlo2]
    omega

end ThreeBoundPackedBits


end
end Sensitivity213981Formal


