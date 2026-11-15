-- Prove2me | solution 1 for APFPaper5.K3.repeat_runs_the_hold_backwards
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:19:45.181411+00:00
-- url     : https://prove2.me/submissions/656b87f5-f5a7-4234-97aa-01b195350af3

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_repeat_runs_backwards
title: On a state a hold brings back after N steps, repeating the hold N - 1 times, n times over, reaches the state from which n steps lead back
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Thm_APFPaper5_K3_held_states_and_undo (undo_is_a_repeat). Thm_APFB07_realized_history_retraces, whose
 hypothesis is that the mirror of an admissible history is admissible.
consumes_inputs: none.
statement: (repeat_runs_the_hold_backwards) if N steps of D bring x back, then n steps of D from the state
 reached by n rounds of N - 1 steps lead to x.
reading: on a state the hold brings back, the history read backwards is the history of the hold repeated
 N - 1 times. So where a repeat of an admitted hold is an admitted hold, the mirror history is the history
 of an admitted hold.
not_claimed: that the admissible histories at an interface are the histories of admitted holds; that binding
 is still supplied.
-/
import Theorems.Thm_APFPaper5_K3_undo_is_a_repeat
import Theorems.Thm_APFPaper5_K3_kept_along_the_hold
import Theorems.Thm_APFPaper5_K3_every_state_comes_to_return
import Theorems.Thm_APFPaper5_K3_occupant_settles
import Theorems.Thm_APFPaper5_K3_finite_of_separating_family
import Theorems.Thm_APFB01_every_object_comes_to_return

set_option autoImplicit false
namespace APFPaper5.K3

theorem repeat_runs_the_hold_backwards {S : Type*} (D : S → S) (x : S) (N : ℕ) (hN : 0 < N)
    (h : D^[N] x = x) (n : ℕ) : D^[n] ((D^[N - 1])^[n] x) = x := by
  have e : n + (N - 1) * n = N * n := by
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, (Nat.sub_add_cancel hN).symm⟩
    rw [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  rw [← Function.iterate_mul, ← Function.iterate_add_apply, e, Function.iterate_mul]
  exact Function.iterate_fixed h n

end APFPaper5.K3


universe apfNative_u_1
theorem solution :
∀ {S : Type apfNative_u_1} (D : S → S) (x : S) (N : Nat)
  (hN : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
  (h : @Eq.{apfNative_u_1 + 1} S (@Nat.iterate.{apfNative_u_1 + 1} S D N x) x) (n : Nat),
  @Eq.{apfNative_u_1 + 1} S
    (@Nat.iterate.{apfNative_u_1 + 1} S D n
      (@Nat.iterate.{apfNative_u_1 + 1} S
        (@Nat.iterate.{apfNative_u_1 + 1} S D
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        n x))
    x := by
  exact @APFPaper5.K3.repeat_runs_the_hold_backwards
