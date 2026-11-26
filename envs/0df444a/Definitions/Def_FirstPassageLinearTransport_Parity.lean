-- Prove2me | Definitions.Def_FirstPassageLinearTransport_Parity
-- name    : FirstPassageLinearTransport_Parity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:58:56.673313+00:00
-- url     : https://prove2.me/theorems/83621626-568c-4679-a70f-7844a3c5234a
-- title:
--   Parity
-- statement:
--   Definitions and structural lemmas for Parity, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_of_even
import Theorems.Thm_FirstPassageLinearTransport_shortcut_of_odd
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators
theorem two_mul_shortcut_of_even {n : ℕ} (hn : n % 2 = 0) :
    2 * shortcut n = n := by
  rw [shortcut_of_even hn]
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hn)
theorem two_mul_shortcut_of_odd {n : ℕ} (hn : n % 2 = 1) :
    2 * shortcut n = 3 * n + 1 := by
  rw [shortcut_of_odd hn]
  apply Nat.mul_div_cancel'
  rw [Nat.dvd_iff_mod_eq_zero]
  omega
theorem orbit_shortcut (i n : ℕ) : orbit i (shortcut n) = orbit (i + 1) n := by
  simp [orbit, Function.iterate_succ_apply]
theorem modEq_of_same_parity_prefix :
    ∀ M n n' : ℕ,
      (∀ i : ℕ, i < M → orbit i n % 2 = orbit i n' % 2) →
        n ≡ n' [MOD 2 ^ M] := by
  intro M
  induction M with
  | zero =>
      intro n n' _h
      simpa using Nat.modEq_one
  | succ M ih =>
      intro n n' h
      have hzero : n % 2 = n' % 2 := by
        simpa using h 0 (by omega)
      have htail :
          ∀ i : ℕ, i < M →
            orbit i (shortcut n) % 2 = orbit i (shortcut n') % 2 := by
        intro i hi
        simpa [orbit_shortcut] using h (i + 1) (by omega)
      have hstep : shortcut n ≡ shortcut n' [MOD 2 ^ M] :=
        ih (shortcut n) (shortcut n') htail
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · have hn' : n' % 2 = 0 := by omega
        have hscaled := hstep.mul_left' 2
        rw [two_mul_shortcut_of_even hn, two_mul_shortcut_of_even hn'] at hscaled
        simpa [pow_succ, Nat.mul_comm] using hscaled
      · have hn' : n' % 2 = 1 := by omega
        have hscaled := hstep.mul_left' 2
        rw [two_mul_shortcut_of_odd hn, two_mul_shortcut_of_odd hn'] at hscaled
        have hthree : 3 * n ≡ 3 * n' [MOD 2 ^ (M + 1)] := by
          apply Nat.ModEq.add_right_cancel' 1
          simpa [pow_succ, Nat.mul_comm] using hscaled
        have hcoprime : Nat.Coprime (2 ^ (M + 1)) 3 := by
          exact (by norm_num : Nat.Coprime 2 3).pow_left (M + 1)
        exact hthree.cancel_left_of_coprime hcoprime
def parityCode (M : ℕ) (n : Fin (2 ^ M)) : Fin M → Fin 2 :=
  fun i => parityBit n i
theorem parityCode_injective (M : ℕ) : Function.Injective (parityCode M) := by
  intro n n' hcode
  apply Fin.ext
  have hprefix :
      ∀ i : ℕ, i < M → orbit i n % 2 = orbit i n' % 2 := by
    intro i hi
    have hbit := congrFun hcode ⟨i, hi⟩
    exact congrArg Fin.val hbit
  exact (modEq_of_same_parity_prefix M n n' hprefix).eq_of_lt_of_lt n.isLt n'.isLt
theorem parityCode_bijective (M : ℕ) : Function.Bijective (parityCode M) := by
  apply (Fintype.bijective_iff_injective_and_card (parityCode M)).2
  constructor
  · exact parityCode_injective M
  · simp
noncomputable def parityEquiv (M : ℕ) : Fin (2 ^ M) ≃ (Fin M → Fin 2) :=
  Equiv.ofBijective (parityCode M) (parityCode_bijective M)
def affineCorrection (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k,
    (parityBit n i : ℕ) * 2 ^ i *
      3 ^ (oddCount n k - oddCount n (i + 1))
def affineCorrectionQ (n k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k,
    ((parityBit n i : ℕ) : ℚ) *
      (3 : ℚ) ^ (oddCount n k - oddCount n (i + 1)) /
        (2 : ℚ) ^ (k - i)
end FirstPassageLinearTransport


