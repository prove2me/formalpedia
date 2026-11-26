-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
-- name    : CollatzEndpointTransport_Common_TerrasParityBijection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:06:22.832656+00:00
-- url     : https://prove2.me/theorems/63302e74-5e42-4681-963c-5e1f69a5b10e
-- title:
--   Terras Parity Bijection
-- statement:
--   Definitions and structural lemmas for Terras Parity Bijection, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean

import Mathlib
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace Terras
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
theorem two_mul_T_of_even {n : ℕ} (h : n % 2 = 0) : 2 * T n = n := by
  unfold T
  rw [if_pos h]
  omega
theorem two_mul_T_of_odd {n : ℕ} (h : n % 2 = 1) : 2 * T n = 3 * n + 1 := by
  unfold T
  rw [if_neg (by omega)]
  omega
def parityBit (n : ℕ) : Bool := decide (n % 2 = 1)
def parityVec (H n : ℕ) : Fin H → Bool := fun i => parityBit (T^[(i : ℕ)] n)
theorem modEq_of_parityVec_eq :
    ∀ (H n n' : ℕ), parityVec H n = parityVec H n' → n ≡ n' [MOD 2 ^ H] := by
  intro H
  induction H with
  | zero => intro n n' _; simp [Nat.ModEq, Nat.mod_one]
  | succ H ih =>
      intro n n' h
      have h0 : parityBit n = parityBit n' := by
        have hc := congrFun h ⟨0, Nat.succ_pos H⟩
        simpa [parityVec] using hc
      have hpar : n % 2 = n' % 2 := by
        simp only [parityBit, decide_eq_decide] at h0
        omega
      have htail : parityVec H (T n) = parityVec H (T n') := by
        funext i
        have hc := congrFun h ⟨(i : ℕ) + 1, by omega⟩
        simpa [parityVec, Function.iterate_succ_apply] using hc
      have hT : T n ≡ T n' [MOD 2 ^ H] := ih (T n) (T n') htail
      have hTT : 2 * T n ≡ 2 * T n' [MOD 2 * 2 ^ H] :=
        Nat.ModEq.mul_left' 2 hT
      have hpow : 2 * 2 ^ H = 2 ^ (H + 1) := by ring
      rw [hpow] at hTT
      rcases Nat.even_or_odd n with he | ho
      · have hn : n % 2 = 0 := Nat.even_iff.mp he
        have hn' : n' % 2 = 0 := by omega
        rwa [two_mul_T_of_even hn, two_mul_T_of_even hn'] at hTT
      · have hn : n % 2 = 1 := Nat.odd_iff.mp ho
        have hn' : n' % 2 = 1 := by omega
        rw [two_mul_T_of_odd hn, two_mul_T_of_odd hn'] at hTT
        have h3 : 3 * n ≡ 3 * n' [MOD 2 ^ (H + 1)] :=
          Nat.ModEq.add_right_cancel' 1 hTT
        have hcop : Nat.gcd (2 ^ (H + 1)) 3 = 1 :=
          Nat.Coprime.pow_left (H + 1) (by norm_num)
        exact Nat.ModEq.cancel_left_of_coprime hcop h3
def terrasMap (H : ℕ) : Fin (2 ^ H) → (Fin H → Bool) :=
  fun x => parityVec H (x : ℕ)
theorem terrasMap_injective (H : ℕ) : Function.Injective (terrasMap H) := by
  intro a b hab
  have h := modEq_of_parityVec_eq H (a : ℕ) (b : ℕ) hab
  have ha : (a : ℕ) < 2 ^ H := a.isLt
  have hb : (b : ℕ) < 2 ^ H := b.isLt
  have : (a : ℕ) = (b : ℕ) := by
    have := h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact Fin.ext this
theorem terrasMap_bijective (H : ℕ) : Function.Bijective (terrasMap H) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨terrasMap_injective H, ?_⟩
  simp
noncomputable def terrasEquiv (H : ℕ) : Fin (2 ^ H) ≃ (Fin H → Bool) :=
  Equiv.ofBijective (terrasMap H) (terrasMap_bijective H)
def oddCount (H n : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin H => parityVec H n i = true)).card
def wordWeight {H : ℕ} (v : Fin H → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin H => v i = true)).card
end Terras
end CollatzEndpointTransport


