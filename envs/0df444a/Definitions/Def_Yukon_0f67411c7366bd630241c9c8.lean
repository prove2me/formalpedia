-- Prove2me | Definitions.Def_Yukon_0f67411c7366bd630241c9c8
-- name    : Yukon_0f67411c7366bd630241c9c8
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T15:26:59.28198+00:00
-- url     : https://prove2.me/theorems/38202caa-452c-43f0-be68-bf349600927c
-- title:
--   Pratt primality certificates
-- statement:
--   Pratt certificate structures, their soundness proofs, and the elementary prime certificates used by the Better Codes field construction. Mathematical declarations are preserved from the pinned CompPoly source; unused tactic implementation code is omitted.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/PrattCertificate.lean
--
--   yukon-proof-operation:0f67411c7366bd630241c9c8b460dce2f6077b05eeb7fcd94c1833c9f25dae55
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MGY2NzQxMWM3MzY2YmQ2MzAyNDFjOWM4YjQ2MGRjZTJmNjA3N2IwNWVlYjdmY2Q5NGMxODMzYzlmMjVkYWU1NSIsImhhc2giOiI2N2E3MjQwZjdlZmEzMjIzNjlmNDQ4N2Q3MWU0MzQ5OTI0NTliZjEzMWM5MjI0MzNjNzAzOWNiOGIxOTBhZTBmIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8wZjY3NDExYzczNjZiZDYzMDI0MWM5YzgiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality

public import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# The Lucas test for primes.

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO

- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness.
  Use `Units.IsCyclic` from `RingTheory/IntegralDomain` to show the group is cyclic.
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate Pratt primality certificates into the norm_num primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`: In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/

@[expose] public section

section New

-- TODO: port to `Mathlib`?

end New

/-- The binary version of `PrattPartList`. This is the one in the original file. -/
inductive PrattPart : (p : ℕ) → (a : ZMod p) → ℕ → Prop
  | prime : {p : ℕ} → {a : ZMod p} → (n k nk : ℕ) → n.Prime →
      a ^ ((p - 1) / n) ≠ 1 → n ^ k = nk → PrattPart p a nk
  | split : {p : ℕ} → {a : ZMod p} → {n : ℕ} → (l r : ℕ) →
      PrattPart p a l → PrattPart p a r → l * r = n → PrattPart p a n

structure PrattCertificate (p : ℕ) : Type where
  a : ZMod p
  pow_eq_one : a ^ (p - 1) = 1
  part : PrattPart p a (p - 1)

theorem PrattPart.out {p : ℕ} {a : ZMod p} {n : ℕ} (h : PrattPart p a n) :
    ∀ q : ℕ, q.Prime → q ∣ n → a ^ ((p - 1) / q) ≠ 1 := by
  induction h with
  | prime n k nk hprime hpow hnk =>
    subst hnk
    intro q hq hdiv
    cases (Nat.prime_dvd_prime_iff_eq hq hprime).mp (hq.dvd_of_dvd_pow hdiv)
    exact hpow
  | split n l r _ hlr ih₁ ih₂ =>
    subst hlr
    intro q hq hdiv
    rcases hq.dvd_mul.mp hdiv with (hdiv|hdiv)
    · exact ih₁ _ hq hdiv
    · exact ih₂ _ hq hdiv

theorem PrattCertificate.out {p : ℕ} (c : PrattCertificate p) : p.Prime :=
  lucas_primality p c.a c.pow_eq_one c.part.out

-- cannot do ^1 correctly it seems?

theorem prime_2 : Nat.Prime 2 := Nat.prime_two
theorem prime_3 : Nat.Prime 3 := Nat.prime_three

theorem prime_7 : Nat.Prime 7 := by
  refine PrattCertificate.out ⟨3, by reduce_mod_char, ?_⟩
  refine .split 2 3 ?_ ?_ (by norm_num)
  · exact .prime 2 1 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ prime_3 (by reduce_mod_char; decide) (by norm_num)

-- theorem prime_987654319 : Nat.Prime 987654319 := sorry

namespace Tactic

open Lean Meta Simp
open Lean.Elab
open Tactic
open Qq
open Mathlib.Meta.NormNum

theorem ZMod.bla : ∀ {n c : ℕ} (a : ZMod n), c = 1 → IsNat (a ^ (n - 1)) c → a ^ (n - 1) = 1
  | n, _, a, rfl, h => by
    conv_rhs => rw [← Nat.cast_one]
    exact h.out

  -- return q(sorry)
  -- have npred : Q(ℕ) := mkRawNatLit (n.natLit! - 1)
  -- haveI : $n =Q Nat.succ $npred := ⟨⟩
  -- -- haveI : $npred =Q $n - 1 := ⟨⟩
  -- let ⟨c, pc⟩ := evalNatPowMod a' npred n
  -- let pc' : Q(Nat.mod (Nat.pow «$a'» «$npred») «$n» = «$c») := q(sorry)
  -- -- have hc : Q(decide ($c = 1) = true) := (q(Eq.refl true) : Expr)
  -- haveI : $c =Q 1 := ⟨⟩
  -- -- return q(sorry)
  -- return q(ZMod.powEqOfPowMod $a $ha $pc' (.refl _))

theorem ZMod.blub :
    ∀ {n q c : ℕ} (a : ZMod n), (decide (n ≥ 2) = true) → (decide (c < n) = true) →
      (decide (c ≠ 1) = true) → IsNat (a ^ ((n - 1) / q)) c → a ^ ((n - 1) / q) ≠ 1
  | n, q, c, a, hn, hc₁, hc₂, ⟨h⟩ => by
    rw [h]
    intro h'
    apply of_decide_eq_true hc₂
    rw [← Nat.cast_one, CharP.natCast_eq_natCast (ZMod n) n] at h'
    rw [← Nat.mod_eq_of_lt (of_decide_eq_true hc₁),
      ← Nat.mod_eq_of_lt (show 1 < n from of_decide_eq_true hn)]
    exact h'

  -- return q(ZMod.powNeOfPowMod $a $ha $hn $pc $hc)

-- Invariant: n'.natLit! = n

theorem Nat.Prime_of_isNat : ∀ {n n' : ℕ}, IsNat n n' → n'.Prime → n.Prime
  | _, _, ⟨rfl⟩, hp => hp

end Tactic


