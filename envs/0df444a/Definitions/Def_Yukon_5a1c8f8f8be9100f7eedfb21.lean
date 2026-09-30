-- Prove2me | Definitions.Def_Yukon_5a1c8f8f8be9100f7eedfb21
-- name    : Yukon_5a1c8f8f8be9100f7eedfb21
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T00:43:15.645011+00:00
-- url     : https://prove2.me/theorems/42295cc4-ed10-4bdf-8d21-9b3ce50d908f
-- title:
--   PrattPart
-- statement:
--   The binary version of `PrattPartList`. This is the one in the original file.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/PrattCertificate.lean
--
--   yukon-proof-operation:0cd45437-1e6c-4026-bc03-b7f01ef1662a; Yukon contributor: historical-source-bootstrap
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MGNkNDU0MzctMWU2Yy00MDI2LWJjMDMtYjdmMDFlZjE2NjJhOyBZdWtvbiBjb250cmlidXRvcjogaGlzdG9yaWNhbC1zb3VyY2UtYm9vdHN0cmFwIiwiaGFzaCI6Ijg2OGUxMzNiMTA1ZjFkMWIwODdhZWVjMzFjNjY1MGRkZWFkYTE2ZjM1MTBmMjcyOGE5ODcxYzhmZDQ4ZWRkMjQiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzVhMWM4ZjhmOGJlOTEwMGY3ZWVkZmIyMSIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImJldHRlci1jb2Rlcy1oaXN0b3J5In0]

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality


@[expose] public section
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
end
end


