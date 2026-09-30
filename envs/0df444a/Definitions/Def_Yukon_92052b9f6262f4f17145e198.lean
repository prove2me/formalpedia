-- Prove2me | Definitions.Def_Yukon_92052b9f6262f4f17145e198
-- name    : Yukon_92052b9f6262f4f17145e198
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T00:52:49.538742+00:00
-- url     : https://prove2.me/theorems/969283c3-c817-4a19-a436-d6692dcc5460
-- title:
--   PrattCertificate
-- statement:
--   Source declaration PrattCertificate.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/PrattCertificate.lean
--
--   yukon-proof-operation:ac37d78f-79da-4eeb-a98c-e902351d1683; Yukon contributor: historical-source-bootstrap
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YWMzN2Q3OGYtNzlkYS00ZWViLWE5OGMtZTkwMjM1MWQxNjgzOyBZdWtvbiBjb250cmlidXRvcjogaGlzdG9yaWNhbC1zb3VyY2UtYm9vdHN0cmFwIiwiaGFzaCI6ImE5ZjdmY2ViMmE3MGIyZTZhYzRmMmUwZWY2ODdlY2NiZjE3ZTRhY2Q3YmE1MGYyODAyNjBiZmM1ZTc1OGJlMjQiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzkyMDUyYjlmNjI2MmY0ZjE3MTQ1ZTE5OCIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImJldHRlci1jb2Rlcy1oaXN0b3J5In0]

/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.LucasPrimality


public import Definitions.Def_Yukon_5a1c8f8f8be9100f7eedfb21
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
structure PrattCertificate (p : ℕ) : Type where
  a : ZMod p
  pow_eq_one : a ^ (p - 1) = 1
  part : PrattPart p a (p - 1)
end
end


