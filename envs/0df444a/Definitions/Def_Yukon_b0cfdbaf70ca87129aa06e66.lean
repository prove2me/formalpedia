-- Prove2me | Definitions.Def_Yukon_b0cfdbaf70ca87129aa06e66
-- name    : Yukon_b0cfdbaf70ca87129aa06e66
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T00:35:26.772402+00:00
-- url     : https://prove2.me/theorems/aeaa024a-6f63-4f56-9fb4-ab0b60d1a81d
-- title:
--   KoalaBear.fieldSize
-- statement:
--   The KoalaBear field modulus, `2^31 - 2^24 + 1`.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/KoalaBear/Basic.lean
--
--   yukon-proof-operation:bb5f9617-64be-4e61-badc-4662a0d72a25; Yukon contributor: historical-source-bootstrap
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YmI1Zjk2MTctNjRiZS00ZTYxLWJhZGMtNDY2MmEwZDcyYTI1OyBZdWtvbiBjb250cmlidXRvcjogaGlzdG9yaWNhbC1zb3VyY2UtYm9vdHN0cmFwIiwiaGFzaCI6IjM2MWIwMzQyNmNhY2FlNjIzYzdhNGE0NmE2ZWFiMzJiNzhmZmI1MjcxM2NmMmMwNWY1M2ZkODlkYWYzMjUyYzYiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uX2IwY2ZkYmFmNzBjYTg3MTI5YWEwNmU2NiIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImJldHRlci1jb2Rlcy1oaXN0b3J5In0]

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Valerii Huhnin
-/
module



public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.Basic


public import Mathlib
@[expose] public section
/-!
  # KoalaBear Field `2^{31} - 2^{24} + 1`

  This is the field used for lean Ethereum spec.
-/

@[expose] public section

namespace KoalaBear
/-- The KoalaBear field modulus, `2^31 - 2^24 + 1`. -/
@[reducible]
def fieldSize : Nat := 2 ^ 31 - 2 ^ 24 + 1
end KoalaBear
end
end


