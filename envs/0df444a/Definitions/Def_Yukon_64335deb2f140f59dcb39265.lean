-- Prove2me | Definitions.Def_Yukon_64335deb2f140f59dcb39265
-- name    : Yukon_64335deb2f140f59dcb39265
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-29T22:32:45.19812+00:00
-- url     : https://prove2.me/theorems/09c00fe2-7cdd-40be-b8cd-964e31e415b2
-- title:
--   ProximityPrize.SubmissionUpper.EnumerationProbe.toyListKey
-- statement:
--   Source declaration ProximityPrize.SubmissionUpper.EnumerationProbe.toyListKey.
--
--   Original contribution: jacklightChen, verified Better Codes submission 908984bd-7ffa-4003-8ee9-09ed8864e0ae. Source Lean 4.32.2, exact commit 4de021b74b21124943c35eeda5da5c891571ad3e. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/4de021b74b21124943c35eeda5da5c891571ad3e/ProximityPrize/SubmissionUpper/EnumerationProbe.lean
--
--   p2m-history-enumeration:9f15b94417234c20220adc4900ca014a75d2379de0c95e2595b48b0ff4591d2a
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1lbnVtZXJhdGlvbjo5ZjE1Yjk0NDE3MjM0YzIwMjIwYWRjNDkwMGNhMDE0YTc1ZDIzNzlkZTBjOTVlMjU5NWI0OGIwZmY0NTkxZDJhIiwiaGFzaCI6ImRmNzcyNTQ3YWI0NjA3NjQ1Yjg5ZDNjOTU4NDdmNTY2MDk4NGY0OGM2NWJkODAwMjEwY2Q2NmMxYThhODE3OGIiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzY0MzM1ZGViMmYxNDBmNTlkY2IzOTI2NSIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImJldHRlci1jb2Rlcy1oaXN0b3J5In0]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/



import Mathlib
import Definitions.Def_Yukon_cd03a0807f2db523ebc7e512
/-!
# A kernel-evaluated small analogue of the 1024-fold key map

This file deliberately leaves the scored construction unchanged.  It asks the
remote verifier to exhaust all eight-subsets of the fifteen nontrivial powers
of a primitive sixteenth root in `ZMod 17`, represented by natural residues.
The two key coordinates are the first Newton coefficient and the product
exponent modulo sixteen.  Candidates are traversed once while accumulating a
`16 × 17` histogram, so the expensive key calculation is not repeated for
every possible key.  A preceding remote smoke test established that this
histogram evaluates within the verifier budget, and a second run proved the
upper bounds 64, 44, 34, and 29, while a remote run proved that the bound 26 is
false.  This probe asks whether every fibre has size at most 28.
-/

namespace ProximityPrize.SubmissionUpper.EnumerationProbe
def toyListKey (U : List ℕ) : ℕ × ℕ :=
  U.foldl
    (fun k e => ((k.1 + toyRoot e) % 17, (k.2 + e + 1) % 16))
    (0, 0)
end EnumerationProbe
end SubmissionUpper
end ProximityPrize


