-- Prove2me | Definitions.Def_Yukon_cd03a0807f2db523ebc7e512
-- name    : Yukon_cd03a0807f2db523ebc7e512
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-29T22:21:05.807003+00:00
-- url     : https://prove2.me/theorems/cdc50db6-7bbc-4594-b139-6b960ab5c605
-- title:
--   ProximityPrize.SubmissionUpper.EnumerationProbe.toyRoot
-- statement:
--   Source declaration ProximityPrize.SubmissionUpper.EnumerationProbe.toyRoot.
--
--   Original contribution: jacklightChen, verified Better Codes submission 908984bd-7ffa-4003-8ee9-09ed8864e0ae. Source Lean 4.32.2, exact commit 4de021b74b21124943c35eeda5da5c891571ad3e. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/4de021b74b21124943c35eeda5da5c891571ad3e/ProximityPrize/SubmissionUpper/EnumerationProbe.lean
--
--   p2m-history-enumeration:e8ca2a7dd8196f33ddcd4c6b6d0bfb7fef964688d582b6d359ddae026ead4fbc
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1lbnVtZXJhdGlvbjplOGNhMmE3ZGQ4MTk2ZjMzZGRjZDRjNmI2ZDBiZmI3ZmVmOTY0Njg4ZDU4MmI2ZDM1OWRkYWUwMjZlYWQ0ZmJjIiwiaGFzaCI6ImE2MTBlNjNhOGJiZDRiOWVhYjBmZDM1NzcxZTU1YmM5YjA0ZmE4ZTk4MWYyMTYwYTQyY2ZjMmM2ZDk2NGMxZjUiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uX2NkMDNhMDgwN2YyZGI1MjNlYmM3ZTUxMiIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImJldHRlci1jb2Rlcy1oaXN0b3J5In0]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/



import Mathlib
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
def toyRoot (e : ℕ) : ℕ :=
  3 ^ (e + 1) % 17
end EnumerationProbe
end SubmissionUpper
end ProximityPrize


