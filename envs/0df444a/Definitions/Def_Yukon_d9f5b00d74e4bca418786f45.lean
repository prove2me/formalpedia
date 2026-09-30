-- Prove2me | Definitions.Def_Yukon_d9f5b00d74e4bca418786f45
-- name    : Yukon_d9f5b00d74e4bca418786f45
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-29T22:50:42.724895+00:00
-- url     : https://prove2.me/theorems/c1729156-61ad-4daa-99df-67ef0d4cc85c
-- title:
--   ProximityPrize.SubmissionUpper.EnumerationProbe.toyMaximum
-- statement:
--   Source declaration ProximityPrize.SubmissionUpper.EnumerationProbe.toyMaximum.
--
--   Original contribution: jacklightChen, verified Better Codes submission 908984bd-7ffa-4003-8ee9-09ed8864e0ae. Source Lean 4.32.2, exact commit 4de021b74b21124943c35eeda5da5c891571ad3e. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/4de021b74b21124943c35eeda5da5c891571ad3e/ProximityPrize/SubmissionUpper/EnumerationProbe.lean
--
--   p2m-history-enumeration:f3b2a606374736fcb97f792c3bd46ef3732657122c824f04c58a73f9eb0cf2ce
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1lbnVtZXJhdGlvbjpmM2IyYTYwNjM3NDczNmZjYjk3Zjc5MmMzYmQ0NmVmMzczMjY1NzEyMmM4MjRmMDRjNThhNzNmOWViMGNmMmNlIiwiaGFzaCI6IjE3MjMwODY4MDg3YjkyZjJiMTRkMmIxMGJjMmE3ZWUyMTVkYjVmYWVhNzZjZjczM2U3YWY5NDJkNmNlZjFjZjAiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uX2Q5ZjViMDBkNzRlNGJjYTQxODc4NmY0NSIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImJldHRlci1jb2Rlcy1oaXN0b3J5In0]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/



import Mathlib
import Definitions.Def_Yukon_8bd9f79a442b61b84572dca3
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
def toyMaximum : ℕ :=
  toyHistogram.foldl (fun m row => row.foldl Nat.max m) 0
end EnumerationProbe
end SubmissionUpper
end ProximityPrize


