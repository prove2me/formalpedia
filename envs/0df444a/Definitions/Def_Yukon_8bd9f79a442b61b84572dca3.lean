-- Prove2me | Definitions.Def_Yukon_8bd9f79a442b61b84572dca3
-- name    : Yukon_8bd9f79a442b61b84572dca3
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-29T22:41:54.673975+00:00
-- url     : https://prove2.me/theorems/f4e04c1e-a956-46b9-9c80-d3011289b7c9
-- title:
--   ProximityPrize.SubmissionUpper.EnumerationProbe.toyHistogram
-- statement:
--   Source declaration ProximityPrize.SubmissionUpper.EnumerationProbe.toyHistogram.
--
--   Original contribution: jacklightChen, verified Better Codes submission 908984bd-7ffa-4003-8ee9-09ed8864e0ae. Source Lean 4.32.2, exact commit 4de021b74b21124943c35eeda5da5c891571ad3e. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/4de021b74b21124943c35eeda5da5c891571ad3e/ProximityPrize/SubmissionUpper/EnumerationProbe.lean
--
--   p2m-history-enumeration:6589977d11ad06c1c32dfbe87fd2ddf3ffd8859b9942d7f63e24396694c51ea8
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1lbnVtZXJhdGlvbjo2NTg5OTc3ZDExYWQwNmMxYzMyZGZiZTg3ZmQyZGRmM2ZmZDg4NTliOTk0MmQ3ZjYzZTI0Mzk2Njk0YzUxZWE4IiwiaGFzaCI6IjFhZTAxM2QyZTkxMmIwZGExM2E2NGE2YTQ2ZmExNjdjM2E0NGVhMTMyZjk2OTMzZjQ5YWMyNTJkOWQwODMyYmMiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzhiZDlmNzlhNDQyYjYxYjg0NTcyZGNhMyIsImVudmlyb25tZW50Ijp7InRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSIsIm1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0In0sInRhZyI6ImJldHRlci1jb2Rlcy1oaXN0b3J5In0]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/



import Mathlib
import Definitions.Def_Yukon_64335deb2f140f59dcb39265
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
def toyHistogram : List (List ℕ) :=
  (List.sublistsLen 8 (List.range 15)).foldl
    (fun h U =>
      let k := toyListKey U
      h.modify k.2 (fun row => row.modify k.1 Nat.succ))
    (List.replicate 16 (List.replicate 17 0))
end EnumerationProbe
end SubmissionUpper
end ProximityPrize


