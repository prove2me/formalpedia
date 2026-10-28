-- Prove2me | Definitions.Def_D1Bound5_SmallPairPureClosureData8DestinationsChunk11_Definitions
-- name    : D1Bound5_SmallPairPureClosureData8DestinationsChunk11_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:28:37.313836+00:00
-- url     : https://prove2.me/theorems/5ab8a885-58f0-4e62-b097-b0b22a4c3c2b
-- title:
--   Small Pair Pure Closure Data8Destinations Chunk11
-- statement:
--   Exact destination-index lists used to verify both signed mutations in the coordinate closure certificates. The named objects in this bundle include `PairLightClosurePrepared8.destinationsChunk11`.
-- source:
--   D1Bound5/SmallPairPureClosureData8DestinationsChunk11.lean, lines 8-38, SHA-256 87926f71765036489956ecf7a0eadb99ec727f336dc7818c0606a0e2fa02a08e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init

section
namespace D1Bound5.PairLightClosurePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def destinationsChunk11 : List (Option Nat × Option Nat) := [
  (some 28, some 26),
  (some 25, some 27),
  (some 26, some 24),
  (some 23, some 25),
  (some 24, some 22),
  (some 21, some 23),
  (some 22, some 20),
  (some 19, some 21),
  (some 20, some 18),
  (some 17, some 19),
  (some 18, some 16),
  (some 15, some 17),
  (some 16, some 14),
  (some 13, some 15),
  (some 14, some 12),
  (some 11, some 13),
  (some 12, some 10),
  (some 9, some 11),
  (some 10, some 8),
  (some 7, some 9),
  (some 8, some 6),
  (some 5, some 7),
  (some 6, some 4),
  (some 3, some 5),
  (some 4, some 2),
  (some 1, some 3),
  (some 2, some 0),
  (none, some 1),
  (some 0, none)
]

end D1Bound5.PairLightClosurePrepared8
end


