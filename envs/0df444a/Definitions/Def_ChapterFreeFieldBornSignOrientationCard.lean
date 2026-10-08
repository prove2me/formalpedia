-- Prove2me | Definitions.Def_ChapterFreeFieldBornSignOrientationCard
-- name    : ChapterFreeFieldBornSignOrientationCard
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T09:20:15.635067+00:00
-- url     : https://prove2.me/theorems/e5ee2f81-c605-43c0-9a06-2ca63107a08c
-- title:
--   Chapter FreeFieldBornSignOrientationCard
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFreeFieldBornSignOrientationCard.lean`): generated def bundle for ChapterFreeFieldBornSignOrientationCard. See BookProof/ChapterFreeFieldBornSignOrientationCard.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFreeFieldBornSignOrientationCard.lean

import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Mathlib

/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# cardinality of the orientation-preserving sign gauge

The preceding files identify the diagonal Born sign gauge with boolean sign
choices and show that a sign matrix preserves orientation exactly when its
Hamming weight is even. This file counts that subgroup. In positive dimension,
exactly half of the `2^(n+1)` diagonal sign choices preserve orientation, so the
orientation-preserving subgroup has `2^n` elements.

## Main results

* `natCard_even_flip` — there are exactly `2^n` even flip choices on `n+1`
  coordinates.
* `natCard_orientationPreserving_flip` — equivalently, exactly `2^n` choices
  have sign matrix in `SO(n+1)`.
-/
namespace BookProof.ChapterFreeFieldBornSignOrientationCard

end BookProof.ChapterFreeFieldBornSignOrientationCard


