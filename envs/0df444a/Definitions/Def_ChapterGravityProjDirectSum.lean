-- Prove2me | Definitions.Def_ChapterGravityProjDirectSum
-- name    : ChapterGravityProjDirectSum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T14:36:27.550985+00:00
-- url     : https://prove2.me/theorems/181f1298-2685-43a6-b7fc-79f613de85bb
-- title:
--   Chapter GravityProjDirectSum
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGravityProjDirectSum.lean`): generated def bundle for ChapterGravityProjDirectSum. See BookProof/ChapterGravityProjDirectSum.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGravityProjDirectSum.lean

import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
import Mathlib

/-!
# The spatial and temporal projectors split Minkowski space

`BookProof.ChapterGravityTimeProj` proves the algebraic identities satisfied by
the spatial projector `χ` and the temporal projector `Π` attached to a unit
timelike vector `v`:

* `spatialProj_add_timeProj` : `χ + Π = δ`;
* `spatialProj_mul_timeProj` : `χ · Π = 0`;
* `timeProj_mul_spatialProj` : `Π · χ = 0`.

The book's chapter on diffeomorphisms and gravity uses these to conclude that
the two projectors decompose spacetime, `ℝ^{1,3} = im χ ⊕ im Π`.  This file
records that conclusion as a genuine submodule statement, via the general
linear-algebra fact that two complementary, mutually annihilating endomorphisms
have complementary ranges.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/
namespace BookProof.ChapterGravityProjDirectSum

end BookProof.ChapterGravityProjDirectSum


