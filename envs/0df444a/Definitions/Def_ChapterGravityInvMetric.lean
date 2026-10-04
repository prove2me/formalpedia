-- Prove2me | Definitions.Def_ChapterGravityInvMetric
-- name    : ChapterGravityInvMetric
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:06:10.461394+00:00
-- url     : https://prove2.me/theorems/36c25ff4-be93-4e12-9ba1-df0503535e5b
-- title:
--   Chapter GravityInvMetric
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGravityInvMetric.lean`): generated def bundle for ChapterGravityInvMetric. See BookProof/ChapterGravityInvMetric.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGravityInvMetric.lean

import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityMetric
import Mathlib


/-!
# Chapter — Diffeomorphisms and gravity: the inverse (raised) spatial metric `h♯ = η + v⊗v`

Source: `book.tex`, chapter *"Diffeomorphisms and gravity"*, §*"Classical
Hamiltonian"* (line ~8091).  Continuing the standing directive (mine the next
self-contained mathematical claim from `book.tex`) and building directly on
`ChapterGravityProjector` (Wave 69) and `ChapterGravityMetric` (Wave 70), we
treat the **inverse spatial metric** obtained by raising both indices of the
induced spatial metric `h_{ab} = η_{ab} + v_a v_b`:

`h^{ab} = η^{ab} + v^a v^b`.

Relative to a globally defined **unit timelike vector** `v`
(`minkSq v = −1` in the mostly-plus Minkowski metric `η = diag(−1,1,1,1)`),
`h^♯` is the metric induced on the cotangent spatial hyperplane.  Since the
Minkowski metric is an involution (`η^{ab} = η_{ab}`, so `η² = 1`), the raised
and lowered spatial metrics compose to the spatial **projector** `χ`, the
hallmark of a (degenerate) inverse metric pair.  This file records those
self-contained linear-algebra facts, reusing `metric`, `lower`, `minkSq`,
`spatialProj` from `ChapterGravityProjector` and `spatialMetric` from
`ChapterGravityMetric`.

Formalized here (all under `minkSq v = -1` where noted):

* `invSpatialMetric v` — the symmetric matrix `h^{ab} = η^{ab} + v^a v^b`;
* `metric_mul_metric` — the Minkowski metric is an involution, `η · η = 1`
  (so `η` is its own inverse: `η^{ab} η_{bc} = δ^a{}_c`);
* `invSpatialMetric_symm` — `h^♯` is symmetric (`(h♯)ᵀ = h♯`);
* `invSpatialMetric_mulVec_lower_self` — `h^♯` annihilates the lowered vector
  `v_a` (`h^{ab} v_b = 0`): the inverse metric degenerates along the time
  covector, complementary to `h_{ab} v^b = 0`;
* `invSpatialMetric_mul_spatialMetric` — **headline**: `h^♯ · h = χ`, the raised
  and lowered spatial metrics compose to the spatial projector `χ^a{}_b`
  (identity on `v^⊥`), the defining relation of an inverse-metric pair on the
  degenerate hyperplane.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); no `EXTERNAL` hypothesis, no `axiom`.
-/

namespace BookProof.ChapterGravityInvMetric

open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric

/-- The inverse (raised) spatial `(2,0)` metric `h^{ab} = η^{ab} + v^a v^b`. -/
noncomputable def invSpatialMetric (v : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  metric + Matrix.of (fun a b => v a * v b)

/-
The Minkowski metric is an involution: `η · η = 1`.  Equivalently `η^{ab}` (=
`η_{ab}` numerically) is its own inverse, `η^{ab} η_{bc} = δ^a{}_c`.
-/


/-
`h^♯` is symmetric.
-/


/-
`h^♯` annihilates the lowered timelike covector `v_a = lower v a`
(`h^{ab} v_b = 0`): the inverse spatial metric is degenerate exactly along the
time covector, complementary to `h_{ab} v^b = 0`.
-/


/-
**Headline.** The raised and lowered spatial metrics compose to the spatial
projector, `h^♯ · h = χ`: the inverse metric pair acts as the identity on the
spatial hyperplane `v^⊥`.
-/


end BookProof.ChapterGravityInvMetric


