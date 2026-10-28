-- Prove2me | Definitions.Def_ChapterSolovaySeparableExistence
-- name    : ChapterSolovaySeparableExistence
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T13:07:49.430983+00:00
-- url     : https://prove2.me/theorems/900a577f-3b31-4759-8ec2-e57e4ee4bd60
-- title:
--   Chapter SolovaySeparableExistence
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSolovaySeparableExistence.lean`): generated def bundle for ChapterSolovaySeparableExistence. See BookProof/ChapterSolovaySeparableExistence.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSolovaySeparableExistence.lean

import Definitions.Def_ChapterSolovay
import Definitions.Def_ChapterSolovayCoordinates
import Definitions.Def_ChapterSolovayTailDimension
import Mathlib

/-!
# The Introduction's question, answered: a separable law with an arbitrary finite
part; wave-functions for finite joint laws; product disintegration
(plan §4.4, §4.5, §4.6)

Three small, self-contained closers of the Solovay–Kopperman programme.

## Deliverables

* **§4.4 — `joint_prob_has_wavefunction`.**  Every finite joint probability law is
  `|Ψ|²` for a wave-function: given `p ≥ 0` on a finite type with `∑ p = 1` there
  is `Ψ` with `‖Ψ z‖² = p z` and `∑ ‖Ψ z‖² = 1`.  `joint_prob_has_wavefunction_prod`
  is the two-variable form, in which the marginal of `|Ψ|²` in the first variable
  is the marginal of `p`;
* **§4.5 — `exists_separable_prob_with_arbitrary_finite_law`.**  The Introduction's
  problem: a *separable* probability space carrying an **arbitrary** law on the
  finite head and the (forced) Mehler law on the infinite tail, with the correct
  finite marginal.  Stated both in the coordinate model
  (`CoordinateSpace N = (Fin N → ℝ) × (ℕ → ℝ)`) and in the abstract substrate model
  (`InnerSpace N = InnerHead N × InnerTail`), together with the separability of both
  carriers.  The tail factor is genuinely infinite dimensional
  (`ChapterSolovayTailDimension.tail_infinite_dimensional`), so the construction is
  not a finite-dimensional artefact;
* **§4.6 — `prod_disintegration`.**  The explicit `joint = marginal ⊗ₘ kernel` form
  of disintegration on a standard Borel second factor, the companion of the
  `condDistrib` route used in `ChapterSelectingEvents`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/
namespace BookProof.ChapterSolovaySeparableExistence

end BookProof.ChapterSolovaySeparableExistence


