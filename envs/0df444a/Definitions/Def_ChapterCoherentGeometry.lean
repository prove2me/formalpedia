-- Prove2me | Definitions.Def_ChapterCoherentGeometry
-- name    : ChapterCoherentGeometry
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-05T15:10:27.479988+00:00
-- url     : https://prove2.me/theorems/4964b3ec-7f6c-4676-837d-da9014c1f268
-- title:
--   Chapter CoherentGeometry
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCoherentGeometry.lean`): generated def bundle for ChapterCoherentGeometry. See BookProof/ChapterCoherentGeometry.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCoherentGeometry.lean

import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib

/-!
# Chapter "The Coherent State of Attention", §"The Geometry of the Wave-packet"

`Book/CoherentState.lean` reads the coherent-state overlap geometrically: a key is
a *wave-packet* centred at its parameter, and the query interrogates the packets by
proximity.  `ChapterCoherentOverlap` already identifies the overlap with the
Gaussian kernel `exp (-‖q - k‖² / 2)`; this module turns that identification into
the order-theoretic statements the prose actually uses.

* `neg_two_mul_log_coherentOverlap` — the kernel is a *metric readout*:
  `-2 log ⟨q|k⟩ = ‖q - k‖²`.  Nothing is lost in passing from the distance to the
  overlap.
* `coherentOverlap_le_iff_dist_le` / `coherentOverlap_lt_iff_dist_lt` — the overlap
  is a strictly decreasing function of the distance between the parameters.
* `bornWeight_eq_scoreSoftmax_neg_dist_sq` — the **Born weight is a Softmax over
  minus the squared distances**, at inverse temperature `1`.  This is the geometric
  face of `coherentBorn_eq_softmax`: it needs no hypothesis on the key norms,
  because the key penalties are exactly what the squared distance absorbs.
* `bornWeight_le_iff_dist_le` — consequently the Born weights order the keys by
  proximity, and `bornWeight_max_of_nearest` / `bornWeight_lt_of_nearest`: the
  nearest key carries the largest attention weight (strictly, if it is strictly
  nearest).

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/
namespace BookProof.ChapterCoherentGeometry

end BookProof.ChapterCoherentGeometry


