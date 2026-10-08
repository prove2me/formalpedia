-- Prove2me | Definitions.Def_ChapterAttentionCapacity
-- name    : ChapterAttentionCapacity
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T05:37:03.682585+00:00
-- url     : https://prove2.me/theorems/3a938c05-1027-4cdb-a83c-c3985da32eb9
-- title:
--   Chapter AttentionCapacity
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionCapacity.lean`): generated def bundle for ChapterAttentionCapacity. See BookProof/ChapterAttentionCapacity.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionCapacity.lean

import Definitions.Def_ChapterAttentionRetrieval
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": the capacity of the memory

`ChapterAttentionRetrieval` retrieves *one* stored value under a hypothesis on the
scores.  This module turns that into a statement about the memory as a whole: a
head storing `m` key–value pairs recovers **every** stored pair, provided the keys
are pairwise separated in the coherent-state geometry.

The scores are the physical ones of `ChapterCoherentGeometry`: probing with a query
`q` gives key `l` the score `-‖q - k l‖²`, so that the Born weights are the Softmax
of these scores at inverse temperature `1`.

* `keysSeparated` — the pairwise separation hypothesis `r ≤ ‖k i - k j‖`;
* `distScore_margin_of_separated` — probing with the stored key `k i` gives `i` a
  score margin of `r²` over every other key;
* `scoreSoftmax_distScore_ge_of_separated` — the probe concentrates on the intended
  slot: weight at least `1/(1 + (m-1)e^{-βr²})`;
* `norm_headOutput_distScore_sub_le_of_separated` — **every stored pair is
  recovered**, with error at most `2C(m-1)e^{-βr²}`, uniformly in the slot `i`;
* `exists_beta_forall_retrieval` — hence, for any tolerance `ε > 0`, a finite
  inverse temperature suffices to read the whole memory to accuracy `ε`.  This is
  the capacity statement: `m` patterns cost only `log m` in the required `β`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

open Filter Topology

noncomputable section

namespace BookProof.ChapterAttentionCapacity

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterAttentionOutput BookProof.ChapterCoherentGeometry
  BookProof.ChapterAttentionRetrieval

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Separated keys -/

/-- The score a query assigns to a key in the coherent-state geometry: minus the
squared distance.  The Born weights are the Softmax of these scores. -/
def distScore (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (l : Fin m) : ℝ := -‖q - k l‖ ^ 2

/-- The stored keys are pairwise separated by at least `r`. -/
def keysSeparated (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) : Prop :=
  ∀ i j, i ≠ j → r ≤ ‖k i - k j‖



/-! ## Every stored pair is recovered -/





/-! ## Capacity: a finite temperature suffices -/





end BookProof.ChapterAttentionCapacity

end


