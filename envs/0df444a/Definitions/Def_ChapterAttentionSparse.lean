-- Prove2me | Definitions.Def_ChapterAttentionSparse
-- name    : ChapterAttentionSparse
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T07:19:19.6637+00:00
-- url     : https://prove2.me/theorems/cfc23de0-7dfa-475b-af5e-5e1b6d9e388a
-- title:
--   Chapter AttentionSparse
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionSparse.lean`): generated def bundle for ChapterAttentionSparse. See BookProof/ChapterAttentionSparse.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionSparse.lean

import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterAttentionMarkov
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": sparse attention costs exactly the
discarded mass

Long-context transformers do not evaluate every key: they keep a set `S` of
candidate keys (a top-`k` shortlist, a sliding window, a block-sparse pattern) and
renormalize the attention over `S` alone.  `ChapterAttentionMasking` identifies
that operation as Bayesian conditioning; this module prices it.

Write `p` for the full attention distribution and `P(S) = ∑_{l ∈ S} pₗ` for the
mass the head would have put on the shortlist.

* `attendedMass_pos`, `attendedMass_le_one`, `attendedMass_univ` — the shortlist
  mass is a probability;
* **`l1dist_maskedSoftmax_eq`** — the headline: the sparse head differs from the
  dense head by exactly `2(1 − P(S))` in `ℓ¹` — no more and no less;
* `l1dist_maskedSoftmax_le_of_mass` — hence a shortlist that captures `1 − ε` of
  the mass is `2ε`-accurate;
* `norm_headOutput_masked_sub_le` — and the sparse output is within
  `2(1 − P(S))·C` of the dense output for values of norm at most `C`;
* `one_sub_attendedMass_le` — a tail bound: if every discarded key carries at most
  `ε`, the discarded mass is at most `(m − |S|)ε`;
* `l1dist_maskedSoftmax_eq_zero_iff_mass_one` and `maskedSoftmax_eq_of_mass_one` —
  sparsification is lossless exactly when the shortlist already carries all the
  mass.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionSparse

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterAttentionMasking BookProof.ChapterAttentionMarkov
  BookProof.ChapterObservableExpectation BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The mass carried by the shortlist -/

/-- The **attended mass**: the share of the dense attention that the shortlist `S`
would have received. -/
def attendedMass (beta : ℝ) (s : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  ∑ l ∈ S, scoreSoftmax beta s l











/-! ## The price of sparsification -/











/-! ## The output of a sparse head -/



end BookProof.ChapterAttentionSparse

end


