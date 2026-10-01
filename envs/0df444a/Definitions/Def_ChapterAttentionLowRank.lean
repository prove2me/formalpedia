-- Prove2me | Definitions.Def_ChapterAttentionLowRank
-- name    : ChapterAttentionLowRank
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:23:06.293431+00:00
-- url     : https://prove2.me/theorems/7445a537-3c59-4004-bb12-9d4c78153354
-- title:
--   Chapter AttentionLowRank
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionLowRank.lean`): generated def bundle for ChapterAttentionLowRank. See BookProof/ChapterAttentionLowRank.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionLowRank.lean

import Mathlib


/-!
# Chapter "The Coherent State of Attention": the low-rank bottleneck of a head

A head computes its scores as `sᵢⱼ = ⟨qᵢ, kⱼ⟩` with queries and keys living in the
*head dimension* `d`, usually far smaller than the number of positions `m`.  That
factorization is a hard structural constraint, and this module states it as one.

* `rank_scoreMatrix_le` — **every score matrix a head can produce has rank at most
  `d`**: the `m × m` table of alignments factors through `ℝ^d`.
* `not_exists_scoreMatrix_one` — consequently, when `d < m` no head can realize the
  "each position attends to itself and to nothing else" pattern, whose score matrix
  is the identity and has rank `m`.  A single head is not a general router.
* `exists_scoreMatrix_one_of_le` — and the bound is sharp: at `d ≥ m` the identity
  pattern is realized by orthonormal query/key vectors.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionLowRank

variable {m d : ℕ}

/-- The score matrix of a head with query vectors `Q i` and key vectors `K j` in
the head dimension `d`. -/
def scoreMatrix (Q K : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => ∑ a, Q i a * K j a











end BookProof.ChapterAttentionLowRank

end


