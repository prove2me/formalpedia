-- Prove2me | Definitions.Def_ChapterAttentionLocality
-- name    : ChapterAttentionLocality
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T08:41:25.505146+00:00
-- url     : https://prove2.me/theorems/5c374783-6518-4698-bb38-a055d0200fff
-- title:
--   Chapter AttentionLocality
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAttentionLocality.lean`): generated def bundle for ChapterAttentionLocality. See BookProof/ChapterAttentionLocality.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAttentionLocality.lean

import Definitions.Def_ChapterAttentionSparse
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib


/-!
# Chapter "The Coherent State of Attention": a distance penalty makes a head local

Position information is often injected as a *penalty* rather than as an embedding:
the score of a key is reduced in proportion to its distance from the query
(`sₗ ↦ sₗ − γ·dₗ`).  This module proves that such a head is genuinely local — the
attention it can place at distance `R` decays exponentially in `R` — and that the
resulting sliding-window approximation is therefore exponentially accurate.

Throughout, `d : Fin m → ℝ` is the distance of each key from the query, `γ ≥ 0` the
penalty slope, and `j₀` a key at distance `0` whose score is within `Δ` of every
other raw score.

* `alibiScore` — the penalized score family;
* `scoreSoftmax_alibi_antitone` — with equal raw scores, the nearer key always wins;
* **`scoreSoftmax_alibi_le`** — the headline decay law:
  `pₗ ≤ e^{βΔ}·e^{−βγ dₗ}`;
* `farMass_le` — hence the total attention beyond distance `R` is at most
  `m·e^{βΔ}·e^{−βγR}`;
* `norm_headOutput_window_sub_le` — and the windowed head (attention restricted to
  the keys within distance `R`) is within `2C·m·e^{βΔ}·e^{−βγR}` of the full head:
  a sliding window is not an approximation one has to apologize for.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterAttentionLocality

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
  BookProof.ChapterAttentionMasking BookProof.ChapterAttentionMarkov
  BookProof.ChapterObservableExpectation BookProof.ChapterAttentionOutput
  BookProof.ChapterAttentionSparse

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The penalized head -/

/-- The **distance-penalized score**: the raw alignment score of a key reduced in
proportion to its distance from the query. -/
def alibiScore (s : Fin m → ℝ) (gamma : ℝ) (d : Fin m → ℝ) (l : Fin m) : ℝ :=
  s l - gamma * d l



/-! ## The decay law -/



/-- The keys within distance `R` of the query: the sliding window. -/
def window (d : Fin m → ℝ) (R : ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun l => d l < R





/-! ## The sliding window is exponentially accurate -/



end BookProof.ChapterAttentionLocality

end


