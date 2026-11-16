-- Prove2me | Definitions.Def_ManipPotential_Supplement_IsScoringVector
-- name    : ManipPotential_Supplement_IsScoringVector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:56:19.859903+00:00
-- url     : https://prove2.me/theorems/69177e40-5247-4a87-8c76-6052ac68f6de
-- title:
--   Positional scoring vectors $1 = s_1 \ge s_2 \ge \dots \ge s_m = 0$
-- statement:
--   A (monotonic) **positional scoring vector** is a vector $s = (s_j)_{j \in [m]}$ of reals with
--   $$1 = s_1 \ge s_2 \ge \dots \ge s_m = 0 .$$
--
--   Such a vector defines the positional scoring rule $F^s$ (Definition 3).
--
--   **Formalization Note** Positions are 0-based: the Lean entry at index $j$ is the paper's $s_{j+1}$, so the condition reads: antitone, entry $0$ equal to $1$, entry $m-1$ equal to $0$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 3, p.15

import Mathlib

namespace ManipPotential.Supplement

/-- A (monotonic) positional scoring vector `s = (s_j)_{j∈[m]}` with `1 = s₁ ≥ s₂ ≥ ⋯ ≥ s_m = 0`
(Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 3, p.15).

**Formalization Note** Positions are 0-based: `s ⟨j, _⟩` is the paper's `s_{j+1}`, so the first
entry (index `0`) is `1`, the last (index `m − 1`) is `0`, and `s` is antitone. -/
def IsScoringVector {m : ℕ} (s : Fin m → ℝ) : Prop :=
  Antitone s ∧ (∀ i : Fin m, i.val = 0 → s i = 1) ∧ (∀ i : Fin m, i.val + 1 = m → s i = 0)

end ManipPotential.Supplement


