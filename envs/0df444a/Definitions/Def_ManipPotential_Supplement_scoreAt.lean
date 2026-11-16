-- Prove2me | Definitions.Def_ManipPotential_Supplement_scoreAt
-- name    : ManipPotential_Supplement_scoreAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:59:08.710598+00:00
-- url     : https://prove2.me/theorems/ddd281fe-c9e6-4eaf-b82d-69b27c4dab36
-- title:
--   1-based entries $s_j$ of a scoring vector
-- statement:
--   For a scoring vector $s$ and $j \in [m]$, $s_j$ denotes its $j$-th entry (1-based), as in the formulas of Section 4.2.
--
--   **Formalization Note** A helper to transcribe the 1-based formulas of Theorems 4.5, 4.6 and 4.9 literally: it returns the Lean entry at index $j-1$ for $1 \le j \le m$, and $0$ outside that range, which no statement queries.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.2, pp.15–16

import Mathlib

namespace ManipPotential.Supplement

/-- The 1-based entry `s_j` of a scoring vector (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 3, p.15), used to transcribe the
1-based formulas of Theorem 4.6 (pp.15–16) literally.

**Formalization Note** `scoreAt s j = s ⟨j − 1, _⟩` for `1 ≤ j ≤ m`, and `0` outside that range;
the statements only query indices in `[1, m]`. -/
def scoreAt {m : ℕ} (s : Fin m → ℝ) (j : ℕ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ m then s ⟨j - 1, by omega⟩ else 0

end ManipPotential.Supplement


