-- Prove2me | Definitions.Def_AvgPHETH_expTime
-- name    : AvgPHETH_expTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:46.614196+00:00
-- url     : https://prove2.me/theorems/45101701-e092-48dd-95f9-ac1356e0aa19
-- title:
--   The time bound $2^{O(n^\alpha)}$
-- statement:
--   The number of steps $\lceil 2^{Cn^\alpha}\rceil+C$, which is the bound $2^{O(n^\alpha)}$ with its hidden constant named. The summand $C$ is for small $n$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 5.1, p.19 (PDF 21); Lemma 6.1, p.24 (PDF 26)

import Mathlib

namespace AvgPHETH

/-- The time bound `2^{O(n^α)}` with hidden constant `C`, as a natural-number clock
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 5.1, p.19 (PDF 21); Lemma 6.1, p.24 (PDF 26)).

**Formalization Note** The summand `C` is for small `n`: at `n = 0` the power alone is one step. -/
noncomputable def expTime (C : ℕ) (α : ℝ) (n : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ ((C : ℝ) * (n : ℝ) ^ α)⌉₊ + C

end AvgPHETH


