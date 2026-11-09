-- Prove2me | Definitions.Def_ManipPotential_manipPotentialAt
-- name    : ManipPotential_manipPotentialAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:29.680463+00:00
-- url     : https://prove2.me/theorems/d8eab0dd-be0b-48d4-ab15-c6a53297ddba
-- title:
--   Manipulation potential $\mathrm{MP}(f)$ at electorate size $n$ (Definition 2)
-- statement:
--   For an SCF $f$ and an electorate size $n$, the **manipulation potential** is
--   $$
--   \mathrm{MP}(f) = \min\{k \in \mathbb Z_{\ge 0} : f \text{ is } k'\text{-ASP for all } k' \ge k\},
--   $$
--   and $\mathrm{MP}(f) = \infty$ if no such $k$ exists. It is the least number of extra truthful copies from which on a voter always weakly prefers the augmented outcome to any manipulation.
--
--   **Formalization Note** The value lies in $\mathbb N \cup \{\infty\}$ (`ℕ∞`), defined as an infimum; the infimum of the empty set is $\infty$, as in the definition. For each $K \in \mathbb N$, $\mathrm{MP}(f) \le K$ holds exactly when $f$ is $k$-ASP at size $n$ for every $k \ge K$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 2, p.8

import Mathlib
import Definitions.Def_ManipPotential_IsKASPAt

namespace ManipPotential

/-- The manipulation potential of `f` at electorate size `n` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Definition 2, p.8):
`MP(f) = min {k ∈ ℤ_{≥0} : f is k'-ASP for all k' ≥ k}`, and `MP(f) = ∞` if no such `k` exists.

**Formalization Note** Valued in `ℕ∞`; the infimum of the empty set is `⊤ = ∞`, as printed. -/
noncomputable def manipPotentialAt {m : ℕ} (f : List (Ranking m) → Fin m) (n : ℕ) : ℕ∞ :=
  sInf {x : ℕ∞ | ∃ k : ℕ, x = k ∧ ∀ k' : ℕ, k ≤ k' → IsKASPAt f n k'}

end ManipPotential


