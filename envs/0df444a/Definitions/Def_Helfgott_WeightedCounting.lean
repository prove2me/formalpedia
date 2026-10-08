-- Prove2me | Definitions.Def_Helfgott_WeightedCounting
-- name    : Helfgott_WeightedCounting
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-04T20:26:53.027652+00:00
-- url     : https://prove2.me/theorems/efbb429d-4b5d-4867-b8cc-58c6c4781548
-- title:
--   Weighted exponential sums and ternary representation counts
-- statement:
--   For a complex coefficient sequence $a$, define its exponential sum on the unit circle by
--
--   $$S_a(\alpha)=\sum_{n\ge0}a_n e(n\alpha).$$
--
--   For three coefficient sequences $a,b,c$, define the finite ternary representation count
--
--   $$R_{a,b,c}(N)=\sum_{i+j+k=N}a_i b_j c_k.$$
--
--   The summation includes zero indices; in the von Mangoldt application their weights vanish. The complex series is the ordinary infinite sum, with its convergence hypotheses supplied by the separate counting theorem. These definitions retain the full tails of the Gaussian-based smoothings used by Helfgott; they do not truncate the exponential sums at $N$.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (1.3) and (7.49), §1.3 and §7.4 (printed pp. 69–71 for the conclusion). https://arxiv.org/abs/1312.7748 . General coefficient interface for the weighted sums, with a_n=Λ(n)η(n/x) in the paper. Written by Codex.

import Mathlib.Analysis.Fourier.AddCircle

open scoped BigOperators

namespace Helfgott

noncomputable def expSum (a : ℕ → ℂ) (α : AddCircle (1 : ℝ)) : ℂ :=
  ∑' n : ℕ, a n * fourier (n : ℤ) α

def tripleIndices (N : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)) ×ˢ Finset.range (N + 1)).filter
    (fun t => t.1.1 + t.1.2 + t.2 = N)

noncomputable def tripleCount (a b c : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ t ∈ tripleIndices N, a t.1.1 * b t.1.2 * c t.2

end Helfgott


