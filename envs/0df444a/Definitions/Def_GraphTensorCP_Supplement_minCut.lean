-- Prove2me | Definitions.Def_GraphTensorCP_Supplement_minCut
-- name    : GraphTensorCP_Supplement_minCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:23:33.988674+00:00
-- url     : https://prove2.me/theorems/02381c52-d937-4644-bda8-ee1eec63eb91
-- title:
--   Weighted minimum cut $\mathrm{MinCut}(W)$
-- statement:
--   For a symmetric nonnegative zero-diagonal matrix $W$ of order $n\ge2$, the **minimum cut weight** is
--
--   $$
--   \mathrm{MinCut}(W)=\min_{\emptyset\ne S\subsetneq[n]}\sum_{\substack{i<j\\|\{i,j\}\cap S|=1}}W_{i,j}.
--   $$
--
--   It is the weighted edge connectivity of the support graph and is the exact logarithmic asymptotic subrank of a weighted graph tensor.
--
--   **Formalization Note** This reuses the published `cutWeight` and takes an infimum over the finite type of nonempty proper subsets of `Fin n`. For $n\ge2$ that type is nonempty, so the infimum is the ordinary minimum.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 2.27, p.26; Theorem B.5, p.80

import Mathlib
import Definitions.Def_GraphTensorCP_maxCut

namespace GraphTensorCP

namespace Supplement

/-- The **minimum cut weight** of a symmetric nonnegative zero-diagonal matrix `W`
(Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*,
arXiv:2610.34273 (version of 2026-11-03), Definition 2.27, p.26, used in Theorem B.5, p.80):
the minimum of `cutWeight W S` over nonempty proper vertex sets.

**Formalization Note.** The infimum is over the same finite subtype as the published `maxCut`.
For the paper's standing assumption `n ≥ 2` the subtype is nonempty and finite, so this is the
ordinary minimum. -/
noncomputable def minCut {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨅ S : {S : Finset (Fin n) // S.Nonempty ∧ S ≠ Finset.univ}, cutWeight W S.1

end Supplement

end GraphTensorCP


