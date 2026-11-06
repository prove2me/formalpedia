-- Prove2me | Definitions.Def_SparseMatchingDesign_survivalWeight
-- name    : SparseMatchingDesign_survivalWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:36.343504+00:00
-- url     : https://prove2.me/theorems/f94b6c48-6ecb-4644-b833-c11f37d671e2
-- title:
--   Probability $p^{|S|}(1-p)^{n-|S|}$ that exactly the nodes of $S$ survive
-- statement:
--   Each of the $n$ nodes of $[n]=\{1,\dots,n\}$ survives independently with probability $p$ and is deleted with probability $q=1-p$. The probability that the set $\widetilde V$ of surviving nodes equals a given $S\subseteq[n]$ is
--   $$w_p(S)=p^{|S|}(1-p)^{\,n-|S|}.$$
--   These weights describe the law of the random residual node set used throughout the paper.
--
--   **Formalization Note** Nodes are `Fin n` (paper node $i$ is index $i-1$); the number of deleted nodes $n-|S|$ is the cardinality of the complement of $S$.
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §2.2, p.6

import Mathlib

namespace SparseMatchingDesign

/-- The probability that the set of surviving nodes is exactly `S` when each of the `n` nodes
survives independently with probability `p` (is deleted with probability `q = 1 - p`):
`w_p(S) = p^{|S|} (1 - p)^{n - |S|}`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §2.2, p.6: "After each node in V is deleted with probability q independently, a random
subset of nodes, Ṽ, remains, so that Pr(i ∈ Ṽ) = p for all i ∈ V."

**Formalization Note** The node set [n] is `Fin n` (paper node i is index i − 1). The number of
deleted nodes n − |S| is written `Sᶜ.card`, which avoids natural-number subtraction. -/
noncomputable def survivalWeight (n : ℕ) (p : ℝ) (S : Finset (Fin n)) : ℝ :=
  p ^ S.card * (1 - p) ^ Sᶜ.card

end SparseMatchingDesign


