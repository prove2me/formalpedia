-- Prove2me | Definitions.Def_SecondBestMatch_Supplement_FullPotentialTuple
-- name    : SecondBestMatch_Supplement_FullPotentialTuple
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:40:35.962197+00:00
-- url     : https://prove2.me/theorems/e9928d0b-4414-4741-ba09-a92cc20646c6
-- title:
--   Tuple $((x_i)_{i\in B},(y_j)_{j\in S},(U_k)_{k\in K})$ of reduced forms and utility potentials
-- statement:
--   A **reduced-form tuple with potentials** consists of an interim service rule $x_i$ for every buyer $i\in B$, an interim service rule $y_j$ for every seller $j\in S$, and a utility potential $U_k$ for every agent $k\in K=B\sqcup S$.
--
--   It is the variable of the full-potential program of Appendix A: Definition A.1 says when such a tuple is feasible, and Theorem A.2 characterizes the second best as the maximum of the reduced-form GFT over feasible tuples.
--
--   **Formalization Note** Every coordinate is a function $\mathbb R\to\mathbb R$. The feasibility conditions constrain the potentials only on $[0,1]$ and the service rules only almost everywhere under the priors. Agents are indexed by the disjoint union `B ⊕ S`.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea7cce1bbfc7757c56937ec4ac13847b6d0025758a63fa8d6a25314385), Definition A.1, p.27

import Mathlib

namespace SecondBestMatch.Supplement

/-- A tuple `((xᵢ)_{i ∈ B}, (yⱼ)_{j ∈ S}, (U_k)_{k ∈ K})` of reduced-form service rules and
utility potentials (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Definition A.1, p.27).

**Formalization Note** Each coordinate is a function `ℝ → ℝ`; the conditions of Definition A.1
(`IsFullPotentialFeasible`) constrain the potentials only on `[0, 1]` and the service rules only
almost everywhere under the priors. The agent set `K` is `B ⊕ S`. -/
structure FullPotentialTuple (B S : Type*) where
  /-- buyer `i`'s interim service rule `xᵢ` -/
  x : B → ℝ → ℝ
  /-- seller `j`'s interim service rule `yⱼ` -/
  y : S → ℝ → ℝ
  /-- agent `k`'s utility potential `U_k` -/
  U : B ⊕ S → ℝ → ℝ

end SecondBestMatch.Supplement


