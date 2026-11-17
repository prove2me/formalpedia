-- Prove2me | Definitions.Def_AuctionMatroidInt_Supplement_RankQueryTree
-- name    : AuctionMatroidInt_Supplement_RankQueryTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:21:15.356425+00:00
-- url     : https://prove2.me/theorems/68bba11e-3e2f-480f-9ba7-dba8c3664c58
-- title:
--   Deterministic rank-query algorithms as adaptive query trees
-- statement:
--   A **rank oracle** for a matroid $M=(E,\mathcal I)$ answers, for a queried set $S\subseteq E$, the rank $\operatorname{rank}_M(S)=\max\{|Y| : Y\subseteq S,\ Y\in\mathcal I\}$. A deterministic algorithm with access to finitely many rank oracles (indexed by $\iota$) is modelled as a **rank-query tree**: a finite tree whose internal nodes ask oracle $i\in\iota$ for the rank of a set $S$ and branch on the answer (one branch for every natural number), and whose leaves return an output in $\beta$.
--
--   For an assignment of answers $O:\iota\times 2^E\to\mathbb N$, $\mathrm{run}_O(A)$ is the output reached by following the answers of $O$ from the root, and $\mathrm{queries}_O(A)$ is the number of query nodes on that root-to-leaf path. For independence predicates $(\mathcal I_i)_{i\in\iota}$, the **rank oracle** $O_{\mathcal I}$ answers $(i,S)$ with $\operatorname{rank}_{M_i}(S)$.
--
--   This is the rank-oracle model of query complexity used for Theorems 1.1 and 1.2: computation between queries is free, and each rank query counts once.
--
--   **Formalization Note** `RankQueryTree ι α β` is the natural-number-answer analogue of the published Boolean `AuctionMatroidInt.QueryTree`; `rankOracle I i S` is the published `CombOpt.MatroidPolytope.rank (I i) S`. Two matroids are indexed by `Fin 2` ($0\mapsto M_1$, $1\mapsto M_2$).
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §2.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_rank

namespace AuctionMatroidInt.Supplement

/-- **Deterministic rank-query algorithms as adaptive query trees.**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), §2.1, p.10: "A rank oracle for a
matroid M is an oracle that, given a subset X ⊆ E, returns rank_M(X)."

A `RankQueryTree ι α β` is a deterministic adaptive algorithm that may ask the oracle `i : ι`
(one oracle per matroid) for the rank of a set `S : Finset α`, branch on the answer (a natural
number; one branch for every possible value), and finally return a value of type `β`.

**Formalization Note.** This is the rank-answer analogue of the published
`AuctionMatroidInt.QueryTree` (whose answers are Booleans). One rank query is one node, so it
costs exactly one query. The tree *is* the algorithm: what the algorithm knows explicitly (`n`,
the weights, `ε`) are parameters from which the tree is built, while the matroids are seen only
through the oracle's answers. Computation between queries is free, which is what query
complexity counts (§2.1, p.10). Trees are inductive, so every algorithm terminates. -/
inductive RankQueryTree (ι α β : Type) where
  /-- Stop and return a value. -/
  | ret : β → RankQueryTree ι α β
  /-- Ask oracle `i` for the rank of `S` and continue with the branch of the answer. -/
  | query : ι → Finset α → (ℕ → RankQueryTree ι α β) → RankQueryTree ι α β

namespace RankQueryTree

variable {ι α β : Type}

/-- The output of the tree when the oracles answer according to `O` (`O i S` is the answer of
oracle `i` to the set `S`). -/
def run (O : ι → Finset α → ℕ) : RankQueryTree ι α β → β
  | ret b => b
  | query i S k => run O (k (O i S))

/-- The number of oracle queries the tree makes when the oracles answer according to `O`: the
number of `query` nodes on the root-to-leaf path that `O` selects (not the size of the tree). -/
def queries (O : ι → Finset α → ℕ) : RankQueryTree ι α β → ℕ
  | ret _ => 0
  | query i S k => queries O (k (O i S)) + 1

end RankQueryTree

/-- **The rank oracle of a family of matroids.** For independence predicates
`I : ι → Finset α → Prop`, the oracle answers the query `(i, S)` with
`rank_{Mᵢ}(S) = max{|Y| : Y ⊆ S, Y ∈ 𝓘ᵢ}` (the published `CombOpt.MatroidPolytope.rank`).

**Formalization Note.** Two matroids are indexed by `Fin 2` (`0 ↦ M₁`, `1 ↦ M₂`). -/
noncomputable def rankOracle {ι α : Type} (I : ι → Finset α → Prop) : ι → Finset α → ℕ :=
  fun i S => CombOpt.MatroidPolytope.rank (I i) S

end AuctionMatroidInt.Supplement


