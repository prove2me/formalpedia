-- Prove2me | Definitions.Def_AuctionMatroidInt_QueryTree
-- name    : AuctionMatroidInt_QueryTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:14.528595+00:00
-- url     : https://prove2.me/theorems/badc892e-d7d8-4d46-b672-19ddd98c4c46
-- title:
--   Deterministic independence-query algorithms as adaptive query trees
-- statement:
--   An **independence oracle** for a matroid $M=(E,\mathcal I)$ answers, for a queried set $S\subseteq E$, whether $S\in\mathcal I$. A deterministic algorithm with access to finitely many such oracles (indexed by $\iota$) is modelled as a **query tree**: a finite tree whose internal nodes ask oracle $i\in\iota$ about a set $S$ and branch on the Boolean answer, and whose leaves return an output in $\beta$.
--
--   For an assignment of answers $O:\iota\times 2^E\to\{\mathrm{true},\mathrm{false}\}$, $\mathrm{run}_O(A)$ is the output reached by following the answers of $O$ from the root, and $\mathrm{queries}_O(A)$ is the number of query nodes on that root-to-leaf path. For independence predicates $(\mathcal I_i)_{i\in\iota}$, the **independence oracle** $O_{\mathcal I}$ answers $(i,S)$ with true exactly when $S\in\mathcal I_i$.
--
--   This is the model of query complexity used in the paper: computation between queries is free, and only the number of oracle calls is counted. The data the algorithm knows explicitly (such as $n$, the weights and $\varepsilon$) are parameters from which the tree is built; the matroids are seen only through the answers.
--
--   **Formalization Note** `QueryTree ι α β` is an inductive type (so every algorithm terminates); `run` and `queries` follow the path selected by the oracle; `indepOracle I` is `fun i S => decide (I i S)` with classical decidability. Two matroids are indexed by `Fin 2` ($0\mapsto M_1$, $1\mapsto M_2$), one matroid by `Unit`.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §2.1, p.10 (PDF p.12)

import Mathlib

namespace AuctionMatroidInt

/-- **Deterministic independence-query algorithms as adaptive query trees.**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), §2.1, p.10: "we suppose that each
matroid is given as oracles. An independence oracle for a matroid M is an oracle that, given a
subset X ⊆ E, determines whether X ∈ I."

A `QueryTree ι α β` is a deterministic adaptive algorithm that may ask the oracle `i : ι`
(one oracle per matroid) whether a set `S : Finset α` is independent, branch on the Boolean
answer, and finally return a value of type `β`.

**Formalization Note.** The tree *is* the algorithm: everything the algorithm knows explicitly
(the ground set, the weights, ε, and for a subroutine its explicit inputs) is a parameter from
which the tree is built, while the matroids are reachable only through the answers of the oracle.
Computation between queries is free, which is what query complexity counts (§2.1, p.10). The
trees are finite (inductive), so every algorithm terminates. -/
inductive QueryTree (ι α β : Type) where
  /-- Stop and return a value. -/
  | ret : β → QueryTree ι α β
  /-- Ask oracle `i` whether `S` is independent and continue with the branch of the answer. -/
  | query : ι → Finset α → (Bool → QueryTree ι α β) → QueryTree ι α β

namespace QueryTree

variable {ι α β : Type}

/-- The output of the query tree `A` when the oracles answer according to `O`
(`O i S = true` meaning "`S` is independent in matroid `i`"). -/
def run (O : ι → Finset α → Bool) : QueryTree ι α β → β
  | ret b => b
  | query i S k => run O (k (O i S))

/-- The number of oracle queries the tree makes when the oracles answer according to `O`:
the number of `query` nodes on the root-to-leaf path that `O` selects (not the size of the
tree). -/
def queries (O : ι → Finset α → Bool) : QueryTree ι α β → ℕ
  | ret _ => 0
  | query i S k => queries O (k (O i S)) + 1

end QueryTree

open Classical in
/-- **The independence oracle of a family of matroids.** For independence predicates
`I : ι → Finset α → Prop` (`I i S` meaning `S ∈ 𝓘ᵢ`), the oracle answers the query
`(i, S)` with `true` exactly when `S` is independent in the `i`-th matroid.

**Formalization Note.** The Boolean answer is `decide (I i S)` with classical decidability; the
algorithm never sees `I` except through these answers. Two matroids are indexed by `Fin 2`
(`0 ↦ M₁`, `1 ↦ M₂`), one matroid by `Unit`. -/
noncomputable def indepOracle {ι α : Type} (I : ι → Finset α → Prop) : ι → Finset α → Bool :=
  fun i S => decide (I i S)

end AuctionMatroidInt


