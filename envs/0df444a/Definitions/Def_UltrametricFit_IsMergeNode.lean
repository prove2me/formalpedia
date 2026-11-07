-- Prove2me | Definitions.Def_UltrametricFit_IsMergeNode
-- name    : UltrametricFit_IsMergeNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:51.525435+00:00
-- url     : https://prove2.me/theorems/1aa508c1-2b2e-471e-b783-f6f67593e7a9
-- title:
--   Nodes of a $\delta$-merge forest, and the interpolation $\mu_t$
-- statement:
--   A **$\delta$-merge forest** with respect to $d$ is a forest of binary trees whose nodes are non-empty subsets of $[n]$, whose leaves are distinct singletons, and in which every non-leaf node $A$ has two children with $A=A_1\cup A_2$, $A_1\cap A_2=\emptyset$ and $d(A_1,A_2)\le\delta$. The predicate here says that a set is a node of such a forest. For a non-leaf node, the **interpolation** $\mu_t(A)$ gives a uniform element of $A_1$ with probability $t$ and a uniform element of $A_2$ with probability $1-t$.
--
--   **Formalization Note** The forest is not modelled as an object. A set satisfies `IsMergeNode` exactly when it is a node of some $\delta$-merge forest, namely the tree below it. $\mu_t(A)$ is represented by its point masses $t/|A_1|$ and $(1-t)/|A_2|$.
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Definition 7, pp.8–9; Definition 9, p.9

import Mathlib
import Definitions.Def_UltrametricFit_avgDist

namespace UltrametricFit

/-- **Node of a δ-merge forest**, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), Definition 7, pp.8–9: nodes are non-empty sets, leaves are singletons, and a non-leaf
node `A` has two children with `A = A₁ ∪ A₂`, `A₁ ∩ A₂ = ∅` and `d(A₁, A₂) ≤ δ`.

**Formalization Note.** The forest itself is not modelled. A set is a node of some δ-merge forest
exactly when it satisfies this predicate, and then the whole tree below it is a one-tree forest.
Statements about "two nodes of the merge forest" therefore become statements about two sets
satisfying the predicate, which need not lie in one forest (a `generalization`). -/
inductive IsMergeNode {n : ℕ} (d : Fin n → Fin n → ℝ) (δ : ℝ) : Finset (Fin n) → Prop
  | singleton (i : Fin n) : IsMergeNode d δ {i}
  | union (A₁ A₂ : Finset (Fin n)) :
      IsMergeNode d δ A₁ → IsMergeNode d δ A₂ → Disjoint A₁ A₂ → avgDist d A₁ A₂ ≤ δ →
      IsMergeNode d δ (A₁ ∪ A₂)

/-- **The interpolation** `μ_t(A)` of a non-leaf node with children `A₁, A₂`, Charikar, Gao, STOC
2027 submission (manuscript sha256 87af12a2…), Definition 9, p.9, as its point masses: `t/|A₁|` on
`A₁`, `(1 − t)/|A₂|` on `A₂`, and `0` elsewhere. -/
noncomputable def interpWeight {n : ℕ} (A₁ A₂ : Finset (Fin n)) (t : ℝ) (i : Fin n) : ℝ :=
  if i ∈ A₁ then t / (A₁.card : ℝ) else if i ∈ A₂ then (1 - t) / (A₂.card : ℝ) else 0

end UltrametricFit


