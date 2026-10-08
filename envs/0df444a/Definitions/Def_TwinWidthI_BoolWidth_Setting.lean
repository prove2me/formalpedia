-- Prove2me | Definitions.Def_TwinWidthI_BoolWidth_Setting
-- name    : TwinWidthI_BoolWidth_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:54.30606+00:00
-- url     : https://prove2.me/theorems/d9295b48-db14-41cf-a253-f3959cb449ce
-- title:
--   pp. 3:11–3:14 — twin-width (partition form), decomposition trees and boolean-width
-- statement:
--   Let $G$ be a finite simple graph on a vertex set $V$.
--
--   **Twin-width.** Two vertex sets $X, Y$ are *homogeneous* in $G$ if either every pair $(x,y)\in X\times Y$ is an edge or no pair is. For a partition $\mathcal P$ of $V$, the *red degree* of a part $X$ is the number of other parts $Y\neq X$ of $\mathcal P$ that are not homogeneous to $X$; $\mathcal P$ is a *$d$-partition* if every part has red degree at most $d$. A *merge step* replaces two distinct parts $X, Y$ by $X\cup Y$. The graph $G$ has *twin-width at most $d$*, written $\operatorname{tww}(G)\le d$, if there is a sequence of partitions
--   $$\mathcal P_0,\ \mathcal P_1,\ \dots,\ \mathcal P_N$$
--   of $V$ such that $\mathcal P_0$ is the partition into singletons, $\mathcal P_N$ has at most one part, each $\mathcal P_{i+1}$ is obtained from $\mathcal P_i$ by one merge step, and every $\mathcal P_i$ is a $d$-partition.
--
--   **Decomposition trees.** A *decomposition tree* of $G$ is a rooted binary tree $T$ (every internal node has exactly two children) whose leaves are in one-to-one correspondence with $V$. Every edge $e$ of $T$ lies directly above exactly one rooted subtree $T_e$, and induces the partition $P_e=(A_e,B_e)$ of $V$ where $A_e$ is the set of leaf labels of $T_e$ and $B_e=V\setminus A_e$.
--
--   **Boolean-width.** For disjoint sets $A,B\subseteq V$, let
--   $$\nu_G(A,B)=\bigl|\{\,N(S)\cap B : S\subseteq A\,\}\bigr|,\qquad N(S)\cap B=\{b\in B:\ b \text{ has a neighbour in } S\},$$
--   the number of different neighbourhoods in $B$ of subsets of $A$ (the empty set $S=\emptyset$ included). The boolean-width of the cut $(A,B)$ is $\log_2\nu_G(A,B)$. The boolean-width of $T$ is the maximum over all edges $e$ of $T$ of the boolean-width of $P_e$, and $\operatorname{boolw}(G)$ is the minimum over decomposition trees. We write $\operatorname{BW}(G,N)$ for "some decomposition tree $T$ of $G$ has $\nu_G(A_e,B_e)\le N$ for every edge $e$ of $T$"; thus $\operatorname{boolw}(G)\le k$ if and only if $\operatorname{BW}(G,2^k)$.
--
--   These are the objects of Theorem 4.2: graphs of boolean-width $k$ have twin-width at most $2^{k+1}-1$.
--
--   **Formalization Note.** Twin-width is stated in the paper's equivalent partition form (p. 3:12: a red edge between two contracted vertices exactly when their vertex sets are not homogeneous; p. 3:32: sequences of $d$-partitions); trigraphs are not formalized. Twin-width is never a number here: $\operatorname{tww}(G)\le d$ is the predicate `TwinWidthLE G d`, so no infimum over an empty set can occur. The final partition is required to have *at most* one part, which covers the empty vertex set. Decomposition trees are the inductive type `DTree V` of binary trees with labelled leaves; the edges of $T$ are its proper rooted subtrees (`properSubtrees`), and the cut of the edge above a subtree $S$ is (leaves of $S$, the rest of $V$). Boolean-width is kept as the integer count $\nu$ (`nbhdCount`), and `BoolWidthLE G N` bounds it by $N$ on every edge, so "boolean-width $k$" is `BoolWidthLE G (2^k)`. A one-vertex graph has a one-leaf tree with no edges, so `BoolWidthLE G N` holds for every $N$; the empty vertex set has no decomposition tree.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), pp. 3:11–3:12 §3 (twin-width), p. 3:32 §7.1 (d-partitions), p. 3:14 §4.2 (boolean-width, decomposition tree, footnote 5)

import Mathlib

namespace TwinWidthI.BoolWidth

open Finset

/-! ### Graph twin-width in partition form (pp. 3:11–3:12, p. 3:32) -/

/-- p. 3:17 "contraction of P and P′", p. 3:32: merging two distinct parts `X`, `Y` of `P`
gives `Q`. -/
def IsMergeStep {α : Type*} [DecidableEq α] {s : Finset α} (P Q : Finpartition s) : Prop :=
  ∃ X ∈ P.parts, ∃ Y ∈ P.parts, X ≠ Y ∧ Q.parts = insert (X ∪ Y) ((P.parts.erase X).erase Y)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- p. 3:12, p. 3:32: two vertex sets are homogeneous in `G` if all pairs or no pairs are
edges. -/
def Homogeneous (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  (∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) ∨ (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y)

open Classical in
/-- p. 3:32: `P` is a d-partition: every part is non-homogeneous to at most `d` other parts
(the red graph `G_P` has maximum degree at most `d`). -/
def IsDPartition (G : SimpleGraph V) (P : Finpartition (univ : Finset V)) (d : ℕ) : Prop :=
  ∀ X ∈ P.parts, #{Y ∈ P.parts | Y ≠ X ∧ ¬ Homogeneous G X Y} ≤ d

/-- pp. 3:12, 3:32: `G` has twin-width at most `d`: a sequence of d-partitions from the
partition into singletons (`⊥`) to a partition with at most one part, each obtained from the
previous by merging two parts. -/
def TwinWidthLE (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ (N : ℕ) (P : Fin (N + 1) → Finpartition (univ : Finset V)),
    P 0 = ⊥ ∧ #(P (Fin.last N)).parts ≤ 1 ∧
    (∀ i : Fin N, IsMergeStep (P i.castSucc) (P i.succ)) ∧
    ∀ i, IsDPartition G (P i) d

/-! ### Decomposition trees and boolean-width (§4.2, p. 3:14) -/

/-- p. 3:14, footnote 5: a rooted binary tree whose leaves carry labels in `α`; every
internal node has exactly two children. -/
inductive DTree (α : Type*)
  | leaf : α → DTree α
  | node : DTree α → DTree α → DTree α

namespace DTree

variable {α : Type*}

/-- The labels of the leaves, left to right. -/
def leaves : DTree α → List α
  | leaf a => [a]
  | node l r => l.leaves ++ r.leaves

/-- Every rooted subtree, the tree itself included. -/
def subtrees : DTree α → List (DTree α)
  | leaf a => [leaf a]
  | node l r => node l r :: (l.subtrees ++ r.subtrees)

/-- Every rooted subtree except the whole tree: the subtrees hanging below an edge of `T`.
Each edge `e` of `T` is the edge above exactly one of them. -/
def properSubtrees : DTree α → List (DTree α)
  | leaf _ => []
  | node l r => l.subtrees ++ r.subtrees

end DTree

/-- p. 3:14: `T` is a decomposition tree of a graph on `V`: its leaves are in one-to-one
correspondence with `V` (no label repeats, every vertex is a label). -/
def IsDecompTree (T : DTree V) : Prop := T.leaves.Nodup ∧ ∀ v, v ∈ T.leaves

/-- p. 3:14: the number of different neighbourhoods in `B` of subsets `S ⊆ A`
(`S = ∅` included); boolean-width of the cut `(A, B)` is the base-2 logarithm of this count. -/
def nbhdCount (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : ℕ :=
  #(A.powerset.image (fun S => B.filter (fun b => ∃ a ∈ S, G.Adj a b)))

/-- p. 3:14: `G` has a decomposition tree `T` in which, for every edge `e` of `T`, the cut
`P_e = (A_e, B_e)` has at most `N` different neighbourhoods. Here `A_e` is the leaf set of the
subtree below `e` and `B_e` the rest of `V`. "boolw(G) ≤ k" is `BoolWidthLE G (2 ^ k)`. -/
def BoolWidthLE (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) : Prop :=
  ∃ T : DTree V, IsDecompTree T ∧
    ∀ S ∈ T.properSubtrees, nbhdCount G S.leaves.toFinset (univ \ S.leaves.toFinset) ≤ N

end TwinWidthI.BoolWidth


