-- Prove2me | Definitions.Def_ClusterDecomp_Alg2Run
-- name    : ClusterDecomp_Alg2Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:08:17.52228+00:00
-- url     : https://prove2.me/theorems/faac1fa7-a012-473c-88eb-597b7528769e
-- title:
--   Algorithm 2 (ConstructPartition): the recursion tree, the contraction, and its runs
-- statement:
--   Given pairwise disjoint backbones $B_1,\dots,B_k$, set $h=\lceil\log_2k\rceil$ and $\alpha_a=1+1/h$. The root of a binary tree has $I_r=[k]$ and $X_r=V$. A node $u$ with $|I_u|\ge2$ splits $I_u=I_{u_L}\sqcup I_{u_R}$ with $\bigl||I_{u_L}|-|I_{u_R}|\bigr|\le1$; in $G[X_u]$ it contracts $\bigcup_{i\in I_{u_L}}B_i$ to $s$ and $\bigcup_{i\in I_{u_R}}B_i$ to $t$, computes an $\alpha_a$-fair $s,t$-cut $(S,T)$ and lets $X_{u_L},X_{u_R}$ be the vertex sets corresponding to $S,T$ after undoing the contraction. A leaf with $I_u=\{i\}$ sets $P_i=X_u$.
--
--   The tree extends backbones to a partition of $V$, and its depth at most $\lceil\log_2k\rceil$ is what bounds the loss in Lemma 3.7.
--
--   **Formalization Note** The contraction sums capacities between classes and drops edges inside a class, so fairness applies to the merged edge. `IsRun` leaves every split and every cut free, `IsAlg2Tree` adds the root and $\alpha_a$, and `Alg2Run` adds the outputs. `Tree.level` and `Tree.depth` are the levels and the depth, with the root at depth $0$.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), §3.2 and Algorithm 2, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_ClusterDecomp_WGraph
import Definitions.Def_ClusterDecomp_IsFairCut

open Finset

namespace ClusterDecomp

/-!
# Algorithm 2 (ConstructPartition) as a relation over its recursion tree

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), §3.2 and Algorithm 2, pp.14–15 (PDF pp.16–17).

**Formalization Note.**
* A run is a finite binary tree `T`. A leaf `leaf i X` is a node with `I_u = {i}`, `X_u = X`; a node `node X L R` has
  `X_u = X` and children `L`, `R`, and `I_u` is the set of labels of the leaves below it.
* The split of `I_u` and the fair cut are free in the relation: `Alg2Run` holds for every balanced split and every
  `α_a`-fair cut, so lemmas stated over it hold for all of them.
* `contract` merges classes: the capacity between the terminal `s` and a free vertex `y` is the whole of `w(B_L, y)`,
  so parallel edges are **summed**, and fairness applies to the merged edge; edges inside a class disappear. Edges of
  `G` leaving `X` are dropped, since the contraction happens in `G[X_u]`.
* The child `X_{u_L}` is `B_L` together with the free vertices on the source side, and `X_{u_R}` is the rest of `X_u`.
* `h = Nat.clog 2 k` is `⌈log₂ k⌉`, and `k ≥ 2` gives `h ≥ 1`, so `α_a = 1 + 1/h` has no division by zero.
-/

/-- A recursion tree of Algorithm 2 for `k` backbones on vertices `V`. -/
inductive Tree (k : ℕ) (V : Type*) where
  /-- A leaf `u` with `I_u = {i}`, `X_u = X`. -/
  | leaf (i : Fin k) (X : Finset V)
  /-- An internal node `u` with `X_u = X` and children `u_L`, `u_R`. -/
  | node (X : Finset V) (L R : Tree k V)

namespace Tree

variable {k : ℕ} {V : Type*} [DecidableEq V]

/-- The vertex set `X_u` of the root of the tree. -/
def X : Tree k V → Finset V
  | .leaf _ X => X
  | .node X _ _ => X

/-- The index set `I_u` of the root of the tree. -/
def I : Tree k V → Finset (Fin k)
  | .leaf i _ => {i}
  | .node _ L R => L.I ∪ R.I

/-- The sets returned on line 10: `P_i = X_u` for the leaf `u` labelled `i` (`∅` when `i` labels no leaf). -/
def part : Tree k V → Fin k → Finset V
  | .leaf i X => fun j => if j = i then X else ∅
  | .node _ L R => fun j => L.part j ∪ R.part j

/-- The vertex sets `X_u` of the nodes at depth `ℓ`, the root being at depth `0`. -/
def level : Tree k V → ℕ → List (Finset V)
  | t, 0 => [t.X]
  | .leaf _ _, _ + 1 => []
  | .node _ L R, ℓ + 1 => L.level ℓ ++ R.level ℓ

/-- The depth of the tree: `0` for a leaf. -/
def depth : Tree k V → ℕ
  | .leaf _ _ => 0
  | .node _ L R => max L.depth R.depth + 1

end Tree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices of `X` outside `BL ∪ BR`, which stay uncontracted. -/
abbrev freeVerts (X BL BR : Finset V) : Finset V := X \ (BL ∪ BR)

/-- Capacities of `G[X]` after contracting `BL` to `s = inr false` and `BR` to `t = inr true` (line 5). -/
def contract (G : WGraph V) (X BL BR : Finset V) :
    ↥(freeVerts X BL BR) ⊕ Bool → ↥(freeVerts X BL BR) ⊕ Bool → ℝ
  | .inl u, .inl v => G.w u v
  | .inr false, .inl v => G.cut BL {(v : V)}
  | .inl v, .inr false => G.cut {(v : V)} BL
  | .inr true, .inl v => G.cut BR {(v : V)}
  | .inl v, .inr true => G.cut {(v : V)} BR
  | .inr false, .inr true => G.cut BL BR
  | .inr true, .inr false => G.cut BR BL
  | .inr false, .inr false => 0
  | .inr true, .inr true => 0

/-- The union of the backbones with index in `I`. -/
def unionB {k : ℕ} (B : Fin k → Finset V) (I : Finset (Fin k)) : Finset V := I.biUnion B

/-- `t` is a run of lines 3–9 of Algorithm 2 on the backbones `B`, with fairness parameter `αa`: at every internal node,
the two index sets are disjoint and balanced, and the children's vertex sets come from an `αa`-fair `s,t`-cut of the
contraction, with the contraction undone (line 7). -/
def IsRun {k : ℕ} (G : WGraph V) (B : Fin k → Finset V) (αa : ℝ) : Tree k V → Prop
  | .leaf _ _ => True
  | .node X L R =>
      Disjoint L.I R.I ∧
      ((L.I.card : ℤ) - (R.I.card : ℤ)).natAbs ≤ 1 ∧
      (∃ S : Finset (↥(freeVerts X (unionB B L.I) (unionB B R.I)) ⊕ Bool),
        IsFairCut (contract G X (unionB B L.I) (unionB B R.I)) (Sum.inr false) (Sum.inr true) S αa ∧
        L.X = unionB B L.I ∪
          ((freeVerts X (unionB B L.I) (unionB B R.I)).attach.filter
            fun v => Sum.inl v ∈ S).map (Function.Embedding.subtype _) ∧
        R.X = X \ L.X) ∧
      IsRun G B αa L ∧ IsRun G B αa R

/-- `T` is a complete recursion tree of Algorithm 2 on the backbones `B`: its root has `I_r = [k]` and `X_r = V` (line 2)
and it is a run with `α_a = 1 + 1/⌈log₂ k⌉` (line 1). -/
def IsAlg2Tree {k : ℕ} (G : WGraph V) (B : Fin k → Finset V) (T : Tree k V) : Prop :=
  T.I = univ ∧ T.X = univ ∧ IsRun G B (1 + 1 / (Nat.clog 2 k : ℝ)) T

/-- `P` is a possible output of Algorithm 2 on the backbones `B` (line 12). -/
def Alg2Run {k : ℕ} (G : WGraph V) (B P : Fin k → Finset V) : Prop :=
  ∃ T : Tree k V, IsAlg2Tree G B T ∧ ∀ i, P i = T.part i

end ClusterDecomp


