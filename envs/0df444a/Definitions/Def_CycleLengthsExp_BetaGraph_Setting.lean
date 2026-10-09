-- Prove2me | Definitions.Def_CycleLengthsExp_BetaGraph_Setting
-- name    : CycleLengthsExp_BetaGraph_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:41.703718+00:00
-- url     : https://prove2.me/theorems/f641595f-1232-4739-acd9-cd3fa5d72f1f
-- title:
--   pp. 3, 16 — β-graph and the tree T_{k,t,p}
-- statement:
--   This file fixes the local objects of §4 of Friedman and Krivelevich, *Cycle lengths in expanding graphs*. All graphs are finite and simple. External neighborhood and cycle lengths come from the shared setting.
--
--   1. **β-graph** (Definition, p. 3). Let $G$ have $n$ vertices and let $\beta>0$. $G$ is a *β-graph* if every two disjoint vertex sets $A,B\subseteq V$ with $|A|,|B|\ge\beta n$ are joined by an edge of $G$.
--   2. **The tree $T_{k,t,p}$** (p. 16). A *complete $k$-ary tree of depth $t$* is a rooted tree whose internal vertices have $k$ children and whose leaves are at distance $t$ from the root; it has $1+k+\dots+k^t$ vertices and $k^t$ leaves. $T_{k,t,p}$ is obtained by joining the roots of two complete $k$-ary trees of depth $t$ by a path of length $p$, so it has $2(k^{t+1}-1)/(k-1)+p-1$ vertices (for $k\ge 2$).
--
--   The β-graph is the hypothesis of Theorem 3, and $T_{k,t,p}$ is the tree whose embedding produces cycles of prescribed lengths.
--
--   **Formalization Note** The β-graph condition compares the real number $\beta n$, $n$ the number of vertices, with the sizes `Set.ncard` of the two sets. On the empty vertex type no graph is a β-graph (take $A=B=\emptyset$). The vertices of the complete $k$-ary tree of depth $t$ are the words over the alphabet $\{0,\dots,k-1\}$ of length at most $t$ (a dependent pair of a length $d\le t$ and a vector of length $d$); the root is the empty word and the children of $w$ are the words $a\,w$. The vertices of $T_{k,t,p}$ are two tagged copies of these words together with $p-1$ internal path vertices; the path runs from the root of copy `false` through the internal vertices to the root of copy `true`, and for $p=1$ the two roots are adjacent. $T_{k,t,p}$ is a tree only for $p\ge 1$, as on the page ("positive integers $k$, $t$ and $p$").
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 3 (Definition of β-graph) and p. 16 (definition of T_{k,t,p} in the proof of Theorem 3)

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.BetaGraph

/-- β-graph (Definition, p. 3): every two disjoint vertex sets `A, B` with `|A|, |B| ≥ βn`
(`n = |V|`) are joined by an edge. -/
def IsBetaGraph {V : Type*} [Fintype V] (β : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ A B : Set V, Disjoint A B → β * Fintype.card V ≤ A.ncard → β * Fintype.card V ≤ B.ncard →
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

/-- Vertices of the complete `k`-ary tree of depth `t` (p. 16): words `(d, w)` of length
`d ≤ t` over the alphabet `Fin k`; the root is the empty word, the leaves are the words of
length `t`. -/
abbrev KaryVertex (k t : ℕ) : Type := Σ d : Fin (t + 1), List.Vector (Fin k) d

/-- `y` is a child of `x`: `y = a :: x` for a letter `a`. -/
def karyChild {k t : ℕ} (x y : KaryVertex k t) : Prop :=
  y.1.val = x.1.val + 1 ∧ ∃ a : Fin k, y.2.toList = a :: x.2.toList

instance {k t : ℕ} : DecidableRel (@karyChild k t) := fun x y => by
  unfold karyChild; infer_instance

/-- The root (the empty word) of the complete `k`-ary tree of depth `t`. -/
def karyRoot (k t : ℕ) : KaryVertex k t := ⟨0, List.Vector.nil⟩

/-- Vertices of `T_{k,t,p}`: two copies (`false`, `true`) of the complete `k`-ary tree of
depth `t`, and the `p - 1` internal vertices of the path joining their roots. -/
abbrev TVertex (k t p : ℕ) : Type := (Bool × KaryVertex k t) ⊕ Fin (p - 1)

/-- Position on the root-to-root path: the root of tree `false` is `0`, the internal path
vertex `i` is `i + 1`, the root of tree `true` is `p`; other vertices are off the path. -/
def pathIdx {k t p : ℕ} : TVertex k t p → Option ℕ
  | .inl (false, x) => if x.1.val = 0 then some 0 else none
  | .inl (true, x) => if x.1.val = 0 then some p else none
  | .inr i => some (i.val + 1)

/-- Tree edges of `T_{k,t,p}`: `y` is a child of `x` inside the same copy. -/
def treeRel {k t p : ℕ} : TVertex k t p → TVertex k t p → Prop
  | .inl (b, x), .inl (b', y) => b = b' ∧ karyChild x y
  | _, _ => False

instance {k t p : ℕ} : DecidableRel (@treeRel k t p) := fun x y => by
  rcases x with ⟨b, x⟩ | x <;> rcases y with ⟨b', y⟩ | y <;> simp only [treeRel] <;>
    infer_instance

/-- Path edges of `T_{k,t,p}`: consecutive positions on the root-to-root path. -/
def pathRel {k t p : ℕ} (x y : TVertex k t p) : Prop :=
  match pathIdx x, pathIdx y with
  | some i, some j => j = i + 1
  | _, _ => False

instance {k t p : ℕ} : DecidableRel (@pathRel k t p) := fun x y => by
  unfold pathRel; split <;> infer_instance

/-- The tree `T_{k,t,p}` (p. 16): the roots of two complete `k`-ary trees of depth `t`
joined by a path of length `p`. -/
def Tktp (k t p : ℕ) : SimpleGraph (TVertex k t p) := SimpleGraph.fromRel fun x y => treeRel x y ∨ pathRel x y

instance {k t p : ℕ} : DecidableRel (Tktp k t p).Adj := fun x y => by
  unfold Tktp; rw [SimpleGraph.fromRel_adj]; infer_instance

end CycleLengthsExp.BetaGraph


