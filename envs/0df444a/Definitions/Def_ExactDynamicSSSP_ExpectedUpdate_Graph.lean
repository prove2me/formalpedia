-- Prove2me | Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Graph
-- name    : ExactDynamicSSSP_ExpectedUpdate_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:22:26.552852+00:00
-- url     : https://prove2.me/theorems/38ca7664-40ab-42eb-a4ee-2af8adbcc435
-- title:
--   §§3.1, 6.1 — weighted digraphs, walks, exact distances, shortest-path trees and subtree counts
-- statement:
--   This file fixes the deterministic graph objects of §3.1 and §6.1.
--
--   **Graphs.** A graph is a directed graph on the vertex set $\{0,\dots,n-1\}$ without loops. Each present arc $x\to y$ carries a finite nonnegative real weight $w(x,y)$; a missing arc is absent (it is not an arc with a sentinel weight). $D^+_x$ and $D^-_x$ are the out- and in-degree, $m=|E|$ the number of arcs, and $N^-(y)$ the in-neighbours.
--
--   **Walks and distances.** A walk from $a$ to $b$ is a vertex sequence $(a=x_0,\dots,x_k=b)$ whose consecutive pairs are arcs; its weight is $\sum_i w(x_{i-1},x_i)$ and its hop count is $k$. The exact distance
--   $$d(a,b)=\inf\{w(P): P\text{ a walk from }a\text{ to }b\}\in[0,+\infty]$$
--   is $+\infty$ exactly when $b$ is unreachable from $a$. The unweighted distance is the least hop count of a walk when $b$ is reachable and $0$ otherwise. For an updated arc $u\to v$, $d^t(e'_x)$ is the least weight of a simple path from $s$ to $x$ that traverses $u\to v$.
--
--   **Updates.** A distance-decreasing update inserts an absent arc or strictly lowers the weight of a present one; a distance-increasing update deletes a present arc or strictly raises its weight; all other arcs are unchanged.
--
--   **Shortest-path trees.** A parent function $\mathrm{par}$ is a shortest-path tree rooted at $s$ when $s$ has a null parent, a vertex has a null parent iff it is $s$ or unreachable, the parent $y$ of $x$ is the tail of a present arc with $d_x=d_y+w(y,x)$, and the parent chain of every reachable vertex reaches $s$ (so the tree is acyclic even with zero-weight arcs and contains exactly the reachable vertices). $V(SPT_v)$ is empty for an unreachable root and otherwise is the set of vertices whose chain passes through $v$ (including an isolated source), and the depth of $x$ is the number of arcs of its chain to $s$ ($0$ for $s$ and for unreachable vertices). For a tree arc $e=(u,v)$,
--   $$q(e)=|V(SPT_v)|,\qquad f^\pm(e)=\sum_{x\in V(SPT_v)}D^\pm_x,$$
--   and all three are $0$ for a non-tree arc (eq. (4), Definition 6.1).
--
--   **Formalization Note** Distances are in $[0,\infty]$ (`ℝ≥0∞`), so the unreachable value $+\infty$ is represented directly; the infimum over the empty set of walks is $\top$.
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), §3.1, PDF p.3 = printed p.3 (notation, eq. (1)–(2), unreachable convention); §6.1, PDF p.8 = printed p.8 (eq. (4), Definition 6.1)

import Mathlib

open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-! # Weighted digraphs, walks, shortest distances and shortest-path trees

Liang–Chen–Zhang, *Exact Fully Dynamic Single-Source Shortest Paths in Nonnegative
Weighted Graphs*, STOC 2027 submission #223, §3.1 (PDF p. 3 = printed p. 3), §6 (pp. 7–9).

Vertices are `Fin n`. A present arc `(x, y)` carries a finite nonnegative real weight; a
missing arc is `none` (it is *absent*, not an arc with a sentinel weight). There are no
loops. Distances live in `[0, +∞]`: the distance is the infimum of the weights of all walks,
which is `⊤` exactly when no walk exists. -/

/-- A finite directed graph on `Fin n` with nonnegative real arc weights and no loops.
`wt x y = some w` means the arc `x → y` is present with weight `w`. -/
structure WDigraph (n : ℕ) where
  /-- Arc weights; `none` means the arc is absent. -/
  wt : Fin n → Fin n → Option ℝ≥0
  /-- No self-loops. -/
  loopless : ∀ v, wt v v = none

namespace WDigraph

variable {n : ℕ} (G : WDigraph n)

/-- Arc presence. -/
def Adj (x y : Fin n) : Prop := (G.wt x y).isSome

instance (x y : Fin n) : Decidable (G.Adj x y) := by unfold Adj; infer_instance

/-- The set of present arcs. -/
def arcs : Finset (Fin n × Fin n) := Finset.univ.filter fun e => G.Adj e.1 e.2

/-- The number of arcs `m = |E|`. -/
def numArcs : ℕ := G.arcs.card

/-- Out-degree `D⁺_x`. -/
def outDeg (x : Fin n) : ℕ := (Finset.univ.filter fun y => G.Adj x y).card

/-- In-degree `D⁻_x`. -/
def inDeg (x : Fin n) : ℕ := (Finset.univ.filter fun y => G.Adj y x).card

/-- The out-neighbours of `x`, as the adjacency list scanned by the algorithm. -/
def outList (x : Fin n) : List (Fin n) := (List.finRange n).filter fun y => decide (G.Adj x y)

/-- The in-neighbours of `y` (tails of the records of the incoming list `C_y`). -/
def inList (y : Fin n) : List (Fin n) := (List.finRange n).filter fun x => decide (G.Adj x y)

/-- Arc weight in `[0, ∞]`, with `⊤` for an absent arc (`d(e_{x→y}) = d_x + w(x,y)` is then `⊤`). -/
def ewt (x y : Fin n) : ℝ≥0∞ :=
  match G.wt x y with
  | some w => (w : ℝ≥0∞)
  | none => ⊤

/-- A walk is a nonempty vertex list `[x₀, …, x_k]` whose consecutive pairs are arcs. -/
def IsWalk (l : List (Fin n)) : Prop := l ≠ [] ∧ l.IsChain fun x y => G.Adj x y

/-- `l` is a walk from `a` to `b`. -/
def IsWalkFrom (a b : Fin n) (l : List (Fin n)) : Prop :=
  G.IsWalk l ∧ l.head? = some a ∧ l.getLast? = some b

/-- Total weight `w(P)` of a vertex list: the sum of the weights of its consecutive arcs. -/
def walkWeight : List (Fin n) → ℝ≥0∞
  | x :: y :: l => G.ewt x y + walkWeight (y :: l)
  | _ => 0

/-- Number of arcs of a walk (its hop count). -/
def hops (l : List (Fin n)) : ℕ := l.length - 1

/-- Directed reachability: some walk from `a` to `b` exists (every vertex reaches itself). -/
def Reach (a b : Fin n) : Prop := ∃ l, G.IsWalkFrom a b l

/-- The exact shortest-path distance `d(a, b) ∈ [0, +∞]`: the infimum of the weights of all
walks from `a` to `b`; it is `+∞` when `b` is unreachable from `a` (infimum over the empty
set). -/
noncomputable def dist (a b : Fin n) : ℝ≥0∞ :=
  ⨅ (l : List (Fin n)) (_ : G.IsWalkFrom a b l), G.walkWeight l

open Classical in
/-- Unweighted directed distance: the least number of arcs of a walk from `a` to `b` when `b`
is reachable, and `0` when it is unreachable (the source's zero extension, used only in sums). -/
noncomputable def udist (a b : Fin n) : ℕ :=
  if G.Reach a b then sInf {k | ∃ l, G.IsWalkFrom a b l ∧ hops l = k} else 0

/-- The graph obtained by setting the arc `u → v` to `o` (`none` deletes it); loops are never
created. -/
def setArc (u v : Fin n) (o : Option ℝ≥0) : WDigraph n where
  wt x y := if x = u ∧ y = v ∧ u ≠ v then o else G.wt x y
  loopless x := by
    by_cases h : x = u ∧ x = v ∧ u ≠ v
    · exact absurd (h.1.symm.trans h.2.1) h.2.2
    · simp only [h, if_false]; exact G.loopless x

/-- The minimum candidate distance to `x` *through the updated arc* `u → v`
(`d^t(e'_x)` of Lemma 4.2, PDF p. 5): the infimum of the weights of the simple paths from `s` to `x`
that traverse the arc `u → v`. Requiring `Nodup` preserves the source's updated-edge path
convention even when a walk through the arc could only revisit a vertex. -/
noncomputable def viaDist (s u v x : Fin n) : ℝ≥0∞ :=
  ⨅ (l : List (Fin n)) (_ : G.IsWalkFrom s x l ∧ l.Nodup ∧ [u, v] <:+: l), G.walkWeight l

end WDigraph

/-! ## Distance-decreasing and distance-increasing single-arc updates (§3.1, p. 2) -/

/-- `G'` arises from `G` by a **distance-decreasing update** of the arc `u → v`: an insertion
of an absent arc or a strict decrease of its weight; every other arc is unchanged. -/
def IsDecreasingUpdate {n : ℕ} (G G' : WDigraph n) (u v : Fin n) : Prop :=
  u ≠ v ∧ (∀ x y, ¬ (x = u ∧ y = v) → G'.wt x y = G.wt x y) ∧
    ∃ w' : ℝ≥0, G'.wt u v = some w' ∧ (G.wt u v = none ∨ ∃ w, G.wt u v = some w ∧ w' < w)

/-- `G'` arises from `G` by a **distance-increasing update** of the present arc `u → v`: its
deletion or a strict increase of its weight; every other arc is unchanged. -/
def IsIncreasingUpdate {n : ℕ} (G G' : WDigraph n) (u v : Fin n) : Prop :=
  u ≠ v ∧ (∀ x y, ¬ (x = u ∧ y = v) → G'.wt x y = G.wt x y) ∧
    ∃ w : ℝ≥0, G.wt u v = some w ∧ (G'.wt u v = none ∨ ∃ w', G'.wt u v = some w' ∧ w < w')

/-! ## Parent functions, shortest-path trees and subtrees (§3.1, §6.1) -/

/-- The `k`-th ancestor of `x` under a parent function (`anc par x 0 = some x`). -/
def anc {n : ℕ} (par : Fin n → Option (Fin n)) (x : Fin n) : ℕ → Option (Fin n)
  | 0 => some x
  | k + 1 => (anc par x k).bind par

/-- `par` is a **shortest-path tree** of `G` rooted at `s` (§3.1, p. 3): the source has a null
parent; a vertex has a null parent iff it is the source or unreachable; the parent `y` of `x`
is the tail of a present arc `y → x` with `d_x = d_y + w(y, x)`; and every reachable vertex's
parent chain reaches `s` (so the chains are acyclic and realize the distances, also with
zero-weight arcs). The tree contains exactly the reachable vertices. -/
structure IsSPT {n : ℕ} (G : WDigraph n) (s : Fin n) (par : Fin n → Option (Fin n)) : Prop where
  src_none : par s = none
  none_iff : ∀ x, par x = none ↔ (x = s ∨ G.dist s x = ⊤)
  tight : ∀ x y, par x = some y → ∃ w, G.wt y x = some w ∧ G.dist s x = G.dist s y + w
  reaches_src : ∀ x, G.dist s x ≠ ⊤ → ∃ k, anc par x k = some s

/-- The vertex set `V(SPT_v)` of the subtree rooted at `v`: the vertices whose parent chain
passes through `v` (including `v` itself). An unreachable root contributes the empty
subtree (Appendix A.1, PDF p. 14). The source is retained even when it has no children. -/
noncomputable def subtree {n : ℕ} (s : Fin n) (par : Fin n → Option (Fin n)) (v : Fin n) : Finset (Fin n) :=
  by
    classical
    exact if v = s ∨ (par v).isSome then
      Finset.univ.filter fun x => ∃ k, anc par x k = some v
    else ∅

/-- Depth of `x` in the tree: the number of arcs of its parent chain to `s`; `0` for `s` and
for a vertex whose chain does not reach `s` (an unreachable vertex). This is the hop count
`H_x` of the certified shortest path (§6.1, p. 8), with `H_s = 0` and `H_x = 0` when `x` is
unreachable. -/
noncomputable def treeDepth {n : ℕ} (par : Fin n → Option (Fin n)) (s x : Fin n) : ℕ :=
  sInf {k | anc par x k = some s}

/-- `q(e) = |V(SPT_v)|` for a tree arc `e = (u, v)` (i.e. `par v = some u`), and `0` for a
non-tree arc (eq. (4), PDF p. 8). -/
noncomputable def subtreeSize {n : ℕ} (s : Fin n) (par : Fin n → Option (Fin n)) (e : Fin n × Fin n) : ℕ :=
  if par e.2 = some e.1 then (subtree s par e.2).card else 0

/-- `f⁺(e) = Σ_{x ∈ V(SPT_v)} D⁺_x` for a tree arc `e = (u, v)`, `0` otherwise (eq. (4),
Definition 6.1). -/
noncomputable def subtreeOut {n : ℕ} (G : WDigraph n) (s : Fin n) (par : Fin n → Option (Fin n))
    (e : Fin n × Fin n) : ℕ :=
  if par e.2 = some e.1 then ∑ x ∈ subtree s par e.2, G.outDeg x else 0

/-- `f⁻(e) = Σ_{x ∈ V(SPT_v)} D⁻_x` for a tree arc `e = (u, v)`, `0` otherwise (eq. (4),
Definition 6.1). An internal arc contributes to both `f⁺` and `f⁻`. -/
noncomputable def subtreeIn {n : ℕ} (G : WDigraph n) (s : Fin n) (par : Fin n → Option (Fin n))
    (e : Fin n × Fin n) : ℕ :=
  if par e.2 = some e.1 then ∑ x ∈ subtree s par e.2, G.inDeg x else 0

end ExactDynamicSSSP.ExpectedUpdate


