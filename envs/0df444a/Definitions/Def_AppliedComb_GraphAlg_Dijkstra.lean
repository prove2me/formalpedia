-- Prove2me | Definitions.Def_AppliedComb_GraphAlg_Dijkstra
-- name    : AppliedComb_GraphAlg_Dijkstra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:32:34.584214+00:00
-- url     : https://prove2.me/theorems/22f15f00-4a69-4fb5-9b21-e2d11b42f3b5
-- title:
--   Weighted digraphs, shortest paths and Dijkstra's algorithm (Sections 12.2–12.3, Algorithm 12.14)
-- statement:
--   A **digraph** $G = (V, E)$ has a finite vertex set $V$ and a set $E \subseteq V \times V$ of **directed edges** with $x \ne y$ for every $(x, y) \in E$. Each directed edge has a **length** $w(x, y) \in \mathbb{N}_0$. The length function is extended by $w(x, y) = \infty$ when $(x, y)$ is not a directed edge; values are then taken in $\mathbb{N}_0 \cup \{\infty\}$ with $a + \infty = \infty$.
--
--   A **directed path** from $a$ to $b$ is a sequence $P = (a = u_0, u_1, \dots, u_t = b)$ of distinct vertices with $(u_i, u_{i+1}) \in E$ for $i = 0, \dots, t-1$; its **length** is $\sum_{i=0}^{t-1} w(u_i, u_{i+1})$. The **distance** from $a$ to $b$ is the minimum length of a directed path from $a$ to $b$ (and $\infty$ when there is none). A **shortest path** from $a$ to $b$ is a directed path from $a$ to $b$ of minimum length.
--
--   **Dijkstra's algorithm** with root $r$, where $n = |V|$, maintains a sequence $\sigma$ of distinct **permanent** vertices (the others are **temporary**), a value $\delta(x)$ and a sequence $P(x)$ for every vertex $x$.
--
--   1. *Step 1 (initialization).* $\delta(r) = 0$, $P(r) = (r)$, $\sigma = (r)$; for $x \ne r$, $\delta(x) = w(r, x)$ and $P(x) = (r, x)$. Then a temporary vertex $x$ with $\delta(x)$ minimum is chosen, $v_2 = x$ is appended to $\sigma$, and the step counter becomes $2$.
--   2. *Step $i$, $1 < i < n$.* Let $v_i$ be the last entry of $\sigma$. For every temporary $x$,
--   $$\delta(x) \leftarrow \min\{\delta(x),\ \delta(v_i) + w(v_i, x)\},$$
--   and if this strictly reduces $\delta(x)$, then $P(x)$ becomes $P(v_i)$ followed by $x$. Then a temporary vertex $x$ with $\delta(x)$ minimum is chosen, $v_{i+1} = x$ is appended to $\sigma$, and the step counter is incremented.
--   3. At Step $n$ the algorithm halts, with $\sigma = (v_1, \dots, v_n)$.
--
--   The choice of a temporary vertex of minimum $\delta$ is arbitrary among ties: $\mathrm{DijkstraRun}(G, r, i, s)$ holds when $s$ is the state at the start of Step $i$ for **some** sequence of admissible choices, and the halted states are those with $i = n$.
--
--   **Formalization Note.** `WeightedDigraph V` bundles the edge relation `Adj`, its looplessness and a length `w : V → V → ℕ` whose values off the edges are ignored; `ext` is the extension by `⊤ : ℕ∞`. Paths are `List V` (head $a$, last $b$, `Nodup`, consecutive entries adjacent), and `dist` is the infimum in `ℕ∞` of the lengths of directed paths, which is `⊤` when there is none. The algorithm's state is `DijkstraState` (`σ`, `δ : V → ℕ∞`, `P : V → List V`), and `DijkstraRun` is an inductive relation whose three constructors are Step 1, the choice ending Step 1, and Step $i$ for $1 < i < n$. When $n = 1$ no temporary vertex exists and the initial state is the halted state.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 245–247, Section 12.2 (digraph, directed path) and Section 12.3 (length, distance, Algorithm 12.14)

import Mathlib

namespace AppliedComb.GraphAlg

/-- Keller–Trotter, p. 245. A digraph `G = (V, E)` with `E ⊆ V × V` and `x ≠ y` for every
`(x, y) ∈ E`, together with a length `w(x, y) ∈ ℕ₀` of each directed edge `(x, y)`. `Adj x y`
means `(x, y) ∈ E`; the length is a function `V → V → ℕ` whose values off `E` are never used
(they are replaced by `∞` in `ext`). -/
structure WeightedDigraph (V : Type*) where
  /-- `Adj x y` means that `(x, y)` is a directed edge. -/
  Adj : V → V → Prop
  /-- `x ≠ y` for every directed edge `(x, y)`. -/
  loopless : ∀ x, ¬ Adj x x
  /-- The length `w(x, y)` of the directed edge `(x, y)`. -/
  w : V → V → ℕ

namespace WeightedDigraph

variable {V : Type*}

open Classical in
/-- Keller–Trotter, p. 246. The length function extended by `w(x, y) = ∞` when `(x, y)` is not
a directed edge, with values in `ℕ∞ = ℕ ∪ {∞}`. -/
noncomputable def ext (G : WeightedDigraph V) (x y : V) : ℕ∞ :=
  if G.Adj x y then (G.w x y : ℕ∞) else ⊤

/-- Keller–Trotter, p. 245. A *directed path* from `a` to `b`: a sequence
`P = (a = u₀, u₁, …, u_t = b)` of distinct vertices such that `(uᵢ, uᵢ₊₁)` is a directed edge
for every `i = 0, 1, …, t - 1`. The sequence is the list `P`. -/
def IsDirPath (G : WeightedDigraph V) (a b : V) (P : List V) : Prop :=
  P.head? = some a ∧ P.getLast? = some b ∧ P.Nodup ∧ P.IsChain G.Adj

/-- Keller–Trotter, p. 245. The *length* of a directed path `(u₀, u₁, …, u_t)`, the sum
`∑_{i=0}^{t-1} w(uᵢ, uᵢ₊₁)` of the lengths of its edges. -/
def pathLength (G : WeightedDigraph V) (P : List V) : ℕ :=
  (List.zipWith G.w P P.tail).sum

/-- Keller–Trotter, pp. 245–246. The *distance* from `a` to `b`: the minimum length of a
directed path from `a` to `b`, as an element of `ℕ∞`. When there is no directed path from `a`
to `b` the infimum is over the empty set and the distance is `∞`. -/
noncomputable def dist (G : WeightedDigraph V) (a b : V) : ℕ∞ :=
  ⨅ (P : List V) (_ : G.IsDirPath a b P), ((G.pathLength P : ℕ) : ℕ∞)

/-- Keller–Trotter, p. 246 (Problem 12.13). A *shortest path* from `a` to `b` is a directed path
from `a` to `b` whose length is at most that of every directed path from `a` to `b`. -/
def IsShortestPath (G : WeightedDigraph V) (a b : V) (P : List V) : Prop :=
  G.IsDirPath a b P ∧ ∀ Q : List V, G.IsDirPath a b Q → G.pathLength P ≤ G.pathLength Q

end WeightedDigraph

/-- Keller–Trotter, pp. 246–247 (Algorithm 12.14). The data Dijkstra's algorithm has determined
at a given step: the sequence `σ = (v₁, …, vᵢ)` of permanent vertices, a number `δ(x) ∈ ℕ∞` and a
sequence `P(x)` for every vertex `x`. -/
structure DijkstraState (V : Type*) where
  /-- The sequence `σ` of permanent vertices, in the order they became permanent. -/
  σ : List V
  /-- The current value `δ(x)`. -/
  δ : V → ℕ∞
  /-- The current path `P(x)`. -/
  P : V → List V

namespace DijkstraState

variable {V : Type*}

open Classical in
/-- Keller–Trotter, p. 247, Initialization (Step 1), before the choice of `v₂`: `δ(r) = 0`,
`P(r) = (r)`, `σ = (r)`, and for each `x ≠ r`, `δ(x) = w(r, x)` (extended by `∞`) and
`P(x) = (r, x)`. -/
noncomputable def init (G : WeightedDigraph V) (r : V) : DijkstraState V where
  σ := [r]
  δ := fun x => if x = r then 0 else G.ext r x
  P := fun x => if x = r then [r] else [r, x]

/-- A vertex is *temporary* when it is not permanent (not in `σ`); `IsMinTemp s x` says that `x`
is a temporary vertex for which `δ(x)` is minimum among the temporary vertices. Ties are not
broken: every such `x` is an admissible choice. -/
def IsMinTemp (s : DijkstraState V) (x : V) : Prop :=
  x ∉ s.σ ∧ ∀ y : V, y ∉ s.σ → s.δ x ≤ s.δ y

/-- Append `x` to the end of `σ` (making `x` permanent); `δ` and `P` are unchanged. -/
def makePermanent (s : DijkstraState V) (x : V) : DijkstraState V where
  σ := s.σ ++ [x]
  δ := s.δ
  P := s.P

open Classical in
/-- Keller–Trotter, p. 247, Inductive Step, scan from `v = vᵢ`: for each temporary `x`, set
`δ(x) = min{δ(x), δ(vᵢ) + w(vᵢ, x)}`; if this assignment reduces `δ(x)`, let `P(x)` be the path
obtained by adding `x` to the end of `P(vᵢ)`. Permanent vertices are unchanged. -/
noncomputable def scan (G : WeightedDigraph V) (s : DijkstraState V) (v : V) :
    DijkstraState V where
  σ := s.σ
  δ := fun x => if x ∉ s.σ then min (s.δ x) (s.δ v + G.ext v x) else s.δ x
  P := fun x => if x ∉ s.σ ∧ s.δ v + G.ext v x < s.δ x then s.P v ++ [x] else s.P x

end DijkstraState

open DijkstraState in
/-- Keller–Trotter, pp. 246–247 (Algorithm 12.14, Dijkstra's algorithm with root `r`), with
`n = |V|`. `DijkstraRun G r i s` says that `s` is a possible state of the algorithm at the start
of Step `i` (so `σ` has `i` entries):
* `init`: at Step 1 the state is the initialization `init G r`;
* `first`: Step 1 ends by choosing a temporary vertex `x` with `δ(x)` minimum, setting `v₂ = x`,
  appending it to `σ`, and incrementing `i`;
* `step`: at Step `i` with `1 < i < n`, scan from `vᵢ` (the last entry of `σ`), then choose a
  temporary vertex `x` with `δ(x)` minimum, append it to `σ` as `vᵢ₊₁`, and increment `i`.
Every admissible choice among tied vertices gives a run. The algorithm halts at Step `n`, where
`σ = (v₁, …, vₙ)` contains every vertex; the halted states are those with `DijkstraRun G r n s`. -/
inductive DijkstraRun {V : Type*} [Fintype V] (G : WeightedDigraph V) (r : V) :
    ℕ → DijkstraState V → Prop
  | init : DijkstraRun G r 1 (init G r)
  | first {x : V} (hx : (init G r).IsMinTemp x) :
      DijkstraRun G r 2 ((init G r).makePermanent x)
  | step {i : ℕ} {s : DijkstraState V} {v x : V} (hrun : DijkstraRun G r i s) (hi : 1 < i)
      (hin : i < Fintype.card V) (hv : s.σ.getLast? = some v)
      (hx : (scan G s v).IsMinTemp x) :
      DijkstraRun G r (i + 1) ((scan G s v).makePermanent x)

end AppliedComb.GraphAlg


