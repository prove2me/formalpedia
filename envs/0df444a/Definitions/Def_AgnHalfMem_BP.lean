-- Prove2me | Definitions.Def_AgnHalfMem_BP
-- name    : AgnHalfMem_BP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:42.137264+00:00
-- url     : https://prove2.me/theorems/015b95e5-78cf-4a8b-b5ac-7ff36184dc3a
-- title:
--   Branching programs for learning (Definitions B.1, B.2)
-- statement:
--   A **branching program of length $T$ and width $W$** for learning over a feature space $X$ is a layered directed graph with layers $0,1,\dots,T$, each with at most $W$ vertices; layer $0$ consists of the single start vertex. Every vertex of layer $T$ is a leaf, and other vertices may be leaves too. A non-leaf vertex $v$ of layer $i$ has a transition function $\Gamma_v:X\times\{-1,1\}\to\{\text{vertices of layer } i+1\}$; the edge from $v$ to $u$ is labelled by $A_e=\Gamma_v^{-1}(u)$. A leaf $v$ is labelled by a classifier $\tilde h_v:X\to\{-1,1\}$.
--
--   **Computation path.** Samples $(x_1,y_1),\dots,(x_T,y_T)$ determine a path: start at the start vertex and at step $t$ follow the edge whose label contains $(x_t,y_t)$, until a leaf is reached. The program outputs the label $\tilde h_v$ of that leaf.
--
--   A streaming learner with $b$ bits of memory that reads at most $T$ samples is such a program of width $2^b$.
--
--   **Formalization Note** All layers share one finite state type $S$, so the width is $|S|$. The structure stores the start state, the transitions `step i v`, a leaf flag `isLeaf i v` and leaf labels `out i v`; a vertex of layer $i\ge T$ is always a leaf. The sample read at layer $i$ is the $(i+1)$-st, indexed $i$ in `Fin T`. `IsMeasurableBP` asks that every edge label and every leaf label be measurable.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), App. B, Definitions B.1 and B.2, p.28

import Mathlib

open MeasureTheory

namespace AgnHalfMem

/-- **Branching program for a learning problem (Definitions B.1 and B.2).** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), App. B, p.28, Definition B.1: "A branching program of length m and
width d, for learning, is a directed (multi) graph with vertices arranged in m+1 layers containing
at most d vertices each. In the first layer, that we think of as layer 0, there is only one vertex,
called the start vertex. A vertex of out degree 0 is called a leaf. All vertices in the last layer
are leaves (but there may be additional leaves). Each non-leaf vertex v is associated with a
transition function Γv : X × {−1, 1} → [d], which determines the next vertex based on the observed
sample (x, y) ∈ X × {−1, 1}. […] Each leaf v in the program is labeled by an element
h̃(v) : X → {−1, 1}, that we think of as the output of the program on that leaf."

A program of length `T` on the state type `S`: the start vertex `start` (layer 0), the transition
`step i v (x, y)` from vertex `v` of layer `i` to a vertex of layer `i + 1`, the leaf flag
`isLeaf i v`, and the leaf label `out i v : X → Bool`.

**Formalization Note.** Every layer `0, …, T` uses the same finite vertex set `S`, so the width is
`Fintype.card S` (vertices that the program never reaches are harmless). A vertex `(i, v)` is a
leaf if `isLeaf i v = true` or `i ≥ T` (every vertex of the last layer is a leaf); `step` and
`out` are consulted only at non-leaves resp. leaves. Labels are `Bool` (`true ↔ +1`). The edges
of the multigraph leaving `v` are represented by the transition function `Γ_v = step i v`; the
edge from `v` to `u` carries the label set `A_e = {z | step i v z = u}`. -/
structure BP (S X : Type*) (T : ℕ) where
  /-- the start vertex (layer 0) -/
  start : S
  /-- the transition `Γ_v` of vertex `v` in layer `i` -/
  step : ℕ → S → X × Bool → S
  /-- the leaf flag of vertex `v` in layer `i` (layer `T` is a leaf layer regardless) -/
  isLeaf : ℕ → S → Bool
  /-- the label `h̃(v) : X → {−1, 1}` of a leaf `v` in layer `i` -/
  out : ℕ → S → X → Bool

namespace BP

variable {S X : Type*} {T : ℕ}

/-- The vertex `v` of layer `i` is a leaf: it is flagged, or it lies in the last layer `T`
(or beyond). -/
def IsLeafAt (b : BP S X T) (i : ℕ) (v : S) : Prop := T ≤ i ∨ b.isLeaf i v = true

/-- **Computation path (Definition B.2, p.28)**: "The samples (x1, y1), …, (xm, ym) […] define a
computation-path in the branching program, by starting from the start vertex and following at step
t the edge labeled by the set containing (xt, yt), until reaching a leaf."
`stateAt b s i` is the vertex of the path at layer `i`; once a leaf is reached the path stays
there. The sample read at layer `i < T` is `s ⟨i, _⟩` (0-based; the paper's `(x_{i+1}, y_{i+1})`). -/
def stateAt (b : BP S X T) (s : Fin T → X × Bool) : ℕ → S
  | 0 => b.start
  | i + 1 =>
    if h : i < T ∧ b.isLeaf i (stateAt b s i) = false then
      b.step i (stateAt b s i) (s ⟨i, h.1⟩)
    else stateAt b s i

open Classical in
/-- The layer at which the computation path reaches a leaf (at most `T`). -/
noncomputable def exitLayer (b : BP S X T) (s : Fin T → X × Bool) : ℕ :=
  Nat.find (⟨T, Or.inl le_rfl⟩ : ∃ i, b.IsLeafAt i (stateAt b s i))

/-- "The program outputs the label h̃_v of the leaf v reached by the computation-path"
(Definition B.2, p.28). -/
noncomputable def output (b : BP S X T) (s : Fin T → X × Bool) : X → Bool :=
  b.out (exitLayer b s) (stateAt b s (exitLayer b s))

/-- Measurability of a deterministic program: every edge label set `A_e = {z | step i v z = u}`
is measurable and every leaf label is a measurable classifier. ("Pr" over the samples presupposes
measurable events.) -/
def IsMeasurableBP [MeasurableSpace X] (b : BP S X T) : Prop :=
  (∀ i v u, MeasurableSet {z : X × Bool | b.step i v z = u}) ∧ (∀ i v, Measurable (b.out i v))

end BP

end AgnHalfMem


