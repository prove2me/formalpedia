-- Prove2me | Definitions.Def_LocalSweepFT_SpaceTimeGraph
-- name    : LocalSweepFT_SpaceTimeGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:38:25.868929+00:00
-- url     : https://prove2.me/theorems/01332dba-55fd-4430-9eba-8c5495dcbefd
-- title:
--   Space–time graphs, histories, slices, the graph of a slice, and predecessors
-- statement:
--   A **space–time graph** $(G,T)$ has arrows $A$ and forks $F$ on a vertex set $V$ and a time $T:V\to\mathbb N$: the ends of an arrow differ in time by one, and two distinct vertices are joined by a fork iff they are both joined by arrows to a common vertex one step later. $\mathrm{pre}(v)$ is the set of arrow-neighbours one step earlier. The **history** $H_u$ is the set of vertices of time $\le T(u)$ joined to $u$ by a path of arrows, and the **slice** of $u$ is the set of vertices with the same history. The **graph $G_K$** of the slice $K$ has as vertices the slices $R\subseteq H_K$ with $T(R)=T(K)-1$, two of them adjacent iff a fork joins them.
--
--   With vertices placed in $\mathbb R^d$, $L_1,\dots,L_{d+1}$ are the potential walls, the size of a fork $\{a,b\}$ is $\sum_i\max(L_i(a),L_i(b))$, and $\mathrm{pre}_i(u)$ is a maximizer of $L_i$ over $\mathrm{pre}(u)$.
--
--   These are the objects of the Toom-contour analysis of Berman–Simon and Gács used in §5.3.
--
--   **Formalization Note** Forks join distinct vertices. The arrow path of a history stays among vertices of time $\le T(u)$, the reading under which the proofs of Claims 5.22 and 5.24 go through.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Definitions 5.19, 5.21, 5.23, 5.25, pp.47–49

import Mathlib

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…): space–time graphs (Def 5.19, p.47), histories and slices
(Def 5.21, p.48), the graph of a slice (Def 5.23, p.48), and pole selections, sizes and
predecessors (Def 5.25, p.49). -/

/-- A space–time graph `(G, T)` with `G = (V, A, F)` (Def 5.19, p.47): undirected arrows `A` and
forks `F` on `V`, and a time coordinate `T : V → ℕ`, such that
1. the ends of an arrow differ in time by one;
2. two distinct vertices `x, y` are joined by a fork iff some `z` is joined to both by arrows and
   `T(x) = T(y) = T(z) − 1`.

**Formalization Note.** Forks join distinct vertices (`SimpleGraph` has no loops). -/
structure SpaceTimeGraph (V : Type) where
  A : SimpleGraph V
  F : SimpleGraph V
  T : V → ℕ
  arrow_time : ∀ x y, A.Adj x y → T y = T x + 1 ∨ T x = T y + 1
  fork_iff : ∀ x y, F.Adj x y ↔
    x ≠ y ∧ ∃ z, A.Adj x z ∧ A.Adj y z ∧ T x + 1 = T z ∧ T y + 1 = T z

namespace SpaceTimeGraph

variable {V : Type} (G : SpaceTimeGraph V)

/-- `pre(v) := {u : {u, v} ∈ A, T(v) = T(u) + 1}` (Def 5.19, p.47). -/
def pre (v : V) : Set V := {u | G.A.Adj u v ∧ G.T v = G.T u + 1}

/-- The history `H_u` of `u` (Def 5.21, p.48): the vertices `x` with `T(x) ≤ T(u)` joined to `u` by a
path of arrows.

**Formalization Note.** The path is taken inside the vertices of time `≤ T(u)` (the reading under
which the proofs of Claims 5.22 and 5.24 go through). -/
def hist (u : V) : Set V :=
  {x | ∃ hx : G.T x ≤ G.T u,
    (G.A.induce {y | G.T y ≤ G.T u}).Reachable ⟨x, hx⟩ ⟨u, le_refl (G.T u)⟩}

/-- The slice of `u` (Def 5.21, p.48): the maximal set of vertices sharing the history of `u`,
i.e. the class of `u` under `v ∼ v′ ⟺ H_v = H_{v′}`. Its history `H_K` is `hist u` and its time
`T(K)` is `T u`. -/
def slice (u : V) : Set V := {v | G.hist v = G.hist u}

/-- `K` is a slice (Def 5.21). -/
def IsSlice (K : Set V) : Prop := ∃ u, K = G.slice u

/-- The vertices of the graph `G_K` of the slice `K` of `u` (Def 5.23, p.48): the slices
`R ⊆ H_K` with `T(R) = T(K) − 1`. -/
def SliceGraphVert (u : V) : Type :=
  {K : Set V // G.IsSlice K ∧ K ⊆ G.hist u ∧ ∀ r ∈ K, G.T r + 1 = G.T u}

/-- The graph `G_K` of the slice `K` of `u` (Def 5.23, p.48): two distinct slices `S, R` are
adjacent iff some fork `{s, r}` has `s ∈ S` and `r ∈ R`. -/
def sliceGraph (u : V) : SimpleGraph (G.SliceGraphVert u) :=
  SimpleGraph.fromRel (fun S R => ∃ s ∈ S.1, ∃ r ∈ R.1, G.F.Adj s r)

end SpaceTimeGraph

variable {d : ℕ}

/-- The potential walls on `ℝ^d` (Def 4.17, p.23): `L_i(x) = x_i` for `i ≤ d` and
`L_{d+1}(x) = −Σ_i x_i`; `potR (Fin.last d)` is `L_{d+1}`. -/
noncomputable def potR (i : Fin (d + 1)) (x : Fin d → ℝ) : ℝ :=
  if h : (i : ℕ) < d then x ⟨i, h⟩ else -∑ j, x j

/-- The size of a fork `{a, b}` (Def 5.25, p.49): `Σ_{i=1}^{d+1} max(L_i(a), L_i(b))`. -/
noncomputable def forkSize {V : Type} (pos : V → (Fin d → ℝ)) (a b : V) : ℝ :=
  ∑ i : Fin (d + 1), max (potR i (pos a)) (potR i (pos b))

/-- `preSel u i` is an `i`-th predecessor `pre_i(u) = argmax_{v ∈ pre(u)} L_i(v)` of `u`
(Def 5.25, p.49), for every `u` with a predecessor. -/
def IsPreSelection {V : Type} (G : SpaceTimeGraph V) (pos : V → (Fin d → ℝ))
    (preSel : V → Fin (d + 1) → V) : Prop :=
  ∀ u i, (G.pre u).Nonempty →
    preSel u i ∈ G.pre u ∧ ∀ w ∈ G.pre u, potR i (pos w) ≤ potR i (pos (preSel u i))

end LocalSweepFT


