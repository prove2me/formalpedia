-- Prove2me | Definitions.Def_SmoothedMIS_IsMIS
-- name    : SmoothedMIS_IsMIS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:39.836602+00:00
-- url     : https://prove2.me/theorems/47ab7dde-b05b-4ce9-8dff-1304d43b7d47
-- title:
--   Maximal independent set, closed and two-hop neighbourhoods
-- statement:
--   Let $H$ be a simple graph on a vertex set $V$. For a vertex $v$, $\deg_H(v)$ is the number of neighbours of $v$; for a set $T\subseteq V$ the **closed neighbourhood** is $N_H[T]=\bigcup_{v\in T}N_H[v]$, where $N_H[v]=N_H(v)\cup\{v\}$, and the **two-hop neighbourhood** is
--   $$
--   N^2_H[T]=\{v\in V:\ \mathrm{dist}_H(v,T)\le 2\},\qquad \mathrm{dist}_H(v,T)=\min_{y\in T}\mathrm{dist}_H(v,y),
--   $$
--   with $\mathrm{dist}_H=\infty$ between different components.
--
--   A set $I\subseteq V$ is a **maximal independent set (MIS)** of $H$ if no two vertices of $I$ are adjacent in $H$ and every vertex of $V$ lies in $N_H[I]$.
--
--   These notions are used by every statement of the mission.
--
--   **Formalization Note** Degrees are counted with `Set.ncard` (all graphs of the mission are finite). Distances are `SimpleGraph.edist` in $\mathbb N\cup\{\infty\}$.
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), §2 Preliminaries and Notation, pp.9–10 (PDF pp.11–12)

import Mathlib

namespace SmoothedMIS

/-- The degree `deg_H(v)`: the number of neighbours of `v` in `H` (Dey, Dufoulon, Moses Jr.,
Pandurangan, *Smoothed Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), §2,
"Notation", p.9).

**Formalization Note** Counted with `Set.ncard`, so no decidability instance is needed. Every
graph of the paper is finite, where this is the number of neighbours. -/
noncomputable def deg {V : Type} (H : SimpleGraph V) (v : V) : ℕ := (H.neighborSet v).ncard

/-- The closed neighbourhood `N_H[T] = ⋃_{v ∈ T} N_H[v]` of a vertex set `T` (§2, p.9). -/
def closedNbhd {V : Type} (H : SimpleGraph V) (T : Set V) : Set V :=
  {v | v ∈ T ∨ ∃ u ∈ T, H.Adj v u}

/-- The two-hop neighbourhood `N²_H[T] = {v : dist_H(v, T) ≤ 2}` (§2, pp.9–10).

**Formalization Note** `dist_H(v, T) = min_{y ∈ T} dist_H(v, y)` with `dist = ∞` between
components, so `dist_H(v, T) ≤ 2` iff some `y ∈ T` has `H.edist v y ≤ 2` (`SimpleGraph.edist`,
`⊤` when disconnected). `N²_H[∅] = ∅`. -/
def twoHop {V : Type} (H : SimpleGraph V) (T : Set V) : Set V :=
  {v | ∃ u ∈ T, H.edist v u ≤ 2}

/-- **Maximal independent set** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis for
Distributed MIS* (manuscript, sha256 dc2131db…), §2, p.9): "A set `I ⊆ V` is an MIS of `𝒢` if no
two vertices of `I` are adjacent in `𝒢` and every vertex of `V` lies in the closed neighborhood
`N_𝒢[I]`."

**Formalization Note** Stated for an arbitrary simple graph `H` on a vertex type `V`. -/
def IsMIS {V : Type} (H : SimpleGraph V) (I : Set V) : Prop :=
  (∀ u ∈ I, ∀ v ∈ I, ¬ H.Adj u v) ∧ ∀ v, v ∈ closedNbhd H I

end SmoothedMIS


