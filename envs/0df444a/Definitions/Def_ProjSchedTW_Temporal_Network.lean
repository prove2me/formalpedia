-- Prove2me | Definitions.Def_ProjSchedTW_Temporal_Network
-- name    : ProjSchedTW_Temporal_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T14:14:02.256983+00:00
-- url     : https://prove2.me/theorems/04b70cf8-87d0-4a33-9a65-2104fe3eeda9
-- title:
--   §1.2–1.3 — AoN project network: walks, paths, cycles, longest path lengths, and the temporal scheduling network N⁺
-- statement:
--   An **activity-on-node (AoN) network** $N$ on the node set $V=\{0,1,\dots,n+1\}$ consists of an arc set $E\subseteq V\times V$ of ordered pairs of *different* nodes and an integer weight $\delta_{ij}$ for every arc $\langle i,j\rangle\in E$. An arc of positive weight encodes a minimum time lag, an arc of negative weight a maximum time lag (as a backward arc), and the weights "may be positive, negative, or zero". There is at most one arc per ordered pair.
--
--   For $m\ge 0$, a **walk** with $m$ arcs is a node sequence $w_0,w_1,\dots,w_m$ with $\langle w_k,w_{k+1}\rangle\in E$ for $k<m$; its **length** is the sum of its arc weights
--   $$\ell(w)=\sum_{k=0}^{m-1}\delta_{w_k w_{k+1}}.$$
--   A **path** is a walk with pairwise distinct nodes (so the one-node sequence $i$ is a path from $i$ to $i$ of length $0$). A **cycle** is a closed walk $w_0\to\dots\to w_m=w_0$ with $m\ge 1$ arcs whose nodes $w_0,\dots,w_{m-1}$ are pairwise distinct. $N$ **contains a cycle of positive length** if some cycle has $\ell(w)>0$.
--
--   The **distance** (longest path length) $d_{ij}$ is the maximum length of a path from $i$ to $j$, taken in $\mathbb Z\cup\{-\infty\}$, with $d_{ij}=-\infty$ when there is no path; in particular $d_{ii}=0$.
--
--   Given an integer $L=LS_{n+1}$ (a prescribed maximum project duration $\bar d$, or the shortest project duration $ES_{n+1}$), the **temporal scheduling network** $N^+$ is $N$ together with the backward arc $\langle n+1,0\rangle$ of weight $\delta_{n+1,0}=-L$, so $E^+=E\cup\{\langle n+1,0\rangle\}$.
--
--   These objects are the graph-theoretic substrate of temporal project scheduling: feasibility of the temporal constraints, earliest and latest start times, and the distance order are all expressed through them.
--
--   **Formalization Note.** Nodes are `Fin (n + 2)`, with $0$ the project beginning and `Fin.last (n + 1)` the project completion. Walks are functions `Fin (m + 1) → Fin (n + 2)`. Distances are maxima over the finitely many *simple* paths (a path has at most $n+1$ arcs), valued in `WithBot ℤ` with $\bot=-\infty$; no supremum over walks is taken, so no junk value arises. Cycles are simple cycles; since a closed walk of positive length always contains a simple cycle of positive length, "no cycle of positive length" is equivalent to "no closed walk of positive length". If $N$ already contains an arc $\langle n+1,0\rangle$, the two arcs are merged into one arc whose weight is the larger of the two, following the book's convention (p. 7) that parallel time lags are replaced by the tightest one.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, §1.2 pp. 6–8 (arc construction, Eq. (1.2.1), cycles and path lengths) and §1.3 p. 11 (temporal scheduling network N⁺, distances d_ij)

import Mathlib

namespace ProjSchedTW.Temporal

/-- An activity-on-node (AoN) network on the node set `V = {0, 1, …, n+1}` (§1.2, p. 7):
an arc set `E` of ordered pairs of distinct nodes, and an integer arc weight `δ i j` for every
arc `⟨i, j⟩ ∈ E` (values of `δ` off `E` are never used). Weights may be positive (minimum time
lags), negative (maximum time lags) or zero. -/
structure Network (n : ℕ) where
  /-- The arc set `E`. -/
  E : Finset (Fin (n + 2) × Fin (n + 2))
  /-- The arc weights `δ_ij`. -/
  δ : Fin (n + 2) → Fin (n + 2) → ℤ
  /-- Arcs join two different activities. -/
  loopless : ∀ i, (i, i) ∉ E

variable {n : ℕ}

/-- A walk with `m` arcs in `N`: a node sequence `w 0, w 1, …, w m` with `⟨w k, w (k+1)⟩ ∈ E`. -/
def IsWalk (N : Network n) {m : ℕ} (w : Fin (m + 1) → Fin (n + 2)) : Prop :=
  ∀ k : Fin m, (w k.castSucc, w k.succ) ∈ N.E

/-- The length of a walk: the sum of its arc weights. -/
def walkLength (N : Network n) {m : ℕ} (w : Fin (m + 1) → Fin (n + 2)) : ℤ :=
  ∑ k : Fin m, N.δ (w k.castSucc) (w k.succ)

/-- A path: a walk whose nodes are pairwise distinct. -/
def IsPath (N : Network n) {m : ℕ} (w : Fin (m + 1) → Fin (n + 2)) : Prop :=
  IsWalk N w ∧ Function.Injective w

/-- A cycle: a closed walk `w 0 → ⋯ → w m = w 0` with at least one arc whose nodes
`w 0, …, w (m-1)` are pairwise distinct. -/
def IsCycle (N : Network n) {m : ℕ} (w : Fin (m + 1) → Fin (n + 2)) : Prop :=
  IsWalk N w ∧ 0 < m ∧ w 0 = w (Fin.last m) ∧
    Function.Injective (fun k : Fin m => w k.castSucc)

/-- `N` contains a cycle of positive length. -/
def HasPositiveCycle (N : Network n) : Prop :=
  ∃ (m : ℕ) (w : Fin (m + 1) → Fin (n + 2)), IsCycle N w ∧ 0 < walkLength N w

open Classical in
/-- The (finite) set of lengths of paths from `i` to `j` in `N`. A path has at most `n + 1`
arcs, so it is indexed by `m : Fin (n + 2)`. -/
noncomputable def pathLengths (N : Network n) (i j : Fin (n + 2)) : Finset ℤ :=
  ((Finset.univ : Finset (Σ m : Fin (n + 2), Fin (m.val + 1) → Fin (n + 2))).filter
      (fun w => IsPath N w.2 ∧ w.2 0 = i ∧ w.2 (Fin.last w.1.val) = j)).image
    (fun w => walkLength N w.2)

/-- The distance `d_ij`: the length of a longest path from `i` to `j` in `N`, and `⊥ = -∞`
if there is no such path. The trivial path gives `d_ii = 0`. -/
noncomputable def dist (N : Network n) (i j : Fin (n + 2)) : WithBot ℤ :=
  (pathLengths N i j).max

/-- The temporal scheduling network `N⁺` (§1.3, p. 11): `N` together with the backward arc
`⟨n+1, 0⟩` of weight `-LS_{n+1}`, where `L = LS_{n+1}`. If `N` already has an arc `⟨n+1, 0⟩`,
the two are merged into one arc whose weight is the larger one, following the convention of
§1.2, p. 7, that parallel time lags are replaced by the tightest one. -/
def Network.plus (N : Network n) (L : ℤ) : Network n where
  E := insert (Fin.last (n + 1), 0) N.E
  δ := fun i j =>
    if i = Fin.last (n + 1) ∧ j = 0 then
      (if (i, j) ∈ N.E then max (N.δ i j) (-L) else -L)
    else N.δ i j
  loopless := by
    intro i h
    rcases Finset.mem_insert.mp h with h | h
    · simp only [Prod.mk.injEq] at h
      exact absurd (h.1.symm.trans h.2) (Fin.last_pos.ne')
    · exact N.loopless i h

end ProjSchedTW.Temporal


