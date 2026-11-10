-- Prove2me | Definitions.Def_CharonChurn_Main_Connectivity
-- name    : CharonChurn_Main_Connectivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:54:30.889805+00:00
-- url     : https://prove2.me/theorems/29c5d757-3b1a-4ab7-807c-940589020254
-- title:
--   Vertex connectivity $\kappa$ with the empty, singleton and complete-graph conventions; neighbourhoods and minimum degree
-- statement:
--   A finite simple graph is represented by an ambient simple graph $G$ on a type $\alpha$ together with a finite vertex set $S$; the graph meant is the induced subgraph $G[S]$ (every finite simple graph is of this form, and $G[K]$, $G-A$ are $K$ and $S\setminus A$).
--
--   A set $Z\subseteq S$ is *separating* when $G[S\setminus Z]$ is disconnected or has at most one vertex. The vertex connectivity $\kappa(G[S])$ is the least $|Z|$ over separating $Z\subseteq S$ (the choice $Z=S$ is always separating). This reproduces the source's conventions exactly: $\kappa=0$ for a disconnected graph and for a graph with at most one vertex, $\kappa(K_h)=h-1$ (including $\kappa(K_1)=0$), and the minimum vertex-separator size for a connected non-complete graph.
--
--   $N_G(v)\cap K$ is the set of neighbours of $v$ in $K$, and for nonempty $S$ the minimum degree $\delta(G[S])$ is $\min_{v\in S}|N_G(v)\cap S|$.
-- source:
--   Sengupta and Perrin (2026), Byzantine Partition Detection Under Churn, supplied 48-page artifact (venue metadata: STOC 2027 submission; citation basis published per source.meta.json; SHA-256 3f9994406f38c73927d0b5cc78d0dd05740de0f7d09e544b7b203eefe39cdb74), §2.6, p. 10 (PDF 10); §4 preamble, p. 18; Lemma 6, p. 19

import Mathlib

namespace CharonChurn.Main

/-! # Vertex connectivity with the source's conventions (Sengupta–Perrin 2026, §2.6, p. 10)

A finite simple graph is given by an ambient `SimpleGraph α` together with a finite vertex set
`S : Finset α`; the graph meant is the induced subgraph `G[S]`. Every finite simple graph is of
this form, and `G[K]`, `G − A` are again of this form (`K`, `S \ A`). -/

/-- Removing `Z` from `S` leaves a disconnected graph or at most one vertex. -/
def IsSeparating {α : Type*} [DecidableEq α] (G : SimpleGraph α) (S Z : Finset α) : Prop :=
  ¬ (G.induce (↑(S \ Z) : Set α)).Connected ∨ (S \ Z).card ≤ 1

/-- Vertex connectivity `κ(G[S])`: the least number of vertices of `S` whose removal leaves a
disconnected graph or at most one vertex. This gives `κ = 0` for a disconnected, empty or
singleton graph, `κ(K_h) = h − 1`, and the minimum vertex-separator size otherwise. -/
noncomputable def kappa {α : Type*} [DecidableEq α] (G : SimpleGraph α) (S : Finset α) : ℕ := by
  classical
  exact Nat.find (⟨S.card, S, Finset.Subset.refl S, rfl, Or.inr (by simp)⟩ :
    ∃ k, ∃ Z ⊆ S, Z.card = k ∧ IsSeparating G S Z)

/-- The neighbours of `v` inside the vertex set `K`: `N_G(v) ∩ K`. -/
noncomputable def nbrsIn {α : Type*} (G : SimpleGraph α) (K : Finset α) (v : α) : Finset α := by
  classical
  exact K.filter (fun w => G.Adj v w)

/-- Minimum degree `δ(G[S])` of a nonempty finite graph. -/
noncomputable def minDegree {α : Type*} (G : SimpleGraph α) (S : Finset α) (hS : S.Nonempty) : ℕ :=
  S.inf' hS (fun v => (nbrsIn G S v).card)

end CharonChurn.Main


