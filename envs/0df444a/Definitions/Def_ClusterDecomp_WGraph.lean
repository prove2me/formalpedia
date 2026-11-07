-- Prove2me | Definitions.Def_ClusterDecomp_WGraph
-- name    : ClusterDecomp_WGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:43.4593+00:00
-- url     : https://prove2.me/theorems/c3b22f4c-60bd-4343-a0e2-99a23e5c4925
-- title:
--   Weighted graphs with loops: degree, volume, cut value, edge sets
-- statement:
--   A weighted graph on a finite vertex set $V$ is a symmetric function $w:V\times V\to\mathbb R_{\ge0}$, where $w(u,v)=0$ means that $\{u,v\}$ is not an edge and $w(v,v)$ is the weight of the loop at $v$. The degree and volume are
--   $$\deg(v)=\sum_{u\in V}w(v,u),\qquad \mathrm{vol}(S)=\sum_{v\in S}\deg(v),$$
--   so a loop counts once in the degree. For $S,T\subseteq V$, the cut value is $w(S,T)=\sum_{u\in S}\sum_{v\in T}w(u,v)$. The edge set $E$ consists of the unordered pairs of positive weight, loops included, and $E(G[X])$ of those with both ends in $X$.
--
--   These are the quantities in which all conductances of the paper are measured.
--
--   **Formalization Note** The cut value is used only for disjoint $S,T$, so a loop never contributes to a cut, though it does contribute to the volume. It is defined through a raw capacity function that the fair-cut layer shares.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), §2.1, p.7 (PDF p.9)

import Mathlib

open Finset

namespace ClusterDecomp

/-!
# Weighted graphs with loops

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), §2.1, p.7 (PDF p.9).

**Formalization Note.**
* A graph is a symmetric nonnegative weight function on a finite vertex type; `w u v = 0` means there
  is no edge and `w v v` is the weight of the loop at `v`. Weights are real (the paper's own type,
  `w : E → ℝ_{>0}`, p.7); integrality is a separate assumption, carried only by the goal.
* `deg v = ∑ u, w v u`, so a loop counts **once** in the degree. This is what makes `G{S}` degree preserving.
* `cutCap c S T = ∑ u ∈ S, ∑ v ∈ T, c u v`, for a raw capacity function `c`; `G.cut S T` is the paper's
  `w(S, T)`, used only for disjoint `S`, `T`, so a loop never contributes to a cut.
* `edges` lists the unordered pairs of positive weight (`s(v, v)` is a loop) and `edgesIn X` those with
  both ends in `X`: `|E(G)|` and `|E(G[X])|`.
-/

/-- `∑_{u ∈ S} ∑_{v ∈ T} c(u, v)` for a raw capacity function `c`. -/
def cutCap {V : Type*} (c : V → V → ℝ) (S T : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ T, c u v

/-- An undirected weighted graph with loops on the vertex type `V`. -/
structure WGraph (V : Type*) where
  /-- The weight `w(u, v)`; `0` when `{u, v}` is not an edge. -/
  w : V → V → ℝ
  /-- The graph is undirected. -/
  symm : ∀ u v, w u v = w v u
  /-- Weights are nonnegative. -/
  nonneg : ∀ u v, 0 ≤ w u v

namespace WGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WGraph V)

/-- The degree `deg(v) = ∑_{u ∼ v} w(u, v)`; a loop counts once (p.7). -/
def deg (v : V) : ℝ := ∑ u, G.w v u

/-- Every vertex has positive degree (standing assumption, p.1). -/
def PosDeg : Prop := ∀ v, 0 < G.deg v

/-- The volume `vol(S) = ∑_{v ∈ S} deg(v)` (p.7). -/
def vol (S : Finset V) : ℝ := ∑ v ∈ S, G.deg v

/-- The cut value `w(S, T)` (p.7), used for disjoint `S`, `T`. -/
def cut (S T : Finset V) : ℝ := cutCap G.w S T

/-- The edge set `E`: unordered pairs of positive weight, loops included. -/
noncomputable def edges : Finset (Sym2 V) := by
  classical
  exact univ.filter fun e => ∃ u v, e = s(u, v) ∧ 0 < G.w u v

/-- `E(G[X])`: the edges with both endpoints in `X`. -/
noncomputable def edgesIn (X : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edges.filter fun e => ∀ v ∈ e, v ∈ X

end WGraph

end ClusterDecomp


