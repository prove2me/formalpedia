-- Prove2me | Definitions.Def_SubexpPermanent_Main_Matchings
-- name    : SubexpPermanent_Main_Matchings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:00:00.856667+00:00
-- url     : https://prove2.me/theorems/b1bbb76d-ef5b-43a4-ac70-d3dc8d3eb211
-- title:
--   Weighted matchings of a finite simple graph: $Z_G(w)$, the matching distribution, unmatched and edge probabilities, vertex deletion
-- statement:
--   Let $G=(V,E)$ be a finite simple graph (no loops, no parallel edges) and $w=(w_e)$ edge weights. For a vertex subset $U\subseteq V$ write $G[U]$ for the subgraph induced on $U$; deleting a set $S$ of vertices together with its incident edges, and keeping the other weights, gives $G-S=G[V\setminus S]$, and $G=G[V]$. A **matching** of $G[U]$ is a set of edges of $G[U]$ no two of which share an endpoint; the empty matching is one. The **matching partition function** is
--   $$Z_{G[U]}(w)=\sum_{M\text{ matching of }G[U]}\ \prod_{e\in M}w_e,$$
--   the empty matching contributing $1$, and the **matching distribution** is $\nu_{G[U],w}(M)=\prod_{e\in M}w_e/Z_{G[U]}(w)$. For $M\sim\nu_{G[U],w}$:
--   - $q_{G[U],w}(u)=\Pr_w(u\text{ is unmatched})$ (`unmatchedProb`),
--   - $\mu_{w,e}=\Pr_w(e\in M)$ (`edgeProb`),
--   - $\Pr_w(u,v\text{ both unmatched})$ (`bothUnmatchedProb`), and
--   - $\mathrm{Cov}(Y_u,Y_v)=\Pr_w(u,v\text{ both unmatched})-q(u)\,q(v)$, where $Y_u$ indicates that $u$ is unmatched (`unmatchedCov`).
--
--   **Formalization Note.** The vertex set is a finite type `V` and the graph a Mathlib `SimpleGraph V`; the weights are a function `w : Sym2 V → ℝ` whose values off the edges are never used. Each quantity takes the vertex subset `U` as an argument, so $G$ is `U = Finset.univ` and $G-S$ is `U = Finset.univ \ S`. The probabilities are written as ratios of weighted sums; every statement assumes $w_e>0$ on the edges, so $Z>0$ and no division by zero occurs.
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 12, §4.1 (and p. 13, Fact 4.5)

import Mathlib

namespace SubexpPermanent.Main

/-! # Weighted matchings of a finite simple graph (Kudria–Luo–Majid, §4.1, p. 12)

A finite simple graph is a `SimpleGraph V` on a finite vertex type `V`, with edge weights
`w : Sym2 V → ℝ` (only the values on edges matter; the theorems assume `w e > 0` on every edge).
Vertex deletion is encoded by a vertex subset: every quantity below is taken in the subgraph of
`G` induced on `U : Finset V`, so `G` itself is `U = Finset.univ` and `G − S` is
`U = Finset.univ \ S` (the paper deletes `S` and its incident edges and keeps the other weights).
-/

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `G` with both endpoints in `U` (the edge set of the induced subgraph `G[U]`). -/
noncomputable def edgesOn (G : SimpleGraph V) (U : Finset V) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ U)

/-- A set of edges is a matching when distinct edges share no endpoint. -/
def IsMatchingSet (M : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → ∀ v ∈ e, v ∉ e'

/-- All matchings of `G[U]`, including the empty matching. -/
noncomputable def matchingsOn (G : SimpleGraph V) (U : Finset V) : Finset (Finset (Sym2 V)) :=
  (edgesOn G U).powerset.filter IsMatchingSet

/-- The weight `∏_{e ∈ M} w_e` of a matching (the empty matching has weight one). -/
noncomputable def matchingWeight (w : Sym2 V → ℝ) (M : Finset (Sym2 V)) : ℝ :=
  ∏ e ∈ M, w e

/-- The vertex `v` is matched (covered) by the edge set `M`. -/
def Covers (M : Finset (Sym2 V)) (v : V) : Prop :=
  ∃ e ∈ M, v ∈ e

/-- The matching partition function `Z_{G[U]}(w) = ∑_{M matching of G[U]} ∏_{e ∈ M} w_e`. -/
noncomputable def matchingZ (G : SimpleGraph V) (w : Sym2 V → ℝ) (U : Finset V) : ℝ :=
  ∑ M ∈ matchingsOn G U, matchingWeight w M

/-- `q_{G[U],w}(u)`: the probability that `u` is unmatched in `M ∼ ν_{G[U],w}`, where
`ν_{G[U],w}(M) = ∏_{e∈M} w_e / Z_{G[U]}(w)`. -/
noncomputable def unmatchedProb (G : SimpleGraph V) (w : Sym2 V → ℝ) (U : Finset V) (u : V) : ℝ :=
  (∑ M ∈ (matchingsOn G U).filter (fun M => ¬ Covers M u), matchingWeight w M) / matchingZ G w U

/-- `μ_{w,e}`: the probability that the edge `e` belongs to `M ∼ ν_{G[U],w}`. -/
noncomputable def edgeProb (G : SimpleGraph V) (w : Sym2 V → ℝ) (U : Finset V) (e : Sym2 V) : ℝ :=
  (∑ M ∈ (matchingsOn G U).filter (fun M => e ∈ M), matchingWeight w M) / matchingZ G w U

/-- `Pr_w(u, v both unmatched in M)` for `M ∼ ν_{G[U],w}`. -/
noncomputable def bothUnmatchedProb (G : SimpleGraph V) (w : Sym2 V → ℝ) (U : Finset V)
    (u v : V) : ℝ :=
  (∑ M ∈ (matchingsOn G U).filter (fun M => ¬ Covers M u ∧ ¬ Covers M v), matchingWeight w M) /
    matchingZ G w U

/-- `Cov(Y_u, Y_v) = E[Y_u Y_v] − E[Y_u] E[Y_v]`, where `Y_u` indicates that `u` is unmatched
in `M ∼ ν_{G[U],w}`. -/
noncomputable def unmatchedCov (G : SimpleGraph V) (w : Sym2 V → ℝ) (U : Finset V) (u v : V) : ℝ :=
  bothUnmatchedProb G w U u v - unmatchedProb G w U u * unmatchedProb G w U v

end SubexpPermanent.Main


