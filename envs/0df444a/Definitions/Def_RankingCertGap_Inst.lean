-- Prove2me | Definitions.Def_RankingCertGap_Inst
-- name    : RankingCertGap_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:10.244915+00:00
-- url     : https://prove2.me/theorems/013fbedd-34c0-490c-a70d-bdb6599cd238
-- title:
--   Finite online bipartite matching instances, their maximum matching $\mathrm{OPT}$, and the degree classes
-- statement:
--   A **finite online bipartite matching instance** is a bipartite graph $G=(I,J,E)$ whose online vertices $J$ carry an arrival order fixed before any randomness is drawn. Here $I=\{0,\dots,m-1\}$, $J=\{0,\dots,n-1\}$ is listed in arrival order, and the edges are given by the neighbourhoods $N_G(j)\subseteq I$.
--
--   A **matching** is a set of edges in which each vertex occurs at most once, and $\mathrm{OPT}(G)$ is the largest cardinality of a matching of the full graph.
--
--   $G$ has **online degree at most $d$** when $|N_G(j)|\le d$ for every $j$, with no restriction on offline degrees. It is **$d$-regular** when it is nonempty and every offline and online vertex has degree exactly $d$.
--
--   These are the instances over which the competitiveness of RANKING and the guarantees of its primal-dual analysis are taken.
--
--   **Formalization Note** An arbitrary arrival order is a relabelling of $J$, so listing $J$ in arrival order loses nothing. Neighbourhoods are sets, so graphs are simple, as on p.35 of the source. $\mathrm{OPT}$ is a supremum over the finitely many edge sets, so it has no junk value.
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), §1, p.1; §1.1, p.2; §1.2, p.4

import Mathlib

namespace RankingCertGap

/-- **Finite online bipartite matching instance.** Xu, *Certifying Capacity and Gaps of the
Rank-Dependent Gain-Sharing Framework for Ranking*, arXiv:2610.17545 (held file sha256 75896dd9…),
§1, p.1 and §1.1, p.2: a finite bipartite graph `G = (I, J, E)` with "an online arrival order fixed
before the offline ranks are sampled".

**Formalization Note.** The offline set is `I = Fin m`, the online set is `J = Fin n`, and `Fin n`
is listed in arrival order: `j` arrives before `j'` iff `j < j'`. An arbitrary arrival order is a
relabelling of `J`. The edges are given by the neighbourhoods `N j ⊆ I`, so graphs are simple. -/
structure Inst (m n : ℕ) where
  /-- The offline neighbourhood `N_G(j)` of the online vertex `j`. -/
  N : Fin n → Finset (Fin m)

namespace Inst

variable {m n : ℕ}

/-- `(i, j) ∈ E(G)`. -/
def Edge (G : Inst m n) (i : Fin m) (j : Fin n) : Prop := i ∈ G.N j

/-- A matching of `G`: a set of edges of `G` in which each offline vertex and each online vertex
occurs at most once. -/
def IsMatching (G : Inst m n) (M : Finset (Fin m × Fin n)) : Prop :=
  (∀ e ∈ M, G.Edge e.1 e.2) ∧
    (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧
    (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e')

open Classical in
/-- `OPT(G)`, "the maximum matching cardinality in the full graph" (§1.1, p.2): the largest
cardinality of a matching, computed as a `Finset.sup` over the finitely many edge sets. -/
noncomputable def OPT (G : Inst m n) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m × Fin n))).filter fun M => G.IsMatching M).sup Finset.card

/-- Online degree at most `d`: "online vertices have degree at most `d`, with no restriction on
offline degrees" (§1.2, p.4). -/
def IsOnlineDegLE (G : Inst m n) (d : ℕ) : Prop := ∀ j, (G.N j).card ≤ d

/-- `d`-regular: "nonempty finite `d`-regular bipartite instances, in which every offline and online
vertex has degree exactly `d`" (§1.2, p.4). Nonemptiness is `0 < m ∨ 0 < n`. -/
def IsRegular (G : Inst m n) (d : ℕ) : Prop :=
  (∀ j, (G.N j).card = d) ∧
    (∀ i, (Finset.univ.filter fun j => i ∈ G.N j).card = d) ∧
    (0 < m ∨ 0 < n)

end Inst

end RankingCertGap


