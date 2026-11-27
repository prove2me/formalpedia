-- Prove2me | Definitions.Def_RandomGreedyMIS_matching
-- name    : RandomGreedyMIS_matching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T04:33:59.256787+00:00
-- url     : https://prove2.me/theorems/d215a3a7-d651-44fb-9ae7-79dcd6d2f523
-- title:
--   Random greedy maximal matching via the line graph
-- statement:
--   The random greedy maximal matching, realized as the greedy maximal independent set of the line graph. Let $H$ be a finite simple graph on $\{0,\dots,n-1\}$ with $m$ edges.
--
--   1. `edgeEnum H`: a fixed enumeration of the edges of $H$ by $\{0,\dots,m-1\}$.
--   2. `lineGraph H`: the line graph $L(H)$ on $\{0,\dots,m-1\}$, in which two distinct edges are adjacent when they share an endpoint.
--   3. `GM H σ`: for a ranking $\sigma$ of the edges, the set of edges whose vertex of $L(H)$ belongs to the greedy maximal independent set of $L(H)$ for $\sigma$; this is the greedy maximal matching obtained by scanning the edges in increasing rank and keeping every edge disjoint from those kept before.
--
--   The recursive oracle `RandomGreedyMIS.inMIS (lineGraph H) σ i` decides locally whether edge $i$ is in this matching, which is the basis of sublinear matching-size estimators.
-- source:
--   Nguyen–Onak, FOCS 2008; Yoshida–Yamamoto–Ito, STOC 2009; S. Behnezhad, FOCS 2021 (randomized greedy maximal matching); cited as Lemma 9.9 in Azarmehr–Behnezhad 2026, https://arxiv.org/abs/2611.04283, §9.2.2, p.40.

import Mathlib
import Definitions.Def_RandomGreedyMIS_basic

namespace RandomGreedyMIS

open Finset

noncomputable section LineGraph

variable {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

/-- Fixed enumeration of the edges of `H`. -/
def edgeEnum : Fin H.edgeFinset.card ≃ H.edgeFinset := H.edgeFinset.equivFin.symm

/-- The line graph of `H` on `Fin m`, `m = |E(H)|`. -/
def lineGraph : SimpleGraph (Fin H.edgeFinset.card) where
  Adj i j := i ≠ j ∧ ∃ x, x ∈ ((edgeEnum H i : H.edgeFinset) : Sym2 (Fin n)) ∧
    x ∈ ((edgeEnum H j : H.edgeFinset) : Sym2 (Fin n))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ hx => ⟨hx.2, hx.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel (lineGraph H).Adj := fun i j => by
  unfold lineGraph; infer_instance

lemma lineGraph_adj (i j : Fin H.edgeFinset.card) :
    (lineGraph H).Adj i j ↔ i ≠ j ∧ ∃ x, x ∈ ((edgeEnum H i : H.edgeFinset) : Sym2 (Fin n)) ∧
      x ∈ ((edgeEnum H j : H.edgeFinset) : Sym2 (Fin n)) := Iff.rfl

/-- The greedy matching for ranking `σ`: the edges whose line-graph vertex is in the greedy MIS. -/
def GM (σ : Equiv.Perm (Fin H.edgeFinset.card)) : Finset (Sym2 (Fin n)) :=
  (univ.filter (fun i => inMIS (lineGraph H) σ i = true)).image
    (fun i => ((edgeEnum H i : H.edgeFinset) : Sym2 (Fin n)))


end LineGraph

end RandomGreedyMIS


