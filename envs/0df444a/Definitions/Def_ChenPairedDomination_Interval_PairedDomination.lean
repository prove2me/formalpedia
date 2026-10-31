-- Prove2me | Definitions.Def_ChenPairedDomination_Interval_PairedDomination
-- name    : ChenPairedDomination_Interval_PairedDomination
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T01:25:25.937174+00:00
-- url     : https://prove2.me/theorems/ff4741ad-09df-4c4e-923b-7e084f66941b
-- title:
--   Paired domination and minimum paired domination on an induced graph
-- statement:
--   For a simple graph G on a type V and finite vertex sets U and S, S paired-dominates G[U] if S is contained in U, every vertex of U outside S has a neighbor in S, and the induced graph G[S] has a perfect matching. The matching covers all and only the selected vertices. S is a minimum paired-dominating set of G[U] if it is feasible and its cardinality is at most the cardinality of every feasible finite set T. These predicates are independent of interval graphs and of MPDI. Finite sets have decidable equality; no graph connectivity or feasibility is built into the predicates.
-- source:
--   Chen, Lu and Zeng, arXiv:0802.2742v1 (2008), https://arxiv.org/abs/0802.2742v1, §1, p. 2

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Finset.Card

namespace ChenPairedDomination.Interval

/-- Paired domination of the induced graph on `U`; matching covers exactly `S`. -/
def PairedDominatesOn {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (U S : Finset V) : Prop :=
  S ⊆ U ∧ (∀ v ∈ U, v ∉ S → ∃ s ∈ S, G.Adj v s) ∧
    ∃ M : (G.induce (S : Set V)).Subgraph, M.IsPerfectMatching

/-- Cardinality minimum over every feasible set, independent of any algorithm. -/
def MinimumPairedDominatesOn {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (U S : Finset V) : Prop :=
  PairedDominatesOn G U S ∧ ∀ T : Finset V, PairedDominatesOn G U T → S.card ≤ T.card

end ChenPairedDomination.Interval


