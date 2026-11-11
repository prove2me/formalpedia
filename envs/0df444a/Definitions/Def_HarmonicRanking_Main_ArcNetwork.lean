-- Prove2me | Definitions.Def_HarmonicRanking_Main_ArcNetwork
-- name    : HarmonicRanking_Main_ArcNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:27.381084+00:00
-- url     : https://prove2.me/theorems/fc9ac1df-8c97-4f6c-90bb-3669c5d63bf3
-- title:
--   Generic arc-indexed capacities, flows, and cuts
-- statement:
--   A generic arc-indexed network consists of a published directed multigraph, source $s$, sink $t$, and a real capacity $c_e$ for each arc record $e$. A flow gives an amount $f_e$ to each record. It is feasible when $0\le f_e\le c_e$ and net outflow vanishes at every vertex other than $s,t$. Define
--
--   $$
--   \operatorname{val}(f)=\sum_{e:\,\operatorname{tail}(e)=s}f_e-\sum_{e:\,\operatorname{head}(e)=s}f_e,
--   \qquad
--   c(S)=\sum_{\operatorname{tail}(e)\in S,\,\operatorname{head}(e)\notin S}c_e.
--   $$
--
--   A cut shore contains $s$ and excludes $t$. Maximum-flow and minimum-cut values are the supremum of feasible flow values and the infimum of such cut capacities. The threshold construction supplies distinct terminals and nonnegative capacities, ensuring nonempty bounded domains. This generic layer is separate from that construction, and preserves parallel records needed for independent rounding. It does not assume max-flow/min-cut equality.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), p. 17, ordinary finite-capacity network following Eqs. (34)–(35)

import Definitions.Def_CombOpt_MinCostFlow_Digraph

set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main

/-- Generic arc-indexed network data, separate from the threshold construction.
The capacities used below are nonnegative; raw data also allow other inputs. -/
structure ArcNetwork (V A : Type*) where
  graph : CombOpt.MinCostFlow.Digraph V A
  source : V
  sink : V
  capacity : A → ℝ

variable {V A : Type*} [Fintype V] [Fintype A]

def divergence (N : ArcNetwork V A) (f : A → ℝ) (v : V) : ℝ := by
  classical
  exact (∑ e, if N.graph.tail e = v then f e else 0) -
    ∑ e, if N.graph.head e = v then f e else 0

def FeasibleFlow (N : ArcNetwork V A) (f : A → ℝ) : Prop :=
  (∀ e, 0 ≤ f e ∧ f e ≤ N.capacity e) ∧
  ∀ v, v ≠ N.source → v ≠ N.sink → divergence N f v = 0

def flowValue (N : ArcNetwork V A) (f : A → ℝ) : ℝ := divergence N f N.source

def cutCapacity (N : ArcNetwork V A) (S : Finset V) : ℝ := by
  classical
  exact ∑ e, if N.graph.tail e ∈ S ∧ N.graph.head e ∉ S then N.capacity e else 0

def IsShore (N : ArcNetwork V A) (S : Finset V) : Prop :=
  N.source ∈ S ∧ N.sink ∉ S

def maxFlow (N : ArcNetwork V A) : ℝ :=
  sSup {v | ∃ f : A → ℝ, FeasibleFlow N f ∧ flowValue N f = v}

def minCut (N : ArcNetwork V A) : ℝ :=
  sInf {v | ∃ S : Finset V, IsShore N S ∧ cutCapacity N S = v}

end HarmonicRanking.Main


