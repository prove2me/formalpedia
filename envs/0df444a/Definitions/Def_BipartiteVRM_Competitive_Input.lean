-- Prove2me | Definitions.Def_BipartiteVRM_Competitive_Input
-- name    : BipartiteVRM_Competitive_Input
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:53.755466+00:00
-- url     : https://prove2.me/theorems/e7b0ce96-c2ab-480b-aada-aa6c12b9174a
-- title:
--   Finite metric inputs, the timed offline objective, and TA distance
-- statement:
--   Let $(X,d)$ be any metric space. An input consists of finite disjoint request and server sets $R,S$ of the same cardinality $m$, locations $x_v\in X$, and real arrival times $a_v\ge0$. Locations and times may coincide. A matching has disjoint endpoints; a perfect matching covers both sets. A feasible match time satisfies $t_{rs}\ge\max(a_r,a_s)$. Define
--
--   $$C(M,t)=\sum_{rs\in M}\bigl[d(x_r,x_s)+(t_{rs}-a_r)+(t_{rs}-a_s)\bigr],\qquad
--   D(u,v)=d(x_u,x_v)+|a_u-a_v|,\qquad D(F)=\sum_{e\in F}D(e).$$
--
--   The offline value is the infimum of $C(M,t)$ over all feasible timed perfect matchings. Its extended nonnegative value is retained before real conversion; finiteness and attainment are theorem conclusions. The predicate that a perfect matching minimizes $D$ is defined independently of the algorithm.
--
--   This is the common input and objective layer for every source statement. The general bipartite matching predicate is the published TwoStageMatch predicate, specialized to the complete bipartite graph. Natural labels identify items without imposing metric separation or supplying the final count to the algorithm.
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 6, §2.1–§2.3, equations (2.1)–(2.2)

import Mathlib
import Definitions.Def_TwoStageMatch_Bipartite

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-! Kuo, STOC 2027 submission #528 (October 2026), §2, p. 6.
Natural labels are names, not a known final cardinality. Only the finite supports are input.
The same label on the two sides denotes different items. No separation of locations is assumed.
-/

abbrev Vertex := ℕ ⊕ ℕ
abbrev Edge := ℕ × ℕ
abbrev Matching := Finset Edge

structure Input (X : Type*) where
  requests : Finset ℕ
  servers : Finset ℕ
  balanced : requests.card = servers.card
  location : Vertex → X
  arrival : Vertex → ℝ
  arrival_nonneg : ∀ v ∈ requests.image Sum.inl ∪ servers.image Sum.inr, 0 ≤ arrival v

def Input.items {X : Type*} (I : Input X) : Finset Vertex :=
  I.requests.image Sum.inl ∪ I.servers.image Sum.inr

def Input.size {X : Type*} (I : Input X) : ℕ := I.requests.card

noncomputable def Input.arrived {X : Type*} (I : Input X) (t : ℝ) : Finset Vertex := by
  classical
  exact I.items.filter (fun v => I.arrival v ≤ t)

def IsMatching (R S : Finset ℕ) (M : Matching) : Prop :=
  TwoStageMatch.IsMatching (fun _ _ => True) R S M

def IsPerfect {X : Type*} (I : Input X) (M : Matching) : Prop :=
  IsMatching I.requests I.servers M ∧ M.image Prod.fst = I.requests ∧
    M.image Prod.snd = I.servers

def FeasibleTimes {X : Type*} (I : Input X) (M : Matching) (τ : Edge → ℝ) : Prop :=
  ∀ e ∈ M, max (I.arrival (.inl e.1)) (I.arrival (.inr e.2)) ≤ τ e

noncomputable def totalCost {X : Type*} [MetricSpace X] (I : Input X)
    (M : Matching) (τ : Edge → ℝ) : ℝ :=
  ∑ e ∈ M, (dist (I.location (.inl e.1)) (I.location (.inr e.2)) +
    (τ e - I.arrival (.inl e.1)) + (τ e - I.arrival (.inr e.2)))

/-- Infimum of the actual timed offline objective (2.1), before any reduction to TA distance.
Empty feasible ranges have value +∞. The offline-attainment theorem proves this does not
occur for an Input, and proves that conversion to ℝ below loses no value. -/
noncomputable def offlineInf {X : Type*} [MetricSpace X] (I : Input X) : ENNReal :=
  ⨅ (M : Matching) (_ : IsPerfect I M) (τ : Edge → ℝ) (_ : FeasibleTimes I M τ),
    ENNReal.ofReal (totalCost I M τ)

noncomputable def OPT {X : Type*} [MetricSpace X] (I : Input X) : ℝ :=
  (offlineInf I).toReal

noncomputable def taDistance {X : Type*} [MetricSpace X] (I : Input X)
    (u v : Vertex) : ℝ := dist (I.location u) (I.location v) + |I.arrival u - I.arrival v|

noncomputable def edgeDistance {X : Type*} [MetricSpace X] (I : Input X) (e : Edge) : ℝ :=
  taDistance I (.inl e.1) (.inr e.2)

noncomputable def matchingDistance {X : Type*} [MetricSpace X] (I : Input X)
    (M : Matching) : ℝ := ∑ e ∈ M, edgeDistance I e

def IsOptimal {X : Type*} [MetricSpace X] (I : Input X) (M : Matching) : Prop :=
  IsPerfect I M ∧ ∀ N, IsPerfect I N → matchingDistance I M ≤ matchingDistance I N

def age {X : Type*} (I : Input X) (v : Vertex) (t : ℝ) : ℝ := t - I.arrival v

end BipartiteVRM.Competitive


