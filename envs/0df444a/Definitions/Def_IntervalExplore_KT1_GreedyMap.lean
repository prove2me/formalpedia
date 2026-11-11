-- Prove2me | Definitions.Def_IntervalExplore_KT1_GreedyMap
-- name    : IntervalExplore_KT1_GreedyMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:46.394051+00:00
-- url     : https://prove2.me/theorems/bc6a4d97-466e-4186-ac21-7dbe3e4e6bae
-- title:
--   Observation map, extended-distance potential and GreedyExp1
-- statement:
--   For a history through time $t$, let $V_{\rm vis}$ be the identifiers of the visited vertices and let $V_{\rm map}$ consist of the initial identifier together with all observed neighbor identifiers. An edge of the map has a visited endpoint and must have been present on every recorded visit to either endpoint. No edge joins a vertex outside $V_{\rm map}$.
--
--   With $U=V_{\rm map}\setminus V_{\rm vis}$ and current vertex $v$, the potential is
--   $$
--   d_{\rm cur}=\begin{cases}\min_{u\in U}d_{G_{\rm map}}(v,u),&U\ne\varnothing,\\0,&U=\varnothing.\end{cases}
--   $$
--   Unreachable vertices have infinite distance. The algorithm terminates exactly when $U$ is empty. Otherwise, every allowed greedy option is an observed neighbor and its local port lying on a shortest path to a closest unvisited vertex. The policy predicate permits every such choice. One deterministic realization chooses the least allowed local port. A fallback invalid port only totalizes histories with no reachable target or malformed observations.
--
--   The agent's map is built entirely on identifiers. For analysis it is pulled back to the original carrier $V$, with unknown vertices isolated. Thus the model supports the paper's graph distances without exposing the underlying graph to the algorithm. The policy predicate imposes no termination or time bound.
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Algorithm 1, map formulas and potential, §2.1, p.6 (PDF p.7); two-stage discussion, p.7 (PDF p.8)

import Definitions.Def_IntervalExplore_KT1_Execution

set_option autoImplicit false

namespace IntervalExplore.KT1

def neighborIDs (o : Obs) : Finset ℕ := o.neighbors.image Prod.fst

def visited (h : List Obs) : Finset ℕ := (h.map Obs.own).toFinset

/-- Exactly the initial vertex and the union of all one-hop observations. -/
def known (h : List Obs) : Finset ℕ :=
  ((h.take 1).map Obs.own).toFinset ∪ h.toFinset.biUnion neighborIDs

def targets (h : List Obs) : Finset ℕ := known h \ visited h

def current (h : List Obs) : Obs := h.getLast?.getD default

/-- §2.1's map, on the fixed label universe. Vertices outside known h are isolated.
An edge has a visited endpoint and must have appeared at every visit to either endpoint. -/
def mapGraph (h : List Obs) : SimpleGraph ℕ where
  Adj x y := x ≠ y ∧ x ∈ known h ∧ y ∈ known h ∧
    (x ∈ visited h ∨ y ∈ visited h) ∧
    ∀ o ∈ h, (o.own = x → y ∈ neighborIDs o) ∧ (o.own = y → x ∈ neighborIDs o)
  symm.symm := by
    intro x y hxy
    exact ⟨hxy.1.symm, hxy.2.2.1, hxy.2.1, hxy.2.2.2.1.symm,
      fun o ho => ⟨(hxy.2.2.2.2 o ho).2, (hxy.2.2.2.2 o ho).1⟩⟩
  loopless.irrefl := by intro x hx; exact hx.1 rfl

/-- Infinity, rather than zero, when the nonempty target set is unreachable.
On an empty target set the paper explicitly sets the potential to zero. -/
noncomputable def potential {V : Type} (H : SimpleGraph V) (v : V) (U : Finset V) : ℕ∞ := by
  classical
  exact if U = ∅ then 0 else ⨅ u ∈ U, H.edist v u

noncomputable def dcur (h : List Obs) : ℕ∞ :=
  potential (mapGraph h) (current h).own (targets h)

/-- The analysis map is a graph on the original carrier V, with unknown vertices
isolated. It is the pullback of the observation-only label map. -/
noncomputable def worldMapGraph {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) :
    SimpleGraph V := (mapGraph (history W A t)).comap W.labels

noncomputable def worldKnown {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) :
    Finset V := by
  classical
  exact Finset.univ.filter fun v => W.labels v ∈ known (history W A t)

noncomputable def worldVisited {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) :
    Finset V := by
  classical
  exact Finset.univ.filter fun v => W.labels v ∈ visited (history W A t)

noncomputable def worldTargets {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) :
    Finset V := by
  classical
  exact worldKnown W A t \ worldVisited W A t

noncomputable def worldDcur {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) : ℕ∞ :=
  potential (worldMapGraph W A t) (state W A t).position (worldTargets W A t)

/-- Every first step of every shortest path to every closest target, with its
currently observed local port. No graph data besides this history is consulted. -/
noncomputable def greedyOptions (h : List Obs) : Finset (ℕ × ℕ) := by
  classical
  exact (current h).neighbors.filter fun up =>
    (mapGraph h).Adj (current h).own up.1 ∧ dcur h ≠ ⊤ ∧
    ∃ w ∈ targets h, (mapGraph h).edist (current h).own w = dcur h ∧
      (mapGraph h).edist up.1 w + 1 = dcur h

/-- Algorithm 1 with arbitrary deterministic tie resolution. The fallback port 0
only totalizes malformed/disconnected histories; it causes failure in the run model.
On common-tree executions a target is always reachable until termination. -/
def IsGreedyAlgorithm (A : Alg) : Prop :=
  ∀ h, if targets h = ∅ then A h = none
    else if (greedyOptions h).Nonempty then
      ∃ up ∈ greedyOptions h, A h = some up.2
    else A h = some 0

/-- One observation-only deterministic resolution, used as a possible goal witness.
Milestones quantify over IsGreedyAlgorithm, rather than fixing this resolution. -/
noncomputable def GreedyExp1 : Alg := fun h => by
  classical
  exact if targets h = ∅ then none else
    if hp : (greedyOptions h).Nonempty then
      some (((greedyOptions h).image Prod.snd).min' (hp.image Prod.snd)) else some 0

end IntervalExplore.KT1


