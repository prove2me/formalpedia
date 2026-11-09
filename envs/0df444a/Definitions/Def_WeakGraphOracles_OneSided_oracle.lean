-- Prove2me | Definitions.Def_WeakGraphOracles_OneSided_oracle
-- name    : WeakGraphOracles_OneSided_oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:18.433617+00:00
-- url     : https://prove2.me/theorems/68248eaf-b84c-4918-9afa-f245f6e6e323
-- title:
--   Operational GEN1 and random-neighbor oracles
-- statement:
--   On $n$ known labels, a query asks either for a random edge or for a random neighbor of any specified label $v$. The response kernel for a graph $G$ returns
--
--   $$\Pr[(u,v)\mid\text{edge query}]=\frac{1}{2|E(G)|},\qquad
--   \Pr[w\mid\text{neighbor query at }v]=\frac{1}{\deg_G(v)}$$
--
--   on oriented edges and on neighbors respectively. Edgeless graphs return a distinguished no-edge reply; isolated vertices return an isolation reply. Every response is fresh and independent conditional on the chosen query. Policies receive no degree, adjacency or edge-count access. An arbitrary vertex label can be chosen without having been discovered.
--
--   GEN1 allows both operations. RN allows only the neighbor operation. Internal randomness can sample any vertex label freely because $n$ is public. Execution produces the decision and transcript. Discovery probability for $H$ is the probability that the graph formed by the edges actually returned in that transcript contains an $H$-appearance, independent of whether the policy accepts or rejects. Neither a role map nor a copy collection is passed to the policy.
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 5 (PDF p. 6), §3 oracle models; p. 9 (PDF p. 10), text following Theorem 8; pp. 15–17 (PDF pp. 16–18), §§7.2–7.3

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_protocol
import Definitions.Def_WeakGraphOracles_OneSided_graphs

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

inductive Query (n : ℕ) where
  | randomEdge : Query n
  | randomNeighbor (v : Fin n) : Query n
  deriving DecidableEq

inductive Reply (n : ℕ) where
  | noEdge : Reply n
  | isolated : Reply n
  | neighbor (w : Fin n) : Reply n
  | edge (u v : Fin n) : Reply n
  deriving DecidableEq

abbrev Policy (n q : ℕ) := RandomPolicy (Query n) (Reply n) q

/-- Uniform over oriented edges: the underlying unordered edge is uniform,
with an independent fair orientation. No edge-count or degree information is returned. -/
noncomputable def oracle {n : ℕ} (G : SimpleGraph (Fin n)) : Query n → PMF (Reply n) := by
  classical
  intro a
  cases a with
  | randomEdge =>
      let S := (Finset.univ : Finset (Fin n × Fin n)).filter fun e => G.Adj e.1 e.2
      exact if hs : S.Nonempty then
        (PMF.uniformOfFinset S hs).map (fun e => Reply.edge e.1 e.2)
      else PMF.pure Reply.noEdge
  | randomNeighbor v =>
      let S := (Finset.univ : Finset (Fin n)).filter fun w => G.Adj v w
      exact if hs : S.Nonempty then
        (PMF.uniformOfFinset S hs).map Reply.neighbor
      else PMF.pure Reply.isolated

/-- Oracle restrictions apply on all branches with positive internal probability.
GEN1 uses `edgeAllowed = true`; RN uses false and has no random-edge action. -/
def AllowedTree {n : ℕ} (edgeAllowed : Bool) :
    {q : ℕ} → QueryTree (Query n) (Reply n) q → Prop
  | _, .stop _ => True
  | _, .ask a next => (a = .randomEdge → edgeAllowed = true) ∧
      ∀ r, AllowedTree edgeAllowed (next r)

def ValidPolicy {n q : ℕ} (edgeAllowed : Bool) (A : Policy n q) : Prop :=
  ∀ t ∈ A.support, AllowedTree edgeAllowed t

noncomputable def run {n q : ℕ} (A : Policy n q) (G : SimpleGraph (Fin n)) :=
  executePolicy (oracle G) A

noncomputable def acceptProbability {n q : ℕ} (A : Policy n q)
    (G : SimpleGraph (Fin n)) : ℝ :=
  eventProbability (run A G) (fun out => out.1 = true)

/-- Only edges actually returned by the oracle enter the observed graph.
Isolation and no-edge replies certify no positive edges. -/
def observedEdges {n : ℕ} (t : List (Query n × Reply n)) : Set (Sym2 (Fin n)) :=
  {e | ∃ a r, (a, r) ∈ t ∧
    ((∃ u v, r = .edge u v ∧ e = s(u, v)) ∨
     (∃ v w, a = .randomNeighbor v ∧ r = .neighbor w ∧ e = s(v, w)))}

noncomputable def observedGraph {n : ℕ} (t : List (Query n × Reply n)) :
    SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (observedEdges t)

noncomputable def discoveryProbability {n q : ℕ} (H : Pattern) (A : Policy n q)
    (G : SimpleGraph (Fin n)) : ℝ :=
  eventProbability (run A G) (fun out => Nonempty (Appearance H (observedGraph out.2)))

end WeakGraphOracles.OneSided


