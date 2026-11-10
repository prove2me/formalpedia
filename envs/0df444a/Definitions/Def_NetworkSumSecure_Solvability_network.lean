-- Prove2me | Definitions.Def_NetworkSumSecure_Solvability_network
-- name    : NetworkSumSecure_Solvability_network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:02:11.635139+00:00
-- url     : https://prove2.me/theorems/7b37fd9d-912c-479c-b41e-259d9a08314f
-- title:
--   Directed sum-computation networks, cuts, paths and field threshold
-- statement:
--   A network $N$ has finite vertex, edge and user index sets $V,E,U$. Every edge has a tail and a head; distinct edges may have the same endpoints. The directed graph is acyclic. Distinct users $\sigma_i$ differ from the server $\rho$, users have no incoming edges, the server has no outgoing edges, and every nonserver vertex has a nonempty directed path to $\rho$.
--
--   A user-to-server path is a nonempty composable list of actual edges. An edge cut meets every such path. Write $c(N)$ for the minimum size of an edge cut, and $\mathcal W_r$ for all subsets of $E$ of size at most $r$. Then the field threshold used below is
--
--   $$Q_0(N,r)=|U|+|\mathcal W_r|+1.$$
--
--   The full edge set is a cut, so the finite minimum is always defined, including when $U$ is empty. A family of $n$ edge-disjoint paths may share vertices and endpoints. The topological edge traversal contains each edge once and places every incoming edge before an outgoing edge at the same vertex.
--
--   This layer keeps graph conditions independent of encoders. The published general multigraph carrier supplies only tail and head maps; its routing-specific quantities are unused.
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), pp. 5–6 (PDF pp. 7–8); p. 16 (PDF p. 18); p. 23 (PDF p. 25), §2.1; equations (34), (53)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network

open scoped BigOperators

namespace NetworkSumSecure.Solvability

/-! Bai–Guang–Wang, STOC 2027 submission #1291, §2.1, printed pp.5–6 (PDF 7–8).
The general directed multigraph carrier is reused without routing assumptions.
The imported `longest` function is not used. -/

/-- The source network assumptions; finiteness is imposed by the surrounding types. -/
structure Network (V E U : Type) where
  graph : AtomicDynRouting.ResidenceTime.Network V E
  acyclic : graph.Acyclic
  user : U → V
  users_distinct : Function.Injective user
  server : V
  user_ne_server : ∀ i, user i ≠ server
  no_user_input : ∀ i e, graph.head e ≠ user i
  no_server_output : ∀ e, graph.tail e ≠ server
  reaches_server : ∀ v, v ≠ server →
    ∃ p : List E, p ≠ [] ∧ graph.IsPathFrom v server p

variable {V E U : Type}

/-- A nonempty path of actual edge identities from one user to the server. -/
structure UserPath (N : Network V E U) where
  start : U
  edges : List E
  nonempty : edges ≠ []
  follows : N.graph.IsPathFrom (N.user start) N.server edges

def UserPath.first {N : Network V E U} (p : UserPath N) : E := p.edges.head p.nonempty
def UserPath.last {N : Network V E U} (p : UserPath N) : E := p.edges.getLast p.nonempty

/-- Edge disjointness permits common vertices, common sources and the common server. -/
def EdgeDisjoint {N : Network V E U} {n : ℕ} (Q : Fin n → UserPath N) : Prop :=
  ∀ j k, j ≠ k → ∀ e, e ∈ (Q j).edges → e ∉ (Q k).edges

/-- Exactly `n` paths suffice to express existence of at least `n` disjoint paths. -/
def HasPaths (N : Network V E U) (n : ℕ) : Prop :=
  ∃ Q : Fin n → UserPath N, EdgeDisjoint Q

/-- A cut meets every nonempty user-to-server path. -/
def IsCut (N : Network V E U) (C : Finset E) : Prop :=
  ∀ p : UserPath N, ∃ e ∈ p.edges, e ∈ C

/-- Minimum over the actual finite cut family. The full edge set is always a cut,
so this definition has no empty-infimum convention. -/
noncomputable def mincut [Fintype E] (N : Network V E U) : ℕ := by
  classical
  let cuts := Finset.univ.powerset.filter (IsCut N)
  have full : IsCut N (Finset.univ : Finset E) := by
    intro p
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges p.nonempty
    exact ⟨e, he, Finset.mem_univ e⟩
  have hc : (Finset.univ : Finset E) ∈ cuts := by simp [cuts, full]
  exact (cuts.image Finset.card).min' ⟨_, Finset.mem_image.mpr ⟨_, hc, rfl⟩⟩

noncomputable def incoming [Fintype E] (N : Network V E U) (v : V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => N.graph.head e = v)

noncomputable def wiretapSets [Fintype E] (r : ℕ) : Finset (Finset E) := by
  classical
  exact Finset.univ.powerset.filter (fun W => W.card ≤ r)

/-- The uniform sufficient field-size witness extracted from (34) and (53). -/
noncomputable def fieldThreshold [Fintype E] [Fintype U] (r : ℕ) : ℕ :=
  Fintype.card U + (wiretapSets (E := E) r).card + 1

/-- A topological edge traversal, without any coding or rank certificates. -/
structure EdgeOrder [Fintype E] (N : Network V E U) where
  edge : Fin (Fintype.card E) ≃ E
  before : ∀ d e, N.graph.head d = N.graph.tail e → edge.symm d < edge.symm e

end NetworkSumSecure.Solvability


