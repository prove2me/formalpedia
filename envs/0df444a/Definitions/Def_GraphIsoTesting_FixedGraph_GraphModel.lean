-- Prove2me | Definitions.Def_GraphIsoTesting_FixedGraph_GraphModel
-- name    : GraphIsoTesting_FixedGraph_GraphModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:27:49.832272+00:00
-- url     : https://prove2.me/theorems/8766a858-79d8-4528-94fc-f71157835d62
-- title:
--   Unordered edge distance, incidence access, and two-sided graph testing
-- statement:
--   Let $G,H$ be finite undirected simple graphs on the same vertex set $V$. For a vertex bijection $\pi$, define
--
--   $$\Delta_{G,H}(\pi)=|\pi(E(G))\mathbin{\triangle}E(H)|,\qquad
--   \operatorname{dist}_{\rm iso}(G,H)=\min_\pi\Delta_{G,H}(\pi).$$
--
--   Each unordered edge is counted once. The permutation set is finite and contains the identity, so the minimum is attained even for an empty vertex set. The degree bound $d$ means every vertex has at most $d$ neighbors. An incidence oracle returns an optional neighbor for a vertex and a port: distinct neighbors occupy exactly the first degree-many ports, in an arbitrary fixed order, and all remaining ports return null. Null is distinct from every vertex label.
--
--   For graphs on $n$ vertices, a tester for the known target $H$ must, for every input graph of maximum degree at most $d$ and every valid oracle, accept each isomorphic input with probability at least $2/3$ and reject each input satisfying
--
--   $$\operatorname{dist}_{\rm iso}(G,H)>\varepsilon nd/2$$
--
--   with probability at least $2/3$. No condition is imposed at equality or on the intermediate inputs. This interface supplies the full two-sided testing problem, with a worst-case query cap from the tree type. Vertices and ports use zero-based finite indices; the real threshold uses no truncated division.
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), pp. 1–2, bounded-degree model, distance, and tester definitions

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_QueryModel

namespace GraphIsoTesting.FixedGraph

/-- Count each unordered edge once after transporting the first graph by a bijection. -/
noncomputable def edgeMismatch {V : Type} [Fintype V]
    (G H : SimpleGraph V) (π : Equiv.Perm V) : ℕ := by
  classical
  let transported := G.edgeFinset.image (Sym2.map π)
  exact ((transported \ H.edgeFinset) ∪ (H.edgeFinset \ transported)).card

/-- A genuine minimum: the finite set of permutations always contains the identity. -/
noncomputable def isoDistance {V : Type} [Fintype V]
    (G H : SimpleGraph V) : ℕ := by
  classical
  exact Finset.univ.inf' Finset.univ_nonempty (edgeMismatch G H)

noncomputable def vertexDegree {V : Type} [Fintype V]
    (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (G.neighborFinset v).card

noncomputable def DegreeBound {V : Type} [Fintype V]
    (G : SimpleGraph V) (d : ℕ) : Prop := by
  classical
  exact ∀ v, (G.neighborFinset v).card ≤ d

abbrev IncidenceOracle (V : Type) (d : ℕ) := V × Fin d → Option V

/-- Arbitrarily ordered distinct neighbors, occupying exactly an initial segment of ports. -/
def ValidOracle {V : Type} (G : SimpleGraph V) (d : ℕ)
    (oracle : IncidenceOracle V d) : Prop :=
  ∀ v, ∃ r : ℕ, r ≤ d ∧
    (∀ p : Fin d, oracle (v, p) ≠ none ↔ p.val < r) ∧
    (∀ u, G.Adj v u ↔ ∃ p : Fin d, oracle (v, p) = some u) ∧
    (∀ (p p' : Fin d) (u : V), oracle (v, p) = some u →
      oracle (v, p') = some u → p = p')

/-- Two-sided success for every graph of the degree bound and every valid port ordering. -/
noncomputable def IsGraphTester {n q : ℕ} (H : SimpleGraph (Fin n))
    (d : ℕ) (ε : ℝ)
    (T : RandomizedTester (Fin n × Fin d) (Option (Fin n)) q) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) (oracle : IncidenceOracle (Fin n) d),
    DegreeBound G d → ValidOracle G d oracle →
    (Nonempty (G ≃g H) → (2 / 3 : ENNReal) ≤ outputProbability T oracle true) ∧
    (ε * (n : ℝ) * (d : ℝ) / 2 < (isoDistance G H : ℝ) →
      (2 / 3 : ENNReal) ≤ outputProbability T oracle false)

end GraphIsoTesting.FixedGraph


