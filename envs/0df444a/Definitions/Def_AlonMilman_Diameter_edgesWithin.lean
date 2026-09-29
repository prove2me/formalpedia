-- Prove2me | Definitions.Def_AlonMilman_Diameter_edgesWithin
-- name    : AlonMilman_Diameter_edgesWithin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:24:57.955188+00:00
-- url     : https://prove2.me/theorems/ccf31210-4b7e-4ea7-a752-6d5eeccbdd8c
-- title:
--   $E_A$: the edges of $G$ with both endpoints in $A$
-- statement:
--   Let $G = (V, E)$ be a finite simple graph and $A \subseteq V$. The set
--   $$
--   E_A = \{\, e = \{u, v\} \in E : u \in A \text{ and } v \in A \,\}
--   $$
--   consists of the edges of $G$ with both endpoints in $A$. The number $|E| - |E_A| - |E_B|$ of edges not lying inside $A$ or inside $B$ is the edge count that controls $\lambda_1$ in Lemma 2.1.
--
--   **Formalization Note** Edges are unordered pairs (`Sym2 V`); $E_A$ is `G.edgeFinset ∩ A.sym2`, where `A.sym2` is the finset of unordered pairs with both entries in $A$. The file also contains the characterization lemma `mem_edgesWithin` (an edge lies in $E_A$ iff every endpoint lies in $A$).
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 77, Section 2 (before Lemma 2.1: definition of E_A, E_B)

import Mathlib

namespace AlonMilman.Diameter

/-- `E_A`: the set of edges of `G` with both endpoints in `A`. -/
def edgesWithin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset ∩ A.sym2

theorem mem_edgesWithin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (e : Sym2 V) :
    e ∈ edgesWithin G A ↔ e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ A := by
  simp [edgesWithin, Finset.mem_sym2_iff]

end AlonMilman.Diameter


