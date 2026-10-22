-- Prove2me | Definitions.Def_QCircMITM_Search_Layers
-- name    : QCircMITM_Search_Layers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:33.796314+00:00
-- url     : https://prove2.me/theorems/3d9ce6c9-d09f-4a6e-962e-60adc2fc33b9
-- title:
--   §2, p. 4 — V_{n,G}, the unitaries of depth-one circuits over an instruction set
-- statement:
--   Let $\mathcal G$ be an instruction set, a set of quantum gates, each a matrix on some number $k$ of qubits. A gate applied to an ordered tuple of $k$ distinct qubits out of $n$ acts as its matrix on those qubits, tensored with the identity on the remaining ones.
--
--   A *depth-one $n$-qubit circuit* over $\mathcal G$ is a nonempty list of such gate applications whose qubit sets are pairwise disjoint. Its unitary is the product of the applied gates. The set of these unitaries is
--   $$\mathcal V_{n,\mathcal G} = \{\, M : M \text{ is the unitary of a depth-one } n\text{-qubit circuit over } \mathcal G \,\}.$$
--
--   A circuit of depth at most $m$ is then a product $U_1U_2\cdots U_m$ of elements of $\mathcal V_{n,\mathcal G}$, which is how the rest of the mission uses this set.
--
--   **Formalization Note.** Gates, gate applications and the unitary of a circuit are the shared QAlgorithms definitions (`QAlgorithms.Gate`, `QAlgorithms.Circuit`, `QAlgorithms.Circuit.unitary`). Since gates in one layer act on disjoint qubits they commute, so the order of the list does not matter. Unitarity of the gates is not built in: it is a hypothesis where it is used.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, p. 4, §2, definition of V_{n,G}

import Definitions.Def_QAlgorithms_Defs_Circuit

namespace QCircMITM.Search

/-- `V_{n,G}` (§2, p. 4): the set of unitaries of depth-one `n`-qubit circuits over the
instruction set `G`, i.e. of nonempty circuits over `G` whose gates act on pairwise disjoint sets
of qubits (each gate tensored with the identity on the remaining qubits). -/
def depthOneSet (G : Set QAlgorithms.Gate) (n : ℕ) :
    Set (Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ) :=
  {M | ∃ c : QAlgorithms.Circuit G n, c ≠ [] ∧
        c.Pairwise (fun g h => Disjoint (Set.range g.wires) (Set.range h.wires)) ∧
        M = c.unitary}

end QCircMITM.Search


