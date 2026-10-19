-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
-- name    : OAI_Combinatorics_Hamiltonian_Bonds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:19:57.825402+00:00
-- url     : https://prove2.me/theorems/8382c636-7d9d-49dc-98f9-c7de1366a33e
-- title:
--   Signed cycle flows, bonds, and adjacency of triangle corners
-- statement:
--   Let $N$ be an oriented network with vertex set $V$, edge set $E$ (finite wherever sums or cuts occur), tail map $t$ and head map $h$, and write $\mathbf{1}_e \in \mathbb{R}^E$ for the standard basis vector of an edge $e$.
--
--   1. **Arc sign.** For an edge $e$ and a vertex $v$,
--   $$
--   \sigma_N(e, v) = \begin{cases} 1 & \text{if } t(e) = v, \\ -1 & \text{otherwise.} \end{cases}
--   $$
--   For an edge with endpoints $v \neq w$, it is $+1$ when going from $v$ to $w$ along $e$ follows the orientation of $e$, and $-1$ when it goes against it.
--
--   2. **Signed cycle flow.** Let $C$ be a cycle of length $m \geq 3$ in the underlying simple graph of $N$, given by distinct vertices $v_i$, $i \in \mathbb{Z}/m$, with $v_i$ adjacent to $v_{i+1}$ (indices mod $m$), and let $e_i$ be the chosen edge of $N$ joining $v_i$ and $v_{i+1}$. The cycle flow of $C$ is
--   $$
--   \chi_C = \sum_{i \in \mathbb{Z}/m} \sigma_N(e_i, v_i)\, \mathbf{1}_{e_i} \in \mathbb{R}^E .
--   $$
--   It equals $+1$ on the edges traversed forward and $-1$ on the edges traversed backward when going around $v_0 \to v_1 \to \cdots \to v_{m-1} \to v_0$, and $0$ off the cycle.
--
--   3. **Bond.** For finite $V$ and $E$, a vertex set $A \subseteq V$ is a bond if its cut $\delta(A)$ (the edges with exactly one endpoint in $A$) is nonempty and inclusion-minimal among all cuts:
--   $$
--   \delta(B) \subseteq \delta(A) \quad \Longrightarrow \quad \delta(B) = \emptyset \ \text{ or } \ \delta(B) = \delta(A) \qquad \text{for all } B \subseteq V.
--   $$
--
--   4. **Triangle corners are adjacent.** The file also records that if a network $D$ carries a labelled triangle (distinct corners $c_0, c_1, c_2$ and edges $e_i$ joining $c_i$ to $c_{i+1}$, indices mod $3$), then any two distinct corners $c_i, c_j$ with $i \neq j$ are adjacent in the underlying simple graph of $D$.
--
--   The cycle flow is the circulation naturally attached to a cycle; elsewhere it is shown to be a flow circuit, and under the duality between a network and its dual, flow circuits of one network correspond to bonds of the other. Since bonds of a connected graph have connected shores, this turns cycles of the dual into connected vertex sets of the original graph.
--
--   **Formalization Note** `arcSign`, `cycleFlow` (built from the chosen edges `cycleEdge` and the basis vectors `basisVec`), the `Prop`-valued structure `Bond A` for `A : Finset V`, and the lemma `Triangle.clique`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Bonds.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Bonds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Cycle flows, minimal cuts, and connected shores. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

omit [Fintype V] [Fintype E] in
def arcSign (e : E) (v : V) : ℝ := if N.tail e = v then 1 else -1

omit [Fintype V] [Fintype E] in
def cycleFlow : E → ℝ :=
  ∑ i, N.arcSign (N.cycleEdge C i) (C.vertex i) • basisVec (N.cycleEdge C i)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

structure Bond (A : Finset V) : Prop where
  nonempty : (N.cut A).Nonempty
  minimal : ∀ B, N.cut B ⊆ N.cut A → N.cut B = ∅ ∨ N.cut B = N.cut A

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype E] [Fintype F] in
lemma Triangle.clique {s : Finset E} (t : D.Triangle s) {i j : Fin 3} (hij : i ≠ j) :
    D.graph.Adj (t.corner i) (t.corner j) := by
  have hne : t.corner i ≠ t.corner j := fun h => hij (t.corner_injective h)
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  have h := hfin i j hij
  rcases h with rfl | rfl
  · exact ⟨hne,t.edge i,Sym2.eq_iff.mp (t.edge_ends i)⟩
  · exact ⟨hne,t.edge j,(Sym2.eq_iff.mp (t.edge_ends j)).symm⟩

end
end Barnette.Network

end OAI


