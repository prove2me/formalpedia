-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
-- name    : OAI_Combinatorics_Hamiltonian_MinorDuality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:40:53.612991+00:00
-- url     : https://prove2.me/theorems/9412a076-5a33-4b9f-9659-256630e20d83
-- title:
--   Fully retained black vertices in the regions of a contracted network
-- statement:
--   **Setting.** $N$ is a network on a finite vertex set $V$ and $D$ a network on a finite vertex set $F$, with the same finite edge set $E$; every edge has a tail and a head in $V$ for $N$ and in $F$ for $D$. For $v\in V$, $\operatorname{star}_N(v)$ is the set of edges having $v$ as tail or head, and "black" is a fixed predicate on $V$. For $U\subseteq F$, let $E_U$ be the set of edges whose tail and head in $D$ both lie in $U$. The *regions* of $U$ are the connected components of the graph on $V$ formed by the edges of $N$ outside $E_U$ (two distinct vertices being adjacent when such an edge joins them), and the shore $V_q\subseteq V$ of a region $q$ is its set of vertices. The regions are the vertices of the network obtained from $N$ by contracting all edges outside $E_U$; its edge set is $E_U$.
--
--   1. **Fully retained black vertices.**
--   $$
--   \operatorname{FB}_U=\{v\in V:\ v\text{ is black and }\operatorname{star}_N(v)\subseteq E_U\},
--   $$
--   the black vertices all of whose incident edges survive in the contracted network.
--   2. **Their number in a region.** For a region $q$ of $U$,
--   $$
--   \operatorname{rb}_U(q)=\bigl|\operatorname{FB}_U\cap V_q\bigr|.
--   $$
--
--   Deleting all edges of $D$ outside $E_U$ corresponds to contracting them in $N$, and a vertex of $\operatorname{FB}_U$ keeps its whole star in this minor. Together with the rims and balances of regions, these counts are used in the module to bound the number of edges of the induced dual subnetwork: for a simple cubic three-edge-connected $N$ with only trivial three-cuts, a dual $D$, a proper black/white colouring and a black root whose star lies in $E_U$, one gets $|E_U|-|\operatorname{FB}_U|\le 2|U|-4$.
--
--   **Formalization Note** The Lean names are `fullBlack` (a `Finset V`) and `regionBlack` (a natural number); regions are elements of `N.Regions D U`, the connected components of `N.regions D U`, and the shore is `regionShore`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/MinorDuality.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/MinorDuality.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction

namespace OAI

/-! Exact duality under finite network minors. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def fullBlack (black : V → Prop) (U : Finset F) : Finset V :=
  Finset.univ.filter fun v => black v ∧ N.star v ⊆ D.inducedEdges U

def regionBlack (black : V → Prop) (U : Finset F) (q : N.Regions D U) : ℕ :=
  ((N.fullBlack D black U).filter fun v => v ∈ N.regionShore D U q).card

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

end OAI


