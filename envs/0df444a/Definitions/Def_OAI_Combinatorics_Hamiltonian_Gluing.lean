-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
-- name    : OAI_Combinatorics_Hamiltonian_Gluing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:48:37.576438+00:00
-- url     : https://prove2.me/theorems/ef68f5d4-7030-473e-9d0c-08410d112c83
-- title:
--   Decidable equality on the edge sets of capped networks
-- statement:
--   Let $N$ be a network on a finite vertex set $V$ with finite edge set $E$ (each edge has a tail and a head in $V$), and for $S\subseteq V$ let
--   $$
--   E(S)=\{e\in E:\ \operatorname{tail}(e)\in S\ \text{or}\ \operatorname{head}(e)\in S\}
--   $$
--   be the set of edges with at least one endpoint in $S$. This is the edge set of the capped network $N^S$, obtained from $N$ by contracting $V\setminus S$ to a single new vertex and discarding the edges with no endpoint in $S$.
--
--   The definitions of this module are pure plumbing: three local instances, one for each section of the module, equip the finite type $E(S)$ with decidable equality, chosen classically, so that finite sets of edges of capped networks (for instance perfect matchings of $N^S$) can be formed and compared.
--
--   The module glues perfect matchings of the two capped sides of a three-edge cut that agree on the cut, and runs a strong induction over three-edge cuts. Its main result states that if $N$ is simple, cubic and three-edge-connected, has a dual network $D$ (both connected, the cycle space of each equal to the cut space of the other) and a black/white colouring in which every edge has exactly one black endpoint, then every edge of $N$ lies in a perfect matching whose complementary edges form a connected spanning subgraph.
--
--   **Formalization Note** The instances are `capMatchingEq`, `capReachableEq` and `unrestrictedInductionEq`, each of the form `DecidableEq (N.regionEdges A) := Classical.decEq _` with high priority, local to its section.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Gluing.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Gluing.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts

namespace OAI

/-! Compatible boundary matchings and strong induction over three-edge cuts. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
local instance (priority := high) capMatchingEq (A : Finset V) :
    DecidableEq (N.regionEdges A) := Classical.decEq _

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
local instance (priority := high) capReachableEq (A : Finset V) :
    DecidableEq (N.regionEdges A) := Classical.decEq _

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
universe uV uE uF
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] (N : Network V E)
local instance (priority := high) unrestrictedInductionEq (A : Finset V) :
    DecidableEq (N.regionEdges A) := Classical.decEq _

variable {F : Type uF} [Fintype F] (D : Network F E)

end
end Barnette.Network

end OAI


