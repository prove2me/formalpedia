-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_ExactDual
-- name    : OAI_Combinatorics_Hamiltonian_ExactDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:04:01.444001+00:00
-- url     : https://prove2.me/theorems/03aa5954-718a-4cd5-a137-a1d6daadf814
-- title:
--   Networks realizing a simple graph
-- statement:
--   Let $G$ be a simple graph on a vertex set $V$; its edges are unordered pairs $\{v,w\}$ of distinct adjacent vertices, and $E(G)$ denotes the set of edges. A *network* with vertex set $V$ and edge set $E(G)$ is a pair of maps $\mathrm{tail},\mathrm{head}:E(G)\to V$. Such a network $M$ *realizes* $G$ if every edge runs between its own two endpoints:
--
--   $$\{\mathrm{tail}(e),\mathrm{head}(e)\}=e\qquad\text{for every } e\in E(G).$$
--
--   Equivalently, $M$ is an orientation of $G$: for each edge $\{v,w\}$ it declares one endpoint to be the tail and the other to be the head. Consequently a realizing network has no loops, and its underlying graph (in which distinct $x,y$ are adjacent iff some edge has endpoint pair $\{x,y\}$) is $G$ itself.
--
--   Realization is the interface between abstract graphs and the linear algebra of networks. For a network with finite edge set $E$ and vertex set $X$, the gradient of $f:X\to\mathbb{R}$ is $(\nabla f)(e)=f(\mathrm{head}\,e)-f(\mathrm{tail}\,e)$ and the boundary of $x:E\to\mathbb{R}$ is $(\partial x)(p)=\sum_{\mathrm{head}(e)=p}x_e-\sum_{\mathrm{tail}(e)=p}x_e$. The notion is used to express that a connected finite plane graph $G$ has an exact dual: a network $P$ realizing $G$ and a network $D$ on a finite set of faces, with the same edge set $E(G)$, such that the underlying graphs of $P$ and $D$ are connected and $\ker\partial_P=\operatorname{im}\nabla_D$, $\ker\partial_D=\operatorname{im}\nabla_P$.
--
--   **Formalization Note** The definition is `Network.Realizes G M` for `M : Network V G.edgeSet`. Edges of $G$ are elements of the subtype `G.edgeSet` of Mathlib's unordered pairs `Sym2 V`, and the condition reads `s(M.tail e, M.head e) = e.val` for every `e`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ExactDual.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ExactDual.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_SquareGrid
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Corridors
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorModel
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Rectangle

namespace OAI

/-! Graph realization and exact finite duality for topological plane embeddings. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V W E : Type*} [Fintype V] [Fintype W] [Fintype E]

def Realizes (G : SimpleGraph V) (M : Network V G.edgeSet) : Prop :=
  ∀ e, s(M.tail e, M.head e) = e.val

universe uF
variable {F : Type uF} [Fintype F]

end
end Barnette.Network

namespace Barnette.PlaneEmbedding
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

end
end Barnette.PlaneEmbedding

end OAI


