-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
-- name    : OAI_Combinatorics_Hamiltonian_ForestMatching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:47:10.027991+00:00
-- url     : https://prove2.me/theorems/9be75397-f69e-4842-9f35-d441dd82733a
-- title:
--   Reversed cycle coordinates, perfect-matching edges and state-selected dual networks
-- statement:
--   **Colored dual setting** (used in item 3). $N$ and $D$ are networks on finite vertex sets $V$ and $F$ with a common finite edge set $E$: every edge has a tail and a head in $V$ (for $N$) and in $F$ (for $D$), and the graph of a network joins two distinct vertices when some edge runs between them. A colored dual structure on $(N,D)$ records that $N$ and $D$ are connected, simple and mutually dual (the cycle space of each equals the cut space of the other), that $N$ is cubic with a black/white colouring in which every edge has exactly one black endpoint, and it assigns to each $v\in V$ a triangle $\Delta_v$ of $D$ with distinct corners $c_v(0),c_v(1),c_v(2)\in F$ (indices in $\mathbb{Z}/3$) whose three sides are exactly the edges of $N$ at $v$, the side with index $k$ joining $c_v(k)$ and $c_v(k+1)$, with compatible orientations in $N$ and $D$. For a root $v_0\in V$ let $B$ be the set of black vertices other than $v_0$, and $F^\circ=F\setminus\{c_{v_0}(0),c_{v_0}(1),c_{v_0}(2)\}$. A *state* is a map $s:B\to\mathbb{Z}/3$ such that $t\mapsto c_t(s(t))$ is a bijection from $B$ onto $F^\circ$. For $v\in V$, $\operatorname{star}_N(v)$ is the set of edges having $v$ as tail or head; for an edge $e$ and $x\in F$, $\operatorname{oe}_D(e,x)$ is $\operatorname{head}_D(e)$ if $\operatorname{tail}_D(e)=x$ and $\operatorname{tail}_D(e)$ otherwise, so it is the other endpoint of $e$ in $D$ when $x$ is an endpoint.
--
--   1. **Reversed cycles.** Let $G$ be a simple graph. Cycle coordinates in $G$ consist of $n\in\mathbb{N}$ and an injective map $y:\mathbb{Z}/(n+3)\to V(G)$ such that $y(k)$ and $y(k+1)$ are adjacent for every $k$. The reversed coordinates have the same $n$ and
--   $$
--   \bar y(k)=y(-k)\qquad(k\in\mathbb{Z}/(n+3)),
--   $$
--   which are again cycle coordinates in $G$: the same cycle traversed backwards.
--   2. **The matching edge at a vertex.** Let $N$ be a network with finite edge set $E$ and let $P\subseteq E$ satisfy $|\operatorname{star}_N(v)\cap P|=1$ for every vertex $v$, i.e. $P$ is a perfect matching. Then $m_P(v)$ denotes the unique edge of $P$ at $v$.
--   3. **The network selected by a state and a matching.** For a state $s$ and a perfect matching $P$ of $N$ as in 2, $\operatorname{Sel}(s,P)$ is the network on $F$ with edge set $B$ in which the edge $t$ runs
--   $$
--   \text{from } c_t(s(t))\ \text{ to }\ \operatorname{oe}_D\bigl(m_P(t),\,c_t(s(t))\bigr).
--   $$
--   Since $m_P(t)$ is an edge of $N$ at $t$, it is a side of $\Delta_t$; when $c_t(s(t))$ is one of its ends, the edge $t$ of $\operatorname{Sel}(s,P)$ runs along this side to the other end.
--
--   These tools serve the passage from forests to perfect matchings with connected complement. In the module, the selected network is shown to be acyclic when every $m_P(t)$ is incident in $D$ to $c_t(s(t))$, and this is used to show that the dual edges of $P$ form a forest in $D$; reversing cycle coordinates is used to orient a cycle consistently with the edges of a network. Combined with the removed-edge construction for pairs of states, this gives, for a pair whose right state has an acyclic opposite graph and a black root, a perfect matching of $N$ through a prescribed root edge whose complement is connected.
--
--   **Formalization Note** The Lean names are `reverseCycle` (an `abbrev` on `Barnette.CycleCoordinates G`), `matchingEdge` (defined by choice from the cardinality hypothesis) and `selectNet`, whose head uses `D.otherEnd`; states are those of the triangle system `M.system root` on the point set `M.nonroots root`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ForestMatching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ForestMatching.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! From opposite forests to connected spanning matching complements. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

end
end Barnette.Network.ColoredDual
namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
abbrev reverseCycle : Barnette.CycleCoordinates G where
  n := C.n
  vertex := ⟨fun i => C.vertex (-i),fun _ _ h => neg_injective (C.vertex.injective h)⟩
  adjacent i := by
    have hh := (C.adjacent (-i-1)).symm
    change G.Adj (C.vertex (-i)) (C.vertex (-(i+1)))
    rw [sub_add_cancel,show -i-1 = -(i+1) by abel] at hh
    exact hh
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
variable {V E : Type*} (N : Network V E)
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype E] (N : Network V E)

def matchingEdge (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (v : V) : E :=
  (Finset.card_eq_one.mp (hd v)).choose

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

abbrev selectNet (s : M.State root) (P : Finset E)
    (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) : Network F (M.Black root) where
  tail t := s.value t
  head t := D.otherEnd (N.matchingEdge P hd t.val) (s.value t)

end
end Barnette.Network.ColoredDual

end OAI


