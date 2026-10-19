-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
-- name    : OAI_Combinatorics_Hamiltonian_Matching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:44:32.758167+00:00
-- url     : https://prove2.me/theorems/f262e95e-de35-4beb-aa63-9ff5a91373e7
-- title:
--   Third-corner networks of paired states with two root edges, and their removed edge sets
-- statement:
--   **Setting.** A network on a vertex set $W$ with edge set $K$ assigns to every edge a tail and a head in $W$. $N$ and $D$ are networks on finite vertex sets $V$ and $F$ with a common finite edge set $E$: every edge has a tail and a head in $V$ (for $N$) and in $F$ (for $D$), and the graph of a network joins two distinct vertices when some edge runs between them. A colored dual structure on $(N,D)$ records that $N$ and $D$ are connected, simple and mutually dual (the cycle space of each equals the cut space of the other), that $N$ is cubic with a black/white colouring in which every edge has exactly one black endpoint, and it assigns to each $v\in V$ a triangle $\Delta_v$ of $D$ with distinct corners $c_v(0),c_v(1),c_v(2)\in F$ (indices in $\mathbb{Z}/3$) whose three sides are exactly the edges of $N$ at $v$, the side with index $k$ joining $c_v(k)$ and $c_v(k+1)$, with compatible orientations in $N$ and $D$. For a root $v_0\in V$ let $B$ be the set of black vertices other than $v_0$, and $F^\circ=F\setminus\{c_{v_0}(0),c_{v_0}(1),c_{v_0}(2)\}$. A *state* is a map $s:B\to\mathbb{Z}/3$ such that $t\mapsto c_t(s(t))$ is a bijection from $B$ onto $F^\circ$. For $j\ne k$ let $\operatorname{side}_v(j,k)\in E$ be the side of $\Delta_v$ joining $c_v(j)$ and $c_v(k)$. A *pair* $P=(\ell,\rho)$ is an ordered pair of states with $\ell(t)\ne\rho(t)$ for all $t\in B$, and $\theta_P(t)=-(\ell(t)+\rho(t))\in\mathbb{Z}/3$ is the index of the corner of $\Delta_t$ used by neither state. Finally fix $i\in\mathbb{Z}/3$.
--
--   1. **Adding a sink.** For a network $Q$ on $W$ with edge set $K$, vertices $r_0,r_1\in W$ and a vertex $x\in W$, the network $Q+_x(r_0,r_1)$ has edge set $K\sqcup\{0,1\}$: it keeps the edges of $Q$ and adds, for $j=0,1$, a new edge from $r_j$ to $x$.
--   2. **The third-corner network of a pair.** $Q_P$ is the network on $F$ with edge set $B$ in which the edge $t$ runs from $c_t(\ell(t))$ to $c_t(\theta_P(t))$. The label of $t$ is $\operatorname{lab}_P(t)=\operatorname{side}_t(\ell(t),\theta_P(t))\in E$, the side of $\Delta_t$ joining these two corners, which is one of the three edges of $N$ at $t$.
--   3. **Augmentation at the root.** With $\operatorname{rs}(i,j)=i+j$ for $j\in\{0,1\}$,
--   $$
--   Q_P^{(i)}=Q_P+_{c_{v_0}(i+2)}\bigl(c_{v_0}(i),\,c_{v_0}(i+1)\bigr),
--   $$
--   that is, $Q_P$ together with an edge from $c_{v_0}(i)$ and an edge from $c_{v_0}(i+1)$ to $c_{v_0}(i+2)$. Its edges are labelled by $\operatorname{lab}_P$ on $B$ and by $\operatorname{side}_{v_0}(i+j,\,i+2)$ on the new edge $j$.
--   4. **Removed edges.** $R_P^{(i)}\subseteq E$ is the set of all these labels:
--   $$
--   R_P^{(i)}=\{\operatorname{lab}_P(t): t\in B\}\cup\{\operatorname{side}_{v_0}(i,i+2),\ \operatorname{side}_{v_0}(i+1,i+2)\}.
--   $$
--
--   Thus $R_P^{(i)}$ consists of the edge $\operatorname{lab}_P(t)$ at each black vertex $t\ne v_0$ and two edges at the root. In the module, when the opposite graph of the right state $\rho$ is acyclic, the augmented network is used to show that the edges of $R_P^{(i)}$ form an acyclic subgraph of $D$; by duality the remaining edges of $N$ then form a connected spanning subgraph. This is the starting point for extracting perfect matchings of $N$ with connected complement.
--
--   **Formalization Note** States and pairs are those of the triangle system `M.system root` on the point set `M.nonroots root`. The Lean names are `addSink`, `QNet`, `qLabel`, `rootStart`, `augQ`, `augLabel` and `removed`; the new edges are indexed by `Fin 2` (cast into `Fin 3` by `rootStart`), and `removed` is the image of `augLabel` as a finite set. The side function of a triangle is `if k = j+1 then edge j else edge k`, which for $j\ne k$ is the side joining corners $j$ and $k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Matching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Matching.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Disk and spoke signs and matching complements. -/

namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

variable {F : Type*} [Fintype F] (D : Network F E)
end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V A : Type*} (Q : Network V A)

def addSink (r : Fin 2 → V) (z : V) : Network V (A ⊕ Fin 2) where
  tail := Sum.elim Q.tail r
  head := Sum.elim Q.head (fun _ => z)

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
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

abbrev QNet (P : (M.system root).Pair (M.nonroots root)) : Network F (M.Black root) where
  tail t := P.left.value t
  head t := (M.face t.val).corner (thirdIndex (P.left.val t) (P.right.val t))

def qLabel (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) : E :=
  (M.face t.val).side D (P.left.val t) (thirdIndex (P.left.val t) (P.right.val t))

def rootStart (i : Fin 3) (j : Fin 2) : Fin 3 := i + j.castLE (by decide)

abbrev augQ (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3) :
    Network F (M.Black root ⊕ Fin 2) :=
  (M.QNet P).addSink (fun j => (M.face root).corner (rootStart i j)) ((M.face root).corner (i+2))

def augLabel (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3) :
    M.Black root ⊕ Fin 2 → E :=
  Sum.elim (M.qLabel P) (fun j => (M.face root).side D (rootStart i j) (i+2))

def removed (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3) : Finset E :=
  Finset.univ.image (M.augLabel P i)

end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (D : Network V E)

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

end
end Barnette.Network.ColoredDual

end OAI


