-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
-- name    : OAI_Combinatorics_Hamiltonian_Contraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:39:39.837249+00:00
-- url     : https://prove2.me/theorems/1d7f3f98-9b57-4eef-9093-a16272e3a31d
-- title:
--   Contracted networks from induced dual subnetworks, region rims and three-edge cuts
-- statement:
--   This file defines the minor of a network obtained by keeping the edges induced by a set of dual vertices and contracting all other edges, counting functions on its vertices (the regions), and two edge-connectivity conditions.
--
--   **Setting.** A network with vertex set $V$ and edge set $E$ assigns to each edge $e$ a tail and a head in $V$; its graph joins two distinct vertices when some edge runs between them. Let $N$ be a network on $V$ and $D$ a network on $F$ with the same edge set $E$, all three sets finite (in the application $D$ is a dual of $N$). Fix $U\subseteq F$ and a predicate "black" on $V$. For $S\subseteq V$, the cut $\partial_N S$ is the set of edges with exactly one endpoint in $S$.
--
--   1. **Induced dual edges and subnetwork.** $E_U=\{e\in E:\operatorname{tail}_D(e)\in U\text{ and }\operatorname{head}_D(e)\in U\}$, and $D[U]$ is the network on $U$ with edge set $E_U$ and endpoints given by $D$.
--   2. **Regions.** Deleting $E_U$ from $N$ gives the network $N\setminus E_U$ on $V$ with edge set $E\setminus E_U$. Its connected components are the *regions* of $U$, and the shore $V_q\subseteq V$ of a region $q$ is its set of vertices.
--   3. **The contracted network.** $N/U$ has the regions as vertices and $E_U$ as edge set; the edge $e$ runs from the region containing $\operatorname{tail}_N(e)$ to the region containing $\operatorname{head}_N(e)$. Equivalently, $N/U$ arises from $N$ by contracting every edge outside $E_U$; it may have loops.
--   4. **Colour sign, rims and balance.** Let $\chi(v)=1$ if $v$ is black and $\chi(v)=-1$ otherwise, and let $[\,\cdot\,]$ be $1$ if the condition holds and $0$ otherwise. For a region $q$,
--   $$
--   \operatorname{rim}(q)=\sum_{e\in E_U}\Bigl([\operatorname{tail}_N(e)\in V_q]+[\operatorname{head}_N(e)\in V_q]\Bigr),\qquad \operatorname{bal}(q)=\sum_{v\in V_q}\chi(v).
--   $$
--   Thus $\operatorname{rim}(q)$ is the degree of $q$ in $N/U$ (loops counted twice) and $\operatorname{bal}(q)$ is the number of black minus the number of non-black vertices of $q$. The black rim of $q$ is the same sum as $\operatorname{rim}(q)$ but counts only endpoints that lie in $V_q$ and are black.
--   5. **Three-edge-connectivity.** $N$ is three-edge-connected if $|\partial_N S|\ge 3$ for every $S\subseteq V$ with $S\ne\emptyset$ and $S\ne V$.
--   6. **Trivial three-cuts.** $N$ has only trivial three-cuts if every $S\subseteq V$ with $|\partial_N S|=3$ satisfies $|S|=1$ or $|V\setminus S|=1$.
--
--   Passing from $D$ to the induced subnetwork $D[U]$ corresponds on the primal side to the contraction $N/U$; this is the sense in which these objects are contraction and deletion minors of a dual pair. Rims, black rims and balances are the local counts compared across this correspondence, and conditions 5 and 6 are the connectivity hypotheses for the reduction along three-edge cuts; condition 6 says that every three-edge cut separates a single vertex from the rest.
--
--   **Formalization Note** Regions are the `ConnectedComponent`s of the graph of `N.regions D U`, which is `N` restricted to the subtype of edges outside `inducedEdges U`; `regionQuotient` is `mapVertices` by the component map followed by restriction to `inducedEdges U`. The colouring is an arbitrary predicate, decided classically; rims are natural numbers and the balance is an integer. The membership simp lemmas `mem_inducedEdges` and `mem_regionShore` are included.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Contraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Contraction.lean by skeleton subtraction
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

namespace OAI

/-! Contraction and deletion of finite oriented dual networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def inducedEdges (U : Finset F) : Finset E :=
  Finset.univ.filter fun e => D.tail e ∈ U ∧ D.head e ∈ U

omit [Fintype F] in
@[simp] lemma mem_inducedEdges (U : Finset F) (e : E) :
    e ∈ D.inducedEdges U ↔ D.tail e ∈ U ∧ D.head e ∈ U := by
  simp [inducedEdges]

def inducedNetwork (U : Finset F) : Network U (D.inducedEdges U) where
  tail e := ⟨D.tail e.val,((D.mem_inducedEdges U e.val).mp e.property).1⟩
  head e := ⟨D.head e.val,((D.mem_inducedEdges U e.val).mp e.property).2⟩

def regions (U : Finset F) : Network V {e // e ∉ D.inducedEdges U} :=
  N.restrict Subtype.val

abbrev Regions (U : Finset F) := (N.regions D U).Components

def regionQuotient (U : Finset F) : Network (N.Regions D U) (D.inducedEdges U) :=
  (N.mapVertices (N.regions D U).componentMap).restrict Subtype.val

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def colorSign (black : V → Prop) (v : V) : ℤ := if black v then 1 else -1

def regionShore (U : Finset F) (q : N.Regions D U) : Finset V :=
  Finset.univ.filter fun v => (N.regions D U).componentMap v = q

omit [Fintype F] in
@[simp] lemma mem_regionShore (U : Finset F) (q : N.Regions D U) (v : V) :
    v ∈ N.regionShore D U q ↔ (N.regions D U).componentMap v = q := by
  simp [regionShore]

def rim (U : Finset F) (q : N.Regions D U) : ℕ :=
  ∑ e ∈ D.inducedEdges U, ((if N.tail e ∈ N.regionShore D U q then 1 else 0) +
    (if N.head e ∈ N.regionShore D U q then 1 else 0))

def blackRim (black : V → Prop) (U : Finset F) (q : N.Regions D U) : ℕ :=
  ∑ e ∈ D.inducedEdges U, ((if N.tail e ∈ N.regionShore D U q ∧ black (N.tail e) then 1 else 0) +
    (if N.head e ∈ N.regionShore D U q ∧ black (N.head e) then 1 else 0))

def regionBalance (black : V → Prop) (U : Finset F) (q : N.Regions D U) : ℤ :=
  ∑ v ∈ N.regionShore D U q, colorSign black v

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def ThreeEdgeConnected : Prop := ∀ A : Finset V, A.Nonempty → Aᶜ.Nonempty → 3 ≤ (N.cut A).card

def TrivialThreeCuts : Prop := ∀ A : Finset V, (N.cut A).card = 3 → A.card = 1 ∨ Aᶜ.card = 1

end
end Barnette.Network

end OAI


