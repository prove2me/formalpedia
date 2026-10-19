-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
-- name    : OAI_Combinatorics_Hamiltonian_ThreeCuts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:47:52.324624+00:00
-- url     : https://prove2.me/theorems/2071afee-b84f-48ba-b683-8597ee47bb6b
-- title:
--   Capping a vertex set: contracting its complement to a single new vertex
-- statement:
--   **Setting.** $N$ is a network on a finite vertex set $V$ with finite edge set $E$: each edge $e$ has a tail and a head in $V$. For $S\subseteq V$, $\partial_N S$ is the cut (the edges with exactly one endpoint in $S$), and $E(S)$ is the set of edges with at least one endpoint in $S$. A predicate "black" on $V$ is fixed; the black end $\beta(e)$ of an edge is its tail if the tail is black and its head otherwise. Let $\ast$ be a new vertex not in $V$.
--
--   1. **The cap map.** For $S\subseteq V$, $\kappa_S:V\to S\cup\{\ast\}$ is the identity on $S$ and sends every vertex outside $S$ to $\ast$. The file records that $\kappa_S(v)=v$ for $v\in S$, that $\kappa_S(v)=\ast$ iff $v\notin S$, and that $\kappa_S(v)=u$ for $u\in S$ iff $v=u$.
--   2. **The capped network.** $N^S$ is the network on $S\cup\{\ast\}$ with edge set $E(S)$, the edge $e$ running from $\kappa_S(\operatorname{tail}(e))$ to $\kappa_S(\operatorname{head}(e))$. Edges inside $S$ are kept, each edge of $\partial_N S$ now joins its endpoint in $S$ to $\ast$, and edges with both endpoints outside $S$ are discarded; so the edges at $\ast$ are exactly those of $\partial_N S$.
--   3. **Pulling back vertex sets.** For $T\subseteq S\cup\{\ast\}$, $\kappa_S^{-1}(T)=\{v\in V:\kappa_S(v)\in T\}$.
--   4. **Colour of the cap.** A vertex $v\in S$ keeps its colour, and
--   $$
--   \ast\text{ is black}\iff\{e\in\partial_N S:\ \beta(e)\in S\}=\emptyset .
--   $$
--   If every edge has exactly one black endpoint, the cut is nonempty and all its edges have endpoints of one colour in $S$, then $\ast$ receives the other colour.
--
--   Capping is the reduction along a three-edge cut. In the module, for a simple cubic three-edge-connected network and a set $S$ with $|\partial_N S|=3$, $|S|\ge 2$ and $S\ne V$, the capped network $N^S$ is again simple, cubic and three-edge-connected, and for a proper black/white colouring the rule in item 4 colours $N^S$ properly (all black ends of a three-edge cut then lie on the same side).
--
--   **Formalization Note** The new vertex is `none : Option A`, so the cap lives on `Option A`; `capMap`, `cap`, `capPreimage` and `capBlack` are the Lean names, `cap` is `mapVertices` by `capMap` followed by restriction to `regionEdges A`, and the black predicate on the new vertex is `(N.blackCut black A).card = 0`. The private theorem `dite_eq_right` is a backport alias for the Lean version in use, and `capMap_some`, `capMap_eq_none`, `capMap_eq_some`, `mem_capPreimage` are simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ThreeCuts.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

/-! Three-edge cuts, capped graphs, and preservation of graph properties. -/

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
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

def capMap (_N : Network V E) (A : Finset V) (v : V) : Option A := if h : v ∈ A then some ⟨v,h⟩ else none

omit [Fintype V] [Fintype E] in
@[simp] lemma capMap_some (A : Finset V) (v : A) : N.capMap A v.val = some v := by
  simp [capMap,v.property]
omit [Fintype V] [Fintype E] in
@[simp] lemma capMap_eq_none (A : Finset V) (v : V) : N.capMap A v = none ↔ v ∉ A := by
  simp [capMap]
omit [Fintype V] [Fintype E] in
@[simp] lemma capMap_eq_some (A : Finset V) (v : V) (w : A) :
    N.capMap A v = some w ↔ v = w.val := by
  by_cases h : v ∈ A
  · simp [capMap,h,Subtype.ext_iff]
  · simp only [capMap,dite_eq_right h,reduceCtorEq,false_iff]
    exact fun he => h (he ▸ w.property)

abbrev cap (A : Finset V) : Network (Option A) (N.regionEdges A) :=
  (N.mapVertices (N.capMap A)).restrict Subtype.val

def capPreimage (A : Finset V) (B : Finset (Option A)) : Finset V :=
  Finset.univ.filter fun v => N.capMap A v ∈ B

omit [Fintype E] in
@[simp] lemma mem_capPreimage (A : Finset V) (B : Finset (Option A)) (v : V) :
    v ∈ N.capPreimage A B ↔ N.capMap A v ∈ B := by simp [capPreimage]

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

def capBlack (black : V → Prop) (A : Finset V) : Option A → Prop
  | none => (N.blackCut black A).card = 0
  | some v => black v.val

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network

end OAI


