-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Corridors
-- name    : OAI_Combinatorics_Hamiltonian_Corridors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:55:23.893214+00:00
-- url     : https://prove2.me/theorems/2d73d30f-cf03-4dd0-8437-8612bc3c375a
-- title:
--   Corridor models of one graph in another and the disjointness pattern of a plane drawing
-- statement:
--   Let $G$ be a simple graph on $V$ and $H$ a simple graph on $W$. A dart of $G$ is an ordered pair $d=(v,w)$ of adjacent vertices, with first vertex $v$, second vertex $w$ and underlying edge $\{v,w\}$.
--
--   1. **Corridor models.** A corridor model of $G$ in $H$ consists of a branch set $\beta(v)\subseteq W$ for each vertex $v$ of $G$ and a corridor $\kappa(d)\subseteq W$ for each dart $d$ of $G$ such that
--      - every $\beta(v)$ and every $\kappa(d)$ is finite and induces a connected subgraph of $H$ (in particular it is nonempty);
--      - $\beta(v)\cap\beta(v')=\emptyset$ whenever $v\ne v'$;
--      - $\kappa(d)\cap\kappa(d')=\emptyset$ whenever $d$ and $d'$ have different underlying edges;
--      - $\beta(v)\cap\kappa(d)=\emptyset$ whenever $v$ is neither the first nor the second vertex of $d$;
--      - for $d=(v,w)$, both $\beta(v)\cap\kappa(d)$ and $\beta(w)\cap\kappa(d)$ are nonempty.
--   2. **The sets of a plane embedding.** A plane embedding of $G$ places the vertices at distinct points $p_v\in\mathbb{R}^2$ and each dart $(v,w)$ along an injective arc from $p_v$ to $p_w$, the arc of the reversed dart being the reversed arc, arcs meeting vertex points only at their ends, and interiors of arcs of different edges being disjoint. Its branch set $\operatorname{br}(v)$ is $p_v$ together with the first third of every arc leaving $v$, and the core $\operatorname{core}(d)$ is the middle third of the arc of $d$. For finite $V$, the file collects these into one family indexed by $V\sqcup\{\text{darts of }G\}$, assigning $\operatorname{br}(v)$ to $v$ and $\operatorname{core}(d)$ to $d$.
--   3. **Apartness.** On $V\sqcup\{\text{darts of }G\}$, two vertices $v,v'$ are apart if $v\ne v'$; a vertex $v$ and a dart $d$ (in either order) are apart if $v$ is neither endpoint of $d$; two darts are apart if their underlying edges differ. These are exactly the pairs that item 1 requires to be disjoint.
--
--   A corridor model records a drawing of $G$ inside $H$ combinatorially: connected disjoint branch sets for the vertices, and for each edge a connected corridor that meets the branch sets of its two ends and avoids everything else it must avoid. In the module, the planar sets of item 2 are disjoint along the apartness relation of item 3, and replacing them by the cells of a sufficiently fine square grid shows that every plane embedding of a finite graph $G$ yields a corridor model of $G$ in the square lattice graph on $\mathbb{Z}^2$.
--
--   **Formalization Note** `CorridorModel` is a structure whose fields are the conditions of item 1; connectedness is Mathlib's `SimpleGraph.Connected` of the induced subgraph, which includes nonemptiness. `allSets` and `apart` are defined on the sum type `V ⊕ G.Dart` under the assumptions `Fintype V`, `DecidableEq V` and `DecidableRel G.Adj`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Corridors.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Corridors.lean by skeleton subtraction
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

namespace OAI

/-! Disjoint lattice corridors obtained from a crossing-free plane embedding. -/

namespace Barnette

structure CorridorModel {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : V → Set W
  corridor : G.Dart → Set W
  branch_finite : ∀ v, (branch v).Finite
  corridor_finite : ∀ d, (corridor d).Finite
  branch_connected : ∀ v, (H.induce (branch v)).Connected
  corridor_connected : ∀ d, (H.induce (corridor d)).Connected
  branches_disjoint : ∀ v w, v ≠ w → Disjoint (branch v) (branch w)
  corridors_disjoint : ∀ d e, d.edge ≠ e.edge → Disjoint (corridor d) (corridor e)
  nonincident_disjoint : ∀ v d, v ≠ d.fst → v ≠ d.snd →
    Disjoint (branch v) (corridor d)
  incident_meets : ∀ d, (branch d.fst ∩ corridor d).Nonempty ∧
    (branch d.snd ∩ corridor d).Nonempty

namespace PlaneEmbedding

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] (E : PlaneEmbedding G)

 def allSets : V ⊕ G.Dart → Set (ℝ × ℝ)
  | .inl v => E.branch v
  | .inr d => E.core d

 def apart : V ⊕ G.Dart → V ⊕ G.Dart → Prop
  | .inl v, .inl w => v ≠ w
  | .inl v, .inr d => v ≠ d.fst ∧ v ≠ d.snd
  | .inr d, .inl v => v ≠ d.fst ∧ v ≠ d.snd
  | .inr d, .inr e => d.edge ≠ e.edge

end
end PlaneEmbedding
end Barnette

end OAI


