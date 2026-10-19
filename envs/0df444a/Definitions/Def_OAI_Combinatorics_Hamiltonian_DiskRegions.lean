-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
-- name    : OAI_Combinatorics_Hamiltonian_DiskRegions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:22:22.472636+00:00
-- url     : https://prove2.me/theorems/2d92abd2-00bd-4d2e-81d4-f87480fc4633
-- title:
--   The dual region around a vertex set: region edges, region faces, and the region network
-- statement:
--   Let $N$ and $D$ be oriented networks on the same finite edge set $E$: $N$ has finite vertex set $V$ with tail and head maps $t_N, h_N : E \to V$, and $D$ has finite vertex set $F$ with tail and head maps $t_D, h_D : E \to F$. (In the application $N$ is a cubic plane graph and $D$ its dual, whose vertices are the faces of $N$.) Fix a set of vertices $A \subseteq V$.
--
--   1. **Region edges.** $E_A = \{ e \in E : t_N(e) \in A \text{ or } h_N(e) \in A \}$, the edges of $N$ with at least one endpoint in $A$.
--
--   2. **Region vertices.** $F_A = \{ z \in F : z \in \{ t_D(e), h_D(e) \} \text{ for some } e \in E_A \}$, the vertices of $D$ that are endpoints in $D$ of some region edge.
--
--   3. **Region network.** $D_A$ is the network with vertex set $F_A$ and edge set $E_A$ obtained by restricting $D$: each $e \in E_A$ keeps its $D$-tail and $D$-head, which lie in $F_A$ by definition.
--
--   4. **Region cycle map.** The linear map $\Phi_A : \mathbb{R}^A \to \mathbb{R}^{E_A}$,
--   $$
--   \Phi_A(f)(e) = \tilde f(h_N(e)) - \tilde f(t_N(e)) \qquad (e \in E_A),
--   $$
--   where $\tilde f \in \mathbb{R}^V$ is the extension of $f$ by zero outside $A$. In other words, $\Phi_A$ is the $N$-gradient of the zero extension, restricted to the region edges.
--
--   When every vertex star of $N$ forms a triangle of $D$ (as for a cubic plane graph and its dual triangulation), $D_A$ is the union of the triangles dual to the vertices of $A$, a disk-like piece of the triangulation when $A$ and its complement are suitably connected. These objects are used to identify the cycle space of $D_A$ with the image of $\Phi_A$ and to obtain exact Euler-type counts relating $|A|$, $|E_A|$, $|F_A|$ and the cut of $A$.
--
--   **Formalization Note** `regionEdges A : Finset E` and `regionVertices A : Finset F` (with simp lemmas `mem_regionEdges`, `mem_regionVertices`), `region A`, a network whose vertex and edge types are the corresponding subtypes, and `regionCycleMap A`, defined as `pull Subtype.val` composed with `N.gradient` and `push Subtype.val`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/DiskRegions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/DiskRegions.lean by skeleton subtraction
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

namespace OAI

/-! Connected face regions and the exact disk Euler formula. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def regionEdges (A : Finset V) : Finset E :=
  Finset.univ.filter fun e => N.tail e ∈ A ∨ N.head e ∈ A

omit [Fintype V] in
@[simp] lemma mem_regionEdges (A : Finset V) (e : E) :
    e ∈ N.regionEdges A ↔ N.tail e ∈ A ∨ N.head e ∈ A := by
  simp [regionEdges]

def regionVertices (A : Finset V) : Finset F :=
  Finset.univ.filter fun z => ∃ e ∈ N.regionEdges A, D.Incident e z

omit [Fintype V] in
@[simp] lemma mem_regionVertices (A : Finset V) (z : F) :
    z ∈ N.regionVertices D A ↔ ∃ e ∈ N.regionEdges A, D.Incident e z := by
  simp [regionVertices]

def region (A : Finset V) : Network (N.regionVertices D A) (N.regionEdges A) where
  tail e := ⟨D.tail e.val, (N.mem_regionVertices D A _).mpr ⟨e.val,e.property,Or.inl rfl⟩⟩
  head e := ⟨D.head e.val, (N.mem_regionVertices D A _).mpr ⟨e.val,e.property,Or.inr rfl⟩⟩

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def regionCycleMap (A : Finset V) : (A → ℝ) →ₗ[ℝ] (N.regionEdges A → ℝ) :=
  (pull (Subtype.val : N.regionEdges A → E)).comp
    (N.gradient.comp (push (Subtype.val : A → V)))

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


