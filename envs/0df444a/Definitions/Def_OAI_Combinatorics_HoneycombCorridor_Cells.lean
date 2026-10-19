-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
-- name    : OAI_Combinatorics_HoneycombCorridor_Cells
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:30:04.603451+00:00
-- url     : https://prove2.me/theorems/219b5bdc-d2fa-4980-ad86-a738e7a405f9
-- title:
--   Edges and vertices of hexagonal faces and finite cells
-- statement:
--   Faces of the honeycomb lattice are hexagons indexed by $a=(a_1,a_2)\in\mathbb Z^2$.
--
--   1. **Face edges and vertices.** $\mathrm{faceEdges}(a)$ is the set of the six edges of hexagon $a$ and $\mathrm{faceVertices}(a)$ its six vertices, namely $\mathrm{up}(a_1,a_2)$, $\mathrm{down}(a_1,a_2-1)$, $\mathrm{up}(a_1+1,a_2-1)$, $\mathrm{down}(a_1,a_2)$, $\mathrm{up}(a_1+1,a_2)$ and $\mathrm{down}(a_1+1,a_2-1)$.
--   2. **Cells.** For a finite set $S$ of faces, the cell edges and cell vertices are the unions of the face edges and face vertices over $a\in S$.
--   3. **Characterizations.** An edge lies on face $a$ iff $a$ is the left or right face of its canonical dart, and a vertex lies on $a$ iff $a$ is the left face of one of its three germs:
--   $$
--   e\in\mathrm{cellEdges}(S)\iff\mathrm{left}(e)\in S\ \text{or}\ \mathrm{right}(e)\in S .
--   $$
--   Both endpoints of a cell edge are cell vertices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Cells.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Cells.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def faceEdges (a : FaceIndex) : Finset EdgeIndex :=
  {((a.1,a.2),0), ((a.1+1,a.2),0),
   ((a.1+1,a.2-1),1), ((a.1,a.2),1),
   ((a.1+1,a.2),2), ((a.1+1,a.2-1),2)}

def faceVertices (a : FaceIndex) : Finset Vertex :=
  {.up a.1 a.2, .down a.1 (a.2-1), .up (a.1+1) (a.2-1),
   .down a.1 a.2, .up (a.1+1) a.2, .down (a.1+1) (a.2-1)}

def cellEdges (S : Finset FaceIndex) : Finset EdgeIndex := S.biUnion faceEdges

def cellVertices (S : Finset FaceIndex) : Finset Vertex := S.biUnion faceVertices

theorem mem_faceEdges (e : EdgeIndex) (a : FaceIndex) :
    e ∈ faceEdges a ↔ leftFace (canonicalDart e) = a ∨ rightFace (canonicalDart e) = a := by
  rcases e with ⟨⟨i,j⟩,k⟩
  rcases a with ⟨x,y⟩
  fin_cases k <;>
    simp [faceEdges,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] <;> omega

theorem mem_faceVertices (v : Vertex) (a : FaceIndex) :
    v ∈ faceVertices a ↔ ∃ k : Fin 3, leftFace (v,k) = a := by
  rcases a with ⟨x,y⟩
  cases v <;>
    simp [faceVertices,Fin.exists_fin_succ,leftFace] <;> omega

theorem mem_cellEdges (S : Finset FaceIndex) (e : EdgeIndex) :
    e ∈ cellEdges S ↔ leftFace (canonicalDart e) ∈ S ∨ rightFace (canonicalDart e) ∈ S := by
  simp only [cellEdges,Finset.mem_biUnion,mem_faceEdges]
  constructor
  · rintro ⟨a,ha,h | h⟩
    · exact Or.inl (h ▸ ha)
    · exact Or.inr (h ▸ ha)
  · rintro (h | h)
    · exact ⟨_,h,Or.inl rfl⟩
    · exact ⟨_,h,Or.inr rfl⟩

theorem mem_cellVertices (S : Finset FaceIndex) (v : Vertex) :
    v ∈ cellVertices S ↔ ∃ k : Fin 3, leftFace (v,k) ∈ S := by
  simp only [cellVertices,Finset.mem_biUnion,mem_faceVertices]
  constructor
  · rintro ⟨a,ha,k,hk⟩
    exact ⟨k,hk ▸ ha⟩
  · rintro ⟨k,hk⟩
    exact ⟨_,hk,k,rfl⟩

theorem edge_mem_vertex (S : Finset FaceIndex) (g : Germ)
    (h : edgeOf g ∈ cellEdges S) : g.1 ∈ cellVertices S := by
  rw [mem_cellEdges] at h
  rcases canonicalDart_edgeOf g with hg | hg
  · rw [hg] at h
    rcases h with h | h
    · exact (mem_cellVertices S g.1).mpr ⟨g.2,h⟩
    · rcases g with ⟨v,k⟩
      rw [mem_cellVertices]
      cases v <;> fin_cases k <;>
        simp [rightFace,reverseGerm,neighbor] at h <;>
        simp_all [Fin.exists_fin_succ,leftFace]
  · rw [hg,rightFace_reverse] at h
    rcases h with h | h
    · rcases g with ⟨v,k⟩
      rw [mem_cellVertices]
      cases v <;> fin_cases k <;>
        simp [reverseGerm,neighbor] at h <;>
        simp_all [Fin.exists_fin_succ,leftFace]
    · exact (mem_cellVertices S g.1).mpr ⟨g.2,h⟩

@[simp] theorem edgeOf_reverse (g : Germ) : edgeOf (reverseGerm g) = edgeOf g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [edgeOf,reverseGerm,neighbor]

theorem edge_mem_neighbor (S : Finset FaceIndex) (g : Germ)
    (h : edgeOf g ∈ cellEdges S) : neighbor g.1 g.2 ∈ cellVertices S := by
  exact edge_mem_vertex S (reverseGerm g) (by simpa using h)

end PolynomialVacuumBridge.Corridor

end

end OAI


