-- Prove2me | Definitions.Def_PlanarDFVSKernel_dualArc
-- name    : PlanarDFVSKernel_dualArc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:32.867226+00:00
-- url     : https://prove2.me/theorems/22fbe465-2981-4bee-bb13-926c3d9df96b
-- title:
--   The directed dual and the groups $R_u$
-- statement:
--   Let $D$ be a plane digraph. Its **directed dual** $H$ has one vertex for each face and one dual arc for each arc $e$ of $D$, directed from the face on the right of $e$ to the face on the left of $e$. For a vertex $u$ of $D$, the group $R_u$ consists of the reversals of the dual arcs of all arcs incident with $u$ (the boundary arcs of the dual face $F_u$).
--
--   **Formalization Note** Faces are the published dart orbits; the face containing the dart $(e,\mathrm{false})$ (the tail end of $e$) lies on the left of $e$, that of $(e,\mathrm{true})$ on the right. For a disconnected $D$ this is the disjoint union of the duals of the components. All statements using it are invariant under reversing every dual arc together with the groups.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §2.2, p.7 (PDF 8); §4.1, p.14 (PDF 15)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- The **faces** of a drawing, as a type: the published dart orbits `faces E` (Sheng, Xiao,
*A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version,
sha256 75cfca8f…), §2.2, p.7 (PDF 8)). They are the vertices of the directed dual. -/
abbrev Face {n m : ℕ} {G : Graph n m} (E : Drawing G) : Type :=
  {f : Finset (Dart m) // f ∈ faces E}

/-- The face containing the dart `d` (its orbit under the published face permutation
`faceNext E = reverseDart ∘ E.rot`). Geometrically it is the face in the angle between `d` and its
counterclockwise successor `E.rot d`, i.e. the face on the left of `d` read from its origin. -/
noncomputable def faceOf {n m : ℕ} {G : Graph n m} (E : Drawing G) (d : Dart m) : Face E :=
  ⟨faceOrbit E d, by unfold faces; exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩⟩

/-- **The dual arc of the arc `e`** (Sheng, Xiao, arXiv:2609.23669 (held version, sha256
75cfca8f…), §2.2, p.7 (PDF 8)): "The directed dual of a connected plane digraph has one vertex for
each face and one dual arc for each original arc. The dual arc crosses the original arc once and is
directed from its right-hand face to its left-hand face, as viewed along the original arc."

The dual arc of `e` goes from `faceOf E (e, true)` to `faceOf E (e, false)`.

**Formalization Note** `(e, false)` is the arc end at the tail, pointing along `e`; its face lies in
the angle counterclockwise after it, i.e. to the left of `e`. `(e, true)` is the end at the head,
pointing against `e`; its face is to the left of the reversed arc, i.e. to the right of `e`. So the
dual arc runs from the right-hand face to the left-hand face. Every statement of the mission is
invariant under reversing all dual arcs together with all reverse arcs built from them, so the
choice of orientation convention cannot affect their truth. -/
noncomputable def dualArc {n m : ℕ} {G : Graph n m} (E : Drawing G) (e : Fin m) :
    Face E × Face E :=
  (faceOf E (e, true), faceOf E (e, false))

/-- **The directed dual `H`** as an arc list on the faces (ibid., p.7 (PDF 8), p.14 (PDF 15)):
one dual arc for each original arc, `e = 0, …, m − 1`. These are the base arcs of the GSCA instance.

**Formalization Note** For a disconnected drawing the dart orbits of each connected component are
separate, so this is the disjoint union of the duals of the components (p.14–15, PDF 15–16: "apply
the construction separately and take the union"). -/
noncomputable def dualArcs {n m : ℕ} {G : Graph n m} (E : Drawing G) : List (Face E × Face E) :=
  (List.finRange m).map (dualArc E)

/-- **The group `R_u`** (Sheng, Xiao, arXiv:2609.23669 (held version, sha256 75cfca8f…), §4.1,
p.14 (PDF 15)): "An original vertex u corresponds to a dual face F_u, and each original arc incident
with u becomes a boundary arc of F_u in the dual. For each u ∈ V(D), let R_u be the group containing
the reversals of all boundary arcs of F_u."

`R_u` is the set of reversals of the dual arcs of the arcs with an endpoint at `u`. -/
noncomputable def vertexGroup {n m : ℕ} {G : Graph n m} (E : Drawing G) (u : Fin n) :
    Finset (Face E × Face E) := by
  classical exact ((Finset.univ.filter fun e : Fin m => G.tail e = u ∨ G.head e = u).image
    (fun e => (dualArc E e).swap))

end PlanarDFVSKernel


