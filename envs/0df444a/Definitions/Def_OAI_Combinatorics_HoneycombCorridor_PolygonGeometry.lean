-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
-- name    : OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:47:37.056127+00:00
-- url     : https://prove2.me/theorems/c0cfb02e-adc4-42e0-89b2-4f6a04bc7032
-- title:
--   Vertices of edge sets, induced edges and potential levels
-- statement:
--   Auxiliary notions relating honeycomb polygons, edge sets and face potentials.
--
--   1. **Rational casting.** An integer finitely supported function is converted to a rational one with the same values and support.
--   2. **Edge vertices.** For a finite edge set $E$, $\mathrm{edgeVertices}(E)$ is the set of all endpoints; $v$ belongs to it iff one of the three edges at $v$ lies in $E$. For a simple closed walk, the edge vertices of the support of its word flow are exactly its traced vertices, and every vertex of a word contour carries a nonzero edge of the chain.
--   3. **Membership.** A vertex is interior to a polygon iff it lies on the interior faces and not on the polygon. An edge is induced by $D$ iff both ends are in $D$, and a polygon belongs to $\mathrm{polygons}(D)$ iff its vertices lie in $D$.
--   4. **Vertex level.** For a face potential $p$, the level of a vertex is the value of $p$ on the left face of its slot-$0$ germ:
--   $$
--   \mathrm{vertexLevel}(p,v)=p\bigl(\mathrm{leftFace}(v,0)\bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/PolygonGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/PolygonGeometry.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def toRatFinsupp {α : Type*} (p : α →₀ ℤ) : α →₀ ℚ :=
  p.mapRange (fun x : ℤ => (x : ℚ)) (by norm_num)

@[simp] theorem toRatFinsupp_apply {α : Type*} (p : α →₀ ℤ) (a : α) :
    toRatFinsupp p a = (p a : ℚ) := rfl

@[simp] theorem toRatFinsupp_support {α : Type*} (p : α →₀ ℤ) :
    (toRatFinsupp p).support = p.support := by
  ext a
  simp [Finsupp.mem_support_iff]

def edgeVertices (E : Finset EdgeIndex) : Finset Vertex := E.biUnion fun e => {upEnd e,downEnd e}

@[simp] theorem mem_edgeVertices (E : Finset EdgeIndex) (v : Vertex) :
    v ∈ edgeVertices E ↔ ∃ k : Fin 3, edgeOf (v,k) ∈ E := by
  classical
  constructor
  · intro h
    obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp h
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · refine ⟨e.2,?_⟩
      change edgeOf (canonicalDart e) ∈ E
      simpa using he
    · exact ⟨e.2,by simpa using he⟩
  · rintro ⟨k,hk⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨edgeOf (v,k),hk,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    exact (edgeOf_eq_iff v (edgeOf (v,k))).mp (by simp)

theorem wordContour_has_edge (q : EdgeIndex →₀ ℤ) (g : Germ) (w : List Bool)
    (hw : WordContour q g w) (v : Vertex) (hv : v ∈ traced g w) :
    ∃ k : Fin 3, q (edgeOf (v,k)) ≠ 0 := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
      simp only [traced,List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ⟨outgoingSlot g b, fun hz => contour_outgoing_nonzero q g b hw.1
          ((orientedFlow_zero_iff q _).mpr hz)⟩
      · exact ih _ hw.2 hv

theorem wordFlow_edgeVertices (g : Germ) (w : List Bool)
    (hw : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    edgeVertices (wordFlow g w).support = (traced g w).toFinset := by
  classical
  ext v
  simp only [mem_edgeVertices,Finsupp.mem_support_iff,List.mem_toFinset]
  constructor
  · rintro ⟨k,hk⟩
    by_contra hn
    have h := turnVisit_eq_zero_of_not_mem g w v k hn
    have hz : orientedFlow (wordFlow g w) (v,k) = 0 := by
      rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
      exact h
    exact hk ((orientedFlow_zero_iff _ _).mp hz)
  · exact wordContour_has_edge _ g w (simple_closed_word_contour g w hw hc) v

namespace Polygon

@[simp] theorem mem_interior (P : Polygon) (v : Vertex) :
    v ∈ P.interior ↔ v ∈ cellVertices P.interiorFaces ∧ v ∉ P.vertices := by
  simp [interior]

end Polygon

@[simp] theorem mem_inducedEdges (D : Finset Vertex) (e : EdgeIndex) :
    e ∈ inducedEdges D ↔ upEnd e ∈ D ∧ downEnd e ∈ D := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨canonicalDart e,?_,edgeOf_canonical e⟩,h⟩
    exact Finset.mem_product.mpr ⟨h.1,Finset.mem_univ _⟩

@[simp] theorem mem_polygons (D : Finset Vertex) (P : Polygon) :
    P ∈ polygons D ↔ P.vertices ⊆ D := by
  classical
  have hm : P ∈ polygons D ↔ P.val ⊆ inducedEdges D := by
    simp [polygons]
  rw [hm]
  constructor
  · intro h v hv
    obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp hv
    have he' := (mem_inducedEdges D e).mp (h he)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact he'.1
    · exact he'.2
  · intro h e he
    apply (mem_inducedEdges D e).mpr
    constructor
    · exact h (Finset.mem_biUnion.mpr ⟨e,he,by simp⟩)
    · exact h (Finset.mem_biUnion.mpr ⟨e,he,by simp⟩)

noncomputable def vertexLevel (p : FaceIndex →₀ ℤ) (v : Vertex) : ℤ :=
  p (leftFace (v,0))

namespace Polygon

end Polygon
end PolynomialVacuumBridge.Corridor

end

end OAI


