-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
-- name    : OAI_Combinatorics_HoneycombCorridor_Incidence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:35:43.845781+00:00
-- url     : https://prove2.me/theorems/6ed40f9c-222a-49b7-a1ef-79df36f90f38
-- title:
--   Rational boundary map and vertex-edge incidence matrix of a cell
-- statement:
--   Rational linear algebra on finite cells of the honeycomb lattice. Edges $e$ have an up end and a down end, and a cell is a finite set $S$ of hexagonal faces with its cell edges and cell vertices.
--
--   1. **Extension by zero.** For a finite set $S$ and $f:S\to\mathbb Q$, $\mathrm{extendOn}(S,f)$ is the finitely supported function equal to $f$ on $S$ and $0$ elsewhere; it is additive and homogeneous in $f$.
--   2. **Rational boundary.** $\partial q=\sum_eq(e)\bigl(\delta_{\mathrm{up}(e)}-\delta_{\mathrm{down}(e)}\bigr)$ for rational edge chains.
--   3. **Incidence matrix.** For a cell $S$, the incidence matrix has rows indexed by cell vertices and columns by cell edges, with
--   $$
--   M_{v,e}=[v=\mathrm{up}(e)]-[v=\mathrm{down}(e)] .
--   $$
--   4. **Face boundary operator.** The linear map from $\mathbb Q^S$ to functions on cell edges sends $f$ to the face gradient $e\mapsto r(\mathrm{left}(e))-r(\mathrm{right}(e))$ of its zero extension $r$.
--   5. A local contour has nonzero oriented flow on its outgoing slot.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Incidence.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Incidence.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def extendOn {α : Type*} [DecidableEq α] (S : Finset α) (f : S → ℚ) : α →₀ ℚ :=
  Finsupp.onFinset S (fun a => if ha : a ∈ S then f ⟨a,ha⟩ else 0)
    (by intro a h; by_contra ha; simp [ha] at h)

@[simp] theorem extendOn_apply_mem {α : Type*} [DecidableEq α]
    (S : Finset α) (f : S → ℚ) (a : S) : extendOn S f a = f a := by
  simp [extendOn]

@[simp] theorem extendOn_apply_not_mem {α : Type*} [DecidableEq α]
    (S : Finset α) (f : S → ℚ) (a : α) (ha : a ∉ S) : extendOn S f a = 0 := by
  simp [extendOn,ha]

noncomputable def rationalBoundary : (EdgeIndex →₀ ℚ) →+ (Vertex →₀ ℚ) :=
  Finsupp.liftAddHom fun e => Finsupp.singleAddHom (upEnd e) - Finsupp.singleAddHom (downEnd e)

@[simp] theorem rationalBoundary_single (e : EdgeIndex) (a : ℚ) :
    rationalBoundary (Finsupp.single e a) =
      Finsupp.single (upEnd e) a - Finsupp.single (downEnd e) a := by
  simp [rationalBoundary]

noncomputable def incidenceMatrix (S : Finset FaceIndex) :
    Matrix (cellVertices S) (cellEdges S) ℚ :=
  fun v e => (if v.1 = upEnd e then 1 else 0) - (if v.1 = downEnd e then 1 else 0)

theorem cell_upEnd (S : Finset FaceIndex) (e : cellEdges S) : upEnd e ∈ cellVertices S := by
  apply edge_mem_vertex S (canonicalDart e)
  have h : edgeOf (canonicalDart e) = e := by
    rcases e with ⟨⟨⟨i,j⟩,k⟩,he⟩
    rfl
  rw [h]
  exact e.property

theorem cell_downEnd (S : Finset FaceIndex) (e : cellEdges S) : downEnd e ∈ cellVertices S := by
  apply edge_mem_neighbor S (canonicalDart e)
  have h : edgeOf (canonicalDart e) = e := by
    rcases e with ⟨⟨⟨i,j⟩,k⟩,he⟩
    rfl
  rw [h]
  exact e.property

@[simp] theorem extendOn_add {α : Type*} [DecidableEq α] (S : Finset α)
    (f g : S → ℚ) : extendOn S (f + g) = extendOn S f + extendOn S g := by
  ext a
  by_cases ha : a ∈ S <;> simp [extendOn,ha]

@[simp] theorem extendOn_smul {α : Type*} [DecidableEq α] (S : Finset α)
    (c : ℚ) (f : S → ℚ) : extendOn S (c • f) = c • extendOn S f := by
  ext a
  by_cases ha : a ∈ S <;> simp [extendOn,ha]

noncomputable def cellFaceBoundary (S : Finset FaceIndex) :
    (S → ℚ) →ₗ[ℚ] (cellEdges S → ℚ) where
  toFun f e := faceGradient (extendOn S f) e
  map_add' f g := by
    funext e
    simp [extendOn_add,faceGradient]
    ring
  map_smul' c f := by
    funext e
    simp [extendOn_smul,faceGradient]
    ring

theorem contour_outgoing_nonzero (q : EdgeIndex →₀ ℤ) (g : Germ) (b : Bool)
    (h : LocalContour q g b) : orientedFlow q (g.1,outgoingSlot g b) ≠ 0 := by
  have hk : outgoingSlot g b ≠ g.2 := by
    rcases g with ⟨v,k⟩
    fin_cases k <;> cases b <;> simp [outgoingSlot]
  rw [h (outgoingSlot g b)]
  simp [hk]

end PolynomialVacuumBridge.Corridor

end

end OAI


