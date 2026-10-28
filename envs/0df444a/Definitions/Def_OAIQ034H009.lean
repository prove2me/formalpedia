-- Prove2me | Definitions.Def_OAIQ034H009
-- name    : OAIQ034H009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:40:24.499545+00:00
-- url     : https://prove2.me/theorems/d742df0a-e1b0-45fd-85c1-785e2ea78d23
-- title:
--   Definitions bundle OAIQ034H009 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 258 declarations of OpenAI's Lean: 59 definitions, 1 inductive type or structure, 1 instance and 197 theorems. The definitions and types are `OAI.HyperbolicObstruction.ConeSkeleton.allTurnDart`, `OAI.HyperbolicObstruction.ConeSkeleton.boundaryTransition`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryContractIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryFiniteComplex`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryFreeComparison`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryMacroWeight`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryMarkPosition`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryPolygonToTopology`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryPolygons`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryRootedVoltage`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryTopWeight`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryWalkIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.exteriorCellStep`, `OAI.HyperbolicObstruction.ConeSkeleton.exteriorCellTarget`, `OAI.HyperbolicObstruction.ConeSkeleton.exteriorCellToWalk`, `OAI.HyperbolicObstruction.ConeSkeleton.faceOccurrence`, `OAI.HyperbolicObstruction.ConeSkeleton.freeComparison`, `OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryCell_2`, `OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryEdge_2`, `OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryVertex_2`, `OAI.HyperbolicObstruction.ConeSkeleton.instTopologicalSpaceGroup`, `OAI.HyperbolicObstruction.ConeSkeleton.instTopologicalSpaceGroup_1`, `OAI.HyperbolicObstruction.ConeSkeleton.instTopologicalSpaceGroup_2`, `OAI.HyperbolicObstruction.ConeSkeleton.letterVoltage`, `OAI.HyperbolicObstruction.ConeSkeleton.mappedMacroPolygon`, `OAI.HyperbolicObstruction.ConeSkeleton.originalEdgeIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.polygonValue`, `OAI.HyperbolicObstruction.ConeSkeleton.sixCellIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.topPotential`, `OAI.HyperbolicObstruction.ConeSkeleton.topSlot`, `OAI.HyperbolicObstruction.CoreGeometry.Opposite`, `OAI.HyperbolicObstruction.CoreWordGraph.Fields`, `OAI.HyperbolicObstruction.CoreWordGraph.path`, `OAI.HyperbolicObstruction.CoreWordGraph.toMaster`, `OAI.HyperbolicObstruction.FinitePolyhedron.EdgePresentation.routeClasses`, `OAI.HyperbolicObstruction.FinitePolyhedron.EdgePresentation.toTopology`, `OAI.HyperbolicObstruction.FinitePolyhedron.EdgePresentation.topGenerator`, `OAI.HyperbolicObstruction.LetterPresentation.WordRelator`, `OAI.HyperbolicObstruction.LetterPresentation.letter`, `OAI.HyperbolicObstruction.LetterPresentation.pathWord` and 20 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_ActualDegree`, `HyperbolicGroups_BigonRemove`, `HyperbolicGroups_BoundaryIndex`, `HyperbolicGroups_ColoredApex`, `HyperbolicGroups_ConeCellWalk`, `HyperbolicGroups_ConeDecorationGroup`, `HyperbolicGroups_ConeExteriorWalk`, `HyperbolicGroups_ConeFanGroup`, `HyperbolicGroups_ConeMappedWalk`, `HyperbolicGroups_ConePresentationGroup`, `HyperbolicGroups_ConeTopGroup`, `HyperbolicGroups_CoreWordGraph`, `HyperbolicGroups_DipoleChain`, `HyperbolicGroups_DipoleRemove`, `HyperbolicGroups_DipoleSwitch`, `HyperbolicGroups_EdgeMerge`, `HyperbolicGroups_EdgeMergeComponents`, `HyperbolicGroups_ElementaryCone`, `HyperbolicGroups_ElementaryCover`, `HyperbolicGroups_FaceSplice`, `HyperbolicGroups_FaceWalk`, `HyperbolicGroups_FragmentSlots`, `HyperbolicGroups_FrozenCancel`, `HyperbolicGroups_FrozenWalk`, `HyperbolicGroups_FullWalkNormal`, `HyperbolicGroups_IndexedFace`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_LetterCover`, `HyperbolicGroups_MappedCancellation`, `HyperbolicGroups_MappedPicture`, `HyperbolicGroups_MergeWalk`, `HyperbolicGroups_MetricHexagon`, `HyperbolicGroups_PictureGenus`, `HyperbolicGroups_PictureMap`, `HyperbolicGroups_PicturePartition`, `HyperbolicGroups_PictureSum`, `HyperbolicGroups_PolygonBoundaryList`, `HyperbolicGroups_PolygonDiskProducer`, `HyperbolicGroups_Presentation`, `HyperbolicGroups_PresentationDisk`, `HyperbolicGroups_SimpleLetterPresentation`, `HyperbolicGroups_WalkCancel`, `HyperbolicGroups_WalkCell`, `HyperbolicGroups_WalkCover`, `HyperbolicGroups_WalkFacePosition`, `HyperbolicGroups_WalkNormal`, `HyperbolicGroups_WalkRadial`, `HyperbolicGroups_WalkRadialBoundary`, `HyperbolicGroups_WalkTopTurns`, `HyperbolicGroups_WalkTurnTransport`, `HyperbolicGroups_WordDisk`, `HyperbolicGroups_WordPictureAppend`, `HyperbolicGroups_WordPictureCell`, `HyperbolicGroups_WordPictureFold`, `HyperbolicGroups_WordPictureMarked`.
--
--   **Imports.** It imports the published bundle `Def_HyperbolicObstruction`; the bundles `OAIQ034H003`, `OAIQ034H004` and `OAIQ034H005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ034H011`; the proof of `OAI.HyperbolicObstruction.main`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_HyperbolicObstruction
import Definitions.Def_OAIQ034H003
import Definitions.Def_OAIQ034H004
import Definitions.Def_OAIQ034H005

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricHexagon
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry
open IncidenceTemplate

def Opposite : Vertex → Vertex → Prop
  | .inl r, .inr l => ¬Incident (pointOfRepresentative r) l
  | .inr l, .inl r => ¬Incident (pointOfRepresentative r) l
  | _, _ => False

end CoreGeometry
end HyperbolicObstruction


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry
open IncidenceTemplate

lemma Adjacent.symm {a b : Vertex} (hab : Adjacent a b) : Adjacent b a := by
  cases a <;> cases b <;> exact hab

lemma Adjacent.not_opposite {a b : Vertex} (hab : Adjacent a b) : ¬ Opposite a b := by
  cases a <;> cases b <;> simp_all [Adjacent, Opposite]

end CoreGeometry
end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureMap
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.instFinite _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*}

namespace PictureMap
variable (M : PictureMap D)

variable [DecidableEq D]

section Finite
variable [Fintype D]

/-- Exact vertex count under the radial switch in the manuscript. The two
far vertices are either joined, or each original link is split. -/
theorem switch_vertices (a b : D) (hab : a ≠ b)
    (hv : M.vertex.SameCycle a b)
    (hfar₁ : ¬ M.vertex.SameCycle a (M.edge a))
    (hfar₂ : ¬ M.vertex.SameCycle a (M.edge b)) :
    cycles (M.switch a b).vertex = cycles M.vertex +
      if M.vertex.SameCycle (M.edge a) (M.edge b) then 2 else 0 := by
  rw [vertex_switch]
  have hn : (M.vertex * swap (M.edge a) (M.edge b)).SameCycle a b :=
    (sameCycle_right_swap_away M.vertex hfar₁ hfar₂).mpr hv
  rw [cycles_split_right _ hab hn]
  by_cases he : M.vertex.SameCycle (M.edge a) (M.edge b)
  · rw [ite_eq_left he,cycles_split_right _ (M.edge.injective.ne hab) he]
    ring
  · rw [ite_eq_right he]
    have hh := cycles_merge_right M.vertex he
    omega

/-- No appeal to a drawing is used for the Euler change; all faces and edges
are retained, while the exact vertex-cycle computation gives the change. -/
theorem switch_euler (a b : D) (hab : a ≠ b)
    (hv : M.vertex.SameCycle a b)
    (hfar₁ : ¬ M.vertex.SameCycle a (M.edge a))
    (hfar₂ : ¬ M.vertex.SameCycle a (M.edge b)) :
    (M.switch a b).euler = M.euler +
      if M.vertex.SameCycle (M.edge a) (M.edge b) then 2 else 0 := by
  simp only [euler,switch_face,M.switch_vertices a b hab hv hfar₁ hfar₂]
  ring

end Finite
end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ColoredApex
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.instFinite _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap
variable (c : D → Bool) (M : PictureMap D)

lemma apexCount_eq (h : ∀ x, c (M.vertex x) = c x) :
    (M.apexCount c : ℤ) = cycles (M.apexPerm c h) := by
  rw [cycles_eq_card_classes]
  congr 1
  apply Nat.card_congr
  exact Quotient.congrRight (fun a b => (sameCycle_subtypePerm_iff M.vertex _ a b).symm)

omit [Fintype D] in
lemma switch_color (h : ∀ x, c (M.vertex x) = c x) {a b : D}
    (hab : c a = c b) (hfar : c (M.edge a) = c (M.edge b)) :
    ∀ x, c ((M.switch a b).vertex x) = c x := by
  intro x
  rw [M.vertex_switch]
  simp only [mul_apply,h,Equiv.apply_swap_eq_self hfar,Equiv.apply_swap_eq_self hab]

omit [Fintype D] in
lemma apexPerm_switch (h : ∀ x, c (M.vertex x) = c x) {a b : D}
    (ha : c a = true) (hb : c b = true)
    (hfa : c (M.edge a) = false) (hfb : c (M.edge b) = false) :
    (M.switch a b).apexPerm c (M.switch_color c h (ha.trans hb.symm) (hfa.trans hfb.symm)) =
      M.apexPerm c h * swap (⟨a,ha⟩ : {x : D // c x = true}) ⟨b,hb⟩ := by
  ext x
  simp only [apexPerm,subtypePerm_apply,mul_apply]
  rw [M.vertex_switch]
  simp only [mul_apply]
  have hv : (swap (⟨a,ha⟩ : {x : D // c x = true}) ⟨b,hb⟩ x).val = swap a b x.val :=
    (Subtype.val_injective.swap_apply ⟨a,ha⟩ ⟨b,hb⟩ x).symm
  rw [hv]
  have hc : c (swap a b x.val) = true := by
    rw [Equiv.apply_swap_eq_self (ha.trans hb.symm)]
    exact x.property
  have hna : swap a b x.val ≠ M.edge a := by
    intro he; rw [he,hfa] at hc; exact Bool.noConfusion hc
  have hnb : swap a b x.val ≠ M.edge b := by
    intro he; rw [he,hfb] at hc; exact Bool.noConfusion hc
  rw [swap_apply_of_ne_of_ne hna hnb]

/-- The termination measure counts actual apex vertex instances, rather than
all vertices: at each repeated radial-label switch this increases by one. -/
theorem switch_apexCount (h : ∀ x, c (M.vertex x) = c x) {a b : D}
    (hne : a ≠ b) (hv : M.vertex.SameCycle a b)
    (ha : c a = true) (hb : c b = true)
    (hfa : c (M.edge a) = false) (hfb : c (M.edge b) = false) :
    (M.switch a b).apexCount c = M.apexCount c + 1 := by
  have hc : ∀ x, c ((M.switch a b).vertex x) = c x :=
    M.switch_color c h (ha.trans hb.symm) (hfa.trans hfb.symm)
  have hs : (M.apexPerm c h).SameCycle ⟨a,ha⟩ ⟨b,hb⟩ :=
    (sameCycle_subtypePerm_iff M.vertex _ _ _).mpr hv
  have hn : (⟨a,ha⟩ : {x : D // c x = true}) ≠ ⟨b,hb⟩ :=
    fun he => hne (congrArg Subtype.val he)
  have he := cycles_split_right (M.apexPerm c h) hn hs
  rw [← M.apexPerm_switch c h ha hb hfa hfb] at he
  rw [← (M.switch a b).apexCount_eq c hc,← M.apexCount_eq c h] at he
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureGenus
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.instFinite _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap
variable (M : PictureMap D)

/-- When the far vertices were distinct, their merged link still joins both
switched edges. Thus no component is split in this case. -/
theorem switch_components_eq_of_far_distinct (a b : D)
    (hv : M.vertex.SameCycle a b)
    (hfar₁ : ¬ M.vertex.SameCycle a (M.edge a))
    (hfar₂ : ¬ M.vertex.SameCycle a (M.edge b))
    (hne : ¬ M.vertex.SameCycle (M.edge a) (M.edge b)) :
    (M.switch a b).components = M.components := by
  let q := M.vertex * swap (M.edge a) (M.edge b)
  have hq : q.SameCycle (M.edge a) (M.edge b) := sameCycle_after_swap_right _ hne
  have hqab : q.SameCycle a b := (sameCycle_right_swap_away _ hfar₁ hfar₂).mpr hv
  have hqa : ¬ q.SameCycle (M.edge a) a := fun h =>
    hfar₁ ((sameCycle_right_swap_away _ hfar₁ hfar₂).mp h.symm)
  have hqb : ¬ q.SameCycle (M.edge a) b := fun h => hqa (h.trans hqab.symm)
  have hnew : (M.switch a b).vertex.SameCycle (M.edge a) (M.edge b) := by
    rw [M.vertex_switch]
    exact (sameCycle_right_swap_away q hqa hqb).mpr hq
  have ha : (M.switch a b).components a (M.edge b) := by
    rw [← M.switch_edge_a a b hfar₂]
    exact (M.switch a b).edge_le_components SameCycle.rfl.apply_right
  have hb : (M.switch a b).components b (M.edge a) := by
    rw [← M.switch_edge_b a b hv hfar₁]
    exact (M.switch a b).edge_le_components SameCycle.rfl.apply_right
  have hab : (M.switch a b).components a b :=
    (M.switch a b).components.trans' ha
      ((M.switch a b).components.trans' ((M.switch a b).vertex_le_components hnew.symm)
        ((M.switch a b).components.symm' hb))
  have h := M.switch_components_glue a b hv
  rwa [glue_eq_of_rel _ _ _ hab] at h

/-- Genus-zero preservation under radial-label normalization.
Counts refer to actual permutation cycles and their actual
component quotient; Euler's bound was proved without surface classification. -/
theorem switch_genusZero (hM : M.GenusZero) (a b : D) (hab : a ≠ b)
    (hv : M.vertex.SameCycle a b)
    (hfar₁ : ¬ M.vertex.SameCycle a (M.edge a))
    (hfar₂ : ¬ M.vertex.SameCycle a (M.edge b)) : (M.switch a b).GenusZero := by
  have hE := M.switch_euler a b hab hv hfar₁ hfar₂
  change M.euler = _ at hM
  change (M.switch a b).euler = _
  by_cases hf : M.vertex.SameCycle (M.edge a) (M.edge b)
  · rw [ite_eq_left hf,hM] at hE
    have hC := M.switch_components_card a b hv
    have hbound := (M.switch a b).euler_le
    split_ifs at hC <;> omega
  · rw [ite_eq_right hf,hM] at hE
    rw [M.switch_components_eq_of_far_distinct a b hv hfar₁ hfar₂ hf]
    omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MappedPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap

variable {L V : Type*}

/-- A finite normalizing producer for radial labels on actual side-pairings.
The same darts, face cycles and mapped oriented edge labels are retained.
Thus all face maps/lifted face chains remain unchanged. Genus zero is retained
by the checked switch theorem, not assumed of the output.

`radial` is the target incidence fact: every edge starting at an apex ends at
an ordinary vertex. The conclusion says each outgoing radial label occurs
at most once in each actual apex vertex-link cycle. -/
theorem normalize_radial {M : PictureMap D} {label : D → L} {start : L → V} {rev : L → L}
    (isApex : V → Bool) (hM : M.Respects label start rev) (hG : M.GenusZero)
    (radial : ∀ d, isApex (start (label d)) = true →
      isApex (start (rev (label d))) = false) :
    ∃ N : PictureMap D, N.face = M.face ∧ N.Respects label start rev ∧ N.GenusZero ∧
      ∀ a b, isApex (start (label a)) = true → N.vertex.SameCycle a b →
        label a = label b → a = b := by
  classical
  let c : D → Bool := fun d => isApex (start (label d))
  let good : PictureMap D → Prop := fun N => N.face = M.face ∧ N.Respects label start rev ∧ N.GenusZero
  let := Fintype.ofFinite (PictureMap D)
  let s := Finset.univ.filter good
  have hm : M ∈ s := by simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨rfl,hM,hG⟩
  obtain ⟨N,hN,hmax⟩ := s.exists_max_image (fun N => N.apexCount c) ⟨M,hm⟩
  have hn : good N := (Finset.mem_filter.mp hN).2
  refine ⟨N,hn.1,hn.2.1,hn.2.2,?_⟩
  intro a b ha hv hl
  by_contra hne
  have hc : ∀ x, c (N.vertex x) = c x := fun x => congrArg isApex (hn.2.1.1 x)
  have hb : c b = true := by change isApex (start (label b)) = true; rw [← hl]; exact ha
  have hfa : c (N.edge a) = false := by
    change isApex (start (label (N.edge a))) = false
    rw [hn.2.1.2 a]
    exact radial a ha
  have hfb : c (N.edge b) = false := by
    change isApex (start (label (N.edge b))) = false
    rw [hn.2.1.2 b]
    exact radial b hb
  have hs : good (N.switch a b) := ⟨hn.1,switch_respects hn.2.1 hl,
    N.switch_genusZero hn.2.2 a b hne hv
      (N.radial_far c hc ha hfa) (N.radial_far c hc ha hfb)⟩
  have hmem : N.switch a b ∈ s := by simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]; exact hs
  have hbound := hmax (N.switch a b) hmem
  have hinc := N.switch_apexCount c hc hne hv ha hb hfa hfb
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Presentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate

namespace Path
variable {a b c : Vertex}

lemma eval_map {G H L : Type*} [Group G] [Group H] (f : G →* H)
    (l : Field → L) (r : L → G) (p : Path a b) :
    f (p.eval l r) = p.eval l (fun i => f (r i)) := by
  induction p with
  | nil => exact map_one f
  | cons s p ih =>
    simp only [eval,map_mul,ih]
    congr 1
    cases h : s.forward <;> simp [Step.value,h]
end Path

lemma squareWord_map {G H L : Type*} [Group G] [Group H] (f : G →* H)
    (l : Field → L) (r : L → G) (τ : TwoPath) :
    f (squareWord l r τ) = squareWord l (fun i => f (r i)) τ := by
  simp only [squareWord,map_mul,Step.value]
  split_ifs <;> simp

end MasterGraph

namespace LetterPresentation
open IncidenceTemplate MasterGraph
variable (n : ℕ)

lemma freeLetter_inv (a : Alphabet n) : freeLetter n (inverseLetter n a) = (freeLetter n a)⁻¹ := by
  rcases a with ⟨i,b⟩
  cases b <;> simp [freeLetter,inverseLetter]

variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def letter (a : Alphabet n) : Group n w d := PresentedGroup.mk _ (freeLetter n a)

end LetterPresentation
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DipoleSwitch
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I L V : Type*}
namespace PictureMap

variable (M : PictureMap D) {q : Perm I} {a b : I → D}

variable [DecidableEq D]

/-- The elementary cancellation switch pairs the next two boundary sides,
while retaining every already paired side of the two cancellation faces. -/
lemma dipole_switch_pairs (hF : OppositeFaces M.face q a b) (k : I) :
    (M.switch (a k) (M.edge (b k))).edge (a k) = b k ∧
      ∀ j, M.edge (a j) = b j → (M.switch (a k) (M.edge (b k))).edge (a j) = b j := by
  have hnew : (M.switch (a k) (M.edge (b k))).edge (a k) = b k := by
    rw [M.switch_edge_a_of_ne]
    · exact M.edge_edge (b k)
    · rw [M.edge_edge]
      exact (hF.disjoint k k).symm
  refine ⟨hnew,?_⟩
  intro j hj
  by_cases he : j = k
  · simpa only [he] using hnew
  have h₁ : a j ≠ a k := hF.a_inj.ne he
  have h₂ : a j ≠ M.edge (b k) := by
    intro h
    have hh := congrArg M.edge h
    rw [M.edge_edge,hj] at hh
    exact he (hF.b_inj hh)
  have h₃ : b j ≠ a k := (hF.disjoint k j).symm
  have h₄ : b j ≠ M.edge (b k) := by
    intro h
    have hh := congrArg M.edge h
    rw [M.edge_edge,M.paired_reverse hj] at hh
    exact hF.disjoint j k hh
  change swap (a k) (M.edge (b k)) (M.edge (swap (a k) (M.edge (b k)) (a j))) = b j
  rw [swap_apply_of_ne_of_ne h₁ h₂,hj,swap_apply_of_ne_of_ne h₃ h₄]

variable [Fintype D] [Fintype I]

/-- A complete dipole can be separated by finitely many genuine crosswise
side-pairing switches. This is the producer behind cancellation in a minimal
mapped sphere/disk picture. It preserves genus zero, the face permutation and
all original oriented side labels; it does NOT presuppose a normal picture. -/
theorem isolate_dipole (hF : OppositeFaces M.face q a b) (i₀ : I)
    (hseed : M.edge (a i₀) = b i₀) {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) (hG : M.GenusZero)
    (hinv : ∀ l, rev (rev l) = l) (hop : ∀ i, label (b i) = rev (label (a i))) :
    ∃ N : PictureMap D, N.face = M.face ∧ N.Respects label start rev ∧ N.GenusZero ∧
      (∀ i, M.edge (a i) = b i → N.edge (a i) = b i) ∧ ∀ i, N.edge (a i) = b i := by
  classical
  let good : PictureMap D → Prop := fun N => N.face = M.face ∧ N.Respects label start rev ∧
    N.GenusZero ∧ ∀ i, M.edge (a i) = b i → N.edge (a i) = b i
  let paired : PictureMap D → Finset I := fun N => Finset.univ.filter (fun i => N.edge (a i) = b i)
  let := Fintype.ofFinite (PictureMap D)
  let s := Finset.univ.filter good
  have hm : M ∈ s := by
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨rfl,hM,hG,fun _ h => h⟩
  obtain ⟨N,hN,hmax⟩ := s.exists_max_image (fun N => (paired N).card) ⟨M,hm⟩
  have hn : good N := (Finset.mem_filter.mp hN).2
  have fn : OppositeFaces N.face q a b := by rw [hn.1]; exact hF
  have hadvance : ∀ i, N.edge (a i) = b i → N.edge (a (q i)) = b (q i) := by
    intro i hi
    by_contra hbad
    let T := N.switch (a (q i)) (N.edge (b (q i)))
    have hl : label (a (q i)) = label (N.edge (b (q i))) := by
      rw [hn.2.1.2,hop,hinv]
    have ht : good T := ⟨hn.1,switch_respects hn.2.1 hl,
      N.switch_genusZero_general hn.2.2.1 _ _ (N.dipole_sameVertex fn hi),
      fun j hj => (N.dipole_switch_pairs fn (q i)).2 j (hn.2.2.2 j hj)⟩
    have hsub : paired N ⊆ paired T := by
      intro j hj
      have hj' : N.edge (a j) = b j := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(N.dipole_switch_pairs fn (q i)).2 j hj'⟩
    have hnew : q i ∈ paired T :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(N.dipole_switch_pairs fn (q i)).1⟩
    have hold : q i ∉ paired N := by simpa only [paired,Finset.mem_filter,Finset.mem_univ,true_and] using hbad
    have hstrict : paired N ⊂ paired T := lt_of_le_of_ne hsub (fun he => hold (he ▸ hnew))
    have hlt := Finset.card_lt_card hstrict
    have hmem : T ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩
    have hle := hmax T hmem
    omega
  refine ⟨N,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,?_⟩
  intro i
  obtain ⟨n,rfl⟩ := (hF.cyclic i₀ i).exists_nat_pow_eq
  induction n with
  | zero => simpa only [pow_zero,one_apply] using hn.2.2.2 i₀ hseed
  | succ n ih =>
      rw [pow_succ',mul_apply]
      exact hadvance _ ih

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DipoleRemove
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I : Type*}
namespace PictureMap

namespace OppositeFaces
variable {f : Perm D} {q : Perm I} {a b : I → D} (h : OppositeFaces f q a b)
include h

lemma not_sameCycle_ab [Fintype D] (i j : I) : ¬ f.SameCycle (a i) (b j) := by
  intro hab
  have hh := invariant_of_sameCycle (P := fun x => ∃ i, a i = x) f h.range_a_invariant hab
  obtain ⟨k,hk⟩ := hh.mp ⟨i,rfl⟩
  exact h.disjoint k j hk

/-- Exactly the two face classes, not an arbitrary assumed two-cell subset. -/
def dipoleClassesEquiv [Fintype D] [Fintype I] (i₀ : I) : Bool ≃
    Quotient ((SameCycle.setoid f).comap (Subtype.val : {x // InDipole a b x} → D)) := by
  let g : Bool → Quotient ((SameCycle.setoid f).comap (Subtype.val : {x // InDipole a b x} → D)) :=
    fun t => if t then Quotient.mk _ ⟨b i₀,Or.inr ⟨i₀,rfl⟩⟩ else Quotient.mk _ ⟨a i₀,Or.inl ⟨i₀,rfl⟩⟩
  refine Equiv.ofBijective g ⟨?_,?_⟩
  · intro x y hxy
    cases x <;> cases y
    · rfl
    · exact False.elim (h.not_sameCycle_ab i₀ i₀ (Quotient.exact hxy))
    · exact False.elim (h.not_sameCycle_ab i₀ i₀ (Quotient.exact hxy.symm))
    · rfl
  · intro x
    induction x using Quotient.inductionOn with
    | h x =>
      rcases x.property with ⟨i,hi⟩ | ⟨i,hi⟩
      · refine ⟨false,Quotient.sound ?_⟩
        change f.SameCycle (a i₀) x.val
        rw [← hi]
        exact h.a_sameCycle i₀ i
      · refine ⟨true,Quotient.sound ?_⟩
        change f.SameCycle (b i₀) x.val
        rw [← hi]
        exact h.b_sameCycle i₀ i

lemma cycles_dipole [DecidableEq D] [Fintype D] [Fintype I] (i₀ : I) :
    cycles (f.subtypePerm h.inDipole_face) = 2 := by
  rw [cycles_eq_card_classes]
  have he : Nat.card (Quotient (SameCycle.setoid (f.subtypePerm h.inDipole_face))) =
      Nat.card (Quotient ((SameCycle.setoid f).comap (Subtype.val : {x // InDipole a b x} → D))) :=
    Nat.card_congr (Quotient.congrRight (sameCycle_subtypePerm_iff f h.inDipole_face))
  rw [he,← Nat.card_congr (h.dipoleClassesEquiv i₀)]
  norm_num

end OppositeFaces
variable (M : PictureMap D) {q : Perm I} {a b : I → D}

/-- Delete the isolated dipole; every unremoved face and dart retains its
original index, and every surviving side pairing is unchanged. -/
def removeDipole (hF : OppositeFaces M.face q a b) (hp : ∀ i, M.edge (a i) = b i) :
    PictureMap {x : D // ¬ InDipole a b x} :=
  M.restrict _ (fun x => not_congr (hF.inDipole_face x)) (fun x => not_congr (M.inDipole_edge hp x))

lemma removeDipole_genusZero [DecidableEq D] [Fintype D]
    (hF : OppositeFaces M.face q a b) (hp : ∀ i, M.edge (a i) = b i)
    (hG : M.GenusZero) : (M.removeDipole hF hp).GenusZero := by
  classical
  convert M.restrict_genusZero (fun x => ¬ InDipole a b x) hG
    (fun x => not_congr (hF.inDipole_face x))
    (fun x => not_congr (M.inDipole_edge hp x)) using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma removeDipole_faces [DecidableEq D] [Fintype D] [Fintype I]
    (hF : OppositeFaces M.face q a b) (hp : ∀ i, M.edge (a i) = b i) (i₀ : I) :
    cycles (M.removeDipole hF hp).face = cycles M.face - 2 := by
  have hh := cycles_subtype_split M.face hF.inDipole_face
  rw [hF.cycles_dipole i₀] at hh
  change cycles (M.face.subtypePerm (fun x => not_congr (hF.inDipole_face x))) = _
  omega

lemma restrict_respects {L V : Type*} {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) (P : D → Prop)
    (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    (M.restrict P hf he).Respects (label ∘ Subtype.val) start rev := by
  constructor
  · intro x; exact hM.1 x.val
  · intro x; exact hM.2 x.val

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DipoleChain
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D A : Type*} [DecidableEq D] [Fintype D] [AddCommMonoid A]

omit [DecidableEq D] in
lemma faceChain_split (f : Perm D) (w : D → A) (hw : ∀ x, w (f x) = w x)
    (P : D → Prop) (hp : ∀ x, P (f x) ↔ P x) :
    faceChain f w hw =
      faceChain (f.subtypePerm hp) (w ∘ Subtype.val) (fun x => hw x.val) +
      faceChain (f.subtypePerm (p := fun x => ¬ P x) (fun x => not_congr (hp x)))
        (w ∘ Subtype.val) (fun x => hw x.val) := by
  classical
  convert classSum_split (SameCycle.setoid f) w
    (sameCycle_le_of_apply (s := Setoid.ker w) (fun x => (hw x).symm))
    P (invariant_of_sameCycle f hp) using 1
  · rfl
  · rw [faceChain_subtype]
    congr 1
    convert faceChain_subtype f w hw (fun x => ¬ P x) (fun x => not_congr (hp x)) using 1 <;> congr 1 <;> exact Subsingleton.elim _ _

namespace PictureMap
variable {I : Type*} [DecidableEq I] [Fintype I] {q : Perm I} {a b : I → D}

omit [DecidableEq D] [DecidableEq I] in
lemma OppositeFaces.faceChain_dipole {f : Perm D} (hF : OppositeFaces f q a b) (i₀ : I)
    (w : D → A) (hw : ∀ x, w (f x) = w x) :
    faceChain (f.subtypePerm hF.inDipole_face) (w ∘ Subtype.val) (fun x => hw x.val) =
      w (a i₀) + w (b i₀) := by
  classical
  rw [faceChain_subtype]
  let hs : (SameCycle.setoid f).comap (Subtype.val : {x // InDipole a b x} → D) ≤
      Setoid.ker (w ∘ Subtype.val) := fun _ _ h =>
    (sameCycle_le_of_apply (s := Setoid.ker w) (fun x => (hw x).symm)) h
  let v := Quotient.lift (w ∘ (Subtype.val : {x // InDipole a b x} → D)) (fun _ _ h => hs h)
  have hh := Fintype.sum_equiv (hF.dipoleClassesEquiv i₀)
    (fun t : Bool => if t then w (b i₀) else w (a i₀)) v (by intro t; cases t <;> rfl)
  rw [Fintype.sum_bool] at hh
  simp only [Bool.false_eq_true,ite_false,ite_true] at hh
  exact hh.symm.trans (add_comm _ _)

variable (M : PictureMap D)
omit [DecidableEq D] [DecidableEq I] in
/-- Cancellation preserves the exact signed chain in an arbitrary additive
coefficient group, not just its homology class or its unsigned face count. -/
theorem removeDipole_chain (hF : OppositeFaces M.face q a b) (hp : ∀ i, M.edge (a i) = b i)
    (i₀ : I) (w : D → A) (hw : ∀ x, w (M.face x) = w x)
    (hc : w (a i₀) + w (b i₀) = 0) :
    faceChain (M.removeDipole hF hp).face (w ∘ Subtype.val) (fun x => hw x.val) =
      faceChain M.face w hw := by
  have hh := faceChain_split M.face w hw (InDipole a b) hF.inDipole_face
  rw [hF.faceChain_dipole i₀ w hw,hc,zero_add] at hh
  exact hh.symm

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFace
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

variable {D S : Type*}

namespace IndexedFaceMap
variable {f : Perm D} {t : Perm S} {j : D → S} (h : IndexedFaceMap f t j)
include h

/-- Opposite target sides, including their INDEX, determine opposite complete
source face parametrizations. In particular, this derives cancellation data
from a cellular map rather than taking opposite copies as an extra normality
assumption. Target cycles of opposite orientations are disjoint. -/
theorem opposite_faces [DecidableEq D] [Fintype D]
    (r : Perm S) (hr : r * r = 1)
    (hrev : ∀ s, r (t s) = t⁻¹ (r s))
    (hdisj : ∀ s, ¬ t.SameCycle s (r s))
    (a b : D) (hab : j b = r (j a)) :
    ∃ q : Perm {x : D // f.SameCycle a x},
      ∃ v : {x : D // f.SameCycle a x} → D,
        PictureMap.OppositeFaces f q Subtype.val v ∧
        v ⟨a,SameCycle.rfl⟩ = b ∧ ∀ x, j (v x) = r (j x.val) := by
  classical
  let I := {x : D // f.SameCycle a x}
  let q : Perm I := f.subtypePerm (fun x => sameCycle_apply_right)
  have hr' (s : S) : r (r s) = s := congrArg (fun p : Perm S => p s) hr
  have hv (x : I) : ∃ y, f.SameCycle b y ∧ j y = r (j x.val) := by
    apply h.orbit_surjective b
    rw [hab]
    exact (semiconj_perm_sameCycle hrev
      (semiconj_perm_sameCycle h.commute x.property)).of_inv
  let v : I → D := fun x => (hv x).choose
  have v_cycle (x : I) : f.SameCycle b (v x) := (hv x).choose_spec.1
  have v_map (x : I) : j (v x) = r (j x.val) := (hv x).choose_spec.2
  have v_inj : Function.Injective v := by
    intro x y he
    apply Subtype.ext
    apply h.injective (x.property.symm.trans y.property)
    apply r.injective
    rw [← v_map,← v_map,he]
  have v_disj (x y : I) : x.val ≠ v y := by
    intro he
    have hc : f.SameCycle a b := x.property.trans (he ▸ (v_cycle y).symm)
    have ht := semiconj_perm_sameCycle h.commute hc
    rw [hab] at ht
    exact hdisj (j a) ht
  have v_face (x : I) : f (v (q x)) = v x := by
    apply h.injective ((v_cycle (q x)).apply_right.symm.trans (v_cycle x))
    rw [h.commute,v_map,v_map]
    change t (r (j (f x.val))) = r (j x.val)
    rw [h.commute,hrev,Perm.inv_def,apply_symm_apply]
  refine ⟨q,v,⟨Subtype.val_injective,v_inj,v_disj,fun _ => rfl,v_face,?_⟩,?_,v_map⟩
  · intro x y
    exact (sameCycle_subtypePerm).mpr (x.property.symm.trans y.property)
  · apply h.injective (v_cycle ⟨a,SameCycle.rfl⟩).symm
    exact (v_map ⟨a,SameCycle.rfl⟩).trans hab.symm

end IndexedFaceMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MappedCancellation
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I L V A : Type*} [DecidableEq D] [Fintype D] [Fintype I]
  [AddCommMonoid A]
namespace PictureMap

/-- Two opposite
face occurrences sharing one indexed side are removed. The number of faces
falls by exactly two, genus zero is retained, the target map on every surviving
side is unchanged, and the exact lifted cellular chain is unchanged. -/
theorem cancel_mapped_dipole (M : PictureMap D) {q : Perm I} {a b : I → D}
    (hF : OppositeFaces M.face q a b) (i₀ : I) (hseed : M.edge (a i₀) = b i₀)
    {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) (hG : M.GenusZero)
    (hinv : ∀ l, rev (rev l) = l) (hop : ∀ i, label (b i) = rev (label (a i)))
    (w : D → A) (hw : ∀ x, w (M.face x) = w x) (hchain : w (a i₀) + w (b i₀) = 0) :
    ∃ R : PictureMap {x : D // ¬ InDipole a b x},
      R.GenusZero ∧ R.Respects (label ∘ Subtype.val) start rev ∧
      (∀ x, (R.face x).val = M.face x.val) ∧
      cycles R.face = cycles M.face - 2 ∧
      ∃ hR : ∀ x, (w ∘ Subtype.val) (R.face x) = (w ∘ Subtype.val) x,
        faceChain R.face (w ∘ Subtype.val) hR = faceChain M.face w hw := by
  classical
  obtain ⟨N,hf,hn,hng,_,hp⟩ := M.isolate_dipole hF i₀ hseed hM hG hinv hop
  have hfn : OppositeFaces N.face q a b := by rw [hf]; exact hF
  have hwn : ∀ x, w (N.face x) = w x := by rw [hf]; exact hw
  let R := N.removeDipole hfn hp
  refine ⟨R,?_,?_,?_,?_,?_⟩
  · convert N.removeDipole_genusZero hfn hp hng using 1
  · exact N.restrict_respects hn _ _ _
  · intro x
    change N.face x.val = M.face x.val
    rw [hf]
  · convert N.removeDipole_faces hfn hp i₀ using 1
    all_goals try with_reducible_and_instances rfl
    rw [hf]
  · refine ⟨fun x => hwn x.val,?_⟩
    have hh := N.removeDipole_chain hfn hp i₀ w hwn hchain
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [hf]

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordDisk
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


/-! Algebraic van Kampen existence, with actual words and area-counted local
moves (not a finiteness or isoperimetric assumption). Free cancellation has
zero cost; each orientation of a listed relator disk has cost one. -/
noncomputable section
namespace HyperbolicObstruction.WordPictures

variable {A : Type*}

lemma move_sound {R : Set (Word A)} {u v : Word A} {n : ℕ} (h : Move R u v n) :
    PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk u) =
      PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk v) := by
  let f := PresentedGroup.mk (FreeGroup.mk '' R)
  cases h with
  | free h => exact congrArg f (Quot.sound h)
  | face l r w h =>
    have hw : f (FreeGroup.mk w) = 1 := PresentedGroup.one_of_mem ⟨w,h,rfl⟩
    change f _ = f _
    simp only [← FreeGroup.mul_mk,map_mul,hw,mul_one]
  | reverseFace l r w h =>
    have hw : f (FreeGroup.mk w) = 1 := PresentedGroup.one_of_mem ⟨w,h,rfl⟩
    change f _ = f _
    simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk,map_mul,map_inv,hw,inv_one,mul_one]

lemma sound {R : Set (Word A)} {u v : Word A} {n : ℕ} (h : Homotopy R u v n) :
    PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk u) =
      PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk v) := by
  induction h with
  | refl => rfl
  | move h => exact move_sound h
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PresentationDisk
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace LetterPresentation
open IncidenceTemplate MasterGraph
variable (n : ℕ)

lemma freeLetter_mk (a : Alphabet n) : freeLetter n a = FreeGroup.mk [a] := by
  rcases a with ⟨i,b⟩
  cases b <;> rfl

lemma mk_prod (w : List (Alphabet n)) :
    FreeGroup.mk w = (w.map (freeLetter n)).prod := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change FreeGroup.mk ([a]++w) = freeLetter n a * (w.map (freeLetter n)).prod
    rw [← FreeGroup.mul_mk,← freeLetter_mk,ih]

lemma mk_stepLetter {a b : MasterGraph.Vertex} (l : Field → Alphabet n) (s : MasterGraph.Step a b) :
    FreeGroup.mk [stepLetter n l s] = s.value l (freeLetter n) := by
  rw [← freeLetter_mk]
  cases h : s.forward <;> simp [stepLetter,Step.value,h,freeLetter_inv]

def pathWord (l : Field → Alphabet n) : {a b : MasterGraph.Vertex} → MasterGraph.Path a b → List (Alphabet n)
  | _,_,.nil _ => []
  | _,_,.cons s p => stepLetter n l s :: pathWord l p

lemma pathWord_length {a b : MasterGraph.Vertex} (l : Field → Alphabet n) (p : MasterGraph.Path a b) :
    (pathWord n l p).length = p.length := by
  induction p with
  | nil => rfl
  | cons s p ih => simp [pathWord,Path.length,ih]

lemma mk_pathWord {a b : MasterGraph.Vertex} (l : Field → Alphabet n) (p : MasterGraph.Path a b) :
    FreeGroup.mk (pathWord n l p) = p.eval l (freeLetter n) := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    change FreeGroup.mk ([stepLetter n l s] ++ pathWord n l p) = _
    rw [← FreeGroup.mul_mk,mk_stepLetter,ih]
    rfl

lemma mk_literalSquare (l : Field → Alphabet n) (τ : TwoPath) :
    FreeGroup.mk (literalSquare n l τ) = squareWord l (freeLetter n) τ := by
  rw [mk_prod]
  simp only [literalSquare,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rw [freeLetter_mk,freeLetter_mk,mk_stepLetter,mk_stepLetter]
  simp only [squareWord,mul_assoc]

variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Literal boundaries, retaining every side index of its graph walk or row.
The arbitrary fan/top walks will later be reduced to a finite list of defining
cycles; the disk theorem here has no area estimate. -/
inductive WordRelator : List (Alphabet n) → Prop
  | fan (l : Field → Alphabet n) (i : Fin 7)
      (present : w (TableModel.row rowSupport l (.inl i)) = true)
      (v : MasterGraph.Vertex) (p : MasterGraph.Path v v)
      (fields : p.fields.toFinset ⊆ rowSupport (.inl i)) : WordRelator (pathWord n l p)
  | top (l : Field → Alphabet n)
      (present : w (TableModel.row rowSupport l (.inr (.inl ()))) = true)
      (fans : ∀ i : Fin 7, w (TableModel.row rowSupport l (.inl i)) = true)
      (v : MasterGraph.Vertex) (p : MasterGraph.Path v v) (core : p.IsCore) :
      WordRelator (pathWord n l p)
  | square (l : Field → Alphabet n) (τ : TwoPath)
      (present : w (TableModel.row rowSupport l (.inr (.inr τ))) = true) :
      WordRelator (literalSquare n l τ)
  | six (x : Fin 6 → Alphabet n) (present : d x = true) : WordRelator (List.ofFn x)

lemma mk_ofFn (x : Fin 6 → Alphabet n) :
    FreeGroup.mk (List.ofFn x) = (List.ofFn (freeLetter n ∘ x)).prod := by
  rw [mk_prod,List.map_ofFn]

lemma wordRelator_image : FreeGroup.mk '' WordRelator n w d = Relator n w d := by
  ext g
  constructor
  · rintro ⟨v,hv,rfl⟩
    cases hv with
    | fan l i present v p fields =>
      rw [mk_pathWord]
      exact Relator.fan l i present v p fields
    | top l present fans v p core =>
      rw [mk_pathWord]
      exact Relator.top l present fans v p core
    | square l τ present =>
      rw [mk_literalSquare]
      exact Relator.square l τ present
    | six x present =>
      rw [mk_ofFn]
      exact Relator.six x present
  · intro hg
    cases hg with
    | fan l i present v p fields =>
      exact ⟨_,WordRelator.fan l i present v p fields,mk_pathWord n l p⟩
    | top l present fans v p core =>
      exact ⟨_,WordRelator.top l present fans v p core,mk_pathWord n l p⟩
    | square l τ present =>
      exact ⟨_,WordRelator.square l τ present,mk_literalSquare n l τ⟩
    | six x present => exact ⟨_,WordRelator.six x present,mk_ofFn n x⟩

end LetterPresentation
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FaceSplice
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.instFinite _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap
variable (M : PictureMap D)

lemma components_le_splice (a b : D) (h : (M.splice a b).components a b) :
    M.components ≤ (M.splice a b).components := by
  let s := (M.splice a b).components
  have ht : ∀ x, s x (swap a b x) := fun x =>
    sameCycle_swap_le h SameCycle.rfl.apply_right
  apply M.components_le
  · intro x
    have hf := (M.splice a b).face_le_components (SameCycle.rfl (x := swap a b x)).apply_right
    have he : (M.splice a b).face (swap a b x) = M.face x := by simp [splice]
    rw [he] at hf
    exact s.trans' (ht x) hf
  · intro x
    exact (M.splice a b).edge_le_components SameCycle.rfl.apply_right

/-- Two components are joined, with their actual new component equivalence
exactly the quotient gluing relation. -/
theorem splice_components (a b : D) (h : ¬ M.components a b) :
    (M.splice a b).components = glue M.components a b := by
  have hf : ¬ M.face.SameCycle a b := fun hh => h (M.face_le_components hh)
  have hn : (M.splice a b).components a b :=
    (M.splice a b).face_le_components (sameCycle_after_swap_right M.face hf)
  apply le_antisymm (M.splice_components_le a b)
  exact glue_le _ _ _ (M.components_le_splice a b hn) hn

lemma splice_euler (a b : D) (h : ¬ M.components a b) :
    (M.splice a b).euler + 2 = M.euler := by
  have hf : ¬ M.face.SameCycle a b := fun hh => h (M.face_le_components hh)
  have hv : ¬ M.vertex.SameCycle (M.edge a) (M.edge b) := by
    intro hh
    exact h (M.components.trans' (M.edge_le_components (SameCycle.rfl (x := a)).apply_right)
      (M.components.trans' (M.vertex_le_components hh)
        (M.components.symm' (M.edge_le_components (SameCycle.rfl (x := b)).apply_right))))
  have hF := cycles_merge_right M.face hf
  have hV := cycles_merge_right M.vertex hv
  rw [euler,euler,splice_vertex]
  change cycles (M.vertex * swap (M.edge a) (M.edge b)) + cycles (M.face * swap a b) - _ + 2 = _
  omega

/-- Joining two genus-zero components along the outside face preserves genus
zero. This is the finite combinatorial gluing used to assemble disk pictures. -/
theorem splice_genusZero (hM : M.GenusZero) (a b : D) (h : ¬ M.components a b) :
    (M.splice a b).GenusZero := by
  have hE := M.splice_euler a b h
  have hC := card_glue M.components a b
  rw [ite_eq_right h] at hC
  rw [← M.splice_components a b h] at hC
  change M.euler = _ at hM
  change (M.splice a b).euler = _
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FaceWalk
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D C V : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap

omit [Fintype D] in
lemma splice_closed {M : PictureMap D} {source target : D → V}
    (hclosed : M.FaceClosed source target) {a b : D} (hab : target a = target b) :
    (M.splice a b).FaceClosed source target := by
  intro x
  change source (M.face (swap a b x)) = target x
  rw [hclosed,Equiv.apply_swap_eq_self hab]

omit [Fintype D] in
lemma splice_kind {M : PictureMap D} {kind : D → C} (hk : M.FaceKind kind)
    {a b : D} (hab : kind a = kind b) : (M.splice a b).FaceKind kind := by
  intro x
  change kind (M.face (swap a b x)) = kind x
  rw [hk,Equiv.apply_swap_eq_self hab]

/-- Split repeated vertex visits in selected kinds of closed polygon walks.
Only face permutations change; all oriented steps, occurrence indices, edge
pairings and therefore every additive cone-step chain are retained literally.
Unselected faces retain their entire cyclic parametrization. The normalization
is a finite maximization, not an assumed simple-polygon representative. -/
theorem normalize_simple_faces (M : PictureMap D) (hG : M.GenusZero)
    (source target : D → V) (hc : M.FaceClosed source target)
    (kind : D → C) (hk : M.FaceKind kind) (free : C → Bool) :
    ∃ N : PictureMap D,
      N.edge = M.edge ∧ N.GenusZero ∧ N.FaceClosed source target ∧ N.FaceKind kind ∧
      (∀ x, free (kind x) = false → N.face x = M.face x) ∧
      ∀ a b, free (kind a) = true → N.face.SameCycle a b → target a = target b → a = b := by
  classical
  let good : PictureMap D → Prop := fun N =>
    N.edge = M.edge ∧ N.GenusZero ∧ N.FaceClosed source target ∧ N.FaceKind kind ∧
      ∀ x, free (kind x) = false → N.face x = M.face x
  let := Fintype.ofFinite (PictureMap D)
  let s := Finset.univ.filter good
  have hm : M ∈ s := by
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨rfl,hG,hc,hk,fun _ _ => rfl⟩
  obtain ⟨N,hN,hmax⟩ := s.exists_max_image (fun N => cycles N.face) ⟨M,hm⟩
  have hn : good N := (Finset.mem_filter.mp hN).2
  refine ⟨N,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,?_⟩
  intro a b ha hab ht
  by_contra hne
  have hk' : kind a = kind b := kind_cycle hn.2.2.2.1 hab
  have hsplit : good (N.splice a b) := by
    refine ⟨hn.1,N.split_genusZero hn.2.1 a b hne hab,
      splice_closed hn.2.2.1 ht,splice_kind hn.2.2.2.1 hk',?_⟩
    intro x hx
    have hxa : x ≠ a := by intro he; rw [he,ha] at hx; cases hx
    have hxb : x ≠ b := by intro he; rw [he,← hk',ha] at hx; cases hx
    change N.face (swap a b x) = M.face x
    rw [swap_apply_of_ne_of_ne hxa hxb]
    exact hn.2.2.2.2 x hx
  have hmem : N.splice a b ∈ s := by
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hsplit
  have hbound := hmax (N.splice a b) hmem
  have hinc := cycles_split_right N.face hne hab
  change cycles (N.face * swap a b) ≤ cycles N.face at hbound
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkCell
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r

variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]

attribute [instance] WalkPicture.finite WalkPicture.decEq

namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

lemma bigon_opposite {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (h₂ : P.pairing.face (P.pairing.face a) = a) :
    P.index (P.pairing.face a) = T.opposite (P.index a) := by
  apply T.simple _ _ (P.free_face ha)
  · exact (P.kind a).trans (T.opposite_kind (P.index a)).symm
  · exact (P.closed a).trans (T.opposite_front (P.index a)).symm
  · have hc := P.closed (P.pairing.face a)
    dsimp only [Function.comp_apply] at hc
    rw [← hc,h₂,T.opposite_back]

/-- The finite splitting producer acts on template vertices, NOT quotient
letter vertices. Consequently a top can never acquire a false repeated
visit merely because several numerical generator labels coincide. -/
theorem makeSimple : ∃ Q : WalkPicture.{u} T,
    Nonempty (P.Retains Q) ∧ Q.Simple ∧ Q.chain = P.chain := by
  obtain ⟨N,hE,hG,hC,hK,hF,hS⟩ := P.pairing.normalize_simple_faces P.genusZero
    (T.front ∘ P.index) (T.back ∘ P.index) P.closed (T.kind ∘ P.index) P.kind T.free
  let Q : WalkPicture.{u} T := {
    Dart := P.Dart
    pairing := N
    index := P.index
    closed := hC
    kind := hK
    paired := by intro x; rw [hE]; exact P.paired x
    genusZero := hG }
  exact ⟨Q,⟨⟨id,Function.injective_id,fun _ => rfl,hF,fun x _ => ⟨x,rfl⟩⟩⟩,hS,rfl⟩

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FrozenWalk
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]

namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

variable {P}

variable (P)

/-- Opposite frozen indexed sides determine the COMPLETE opposite faces,
inside the ambient mixed free/frozen picture. -/
theorem frozen_opposite_faces (B : FrozenTarget T) (hm : P.FrozenMapped B)
    (a b : P.Dart) (ha : T.free (T.kind (P.index a)) = false)
    (hop : P.index b = T.opposite (P.index a)) :
    let a' : P.FrozenDart := ⟨a,ha⟩
    let I := {x : P.FrozenDart // P.frozenFace.SameCycle a' x}
    ∃ q : Perm I, ∃ v : I → P.Dart,
      PictureMap.OppositeFaces P.pairing.face q (fun x => x.val.val) v ∧
      v ⟨a',SameCycle.rfl⟩ = b ∧ ∀ x, P.index (v x) = T.opposite (P.index x.val.val) := by
  dsimp only
  let a' : P.FrozenDart := ⟨a,ha⟩
  let b' : P.FrozenDart := ⟨b,P.opposite_frozen ha hop⟩
  obtain ⟨q,v,hF,hb,hv⟩ := hm.opposite_faces B.reverse B.reverse_sq B.reverse_next
    B.opposite_cycle a' b' (by change P.index b = B.reverse (P.index a); rw [B.reverse_eq]; exact hop)
  refine ⟨q,fun x => (v x).val,?_,congrArg Subtype.val hb,?_⟩
  · refine ⟨Subtype.val_injective.comp Subtype.val_injective,
      Subtype.val_injective.comp hF.b_inj,?_,?_,?_,hF.cyclic⟩
    · intro x y he
      exact hF.disjoint x y (Subtype.ext he)
    · intro x
      exact congrArg Subtype.val (hF.a_face x)
    · intro x
      exact congrArg Subtype.val (hF.b_face x)
  · intro x
    exact (hv x).trans (B.reverse_eq _)

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FrozenCancel
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

/-- Frozen dipole cancellation in a picture which also has arbitrary free
macro faces. It removes complete opposite frozen cells, preserves every
surviving frozen face, and preserves the exact elementary signed chain. -/
theorem cancel_frozen (B : FrozenTarget T) (hm : P.FrozenMapped B)
    (a : P.Dart) (ha : T.free (T.kind (P.index a)) = false)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a)) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Survives Q) ∧ Q.FrozenMapped B ∧
      Fintype.card Q.Dart < Fintype.card P.Dart ∧ Q.chain = P.chain := by
  let a' : P.FrozenDart := ⟨a,ha⟩
  let I := {x : P.FrozenDart // P.frozenFace.SameCycle a' x}
  obtain ⟨q,v,hF,hv,hmap⟩ := P.frozen_opposite_faces B hm a (P.pairing.edge a) ha hop
  let i₀ : I := ⟨a',SameCycle.rfl⟩
  obtain ⟨R,hRG,hRM,hRF,hRC,hRW,hRchain⟩ := P.pairing.cancel_mapped_dipole hF i₀ hv.symm
    P.respects P.genusZero T.rev_rev
    (fun i => by change T.label (P.index (v i)) = _; rw [hmap,T.opposite_label]; rfl)
    (fun _ : P.Dart => (0 : ℤ)) (fun _ => rfl) (by simp)
  let Q : WalkPicture.{u} T := {
    Dart := {x : P.Dart // ¬ PictureMap.InDipole (fun y : I => y.val.val) v x}
    pairing := R
    index := P.index ∘ Subtype.val
    closed := by
      intro x
      change T.front (P.index (R.face x).val) = T.back (P.index x.val)
      rw [hRF]
      exact P.closed x.val
    kind := by
      intro x
      change T.kind (P.index (R.face x).val) = T.kind (P.index x.val)
      rw [hRF]
      exact P.kind x.val
    paired := hRM.2
    genusZero := hRG }
  have hret : P.Survives Q :=
    ⟨Subtype.val,Subtype.val_injective,fun _ => rfl,fun x _ => hRF x⟩
  refine ⟨Q,⟨hret⟩,hret.frozenMapped P B hm,?_,?_⟩
  · exact Fintype.card_subtype_lt (x := a) (by
      intro hh
      exact hh (Or.inl ⟨i₀,rfl⟩))
  · change (∑ x : {x : P.Dart // ¬ PictureMap.InDipole (fun y : I => y.val.val) v x},
        T.weight (P.index x.val)) = ∑ x : P.Dart, T.weight (P.index x)
    apply PictureMap.sum_not_inDipole hF (T.weight ∘ P.index)
    intro i
    change T.weight (P.index i.val.val) + T.weight (P.index (v i)) = 0
    rw [hmap,← B.reverse_eq]
    exact B.opposite_weight _

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BigonRemove
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}
namespace PictureMap
variable {M : PictureMap D} {a b : D}

namespace Bigon
variable (h : M.Bigon a b)
include h

variable [DecidableEq D]

lemma remove_closed {V : Type*} {source target : D → V}
    (hc : M.FaceClosed source target) : h.remove.FaceClosed (source ∘ Subtype.val) (target ∘ Subtype.val) :=
  fun x => hc x.val

lemma remove_kind {C : Type*} {kind : D → C} (hk : M.FaceKind kind) :
    h.remove.FaceKind (kind ∘ Subtype.val) := fun x => hk x.val

end Bigon
end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeMerge
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}
namespace PictureMap
variable (M : PictureMap D) {a b : D}

variable [DecidableEq D]

/-- Delete the paired sides and join the remaining oriented boundaries.
Unlike cancellation of an entire equal pair of cells, this works when the
remaining boundaries differ. -/
def mergeEdge (h : M.MergeSide a b) : PictureMap {x // OffPair a b x} where
  face := erasePair (M.face * swap a b) h.ne
  edge := M.edge.subtypePerm h.edge_invariant
  edge_sq := by ext x; exact M.edge_edge x.val
  edge_ne := by intro x he; exact M.edge_ne x.val (congrArg Subtype.val he)

lemma mergeEdge_vertex (h : M.MergeSide a b) :
    (M.mergeEdge h).vertex = erasePair M.vertex h.ne := by
  ext x
  change bypassPair (M.face * swap a b) a b (M.edge x.val) = bypassPair M.vertex a b x.val
  have hx := (h.edge_invariant x.val).mpr x.property
  have he := congrArg (fun p : Perm D => p x.val) h.erase_identity
  simpa only [mul_apply,swap_apply_of_ne_of_ne hx.1 hx.2] using he

variable [Fintype D]

lemma mergeEdge_faces (h : M.MergeSide a b) :
    cycles (M.mergeEdge h).face + 1 = cycles M.face := by
  have ha : (M.face * swap a b) a ≠ a := by rw [MergeSide.crossed_a]; exact h.face_right_ne_left
  have hb : bypass (M.face * swap a b) a b ≠ b := by rw [h.crossed_b]; exact h.face_left_ne_right
  change cycles (erasePair (M.face * swap a b) h.ne) + 1 = _
  rw [erasePair_cycles _ h.ne ha hb]
  exact cycles_merge_right M.face h.distinct_faces

lemma mergeEdge_vertices (h : M.MergeSide a b) :
    cycles (M.mergeEdge h).vertex = cycles M.vertex := by
  rw [mergeEdge_vertex]
  apply erasePair_cycles _ h.ne
  · rw [h.vertex_a]; exact h.face_right_ne_left
  · rw [h.vertex_b]; exact h.face_left_ne_right

lemma mergeEdge_euler (h : M.MergeSide a b) : (M.mergeEdge h).euler = M.euler := by
  have hf := M.mergeEdge_faces h
  have hv := M.mergeEdge_vertices h
  have hd := card_offPair h.ne
  have hde := M.card_darts_even
  have hde' := (M.mergeEdge h).card_darts_even
  rw [euler,euler,hv]
  obtain ⟨k,hk⟩ := hde
  obtain ⟨l,hl⟩ := hde'
  have hn : (Fintype.card {x // OffPair a b x} : ℤ) + 2 = Fintype.card D := by exact_mod_cast hd
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeMergeComponents
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap
variable {M : PictureMap D} {a b : D} (h : M.MergeSide a b)
namespace MergeSide
include h

lemma old_face_le_crossed : SameCycle.setoid M.face ≤ SameCycle.setoid (M.face * swap a b) := by
  have hab : (M.face * swap a b).SameCycle a b := sameCycle_after_swap_right M.face h.distinct_faces
  apply sameCycle_le_of_apply
  intro x
  have ht := sameCycle_swap_le (s := SameCycle.setoid (M.face * swap a b)) hab (SameCycle.rfl (x := x)).apply_right
  have hf := (SameCycle.rfl (f := M.face * swap a b) (x := swap a b x)).apply_right
  have he : (M.face * swap a b) (swap a b x) = M.face x := by simp
  rw [he] at hf
  exact ht.trans hf

lemma crossed_le_components : SameCycle.setoid (M.face * swap a b) ≤ M.components := by
  apply sameCycle_mul_le M.face_le_components
  apply sameCycle_swap_le
  rw [← h.paired]
  exact M.edge_le_components SameCycle.rfl.apply_right

lemma representative_crossed (x : D) :
    (M.face * swap a b).SameCycle x (h.representative x).val := by
  by_cases hx : OffPair a b x
  · simp only [representative,dite_eq_left hx]; exact SameCycle.rfl
  · have hh : x = a ∨ x = b := by unfold OffPair at hx; tauto
    rcases hh with rfl|rfl
    · rw [h.representative_a]
      exact h.old_face_le_crossed SameCycle.rfl.apply_right
    · rw [h.representative_b]
      exact (sameCycle_after_swap_right M.face h.distinct_faces).symm.trans
        (h.old_face_le_crossed SameCycle.rfl.apply_right)

lemma representative_face (x : D) :
    (M.mergeEdge h).face.SameCycle (h.representative x) (h.representative (M.face x)) := by
  change (erasePair (M.face * swap a b) h.ne).SameCycle _ _
  rw [erasePair_orbits]
  exact (h.representative_crossed x).symm.trans
    ((h.old_face_le_crossed SameCycle.rfl.apply_right).trans (h.representative_crossed (M.face x)))

omit [Fintype D] in
lemma representative_edge (x : D) :
    (M.mergeEdge h).components (h.representative x) (h.representative (M.edge x)) := by
  by_cases hx : OffPair a b x
  · have he := (h.edge_invariant x).mpr hx
    have hr : h.representative (M.edge x) = (M.mergeEdge h).edge (h.representative x) := by
      apply Subtype.ext
      simp only [representative,dite_eq_left hx,dite_eq_left he,mergeEdge,subtypePerm_apply]
    rw [hr]
    exact (M.mergeEdge h).edge_le_components SameCycle.rfl.apply_right
  · have hh : x = a ∨ x = b := by unfold OffPair at hx; tauto
    rcases hh with rfl|rfl
    · rw [h.paired,h.representative_a,h.representative_b]
      try exact (M.mergeEdge h).components.refl' _
    · rw [h.paired_back,h.representative_a,h.representative_b]
      try exact (M.mergeEdge h).components.refl' _

lemma retained_components :
    (M.mergeEdge h).components ≤ M.components.comap (Subtype.val : {x // OffPair a b x} → D) := by
  apply (M.mergeEdge h).components_le
  · intro x
    apply h.crossed_le_components
    apply (erasePair_orbits (M.face * swap a b) h.ne x ((M.mergeEdge h).face x)).mp
    exact SameCycle.rfl.apply_right
  · intro x
    exact M.edge_le_components (SameCycle.rfl (x := x.val)).apply_right

/-- No component is created or lost by deleting a common side of distinct
faces, even when their boundaries also touch elsewhere. -/
theorem component_card : Nat.card (Quotient (M.mergeEdge h).components) = Nat.card (Quotient M.components) := by
  let N := M.mergeEdge h
  let j : D → Quotient N.components := fun x => Quotient.mk _ (h.representative x)
  have hforward : M.components ≤ Setoid.ker j := by
    apply M.components_le
    · intro x
      exact Quotient.sound (N.face_le_components (h.representative_face x))
    · intro x
      exact Quotient.sound (h.representative_edge x)
  have hrel (x y : D) : M.components x y ↔ j x = j y := by
    constructor
    · intro hh; exact hforward hh
    · intro he
      have hn : N.components (h.representative x) (h.representative y) := Quotient.exact he
      have hh := h.retained_components hn
      exact M.components.trans' (h.crossed_le_components (h.representative_crossed x))
        (M.components.trans' hh (M.components.symm' (h.crossed_le_components (h.representative_crossed y))))
  have hj : Function.Surjective j := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      refine ⟨x.val,?_⟩
      change Quotient.mk N.components (h.representative x.val) = Quotient.mk N.components x
      rw [h.representative_kept]
  exact (card_quotient_of_classifier M.components j hrel hj).symm
end MergeSide

/-- The connected edge-cancellation surgery preserves literal genus zero
and removes exactly one face and two darts. -/
theorem mergeEdge_genusZero (hG : M.GenusZero) : (M.mergeEdge h).GenusZero := by
  change (M.mergeEdge h).euler = _
  rw [M.mergeEdge_euler h,h.component_card]
  exact hG

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MergeWalk
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D C L V : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap
variable {M : PictureMap D} {a b : D} (h : M.MergeSide a b)

lemma mergeEdge_respects {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) :
    (M.mergeEdge h).Respects (label ∘ Subtype.val) start rev := by
  constructor
  · intro x
    have hc : M.vertex.SameCycle x.val ((M.mergeEdge h).vertex x).val := by
      apply (erasePair_orbits M.vertex h.ne x ((M.mergeEdge h).vertex x)).mp
      rw [← M.mergeEdge_vertex h]
      exact SameCycle.rfl.apply_right
    exact ((sameCycle_le_of_apply (s := Setoid.ker (start ∘ label))
      (fun x => (hM.1 x).symm)) hc).symm
  · intro x
    exact hM.2 x.val

lemma mergeEdge_kind {kind : D → C} (hk : M.FaceKind kind) (hab : kind a = kind b) :
    (M.mergeEdge h).FaceKind (kind ∘ Subtype.val) := by
  intro x
  have hc : (M.splice a b).face.SameCycle x.val ((M.mergeEdge h).face x).val := by
    exact (erasePair_orbits (M.face * swap a b) h.ne x ((M.mergeEdge h).face x)).mp SameCycle.rfl.apply_right
  exact (kind_cycle (splice_kind hk hab) hc).symm

omit [Fintype D] in
lemma mergeEdge_face_of_away (x : {x // OffPair a b x})
    (ha : M.face x.val ≠ a) (hb : M.face x.val ≠ b) :
    ((M.mergeEdge h).face x).val = M.face x.val := by
  change bypass (bypass (M.face * swap a b) a) b x.val = M.face x.val
  rw [bypass_away _ _ _ x.property.2,bypass_away _ _ _ x.property.1]
  simp only [mul_apply,swap_apply_of_ne_of_ne x.property.1 x.property.2,ite_eq_right ha,ite_eq_right hb]

omit [Fintype D] in
lemma mergeEdge_face_hit_left (x : {x // OffPair a b x})
    (hx : M.face x.val = a) : ((M.mergeEdge h).face x).val = M.face b := by
  change bypass (bypass (M.face * swap a b) a) b x.val = M.face b
  rw [bypass_away _ _ _ x.property.2,bypass_away _ _ _ x.property.1]
  simp only [mul_apply,swap_apply_of_ne_of_ne x.property.1 x.property.2,hx,ite_eq_left,
    swap_apply_left,ite_eq_right h.right_nonmonogon]

omit [Fintype D] in
lemma mergeEdge_face_hit_right (x : {x // OffPair a b x})
    (hx : M.face x.val = b) : ((M.mergeEdge h).face x).val = M.face a := by
  change bypass (bypass (M.face * swap a b) a) b x.val = M.face a
  rw [bypass_away _ _ _ x.property.2,bypass_away _ _ _ x.property.1]
  simp only [mul_apply,swap_apply_of_ne_of_ne x.property.1 x.property.2,hx,ite_eq_right h.ne.symm,ite_eq_left]
  exact h.crossed_b

omit [Fintype D] in
/-- Closure in indexed template vertices is retained even though adjacent
polygons belonging to OTHER occurrences use different template vertex types.
Only the two cancelling sides need agree as opposite template steps. -/
lemma mergeEdge_closed_local {source target : D → V} (hc : M.FaceClosed source target)
    (ha : source a = target b) (hb : source b = target a) :
    (M.mergeEdge h).FaceClosed (source ∘ Subtype.val) (target ∘ Subtype.val) := by
  intro x
  change source ((M.mergeEdge h).face x).val = target x.val
  by_cases hxa : M.face x.val = a
  · rw [mergeEdge_face_hit_left h x hxa,hc,← ha]
    exact (congrArg source hxa).symm.trans (hc x.val)
  by_cases hxb : M.face x.val = b
  · rw [mergeEdge_face_hit_right h x hxb,hc,← hb]
    exact (congrArg source hxb).symm.trans (hc x.val)
  · rw [mergeEdge_face_of_away h x hxa hxb,hc]

omit [Fintype D] in
/-- Any frozen kind disjoint from the cancelled kind retains its complete
face cycles and side indices under the common-side cancellation. -/
lemma mergeEdge_face_frozen {kind : D → C} (hk : M.FaceKind kind)
    (free : C → Bool) (ha : free (kind a) = true) (hb : free (kind b) = true)
    (x : {x // OffPair a b x}) (hx : free (kind x.val) = false) :
    ((M.mergeEdge h).face x).val = M.face x.val := by
  apply mergeEdge_face_of_away h x
  · intro he
    have hh := congrArg free (hk x.val)
    rw [he,ha,hx] at hh
    cases hh
  · intro he
    have hh := congrArg free (hk x.val)
    rw [he,hb,hx] at hh
    cases hh

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkCancel
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

def deletedBigon {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (h₂ : P.pairing.face (P.pairing.face a) = a) : WalkPicture.{u} T := by
  let h : P.pairing.Bigon a (P.pairing.face a) :=
    ⟨(P.nonmonogon ha).symm,rfl,h₂⟩
  exact {
    Dart := {x : P.Dart // OffPair a (P.pairing.face a) x}
    pairing := h.remove
    index := P.index ∘ Subtype.val
    closed := h.remove_closed P.closed
    kind := h.remove_kind P.kind
    paired := (h.remove_respects P.respects (P.reverse_label (P.bigon_opposite ha h₂))).2
    genusZero := h.remove_genusZero P.genusZero }

lemma deletedBigon_retains {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (h₂ : P.pairing.face (P.pairing.face a) = a) :
    Nonempty (P.Retains (P.deletedBigon ha h₂)) := by
  refine ⟨⟨Subtype.val,Subtype.val_injective,fun _ => rfl,fun _ _ => rfl,?_⟩⟩
  intro x hx
  have hxa : x ≠ a := by intro he; rw [he,ha] at hx; cases hx
  have hxb : x ≠ P.pairing.face a := by intro he; rw [he,P.free_face ha] at hx; cases hx
  exact ⟨⟨x,hxa,hxb⟩,rfl⟩

lemma deletedBigon_chain {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (h₂ : P.pairing.face (P.pairing.face a) = a) : (P.deletedBigon ha h₂).chain = P.chain := by
  change (∑ x : {x : P.Dart // OffPair a (P.pairing.face a) x}, T.weight (P.index x.val)) =
    ∑ x : P.Dart, T.weight (P.index x)
  apply sum_offPair (P.nonmonogon ha).symm (T.weight ∘ P.index)
  change T.weight (P.index a) + T.weight (P.index (P.pairing.face a)) = 0
  rw [P.bigon_opposite ha h₂]
  exact T.opposite_weight _ ha

def cancelledSide {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a))
    (hf : ¬ P.pairing.face.SameCycle a (P.pairing.edge a)) : WalkPicture.{u} T := by
  let h := P.mergeSide ha hop hf
  exact {
    Dart := {x : P.Dart // OffPair a (P.pairing.edge a) x}
    pairing := P.pairing.mergeEdge h
    index := P.index ∘ Subtype.val
    closed := PictureMap.mergeEdge_closed_local h P.closed
      (by change T.front (P.index a) = T.back (P.index (P.pairing.edge a)); rw [hop,T.opposite_back])
      (by change T.front (P.index (P.pairing.edge a)) = T.back (P.index a); rw [hop,T.opposite_front])
    kind := PictureMap.mergeEdge_kind h P.kind
      (by change T.kind (P.index a) = T.kind (P.index (P.pairing.edge a)); rw [hop,T.opposite_kind])
    paired := (PictureMap.mergeEdge_respects h P.respects).2
    genusZero := P.pairing.mergeEdge_genusZero h P.genusZero }

lemma cancelledSide_retains {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a))
    (hf : ¬ P.pairing.face.SameCycle a (P.pairing.edge a)) :
    Nonempty (P.Retains (P.cancelledSide ha hop hf)) := by
  refine ⟨⟨Subtype.val,Subtype.val_injective,fun _ => rfl,?_,?_⟩⟩
  · intro x hx
    exact PictureMap.mergeEdge_face_frozen (P.mergeSide ha hop hf) P.kind T.free ha
      (P.free_of_opposite ha hop) x hx
  · intro x hx
    have hxa : x ≠ a := by intro he; rw [he,ha] at hx; cases hx
    have hxb : x ≠ P.pairing.edge a := by
      intro he; rw [he,P.free_of_opposite ha hop] at hx; cases hx
    exact ⟨⟨x,hxa,hxb⟩,rfl⟩

lemma cancelledSide_chain {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a))
    (hf : ¬ P.pairing.face.SameCycle a (P.pairing.edge a)) :
    (P.cancelledSide ha hop hf).chain = P.chain := by
  change (∑ x : {x : P.Dart // OffPair a (P.pairing.edge a) x}, T.weight (P.index x.val)) =
    ∑ x : P.Dart, T.weight (P.index x)
  apply sum_offPair (P.pairing.edge_ne a).symm (T.weight ∘ P.index)
  change T.weight (P.index a) + T.weight (P.index (P.pairing.edge a)) = 0
  rw [hop]
  exact T.opposite_weight _ ha

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkNormal
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

lemma opposite_distinct_faces (hs : P.Simple) (hn : P.NoBigon) {a : P.Dart}
    (ha : T.free (T.kind (P.index a)) = true)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a)) :
    ¬ P.pairing.face.SameCycle a (P.pairing.edge a) := by
  intro hf
  have h₁ : P.pairing.face a = P.pairing.edge a := by
    apply P.simple_front hs (P.free_face ha) hf.apply_left
    exact (P.closed a).trans (by change T.back (P.index a) = _; rw [hop,T.opposite_front])
  have h₂ : P.pairing.face (P.pairing.edge a) = a := by
    apply P.simple_front hs (P.free_face (P.free_of_opposite ha hop)) hf.symm.apply_left
    exact (P.closed (P.pairing.edge a)).trans (by change T.back (P.index (P.pairing.edge a)) = _; rw [hop,T.opposite_back])
  exact hn a ha (by rw [h₁,h₂])

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRadial
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

lemma makeSimpleRadial (apex : V → Bool)
    (hr : ∀ s, apex (T.start (T.label s)) = true →
      apex (T.start (T.rev (T.label s))) = false) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Retains Q) ∧
      Q.Simple ∧ Q.RadialInjective apex ∧ Q.chain = P.chain := by
  obtain ⟨P',⟨hret⟩,hs,hc⟩ := P.makeSimple
  obtain ⟨N,hf,hN,hG,hinj⟩ := PictureMap.normalize_radial apex P'.respects P'.genusZero
    (fun x => hr (P'.index x))
  let Q : WalkPicture.{u} T := {
    Dart := P'.Dart
    pairing := N
    index := P'.index
    closed := by unfold PictureMap.FaceClosed; rw [hf]; exact P'.closed
    kind := by unfold PictureMap.FaceKind; rw [hf]; exact P'.kind
    paired := hN.2
    genusZero := hG }
  have hRQ : P'.Retains Q := {
    map := id
    injective := Function.injective_id
    index := fun _ => rfl
    face := fun x _ => congrArg (fun p : Perm P'.Dart => p x) hf
    complete := fun x _ => ⟨x,rfl⟩ }
  refine ⟨Q,⟨Retains.trans P hret hRQ⟩,?_,hinj,hc⟩
  change ∀ a b, _ → N.face.SameCycle a b → _ → a = b
  rw [hf]; exact hs

/-- Simultaneous macro simplicity, top-side cancellation, and radial-label
injectivity. Cross-pairing radial sides may create new cancellable macro
adjacencies; the induction re-tests and removes them rather than silently
assuming old reducedness survives a switch. -/
theorem normalize_radial (apex : V → Bool)
    (hr : ∀ s, apex (T.start (T.label s)) = true →
      apex (T.start (T.rev (T.label s))) = false) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Retains Q) ∧ Q.Simple ∧ Q.NoBigon ∧
      Q.Reduced ∧ Q.RadialInjective apex ∧ Q.chain = P.chain := by
  classical
  have produce : ∀ n, ∀ P : WalkPicture.{u} T, Fintype.card P.Dart = n →
      ∃ Q : WalkPicture.{u} T, Nonempty (P.Retains Q) ∧ Q.Simple ∧ Q.NoBigon ∧
        Q.Reduced ∧ Q.RadialInjective apex ∧ Q.chain = P.chain := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn
      obtain ⟨P',⟨hret⟩,hs,hrad,hc⟩ := P.makeSimpleRadial apex hr
      have hle : Fintype.card P'.Dart ≤ n := by
        rw [← hn]
        exact Fintype.card_le_of_injective _ hret.injective
      by_cases hnb : P'.NoBigon
      · by_cases hred : P'.Reduced
        · exact ⟨P',⟨hret⟩,hs,hnb,hred,hrad,hc⟩
        · obtain ⟨a,ha⟩ := not_forall.mp hred
          have ha : T.free (T.kind (P'.index a)) = true ∧
              P'.index (P'.pairing.edge a) = T.opposite (P'.index a) := by
            simpa only [Classical.not_imp,not_not] using ha
          have hf := P'.opposite_distinct_faces hs hnb ha.1 ha.2
          let P₀ := P'.cancelledSide ha.1 ha.2 hf
          have hsmall : Fintype.card P₀.Dart < n := by
            apply lt_of_lt_of_le _ hle
            exact Fintype.card_subtype_lt (x := a) (by intro h; exact h.1 rfl)
          obtain ⟨Q,⟨hq⟩,hqs,hqn,hqr,hqd,hqc⟩ := ih _ hsmall P₀ rfl
          obtain ⟨hcancel⟩ := P'.cancelledSide_retains ha.1 ha.2 hf
          exact ⟨Q,⟨Retains.trans P hret (Retains.trans P' hcancel hq)⟩,hqs,hqn,hqr,hqd,
            hqc.trans ((P'.cancelledSide_chain ha.1 ha.2 hf).trans hc)⟩
      · obtain ⟨a,ha⟩ := not_forall.mp hnb
        have ha : T.free (T.kind (P'.index a)) = true ∧
            P'.pairing.face (P'.pairing.face a) = a := by
          simpa only [Classical.not_imp,not_not] using ha
        let P₀ := P'.deletedBigon ha.1 ha.2
        have hsmall : Fintype.card P₀.Dart < n := by
          apply lt_of_lt_of_le _ hle
          exact Fintype.card_subtype_lt (x := a) (by intro h; exact h.1 rfl)
        obtain ⟨Q,⟨hq⟩,hqs,hqn,hqr,hqd,hqc⟩ := ih _ hsmall P₀ rfl
        obtain ⟨hdel⟩ := P'.deletedBigon_retains ha.1 ha.2
        exact ⟨Q,⟨Retains.trans P hret (Retains.trans P' hdel hq)⟩,hqs,hqn,hqr,hqd,
          hqc.trans ((P'.deletedBigon_chain ha.1 ha.2).trans hc)⟩
  exact produce (Fintype.card P.Dart) P rfl

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FullWalkNormal
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

/-- Simultaneous normal form for mixed macro walks and literal frozen cells.
Frozen dipoles may be exposed by top surgery or radial switches. The induction
therefore retests all these conditions, and preserves the full elementary
chain, rather than separately asserting that the operations commute. -/
theorem normalize_full (B : FrozenTarget T) (hm : P.FrozenMapped B)
    (apex : V → Bool)
    (hr : ∀ s, apex (T.start (T.label s)) = true →
      apex (T.start (T.rev (T.label s))) = false) :
    ∃ Q : WalkPicture.{u} T, Nonempty (P.Survives Q) ∧ Q.FrozenMapped B ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective apex ∧
      Q.chain = P.chain := by
  classical
  have produce : ∀ n, ∀ P : WalkPicture.{u} T, Fintype.card P.Dart = n →
      P.FrozenMapped B →
      ∃ Q : WalkPicture.{u} T, Nonempty (P.Survives Q) ∧ Q.FrozenMapped B ∧
        Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective apex ∧
        Q.chain = P.chain := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn hm
      obtain ⟨P',⟨hret⟩,hs,hnb,hred,hrad,hc⟩ := P.normalize_radial apex hr
      let hsur := hret.survives
      have hm' := hsur.frozenMapped P B hm
      by_cases hf : P'.FullyReduced
      · exact ⟨P',⟨hsur⟩,hm',hs,hnb,hf,hrad,hc⟩
      · obtain ⟨a,ha⟩ := not_forall.mp hf
        have hop : P'.index (P'.pairing.edge a) = T.opposite (P'.index a) := not_not.mp ha
        have hfree : T.free (T.kind (P'.index a)) = false := by
          cases hb : T.free (T.kind (P'.index a)) with
          | false => rfl
          | true => exact False.elim (hred a hb hop)
        obtain ⟨P₀,⟨hcan⟩,hm₀,hsmall,hchain⟩ := P'.cancel_frozen B hm' a hfree hop
        have hsmall' : Fintype.card P₀.Dart < n := by
          apply lt_of_lt_of_le hsmall
          rw [← hn]
          exact Fintype.card_le_of_injective _ hret.injective
        obtain ⟨Q,⟨hq⟩,hqm,hqs,hqb,hqr,hqd,hqc⟩ := ih _ hsmall' P₀ rfl hm₀
        exact ⟨Q,⟨Survives.trans P hsur (Survives.trans P' hcan hq)⟩,
          hqm,hqs,hqb,hqr,hqd,hqc.trans (hchain.trans hc)⟩
  exact produce (Fintype.card P.Dart) P rfl hm
end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeMappedWalk
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

/-- The actual simple macro polygon carried by one free source face. Its
vertices are the original TEMPLATE vertices in their original cyclic order,
not the possibly identified letter-bouquet vertices. This supplies the finite
macro-cycle perimeter/three-fan bounds from the produced normal picture. -/
noncomputable def mappedMacroPolygon (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart) (hx : P.index x = .inl (a,e)) :
    MacroGraph.Polygon := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let j : I → MacroGraph.graph.Dart := fun y =>
    (same_top_face n w d c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (a,j y) :=
    (same_top_face n w d c hc f P hx y.property).choose_spec
  let q : Perm I := P.pairing.face.subtypePerm (fun _ => sameCycle_apply_right)
  let b : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hfree (y : I) : (walkTarget n w d c hc f).free
      ((walkTarget n w d c hc f).kind (P.index y.val)) = true := by
    rw [hj]; rfl
  have hclose (y : I) : (j (q y)).fst = (j y).snd := by
    have h := P.closed y.val
    change walkFront n w d (P.index (q y).val) = walkBack n w d (P.index y.val) at h
    rw [hj,hj] at h
    exact congrArg Prod.snd (Sum.inl.inj h)
  exact {
    n := Fintype.card I
    vertex := fun i => (j (b i)).fst
    next := b.trans (q.trans b.symm)
    injective := by
      intro i k hik
      apply b.injective
      apply Subtype.ext
      apply P.simple_front hs (hfree (b i)) ((b i).property.symm.trans (b k).property)
      change walkFront n w d (P.index (b i).val) = walkFront n w d (P.index (b k).val)
      rw [hj,hj]
      exact congrArg Sum.inl (Prod.ext rfl hik)
    adjacent := by
      intro i
      change MacroGraph.Adjacent (j (b i)).fst (j (b (b.symm (q (b i))))).fst
      rw [b.apply_symm_apply,hclose]
      exact (j (b i)).adj
    no_backtrack := by
      intro i hi
      have hv := congrArg (fun k => (b k).val) hi
      simp only [Equiv.trans_apply,Equiv.apply_symm_apply] at hv
      exact hb (b i).val (hfree (b i)) hv }

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkFacePosition
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

/-- Every individual source face uses each indexed letter position at most
once. For a top this uses simplicity AND absence of two-step polygons. -/
lemma raw_position_once_per_face (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x y : P.Dart} (hxy : P.pairing.face.SameCycle x y)
    (hx : isLetter n w (walkLabel n w d (P.index x)) = true)
    (hy : isLetter n w (walkLabel n w d (P.index y)) = true)
    (hp : rawPosition n w d (P.index x) = rawPosition n w d (P.index y)) : x = y := by
  have hcx := raw_step_cases n w d (P.index x) hx
  have hcy := raw_step_cases n w d (P.index y) hy
  rw [← hp] at hcy
  rcases hcx with hcx | hcx <;> rcases hcy with hcy | hcy
  · exact P.normalized_index_inj hs _ hm hxy (hcx.trans hcy.symm)
  · exact False.elim (P.normalized_sameface_not_opposite hs hb _ hm hxy (by
      change P.index y = walkOpposite n w d (P.index x)
      rw [hcx,hcy]))
  · exact False.elim (P.normalized_sameface_not_opposite hs hb _ hm hxy.symm (by
      change P.index x = walkOpposite n w d (P.index y)
      rw [hcx,hcy]))
  · exact P.normalized_index_inj hs _ hm hxy (hcx.trans hcy.symm)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FragmentSlots
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

def faceOccurrence (F : SelectedTopFace n w d c hc f P select) : Top n w := F.property.2.choose
lemma faceOccurrence_kind (F : SelectedTopFace n w d c hc f P select) :
    P.faceKind F.val = .inl (faceOccurrence n w d c hc f P select F) := F.property.2.choose_spec

def topSlot (F : SelectedTopFace n w d c hc f P select) (i : Fin 7) :
    Σ b : Fan n w, SelectedTop n w d c hc f P select b :=
  ⟨slot n w (faceOccurrence n w d c hc f P select F) i,
    F.val,F.property.1,faceOccurrence n w d c hc f P select F,
    faceOccurrence_kind n w d c hc f P select F,i,rfl⟩

lemma topSlot_injective : Function.Injective
    (fun p : SelectedTopFace n w d c hc f P select × Fin 7 => topSlot n w d c hc f P select p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : Σ b : Fan n w, SelectedTop n w d c hc f P select b => z.2.val) h
  · exact congrArg (fun z : Σ b : Fan n w, SelectedTop n w d c hc f P select b => z.1.val.1) h

lemma topSlot_surjective : Function.Surjective
    (fun p : SelectedTopFace n w d c hc f P select × Fin 7 => topSlot n w d c hc f P select p.1 p.2) := by
  rintro ⟨b,F⟩
  obtain ⟨a,ha,i,hi⟩ := F.property.2
  let H : SelectedTopFace n w d c hc f P select := ⟨F.val,F.property.1,a,ha⟩
  have hocc : faceOccurrence n w d c hc f P select H = a :=
    Sum.inl.inj ((faceOccurrence_kind n w d c hc f P select H).symm.trans ha)
  have hslot : slot n w (faceOccurrence n w d c hc f P select H) i = b := by rw [hocc,hi]
  refine ⟨(H,i),?_⟩
  apply Sigma.ext hslot
  apply (Subtype.heq_iff_coe_eq (fun z => by change (select z = true ∧ ∃ a, P.faceKind z = .inl a ∧ ∃ j, slot n w a j = slot n w (faceOccurrence n w d c hc f P select H) i) ↔ _; rw [hslot])).mpr
  rfl

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRadialBoundary
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

lemma walk_apex_paired (x : P.Dart) (hx : walkApex n w d c hc f P x = true) :
    walkApex n w d c hc f P (P.pairing.edge x) = false := by
  change isApex n w (start n w (walkLabel n w d (P.index (P.pairing.edge x)))) = false
  have he : walkLabel n w d (P.index (P.pairing.edge x)) = rev n w (walkLabel n w d (P.index x)) := P.paired x
  rw [he]
  exact radial n w _ hx
lemma walk_apex_radial (x : P.Dart) (hx : walkApex n w d c hc f P x = true) :
    walkRadial n w d c hc f P x := by
  change isApex n w (start n w (walkLabel n w d (P.index x))) = true at hx
  change isLetter n w (walkLabel n w d (P.index x)) = false
  generalize hh : walkLabel n w d (P.index x) = l at *
  rcases l with ⟨e,o⟩
  cases e with
  | inl a => cases hx
  | inr e => rfl
lemma walk_radial_paired (x : P.Dart) :
    walkRadial n w d c hc f P (P.pairing.edge x) ↔ walkRadial n w d c hc f P x := by
  unfold walkRadial
  have he : walkLabel n w d (P.index (P.pairing.edge x)) = rev n w (walkLabel n w d (P.index x)) := P.paired x
  rw [he]
  rfl

lemma fragment_active (b : Fan n w) (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    (fragmentMark n w d c hc f P select b z x).plain.active = select (P.faceClass x.val) := by
  unfold fragmentMark
  split_ifs with hs ht <;> simp_all [FanLink.Mark.plain,FanLink.State.active]

variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

def boundaryTransition (p : AllBoundaryIndex n w d c hc f P select hs hm hred hrad) :
    P.pairing.VertexTransition (walkApex n w d c hc f P) (walkSelected n w d c hc f P select) := by
  refine ⟨p.2.val.2.val,instance_apex n w d c hc f P select p.1 p.2.val.1 p.2.val.2,?_⟩
  have hh := p.2.property
  change (fragmentMark n w d c hc f P select p.1 p.2.val.1 p.2.val.2).plain.active ≠
    (fragmentMark n w d c hc f P select p.1 p.2.val.1 (P.linkNext p.2.val.1.val p.2.val.2)).plain.active at hh
  rw [fragment_active,fragment_active] at hh
  exact hh

lemma boundaryTransition_injective : Function.Injective
    (boundaryTransition n w d c hc f P select hs hm hred hrad) := by
  intro p q h
  have hh : (⟨p.1,p.2.val⟩ : Σ b : Fan n w, Σ z : ApexInstance n w d c hc f P select b, P.Link z.val) =
      ⟨q.1,q.2.val⟩ := apexCorner_injective n w d c hc f P select (congrArg Subtype.val h)
  rcases p with ⟨b,x⟩; rcases q with ⟨a,y⟩
  have hb : b = a := congrArg Sigma.fst hh
  subst a
  have hv : x.val = y.val := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hv))

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTopTurns
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

variable (select : P.Face → Bool)
noncomputable instance instFintypeFaceApexDart (F : SelectedTopFace n w d c hc f P select) :
    Fintype (FaceApexDart n w d c hc f P select F) := Fintype.ofFinite _

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTurnTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)


variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

def allTurnDart (p : AllTurnIndex n w d c hc f P select hs hm hred hrad) :
    TopTurnDart n w d c hc f P select := by
  refine ⟨p.2.val.2.val,?_,instance_apex n w d c hc f P select p.1 p.2.val.1 p.2.val.2,?_⟩
  · by_contra hh
    have he := (mark_absent n w d c hc f P select p.1 p.2.val.1 p.2.val.2).mpr hh
    obtain ⟨F,hF⟩ := p.2.property
    change fragmentMark n w d c hc f P select p.1 p.2.val.1 p.2.val.2 = .top F at hF
    rw [he] at hF
    cases hF
  · obtain ⟨F,hF⟩ := p.2.property
    obtain ⟨e,he⟩ := mark_top_index n w d c hc f P select p.1 p.2.val.1 p.2.val.2 F hF
    rw [he]; rfl

lemma allTurnDart_surjective : Function.Surjective
    (allTurnDart n w d c hc f P select hs hm hred hrad) := by
  intro x
  obtain ⟨b,hb⟩ : ∃ b, start n w (walkLabel n w d (P.index x.val)) = .inr b := by
    cases he : start n w (walkLabel n w d (P.index x.val)) with
    | inl a => have hh := x.property.2.1; rw [he] at hh; cases hh
    | inr b => exact ⟨b,rfl⟩
  let z := apexInstanceAt n w d c hc f P select b x.val x.property.1 hb
  let y : P.Link z.val := ⟨x.val,rfl⟩
  have ht : ∃ a e, P.index x.val = .inl (a,e) := by
    cases he : P.index x.val with
    | inl s => exact ⟨s.1,s.2,rfl⟩
    | inr s => have hh := x.property.2.2; rw [he] at hh; cases hh
  have hmark : ∃ F, fragmentMark n w d c hc f P select b z y = .top F := by
    unfold fragmentMark
    exact ⟨_,by rw [dite_eq_left x.property.1,dite_eq_left ht]⟩
  exact ⟨⟨b,⟨⟨z,y⟩,hmark⟩⟩,Subtype.ext rfl⟩

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PicturePartition
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.instFinite _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {X I F : Type*} [Fintype X] [Fintype I] [Fintype F]

omit [Fintype I] in
lemma cut_sides_twice (P : PictureMap X) (part : X → I) :
    Fintype.card (CutSide P part) = 2 * Fintype.card (CutContact P part) := by
  let raw := fun x => part x ≠ part (P.edge x)
  have hr : ∀ x, raw (P.edge x) ↔ raw x := by intro x; dsimp only [raw]; rw [P.edge_edge]; exact ne_comm
  have hh := P.boundary_contacts_eq (fun _ => True) raw hr
  have : IsEmpty (P.BoundarySide (fun _ => True) raw) := ⟨fun x => x.property.2.2 trivial⟩
  simp only [Fintype.card_of_isEmpty,Nat.zero_add] at hh
  have h1 : Fintype.card (PictureMap.SelectedSide (fun _ => True) raw) = Fintype.card (CutSide P part) := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun _ => by simp only [and_true,raw])
  have h2 : Fintype.card (P.Contact (fun _ => True) raw) = Fintype.card (CutContact P part) := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun _ => by dsimp only [raw]; simp only [true_and])
  simp only [← Nat.card_eq_fintype_card] at h1 h2 hh ⊢
  rw [h1,h2] at hh
  omega

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualDegree
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma same_frozen_face {x y : P.Dart} {k : FrozenCell n w d} {o : Bool}
    {i : Fin ((frozenBoundary n w d).size k)} (hx : P.index x = .inr ⟨k,o,i⟩)
    (hxy : P.pairing.face.SameCycle x y) :
    ∃ o' i', P.index y = .inr ⟨k,o',i'⟩ := by
  have hk := walkKind_cycle n w d c hc f P hxy
  rw [hx] at hk
  cases hy : P.index y with
  | inl s => rw [hy] at hk; cases hk
  | inr s =>
    rcases s with ⟨k',o',i'⟩
    rw [hy] at hk
    have he : k = k' := Sum.inr.inj hk
    subst k'
    exact ⟨o',i',rfl⟩

lemma frozen_face_degree_le (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (x : P.Dart) (k : FrozenCell n w d) (o : Bool) (i : Fin ((frozenBoundary n w d).size k))
    (hx : P.index x = .inr ⟨k,o,i⟩) :
    Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y} ≤ 12 := by
  let F := {y : P.Dart // P.pairing.face.SameCycle x y}
  have hF (y : F) : ∃ p : Bool × Fin ((frozenBoundary n w d).size k), P.index y.val = .inr ⟨k,p.1,p.2⟩ := by
    obtain ⟨o',i',he⟩ := same_frozen_face n w d c hc f P hx y.property
    exact ⟨⟨o',i'⟩,he⟩
  let g : F → Bool × Fin ((frozenBoundary n w d).size k) := fun y => (hF y).choose
  have hg (y : F) : P.index y.val = .inr ⟨k,(g y).1,(g y).2⟩ := (hF y).choose_spec
  have hinj : Function.Injective g := by
    intro y z he
    apply Subtype.ext
    apply P.normalized_index_inj hs _ hm (y.property.symm.trans z.property)
    rw [hg,hg,he]
  have hcard := Fintype.card_le_of_injective g hinj
  rw [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at hcard
  have hk : (frozenBoundary n w d).size k ≤ 6 := by rcases k with k | (k | k) <;> norm_num [frozenBoundary,frozenCell,size]
  exact hcard.trans (by omega)

/-- The uniform degree bound for the literal dual multigraph.
Degree counts side copies, so parallel edges and loops are not discarded. -/
theorem actual_face_degree_le (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f)) (F : P.Face) :
    Fintype.card {y : P.Dart // P.faceClass y = F} ≤ 15 := by
  have he : Fintype.card {y : P.Dart // P.faceClass y = F} =
      Fintype.card {y : P.Dart // P.pairing.face.SameCycle F.out y} := by
    apply Fintype.card_congr (Equiv.subtypeEquivRight _)
    intro y
    rw [← P.faceClass_eq,P.faceClass_out,eq_comm]
  rw [he]
  cases hx : P.index F.out with
  | inl s =>
    let B := mappedMacroPolygon n w d c hc f P hs hb F.out s.1 s.2 hx
    exact B.perimeter_le
  | inr s =>
    rcases s with ⟨k,o,i⟩
    exact (frozen_face_degree_le n w d c hc f P hs hm F.out k o i hx).trans (by decide)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryIndex
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D S L : Type*} [DecidableEq D]

variable [DecidableEq S]

lemma boundaryIndex_commute {f : Perm D} {t : Perm S} {xs : List D} {ys : List S}
    (hf : IsBoundary f xs) (ht : IsBoundary t ys) (hlen : xs.length = ys.length)
    (x : D) (hx : x ∈ xs) :
    boundaryIndex xs ys hlen (f x) (hf.invariant hx) = t (boundaryIndex xs ys hlen x hx) := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
  have hn : 0 < xs.length := (Nat.zero_le i).trans_lt hi
  have hn' : 0 < ys.length := by omega
  rw [boundaryIndex_get xs ys hf.nodup hlen i hi,ht.turn _ (List.getElem_mem (by omega)),
    List.formPerm_apply_getElem ys ht.nodup i (by omega)]
  have he : f xs[i] = xs[(i+1)%xs.length]'(Nat.mod_lt _ hn) :=
    (hf.turn _ (List.getElem_mem hi)).trans (List.formPerm_apply_getElem xs hf.nodup i hi)
  simp only [he,boundaryIndex_get xs ys hf.nodup hlen,hlen]

/-- Build a coherent index map by selecting one boundary match PER FACE,
not independently per side. This is the coherence step between
word van Kampen diagrams and actual cellular pictures. -/
theorem indexedFaceMap_exists (f : Perm D) (t : Perm S) (label : D → L) (edge : S → L)
    (h : ∀ x : D, ∃ xs : List D, ∃ ys : List S,
      IsBoundary f xs ∧ x ∈ xs ∧ IsBoundary t ys ∧ xs.map label = ys.map edge) :
    ∃ j : D → S, IndexedFaceMap f t j ∧ ∀ x, edge (j x) = label x := by
  let F := Quotient (SameCycle.setoid f)
  let cls : D → F := Quotient.mk _
  let xs : F → List D := fun c => (h c.out).choose
  let ys : F → List S := fun c => (h c.out).choose_spec.choose
  have hd : ∀ c : F, IsBoundary f (xs c) ∧ c.out ∈ xs c ∧
      IsBoundary t (ys c) ∧ (xs c).map label = (ys c).map edge :=
    fun c => (h c.out).choose_spec.choose_spec
  have hlen : ∀ c, (xs c).length = (ys c).length := fun c => by
    have hh := congrArg List.length (hd c).2.2.2
    simpa only [List.length_map] using hh
  have hm : ∀ x, x ∈ xs (cls x) := by
    intro x
    exact (hd (cls x)).1.mem_of_sameCycle (hd (cls x)).2.1
      (Quotient.exact (Quotient.out_eq' (cls x)))
  have hc : ∀ x, cls (f x) = cls x := fun x =>
    Quotient.sound (SameCycle.rfl.apply_right.symm)
  let j : D → S := fun x => boundaryIndex (xs (cls x)) (ys (cls x)) (hlen _) x (hm x)
  refine ⟨j,⟨?_,?_⟩,?_⟩
  · intro x
    dsimp only [j]
    simp only [hc x]
    exact boundaryIndex_commute (hd (cls x)).1 (hd (cls x)).2.2.1 (hlen _) x (hm x)
  · intro x y hxy he
    have hec : cls x = cls y := Quotient.sound hxy
    dsimp only [j] at he
    simp only [← hec] at he
    exact boundaryIndex_inj _ _ (hd (cls x)).2.2.1.nodup (hlen _) (hm x) (hec ▸ hm y) he
  · intro x
    exact boundaryIndex_label _ _ (hlen _) label edge (hd (cls x)).2.2.2 x (hm x)

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeCellWalk
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma cellWalkStep_closed (s : (boundary n w d).Side) :
    walkFront n w d (cellWalkStep n w d ((boundary n w d).next s)) =
      walkBack n w d (cellWalkStep n w d s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | (a | a)
  · exact congrArg Sum.inr ((frozenBoundary n w d).next_start ⟨.inl a,b,i⟩)
  · cases b with
    | false =>
      change Sum.inl (a.1,a.2.2.val.getVert
        ((finRotate a.2.2.val.length) ((finRotate a.2.2.val.length)⁻¹ i)).val) =
          Sum.inl (a.1,a.2.2.val.getVert i.val)
      change Fin a.2.2.val.length at i
      rw [Perm.inv_def,Equiv.apply_symm_apply]
    | true => rfl
  · exact congrArg Sum.inr ((frozenBoundary n w d).next_start ⟨.inr a,b,i⟩)

universe u

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeDecorationGroup
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

include hc in
lemma stepLetter_value {a b : MasterGraph.Vertex} (s : MasterGraph.Step a b)
    (l : Field → Alphabet n) :
    c (letterDart n w (stepLetter n l s)) = s.value l (c ∘ letterDart n w) := by
  have hr : ∀ a, c (letterDart n w (inverseLetter n a)) = (c (letterDart n w a))⁻¹ :=
    fun a => hc (letterDart n w a)
  cases h : s.forward <;> simp only [stepLetter,MasterGraph.Step.value,h,
    Bool.false_eq_true,ite_false,ite_true,hr,Function.comp_apply]

include hc hcell in
lemma square_relator_value (l : Field → Alphabet n) (τ : TwoPath)
    (present : w (TableModel.row rowSupport l (.inr (.inr τ))) = true) :
    MasterGraph.squareWord l (c ∘ letterDart n w) τ = 1 := by
  let s : Square n w := ⟨τ,⟨fun f => l f.val,present⟩⟩
  let l' := extendRow n (.inr (.inr τ)) s.2.val
  have hf := hcell (.inr (.inr (.inl s)))
  change c (letterDart n w (stepLetter n l' (MasterGraph.first τ))) *
    (c (letterDart n w (stepLetter n l' (MasterGraph.second τ))) *
      (c (letterDart n w (l' (.inr (τ,0)))) *
        (c (letterDart n w (l' (.inr (τ,1)))) * 1))) = 1 at hf
  rw [stepLetter_value n w c hc,stepLetter_value n w c hc,mul_one] at hf
  have hl : ∀ f ∈ squareSupport τ, l' f = l f := by
    intro f hf
    simp only [l',extendRow,show f ∈ rowSupport (.inr (.inr τ)) from hf,dite_eq_left,s]
  have h1 := hl (MasterGraph.first τ).field (by simp [MasterGraph.first_field,squareSupport])
  have h2 := hl (MasterGraph.second τ).field (by simp [MasterGraph.second_field,squareSupport])
  have h3 := hl (.inr (τ,0)) (by simp [squareSupport])
  have h4 := hl (.inr (τ,1)) (by simp [squareSupport])
  simp only [MasterGraph.Step.value,Function.comp_apply,h1,h2,h3,h4] at hf
  simpa only [MasterGraph.squareWord,MasterGraph.Step.value,Function.comp_apply,mul_assoc] using hf

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonBoundaryList
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C L V : Type*} (B : PolygonTarget.Boundary C L V)

variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → L)
  (closed : ∀ i, B.start (word (finRotate ell i)) = B.start (B.rev (word i)))

/-- `none` marks every genuine target cell, while the two exterior
orientations remain separately identifiable. -/
def outsideTag : (B.withOutside ell hell word closed).Side → Option Bool :=
  fun s => match s.1 with | .inl _ => none | .inr _ => some s.2.1

lemma positive_inside_tag (c : C) (s : (B.withOutside ell hell word closed).Side)
    (hs : s ∈ (B.withOutside ell hell word closed).positiveSides (.inl c)) :
    B.outsideTag ell hell word closed s = none ∧
    B.outsideTag ell hell word closed ((B.withOutside ell hell word closed).opposite s) = none := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
  exact ⟨rfl,rfl⟩

lemma positive_outside_tag (s : (B.withOutside ell hell word closed).Side)
    (hs : s ∈ (B.withOutside ell hell word closed).positiveSides (.inr ())) :
    B.outsideTag ell hell word closed s = some true := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
  rfl

end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureSum
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D E : Type*} [DecidableEq D] [DecidableEq E] [Fintype D] [Fintype E]

lemma cycles_sum (p : Perm D) (q : Perm E) :
    cycles (Equiv.sumCongr p q) = cycles p + cycles q := by
  let j : D ⊕ E → Quotient (SameCycle.setoid p) ⊕ Quotient (SameCycle.setoid q) :=
    Sum.map (Quotient.mk _) (Quotient.mk _)
  have hc : ∀ x y, SameCycle (Equiv.sumCongr p q) x y ↔ j x = j y := by
    intro x y
    constructor
    · intro h
      apply sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Quotient (SameCycle.setoid p) ⊕ Quotient (SameCycle.setoid q)))) (j := j) ?_ h)
      intro z; cases z with
      | inl z =>
        exact congrArg Sum.inl (Quotient.sound (SameCycle.rfl (f := p) (x := z)).apply_left)
      | inr z =>
        exact congrArg Sum.inr (Quotient.sound (SameCycle.rfl (f := q) (x := z)).apply_left)
    · cases x with
      | inl x => cases y with
        | inl y =>
          intro h
          exact semiconj_perm_sameCycle (f := p) (t := Equiv.sumCongr p q)
            (j := Sum.inl) (fun _ => rfl) (Quotient.exact (Sum.inl.inj h))
        | inr y =>
          intro h
          exact False.elim (Sum.inl_ne_inr (by exact h))
      | inr x => cases y with
        | inl y =>
          intro h
          exact False.elim (Sum.inr_ne_inl (by exact h))
        | inr y =>
          intro h
          exact semiconj_perm_sameCycle (f := q) (t := Equiv.sumCongr p q)
            (j := Sum.inr) (fun _ => rfl) (Quotient.exact (Sum.inr.inj h))
  have hj : Function.Surjective j := by
    intro z; cases z with
    | inl z => obtain ⟨x,rfl⟩ := Quotient.exists_rep z; exact ⟨Sum.inl x,rfl⟩
    | inr z => obtain ⟨x,rfl⟩ := Quotient.exists_rep z; exact ⟨Sum.inr x,rfl⟩
  rw [cycles_eq_card_classes,card_quotient_of_classifier _ j hc hj,Nat.card_sum,
    Nat.cast_add,← cycles_eq_card_classes,← cycles_eq_card_classes]

namespace PictureMap
variable (M : PictureMap D) (N : PictureMap E)

omit [DecidableEq D] [DecidableEq E] in
lemma sum_components : ∀ x y, (M.sum N).components x y ↔ M.sumClassifier N x = M.sumClassifier N y := by
  have hleft : M.components ≤ ((M.sum N).components.comap Sum.inl) := by
    apply M.components_le
    · intro x
      exact (M.sum N).face_le_components (SameCycle.rfl (x := Sum.inl x)).apply_right
    · intro x
      exact (M.sum N).edge_le_components (SameCycle.rfl (x := Sum.inl x)).apply_right
  have hright : N.components ≤ ((M.sum N).components.comap Sum.inr) := by
    apply N.components_le
    · intro x
      exact (M.sum N).face_le_components (SameCycle.rfl (x := Sum.inr x)).apply_right
    · intro x
      exact (M.sum N).edge_le_components (SameCycle.rfl (x := Sum.inr x)).apply_right
  have hk : (M.sum N).components ≤ Setoid.ker (M.sumClassifier N) := by
    apply (M.sum N).components_le
    · intro x; cases x with
      | inl x => exact congrArg Sum.inl (Quotient.sound (M.face_le_components SameCycle.rfl.apply_right))
      | inr x => exact congrArg Sum.inr (Quotient.sound (N.face_le_components SameCycle.rfl.apply_right))
    · intro x; cases x with
      | inl x => exact congrArg Sum.inl (Quotient.sound (M.edge_le_components SameCycle.rfl.apply_right))
      | inr x => exact congrArg Sum.inr (Quotient.sound (N.edge_le_components SameCycle.rfl.apply_right))
  intro x y
  refine ⟨fun h => hk h,?_⟩
  cases x with
  | inl x => cases y with
    | inl y => intro h; exact hleft (Quotient.exact (Sum.inl.inj h))
    | inr y => intro h; exact False.elim (Sum.inl_ne_inr (by exact h))
  | inr x => cases y with
    | inl y => intro h; exact False.elim (Sum.inr_ne_inl (by exact h))
    | inr y => intro h; exact hright (Quotient.exact (Sum.inr.inj h))

omit [DecidableEq D] [DecidableEq E] in
lemma sum_components_card : Nat.card (Quotient (M.sum N).components) =
    Nat.card (Quotient M.components) + Nat.card (Quotient N.components) := by
  rw [card_quotient_of_classifier _ (M.sumClassifier N) (M.sum_components N) ?_,Nat.card_sum]
  intro z; cases z with
  | inl z => obtain ⟨x,rfl⟩ := Quotient.exists_rep z; exact ⟨Sum.inl x,rfl⟩
  | inr z => obtain ⟨x,rfl⟩ := Quotient.exists_rep z; exact ⟨Sum.inr x,rfl⟩

omit [DecidableEq D] [DecidableEq E] in
lemma sum_not_components (x : D) (y : E) : ¬ (M.sum N).components (Sum.inl x) (Sum.inr y) := by
  rw [M.sum_components N]
  exact Sum.inl_ne_inr

lemma sum_euler : (M.sum N).euler = M.euler + N.euler := by
  obtain ⟨n,hn⟩ := M.card_darts_even
  obtain ⟨m,hm⟩ := N.card_darts_even
  rw [euler,euler,euler,sum_vertex,cycles_sum]
  change cycles M.vertex + cycles N.vertex + cycles (Equiv.sumCongr M.face N.face) - _ = _
  rw [cycles_sum,Fintype.card_sum,Nat.cast_add]
  omega

theorem sum_genusZero (hM : M.GenusZero) (hN : N.GenusZero) : (M.sum N).GenusZero := by
  change (M.sum N).euler = _
  rw [M.sum_euler N,M.sum_components_card N]
  change M.euler = _ at hM
  change N.euler = _ at hN
  rw [hM,hN,Nat.cast_add,mul_add]

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureAppend
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace IsBoundary
variable {D : Type*} [DecidableEq D] {f : Perm D} {xs ys : List D}
lemma splice_nonempty (hx : IsBoundary f xs) (hy : IsBoundary f ys)
    (hxn : xs ≠ []) (hyn : ys ≠ []) (hd : ∀ x ∈ xs, x ∉ ys) :
    IsBoundary (f * swap (xs.getLast hxn) (ys.getLast hyn)) (xs++ys) := by
  obtain ⟨b,r,rfl⟩ := List.exists_cons_of_ne_nil hyn
  have h := splice_append (l := xs.dropLast) (a := xs.getLast hxn)
    (by simpa only [List.dropLast_append_getLast] using hx) hy
    (by simpa only [List.dropLast_append_getLast] using hd)
  simpa only [List.dropLast_append_getLast] using h
end IsBoundary
end HyperbolicObstruction.PictureSwitch

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureFold
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w : Word A}
namespace WordPicture
variable (P : WordPicture R w)

include P

lemma of_step {v : Word A} (h : FreeGroup.Red.Step w v) : Nonempty (WordPicture R v) := by
  cases h with
  | @not l r x b =>
    obtain ⟨ls,rs,he,hl,hrs⟩ := List.map_eq_append_iff.mp P.word
    obtain ⟨a,rs',hr,ha,hrs'⟩ := List.map_eq_cons_iff.mp hrs
    obtain ⟨b',rs'',hr',hb,hrs''⟩ := List.map_eq_cons_iff.mp hrs'
    have hout : P.outside = ls++a::b'::rs'' := by rw [he,hr,hr']
    have hc : P.label a = invLetter (P.label b') := by rw [ha,hb]; simp [invLetter]
    have H := P.foldAt hout hc
    have hw : (ls++rs'').map P.label = l++r := by rw [List.map_append,hl,hrs'']
    exact ⟨hw ▸ H⟩

lemma of_red {v : Word A} (h : FreeGroup.Red w v) : Nonempty (WordPicture R v) := by
  induction h with
  | refl => exact ⟨P⟩
  | tail h h' ih => obtain ⟨Q⟩ := ih; exact Q.of_step h'

end WordPicture

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureCell
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {S L V B : Type*} [DecidableEq S] [AddCommMonoid B]
namespace CellTarget
variable (T : CellTarget S L V B)

lemma reverse_boundary {xs : List S} (h : IsBoundary T.next xs) :
    IsBoundary T.next (xs.reverse.map T.opposite) := by
  have hrev : IsBoundary T.next⁻¹ xs.reverse := by
    refine ⟨by simpa using h.nodup,?_⟩
    intro x hx
    rw [List.formPerm_reverse]
    have hx' : x ∈ xs := List.mem_reverse.mp hx
    have hy : xs.formPerm⁻¹ x ∈ xs := by
      apply List.mem_of_formPerm_apply_mem
      simpa only [Perm.inv_def,Equiv.apply_symm_apply] using hx'
    apply T.next.injective
    rw [Perm.inv_def,Equiv.apply_symm_apply,h.turn _ hy,Perm.inv_def,Equiv.apply_symm_apply]
  exact hrev.map T.opposite T.opposite.injective T.opposite_inv_next

end CellTarget
end HyperbolicObstruction.PictureSwitch

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureMarked
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A S V B K : Type*} [DecidableEq S] [AddCommMonoid B]
variable (T : CellTarget S (A × Bool) V B) (hinv : T.rev = invLetter)
variable {R : Set (Word A)} {w : Word A}
include hinv
namespace WordPicture
variable (P : WordPicture R w)

/-- Coherent indexing retains a distinguished face tag. In particular the
outside can only map to the positive exterior polygon; no opposite exterior
face or extra exterior face is silently introduced. -/
theorem cellular_index_tag (tag : S → K) (inside outside : K)
    (hR : ∀ r ∈ R, ∃ ys : List S, IsBoundary T.next ys ∧ ys.map T.edge = r ∧
      (∀ y ∈ ys, tag y = inside ∧ tag (T.opposite y) = inside))
    (hw : ∃ ys : List S, IsBoundary T.next ys ∧ ys.map T.edge = w ∧
      (∀ y ∈ ys, tag y = outside)) :
    ∃ j : P.Dart → S, IndexedFaceMap P.pairing.face T.next j ∧
      (∀ x, T.edge (j x) = P.label x) ∧
      ∀ x, tag (j x) = if x ∈ P.outside then outside else inside := by
  let lab : P.Dart → K × (A × Bool) :=
    fun x => (if x ∈ P.outside then outside else inside, P.label x)
  let edge : S → K × (A × Bool) := fun s => (tag s,T.edge s)
  have hex : ∀ x : P.Dart, ∃ xs : List P.Dart, ∃ ys : List S,
      IsBoundary P.pairing.face xs ∧ x ∈ xs ∧ IsBoundary T.next ys ∧
        xs.map lab = ys.map edge := by
    intro x
    by_cases hx : x ∈ P.outside
    · obtain ⟨ys,hy,hyw,hyt⟩ := hw
      refine ⟨P.outside,ys,P.boundary,hx,hy,?_⟩
      have he1 : P.outside.map lab = P.outside.map (fun x => (outside,P.label x)) := by
        apply List.map_congr_left
        intro z hz
        simp only [lab,ite_eq_left hz]
      have he2 : ys.map edge = ys.map (fun y => (outside,T.edge y)) := by
        apply List.map_congr_left
        intro z hz
        simp only [edge,hyt z hz]
      rw [he1,he2]
      change P.outside.map ((fun l => (outside,l)) ∘ P.label) =
        ys.map ((fun l => (outside,l)) ∘ T.edge)
      rw [← List.map_map,← List.map_map,P.word,hyw]
    · obtain ⟨xs,hxs,hxm,hr⟩ := P.interior x hx
      have hout : ∀ z ∈ xs, z ∉ P.outside := by
        intro z hz hzo
        exact hx (P.boundary.mem_of_sameCycle hzo (hxs.sameCycle hz hxm))
      have he1 : xs.map lab = xs.map (fun x => (inside,P.label x)) := by
        apply List.map_congr_left
        intro z hz
        simp only [lab,ite_eq_right (hout z hz)]
      have present : ∀ ys : List S, IsBoundary T.next ys →
          ys.map T.edge = xs.map P.label → (∀ y ∈ ys, tag y = inside) →
          ∃ xs' ys', IsBoundary P.pairing.face xs' ∧ x ∈ xs' ∧ IsBoundary T.next ys' ∧
            xs'.map lab = ys'.map edge := by
        intro ys hys he htag
        refine ⟨xs,ys,hxs,hxm,hys,?_⟩
        have he2 : ys.map edge = ys.map (fun y => (inside,T.edge y)) := by
          apply List.map_congr_left
          intro z hz
          simp only [edge,htag z hz]
        rw [he1,he2]
        change xs.map ((fun l => (inside,l)) ∘ P.label) =
          ys.map ((fun l => (inside,l)) ∘ T.edge)
        rw [← List.map_map,← List.map_map,he]
      rcases hr with hr | hr
      · obtain ⟨ys,hys,hy,ht⟩ := hR _ hr
        exact present ys hys hy (fun y hy => (ht y hy).1)
      · obtain ⟨ys,hys,hy,ht⟩ := hR _ hr
        apply present (ys.reverse.map T.opposite) (T.reverse_boundary hys)
        · rw [T.reverse_boundary_labels,hinv]
          have he : (ys.map (invLetter ∘ T.edge)).reverse = FreeGroup.invRev (ys.map T.edge) := by
            simp only [FreeGroup.invRev,List.map_map,invLetter,Function.comp_def]
          rw [he,hy,FreeGroup.invRev_invRev]
        · intro y hy
          obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
          exact (ht z (List.mem_reverse.mp hz)).2
  obtain ⟨j,hj,hl⟩ := indexedFaceMap_exists _ _ lab edge hex
  exact ⟨j,hj,(fun x => congrArg Prod.snd (hl x)),(fun x => congrArg Prod.fst (hl x))⟩

end WordPicture
end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonDiskProducer
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open HyperbolicObstruction.PictureSwitch HyperbolicObstruction.WordPictures Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C A V M : Type*} [AddCommGroup M]
variable (B : PolygonTarget.Boundary C (A × Bool) V)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → A × Bool)
  (closed : ∀ i, B.start (word (finRotate ell i)) = B.start (B.rev (word i)))
variable (weight : C → M) (apex : V → Bool)
  (radial : ∀ l, apex (B.start l) = true → apex (B.start (B.rev l)) = false)

abbrev outsideTarget := (B.withOutside ell hell word closed).target
  (Sum.elim weight (fun _ => 0)) apex radial

end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeExteriorWalk
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Dart n w)
  (closed : ∀ i, start n w (word (finRotate ell i)) = start n w (rev n w (word i)))
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

def exteriorCellStep : OutsideCellSide n w d ell hell word closed →
    (WalkStep n w d ⊕ (walkTarget n w d c hc f).ExteriorSide ell hell word closed)
  | ⟨.inl a,b,i⟩ => .inl (cellWalkStep n w d ⟨a,b,i⟩)
  | ⟨.inr a,b,i⟩ => .inr ⟨a,b,i⟩

lemma exteriorCellStep_label (s : OutsideCellSide n w d ell hell word closed) :
    (exteriorWalkTarget n w d ell hell word closed c hc f).label
      (exteriorCellStep n w d ell hell word closed c hc f s) =
      ((boundary n w d).withOutside ell hell word closed).sideLabel s := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | a
  · exact cellWalkStep_label n w d ⟨a,b,i⟩
  · rfl

lemma exteriorCellStep_kind (s : OutsideCellSide n w d ell hell word closed) :
    (exteriorWalkTarget n w d ell hell word closed c hc f).kind
      (exteriorCellStep n w d ell hell word closed c hc f
        (((boundary n w d).withOutside ell hell word closed).next s)) =
    (exteriorWalkTarget n w d ell hell word closed c hc f).kind
      (exteriorCellStep n w d ell hell word closed c hc f s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | a
  · exact congrArg Sum.inl (cellWalkStep_kind n w d ⟨a,b,i⟩)
  · rfl

lemma exteriorCellStep_closed (s : OutsideCellSide n w d ell hell word closed) :
    (exteriorWalkTarget n w d ell hell word closed c hc f).front
      (exteriorCellStep n w d ell hell word closed c hc f
        (((boundary n w d).withOutside ell hell word closed).next s)) =
    (exteriorWalkTarget n w d ell hell word closed c hc f).back
      (exteriorCellStep n w d ell hell word closed c hc f s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | a
  · exact congrArg Sum.inl (cellWalkStep_closed n w d ⟨a,b,i⟩)
  · exact congrArg Sum.inr
      (((walkTarget n w d c hc f).exteriorBoundary ell hell word closed).next_start ⟨a,b,i⟩)

lemma exteriorCellStep_frozen_next (s : OutsideCellSide n w d ell hell word closed)
    (h : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind
        (exteriorCellStep n w d ell hell word closed c hc f s)) = false) :
    exteriorCellStep n w d ell hell word closed c hc f
      (((boundary n w d).withOutside ell hell word closed).next s) =
    (exteriorWalkFrozen n w d ell hell word closed c hc f).next
      (exteriorCellStep n w d ell hell word closed c hc f s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | a
  · exact congrArg Sum.inl (cellWalkStep_frozen_next n w d ⟨a,b,i⟩ h)
  · rfl

lemma exteriorCellStep_frozen_inj {s t : OutsideCellSide n w d ell hell word closed}
    (h : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind
        (exteriorCellStep n w d ell hell word closed c hc f s)) = false)
    (he : exteriorCellStep n w d ell hell word closed c hc f s =
      exteriorCellStep n w d ell hell word closed c hc f t) : s = t := by
  rcases s with ⟨a,b,i⟩
  rcases t with ⟨a',b',i'⟩
  rcases a with a | a <;> rcases a' with a' | a'
  · have hh := cellWalkStep_frozen_inj n w d h (Sum.inl.inj he)
    have ha := (Sigma.mk.inj hh).1
    subst a'
    have hi := eq_of_heq (Sigma.mk.inj hh).2
    cases hi
    rfl
  · cases he
  · cases he
  · have hh := Sum.inr.inj he
    have ha := (Sigma.mk.inj hh).1
    subst a'
    have hi := eq_of_heq (Sigma.mk.inj hh).2
    cases hi
    rfl

variable (weight : Cell n w d → A)
abbrev exteriorCellTarget := (boundary n w d).outsideTarget ell hell word closed weight
  (isApex n w) (radial n w)
universe u
variable (P : CellPicture.{u} (exteriorCellTarget n w d ell hell word closed weight))

/-- Transfer keeps the raw diagram and arbitrary outside word literally,
while opening top polygon steps to the checked cone surgeries. -/
def exteriorCellToWalk : WalkPicture.{u} (exteriorWalkTarget n w d ell hell word closed c hc f) where
  Dart := P.Dart
  pairing := P.pairing
  index := exteriorCellStep n w d ell hell word closed c hc f ∘ P.index
  closed := by
    intro x
    change (exteriorWalkTarget n w d ell hell word closed c hc f).front
      (exteriorCellStep n w d ell hell word closed c hc f (P.index (P.pairing.face x))) = _
    rw [P.mapped.commute]
    exact exteriorCellStep_closed n w d ell hell word closed c hc f _
  kind := by
    intro x
    change (exteriorWalkTarget n w d ell hell word closed c hc f).kind
      (exteriorCellStep n w d ell hell word closed c hc f (P.index (P.pairing.face x))) = _
    rw [P.mapped.commute]
    exact exteriorCellStep_kind n w d ell hell word closed c hc f _
  paired := by
    intro x
    change (exteriorWalkTarget n w d ell hell word closed c hc f).label
      (exteriorCellStep n w d ell hell word closed c hc f (P.index (P.pairing.edge x))) =
      rev n w ((exteriorWalkTarget n w d ell hell word closed c hc f).label
        (exteriorCellStep n w d ell hell word closed c hc f (P.index x)))
    rw [exteriorCellStep_label,exteriorCellStep_label]
    exact P.respects.2 x
  genusZero := P.genusZero

lemma exteriorCellToWalk_frozen :
    (exteriorCellToWalk n w d ell hell word closed c hc f weight P).FrozenMapped
      (exteriorWalkFrozen n w d ell hell word closed c hc f) := by
  constructor
  · intro x
    exact (congrArg (exteriorCellStep n w d ell hell word closed c hc f)
      (P.mapped.commute x.val)).trans
      (exteriorCellStep_frozen_next n w d ell hell word closed c hc f _ x.property)
  · intro x y hxy he
    apply Subtype.ext
    apply P.mapped.injective
    · exact semiconj_perm_sameCycle
        (j := fun x : (exteriorCellToWalk n w d ell hell word closed c hc f weight P).FrozenDart => (x.val : P.Dart))
        (t := P.pairing.face) (fun _ => rfl) hxy
    · exact exteriorCellStep_frozen_inj n w d ell hell word closed c hc f x.property he

lemma exteriorCellToWalk_tag (xs : List P.Dart)
    (hp : ∀ x, (boundary n w d).outsideTag ell hell word closed (P.index x) =
      if x ∈ xs then some true else none) :
    ∀ x s, (exteriorCellToWalk n w d ell hell word closed c hc f weight P).index x = .inr s →
      s.2.1 = true := by
  intro x s he
  have hx := hp x
  cases hxi : P.index x with
  | mk a bi =>
    rcases bi with ⟨b,i⟩
    cases a with
    | inl a =>
      change exteriorCellStep n w d ell hell word closed c hc f (P.index x) = _ at he
      rw [hxi] at he
      cases he
    | inr a =>
      change exteriorCellStep n w d ell hell word closed c hc f (P.index x) = _ at he
      rw [hxi] at he
      have hs : (⟨a,b,i⟩ : (walkTarget n w d c hc f).ExteriorSide ell hell word closed) = s := Sum.inr.inj he
      rw [← hs]
      rw [hxi] at hx
      change some b = _ at hx
      split_ifs at hx with hm
      · exact Option.some.inj hx

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeFanGroup
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate
variable {H : Type*} [_root_.Group H]

lemma Path.eval_potential (U : Vertex → H) (l : Field → H)
    {a b : Vertex} (p : Path a b)
    (h : ∀ f ∈ p.fields, U (source f) * l f = U (target f)) :
    U a * p.eval l id = U b := by
  induction p with
  | nil => simp [Path.eval]
  | @cons a b c s p ih =>
    have hs := h s.field List.mem_cons_self
    have ht : U a * s.value l id = U b := by
      cases hh : s.forward
      · obtain ⟨ha,hb⟩ := s.endpoints_neg hh
        rw [ha,hb] at hs
        simpa only [Step.value,hh,Bool.false_eq_true,ite_false,id_eq] using
          (eq_mul_inv_iff_mul_eq.mpr hs).symm
      · obtain ⟨ha,hb⟩ := s.endpoints_pos hh
        rw [ha,hb] at hs
        simpa only [Step.value,hh,ite_true,id_eq] using hs
    rw [Path.eval,← mul_assoc,ht]
    exact ih (fun f hf => h f (List.mem_cons_of_mem _ hf))

lemma Path.eval_comp {n : ℕ} (l : Field → LetterPresentation.Alphabet n)
    (r : LetterPresentation.Alphabet n → H) {a b : Vertex} (p : Path a b) :
    p.eval (r ∘ l) id = p.eval l r := by
  induction p with
  | nil => rfl
  | cons s p ih => simp only [Path.eval,Step.value,Function.comp_apply,id_eq,ih]

end MasterGraph
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

include hc hcell in
lemma fan_relator_value (l : Field → Alphabet n) (i : Fin 7)
    (present : w (TableModel.row rowSupport l (.inl i)) = true)
    (v : MasterGraph.Vertex) (p : MasterGraph.Path v v)
    (fields : p.fields.toFinset ⊆ rowSupport (.inl i)) :
    p.eval l (c ∘ letterDart n w) = 1 := by
  let b : Fan n w := ⟨⟨i,fun f => l f.val⟩,present⟩
  have hp : fanPotential n w c b v * p.eval ((c ∘ letterDart n w) ∘ l) id =
      fanPotential n w c b v := by
    apply p.eval_potential
    intro f hf
    have hh : f ∈ (fan i).map Function.Embedding.inl := fields (List.mem_toFinset.mpr hf)
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hh
    exact fanPotential_edge n w d c hc hcell b e he
  rw [MasterGraph.Path.eval_comp] at hp
  exact mul_left_cancel (hp.trans (mul_one _).symm)

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeTopGroup
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

def topPotential (a : Top n w) : MasterGraph.Vertex → H
  | .inl (.inl r) => macroPotential n w c a (MacroGraph.point (pointOfRepresentative r)) *
      radialValue n w c (slot n w a (pointOfRepresentative r)) ⟨.inl r,rfl⟩
  | .inl (.inr l) => macroPotential n w c a (MacroGraph.line l)
  | .inr _ => 1

include hc hcell in
lemma topPotential_edge (a : Top n w) (e : IncidenceTemplate.Edge) :
    topPotential n w c a (MasterGraph.source (.inl e)) * c (letterDart n w (a.val e)) =
    topPotential n w c a (MasterGraph.target (.inl e)) := by
  by_cases he : isLoose e
  · have he' : e = loose := Subtype.ext he
    subst e
    have hp := macroPotential_edge n w d c hc hcell a
      (show MacroGraph.Adjacent (MacroGraph.point 3) MacroGraph.exceptional from rfl)
    have hl := macroPotential_edge n w d c hc hcell a
      (show MacroGraph.Adjacent MacroGraph.exceptional (MacroGraph.line 4) from rfl)
    change (macroPotential n w c a (MacroGraph.point 3) *
      c (.inr ⟨slot n w a 3,⟨.inl 3,by change IsFanVertex 3 (.inl 3); decide⟩⟩,true)) * c (letterDart n w (a.val loose)) = _
    change macroPotential n w c a (MacroGraph.point 3) *
      c (.inr ⟨slot n w a 3,⟨.inl 3,by change IsFanVertex 3 (.inl 3); decide⟩⟩,true) = _ at hp
    rw [hp]
    exact hl
  · let i := pointOfRepresentative e.val.1
    have hf : e ∈ fan i := by simp [fan,i,he]
    have htri := fanTriangle_relation n w d c hc hcell ⟨slot n w a i,⟨e,hf⟩⟩
    have hadj : MacroGraph.Adjacent (MacroGraph.point i) (MacroGraph.line e.val.2) :=
      (edge_fan_vertices e i hf).2
    have hrad := macroPotential_edge n w d c hc hcell a hadj
    change (macroPotential n w c a (MacroGraph.point i) *
      radialValue n w c (slot n w a i) ⟨.inl e.val.1,rfl⟩) *
      c (letterDart n w (a.val e)) = macroPotential n w c a (MacroGraph.line e.val.2)
    rw [mul_assoc]
    change radialValue n w c (slot n w a i) ⟨.inl e.val.1,rfl⟩ *
      c (letterDart n w (a.val e)) =
      radialValue n w c (slot n w a i) ⟨.inr e.val.2,hadj⟩ at htri
    rw [htri]
    exact hrad

include hc hcell in
lemma top_relator_value (l : Field → Alphabet n)
    (present : w (TableModel.row rowSupport l (.inr (.inl ()))) = true)
    (fans : ∀ i : Fin 7, w (TableModel.row rowSupport l (.inl i)) = true)
    (v : MasterGraph.Vertex) (p : MasterGraph.Path v v) (core : p.IsCore) :
    p.eval l (c ∘ letterDart n w) = 1 := by
  let a : Top n w := ⟨fun e => l (.inl e),by
    constructor
    · simpa only [row_extendCore_top] using present
    · intro i; simpa only [row_extendCore_fan] using fans i⟩
  have hp : topPotential n w c a v * p.eval ((c ∘ letterDart n w) ∘ l) id =
      topPotential n w c a v := by
    apply p.eval_potential
    intro f hf
    obtain ⟨e,rfl⟩ := core f hf
    exact topPotential_edge n w d c hc hcell a e
  rw [MasterGraph.Path.eval_comp] at hp
  exact mul_left_cancel (hp.trans (mul_one _).symm)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConePresentationGroup
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def polygonValue (e : Dart n w) : PolygonGroup n w d := PresentedGroup.mk _ (FreeGroup.mk [e])

lemma polygonValue_rev (e : Dart n w) :
    polygonValue n w d (rev n w e) = (polygonValue n w d e)⁻¹ := by
  unfold polygonValue
  rw [← map_inv]
  congr 1

lemma polygonValue_word (z : List (Dart n w)) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)
      (FreeGroup.mk z) = (z.map (polygonValue n w d)).prod := by
  induction z with
  | nil => exact map_one _
  | cons a z ih =>
    change PresentedGroup.mk _ (FreeGroup.mk ([a]++z)) = _
    rw [← FreeGroup.mul_mk,map_mul,ih]
    rfl

lemma polygonValue_cell (a : Cell n w d) :
    (List.ofFn (fun i => polygonValue n w d (side n w d a i))).prod = 1 := by
  have he := PresentedGroup.one_of_mem (show FreeGroup.mk (List.ofFn (side n w d a)) ∈
      FreeGroup.mk '' Set.range (boundary n w d).attachingWord from
    ⟨(boundary n w d).attachingWord a,⟨a,rfl⟩,rfl⟩)
  rw [polygonValue_word,List.map_ofFn] at he
  exact he

def freeComparison : FreeGroup (Fin (n+1)) →* PolygonGroup n w d :=
  (PresentedGroup.mk _).comp (FreeGroup.map (Sum.inl : Fin (n+1) → Edge n w))

lemma freeComparison_letter (a : Alphabet n) :
    freeComparison n w d (freeLetter n a) = polygonValue n w d (letterDart n w a) := by
  rw [freeLetter_mk]
  simp only [freeComparison,MonoidHom.comp_apply,FreeGroup.map.mk,List.map_cons,List.map_nil]
  rfl

lemma freeComparison_word (z : List (Alphabet n)) :
    freeComparison n w d (FreeGroup.mk z) =
    PresentedGroup.mk (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)
      (FreeGroup.mk (z.map (letterDart n w))) := by
  simp only [freeComparison,MonoidHom.comp_apply,FreeGroup.map.mk]
  rfl

/-- Both arbitrary closed-walk relator families, including the exceptional
loose edge, and both decoration families are consequences of the literal
fan triangles and simple macro polygons. -/
lemma freeComparison_relator (r : FreeGroup (Fin (n+1))) (hr : Relator n w d r) :
    freeComparison n w d r = 1 := by
  have hc := polygonValue_rev n w d
  have hcell := polygonValue_cell n w d
  cases hr with
  | fan l i present v p fields =>
    rw [MasterGraph.Path.eval_map]
    simp only [freeComparison_letter]
    exact fan_relator_value n w d (polygonValue n w d) hc hcell l i present v p fields
  | top l present fans v p core =>
    rw [MasterGraph.Path.eval_map]
    simp only [freeComparison_letter]
    exact top_relator_value n w d (polygonValue n w d) hc hcell l present fans v p core
  | square l τ present =>
    rw [MasterGraph.squareWord_map]
    simp only [freeComparison_letter]
    exact square_relator_value n w d (polygonValue n w d) hc hcell l τ present
  | six x present =>
    rw [map_list_prod,List.map_ofFn]
    simp only [Function.comp_def,freeComparison_letter]
    exact six_relator_value n w d (polygonValue n w d) hcell x present

lemma relator_normalClosure_le :
    Subgroup.normalClosure (Relator n w d) ≤ (freeComparison n w d).ker := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact freeComparison_relator n w d r hr

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CoreWordGraph
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate CoreGeometry MasterGraph LetterPresentation SimpleGraph
variable (S : Finset IncidenceTemplate.Edge)

lemma oriented_adj {a b : MasterGraph.Vertex} (s : Step a b)
    (e : IncidenceTemplate.Edge) (he : s.field = .inl e) (hm : e ∈ S) :
    (graph S).Adj (projection a) (projection b) := by
  rcases s with ⟨f,o,hh⟩
  dsimp at he
  subst f
  cases o <;> simp only [Bool.false_eq_true,↓reduceIte,source,target] at hh
  all_goals rcases hh with ⟨rfl,rfl⟩; exact ⟨e,rfl,hm⟩

lemma oriented_label (n : ℕ) (l : Field → Alphabet n)
    {a b : MasterGraph.Vertex} (s : Step a b)
    (e : IncidenceTemplate.Edge) (he : s.field = .inl e) (hm : e ∈ S) :
    label S n l ⟨(projection a,projection b),oriented_adj S s e he hm⟩ = stepLetter n l s := by
  rcases s with ⟨f,o,hh⟩
  dsimp at he
  subst f
  cases o <;> simp only [Bool.false_eq_true,↓reduceIte,source,target] at hh
  all_goals rcases hh with ⟨rfl,rfl⟩; rfl

abbrev Fields {a b : MasterGraph.Vertex} (p : MasterGraph.Path a b) : Prop :=
  ∀ f ∈ p.fields, ∃ e : IncidenceTemplate.Edge, f = .inl e ∧ e ∈ S

def path {a b : MasterGraph.Vertex} (p : MasterGraph.Path a b) (hp : Fields S p) :
    (graph S).Walk (projection a) (projection b) := by
  induction p with
  | nil a => exact .nil
  | cons s p ih =>
    let hh := hp _ List.mem_cons_self
    let e := Classical.choose hh
    exact .cons (oriented_adj S s e (Classical.choose_spec hh).1 (Classical.choose_spec hh).2) (ih (fun f hf => hp f (List.mem_cons_of_mem _ hf)))

lemma path_length {a b : MasterGraph.Vertex} (p : MasterGraph.Path a b) (hp : Fields S p) :
    (path S p hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    change (path S p (fun f hf => hp f (List.mem_cons_of_mem _ hf))).length + 1 = p.length + 1
    rw [ih]

lemma path_word (n : ℕ) (l : Field → Alphabet n)
    {a b : MasterGraph.Vertex} (p : MasterGraph.Path a b) (hp : Fields S p) :
    GraphWordFilling.word (label S n l) (path S p hp) = pathWord n l p := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    let hh := hp _ List.mem_cons_self
    let ht : Fields S p := fun f hf => hp f (List.mem_cons_of_mem _ hf)
    change label S n l ⟨_,oriented_adj S s (Classical.choose hh)
      (Classical.choose_spec hh).1 (Classical.choose_spec hh).2⟩ ::
      GraphWordFilling.word (label S n l) (path S p ht) = _ :: _
    rw [oriented_label S n l s (Classical.choose hh) (Classical.choose_spec hh).1 (Classical.choose_spec hh).2,ih]

def toMaster : {a b : CoreGeometry.Vertex} → (graph S).Walk a b → MasterGraph.Path (.inl a) (.inl b)
  | _,_,.nil => .nil _
  | _,_,.cons h p => .cons (coreStep (core_adj S h)) (toMaster p)

lemma toMaster_word (n : ℕ) (l : Field → Alphabet n)
    {a b : CoreGeometry.Vertex} (p : (graph S).Walk a b) :
    pathWord n l (toMaster S p) = GraphWordFilling.word (label S n l) p := by
  induction p with
  | nil => rfl
  | cons h p ih => change _ :: _ = _ :: _; exact congrArg (List.cons _) ih

end HyperbolicObstruction.CoreWordGraph
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r q p
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]

namespace WalkCellCover
variable {T : WalkCellTarget S C W L V A} {G : Type q} [Group G]
  (H : WalkCellCover T G) {B : Type p} [AddCommMonoid B]

variable (weight : G → S → B)
  (hw : ∀ g s, T.free (T.kind s) = true → weight g s + weight g (T.opposite s) = 0)

variable (P : WalkPicture.{u} (H.target weight hw))

lemma forget_noBigon (hs : P.NoBigon) : (H.forget weight hw P).NoBigon := hs

end WalkCellCover
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SimpleLetterPresentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFaceApexDart _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.LetterPresentation
open IncidenceTemplate CoreGeometry MasterGraph SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma fan_fields {v z : MasterGraph.Vertex} (i : Fin 7)
    (p : MasterGraph.Path v z) (hp : p.fields.toFinset ⊆ rowSupport (.inl i)) :
    CoreWordGraph.Fields (fan i) p := by
  intro f hf
  have hh := hp (List.mem_toFinset.mpr hf)
  rcases f with e | x
  · exact ⟨e,rfl,by simpa [rowSupport] using hh⟩
  · simp [rowSupport] at hh

lemma top_fields {v z : MasterGraph.Vertex} (p : MasterGraph.Path v z) (hp : p.IsCore) :
    CoreWordGraph.Fields Finset.univ p := by
  intro f hf
  obtain ⟨e,rfl⟩ := hp f hf
  exact ⟨e,rfl,Finset.mem_univ _⟩

end HyperbolicObstruction.LetterPresentation
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LetterCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The actual original marked presentation supplies the deck labels, via
fixed fan routes; the larger auxiliary polygon bouquet group is not used. -/
def letterVoltage (e : Dart n w) : LetterPresentation.Group n w d :=
  PresentedGroup.mk (Relator n w d) (FreeGroup.mk (collapse n w e))

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ElementaryCone
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable

lemma macroCellDart_cell (c : MacroCell) : macroCell (macroCellDart c) = c :=
  (macroCell_representative c).choose_spec.1

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma elementaryOld_rev (e : Dart n w) :
    elementaryOld n w (rev n w e) = elementaryRev n w (elementaryOld n w e) := rfl

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ElementaryCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

/-- Apex coordinate of a triangle lift is exactly its independent chain index. -/
lemma elementaryOffset_triangle_zero (a : Top n w) (c : MacroCell) :
    elementaryOffset n w d v (.inl (a,c)) (0 : Fin 3) = 1 := rfl

lemma elementaryOffset_triangle_one (a : Top n w) (c : MacroCell) :
    elementaryOffset n w d v (.inl (a,c)) (1 : Fin 3) =
      macroPotential n w v a (macroCellDart c).fst := by
  change ((List.ofFn (fun j : Fin 3 => elementaryVoltage n w v
    (elementaryTriangle n w a (macroCellDart c) j))).take 1).prod = _
  simp [elementaryTriangle,List.ofFn_succ,elementaryVoltage]

include hv hcell in
lemma elementaryOffset_triangle_two (a : Top n w) (c : MacroCell) :
    elementaryOffset n w d v (.inl (a,c)) (2 : Fin 3) =
      macroPotential n w v a (macroCellDart c).snd := by
  have he := macroPotential_edge n w d v hv hcell a (macroCellDart c).adj
  change ((List.ofFn (fun j : Fin 3 => elementaryVoltage n w v
    (elementaryTriangle n w a (macroCellDart c) j))).take 2).prod = _
  simpa [elementaryTriangle,List.ofFn_succ,elementaryVoltage,elementaryOld] using he

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFillingValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction

/-! The integral filling value of a literal nullword. This is a consequence
of constructed disks and sphere vanishing, not a replacement hypothesis. -/

/-! Literal walks in a signed incidence graph, with componentwise root paths.
No connectedness or universal-cover assertion is assumed. -/

/-! A literal disk-chain left inverse for the integral cell boundary. The
rooted-edge construction avoids assuming an arbitrary-cycle sphere producer. -/

/-! Subdivision of permutation cycles, with exact orbit-count preservation. -/
namespace PictureSwitch

section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D] [DecidableEq D]

namespace PermInsertion
variable (f : Perm D) (p : D → Prop)

lemma cycles_eq : cycles (perm f p) = cycles f := by
  rw [cycles_eq_card_classes,cycles_eq_card_classes]
  exact_mod_cast Nat.card_congr (orbitEquiv f p)

end PermInsertion
end

/-! Literal radial triangulation of the free polygon faces of a finite map.
This section concerns genuine permutations; no topological genus assertion is
included in the input. -/
section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

lemma cycles_equiv (f : Perm D) (g : Perm E) (e : D ≃ E)
    (h : ∀ x, e (f x) = g (e x)) : cycles f = cycles g := by
  have hs : ∀ x, e.symm (g x) = f (e.symm x) := by
    intro x
    apply e.injective
    simp only [apply_symm_apply,h]
  let q : Quotient (SameCycle.setoid f) ≃ Quotient (SameCycle.setoid g) := {
    toFun := Quotient.map e (fun _ _ => semiconj_perm_sameCycle h)
    invFun := Quotient.map e.symm (fun _ _ => semiconj_perm_sameCycle hs)
    left_inv := by
      intro x; induction x using Quotient.inductionOn with
      | h x => simp only [Quotient.map_mk,symm_apply_apply]
    right_inv := by
      intro x; induction x using Quotient.inductionOn with
      | h x => simp only [Quotient.map_mk,apply_symm_apply] }
  rw [cycles_eq_card_classes,cycles_eq_card_classes]
  exact_mod_cast Nat.card_congr q

namespace ConeExpansion
variable (M : PictureMap D) (p : D → Prop) (hf : ∀ d, p (M.face d) ↔ p d)

def freeFace : Perm (Subtype p) := M.face.subtypePerm hf

def face : Perm (Point p) where
  toFun := fun x => match x with
    | .inl d => if h : p d then .inr (.inl ⟨d,h⟩) else .inl (M.face d)
    | .inr (.inl t) => .inr (.inr t)
    | .inr (.inr t) => .inl t.val
  invFun := fun x => match x with
    | .inl d => if h : p d then .inr (.inr ⟨d,h⟩) else .inl (M.face.symm d)
    | .inr (.inl t) => .inl t.val
    | .inr (.inr t) => .inr (.inl t)
  left_inv := by
    rintro (d|(t|t))
    · by_cases h : p d
      · simp [h]
      · simp [h,(hf d).not.mpr h]
    · rfl
    · simp [t.property]
  right_inv := by
    rintro (d|(t|t))
    · by_cases h : p d
      · simp [h]
      · have h' : ¬ p (M.face.symm d) := by
          apply (hf (M.face.symm d)).not.mp
          simpa only [apply_symm_apply] using h
        simp [h,h']
    · simp [t.property]
    · rfl

def edge : Perm (Point p) where
  toFun := fun x => match x with
    | .inl d => .inl (M.edge d)
    | .inr (.inl t) => .inr (.inr (freeFace M p hf t))
    | .inr (.inr t) => .inr (.inl ((freeFace M p hf).symm t))
  invFun := fun x => match x with
    | .inl d => .inl (M.edge d)
    | .inr (.inl t) => .inr (.inr (freeFace M p hf t))
    | .inr (.inr t) => .inr (.inl ((freeFace M p hf).symm t))
  left_inv := by rintro (d|(t|t)) <;> simp [M.edge_edge]
  right_inv := by rintro (d|(t|t)) <;> simp [M.edge_edge]

def map : PictureMap (Point p) where
  face := face M p hf
  edge := edge M p hf
  edge_sq := by ext x; rcases x with d|(t|t) <;> simp [edge,M.edge_edge]
  edge_ne := by
    rintro (d|(t|t)) h
    · exact M.edge_ne d (Sum.inl.inj h)
    · exact Sum.inr_ne_inl (Sum.inr.inj h)
    · exact Sum.inl_ne_inr (Sum.inr.inj h)

/-- Arrange the old vertices, their inserted corners, and the new apices. -/
def vertexEquiv : ((D ⊕ {d // p (M.edge d)}) ⊕ Subtype p) ≃ Point p where
  toFun := fun x => match x with
    | .inl (.inl d) => .inl d
    | .inl (.inr t) => .inr (.inl ⟨M.edge t.val,t.property⟩)
    | .inr t => .inr (.inr t)
  invFun := fun x => match x with
    | .inl d => .inl (.inl d)
    | .inr (.inl t) => .inl (.inr ⟨M.edge t.val,by simpa only [M.edge_edge] using t.property⟩)
    | .inr (.inr t) => .inr t
  left_inv := by rintro ((d|t)|t) <;> simp [M.edge_edge]
  right_inv := by rintro (d|(t|t)) <;> simp [M.edge_edge]

omit [Fintype D] [DecidableEq D] in
lemma vertex_equiv (x : (D ⊕ {d // p (M.edge d)}) ⊕ Subtype p) :
    vertexEquiv M p (Equiv.sumCongr (PermInsertion.perm M.vertex (fun d => p (M.edge d)))
       (freeFace M p hf)⁻¹ x) = (map M p hf).vertex (vertexEquiv M p x) := by
  rcases x with (d|t)|t
  · by_cases h : p (M.edge d) <;> simp [vertexEquiv,PermInsertion.perm,map,PictureMap.vertex,face,edge,h]
  · simp [vertexEquiv,PermInsertion.perm,map,PictureMap.vertex,face,edge,freeFace]
  · rfl

lemma vertex_cycles : cycles (map M p hf).vertex = cycles M.vertex + cycles (freeFace M p hf) := by
  rw [← cycles_equiv _ _ (vertexEquiv M p) (vertex_equiv M p hf),cycles_sum,
    PermInsertion.cycles_eq,cycles_inverse]

def frozenFace : Perm {d // ¬ p d} := M.face.subtypePerm (fun d => (hf d).not)

def faceClass : Point p → Quotient (SameCycle.setoid (frozenFace M p hf)) ⊕ Subtype p
  | .inl d => if h : p d then .inr ⟨d,h⟩ else .inl (Quotient.mk _ ⟨d,h⟩)
  | .inr (.inl t) => .inr t
  | .inr (.inr t) => .inr t

omit [Fintype D] [DecidableEq D] in
lemma faceClass_step (x : Point p) : faceClass M p hf x = faceClass M p hf (face M p hf x) := by
  rcases x with d|(t|t)
  · by_cases h : p d
    · simp [face,faceClass,h]
    · simp only [face,Equiv.coe_fn_mk,dite_eq_right h,faceClass,dite_eq_right ((hf d).not.mpr h)]
      apply congrArg Sum.inl
      apply Quotient.sound
      exact (SameCycle.rfl (f := frozenFace M p hf) (x := ⟨d,h⟩)).apply_right
  · rfl
  · simp [face,faceClass,t.property]

omit [Fintype D] [DecidableEq D] in
lemma frozen_step (x : {d // ¬ p d}) :
    (Sum.inl ((frozenFace M p hf) x).val : Point p) = face M p hf (.inl x.val) := by
  simp [face,frozenFace,x.property]

/-- New triangular faces are indexed by the old free sides, not merely by
an unlabelled area count. All other face orbits are literally unchanged. -/
def faceOrbitEquiv : Quotient (SameCycle.setoid (face M p hf)) ≃
    (Quotient (SameCycle.setoid (frozenFace M p hf)) ⊕ Subtype p) where
  toFun := Quotient.lift (faceClass M p hf)
    (fun _ _ h => (sameCycle_le_of_apply (s := Setoid.ker (faceClass M p hf))
      (faceClass_step M p hf)) h)
  invFun := Sum.elim
    (Quotient.map (fun x : {d // ¬ p d} => (Sum.inl x.val : Point p))
      (fun a b h => (semiconj_perm_sameCycle (f := frozenFace M p hf)
        (t := face M p hf) (j := fun x => Sum.inl x.val) (frozen_step M p hf) h)) :
        Quotient (SameCycle.setoid (frozenFace M p hf)) → Quotient (SameCycle.setoid (face M p hf)))
    (fun t => Quotient.mk (SameCycle.setoid (face M p hf)) (.inl t.val))
  left_inv := by
    intro x; induction x using Quotient.inductionOn with
    | h x =>
      rcases x with d|(t|t)
      · by_cases h : p d <;> simp [faceClass,h]
      · change Quotient.mk (SameCycle.setoid (face M p hf)) (.inl t.val) = Quotient.mk _ (.inr (.inl t))
        apply Quotient.sound
        change (face M p hf).SameCycle _ _
        have h := (SameCycle.rfl (f := face M p hf) (x := Sum.inl t.val)).apply_right
        simpa [face,t.property] using h
      · change Quotient.mk (SameCycle.setoid (face M p hf)) (.inl t.val) = Quotient.mk _ (.inr (.inr t))
        apply Quotient.sound
        change (face M p hf).SameCycle _ _
        have h := (SameCycle.rfl (f := face M p hf) (x := Sum.inl t.val)).apply_right.apply_right
        simpa [face,t.property] using h
  right_inv := by
    rintro (x|t)
    · induction x using Quotient.inductionOn with
      | h x => simp [faceClass,x.property]
    · simp [faceClass,t.property]

lemma face_cycles : cycles (map M p hf).face = cycles (frozenFace M p hf) + Fintype.card (Subtype p) := by
  rw [cycles_eq_card_classes,cycles_eq_card_classes]
  change (Nat.card (Quotient (SameCycle.setoid (face M p hf))) : ℤ) = _
  rw [Nat.card_congr (faceOrbitEquiv M p hf),Nat.card_sum,Nat.cast_add,Nat.card_eq_fintype_card (α := Subtype p)]

lemma euler_eq : (map M p hf).euler = M.euler := by
  have hc := cycles_subtype_split M.face hf
  change cycles M.face = cycles (freeFace M p hf) + cycles (frozenFace M p hf) at hc
  rw [PictureMap.euler,vertex_cycles,face_cycles]
  change cycles M.vertex + cycles (freeFace M p hf) +
    (cycles (frozenFace M p hf) + Fintype.card (Subtype p)) -
    (Fintype.card (D ⊕ (Subtype p ⊕ Subtype p)) : ℤ) / 2 = _
  simp only [Fintype.card_sum,Nat.cast_add]
  unfold PictureMap.euler
  omega

omit [DecidableEq D] in
lemma collapse_face (x : Point p) : M.components (collapse p x) (collapse p (face M p hf x)) := by
  rcases x with d|(t|t)
  · by_cases h : p d
    · simp only [face,Equiv.coe_fn_mk,dite_eq_left h,collapse,Sum.elim_inl,Sum.elim_inr,id_eq]
      exact M.components.refl _
    · simp only [face,Equiv.coe_fn_mk,dite_eq_right h,collapse,Sum.elim_inl,id_eq]
      exact M.face_le_components SameCycle.rfl.apply_right
  · exact M.components.refl _
  · exact M.components.refl _

omit [DecidableEq D] in
lemma collapse_edge (x : Point p) : M.components (collapse p x) (collapse p (edge M p hf x)) := by
  rcases x with d|(t|t)
  · exact M.edge_le_components SameCycle.rfl.apply_right
  · exact M.face_le_components SameCycle.rfl.apply_right
  · have h := (SameCycle.rfl (f := M.face) (x := M.face.symm t.val)).apply_right.symm
    simp only [apply_symm_apply] at h
    exact M.face_le_components h

omit [DecidableEq D] in
lemma components_bound : Nat.card (Quotient M.components) ≤ Nat.card (Quotient (map M p hf).components) := by
  have hh : (map M p hf).components ≤ M.components.comap (collapse p) :=
    (map M p hf).components_le (collapse_face M p hf) (collapse_edge M p hf)
  let q : Quotient (map M p hf).components → Quotient M.components :=
    Quotient.map (collapse p) (fun _ _ h => hh h)
  have hq : Function.Surjective q := by
    intro x; obtain ⟨d,rfl⟩ := Quotient.exists_rep x
    exact ⟨Quotient.mk _ (.inl d),rfl⟩
  exact Nat.card_le_card_of_surjective q hq

/-- Removing all radial stars from a genus-zero triangulated side-pairing
preserves genus zero. This is a consequence of the permutation counts. -/
theorem genusZero_of_expansion (h : (map M p hf).GenusZero) : M.GenusZero := by
  have h₁ := euler_eq M p hf
  have h₂ := components_bound M p hf
  have h₃ := M.euler_le
  unfold PictureMap.GenusZero at h ⊢
  omega

end ConeExpansion
end

section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
namespace PictureMap
variable (M : PictureMap D) (N : PictureMap E) (e : D ≃ E)
  (hf : ∀ x, e (M.face x) = N.face (e x)) (he : ∀ x, e (M.edge x) = N.edge (e x))

include hf he

lemma euler_equiv : M.euler = N.euler := by
  have hv : ∀ x, e (M.vertex x) = N.vertex (e x) := by
    intro x; simp only [vertex,mul_apply,hf,he]
  rw [euler,euler,cycles_equiv M.vertex N.vertex e hv,cycles_equiv M.face N.face e hf,
    Fintype.card_congr e]

omit [DecidableEq D] [DecidableEq E] in
lemma components_equiv (x y : D) : M.components x y ↔ N.components (e x) (e y) := by
  have h₁ : M.components ≤ N.components.comap e := by
    apply M.components_le
    · intro x; change N.components (e x) (e (M.face x)); rw [hf]
      exact N.face_le_components SameCycle.rfl.apply_right
    · intro x; change N.components (e x) (e (M.edge x)); rw [he]
      exact N.edge_le_components SameCycle.rfl.apply_right
  have hf' : ∀ x, e.symm (N.face x) = M.face (e.symm x) := by
    intro x; apply e.injective; simp only [apply_symm_apply,hf]
  have he' : ∀ x, e.symm (N.edge x) = M.edge (e.symm x) := by
    intro x; apply e.injective; simp only [apply_symm_apply,he]
  have h₂ : N.components ≤ M.components.comap e.symm := by
    apply N.components_le
    · intro x; change M.components (e.symm x) (e.symm (N.face x)); rw [hf']
      exact M.face_le_components SameCycle.rfl.apply_right
    · intro x; change M.components (e.symm x) (e.symm (N.edge x)); rw [he']
      exact M.edge_le_components SameCycle.rfl.apply_right
  exact ⟨fun h => h₁ h,fun h => by simpa only [Setoid.comap_rel,symm_apply_apply] using h₂ h⟩

omit [DecidableEq D] [DecidableEq E] in
lemma components_card_equiv : Nat.card (Quotient M.components) = Nat.card (Quotient N.components) := by
  let q : Quotient M.components ≃ Quotient N.components := {
    toFun := Quotient.map e (fun _ _ h => (components_equiv M N e hf he _ _).mp h)
    invFun := Quotient.map e.symm (by
      intro x y h
      apply (components_equiv M N e hf he _ _).mpr
      simpa only [apply_symm_apply] using h)
    left_inv := by
      intro x; induction x using Quotient.inductionOn with
      | h x => simp only [Quotient.map_mk,symm_apply_apply]
    right_inv := by
      intro x; induction x using Quotient.inductionOn with
      | h x => simp only [Quotient.map_mk,apply_symm_apply] }
  exact Nat.card_congr q

lemma genusZero_equiv : M.GenusZero ↔ N.GenusZero := by
  simp only [GenusZero,euler_equiv M N e hf he,components_card_equiv M N e hf he]

end PictureMap
end

/-! Exact contraction of radial triangle stars. -/
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D] [DecidableEq D]

namespace TriangleMarking
variable {M : PictureMap D} (H : TriangleMarking M)

omit [Fintype D] [DecidableEq D] in
lemma top_of_role {x : D} (h : H.role x ≠ 0) : H.top x = true := by
  cases htop : H.top x with
  | false => exact False.elim (h (H.frozen x htop))
  | true => rfl

omit [Fintype D] [DecidableEq D] in
lemma top_prev (x : D) : H.top (M.face.symm x) = H.top x := by
  have h := H.top_face (M.face.symm x)
  simpa only [apply_symm_apply] using h.symm

omit [Fintype D] [DecidableEq D] in
lemma prev_eq {x : D} (h : H.top x = true) : M.face.symm x = M.face (M.face x) := by
  apply M.face.injective
  rw [apply_symm_apply,H.period x h]

omit [Fintype D] [DecidableEq D] in
lemma role_next0 {x : D} (ht : H.top x = true) (h : H.role x = 0) : H.role (M.face x) = 1 := by
  rw [H.turn x ht,h]; rfl
omit [Fintype D] [DecidableEq D] in
lemma role_next1 {x : D} (h : H.role x = 1) : H.role (M.face x) = 2 := by
  have ht := H.top_of_role (by rw [h]; decide)
  rw [H.turn x ht,h]; rfl
omit [Fintype D] [DecidableEq D] in
lemma role_next2 {x : D} (h : H.role x = 2) : H.role (M.face x) = 0 := by
  have ht := H.top_of_role (by rw [h]; decide)
  rw [H.turn x ht,h]; rfl
omit [Fintype D] [DecidableEq D] in
lemma role_prev0 {x : D} (ht : H.top x = true) (h : H.role x = 0) : H.role (M.face.symm x) = 2 := by
  rw [H.prev_eq ht]
  exact H.role_next1 (H.role_next0 ht h)
omit [Fintype D] [DecidableEq D] in
lemma role_prev1 {x : D} (h : H.role x = 1) : H.role (M.face.symm x) = 0 := by
  rw [H.prev_eq (H.top_of_role (by rw [h]; decide))]
  exact H.role_next2 (H.role_next1 h)

def next (x : D) : D := if H.top x then M.face (M.edge (M.face x)) else M.face x
def prev (x : D) : D := if H.top x then M.face.symm (M.edge (M.face.symm x)) else M.face.symm x

omit [Fintype D] [DecidableEq D] in
lemma next_role (x : H.Base) : H.role (H.next x.val) = 0 := by
  by_cases ht : H.top x.val = true
  · simp only [next,ht,ite_true]
    exact H.role_next2 (H.edge1 _ (H.role_next0 ht x.property))
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [next,hf,Bool.false_eq_true,ite_false]
    exact H.frozen _ ((H.top_face _).trans hf)

omit [Fintype D] [DecidableEq D] in
lemma next_top (x : H.Base) : H.top (H.next x.val) = H.top x.val := by
  by_cases ht : H.top x.val = true
  · simp only [next,ht,ite_true,H.top_face]
    apply H.top_of_role
    rw [H.edge1 _ (H.role_next0 ht x.property)]; decide
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [next,hf,Bool.false_eq_true,ite_false,H.top_face]

omit [Fintype D] [DecidableEq D] in
lemma prev_role (x : H.Base) : H.role (H.prev x.val) = 0 := by
  by_cases ht : H.top x.val = true
  · simp only [prev,ht,ite_true]
    exact H.role_prev1 (H.edge2 _ (H.role_prev0 ht x.property))
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [prev,hf,Bool.false_eq_true,ite_false]
    exact H.frozen _ ((H.top_prev _).trans hf)

omit [Fintype D] [DecidableEq D] in
lemma prev_top (x : H.Base) : H.top (H.prev x.val) = H.top x.val := by
  by_cases ht : H.top x.val = true
  · simp only [prev,ht,ite_true,H.top_prev]
    apply H.top_of_role
    rw [H.edge2 _ (H.role_prev0 ht x.property)]; decide
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [prev,hf,Bool.false_eq_true,ite_false,H.top_prev]

omit [Fintype D] [DecidableEq D] in
lemma prev_next (x : H.Base) : H.prev (H.next x.val) = x.val := by
  unfold prev
  rw [H.next_top]
  by_cases ht : H.top x.val = true
  · simp only [ht,ite_true,next,symm_apply_apply,M.edge_edge]
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [hf,Bool.false_eq_true,ite_false,next,symm_apply_apply]

omit [Fintype D] [DecidableEq D] in
lemma next_prev (x : H.Base) : H.next (H.prev x.val) = x.val := by
  unfold next
  rw [H.prev_top]
  by_cases ht : H.top x.val = true
  · simp only [ht,ite_true,prev,apply_symm_apply,M.edge_edge]
  · have hf : H.top x.val = false := Bool.eq_false_iff.mpr ht
    simp only [hf,Bool.false_eq_true,ite_false,prev,apply_symm_apply]

/-- Each macro face walks through consecutive radial triangles around one
actual apex. Frozen face cycles are unchanged. -/
def face : Perm H.Base where
  toFun x := ⟨H.next x.val,H.next_role x⟩
  invFun x := ⟨H.prev x.val,H.prev_role x⟩
  left_inv x := Subtype.ext (H.prev_next x)
  right_inv x := Subtype.ext (H.next_prev x)

omit [Fintype D] [DecidableEq D] in
lemma edge_invariant (x : D) : H.role (M.edge x) = 0 ↔ H.role x = 0 :=
  ⟨fun h => by simpa only [M.edge_edge] using H.edge0 (M.edge x) h,H.edge0 x⟩

def contraction : PictureMap H.Base where
  face := H.face
  edge := M.edge.subtypePerm H.edge_invariant
  edge_sq := by ext x; exact M.edge_edge x.val
  edge_ne := by intro x h; exact M.edge_ne x.val (congrArg Subtype.val h)

end TriangleMarking
end PictureSwitch

/-! Local elementary triangle incidence induces the exact radial contraction. -/
namespace ConeSkeleton

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

lemma elementaryTop_next (s : ElementaryLiftSide n w d v hv hcell) :
    elementaryTop n w d v hv hcell ((elementaryLiftedBoundary n w d v hv hcell).next s) =
      elementaryTop n w d v hv hcell s := rfl

end

/-! Exact deck coordinates on the old and two radial sides of every triangle. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

def elementaryWalkIndex : ElementaryLiftSide n w d v hv hcell → G × WalkStep n w d
  | ⟨⟨g,.inl a⟩,b,_⟩ => (g,.inl (a.1,if b then macroCellDart a.2 else (macroCellDart a.2).symm))
  | ⟨⟨g,.inr a⟩,b,i⟩ => (g,.inr ⟨a,b,i⟩)

lemma elementaryTop_walk (s : ElementaryLiftSide n w d v hv hcell) :
    elementaryTop n w d v hv hcell s = walkFree n w d (walkKind n w d
      (elementaryWalkIndex n w d v hv hcell s).2) := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩ <;> rfl

lemma elementaryOld_injective : Function.Injective (elementaryOld n w) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  exact Prod.ext (Sum.inl.inj (congrArg (fun z : ElementaryDart n w => z.1) h))
    (congrArg (fun z : ElementaryDart n w => z.2) h)

lemma elementaryOffset_frozen (_ : G) (c : FrozenCell n w d)
    (i : Fin ((frozenBoundary n w d).size c)) :
    elementaryOffset n w d v (.inr c) i =
      (((List.ofFn ((frozenBoundary n w d).label c)).take i.val).map v).prod := by
  simp only [elementaryOffset,List.map_take,List.map_ofFn,Function.comp_def]
  rfl

/-- Incoming radial dart after the old side, using the actual top basepoint. -/
lemma elementary_incoming (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementarySideRole n w d v hv hcell s = 0)
    (g : G) (a : Top n w) (e : MacroGraph.graph.Dart)
    (he : elementaryWalkIndex n w d v hv hcell s = (g,.inl (a,e))) :
    (elementaryLiftedBoundary n w d v hv hcell).sideLabel
      ((elementaryLiftedBoundary n w d v hv hcell).next s) =
      (g * macroPotential n w v a e.snd, (.inr (a,e.snd),false)) := by
  rcases s with ⟨⟨k,c|c⟩,b,i⟩
  · have hi : i = (1 : Fin 3) := by
      cases b <;> fin_cases i <;> first | rfl | cases h
    subst i
    cases b with
    | false =>
      simp only [elementaryWalkIndex,Bool.false_eq_true,ite_false] at he
      cases he
      change (g * elementaryOffset n w d v (.inl c) (0 : Fin 3) * macroPotential n w v c.1 _,_) = _
      rw [elementaryOffset_triangle_zero,mul_one]
      rfl
    | true =>
      simp only [elementaryWalkIndex,ite_true] at he
      cases he
      change (g * elementaryOffset n w d v (.inl c) (2 : Fin 3),_) = _
      rw [elementaryOffset_triangle_two n w d v hv hcell]
      rfl
  · cases he

/-- Outgoing radial dart before the old side; its deck coordinate is EXACTLY
that of the independent lifted elementary-cell coordinate. -/
lemma elementary_outgoing (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementarySideRole n w d v hv hcell s = 0)
    (g : G) (a : Top n w) (e : MacroGraph.graph.Dart)
    (he : elementaryWalkIndex n w d v hv hcell s = (g,.inl (a,e))) :
    (elementaryLiftedBoundary n w d v hv hcell).sideLabel
      ((elementaryLiftedBoundary n w d v hv hcell).next
        ((elementaryLiftedBoundary n w d v hv hcell).next s)) =
      (g, (.inr (a,e.fst),true)) := by
  rcases s with ⟨⟨k,c|c⟩,b,i⟩
  · have hi : i = (1 : Fin 3) := by
      cases b <;> fin_cases i <;> first | rfl | cases h
    subst i
    cases b with
    | false =>
      simp only [elementaryWalkIndex,Bool.false_eq_true,ite_false] at he
      cases he
      change (g * elementaryOffset n w d v (.inl c) (2 : Fin 3) * (macroPotential n w v c.1 _)⁻¹,_) = _
      rw [elementaryOffset_triangle_two n w d v hv hcell,mul_inv_cancel_right]
      rfl
    | true =>
      simp only [elementaryWalkIndex,ite_true] at he
      cases he
      change (g * elementaryOffset n w d v (.inl c) (0 : Fin 3),_) = _
      rw [elementaryOffset_triangle_zero,mul_one]
      rfl
  · cases he

end

/-! Every genuine elementary genus-zero picture contracts to the unchanged
macro/frozen target, preserving the literal original-group deck coordinates. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)
variable {A : Type*} [AddCommGroup A] (weight : G × ElementaryCell n w d → A)
  (P : CellPicture (elementaryRawTarget n w d v hv hcell weight))

def elementaryContractIndex (x : ElementaryBases n w d v hv hcell weight P) : G × WalkStep n w d :=
  elementaryWalkIndex n w d v hv hcell (P.index x.val)

end

/-! The radial contraction preserves every independent lifted elementary-cell
coefficient, not just an augmentation or a projection to the old edges. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)
variable {A : Type*} [AddCommGroup A]
  (tc : G → Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ g a e, tc g a e.symm = -tc g a e) (fc : G → FrozenCell n w d → A)

def elementaryMacroWeight : G × ElementaryCell n w d → A
  | (g,.inl a) => tc g a.1 (macroCellDart a.2)
  | (g,.inr a) => fc g a

def elementaryMarkPosition : (c : ElementaryCell n w d) → Fin (elementarySize n w d c)
  | .inl _ => (1 : Fin 3)
  | .inr a => ⟨0,(frozenBoundary n w d).positive a⟩

end

/-! Every genus-zero picture over the literal elementary lifted-cell boundary
has zero FULL cellular chain, by exact radial contraction. -/
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u v z
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type v} [Group G] {A : Type z} [AddCommGroup A]
  (weight : G × ElementaryCell n w d → A)

def elementaryTopWeight (g : G) (a : Top n w) (e : MacroGraph.graph.Dart) : A :=
  macroOrientation e • weight (g, .inl (a, macroCell e))

end ConeSkeleton

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/
namespace VoltageWords

open HyperbolicObstruction.WordPictures HyperbolicObstruction.PictureSwitch
variable {A G V C : Type*} [Group G]

variable (B : PolygonTarget.Boundary C (A × Bool) V) (v : A → G)
  (hinv : B.rev = invLetter)
  (hc : ∀ c, total v (B.attachingWord c) = 1)

/-- All individual lifted polygons, expressed in genuine signed lift edges. -/
def liftedBoundary : PolygonTarget.Boundary (G × C) ((G × A) × Bool) (G × V) where
  size c := B.size c.2
  positive c := B.positive c.2
  label c i := encode v (c.1 * ((List.ofFn (voltage v ∘ B.label c.2)).take i.val).prod,
    B.label c.2 i)
  start := liftedStart B v
  rev := invLetter
  inv := invLetter_invLetter
  closed c i := by
    rw [← encode_reverse,liftedStart_encode,liftedStart_encode]
    apply Prod.ext
    · rw [ConeSkeleton.group_prefix_rotate _ (by
        simpa only [total,PolygonTarget.Boundary.attachingWord,List.map_ofFn] using hc c.2) i]
      exact (mul_assoc _ _ _).symm
    · simpa only [hinv] using B.closed c.2 i

end VoltageWords

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

section
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable

lemma macroCell_eq_or_symm {e f : MacroGraph.graph.Dart} (h : macroCell e = macroCell f) :
    e = f ∨ e = f.symm := by
  have hh := Sym2.eq_iff.mp (congrArg Subtype.val h)
  rcases e with ⟨⟨a,b⟩,he⟩
  rcases f with ⟨⟨c,d⟩,hf⟩
  rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : ElementaryDart n w → H)
  (hc : ∀ e, c (elementaryRev n w e) = (c e)⁻¹)
  (hcell : ∀ a : ElementaryCell n w d,
    (List.ofFn (fun i => c (elementarySide n w d a i))).prod = 1)

include hc hcell in
lemma elementary_radial_relation (a : Top n w) (e : MacroGraph.graph.Dart) :
    c (.inr (a,e.fst),true) * c (elementaryOld n w (macroStep n w a e.adj)) =
      c (.inr (a,e.snd),true) := by
  have hp (f : MacroGraph.graph.Dart) (hf : macroCellDart (macroCell e) = f) :
      c (.inr (a,f.fst),true) * c (elementaryOld n w (macroStep n w a f.adj)) =
        c (.inr (a,f.snd),true) := by
    have hh := hcell (.inl (a,macroCell e))
    change (List.ofFn (fun i => c (elementaryTriangle n w a (macroCellDart (macroCell e)) i))).prod = 1 at hh
    rw [hf] at hh
    simp only [elementaryTriangle,List.ofFn_succ,List.ofFn_zero,Matrix.cons_val_zero,
      Matrix.cons_val_succ,List.prod_cons,List.prod_nil,mul_one] at hh
    have hr := hc (.inr (a,f.snd),true)
    change c (.inr (a,f.snd),false) = _ at hr
    rw [hr,← mul_assoc] at hh
    exact mul_inv_eq_one.mp hh
  rcases macroCell_eq_or_symm (macroCellDart_cell (macroCell e)) with he | he
  · exact hp e he
  · have hh := hp e.symm he
    have hr : c (elementaryOld n w (macroStep n w a e.symm.adj)) =
        (c (elementaryOld n w (macroStep n w a e.adj)))⁻¹ := by
      exact (congrArg (fun z => c (elementaryOld n w z)) (macroStep_reverse n w a e.adj)).trans
        ((congrArg c (elementaryOld_rev n w (macroStep n w a e.adj))).trans
          (hc (elementaryOld n w (macroStep n w a e.adj))))
    rw [hr] at hh
    exact (eq_mul_inv_iff_mul_eq.mp hh.symm)

include hc hcell in
lemma elementary_old_cell (a : Cell n w d) :
    (List.ofFn (fun i => c (elementaryOld n w (side n w d a i)))).prod = 1 := by
  rcases a with f | a | a | a
  · exact hcell (.inr (.inl f))
  · rcases a with ⟨a,u,p,hp⟩
    have he := GraphGroupWalk.eval_potential
      (fun e : MacroGraph.graph.Dart => c (elementaryOld n w (macroStep n w a e.adj)))
      (fun v => c (.inr (a,v),true)) (elementary_radial_relation n w d c hc hcell a) p
    have hz : GraphGroupWalk.eval
        (fun e : MacroGraph.graph.Dart => c (elementaryOld n w (macroStep n w a e.adj))) p = 1 :=
      mul_left_cancel (he.trans (mul_one _).symm)
    have hm := congrArg (fun z : List (Dart n w) => (z.map (c ∘ elementaryOld n w)).prod)
      (macro_darts n w a p hp)
    simp only [List.map_map,List.map_ofFn,Function.comp_def] at hm
    exact hm.symm.trans hz
  · exact hcell (.inr (.inr (.inl a)))
  · exact hcell (.inr (.inr (.inr a)))

lemma elementaryPolygonValue_rev (e : ElementaryDart n w) :
    elementaryPolygonValue n w d (elementaryRev n w e) = (elementaryPolygonValue n w d e)⁻¹ := by
  unfold elementaryPolygonValue
  rw [← map_inv]
  congr 1

lemma elementaryPolygonValue_word (z : List (ElementaryDart n w)) :
    PresentedGroup.mk (FreeGroup.mk '' Set.range (elementaryBoundary n w d).attachingWord)
      (FreeGroup.mk z) = (z.map (elementaryPolygonValue n w d)).prod := by
  induction z with
  | nil => exact map_one _
  | cons a z ih =>
    change PresentedGroup.mk _ (FreeGroup.mk ([a] ++ z)) = _
    rw [← FreeGroup.mul_mk,map_mul,ih]
    rfl

lemma elementaryPolygonValue_cell (a : ElementaryCell n w d) :
    (List.ofFn (fun i => elementaryPolygonValue n w d (elementarySide n w d a i))).prod = 1 := by
  have he := PresentedGroup.one_of_mem (show FreeGroup.mk (List.ofFn (elementarySide n w d a)) ∈
      FreeGroup.mk '' Set.range (elementaryBoundary n w d).attachingWord from
    ⟨(elementaryBoundary n w d).attachingWord a,⟨a,rfl⟩,rfl⟩)
  rw [elementaryPolygonValue_word,List.map_ofFn] at he
  exact he

end ConeSkeleton
end

namespace ConeSkeleton

section
open IncidenceTemplate CoreGeometry LetterPresentation
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Inclusion of original letters in the literal elementary edge bouquet. -/
def elementaryFreeComparison : FreeGroup (Fin (n+1)) →* ElementaryPolygonGroup n w d :=
  (PresentedGroup.mk _).comp
    (FreeGroup.map (fun i : Fin (n+1) => (Sum.inl (Sum.inl i) : ElementaryEdge n w)))

lemma elementaryFreeComparison_letter (a : Alphabet n) :
    elementaryFreeComparison n w d (freeLetter n a) =
      elementaryPolygonValue n w d (elementaryOld n w (letterDart n w a)) := by
  rw [freeLetter_mk]
  simp only [elementaryFreeComparison,MonoidHom.comp_apply,FreeGroup.map.mk,List.map_cons,List.map_nil]
  rfl

lemma elementaryFreeComparison_relator (r : FreeGroup (Fin (n+1))) (hr : Relator n w d r) :
    elementaryFreeComparison n w d r = 1 := by
  let c : Dart n w → ElementaryPolygonGroup n w d := elementaryPolygonValue n w d ∘ elementaryOld n w
  have hc : ∀ e, c (rev n w e) = (c e)⁻¹ := fun e => elementaryPolygonValue_rev n w d (elementaryOld n w e)
  have hcell := elementary_old_cell n w d (elementaryPolygonValue n w d)
    (elementaryPolygonValue_rev n w d) (elementaryPolygonValue_cell n w d)
  cases hr with
  | fan l i present v p fields =>
    rw [MasterGraph.Path.eval_map]
    simp only [elementaryFreeComparison_letter]
    exact fan_relator_value n w d c hc hcell l i present v p fields
  | top l present fans v p core =>
    rw [MasterGraph.Path.eval_map]
    simp only [elementaryFreeComparison_letter]
    exact top_relator_value n w d c hc hcell l present fans v p core
  | square l τ present =>
    rw [MasterGraph.squareWord_map]
    simp only [elementaryFreeComparison_letter]
    exact square_relator_value n w d c hc hcell l τ present
  | six x present =>
    rw [map_list_prod,List.map_ofFn]
    simp only [Function.comp_def,elementaryFreeComparison_letter]
    exact six_relator_value n w d c hcell x present

lemma elementaryRelatorClosure_le :
    Subgroup.normalClosure (Relator n w d) ≤ (elementaryFreeComparison n w d).ker := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact elementaryFreeComparison_relator n w d r hr

end

open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch SimpleGraph
attribute [local instance] Classical.propDecidable

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma elementaryOldValue_rev (e : Dart n w) :
    elementaryOldValue n w d (rev n w e) = (elementaryOldValue n w d e)⁻¹ :=
  elementaryPolygonValue_rev n w d (elementaryOld n w e)

lemma elementaryOldValue_cell (a : Cell n w d) :
    (List.ofFn (fun i => elementaryOldValue n w d (side n w d a i))).prod = 1 :=
  elementary_old_cell n w d (elementaryPolygonValue n w d)
    (elementaryPolygonValue_rev n w d) (elementaryPolygonValue_cell n w d) a

end ConeSkeleton

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

namespace ConeSkeleton

/-! Signed-edge encoding preserves all individual cell identities and the
closed-picture chain. Sphere vanishing therefore applies to indexed disks. -/

/-! Actual integral boundaries for the uncompressed cone cells. -/
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch IntegralIncidence

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def elementaryPolygons : Polygons (ElementaryEdge n w) (ElementaryVertex n w)
    (ElementaryCell n w d) where
  start := elementaryStart n w
  size := elementarySize n w d
  positive := (elementaryBoundary n w d).positive
  side := elementarySide n w d
  closed := (elementaryBoundary n w d).closed

end ConeSkeleton

/-! No reselection: the same final arrays already have the precise uniform
lifted-picture estimate. Apply the new disk-chain left inverse to those arrays. -/

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

namespace ConeSkeleton
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
attribute [local instance] Classical.propDecidable

/-- Literal conversion into the finite complex type. -/
def elementaryFiniteComplex : FiniteComplex :=
  toFiniteComplex (elementarySimplicialComplex n w d)

end ConeSkeleton

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

/-! Identification of the actual finite elementary polyhedron's pi1 with the
original letter presentation, using actual path classes and voltage covers. -/

namespace ConeSkeleton

section
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryVertex_1
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryEdge_1
attribute [local instance] OAI.HyperbolicObstruction.ConeSkeleton.instDecidableEqElementaryCell_1
abbrev elementaryRootedVoltage := (elementaryPolygonData n w d).rootedVoltage
  (elementaryRoot n w) (elementaryOldRoutes n w d)

def elementaryPolygonToTopology : ElementaryPolygonGroup n w d →* ElementaryPiOne n w d :=
  (elementaryPolygonData n w d).polygonToTopology (elementaryRoot n w) (elementaryOldRoutes n w d)

lemma elementaryPolygonToTopology_value (e : ElementaryDart n w) :
    elementaryPolygonToTopology n w d (elementaryPolygonValue n w d e) =
      (elementaryPolygonData n w d).graphTransport (elementaryRootedVoltage n w d) e :=
  (elementaryPolygonData n w d).polygonToTopology_value (elementaryRoot n w) (elementaryOldRoutes n w d) e

lemma elementary_oldGauge_toTopology (v : Vertex n w) :
    elementaryPolygonToTopology n w d (oldGauge n w d v) = 1 := by
  rcases v with u|f
  · exact map_one _
  · rw [oldGauge,elementaryPolygonToTopology_value,Data.rooted_graphChain]
    apply MulOpposite.unop_injective
    change (((elementaryPolygonData n w d).graphChain (.inl (.inr ⟨f,fanBase f.val.1⟩),true)).pathClass.symm).trans
      (((elementaryPolygonData n w d).graphChain (.inl (.inr ⟨f,fanBase f.val.1⟩),true)).pathClass.trans (.refl _)) = .refl _
    simp

lemma elementary_gauge_toTopology (v : ElementaryVertex n w) :
    elementaryPolygonToTopology n w d (elementaryGauge n w d v) = 1 := by
  rcases v with v|a
  · exact elementary_oldGauge_toTopology n w d v
  · rw [elementaryGauge,map_mul]
    have hg : elementaryPolygonToTopology n w d (oldGauge n w d
        (macroVertex n w a (MacroGraph.point 0))) = 1 := by
      exact elementary_oldGauge_toTopology n w d _
    rw [hg,mul_one,elementaryPolygonToTopology_value,Data.rooted_graphChain]
    apply MulOpposite.unop_injective
    exact Data.based_eq_one_of_rev_route
      (elementaryCoreRoutes n w d (macroVertex n w a (MacroGraph.point 0)))
      ((elementaryPolygonData n w d).graphChain (.inr (a,MacroGraph.point 0),true)).pathClass

end

/-! Injectivity of the actual pi1 comparison, detected by the genuine
voltage covering. -/

open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
local instance instDecidableEqElementaryVertex_2 : DecidableEq (ElementaryVertex n w) := Classical.decEq _
local instance instDecidableEqElementaryEdge_2 : DecidableEq (ElementaryEdge n w) := Classical.decEq _
local instance instDecidableEqElementaryCell_2 : DecidableEq (ElementaryCell n w d) := Classical.decEq _
local instance instTopologicalSpaceGroup : TopologicalSpace (LetterPresentation.Group n w d) := ⊥
local instance instDiscreteTopologyGroup : DiscreteTopology (LetterPresentation.Group n w d) := ⟨rfl⟩

end ConeSkeleton

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

namespace ConeSkeleton
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
local instance instTopologicalSpaceGroup_1 : TopologicalSpace (LetterPresentation.Group n w d) := ⊥
local instance instDiscreteTopologyGroup_1 : DiscreteTopology (LetterPresentation.Group n w d) := ⟨rfl⟩

end ConeSkeleton

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

namespace ConeSkeleton
attribute [local instance] Classical.propDecidable
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
local instance instTopologicalSpaceGroup_2 : TopologicalSpace (LetterPresentation.Group n w d) := ⊥
local instance instDiscreteTopologyGroup_2 : DiscreteTopology (LetterPresentation.Group n w d) := ⟨rfl⟩

end ConeSkeleton

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/

section

/-! A proved edge-and-triangle presentation of the actual fundamental group
of a finite barycentric realization. The rooted routes are actual edge paths;
no van Kampen theorem or fundamental-group comparison is postulated. -/

attribute [local instance] Classical.propDecidable
open Set
namespace FinitePolyhedron.EdgePresentation
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

variable (o : V) (R : ∀ a, EdgeChain K o a)

abbrev routeClasses (a : V) := (R a).pathClass
abbrev topGenerator (s : Generator K) : RootedPaths.PiOne (K := K) o :=
  RootedPaths.edgeLoop o (routeClasses K o R) s.val.1 s.val.2

lemma lift_freeEval {a b : V} (p : EdgeChain K a b) :
    FreeGroup.lift (topGenerator K o R) (freeEval K p) =
      RootedPaths.based o (routeClasses K o R) p.pathClass := by
  induction p with
  | nil a => simpa using (RootedPaths.based_refl o (routeClasses K o R) a).symm
  | cons h q ih =>
    rw [freeEval_cons,map_mul,FreeGroup.lift_apply_of,ih,EdgeChain.pathClass_cons,
      RootedPaths.based_trans]
    congr 1
    exact RootedPaths.edgeLoop_of_edge o (routeClasses K o R) h

lemma relation_valid (hR : R o = .nil o) (r : FreeGroup (Generator K))
    (hr : Relation K o R r) : FreeGroup.lift (topGenerator K o R) r = 1 := by
  cases hr with
  | self a =>
    rw [FreeGroup.lift_apply_of]
    exact (RootedPaths.voltage o (routeClasses K o R)).self a
  | triangle h hab hbc hac =>
    rw [map_mul,map_mul,map_inv,FreeGroup.lift_apply_of,FreeGroup.lift_apply_of,FreeGroup.lift_apply_of,
      mul_inv_eq_one]
    exact (RootedPaths.voltage o (routeClasses K o R)).triangle _ _ _ h
  | route a =>
    rw [lift_freeEval]
    apply RootedPaths.based_route
    simp [routeClasses,hR]

/-- The presented edge group maps into the actual topological pi1. -/
def toTopology (hR : R o = .nil o) : PresentationGroup K o R →* RootedPaths.PiOne (K := K) o :=
  PresentedGroup.toGroup (relation_valid K o R hR)

@[simp] lemma toTopology_gen (hR : R o = .nil o) {a b : V} (h : {a,b} ∈ K.faces) :
    toTopology K o R hR (gen K o R h) = RootedPaths.edgeLoop o (routeClasses K o R) a b := by
  exact PresentedGroup.toGroup.of _

end FinitePolyhedron.EdgePresentation
end

/-! Quantitative finite-presentation change, with all word substitutions and
comparison disks constructed. Relator disks are used only after establishing
that the corresponding literal words are null. -/

/-! Literal finite relator words for the proved actual fundamental-group
presentation, including exact rooted route words. -/

/-! Realization of ordinary word disks as literal triangular edge disks over
the frozen finite polyhedron. Free-group folds become actual zero-cost spurs. -/

/-! Group-isomorphism transport for geometric actions. -/

/-! Actual homotopy-equivalence invariance of the fundamental group. -/

/-! The literal finite barycentric complex has exactly the original letter group,
not a conditional presentation of it. -/

namespace ConeSkeleton

/-! Infinitude can be obtained without a topological Euler theorem: the many
six-letter cells alone inject into the original letter-edge module of any
finite cover. Their cardinality exceeds the number of original generators. -/

open IncidenceTemplate CoreGeometry LetterPresentation IntegralIncidence
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def sixCellIndex (c : LetterPresentation.Group n w d × Six n d) :
    LetterPresentation.Group n w d × ElementaryCell n w d :=
  (c.1,.inr (.inr (.inr c.2)))

def originalEdgeIndex (e : LetterPresentation.Group n w d × Fin (n+1)) :
    LetterPresentation.Group n w d × ElementaryEdge n w :=
  (e.1,.inl (.inl e.2))

end ConeSkeleton

/-! The same supplied final arrays yield infinite groups unconditionally.
This discharges the last group-action-side hypothesis; the finite-polyhedron
realization and group-to-topology consequences are still separate obligations. -/

/-! Elementary facts about WordLength and WordDistance for the four-point
characterization of hyperbolicity. -/

/-! Cochains are evaluated on the actual area-counted word homotopies.
Free folds contribute exactly zero; each literal relator contributes its
own cochain integral. No planar realization hypothesis is needed. -/

/-! Finite unit-speed vertex paths; all indices are bounded explicitly. -/

/-! A quantitative proof that linear word-homotopy filling bounds imply
four-point hyperbolicity. -/

/-! All clauses of the exact main except exclusion of compatible locally
CAT(-1) finite homotopy models. The complete literal hyperbolicity consequence
is now unconditional, on the SAME finite aspherical complex. -/

/-! The real comparison inequality needed to pass the manuscript's exact
cosh-midpoint CAT(-1) definition to the Euclidean CN midpoint inequality. -/

/-! The global cosh-midpoint comparison implies whole-segment CAT(0)
comparison. No completeness or globalization
hypothesis is hidden in this elementary curvature-monotonicity step. -/

/-! The finite difference maximum principle required for local geodesic
continuation. Endpoint estimates are literal, with no convergence assumption. -/

/-! Literal equal-time interpolation of finite geodesic polygons. -/
open Set Metric

end HyperbolicObstruction

end

end OAI
end


