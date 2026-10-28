-- Prove2me | Definitions.Def_OAIQ034H008
-- name    : OAIQ034H008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:39:27.474158+00:00
-- url     : https://prove2.me/theorems/1c379a5e-ca84-473c-a405-d01f848a35e1
-- title:
--   Definitions bundle OAIQ034H008 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 154 declarations of OpenAI's Lean: 40 definitions, 7 instances and 107 theorems. The definitions and types are `OAI.HyperbolicObstruction.ConeSkeleton.accountDart`, `OAI.HyperbolicObstruction.ConeSkeleton.actualArea`, `OAI.HyperbolicObstruction.ConeSkeleton.actualBoundary`, `OAI.HyperbolicObstruction.ConeSkeleton.actualCellCover`, `OAI.HyperbolicObstruction.ConeSkeleton.actualFanWeight`, `OAI.HyperbolicObstruction.ConeSkeleton.actualPartialCount`, `OAI.HyperbolicObstruction.ConeSkeleton.actualPayments`, `OAI.HyperbolicObstruction.ConeSkeleton.actualSixCount`, `OAI.HyperbolicObstruction.ConeSkeleton.actualSquareCount`, `OAI.HyperbolicObstruction.ConeSkeleton.actualTopCount`, `OAI.HyperbolicObstruction.ConeSkeleton.actualTriangleCount`, `OAI.HyperbolicObstruction.ConeSkeleton.actualWeights`, `OAI.HyperbolicObstruction.ConeSkeleton.contactLeft`, `OAI.HyperbolicObstruction.ConeSkeleton.contactRight`, `OAI.HyperbolicObstruction.ConeSkeleton.coverOffset`, `OAI.HyperbolicObstruction.ConeSkeleton.decorationRawDart`, `OAI.HyperbolicObstruction.ConeSkeleton.elementaryPolyhedron`, `OAI.HyperbolicObstruction.ConeSkeleton.frozenFaceDart`, `OAI.HyperbolicObstruction.ConeSkeleton.paymentBool`, `OAI.HyperbolicObstruction.ConeSkeleton.paymentCorner`, `OAI.HyperbolicObstruction.ConeSkeleton.paymentRawDart`, `OAI.HyperbolicObstruction.ConeSkeleton.triangleCorner`, `OAI.HyperbolicObstruction.ConeSkeleton.triangleRawDart`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.RetainedContact`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentHom`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentPicture`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentVertex`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.cotreeColor`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.cotreeGraph`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.faceCorners`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.retainedContactEdge`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.starComponent`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.starIndex`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.starOldHom`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.starOldVertex`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.starVertexClass`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.vertexColor`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.vertexRepresentative`, `OAI.HyperbolicObstruction.PictureSwitch.TriangleMarking.free`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_ActualContact`, `HyperbolicGroups_ActualFaceCounts`, `HyperbolicGroups_ActualFragment`, `HyperbolicGroups_ActualPartition`, `HyperbolicGroups_ActualRawCount`, `HyperbolicGroups_ActualWeights`, `HyperbolicGroups_ConeCover`, `HyperbolicGroups_FragmentSlots`, `HyperbolicGroups_FrozenFaceSide`, `HyperbolicGroups_FrozenSideExists`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_MacroExceptional`, `HyperbolicGroups_PairingTreeCotree`, `HyperbolicGroups_PictureBFSSeparator`, `HyperbolicGroups_PictureBoundaryHull`, `HyperbolicGroups_PictureComponentGraph`, `HyperbolicGroups_PictureCotreeColor`, `HyperbolicGroups_PictureCotreeTree`, `HyperbolicGroups_PictureDual`, `HyperbolicGroups_PictureFaceCorners`, `HyperbolicGroups_PictureFullSeparator`, `HyperbolicGroups_PictureOutsideColor`, `HyperbolicGroups_PicturePlanarSeparator`, `HyperbolicGroups_PictureRootSeparator`, `HyperbolicGroups_PictureSqrtSeparator`, `HyperbolicGroups_PictureStarGraph`, `HyperbolicGroups_PictureTriangulation`, `HyperbolicGroups_PictureTriangulationEuler`, `HyperbolicGroups_PictureVertexCut`, `HyperbolicGroups_PlanarEdgeOrdering`, `HyperbolicGroups_PlanarFacePartition`, `HyperbolicGroups_PlanarPartitionBridge`, `HyperbolicGroups_PlanarSubpairing`, `HyperbolicGroups_Presentation`, `HyperbolicGroups_RelativeDegree`, `HyperbolicGroups_SubpairingCopies`, `HyperbolicGroups_SubpairingDarts`, `HyperbolicGroups_SubpairingGraph`, `HyperbolicGroups_SubpairingTree`, `HyperbolicGroups_TreeSubpairingLift`, `HyperbolicGroups_WalkFanCapacity`, `HyperbolicGroups_WalkMultiplicity`, `HyperbolicGroups_WalkPayment`, `HyperbolicGroups_WalkRadialBoundary`, `HyperbolicGroups_WalkTopTurns`, `HyperbolicGroups_WalkTriangleTransport`.
--
--   **Imports.** It imports the bundles `OAIQ034H003`, `OAIQ034H004` and `OAIQ034H005` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ034H011`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ034H003
import Definitions.Def_OAIQ034H004
import Definitions.Def_OAIQ034H005

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Presentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

instance group : _root_.Group (Group n w d) := instGroupPresentedGroup _

end LetterPresentation
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkFanCapacity
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace
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

/-- The same indexed fan field occurs at most once at one normalized apex
instance, INCLUDING opposite triangle orientations. Opposite orientations
would force a canceling two-step vertex link. -/
lemma fan_field_once (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))
    {x y : P.Dart} {g : FanTriangle n w} {o p : Bool}
    (hx : P.index x = frozenCorner n w d g o)
    (hy : P.index y = frozenCorner n w d g p)
    (hxy : P.pairing.vertex.SameCycle x y) : x = y := by
  have hax : isApex n w (start n w (walkLabel n w d (P.index x))) = true := by
    rw [hx,frozenCorner_start]; rfl
  by_cases hop : o = p
  · apply hrad x y hax hxy
    change walkLabel n w d (P.index x) = walkLabel n w d (P.index y)
    rw [hx,hy,hop]
  · have hprev : ∀ z : P.Dart, P.pairing.vertex.SameCycle (P.pairing.vertex⁻¹ z) z :=
      fun z => sameCycle_inv.mp (SameCycle.rfl (x := z)).apply_left
    have hp : p = !o := by cases o <;> cases p <;> simp_all
    have h1 : P.pairing.vertex⁻¹ x = y := by
      refine hrad _ _ ?_ ((hprev x).trans hxy) ?_
      · change isApex n w (start n w (walkLabel n w d (P.index (P.pairing.vertex⁻¹ x)))) = true
        rw [walk_start_link_constant n w d c hc f P (hprev x)]
        exact hax
      · change walkLabel n w d (P.index (P.pairing.vertex⁻¹ x)) = walkLabel n w d (P.index y)
        rw [walk_corner_incoming n w d c hc f P hm hx,hy,frozenCorner_label,hp]
        cases o <;> rfl
    have h2 : P.pairing.vertex⁻¹ y = x := by
      refine hrad _ _ ?_ ((hprev y).trans hxy.symm) ?_
      · change isApex n w (start n w (walkLabel n w d (P.index (P.pairing.vertex⁻¹ y)))) = true
        rw [walk_start_link_constant n w d c hc f P ((hprev y).trans hxy.symm)]
        exact hax
      · change walkLabel n w d (P.index (P.pairing.vertex⁻¹ y)) = walkLabel n w d (P.index x)
        rw [walk_corner_incoming n w d c hc f P hm hy,hx,frozenCorner_label,hp]
        cases o <;> rfl
    exact False.elim (walk_triangle_inverse_no_two n w d c hc f P hm hred hx
      (by rw [h1]; exact hy) (by rw [h1,h2]))

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkMultiplicity
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

noncomputable instance instFintypeRawPositionSide (p : RawPosition n w d) : Fintype (RawPositionSide n w d c hc f P select p) :=
  Fintype.ofFinite _

noncomputable instance instFintypeKindFace (k : WalkKind n w d) : Fintype (KindFace n w d c hc f P select k) :=
  Fintype.ofFinite _

lemma raw_fan_index {x : P.Dart} {g : FanTriangle n w}
    (hr : isLetter n w (walkLabel n w d (P.index x)) = true)
    (hp : rawPosition n w d (P.index x) = .inr (.inl g)) :
    ∃ o, P.index x = .inr ⟨.inl g,o,(1 : Fin 3)⟩ := by
  cases he : P.index x with
  | inl s => rw [he] at hp; cases hp
  | inr s =>
    rcases s with ⟨k,o,i⟩
    rcases k with h | (q | q)
    · rw [he] at hp hr
      have hg : h = g := Sum.inl.inj (Sum.inr.inj hp)
      have hi := fan_letter_index n w d h o i hr
      subst h; subst i
      exact ⟨o,rfl⟩
    · rw [he] at hp; cases hp
    · rw [he] at hp; cases hp

lemma raw_fan_previous (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = .inr ⟨.inl g,o,(1 : Fin 3)⟩) :
    P.index (P.pairing.face⁻¹ x) = frozenCorner n w d g o := by
  rw [P.frozen_previous_index (walkFrozenTarget n w d c hc f) hm (by rw [hx]; rfl),hx]
  cases o <;> rfl

lemma raw_fan_previous_start (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (g : FanTriangle n w) (x : RawPositionSide n w d c hc f P select (.inr (.inl g))) :
    start n w (walkLabel n w d (P.index (P.pairing.face⁻¹ x.val))) = .inr g.1 := by
  obtain ⟨o,ho⟩ := raw_fan_index n w d c hc f P x.property.2.1 x.property.2.2
  rw [raw_fan_previous n w d c hc f P hm ho,frozenCorner_start]

/-- A fan field's selected copies inject into the ACTUAL represented apex
instances, not into an assumed nominal collection of links. -/
lemma raw_fan_multiplicity_le (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (g : FanTriangle n w) :
    Fintype.card (RawPositionSide n w d c hc f P select (.inr (.inl g))) ≤
      Fintype.card (ApexInstance n w d c hc f P select g.1) := by
  let j : RawPositionSide n w d c hc f P select (.inr (.inl g)) →
      ApexInstance n w d c hc f P select g.1 := fun x =>
    apexInstanceAt n w d c hc f P select g.1 (P.pairing.face⁻¹ x.val)
      (by rw [P.faceClass_previous]; exact x.property.1)
      (raw_fan_previous_start n w d c hc f P select hm g x)
  apply Fintype.card_le_of_injective j
  intro x y h
  obtain ⟨o,ho⟩ := raw_fan_index n w d c hc f P x.property.2.1 x.property.2.2
  obtain ⟨p,hp⟩ := raw_fan_index n w d c hc f P y.property.2.1 y.property.2.2
  have hv : P.vertexClass (P.pairing.face⁻¹ x.val) = P.vertexClass (P.pairing.face⁻¹ y.val) :=
    congrArg Subtype.val h
  have hh := fan_field_once n w d c hc f P hm hred hrad
    (raw_fan_previous n w d c hc f P hm ho) (raw_fan_previous n w d c hc f P hm hp)
    (P.vertexClass_eq.mp hv)
  exact Subtype.ext ((P.pairing.face⁻¹).injective hh)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualWeights
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma top_count_le_slot (a : Top n w) (i : Fin 7) :
    Fintype.card (KindFace n w d c hc f P select (.inl a)) ≤
      (indexedFanData n w d c hc f P select (slot n w a i) hs hm hred hrad).weight := by
  by_cases he : Nonempty (KindFace n w d c hc f P select (.inl a))
  · let F := Classical.choice he
    let ao : SelectedOccurrence n w d c hc f P select := ⟨a,F.val,F.property⟩
    let b := slot n w a i
    let D := indexedFanData n w d c hc f P select b hs hm hred hrad
    let g : KindFace n w d c hc f P select (.inl a) →
        {H : SelectedTop n w d c hc f P select b // D.occurrence H = ao} := fun H =>
      ⟨⟨H.val,H.property.1,a,H.property.2,i,rfl⟩,by
        apply Subtype.ext
        exact Sum.inl.inj ((selectedOccurrence_kind n w d c hc f P select b _).symm.trans H.property.2)⟩
    have hcount : Fintype.card (KindFace n w d c hc f P select (.inl a)) ≤ D.multiplicity ao := by
      apply Fintype.card_le_of_injective g
      intro H K h
      exact Subtype.ext (congrArg (fun z => z.val.val) h)
    exact hcount.trans ((Finset.le_sup (f := D.multiplicity) (Finset.mem_univ ao)).trans (le_max_right _ _))
  · have hi : IsEmpty (KindFace n w d c hc f P select (.inl a)) := not_nonempty_iff.mp he
    have hzero : Fintype.card (KindFace n w d c hc f P select (.inl a)) = 0 := Fintype.card_eq_zero_iff.mpr hi
    rw [hzero]
    exact Nat.zero_le _

lemma indexed_weight_congr {b b' : Fan n w} (h : b = b') :
    (indexedFanData n w d c hc f P select b hs hm hred hrad).weight =
    (indexedFanData n w d c hc f P select b' hs hm hred hrad).weight := by
  cases h
  rfl

/-- Weights are the literal selected-face multiplicities and maximum of actual
apex count / same-top slot multiplicity. No contact capacity is a field. -/
def actualWeights : (occurrenceShape n w).Weights (v := Fintype.card (Six n d)) where
  top := fun a => Fintype.card (KindFace n w d c hc f P select (.inl ((enumTop n w).symm a)))
  fan := fun b => (indexedFanData n w d c hc f P select ((enumFan n w).symm b) hs hm hred hrad).weight
  square := fun q => Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inl ((enumSquare n w).symm q)))))
  six := fun q => Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inr ((enumSix n d).symm q)))))
  slot := by
    intro a i
    change _ ≤ (indexedFanData n w d c hc f P select
      ((enumFan n w).symm ((enumFan n w) (slot n w ((enumTop n w).symm a) i))) hs hm hred hrad).weight
    rw [indexed_weight_congr n w d c hc f P select hs hm hred hrad ((enumFan n w).symm_apply_apply _)]
    exact top_count_le_slot n w d c hc f P select hs hm hred hrad _ i

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualContact
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

def contactLeft (e : ActualContact n w d c hc f P select) := rawToPosition n w d (rawPosition n w d (P.index e.val))
def contactRight (e : ActualContact n w d c hc f P select) := rawToPosition n w d (rawPosition n w d (P.index (P.pairing.edge e.val)))

variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_boundary_contacts_eq :
    Fintype.card (ActualRawBoundary n w d c hc f P select) +
      2 * Fintype.card (ActualContact n w d c hc f P select) =
    Fintype.card (ActualRawSide n w d c hc f P select) :=
  P.pairing.boundary_contacts_eq (selectedDart n w d c hc f P select) (rawDart n w d c hc f P)
    (rawDart_pair n w d c hc f P)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FragmentSlots
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

noncomputable instance instFintypeSelectedTopFace : Fintype (SelectedTopFace n w d c hc f P select) := Fintype.ofFinite _

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FrozenSideExists
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma frozen_side_exists (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x : P.Dart} {k : FrozenCell n w d} {o : Bool} {i : Fin ((frozenBoundary n w d).size k)}
    (hx : P.index x = .inr ⟨k,o,i⟩) (j : Fin ((frozenBoundary n w d).size k)) :
    ∃ y, P.pairing.face.SameCycle x y ∧ P.index y = .inr ⟨k,o,j⟩ := by
  let x' : P.FrozenDart := ⟨x,by rw [hx]; rfl⟩
  have hh : (walkFrozenTarget n w d c hc f).next.SameCycle (P.index x) (.inr ⟨k,o,j⟩) := by
    rw [hx]
    apply semiconj_perm_sameCycle (f := (frozenBoundary n w d).next)
      (j := Sum.inr) (fun s => rfl) ((frozenBoundary n w d).side_sameCycle k o i j)
  obtain ⟨y,hy,he⟩ := hm.orbit_surjective x' hh
  exact ⟨y.val,sameCycle_subtypePerm.mp hy,he⟩

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRadialBoundary
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

lemma walk_apex_previous (x : P.Dart) :
    walkApex n w d c hc f P (P.pairing.vertex⁻¹ x) = walkApex n w d c hc f P x := by
  exact congrArg (isApex n w) (walk_start_link_constant n w d c hc f P
    (sameCycle_inv.mp (SameCycle.rfl.apply_left)))

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTriangleTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev triangleCorner (p : AllTriangleIndex n w d c hc f P select hs hm hred hrad) := p.2.val.2.val

def triangleRawDart (p : AllTriangleIndex n w d c hc f P select hs hm hred hrad) : P.Dart :=
  P.pairing.face (triangleCorner n w d c hc f P select hs hm hred hrad p)

lemma triangle_selected (p : AllTriangleIndex n w d c hc f P select hs hm hred hrad) :
    select (P.faceClass (triangleCorner n w d c hc f P select hs hm hred hrad p)) = true := by
  by_contra hh
  have hx := (mark_absent n w d c hc f P select p.1 p.2.val.1 p.2.val.2).mpr hh
  have ht := p.2.property
  change fragmentMark n w d c hc f P select p.1 p.2.val.1 p.2.val.2 = .triangle at ht
  rw [hx] at ht
  cases ht

lemma triangle_raw_index (p : AllTriangleIndex n w d c hc f P select hs hm hred hrad) :
    ∃ g o, P.index (triangleRawDart n w d c hc f P select hs hm hred hrad p) =
      .inr ⟨.inl g,o,(1 : Fin 3)⟩ := by
  obtain ⟨g,o,hx⟩ := mark_triangle_corner n w d c hc f P select p.1 p.2.val.1 p.2.val.2 p.2.property
  have he := hm.commute ⟨p.2.val.2.val,by rw [hx]; rfl⟩
  change P.index (P.pairing.face p.2.val.2.val) =
    (walkFrozenTarget n w d c hc f).next (P.index p.2.val.2.val) at he
  refine ⟨g,o,?_⟩
  change P.index (P.pairing.face p.2.val.2.val) = _
  rw [he,hx]
  cases o <;> rfl

lemma triangleRawDart_injective : Function.Injective
    (triangleRawDart n w d c hc f P select hs hm hred hrad) := by
  intro p q h
  have hh := apexCorner_injective n w d c hc f P select
    (a₁ := ⟨p.1,p.2.val⟩) (a₂ := ⟨q.1,q.2.val⟩) (P.pairing.face.injective h)
  rcases p with ⟨b,x⟩; rcases q with ⟨a,y⟩
  have hb : b = a := congrArg Sigma.fst hh
  subst a
  have hv : x.val = y.val := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hv))

noncomputable instance instFintypeSelectedTriangleFace : Fintype (SelectedTriangleFace n w d c hc f P select) := Fintype.ofFinite _

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualFaceCounts
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

lemma count_faces_in {K : Type*} [Fintype K] (g : K → WalkKind n w d) (hg : Function.Injective g) :
    (∑ k, Fintype.card (KindFace n w d c hc f P select (g k))) =
      Fintype.card {F : P.Face // select F = true ∧ ∃ k, P.faceKind F = g k} := by
  rw [← Fintype.card_sigma]
  let v : (Σ k, KindFace n w d c hc f P select (g k)) →
      {F : P.Face // select F = true ∧ ∃ k, P.faceKind F = g k} :=
    fun p => ⟨p.2.val,p.2.property.1,p.1,p.2.property.2⟩
  apply Fintype.card_congr (Equiv.ofBijective v ?_)
  constructor
  · rintro ⟨k,F⟩ ⟨l,G⟩ h
    have hFG : F.val = G.val := congrArg Subtype.val h
    have hkl : k = l := hg (F.property.2.symm.trans ((congrArg P.faceKind hFG).trans G.property.2))
    subst l
    have hh : F = G := Subtype.ext hFG
    subst G
    rfl
  · rintro ⟨F,hF,k,hk⟩
    exact ⟨⟨k,F,hF,hk⟩,rfl⟩

def actualTopCount : ℕ := Fintype.card (SelectedTopFace n w d c hc f P select)
def actualTriangleCount : ℕ := Fintype.card (SelectedTriangleFace n w d c hc f P select)
def actualSquareCount : ℕ := ∑ q : Square n w, Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inl q))))
def actualSixCount : ℕ := ∑ q : Six n d, Fintype.card (KindFace n w d c hc f P select (.inr (.inr (.inr q))))
def actualArea : ℕ := Fintype.card (SelectedFace n w d c hc f P select)

lemma sum_top_count : (∑ a : Top n w, Fintype.card (KindFace n w d c hc f P select (.inl a))) =
    actualTopCount n w d c hc f P select := by
  simpa only [actualTopCount,← Nat.card_eq_fintype_card] using
    count_faces_in n w d c hc f P select Sum.inl Sum.inl_injective
lemma sum_triangle_count : (∑ g : FanTriangle n w, Fintype.card (KindFace n w d c hc f P select (.inr (.inl g)))) =
    actualTriangleCount n w d c hc f P select := by
  simpa only [actualTriangleCount,Function.comp_apply,← Nat.card_eq_fintype_card] using
    count_faces_in n w d c hc f P select (Sum.inr ∘ Sum.inl) (Sum.inr_injective.comp Sum.inl_injective)

lemma actual_area_eq : actualArea n w d c hc f P select = actualTopCount n w d c hc f P select +
    actualTriangleCount n w d c hc f P select + actualSquareCount n w d c hc f P select +
    actualSixCount n w d c hc f P select := by
  have hh := count_faces_in n w d c hc f P select id Function.injective_id
  have he : Fintype.card {F : P.Face // select F = true ∧ ∃ k, P.faceKind F = id k} =
      actualArea n w d c hc f P select := by
    apply Fintype.card_congr
    exact { toFun := fun F => ⟨F.val,F.property.1⟩
            invFun := fun F => ⟨F.val,F.property,P.faceKind F.val,rfl⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [he] at hh
  simp only [id_eq,Fintype.sum_sum_type] at hh
  rw [sum_top_count n w d c hc f P select,sum_triangle_count n w d c hc f P select] at hh
  unfold actualSquareCount actualSixCount
  omega

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FrozenFaceSide
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))

include hm in
lemma frozenFaceSide_exists (k : FrozenCell n w d)
    (F : KindFace n w d c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    ∃ y, P.faceClass y = F.val ∧ ∃ o, P.index y = .inr ⟨k,o,j⟩ := by
  have ho := P.faceClass_out F.val
  have hk : walkKind n w d (P.index F.val.out) = .inr k := by
    change P.faceKind (P.faceClass F.val.out) = _
    rw [ho]
    exact F.property.2
  obtain ⟨o,i,hi⟩ : ∃ (o : Bool) (i : Fin ((frozenBoundary n w d).size k)),
      P.index F.val.out = .inr ⟨k,o,i⟩ := by
    cases h : P.index F.val.out with
    | inl a => rw [h] at hk; cases hk
    | inr s =>
      rcases s with ⟨k',o,i⟩
      have hh : k' = k := Sum.inr.inj (by simpa only [h,walkKind] using hk)
      subst k'
      exact ⟨o,i,rfl⟩
  obtain ⟨y,hy,he⟩ := frozen_side_exists n w d c hc f P hm hi j
  exact ⟨y,((P.faceClass_eq).mpr hy).symm.trans ho,o,he⟩

def frozenFaceDart (k : FrozenCell n w d)
    (F : KindFace n w d c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) : P.Dart :=
  (frozenFaceSide_exists n w d c hc f P select hm k F j).choose
lemma frozenFaceDart_face (k : FrozenCell n w d)
    (F : KindFace n w d c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    P.faceClass (frozenFaceDart n w d c hc f P select hm k F j) = F.val :=
  (frozenFaceSide_exists n w d c hc f P select hm k F j).choose_spec.1
lemma frozenFaceDart_index (k : FrozenCell n w d)
    (F : KindFace n w d c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    ∃ o, P.index (frozenFaceDart n w d c hc f P select hm k F j) = .inr ⟨k,o,j⟩ :=
  (frozenFaceSide_exists n w d c hc f P select hm k F j).choose_spec.2
lemma frozenFaceDart_selected (k : FrozenCell n w d)
    (F : KindFace n w d c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    select (P.faceClass (frozenFaceDart n w d c hc f P select hm k F j)) = true := by
  rw [frozenFaceDart_face]
  exact F.property.1

lemma frozenFaceDart_injective (k : FrozenCell n w d) : Function.Injective
    (fun p : KindFace n w d c hc f P select (.inr k) × Fin ((frozenBoundary n w d).size k) =>
      frozenFaceDart n w d c hc f P select hm k p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    have hf := congrArg P.faceClass h
    simpa only [frozenFaceDart_face] using hf
  · obtain ⟨o,ho⟩ := frozenFaceDart_index n w d c hc f P select hm k p.1 p.2
    obtain ⟨o',ho'⟩ := frozenFaceDart_index n w d c hc f P select hm k q.1 q.2
    have hh := congrArg P.index h
    rw [ho,ho'] at hh
    have he : (o, p.2) = (o', q.2) := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj hh)).2
    exact congrArg (fun t : Bool × Fin ((frozenBoundary n w d).size k) => t.2) he

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroExceptional
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

universe u
variable (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma exceptional_next (hs : P.Simple) (hb : P.NoBigon)
    {x : P.Dart} {a : Top n w} (hx : P.index x = .inl (a,exceptionalMacro)) :
    P.index (P.pairing.face x) = .inl (a,looseMacro) := by
  obtain ⟨e,he⟩ := same_top_face n w d c hc f P hx (SameCycle.rfl.apply_right)
  have hh := P.closed x
  change walkFront n w d (P.index (P.pairing.face x)) = walkBack n w d (P.index x) at hh
  rw [he,hx] at hh
  have hf : e.fst = MacroGraph.exceptional := congrArg Prod.snd (Sum.inl.inj hh)
  have hn : e ≠ exceptionalMacro.symm := by
    intro hh
    apply P.free_sameface_not_opposite hs hb (x := x) (y := P.pairing.face x) (by rw [hx]; rfl)
      (SameCycle.rfl.apply_right)
    change P.index (P.pairing.face x) = walkOpposite n w d (P.index x)
    rw [he,hx,hh]; rfl
  rw [he,exceptional_successor e hf hn]

lemma exceptional_previous (hs : P.Simple) (hb : P.NoBigon)
    {x : P.Dart} {a : Top n w} (hx : P.index x = .inl (a,exceptionalMacro.symm)) :
    P.index (P.pairing.face⁻¹ x) = .inl (a,looseMacro.symm) := by
  have hxy : P.pairing.face.SameCycle x (P.pairing.face⁻¹ x) :=
    sameCycle_inv.mp (SameCycle.rfl.apply_right)
  obtain ⟨e,he⟩ := same_top_face n w d c hc f P hx hxy
  have hh := P.closed (P.pairing.face⁻¹ x)
  rw [Perm.inv_def,apply_symm_apply] at hh
  change walkFront n w d (P.index x) = walkBack n w d (P.index (P.pairing.face⁻¹ x)) at hh
  rw [he,hx] at hh
  have hf : e.snd = MacroGraph.exceptional := (congrArg Prod.snd (Sum.inl.inj hh)).symm
  have hn : e ≠ exceptionalMacro := by
    intro hh
    apply P.free_sameface_not_opposite hs hb (x := x) (y := P.pairing.face⁻¹ x) (by rw [hx]; rfl) hxy
    change P.index (P.pairing.face⁻¹ x) = walkOpposite n w d (P.index x)
    rw [he,hx,hh]; rfl
  rw [he,exceptional_predecessor e hf hn]

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkPayment
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

lemma top_exceptional_incoming {x : P.Dart} {a : Top n w} {e : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (a,e))
    (ha : isApex n w (start n w (walkLabel n w d (P.index x))) = true)
    (hl : dartPart n w (walkLabel n w d (P.index (P.pairing.vertex⁻¹ x))) = false) :
    P.index (P.pairing.face⁻¹ x) = .inl (a,exceptionalMacro.symm) := by
  obtain ⟨k,hk⟩ := same_top_face n w d c hc f P hx
    (sameCycle_inv.mp (SameCycle.rfl.apply_right))
  have hei : walkLabel n w d (P.index (P.pairing.vertex⁻¹ x)) =
      rev n w (walkLabel n w d (P.index (P.pairing.face⁻¹ x))) := by
    rw [walk_vertex_inverse]
    exact P.paired _
  have hax : isApex n w (start n w (walkLabel n w d (P.index (P.pairing.vertex⁻¹ x)))) = true :=
    (walk_apex_previous n w d c hc f P x).trans ha
  rw [hei,hk] at hl hax
  have hlab : macroStep n w a k.symm.adj = rev n w (macroStep n w a k.adj) :=
    macroStep_reverse n w a k.adj
  have he : k.symm = exceptionalMacro := macro_exceptional_port n w a k.symm
    (by rw [hlab]; exact hax)
    (by rw [hlab]; exact hl)
  have hh : k = exceptionalMacro.symm := congrArg SimpleGraph.Dart.symm he
  rw [hk,hh]

variable (hs : P.Simple) (hb : P.NoBigon)
  (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev paymentCorner (p : AllPaymentIndex n w d c hc f P select hs hm hred hrad) := p.2.val.1.2.val
abbrev paymentBool (p : AllPaymentIndex n w d c hc f P select hs hm hred hrad) := p.2.val.2

def paymentRawDart (p : AllPaymentIndex n w d c hc f P select hs hm hred hrad) : P.Dart :=
  if paymentBool n w d c hc f P select hs hm hred hrad p then
    P.pairing.face (paymentCorner n w d c hc f P select hs hm hred hrad p)
  else P.pairing.face⁻¹ (P.pairing.face⁻¹ (paymentCorner n w d c hc f P select hs hm hred hrad p))

include hb in
lemma payment_raw_index (p : AllPaymentIndex n w d c hc f P select hs hm hred hrad) :
    ∃ a, P.index (paymentRawDart n w d c hc f P select hs hm hred hrad p) =
      .inl (a,if paymentBool n w d c hc f P select hs hm hred hrad p then looseMacro else looseMacro.symm) := by
  obtain ⟨F,hF⟩ := p.2.property.1
  obtain ⟨e,he⟩ := mark_top_index n w d c hc f P select p.1 p.2.val.1.1 p.2.val.1.2 F hF
  let a := selectedOccurrence n w d c hc f P select p.1 F
  refine ⟨a,?_⟩
  have ha := instance_apex n w d c hc f P select p.1 p.2.val.1.1 p.2.val.1.2
  have hl := p.2.property.2
  cases ho : paymentBool n w d c hc f P select hs hm hred hrad p
  · have hl' : dartPart n w (walkLabel n w d (P.index (P.pairing.vertex⁻¹ p.2.val.1.2.val))) = false := by
      simpa only [indexedFanData,ho,Bool.false_eq_true,↓reduceIte,P.linkNext_val] using hl
    have hx := top_exceptional_incoming n w d c hc f P he ha hl'
    simpa only [paymentRawDart,ho,Bool.false_eq_true,↓reduceIte] using
      exceptional_previous n w d c hc f P hs hb hx
  · have hl' : dartPart n w (macroStep n w a e.adj) = false := by
      simpa only [indexedFanData,ho,↓reduceIte,he,walkLabel] using hl
    have hh : e = exceptionalMacro := macro_exceptional_port n w a e
      (by simpa only [he,walkLabel] using ha) hl'
    have hx : P.index p.2.val.1.2.val = .inl (a,exceptionalMacro) := by rw [he,hh]
    simpa only [paymentRawDart,ho,↓reduceIte] using
      exceptional_next n w d c hc f P hs hb hx

lemma payment_selected (p : AllPaymentIndex n w d c hc f P select hs hm hred hrad) :
    select (P.faceClass (paymentRawDart n w d c hc f P select hs hm hred hrad p)) = true := by
  obtain ⟨F,hF⟩ := p.2.property.1
  have hf := mark_top_face n w d c hc f P select p.1 p.2.val.1.1 p.2.val.1.2 F hF
  have hx : select (P.faceClass p.2.val.1.2.val) = true := by rw [← hf]; exact F.property.1
  unfold paymentRawDart
  split_ifs <;> simpa only [P.faceClass_apply,P.faceClass_previous] using hx

lemma payment_param_injective : Function.Injective (fun p : AllPaymentIndex n w d c hc f P select hs hm hred hrad =>
    (paymentCorner n w d c hc f P select hs hm hred hrad p,paymentBool n w d c hc f P select hs hm hred hrad p)) := by
  rintro ⟨b,⟨⟨⟨z,x⟩,o⟩,hp⟩⟩ ⟨a,⟨⟨⟨y,k⟩,q⟩,hq⟩⟩ hh
  obtain ⟨hx,ho⟩ := Prod.mk.inj hh
  have hv := apexCorner_injective n w d c hc f P select (a₁ := ⟨b,z,x⟩) (a₂ := ⟨a,y,k⟩) hx
  have hb : b = a := congrArg Sigma.fst hv
  subst a
  have hz : z = y := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj_iff.mp hv).2)
  subst y
  have hk : x = k := Subtype.ext hx
  subst k
  change o = q at ho
  subst q
  rfl

include hb in
lemma paymentRawDart_injective : Function.Injective
    (paymentRawDart n w d c hc f P select hs hm hred hrad) := by
  intro p q he
  apply payment_param_injective n w d c hc f P select hs hm hred hrad
  have ho : paymentBool n w d c hc f P select hs hm hred hrad p =
      paymentBool n w d c hc f P select hs hm hred hrad q := by
    obtain ⟨a,ha⟩ := payment_raw_index n w d c hc f P select hs hb hm hred hrad p
    obtain ⟨b,hb⟩ := payment_raw_index n w d c hc f P select hs hb hm hred hrad q
    have hh := congrArg P.index he
    rw [ha,hb] at hh
    have hh' := congrArg (fun t : Top n w × MacroGraph.graph.Dart => t.2.fst) (Sum.inl.inj hh)
    cases hp : paymentBool n w d c hc f P select hs hm hred hrad p <;>
      cases hq : paymentBool n w d c hc f P select hs hm hred hrad q <;>
      simp only [hp,hq,Bool.false_eq_true,↓reduceIte] at hh' ⊢
    all_goals cases hh'
  refine Prod.ext ?_ ho
  unfold paymentRawDart at he
  rw [ho] at he
  split_ifs at he
  · exact P.pairing.face.injective he
  · exact (P.pairing.face⁻¹).injective ((P.pairing.face⁻¹).injective he)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualRawCount
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

def decorationRawDart (p : DecorationSideIndex n w d c hc f P select) : P.Dart :=
  frozenFaceDart n w d c hc f P select hm (.inr p.1) p.2.1 p.2.2

lemma decorationRawDart_injective : Function.Injective
    (decorationRawDart n w d c hc f P select hm) := by
  rintro ⟨k,F,j⟩ ⟨k',F',j'⟩ hh
  obtain ⟨o,ho⟩ := frozenFaceDart_index n w d c hc f P select hm (.inr k) F j
  obtain ⟨o',ho'⟩ := frozenFaceDart_index n w d c hc f P select hm (.inr k') F' j'
  have he := congrArg P.index hh
  change P.index (frozenFaceDart n w d c hc f P select hm (.inr k) F j) =
    P.index (frozenFaceDart n w d c hc f P select hm (.inr k') F' j') at he
  rw [ho,ho'] at he
  have hk : k = k' := Sum.inr.inj (congrArg Sigma.fst (Sum.inr.inj he))
  subst k'
  exact Sigma.ext rfl (heq_of_eq (frozenFaceDart_injective n w d c hc f P select hm (.inr k) hh))

lemma decorationRawDart_raw (p : DecorationSideIndex n w d c hc f P select) :
    rawDart n w d c hc f P (decorationRawDart n w d c hc f P select hm p) := by
  obtain ⟨o,ho⟩ := frozenFaceDart_index n w d c hc f P select hm (.inr p.1) p.2.1 p.2.2
  unfold rawDart decorationRawDart
  rw [ho]
  rcases p with ⟨k,F,j⟩
  rcases k with k | k
  · change Fin 4 at j
    fin_cases j <;> cases o <;> rfl
  · cases o <;> rfl

def accountDart : RawAccountIndex n w d c hc f P select hs hm hred hrad → P.Dart :=
  Sum.elim (paymentRawDart n w d c hc f P select hs hm hred hrad)
    (Sum.elim (triangleRawDart n w d c hc f P select hs hm hred hrad)
      (decorationRawDart n w d c hc f P select hm))

lemma accountDart_injective (hb : P.NoBigon) : Function.Injective
    (accountDart n w d c hc f P select hs hm hred hrad) := by
  intro p q hh
  have hi := congrArg P.index hh
  rcases p with p | (p | p) <;> rcases q with q | (q | q)
  all_goals dsimp only [accountDart,Sum.elim,decorationRawDart] at hh hi
  · exact congrArg Sum.inl (paymentRawDart_injective n w d c hc f P select hs hb hm hred hrad hh)
  · obtain ⟨a,ha⟩ := payment_raw_index n w d c hc f P select hs hb hm hred hrad p
    obtain ⟨g,o,hg⟩ := triangle_raw_index n w d c hc f P select hs hm hred hrad q
    change P.index (paymentRawDart _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [ha,hg] at hi; cases hi
  · obtain ⟨a,ha⟩ := payment_raw_index n w d c hc f P select hs hb hm hred hrad p
    obtain ⟨o,hg⟩ := frozenFaceDart_index n w d c hc f P select hm (.inr q.1) q.2.1 q.2.2
    change P.index (paymentRawDart _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [ha,hg] at hi; cases hi
  · obtain ⟨a,ha⟩ := payment_raw_index n w d c hc f P select hs hb hm hred hrad q
    obtain ⟨g,o,hg⟩ := triangle_raw_index n w d c hc f P select hs hm hred hrad p
    change P.index (triangleRawDart _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [ha,hg] at hi; cases hi
  · exact congrArg (Sum.inr ∘ Sum.inl) (triangleRawDart_injective n w d c hc f P select hs hm hred hrad hh)
  · obtain ⟨g,o,hg⟩ := triangle_raw_index n w d c hc f P select hs hm hred hrad p
    obtain ⟨o',hk⟩ := frozenFaceDart_index n w d c hc f P select hm (.inr q.1) q.2.1 q.2.2
    change P.index (triangleRawDart _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [hg,hk] at hi
    have he := congrArg Sigma.fst (Sum.inr.inj hi)
    cases he
  · obtain ⟨a,ha⟩ := payment_raw_index n w d c hc f P select hs hb hm hred hrad q
    obtain ⟨o,hg⟩ := frozenFaceDart_index n w d c hc f P select hm (.inr p.1) p.2.1 p.2.2
    change P.index (frozenFaceDart _ _ _ _ _ _ _ _ _ _ p.2.1 p.2.2) = _ at hi
    rw [ha,hg] at hi; cases hi
  · obtain ⟨g,o,hg⟩ := triangle_raw_index n w d c hc f P select hs hm hred hrad q
    obtain ⟨o',hk⟩ := frozenFaceDart_index n w d c hc f P select hm (.inr p.1) p.2.1 p.2.2
    change P.index (frozenFaceDart _ _ _ _ _ _ _ _ _ _ p.2.1 p.2.2) = _ at hi
    rw [hg,hk] at hi
    have he := congrArg Sigma.fst (Sum.inr.inj hi)
    cases he
  · exact congrArg (Sum.inr ∘ Sum.inr) (decorationRawDart_injective n w d c hc f P select hm hh)

lemma accountDart_selected (p : RawAccountIndex n w d c hc f P select hs hm hred hrad) :
    selectedDart n w d c hc f P select (accountDart n w d c hc f P select hs hm hred hrad p) := by
  rcases p with p | (p | p)
  · exact payment_selected n w d c hc f P select hs hm hred hrad p
  · change select (P.faceClass (P.pairing.face _)) = true
    rw [P.faceClass_apply]
    exact triangle_selected n w d c hc f P select hs hm hred hrad p
  · exact frozenFaceDart_selected n w d c hc f P select hm (.inr p.1) p.2.1 p.2.2

lemma accountDart_raw (hb : P.NoBigon)
    (p : RawAccountIndex n w d c hc f P select hs hm hred hrad) :
    rawDart n w d c hc f P (accountDart n w d c hc f P select hs hm hred hrad p) := by
  rcases p with p | (p | p)
  · obtain ⟨a,ha⟩ := payment_raw_index n w d c hc f P select hs hb hm hred hrad p
    change isLetter n w (walkLabel n w d (P.index (paymentRawDart _ _ _ _ _ _ _ _ _ _ _ _ p))) = true
    rw [ha]
    cases ho : paymentBool n w d c hc f P select hs hm hred hrad p <;> rfl
  · obtain ⟨g,o,hg⟩ := triangle_raw_index n w d c hc f P select hs hm hred hrad p
    change isLetter n w (walkLabel n w d (P.index (triangleRawDart _ _ _ _ _ _ _ _ _ _ _ _ p))) = true
    rw [hg]
    cases o <;> rfl
  · exact decorationRawDart_raw n w d c hc f P select hm p

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTopTurns
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
noncomputable instance instFintypeTopTurnDart : Fintype (TopTurnDart n w d c hc f P select) := Fintype.ofFinite _

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualFragment
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction
open IncidenceTemplate.Occurrences.Shape

namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

def actualFanWeight := ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).weight
def actualPayments := ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).payments
def actualPartialCount := ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).partialCount
def actualBoundary := Fintype.card (ActualRawBoundary n w d c hc f P select) +
  Fintype.card (RadialBoundarySide n w d c hc f P select)

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualPartition
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
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

lemma actual_boundary_card (select : P.Face → Bool) :
    actualBoundary n w d c hc f P select =
      Fintype.card {x : P.Dart // select (P.faceClass x) = true ∧
        select (P.faceClass (P.pairing.edge x)) ≠ true} := by
  rw [actualBoundary,← Fintype.card_sum]
  let g : ActualRawBoundary n w d c hc f P select ⊕ RadialBoundarySide n w d c hc f P select →
      {x : P.Dart // select (P.faceClass x) = true ∧ select (P.faceClass (P.pairing.edge x)) ≠ true} :=
    Sum.elim (fun x => ⟨x.val,x.property.2⟩) (fun x => ⟨x.val,x.property.2⟩)
  apply Fintype.card_congr (Equiv.ofBijective g ?_)
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subtype.ext he)
    · have hx := x.property.1
      have hy := y.property.1
      change x.val = y.val at he
      dsimp only [rawDart] at hx
      dsimp only [walkRadial] at hy
      rw [he,hy] at hx
      cases hx
    · have hx := x.property.1
      have hy := y.property.1
      change x.val = y.val at he
      dsimp only [rawDart] at hy
      dsimp only [walkRadial] at hx
      rw [he,hy] at hx
      cases hx
    · exact congrArg Sum.inr (Subtype.ext he)
  · rintro ⟨x,hx,he⟩
    cases hr : isLetter n w (walkLabel n w d (P.index x)) with
    | false => exact ⟨.inr ⟨x,hr,hx,he⟩,rfl⟩
    | true => exact ⟨.inl ⟨x,hr,hx,he⟩,rfl⟩

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureDual
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
namespace PictureMap
variable {D : Type*} (P : PictureMap D)

variable [Fintype D]

lemma dual_components : P.dual.components = P.components := by
  apply le_antisymm
  · apply P.dual.components_le
    · intro x
      exact P.vertex_le_components (SameCycle.rfl.apply_right)
    · intro x
      exact P.edge_le_components (SameCycle.rfl.apply_right)
  · apply P.components_le
    · intro x
      apply P.dual.vertex_le_components
      rw [P.dual_vertex]
      exact SameCycle.rfl.apply_right
    · intro x
      exact P.dual.edge_le_components (SameCycle.rfl.apply_right)

variable [DecidableEq D]

lemma dual_genusZero (h : P.GenusZero) : P.dual.GenusZero := by
  change P.dual.euler = 2 * (Nat.card (Quotient P.dual.components) : ℤ)
  rw [P.dual_euler,P.dual_components]
  exact h

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PlanarEdgeOrdering
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

/-- Equality in the Euler potential propagates to every initial segment.
It therefore rules out a hidden handle in every sub-pairing, not only in the
fully glued surface. -/
lemma potential_prefix_eq {p : Perm D} {s : Setoid D}
    (hp : SameCycle.setoid p ≤ s) (l r : List (D × D))
    (he : cycles (p * swaps (l ++ r)) - 2 * (Nat.card (Quotient (joins s (l ++ r))) : ℤ) =
      cycles p - 2 * (Nat.card (Quotient s) : ℤ) + (l ++ r).length) :
    cycles (p * swaps l) - 2 * (Nat.card (Quotient (joins s l)) : ℤ) =
      cycles p - 2 * (Nat.card (Quotient s) : ℤ) + l.length := by
  have h₁ := potential_list hp l
  have h₂ := potential_list (sameCycle_joins hp l) r
  rw [swaps_append,joins_append,← mul_assoc,List.length_append,Nat.cast_add] at he
  omega

namespace PictureMap
variable (M : PictureMap D)

lemma paired_potential_eq (hG : M.GenusZero) (l : List (D × D))
    (hl : swaps l = M.edge) (hn : 2 * l.length = Fintype.card D)
    (hpairs : ∀ ab ∈ l, M.edge ab.1 = ab.2) :
    cycles (M.vertex * swaps l) -
      2 * (Nat.card (Quotient (joins (SameCycle.setoid M.vertex) l)) : ℤ) =
      cycles M.vertex - 2 * (Nat.card (Quotient (SameCycle.setoid M.vertex)) : ℤ) + l.length := by
  rw [M.paired_joins l hl hpairs,hl]
  have hv : M.vertex * M.edge = M.face := by rw [vertex,mul_assoc,M.edge_sq,mul_one]
  rw [hv,← cycles_eq_card_classes]
  have he : M.euler = cycles M.vertex + cycles M.face - l.length := by
    rw [euler]
    omega
  change M.euler = _ at hG
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PlanarSubpairing
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
variable (M : PictureMap D) (q : Perm D)
variable (hsub : ∀ x, q x = x ∨ q x = M.edge x)
include hsub

/-- Literal edge-subgraph planarity with retained vertex slots. Fixed points
of q are unpaired stubs, so support/2 counts ONLY remaining edges. This
Euler equation is proved for EVERY chosen subset of actual edges, and is the
subgraph input needed in a recursive planar separator construction. -/
theorem subpairing_euler (hG : M.GenusZero) :
    cycles M.vertex + cycles (M.vertex * q) - (q.support.card : ℤ) / 2 =
      2 * (Nat.card (Quotient (SameCycle.setoid M.vertex ⊔ SameCycle.setoid q)) : ℤ) := by
  obtain ⟨l,hl,hn,hpairs⟩ := involution_pairs q (M.subpairing_sq q hsub)
  let r := q * M.edge
  have hrsub := M.complement_subpairing q hsub
  obtain ⟨t,ht,htn,htpairs⟩ := involution_pairs r (M.subpairing_sq r hrsub)
  have hsupp : q.support.card + r.support.card = Fintype.card D := by
    rw [show r.support = Finset.univ \ q.support from M.complement_support q hsub]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
    have hh := Finset.card_le_card (Finset.subset_univ q.support)
    rw [Finset.card_univ] at hh
    omega
  have hprod : swaps (l ++ t) = M.edge := by
    rw [swaps_append,show swaps l = q from hl,show swaps t = r from ht]
    change q * (q * M.edge) = M.edge
    rw [← mul_assoc,M.subpairing_sq q hsub,one_mul]
  have hlen : 2 * (l ++ t).length = Fintype.card D := by
    rw [List.length_append]; omega
  have hact : ∀ ab ∈ l ++ t, M.edge ab.1 = ab.2 := by
    intro ab hab
    rcases List.mem_append.mp hab with hab | hab
    · obtain ⟨hne,he⟩ := hpairs ab hab
      rcases hsub ab.1 with hx | hx
      · exact False.elim (hne (hx.symm.trans he))
      · exact hx.symm.trans he
    · obtain ⟨hne,he⟩ := htpairs ab hab
      rcases hrsub ab.1 with hx | hx
      · exact False.elim (hne (hx.symm.trans he))
      · exact hx.symm.trans he
  have hfull := M.paired_potential_eq hG (l ++ t) hprod hlen hact
  have hp := potential_prefix_eq (p := M.vertex) (s := SameCycle.setoid M.vertex) le_rfl l t hfull
  rw [joins_pairing M.vertex q l hl (fun ab hab => (hpairs ab hab).2),
    show swaps l = q from hl,← cycles_eq_card_classes] at hp
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PairingTreeCotree
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
variable (M : PictureMap D)

omit [DecidableEq D] in
lemma subpairing_components_le (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x) :
    SameCycle.setoid M.vertex ⊔ SameCycle.setoid q ≤ M.components := by
  apply sup_le M.vertex_le_components
  apply sameCycle_le_of_apply
  intro x
  rcases hq x with hx | hx
  · rw [hx]
  · rw [hx]; exact M.edge_le_components SameCycle.rfl.apply_right

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SubpairingGraph
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
variable (M : PictureMap D) (q : Perm D) (hq : q*q = 1)

lemma subpairing_edge_card_le (l : List (D × D)) (hl : swaps l = q)
    (hpairs : ∀ ab ∈ l, q ab.1 = ab.2) :
    Nat.card (M.subpairingGraph q hq).edgeSet ≤ l.length := by
  classical
  let f : D × D → Sym2 M.GraphVertex := fun ab => s(M.vertexClass ab.1,M.vertexClass ab.2)
  have hsub : (M.subpairingGraph q hq).edgeFinset ⊆ l.toFinset.image f := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf v w =>
      have hadj : (M.subpairingGraph q hq).Adj v w := by simpa using he
      obtain ⟨hne,x,rfl,rfl⟩ := hadj
      have hqx : q x ≠ x := fun hh => hne (congrArg M.vertexClass hh.symm)
      have hex : ∃ ab ∈ l, x = ab.1 ∨ x = ab.2 := by
        by_contra h
        push Not at h
        exact hqx (hl ▸ swaps_fix_of_outside l x h)
      obtain ⟨ab,hab,ha | hb⟩ := hex
      · apply Finset.mem_image.mpr
        refine ⟨ab,List.mem_toFinset.mpr hab,?_⟩
        dsimp only [f]
        rw [ha,hpairs ab hab]
      · apply Finset.mem_image.mpr
        refine ⟨ab,List.mem_toFinset.mpr hab,?_⟩
        have hh : q ab.2 = ab.1 := by
          rw [← hpairs ab hab]
          exact congrArg (fun p : Perm D => p ab.1) hq
        dsimp only [f]
        rw [hb,hh,Sym2.eq_swap]
  calc
    Nat.card (M.subpairingGraph q hq).edgeSet = (M.subpairingGraph q hq).edgeFinset.card := by
      rw [Nat.card_eq_fintype_card,SimpleGraph.edgeFinset_card]
    _ ≤ (l.toFinset.image f).card := Finset.card_le_card hsub
    _ ≤ l.toFinset.card := Finset.card_image_le
    _ ≤ l.length := List.toFinset_card_le l

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SubpairingTree
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
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]

namespace PictureMap
variable (M : PictureMap D)

/-- A literal one-boundary spanning subpairing of a connected genus-zero
map is a tree on the actual rotation vertices. This also rules out retained
loops and duplicate edges: the edge-count bound and connectivity force equality. -/
theorem subpairing_isTree (hG : M.GenusZero) (q : Perm D)
    (hsub : ∀ x, q x = x ∨ q x = M.edge x)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1) :
    (M.subpairingGraph q (M.subpairing_sq q hsub)).IsTree := by
  have hconn := M.subpairing_connected q (M.subpairing_sq q hsub) hspan
  obtain ⟨l,hl,hn,hpairs⟩ := involution_pairs q (M.subpairing_sq q hsub)
  have hedge := M.subpairing_edge_card_le q (M.subpairing_sq q hsub) l hl
    (fun ab hab => (hpairs ab hab).2)
  have heuler := M.subpairing_euler q hsub hG
  rw [hspan,card_quotient_top_one,hboundary,cycles_eq_card_classes] at heuler
  change (Nat.card M.GraphVertex : ℤ) + 1 - (q.support.card : ℤ)/2 = 2 at heuler
  have hnZ : (q.support.card : ℤ) = 2*(l.length : ℤ) := by exact_mod_cast hn.symm
  have hdiv : (q.support.card : ℤ)/2 = (l.length : ℤ) := by
    rw [hnZ]
    omega
  rw [hdiv] at heuler
  have hv : Nat.card M.GraphVertex = l.length+1 := by
    have hh : (Nat.card M.GraphVertex : ℤ) = (l.length : ℤ)+1 := by linarith
    exact_mod_cast hh
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn,?_⟩
  have hlo := hconn.card_vert_le_card_edgeSet_add_one
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SubpairingCopies
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D) (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)

abbrev RetainedContact := M.Contact (fun _ => True) (fun x => q x ≠ x)

def retainedContactEdge (a : M.RetainedContact q) : Sym2 M.GraphVertex :=
  s(M.vertexClass a.val, M.vertexClass (M.edge a.val))

include hq in
omit [DecidableEq D] [Fintype D] [Nonempty D] in
lemma retained_raw_edge (x : D) : q (M.edge x) ≠ M.edge x ↔ q x ≠ x := by
  rw [M.subpairing_edge q hq]
  exact not_congr M.edge.injective.eq_iff

include hq in
omit [Nonempty D] in
lemma retained_contact_card : q.support.card = 2 * Fintype.card (M.RetainedContact q) := by
  have hh := M.internal_card (fun _ => True) (fun x => q x ≠ x)
    (M.retained_raw_edge q hq)
  have he : q.support.card = Fintype.card {x : D // q x ≠ x} := by
    simpa only [mem_support] using (Fintype.card_coe q.support).symm
  rw [he]
  simpa only [← Nat.card_eq_fintype_card,InternalSide,and_true] using hh

include hq in
omit [DecidableEq D] [Nonempty D] in
lemma retained_contact_covers (x : D) (hx : q x ≠ x) :
    ∃ a : M.RetainedContact q, a.val = x ∨ a.val = M.edge x := by
  by_cases hn : M.number x < M.number (M.edge x)
  · exact ⟨⟨x,hx,trivial,trivial,hn⟩,Or.inl rfl⟩
  · refine ⟨⟨M.edge x,(M.retained_raw_edge q hq x).mpr hx,trivial,trivial,?_⟩,Or.inr rfl⟩
    rw [M.edge_edge]
    exact lt_of_le_of_ne (le_of_not_gt hn) (M.number_ne x).symm

omit [Nonempty D] in
lemma subpairing_edges_subset_retained :
    (M.subpairingGraph q (M.subpairing_sq q hq)).edgeFinset ⊆
      Finset.univ.image (M.retainedContactEdge q) := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf v w =>
    have hadj : (M.subpairingGraph q (M.subpairing_sq q hq)).Adj v w := by simpa using he
    obtain ⟨hne,x,rfl,rfl⟩ := hadj
    have hx : q x ≠ x := fun hh => hne (congrArg M.vertexClass hh.symm)
    have hxe : q x = M.edge x := (hq x).resolve_left hx
    obtain ⟨a,ha | ha⟩ := M.retained_contact_covers q hq x hx
    · exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,by simp [retainedContactEdge,ha,hxe]⟩
    · exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,by
        simp only [retainedContactEdge,ha,M.edge_edge,hxe]
        exact Sym2.eq_swap⟩

/-- A one-boundary spanning subpairing has exactly one retained contact for
each edge of its underlying tree. Euler and connectivity rule out BOTH
loops and parallel copies, rather than silently forgetting them. -/
theorem tree_retained_contacts_bijective (hG : M.GenusZero)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1) :
    Function.Injective (M.retainedContactEdge q) ∧
    (M.subpairingGraph q (M.subpairing_sq q hq)).edgeFinset =
      Finset.univ.image (M.retainedContactEdge q) := by
  classical
  have heuler := M.subpairing_euler q hq hG
  rw [hspan,card_quotient_top_one,hboundary,cycles_eq_card_classes] at heuler
  change (Nat.card M.GraphVertex : ℤ) + 1 - (q.support.card : ℤ)/2 = 2 at heuler
  have hc := M.retained_contact_card q hq
  have hcZ : (q.support.card : ℤ) = 2*(Fintype.card (M.RetainedContact q) : ℤ) := by
    exact_mod_cast hc
  rw [hcZ] at heuler
  have hv : Fintype.card M.GraphVertex = Fintype.card (M.RetainedContact q) + 1 := by
    rw [Nat.card_eq_fintype_card] at heuler
    omega
  have hconn := M.subpairing_connected q (M.subpairing_sq q hq) hspan
  have hlo := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card] at hlo
  have hs := M.subpairing_edges_subset_retained q hq
  have hle := Finset.card_le_card hs
  have hi := Finset.card_image_le (s := Finset.univ) (f := M.retainedContactEdge q)
  rw [Finset.card_univ] at hi
  have heq : (M.subpairingGraph q (M.subpairing_sq q hq)).edgeFinset = Finset.univ.image (M.retainedContactEdge q) := by
    apply Finset.eq_of_subset_of_card_le hs
    omega
  refine ⟨?_,heq⟩
  have hic : (Finset.univ.image (M.retainedContactEdge q)).card =
      (Finset.univ : Finset (M.RetainedContact q)).card := by
    rw [Finset.card_univ]
    rw [← heq]
    omega
  have hinj := Finset.card_image_iff.mp hic
  exact fun a b hab => hinj (Finset.mem_univ a) (Finset.mem_univ b) hab

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SubpairingDarts
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D) (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)
variable (hG : M.GenusZero) (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
variable (hboundary : cycles (M.vertex*q) = 1)

omit [DecidableEq D] [Nonempty D] in
lemma retained_contact_edge_of_covers (x : D) (a : M.RetainedContact q)
    (ha : a.val = x ∨ a.val = M.edge x) :
    M.retainedContactEdge q a = s(M.vertexClass x,M.vertexClass (M.edge x)) := by
  rcases ha with ha | ha
  · simp only [retainedContactEdge,ha]
  · simp only [retainedContactEdge,ha,M.edge_edge]
    exact Sym2.eq_swap

include hq hG hspan hboundary in
lemma tree_retained_loopless (x : D) (hx : q x ≠ x) :
    M.vertexClass x ≠ M.vertexClass (M.edge x) := by
  obtain ⟨a,ha⟩ := M.retained_contact_covers q hq x hx
  have he := (M.tree_retained_contacts_bijective q hq hG hspan hboundary).2
  have hm : s(M.vertexClass x,M.vertexClass (M.edge x)) ∈
      (M.subpairingGraph q (M.subpairing_sq q hq)).edgeFinset := by
    rw [he]
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,M.retained_contact_edge_of_covers q x a ha⟩
  have hadj : (M.subpairingGraph q (M.subpairing_sq q hq)).Adj
      (M.vertexClass x) (M.vertexClass (M.edge x)) := by simpa using hm
  exact hadj.1

include hq hG hspan hboundary in
/-- Exact oriented dart-copy uniqueness in the primal spanning tree. It is
stronger than acyclicity of the simplified graph: parallel copies cannot
be discarded before using a boundary-conservation argument. -/
theorem tree_retained_dart_unique (x y : D) (hx : q x ≠ x) (hy : q y ≠ y)
    (hv : M.vertexClass x = M.vertexClass y)
    (hw : M.vertexClass (M.edge x) = M.vertexClass (M.edge y)) : x = y := by
  obtain ⟨a,ha⟩ := M.retained_contact_covers q hq x hx
  obtain ⟨b,hb⟩ := M.retained_contact_covers q hq y hy
  have hab : a = b := (M.tree_retained_contacts_bijective q hq hG hspan hboundary).1 (by
    rw [M.retained_contact_edge_of_covers q x a ha,
      M.retained_contact_edge_of_covers q y b hb,hv,hw])
  have habv := congrArg Subtype.val hab
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact ha.symm.trans (habv.trans hb)
  · have he : x = M.edge y := ha.symm.trans (habv.trans hb)
    exact False.elim (M.tree_retained_loopless q hq hG hspan hboundary y hy
      (hv.symm.trans (congrArg M.vertexClass he)))
  · have he : M.edge x = y := ha.symm.trans (habv.trans hb)
    exact False.elim (M.tree_retained_loopless q hq hG hspan hboundary x hx
      (hv.trans (congrArg M.vertexClass he).symm))
  · exact M.edge.injective (ha.symm.trans (habv.trans hb))

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureBoundaryHull
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D) (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)

/-- The topological separation mechanism behind the tree--cotree separator.
A face coloring can change across tree edges only inside the root-path hull
of its non-tree changes. Proof: literal vertex-rotation conservation gives
two distinct boundary Dart copies at every unprotected boundary vertex;
exact tree-copy uniqueness turns them into two distinct tree neighbors,
contradicting a furthest-vertex argument. -/
theorem face_color_boundary_in_hull (hG : M.GenusZero)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1)
    (root : M.GraphVertex) (S : Set M.GraphVertex)
    (hS : RootClosed (M.subpairingGraph q (M.subpairing_sq q hq)) root S)
    {C : Type*} (color : D → C) (hface : ∀ x, color (M.face x) = color x)
    (hother : ∀ x, q x = x → color (M.edge x) ≠ color x → M.vertexClass x ∈ S) :
    ∀ x, color (M.edge x) ≠ color x → M.vertexClass x ∈ S := by
  let G := M.subpairingGraph q (M.subpairing_sq q hq)
  have hT : G.IsTree := M.subpairing_isTree hG q hq hspan hboundary
  let B : M.GraphVertex → Prop := fun v => ∃ x, M.vertexClass x = v ∧ color (M.edge x) ≠ color x
  have hb : ∀ v, B v → v ∈ S := by
    apply tree_boundary_in_hull hT root S hS B
    intro v hv hvS
    obtain ⟨x,hxv,hxc⟩ := hv
    have hxq : q x ≠ x := fun he => hvS (hxv ▸ hother x he hxc)
    obtain ⟨y,hyx,hyv,hyc⟩ := M.boundary_dart_not_unique color hface x hxc
    have hyq : q y ≠ y := fun he => hvS ((hyv.trans hxv) ▸ hother y he hyc)
    have hxe : q x = M.edge x := (hq x).resolve_left hxq
    have hye : q y = M.edge y := (hq y).resolve_left hyq
    refine ⟨M.vertexClass (M.edge x),M.vertexClass (M.edge y),?_,?_,?_,?_,?_⟩
    · intro he
      exact hyx (M.tree_retained_dart_unique q hq hG hspan hboundary x y hxq hyq hyv.symm he).symm
    · refine ⟨?_,x,hxv,?_⟩
      · rw [← hxv]
        exact M.tree_retained_loopless q hq hG hspan hboundary x hxq
      · rw [hxe]
    · refine ⟨?_,y,hyv.trans hxv,?_⟩
      · rw [← hxv,← hyv]
        exact M.tree_retained_loopless q hq hG hspan hboundary y hyq
      · rw [hye]
    · refine ⟨M.edge x,rfl,?_⟩
      rw [M.edge_edge]
      exact hxc.symm
    · refine ⟨M.edge y,rfl,?_⟩
      rw [M.edge_edge]
      exact hyc.symm
  intro x hx
  exact hb _ ⟨x,rfl,hx⟩

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureCotreeColor
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D)

omit [DecidableEq D] [Fintype D] in
lemma vertexClass_vertex (x : D) : M.vertexClass (M.vertex x) = M.vertexClass x :=
  (M.vertexClass_eq_iff _ _).mpr SameCycle.rfl.apply_left

omit [DecidableEq D] [Fintype D] in
lemma dual_vertexClass_face (x : D) : M.dual.vertexClass (M.face x) = M.dual.vertexClass x := by
  apply (M.dual.vertexClass_eq_iff _ _).mpr
  rw [M.dual_vertex]
  exact SameCycle.rfl.apply_left

/-- The actual corners of a selected dual vertex (primal face). -/
def faceCorners (f : M.dual.GraphVertex) : Finset M.GraphVertex :=
  (Finset.univ.filter (fun x => M.dual.vertexClass x = f)).image M.vertexClass

omit [DecidableEq D] in
lemma corner_mem (f : M.dual.GraphVertex) (x : D) (hx : M.dual.vertexClass x = f) :
    M.vertexClass x ∈ M.faceCorners f :=
  Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩

omit [DecidableEq D] in
lemma corner_opposite_mem (f : M.dual.GraphVertex) (x : D)
    (hx : M.dual.vertexClass (M.edge x) = f) : M.vertexClass x ∈ M.faceCorners f := by
  have hh := M.corner_mem f (M.face (M.edge x)) ((M.dual_vertexClass_face _).trans hx)
  change M.vertexClass (M.vertex x) ∈ M.faceCorners f at hh
  rwa [M.vertexClass_vertex] at hh

variable (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)

def cotreeGraph : SimpleGraph M.dual.GraphVertex :=
  M.dual.subpairingGraph (q*M.edge) (M.subpairing_sq (q*M.edge) (M.complement_subpairing q hq))

/-- Colors are ACTUAL components of the complementary dual graph after
isolating one specified face; the face itself receives its isolated color. -/
def cotreeColor (f : M.dual.GraphVertex) (x : D) :
    ((M.cotreeGraph q hq).deleteIncidenceSet f).ConnectedComponent :=
  ((M.cotreeGraph q hq).deleteIncidenceSet f).connectedComponentMk (M.dual.vertexClass x)

omit [DecidableEq D] [Fintype D] in
lemma cotreeColor_face (f : M.dual.GraphVertex) (x : D) :
    M.cotreeColor q hq f (M.face x) = M.cotreeColor q hq f x := by
  unfold cotreeColor
  rw [M.dual_vertexClass_face]

omit [DecidableEq D] [Fintype D] in
lemma cotreeColor_fixed_edge (f : M.dual.GraphVertex) (x : D)
    (hx : q x = x) (hf : M.dual.vertexClass x ≠ f)
    (he : M.dual.vertexClass (M.edge x) ≠ f) :
    M.cotreeColor q hq f (M.edge x) = M.cotreeColor q hq f x := by
  by_cases hc : M.dual.vertexClass x = M.dual.vertexClass (M.edge x)
  · exact congrArg (((M.cotreeGraph q hq).deleteIncidenceSet f).connectedComponentMk) hc.symm
  · apply SimpleGraph.ConnectedComponent.sound
    apply SimpleGraph.Adj.reachable
    apply SimpleGraph.deleteIncidenceSet_adj.mpr
    refine ⟨?_,he,hf⟩
    apply SimpleGraph.Adj.symm
    refine ⟨hc,x,rfl,?_⟩
    rw [mul_apply,M.subpairing_edge q hq,hx]

variable [Nonempty D]

/-- The rooted paths to the corners of a dual-tree vertex contain every
edge across which the associated deleted-dual-component color changes.
Unlike an abstract Jordan-curve assumption, this follows from the exact
rotation permutations, genus-zero Euler formula and tree copy counts. -/
theorem cotree_color_boundary_in_path_hull (hG : M.GenusZero)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1) (root : M.GraphVertex)
    (f : M.dual.GraphVertex) :
    ∀ x, M.cotreeColor q hq f (M.edge x) ≠ M.cotreeColor q hq f x →
      M.vertexClass x ∈ treePathHull (M.subpairingGraph q (M.subpairing_sq q hq))
        (M.subpairing_isTree hG q hq hspan hboundary) root (M.faceCorners f) := by
  apply M.face_color_boundary_in_hull q hq hG hspan hboundary root _
    (treePathHull_rootClosed _ _ root _) (M.cotreeColor q hq f) (M.cotreeColor_face q hq f)
  intro x hx hc
  by_cases hf : M.dual.vertexClass x = f
  · exact subset_treePathHull _ _ _ _ (M.corner_mem f x hf)
  · by_cases he : M.dual.vertexClass (M.edge x) = f
    · exact subset_treePathHull _ _ _ _ (M.corner_opposite_mem f x he)
    · exact (hc (M.cotreeColor_fixed_edge q hq f x hx hf he)).elim

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureCotreeTree
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D) (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)

include hq in
omit [DecidableEq D] [Fintype D] [Nonempty D] in
lemma complement_boundary_eq : M.face * (q*M.edge) = M.vertex*q := by
  have hcomm : q*M.edge = M.edge*q := by
    ext x; exact M.subpairing_edge q hq x
  have hface : M.face = M.vertex*M.edge := by
    rw [vertex,mul_assoc,M.edge_sq,mul_one]
  rw [hface]
  calc
    _ = M.vertex * (M.edge*q) * M.edge := by simp only [mul_assoc]
    _ = M.vertex * (q*M.edge) * M.edge := by rw [← hcomm]
    _ = (M.vertex*q) * (M.edge*M.edge) := by simp only [mul_assoc]
    _ = M.vertex*q := by rw [M.edge_sq,mul_one]

/-- The complement of ANY literal spanning-tree subpairing is a dual tree,
not just the particular Kruskal forest supplied by tree_cotree. This is
needed when the primal tree is chosen for a radius bound. -/
theorem cotree_isTree (hG : M.GenusZero)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1) : (M.cotreeGraph q hq).IsTree := by
  have hconn : M.components = ⊤ := top_unique (hspan ▸ M.subpairing_components_le q hq)
  let r := q*M.edge
  have hr := M.complement_subpairing q hq
  have hrb : cycles (M.face*r) = 1 := by
    rw [show M.face*r = M.vertex*q from M.complement_boundary_eq q hq,hboundary]
  have hqE := M.subpairing_euler q hq hG
  rw [hspan,card_quotient_top_one,hboundary] at hqE
  have hrE := M.dual.subpairing_euler r hr (M.dual_genusZero hG)
  rw [M.dual_vertex,hrb] at hrE
  have hE := hG
  change cycles M.vertex + cycles M.face - (Fintype.card D : ℤ)/2 =
    2*(Nat.card (Quotient M.components) : ℤ) at hE
  rw [hconn,card_quotient_top_one] at hE
  have hsupp : q.support.card + r.support.card = Fintype.card D := by
    rw [show r.support = Finset.univ \ q.support from M.complement_support q hq,
      Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
    have hh := Finset.card_le_card (Finset.subset_univ q.support)
    rw [Finset.card_univ] at hh
    omega
  obtain ⟨l,_,hl,_⟩ := involution_pairs q (M.subpairing_sq q hq)
  obtain ⟨t,_,ht,_⟩ := involution_pairs r (M.subpairing_sq r hr)
  have hc : Nat.card (Quotient (SameCycle.setoid M.face ⊔ SameCycle.setoid r)) = 1 := by omega
  have hds : SameCycle.setoid M.face ⊔ SameCycle.setoid r = ⊤ :=
    setoid_eq_of_card_eq le_top (hc.trans card_quotient_top_one.symm)
  apply M.dual.subpairing_isTree (M.dual_genusZero hG) r hr
  · simpa only [M.dual_vertex] using hds
  · simpa only [M.dual_vertex] using hrb

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureOutsideColor
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D)

def vertexRepresentative (v : M.GraphVertex) : D := Quotient.out v
omit [DecidableEq D] [Fintype D] in
lemma vertexClass_representative (v : M.GraphVertex) :
    M.vertexClass (M.vertexRepresentative v) = v := Quotient.out_eq v

def vertexColor {C : Type*} (color : D → C) (v : M.GraphVertex) : C :=
  color (M.vertexRepresentative v)

omit [DecidableEq D]

/-- Outside a set containing every edge-color boundary, incident face
colors agree around the ENTIRE literal vertex rotation orbit. -/
lemma color_eq_on_vertex_outside {C : Type*} (color : D → C)
    (hface : ∀ x, color (M.face x) = color x) (S : Set M.GraphVertex)
    (hboundary : ∀ x, color (M.edge x) ≠ color x → M.vertexClass x ∈ S)
    (x y : D) (hv : M.vertexClass x = M.vertexClass y) (hx : M.vertexClass x ∉ S) :
    color x = color y := by
  classical
  let f : D → Option C := fun z => if M.vertexClass z ∈ S then none else some (color z)
  have hf : ∀ z, f (M.vertex z) = f z := by
    intro z
    simp only [f,M.vertexClass_vertex]
    by_cases hz : M.vertexClass z ∈ S
    · rw [ite_eq_left hz,ite_eq_left hz]
    · rw [ite_eq_right hz,ite_eq_right hz]
      congr 1
      have he : color (M.edge z) = color z := by
        by_contra hh
        exact hz (hboundary z hh)
      exact (hface (M.edge z)).trans he
  have he : f x = f y := (sameCycle_le_of_apply (s := Setoid.ker f)
    (fun z => (hf z).symm)) ((M.vertexClass_eq_iff _ _).mp hv)
  have hy : M.vertexClass y ∉ S := hv ▸ hx
  simp only [f,ite_eq_right hx,ite_eq_right hy,Option.some.injEq] at he
  exact he

lemma vertexColor_eq_dart_outside {C : Type*} (color : D → C)
    (hface : ∀ x, color (M.face x) = color x) (S : Set M.GraphVertex)
    (hboundary : ∀ x, color (M.edge x) ≠ color x → M.vertexClass x ∈ S)
    (x : D) (hx : M.vertexClass x ∉ S) :
    M.vertexColor color (M.vertexClass x) = color x := by
  apply M.color_eq_on_vertex_outside color hface S hboundary
  · exact M.vertexClass_representative _
  · rwa [M.vertexClass_representative]

lemma vertexColor_adj_outside {C : Type*} (color : D → C)
    (hface : ∀ x, color (M.face x) = color x) (S : Set M.GraphVertex)
    (hboundary : ∀ x, color (M.edge x) ≠ color x → M.vertexClass x ∈ S)
    {v w : M.GraphVertex} (hadj : M.underlyingGraph.Adj v w) (hv : v ∉ S) (hw : w ∉ S) :
    M.vertexColor color v = M.vertexColor color w := by
  obtain ⟨hne,x,rfl,rfl⟩ := hadj
  rw [M.vertexColor_eq_dart_outside color hface S hboundary _ hv,
    M.vertexColor_eq_dart_outside color hface S hboundary _ hw]
  by_contra he
  exact hv (hboundary x (fun hh => he hh.symm))

/-- A connected set of primal vertices off the rooted separator carries
one deleted-dual-component color. This closes the actual separation bridge
from rotation-system boundaries to the underlying graph. -/
theorem vertexColor_connected_outside {C : Type*} (color : D → C)
    (hface : ∀ x, color (M.face x) = color x) (S : Set M.GraphVertex)
    (hboundary : ∀ x, color (M.edge x) ≠ color x → M.vertexClass x ∈ S)
    (U : Set M.GraphVertex) (hU : ∀ v ∈ U, v ∉ S)
    (hconn : (M.underlyingGraph.induce U).Preconnected) :
    ∀ v ∈ U, ∀ w ∈ U, M.vertexColor color v = M.vertexColor color w := by
  have hpath : ∀ {a b : U}, (M.underlyingGraph.induce U).Walk a b →
      M.vertexColor color a.val = M.vertexColor color b.val := by
    intro a b p
    induction p with
    | nil => rfl
    | @cons a b c h p ih =>
      exact (M.vertexColor_adj_outside color hface S hboundary h
        (hU a.val a.property) (hU b.val b.property)).trans ih
  intro v hv w hw
  obtain ⟨p⟩ := hconn ⟨v,hv⟩ ⟨w,hw⟩
  exact hpath p

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureFaceCorners
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D]
variable (M : PictureMap D)

lemma faceCorners_card_le_fiber (f : M.dual.GraphVertex) :
    (M.faceCorners f).card ≤ Nat.card {x : D // M.dual.vertexClass x = f} := by
  have hh := Finset.card_image_le (f := M.vertexClass)
    (s := Finset.univ.filter (fun x => M.dual.vertexClass x = f))
  change (M.faceCorners f).card ≤ _ at hh
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact hh

/-- A bound on the literal side-degree of each face bounds the number of
its distinct corner vertices, even for faces touching the same vertex
repeatedly or traversing both sides of a loop. -/
theorem faceCorners_card_le (k : ℕ)
    (hdegree : ∀ x : D, Fintype.card {y : D // M.face.SameCycle x y} ≤ k)
    (f : M.dual.GraphVertex) : (M.faceCorners f).card ≤ k := by
  have hh := M.faceCorners_card_le_fiber f
  let x := M.dual.vertexRepresentative f
  have hx : M.dual.vertexClass x = f := M.dual.vertexClass_representative f
  have he : Nat.card {y : D // M.dual.vertexClass y = f} =
      Nat.card {y : D // M.face.SameCycle x y} := by
    rw [← hx,Nat.card_congr (M.dual.vertex_fiber_equiv x),M.dual_vertex]
  rw [he,Nat.card_eq_fintype_card] at hh
  exact hh.trans (hdegree x)

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TreeSubpairingLift
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D)

/-- Every spanning tree of the actual underlying graph lifts to a genuine
one-boundary dart subpairing. Kruskal is applied ONLY to actual copies of
its own edges; connectedness then forces equality with the selected tree.
This permits a shortest-path tree, rather than an arbitrary-radius tree. -/
theorem lift_spanning_tree (T : SimpleGraph M.GraphVertex)
    (hle : T ≤ M.underlyingGraph) (hT : T.IsTree) :
    ∃ q : Perm D, ∃ hq : ∀ x, q x = x ∨ q x = M.edge x,
      SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤ ∧
      cycles (M.vertex*q) = 1 ∧
      M.subpairingGraph q (M.subpairing_sq q hq) = T := by
  let p := M.graphPairing T
  have hp := M.graphPairing_sub T
  have hpg := M.graphPairing_graph T hle
  have hspan := M.subpairing_span_of_connected p (M.subpairing_sq p hp)
    (hpg ▸ hT.connected)
  obtain ⟨l,hl,hn,hpairs⟩ := involution_pairs p (M.subpairing_sq p hp)
  let t := forestEdges (SameCycle.setoid M.vertex) l
  let q := swaps t
  have hmem : ∀ ab ∈ l, M.edge ab.1 = ab.2 := by
    intro ab hab
    rcases hp ab.1 with he | he
    · exact ((hpairs ab hab).1 (he.symm.trans (hpairs ab hab).2)).elim
    · exact he.symm.trans (hpairs ab hab).2
  have hq := M.swaps_subpairing t (fun ab hab => hmem ab ((forestEdges_sublist _ l).subset hab))
  have hjoin : joins (SameCycle.setoid M.vertex) l = ⊤ :=
    (joins_pairing M.vertex p l hl (fun ab hab => (hpairs ab hab).2)).trans hspan
  have hb : cycles (M.vertex*q) = 1 := by
    have hc := forestEdges_cycles M.vertex (SameCycle.setoid M.vertex) le_rfl l
    have hd := forestEdges_card (SameCycle.setoid M.vertex) l
    rw [hjoin,card_quotient_top_one,← cycles_eq_card_classes] at hd
    change cycles (M.vertex*q) = _ at hc
    omega
  have hqs : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤ := by
    have hs : SameCycle.setoid (M.vertex*q) = ⊤ := by
      apply setoid_eq_of_card_eq le_top
      rw [cycles_eq_card_classes] at hb
      have hc : Nat.card (Quotient (SameCycle.setoid (M.vertex*q))) = 1 := by exact_mod_cast hb
      exact hc.trans card_quotient_top_one.symm
    exact top_unique (hs ▸ sameCycle_mul_le (p := M.vertex) (q := q) le_sup_left le_sup_right)
  let Q := M.subpairingGraph q (M.subpairing_sq q hq)
  have hQT : Q ≤ T := by
    rintro v w ⟨hne,x,rfl,rfl⟩
    have hx : q x ≠ x := fun he => hne (congrArg M.vertexClass he.symm)
    have hqx : q x = M.edge x := (hq x).resolve_left hx
    rw [hqx]
    have hex : ∃ ab ∈ t, x = ab.1 ∨ x = ab.2 := by
      by_contra hh
      push Not at hh
      exact hx (swaps_fix_of_outside t x hh)
    obtain ⟨ab,hab,ha | ha⟩ := hex
    all_goals
      have habl := (forestEdges_sublist _ l).subset hab
      have hpab := (hpairs ab habl).2
      have ht : T.Adj (M.vertexClass ab.1) (M.vertexClass ab.2) := by
        rw [show p ab.1 = if T.Adj (M.vertexClass ab.1) (M.vertexClass (M.edge ab.1))
          then M.edge ab.1 else ab.1 from rfl] at hpab
        split_ifs at hpab with hadj
        · rwa [hpab] at hadj
        · exact ((hpairs ab habl).1 hpab).elim
    · simpa only [ha,hmem ab habl] using ht
    · have haedge : M.edge ab.2 = ab.1 := by rw [← hmem ab habl,M.edge_edge]
      simpa only [ha,haedge] using ht.symm
  have hQc : Q.Connected := M.subpairing_connected q (M.subpairing_sq q hq) hqs
  have hmin := SimpleGraph.isTree_iff_minimal_connected.mp hT
  have hEQ : Q = T := le_antisymm hQT (hmin.2 hQc hQT)
  exact ⟨q,hq,hqs,hb,hEQ⟩

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureBFSSeparator
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D)

/-- Radius-preserving literal dart-tree producer. The finite graph BFS
construction is lifted without forgetting actual parallel edge copies. -/
theorem bfs_subpairing (hc : M.underlyingGraph.Connected) (root : M.GraphVertex) :
    ∃ q : Perm D, ∃ hq : ∀ x, q x = x ∨ q x = M.edge x,
      SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤ ∧
      cycles (M.vertex*q) = 1 ∧
      ∀ v, (M.subpairingGraph q (M.subpairing_sq q hq)).dist root v =
        M.underlyingGraph.dist root v := by
  obtain ⟨T,hle,hT,hdepth⟩ := exists_bfs_tree M.underlyingGraph hc root
  obtain ⟨q,hq,hspan,hb,he⟩ := M.lift_spanning_tree T hle hT
  exact ⟨q,hq,hspan,hb,fun v => by rw [he]; exact hdepth v⟩

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureRootSeparator
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D) (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)

/-- A dual centroid gives a separator consisting of the actual root paths
to one face. No radius hypothesis is imposed; a later annulus argument
counts only the portion between two selected BFS levels. -/
theorem root_path_weighted_separator (hG : M.GenusZero)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1)
    (root : M.GraphVertex)
    (weight : M.GraphVertex → ℝ) (hw : ∀ v, 0 ≤ weight v) :
    ∃ f : M.dual.GraphVertex, ∀ U : Finset M.GraphVertex,
      Disjoint U (treePathHull _ (M.subpairing_isTree hG q hq hspan hboundary) root (M.faceCorners f)) →
      (M.underlyingGraph.induce (U : Set M.GraphVertex)).Preconnected →
      2 * ∑ v ∈ U, weight v ≤ ∑ v : M.GraphVertex, weight v := by
  classical
  let T := M.subpairingGraph q (M.subpairing_sq q hq)
  have hT : T.IsTree := M.subpairing_isTree hG q hq hspan hboundary
  let A : M.GraphVertex → M.dual.GraphVertex :=
    fun v => M.dual.vertexClass (M.vertexRepresentative v)
  let mass := pushMass A weight
  have hm : ∀ f, 0 ≤ mass f := pushMass_nonneg A weight hw
  obtain ⟨f,hf⟩ := weighted_tree_component_separator (M.cotreeGraph q hq)
    (M.cotree_isTree q hq hG hspan hboundary) mass hm
  let S := treePathHull T hT root (M.faceCorners f)
  refine ⟨f,?_⟩
  intro U hUS hconn
  have hout : ∀ v ∈ U, v ∉ (S : Set M.GraphVertex) := by
    intro v hv hs
    exact Finset.disjoint_left.mp hUS hv hs
  have hbound : ∀ x, M.cotreeColor q hq f (M.edge x) ≠ M.cotreeColor q hq f x →
      M.vertexClass x ∈ (S : Set M.GraphVertex) :=
    M.cotree_color_boundary_in_path_hull q hq hG hspan hboundary root f
  have hcolor := M.vertexColor_connected_outside (M.cotreeColor q hq f)
    (M.cotreeColor_face q hq f) (S : Set M.GraphVertex) hbound
    (U : Set M.GraphVertex) hout hconn
  by_cases hU : U.Nonempty
  · obtain ⟨v,hv⟩ := hU
    let H := (M.cotreeGraph q hq).deleteIncidenceSet f
    let C := H.connectedComponentMk (A v)
    have hAf : A v ≠ f := by
      intro he
      have hcorner := M.corner_mem f (M.vertexRepresentative v) he
      rw [M.vertexClass_representative] at hcorner
      exact hout v hv (subset_treePathHull T hT root (M.faceCorners f) hcorner)
    have hC : C ≠ H.connectedComponentMk f := by
      intro he
      exact hAf ((deleteIncidence_center_component_iff (M.cotreeGraph q hq) f (A v)).mp he)
    have hUC : ∀ w ∈ U, A w ∈ C.supp.toFinset := by
      intro w hwU
      rw [Set.mem_toFinset]
      exact hcolor w hwU v hv
    calc
      2 * ∑ v ∈ U, weight v ≤ 2 * ∑ g ∈ C.supp.toFinset, mass g :=
        mul_le_mul_of_nonneg_left (mass_le_pushMass A weight hw U C.supp.toFinset hUC) (by norm_num)
      _ ≤ ∑ g : M.dual.GraphVertex, mass g := hf C hC
      _ = ∑ v : M.GraphVertex, weight v := pushMass_total A weight
  · rw [Finset.not_nonempty_iff_eq_empty.mp hU]
    simp only [Finset.sum_empty,mul_zero]
    exact Finset.sum_nonneg (fun v _ => hw v)

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureSqrtSeparator
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D)

/-- A sqrt-cardinality separator of EVERY specified vertex carrier in a
connected literal genus-zero map. Unlike the radius precursor, this has no
tree, diameter, radius, or separator assumption. -/
theorem sqrt_component_separator (hG : M.GenusZero) (hc : M.underlyingGraph.Connected)
    (k : ℕ) (hdegree : ∀ x : D, Fintype.card {y : D // M.face.SameCycle x y} ≤ k)
    (U : Finset M.GraphVertex) :
    ∃ S : Finset M.GraphVertex, S ⊆ U ∧ S.card ≤ (3*k+2)*Nat.sqrt U.card ∧
      ∀ W : Finset M.GraphVertex, W ⊆ U → Disjoint W S →
        (M.underlyingGraph.induce (W : Set M.GraphVertex)).Preconnected →
        2*W.card ≤ U.card := by
  classical
  let root : M.GraphVertex := M.vertexClass (Classical.choice inferInstance)
  obtain ⟨q,hq,hspan,hb,hd⟩ := M.bfs_subpairing hc root
  let T := M.subpairingGraph q (M.subpairing_sq q hq)
  have hT : T.IsTree := M.subpairing_isTree hG q hq hspan hb
  let weight : M.GraphVertex → ℝ := fun v => if v ∈ U then 1 else 0
  have hw : ∀ v, 0 ≤ weight v := by intro v; dsimp [weight]; split_ifs <;> norm_num
  obtain ⟨f,hf⟩ := M.root_path_weighted_separator q hq hG hspan hb root weight hw
  let B := treePathHull T hT root (M.faceCorners f)
  apply sqrt_separator_of_banded_hull M.underlyingGraph U B (M.underlyingGraph.dist root) k
    (graph_dist_int_adj M.underlyingGraph root)
  · intro L H
    have he : ∀ v, M.underlyingGraph.dist root v = T.dist root v := fun v => (hd v).symm
    simp only [he]
    exact (treePathHull_intBand_card_le T hT root (M.faceCorners f) L H).trans
      (Nat.mul_le_mul_right _ (M.faceCorners_card_le k (fun dart => by
        simpa only [← Nat.card_eq_fintype_card] using hdegree dart) f))
  · intro W hWU hWB hconn
    have hh := hf W hWB hconn
    have htotal : ∑ v : M.GraphVertex, weight v = (U.card : ℝ) := by
      simp [weight]
    have hpart : ∑ v ∈ W, weight v = (W.card : ℝ) := by
      calc
        _ = ∑ v ∈ W, (1 : ℝ) := Finset.sum_congr rfl (fun vertex hvertex => ite_eq_left (hWU hvertex))
        _ = _ := by simp
    rw [htotal,hpart] at hh
    exact_mod_cast hh

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureTriangulation
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
variable (M : PictureMap D)

def starIndex : StarDart D → D := Sum.elim id (Sum.elim id id)

lemma star_face_to_left (x : StarDart D) :
    M.triangulation.face.SameCycle x (.inl (starIndex x)) := by
  rcases x with x | (x | x)
  · exact SameCycle.rfl
  · exact (SameCycle.rfl (x := Sum.inl x)).apply_left
  · exact (SameCycle.rfl (x := Sum.inr (Sum.inr x))).apply_right

lemma triangulation_face_cycle (x y : StarDart D) :
    M.triangulation.face.SameCycle x y ↔ starIndex x = starIndex y := by
  constructor
  · intro h
    apply sameCycle_one.mp (semiconj_perm_sameCycle
      (t := (1 : Perm D)) (j := starIndex) ?_ h)
    rintro (z | (z | z)) <;> rfl
  · intro h
    exact (M.star_face_to_left x).trans (by rw [h]; exact (M.star_face_to_left y).symm)

variable [DecidableEq D] [Fintype D]

lemma triangulation_face_cycles : cycles M.triangulation.face = (Fintype.card D : ℤ) := by
  rw [cycles_eq_card_classes,card_quotient_of_classifier _ starIndex M.triangulation_face_cycle ?_]
  · rw [Nat.card_eq_fintype_card]
  · intro x; exact ⟨.inl x,rfl⟩

/-- All new faces have exactly three sides, including when the old map had
loops, multiple edges, or monogons. -/
lemma triangulation_face_degree (x : StarDart D) :
    Fintype.card {y : StarDart D // M.triangulation.face.SameCycle x y} = 3 := by
  rw [Fintype.card_of_subtype
    ({.inl (starIndex x),.inr (.inl (starIndex x)),.inr (.inr (starIndex x))} : Finset (StarDart D))
    (by
      rintro (y | (y | y)) <;> rw [M.triangulation_face_cycle] <;>
        simp [starIndex,eq_comm])]
  simp

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureTriangulationEuler
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
variable (M : PictureMap D)

omit [DecidableEq D] in
lemma star_vertex_lift : SameCycle.setoid M.vertex ≤
    Setoid.comap Sum.inl (SameCycle.setoid M.triangulation.vertex) := by
  apply sameCycle_le_of_apply
  intro x
  have h : M.triangulation.vertex.SameCycle (.inl x)
      (M.triangulation.vertex (M.triangulation.vertex (.inl x))) :=
    SameCycle.rfl.apply_right.apply_right
  rw [M.triangulation_vertex_left,M.triangulation_vertex_middle] at h
  exact h

omit [DecidableEq D] [Fintype D] in
lemma star_center_lift {x y : D} (h : M.face.SameCycle x y) :
    M.triangulation.vertex.SameCycle (.inr (.inr x)) (.inr (.inr y)) :=
  semiconj_perm_sameCycle (f := M.face⁻¹) (t := M.triangulation.vertex)
    (j := fun x => Sum.inr (Sum.inr x)) (fun _ => rfl) h.inv

/-- The new vertices are exactly the old vertices plus the separate centers
of the old faces. This retains all original vertex identifications. -/
def starVertexClass : StarDart D → M.GraphVertex ⊕ Quotient (SameCycle.setoid M.face)
  | .inl x => .inl (M.vertexClass x)
  | .inr (.inl x) => .inl (M.vertexClass (M.face x))
  | .inr (.inr x) => .inr (Quotient.mk _ x)

omit [DecidableEq D] [Fintype D] in
lemma starVertexClass_step (z : StarDart D) :
    M.starVertexClass (M.triangulation.vertex z) = M.starVertexClass z := by
  rcases z with z | (z | z)
  · change Sum.inl (M.vertexClass (M.vertex z)) = Sum.inl (M.vertexClass z)
    exact congrArg Sum.inl (Quotient.sound SameCycle.rfl.apply_left)
  · rfl
  · change Sum.inr (Quotient.mk (SameCycle.setoid M.face) (M.face⁻¹ z)) =
      Sum.inr (Quotient.mk (SameCycle.setoid M.face) z)
    exact congrArg Sum.inr (Quotient.sound SameCycle.rfl.symm_apply_left)

omit [DecidableEq D] in
lemma star_vertex_cycle (x y : StarDart D) :
    M.triangulation.vertex.SameCycle x y ↔ M.starVertexClass x = M.starVertexClass y := by
  constructor
  · intro h
    exact sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (M.GraphVertex ⊕ Quotient (SameCycle.setoid M.face))))
      (j := M.starVertexClass) M.starVertexClass_step h)
  · rcases x with x | (x | x) <;> rcases y with y | (y | y)
    · intro h; exact M.star_vertex_lift (Quotient.exact (Sum.inl.inj h))
    · intro h
      have hh := M.star_vertex_lift (Quotient.exact (Sum.inl.inj h))
      change M.triangulation.vertex.SameCycle (.inl x)
        (M.triangulation.vertex (.inr (.inl y))) at hh
      exact hh.of_apply_right
    · intro h; exact False.elim (Sum.inl_ne_inr h)
    · intro h
      have hh := M.star_vertex_lift (Quotient.exact (Sum.inl.inj h))
      change M.triangulation.vertex.SameCycle
        (M.triangulation.vertex (.inr (.inl x))) (.inl y) at hh
      exact hh.of_apply_left
    · intro h
      have hh := M.star_vertex_lift (Quotient.exact (Sum.inl.inj h))
      change M.triangulation.vertex.SameCycle
        (M.triangulation.vertex (.inr (.inl x)))
        (M.triangulation.vertex (.inr (.inl y))) at hh
      exact hh.of_apply_left.of_apply_right
    · intro h; exact False.elim (Sum.inl_ne_inr h)
    · intro h; exact False.elim (Sum.inr_ne_inl h)
    · intro h; exact False.elim (Sum.inr_ne_inl h)
    · intro h; exact M.star_center_lift (Quotient.exact (Sum.inr.inj h))

omit [DecidableEq D] [Fintype D] in
lemma starVertexClass_surjective : Function.Surjective M.starVertexClass := by
  intro z
  rcases z with z | z
  · obtain ⟨x,rfl⟩ := Quotient.exists_rep z
    exact ⟨.inl x,rfl⟩
  · obtain ⟨x,rfl⟩ := Quotient.exists_rep z
    exact ⟨.inr (.inr x),rfl⟩

lemma triangulation_vertex_cycles : cycles M.triangulation.vertex = cycles M.vertex + cycles M.face := by
  rw [cycles_eq_card_classes,
    card_quotient_of_classifier _ M.starVertexClass M.star_vertex_cycle M.starVertexClass_surjective,
    Nat.card_sum,Nat.cast_add,← cycles_eq_card_classes,← cycles_eq_card_classes]

omit [DecidableEq D] in
lemma star_components_lift : M.components ≤ Setoid.comap Sum.inl M.triangulation.components := by
  apply M.components_le
  · intro x
    apply M.triangulation.components.trans'
      (M.triangulation.face_le_components
        (show M.triangulation.face.SameCycle (.inl x) (.inr (.inl x)) from SameCycle.rfl.apply_right))
    exact M.triangulation.vertex_le_components
      (show M.triangulation.vertex.SameCycle (.inr (.inl x)) (.inl (M.face x)) from SameCycle.rfl.apply_right)
  · intro x
    exact M.triangulation.edge_le_components
      (show M.triangulation.edge.SameCycle (.inl x) (.inl (M.edge x)) from SameCycle.rfl.apply_right)

def starComponent (x : StarDart D) : Quotient M.components :=
  Quotient.mk M.components (starIndex x)

omit [DecidableEq D] in
lemma star_components (x y : StarDart D) :
    M.triangulation.components x y ↔ M.starComponent x = M.starComponent y := by
  have hle : M.triangulation.components ≤ Setoid.ker M.starComponent := by
    apply M.triangulation.components_le
    · rintro (z | (z | z)) <;> rfl
    · rintro (z | (z | z))
      · exact Quotient.sound (M.edge_le_components SameCycle.rfl.apply_right)
      · exact Quotient.sound (M.face_le_components SameCycle.rfl.apply_right)
      · exact Quotient.sound (M.face_le_components SameCycle.rfl.symm_apply_right)
  refine ⟨fun h => hle h,?_⟩
  intro h
  exact M.triangulation.components.trans'
    (M.triangulation.face_le_components (M.star_face_to_left x))
    (M.triangulation.components.trans'
      (M.star_components_lift (Quotient.exact h))
      (M.triangulation.face_le_components (M.star_face_to_left y).symm))

omit [DecidableEq D] in
lemma triangulation_components_card : Nat.card (Quotient M.triangulation.components) =
    Nat.card (Quotient M.components) := by
  apply card_quotient_of_classifier _ M.starComponent M.star_components
  intro z
  obtain ⟨x,rfl⟩ := Quotient.exists_rep z
  exact ⟨.inl x,rfl⟩

lemma triangulation_euler : M.triangulation.euler = M.euler := by
  obtain ⟨k,hk⟩ := M.card_darts_even
  rw [euler,euler,M.triangulation_vertex_cycles,M.triangulation_face_cycles]
  change cycles M.vertex + cycles M.face + (Fintype.card D : ℤ) -
    (Fintype.card (D ⊕ (D ⊕ D)) : ℤ) / 2 = _
  rw [Fintype.card_sum,Fintype.card_sum,Nat.cast_add,Nat.cast_add]
  omega

/-- Literal face starring preserves genus zero and connected-component count;
its dual is therefore a genuine degree-three genus-zero ribbon graph. -/
theorem triangulation_genusZero (h : M.GenusZero) : M.triangulation.GenusZero := by
  change M.triangulation.euler = 2*(Nat.card (Quotient M.triangulation.components) : ℤ)
  rw [M.triangulation_euler,M.triangulation_components_card]
  exact h

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureStarGraph
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D)

def starOldVertex : M.GraphVertex → M.triangulation.GraphVertex :=
  Quotient.map Sum.inl (fun _ _ h => M.star_vertex_lift h)

omit [DecidableEq D] in
lemma starOldVertex_injective : Function.Injective M.starOldVertex := by
  intro v w
  induction v using Quotient.inductionOn with | _ x =>
    induction w using Quotient.inductionOn with | _ y =>
      intro h
      have hh := (M.star_vertex_cycle (.inl x) (.inl y)).mp (Quotient.exact h)
      exact Sum.inl.inj hh

def starOldHom : M.underlyingGraph →g M.triangulation.underlyingGraph where
  toFun := M.starOldVertex
  map_rel' := by
    intro v w h
    obtain ⟨hne,x,rfl,rfl⟩ := h
    exact ⟨fun he => hne (M.starOldVertex_injective he),.inl x,rfl,rfl⟩

omit [DecidableEq D] in
lemma triangulation_connected (hc : M.underlyingGraph.Connected) :
    M.triangulation.underlyingGraph.Connected := by
  have : Nonempty M.triangulation.GraphVertex := by
    obtain ⟨v⟩ := hc.nonempty
    exact ⟨M.starOldVertex v⟩
  apply SimpleGraph.Connected.mk
  intro v w
  induction v using Quotient.inductionOn with | _ x =>
    induction w using Quotient.inductionOn with | _ y =>
      apply (M.triangulation.underlying_reachable_iff x y).mpr
      apply (M.star_components x y).mpr
      exact Quotient.sound ((M.underlying_reachable_iff _ _).mp (hc _ _))

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PicturePlanarSeparator
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D)

/-- Literal genus-zero planar separator, independent of face degrees,
vertex degrees, all parallel copies, and the specified vertex carrier. -/
theorem planar_component_separator (hG : M.GenusZero) (hc : M.underlyingGraph.Connected)
    (U : Finset M.GraphVertex) :
    ∃ S : Finset M.GraphVertex, S ⊆ U ∧ S.card ≤ 11*Nat.sqrt U.card ∧
      ∀ W : Finset M.GraphVertex, W ⊆ U → Disjoint W S →
        (M.underlyingGraph.induce (W : Set M.GraphVertex)).Preconnected →
        2*W.card ≤ U.card := by
  have hs := M.triangulation.sqrt_component_separator (M.triangulation_genusZero hG)
    (M.triangulation_connected hc) 3 (fun x => (M.triangulation_face_degree x).le)
  exact component_separator_pullback M.underlyingGraph M.triangulation.underlyingGraph
    M.starOldHom M.starOldVertex_injective 11 (by simpa using hs) U

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureComponentGraph
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion SimpleGraph
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D) (C : M.underlyingGraph.ConnectedComponent)

def componentDarts (x : D) : Prop := M.vertexClass x ∈ C.supp

omit [DecidableEq D] in
lemma componentDarts_face (x : D) : M.componentDarts C (M.face x) ↔ M.componentDarts C x := by
  have hh := ConnectedComponent.sound ((M.underlying_reachable_iff (M.face x) x).mpr
    (M.face_le_components SameCycle.rfl.apply_left))
  change M.underlyingGraph.connectedComponentMk (M.vertexClass (M.face x)) = C ↔
    M.underlyingGraph.connectedComponentMk (M.vertexClass x) = C
  rw [hh]

omit [DecidableEq D] in
lemma componentDarts_edge (x : D) : M.componentDarts C (M.edge x) ↔ M.componentDarts C x := by
  have hh := ConnectedComponent.sound ((M.underlying_reachable_iff (M.edge x) x).mpr
    (M.edge_le_components SameCycle.rfl.apply_left))
  change M.underlyingGraph.connectedComponentMk (M.vertexClass (M.edge x)) = C ↔
    M.underlyingGraph.connectedComponentMk (M.vertexClass x) = C
  rw [hh]

def componentPicture : PictureMap {x : D // M.componentDarts C x} :=
  M.restrict (M.componentDarts C) (M.componentDarts_face C) (M.componentDarts_edge C)

lemma componentPicture_genusZero (hG : M.GenusZero) : (M.componentPicture C).GenusZero :=
  M.restrict_genusZero _ hG _ _

omit [DecidableEq D] in
lemma componentPicture_cycle (x y : {x : D // M.componentDarts C x}) :
    (M.componentPicture C).vertex.SameCycle x y ↔ M.vertex.SameCycle x.val y.val := by
  unfold componentPicture
  rw [M.restrict_vertex]
  exact sameCycle_subtypePerm_iff _ _ x y

instance componentDarts_nonempty : Nonempty {x : D // M.componentDarts C x} := by
  obtain ⟨v,hv⟩ := C.connected_toSimpleGraph.nonempty
  obtain ⟨x,hx⟩ := Quotient.exists_rep v
  change M.vertexClass x = v at hx
  exact ⟨⟨x,by change M.vertexClass x ∈ C.supp; rw [hx]; exact hv⟩⟩

omit [DecidableEq D] in
lemma componentPicture_connected : (M.componentPicture C).underlyingGraph.Connected := by
  have : Nonempty (M.componentPicture C).GraphVertex :=
    ⟨(M.componentPicture C).vertexClass (Classical.choice (M.componentDarts_nonempty C))⟩
  apply Connected.mk
  intro v w
  induction v using Quotient.inductionOn with | _ x =>
    induction w using Quotient.inductionOn with | _ y =>
      apply ((M.componentPicture C).underlying_reachable_iff x y).mpr
      change (M.restrict (M.componentDarts C) _ _).components x y
      rw [M.restrict_components]
      exact (M.underlying_reachable_iff x.val y.val).mp
        (C.reachable_of_mem_supp x.property y.property)

/-- Original graph-component vertices are carried to the actual restricted
rotation system, using representatives only to define the quotient map. -/
def componentVertex (v : C.supp) : (M.componentPicture C).GraphVertex :=
  (M.componentPicture C).vertexClass ⟨M.vertexRepresentative v.val,by
    change M.vertexClass (M.vertexRepresentative v.val) ∈ C.supp
    rw [M.vertexClass_representative]
    exact v.property⟩

omit [DecidableEq D] in
lemma componentVertex_class (x : D) (hx : M.componentDarts C x) :
    M.componentVertex C ⟨M.vertexClass x,hx⟩ =
      (M.componentPicture C).vertexClass ⟨x,hx⟩ := by
  apply Quotient.sound
  apply (M.componentPicture_cycle C _ _).mpr
  exact Quotient.exact (M.vertexClass_representative (M.vertexClass x))

omit [DecidableEq D] in
lemma componentVertex_injective : Function.Injective (M.componentVertex C) := by
  intro v w h
  apply Subtype.ext
  have hh := (M.componentPicture_cycle C _ _).mp (Quotient.exact h)
  have he : M.vertexClass (M.vertexRepresentative v.val) =
      M.vertexClass (M.vertexRepresentative w.val) := Quotient.sound hh
  simpa only [M.vertexClass_representative] using he

def componentHom : C.toSimpleGraph →g (M.componentPicture C).underlyingGraph where
  toFun := M.componentVertex C
  map_rel' := by
    intro v w h
    obtain ⟨hne,x,hx,he⟩ := h
    have hxp : M.componentDarts C x := by change M.vertexClass x ∈ C.supp; rw [hx]; exact v.property
    have hep : M.componentDarts C (M.edge x) := by change M.vertexClass (M.edge x) ∈ C.supp; rw [he]; exact w.property
    have hxv : (⟨M.vertexClass x,hxp⟩ : C.supp) = v := Subtype.ext hx
    have hew : (⟨M.vertexClass (M.edge x),hep⟩ : C.supp) = w := Subtype.ext he
    refine ⟨fun hh => hne (congrArg Subtype.val (M.componentVertex_injective C hh)),⟨x,hxp⟩,?_,?_⟩
    · rw [← hxv,M.componentVertex_class]
    · rw [← hew,M.componentVertex_class]
      rfl

/-- Every graph component has the separator produced by its literal
restricted genus-zero map. In particular no embedding of an induced graph
is being assumed. -/
theorem graph_component_separator (hG : M.GenusZero) (U : Finset C.supp) :
    ∃ S : Finset C.supp, S ⊆ U ∧ S.card ≤ 11*Nat.sqrt U.card ∧
      ∀ W : Finset C.supp, W ⊆ U → Disjoint W S →
        (C.toSimpleGraph.induce (W : Set C.supp)).Preconnected → 2*W.card ≤ U.card := by
  exact component_separator_pullback C.toSimpleGraph (M.componentPicture C).underlyingGraph
    (M.componentHom C) (M.componentVertex_injective C) 11
    ((M.componentPicture C).planar_component_separator (M.componentPicture_genusZero C hG)
      (M.componentPicture_connected C)) U

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureVertexCut
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.instFinite _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary
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
variable {D I : Type*} [DecidableEq D] [Fintype D] [Fintype I]
namespace PictureMap
variable (M : PictureMap D)

omit [DecidableEq D] in
lemma incident_darts_card (S : Finset M.GraphVertex) :
    Nat.card {x : D // M.vertexClass x ∈ S} =
      ∑ v : S, Nat.card {x : D // M.vertexClass x = v.val} := by
  let e : {x : D // M.vertexClass x ∈ S} ≃
      (v : S) × {x : D // M.vertexClass x = v.val} := {
    toFun := fun x => ⟨⟨M.vertexClass x.val,x.property⟩,x.val,rfl⟩
    invFun := fun x => ⟨x.2.val,by rw [x.2.property]; exact x.1.property⟩
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨⟨v,hv⟩,x,hx⟩; cases hx; rfl }
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]

omit [DecidableEq D] [Fintype I] in
/-- Recover the true multigraph cut count from a vertex separator in the
underlying simple graph. Every unordered edge copy is retained; multiple
contacts inject into distinct incident darts of separator vertices. -/
theorem relative_cuts_le_separator (active : D → Prop) (part : M.GraphVertex → I)
    (S : Finset M.GraphVertex) (d : ℕ)
    (hdegree : ∀ v ∈ S, Nat.card {x : D // M.vertexClass x = v} ≤ d)
    (hhit : ∀ x, active x → active (M.edge x) →
      part (M.vertexClass x) ≠ part (M.vertexClass (M.edge x)) →
      M.vertexClass x ∈ S ∨ M.vertexClass (M.edge x) ∈ S) :
    Fintype.card (RelativeCutContact M active (part ∘ M.vertexClass)) ≤ d * S.card := by
  let f : RelativeCutContact M active (part ∘ M.vertexClass) →
      {x : D // M.vertexClass x ∈ S} := fun x =>
    if h : M.vertexClass x.val ∈ S then ⟨x.val,h⟩ else
      ⟨M.edge x.val,(hhit x.val x.property.1 x.property.2.1 x.property.2.2.1).resolve_left h⟩
  have hf : Function.Injective f := by
    intro x y heq
    have he := congrArg Subtype.val heq
    apply Subtype.ext
    dsimp only [f] at he
    split_ifs at he with hx hy hy
    · exact he
    · have hxlt := x.property.2.2.2
      have hylt := y.property.2.2.2
      change x.val = M.edge y.val at he
      have hh : M.number (M.edge y.val) < M.number y.val := by
        simpa only [he,M.edge_edge] using hxlt
      exact (lt_asymm hylt hh).elim
    · have hxlt := x.property.2.2.2
      have hylt := y.property.2.2.2
      change M.edge x.val = y.val at he
      have hh : M.number (M.edge x.val) < M.number x.val := by
        simpa only [← he,M.edge_edge] using hylt
      exact (lt_asymm hxlt hh).elim
    · exact M.edge.injective he
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card {x : D // M.vertexClass x ∈ S} ≤ d * S.card := by
    rw [M.incident_darts_card]
    calc
      _ ≤ ∑ _v : S, d := Finset.sum_le_sum (fun v _ => hdegree v.val v.property)
      _ = d * S.card := by simp [mul_comm]
  simpa only [Nat.card_eq_fintype_card] using h1.trans h2

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PlanarPartitionBridge
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.instFinite _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

section
section


noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable

/-- Full uniform partition-to-multigraph-cut bridge. The required planar
separator producer remains EXPLICIT in the hypothesis; this theorem proves
all its downstream recursion, finite labeling and parallel-edge accounting.
The cutoff is chosen before the graph, its dart type, and its active carrier. -/
theorem uniform_relative_cut_partition (c : ℝ) (d : ℕ) (eta : ℝ)
    (hc : 0 ≤ c) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ ∀ (D : Type u) [Fintype D] [DecidableEq D] (M : PictureMap D),
      HasBalancedSeparators M.underlyingGraph c → ∀ U : Finset M.GraphVertex,
      (∀ v ∈ U, Nat.card {x : D // M.vertexClass x = v} ≤ d) →
      ∃ (I : Type) (_ : Fintype I) (part : M.GraphVertex → I),
        (∀ i, (U.filter (fun x => part x = i)).card ≤ K) ∧
        (Fintype.card (RelativeCutContact M (fun x => M.vertexClass x ∈ U)
          (part ∘ M.vertexClass)) : ℝ) ≤ eta * U.card := by
  obtain ⟨K,hK,huniform⟩ := uniform_bounded_partition c d eta hc (by positivity) heta
  refine ⟨K,hK,?_⟩
  intro D _ _ M hsep U hdegree
  classical
  obtain ⟨P,hP⟩ := huniform M.GraphVertex M.underlyingGraph hsep U
  refine ⟨P.Label,inferInstance,P.finiteLabel,?_,?_⟩
  · intro i
    convert P.finiteLabel_small i using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    simp only [Finset.mem_filter]
  ·
    have hcut := M.relative_cuts_le_separator (fun x => M.vertexClass x ∈ U)
      P.finiteLabel P.removed d (fun v hv => hdegree v (P.removed_subset hv)) ?_
    · have hcR : (Fintype.card (RelativeCutContact M (fun x => M.vertexClass x ∈ U)
          (P.finiteLabel ∘ M.vertexClass)) : ℝ) ≤ d * (P.removed.card : ℝ) := by
        exact_mod_cast hcut
      exact hcR.trans hP
    · intro x hx he hne
      by_contra h
      push Not at h
      have hlabels := P.edge_const (M.vertexClass x) hx (M.vertexClass (M.edge x)) he
        (show M.underlyingGraph.Adj (M.vertexClass x) (M.vertexClass (M.edge x)) from
          ⟨fun hh => hne (congrArg P.finiteLabel hh),x,rfl,rfl⟩) h.1 h.2
      exact hne (Subtype.ext hlabels)

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureFullSeparator
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D)

/-- Uniform planar separator for an arbitrary (possibly empty or
 disconnected) literal genus-zero rotation system and every vertex carrier.
 All genus, component, radius, triangulation and tree obligations are proved. -/
theorem genusZero_component_separator (hG : M.GenusZero) (U : Finset M.GraphVertex) :
    ∃ S : Finset M.GraphVertex, S ⊆ U ∧ S.card ≤ 11*Nat.sqrt U.card ∧
      ∀ W : Finset M.GraphVertex, W ⊆ U → Disjoint W S →
        (M.underlyingGraph.induce (W : Set M.GraphVertex)).Preconnected →
        2*W.card ≤ U.card :=
  component_separators_union M.underlyingGraph 11 (fun C => M.graph_component_separator C hG) U

/-- The actual Lipton--Tarjan-style input required by the manuscript's
recursive partition proof, proved from its finite genus-zero maps. -/
theorem genusZero_balanced_separators (hG : M.GenusZero) :
    HasBalancedSeparators M.underlyingGraph 11 :=
  balanced_separators_of_component_separators M.underlyingGraph 11
    (M.genusZero_component_separator hG)

end HyperbolicObstruction.PictureSwitch.PictureMap
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable

/-- The planar-multigraph partition producer. K is chosen
before EVERY finite dart type, genus-zero map and active carrier. The exact
multigraph cut cost is retained, including loops/parallel copies and an
arbitrary-degree protected exterior. -/
theorem uniform_genusZero_cut_partition (d : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ ∀ (D : Type u) [Fintype D] [DecidableEq D] (M : PictureMap D),
      M.GenusZero → ∀ U : Finset M.GraphVertex,
      (∀ v ∈ U, Nat.card {x : D // M.vertexClass x = v} ≤ d) →
      ∃ (I : Type) (_ : Fintype I) (part : M.GraphVertex → I),
        (∀ i, (U.filter (fun x => part x = i)).card ≤ K) ∧
        (Fintype.card (RelativeCutContact M (fun x => M.vertexClass x ∈ U)
          (part ∘ M.vertexClass)) : ℝ) ≤ eta * U.card := by
  obtain ⟨K,hK,hh⟩ := uniform_relative_cut_partition 11 d eta (by norm_num) heta
  exact ⟨K,hK,fun D _ _ M hM U hd => hh D M (M.genusZero_balanced_separators hM) U hd⟩

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PlanarFacePartition
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
universe u
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable

/-- Dual form of the proved genus-zero partition theorem, with literal
selected face classes and the original map's unordered edge-copy cuts. -/
theorem uniform_genusZero_face_partition (d : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ ∀ (D : Type u) [Fintype D] [DecidableEq D] (M : PictureMap D),
      M.GenusZero → ∀ U : Finset (Quotient (SameCycle.setoid M.face)),
      (∀ v ∈ U, Nat.card {x : D // Quotient.mk (SameCycle.setoid M.face) x = v} ≤ d) →
      ∃ (I : Type) (_ : Fintype I) (part : Quotient (SameCycle.setoid M.face) → I),
        (∀ i, (U.filter (fun x => part x = i)).card ≤ K) ∧
        (Fintype.card (RelativeCutContact M
          (fun x => Quotient.mk (SameCycle.setoid M.face) x ∈ U)
          (part ∘ Quotient.mk (SameCycle.setoid M.face))) : ℝ) ≤ eta * U.card := by
  obtain ⟨K,hK,hh⟩ := uniform_genusZero_cut_partition d eta heta
  refine ⟨K,hK,?_⟩
  intro D _ _ M hG
  let Q (v : Perm D) : Prop :=
    ∀ U : Finset (Quotient (SameCycle.setoid v)),
      (∀ f ∈ U, Nat.card {x : D // Quotient.mk (SameCycle.setoid v) x = f} ≤ d) →
      ∃ (I : Type) (_ : Fintype I) (part : Quotient (SameCycle.setoid v) → I),
        (∀ i, (U.filter (fun x => part x = i)).card ≤ K) ∧
        (Nat.card {x : D // Quotient.mk (SameCycle.setoid v) x ∈ U ∧
            Quotient.mk (SameCycle.setoid v) (M.edge x) ∈ U ∧
            part (Quotient.mk (SameCycle.setoid v) x) ≠
              part (Quotient.mk (SameCycle.setoid v) (M.edge x)) ∧
            M.number x < M.number (M.edge x)} : ℝ) ≤ eta * U.card
  have h := hh D M.dual (M.dual_genusZero hG)
  simp only [← Nat.card_eq_fintype_card] at h
  have hQ : Q M.dual.vertex := by
    simpa only [Q,PictureMap.GraphVertex,PictureMap.vertexClass,RelativeCutContact,
      Function.comp_apply,PictureMap.dual_edge,PictureMap.number] using h
  rw [M.dual_vertex] at hQ
  simpa only [Q,RelativeCutContact,Function.comp_apply,← Nat.card_eq_fintype_card] using hQ

end HyperbolicObstruction.PictureSwitch
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

def coverOffset : WalkStep n w d → G
  | .inl s => macroPotential n w v s.1 s.2.fst
  | .inr s => frozenOffset n w d v s

include hv hcell in
lemma coverOffset_opposite (s : WalkStep n w d) :
    coverOffset n w d v (walkOpposite n w d s) =
      coverOffset n w d v s * v (walkLabel n w d s) := by
  rcases s with ⟨a,e⟩ | s
  · exact (macroPotential_edge n w d v hv hcell a e.adj).symm
  · exact frozenOffset_opposite n w d v hv s

/-- The actual regular covering target, constructed from ordinary group edge
values satisfying the ORIGINAL cell equations. No lifted-chain conclusion is
assumed. In particular it applies to quotient group values, not only to the
bouquet auxiliary group. -/
def actualCellCover : WalkCellCover (indexingTarget n w d) G where
  voltage := v
  voltage_rev := hv
  offset := coverOffset n w d v
  offset_opposite := coverOffset_opposite n w d v hv hcell
  free_back := by
    rintro (⟨a,e⟩ | s) (⟨b,f⟩ | t) hs hk he
    · change Sum.inl (a,e.snd) = (Sum.inl (b,f.snd) : WalkVertex n w) at he
      have hh := Sum.inl.inj he
      exact congrArg (fun p : Top n w × MacroGraph.Vertex => macroPotential n w v p.1 p.2) hh
    · cases hk
    · cases hs
    · cases hs

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeDegree
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTopTurnDart _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.componentDarts_nonempty _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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
variable (P : WalkPicture.{0} (exteriorWalkTarget n w d ell hell word closed c hc f))

lemma exterior_top_degree (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart)
    (hx : P.index x = .inl (.inl (a,e))) :
    Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y} ≤ 15 := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let j : I → MacroGraph.graph.Dart := fun y =>
    (exterior_same_top n w d ell hell word closed c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (.inl (a,j y)) :=
    (exterior_same_top n w d ell hell word closed c hc f P hx y.property).choose_spec
  let q : Perm I := P.pairing.face.subtypePerm (fun _ => sameCycle_apply_right)
  have hfree (y : I) : (exteriorWalkTarget n w d ell hell word closed c hc f).free
      ((exteriorWalkTarget n w d ell hell word closed c hc f).kind (P.index y.val)) = true := by
    rw [hj]; rfl
  apply macro_parametrization_card q j
  · intro y
    have h := P.closed y.val
    change (exteriorWalkTarget n w d ell hell word closed c hc f).front
      (P.index (q y).val) = (exteriorWalkTarget n w d ell hell word closed c hc f).back
        (P.index y.val) at h
    rw [hj,hj] at h
    exact congrArg Prod.snd (Sum.inl.inj (Sum.inl.inj h))
  · intro i k hik
    apply Subtype.ext
    apply P.simple_front hs (hfree i) (i.property.symm.trans k.property)
    rw [hj,hj]
    exact congrArg Sum.inl (congrArg Sum.inl (Prod.ext rfl hik))
  · intro y he
    exact hb y.val (hfree y) (congrArg Subtype.val he)

end HyperbolicObstruction.ConeSkeleton
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

/-! Literal radial triangulation of the free polygon faces of a finite map.
This section concerns genuine permutations; no topological genus assertion is
included in the input. -/

/-! Exact contraction of radial triangle stars. -/
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D] [DecidableEq D]

namespace TriangleMarking
variable {M : PictureMap D} (H : TriangleMarking M)

def free (x : H.Base) : Prop := H.top x.val = true

end TriangleMarking
end PictureSwitch

/-! Local elementary triangle incidence induces the exact radial contraction. -/

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

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
abbrev elementaryPolyhedron := Carrier (elementarySimplicialComplex n w d)

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

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/

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


