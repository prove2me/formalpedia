-- Prove2me | Definitions.Def_OAIQ034H004
-- name    : OAIQ034H004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:34:53.813155+00:00
-- url     : https://prove2.me/theorems/91b14f6c-93cb-463a-9ba4-302173db858a
-- title:
--   Definitions bundle OAIQ034H004 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 208 declarations of OpenAI's Lean: 38 definitions, 2 inductive types or structures, 5 instances and 163 theorems. The definitions and types are `OAI.HyperbolicObstruction.ConeSkeleton.SelectedFace`, `OAI.HyperbolicObstruction.ConeSkeleton.SelectedTriangleFace`, `OAI.HyperbolicObstruction.ConeSkeleton.TopTurnDart`, `OAI.HyperbolicObstruction.ConeSkeleton.macroBase`, `OAI.HyperbolicObstruction.ConeSkeleton.walkApex`, `OAI.HyperbolicObstruction.FanLink.FanData`, `OAI.HyperbolicObstruction.FanLink.FanData.isPartial`, `OAI.HyperbolicObstruction.FanLink.FanData.maxMultiplicity`, `OAI.HyperbolicObstruction.FanLink.FanData.multiplicity`, `OAI.HyperbolicObstruction.FanLink.FanData.partialCount`, `OAI.HyperbolicObstruction.FanLink.FanData.weight`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.Entry`, `OAI.HyperbolicObstruction.MacroGraph.Allowed`, `OAI.HyperbolicObstruction.MacroGraph.Certificate`, `OAI.HyperbolicObstruction.MacroGraph.Polygon.vertices`, `OAI.HyperbolicObstruction.MacroGraph.rank`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.Bigon`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.Bigon.remove`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.GraphVertex`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.VertexTransition`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.boundaryFold`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.boundaryPinch`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.eraseEdge`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.graphComponent`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.graphPairing`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.restrict`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.splice`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.subpairingGraph`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.transitionSide`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.underlyingGraph`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.vertexClass`, `OAI.HyperbolicObstruction.PictureSwitch.PictureMap.vertex_fiber_equiv`, `OAI.HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary.positiveSides`, `OAI.HyperbolicObstruction.PictureSwitch.RelativeCutContact`, `OAI.HyperbolicObstruction.PictureSwitch.RelativePartBoundary`, `OAI.HyperbolicObstruction.PictureSwitch.classifierMap`, `OAI.HyperbolicObstruction.PictureSwitch.erasePair`, `OAI.HyperbolicObstruction.WordPictures.WordPicture.foldAt`, `OAI.HyperbolicObstruction.WordPictures.WordPicture.peelAt`, `OAI.HyperbolicObstruction.WordPictures.WordPicture.rotate`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_ActualFaceCounts`, `HyperbolicGroups_ActualLabel`, `HyperbolicGroups_BFSTree`, `HyperbolicGroups_BigonRemove`, `HyperbolicGroups_BoundaryEnumeration`, `HyperbolicGroups_BoundaryEraseList`, `HyperbolicGroups_BoundaryFold`, `HyperbolicGroups_BoundaryGraphWalk`, `HyperbolicGroups_BoundaryLift`, `HyperbolicGroups_BoundaryList`, `HyperbolicGroups_BoundaryRotation`, `HyperbolicGroups_BoundarySplice`, `HyperbolicGroups_ConeCellTarget`, `HyperbolicGroups_ConeGraph`, `HyperbolicGroups_ConeSkeleton`, `HyperbolicGroups_ConeTopCollapse`, `HyperbolicGroups_CycleCount`, `HyperbolicGroups_EdgeErase`, `HyperbolicGroups_EdgeEraseBoundary`, `HyperbolicGroups_EdgeEraseComponents`, `HyperbolicGroups_EdgeEraseCount`, `HyperbolicGroups_EdgeEraseGenus`, `HyperbolicGroups_FaceSplice`, `HyperbolicGroups_FaceSplit`, `HyperbolicGroups_FanApex`, `HyperbolicGroups_GeneralSwitch`, `HyperbolicGroups_GraphSubpairing`, `HyperbolicGroups_MacroCertificate`, `HyperbolicGroups_MacroCycle`, `HyperbolicGroups_MacroFaceFilling`, `HyperbolicGroups_MacroWalk`, `HyperbolicGroups_MappedPicture`, `HyperbolicGroups_Occurrence`, `HyperbolicGroups_PairingForest`, `HyperbolicGroups_PermErase`, `HyperbolicGroups_PermErasePair`, `HyperbolicGroups_PermEuler`, `HyperbolicGroups_PermSwitch`, `HyperbolicGroups_PictureBoundaryParity`, `HyperbolicGroups_PictureEuler`, `HyperbolicGroups_PictureGenus`, `HyperbolicGroups_PictureLeaf`, `HyperbolicGroups_PictureMap`, `HyperbolicGroups_PictureMapFurther`, `HyperbolicGroups_PictureMirror`, `HyperbolicGroups_PictureRestrict`, `HyperbolicGroups_PictureUnderlyingGraph`, `HyperbolicGroups_PictureVertexBoundary`, `HyperbolicGroups_PlanarEdgeOrdering`, `HyperbolicGroups_PlanarSubpairing`, `HyperbolicGroups_PolygonBoundaryList`, `HyperbolicGroups_RelativeDegree`, `HyperbolicGroups_RelativePartition`, `HyperbolicGroups_SetoidGlue`, `HyperbolicGroups_SetoidRestrict`, `HyperbolicGroups_SubpairingGraph`, `HyperbolicGroups_WalkRadialBoundary`, `HyperbolicGroups_WalkTopTurns`, `HyperbolicGroups_WalkTriangleTransport`, `HyperbolicGroups_WeightedRank`, `HyperbolicGroups_WordPicture`, `HyperbolicGroups_WordPictureArea`, `HyperbolicGroups_WordPictureBase`, `HyperbolicGroups_WordPictureExist`, `HyperbolicGroups_WordPictureFold`, `HyperbolicGroups_WordPicturePeel`, `HyperbolicGroups_WordSubstitution`.
--
--   **Imports.** It imports the bundles `OAIQ034H000` and `OAIQ034H001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ034H007`, `OAIQ034H008`, `OAIQ034H009` and `OAIQ034H010`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ034H000
import Definitions.Def_OAIQ034H001

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermSwitch
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
variable {D : Type*} [DecidableEq D]

section Finite
variable [Fintype D]

lemma defect_disjoint {p q : Perm D} (h : p.Disjoint q) :
    defect (p * q) = defect p + defect q := by
  simp only [defect,h.card_support_mul,h.cycleType_mul,Multiset.card_add,Nat.cast_add]
  ring

lemma defect_list (a : D) (l : List D) (h : (a :: l).Nodup) :
    defect (a :: l).formPerm = l.length := by
  cases l with
  | nil => simp [defect]
  | cons b l =>
    have hl : 2 ≤ (a :: b :: l).length := by simp
    have hc := List.isCycle_formPerm h hl
    have hs := List.support_formPerm_of_nodup (a :: b :: l) h (by
      intro x he; have := congrArg List.length he; simp at this)
    rw [defect,hc.cycleType,hs,List.toFinset_card_of_nodup h]
    simp

lemma defect_split_list (a b : D) (l m : List D)
    (h : (a :: l ++ b :: m).Nodup) :
    defect (swap a b * (a :: l ++ b :: m).formPerm) + 1 =
      defect (a :: l ++ b :: m).formPerm := by
  have hs : ((a::l) ++ (b::m)).Nodup := h
  have hd : (a::l).Disjoint (b::m) := by
    intro x hx hm
    exact (List.nodup_append.mp hs).2.2 x hx x hm rfl
  rw [split_list a b l m h,defect_disjoint (disjoint_lists _ _ hd),
    defect_list a l hs.of_append_left,defect_list b m hs.of_append_right]
  have ho := defect_list a (l ++ b :: m) (by simpa only [List.cons_append] using h)
  simp only [List.cons_append] at ⊢
  rw [ho]
  simp only [List.length_append,List.length_cons,Nat.cast_add,Nat.cast_one]
  ring

/-- A transposition between two corners of one vertex splits that vertex.
This includes the extremal cut creating one or two valence-one vertices. -/
theorem cycles_split (p : Perm D) {a b : D} (hab : a ≠ b)
    (hsame : p.SameCycle a b) : cycles (swap a b * p) = cycles p + 1 := by
  have ha : a ∈ p.support := by
    apply mem_support.mpr
    intro h
    exact hab (hsame.eq_of_left h)
  have hb : b ∈ p.toList a := mem_toList_iff.mpr ⟨hsame,ha⟩
  obtain ⟨l,hl⟩ : ∃ l, p.toList a = a :: l := by
    have hn := p.length_toList_pos_of_mem_support a ha
    cases ht : p.toList a with
    | nil => simp [ht] at hn
    | cons x l =>
      have hx := p.toList_getElem_zero a ha
      simp only [ht,List.getElem_cons_zero] at hx
      exact ⟨l,by simp only [hx]⟩
  have hbl : b ∈ l := by simpa only [hl,List.mem_cons,hab.symm,false_or] using hb
  obtain ⟨l₁,l₂,he⟩ := List.mem_iff_append.mp hbl
  subst l
  have hc : p.cycleOf a = (a :: l₁ ++ b :: l₂).formPerm := by
    rw [← p.formPerm_toList a,hl]
    rfl
  have hn : (a :: l₁ ++ b :: l₂).Nodup := by
    have := p.nodup_toList a
    simpa only [hl,List.cons_append] using this
  have hd := remainder_disjoint p a
  have hh : (swap a b).Disjoint ((p.cycleOf a)⁻¹ * p) := by
    apply disjoint_iff_eq_or_eq.mpr
    intro x
    by_cases hx : x = a ∨ x = b
    · right
      have hxm : x ∈ (p.cycleOf a).support := by
        rcases hx with rfl | rfl
        · exact mem_support_cycleOf_iff.mpr ⟨SameCycle.rfl,ha⟩
        · exact mem_support_cycleOf_iff.mpr ⟨hsame,ha⟩
      exact (disjoint_iff_eq_or_eq.mp hd x).resolve_left (mem_support.mp hxm)
    · left
      exact swap_apply_of_ne_of_ne (by tauto) (by tauto)
  have hnew := hh.mul_left hd
  have hfac : p.cycleOf a * ((p.cycleOf a)⁻¹ * p) = p := by group
  have heq : swap a b * p = (swap a b * p.cycleOf a) * ((p.cycleOf a)⁻¹ * p) := by
    rw [mul_assoc,hfac]
  have ho := defect_disjoint hd
  have hs := defect_split_list a b l₁ l₂ hn
  rw [← hc] at hs
  rw [hfac] at ho
  unfold cycles
  rw [heq,defect_disjoint hnew]
  omega

theorem cycles_merge (p : Perm D) {a b : D}
    (h : ¬ p.SameCycle a b) : cycles (swap a b * p) + 1 = cycles p := by
  have hab : a ≠ b := fun he => h (he.sameCycle p)
  have hs := cycles_split (swap a b * p) hab (sameCycle_after_swap p h)
  simpa only [← mul_assoc,swap_mul_self,one_mul] using hs.symm

/-- Right multiplication cuts the outgoing ends instead of the incoming ends. -/
theorem cycles_split_right (p : Perm D) {a b : D} (hab : a ≠ b)
    (h : p.SameCycle a b) : cycles (p * swap a b) = cycles p + 1 := by
  rw [mul_swap_eq_swap_mul]
  exact cycles_split p (p.injective.ne hab) (h.apply_left.apply_right)

theorem cycles_merge_right (p : Perm D) {a b : D}
    (h : ¬ p.SameCycle a b) : cycles (p * swap a b) + 1 = cycles p := by
  rw [mul_swap_eq_swap_mul]
  apply cycles_merge
  simpa only [sameCycle_apply_left,sameCycle_apply_right] using h

lemma cycles_eq_fixed_add (p : Perm D) :
    cycles p = Fintype.card (Function.fixedPoints p) + p.cycleType.card := by
  have hs : p.support.card ≤ Fintype.card D := p.support.card_le_univ
  rw [Equiv.Perm.card_fixedPoints,p.sum_cycleType]
  simp only [cycles,defect,Nat.cast_sub hs]
  ring

end Finite
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CycleCount
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
variable {D : Type*} [DecidableEq D] [Fintype D]

lemma classify_eq_iff (p : Perm D) (a b : D) :
    classify p a = classify p b ↔ p.SameCycle a b := by
  by_cases ha : p a = a
  · constructor
    · intro he
      by_cases hb : p b = b
      · simp only [classify,dite_eq_left ha,dite_eq_left hb,Sum.inl.injEq] at he
        exact (congrArg Subtype.val he).sameCycle p
      · simp only [classify,dite_eq_left ha,dite_eq_right hb,Sum.inl_ne_inr] at he
    · intro he
      have hab := he.eq_of_left ha
      rw [hab]
  · constructor
    · intro he
      by_cases hb : p b = b
      · simp only [classify,dite_eq_right ha,dite_eq_left hb,Sum.inr_ne_inl] at he
      · simp only [classify,dite_eq_right ha,dite_eq_right hb,Sum.inr.injEq,Subtype.mk.injEq] at he
        exact (sameCycle_iff_cycleOf_eq_of_mem_support (mem_support.mpr ha) (mem_support.mpr hb)).mpr he
    · intro he
      have hb : p b ≠ b := fun hb => ha (he.apply_eq_self_iff.mpr hb)
      simp only [classify,dite_eq_right ha,dite_eq_right hb,Sum.inr.injEq,Subtype.mk.injEq]
      exact he.cycleOf_eq

def classifierMap (p : Perm D) : VertexClasses p → Classifier p :=
  Quotient.lift (classify p) (fun a b h => (classify_eq_iff p a b).mpr h)

lemma classifierMap_bijective (p : Perm D) : Function.Bijective (classifierMap p) := by
  constructor
  · intro a b
    induction a,b using Quotient.inductionOn₂ with
    | h a b =>
      intro he
      exact Quotient.sound ((classify_eq_iff p a b).mp he)
  · intro z
    cases z with
    | inl x =>
      refine ⟨Quotient.mk _ x.val,?_⟩
      change classify p x.val = Sum.inl x
      have hx : p x.val = x.val := x.property
      simp only [classify,dite_eq_left hx]
    | inr c =>
      obtain ⟨x,hx⟩ := (mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support
      have hp : p x ≠ x := mem_support.mp ((mem_cycleFactorsFinset_support_le c.property) hx)
      refine ⟨Quotient.mk _ x,?_⟩
      change classify p x = Sum.inr c
      simp only [classify,dite_eq_right hp,Sum.inr.injEq]
      apply Subtype.ext
      exact ((eq_cycleOf_of_mem_cycleFactorsFinset_iff p c c.property x).mpr hx).symm

/-- The numerical cycle count used in the Euler computation equals the actual
finite quotient of side corners by vertex-link connectivity. -/
theorem cycles_eq_card_classes (p : Perm D) :
    cycles p = Nat.card (VertexClasses p) := by
  classical
  let := Fintype.ofFinite (VertexClasses p)
  rw [Nat.card_eq_fintype_card]
  have hc := Fintype.card_congr (Equiv.ofBijective (classifierMap p) (classifierMap_bijective p))
  rw [hc,Fintype.card_sum,Fintype.card_coe,cycles_eq_fixed_add]
  simp [cycleType]

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SetoidGlue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
attribute [local instance] Classical.propDecidable

variable {D : Type*} (s : Setoid D) (a b : D)

section Finite
variable [Finite D]

/-- Exactly one component is lost when previously distinct classes are glued. -/
theorem card_glue_of_not_rel (h : ¬ s a b) :
    Nat.card (Quotient (glue s a b)) + 1 = Nat.card (Quotient s) := by
  classical
  let qa : Quotient s := Quotient.mk s a
  let qb : Quotient s := Quotient.mk s b
  have hn : qa ≠ qb := fun he => h (Quotient.exact he)
  let f : D → {q : Quotient s // q ≠ qb} := fun x =>
    ⟨if (Quotient.mk s x : Quotient s) = qb then qa else Quotient.mk s x,
      by split_ifs with hx <;> assumption⟩
  have hf : Function.Surjective f := by
    rintro ⟨q,hq⟩
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective q
    refine ⟨x,Subtype.ext ?_⟩
    exact ite_eq_right hq
  have hk : Setoid.ker f = glue s a b := by
    ext x y
    change (f x = f y) ↔ ((if (Quotient.mk s x : Quotient s) = qb then qa else Quotient.mk s x) =
      (if (Quotient.mk s y : Quotient s) = qb then qa else Quotient.mk s y))
    simp only [f,Subtype.mk.injEq]
  have hc := Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hf)
  rw [hk] at hc
  rw [hc]
  let := Fintype.ofFinite (Quotient s)
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  have hpos : 0 < Fintype.card (Quotient s) := Fintype.card_pos_iff.mpr ⟨qa⟩
  simp only [Fintype.card_unique]
  omega

/-- A uniformly phrased count, including the already-related case. -/
theorem card_glue : (Nat.card (Quotient (glue s a b)) : ℤ) =
    Nat.card (Quotient s) - if s a b then 0 else 1 := by
  classical
  by_cases h : s a b
  · rw [glue_eq_of_rel s a b h,ite_eq_left h,sub_zero]
  · rw [ite_eq_right h]
    have hc := card_glue_of_not_rel s a b h
    omega

end Finite
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermEuler
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

lemma sameCycle_swap_le {s : Setoid D} {a b : D} (h : s a b) :
    SameCycle.setoid (swap a b) ≤ s := by
  apply sameCycle_le_of_apply
  intro x
  by_cases ha : x = a
  · subst x; simpa using h
  by_cases hb : x = b
  · subst x; simpa using s.symm' h
  · simp [swap_apply_of_ne_of_ne ha hb]

omit [DecidableEq D] in
lemma sameCycle_mul_le {s : Setoid D} {p q : Perm D}
    (hp : SameCycle.setoid p ≤ s) (hq : SameCycle.setoid q ≤ s) :
    SameCycle.setoid (p*q) ≤ s := by
  apply sameCycle_le_of_apply
  intro x
  exact s.trans' (hq (SameCycle.rfl.apply_right)) (hp (SameCycle.rfl.apply_right))

lemma sameCycle_glue {p : Perm D} {s : Setoid D} (h : SameCycle.setoid p ≤ s) (a b : D) :
    SameCycle.setoid (p * swap a b) ≤ glue s a b :=
  sameCycle_mul_le (h.trans (le_glue s a b)) (sameCycle_swap_le (glue_pair s a b))

/-- The Euler potential increases by at most one on adjoining a paired side.
If the side joins different components, the face cycles merge and the bound
is an equality. This is the combinatorial source of the genus inequality. -/
lemma potential_step {p : Perm D} {s : Setoid D} (h : SameCycle.setoid p ≤ s)
    (a b : D) :
    cycles (p * swap a b) - 2 * (Nat.card (Quotient (glue s a b)) : ℤ) ≤
      cycles p - 2 * (Nat.card (Quotient s) : ℤ) + 1 := by
  rw [card_glue]
  by_cases hs : s a b
  · rw [ite_eq_left hs,sub_zero]
    by_cases hab : a = b
    · subst b
      have he : swap a a = (1 : Perm D) := swap_self a
      rw [he,mul_one]
      omega
    by_cases hp : p.SameCycle a b
    · rw [cycles_split_right p hab hp]
      omega
    · have hc := cycles_merge_right p hp
      omega
  · rw [ite_eq_right hs]
    have hp : ¬ p.SameCycle a b := fun hp => hs (h hp)
    have hc := cycles_merge_right p hp
    omega

lemma sameCycle_joins {p : Perm D} {s : Setoid D} (h : SameCycle.setoid p ≤ s)
    (l : List (D × D)) : SameCycle.setoid (p * swaps l) ≤ joins s l := by
  induction l generalizing p s with
  | nil => simpa [swaps,joins] using h
  | cons ab l ih =>
    simpa [swaps,joins,← mul_assoc] using ih (sameCycle_glue h ab.1 ab.2)

/-- The full finite combinatorial Euler inequality before identifying the
final components with a particular surface. -/
theorem potential_list {p : Perm D} {s : Setoid D} (h : SameCycle.setoid p ≤ s)
    (l : List (D × D)) :
    cycles (p * swaps l) - 2 * (Nat.card (Quotient (joins s l)) : ℤ) ≤
      cycles p - 2 * (Nat.card (Quotient s) : ℤ) + l.length := by
  induction l generalizing p s with
  | nil => simp [swaps,joins]
  | cons ab l ih =>
    have hh := ih (sameCycle_glue h ab.1 ab.2)
    have hs := potential_step h ab.1 ab.2
    simp only [swaps,List.map_cons,List.prod_cons,← mul_assoc,joins] at *
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    omega

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureMap
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

lemma vertex_switch (a b : D) :
    (M.switch a b).vertex =
      M.vertex * swap (M.edge a) (M.edge b) * swap a b := by
  have he : M.edge * swap (M.edge a) (M.edge b) = swap a b * M.edge := by
    rw [mul_swap_eq_swap_mul,M.edge_edge,M.edge_edge]
  simp only [vertex,switch]
  rw [mul_assoc M.face M.edge,he]
  group

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureEuler
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
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap
variable (M : PictureMap D)

omit [DecidableEq D] [Fintype D] in
lemma vertex_le_components : SameCycle.setoid M.vertex ≤ M.components := le_sup_left
omit [DecidableEq D] [Fintype D] in
lemma edge_le_components : SameCycle.setoid M.edge ≤ M.components := le_sup_right

omit [DecidableEq D] in
lemma face_le_components : SameCycle.setoid M.face ≤ M.components := by
  have h := sameCycle_mul_le M.vertex_le_components M.edge_le_components
  have he : M.vertex * M.edge = M.face := by
    rw [vertex,mul_assoc,M.edge_sq,mul_one]
  rwa [he] at h

omit [DecidableEq D] in
lemma components_le {s : Setoid D}
    (hf : ∀ x, s x (M.face x)) (he : ∀ x, s x (M.edge x)) : M.components ≤ s := by
  apply sup_le
  · exact sameCycle_mul_le (sameCycle_le_of_apply hf) (sameCycle_le_of_apply he)
  · exact sameCycle_le_of_apply he

/-- Euler's upper bound for every finite oriented side-pairing, without
assuming a drawing or the surface classification theorem. -/
theorem euler_le : M.euler ≤ 2 * (Nat.card (Quotient M.components) : ℤ) := by
  classical
  obtain ⟨l,hl,hcard,hpairs⟩ := involution_pairs M.edge M.edge_sq
  have hsupp : M.edge.support = Finset.univ := by
    ext x
    simp [mem_support,M.edge_ne]
  rw [hsupp,Finset.card_univ] at hcard
  have hprod : swaps l = M.edge := hl
  have hc : joins (SameCycle.setoid M.vertex) l = M.components := by
    apply le_antisymm
    · apply joins_le _ _ _ M.vertex_le_components
      intro ab hab
      apply M.edge_le_components
      rw [← (hpairs ab hab).2]
      exact SameCycle.rfl.apply_right
    · apply sup_le
      · exact le_joins _ _
      · have h1 : SameCycle.setoid (1 : Perm D) ≤ SameCycle.setoid M.vertex := by
          intro a b hab
          exact (hab.eq_of_left rfl).sameCycle M.vertex
        have h := sameCycle_joins h1 l
        simpa only [one_mul,hprod] using h
  have h := potential_list (p := M.vertex) (s := SameCycle.setoid M.vertex) le_rfl l
  rw [hc,hprod] at h
  have he : M.vertex * M.edge = M.face := by rw [vertex,mul_assoc,M.edge_sq,mul_one]
  rw [he,← cycles_eq_card_classes M.vertex] at h
  have hn : (Fintype.card D : ℤ) = 2 * (l.length : ℤ) := by exact_mod_cast hcard.symm
  have heuler : M.euler = cycles M.vertex + cycles M.face - l.length := by
    rw [euler,hn]
    omega
  rw [heuler]
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

lemma sameCycle_after_swap_right (p : Perm D) {a b : D}
    (h : ¬ p.SameCycle a b) : (p * swap a b).SameCycle a b := by
  by_contra hn
  have h1 := cycles_merge_right p h
  have h2 := cycles_merge_right (p * swap a b) hn
  simp only [mul_assoc,swap_mul_self,mul_one] at h2
  omega

namespace PictureMap
variable (M : PictureMap D)

lemma components_le_glue_switch (a b : D) :
    M.components ≤ glue (M.switch a b).components a b := by
  let s := glue (M.switch a b).components a b
  have hs : (M.switch a b).components ≤ s := le_glue _ _ _
  have ht : ∀ x, s x (swap a b x) := fun x =>
    sameCycle_swap_le (glue_pair _ a b) SameCycle.rfl.apply_right
  apply M.components_le
  · intro x
    exact hs ((M.switch a b).face_le_components SameCycle.rfl.apply_right)
  · intro x
    have hx := hs ((M.switch a b).edge_le_components (SameCycle.rfl (x := swap a b x)).apply_right)
    have hh := s.trans' (ht x) (s.trans' hx (ht ((M.switch a b).edge (swap a b x))))
    simpa only [switch,mul_apply,swap_apply_self] using hh

lemma switch_components_le_glue (a b : D) :
    (M.switch a b).components ≤ glue M.components a b := by
  let s := glue M.components a b
  have hs : M.components ≤ s := le_glue _ _ _
  have ht : ∀ x, s x (swap a b x) := fun x =>
    sameCycle_swap_le (glue_pair _ a b) SameCycle.rfl.apply_right
  apply (M.switch a b).components_le
  · intro x
    exact hs (M.face_le_components SameCycle.rfl.apply_right)
  · intro x
    have hx := hs (M.edge_le_components (SameCycle.rfl (x := swap a b x)).apply_right)
    exact s.trans' (ht x) (s.trans' hx (ht (M.edge (swap a b x))))

/-- Restoring a single connection between the two new apex instances recovers
exactly the previous surface components. In particular a switch can split
only the affected component, into at most two components. -/
theorem switch_components_glue (a b : D) (hv : M.vertex.SameCycle a b) :
    glue (M.switch a b).components a b = M.components := by
  have hab : M.components a b := M.vertex_le_components hv
  have hnew : (M.switch a b).components ≤ M.components := by
    have h := M.switch_components_le_glue a b
    rwa [glue_eq_of_rel _ _ _ hab] at h
  exact le_antisymm (glue_le _ _ _ hnew hab) (M.components_le_glue_switch a b)

theorem switch_components_card (a b : D) (hv : M.vertex.SameCycle a b) :
    (Nat.card (Quotient (M.switch a b).components) : ℤ) =
      Nat.card (Quotient M.components) +
        if (M.switch a b).components a b then 0 else 1 := by
  have h := card_glue (M.switch a b).components a b
  rw [M.switch_components_glue a b hv] at h
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

omit [Fintype D] in
lemma switch_respects {M : PictureMap D} {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) {a b : D} (hab : label a = label b) :
    (M.switch a b).Respects label start rev := by
  constructor
  · intro x
    have hfar : start (label (M.edge a)) = start (label (M.edge b)) := by
      rw [hM.2 a,hM.2 b,hab]
    have hnear : start (label a) = start (label b) := congrArg start hab
    rw [M.vertex_switch]
    simp only [mul_apply,hM.1]
    change (start ∘ label) (swap (M.edge a) (M.edge b) (swap a b x)) = (start ∘ label) x
    rw [Equiv.apply_swap_eq_self (v := start ∘ label) hfar,
      Equiv.apply_swap_eq_self (v := start ∘ label) hnear]
  · intro x
    change label (swap a b (M.edge (swap a b x))) = rev (label x)
    rw [Equiv.apply_swap_eq_self hab,hM.2,Equiv.apply_swap_eq_self hab]

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeSkeleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation

variable (n : ℕ)
variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)

lemma radial (l : Dart n w) (h : isApex n w (start n w l) = true) :
    isApex n w (start n w (rev n w l)) = false := by
  rcases l with ⟨e,b⟩; cases e <;> cases b <;> simp_all [start,isApex,rev]

end ConeSkeleton
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.MacroGraph
open IncidenceTemplate

/-- Keep at most the specified two points, but retain every line and the
subdivision vertex. Such an induced graph is a forest. -/
def Allowed (p q : Fin 7) : Vertex → Prop
  | .inl (.inl i) => i = p ∨ i = q
  | _ => True
instance instDecidableAllowed (p q : Fin 7) (a : Vertex) : Decidable (Allowed p q a) := by
  rcases a with ((i|l)|⟨⟩) <;> unfold Allowed <;> infer_instance

/-- A leaf-elimination certificate, rooted at p. Ranks strictly rise towards
the unique common line and the root; the exceptional rank subdivides its edge.
This is a formula on the actual seven Fano vectors, not a graph hypothesis. -/
def rank (p q : Fin 7) : Vertex → ℕ
  | .inl (.inl i) => if i = p then 8 else if i = q then 4 else 0
  | .inl (.inr l) => if p ≠ q ∧ Incident p l ∧ Incident q l then 6 else 2
  | .inr _ => if (3:Fin 7) = p ∨ (3:Fin 7) = q then
      if p ≠ q ∧ Incident p 4 ∧ Incident q 4 then if p = 3 then 7 else 5 else 3
    else 1

def Certificate (p q : Fin 7) : Prop :=
  ∀ v a b : Vertex, (Allowed p q v ∧ Allowed p q a ∧ Allowed p q b ∧
    Adjacent v a ∧ Adjacent v b ∧ rank p q v ≤ rank p q a ∧ rank p q v ≤ rank p q b) → a = b


end HyperbolicObstruction.MacroGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeGraph
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
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)

lemma top_row_injective : Function.Injective
    (fun a : CoreRow n => TableModel.row rowSupport (extendCore n a) (.inr (.inl ()))) := by
  intro a b he
  funext e
  have hh := Sigma.mk.inj he
  have hh' : (fun f : rowSupport (.inr (.inl ())) => extendCore n a f.val) =
      (fun f : rowSupport (.inr (.inl ())) => extendCore n b f.val) := eq_of_heq hh.2
  exact congrFun hh' ⟨.inl e,by simp [rowSupport]⟩

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.MacroGraph
open IncidenceTemplate

namespace Polygon
variable (P : Polygon)

def vertices : Finset Vertex := Finset.univ.image P.vertex

lemma perimeter_le : P.n ≤ 15 := by
  have h := Fintype.card_le_of_injective P.vertex P.injective
  simpa [Vertex] using h

lemma two_neighbors : ∀ v ∈ P.vertices, ∃ a ∈ P.vertices, ∃ b ∈ P.vertices,
    a ≠ b ∧ Adjacent v a ∧ Adjacent v b := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  refine ⟨P.vertex (P.next i),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,
    P.vertex (P.next.symm i),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,?_,P.adjacent i,?_⟩
  · intro h
    have hi := P.injective h
    have he := congrArg P.next hi
    simp only [Equiv.apply_symm_apply] at he
    exact P.no_backtrack i he
  · have h := adjacent_symm (P.adjacent (P.next.symm i))
    simpa only [Equiv.apply_symm_apply] using h

end Polygon
end HyperbolicObstruction.MacroGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.MacroGraph

theorem cycle_perimeter {u : Vertex} (p : graph.Walk u u) (hp : p.IsCycle) :
    p.length ≤ 15 := (ofCycle p hp).perimeter_le

end HyperbolicObstruction.MacroGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GeneralSwitch
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
variable {D : Type*} [DecidableEq D]
namespace PictureMap
variable (M : PictureMap D)

lemma switch_opposite (a : D) : M.switch a (M.edge a) = M := by
  refine PictureMap.ext (M := M.switch a (M.edge a)) (N := M) rfl ?_
  change swap a (M.edge a) * M.edge * swap a (M.edge a) = M.edge
  rw [mul_assoc,mul_swap_eq_swap_mul M.edge a (M.edge a),M.edge_edge,swap_comm (M.edge a) a]
  rw [← mul_assoc,swap_mul_self,one_mul]

lemma switch_edge_a_of_ne (a b : D) (hn : M.edge b ≠ a) :
    (M.switch a b).edge a = M.edge b := by
  simp only [switch,mul_apply,swap_apply_left,swap_apply_of_ne_of_ne hn (M.edge_ne b)]

lemma switch_edge_b_of_ne (a b : D) (hn : M.edge a ≠ b) :
    (M.switch a b).edge b = M.edge a := by
  simp only [switch,mul_apply,swap_apply_right,swap_apply_of_ne_of_ne (M.edge_ne a) hn]

lemma vertex_switch_order (a b : D) (hne : b ≠ M.edge a) :
    (M.switch a b).vertex = (M.vertex * swap a b) * swap (M.edge a) (M.edge b) := by
  have hab : a ≠ M.edge b := by
    intro he
    apply hne
    rw [he,M.edge_edge]
  have hdis : (swap (M.edge a) (M.edge b)).Disjoint (swap a b) := by
    apply disjoint_iff_eq_or_eq.mpr
    intro x
    by_cases ha : x = a
    · subst x
      exact Or.inl (swap_apply_of_ne_of_ne (M.edge_ne a).symm hab)
    by_cases hb : x = b
    · subst x
      exact Or.inl (swap_apply_of_ne_of_ne hne (M.edge_ne b).symm)
    exact Or.inr (swap_apply_of_ne_of_ne ha hb)
  rw [M.vertex_switch,mul_assoc,hdis.commute.eq,← mul_assoc]

variable [Fintype D]

/-- Genus-zero is preserved by ANY cross-pairing of two outgoing edges at a
single actual source vertex, even when some far vertex is the same source
vertex. This includes the switches used in elementary disk cancellation.
The radial case is the disjoint-far-vertices special case. -/
theorem switch_genusZero_general (hM : M.GenusZero) (a b : D)
    (hv : M.vertex.SameCycle a b) : (M.switch a b).GenusZero := by
  by_cases heq : a = b
  · subst b
    have hs : M.switch a a = M := by
      apply PictureMap.ext (M := M.switch a a) (N := M) rfl
      change swap a a * M.edge * swap a a = M.edge
      rw [swap_self]
      change (1 : Perm D) * M.edge * 1 = M.edge
      simp only [one_mul,mul_one]
    rwa [hs]
  by_cases hop : b = M.edge a
  · subst b
    rwa [M.switch_opposite]
  have hba : M.edge a ≠ b := Ne.symm hop
  have hab : M.edge b ≠ a := by
    intro he
    apply hop
    have hh := congrArg M.edge he
    simpa only [M.edge_edge] using hh
  let q := M.vertex * swap a b
  have hq : cycles q = cycles M.vertex + 1 := cycles_split_right _ heq hv
  have hnew := M.vertex_switch_order a b hop
  have hC := M.switch_components_card a b hv
  change M.euler = _ at hM
  change (M.switch a b).euler = _
  by_cases hf : q.SameCycle (M.edge a) (M.edge b)
  · have hc := cycles_split_right q (M.edge.injective.ne heq) hf
    have hE : (M.switch a b).euler = M.euler + 2 := by
      simp only [euler,switch_face,hnew]
      change cycles (q * swap (M.edge a) (M.edge b)) + _ - _ = _
      rw [hc,hq]; ring
    have he := (M.switch a b).euler_le
    split_ifs at hC <;> omega
  · have hc := cycles_merge_right q hf
    have hE : (M.switch a b).euler = M.euler := by
      simp only [euler,switch_face,hnew]
      change cycles (q * swap (M.edge a) (M.edge b)) + _ - _ = _
      omega
    have hf' : (M.switch a b).vertex.SameCycle (M.edge a) (M.edge b) := by
      rw [hnew]
      exact sameCycle_after_swap_right q hf
    have h1 : (M.switch a b).components a (M.edge b) := by
      rw [← M.switch_edge_a_of_ne a b hab]
      exact (M.switch a b).edge_le_components SameCycle.rfl.apply_right
    have h2 : (M.switch a b).components b (M.edge a) := by
      rw [← M.switch_edge_b_of_ne a b hba]
      exact (M.switch a b).edge_le_components SameCycle.rfl.apply_right
    have hsame : (M.switch a b).components a b :=
      (M.switch a b).components.trans' h1 ((M.switch a b).components.trans'
        ((M.switch a b).vertex_le_components hf'.symm)
        ((M.switch a b).components.symm' h2))
    rw [ite_eq_left hsame] at hC
    omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SetoidRestrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv
attribute [local instance] Classical.propDecidable
variable {D : Type*}

/-- For invariant subsets, taking the join of equivalence relations commutes
with restriction. The invariant hypothesis is essential. -/
theorem comap_sup_of_invariant (r s : Setoid D) (P : D → Prop)
    (hr : ∀ {x y}, r x y → (P x ↔ P y))
    (hs : ∀ {x y}, s x y → (P x ↔ P y)) :
    (r ⊔ s).comap (Subtype.val : Subtype P → D) =
      r.comap Subtype.val ⊔ s.comap Subtype.val := by
  classical
  let t : Setoid (Subtype P) := r.comap Subtype.val ⊔ s.comap Subtype.val
  let f : D → Option (Quotient t) := fun x => if h : P x then some (Quotient.mk t ⟨x,h⟩) else none
  have hf : ∀ (u : Setoid D), (∀ {x y}, u x y → (P x ↔ P y)) →
      u.comap (Subtype.val : Subtype P → D) ≤ t → u ≤ Setoid.ker f := by
    intro u hu ht x y hxy
    change f x = f y
    by_cases hx : P x
    · have hy := (hu hxy).mp hx
      simp only [f,dite_eq_left hx,dite_eq_left hy]
      exact congrArg some (Quotient.sound (ht hxy))
    · have hy : ¬ P y := fun hy => hx ((hu hxy).mpr hy)
      simp only [f,dite_eq_right hx,dite_eq_right hy]
  have hjoin : r ⊔ s ≤ Setoid.ker f := sup_le (hf r hr le_sup_left) (hf s hs le_sup_right)
  apply le_antisymm
  · intro x y hxy
    have he := hjoin hxy
    change f x.val = f y.val at he
    simp only [f,dite_eq_left x.property,dite_eq_left y.property,Option.some.injEq] at he
    exact Quotient.exact he
  · apply sup_le
    · intro x y hxy; exact (le_sup_left : r ≤ r ⊔ s) hxy
    · intro x y hxy; exact (le_sup_right : s ≤ r ⊔ s) hxy

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureRestrict
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

omit [DecidableEq D] in
lemma invariant_of_sameCycle {P : D → Prop} (p : Perm D)
    (hp : ∀ x, P (p x) ↔ P x) {a b : D} (hab : p.SameCycle a b) : P a ↔ P b := by
  have hh : SameCycle.setoid p ≤ Setoid.ker P :=
    sameCycle_le_of_apply (fun x => propext (hp x).symm)
  exact Iff.of_eq (hh hab)

lemma cycles_subtype_split {P : D → Prop} (p : Perm D)
    (hp : ∀ x, P (p x) ↔ P x) :
    cycles p = cycles (p.subtypePerm hp) +
      cycles (p.subtypePerm (p := fun x => ¬ P x) (fun x => not_congr (hp x))) := by
  have hc := card_quotient_split (SameCycle.setoid p) P (invariant_of_sameCycle p hp)
  have he (Q : D → Prop) (hQ : ∀ x, Q (p x) ↔ Q x) :
      Nat.card (Quotient ((SameCycle.setoid p).comap (Subtype.val : Subtype Q → D))) =
        Nat.card (Quotient (SameCycle.setoid (p.subtypePerm hQ))) := by
    exact Nat.card_congr (Quotient.congrRight (fun a b => (sameCycle_subtypePerm_iff p hQ a b).symm))
  rw [he P hp,he (fun x => ¬ P x) (fun x => not_congr (hp x))] at hc
  simp only [cycles_eq_card_classes]
  exact_mod_cast hc


end HyperbolicObstruction.PictureSwitch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureMapFurther
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
variable {D : Type*} [Fintype D]

namespace PictureMap
variable (M : PictureMap D) (P : D → Prop)

/-- A union of whole polygonal components can be kept, discarding the others.
This is a literal restriction of both permutations. -/
def restrict (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    PictureMap (Subtype P) where
  face := M.face.subtypePerm hf
  edge := M.edge.subtypePerm he
  edge_sq := by
    ext x
    exact M.edge_edge x.val
  edge_ne := by
    intro x hx
    exact M.edge_ne x.val (congrArg Subtype.val hx)

omit [Fintype D] in
lemma restrict_vertex (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    (M.restrict P hf he).vertex = M.vertex.subtypePerm (fun x => (hf (M.edge x)).trans (he x)) := by
  ext x
  rfl

lemma restrict_components (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    (M.restrict P hf he).components = M.components.comap (Subtype.val : Subtype P → D) := by
  rw [components,restrict_vertex,components]
  have hv : ∀ x, P (M.vertex x) ↔ P x := fun x => (hf (M.edge x)).trans (he x)
  rw [comap_sup_of_invariant _ _ P (invariant_of_sameCycle M.vertex hv)
    (invariant_of_sameCycle M.edge he)]
  congr 1
  · ext x y
    exact sameCycle_subtypePerm_iff M.vertex hv x y
  · ext x y
    exact sameCycle_subtypePerm_iff M.edge he x y

lemma component_invariant (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x)
    {x y : D} (h : M.components x y) : P x ↔ P y := by
  have hh : M.components ≤ Setoid.ker P :=
    M.components_le (fun x => propext (hf x).symm) (fun x => propext (he x).symm)
  exact Iff.of_eq (hh h)

lemma components_split (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    Nat.card (Quotient M.components) =
      Nat.card (Quotient (M.restrict P hf he).components) +
      Nat.card (Quotient (M.restrict (fun x => ¬ P x)
        (fun x => not_congr (hf x)) (fun x => not_congr (he x))).components) := by
  rw [restrict_components,restrict_components]
  exact card_quotient_split M.components P (M.component_invariant P hf he)

variable [DecidableEq D]

lemma card_darts_even (M : PictureMap D) : ∃ n : ℤ, (Fintype.card D : ℤ) = 2*n := by
  obtain ⟨l,_,hc,_⟩ := involution_pairs M.edge M.edge_sq
  have hs : M.edge.support = Finset.univ := by ext x; simp [mem_support,M.edge_ne]
  rw [hs,Finset.card_univ] at hc
  exact ⟨l.length,by exact_mod_cast hc.symm⟩

/-- The Euler characteristic is additive over actual invariant dart subsets. -/
theorem euler_split (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    M.euler = (M.restrict P hf he).euler + (M.restrict (fun x => ¬ P x)
      (fun x => not_congr (hf x)) (fun x => not_congr (he x))).euler := by
  have hc := Fintype.card_congr (Equiv.sumCompl P)
  rw [Fintype.card_sum] at hc
  obtain ⟨n,hn⟩ := (M.restrict P hf he).card_darts_even
  obtain ⟨m,hm⟩ := (M.restrict (fun x => ¬ P x)
    (fun x => not_congr (hf x)) (fun x => not_congr (he x))).card_darts_even
  have hv := cycles_subtype_split M.vertex (fun x => (hf (M.edge x)).trans (he x))
  have hface := cycles_subtype_split M.face hf
  simp only [euler]
  rw [M.restrict_vertex P hf he,M.restrict_vertex (fun x => ¬ P x)
    (fun x => not_congr (hf x)) (fun x => not_congr (he x))]
  dsimp only [restrict]
  have hc' : (Fintype.card D : ℤ) = Fintype.card (Subtype P) + Fintype.card {x : D // ¬ P x} := by
    exact_mod_cast hc.symm
  omega

/-- Discarding components of a genus-zero picture preserves genus zero. This
justifies keeping the disk component and deleting sphere components after
crosswise switches, at the level of the actual finite side-pairing. -/
theorem restrict_genusZero (hM : M.GenusZero)
    (hf : ∀ x, P (M.face x) ↔ P x) (he : ∀ x, P (M.edge x) ↔ P x) :
    (M.restrict P hf he).GenusZero := by
  have hE := M.euler_split P hf he
  have hC := M.components_split P hf he
  have h₁ := (M.restrict P hf he).euler_le
  have h₂ := (M.restrict (fun x => ¬ P x)
    (fun x => not_congr (hf x)) (fun x => not_congr (he x))).euler_le
  change M.euler = _ at hM
  change (M.restrict P hf he).euler = _
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeCellTarget
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
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma row_extend (r : Row) (l : rowSupport r → Alphabet n) :
    TableModel.row rowSupport (extendRow n r l) r = ⟨r,l⟩ := by
  change (⟨r, fun f => extendRow n r l f.val⟩ : TableModel.Entry (A := Alphabet n) rowSupport) = ⟨r,l⟩
  congr 1
  funext f
  simp [extendRow,f.property]

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Occurrence
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace Occurrences

abbrev Entry (A : Type*) := TableModel.Entry (A := A) rowSupport ⊕ (Fin 6 → A)


end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FaceSplice
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

/-- Splicing oriented boundary polygons at their outgoing corners. This is
connected sum at the outside faces when the two corners are in distinct
components; no edge or side map is changed. -/
def splice (a b : D) : PictureMap D where
  face := M.face * swap a b
  edge := M.edge
  edge_sq := M.edge_sq
  edge_ne := M.edge_ne

omit [Fintype D] in
lemma splice_vertex (a b : D) :
    (M.splice a b).vertex = M.vertex * swap (M.edge a) (M.edge b) := by
  rw [vertex,splice,vertex]
  have h : swap a b * M.edge = M.edge * swap (M.edge a) (M.edge b) := by
    rw [mul_swap_eq_swap_mul,M.edge_edge,M.edge_edge]
  rw [mul_assoc,h,← mul_assoc]

lemma splice_components_le (a b : D) :
    (M.splice a b).components ≤ glue M.components a b := by
  let s := glue M.components a b
  have hs : M.components ≤ s := le_glue _ _ _
  have ht : ∀ x, s x (swap a b x) := fun x =>
    sameCycle_swap_le (glue_pair _ a b) SameCycle.rfl.apply_right
  apply (M.splice a b).components_le
  · intro x
    exact s.trans' (ht x) (hs (M.face_le_components (SameCycle.rfl (x := swap a b x)).apply_right))
  · intro x
    exact hs (M.edge_le_components SameCycle.rfl.apply_right)

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FaceSplit
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

lemma components_le_glue_splice (a b : D) :
    M.components ≤ glue (M.splice a b).components a b := by
  let s := glue (M.splice a b).components a b
  have hs : (M.splice a b).components ≤ s := le_glue _ _ _
  have ht : ∀ x, s x (swap a b x) := fun x =>
    sameCycle_swap_le (glue_pair _ a b) SameCycle.rfl.apply_right
  apply M.components_le
  · intro x
    have hf := hs ((M.splice a b).face_le_components (SameCycle.rfl (x := swap a b x)).apply_right)
    have he : (M.splice a b).face (swap a b x) = M.face x := by simp [splice]
    rw [he] at hf
    exact s.trans' (ht x) hf
  · intro x
    exact hs ((M.splice a b).edge_le_components SameCycle.rfl.apply_right)

lemma split_components_glue (a b : D) (hf : M.face.SameCycle a b) :
    glue (M.splice a b).components a b = M.components := by
  have hab : M.components a b := M.face_le_components hf
  have hnew : (M.splice a b).components ≤ M.components := by
    have h := M.splice_components_le a b
    rwa [glue_eq_of_rel _ _ _ hab] at h
  exact le_antisymm (glue_le _ _ _ hnew hab) (M.components_le_glue_splice a b)

lemma split_components_card (a b : D) (hf : M.face.SameCycle a b) :
    (Nat.card (Quotient (M.splice a b).components) : ℤ) =
      Nat.card (Quotient M.components) +
        if (M.splice a b).components a b then 0 else 1 := by
  have h := card_glue (M.splice a b).components a b
  rw [M.split_components_glue a b hf] at h
  omega

/-- Split a face at ANY two of its corners, identifying their endpoint
regions. Neither an embedded boundary nor distinct source endpoints is
required. If the endpoints were already equal the affected sphere can
split into two; otherwise the number of components is unchanged. -/
theorem split_genusZero (hM : M.GenusZero) (a b : D)
    (hne : a ≠ b) (hf : M.face.SameCycle a b) : (M.splice a b).GenusZero := by
  have hF := cycles_split_right M.face hne hf
  have hC := M.split_components_card a b hf
  have hV := M.splice_vertex a b
  change M.euler = _ at hM
  change (M.splice a b).euler = _
  by_cases hv : M.vertex.SameCycle (M.edge a) (M.edge b)
  · have hc := cycles_split_right M.vertex (M.edge.injective.ne hne) hv
    have hE : (M.splice a b).euler = M.euler + 2 := by
      rw [euler,euler,hV]
      change cycles (M.vertex * swap (M.edge a) (M.edge b)) + cycles (M.face * swap a b) - _ = _
      rw [hc,hF]; ring
    have he := (M.splice a b).euler_le
    split_ifs at hC <;> omega
  · have hc := cycles_merge_right M.vertex hv
    have hE : (M.splice a b).euler = M.euler := by
      rw [euler,euler,hV]
      change cycles (M.vertex * swap (M.edge a) (M.edge b)) + cycles (M.face * swap a b) - _ = _
      omega
    have hv' : (M.splice a b).vertex.SameCycle (M.edge a) (M.edge b) := by
      rw [hV]
      exact sameCycle_after_swap_right M.vertex hv
    have hsame : (M.splice a b).components a b := by
      apply (M.splice a b).components.trans' ((M.splice a b).edge_le_components (SameCycle.rfl (x := a)).apply_right)
      exact (M.splice a b).components.trans' ((M.splice a b).vertex_le_components hv')
        ((M.splice a b).components.symm' ((M.splice a b).edge_le_components (SameCycle.rfl (x := b)).apply_right))
    rw [ite_eq_left hsame] at hC
    omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermErase
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
variable {D : Type*} [DecidableEq D]

lemma sameCycle_setoid_merge_left [Fintype D] (p : Perm D) {a b : D}
    (h : ¬ p.SameCycle a b) :
    SameCycle.setoid (swap a b * p) = glue (SameCycle.setoid p) a b := by
  let q := swap a b * p
  have hq : q.SameCycle a b := sameCycle_after_swap p h
  have hle : SameCycle.setoid p ≤ SameCycle.setoid q := by
    apply sameCycle_le_of_apply
    intro x
    have ht : SameCycle.setoid q (q x) (swap a b (q x)) :=
      sameCycle_swap_le hq SameCycle.rfl.apply_right
    have he : swap a b (q x) = p x := by simp [q]
    rw [he] at ht
    exact SameCycle.rfl.apply_right.trans ht
  apply le_antisymm
  · exact sameCycle_mul_le (sameCycle_swap_le (glue_pair _ a b)) (le_glue _ a b)
  · exact glue_le _ a b hle hq

variable [Fintype D]

lemma bypass_orbits (p : Perm D) (a x y : D) (hx : x ≠ a) (hy : y ≠ a) :
    (bypass p a).SameCycle x y ↔ p.SameCycle x y := by
  by_cases ha : p a = a
  · simp only [bypass,ha,swap_self,← Equiv.Perm.one_def,one_mul]
  · have hq : ¬ (bypass p a).SameCycle (p a) a := by
      intro h
      exact ha (h.eq_of_right (bypass_fixed p a))
    have hmerge := sameCycle_setoid_merge_left (bypass p a) hq
    have he : swap (p a) a * bypass p a = p := by
      rw [bypass,swap_comm (p a) a,← mul_assoc,swap_mul_self,one_mul]
    rw [he] at hmerge
    have hxa : ¬ (bypass p a).SameCycle x a := fun h => hx (h.eq_of_right (bypass_fixed p a))
    have hya : ¬ (bypass p a).SameCycle y a := fun h => hy (h.eq_of_right (bypass_fixed p a))
    change SameCycle.setoid (bypass p a) x y ↔ SameCycle.setoid p x y
    rw [hmerge,glue_iff]
    have hxq : ¬ (SameCycle.setoid (bypass p a)) x a := hxa
    have hyq : ¬ (SameCycle.setoid (bypass p a)) y a := hya
    simp only [hxq,hyq,ite_false,Quotient.eq]

lemma bypass_cycles (p : Perm D) (a : D) :
    cycles (bypass p a) = cycles p + if p a = a then 0 else 1 := by
  by_cases h : p a = a
  · simp only [bypass,h,swap_self,← Equiv.Perm.one_def,one_mul,ite_eq_left,add_zero]
  · rw [ite_eq_right h,bypass]
    exact cycles_split p (Ne.symm h) SameCycle.rfl.apply_right

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermErasePair
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

variable [DecidableEq D]

lemma bypass_keeps_fixed (p : Perm D) {a b : D} (hab : a ≠ b) (hb : p b = b) :
    bypass p a b = b := by
  rw [bypass_away p a b hab.symm,hb,ite_eq_right hab.symm]

lemma bypassPair_a (p : Perm D) {a b : D} (hab : a ≠ b) : bypassPair p a b a = a :=
  bypass_keeps_fixed (bypass p a) hab.symm (bypass_fixed p a)

def erasePair (p : Perm D) {a b : D} (hab : a ≠ b) : Perm {x // OffPair a b x} :=
  (bypassPair p a b).subtypePerm (offPair_invariant (bypassPair_a p hab) (bypassPair_b p a b))

variable [Fintype D]

lemma erasePair_orbits (p : Perm D) {a b : D} (hab : a ≠ b)
    (x y : {x // OffPair a b x}) :
    (erasePair p hab).SameCycle x y ↔ p.SameCycle x.val y.val := by
  rw [erasePair,sameCycle_subtypePerm]
  change (bypass (bypass p a) b).SameCycle x.val y.val ↔ _
  rw [bypass_orbits _ _ _ _ x.property.2 y.property.2,
    bypass_orbits _ _ _ _ x.property.1 y.property.1]

lemma erasePair_cycles (p : Perm D) {a b : D} (hab : a ≠ b)
    (ha : p a ≠ a) (hb : bypass p a b ≠ b) : cycles (erasePair p hab) = cycles p := by
  let q := bypassPair p a b
  have hqA : q a = a := bypassPair_a p hab
  have hqB : q b = b := bypassPair_b p a b
  let s := q.subtypePerm (p := fun x => ¬ OffPair a b x)
    (fun x => not_congr (offPair_invariant hqA hqB x))
  have hc : cycles q = cycles (erasePair p hab) + cycles s := by
    simpa only [cycles_eq_card_classes,erasePair,q,s] using
      (cycles_subtype_split (P := OffPair a b) q (offPair_invariant hqA hqB))
  have hs : s = 1 := by
    ext x
    change q x.val = x.val
    have hx : x.val = a ∨ x.val = b := by
      have hh := x.property
      unfold OffPair at hh
      tauto
    rcases hx with hx|hx
    · rw [hx,hqA]
    · rw [hx,hqB]
  have hcard : Fintype.card {x : D // ¬ OffPair a b x} = 2 := by
    rw [Fintype.card_of_subtype ({a,b} : Finset D) (by intro x; simp only [Finset.mem_insert,Finset.mem_singleton,OffPair]; tauto)]
    simp [hab]
  have hsC : cycles s = 2 := by rw [hs]; simp [cycles,defect,hcard]
  have hqC : cycles q = cycles p + 2 := by
    change cycles (bypass (bypass p a) b) = _
    rw [bypass_cycles,bypass_cycles,ite_eq_right hb,ite_eq_right ha]
    omega
  rw [hsC,hqC] at hc
  omega

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BigonRemove
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

structure Bigon (a b : D) : Prop where
  ne : a ≠ b
  forward : M.face a = b
  backward : M.face b = a

namespace Bigon
variable (h : M.Bigon a b)
include h

lemma face_invariant (x : D) : OffPair a b (M.face x) ↔ OffPair a b x := by
  have h₁ : M.face x = a ↔ x = b := by rw [← h.backward]; exact M.face.apply_eq_iff_eq
  have h₂ : M.face x = b ↔ x = a := by rw [← h.forward]; exact M.face.apply_eq_iff_eq
  simp only [OffPair,ne_eq,h₁,h₂,and_comm]

lemma switching_vertex : M.vertex.SameCycle a (M.edge b) := by
  have hh : M.vertex (M.edge b) = a := by rw [vertex,mul_apply,M.edge_edge,h.backward]
  exact (hh ▸ (SameCycle.rfl (x := M.edge b)).apply_right).symm

variable [DecidableEq D]

lemma switched_pair : (M.switch a (M.edge b)).edge a = b := by
  change swap a (M.edge b) (M.edge (swap a (M.edge b) a)) = b
  rw [swap_apply_left,M.edge_edge,swap_apply_of_ne_of_ne h.ne.symm (M.edge_ne b).symm]

lemma switched_back : (M.switch a (M.edge b)).edge b = a := by
  have hh := congrArg (M.switch a (M.edge b)).edge h.switched_pair
  simpa only [edge_edge] using hh.symm

lemma edge_invariant (x : D) : OffPair a b ((M.switch a (M.edge b)).edge x) ↔ OffPair a b x := by
  have h₁ : (M.switch a (M.edge b)).edge x = a ↔ x = b := by
    simpa only [h.switched_back] using ((M.switch a (M.edge b)).edge.apply_eq_iff_eq (x := x) (y := b))
  have h₂ : (M.switch a (M.edge b)).edge x = b ↔ x = a := by
    simpa only [h.switched_pair] using ((M.switch a (M.edge b)).edge.apply_eq_iff_eq (x := x) (y := a))
  simp only [OffPair,ne_eq,h₁,h₂,and_comm]

/-- The zero-chain backtracking bigon is first pinched off by a legal vertex
switch and then deleted as a whole component. Its other edge contacts need
not initially meet one another. -/
def remove : PictureMap {x // OffPair a b x} :=
  (M.switch a (M.edge b)).restrict (OffPair a b) h.face_invariant h.edge_invariant

lemma remove_genusZero [Fintype D] (hG : M.GenusZero) : h.remove.GenusZero := by
  exact (M.switch a (M.edge b)).restrict_genusZero (OffPair a b)
    (M.switch_genusZero_general hG a (M.edge b) h.switching_vertex)
    h.face_invariant h.edge_invariant

lemma remove_respects {L V : Type*} {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) (hab : label a = rev (label b)) :
    h.remove.Respects (label ∘ Subtype.val) start rev := by
  have hs := switch_respects hM (a := a) (b := M.edge b) (hab.trans (hM.2 b).symm)
  exact ⟨fun x => hs.1 x.val,fun x => hs.2 x.val⟩

end Bigon
end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FanApex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink
open State

/-- Combinatorial data at ONE fan occurrence in a fragment of a normalized
picture. `S` indexes all selected top faces whose occurrence has this fan slot,
including top faces that do not actually turn at this fan. The injectivity
condition is that a simple macro polygon turns at a fan at most once. -/
structure FanData (r S o : ℕ) where
  n : Fin r → ℕ
  next : (z : Fin r) → Equiv.Perm (Fin (n z))
  cyclic : ∀ z, IsCyclic (next z)
  mark : (z : Fin r) → Fin (n z) → Mark (Fin S)
  line : (z : Fin r) → Fin (n z) → Bool
  occurrence : Fin S → Fin o
  represented : ∀ z, ∃ i, mark z i ≠ .absent
  card_le : ∀ z, n z ≤ 5
  no_fixed : ∀ z i, next z i ≠ i
  bipartite : ∀ z i, mark z i = .triangle → line z i ≠ line z (next z i)
  no_backtrack : ∀ z i, mark z i = .triangle → mark z (next z i) = .triangle →
    next z (next z i) ≠ i
  no_same_side : ∀ z i f g, mark z i = .top f → mark z (next z i) = .top g →
    occurrence f ≠ occurrence g
  unique_turn : ∀ (p q : Σ z, Fin (n z)) f,
    mark p.1 p.2 = .top f → mark q.1 q.2 = .top f → p = q

namespace FanData
variable {r S o : ℕ} (L : FanData r S o)

def isPartial (z : Fin r) : Prop := ∃ i, L.mark z i = .absent
instance partialDecidable (z : Fin r) : Decidable (L.isPartial z) := inferInstanceAs (Decidable (∃ i, L.mark z i = .absent))
def partialCount : ℕ := ∑ z, if L.isPartial z then 1 else 0

def multiplicity (a : Fin o) : ℕ := Fintype.card {f : Fin S // L.occurrence f = a}
def maxMultiplicity : ℕ := Finset.univ.sup L.multiplicity
def weight : ℕ := max r L.maxMultiplicity

lemma count_le (R : Fin S → Prop) [DecidablePred R] :
    (∑ z, ∑ i, match L.mark z i with
      | .top f => if R f then (1:ℕ) else 0
      | _ => 0) ≤ Fintype.card {f : Fin S // R f} := by
  classical
  let Idx := {p : Σ z, Fin (L.n z) // ∃ f, L.mark p.1 p.2 = .top f ∧ R f}
  let g : Idx → {f : Fin S // R f} := fun p =>
    ⟨p.property.choose,p.property.choose_spec.2⟩
  have hg : Function.Injective g := by
    intro p q hpq
    apply Subtype.ext
    apply L.unique_turn p.val q.val p.property.choose p.property.choose_spec.1
    have hval := congrArg Subtype.val hpq
    change p.property.choose = q.property.choose at hval
    rw [hval]
    exact q.property.choose_spec.1
  have h := Fintype.card_le_of_injective g hg
  have hcard : Fintype.card Idx = (∑ z, ∑ i, match L.mark z i with
      | .top f => if R f then (1:ℕ) else 0
      | _ => 0) := by
    rw [show Fintype.card Idx = _ from Fintype.card_subtype _]
    have hh := Finset.sum_boole (R := ℕ)
      (fun p : Σ z, Fin (L.n z) => ∃ f, L.mark p.1 p.2 = .top f ∧ R f) Finset.univ
    simp only [Nat.cast_id] at hh
    rw [← hh,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro i _
    cases L.mark z i <;> simp
  rwa [hcard] at h

lemma multiplicity_le (a : Fin o) : L.multiplicity a ≤ S := by
  simpa [multiplicity] using (Fintype.card_le_of_injective
    (Subtype.val : {f : Fin S // L.occurrence f = a} → Fin S) Subtype.val_injective)

end FanData
end HyperbolicObstruction.FanLink
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureVertexBoundary
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
variable {X : Type*} (P : PictureMap X)
variable (apex selected : X → Bool) (radial : X → Prop)
variable (hface : ∀ x, selected (P.face x) = selected x)
  (hvertex : ∀ x, apex (P.vertex⁻¹ x) = apex x)
  (hrev : ∀ x, apex x = true → apex (P.edge x) = false)
  (hradial : ∀ x, apex x = true → radial x)
  (hedge : ∀ x, radial (P.edge x) ↔ radial x)

abbrev VertexTransition := {x : X // apex x = true ∧ selected x ≠ selected (P.vertex⁻¹ x)}

def transitionSide (x : P.VertexTransition apex selected) : X :=
  if selected x.val then P.edge (P.vertex⁻¹ x.val) else P.vertex⁻¹ x.val

lemma edge_previous_face (x : X) : P.face (P.edge (P.vertex⁻¹ x)) = x := by
  exact P.vertex.apply_symm_apply x

include hface in
lemma transition_previous_selected (x : X) : selected (P.edge (P.vertex⁻¹ x)) = selected x := by
  rw [← hface (P.edge (P.vertex⁻¹ x)),P.edge_previous_face]

include hface hvertex hradial hedge in
lemma transitionSide_properties (x : P.VertexTransition apex selected) :
    radial (P.transitionSide apex selected x) ∧
      selected (P.transitionSide apex selected x) = true ∧
      selected (P.edge (P.transitionSide apex selected x)) ≠ true := by
  have ha : apex (P.vertex⁻¹ x.val) = true := (hvertex _).trans x.property.1
  have hr : radial (P.vertex⁻¹ x.val) := hradial _ ha
  have he := P.transition_previous_selected selected hface x.val
  have hn := x.property.2
  unfold transitionSide
  cases hs : selected x.val with
  | true =>
    simp only [ite_true]
    refine ⟨(hedge _).mpr hr,he.trans hs,?_⟩
    rw [P.edge_edge]
    exact fun h => hn (hs.trans h.symm)
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    have hy : selected (P.vertex⁻¹ x.val) = true := by
      cases hh : selected (P.vertex⁻¹ x.val)
      · exact False.elim (hn (hs.trans hh.symm))
      · rfl
    exact ⟨hr,hy,by rw [he,hs]; decide⟩

include hvertex hrev in
lemma transitionSide_recover (x : P.VertexTransition apex selected) :
    (if apex (P.transitionSide apex selected x) then P.transitionSide apex selected x
      else P.edge (P.transitionSide apex selected x)) = P.vertex⁻¹ x.val := by
  have ha : apex (P.vertex⁻¹ x.val) = true := (hvertex _).trans x.property.1
  have hb := hrev _ ha
  unfold transitionSide
  cases selected x.val <;> simp only [Bool.false_eq_true,ite_true,ite_false,ha,hb,P.edge_edge]

include hvertex hrev in
lemma transitionSide_injective : Function.Injective (P.transitionSide apex selected) := by
  intro x y he
  have h := congrArg (fun z => if apex z then z else P.edge z) he
  rw [P.transitionSide_recover apex selected hvertex hrev,
    P.transitionSide_recover apex selected hvertex hrev] at h
  exact Subtype.ext ((P.vertex⁻¹).injective h)

variable [Fintype X]

include hface hvertex hrev hradial hedge in
/-- Every change of selection at an apex link charges a distinct actual
radial boundary side. The two orientations are handled by the unique apex end. -/
theorem vertex_transitions_le_boundary : Fintype.card (P.VertexTransition apex selected) ≤
    Fintype.card (P.BoundarySide (fun x => selected x = true) radial) := by
  let g : P.VertexTransition apex selected → P.BoundarySide (fun x => selected x = true) radial :=
    fun x => ⟨P.transitionSide apex selected x,
      P.transitionSide_properties apex selected radial hface hvertex hradial hedge x⟩
  apply Fintype.card_le_of_injective g
  intro x y h
  exact P.transitionSide_injective apex selected hvertex hrev (congrArg Subtype.val h)

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRadialBoundary
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

def walkApex (x : P.Dart) := isApex n w (start n w (walkLabel n w d (P.index x)))

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTriangleTransport
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
variable (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced)
  (hrad : P.RadialInjective (isApex n w))

abbrev SelectedTriangleFace := {F : P.Face // select F = true ∧
  ∃ g : FanTriangle n w, P.faceKind F = .inr (.inl g)}

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualFaceCounts
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

abbrev SelectedFace := {F : P.Face // select F = true}
noncomputable instance instFintypeSelectedFace : Fintype (SelectedFace n w d c hc f P select) := Fintype.ofFinite _

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualLabel
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma square_value_congr {q q' : Square n w} (h : q = q') (v : Field)
    (h1 : v ∈ rowSupport (.inr (.inr q.1))) (h2 : v ∈ rowSupport (.inr (.inr q'.1))) :
    q.2.val ⟨v,h1⟩ = q'.2.val ⟨v,h2⟩ := by
  cases h
  rfl

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BFSTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*}

variable [Fintype V]

/-- A literal shortest-path spanning tree of a finite connected graph.
Root distances are preserved exactly, not merely bounded by the number of
vertices. This is the radius-control input for the planar separator. -/
theorem exists_bfs_tree (G : SimpleGraph V) (hG : G.Connected) (root : V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ ∀ v, T.dist root v = G.dist root v := by
  classical
  have : Nonempty V := ⟨root⟩
  let parent : V → V := fun v => if h : v = root then root else
    (exists_distance_parent G hG root v h).choose
  have hp : ∀ v, v ≠ root → G.Adj v (parent v) ∧
      G.dist root (parent v)+1 = G.dist root v := by
    intro v hv
    dsimp only [parent]
    rw [dite_eq_right hv]
    exact (exists_distance_parent G hG root v hv).choose_spec
  let T : SimpleGraph V := {
    Adj := fun v w => (v ≠ root ∧ parent v = w) ∨ (w ≠ root ∧ parent w = v)
    symm := ⟨by intro v w h; exact h.elim Or.inr Or.inl⟩
    loopless := ⟨by
      intro v h
      rcases h with ⟨hv,he⟩ | ⟨hv,he⟩ <;>
        exact (hp v hv).1.ne he.symm⟩ }
  have hle : T ≤ G := by
    intro v w h
    rcases h with ⟨hv,rfl⟩ | ⟨hw,rfl⟩
    · exact (hp v hv).1
    · exact (hp w hw).1.symm
  have hpaths : ∀ v, ∃ p : T.Walk v root, p.length = G.dist root v := by
    intro v
    generalize hn : G.dist root v = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = root
      · subst v
        exact ⟨.nil,by simpa only [Walk.length_nil,SimpleGraph.dist_self] using hn⟩
      · have hd := (hp v hv).2
        obtain ⟨p,hp'⟩ := ih (G.dist root (parent v)) (by omega) (parent v) rfl
        exact ⟨p.cons (Or.inl ⟨hv,rfl⟩),by simp only [Walk.length_cons,hp']; omega⟩
  have hconn : T.Connected := by
    apply Connected.mk
    intro v w
    exact (show T.Reachable v root from ⟨(hpaths v).choose⟩).trans
      (show T.Reachable w root from ⟨(hpaths w).choose⟩).symm
  have hcard : Nat.card T.edgeSet + 1 ≤ Nat.card V := by
    let E := (Finset.univ.erase root).image (fun v => s(v,parent v))
    have hsub : T.edgeFinset ⊆ E := by
      intro e he
      induction e using Sym2.inductionOn with
      | hf v w =>
        have hadj : T.Adj v w := by simpa using he
        rcases hadj with ⟨hv,rfl⟩ | ⟨hw,rfl⟩
        · exact Finset.mem_image.mpr ⟨v,Finset.mem_erase.mpr ⟨hv,Finset.mem_univ _⟩,rfl⟩
        · exact Finset.mem_image.mpr ⟨w,Finset.mem_erase.mpr ⟨hw,Finset.mem_univ _⟩,Sym2.eq_swap⟩
    have hh := (Finset.card_le_card hsub).trans (Finset.card_image_le (s := Finset.univ.erase root)
      (f := fun v => s(v,parent v)))
    have he : (Finset.univ.erase root).card + 1 = Fintype.card V := by
      have hh : 0 < Fintype.card V := Fintype.card_pos
      simp only [Finset.card_erase_of_mem (Finset.mem_univ root),Finset.card_univ]
      omega
    rw [edgeFinset_card] at hh
    simp only [Nat.card_eq_fintype_card]
    omega
  have hT : T.IsTree := by
    apply isTree_iff_connected_and_card.mpr
    exact ⟨hconn,Nat.le_antisymm hcard hconn.card_vert_le_card_edgeSet_add_one⟩
  refine ⟨T,hle,hT,?_⟩
  intro v
  apply le_antisymm
  · obtain ⟨p,hp'⟩ := hpaths v
    simpa only [T.dist_comm (u := v) (v := root),hp'] using dist_le p
  · exact (hconn root v).dist_anti hle

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryList
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
variable {D : Type*} [DecidableEq D]

namespace IsBoundary
variable {f : Perm D} {xs : List D} (h : IsBoundary f xs)
include h

lemma invariant {x : D} (hx : x ∈ xs) : f x ∈ xs := by
  rw [h.turn x hx]
  exact List.formPerm_apply_mem_of_mem hx

lemma iterate {x : D} (hx : x ∈ xs) (k : ℕ) :
    (f^k) x = (xs.formPerm^k) x := by
  have hk : ∀ i : ℕ, (xs.formPerm^i) x ∈ xs := by
    intro i
    induction i with
    | zero => exact hx
    | succ i ih =>
      rw [pow_succ',mul_apply]
      exact List.formPerm_apply_mem_of_mem ih
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',mul_apply,ih,h.turn _ (hk k),pow_succ',mul_apply]

lemma sameCycle {x y : D} (hx : x ∈ xs) (hy : y ∈ xs) : f.SameCycle x y := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hy
  have h0 : 0 < xs.length := by omega
  have hs : ∀ j (hj : j < xs.length), f.SameCycle xs[0] xs[j] := by
    intro j hj
    have he : (f^j) xs[0] = xs[j] := by
      rw [h.iterate (List.getElem_mem h0),List.formPerm_pow_apply_getElem _ h.nodup]
      simp only [Nat.zero_add,Nat.mod_eq_of_lt hj]
    exact he ▸ (SameCycle.rfl (f := f) (x := xs[0])).pow_right
  exact (hs i hi).symm.trans (hs j hj)

lemma mem_of_sameCycle {x y : D} (hx : x ∈ xs) (hxy : f.SameCycle x y) : y ∈ xs := by
  have hinv : ∀ z, f z ∈ xs ↔ z ∈ xs := by
    intro z
    constructor
    · intro hz
      have hh : xs.formPerm⁻¹ (f z) ∈ xs := by
        apply List.mem_of_formPerm_apply_mem
        simpa only [Perm.inv_def,Equiv.apply_symm_apply] using hz
      have he := h.turn _ hh
      simp only [Perm.inv_def,Equiv.apply_symm_apply] at he
      have he' : xs.formPerm⁻¹ (f z) = z := f.injective he
      rwa [he'] at hh
    · exact h.invariant
  obtain ⟨k,rfl⟩ := hxy
  have hmap : ∀ z, decide (f z ∈ xs) = decide (z ∈ xs) := fun z => by simp only [hinv z]
  have he := semiconj_perm_zpow (t := (1 : Perm Bool)) (j := fun z => decide (z ∈ xs)) hmap k x
  simpa only [one_zpow,one_apply,show decide (x ∈ xs) = true from decide_eq_true hx,decide_eq_true_eq] using he

lemma disjoint {ys : List D} (hg : IsBoundary f ys) {x y : D}
    (hx : x ∈ xs) (hy : y ∈ ys) (hne : ¬ f.SameCycle x y) :
    ∀ z ∈ xs, z ∉ ys := by
  intro z hz hzy
  exact hne ((h.sameCycle hx hz).trans (hg.sameCycle hzy hy))

lemma map {E : Type*} [DecidableEq E] {g : Perm E} (j : D → E)
    (hj : Function.Injective j) (hc : ∀ x, j (f x) = g (j x)) :
    IsBoundary g (xs.map j) := by
  refine ⟨h.nodup.map hj,?_⟩
  intro y hy
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
  rw [← hc,h.turn x hx,formPerm_map_apply j hj]

end IsBoundary
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryEnumeration
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

/-- Every finite face orbit has a literal nonempty boundary enumeration,
including monogons (which Perm.toList alone omits). -/
theorem exists_boundary (p : Perm D) (a : D) :
    ∃ xs, IsBoundary p xs ∧ a ∈ xs := by
  by_cases ha : p a = a
  · refine ⟨[a],⟨by simp,?_⟩,by simp⟩
    intro x hx
    have he : x = a := by simpa only [List.mem_singleton] using hx
    subst x
    simpa only [List.formPerm_singleton,one_apply] using ha
  · have has : a ∈ p.support := mem_support.mpr ha
    refine ⟨p.toList a,⟨p.nodup_toList a,?_⟩,mem_toList_iff.mpr ⟨SameCycle.rfl,has⟩⟩
    intro x hx
    rw [formPerm_toList]
    rw [cycleOf_apply,ite_eq_left (mem_toList_iff.mp hx).1]

lemma IsBoundary.length_eq_card {p : Perm D} {xs : List D} (h : IsBoundary p xs)
    {a : D} (ha : a ∈ xs) :
    xs.length = Fintype.card {x : D // p.SameCycle a x} := by
  rw [Fintype.card_of_subtype xs.toFinset (by
    intro x
    rw [List.mem_toFinset]
    exact ⟨h.sameCycle ha,h.mem_of_sameCycle ha⟩),List.toFinset_card_of_nodup h.nodup]

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryFold
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
variable (M : PictureMap D) {a b : D} (hab : a ≠ b) (hnext : M.face a = b)

/-- Pinch the two consecutive boundary sides off as a genuine bigon. The
other side pairs are unchanged, and the remaining boundary bypasses them. -/
def boundaryPinch (_ : a ≠ b) (_ : M.face a = b) : PictureMap D := M.splice b (M.face⁻¹ a)

omit [Fintype D] in
lemma boundaryPinch_bigon : (M.boundaryPinch hab hnext).Bigon a b := by
  have har : a ≠ M.face⁻¹ a := by
    intro h
    have hh := congrArg M.face h
    simp only [Perm.inv_def,Equiv.apply_symm_apply] at hh
    exact hab (hnext.symm.trans hh).symm
  refine ⟨hab,?_,?_⟩
  · change M.face (swap b (M.face⁻¹ a) a) = b
    rw [swap_apply_of_ne_of_ne hab har,hnext]
  · change M.face (swap b (M.face⁻¹ a) b) = a
    rw [swap_apply_left,Perm.inv_def,Equiv.apply_symm_apply]

lemma boundaryPinch_genusZero (hG : M.GenusZero) : (M.boundaryPinch hab hnext).GenusZero := by
  by_cases he : b = M.face⁻¹ a
  · have he' : M.boundaryPinch hab hnext = M := by
      apply PictureMap.ext
      · ext x
        simp [boundaryPinch,splice,he]
      · rfl
    rwa [he']
  · apply M.split_genusZero hG b (M.face⁻¹ a) he
    have h₁ : M.face.SameCycle a b := hnext ▸ (SameCycle.rfl (f := M.face) (x := a)).apply_right
    have h₂ : M.face.SameCycle (M.face⁻¹ a) a := by
      simpa only [Perm.inv_def,Equiv.apply_symm_apply] using (SameCycle.rfl (f := M.face) (x := M.face⁻¹ a)).apply_right
    exact h₁.symm.trans h₂.symm

variable {L V : Type*} {label : D → L} {start : L → V} {rev : L → L}

omit [Fintype D] in
lemma boundaryPinch_respects (hM : M.Respects label start rev)
    (hc : label a = rev (label b)) :
    (M.boundaryPinch hab hnext).Respects label start rev := by
  have hr : start (label (M.edge (M.face⁻¹ a))) = start (label a) := by
    have h := hM.1 (M.edge (M.face⁻¹ a))
    simpa only [vertex,mul_apply,M.edge_edge,Perm.inv_def,Equiv.apply_symm_apply] using h.symm
  have hv : start (label (M.edge b)) = start (label (M.edge (M.face⁻¹ a))) := by
    rw [hr,hM.2 b,← hc]
  constructor
  · intro x
    rw [boundaryPinch,M.splice_vertex,mul_apply,hM.1]
    exact Equiv.apply_swap_eq_self (v := start ∘ label) hv x
  · exact hM.2

/-- Literal free boundary cancellation, valid even when either canceled
side was paired to an interior side or to another part of the outside.
It is a genus-zero operation, not an assumed disk replacement. -/
def boundaryFold : PictureMap {x // OffPair a b x} :=
  (M.boundaryPinch_bigon hab hnext).remove

lemma boundaryFold_genusZero (hG : M.GenusZero) : (M.boundaryFold hab hnext).GenusZero :=
  (M.boundaryPinch_bigon hab hnext).remove_genusZero (M.boundaryPinch_genusZero hab hnext hG)

omit [Fintype D] in
lemma boundaryFold_respects (hM : M.Respects label start rev)
    (hc : label a = rev (label b)) :
    (M.boundaryFold hab hnext).Respects (label ∘ Subtype.val) start rev :=
  (M.boundaryPinch_bigon hab hnext).remove_respects (M.boundaryPinch_respects hab hnext hM hc) hc

omit [Fintype D] in
lemma boundaryFold_face (x : {x // OffPair a b x}) :
    (M.boundaryFold hab hnext).face x = erasePair M.face hab x := by
  apply Subtype.ext
  change M.face (swap b (M.face⁻¹ a) x.val) = bypassPair M.face a b x.val
  rw [bypassPair,bypass_away _ b x.val x.property.2,bypass_away M.face a x.val x.property.1]
  by_cases hx : M.face x.val = a
  · have hxr : x.val = M.face⁻¹ a := M.face.injective (by simpa only [Perm.inv_def,Equiv.apply_symm_apply] using hx)
    have hba : M.face b ≠ a := by
      intro h
      exact x.property.2 (M.face.injective (hx.trans h.symm))
    rw [ite_eq_left hx,hnext,ite_eq_left rfl,bypass_away M.face a b hab.symm,ite_eq_right hba,
      hxr,swap_apply_right]
  · have hxr : x.val ≠ M.face⁻¹ a := by intro h; apply hx; rw [h,Perm.inv_def,Equiv.apply_symm_apply]
    have hxb : M.face x.val ≠ b := by
      intro h
      exact x.property.1 (M.face.injective (h.trans hnext.symm))
    rw [swap_apply_of_ne_of_ne x.property.2 hxr,ite_eq_right hx,ite_eq_right hxb]

omit [Fintype D] in
/-- No cell-side index on another face changes. This is the compatibility
needed to turn algebraic free reduction into an actual mapped disk picture. -/
lemma boundaryFold_other_face (x : {x // OffPair a b x})
    (hx : ¬ M.face.SameCycle a x.val) :
    ((M.boundaryFold hab hnext).face x).val = M.face x.val := by
  change M.face (swap b (M.face⁻¹ a) x.val) = M.face x.val
  apply congrArg M.face
  apply swap_apply_of_ne_of_ne x.property.2
  intro he
  apply hx
  rw [he]
  have hr : M.face.SameCycle (M.face⁻¹ a) a := by
    simpa only [Perm.inv_def,Equiv.apply_symm_apply] using
      (SameCycle.rfl (f := M.face) (x := M.face⁻¹ a)).apply_right
  exact hr.symm

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryEraseList
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
variable {D : Type*} [DecidableEq D]

lemma bypassPair_consecutive (f : Perm D) {a b x : D} (ha : x ≠ a) (hb : x ≠ b)
    (hab : a ≠ b) (hn : f a = b) :
    bypassPair f a b x = if f x = a then f b else f x := by
  rw [bypassPair,bypass_away _ _ _ hb,bypass_away _ _ _ ha]
  by_cases he : f x = a
  · have hf : f b ≠ a := fun h => hb (f.injective (he.trans h.symm))
    rw [ite_eq_left he,hn,ite_eq_left rfl,bypass_away _ _ _ hab.symm,ite_eq_right hf,ite_eq_left he]
  · have hf : f x ≠ b := fun h => ha (f.injective (h.trans hn.symm))
    rw [ite_eq_right he,ite_eq_right hf,ite_eq_right he]

namespace IsBoundary
variable {f : Perm D} {xs : List D} (h : IsBoundary f xs)
include h

lemma lift {p : D → Prop} (hp : ∀ x ∈ xs, p x) (g : Perm {x // p x})
    (hg : ∀ x (hx : x ∈ xs), (g ⟨x,hp x hx⟩).val = f x) :
    IsBoundary g (xs.attachWith p hp) := by
  let ys := xs.attachWith p hp
  have hm : ys.map Subtype.val = xs := by
    simpa only [List.map_id_fun,id_eq] using (List.attachWith_map_val (f := id) hp)
  have hnodup : (ys.map Subtype.val).Nodup := by rw [hm]; exact h.nodup
  refine ⟨(List.nodup_map_iff Subtype.val_injective).mp hnodup,?_⟩
  intro x hx
  have hx' : x.val ∈ xs := (List.mem_attachWith hp x).mp hx
  apply Subtype.ext
  have hh := formPerm_map_apply Subtype.val Subtype.val_injective ys x
  rw [hm] at hh
  exact (hg x.val hx').trans ((h.turn x.val hx').trans hh)

omit h in
lemma middle_next {l r : List D} {a b : D} (h : IsBoundary f (l++a::b::r)) : f a = b := by
  have hr : (l++a::b::r) ~r (a::b::(r++l)) := by
    simpa using (List.isRotated_append : (l++a::b::r) ~r ((a::b::r)++l))
  rw [h.turn a (by simp),List.formPerm_eq_of_isRotated h.nodup hr]
  exact List.formPerm_apply_head a b (r++l) (hr.nodup_iff.mp h.nodup)

omit h in
lemma erase_middle {l r : List D} {a b : D} (h : IsBoundary f (l++a::b::r)) :
    IsBoundary (bypassPair f a b) (l++r) := by
  have ho := middle_offpair h.nodup
  have hn := List.nodup_append.mp h.nodup
  have ht : (a::b::r).Nodup := hn.2.1
  have hab : a ≠ b := by
    intro he
    exact (List.nodup_cons.mp ht).1 (by simp [he])
  have hp : (l++a::b::r).formPerm a = b := by
    rw [← h.turn a (by simp)]
    exact h.middle_next
  refine ⟨List.nodup_append.mpr ⟨hn.1,ht.of_cons.of_cons,?_⟩,?_⟩
  · intro x hx y hy
    exact hn.2.2 x hx y (by simp [hy])
  · intro x hx
    have ix : x ∈ l++a::b::r := by
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · simp [hx]
    rw [← bypassPair_formPerm l r a b h.nodup]
    rw [bypassPair_consecutive f (ho x hx).1 (ho x hx).2 hab h.middle_next,
      bypassPair_consecutive _ (ho x hx).1 (ho x hx).2 hab hp,
      h.turn x ix,h.turn b (by simp)]

end IsBoundary

namespace PictureMap
variable (M : PictureMap D) {l r : List D} {a b : D}

/-- The free fold deletes exactly the two consecutive entries of the literal
outside word; no cyclic rotation or word-equality surrogate is used. -/
theorem boundaryFold_boundary (h : IsBoundary M.face (l++a::b::r)) (hab : a ≠ b) :
    IsBoundary (M.boundaryFold hab h.middle_next).face
      ((l++r).attachWith (OffPair a b) (IsBoundary.middle_offpair h.nodup)) := by
  apply h.erase_middle.lift
  intro x hx
  exact congrArg Subtype.val (M.boundaryFold_face hab h.middle_next _)

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryGraphWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm SimpleGraph
attribute [local instance] Classical.propDecidable
variable {D V : Type*} [DecidableEq D] {p : Perm D} {G : SimpleGraph V}
variable {xs : List D} (h : IsBoundary p xs) (j : D → G.Dart)
  (hc : ∀ x ∈ xs, (j (p x)).fst = (j x).snd)

include h hc in
lemma IsBoundary.graph_chain : (xs.map j).IsChain G.DartAdj := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hl : i+1 < xs.length := by simpa only [List.length_map] using hi
  have hi' : i < xs.length := by omega
  simp only [List.getElem_map]
  change (j xs[i]).snd = (j xs[i+1]).fst
  have he := hc xs[i] (List.getElem_mem hi')
  rw [h.turn _ (List.getElem_mem hi'),List.formPerm_apply_getElem _ h.nodup] at he
  simpa only [Nat.mod_eq_of_lt hl] using he.symm

include h hc in
/-- Read a literal permutation face as an actual graph closed walk. -/
lemma IsBoundary.graph_closed_walk (hne : xs ≠ []) :
    ∃ (v : V) (q : G.Walk v v), q.darts = xs.map j := by
  have hn : xs.map j ≠ [] := by
    intro hh
    exact hne (List.map_eq_nil_iff.mp hh)
  let q := Walk.ofDarts (xs.map j) hn (h.graph_chain j hc)
  have he : ((xs.map j).getLast hn).snd = ((xs.map j).head hn).fst := by
    rw [List.getLast_map,List.head_map]
    have hh := hc (xs.getLast hne) (List.getLast_mem hne)
    rw [h.turn _ (List.getLast_mem hne)] at hh
    have hp : xs.formPerm (xs.getLast hne) = xs.head hne := by
      cases xs with
      | nil => contradiction
      | cons a xs => exact List.formPerm_apply_getLast a xs
    rw [hp] at hh
    exact hh.symm
  refine ⟨((xs.map j).head hn).fst,q.copy rfl he,?_⟩
  rw [Walk.darts_copy]
  exact Walk.darts_ofDarts hn (h.graph_chain j hc)

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryLift
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

/-- A literal boundary can be pulled back through an injective survival map,
provided every one of its sides survives and its successor is retained. -/
lemma IsBoundary.pullback_surviving {D E : Type*} [DecidableEq D] [DecidableEq E]
    {p : Perm D} {q : Perm E} {xs : List D} (h : IsBoundary p xs)
    (j : E → D) (hj : Function.Injective j)
    (hcomplete : ∀ x ∈ xs, ∃ y, j y = x)
    (hface : ∀ y, j y ∈ xs → j (q y) = p (j y)) :
    ∃ ys : List E, IsBoundary q ys ∧ ys.map j = xs := by
  let k : {x : D // x ∈ xs} → E := fun x => Classical.choose (hcomplete x.val x.property)
  have hk : ∀ x, j (k x) = x.val := fun x => Classical.choose_spec (hcomplete x.val x.property)
  let ys := xs.attach.map k
  have he : ys.map j = xs := by
    dsimp only [ys]
    rw [List.map_map]
    have hc : j ∘ k = Subtype.val := funext hk
    rw [hc,List.attach_map_subtype_val]
  refine ⟨ys,⟨?_,?_⟩,he⟩
  · exact List.Nodup.of_map j (he ▸ h.nodup)
  · intro y hy
    have hx : j y ∈ xs := he ▸ List.mem_map_of_mem hy
    apply hj
    rw [hface y hx,h.turn _ hx,← he,formPerm_map_apply j hj]

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundarySplice
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
variable {D : Type*} [DecidableEq D]

namespace IsBoundary
variable {f : Perm D} {l r : List D} {a b : D}

/-- Concatenation is the literal connected-sum splice at the two incoming
corners. The side order, not merely the freely represented word, is retained. -/
theorem splice_append (hl : IsBoundary f (l++[a])) (hr : IsBoundary f (b::r))
    (hd : ∀ x ∈ l++[a], x ∉ b::r) :
    IsBoundary (f * swap a ((b::r).getLast (by simp))) ((l++[a])++(b::r)) := by
  let xs := l++[a]
  let ys := b::r
  let c := ys.getLast (by simp [ys])
  have ha : a ∈ xs := by simp [xs]
  have hc : c ∈ ys := List.getLast_mem _
  have hdis : ∀ x ∈ xs, x ∉ ys := hd
  have hn : (xs++ys).Nodup := by
    rw [List.nodup_append]
    exact ⟨hl.nodup,hr.nodup,fun x hx y hy he => hdis x hx (he ▸ hy)⟩
  have hform : (xs++ys).formPerm = xs.formPerm * ys.formPerm * swap a c := by
    have hz : ys.formPerm a = a := List.formPerm_apply_of_notMem (hdis a ha)
    have hy : ys.formPerm c = b := List.formPerm_apply_getLast b r
    have hs : ys.formPerm * swap a c = swap a b * ys.formPerm := by
      rw [mul_swap_eq_swap_mul,hz,hy]
    dsimp only [xs,ys]
    rw [List.append_assoc]
    change (l++a::b::r).formPerm = (l++[a]).formPerm * (b::r).formPerm * swap a c
    rw [formPerm_append_join]
    simp only [mul_assoc]
    rw [hs]
  have ht : ∀ x ∈ xs++ys, f x = (xs.formPerm*ys.formPerm) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [mul_apply,List.formPerm_apply_of_notMem (hdis x hx),hl.turn x hx]
    · have hn : ys.formPerm x ∉ xs := by
        intro hh
        exact hdis _ hh (List.formPerm_apply_mem_of_mem hx)
      rw [mul_apply,List.formPerm_apply_of_notMem hn,hr.turn x hx]
  refine ⟨hn,?_⟩
  intro x hx
  have hs : swap a c x ∈ xs++ys := by
    by_cases he : x = a
    · subst x; rw [swap_apply_left]; exact List.mem_append_right xs hc
    by_cases hf : x = c
    · subst x; rw [swap_apply_right]; exact List.mem_append_left ys ha
    · rwa [swap_apply_of_ne_of_ne he hf]
  change f (swap a c x) = (xs++ys).formPerm x
  rw [ht _ hs,hform]; rfl

end IsBoundary
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureMirror
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

namespace IsBoundary
variable {f : Perm D} {xs : List D} (h : IsBoundary f xs)
include h
omit [Fintype D] in
lemma reverse : IsBoundary f⁻¹ xs.reverse := by
  refine ⟨by simpa using h.nodup,?_⟩
  intro x hx
  rw [List.formPerm_reverse]
  have hx' : x ∈ xs := List.mem_reverse.mp hx
  have hy : xs.formPerm⁻¹ x ∈ xs := by
    apply List.mem_of_formPerm_apply_mem
    simpa only [Perm.inv_def,Equiv.apply_symm_apply] using hx'
  apply f.injective
  rw [Perm.inv_def,Equiv.apply_symm_apply,h.turn _ hy,Perm.inv_def,Equiv.apply_symm_apply]
end IsBoundary

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPicture
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
universe u
variable {A : Type u}

lemma symmetricRelator_inv {R : Set (Word A)} {w : Word A} (h : SymmetricRelator R w) :
    SymmetricRelator R (FreeGroup.invRev w) := by
  rcases h with h | h
  · exact Or.inr (by simpa using h)
  · exact Or.inl h

attribute [instance] WordPicture.finite WordPicture.decEq

namespace WordPicture
variable {R : Set (Word A)} {w : Word A} (P : WordPicture R w)

lemma respects : P.pairing.Respects P.label (fun _ => ()) invLetter :=
  ⟨fun _ => rfl,P.paired⟩

end WordPicture
end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureBase
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

lemma finRange_boundary (n : ℕ) : IsBoundary (finRotate n) (List.finRange n) := by
  refine ⟨List.nodup_finRange n,?_⟩
  intro x _
  let : NeZero n := x.neZero
  have hi : x.val < (List.finRange n).length := by simp
  have hh := List.formPerm_apply_getElem (List.finRange n) (List.nodup_finRange n) x.val hi
  simp only [List.length_finRange,List.getElem_finRange] at hh
  have he : (List.finRange n).formPerm x = ⟨(x.val+1)%n,Nat.mod_lt _ (NeZero.pos n)⟩ := hh
  rw [he,finRotate_apply]
  apply Fin.ext
  change (x.val + 1 % n) % n = (x.val + 1) % n
  exact Nat.add_mod_mod _ _ _

end HyperbolicObstruction.PictureSwitch

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureExist
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
variable {D : Type*} [DecidableEq D] {f : Perm D} {xs : List D}
lemma rotate (h : IsBoundary f xs) (n : ℕ) : IsBoundary f (xs.rotate n) := by
  refine ⟨by simpa using h.nodup,?_⟩
  intro x hx
  rw [List.formPerm_rotate _ h.nodup]
  exact h.turn x (List.mem_rotate.mp hx)
end IsBoundary
end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w : Word A}
namespace WordPicture
variable (P : WordPicture R w)

def rotate (n : ℕ) : WordPicture R (w.rotate n) where
  Dart := P.Dart
  pairing := P.pairing
  genusZero := P.genusZero
  label := P.label
  paired := P.paired
  outside := P.outside.rotate n
  boundary := P.boundary.rotate n
  word := by rw [List.map_rotate,P.word]
  interior := by intro x hx; exact P.interior x (by simpa using hx)

end WordPicture

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureFold
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

/-- Free boundary cancellation lands in a new actual genus-zero diagram,
retaining every interior relator face, with all repeated side indices intact. -/
def foldAt {l r : List P.Dart} {a b : P.Dart} (he : P.outside = l++a::b::r)
    (hc : P.label a = invLetter (P.label b)) : WordPicture R ((l++r).map P.label) := by
  have hb : IsBoundary P.pairing.face (l++a::b::r) := he ▸ P.boundary
  have hab : a ≠ b := by
    have hn := (List.nodup_append.mp hb.nodup).2.1
    exact fun he => (List.nodup_cons.mp hn).1 (by simp [he])
  let M := P.pairing.boundaryFold hab hb.middle_next
  have hp := IsBoundary.middle_offpair hb.nodup
  refine {
    Dart := {x // OffPair a b x}
    pairing := M
    genusZero := P.pairing.boundaryFold_genusZero hab hb.middle_next P.genusZero
    label := P.label ∘ Subtype.val
    paired := (P.pairing.boundaryFold_respects hab hb.middle_next P.respects hc).2
    outside := (l++r).attachWith (OffPair a b) hp
    boundary := P.pairing.boundaryFold_boundary hb hab
    word := List.attachWith_map_val hp
    interior := ?_ }
  intro x hx
  have hxo : x.val ∉ P.outside := by
    intro hm
    have he' : x.val ∈ l++r := by
      rw [he] at hm
      simp only [List.mem_append,List.mem_cons] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl hm
      · rcases hm with ha | hb | hr
        · exact False.elim (x.property.1 ha)
        · exact False.elim (x.property.2 hb)
        · exact Or.inr hr
    exact hx ((List.mem_attachWith hp x).mpr he')
  obtain ⟨xs,hxs,hxm,hr⟩ := P.interior x.val hxo
  have hdis : ∀ y ∈ xs, y ∉ P.outside := by
    intro y hy hyo
    exact hxo (P.boundary.mem_of_sameCycle hyo (hxs.sameCycle hy hxm))
  have ha : a ∈ P.outside := by rw [he]; simp
  have hb' : b ∈ P.outside := by rw [he]; simp
  have hp' : ∀ y ∈ xs, OffPair a b y := by
    intro y hy
    exact ⟨fun he => hdis y hy (he ▸ ha),fun he => hdis y hy (he ▸ hb')⟩
  refine ⟨xs.attachWith (OffPair a b) hp',?_,(List.mem_attachWith hp' x).mpr hxm,?_⟩
  · apply hxs.lift hp' M.face
    intro y hy
    apply P.pairing.boundaryFold_other_face hab hb.middle_next
    intro hf
    exact hdis y hy (P.boundary.mem_of_sameCycle ha hf)
  · simpa only [Function.comp_def,List.attachWith_map_val] using hr

end WordPicture

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryRotation
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
variable {D : Type*} [DecidableEq D]
lemma IsBoundary.rotate_append {p : Perm D} {l r : List D}
    (h : IsBoundary p (l++r)) : IsBoundary p (r++l) := by
  simpa only [List.rotate_append_length_eq] using h.rotate l.length

lemma IsBoundary.adjacent_rotate {p : Perm D} {xs : List D} (h : IsBoundary p xs)
    {a b : D} (ha : a ∈ xs) (hab : a ≠ b) (hp : p a = b) :
    ∃ k < xs.length, ∃ z, xs.rotate k = a::b::z := by
  obtain ⟨l,r,he⟩ := List.mem_iff_append.mp ha
  have hb : IsBoundary p ((a::r)++l) := (he ▸ h).rotate_append
  have hlen : r++l ≠ [] := by
    intro hn
    have hc := hb.turn a (by simp)
    rw [List.cons_append,hn,List.formPerm_singleton,one_apply,hp] at hc
    exact hab hc.symm
  obtain ⟨c,z,hz⟩ : ∃ c z, r++l = c::z := List.exists_cons_of_ne_nil hlen
  have hc := hb.turn a (by simp)
  rw [List.cons_append,hz,List.formPerm_apply_head _ _ _ (by simpa only [List.cons_append,hz] using hb.nodup),hp] at hc
  refine ⟨l.length,by simp [he],z,?_⟩
  rw [he,List.rotate_append_length_eq,List.cons_append,hz,hc]

end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.WordPictures

namespace WordPicture
open HyperbolicObstruction.PictureSwitch
variable {A : Type*} {R : Set (Word A)} {w : Word A}
variable (P : WordPicture R w)

lemma all_outside_rotate (h : ∀ x, x ∈ P.outside) (k : ℕ) :
    ∀ x, x ∈ (P.rotate k).outside := fun x => List.mem_rotate.mpr (h x)

lemma all_outside_fold {l r : List P.Dart} {a b : P.Dart}
    (he : P.outside = l++a::b::r) (hc : P.label a = invLetter (P.label b))
    (h : ∀ x, x ∈ P.outside) : ∀ x, x ∈ (P.foldAt he hc).outside := by
  intro x
  change x ∈ (l++r).attachWith (OffPair a b) _
  apply (List.mem_attachWith _ x).mpr
  have hx := h x.val
  rw [he] at hx
  simp only [List.mem_append,List.mem_cons] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · rcases hx with ha | hb | hx
    · exact False.elim (x.property.1 ha)
    · exact False.elim (x.property.2 hb)
    · exact Or.inr hx

end WordPicture
end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeTopCollapse
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def macroBase : MacroGraph.Vertex → CoreGeometry.Vertex
  | .inl (.inl i) => .inl (CoreWordGraph.base i)
  | .inl (.inr l) => .inr l
  | .inr _ => .inl 3

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeErase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap
variable (M : PictureMap D) (a : D)

omit [DecidableEq D] [Fintype D] in
lemma eraseEdge_invariant (x : D) :
    OffPair a (M.edge a) (M.edge x) ↔ OffPair a (M.edge a) x := by
  have h₁ : M.edge x = a ↔ x = M.edge a := by
    constructor
    · intro h; simpa only [M.edge_edge] using congrArg M.edge h
    · intro h; rw [h,M.edge_edge]
  have h₂ : M.edge x = M.edge a ↔ x = a := M.edge.apply_eq_iff_eq
  simp only [OffPair,ne_eq,h₁,h₂,and_comm]

/-- Deletion of an actual paired edge: its incident face boundaries are
spliced and the two indexed sides erased. No label or surface premise is
hidden in this finite permutation construction. -/
def eraseEdge : PictureMap {x // OffPair a (M.edge a) x} where
  face := erasePair (M.face * swap a (M.edge a)) (M.edge_ne a).symm
  edge := M.edge.subtypePerm (M.eraseEdge_invariant a)
  edge_sq := by ext x; change M.edge (M.edge x.val) = x.val; exact M.edge_edge _
  edge_ne := fun x he => M.edge_ne x.val (congrArg Subtype.val he)

omit [Fintype D] in
lemma eraseEdge_vertex (x : {x // OffPair a (M.edge a) x}) :
    ((M.eraseEdge a).vertex x).val = (erasePair M.vertex (M.edge_ne a).symm x).val := by
  change bypassPair (M.face * swap a (M.edge a)) a (M.edge a) (M.edge x.val) =
    bypassPair M.vertex a (M.edge a) x.val
  have hx := (M.eraseEdge_invariant a x.val).mpr x.property
  rw [bypassPair,bypassPair,bypass_away _ _ _ hx.2,bypass_away _ _ _ x.property.2,
    bypass_away _ _ _ hx.1,bypass_away _ _ _ x.property.1]
  simp only [vertex,mul_apply,swap_apply_of_ne_of_ne hx.1 hx.2,swap_apply_left]
  have hh : bypass (M.face * swap a (M.edge a)) a (M.edge a) =
      bypass (M.face * M.edge) a (M.edge a) := by
    simp only [bypass_away _ _ _ (M.edge_ne a),mul_apply,swap_apply_right,
      swap_apply_left,M.edge_edge]
  rw [hh]

lemma eraseEdge_face_orbits (x y : {x // OffPair a (M.edge a) x}) :
    (M.eraseEdge a).face.SameCycle x y ↔
      (M.face * swap a (M.edge a)).SameCycle x.val y.val :=
  erasePair_orbits _ (M.edge_ne a).symm _ _

omit [Fintype D] in
lemma eraseEdge_vertex_perm : (M.eraseEdge a).vertex =
    erasePair M.vertex (M.edge_ne a).symm := by
  ext x
  exact M.eraseEdge_vertex a x

end PictureMap
end HyperbolicObstruction.PictureSwitch
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeEraseBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]
namespace IsBoundary

lemma erase_head {f : Perm D} {a : D} {xs : List D} (h : IsBoundary f (a::xs)) :
    IsBoundary (bypass f a) xs := by
  refine ⟨h.nodup.of_cons,?_⟩
  intro x hx
  have ha : x ≠ a := fun he => (List.nodup_cons.mp h.nodup).1 (he ▸ hx)
  rw [← bypass_formPerm_head a xs h.nodup]
  rw [bypass_away _ _ _ ha,bypass_away _ _ _ ha,
    h.turn x (List.mem_cons_of_mem _ hx),h.turn a (by simp)]

lemma erase_at {f : Perm D} {a : D} {l r : List D} (h : IsBoundary f (l++a::r)) :
    IsBoundary (bypass f a) (l++r) := by
  have hh : IsBoundary f (a::(r++l)) := by
    simpa only [List.cons_append] using h.rotate_append
  exact hh.erase_head.rotate_append

/-- The two actual face cycles are spliced at the deleted paired sides. -/
lemma splice_heads {f : Perm D} {a b : D} {l r : List D}
    (hl : IsBoundary f (a::l)) (hr : IsBoundary f (b::r))
    (hd : ∀ x ∈ a::l, x ∉ b::r) :
    IsBoundary (f * swap a b) (a::(r++b::l)) := by
  have hl' : IsBoundary f (l++[a]) := by
    simpa using (hl.rotate_append (l := [a]) (r := l))
  have hr' : IsBoundary f (r++[b]) := by
    simpa using (hr.rotate_append (l := [b]) (r := r))
  obtain ⟨c,s,hs⟩ : ∃ c s, r++[b] = c::s := List.exists_cons_of_ne_nil (by simp)
  have hh := hl'.splice_append (hs ▸ hr') (by
    intro x hx hy
    apply hd x (by simpa only [List.mem_append,List.mem_singleton,List.mem_cons,List.not_mem_nil,or_false,false_or,or_comm] using hx)
    rw [← hs] at hy
    simpa only [List.mem_append,List.mem_singleton,List.mem_cons,List.not_mem_nil,or_false,false_or,or_comm] using hy)
  have hb : (c::s).getLast (by simp) = b := by simpa only [hs] using (List.getLast_append_singleton (a := b) r)
  rw [hb,← hs,List.append_assoc] at hh
  have hh' : IsBoundary (f*swap a b) (([a]++(r++[b]))++l) := hh.rotate_append
  simpa only [List.singleton_append,List.append_assoc,List.cons_append,List.nil_append] using hh'

end IsBoundary
end HyperbolicObstruction.PictureSwitch
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeEraseComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D) (a : D)

/-- When the spliced face retains a side, deleting its paired edge cannot
create a new component. This is a quotient-of-darts proof, not a drawing. -/
lemma eraseEdge_components_le (c : {x // OffPair a (M.edge a) x})
    (ha : (M.face * swap a (M.edge a)).SameCycle a c.val)
    (hb : (M.face * swap a (M.edge a)).SameCycle (M.edge a) c.val) :
    Nat.card (Quotient (M.eraseEdge a).components) ≤ Nat.card (Quotient M.components) := by
  let rep : D → {x // OffPair a (M.edge a) x} :=
    fun x => if hx : OffPair a (M.edge a) x then ⟨x,hx⟩ else c
  let j : D → Quotient (M.eraseEdge a).components :=
    fun x => Quotient.mk _ (rep x)
  have hr (x : D) : (M.face * swap a (M.edge a)).SameCycle x (rep x).val := by
    by_cases hx : OffPair a (M.edge a) x
    · simp only [rep,dite_eq_left hx]; exact SameCycle.rfl
    · simp only [rep,dite_eq_right hx]
      have hx' : x = a ∨ x = M.edge a := by unfold OffPair at hx; tauto
      rcases hx' with rfl | rfl
      · exact ha
      · exact hb
  have hf : ∀ x y, (M.face * swap a (M.edge a)).SameCycle x y → j x = j y := by
    intro x y hxy
    apply Quotient.sound
    apply (M.eraseEdge a).face_le_components
    apply (M.eraseEdge_face_orbits a _ _).mpr
    exact (hr x).symm.trans (hxy.trans (hr y))
  have hrepA : rep a = c := dite_eq_right (fun h => h.1 rfl)
  have hrepB : rep (M.edge a) = c := dite_eq_right (fun h => h.2 rfl)
  have hswap : ∀ x, j (swap a (M.edge a) x) = j x := by
    intro x
    by_cases hxa : x = a
    · subst x
      rw [swap_apply_left]
      exact congrArg (Quotient.mk (M.eraseEdge a).components) (hrepB.trans hrepA.symm)
    by_cases hxb : x = M.edge a
    · subst x
      rw [swap_apply_right]
      exact congrArg (Quotient.mk (M.eraseEdge a).components) (hrepA.trans hrepB.symm)
    · rw [swap_apply_of_ne_of_ne hxa hxb]
  have he : ∀ x, j x = j (M.edge x) := by
    intro x
    by_cases hx : OffPair a (M.edge a) x
    · have hx' := (M.eraseEdge_invariant a x).mpr hx
      simp only [j,rep,dite_eq_left hx,dite_eq_left hx']
      apply Quotient.sound
      exact (M.eraseEdge a).edge_le_components (SameCycle.rfl (f := (M.eraseEdge a).edge) (x := ⟨x,hx⟩)).apply_right
    · have hx' : ¬ OffPair a (M.edge a) (M.edge x) :=
        fun h => hx ((M.eraseEdge_invariant a x).mp h)
      simp only [j,rep,dite_eq_right hx,dite_eq_right hx']
  have hj : M.components ≤ Setoid.ker j := by
    apply M.components_le
    · intro x
      have hh := hf (swap a (M.edge a) x) (M.face x) (by
        have hz := (SameCycle.rfl (f := M.face * swap a (M.edge a))
          (x := swap a (M.edge a) x)).apply_right
        simpa only [mul_apply,swap_apply_self] using hz)
      exact (hswap x).symm.trans hh
    · exact he
  let q : Quotient M.components → Quotient (M.eraseEdge a).components :=
    Quotient.lift j (fun _ _ h => hj h)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x,rfl⟩ := Quotient.exists_rep y
    refine ⟨Quotient.mk _ x.val,?_⟩
    change j x.val = Quotient.mk _ x
    simp only [j,rep,dite_eq_left x.property]
  let : Fintype (Quotient M.components) := Fintype.ofFinite _
  let : Fintype (Quotient (M.eraseEdge a).components) := Fintype.ofFinite _
  simpa only [← Nat.card_eq_fintype_card] using Fintype.card_le_of_surjective q hq

lemma eraseEdge_component_witness (hne : ¬ M.face.SameCycle a (M.edge a))
    (hfixed : ¬ (M.face a = a ∧ M.face (M.edge a) = M.edge a)) :
    ∃ c : {x // OffPair a (M.edge a) x},
      (M.face * swap a (M.edge a)).SameCycle a c.val ∧
      (M.face * swap a (M.edge a)).SameCycle (M.edge a) c.val := by
  have hab : (M.face * swap a (M.edge a)).SameCycle a (M.edge a) :=
    sameCycle_after_swap_right M.face hne
  have hfa : M.face a ≠ M.edge a := by
    intro he; apply hne; rw [← he]; exact SameCycle.rfl.apply_right
  have hfb : M.face (M.edge a) ≠ a := by
    intro he
    have hh := (SameCycle.rfl (f := M.face) (x := M.edge a)).apply_right
    rw [he] at hh
    exact hne hh.symm
  by_cases haa : M.face a = a
  · have hbb : M.face (M.edge a) ≠ M.edge a := fun h => hfixed ⟨haa,h⟩
    have hc : (M.face * swap a (M.edge a)).SameCycle a (M.face (M.edge a)) := by
      simpa only [mul_apply,swap_apply_left] using
        (SameCycle.rfl (f := M.face * swap a (M.edge a)) (x := a)).apply_right
    exact ⟨⟨M.face (M.edge a),hfb,hbb⟩,hc,hab.symm.trans hc⟩
  · have hc : (M.face * swap a (M.edge a)).SameCycle (M.edge a) (M.face a) := by
      simpa only [mul_apply,swap_apply_right] using
        (SameCycle.rfl (f := M.face * swap a (M.edge a)) (x := M.edge a)).apply_right
    exact ⟨⟨M.face a,haa,hfa⟩,hab.trans hc,hc⟩

end HyperbolicObstruction.PictureSwitch.PictureMap
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeEraseCount
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

lemma erasePair_cycles_le (p : Perm D) {a b : D} (hab : a ≠ b) :
    cycles (erasePair p hab) ≤ cycles p := by
  let q := bypassPair p a b
  have hqA : q a = a := bypassPair_a p hab
  have hqB : q b = b := bypassPair_b p a b
  let s := q.subtypePerm (p := fun x => ¬ OffPair a b x)
    (fun x => not_congr (offPair_invariant hqA hqB x))
  have hc : cycles q = cycles (erasePair p hab) + cycles s := by
    simpa only [cycles_eq_card_classes,erasePair,q,s] using
      (cycles_subtype_split (P := OffPair a b) q (offPair_invariant hqA hqB))
  have hs : s = 1 := by
    ext x
    change q x.val = x.val
    have hx : x.val = a ∨ x.val = b := by
      have hh := x.property
      unfold OffPair at hh
      tauto
    rcases hx with hx | hx
    · rw [hx,hqA]
    · rw [hx,hqB]
  have hcard : Fintype.card {x : D // ¬ OffPair a b x} = 2 := by
    rw [Fintype.card_of_subtype ({a,b} : Finset D) (by intro x; simp only [Finset.mem_insert,Finset.mem_singleton,OffPair]; tauto)]
    simp [hab]
  have hsC : cycles s = 2 := by rw [hs]; simp [cycles,defect,hcard]
  have hqC : cycles q ≤ cycles p + 2 := by
    change cycles (bypass (bypass p a) b) ≤ _
    rw [bypass_cycles,bypass_cycles]
    split_ifs <;> omega
  rw [hsC] at hc
  omega

namespace PictureMap
lemma eraseEdge_faces_le (M : PictureMap D) (a : D)
    (hne : ¬ M.face.SameCycle a (M.edge a)) :
    cycles (M.eraseEdge a).face + 1 ≤ cycles M.face := by
  have h₁ := erasePair_cycles_le (M.face*swap a (M.edge a)) (M.edge_ne a).symm
  have h₂ := cycles_merge_right M.face hne
  change cycles (erasePair (M.face*swap a (M.edge a)) (M.edge_ne a).symm) + 1 ≤ _
  omega
end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeEraseGenus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D) (a : D)

lemma eraseEdge_euler (hne : ¬ M.face.SameCycle a (M.edge a))
    (hfixed : ¬ (M.face a = a ∧ M.face (M.edge a) = M.edge a)) :
    (M.eraseEdge a).euler = M.euler := by
  have hfa : M.face a ≠ M.edge a := by
    intro he; apply hne; rw [← he]; exact SameCycle.rfl.apply_right
  have hfb : M.face (M.edge a) ≠ a := by
    intro he
    have hh := (SameCycle.rfl (f := M.face) (x := M.edge a)).apply_right
    rw [he] at hh
    exact hne hh.symm
  have hv : M.vertex a ≠ a := hfb
  have hf : (M.face * swap a (M.edge a)) a ≠ a := by
    simpa only [mul_apply,swap_apply_left] using hfb
  have hbvp : bypass M.vertex a (M.edge a) ≠ M.edge a := by
    rw [bypass_away _ _ _ (M.edge_ne a)]
    simp only [vertex,mul_apply,M.edge_edge]
    by_cases h : M.face a = a
    · rw [ite_eq_left h]; exact fun hb => hfixed ⟨h,hb⟩
    · rw [ite_eq_right h]; exact hfa
  have hbfp : bypass (M.face * swap a (M.edge a)) a (M.edge a) ≠ M.edge a := by
    simpa only [bypass_away _ _ _ (M.edge_ne a),vertex,mul_apply,M.edge_edge,
      swap_apply_right,swap_apply_left] using hbvp
  have hcV := erasePair_cycles M.vertex (M.edge_ne a).symm hv hbvp
  have hcF := erasePair_cycles (M.face * swap a (M.edge a)) (M.edge_ne a).symm hf hbfp
  have hm := cycles_merge_right M.face hne
  have hD := card_offPair (M.edge_ne a).symm
  rw [euler,euler,M.eraseEdge_vertex_perm a,hcV]
  change cycles M.vertex + cycles (erasePair (M.face * swap a (M.edge a)) (M.edge_ne a).symm) - _ = _
  rw [hcF]
  omega

/-- Deleting an edge separating two distinct face cycles preserves actual
combinatorial genus zero, including the component consisting of two monogons. -/
theorem eraseEdge_genusZero (hG : M.GenusZero)
    (hne : ¬ M.face.SameCycle a (M.edge a)) : (M.eraseEdge a).GenusZero := by
  by_cases hfixed : M.face a = a ∧ M.face (M.edge a) = M.edge a
  · have hinv := offPair_invariant hfixed.1 hfixed.2
    have heq : M.eraseEdge a = M.restrict (OffPair a (M.edge a)) hinv (M.eraseEdge_invariant a) := by
      apply PictureMap.ext
      · ext x
        change bypassPair (M.face * swap a (M.edge a)) a (M.edge a) x.val = M.face x.val
        have hx := (hinv x.val).mpr x.property
        rw [bypassPair,bypass_away _ _ _ x.property.2,bypass_away _ _ _ x.property.1]
        simp only [mul_apply,swap_apply_of_ne_of_ne x.property.1 x.property.2,
          ite_eq_right hx.1,ite_eq_right hx.2]
      · rfl
    rw [heq]
    exact M.restrict_genusZero _ hG hinv (M.eraseEdge_invariant a)
  · obtain ⟨c,ha,hb⟩ := M.eraseEdge_component_witness a hne hfixed
    have hc := M.eraseEdge_components_le a c ha hb
    have he := M.eraseEdge_euler a hne hfixed
    have hh := (M.eraseEdge a).euler_le
    change M.euler = _ at hG
    change (M.eraseEdge a).euler = _
    omega

end HyperbolicObstruction.PictureSwitch.PictureMap
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureUnderlyingGraph
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

/-- The vertices of the actual rotation system, without collapsing darts or
parallel edge copies. Only the associated simple adjacency ignores loops. -/
abbrev GraphVertex := Quotient (SameCycle.setoid M.vertex)

def vertexClass (x : D) : M.GraphVertex := Quotient.mk _ x

omit [DecidableEq D] [Fintype D] in
lemma vertexClass_eq_iff (x y : D) :
    M.vertexClass x = M.vertexClass y ↔ M.vertex.SameCycle x y :=
  Quotient.eq

/-- The underlying simple graph used in the planar-separator argument.
Its adjacency is induced by real edge copies of the rotation system. -/
def underlyingGraph : SimpleGraph M.GraphVertex where
  Adj v w := v ≠ w ∧ ∃ x : D, M.vertexClass x = v ∧ M.vertexClass (M.edge x) = w
  symm := ⟨by
    rintro v w ⟨hne,x,hx,he⟩
    exact ⟨hne.symm,M.edge x,he,by rw [M.edge_edge]; exact hx⟩⟩
  loopless := ⟨by rintro v ⟨h,_⟩; exact h rfl⟩

def vertex_fiber_equiv (x : D) :
    {y : D // M.vertexClass y = M.vertexClass x} ≃ {y : D // M.vertex.SameCycle x y} :=
  Equiv.subtypeEquivRight fun y => (M.vertexClass_eq_iff y x).trans sameCycle_comm

omit [DecidableEq D] in
lemma components_le_underlying_reachable :
    M.components ≤ Setoid.comap M.vertexClass M.underlyingGraph.reachableSetoid := by
  apply sup_le
  · intro x y h
    change M.underlyingGraph.Reachable (M.vertexClass x) (M.vertexClass y)
    rw [(M.vertexClass_eq_iff x y).mpr h]
  · apply sameCycle_le_of_apply
    intro x
    change M.underlyingGraph.Reachable (M.vertexClass x) (M.vertexClass (M.edge x))
    by_cases h : M.vertexClass x = M.vertexClass (M.edge x)
    · rw [h]
    · exact SimpleGraph.Adj.reachable ⟨h,x,rfl,rfl⟩

/-- Sending each rotation vertex to its true connected component. -/
def graphComponent : M.GraphVertex → Quotient M.components :=
  Quotient.map id (fun _ _ h => M.vertex_le_components h)

omit [DecidableEq D] [Fintype D] in
lemma graphComponent_adj {v w : M.GraphVertex} (h : M.underlyingGraph.Adj v w) :
    M.graphComponent v = M.graphComponent w := by
  obtain ⟨hne,x,rfl,rfl⟩ := h
  exact Quotient.sound (M.edge_le_components SameCycle.rfl.apply_right)

omit [DecidableEq D] [Fintype D] in
lemma graphComponent_reachable {v w : M.GraphVertex} (h : M.underlyingGraph.Reachable v w) :
    M.graphComponent v = M.graphComponent w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (M.graphComponent_adj h).trans ih

omit [DecidableEq D] in
/-- Simple-graph reachability is exactly connectivity of the actual side
identifications, not an additional assumption about a planar drawing. -/
theorem underlying_reachable_iff (x y : D) :
    M.underlyingGraph.Reachable (M.vertexClass x) (M.vertexClass y) ↔ M.components x y := by
  constructor
  · intro h
    exact Quotient.exact (M.graphComponent_reachable h)
  · intro h; exact M.components_le_underlying_reachable h

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PlanarEdgeOrdering
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

lemma paired_joins (l : List (D × D)) (hl : swaps l = M.edge)
    (hpairs : ∀ ab ∈ l, M.edge ab.1 = ab.2) :
    joins (SameCycle.setoid M.vertex) l = M.components := by
  apply le_antisymm
  · apply joins_le _ _ _ M.vertex_le_components
    intro ab hab
    apply M.edge_le_components
    rw [← hpairs ab hab]
    exact SameCycle.rfl.apply_right
  · apply sup_le
    · exact le_joins _ _
    · have h₁ : SameCycle.setoid (1 : Perm D) ≤ SameCycle.setoid M.vertex := by
        intro a b hab
        exact (hab.eq_of_left rfl).sameCycle M.vertex
      have h := sameCycle_joins h₁ l
      simpa only [one_mul,hl] using h

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PlanarSubpairing
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

lemma joins_pairing (p q : Perm D) (l : List (D × D)) (hl : swaps l = q)
    (hpairs : ∀ ab ∈ l, q ab.1 = ab.2) :
    joins (SameCycle.setoid p) l = SameCycle.setoid p ⊔ SameCycle.setoid q := by
  apply le_antisymm
  · apply joins_le _ _ _ le_sup_left
    intro ab hab
    apply (show SameCycle.setoid q ≤ SameCycle.setoid p ⊔ SameCycle.setoid q from le_sup_right)
    rw [← hpairs ab hab]; exact SameCycle.rfl.apply_right
  · apply sup_le (le_joins _ _)
    have h₁ : SameCycle.setoid (1 : Perm D) ≤ SameCycle.setoid p := by
      intro a b hab; exact (hab.eq_of_left rfl).sameCycle p
    have h := sameCycle_joins h₁ l
    simpa only [one_mul,hl] using h

namespace PictureMap
variable (M : PictureMap D) (q : Perm D)
variable (hsub : ∀ x, q x = x ∨ q x = M.edge x)
include hsub

omit [DecidableEq D] [Fintype D] in
lemma subpairing_edge (x : D) : q (M.edge x) = M.edge (q x) := by
  rcases hsub x with hx | hx
  · rw [hx]
    rcases hsub (M.edge x) with he | he
    · exact he
    · rw [M.edge_edge] at he
      have hh := q.injective (he.trans hx.symm)
      exact False.elim (M.edge_ne x hh)
  · rw [hx,M.edge_edge]
    rcases hsub (M.edge x) with he | he
    · have hh := q.injective (hx.trans he.symm)
      exact False.elim ((M.edge_ne x) hh.symm)
    · simpa only [M.edge_edge] using he

omit [DecidableEq D] [Fintype D] in
lemma subpairing_sq : q * q = 1 := by
  ext x
  change q (q x) = x
  rcases hsub x with hx | hx
  · rw [hx,hx]
  · rw [hx,M.subpairing_edge q hsub x,hx,M.edge_edge]

omit [DecidableEq D] [Fintype D] in
lemma complement_subpairing (x : D) : (q * M.edge) x = x ∨ (q * M.edge) x = M.edge x := by
  rw [mul_apply,M.subpairing_edge q hsub x]
  rcases hsub x with hx | hx
  · exact Or.inr (congrArg M.edge hx)
  · exact Or.inl ((congrArg M.edge hx).trans (M.edge_edge x))

lemma complement_support : (q * M.edge).support = Finset.univ \ q.support := by
  ext x
  simp only [mem_support,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not]
  rw [mul_apply,M.subpairing_edge q hsub x]
  rcases hsub x with hx | hx
  · rw [hx]; exact ⟨fun _ => rfl,fun _ => M.edge_ne x⟩
  · rw [hx,M.edge_edge]
    simp only [ne_eq,not_true_eq_false]
    exact iff_of_false (fun h => h) (M.edge_ne x)

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SubpairingGraph
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

def subpairingGraph : SimpleGraph M.GraphVertex where
  Adj v w := v ≠ w ∧ ∃ x : D, M.vertexClass x = v ∧ M.vertexClass (q x) = w
  symm := ⟨by
    rintro v w ⟨hne,x,hx,he⟩
    refine ⟨hne.symm,q x,he,?_⟩
    have hh : q (q x) = x := congrArg (fun p : Perm D => p x) hq
    rw [hh]; exact hx⟩
  loopless := ⟨by rintro v ⟨h,_⟩; exact h rfl⟩

omit [DecidableEq D] in
lemma subpairing_reachable (x y : D)
    (h : (SameCycle.setoid M.vertex ⊔ SameCycle.setoid q) x y) :
    (M.subpairingGraph q hq).Reachable (M.vertexClass x) (M.vertexClass y) := by
  have hle : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q ≤
      Setoid.comap M.vertexClass (M.subpairingGraph q hq).reachableSetoid := by
    apply sup_le
    · intro a b hab
      change (M.subpairingGraph q hq).Reachable (M.vertexClass a) (M.vertexClass b)
      rw [(M.vertexClass_eq_iff a b).mpr hab]
    · apply sameCycle_le_of_apply
      intro a
      change (M.subpairingGraph q hq).Reachable (M.vertexClass a) (M.vertexClass (q a))
      by_cases he : M.vertexClass a = M.vertexClass (q a)
      · rw [he]
      · exact SimpleGraph.Adj.reachable ⟨he,a,rfl,rfl⟩
  exact hle h

omit [DecidableEq D] in
lemma subpairing_connected [Nonempty D]
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤) :
    (M.subpairingGraph q hq).Connected := by
  have : Nonempty M.GraphVertex := ⟨M.vertexClass (Classical.arbitrary D)⟩
  apply SimpleGraph.Connected.mk
  intro v w
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective v
  obtain ⟨y,rfl⟩ := Quotient.mk_surjective w
  apply M.subpairing_reachable q hq x y
  rw [hspan]; trivial

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphSubpairing
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
variable {D : Type*}
variable (M : PictureMap D)

/-- Retain all literal edge copies whose endpoints are adjacent in T.
Fixed darts are stubs; no parallel edge is silently identified. -/
def graphPairing (T : SimpleGraph M.GraphVertex) : Perm D :=
  Function.Involutive.toPerm (fun x => if T.Adj (M.vertexClass x) (M.vertexClass (M.edge x))
    then M.edge x else x) (by
    intro x
    by_cases h : T.Adj (M.vertexClass x) (M.vertexClass (M.edge x))
    · simp only [ite_eq_left h,M.edge_edge,ite_eq_left h.symm]
    · simp only [ite_eq_right h])

lemma graphPairing_apply (T : SimpleGraph M.GraphVertex) (x : D) :
    M.graphPairing T x = if T.Adj (M.vertexClass x) (M.vertexClass (M.edge x))
      then M.edge x else x := rfl

lemma graphPairing_sub (T : SimpleGraph M.GraphVertex) (x : D) :
    M.graphPairing T x = x ∨ M.graphPairing T x = M.edge x := by
  rw [M.graphPairing_apply]; split_ifs <;> simp

lemma graphPairing_graph (T : SimpleGraph M.GraphVertex) (hle : T ≤ M.underlyingGraph) :
    M.subpairingGraph (M.graphPairing T) (M.subpairing_sq _ (M.graphPairing_sub T)) = T := by
  ext v w
  constructor
  · rintro ⟨hne,x,rfl,rfl⟩
    rw [M.graphPairing_apply] at hne ⊢
    split_ifs at hne ⊢ with h
    · exact h
    · exact (hne rfl).elim
  · intro h
    obtain ⟨hne,x,hx,hy⟩ := hle h
    refine ⟨hne,x,hx,?_⟩
    rw [M.graphPairing_apply,ite_eq_left (by rwa [hx,hy])]
    exact hy

lemma subpairing_span_of_connected (q : Perm D) (hq : q*q = 1)
    (hc : (M.subpairingGraph q hq).Connected) :
    SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤ := by
  let s := SameCycle.setoid M.vertex ⊔ SameCycle.setoid q
  let f : M.GraphVertex → Quotient s := Quotient.map id (show SameCycle.setoid M.vertex ≤ s from le_sup_left)
  have hadj : ∀ {v w}, (M.subpairingGraph q hq).Adj v w → f v = f w := by
    rintro v w ⟨_,x,rfl,rfl⟩
    exact Quotient.sound ((show SameCycle.setoid q ≤ s from le_sup_right) (SameCycle.rfl.apply_right (f := q)))
  have hpath : ∀ {v w}, (M.subpairingGraph q hq).Walk v w → f v = f w := by
    intro v w p
    induction p with
    | nil => rfl
    | cons h p ih => exact (hadj h).trans ih
  apply top_unique
  intro x y _
  obtain ⟨p⟩ := hc (M.vertexClass x) (M.vertexClass y)
  exact Quotient.exact (hpath p)

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroFaceFilling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace
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
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- The source's fifteen-side bound read directly from the actual cyclic
macro-face parametrization, without identifying random letters. -/
lemma macro_parametrization_card (p : Perm D) (j : D → MacroGraph.graph.Dart)
    (hc : ∀ x, (j (p x)).fst = (j x).snd)
    (hi : Function.Injective (fun x => (j x).fst))
    (hb : ∀ x, p (p x) ≠ x) : Fintype.card D ≤ 15 := by
  let b := (Fintype.equivFin D).symm
  let Q : MacroGraph.Polygon := {
    n := Fintype.card D
    vertex := fun i => (j (b i)).fst
    next := b.trans (p.trans b.symm)
    injective := hi.comp b.injective
    adjacent := by
      intro i
      change MacroGraph.Adjacent (j (b i)).fst (j (b (b.symm (p (b i))))).fst
      rw [b.apply_symm_apply,hc]
      exact (j (b i)).adj
    no_backtrack := by
      intro i he
      have hh := congrArg b he
      simp only [Equiv.trans_apply,Equiv.apply_symm_apply] at hh
      exact hb (b i) hh }
  exact Q.perimeter_le

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PairingForest
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

variable [Fintype D]

lemma forestEdges_card (s : Setoid D) (l : List (D × D)) :
    (Nat.card (Quotient (joins s l)) : ℤ) + (forestEdges s l).length = Nat.card (Quotient s) := by
  induction l generalizing s with
  | nil => simp only [joins,forestEdges,List.length_nil,Nat.cast_zero,add_zero]
  | cons ab l ih =>
    simp only [forestEdges]
    split_ifs with h
    · rw [joins,glue_eq_of_rel _ _ _ h]; exact ih s
    · have hc := card_glue s ab.1 ab.2
      rw [ite_eq_right h] at hc
      have hh := ih (glue s ab.1 ab.2)
      simp only [joins,List.length_cons,Nat.cast_add,Nat.cast_one]
      omega

variable [DecidableEq D]

lemma forestEdges_cycles (p : Perm D) (s : Setoid D) (hp : SameCycle.setoid p ≤ s)
    (l : List (D × D)) :
    cycles (p * swaps (forestEdges s l)) = cycles p - (forestEdges s l).length := by
  induction l generalizing p s with
  | nil => simp only [forestEdges,swaps,List.map_nil,List.prod_nil,mul_one,List.length_nil,Nat.cast_zero,sub_zero]
  | cons ab l ih =>
    simp only [forestEdges]
    split_ifs with h
    · exact ih p s hp
    · have hh := ih (p * swap ab.1 ab.2) (glue s ab.1 ab.2) (sameCycle_glue hp _ _)
      have hc := cycles_merge_right p (fun hab => h (hp hab))
      have he : swaps (ab :: forestEdges (glue s ab.1 ab.2) l) =
          swap ab.1 ab.2 * swaps (forestEdges (glue s ab.1 ab.2) l) := rfl
      rw [he,← mul_assoc,hh]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      omega

namespace PictureMap
variable (M : PictureMap D)

omit [Fintype D] in
lemma swap_subpair (a b : D) (he : M.edge a = b) (x : D) :
    swap a b x = x ∨ swap a b x = M.edge x := by
  by_cases ha : x = a
  · subst x; exact Or.inr (by rw [swap_apply_left,he])
  by_cases hb : x = b
  · subst x; apply Or.inr
    rw [swap_apply_right,← he,M.edge_edge]
  · exact Or.inl (swap_apply_of_ne_of_ne ha hb)

omit [Fintype D] [DecidableEq D] in
lemma subpairing_mul (q r : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)
    (hr : ∀ x, r x = x ∨ r x = M.edge x) (x : D) :
    (q*r) x = x ∨ (q*r) x = M.edge x := by
  rw [mul_apply]
  rcases hr x with hx | hx
  · rw [hx]; exact hq x
  · rw [hx,M.subpairing_edge q hq x]
    rcases hq x with hy | hy
    · exact Or.inr (congrArg M.edge hy)
    · exact Or.inl ((congrArg M.edge hy).trans (M.edge_edge x))

omit [Fintype D] in
lemma swaps_subpairing (l : List (D × D)) (hl : ∀ ab ∈ l, M.edge ab.1 = ab.2) (x : D) :
    swaps l x = x ∨ swaps l x = M.edge x := by
  induction l generalizing x with
  | nil => exact Or.inl rfl
  | cons ab l ih =>
    apply M.subpairing_mul (swap ab.1 ab.2) (swaps l)
    · exact M.swap_subpair _ _ (hl _ (by simp))
    · exact ih (fun cd hc => hl cd (List.mem_cons_of_mem _ hc))

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureBoundaryParity
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

/-- A cyclic word cannot have just one change of color. The colors need not
be Boolean; the proof counts the occurrences of the color at the exceptional
position. This is the literal rotation-system boundary conservation law. -/
lemma perm_transition_not_unique {C : Type*} (p : Perm D) (color : D → C) (x : D)
    (hx : color (p x) ≠ color x) :
    ∃ y : D, y ≠ x ∧ p.SameCycle x y ∧ color (p y) ≠ color y := by
  classical
  by_contra h
  push Not at h
  let V := {y : D // p.SameCycle x y}
  let z : V := ⟨x,SameCycle.rfl⟩
  let r : Perm V := p.subtypePerm (fun y => sameCycle_apply_right)
  let f : V → ℕ := fun y => if color y.val = color x then 1 else 0
  have hz : f z = 1 := by simp [f,z]
  have hrz : f (r z) = 0 := by
    change (if color (p x) = color x then 1 else 0) = 0
    simp only [ite_eq_right hx]
  have hrest : ∀ y ∈ (Finset.univ : Finset V).erase z, f (r y) = f y := by
    intro y hy
    have hne : y.val ≠ x := fun he => (Finset.mem_erase.mp hy).1 (Subtype.ext he)
    have hc := h y.val hne y.property
    change (if color (p y.val) = color x then 1 else 0) =
      (if color y.val = color x then 1 else 0)
    rw [hc]
  have hs := Equiv.sum_comp r f
  have hs₁ := Finset.sum_erase_add (Finset.univ : Finset V) (f ∘ r) (Finset.mem_univ z)
  have hs₂ := Finset.sum_erase_add (Finset.univ : Finset V) f (Finset.mem_univ z)
  have he : ∑ y ∈ (Finset.univ : Finset V).erase z, (f ∘ r) y =
      ∑ y ∈ (Finset.univ : Finset V).erase z, f y := by
    apply Finset.sum_congr rfl
    exact hrest
  change (∑ y ∈ (Finset.univ : Finset V).erase z, (f ∘ r) y) + f (r z) = _ at hs₁
  rw [he,hrz] at hs₁
  rw [hz] at hs₂
  change (∑ y : V, f (r y)) = ∑ y : V, f y at hs
  simp only [Function.comp_apply] at hs₁
  omega

namespace PictureMap
variable (M : PictureMap D)

/-- If a coloring is constant around faces, every vertex incident to a
color-boundary edge has at least TWO distinct incident boundary darts.
Parallel edges and loops are retained; there is no simple-graph assumption. -/
theorem boundary_dart_not_unique {C : Type*} (color : D → C)
    (hface : ∀ x, color (M.face x) = color x) (x : D)
    (hx : color (M.edge x) ≠ color x) :
    ∃ y : D, y ≠ x ∧ M.vertexClass y = M.vertexClass x ∧
      color (M.edge y) ≠ color y := by
  have hv : ∀ y, color (M.vertex y) = color (M.edge y) := by
    intro y
    exact hface (M.edge y)
  obtain ⟨y,hne,hcycle,hy⟩ := perm_transition_not_unique M.vertex color x (by rwa [hv])
  refine ⟨y,hne,(M.vertexClass_eq_iff y x).mpr hcycle.symm,?_⟩
  rwa [hv] at hy

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureLeaf
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

lemma cycles_le_half_of_no_fixed (p : Perm D) (h : ∀ x, p x ≠ x) :
    2 * cycles p ≤ Fintype.card D := by
  have hb : ∀ s : Multiset ℕ, (∀ t ∈ s, 2 ≤ t) → 2*s.card ≤ s.sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      intro hs
      have ha := hs a (by simp)
      have hi := ih (fun t ht => hs t (by simp [ht]))
      simp only [Multiset.card_cons,Multiset.sum_cons]
      omega
  have hc := hb p.cycleType (fun _ hm => two_le_of_mem_cycleType hm)
  have hs : p.support = Finset.univ := by ext x; simp [mem_support,h x]
  rw [sum_cycleType,hs,Finset.card_univ] at hc
  simp only [cycles,defect,hs,Finset.card_univ]
  omega

lemma IsBoundary.cycles_eq_one {p : Perm D} {xs : List D}
    (h : IsBoundary p xs) (hall : ∀ x, x ∈ xs) (hne : xs ≠ []) : cycles p = 1 := by
  have hp : p = xs.formPerm := by ext x; exact h.turn x (hall x)
  have hf : xs.toFinset = Finset.univ := by ext x; simp [hall x]
  have hl : xs.length = Fintype.card D := by
    rw [← List.toFinset_card_of_nodup h.nodup,hf,Finset.card_univ]
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a s =>
    rw [hp,cycles,defect_list a s h.nodup]
    simp only [List.length_cons] at hl
    omega

/-- A one-face genus-zero side pairing has a genuine valence-one vertex.
The genus assumption is essential: the analogous torus pairing has none. -/
theorem PictureMap.single_face_leaf (M : PictureMap D) (hG : M.GenusZero)
    {xs : List D} (hb : IsBoundary M.face xs) (hall : ∀ x, x ∈ xs)
    (hne : xs ≠ []) : ∃ x, M.face (M.edge x) = x := by
  have : Nonempty D := by
    cases xs with
    | nil => exact False.elim (hne rfl)
    | cons a xs => exact ⟨a⟩
  have : Nonempty (Quotient M.components) := ⟨Quotient.mk _ (Classical.choice ‹Nonempty D›)⟩
  have hco : 0 < Nat.card (Quotient M.components) := Nat.card_pos
  have hf := hb.cycles_eq_one hall hne
  by_contra hn
  push Not at hn
  have hv := cycles_le_half_of_no_fixed M.vertex hn
  change M.euler = _ at hG
  rw [PictureMap.euler,hf] at hG
  omega

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonBoundaryList
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

/-- The literal positive indexed attaching word, with no quotienting of
repeated labels or cyclic starting positions. -/
def positiveSides (c : C) : List B.Side :=
  (List.finRange (B.size c)).map (fun i => ⟨c,true,i⟩)

lemma positiveSides_boundary (c : C) : IsBoundary B.next (B.positiveSides c) := by
  change IsBoundary B.next ((List.finRange (B.size c)).map (fun i => (⟨c,true,i⟩ : B.Side)))
  apply (finRange_boundary (B.size c)).map (fun i : Fin (B.size c) => (⟨c,true,i⟩ : B.Side))
  · intro x y h
    exact Prod.mk.inj (eq_of_heq (Sigma.mk.inj h).2) |>.2
  · intro x
    rfl

end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
variable {A B : Type*}
variable (c : A × Bool → Word B) (hc : ∀ e, c (e.1,!e.2) = FreeGroup.invRev (c e))

include hc

lemma substitute_reverse (z : Word A) :
    (FreeGroup.invRev z).flatMap c = FreeGroup.invRev (z.flatMap c) := by
  induction z with
  | nil => rfl
  | cons e z ih =>
    rw [FreeGroup.invRev_cons,List.flatMap_append,ih,List.flatMap_cons,FreeGroup.invRev_append]
    congr 1
    change c (e.1,!e.2) ++ [] = FreeGroup.invRev (c e)
    simpa only [List.append_nil] using hc e

lemma substitute_free_step {z t : Word A} (h : FreeGroup.Red.Step z t) :
    FreeGroup.mk (z.flatMap c) = FreeGroup.mk (t.flatMap c) := by
  cases h with
  | @not l r x b =>
    simp only [List.flatMap_append,List.flatMap_cons]
    rw [hc (x,b)]
    simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk]
    group

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPicturePeel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]
namespace PictureMap
variable (M : PictureMap D) {a : D} {xs : List D}

lemma eraseEdge_other_boundary (h : IsBoundary M.face xs)
    (ha : a ∉ xs) (hb : M.edge a ∉ xs) :
    IsBoundary (M.eraseEdge a).face
      (xs.attachWith (OffPair a (M.edge a))
        (fun _ hx => ⟨fun he => ha (he ▸ hx), fun he => hb (he ▸ hx)⟩)) := by
  apply h.lift
  intro x hx
  have hxa : x ≠ a := fun he => ha (he ▸ hx)
  have hxb : x ≠ M.edge a := fun he => hb (he ▸ hx)
  have hfa : M.face x ≠ a := fun he => ha (he ▸ h.invariant hx)
  have hfb : M.face x ≠ M.edge a := fun he => hb (he ▸ h.invariant hx)
  change bypassPair (M.face*swap a (M.edge a)) a (M.edge a) x = M.face x
  rw [bypassPair,bypass_away _ _ _ hxb,bypass_away _ _ _ hxa]
  simp only [mul_apply,swap_apply_of_ne_of_ne hxa hxb,ite_eq_right hfa,ite_eq_right hfb]

end PictureMap
end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w : Word A}
variable (P : WordPicture R w)

/-- Peeling a genuine interior face adjacent to the outside deletes one
paired edge and retains every other indexed relator boundary and label. -/
def peelAt {a : P.Dart} {l r : List P.Dart} (he : P.outside = a::l)
    (hr : IsBoundary P.pairing.face (P.pairing.edge a::r))
    (hne : ¬ P.pairing.face.SameCycle a (P.pairing.edge a)) :
    WordPicture R ((r++l).map P.label) := by
  have hl : IsBoundary P.pairing.face (a::l) := he ▸ P.boundary
  have hs := hl.splice_heads hr (hl.disjoint hr (by simp) (by simp) hne)
  have hp := IsBoundary.splice_heads_offpair hs.nodup
  let M := P.pairing.eraseEdge a
  refine {
    Dart := {x // OffPair a (P.pairing.edge a) x}
    pairing := M
    genusZero := P.pairing.eraseEdge_genusZero a P.genusZero hne
    label := P.label ∘ Subtype.val
    paired := fun x => P.paired x.val
    outside := (r++l).attachWith (OffPair a (P.pairing.edge a)) hp
    boundary := ?_
    word := List.attachWith_map_val hp
    interior := ?_ }
  · apply hs.erase_head.erase_at.lift hp
    intro x hx
    rfl
  · intro x hx
    have hxrl : x.val ∉ r++l := fun h => hx ((List.mem_attachWith hp x).mpr h)
    have hxo : x.val ∉ P.outside := by
      rw [he]
      intro hm
      rcases List.mem_cons.mp hm with h | h
      · exact x.property.1 h
      · exact hxrl (List.mem_append_right _ h)
    have hxi : x.val ∉ P.pairing.edge a::r := by
      intro hm
      rcases List.mem_cons.mp hm with h | h
      · exact x.property.2 h
      · exact hxrl (List.mem_append_left _ h)
    obtain ⟨xs,hxs,hxm,hrel⟩ := P.interior x.val hxo
    have ha : a ∉ xs := by
      intro ha
      exact hxo (P.boundary.mem_of_sameCycle (by rw [he]; simp) (hxs.sameCycle ha hxm))
    have hb : P.pairing.edge a ∉ xs := by
      intro hb
      exact hxi (hr.mem_of_sameCycle (by simp) (hxs.sameCycle hb hxm))
    have hp' : ∀ y ∈ xs, OffPair a (P.pairing.edge a) y :=
      fun y hy => ⟨fun he => ha (he ▸ hy),fun he => hb (he ▸ hy)⟩
    refine ⟨xs.attachWith _ hp',P.pairing.eraseEdge_other_boundary hxs ha hb,
      (List.mem_attachWith hp' x).mpr hxm,?_⟩
    simpa only [Function.comp_def,List.attachWith_map_val] using hrel

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace PolygonTarget.Boundary
variable {C L V : Type*} (B : Boundary C L V)

/-- The two orientations have exactly the same indexed perimeter. -/
lemma oriented_boundary (s : B.Side) :
    ∃ ys : List B.Side, IsBoundary B.next ys ∧ s ∈ ys ∧ ys.length = B.size s.1 := by
  rcases s with ⟨c,b,i⟩
  cases b with
  | true =>
    refine ⟨B.positiveSides c,B.positiveSides_boundary c,?_,?_⟩
    · exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    · simp only [positiveSides,List.length_map,List.length_finRange]
  | false =>
    have hp := B.positiveSides_boundary c
    have hh : IsBoundary B.next ((B.positiveSides c).reverse.map B.opposite) := by
      apply hp.reverse.map B.opposite B.opposite.injective
      intro s
      simpa only [Perm.inv_def,Equiv.apply_symm_apply] using
        (congrArg B.next (B.reverse_next (B.next⁻¹ s))).symm
    refine ⟨(B.positiveSides c).reverse.map B.opposite,hh,?_,?_⟩
    · apply List.mem_map.mpr
      refine ⟨⟨c,true,i⟩,List.mem_reverse.mpr ?_,rfl⟩
      exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    · simp only [List.length_map,List.length_reverse,positiveSides,List.length_finRange]
end PolygonTarget.Boundary

end HyperbolicObstruction.PictureSwitch

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativePartition
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
variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
variable (P : PictureMap X) (active : X → Prop) (part : X → I)

/-- One side of a selected INTERIOR fragment. The complement includes the
protected outside, even when its arbitrary partition label agrees. -/
abbrev RelativePartBoundary (i : I) :=
  {x : X // active x ∧ part x = i ∧ ¬ (active (P.edge x) ∧ part (P.edge x) = i)}
instance instFintypeRelativePartBoundary (i : I) : Fintype (RelativePartBoundary P active part i) := Fintype.ofFinite _

abbrev RelativeCutContact := {x : X // active x ∧ active (P.edge x) ∧
  part x ≠ part (P.edge x) ∧ P.number x < P.number (P.edge x)}
instance instFintypeRelativeCutContact : Fintype (RelativeCutContact P active part) := Fintype.ofFinite _

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTopTurns
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace
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
abbrev TopTurnDart := {x : P.Dart // select (P.faceClass x) = true ∧
  isApex n w (start n w (walkLabel n w d (P.index x))) = true ∧
  walkFree n w d (walkKind n w d (P.index x)) = true}

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WeightedRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences.Shape.Weights

variable {s u q v : ℕ}

lemma layer_card {I : Type*} [Fintype I] (r : I → ℕ) (K : ℕ) (h : ∀ i, r i ≤ K) :
    (∑ j ∈ Finset.range K, (Fintype.card {i : I // j < r i} : ℝ)) = ∑ i, (r i : ℝ) := by
  classical
  have hh := Coincidence.layer_cake Finset.univ r K (fun i _ => h i)
  exact_mod_cast (by simpa only [Fintype.card_subtype] using hh :
    (∑ j ∈ Finset.range K, Fintype.card {i : I // j < r i}) = ∑ i, r i)

end IncidenceTemplate.Occurrences.Shape.Weights
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)}

lemma cycles_positive {D : Type*} [DecidableEq D] [Fintype D] (p : Perm D) (a : D) :
    1 ≤ cycles p := by
  rw [cycles_eq_card_classes]
  let : Nonempty (Quotient (SameCycle.setoid p)) := ⟨Quotient.mk _ a⟩
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end


