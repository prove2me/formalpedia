-- Prove2me | Definitions.Def_PricingWithTips3DM_d15dc1bc5c68c26e893b7ba8
-- name    : PricingWithTips3DM_d15dc1bc5c68c26e893b7ba8
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:11:09.262869+00:00
-- url     : https://prove2.me/theorems/5e5e5d60-552f-4915-bf4d-040b518e7be0
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapePaddingSelectorSemantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_89548ba1d154810acde5067a
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShapePaddingSelectorSemantics

open CLRS.Chapter34
open CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeClauseMembershipTM2
open PricingWithTips.FixedShapePaddingSelectorTM2
open PricingWithTips.FixedShapePaddingKeysTM2
open PricingWithTips.FixedShapeLiteralMembershipTM2

private theorem selectedEdges_append
    (left right : List (Nat × Nat)) (leftBits rightBits : List Bool)
    (h : left.length = leftBits.length) :
    Selector.selectedEdges (left ++ right) (leftBits ++ rightBits) =
      Selector.selectedEdges left leftBits ++
        Selector.selectedEdges right rightBits := by
  induction left generalizing leftBits with
  | nil =>
      have : leftBits = [] := List.eq_nil_of_length_eq_zero h.symm
      subst leftBits
      rfl
  | cons item left ih =>
      cases leftBits with
      | nil => simp at h
      | cons bit bits =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          cases bit <;> simp [Selector.selectedEdges, ih bits h]

private theorem selectedEdges_map_not {α : Type}
    (items : List α) (value : α → Nat × Nat) (present : α → Bool) :
    Selector.selectedEdges (items.map value)
        ((items.map present).map Bool.not) =
      (items.filter fun item => present item).map value := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      cases h : present item <;>
        simp [Selector.selectedEdges, h, List.map_map] at ih ⊢ <;>
        exact ih

theorem selectedPaddingEdges_eq (input : List CNFSym) :
    selectedPaddingEdges input =
      ((List.range input.length).filter fun q =>
          decide ((baseCNF input).length ≤ q)).map (fun q => (q, 0)) ++
      ((List.range input.length).filter fun q =>
          decide ((baseCNF input).length ≤ q)).map (fun q => (q, 1)) := by
  unfold selectedPaddingEdges Selector.alignedSelectedEdges
  simp only [PricingWithTips.FixedShapePaddingSelectorTM2.alignedInput,
    retainPaddingBits, duplicatedPaddingBits, allPaddingCandidates,
    paddingClauseMembershipBits_eq, List.map_append]
  rw [selectedEdges_append]
  · rw [selectedEdges_map_not, selectedEdges_map_not]
  · simp

theorem mem_selectedPaddingEdges_iff (input : List CNFSym)
    (edge : Nat × Nat) :
    edge ∈ selectedPaddingEdges input ↔
      ∃ q, q < input.length ∧ (baseCNF input).length ≤ q ∧
        (edge = (q, 0) ∨ edge = (q, 1)) := by
  rw [selectedPaddingEdges_eq]
  simp only [List.mem_append, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  constructor
  · rintro (⟨q, ⟨hq, hbase⟩, rfl⟩ | ⟨q, ⟨hq, hbase⟩, rfl⟩)
    · exact ⟨q, hq, hbase, Or.inl rfl⟩
    · exact ⟨q, hq, hbase, Or.inr rfl⟩
  · rintro ⟨q, hq, hbase, rfl | rfl⟩
    · exact Or.inl ⟨q, ⟨hq, hbase⟩, rfl⟩
    · exact Or.inr ⟨q, ⟨hq, hbase⟩, rfl⟩

end PricingWithTips.FixedShapePaddingSelectorSemantics


