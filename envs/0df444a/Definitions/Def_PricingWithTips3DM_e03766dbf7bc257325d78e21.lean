-- Prove2me | Definitions.Def_PricingWithTips3DM_e03766dbf7bc257325d78e21
-- name    : PricingWithTips3DM_e03766dbf7bc257325d78e21
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:18:40.669448+00:00
-- url     : https://prove2.me/theorems/6f1b0054-a234-4428-9e88-960daecb2a32
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeLiteralKeyTableSemantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_d15dc1bc5c68c26e893b7ba8
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

namespace PricingWithTips.FixedShapeLiteralKeyTableSemantics

open CLRS.Chapter34
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeLiteralKeySemantics
open PricingWithTips.FixedShapeLiteralMembershipTM2
open PricingWithTips.FixedShapePaddingSelectorSemantics

theorem mem_certifiedFormulaKeysFrom_iff (start : Nat)
    (formula : Hardness.CNF Nat) (key : Nat × Nat) :
    key ∈ certifiedFormulaKeysFrom start formula ↔
      ∃ offset clause, formula[offset]? = some clause ∧
        ∃ literal, literal ∈ clause ∧
          certifiedLiteralKey (start + offset) literal = key := by
  induction formula generalizing start with
  | nil => simp [certifiedFormulaKeysFrom]
  | cons clause formula ih =>
      simp only [certifiedFormulaKeysFrom, List.mem_append,
        List.length_cons]
      rw [ih (start + 1)]
      simp only [certifiedClauseKeys, List.mem_map]
      constructor
      · rintro (⟨literal, hliteral, rfl⟩ |
            ⟨offset, tailClause, htail, literal, hliteral, rfl⟩)
        · exact ⟨0, clause, rfl, literal, hliteral, by simp⟩
        · exact ⟨offset + 1, tailClause, by simpa using htail,
            literal, hliteral, by
            congr 1
            omega⟩
      · rintro ⟨offset, foundClause, hfound, literal, hliteral, hkey⟩
        cases offset with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hfound
            subst foundClause
            left
            exact ⟨literal, hliteral, by simpa using hkey⟩
        | succ offset =>
            right
            exact ⟨offset, foundClause, by simpa using hfound,
              literal, hliteral, by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkey⟩

theorem mem_certifiedFormulaKeys_iff (formula : Hardness.CNF Nat)
    (key : Nat × Nat) :
    key ∈ certifiedFormulaKeys formula ↔
      ∃ q clause, formula[q]? = some clause ∧ ∃ literal, literal ∈ clause ∧
        certifiedLiteralKey q literal = key := by
  simpa [certifiedFormulaKeys] using
    mem_certifiedFormulaKeysFrom_iff 0 formula key

theorem mem_paddingKeysFrom_iff (start count : Nat) (key : Nat × Nat) :
    key ∈ paddingKeysFrom start count ↔
      ∃ q, start ≤ q ∧ q < start + count ∧
        (key = (q, 1) ∨ key = (q, 0)) := by
  induction count generalizing start with
  | zero =>
      simp [paddingKeysFrom]
      omega
  | succ count ih =>
      rw [paddingKeysFrom]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false]
      rw [ih (start + 1)]
      constructor
      · rintro ((h1 | h0) | ⟨q, hq, hlt, hk⟩)
        · rw [h1]
          exact ⟨start, le_rfl, by omega, Or.inl rfl⟩
        · rw [h0]
          exact ⟨start, le_rfl, by omega, Or.inr rfl⟩
        · exact ⟨q, by omega, by omega, hk⟩
      · rintro ⟨q, hq, hlt, hk⟩
        by_cases heq : q = start
        · subst q
          rcases hk with rfl | rfl
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr rfl)
        · exact Or.inr ⟨q, by omega, by omega, hk⟩

theorem mem_paddingKeys_selected_iff (input : List CNFSym)
    (key : Nat × Nat) :
    key ∈ paddingKeysFrom (baseCNF input).length
          (input.length - (baseCNF input).length) ↔
      key ∈ selectedPaddingEdges input := by
  rw [mem_paddingKeysFrom_iff,
    PricingWithTips.FixedShapePaddingSelectorSemantics.mem_selectedPaddingEdges_iff]
  have hle := baseCNF_length_le input
  rw [Nat.add_sub_of_le hle]
  constructor
  · rintro ⟨q, hbase, hq, hkey⟩
    exact ⟨q, hq, hbase, hkey.elim Or.inr Or.inl⟩
  · rintro ⟨q, hq, hbase, hkey⟩
    exact ⟨q, hbase, hq, hkey.elim Or.inr Or.inl⟩

theorem mem_allTaggedKeys_iff (input : List CNFSym)
    (edge : Nat × Nat) :
    edge ∈ allTaggedKeys input ↔
      ∃ key, key ∈ certifiedFormulaKeys (paddedCNF input) ∧
        taggedKey key = edge := by
  rw [certifiedFormulaKeys_paddedCNF]
  simp only [allTaggedKeys, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨key, hkey, rfl⟩ | ⟨key, hkey, rfl⟩)
    · exact ⟨key, Or.inl hkey, rfl⟩
    · exact ⟨key, Or.inr ((mem_paddingKeys_selected_iff input key).2 hkey), rfl⟩
  · rintro ⟨key, hbase | hpadding, rfl⟩
    · exact Or.inl ⟨key, hbase, rfl⟩
    · exact Or.inr ⟨key,
        (mem_paddingKeys_selected_iff input key).1 hpadding, rfl⟩

end PricingWithTips.FixedShapeLiteralKeyTableSemantics


