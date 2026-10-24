-- Prove2me | Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Clause
-- name    : PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Clause
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T04:22:02.14023+00:00
-- url     : https://prove2.me/theorems/70b2118e-972e-4a8f-944f-ec9a94863d41
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesBounds.Part1.Lemma2.Clause
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_188c204bbb0abeaa041ddea5Part1Vertex
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

theorem value_le_encodeUnaryFrame_length {value : Nat} {values : List Nat}
    (hvalue : value ∈ values) : value ≤ (encodeUnaryFrame values).length := by
  rw [encodeUnaryFrame_length]
  have hm : value + 1 ∈ values.map (fun item => item + 1) :=
    List.mem_map.mpr ⟨value, hvalue, rfl⟩
  exact (Nat.le_succ value).trans (List.le_sum_of_mem hm)

theorem entry_clause_le_entry_length (entry : IndexedOccurrence × Nat) :
    entry.1.clauseIndex ≤ (encodeIndexedOccurrenceEntry entry).length := by
  have h := value_le_encodeUnaryFrame_length
    (value := entry.1.clauseIndex)
    (values := indexedOccurrenceRowValues entry.2 entry.1)
    (by simp [indexedOccurrenceRowValues])
  simpa [encodeIndexedOccurrenceEntry] using
    h.trans (Nat.le_add_right (encodeUnaryFrame
      (indexedOccurrenceRowValues entry.2 entry.1)).length 1)

end CLRS.Chapter34.Turing.TMClique


