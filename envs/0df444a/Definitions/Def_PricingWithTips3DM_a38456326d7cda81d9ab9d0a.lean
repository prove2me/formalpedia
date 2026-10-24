-- Prove2me | Definitions.Def_PricingWithTips3DM_a38456326d7cda81d9ab9d0a
-- name    : PricingWithTips3DM_a38456326d7cda81d9ab9d0a
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:41:19.71861+00:00
-- url     : https://prove2.me/theorems/33307cc0-bd6b-491d-844f-13d10f30156b
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeLiteralSelectorSemantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_e03766dbf7bc257325d78e21
import Definitions.Def_PricingWithTips3DM_a08d30f6b66a2a276a87ce8f
import Definitions.Def_PricingWithTips3DM_d6bf031a4c170e9e4c6ac0fd
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Exact semantics of the literal-test selector. -/

namespace PricingWithTips.FixedShapeLiteralSelectorSemantics

open CLRS.Chapter34
open Hardness.Cert.SatToMatching3DCode
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
open CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream
open CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter
open PricingWithTips.FixedShape3DM
open PricingWithTips.FixedShapeLiteralCandidatesTM2
open PricingWithTips.FixedShapeLiteralMembershipTM2
open PricingWithTips.FixedShapeLiteralSelectorTM2
open PricingWithTips.FixedShapeLiteralKeySemantics
open PricingWithTips.FixedShapeLiteralKeyTableSemantics
open PricingWithTips.FixedShapePairPayloadSemantics
open PricingWithTips.FixedShapeLiteralOrdinalArithmetic
open PricingWithTips.FixedShapeSparseCells
open PricingWithTips.FixedShapeCell

theorem pair_mem_certificateRawPairs_append
    (left right : List Nat) (a b : Nat)
    (ha : a ∈ left) (hb : b ∈ right) :
    (a, b) ∈ certificateRawPairs (left ++ right) := by
  induction right using List.reverseRecOn with
  | nil => simp at hb
  | append_singleton right last ih =>
      rw [List.mem_append, List.mem_singleton] at hb
      rw [← List.append_assoc, certificateRawPairs_append_singleton,
        List.mem_append]
      rcases hb with hb | rfl
      · exact Or.inl (ih hb)
      · exact Or.inr (List.mem_map.mpr
          ⟨a, List.mem_append_left right ha, rfl⟩)

theorem taggedKey_mem_rawCandidatePairs (input : List CNFSym)
    (key : Nat × Nat) (hkey : key ∈ certifiedFormulaKeys (paddedCNF input)) :
    taggedKey key ∈ rawCandidatePairs input := by
  obtain ⟨q, clause, hclause, literal, hliteral, rfl⟩ :=
    (mem_certifiedFormulaKeys_iff (paddedCNF input) key).mp hkey
  obtain ⟨hq, hclause'⟩ := List.getElem?_eq_some_iff.mp hclause
  have hqL : q < input.length := by
    simpa [paddedCNF_length] using hq
  have hclauseMem : clause ∈ paddedCNF input := by
    have := List.getElem_mem (l := paddedCNF input) hq
    simpa [hclause'] using this
  have hvL : literal.var < input.length := by
    simpa [variableList] using variable_coverage input clause hclauseMem
      literal hliteral
  rw [rawCandidatePairs, candidateVertices, List.append_assoc]
  apply pair_mem_certificateRawPairs_append
  · simp [taggedKey, certifiedLiteralKey, hqL]
  · cases literal with
    | mk v polarity =>
        have hv : v < input.length := hvL
        cases polarity with
        | false =>
            simp_all [taggedKey, certifiedLiteralKey, bitOf]
            exact Or.inl ⟨v, by omega, by omega⟩
        | true =>
            simp_all [taggedKey, certifiedLiteralKey, bitOf]
            exact Or.inr ⟨v, by omega, by omega⟩

private theorem selectedEdges_map_not_membership
    (table : List (Nat × Nat))
    (f : (Nat × Nat) → (Nat × Nat))
    (source : List (Nat × Nat)) :
    Selector.selectedEdges (source.map f)
        (source.map fun x => Bool.not (decide (x ∈ table))) =
      (source.filter fun x => x ∈ table).map f := by
  induction source with
  | nil => rfl
  | cons x source ih =>
      by_cases hx : x ∈ table <;>
        simp [Selector.selectedEdges, hx, ih]

theorem selectedStructuralPairs_eq (input : List CNFSym) :
    selectedStructuralPairs input =
      ((rawCandidatePairs input).filter fun edge =>
          edge ∈ allTaggedKeys input).map
        (fun pair =>
          (structuralize input.length pair.1,
            structuralize input.length pair.2)) := by
  simp only [selectedStructuralPairs, alignedInput,
    Selector.alignedSelectedEdges, retainBits, literalMembershipBits,
    literalKeyInstance, rawStructuralPairs_eq_map]
  rw [List.map_map]
  change Selector.selectedEdges
      ((rawCandidatePairs input).map fun pair =>
        (structuralize input.length pair.1,
          structuralize input.length pair.2))
      ((rawCandidatePairs input).map fun edge =>
        Bool.not (decide (edge ∈ allTaggedKeys input))) = _
  rw [selectedEdges_map_not_membership]

@[simp] theorem structuralize_tagged_certifiedLiteralKey
    (L q : Nat) (literal : Hardness.Literal Nat) :
    (structuralize L (taggedKey (certifiedLiteralKey q literal)).1,
      structuralize L (taggedKey (certifiedLiteralKey q literal)).2) =
      (clauseContribution L q, literalBase L literal.var literal.polarity) := by
  rcases literal with ⟨v, polarity⟩
  cases polarity with
  | false =>
      change (structuralize L (2 * q), structuralize L (2 * (2 * v) + 1)) = _
      rw [show 2 * (2 * v) + 1 = 4 * v + 1 by omega]
      simp
  | true =>
      change (structuralize L (2 * q),
        structuralize L (2 * (2 * v + 1) + 1)) = _
      rw [show 2 * (2 * v + 1) + 1 = 4 * v + 3 by omega]
      simp

theorem structuralize_tagged_certifiedLiteralKey_sum
    (L q : Nat) (literal : Hardness.Literal Nat) :
    structuralize L (taggedKey (certifiedLiteralKey q literal)).1 +
        structuralize L (taggedKey (certifiedLiteralKey q literal)).2 =
      literalBase L literal.var literal.polarity + clauseContribution L q := by
  have h := structuralize_tagged_certifiedLiteralKey L q literal
  have hleft := congrArg Prod.fst h
  have hright := congrArg Prod.snd h
  omega

theorem mem_selectedStructuralPairs_iff (input : List CNFSym)
    (pair : Nat × Nat) :
    pair ∈ selectedStructuralPairs input ↔
      ∃ key, key ∈ certifiedFormulaKeys (paddedCNF input) ∧
        pair =
          (structuralize input.length (taggedKey key).1,
            structuralize input.length (taggedKey key).2) := by
  rw [selectedStructuralPairs_eq]
  constructor
  · intro hpair
    obtain ⟨tagged, htaggedFilter, hp⟩ := List.mem_map.mp hpair
    obtain ⟨_, htagged⟩ := List.mem_filter.mp htaggedFilter
    obtain ⟨key, hkey, rfl⟩ := (mem_allTaggedKeys_iff input tagged).mp
      (of_decide_eq_true htagged)
    exact ⟨key, hkey, hp.symm⟩
  · rintro ⟨key, hkey, rfl⟩
    apply List.mem_map.mpr
    refine ⟨taggedKey key, List.mem_filter.mpr ⟨
      taggedKey_mem_rawCandidatePairs input key hkey, ?_⟩, rfl⟩
    have hall : taggedKey key ∈ allTaggedKeys input :=
      (mem_allTaggedKeys_iff input (taggedKey key)).mpr ⟨key, hkey, rfl⟩
    simpa using hall

theorem mem_literalEdges_iff (input : List CNFSym) (edge : Nat × Nat) :
    edge ∈ literalEdges input ↔
      edge ∈ (testTriples input).map
        (fun t => (0, ordinal (dimension input) t)) := by
  constructor
  · intro hedge
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hedge
    obtain ⟨key, hkey, rfl⟩ :=
      (mem_selectedStructuralPairs_iff input pair).mp hpair
    obtain ⟨q, clause, hclause, literal, hliteral, rfl⟩ :=
      (mem_certifiedFormulaKeys_iff (paddedCNF input) key).mp hkey
    let t : FixedShapeCell.Triple :=
      (extIdxN input.length literal.var q (bitOf literal.polarity),
        (testIdxN input.length input.length q,
          testIdxN input.length input.length q))
    apply List.mem_map.mpr
    refine ⟨t, ?_, ?_⟩
    · apply (mem_testTriples_iff input t).mpr
      apply (testCell_iff input t).mpr
      refine ⟨(clause, q), ?_, literal, hliteral, rfl⟩
      rw [List.mem_zipIdx_iff_getElem?]
      exact hclause
    · simp only [structuralize_tagged_certifiedLiteralKey]
      apply Prod.ext
      · rfl
      · simp only [t]
        rw [show dimension input = dimensionValue input.length by
          simp [dimension, dimensionValue, variableList, paddedCNF_length]]
        rw [show bitOf literal.polarity = literal.polarity.toNat by
          cases literal.polarity <;> rfl]
        rw [test_ordinal_eq_contributions]
        rw [structuralize_tagged_certifiedLiteralKey_sum]
  · intro hedge
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hedge
    have htest := (mem_testTriples_iff input t).mp ht
    obtain ⟨qpair, hqpair, literal, hliteral, rfl⟩ :=
      (testCell_iff input t).mp htest
    rw [List.mem_zipIdx_iff_getElem?] at hqpair
    let key := certifiedLiteralKey qpair.2 literal
    have hkey : key ∈ certifiedFormulaKeys (paddedCNF input) := by
      apply (mem_certifiedFormulaKeys_iff (paddedCNF input) key).mpr
      exact ⟨qpair.2, qpair.1, hqpair, literal, hliteral, rfl⟩
    apply List.mem_map.mpr
    refine ⟨(structuralize input.length (taggedKey key).1,
      structuralize input.length (taggedKey key).2),
      (mem_selectedStructuralPairs_iff input _).mpr ⟨key, hkey, rfl⟩, ?_⟩
    simp only [key]
    apply Prod.ext
    · rfl
    · simp only
      rw [structuralize_tagged_certifiedLiteralKey_sum]
      rw [show dimension input = dimensionValue input.length by
        simp [dimension, dimensionValue, variableList, paddedCNF_length]]
      rw [show bitOf literal.polarity = literal.polarity.toNat by
        cases literal.polarity <;> rfl]
      rw [test_ordinal_eq_contributions]

theorem query_mem_literalEdges_iff (input : List CNFSym)
    (t : FixedShapeCell.Triple)
    (hb : t.1 < dimension input) (hs : t.2.1 < dimension input)
    (hd : t.2.2 < dimension input) :
    (0, ordinal (dimension input) t) ∈ literalEdges input ↔
      testCell input t = true := by
  rw [mem_literalEdges_iff]
  constructor
  · intro hedge
    obtain ⟨u, hu, hedgeEq⟩ := List.mem_map.mp hedge
    have htestu := (mem_testTriples_iff input u).mp hu
    have hcellu : cell input u = true := by
      simp [cell, htestu]
    rcases PricingWithTips.FixedShapeOrdinal.cell_true_bounds input u hcellu with
      ⟨hub, hus, hud⟩
    have hord : ordinal (dimension input) u = ordinal (dimension input) t := by
      exact congrArg Prod.snd hedgeEq
    have hut := PricingWithTips.FixedShapeOrdinal.ordinal_injective_of_lt
      (dimension input) u t hus hud hs hd hord
    simpa [hut] using htestu
  · intro htest
    apply List.mem_map.mpr
    exact ⟨t, (mem_testTriples_iff input t).mpr htest, rfl⟩

end PricingWithTips.FixedShapeLiteralSelectorSemantics


