-- Prove2me | Definitions.Def_PricingWithTips3DM_d6bf031a4c170e9e4c6ac0fd
-- name    : PricingWithTips3DM_d6bf031a4c170e9e4c6ac0fd
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:32:17.9133+00:00
-- url     : https://prove2.me/theorems/1f5baf88-0383-440b-9767-7298e409d4e9
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapePairPayloadSemantics
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_2debcc86a25e56c040470795
import Definitions.Def_PricingWithTips3DM_2cc611cce1fcd18f55c4e8e3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Payload functoriality for the verified positional pair generator. -/

namespace PricingWithTips.FixedShapePairPayloadSemantics

open CLRS.Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
open CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream
open PricingWithTips.FixedShapeLiteralCandidatesTM2
open PricingWithTips.FixedShapeStructuralCandidatesTM2
open PricingWithTips.FixedShapeLiteralOrdinalArithmetic

theorem certificateRawPairs_map (f : Nat → Nat) (vertices : List Nat) :
    certificateRawPairs (vertices.map f) =
      (certificateRawPairs vertices).map
        (fun pair => (f pair.1, f pair.2)) := by
  induction vertices using List.reverseRecOn with
  | nil => rfl
  | append_singleton vertices vertex ih =>
      rw [List.map_append, List.map_singleton,
        certificateRawPairs_append_singleton,
        certificateRawPairs_append_singleton, ih]
      simp [List.map_append, List.map_map, Function.comp_def]

def structuralize (L key : Nat) : Nat :=
  if key % 2 = 0 then
    clauseContribution L (key / 2)
  else if key % 4 = 1 then
    literalBase L ((key - 1) / 4) false
  else
    literalBase L ((key - 3) / 4) true

@[simp] theorem structuralize_clause (L q : Nat) :
    structuralize L (2 * q) = clauseContribution L q := by
  simp [structuralize]

@[simp] theorem structuralize_negative (L v : Nat) :
    structuralize L (4 * v + 1) = literalBase L v false := by
  simp [structuralize] <;> omega

@[simp] theorem structuralize_positive (L v : Nat) :
    structuralize L (4 * v + 3) = literalBase L v true := by
  simp [structuralize] <;> omega

theorem structuralVertices_eq_map (input : List CNFSym) :
    structuralVertices input =
      (candidateVertices input).map (structuralize input.length) := by
  simp [structuralVertices, candidateVertices, List.map_append,
    List.map_map, Function.comp_def]

theorem rawStructuralPairs_eq_map (input : List CNFSym) :
    rawStructuralPairs input =
      (rawCandidatePairs input).map (fun pair =>
        (structuralize input.length pair.1,
          structuralize input.length pair.2)) := by
  rw [rawStructuralPairs, rawCandidatePairs, structuralVertices_eq_map,
    certificateRawPairs_map]

end PricingWithTips.FixedShapePairPayloadSemantics


