-- Prove2me | Definitions.Def_PricingWithTips3DM_ddacc2a9bb82165e591a45f7
-- name    : PricingWithTips3DM_ddacc2a9bb82165e591a45f7
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:31:02.552009+00:00
-- url     : https://prove2.me/theorems/26063a92-da8f-45d2-88ae-d8dce018f83f
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapePairAlignment
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_2debcc86a25e56c040470795
import Definitions.Def_PricingWithTips3DM_89548ba1d154810acde5067a
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! Parametricity of the reused certificate pair generator: changing only
the vertex payloads preserves the number and order of generated pairs. -/

namespace PricingWithTips.FixedShapePairAlignment

open CLRS.Chapter34
open CLRS.Chapter34.Turing.TMClique
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
open PricingWithTips.FixedShapeLiteralCandidatesTM2
open PricingWithTips.FixedShapeStructuralCandidatesTM2
open PricingWithTips.FixedShapeLiteralMembershipTM2

private theorem compatiblePair_length_congr
    (current₁ current₂ prior₁ prior₂ : IndexedOccurrence × Nat)
    (hc : current₁.1 = current₂.1) (hp : prior₁.1 = prior₂.1) :
    (compatibleOccurrencePair current₁ prior₁).length =
      (compatibleOccurrencePair current₂ prior₂).length := by
  rcases current₁ with ⟨current₁, value₁⟩
  rcases current₂ with ⟨current₂, value₂⟩
  rcases prior₁ with ⟨prior₁, priorValue₁⟩
  rcases prior₂ with ⟨prior₂, priorValue₂⟩
  simp only at hc hp
  subst current₂
  subst prior₂
  have hs : indexedOccurrencesCompatibleCode
      (current₁, value₂) (prior₁, priorValue₂) =
      indexedOccurrencesCompatibleCode
        (current₁, value₁) (prior₁, priorValue₁) := rfl
  unfold compatibleOccurrencePair
  rw [hs]
  cases h : indexedOccurrencesCompatibleCode
      (current₁, value₁) (prior₁, priorValue₁) <;>
    simp only [h, Bool.false_eq_true, if_false,
      if_true, List.length_nil, List.length_singleton]

private theorem compatiblePairs_length_congr
    (current₁ current₂ : IndexedOccurrence × Nat)
    (priors₁ priors₂ : List (IndexedOccurrence × Nat))
    (hc : current₁.1 = current₂.1)
    (hp : priors₁.map Prod.fst = priors₂.map Prod.fst) :
    (compatibleOccurrencePairs current₁ priors₁).length =
      (compatibleOccurrencePairs current₂ priors₂).length := by
  induction priors₁ generalizing priors₂ with
  | nil =>
      have : priors₂ = [] := by
        cases priors₂ <;> simp_all
      subst priors₂
      rfl
  | cons prior₁ priors₁ ih =>
      cases priors₂ with
      | nil => simp at hp
      | cons prior₂ priors₂ =>
          simp only [List.map_cons, List.cons.injEq] at hp
          simp only [compatibleOccurrencePairs, List.flatMap_cons,
            List.length_append]
          exact congrArg₂ (· + ·)
            (compatiblePair_length_congr current₁ current₂ prior₁ prior₂
              hc hp.1)
            (ih priors₂ hp.2)

theorem compatibleIterations_length_congr
    (entries₁ entries₂ : List (IndexedOccurrence × Nat))
    (h : entries₁.map Prod.fst = entries₂.map Prod.fst) :
    (compatibleOccurrencePairIterations entries₁).length =
      (compatibleOccurrencePairIterations entries₂).length := by
  induction entries₁ generalizing entries₂ with
  | nil =>
      have : entries₂ = [] := by
        cases entries₂ <;> simp_all
      subst entries₂
      rfl
  | cons current₁ priors₁ ih =>
      cases entries₂ with
      | nil => simp at h
      | cons current₂ priors₂ =>
          simp only [List.map_cons, List.cons.injEq] at h
          simp only [compatibleOccurrencePairIterations,
            List.length_append]
          refine congrArg₂ (· + ·) (ih priors₂ h.2) ?_
          apply compatiblePairs_length_congr current₁ current₂
          · exact h.1
          · simpa using congrArg List.reverse h.2

private theorem entriesFrom_fst_eq_of_length (start : Nat)
    (left right : List Nat) (h : left.length = right.length) :
    (certificatePairEntriesFrom start left).map Prod.fst =
      (certificatePairEntriesFrom start right).map Prod.fst := by
  induction left generalizing start right with
  | nil =>
      have : right = [] := List.eq_nil_of_length_eq_zero h.symm
      subst right
      rfl
  | cons value left ih =>
      cases right with
      | nil => simp at h
      | cons other right =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp only [certificatePairEntriesFrom_cons, List.map_cons,
            List.cons.injEq]
          exact ⟨trivial, ih (start + 1) right h⟩

theorem certificateRawPairs_length_congr (left right : List Nat)
    (h : left.length = right.length) :
    (certificateRawPairs left).length = (certificateRawPairs right).length := by
  unfold certificateRawPairs certificatePairEntries
  apply compatibleIterations_length_congr
  simpa using congrArg List.reverse (entriesFrom_fst_eq_of_length 0 left right h)

theorem candidate_structural_vertices_length (input : List CNFSym) :
    (candidateVertices input).length = (structuralVertices input).length := by
  simp [candidateVertices, structuralVertices]

theorem rawPair_lengths (input : List CNFSym) :
    (rawStructuralPairs input).length =
      (rawCandidatePairs input).length := by
  apply certificateRawPairs_length_congr
  exact (candidate_structural_vertices_length input).symm

theorem structural_membership_lengths (input : List CNFSym) :
    (rawStructuralPairs input).length =
      (literalMembershipBits input).length := by
  rw [literalMembershipBits, List.length_map]
  exact rawPair_lengths input

end PricingWithTips.FixedShapePairAlignment


