-- Prove2me | Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part2
-- name    : PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:47:01.38061+00:00
-- url     : https://prove2.me/theorems/71b31dae-ed0f-4c89-af41-027907304def
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Semantics.Part2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

theorem encodeCompatibleOccurrencePair
    (current prior : IndexedOccurrence × Nat) :
    TMClique.encodeCompatibleOccurrenceEdge current prior =
      (compatibleOccurrencePair current prior).flatMap encodeCliqueEdge := by
  cases hcompatible :
      TMClique.indexedOccurrencesCompatibleCode current prior <;>
    simp [TMClique.encodeCompatibleOccurrenceEdge,
      compatibleOccurrencePair, hcompatible]

theorem encodeCompatibleOccurrencePairs
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    TMClique.encodeCompatibleOccurrenceEdges current priors =
      (compatibleOccurrencePairs current priors).flatMap encodeCliqueEdge := by
  unfold TMClique.encodeCompatibleOccurrenceEdges compatibleOccurrencePairs
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro prior _
  exact encodeCompatibleOccurrencePair current prior

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator


