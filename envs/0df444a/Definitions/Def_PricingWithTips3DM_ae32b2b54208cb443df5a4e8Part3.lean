-- Prove2me | Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part3
-- name    : PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:50:20.455338+00:00
-- url     : https://prove2.me/theorems/47ecc3ba-acf0-44a5-9748-97759bf13ef2
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Semantics.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

theorem encodeCompatibleOccurrencePairIterations
    (entries : List (IndexedOccurrence × Nat)) :
    TMClique.encodeCompatibleOccurrenceIterations entries =
      (compatibleOccurrencePairIterations entries).flatMap
        encodeCliqueEdge := by
  induction entries with
  | nil => rfl
  | cons current priors ih =>
      simp only [TMClique.encodeCompatibleOccurrenceIterations,
        compatibleOccurrencePairIterations, List.flatMap_append]
      rw [ih, encodeCompatibleOccurrencePairs]

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator


