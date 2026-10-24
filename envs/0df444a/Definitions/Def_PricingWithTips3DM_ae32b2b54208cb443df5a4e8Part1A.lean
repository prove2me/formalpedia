-- Prove2me | Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part1A
-- name    : PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part1A
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:38:23.483754+00:00
-- url     : https://prove2.me/theorems/5b3ce275-9214-4809-ac6f-f36b5413bd34
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Semantics.Part1A
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_88801654eeed9b1dbb21ce0f
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

def compatibleOccurrencePair
    (current prior : IndexedOccurrence × Nat) : List (Nat × Nat) :=
  if TMClique.indexedOccurrencesCompatibleCode current prior then
    [(prior.2, current.2)]
  else []

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator


