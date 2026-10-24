-- Prove2me | Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part1B
-- name    : PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part1B
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:39:40.662552+00:00
-- url     : https://prove2.me/theorems/d1a602b9-d5bd-4b34-a189-c605b1387b96
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Semantics.Part1B
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part1A
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

def compatibleOccurrencePairs
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : List (Nat × Nat) :=
  priors.flatMap (compatibleOccurrencePair current)

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator


