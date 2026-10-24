-- Prove2me | Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part4
-- name    : PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:54:24.109037+00:00
-- url     : https://prove2.me/theorems/661622d6-0629-442d-9498-f7605738c6cd
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Semantics.Part4
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part3
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

def certificateRawPairs (vertices : List Nat) : List (Nat × Nat) :=
  compatibleOccurrencePairIterations (certificatePairEntries vertices).reverse

theorem encodeCertificatePairIterations_eq (vertices : List Nat) :
    encodeCertificatePairIterations vertices =
      (certificateRawPairs vertices).flatMap encodeCliqueEdge := by
  exact encodeCompatibleOccurrencePairIterations _

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator


