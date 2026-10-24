-- Prove2me | Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part5
-- name    : PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part5
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:56:06.61999+00:00
-- url     : https://prove2.me/theorems/2a88de99-8ae6-4959-b118-703cbb6dac20
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Semantics.Part5
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8Part4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

noncomputable def rawPairs_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      certificateRawPairs := by
  let pairs := pairIterations_computableInPolyTime
  exact
    { tm := pairs.tm
      inputAlphabet := pairs.inputAlphabet
      outputAlphabet := pairs.outputAlphabet
      time := pairs.time
      outputsFun := fun vertices => by
        simpa [encodeCertificatePairIterations_eq] using
          pairs.outputsFun vertices }

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator


