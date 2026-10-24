-- Prove2me | Definitions.Def_PricingWithTips3DM_3db1e183bd6d6028f5adfa5e
-- name    : PricingWithTips3DM_3db1e183bd6d6028f5adfa5e
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T07:00:46.415848+00:00
-- url     : https://prove2.me/theorems/a2551c48-d47d-42b0-a09d-c88a749db250
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.QueryNormalizer.Composition
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_ae32b2b54208cb443df5a4e8
import Definitions.Def_PricingWithTips3DM_617ad59f689a8cb60fb1accd
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Query normalization: certificate-pair composition

This module connects the two concrete verifier stages: certificate values are
expanded into every positional pair, then each pair is put into the canonical
orientation used by the undirected graph encoding.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer

/-- Canonically oriented pair queries generated from a certificate. -/
def normalizedCertificatePairs (vertices : List Nat) : List (Nat × Nat) :=
  (PairGenerator.certificateRawPairs vertices).map normalizeQuery

/-- A fixed polynomial-time TM2 maps a canonical certificate to the complete
canonical edge-query family needed by graph membership checking. -/
noncomputable def normalizedCertificatePairs_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      normalizedCertificatePairs := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      PairGenerator.rawPairs_computableInPolyTime
      normalizer_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate
    (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
    (fun vertices =>
      List.map normalizeQuery (PairGenerator.certificateRawPairs vertices))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer


