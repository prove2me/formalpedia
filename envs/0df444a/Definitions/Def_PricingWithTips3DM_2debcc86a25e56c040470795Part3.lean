-- Prove2me | Definitions.Def_PricingWithTips3DM_2debcc86a25e56c040470795Part3
-- name    : PricingWithTips3DM_2debcc86a25e56c040470795Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:22:02.114992+00:00
-- url     : https://prove2.me/theorems/c45c4942-98b3-4440-a5b9-822dded7ea79
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeStructuralCandidatesTM2.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_2debcc86a25e56c040470795Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace PricingWithTips.FixedShapeStructuralCandidatesTM2

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open CLRS.Chapter34.Turing.TMClique
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open _root_.Turing
open PricingWithTips.FixedShapeLiteralCandidatesTM2
open PricingWithTips.FixedShapeLiteralOrdinalArithmetic

noncomputable def structuralCertificateStream_computableInPolyTime :
    TM2ComputableInPolyTime id encodeCliqueCertificate structuralVertices := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    certificateMarkStream_computableInPolyTime
    structuralBody_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [← structuralCertificateStream_eq input] at output
        exact output }

def rawStructuralPairs (input : List CNFSym) : List (Nat × Nat) :=
  PairGenerator.certificateRawPairs (structuralVertices input)

noncomputable def rawStructuralPairs_computableInPolyTime :
    TM2ComputableInPolyTime id
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      rawStructuralPairs := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    structuralCertificateStream_computableInPolyTime
    PairGenerator.rawPairs_computableInPolyTime
  change TM2ComputableInPolyTime id
    (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
    (fun input => PairGenerator.certificateRawPairs (structuralVertices input))
  simpa [Function.comp_def] using Classical.choice composed
end PricingWithTips.FixedShapeStructuralCandidatesTM2


