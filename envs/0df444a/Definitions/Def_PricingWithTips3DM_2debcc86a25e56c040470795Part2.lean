-- Prove2me | Definitions.Def_PricingWithTips3DM_2debcc86a25e56c040470795Part2
-- name    : PricingWithTips3DM_2debcc86a25e56c040470795Part2
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T10:18:05.92132+00:00
-- url     : https://prove2.me/theorems/36ccb7fc-ab04-4e83-94c5-a2c4d7b7358d
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_FixedShapeStructuralCandidatesTM2.Part2
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_2debcc86a25e56c040470795Part1
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

private theorem map_finRange_val (n : Nat) :
    (List.finRange n).map (fun index => index.val) = List.range n := by
  rw [← List.ofFn_eq_map, List.ofFn_eq_pmap]
  simp

theorem clauseFrames_eq (input : List CNFSym) :
    clauseFrames input = encodeUnaryFrame
      ((List.range input.length).map
        (clauseContribution input.length)) := by
  simp only [clauseFrames, exactPolynomialAffineUnaryProgressionFrameStream,
    exactPolynomialAffineUnaryProgression, affineUnaryProgressionFrameStream,
    affineUnaryProgressionValues,
    affineUnaryProgressionValuesFrom_eq_ofFn, lengthPolynomial,
    List.ofFn_eq_map, Polynomial.eval_X, Polynomial.eval_zero,
    Nat.zero_add]
  apply congrArg encodeUnaryFrame
  rw [show clauseContribution input.length =
      (fun q => q * (2 * dimensionValue input.length ^ 2 +
        dimensionValue input.length + 1)) by rfl]
  have h := congrArg
    (List.map fun q : Nat => q * clauseStridePolynomial.eval input.length)
    (map_finRange_val input.length)
  simpa only [List.map_map, Function.comp_def, clauseContribution,
    clauseStridePolynomial_eval, dimensionValue] using h

theorem negativeBaseFrames_eq (input : List CNFSym) :
    negativeBaseFrames input = encodeUnaryFrame
      ((List.range input.length).map
        (fun v => literalBase input.length v false)) := by
  simp only [negativeBaseFrames,
    exactPolynomialAffineUnaryProgressionFrameStream,
    exactPolynomialAffineUnaryProgression, affineUnaryProgressionFrameStream,
    affineUnaryProgressionValues,
    affineUnaryProgressionValuesFrom_eq_ofFn, lengthPolynomial,
    List.ofFn_eq_map, Polynomial.eval_X]
  apply congrArg encodeUnaryFrame
  have h := congrArg (List.map fun v : Nat =>
      negativeBasePolynomial.eval input.length +
        v * variableStridePolynomial.eval input.length)
    (map_finRange_val input.length)
  simpa only [List.map_map, Function.comp_def, negativeBase_affine] using h

theorem positiveBaseFrames_eq (input : List CNFSym) :
    positiveBaseFrames input = encodeUnaryFrame
      ((List.range input.length).map
        (fun v => literalBase input.length v true)) := by
  simp only [positiveBaseFrames,
    exactPolynomialAffineUnaryProgressionFrameStream,
    exactPolynomialAffineUnaryProgression, affineUnaryProgressionFrameStream,
    affineUnaryProgressionValues,
    affineUnaryProgressionValuesFrom_eq_ofFn, lengthPolynomial,
    List.ofFn_eq_map, Polynomial.eval_X]
  apply congrArg encodeUnaryFrame
  have h := congrArg (List.map fun v : Nat =>
      positiveBasePolynomial.eval input.length +
        v * variableStridePolynomial.eval input.length)
    (map_finRange_val input.length)
  simpa only [List.map_map, Function.comp_def, positiveBase_affine] using h

def structuralCertificateStream (input : List CNFSym) : List CliqueSym :=
  encodeCliqueCertificate (structuralVertices input)

theorem structuralCertificateStream_eq (input : List CNFSym) :
    structuralCertificateStream input =
      certificateMarkStream input ++ structuralBody input := by
  simp only [PricingWithTips.FixedShapeLiteralCandidatesTM2.certificateMarkStream_eq,
    structuralBody, clauseRecords, literalBaseRecords,
    negativeBaseRecords, positiveBaseRecords, clauseFrames_eq,
    negativeBaseFrames_eq, positiveBaseFrames_eq, formatter_frame]
  simp [structuralCertificateStream, structuralVertices,
    encodeCliqueCertificate, List.flatMap_append]
end PricingWithTips.FixedShapeStructuralCandidatesTM2


