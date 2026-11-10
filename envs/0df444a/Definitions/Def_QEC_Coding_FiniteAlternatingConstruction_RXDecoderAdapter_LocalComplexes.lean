-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:04:15.574313+00:00
-- url     : https://prove2.me/theorems/b75a7b20-783b-426f-8adc-64ee2ef0b3f0
-- title:
--   Local Complexes
-- statement:
--   Definitions and structural lemmas for Local Complexes, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/LocalComplexes.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCqH1Coordinate_bijective
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder
open scoped Classical
noncomputable def localCx (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :=
  reindexComplex (rxCx P x S) (Equiv.refl _) (xCorrectionEquiv P S x) (xSyndromeEquiv P S x)
noncomputable def localCq (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :=
  reindexComplex (rxCq P q S) (Equiv.refl _) (qCorrectionEquiv P S q) (qSyndromeEquiv P S q)
noncomputable def localCxCohomologyEquiv (P : TannerSquarePresentation)
    (S : OddScale) (x : P.X) :
    (localCx P S x).middleCohomology ≃ₗ[BDL26Field] (rxCx P x S).middleCohomology :=
  reindexCohomologyEquiv _ _ _ _
noncomputable def localCqCohomologyEquiv (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) :
    (localCq P S q).middleCohomology ≃ₗ[BDL26Field] BDL26Field :=
  (reindexCohomologyEquiv (rxCq P q S) (Equiv.refl _)
    (qCorrectionEquiv P S q) (qSyndromeEquiv P S q)).trans
      (LinearEquiv.ofBijective (rxCqH1Coordinate P q S) (rxCqH1Coordinate_bijective P A q S))
end QEC.Coding.BDL26RXDecoderAdapter


