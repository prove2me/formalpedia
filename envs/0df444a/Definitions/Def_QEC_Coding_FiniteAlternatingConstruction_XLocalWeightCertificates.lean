-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
-- name    : QEC_Coding_FiniteAlternatingConstruction_XLocalWeightCertificates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:31:16.846801+00:00
-- url     : https://prove2.me/theorems/f163d620-0911-4a29-8e2c-ae2a2ee1098d
-- title:
--   XLocal Weight Certificates
-- statement:
--   Definitions and structural lemmas for XLocal Weight Certificates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeightCertificates.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalRadialParity
set_option autoImplicit false
namespace QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity BDL26XLocalConnectingWeight
open BDL26XLocalRadialParity
open scoped BigOperators
noncomputable def xLocalCrossingBudget
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (s : Word Field (DoubleCylinderFace P x S)) : Nat :=
  ∑ face : XStarFace P x, pieceCrossingCost
    (xLocalRegionParity P x S s face (Sum.inl 0))
    (xLocalRegionParity P x S s face (Sum.inl 1))
    (xLocalRegionParity P x S s face (Sum.inr 0))
    (xLocalRegionParity P x S s face (Sum.inr 1))
end QEC.Coding.BDL26RXLocalReplacement


