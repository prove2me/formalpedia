-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T07:40:27.776852+00:00
-- url     : https://prove2.me/theorems/4ab57b9d-5a04-416e-ae85-1ca48c1961c1
-- title:
--   RXIncidence Hull Successors
-- statement:
--   Definitions and structural lemmas for RXIncidence Hull Successors, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullSuccessors.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26RXIncidenceHullSuccessors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXIncidenceHullGrowth
def rxRoot (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) (copy : BDL26FiniteTannerSquare.Two) :
    (rxReplacementPresentation P S).Q := Sum.inr ⟨q,(copy,Sum.inl (Sum.inl ()))⟩
end QEC.Coding.BDL26RXIncidenceHullSuccessors
end


