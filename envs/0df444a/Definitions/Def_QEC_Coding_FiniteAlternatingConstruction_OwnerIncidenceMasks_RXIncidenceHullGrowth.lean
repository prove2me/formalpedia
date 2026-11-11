-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T07:37:23.239119+00:00
-- url     : https://prove2.me/theorems/a04c29e9-0e70-4a25-9474-fa7f65aa2d18
-- title:
--   RXIncidence Hull Growth
-- statement:
--   Definitions and structural lemmas for RXIncidence Hull Growth, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGrowth.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
inductive SharedZPath (P : TannerSquarePresentation) : P.Q → P.Q → Prop
  | refl (q : P.Q) : SharedZPath P q q
  | snoc {q r t : P.Q} (path : SharedZPath P q r) (z : P.Z)
      (left : P.qz r z = true) (right : P.qz t z = true) : SharedZPath P q t
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
def pathUnion (seed : Finset (state S i.val).presentation.Q) :
    Finset (state S i.val).presentation.Q :=
  Finset.univ.filter fun r => ∃ q ∈ seed, SharedZPath (state S i.val).presentation q r
end QEC.Coding.BDL26RXIncidenceHullGrowth
end


