-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:09:20.937077+00:00
-- url     : https://prove2.me/theorems/7fbd3250-5f60-4466-bc57-fe806ffe9195
-- title:
--   Uniform Weight
-- statement:
--   Definitions and structural lemmas for Uniform Weight, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
set_option autoImplicit false
namespace QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators
noncomputable def lowerBasisRaw (S : OddScale) (n : Nat) : RX1 (state S n).presentation S :=
  .inl ⟨retainedX S n, .inl (0, .inl
    (radialEdge (state S n).presentation (state S n).admissible.toTannerSquareAdmissible
      (retainedX S n) (faceNeighbor (state S n).presentation (retainedX S n)
        (retainedStarFace S n) 0), rxRadialGridZero S))⟩
noncomputable def lowerBasis (S : OddScale) (j : Nat) :
    (state S ((2 * j + 2) + 1)).presentation.Q :=
  Eq.mpr (congrArg (fun C : ConstructionState => C.presentation.Q)
    (state_rx S (2 * j + 2) (by omega))) (lowerBasisRaw S (2 * j + 2))
end QEC.Coding.BDL26UniformHistoryObstruction


