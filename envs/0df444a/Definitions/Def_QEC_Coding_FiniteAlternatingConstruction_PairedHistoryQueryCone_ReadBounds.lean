-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
-- name    : QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T07:37:23.323803+00:00
-- url     : https://prove2.me/theorems/790cfc61-35cc-4307-a3c9-0eff06b15b89
-- title:
--   Read Bounds
-- statement:
--   Definitions and structural lemmas for Read Bounds, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone/ReadBounds.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_LocalReads
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26RXDecoderAdapter BDL26RZDecoderAdapter BDL26RXCoarseInfluence
open BDL26RXInfluenceBounds BDL26GraphQuantitativeBounds
open MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
def reverseGraph {V : Type} [Fintype V] [DecidableEq V] (G : DirectedGraph V) :
    DirectedGraph V where
  edge u v := G.edge v u
  loopless := G.loopless
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
def queryBlockBound (S : OddScale) : Nat := 57 * localCoordinateBound S
end QEC.Coding.BDL26PairedHistoryQueryCone


