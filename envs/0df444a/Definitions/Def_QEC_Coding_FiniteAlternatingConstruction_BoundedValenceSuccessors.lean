-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
-- name    : QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:14:14.064985+00:00
-- url     : https://prove2.me/theorems/a2f0004a-a944-4f9d-bdda-a3a01cd828ee
-- title:
--   Bounded Valence Successors
-- statement:
--   Definitions and structural lemmas for Bounded Valence Successors, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/BoundedValenceSuccessors.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
namespace QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26RXLocalReplacement
open BDL26TannerLocalRegularity
def rzFaceToRX (P : TannerSquarePresentation) (S : OddScale) :
    BDL26RZLocalReplacement.RZFace P S → RXFace (transposePresentation P) S
  | Sum.inl localFace => Sum.inl localFace
  | Sum.inr (Sum.inl ⟨edge, cylinderEdge, endpoint⟩) =>
      Sum.inr (Sum.inl ⟨⟨(edge.1.2, edge.1.1), edge.2⟩, cylinderEdge, endpoint⟩)
  | Sum.inr (Sum.inr oldFace) => Sum.inr (Sum.inr oldFace)
end QEC.Coding.BDL26BoundedValence


