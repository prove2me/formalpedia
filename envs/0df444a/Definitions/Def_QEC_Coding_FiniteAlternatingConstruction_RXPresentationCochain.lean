-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:06:55.117909+00:00
-- url     : https://prove2.me/theorems/160c5fff-2084-4dcd-8b81-7fe5de4df4d6
-- title:
--   RXPresentation Cochain
-- statement:
--   Definitions and structural lemmas for RXPresentation Cochain, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
set_option autoImplicit false
namespace QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators
noncomputable def rxPresentationCochainVertexIndicator {V : Type} (a b : V) : Field := by
  classical
  exact if a = b then 1 else 0
def rxPresentationCochainFinTwoElim {motive : Fin 2 → Sort _}
    (zero : motive 0) (one : motive 1) (endpoint : Fin 2) : motive endpoint := by
  rcases endpoint with ⟨n, hn⟩
  rcases n with _ | n
  · exact zero
  · rcases n with _ | n
    · exact one
    · omega
noncomputable def rxLocalBoundarySlot
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (cell : DoubleCylinderFace P x S) (slot : Two × Two) :
    DoubleCylinderEdge P x S :=
  match cell with
  | Sum.inl cf => Sum.inl (cf.1, subdivisionFaceBoundaryEdge P x S cf.2 slot)
  | Sum.inr r => doubleCylinderRectangleBoundaryEdge P x S r slot
end QEC.Coding.BDL26RXLocalReplacement


