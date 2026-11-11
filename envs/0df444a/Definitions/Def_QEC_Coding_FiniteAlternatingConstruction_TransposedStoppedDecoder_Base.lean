-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
-- name    : QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_Base
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T14:33:40.790397+00:00
-- url     : https://prove2.me/theorems/f91ba49d-881f-4d52-a5c6-a42455223962
-- title:
--   Base
-- statement:
--   Definitions and structural lemmas for Base, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TransposedStoppedDecoder/Base.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder_LocalSteps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26TransposedStoppedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26LevelTwoCode BDL26LevelTwoDecoder BDL26ReplacementSupport
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RXDecoderAdapter
open BDL26RZMap1CoordinateBridge MultiscaleDecoder Coordinates
open scoped Classical
def dualBaseTable (S : OddScale) : List (Word BDL26Field (dualPresentation S 2).Q) :=
  (allWords (ExecutableQ S)).map (toActualError S)
def dualBaseOwner (S : OddScale) (q : (dualPresentation S 2).Q) :
    Vertex (transposePresentation (state S 1).presentation) :=
  rxCorrectionOwner (transposePresentation (state S 1).presentation) S
    (rzDualQ (state S 1).presentation S q)
def dualBaseLocal (S : OddScale) (e : Word BDL26Field (dualPresentation S 2).Q) : Bool :=
  decide (∃ center : Vertex (transposePresentation (state S 1).presentation),
    ∀ q, e q ≠ 0 → dualBaseOwner S q = center)
def dualBaseDecode (S : OddScale)
    (sigma : Word BDL26Field (dualPresentation S 2).Z) :
    Word BDL26Field (dualPresentation S 2).Q :=
  lookup (dualBaseTable S) (tannerCoboundary1 (dualPresentation S 2))
    (dualBaseLocal S) 0 sigma
end QEC.Coding.BDL26TransposedStoppedDecoder
end


