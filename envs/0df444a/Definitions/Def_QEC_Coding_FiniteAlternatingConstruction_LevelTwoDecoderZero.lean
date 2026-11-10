-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
-- name    : QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:59:31.062882+00:00
-- url     : https://prove2.me/theorems/6d0b6a92-9852-49f4-a5a6-b2cbb32d156f
-- title:
--   Level Two Decoder Zero
-- statement:
--   Definitions and structural lemmas for Level Two Decoder Zero, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
namespace QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder
def executableOwnerAtZero (S : OddScale) : Vertex (executableLevelOne S) :=
  Vertex.q (cast (congrArg (fun P : TannerSquarePresentation => P.Q)
    (executableLevelOne_eq S)).symm (levelOneQDefault S))
end QEC.Coding.BDL26LevelTwoDecoder
namespace QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
end QEC.Coding.BDL26OwnerIncidenceMasks


