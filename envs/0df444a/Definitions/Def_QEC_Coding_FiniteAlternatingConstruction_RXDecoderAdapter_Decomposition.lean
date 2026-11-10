-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:12:59.563681+00:00
-- url     : https://prove2.me/theorems/4be96e0a-bfcd-4777-9844-bc624b6325fc
-- title:
--   Decomposition
-- statement:
--   Definitions and structural lemmas for Decomposition, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Decomposition.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
set_option autoImplicit false
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open MultiscaleDecoder
open scoped Classical BigOperators
noncomputable def xSyndromeExtend (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    Word BDL26Field (DoubleCylinderFace P x S) →ₗ[BDL26Field] Word BDL26Field (RX2 P S) :=
  (extendWordLinear ((localX P S).syndromeRegion x)).comp
    (wordEquiv (xSyndromeEquiv P S x)).toLinearMap
noncomputable def qSyndromeExtend (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Word BDL26Field (QDoubleCylinderEdge P q S) →ₗ[BDL26Field] Word BDL26Field (RX2 P S) :=
  (extendWordLinear ((localQ P S).syndromeRegion q)).comp
    (wordEquiv (qSyndromeEquiv P S q)).toLinearMap
end QEC.Coding.BDL26RXDecoderAdapter


