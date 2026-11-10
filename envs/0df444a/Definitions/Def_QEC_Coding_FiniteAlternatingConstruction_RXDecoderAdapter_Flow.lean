-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:08:23.717178+00:00
-- url     : https://prove2.me/theorems/bca76788-9f02-4895-ab58-d2e31581aa3c
-- title:
--   Flow
-- statement:
--   Definitions and structural lemmas for Flow, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter/Flow.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
set_option autoImplicit false
namespace QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
noncomputable def xExtend (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    Word BDL26Field (DoubleCylinderEdge P x S) →ₗ[BDL26Field] Word BDL26Field (RX1 P S) :=
  (extendWordLinear ((localX P S).correctionRegion x)).comp
    (wordEquiv (xCorrectionEquiv P S x)).toLinearMap
noncomputable def qExtend (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) →ₗ[BDL26Field] Word BDL26Field (RX1 P S) :=
  (extendWordLinear ((localQ P S).correctionRegion q)).comp
    (wordEquiv (qCorrectionEquiv P S q)).toLinearMap
noncomputable def xFlow (P : TannerSquarePresentation) (S : OddScale) (x : P.X) :
    Word BDL26Field (DoubleCylinderEdge P x S) →ₗ[BDL26Field] Word BDL26Field (RX2 P S) :=
  (rxConnectingXQ1 P S).comp (xExtend P S x)
noncomputable def qFlow (P : TannerSquarePresentation) (S : OddScale) (q : P.Q) :
    Word BDL26Field (QDoubleCylinderVertex P q S) →ₗ[BDL26Field] Word BDL26Field (RX2 P S) :=
  (rxConnectingQZ1 P S).comp (qExtend P S q)
end QEC.Coding.BDL26RXDecoderAdapter


