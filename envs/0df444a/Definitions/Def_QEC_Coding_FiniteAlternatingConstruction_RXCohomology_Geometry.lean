-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Geometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:14:06.175809+00:00
-- url     : https://prove2.me/theorems/21c9550a-8d95-4830-908e-f1498cc59e3c
-- title:
--   Geometry
-- statement:
--   Definitions and structural lemmas for Geometry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCohomology/Geometry.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology_Representatives
set_option autoImplicit false
namespace QEC.Coding.BDL26RXCohomology
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RXDecoderAdapter BDL26ReplacementSupport
open BDL26RZMap1CoordinateBridge
open BDL26RXStagedRestriction MultiscaleDecoder
open scoped Classical BigOperators
abbrev Field := BDL26FiniteTannerSquare.Field
noncomputable abbrev complex := BDL26RZCohomology.complex
noncomputable abbrev Cocycle := BDL26RZCohomology.Cocycle
noncomputable abbrev H1 := BDL26RZCohomology.H1
noncomputable abbrev classOf := BDL26RZCohomology.classOf
def coarseWord (P : TannerSquarePresentation) (S : OddScale)
    (w : Word Field (RX1 P S)) : Word Field P.Q :=
  fun q => w (Sum.inr ⟨q, (0, Sum.inl (Sum.inl ()))⟩)
end QEC.Coding.BDL26RXCohomology


