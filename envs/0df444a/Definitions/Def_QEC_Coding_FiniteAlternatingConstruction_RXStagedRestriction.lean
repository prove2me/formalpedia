-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:16:19.572269+00:00
-- url     : https://prove2.me/theorems/8869f7c6-6f84-4c07-8515-dcd6e5e2b90f
-- title:
--   RXStaged Restriction
-- statement:
--   Definitions and structural lemmas for RXStaged Restriction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXStagedRestriction.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
set_option autoImplicit false
namespace QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators
def seedQEdge : QDoubleCylinderEdge baseTannerSquarePresentation (0 : BaseQubit) scaleFive :=
  Sum.inr ⟨(0 : BaseZ), by decide⟩
noncomputable def seedXEdge :
    DoubleCylinderEdge baseTannerSquarePresentation (0 : BaseX) scaleFive :=
  qToXDoubleCylinderEdgeRaw baseTannerSquarePresentation (0 : BaseQubit)
    (0 : BaseX) (by decide) scaleFive seedQEdge
noncomputable def seedError : Word BDL26Field (RX1 baseTannerSquarePresentation scaleFive) :=
  canonicalBasisWord (Sum.inl ⟨(0 : BaseX),seedXEdge⟩)
end QEC.Coding.BDL26RXStagedRestriction


