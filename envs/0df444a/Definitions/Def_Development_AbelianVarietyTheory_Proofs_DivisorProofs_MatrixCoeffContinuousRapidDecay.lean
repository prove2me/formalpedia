-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffContinuousRapidDecay
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffContinuousRapidDecay
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:23.900257+00:00
-- url     : https://prove2.me/theorems/0535c0fe-9831-4a54-9661-52ad83303200
-- title:
--   Matrix Coeff Continuous Rapid Decay
-- statement:
--   Definitions and structural lemmas for Matrix Coeff Continuous Rapid Decay, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixCoeffContinuousRapidDecay.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecayFirstPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPartStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
namespace GlobalTheory
namespace MatrixCoeff
end MatrixCoeff
open MatrixCoeff
end GlobalTheory


