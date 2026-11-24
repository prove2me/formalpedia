-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:04.818683+00:00
-- url     : https://prove2.me/theorems/6819a35e-2485-4e3d-8b24-946c389ec534
-- title:
--   Is Coset Quadratic Phase Test Function Conj Character Mu
-- statement:
--   Definitions and structural lemmas for Is Coset Quadratic Phase Test Function Conj Character Mu, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
namespace GlobalTheory.Phase.ShapeOps
section Quad
variable {M : Type} [AddCommGroup M]
end Quad
variable {κ ι : Type} [Fintype κ] [Fintype ι]
end GlobalTheory.Phase.ShapeOps


