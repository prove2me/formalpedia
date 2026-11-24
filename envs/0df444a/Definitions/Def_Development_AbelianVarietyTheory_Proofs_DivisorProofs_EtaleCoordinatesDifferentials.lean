-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleCoordinatesDifferentials
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleCoordinatesDifferentials
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:07.768626+00:00
-- url     : https://prove2.me/theorems/f85f1496-fcda-429d-8707-2ae54c7a5d06
-- title:
--   Etale Coordinates Differentials
-- statement:
--   Definitions and structural lemmas for Etale Coordinates Differentials, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleCoordinatesDifferentials.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
namespace GlobalTheory.EtaleCoordRank
open KaehlerDifferential TensorProduct
end GlobalTheory.EtaleCoordRank


