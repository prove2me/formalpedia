-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:42.949727+00:00
-- url     : https://prove2.me/theorems/3dd78b58-6eb2-4322-83d7-fa5fbc3c3336
-- title:
--   Chain Rule And Jacobian Criterion
-- statement:
--   Definitions and structural lemmas for Chain Rule And Jacobian Criterion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ChainRuleAndJacobianCriterion.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KaehlerDifferential TensorProduct
namespace GlobalTheory.EtaleCoordJacobian
section tower
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B]
end tower
end GlobalTheory.EtaleCoordJacobian


