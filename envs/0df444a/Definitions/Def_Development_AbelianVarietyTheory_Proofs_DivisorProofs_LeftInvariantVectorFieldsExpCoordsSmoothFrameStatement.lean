-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrameStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrameStatement
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:46:52.99626+00:00
-- url     : https://prove2.me/theorems/b2ca2993-6082-4a8d-8229-48c060788b90
-- title:
--   Left Invariant Vector Fields Exp Coords Smooth Frame Statement
-- statement:
--   Definitions and structural lemmas for Left Invariant Vector Fields Exp Coords Smooth Frame Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftInvariantVectorFieldsExpCoordsSmoothFrameStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff


