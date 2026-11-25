-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStep
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DixmierMalliavinFactorisationBasisStep
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:42.683102+00:00
-- url     : https://prove2.me/theorems/e20ceae0-9a09-4e6b-ac10-eb44d800b349
-- title:
--   Dixmier Malliavin Factorisation Basis Step
-- statement:
--   Definitions and structural lemmas for Dixmier Malliavin Factorisation Basis Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DixmierMalliavinFactorisationBasisStep.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedDerivFunctionalContDiffExpLineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedDerivFunctionalTsumReplicateStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic Set
open scoped ContDiff
namespace GlobalTheory.HCA
end GlobalTheory.HCA
end


