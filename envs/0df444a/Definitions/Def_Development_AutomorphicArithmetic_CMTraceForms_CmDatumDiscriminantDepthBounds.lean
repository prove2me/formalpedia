-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_CmDatumDiscriminantDepthBounds
-- name    : Development_AutomorphicArithmetic_CMTraceForms_CmDatumDiscriminantDepthBounds
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:53.036014+00:00
-- url     : https://prove2.me/theorems/5bb8aeb4-95bd-44fb-9594-74c307f5db13
-- title:
--   Cm Datum Discriminant Depth Bounds
-- statement:
--   Definitions and structural lemmas for Cm Datum Discriminant Depth Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/CmDatumDiscriminantDepthBounds.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdLe
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_inertQ
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_InertD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Formalism.HC


