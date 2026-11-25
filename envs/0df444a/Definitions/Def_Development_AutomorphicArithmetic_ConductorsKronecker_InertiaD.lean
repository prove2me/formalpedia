-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_InertiaD
-- name    : Development_AutomorphicArithmetic_ConductorsKronecker_InertiaD
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:16.669862+00:00
-- url     : https://prove2.me/theorems/ee305cd2-e213-464d-a715-94599a6a49b1
-- title:
--   Inertia D
-- statement:
--   Definitions and structural lemmas for Inertia D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/InertiaD.lean

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_hostFactsS
import Theorems.Thm_P2M_UpperTheory_Comparison__hostFactsS_fb5313d5199c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal


