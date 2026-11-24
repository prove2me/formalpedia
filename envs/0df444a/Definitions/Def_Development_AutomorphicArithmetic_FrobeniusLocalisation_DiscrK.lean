-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiscrK
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_DiscrK
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:37.92523+00:00
-- url     : https://prove2.me/theorems/d5668451-2a28-48ed-8451-4310910c4aba
-- title:
--   Discr K
-- statement:
--   Definitions and structural lemmas for Discr K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiscrK.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
section
open Polynomial
end


