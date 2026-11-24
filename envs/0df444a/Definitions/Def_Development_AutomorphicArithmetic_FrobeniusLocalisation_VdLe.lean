-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdLe
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_VdLe
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:19.360302+00:00
-- url     : https://prove2.me/theorems/da7cf490-adab-42be-a072-04a161795858
-- title:
--   Vd Le
-- statement:
--   Definitions and structural lemmas for Vd Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/VdLe.lean

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise


