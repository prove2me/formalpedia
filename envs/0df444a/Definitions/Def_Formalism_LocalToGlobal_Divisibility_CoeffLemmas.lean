-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
-- name    : Formalism_LocalToGlobal_Divisibility_CoeffLemmas
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T20:15:52.211672+00:00
-- url     : https://prove2.me/theorems/99af9560-e7f5-41e4-96d4-e69959ae34e8
-- title:
--   Coeff Lemmas
-- statement:
--   Definitions and structural lemmas for Coeff Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
namespace Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
end Formalism.L2.DIV


