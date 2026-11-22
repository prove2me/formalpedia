-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_ClassInjectiveOfSpanRecovery
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_ClassInjectiveOfSpanRecovery
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:45.88766+00:00
-- url     : https://prove2.me/theorems/7adbabc8-a829-4373-8574-0bd4d752bec1
-- title:
--   Class Injective Of Span Recovery
-- statement:
--   Definitions and structural lemmas for Class Injective Of Span Recovery, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/ClassInjectiveOfSpanRecovery.lean

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG Formalism.UG.CS
end Formalism.UG.P


