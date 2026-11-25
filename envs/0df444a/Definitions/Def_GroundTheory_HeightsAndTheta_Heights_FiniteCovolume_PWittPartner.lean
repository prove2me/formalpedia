-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWittPartner
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWittPartner
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:32:58.253616+00:00
-- url     : https://prove2.me/theorems/49539b48-8367-5837-a5c1-4ba857180449
-- title:
--   PWitt Partner
-- statement:
--   Definitions and structural lemmas for PWitt Partner, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PWittPartner.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
end GroundTheory.Heights₂.Heights.FiniteCovolume


