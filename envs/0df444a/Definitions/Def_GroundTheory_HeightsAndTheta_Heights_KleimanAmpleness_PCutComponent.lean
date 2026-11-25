-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutComponent
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutComponent
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:38:01.547049+00:00
-- url     : https://prove2.me/theorems/4bfe1182-7af7-44b6-af15-0fa93ef8c731
-- title:
--   PCut Component
-- statement:
--   Definitions and structural lemmas for PCut Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutComponent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutComponentSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutZeroNotLeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutNonemptySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutDimLowerSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
universe u w
end GroundTheory.Heights₂.Heights.Kleiman


