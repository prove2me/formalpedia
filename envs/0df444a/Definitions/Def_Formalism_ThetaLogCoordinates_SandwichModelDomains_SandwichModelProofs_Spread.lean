-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
-- name    : Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:54.873938+00:00
-- url     : https://prove2.me/theorems/3258d6be-e1f5-4e6d-9f36-c06323d9fff0
-- title:
--   Spread
-- statement:
--   Definitions and structural lemmas for Spread, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/Spread.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
end Formalism.InvariantFactorPaths.INST


