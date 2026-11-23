-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:31.116185+00:00
-- url     : https://prove2.me/theorems/1480a6fd-237f-4db5-9059-efa93866b416
-- title:
--   Coef Op
-- statement:
--   Definitions and structural lemmas for Coef Op, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CoefOp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra
end Frob
end ReciprocityTheory.ChartRestriction.DS


