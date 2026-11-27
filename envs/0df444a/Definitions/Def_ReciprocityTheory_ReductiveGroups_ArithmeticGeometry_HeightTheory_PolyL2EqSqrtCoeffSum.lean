-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-27T06:02:54.322324+00:00
-- url     : https://prove2.me/theorems/7b0b910b-1081-52a8-8616-55a9bd714bdd
-- title:
--   Poly L2 Eq Sqrt Coeff Sum
-- statement:
--   Definitions and structural lemmas for Poly L2 Eq Sqrt Coeff Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PolyL2EqSqrtCoeffSum.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
def hupsWx (D N : ℕ) : UXVar D N → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
def hupsWu (D N : ℕ) : UXVar D N → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)
end ReciprocityTheory.ChartRestriction.G.T0


