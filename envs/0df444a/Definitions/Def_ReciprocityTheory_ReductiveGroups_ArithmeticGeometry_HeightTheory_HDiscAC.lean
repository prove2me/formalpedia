-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:48.203065+00:00
-- url     : https://prove2.me/theorems/4a46bacc-fab2-4e94-afc6-aca0ac0553ee
-- title:
--   HDisc AC
-- statement:
--   Definitions and structural lemmas for HDisc AC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
namespace HDiscVal
open IsDedekindDomain WithZero ValPl
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
end HDiscVal
end ReciprocityTheory.ChartRestriction.G.T0


