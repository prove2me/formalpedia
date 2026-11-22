-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_LatRetract
-- name    : Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_LatRetract
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:57.178802+00:00
-- url     : https://prove2.me/theorems/abf0eb5d-5621-487e-ad06-c563c5a861aa
-- title:
--   Lat Retract
-- statement:
--   Definitions and structural lemmas for Lat Retract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/LatRetract.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.flipOneThree.Pf.KP
open Submodule
section LatRetract
variable {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V']
  {ι ι' : Type} [Fintype ι] [Fintype ι']
end LatRetract
end Formalism.MainNotions.flipOneThree.Pf.KP


