-- Prove2me | Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
-- name    : Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:36.862975+00:00
-- url     : https://prove2.me/theorems/ed99bc42-4c30-4359-b329-a74f8c47693b
-- title:
--   Has Unique Fixed Point
-- statement:
--   Definitions and structural lemmas for Has Unique Fixed Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/HasUniqueFixedPoint.lean

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
namespace Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
namespace Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
def fixPt : C → MvPowerSeries Z k := fun c A => coeff A ((D.Psi)^[A.degree] 0 c)
end Data
end
end Formalism.BaseCaseIdentities


