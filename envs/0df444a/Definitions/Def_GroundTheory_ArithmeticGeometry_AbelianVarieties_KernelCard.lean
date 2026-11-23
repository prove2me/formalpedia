-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:31.052149+00:00
-- url     : https://prove2.me/theorems/0dd2754f-276d-402e-903b-d904faf45431
-- title:
--   Kernel Card
-- statement:
--   Definitions and structural lemmas for Kernel Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
section Coprime
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [W.IsElliptic]
end Coprime
section Count
variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
end Count
section Kernel
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic]
end Kernel
end GroundTheory.Arith.Abelian


