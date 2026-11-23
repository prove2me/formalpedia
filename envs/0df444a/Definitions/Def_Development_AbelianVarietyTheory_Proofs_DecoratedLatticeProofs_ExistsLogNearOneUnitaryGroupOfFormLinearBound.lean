-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBound
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:44.531733+00:00
-- url     : https://prove2.me/theorems/d915799a-afe7-4afe-a5ce-7cdfc6e23d1f
-- title:
--   Exists Log Near One Unitary Group Of Form Linear Bound
-- statement:
--   Definitions and structural lemmas for Exists Log Near One Unitary Group Of Form Linear Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBound.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
namespace GlobalTheory.UnitaryLog
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end GlobalTheory.UnitaryLog


