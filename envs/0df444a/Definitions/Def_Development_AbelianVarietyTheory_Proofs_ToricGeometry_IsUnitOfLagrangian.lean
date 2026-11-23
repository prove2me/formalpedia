-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:49.979319+00:00
-- url     : https://prove2.me/theorems/b7b01d5c-8d86-466f-a90c-3d4724b8af82
-- title:
--   Is Unit Of Lagrangian
-- statement:
--   Definitions and structural lemmas for Is Unit Of Lagrangian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfLagrangian.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory.SiegelNormalForm
variable {g : ℕ}
noncomputable def quad (Y : Matrix (Fin g) (Fin g) ℂ) (c z : Fin g → ℂ) : ℂ :=
  Real.pi / 2 * (z ⬝ᵥ Y *ᵥ z) + c ⬝ᵥ z
end GlobalTheory.SiegelNormalForm


