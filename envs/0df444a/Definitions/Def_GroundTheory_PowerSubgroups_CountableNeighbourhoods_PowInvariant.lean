-- Prove2me | Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PowInvariant
-- name    : GroundTheory_PowerSubgroups_CountableNeighbourhoods_PowInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:54.945799+00:00
-- url     : https://prove2.me/theorems/49cea8b8-dd7a-413c-a081-db9bf9ffae7d
-- title:
--   Pow Invariant
-- statement:
--   Definitions and structural lemmas for Pow Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PowInvariant.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Variant₂.N1
def mulZPowers (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ)) (s : Gal(AlgebraicClosure ℚ/ℚ))
    (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    Subgroup Gal(AlgebraicClosure ℚ/ℚ) where
  carrier := {x | ∃ k : ℤ, ∃ u ∈ U, x = s ^ k * u}
  one_mem' := ⟨0, 1, U.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, u, hu, rfl⟩ ⟨b, v, hv, rfl⟩
    refine ⟨a + b, s ^ (-b) * u * (s ^ (-b))⁻¹ * v, U.mul_mem (hU (-b) u hu) hv, ?_⟩
    rw [zpow_add, zpow_neg, inv_inv]
    group
  inv_mem' := by
    rintro _ ⟨k, u, hu, rfl⟩
    refine ⟨-k, s ^ k * u⁻¹ * (s ^ k)⁻¹, hU k _ (U.inv_mem hu), ?_⟩
    rw [zpow_neg]
    group
end GroundTheory.Variant₂.N1


