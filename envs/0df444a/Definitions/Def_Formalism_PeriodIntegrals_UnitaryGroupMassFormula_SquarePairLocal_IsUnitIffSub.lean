-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsUnitIffSub
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:50.962797+00:00
-- url     : https://prove2.me/theorems/260acaa4-8a39-4c60-8e17-5f39096b3002
-- title:
--   Is Unit Iff Sub
-- statement:
--   Definitions and structural lemmas for Is Unit Iff Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsUnitIffSub.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Theorems.Thm_PI_SqPairLocal_mem_fixSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
namespace PI.SqPairLocal.FixD
variable {R : Type} [CommRing R] [IsDomain R] (σ : R ≃+* R)
theorem isUnit_sub {x : fixSub σ} (hu : IsUnit (x : R)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hu
  have hx : σ (x : R) = x := (mem_fixSub σ x).1 x.2
  have hinv : (↑u⁻¹ : R) ∈ fixSub σ := by
    rw [mem_fixSub]
    have h1 : σ (↑u⁻¹ : R) * (x : R) = 1 := by
      rw [← hx, ← map_mul, ← hu, Units.inv_mul, map_one]
    calc σ (↑u⁻¹ : R) = σ (↑u⁻¹ : R) * ((x : R) * ↑u⁻¹) := by rw [← hu, Units.mul_inv, mul_one]
      _ = ↑u⁻¹ := by rw [← mul_assoc, h1, one_mul]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  show (x : R) * ↑u⁻¹ = 1
  rw [← hu, Units.mul_inv]
instance isLocalHom_sub : IsLocalHom (fixSub σ).subtype :=
  ⟨fun _ hx => isUnit_sub σ hx⟩
end FixD
end PI.SqPairLocal


