-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationBound_AlgebraMapMemFil
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationBound_AlgebraMapMemFil
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:42.411955+00:00
-- url     : https://prove2.me/theorems/6af4ff23-743e-4b52-ac86-e369579d16c5
-- title:
--   Algebra Map Mem Fil
-- statement:
--   Definitions and structural lemmas for Algebra Map Mem Fil, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RamificationBound/AlgebraMapMemFil.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace PI.RamBoundW
section Fil
variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P] {ι : Type*} (δ : ι → Derivation R P P)
def apL : List ι → P →ₗ[R] P
  | [] => LinearMap.id
  | i :: T => apL T ∘ₗ (δ i).toLinearMap
def Fil (a : ℕ) : Submodule R P where
  carrier := {M | ∀ T : List ι, a < T.length → apL δ T M = 0}
  add_mem' := by
    intro M N hM hN T hT
    rw [map_add, hM T hT, hN T hT, add_zero]
  zero_mem' := by
    intro T _
    exact map_zero _
  smul_mem' := by
    intro r M hM T hT
    rw [map_smul, hM T hT, smul_zero]
variable {δ}
end Fil
section Leib
variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]
end Leib
end PI.RamBoundW


