-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Imports
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:21.75731+00:00
-- url     : https://prove2.me/theorems/bd0fdd81-88a6-4987-9bbc-bfa66812cf74
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/Imports.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_CthFac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups
namespace GlobalTheory.Sieg
def th (z : ℂ) (τ : ℍ) : ℂ :=
  ee ((τ : ℂ) / 12) * (ee (z / 2) - ee (-z / 2)) *
    ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹)
def act (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : Fin 2 → ℚ := fun i => ∑ j, x j * (((γ : Matrix (Fin 2) (Fin 2) ℤ) j i : ℤ) : ℚ)
end GlobalTheory.Sieg


