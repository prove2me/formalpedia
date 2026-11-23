-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:04.544497+00:00
-- url     : https://prove2.me/theorems/aa002e0c-f774-451d-a75a-d614e422133c
-- title:
--   PStabilizer Levi Matrices
-- statement:
--   Definitions and structural lemmas for PStabilizer Levi Matrices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
def leftInv (H : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) : Matrix κ ι ℂ := (Bᴴ * H * B)⁻¹ * Bᴴ * H
def leviSec (H : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (m : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  1 - B * leftInv H B + B * m * leftInv H B
def leviProj (H : Matrix ι ι ℂ) (B : Matrix ι κ ℂ) (g : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  leftInv H B * g * B
section Forms
variable {κ' : Type*} [Fintype κ']
end Forms
section Section
variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ}
end Section
section Projection
variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ} {X Y : ι → ℂ}
variable (hH : Hᴴ = H) (hG : IsUnit (Bᴴ * H * B).det) (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0)
    (hBY : Bᴴ *ᵥ (H *ᵥ Y) = 0) (hXX : star X ⬝ᵥ (H *ᵥ X) = 0) (hYY : star Y ⬝ᵥ (H *ᵥ Y) = 0)
    (hXY : star X ⬝ᵥ (H *ᵥ Y) = 1) (hspan : ∀ z, ∃ (a b : ℂ) (c : κ → ℂ), z = a • X + b • Y + B *ᵥ c)
include hH hG hBX hBY hXX hYY hXY hspan
end Projection
end
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi


