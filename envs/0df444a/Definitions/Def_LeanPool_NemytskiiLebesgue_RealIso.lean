-- Prove2me | Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
-- name    : LeanPool_NemytskiiLebesgue_RealIso
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:33:07.51209+00:00
-- url     : https://prove2.me/theorems/80edddab-2215-4707-9ac7-9398fcb4ebe4
-- title:
--   Real Iso
-- statement:
--   Definitions and structural lemmas for Real Iso, from Petr Girg; Petr Nečesal; Martin Dvořák; Jakub Psutka; LeanPool contributors's pinned Nemytskii operators on Lebesgue spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
@[expose] noncomputable def realLIE : ℝ ≃ₗᵢ[ℝ] ℝ^1 where
  toLinearEquiv :=
    (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).symm
  norm_map' := by
    intro
    rw [EuclideanSpace.norm_eq]
    simp [WithLp.linearEquiv, LinearEquiv.funUnique, Real.sqrt_sq_eq_abs]
end NemytskiiLebesgue


