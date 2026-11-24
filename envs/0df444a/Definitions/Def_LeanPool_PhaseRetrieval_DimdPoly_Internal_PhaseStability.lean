-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:22:21.626738+00:00
-- url     : https://prove2.me/theorems/b3dbdade-2ff1-4b74-a1d9-80d804e26d22
-- title:
--   Phase Stability
-- statement:
--   Definitions and structural lemmas for Phase Stability, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/PhaseStability.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_add
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_smul
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_zero

set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace DimdPolyLEAN
def modulusDefect {d : Nat} (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) : ℝ :=
  Real.sqrt <| ∫ z, (‖evalPkappa kappa Q z‖ - ‖evalPkappa kappa F z‖) ^ 2 ∂ gammaD d
def phasedCoeffDistance {d : Nat} {kappa : MultiIndex d} (F Q : Pkappa d kappa)
    (phase : ℂ) : ℝ :=
  ‖phase • Q - F‖
def polyL2Submodule {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    Submodule ℂ (L2Tensor d) where
  carrier := Set.range (evalPkappaL2 kappa)
  zero_mem' := ⟨0, evalPkappaL2_zero hd kappa⟩
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨F, rfl⟩
    rcases hy with ⟨G, rfl⟩
    exact ⟨F + G, evalPkappaL2_add hd kappa F G⟩
  smul_mem' := by
    intro c x hx
    rcases hx with ⟨F, rfl⟩
    exact ⟨c • F, evalPkappaL2_smul hd kappa c F⟩
end DimdPolyLEAN


