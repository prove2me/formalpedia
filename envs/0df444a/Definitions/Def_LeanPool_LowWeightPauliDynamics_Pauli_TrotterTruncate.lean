-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:34:36.440185+00:00
-- url     : https://prove2.me/theorems/d665f41e-595c-4d76-87fb-2df0ba554127
-- title:
--   Trotter Truncate
-- statement:
--   Definitions and structural lemmas for Trotter Truncate, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TrotterTruncate.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
namespace PauliString
open Finset
variable {n : ℕ}
def trotterSchedule (period wstar : ℕ) (g : ℕ) : Finset (PauliIndex n) :=
  if (g + 1) % period = 0 then (highSet n wstar)ᶜ else univ
noncomputable def trotterTraj (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    ℕ → Matrix (Bits n) (Bits n) ℂ :=
  trajTrunc (fun g => Gs (g % period)) (fun g => θ (g % period))
    (trotterSchedule period wstar) O
noncomputable def trotterStepTraj (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | d + 1 => truncOp (highSet n wstar)ᶜ
      (traj Gs θ (trotterStepTraj Gs θ period wstar O d) period)
noncomputable def discardedStep (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (period wstar : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) (d : ℕ) :
    Matrix (Bits n) (Bits n) ℂ :=
  traj Gs θ (trotterStepTraj Gs θ period wstar O d) period -
    trotterStepTraj Gs θ period wstar O (d + 1)
end PauliString
end Lean4LPD


