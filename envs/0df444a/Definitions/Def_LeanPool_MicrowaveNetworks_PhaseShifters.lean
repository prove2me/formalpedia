-- Prove2me | Definitions.Def_LeanPool_MicrowaveNetworks_PhaseShifters
-- name    : LeanPool_MicrowaveNetworks_PhaseShifters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:36:07.472543+00:00
-- url     : https://prove2.me/theorems/900f53f4-5cd1-4561-b025-2e87d66a26a9
-- title:
--   Phase Shifters
-- statement:
--   Definitions and structural lemmas for Phase Shifters, from Matteo Nerini and Claude AI; maintained by LeanPool contributors's pinned Microwave network synthesis and power-of-two DFT implementation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/PhaseShifters.lean

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace MiLAC.PhaseShifters
@[expose] noncomputable def permutedPhaseDiagonal {n : ℕ}
    (φ : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Network n :=
  σ.toPEquiv.toMatrix *
    Matrix.diagonal (fun i => Complex.exp (φ i * Complex.I))
end MiLAC.PhaseShifters


