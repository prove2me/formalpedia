-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
-- name    : QEC_Semantics_Dynamics_Davies_Hamiltonian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:07:10.668511+00:00
-- url     : https://prove2.me/theorems/e3d2c96e-357a-4eae-9642-18ffd5de7f14
-- title:
--   Hamiltonian
-- statement:
--   Definitions and structural lemmas for Hamiltonian, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Hamiltonian.lean

import Definitions.Def_QEC_Semantics_Dynamics_Davies_NormBound
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
set_option autoImplicit false
namespace QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V] [Nontrivial V]
variable {κ : Type*} [Fintype κ]
abbrev HamiltonianFrequency (H : Operator V) (hH : H.IsSymmetric) :=
  Frequency (hamiltonianEnergies H hH)
def hamiltonianJump (H : Operator V) (hH : H.IsSymmetric) (A : κ → Operator V)
    (rate : κ → HamiltonianFrequency H hH → ℝ) : κ × HamiltonianFrequency H hH → Operator V :=
  weightedJump (hamiltonianBasis H hH) (hamiltonianEnergies H hH) A rate
def hamiltonianGibbs (H : Operator V) (hH : H.IsSymmetric) (β : ℝ) : DensityOperator V := by
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  exact spectralGibbsDensity (hamiltonianBasis H hH) (hamiltonianEnergies H hH) β
def hamiltonianDissipator (H : Operator V) (hH : H.IsSymmetric) (A : κ → Operator V)
    (rate : κ → HamiltonianFrequency H hH → ℝ) : Superoperator V :=
  lindbladDissipator (hamiltonianJump H hH A rate)
def hamiltonianEnergyProjector (H : Operator V) (hH : H.IsSymmetric) (E : ℝ) : Operator V :=
  energyProjector (hamiltonianBasis H hH) (hamiltonianEnergies H hH) E
end
end QEC.Semantics.Davies


