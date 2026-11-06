-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
-- name    : QEC_Semantics_Dynamics_Davies_FrequencyLocality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:11:13.343046+00:00
-- url     : https://prove2.me/theorems/e0d5207a-74f3-495c-8e47-e7ca605f2ed8
-- title:
--   Frequency Locality
-- statement:
--   Definitions and structural lemmas for Frequency Locality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
namespace QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def energyDifference (H A : Operator V) : Operator V := A*H-H*A
def actualFrequency (H : Operator V) (hH : H.IsSymmetric) (A : Operator V) (ω : ℝ) :
    Operator V := frequencyComponent (hamiltonianBasis H hH) (hamiltonianEnergies H hH) A ω
def frequencyFilterStep (H : Operator V) (ω ν : ℝ) (A : Operator V) : Operator V :=
  (((ω-ν : ℝ) : ℂ)⁻¹) • (energyDifference H A - (ν : ℂ) • A)
def frequencyFilter (H : Operator V) (ω : ℝ) (l : List ℝ) (A : Operator V) : Operator V :=
  l.foldr (frequencyFilterStep H ω) A
variable {q : Type} [Fintype q] [DecidableEq q]
end
end QEC.Semantics.Davies


