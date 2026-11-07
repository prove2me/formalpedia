-- Prove2me | Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Gibbs
-- name    : QEC_Coding_CSS_GibbsSyndrome_Gibbs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:25:36.341971+00:00
-- url     : https://prove2.me/theorems/d0060293-e74e-432b-bfa1-984404c621d3
-- title:
--   Gibbs
-- statement:
--   Definitions and structural lemmas for Gibbs, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/GibbsSyndrome/Gibbs.lean

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics Semantics.Davies Semantics.ThermalEncoding
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
local instance _p2m_local_instance_28fb820634_14 : Fintype (LinearMap.range P) := Fintype.ofFinite _
local instance _p2m_local_instance_28fb820634_15 : Fintype (LinearMap.range Q) := Fintype.ofFinite _
def rowPartition (t : ℝ) : ℝ := ∑ u : LinearMap.range P, Real.exp (-t * HammingWeight u.val)
def gibbs (β : ℝ) : DensityOperator (Qubit.QubitRegister ι) :=
  hamiltonianGibbs (hamiltonian P Q) (hamiltonian_symmetric P Q) β
def thermalExponential (β : ℝ) : Operator (Qubit.QubitRegister ι) :=
  (NormedSpace.exp ((-β : ℂ) • LinearMap.toContinuousLinearMap (hamiltonian P Q))).toLinearMap
def physicalPartition (β : ℝ) : ℝ :=
  gibbsPartitionFunction β (hamiltonianEnergies (hamiltonian P Q) (hamiltonian_symmetric P Q))
def jointProbability (β : ℝ) (s : Word (ZMod 2) (Sum κP κQ)) : ℝ :=
  if s ∈ realizableSyndromes P Q then
    Real.exp (-(2 * β) * HammingWeight s) / (rowPartition P (2 * β) * rowPartition Q (2 * β))
  else 0
def rowProbability (t : ℝ) (u : LinearMap.range P) : ℝ :=
  Real.exp (-t * HammingWeight u.val) / rowPartition P t
def badProjector (B : Finset (Word (ZMod 2) (Sum κP κQ))) : Operator (Qubit.QubitRegister ι) :=
  ∑ s ∈ B, projector P Q horth s
def pMarginalProjector (u : LinearMap.range P) : Operator (Qubit.QubitRegister ι) :=
  ∑ v : LinearMap.range Q, projector P Q horth (joinSyndrome u.val v.val)
def qMarginalProjector (v : LinearMap.range Q) : Operator (Qubit.QubitRegister ι) :=
  ∑ u : LinearMap.range P, projector P Q horth (joinSyndrome u.val v.val)
end QEC.Coding.CSSGibbs


