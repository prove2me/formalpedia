-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:21:17.304995+00:00
-- url     : https://prove2.me/theorems/17f8765b-a613-46eb-802f-2ad068c8223f
-- title:
--   Bounded Rate Davies
-- statement:
--   Definitions and structural lemmas for Bounded Rate Davies, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/BoundedRateDavies.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
abbrev oppositeFrequency (ω : BDL26CSSDaviesLocality.Frequency S n) :
    BDL26CSSDaviesLocality.Frequency S n :=
  negFrequency (hamiltonianEnergies (BDL26CSSHamiltonian.hamiltonian S n)
    (hamiltonian_symmetric S n)) ω
def jump (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) :
    CouplingIndex S n × BDL26CSSDaviesLocality.Frequency S n →
      Operator (Qubit.QubitRegister (Physical S n)) :=
  hamiltonianJump (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
    (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate
def dissipator (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) :
    Superoperator (Qubit.QubitRegister (Physical S n)) :=
  hamiltonianDissipator (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
    (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2) rate
end QEC.Coding.BDL26BoundedRateDavies


