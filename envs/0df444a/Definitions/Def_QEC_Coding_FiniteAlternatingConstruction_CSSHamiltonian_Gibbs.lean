-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:55:23.260485+00:00
-- url     : https://prove2.me/theorems/b503f791-5838-45d5-a923-e8183f3728ae
-- title:
--   Gibbs
-- statement:
--   Definitions and structural lemmas for Gibbs, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Gibbs.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity PauliSymplectic Semantics
open scoped BigOperators
variable (S : OddScale) (n : Nat)
def hamiltonian : Operator (Qubit.QubitRegister (Physical S n)) :=
  -∑ j : Sum (ZLabel S n) (XLabel S n), toQubitOperator (check S n j)
abbrev projector := CSSGibbs.projector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
abbrev sector := CSSGibbs.sector (zSyndrome S n) (xSyndrome S n) (row_orthogonal S n)
abbrev realizable := CSSGibbs.Realizable (zSyndrome S n) (xSyndrome S n)
abbrev multiplicity := CSSGibbs.multiplicity (zSyndrome S n) (xSyndrome S n)
abbrev gibbs := CSSGibbs.gibbs (zSyndrome S n) (xSyndrome S n)
abbrev physicalPartition := CSSGibbs.physicalPartition (zSyndrome S n) (xSyndrome S n)
abbrev thermalExponential := CSSGibbs.thermalExponential (zSyndrome S n) (xSyndrome S n)
local instance _p2m_local_instance_ce658d38ff_24 : Fintype (LinearMap.range (zSyndrome S n)) := Fintype.ofFinite _
local instance _p2m_local_instance_ce658d38ff_25 : Fintype (LinearMap.range (xSyndrome S n)) := Fintype.ofFinite _
end QEC.Coding.BDL26CSSHamiltonian


