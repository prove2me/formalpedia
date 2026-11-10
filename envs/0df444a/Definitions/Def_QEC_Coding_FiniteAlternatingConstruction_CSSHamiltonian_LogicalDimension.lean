-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:27:37.706716+00:00
-- url     : https://prove2.me/theorems/3207c603-3cb5-4ffd-bcc4-0b273c785875
-- title:
--   Logical Dimension
-- statement:
--   Definitions and structural lemmas for Logical Dimension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LogicalDimension.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open PauliSymplectic Semantics MultiscaleDecoder
variable (S : OddScale) (n : Nat)
def labelledCode : QuantumCode (Qubit.QubitRegister (Physical S n)) :=
  (binaryCSSStabilizerCodeOfParityChecks (zSyndrome S n) (xSyndrome S n)
    (row_orthogonal S n)).code
local instance _p2m_local_instance_e0d1cb1e0b_118 : Fintype (LinearMap.range (zSyndrome S n)) := Fintype.ofFinite _
local instance _p2m_local_instance_e0d1cb1e0b_119 : Fintype (LinearMap.range (xSyndrome S n)) := Fintype.ofFinite _
abbrev visibleRealizable := CSSGibbs.realizableSyndromes (zSyndrome S n) (xSyndrome S n)
def indexedLabelledCode (depth : Nat) (i : LevelIndex depth) :
    QuantumCode (Qubit.QubitRegister (BDL26IndexedDecoder.FamilyQ S depth i)) :=
  labelledCode S i.val
end QEC.Coding.BDL26CSSHamiltonian


