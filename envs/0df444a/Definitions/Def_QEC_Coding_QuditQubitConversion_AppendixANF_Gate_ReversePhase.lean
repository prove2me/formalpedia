-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
-- name    : QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:44:24.725244+00:00
-- url     : https://prove2.me/theorems/7eed0f2a-3788-4e7e-9133-f07c578c2d04
-- title:
--   Reverse Phase
-- statement:
--   Definitions and structural lemmas for Reverse Phase, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/ReversePhase.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
set_option autoImplicit false
noncomputable section
namespace QEC.Coding
def why24AppendixRetainedSites : Finset (Fin 10) :=
  {0, 1, 2}
abbrev Why24CCZSpace : Type :=
  Semantics.Qubit.QubitRegister (Fin 3)
abbrev Why24AppendixReverseOutcome : Type :=
  Semantics.Qubit.Bitstring (Fin 7)
def why24AppendixReverseZeroOutcome : Why24AppendixReverseOutcome :=
  fun _ => 0
def why24AppendixReverseRecombine
    (retained : Semantics.Qubit.Bitstring (Fin 3))
    (outcome : Why24AppendixReverseOutcome) :
    Semantics.Qubit.Bitstring (Fin 10) :=
  fun site =>
    if hsite : (site : Nat) < 3 then
      retained ⟨site, hsite⟩
    else
      outcome ⟨(site : Nat) - 3, by omega⟩
def why24CCZPhase (retained : Semantics.Qubit.Bitstring (Fin 3)) : ZMod 2 :=
  let word := PauliSymplectic.bitstringWordEquiv (Fin 3) retained
  word 0 * word 1 * word 2
def why24AppendixReverseSourcePhase
    (outcome : Why24AppendixReverseOutcome)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) : ZMod 2 :=
  why24AppendixWordPhaseList why24AppendixGateList
    (PauliSymplectic.bitstringWordEquiv (Fin 10)
      (why24AppendixReverseRecombine retained outcome))
def why24AppendixReverseCorrectionPhase
    (outcome : Why24AppendixReverseOutcome)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) : ZMod 2 :=
  why24AppendixReverseSourcePhase outcome retained + why24CCZPhase retained
end QEC.Coding


