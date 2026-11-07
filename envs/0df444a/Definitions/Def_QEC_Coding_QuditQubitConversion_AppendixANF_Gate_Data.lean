-- Prove2me | Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
-- name    : QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:42:36.575844+00:00
-- url     : https://prove2.me/theorems/8462c8b6-644d-42f1-bc64-c44e51c8845a
-- title:
--   Data
-- statement:
--   Definitions and structural lemmas for Data, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/AppendixANF/Gate/Data.lean

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
set_option autoImplicit false
noncomputable section
namespace QEC.Coding
open scoped BigOperators
open Why24BooleanANF
open Why24AppendixANF
inductive Why24AppendixGate where
  | z (site : Fin 10)
  | cz (left right : Fin 10)
  | ccz (first second third : Fin 10)
  deriving DecidableEq
def why24AppendixZGateList : List Why24AppendixGate :=
  List.ofFn fun site : Fin 10 => .z site
def why24AppendixGateList : List Why24AppendixGate :=
  why24AppendixZGateList ++
    quadraticGatePairs.map (fun pair => .cz pair.1 pair.2) ++
    cubicGateTriples.map
      (fun triple => .ccz triple.1 triple.2.1 triple.2.2)
def why24AppendixGateIsZ : Why24AppendixGate → Bool
  | .z _ => true
  | .cz _ _ => false
  | .ccz _ _ _ => false
def why24AppendixGateIsCZ : Why24AppendixGate → Bool
  | .z _ => false
  | .cz _ _ => true
  | .ccz _ _ _ => false
def why24AppendixGateIsCCZ : Why24AppendixGate → Bool
  | .z _ => false
  | .cz _ _ => false
  | .ccz _ _ _ => true
def why24AppendixGateCounts : Nat × Nat × Nat :=
  (why24AppendixGateList.countP why24AppendixGateIsZ,
    why24AppendixGateList.countP why24AppendixGateIsCZ,
    why24AppendixGateList.countP why24AppendixGateIsCCZ)
def why24AppendixGateANF : Why24AppendixGate → ANF
  | .z site => generator site
  | .cz left right => generator left * generator right
  | .ccz first second third =>
      generator first * generator second * generator third
def why24AppendixGateListANF (gates : List Why24AppendixGate) : ANF :=
  gates.foldr (fun gate polynomial => why24AppendixGateANF gate + polynomial) 0
def why24AppendixWordGatePhase (gate : Why24AppendixGate)
    (word : Why24AppendixANF.Word) : ZMod 2 :=
  match gate with
  | .z site => word site
  | .cz left right => word left * word right
  | .ccz first second third => word first * word second * word third
def why24AppendixWordPhaseList (gates : List Why24AppendixGate)
    (word : Why24AppendixANF.Word) : ZMod 2 :=
  gates.foldr (fun gate phase => why24AppendixWordGatePhase gate word + phase) 0
end QEC.Coding


