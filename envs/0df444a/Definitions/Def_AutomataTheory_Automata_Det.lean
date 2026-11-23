-- Prove2me | Definitions.Def_AutomataTheory_Automata_Det
-- name    : AutomataTheory_Automata_Det
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:12:30.093822+00:00
-- url     : https://prove2.me/theorems/d1a311a7-7843-4d99-b34f-975b513903bf
-- title:
--   Det
-- statement:
--   Definitions and structural lemmas for Det, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Det.lean

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
namespace Automata
section DetAutomataBasic
class DA (A : Type) where
  State : Type
  init : State
  next : State → A → State
variable {A : Type}
def DA.toNA (M : DA A) : NA A where
  State := M.State
  init := {M.init}
  next := ({M.next · ·})
def DA.DetRun (M : DA A) (as : Stream' A) : Stream' M.State
  | 0 => M.init
  | k + 1 => M.next (DetRun M as k) (as k)
def DA.RunFromOn (M : DA A) (s : M.State) (al : List A) : M.State :=
  al.foldl M.next s
def DA.RunOn (M : DA A) : List A → M.State :=
  M.RunFromOn M.init
attribute [local instance_reducible] DA.toNA
variable {M : DA A}
end DetAutomataBasic
section DetAcceptedLang
variable {A : Type} {M : DA A} {acc : Set M.State}
end DetAcceptedLang
section DetMullerAccept
variable {A : Type}
def DA.MullerAccept (M : DA A) (accSet : Set (Set M.State)) (as : Stream' A) :=
  InfOcc (M.DetRun as) ∈ accSet
end DetMullerAccept


