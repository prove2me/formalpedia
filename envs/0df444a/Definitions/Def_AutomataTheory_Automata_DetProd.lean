-- Prove2me | Definitions.Def_AutomataTheory_Automata_DetProd
-- name    : AutomataTheory_Automata_DetProd
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:13:29.972279+00:00
-- url     : https://prove2.me/theorems/8f0ef5d1-8713-4689-9869-49dd2ec2754d
-- title:
--   Det Prod
-- statement:
--   Definitions and structural lemmas for Det Prod, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/DetProd.lean

import Definitions.Def_AutomataTheory_Automata_Det
set_option autoImplicit true
open Function Set Filter Stream'
namespace Automata
section DetAutomataProd
variable {I A : Type}
def DA.Prod (M : I → DA A) : DA A where
  State := Π i : I, (M i).State
  init := fun i ↦  (M i).init
  next := fun s a ↦ fun i ↦ (M i).next (s i) a
variable (M : I → DA A)
variable [Finite I] [∀ i, Finite (M i).State]
variable (accSet : (i : I) → Set (Set (M i).State))
def DA.MullerAcc_Inter : Set (Set (DA.Prod M).State) :=
  { acc | ∀ i : I, ((· i) '' acc) ∈ (accSet i) }
def DA.MullerAcc_Union : Set (Set (DA.Prod M).State) :=
  { acc | ∃ i : I, ((· i) '' acc) ∈ (accSet i) }
end DetAutomataProd


