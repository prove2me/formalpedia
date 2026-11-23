-- Prove2me | Definitions.Def_AutomataTheory_Languages_RegLang
-- name    : AutomataTheory_Languages_RegLang
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:14:23.595324+00:00
-- url     : https://prove2.me/theorems/ef151ed1-7df0-49db-9013-dcbce9d6ec05
-- title:
--   Reg Lang
-- statement:
--   Definitions and structural lemmas for Reg Lang, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
section RegLang
open Classical
variable {A : Type}
def RegLang (L : Set (List A)) :=
  ∃ M : Automata.NA A, ∃ acc : Set M.State, Finite M.State ∧ M.AcceptedLang acc = L
end RegLang


