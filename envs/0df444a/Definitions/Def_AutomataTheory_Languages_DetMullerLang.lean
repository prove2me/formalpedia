-- Prove2me | Definitions.Def_AutomataTheory_Languages_DetMullerLang
-- name    : AutomataTheory_Languages_DetMullerLang
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:48:43.232108+00:00
-- url     : https://prove2.me/theorems/c8f427b7-f310-4ff9-8cbc-a7823a519013
-- title:
--   Det Muller Lang
-- statement:
--   Definitions and structural lemmas for Det Muller Lang, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
section DetMullerLang
variable {A : Type}
def DetMullerLang (L : Set (Stream' A)) :=
  ∃ M : Automata.DA A, ∃ accSet : Set (Set M.State),
  Finite M.State ∧ { as | M.MullerAccept accSet as } = L
end DetMullerLang


