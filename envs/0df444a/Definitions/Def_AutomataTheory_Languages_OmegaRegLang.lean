-- Prove2me | Definitions.Def_AutomataTheory_Languages_OmegaRegLang
-- name    : AutomataTheory_Languages_OmegaRegLang
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:48:02.393877+00:00
-- url     : https://prove2.me/theorems/4c9085c9-a1dd-47ba-9bab-fcad0e17cced
-- title:
--   Omega Reg Lang
-- statement:
--   Definitions and structural lemmas for Omega Reg Lang, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
section OmegaRegLang
open Classical
variable {A : Type}
def OmegaRegLang (L : Set (Stream' A)) :=
  ∃ M : Automata.NA A, ∃ acc : Set M.State, Finite M.State ∧ M.AcceptedOmegaLang acc = L
end OmegaRegLang


