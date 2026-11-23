-- Prove2me | Definitions.Def_AutomataTheory_Languages_ChouekaLemma
-- name    : AutomataTheory_Languages_ChouekaLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:16:34.633821+00:00
-- url     : https://prove2.me/theorems/9a824c2c-901e-4a61-aa65-17b43ff9588b
-- title:
--   Choueka Lemma
-- statement:
--   Definitions and structural lemmas for Choueka Lemma, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/ChouekaLemma.lean

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
set_option autoImplicit true
open Function Set Filter Stream'
open scoped Computability
open Classical
attribute [local implicit_reducible] Stream'
namespace Automata
attribute [local instance_reducible] DA.toNA
section ChouekaLemma
variable {A : Type}
def DA.ChouekaLang (M : DA A) (acc : Set M.State) : Set (List A) :=
  { al | ∃ m, 0 < m ∧ m < al.length ∧
    M.RunOn (al.extract 0 m) ∈ acc ∧ M.RunOn (al.extract m al.length) = M.RunOn al ∧
    ∀ k, m < k → k < al.length → ¬ M.RunOn (al.extract m k) = M.RunOn (al.extract 0 k) }
end ChouekaLemma


