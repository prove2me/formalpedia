-- Prove2me | Definitions.Def_AutomataTheory_Automata_Congr
-- name    : AutomataTheory_Automata_Congr
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:13:31.35867+00:00
-- url     : https://prove2.me/theorems/f0919a76-73ff-4437-8675-18fcfa735d4e
-- title:
--   Congr
-- statement:
--   Definitions and structural lemmas for Congr, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Congr.lean

import Definitions.Def_AutomataTheory_Congruences_Basic
import Definitions.Def_AutomataTheory_Automata_Det
set_option autoImplicit true
open Function Set Stream'
attribute [local instance_reducible] Stream' Congruence.QuotType
section AutomataCongr
variable {A : Type}
def Congruence.toDA (c : Congruence A) : Automata.DA A where
  State := c.QuotType
  init := ⟦ [] ⟧
  next := fun s a ↦ Quotient.lift (fun u ↦ ⟦ u ++ [a] ⟧) ( by
    intro u v h_eq
    exact Quotient.sound (Congruence.right_congr u v h_eq [a])
  ) s
attribute [local instance_reducible] Congruence.toDA
variable {c : Congruence A}
end AutomataCongr


