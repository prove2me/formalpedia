-- Prove2me | Definitions.Def_AutomataTheory_Automata_OI2
-- name    : AutomataTheory_Automata_OI2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:12:41.32809+00:00
-- url     : https://prove2.me/theorems/9d148efd-75ac-494a-a3e8-570982c165d7
-- title:
--   OI2
-- statement:
--   Definitions and structural lemmas for OI2, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/OI2.lean

import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Sequences_Temporal
set_option autoImplicit true
open Function Set Filter Stream'
namespace Automata
section AutomataOI2
open Classical
variable {A : Type} (M : Fin 2 → NA A) (acc : (i : Fin 2) → Set ((M i).State))
def NA.OI2_HistInit : Set (Fin 2) := {0}
def NA.OI2_HistNext : (NA.Prod M).State × Fin 2 → A → Set (Fin 2) :=
  fun s _ ↦
    if s.1 0 ∈ acc 0 ∧ s.2 = 0 then {1} else
    if s.1 1 ∈ acc 1 ∧ s.2 = 1 then {0} else {s.2}
def NA.OI2 : NA A :=
  (NA.Prod M).addHist NA.OI2_HistInit (NA.OI2_HistNext M acc)
def NA.OI2_Acc : Set (NA.OI2 M acc).State :=
  { s | s.1 0 ∈ acc 0 ∧ s.2 = 0 } ∪ { s | s.1 1 ∈ acc 1 ∧ s.2 = 1 }
end AutomataOI2


