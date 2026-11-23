-- Prove2me | Definitions.Def_AutomataTheory_Automata_Hist
-- name    : AutomataTheory_Automata_Hist
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:11:17.678282+00:00
-- url     : https://prove2.me/theorems/ac2ef1d1-8795-4f3d-88d6-60243c72b4d1
-- title:
--   Hist
-- statement:
--   Definitions and structural lemmas for Hist, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Hist.lean

import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
namespace Automata
section AutomataHist
variable {A H : Type}
def NA.addHist (M : NA A) (hist_init : Set H) (hist_next : M.State × H → A → Set H) : NA A where
  State := M.State × H
  init := { s | s.1 ∈ M.init ∧ s.2 ∈ hist_init }
  next := fun s a ↦ { s' | s'.1 ∈ M.next s.1 a ∧ s'.2 ∈ hist_next s a }
attribute [local instance_reducible] NA.addHist
variable {M : NA A} {hist_init : Set H} {hist_next : M.State × H → A → Set H}
def MakeHist (as : Stream' A) (ss : Stream' M.State) (hs0 : H) (hs' : M.State × H → A -> H) : Stream' H
  | 0 => hs0
  | k + 1 => hs' (ss k, MakeHist as ss hs0 hs' k) (as k)
end AutomataHist


