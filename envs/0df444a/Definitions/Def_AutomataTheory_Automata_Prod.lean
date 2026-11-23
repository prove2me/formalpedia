-- Prove2me | Definitions.Def_AutomataTheory_Automata_Prod
-- name    : AutomataTheory_Automata_Prod
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:11:33.611641+00:00
-- url     : https://prove2.me/theorems/182a75e3-79d5-44ec-a810-9a2525e88462
-- title:
--   Prod
-- statement:
--   Definitions and structural lemmas for Prod, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Prod.lean

import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
namespace Automata
section AutomataProd
variable {I A : Type}
def NA.Prod (M : I → NA A) : NA A where
  State := Π i : I, (M i).State
  init := { s | ∀ i : I, (s i) ∈ (M i).init }
  next := fun s a ↦ { s' | ∀ i : I, (s' i) ∈ (M i).next (s i) a }
variable {M : I → NA A}
end AutomataProd
section AcceptedLangInter
variable {I A : Type} (M : I → NA A) (acc : (i : I) → Set ((M i).State))
def NA.Prod_Acc : Set (NA.Prod M).State := { s | ∀ i, (s i) ∈ (acc i) }
end AcceptedLangInter


