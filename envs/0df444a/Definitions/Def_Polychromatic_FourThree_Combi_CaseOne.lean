-- Prove2me | Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
-- name    : Polychromatic_FourThree_Combi_CaseOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:40:49.169903+00:00
-- url     : https://prove2.me/theorems/f4d8cf60-2031-4def-8252-f14fecb44004
-- title:
--   Case One
-- statement:
--   Definitions and structural lemmas for Case One, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
set_option autoImplicit true
open Finset Pointwise
section Case1_SingleCycle
variable (m : ℕ)
def eqp_idx (q r : ℕ) (p : ℕ) : ℕ :=
  if p < r * (q + 1) then p / (q + 1)
  else r + (p - r * (q + 1)) / q
def eqp_off (q r : ℕ) (p : ℕ) : ℕ :=
  if p < r * (q + 1) then p % (q + 1)
  else (p - r * (q + 1)) % q
section Case1c
end Case1c
section Case1d
end Case1d
end Case1_SingleCycle


