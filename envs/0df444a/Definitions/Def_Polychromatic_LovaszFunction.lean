-- Prove2me | Definitions.Def_Polychromatic_LovaszFunction
-- name    : Polychromatic_LovaszFunction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:40:31.843079+00:00
-- url     : https://prove2.me/theorems/56ebd33e-a668-4cba-b6d5-aaf1c4411ea2
-- title:
--   Lovasz Function
-- statement:
--   Definitions and structural lemmas for Lovasz Function, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
open Finset
noncomputable def straussFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ S : Finset ℤ, m ≤ #S → HasPolychromColouring (Fin k) S}
open Asymptotics Filter


