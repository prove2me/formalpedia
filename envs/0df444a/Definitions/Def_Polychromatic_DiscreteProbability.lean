-- Prove2me | Definitions.Def_Polychromatic_DiscreteProbability
-- name    : Polychromatic_DiscreteProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T08:34:16.339013+00:00
-- url     : https://prove2.me/theorems/ddbe88ef-55e1-4771-b058-3cf6e332e5b1
-- title:
--   Discrete Probability
-- statement:
--   Definitions and structural lemmas for Discrete Probability, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/DiscreteProbability.lean

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
set_option autoImplicit true
open Finset
variable {ι α : Type*} {s : Finset ι} {p f : ι → α} {c : α} [LinearOrder α]


