-- Prove2me | Definitions.Def_Submission_ThreeSum_Balancing
-- name    : Submission_ThreeSum_Balancing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T06:38:33.281522+00:00
-- url     : https://prove2.me/theorems/a15f5a07-fffa-4c02-b967-c342462c415a
-- title:
--   Balancing
-- statement:
--   Definitions and structural lemmas for Balancing, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Balancing.lean

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace ThreeSum.Balancing
open Finset
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G]
def correlation (F H : G → ℕ) (d : G) : ℕ := ∑ k, F k * H (k - d)
def chooseOffset [Inhabited G] (keys : List G) (F H : G → ℕ) : G :=
  (keys.argmin (correlation F H)).getD default
end ThreeSum.Balancing


