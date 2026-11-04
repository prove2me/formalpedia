-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
-- name    : Submission_ThreeSum_TernaryCoverFibers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:41:07.617609+00:00
-- url     : https://prove2.me/theorems/cd35610d-3026-4b9c-8a72-15bd161c3af0
-- title:
--   Ternary Cover Fibers
-- statement:
--   Definitions and structural lemmas for Ternary Cover Fibers, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFibers.lean

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace ThreeSum.TernaryCoverFibers
open Finset
open scoped BigOperators
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
variable [DecidableEq Q] [DecidableEq K] [AddCommGroup K]
def rawPairCount (left right : E → K) (a b : K) : ℕ :=
  (univ.filter fun e => left e = a ∧ right e = b).card
def outputFiberCount (outputHash : Q → K) (o : K) : ℕ :=
  (univ.filter fun q => outputHash q = o).card
end ThreeSum.TernaryCoverFibers


