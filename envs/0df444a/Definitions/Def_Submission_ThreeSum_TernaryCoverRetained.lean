-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
-- name    : Submission_ThreeSum_TernaryCoverRetained
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:45:40.626693+00:00
-- url     : https://prove2.me/theorems/5bb6a642-b617-409d-b6af-f53f2d171d1f
-- title:
--   Ternary Cover Retained
-- statement:
--   Definitions and structural lemmas for Ternary Cover Retained, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRetained.lean

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace ThreeSum.TernaryCoverRetained
open Finset
open scoped BigOperators
variable {E A B K : Type*} [Fintype E]
variable [DecidableEq A] [DecidableEq B] [DecidableEq K]
def bucket (vertices : Finset A) (hash : A → K) (a : K) : Finset A :=
  vertices.filter fun v => hash v = a
def hits (left : E → A) (right : E → B) (hashL : A → K) (hashR : B → K)
    (a b : K) : Finset E :=
  univ.filter fun e => hashL (left e) = a ∧ hashR (right e) = b
end ThreeSum.TernaryCoverRetained


