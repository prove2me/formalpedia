-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
-- name    : Submission_ThreeSum_TernaryCoverRankFibers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:45:45.504964+00:00
-- url     : https://prove2.me/theorems/0119c787-dbe4-435e-95b7-7113e7664204
-- title:
--   Ternary Cover Rank Fibers
-- statement:
--   Definitions and structural lemmas for Ternary Cover Rank Fibers, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRankFibers.lean

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverRankFibers
open Finset
variable {K : Type*} [Field K]
variable {E ι : Type*} [Fintype E] [Fintype ι] [DecidableEq K]
def projectionFiber (left right : E → ι → K) (β γ : K) (q : ι → K) : Finset E :=
  univ.filter fun e => ∀ i, β * left e i + γ * right e i = q i
def affineFiber (left right : E → ι → K) (V : Submodule K (K × K))
    (offset : ι → K × K) : Finset E := by
  classical
  exact univ.filter fun e => ∀ i, (left e i, right e i) - offset i ∈ V
end ThreeSum.TernaryCoverRankFibers


