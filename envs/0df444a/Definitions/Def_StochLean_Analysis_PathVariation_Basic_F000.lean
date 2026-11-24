-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Basic_F000
-- name    : StochLean_Analysis_PathVariation_Basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T13:11:12.31734+00:00
-- url     : https://prove2.me/theorems/d0813943-737e-4678-88ab-66b326f8e68e
-- title:
--   StochLean: Analysis.PathVariation.Basic F000

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Deterministic variation along finite partitions

This layer has no probability space or filtration. Partitions may repeat endpoints;
zero-length cells contribute zero to quadratic variation. The empty partition is
available precisely at horizon zero. Raw stochastic brackets, which retain the
initial square, are not defined here.
-/

@[expose] public section

open Filter Finset
open scoped NNReal Topology BigOperators

namespace StochLean

/-- Finite ordered endpoints of `[0,T]`. Repetition permits degenerate horizons. -/
structure TimePartition (T : ℝ≥0) where
  size : ℕ
  point : Fin (size + 1) → ℝ≥0
  monotone_point : Monotone point
  first_eq_zero : point 0 = 0
  last_eq_horizon : point (Fin.last size) = T
namespace TimePartition

variable {T : ℝ≥0}

def left (π : TimePartition T) (i : Fin π.size) : ℝ≥0 := by exact π.point i.castSucc
def right (π : TimePartition T) (i : Fin π.size) : ℝ≥0 := π.point i.succ
end TimePartition

variable {T : ℝ≥0}

end StochLean


