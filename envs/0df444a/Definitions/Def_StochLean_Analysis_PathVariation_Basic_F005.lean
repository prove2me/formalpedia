-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
-- name    : StochLean_Analysis_PathVariation_Basic_F005
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:14.201595+00:00
-- url     : https://prove2.me/theorems/235af124-9c38-4d62-8d18-f6b91a0c6174
-- title:
--   StochLean: Analysis.PathVariation.Basic F005

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F004

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

namespace TimePartition

variable {T : ℝ≥0}

end TimePartition

variable {T : ℝ≥0}

noncomputable def pVariationSum (p : ℝ) (π : TimePartition T) (f : ℝ≥0 → ℝ) : ℝ :=
  ∑ i, |π.increment f i| ^ p
def quadraticVariationSum (π : TimePartition T) (f : ℝ≥0 → ℝ) : ℝ :=
  ∑ i, (π.increment f i) ^ 2
def covariationSum (π : TimePartition T) (f g : ℝ≥0 → ℝ) : ℝ :=
  ∑ i, π.increment f i * π.increment g i
def HasPVariationAlong (p : ℝ) (π : ℕ → TimePartition T)
    (f : ℝ≥0 → ℝ) (value : ℝ) : Prop :=
  Tendsto (fun n ↦ pVariationSum p (π n) f) atTop (𝓝 value)
def HasQuadraticVariationAlong (π : ℕ → TimePartition T)
    (f : ℝ≥0 → ℝ) (value : ℝ) : Prop :=
  Tendsto (fun n ↦ quadraticVariationSum (π n) f) atTop (𝓝 value)
def HasCovariationAlong (π : ℕ → TimePartition T)
    (f g : ℝ≥0 → ℝ) (value : ℝ) : Prop :=
  Tendsto (fun n ↦ covariationSum (π n) f g) atTop (𝓝 value)
end StochLean


