-- Prove2me | Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductNormalization
-- name    : MarkovProcess_FiniteTime_CoordinateProductNormalization
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:37:58.33936+00:00
-- url     : https://prove2.me/theorems/774794eb-6f29-454f-b0a4-c1d5e7d39880
-- title:
--   MarkovProcess definitions: FiniteTime.CoordinateProductNormalization
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.FiniteTime.CoordinateProductNormalization`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/CoordinateProductNormalization.lean#L1-L122

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-!
# Normalizing finite coordinate products

This file groups every factor of a `CoordinateProductTerm (Fin n) alpha` by its coordinate.
The normalized representation is a function into `Option C₀(alpha, ℝ)`: an active coordinate
contains the single product of all its original factors, while an inactive coordinate is `none`.

Using `none` is essential because `C₀(alpha, ℝ)` generally has no constant-one element.  Scalar
evaluation interprets inactivity as `1 : ℝ`, but the normalization itself never constructs a
spurious `1 : C₀(alpha, ℝ)`.  The resulting evaluation identity is suitable for backward kernel
recursions that branch only over active coordinates.

This is purely algebraic finite-product infrastructure: it involves no measure and no kernel.
-/

open scoped CompactlySupported ZeroAtInfty BigOperators

namespace MarkovProcess.PiContinuousMap

variable {n : ℕ} {alpha : Type*} [TopologicalSpace alpha]

/-- Merge a new factor into an optional factor without requiring a unit in `C₀`. -/
def mergeOptionalFactor (f : C₀(alpha, ℝ)) : Option C₀(alpha, ℝ) → Option C₀(alpha, ℝ)
  | none => some f
  | some g => some (f * g)

/-- Coordinate-indexed normalization of a factor list. `none` marks an inactive coordinate. -/
def normalizedCoordinateFactors (factors : List (Fin n × C₀(alpha, ℝ))) :
    Fin n → Option C₀(alpha, ℝ) :=
  factors.foldr (fun p accumulated ↦
    Function.update accumulated p.1 (mergeOptionalFactor p.2 (accumulated p.1)))
    (fun _ ↦ none)

/-- Scalar evaluation of an optional normalized factor; inactivity contributes scalar one. -/
def evalOptionalFactor (x : alpha) : Option C₀(alpha, ℝ) → ℝ
  | none => 1
  | some f => f x







/-- Active coordinates of a normalized coordinate product. -/
def activeCoordinates (factors : List (Fin n × C₀(alpha, ℝ))) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ (normalizedCoordinateFactors factors i).isSome

@[simp]
theorem mem_activeCoordinates_iff (factors : List (Fin n × C₀(alpha, ℝ)))
    (i : Fin n) :
    i ∈ activeCoordinates factors ↔ (normalizedCoordinateFactors factors i).isSome := by
  simp only [activeCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]






end MarkovProcess.PiContinuousMap


