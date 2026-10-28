-- Prove2me | Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
-- name    : MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T11:56:29.999727+00:00
-- url     : https://prove2.me/theorems/fbe26d83-efc9-4383-93ed-a84f8d9a913d
-- title:
--   MarkovProcess definitions: FiniteTime.FiniteProductCoordinateNormalForm
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.FiniteTime.FiniteProductCoordinateNormalForm`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/FiniteProductCoordinateNormalForm.lean#L1-L163

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-!
# Explicit coordinate-product normal forms

This file replaces abstract membership in the coordinate `C₀` algebra by a concrete finite
sum of finite products.  Factors are stored in lists, so the normal form can subsequently be
consumed by recursion (for example, by iterated kernel integration).  The empty factor list is
the constant function `1`; in particular the representation treats constants and an empty
coordinate type without exceptional cases.
-/

open scoped CompactlySupported ZeroAtInfty

namespace MarkovProcess.PiContinuousMap

variable {I α : Type*} [TopologicalSpace α]

/-- A scalar coefficient together with a finite ordered list of one-coordinate `C₀` factors. -/
structure CoordinateProductTerm (I α : Type*) [TopologicalSpace α] where
  coefficient : ℝ
  factors : List (I × C₀(α, ℝ))

/-- The continuous function represented by one coordinate-product term. -/
def CoordinateProductTerm.toContinuousMap (t : CoordinateProductTerm I α) : C(I → α, ℝ) :=
  t.coefficient • (t.factors.map (fun p ↦ coordinate p.1 (p.2 : C(α, ℝ)))).prod



/-- Evaluate a finite list of coordinate-product terms by summing its terms. -/
def coordinatePolynomial (terms : List (CoordinateProductTerm I α)) : C(I → α, ℝ) :=
  (terms.map CoordinateProductTerm.toContinuousMap).sum









/-- Multiply two terms by multiplying coefficients and concatenating their factor lists. -/
def CoordinateProductTerm.mul (s t : CoordinateProductTerm I α) :
    CoordinateProductTerm I α :=
  ⟨s.coefficient * t.coefficient, s.factors ++ t.factors⟩





/-- Distributive product of two finite coordinate polynomials. -/
def coordinatePolynomialMul (left right : List (CoordinateProductTerm I α)) :
    List (CoordinateProductTerm I α) :=
  left.flatMap fun s ↦ right.map s.mul







end MarkovProcess.PiContinuousMap


