-- Prove2me | Definitions.Def_LeanLevy_Representation_BochnerGaussian
-- name    : LeanLevy_Representation_BochnerGaussian
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-31T10:29:23.084303+00:00
-- url     : https://prove2.me/theorems/48c5a8be-a589-4648-9b18-19f1dd25fa40
-- title:
--   LeanLevy source module: Representation.BochnerGaussian
-- statement:
--   Pinned source definition and helper bundle. The original generated Lean module passed the earlier local build. The Bochner module import was replaced by its public theorem interface; the theorem proof is still open. This draft awaits Prove2Me remote compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Representation/BochnerGaussian.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_Fourier_PositiveDefinite


/-!
# Bochner–Gaussian: Covariance Matrix and Bochner Identity

This file provides two pieces of API connecting positive definite functions to the
Bochner theorem.

## Main definitions

* `ProbabilityTheory.covMatrix` — for times `t : Fin n → ℝ` and `ψ : ℝ → ℂ`, the
  covariance matrix `covMatrix ψ t i j = ψ (t i - t j)`.

## Main results

* `ProbabilityTheory.covMatrix_is_psd` — the covariance matrix of a positive definite
  function is positive semidefinite.
* `ProbabilityTheory.bochner_identity` — Bochner's theorem in explicit-integral form:
  every continuous positive definite `ψ` with `ψ 0 = 1` is the characteristic function
  of a probability measure on `ℝ`.
-/

open MeasureTheory Complex
open scoped ComplexOrder

namespace ProbabilityTheory

/-! ## Covariance matrix -/

/-- The covariance matrix for a finite set of times `t : Fin n → ℝ` given a function `ψ`:
`covMatrix ψ t i j = ψ (t i - t j)`. -/
noncomputable def covMatrix {n : ℕ} (ψ : ℝ → ℂ) (t : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ψ (t i - t j)





/-! ## Bochner Identity -/



end ProbabilityTheory


