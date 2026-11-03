-- Prove2me | Definitions.Def_Bochner_PositiveDefiniteSupport
-- name    : Bochner_PositiveDefiniteSupport
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-31T10:04:30.887131+00:00
-- url     : https://prove2.me/theorems/9dfb2bdf-58f5-4583-8b46-910d59d6f2ca
-- title:
--   Bochner support: positive-definite functions
-- statement:
--   A function f : ℝ → ℂ is positive definite when, for every finite family of real points x and complex weights c, the quadratic form ∑ᵢ ∑ⱼ conj(cᵢ) cⱼ f(xᵢ − xⱼ) is a nonnegative real number.
-- source:
--   Shmuel Link, LeanLevy: Lévy Processes in Lean 4 (2026), MIT, https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/PositiveDefinite.lean#L31-L43 (definition of ProbabilityTheory.IsPositiveDefinite). Adapted only by namespace to match the existing Bochner theorem interface.

import Mathlib.Analysis.Matrix.PosDef

open scoped ComplexOrder

/-- A function on ℝ is positive definite when every finite Hermitian quadratic form is nonnegative. -/
def Bochner_PositiveDefiniteSupport (f : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * f (x i - x j)


