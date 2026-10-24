-- Prove2me | Definitions.Def_PiExponent_FiniteMinorComparison
-- name    : PiExponent_FiniteMinorComparison
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-24T03:56:36.492979+00:00
-- url     : https://prove2.me/theorems/e4a5588c-a300-4d6d-8a22-663c2a364988
-- title:
--   Finite minor error allowances and collision rates
-- statement:
--   Reuse the existing finite interpolation matrix definitions and add explicit arithmetic and analytic allowances whose sum is the target budget E, together with the collision rate and its proposed volume limit.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup
import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily

open scoped BigOperators

/-- Arithmetic allowance using the target's LCM constant, not the coarser
constant in AdmissibleParameters. -/
noncomputable def OAI.PiExponent.FiniteMinorComparison.arithmeticError
    (m : ℕ) (v0 theta F wmin : ℝ) : ℝ :=
  (4 * Real.log 2) * F * (m : ℝ) / v0 +
    ((4 * Real.log 2) * (m : ℝ) + theta) / wmin

/-- Translation and holomorphic allowances, before adding any height remainder. -/
noncomputable def OAI.PiExponent.FiniteMinorComparison.analyticError
    (K : ℕ) (nu F v0 w0 wmin : ℝ) : ℝ :=
  nu / F + 2 * Real.log 2 / v0 + 100 * (K : ℝ) / w0 +
    (Real.log 4 + Real.log (2 * (K : ℝ)) + nu +
      Real.log (200 * (K : ℝ))) / wmin

/-- Collision rate for arbitrary finite denominators; no infinite approximation
sequence or special dimension identities are included in this definition. -/
noncomputable def OAI.PiExponent.FiniteMinorComparison.collisionRate
    {m : ℕ} (K : ℕ) (v0 theta A eta : ℝ) (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  (Real.log 2 / 4) * eta ^ 2 *
    (Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 theta
      (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) /
    (H * ((OAI.PiExponent.realWeightedSimplex
      (OAI.PiExponent.MatrixArithmetic.logWeights q) (A * H)).card : ℝ))

noncomputable def OAI.PiExponent.FiniteMinorComparison.collisionLimit
    (m K : ℕ) (v0 theta A eta : ℝ) : ℝ :=
  (Real.log 2 / 4) *
    (eta ^ 2 * (K : ℝ) * theta ^ m /
      (((m : ℝ) + 1) * v0 * A ^ m))


