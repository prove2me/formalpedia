-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
-- name    : OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:56:50.906776+00:00
-- url     : https://prove2.me/theorems/03bc0316-3599-4c4d-97a8-3fce8ad984af
-- title:
--   Fixed-data interfaces for the determinant contradiction
-- statement:
--   For a real approximation exponent $\nu$, let fixed data be admissible parameters with the source arithmetic constant and collision constant $c=\log(2)/4$. Write $M(H)$ for the row count, $N(H)$ for the low-index count, and $b(H)$ for the normalized weighted row mean. Define the associated matrix, selected minor, and
--
--   $$\gamma(H)=\frac{c\eta^2M(H)}{H N(H)},\qquad \gamma_\infty=\frac{c\eta^2K\theta^m}{(m+1)v_0A^m}.$$
--
--   The global interpolation hypothesis asserts that, for every $\nu>2$, every fixed datum and every real lower height, some larger height has a surjective matrix linear map. The analytic aggregate hypothesis asserts that every such datum admits an error tending to zero whose eventual determinant bound is the exact source analytic-and-collision estimate. These are the original quantified interfaces for the conditional determinant contradiction.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_AdmissibleParameters
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CollisionConstant
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Parameters
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

namespace OAI.PiExponent.DeterminantContradiction

open Filter
open scoped Topology

abbrev FixedData (nu : ℝ) := AdmissibleParameters nu Arithmetic.lcmConstant collisionConstant

noncomputable def finiteNumerators {nu : ℝ} (d : FixedData nu) : Fin d.m → ℤ :=
  fun i => d.p i.val

noncomputable def finiteDenominators {nu : ℝ} (d : FixedData nu) : Fin d.m → ℕ :=
  fun i => d.q i.val

abbrev Row {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  InterpolationMatrix.Row d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H

abbrev Column {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  InterpolationMatrix.Column d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H

noncomputable def actualMatrix {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Matrix (Row d H) (Column d H) ℂ :=
  InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)

noncomputable def actualMinor {nu : ℝ} (d : FixedData nu) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  MatrixArithmetic.selectedMinor d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d) selection

noncomputable def actualMean {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  MatrixArithmetic.meanRowWeight d.K d.v0 d.base.theta (finiteDenominators d) H

noncomputable def actualRowCount {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℕ :=
  Fintype.card (Row d H)

noncomputable def lowIndexCount {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℕ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
    ((d.base.A : ℝ) * H)).card

noncomputable def collisionRate {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  collisionConstant * d.base.eta ^ 2 * (actualRowCount d H : ℝ) /
    (H * (lowIndexCount d H : ℝ))

noncomputable def collisionLimit {nu : ℝ} (d : FixedData nu) : ℝ :=
  collisionConstant *
    (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m))

def GlobalInterpolationStatement : Prop :=
  ∀ nu : ℝ, 2 < nu → ∀ d : FixedData nu,
    ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧ Function.Surjective (actualMatrix d H).mulVecLin

def AnalyticAggregateStatement : Prop :=
  ∀ nu : ℝ, 2 < nu → ∀ d : FixedData nu,
    ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : ℝ in atTop, ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
        Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
          d.analyticError + error H +
            max (-collisionRate d H)
              (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H))

end OAI.PiExponent.DeterminantContradiction


