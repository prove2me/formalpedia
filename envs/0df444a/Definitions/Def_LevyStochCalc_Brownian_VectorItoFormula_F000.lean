-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoFormula_F000
-- name    : LevyStochCalc_Brownian_VectorItoFormula_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:31.283959+00:00
-- url     : https://prove2.me/theorems/8140f648-3ef8-4764-a721-36a644bac561
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoFormula
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoFormula. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F001
import Definitions.Def_LevyStochCalc_Brownian_VectorItoFormulaDecomp_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoQuadVarRiemannDecomposition_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a vector Itô process on a uniform grid

The grid decomposition leaves four errors: the second-order Taylor remainder, one drift Riemann
sum per state index, one martingale Riemann sum per state-and-Brownian index pair, and one
weighted quadratic variation per pair of state indices. Under an affine oscillation bound
`A + K‖z − w‖` on the second derivative each is bounded by a function of the mesh whose limit is
proportional to `A`; a uniformly continuous second derivative supplies such a bound for every
`A > 0`, so the `L¹` defect of Itô's formula vanishes.

## Main statements

* `LevyStochCalc.Brownian.Ito.vectorItoGridError` — the mesh-error function.
* `LevyStochCalc.Brownian.Ito.tendsto_vectorItoGridError` — it vanishes as the mesh does.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_vectorItoFormula_le` — the `L¹`
  defect of Itô's formula on every uniform grid.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula` — Itô's formula in the vector case.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

/-- The residue of the uniform-grid error that the oscillation scale `A` of the second derivative
leaves behind as the mesh vanishes, per unit of `A`. -/
noncomputable def vectorItoGridResidue (nR dR C T : ℝ) : ℝ :=
  nR * (2 * (dR ^ 2 * (C ^ 2 * T))) + 1 / 2 * (nR ^ 2 * (dR * C ^ 2 * T))
theorem vectorItoGridResidue_nonneg {nR dR C T : ℝ} (hnR : 0 ≤ nR) (hdR : 0 ≤ dR)
    (hT : 0 ≤ T) : 0 ≤ vectorItoGridResidue nR dR C T := by
  unfold vectorItoGridResidue
  positivity
/-- The `L¹` error of the uniform-grid approximation in Itô's formula for a vector Itô process,
as a function of the mesh. The four summands are the Taylor remainder, the drift Riemann sums,
the martingale Riemann sums and the weighted quadratic variations; `A` and `K` are the two
constants of the affine oscillation bound `A + K‖z − w‖` on the second derivative. -/
noncomputable def vectorItoGridError (nR dR B C T A K K₂ : ℝ) (x : ℝ) : ℝ :=
  (A * (nR * (2 * (B ^ 2 * (T * x)) + 2 * (dR ^ 2 * (C ^ 2 * T))))
      + K * (nR ^ 2 * (nR * (4 * (B ^ 3 * T * x ^ 2
        + dR ^ 2 * (dR * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt x))))))))
    + nR * (K₂ * B * (T * (nR * (B * x + dR * (C * Real.sqrt x)))))
    + nR * dR * Real.sqrt (C ^ 2 * (K₂ ^ 2
        * (T * (nR * (2 * (B * x) ^ 2 + 2 * (dR ^ 2 * (C ^ 2 * x)))))))
    + 1 / 2 * (nR ^ 2 * (K₂ * B ^ 2 * T * x
        + 2 * (K₂ * B * dR * C * T * Real.sqrt x)
        + dR * Real.sqrt (K₂ ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (T * x))
        + dR ^ 2 * Real.sqrt (K₂ ^ 2 * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
            * (T * x))
        + (A * (dR * C ^ 2) * T
          + K * (dR * C ^ 2) * (T * (nR * (B * x + dR * (C * Real.sqrt x)))))))
@[simp] theorem vectorItoGridError_zero (nR dR B C T A K K₂ : ℝ) :
    vectorItoGridError nR dR B C T A K K₂ 0 = A * vectorItoGridResidue nR dR C T := by
  simp only [vectorItoGridError, vectorItoGridResidue]
  norm_num
  ring
theorem continuous_vectorItoGridError (nR dR B C T A K K₂ : ℝ) :
    Continuous (vectorItoGridError nR dR B C T A K K₂) := by
  unfold vectorItoGridError
  fun_prop
theorem tendsto_vectorItoGridError (nR dR B C T A K K₂ : ℝ) :
    Filter.Tendsto (fun m : ℕ => vectorItoGridError nR dR B C T A K K₂ (T / (m : ℝ)))
      Filter.atTop (𝓝 (A * vectorItoGridResidue nR dR C T)) := by
  have hx : Filter.Tendsto (fun m : ℕ => T / (m : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hcomp := ((continuous_vectorItoGridError nR dR B C T A K K₂).tendsto 0).comp hx
  rwa [vectorItoGridError_zero] at hcomp
section Formula

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

end Formula

end LevyStochCalc.Brownian.Ito


