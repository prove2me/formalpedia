-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F000
-- name    : LevyStochCalc_Ito_PicardStepMap_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:27:07.91607+00:00
-- url     : https://prove2.me/theorems/e8f93f4a-47ea-49ee-b3fc-3a1601939e41
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardStepMap
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardStepMap. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F001
import Definitions.Def_SourceProof_c06333d6fb82799a96874046

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard map for jump-diffusion SDEs

The vector-norm and `ω`-integrated forms of the drift Lipschitz estimate; the Bielecki
exponential-weight calculus `∫_0^t e^{2βs} ds = (e^{2βt} - 1) / (2β)` together with the
weighted-integral bound and the contraction-rate threshold it yields; the joint measurability of
the coefficients `σ` and `γ` composed with a process; and the Picard map `picardStep` itself, the
sum of the initial value, the drift integral, the Brownian component `picardStep_diffusion` and
the compensated-Poisson component `picardStep_jump`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Vector-norm L² Lipschitz bound on the drift step.**

Sum the per-component L² bound over `i : Fin n`:

  `∑ i, ((drift X - drift Y) i)² ≤ n · L_μ² · t · ∫_0^t ‖X-Y‖²`.

This is the squared-Euclidean-norm bound on the drift difference; the
factor `n` comes from summing the per-component bound. Together with
the `E[·]` step (next lemma) this gives the Bielecki-norm Lipschitz
constant for the drift step. -/
lemma picardStep_drift_diff_sum_sq_bound
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω)
    (h_X_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_int : MeasureTheory.IntegrableOn
      (fun s => ‖X s ω - Y s ω‖) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_sq_L2 : MeasureTheory.MemLp
      (fun s => ‖X s ω - Y s ω‖) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
      ≤ (n : ℝ) * L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by
  -- Per-component bound, summed over Fin n.
  have h_each : ∀ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ L_μ ^ 2 * t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := fun i =>
    _root_.Prove2MeSourceProof.h_c06333d6fb82799a96874046
      coeffs hL_μ_nn h_μ_lip X Y x₀ t ht ω i
      (h_X_int i) (h_Y_int i) h_XY_diff_int h_XY_diff_sq_L2
  -- Sum the bounds. Sum of n copies of B = n · B.
  calc (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
      ≤ ∑ _i : Fin n, L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => h_each i)
    _ = (n : ℝ) * (L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ = (n : ℝ) * L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by ring
/-! ## Map of the contraction argument

The Picard map `picardStep` and its three components are defined above,
together with the drift-component Lipschitz estimates. The rest of the
argument is:

1. `integral_sq_le_mul_integral_sq_on_Icc` (above) — the `L²`
   Cauchy–Schwarz bound `(∫_0^t f)² ≤ t · ∫_0^t f²` behind the
   Bielecki-norm contraction estimate.
2. `picardStep_diffusion_diff_lipschitz_sq_componentwise` — the Lipschitz
   bound of the Brownian component, via the `L²`-isometry of the integral
   difference (`itoIsometry_diff_brownian`) and the Lipschitz hypothesis on
   `σ`.
3. `picardStep_jump_diff_lipschitz_sq_componentwise` — the Lipschitz bound
   of the compensated-Poisson component, via `itoIsometry_diff_compensated`
   and the Lipschitz hypothesis on `γ`.
4. `picardStep_bielecki_contraction`, `picardStep_bielecki_contraction_tight`
   — the map is a Bielecki contraction once `β` is large relative to the
   Lipschitz constant; `bieleckiNorm_picardStep_diff_le`
   (`Ito/PicardOutput.lean`) is the form the well-posedness proof uses, and
   `bieleckiNorm_picardSelfMap_diff_le` (`Ito/PicardContraction.lean`) its
   transfer to the self-map of the process space.
5. `picardIter`, `picardLimit` (`Ito/PicardContraction.lean`, on
   `bieleckiLimit` of `Ito/PicardLimit.lean`) and
   `picardSelfMapRaw_isFixedPoint` — the iterates converge and the limit is
   a fixed point.
6. `exists_solvesOn`, `ae_eq_of_solvesOn` (`Ito/PicardWindow.lean`),
   `exists_globalSolution` (`Ito/PicardGlobal.lean`) and
   `exists_jumpDiffusion_unique_of_solvesOn` (`Ito/PicardWellPosed.lean`)
   — the fixed point solves the SDE on each window, is unique there, and
   the windows glue to a strong solution on `[0, ∞)`; `Ito/PicardFixedPoint.lean`
   restates the result as `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique`. -/

end LevyStochCalc.Ito.Picard


