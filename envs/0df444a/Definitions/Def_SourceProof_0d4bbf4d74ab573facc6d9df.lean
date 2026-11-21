-- Prove2me | Definitions.Def_SourceProof_0d4bbf4d74ab573facc6d9df
-- name    : SourceProof_0d4bbf4d74ab573facc6d9df
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:15:24.770471+00:00
-- url     : https://prove2.me/theorems/a11a3388-a439-4d9b-959f-fa6c00b7debd
-- title:
--   LevyStochCalc source module: SourceProof_0d4bbf4d74ab573facc6d9df
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.PicardOutput.isItoLevyProcess_clampT` comes from the `LevyStochCalc.BSDEJ.PicardItoLevy` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardItoLevy_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy decomposition of a Picard output

The output `Y` of a Picard step satisfies the backward equation on the horizon `[0, T]` only.
Frozen at the horizon, `t ↦ Y (min t T)`, it carries an Itô–Lévy decomposition at every
nonnegative time, with drift `-b` for a drift `b` that is almost everywhere the generator along
the input triple, diffusion vector `Z` and jump integrand `U`: subtracting the backward equation
at `t` from the backward equation at `0` turns the remaining window `[t, T]` of the drift
integral into the initial window `[0, t]`, and past the horizon neither the drift integral nor
either stochastic leg moves.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.clampT` — a process frozen at the horizon.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.clampT_decomposition_of_eqn` — the decomposition of a frozen path
  satisfying the backward equation, for abstract stochastic legs.
* `LevyStochCalc.BSDEJ.Solves.PicardOutput.isItoLevyProcess_clampT` — the frozen Picard output
  is an Itô–Lévy process.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Freezing a process at the horizon -/

/-! ### The drift integral past the horizon -/

/-! ### The decomposition of a frozen backward path -/

/-! ### The frozen Picard output -/


theorem _root_.Prove2MeSourceProof.h_0d4bbf4d74ab573facc6d9df
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y' : ℝ → Ω → ℝ}
    {Z' : ℝ → Ω → (Fin d → ℝ)} {U' : ℝ → Ω → E → ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (h : PicardOutput D f ξ T Y' Z' U' Y Z U) (hT : 0 < T)
    {b : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry b))
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hb : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b p.1 p.2 = f p.2 (Y' p.2 p.1) (Z' p.2 p.1) (U' p.2 p.1)) :
    LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N (augJoint D)
      D.isBrownianFiltration_aug D.isPoissonFiltration_aug (clampT T Y) (Y 0)
      (fun s ω => -b ω s) Z (fun ω s e => U s ω e) where
  measurable_path := LevyStochCalc.BSDEJ.Solves.measurable_uncurry_clampT h.Y_meas
  σ_meas := h.Z_meas
  σ_prog := h.Z_prog
  σ_sq := LevyStochCalc.BSDEJ.Solves.sq_int_global_of_vanishing h.Z_vanish h.Z_sq
  γ_meas := h.U_meas
  γ_prog := h.U_prog
  γ_sq := LevyStochCalc.BSDEJ.Solves.marked_sq_int_global_of_vanishing h.U_vanish h.U_sq
  decomposition := by
    refine LevyStochCalc.BSDEJ.Solves.clampT_decomposition_of_eqn (ξ := ξ) hT hbm hbq hbz ?_ ?_ ?_ ?_ ?_
    · intro t ht
      have hbf : ∀ᵐ ω ∂P, ∫ s in Set.Icc t T, b ω s
          = ∫ s in Set.Icc t T, f s (Y' s ω) (Z' s ω) (U' s ω) := by
        filter_upwards [Measure.ae_ae_of_ae_prod hb] with ω hω
        exact integral_congr_ae
          (ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc ht.1 le_rfl) hω)
      filter_upwards [h.eqn t ht, hbf] with ω h1 h2
      rw [h2]
      exact h1
    · exact LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W
        (LevyStochCalc.BSDEJ.Solves.augJoint D) D.isBrownianFiltration_aug Z h.Z_meas h.Z_prog
        (LevyStochCalc.BSDEJ.Solves.sq_int_global_of_vanishing h.Z_vanish h.Z_sq) le_rfl
    · exact LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos
        (φ := fun ω s e => U s ω e) D.N D.isPoissonFiltration_aug h.U_meas h.U_prog
        (LevyStochCalc.BSDEJ.Solves.marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) le_rfl
    · exact fun t hTt =>
        LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_eq_of_vanish D.W
          (LevyStochCalc.BSDEJ.Solves.augJoint D) D.isBrownianFiltration_aug h.Z_meas h.Z_prog
          (LevyStochCalc.BSDEJ.Solves.sq_int_global_of_vanishing h.Z_vanish h.Z_sq) hT hTt h.Z_vanish
    · exact fun t hTt =>
        LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_of_vanish (φ := fun ω s e => U s ω e) D.N
          D.isPoissonFiltration_aug h.U_meas h.U_prog
          (LevyStochCalc.BSDEJ.Solves.marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) hT hTt h.U_vanish
end LevyStochCalc.BSDEJ.Solves


