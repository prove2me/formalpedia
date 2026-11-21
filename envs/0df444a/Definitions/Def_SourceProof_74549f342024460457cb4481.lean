-- Prove2me | Definitions.Def_SourceProof_74549f342024460457cb4481
-- name    : SourceProof_74549f342024460457cb4481
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:28:45.099865+00:00
-- url     : https://prove2.me/theorems/5bbedcaf-57a0-43e2-953d-23de730c5f80
-- title:
--   LevyStochCalc source module: SourceProof_74549f342024460457cb4481
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.wNorm_ne_top_of_energies` comes from the `LevyStochCalc.BSDEJ.PicardContractionNorm` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_869b93343dd8836d1387ab78

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponentially weighted norm of a triple

The exponentially weighted `L²` norm `wNorm` of a triple `(Y, Z, U)` over a horizon `[0, T]`
weights the squared value, the squared diffusion coordinates and the marked energy of the jump
integrand by `e^{βs}` and integrates them over the horizon and the sample space. Its integrand at
a sample point and a time is the pointwise energy density `density`; the norm is finite when the
value, the diffusion coordinates and the jump integrand have finite energy on the horizon, and it
is then the real integral over the horizon of the weighted sample energy density.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Norm

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {d : ℕ}

variable {P : Measure Ω} {ν : Measure E} {β T : ℝ}

variable [SigmaFinite ν]

omit [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_74549f342024460457cb4481 [SFinite P] (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hY : Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤)
    (hZ : ∀ j, Brownian.Ito.energy P T (fun ω s => Z s ω j) ≠ ⊤)
    (hU : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    wNorm P ν β T Y Z U ≠ ⊤ := by
  classical
  have hbound : LevyStochCalc.BSDEJ.Solves.wNorm P ν β T Y Z U
      ≤ ENNReal.ofReal (Real.exp (β * T)) * (LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Y s ω)
        + (∑ j, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω j))
        + LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)) := by
    rw [LevyStochCalc.BSDEJ.Solves.wNorm_eq_lintegral_density, ← _root_.Prove2MeSourceProof.h_869b93343dd8836d1387ab78 hYm hZm,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hs.2 hβ))) le_rfl
  refine ne_top_of_le_ne_top ?_ hbound
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hY,
      (ENNReal.sum_ne_top).2 fun j _ => hZ j⟩, hU⟩)
end Norm

end LevyStochCalc.BSDEJ.Solves


