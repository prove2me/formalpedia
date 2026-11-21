-- Prove2me | Definitions.Def_SourceProof_2885abf558bfdbae518a75a6
-- name    : SourceProof_2885abf558bfdbae518a75a6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:42:14.680057+00:00
-- url     : https://prove2.me/theorems/8ad8e585-0280-43dc-89c5-ab27125441a6
-- title:
--   LevyStochCalc source module: SourceProof_2885abf558bfdbae518a75a6
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.exists_solvesOn` comes from the `LevyStochCalc.Ito.PicardWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F002
import Definitions.Def_SourceProof_1f315702e69a962a8644d530
import Definitions.Def_SourceProof_34982f0b1ca1f7510c2d1e94
import Definitions.Def_SourceProof_d01b428b3bc2c410c5d79d5f
import Definitions.Def_SourceProof_eb8f90c564e2c0a8f493e6ac

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of the SDE on a window

`SolvesOn` records that a path map satisfies the jump-diffusion integral equation at every time
of `[0, T]`, in the `picardStep` form; the integrand hypotheses that make the two stochastic
integrals well-typed are bundled existentially, as in
`LevyStochCalc.Ito.Setting.JumpDiffusion.is_solution`, so that a solution can be re-read with any
proof of them. Two solutions on a common window and a common filtration agree, by the Bielecki
contraction.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### From an `S²` bound to the time-integrated energy -/

/-! ### Auxiliary Bielecki facts -/

/-! ### Solutions on a window -/

section Solves

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)

end Solves

/-! ### The canonical integrand hypotheses along a process with a finite `S²` norm -/

section Canonical

variable {ν : Measure E}
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}

end Canonical

/-! ### The window fixed point is a solution -/

section FixedPoint

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)


theorem _root_.Prove2MeSourceProof.h_2885abf558bfdbae518a75a6 [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ Y : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry Y)
        ∧ (∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
            Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T := by
  obtain ⟨β, hβ, hq⟩ := _root_.Prove2MeSourceProof.h_eb8f90c564e2c0a8f493e6ac (n := n) (d := d) (T := T) L hT
  set X₀ := LevyStochCalc.Ito.Picard.constantZeroProcess (n := n) P ℱ T with hX₀
  set Z := LevyStochCalc.Ito.Picard.picardLimit W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ with hZ
  have hZm := LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hZa := LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hZb := _root_.Prove2MeSourceProof.h_34982f0b1ca1f7510c2d1e94 W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  set Y := LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb with hY
  have hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ :=
    fun T' hT' => _root_.Prove2MeSourceProof.h_d01b428b3bc2c410c5d79d5f W N ℱ hℱW hℱN hℱ0 hnull coeffs
      hReg hLip x₀ hT hZm hZa hZb hT'
  refine ⟨Y.X, Y.measurable_path, Y.adapted, Y.cadlag_paths, hYS, ?_⟩
  refine LevyStochCalc.Ito.Picard.solvesOn_of_isFixedPoint W N ℱ hℱW hℱN coeffs hReg hLip x₀ hT.le
    Y.measurable_path Y.adapted Y.sup_L2 hYS ?_
  intro t ht
  exact _root_.Prove2MeSourceProof.h_1f315702e69a962a8644d530 W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hβ hT X₀
    hq ht
end FixedPoint

end LevyStochCalc.Ito.Picard


