-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardWindow_F001
-- name    : LevyStochCalc_Ito_PicardWindow_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:33:48.360885+00:00
-- url     : https://prove2.me/theorems/c8d7e1b9-ed17-4511-af53-3b1fbb2c4d45
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardWindow
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardWindow. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F002
import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F000
import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F001
import Definitions.Def_SourceProof_1cfc3aa11ae6a425fc4b5453
import Definitions.Def_SourceProof_ac85444679aa3a412d1927d4
import Definitions.Def_SourceProof_bdaa282fd363a3be48f8fdce

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

omit [IsProbabilityMeasure P] in
/-- Progressive measurability of the diffusion integrand along a progressively measurable
state process. -/
theorem progressivelyMeasurable_sigma_comp_state
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (i : Fin n) (j : Fin d) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X s ω) i j := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.σ s x i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hReg.2.1)
  exact progressivelyMeasurable_comp_state hXa h
omit [IsProbabilityMeasure P] in
/-- Marked progressive measurability of the jump integrand along a progressively measurable
state process. -/
theorem markedProgressivelyMeasurable_gamma_comp_state
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (i : Fin n) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X s ω) e i := by
  have h : Measurable fun p : ℝ × (Fin n → ℝ) × E => coeffs.γ p.1 p.2.1 p.2.2 i :=
    (measurable_pi_apply i).comp hReg.2.2.1
  exact _root_.Prove2MeSourceProof.h_ac85444679aa3a412d1927d4
    (g := fun (s : ℝ) (x : Fin n → ℝ) (e : E) => coeffs.γ s x e i) hXa h
/-- The `L²` bound on the diffusion integrand along a process with a finite `S²` norm. -/
theorem lintegral_sq_sigma_lt_top_of_supL2
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (i : Fin n) (j : Fin d) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip hXm
    (_root_.Prove2MeSourceProof.h_1cfc3aa11ae6a425fc4b5453 hXS) i j hT'
/-- The `L²` bound on the jump integrand along a process with a finite `S²` norm. -/
theorem lintegral_sq_gamma_lt_top_of_supL2 [SigmaFinite ν]
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (i : Fin n) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip hXm
    (_root_.Prove2MeSourceProof.h_1cfc3aa11ae6a425fc4b5453 hXS) i hT'
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

end FixedPoint

end LevyStochCalc.Ito.Picard


