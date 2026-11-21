-- Prove2me | Definitions.Def_SourceProof_48fc762eec2686f4f3c5681d
-- name    : SourceProof_48fc762eec2686f4f3c5681d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:30:36.47256+00:00
-- url     : https://prove2.me/theorems/2e31ca8b-9c5e-4b45-9ad2-0f6ca301bc5f
-- title:
--   LevyStochCalc source module: SourceProof_48fc762eec2686f4f3c5681d
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.ae_eq_of_solvesOn` comes from the `LevyStochCalc.Ito.PicardWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F004
import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F000
import Definitions.Def_SourceProof_1cfc3aa11ae6a425fc4b5453
import Definitions.Def_SourceProof_69f8ae19d7aa20df82811c65
import Definitions.Def_SourceProof_c94cbdb36d9b3fa8f9bc948b
import Definitions.Def_SourceProof_eb0e2237c948399f92e4f8c8
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


theorem _root_.Prove2MeSourceProof.h_48fc762eec2686f4f3c5681d
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {X Y : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X)) (hYm : Measurable (Function.uncurry Y))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hX : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T)
    (hY : SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n, X t ω i = Y t ω i := by
  obtain ⟨hσmX, hσpX, hσsX, hγmX, hγpX, hγsX, heqX⟩ := hX
  obtain ⟨hσmY, hσpY, hσsY, hγmY, hγpY, hγsY, heqY⟩ := hY
  obtain ⟨β, hβ, hq⟩ := _root_.Prove2MeSourceProof.h_eb8f90c564e2c0a8f493e6ac (n := n) (d := d) (T := T) L hT
  set q := (ENNReal.ofReal
      ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
        / (2 * β))) ^ ((1 : ℝ) / 2) with hqdef
  have hXe := _root_.Prove2MeSourceProof.h_1cfc3aa11ae6a425fc4b5453 hXS
  have hYe := _root_.Prove2MeSourceProof.h_1cfc3aa11ae6a425fc4b5453 hYS
  have hswapX : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω) :=
    hXm.comp (measurable_snd.prodMk measurable_fst)
  have hswapY : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Y s ω) :=
    hYm.comp (measurable_snd.prodMk measurable_fst)
  have hsubm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω - Y s ω) :=
    hswapX.sub hswapY
  have hnorm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖) :=
    hsubm.norm
  have hcontr := _root_.Prove2MeSourceProof.h_c94cbdb36d9b3fa8f9bc948b W N ℱ hℱW hℱN coeffs hLip X Y x₀
    hσmX hσpX hσsX hγmX hγpX hγsX hσmY hσpY hσsY hγmY hγpY hγsY
    (fun i => LevyStochCalc.Ito.Picard.measurable_mu_comp_state coeffs hReg hXm i)
    (fun i => LevyStochCalc.Ito.Picard.measurable_mu_comp_state coeffs hReg hYm i)
    hnorm
    (fun i b _ => _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a coeffs hReg hLip hXe i (by assumption))
    (fun i b _ => _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a coeffs hReg hLip hYe i (by assumption))
    (fun b _ => _root_.Prove2MeSourceProof.h_69f8ae19d7aa20df82811c65 hXm hYm hXe hYe b)
    hsubm hβ hT
  have hcongr : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i)
      = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
          LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs X x₀ hσmX hσpX hσsX hγmX hγpX hγsX t ω i
            - LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs Y x₀ hσmY hσpY hσsY hγmY hγpY hγsY t ω i) := by
    refine LevyStochCalc.Ito.Picard.bieleckiNorm_congr_ae_on β T fun t ht => ?_
    filter_upwards [heqX t ht, heqY t ht] with ω hωX hωY
    funext i
    rw [hωX i, hωY i]
  have hfin : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) ≠ ⊤ :=
    (LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top_of_lt_top hβ.le T hXm hYm
      (LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_supL2 hT hXS) (LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_supL2 hT hYS)).ne
  have hle : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i)
      ≤ q * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) := by
    rw [hqdef]
    conv_lhs => rw [hcongr]
    exact hcontr
  have hzero : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) = 0 :=
    LevyStochCalc.Ito.Picard.eq_zero_of_le_mul_self hfin hq hle
  intro t ht
  have hsl : ∀ (u : ℝ) (i : Fin n), Measurable fun ω => X u ω i - Y u ω i := by
    intro u i
    exact ((measurable_pi_apply i).comp (Measurable.of_uncurry_left hXm)).sub
      ((measurable_pi_apply i).comp (Measurable.of_uncurry_left hYm))
  filter_upwards [_root_.Prove2MeSourceProof.h_eb0e2237c948399f92e4f8c8 hsl hzero ht] with ω hω
  intro i
  exact sub_eq_zero.mp (hω i)
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

end FixedPoint

end LevyStochCalc.Ito.Picard


