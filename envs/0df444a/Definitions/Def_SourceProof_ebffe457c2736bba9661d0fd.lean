-- Prove2me | Definitions.Def_SourceProof_ebffe457c2736bba9661d0fd
-- name    : SourceProof_ebffe457c2736bba9661d0fd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:44:56.769175+00:00
-- url     : https://prove2.me/theorems/d6ecee8a-3e48-4c26-95d4-71a3c302efc2
-- title:
--   LevyStochCalc source module: SourceProof_ebffe457c2736bba9661d0fd
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.integral_mul_increment_eq_zero` comes from the `LevyStochCalc.Poisson.PerpBridge` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The perp bridge for the compensated integral

A weight measurable before a horizon does not see the compensated integral beyond it: the
increment is a martingale increment, and conditioning on the horizon kills it. So orthogonality
to every admissible integrand over `[0, T]` extends to every admissible integrand over any
larger horizon. This is the marked counterpart of the Brownian perp bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Congr

end Congr

section Clip

namespace MarkedHorizonIntegrand

end MarkedHorizonIntegrand

end Clip

section Bridge


theorem _root_.Prove2MeSourceProof.h_ebffe457c2736bba9661d0fd (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {z : Ω → ℝ} (hz2 : MemLp z 2 P) {T t : ℝ}
    (hzm : AEStronglyMeasurable[ℱ T] z P) (hTt : T ≤ t) :
    ∫ ω, z ω * (stochasticIntegral N ℱ hℱ φ hm hp hq t ω
      - stochasticIntegral N ℱ hℱ φ hm hp hq T ω) ∂P = 0 := by
  haveI : SigmaFinite (P.trim (ℱ.rightCont.le T)) := by infer_instance
  set M := LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq with hMdef
  have hmart : MeasureTheory.Martingale M ℱ.rightCont P :=
    LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral_rightCont N ℱ hℱ φ hm hp hq
  have hMLp : ∀ u : ℝ, MemLp (M u) 2 P := fun u => LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ φ hm hp hq u
  have hMint : ∀ u : ℝ, Integrable (M u) P := fun u => (hMLp u).integrable (by norm_num)
  have hgLp : MemLp (fun ω => M t ω - M T ω) 2 P := (hMLp t).sub (hMLp T)
  have hgint : Integrable (fun ω => M t ω - M T ω) P := (hMint t).sub (hMint T)
  have hzm' : AEStronglyMeasurable[ℱ.rightCont T] z P := hzm.mono (ℱ.le_rightCont T)
  have hprod : Integrable (fun ω => z ω * (M t ω - M T ω)) P :=
    LevyStochCalc.Poisson.Compensated.integrable_mul_of_memLp_two hz2 hgLp
  have hpull := condExp_mul_of_aestronglyMeasurable_left (m := ℱ.rightCont T)
    (f := z) (g := fun ω => M t ω - M T ω) hzm' hprod hgint
  have hcond : P[(fun ω => M t ω - M T ω) | ℱ.rightCont T] =ᵐ[P] 0 := by
    have h1 : P[(fun ω => M t ω - M T ω) | ℱ.rightCont T]
        =ᵐ[P] P[M t | ℱ.rightCont T] - P[M T | ℱ.rightCont T] :=
      condExp_sub (hMint t) (hMint T) _
    have h2 : P[M t | ℱ.rightCont T] =ᵐ[P] M T := hmart.2 T t hTt
    have h3 : P[M T | ℱ.rightCont T] = M T :=
      condExp_of_stronglyMeasurable (ℱ.rightCont.le T) (hmart.1 T) (hMint T)
    rw [h3] at h1
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, Pi.sub_apply, e2, sub_self]
    rfl
  have key : ∫ ω, z ω * (M t ω - M T ω) ∂P
      = ∫ ω, (P[(fun ω => z ω * (M t ω - M T ω)) | ℱ.rightCont T]) ω ∂P :=
    (integral_condExp (ℱ.rightCont.le T)).symm
  have hpull' : P[(fun ω => z ω * (M t ω - M T ω)) | ℱ.rightCont T]
      =ᵐ[P] z * P[(fun ω => M t ω - M T ω) | ℱ.rightCont T] := hpull
  rw [key]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hpull', hcond] with ω e1 e2
  rw [e1, Pi.mul_apply, e2, Pi.zero_apply, mul_zero]
end Bridge

end LevyStochCalc.Poisson.Compensated


