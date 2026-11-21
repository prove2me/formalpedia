-- Prove2me | Definitions.Def_SourceProof_21680fbb00c3cbdc68b476b2
-- name    : SourceProof_21680fbb00c3cbdc68b476b2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:36:33.572481+00:00
-- url     : https://prove2.me/theorems/59e6a04e-ae3f-44c4-9c04-c60bc5acf7fe
-- title:
--   LevyStochCalc source module: SourceProof_21680fbb00c3cbdc68b476b2
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_mul_increment_eq_zero` comes from the `LevyStochCalc.Brownian.PRPPerpBridge` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPPerpBridge_F000
import Definitions.Def_SourceProof_08c64b3622d7f10f8c921d88

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From horizon orthogonality to orthogonality against every Itô integral

A weight orthogonal to the Itô integrals of integrands supported in `[0, T]` is orthogonal to
`∫_0^t K dW` for every admissible `K` and every `t > 0`. For `t ≤ T` this is because `K` clipped
to `(0, t]` is such an integrand and its integral over the horizon is `∫_0^t K dW`; for `t > T`
the remaining increment is a martingale increment after `T`, which a weight measurable before `T`
does not see.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_21680fbb00c3cbdc68b476b2 (V : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration V ℱ) (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {z : Ω → ℝ} (hz2 : MemLp z 2 P) {T t : ℝ}
    (hzm : AEStronglyMeasurable[ℱ T] z P) (hTt : T ≤ t) :
    ∫ ω, z ω * (stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω
      - stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω) ∂P = 0 := by
  haveI : SigmaFinite (P.trim (ℱ.rightCont.le T)) := by infer_instance
  set M := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq with hMdef
  have hmart : MeasureTheory.Martingale M ℱ.rightCont P :=
    _root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 V ℱ hℱ K hm hp hq
  have hMLp : ∀ u : ℝ, MemLp (M u) 2 P := fun u =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp V ℱ hℱ K hm hp hq u
  have hMint : ∀ u : ℝ, Integrable (M u) P := fun u => (hMLp u).integrable (by norm_num)
  have hgLp : MemLp (fun ω => M t ω - M T ω) 2 P := (hMLp t).sub (hMLp T)
  have hgint : Integrable (fun ω => M t ω - M T ω) P := (hMint t).sub (hMint T)
  have hzm' : AEStronglyMeasurable[ℱ.rightCont T] z P := hzm.mono (ℱ.le_rightCont T)
  have hprod : Integrable (fun ω => z ω * (M t ω - M T ω)) P :=
    LevyStochCalc.Brownian.Ito.integrable_mul_of_memLp_two hz2 hgLp
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
end LevyStochCalc.Brownian.Ito


