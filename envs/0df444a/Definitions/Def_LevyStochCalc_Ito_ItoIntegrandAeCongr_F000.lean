-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoIntegrandAeCongr_F000
-- name    : LevyStochCalc_Ito_ItoIntegrandAeCongr_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:13:23.467822+00:00
-- url     : https://prove2.me/theorems/1a83cb27-6d32-417f-b4ad-d9995e37eb7a
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoIntegrandAeCongr
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoIntegrandAeCongr. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
import Definitions.Def_SourceProof_c2510fef121a9f6103ef8e5e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Almost-everywhere dependence of the Itô integral on its integrand

Two integrands that agree for `P ⊗ ds`-almost every sample point and time of a window have the
same Itô integral at the end of that window: the `L²`-isometry for the difference of two Itô
integrals turns the vanishing of the energy of the difference of the integrands into the almost
sure vanishing of the difference of the integrals. Agreement off a countable set of times for
each sample point is a special case, because a countable set of reals is Lebesgue null. It is the
case met by a path translated by a vector that tracks a second path only strictly between two
stopping times: the increments of the two cut-off integrands can part at the later of the two
times and nowhere else.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_countable` — integrands
  agreeing off a countable set of times at each sample point have the same Itô integral at the
  end of the window (the almost-everywhere form is `stochasticIntegralBrownian_congr_ae` of
  `Brownian/ItoLocalityStrict.lean`).
* `LevyStochCalc.Brownian.Ito.stopped_sub_congr_of_lt` — the increment of a cut-off integrand
  between two times depends on the integrand only at the times strictly between them, away from
  the later time.
* `LevyStochCalc.Brownian.Ito.integral_stopped_sub_shift_of_lt` — the Lebesgue integral of the
  increment of the cut-off integrand of a translated path agreeing with a second path strictly
  between the two times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_shift_congr_of_lt` — the
  corresponding identity for the Itô integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section CountableTimes

/-- The times carried to a given value of `WithTop ℝ` form a countable set. -/
theorem countable_setOf_coe_eq (c : WithTop ℝ) :
    {s : ℝ | ((s : ℝ) : WithTop ℝ) = c}.Countable := by
  refine Set.Subsingleton.countable ?_
  intro a ha b hb
  have h : ((a : ℝ) : WithTop ℝ) = ((b : ℝ) : WithTop ℝ) := ha.trans hb.symm
  exact_mod_cast h
/-- Almost every time is carried to a value of `WithTop ℝ` other than a given one. -/
theorem ae_coe_ne (c : WithTop ℝ) : ∀ᵐ s : ℝ ∂volume, ((s : ℝ) : WithTop ℝ) ≠ c := by
  have h : {s : ℝ | ¬ ((s : ℝ) : WithTop ℝ) ≠ c} = {s : ℝ | ((s : ℝ) : WithTop ℝ) = c} := by
    ext s
    simp
  rw [MeasureTheory.ae_iff, h]
  exact (countable_setOf_coe_eq c).measure_zero volume
end CountableTimes

section AeCongr

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **Two integrands agreeing off a countable set of times at each sample point have the same Itô
integral.** -/
theorem stochasticIntegralBrownian_congr_of_countable
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {D : Ω → Set ℝ} (hD : ∀ ω, (D ω).Countable)
    (hagree : ∀ (ω : Ω) (s : ℝ), s ∉ D ω → H₁ ω s = H₂ ω s)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T := by
  refine _root_.Prove2MeSourceProof.h_c2510fef121a9f6103ef8e5e W ℱ hℱ hm₁ hp₁ hq₁ hm₂ hp₂ hq₂ hT ?_
  refine Filter.Eventually.of_forall fun ω => MeasureTheory.ae_restrict_of_ae ?_
  have hsub : {s : ℝ | ¬ H₁ ω s = H₂ ω s} ⊆ D ω := by
    intro s hs
    by_contra hsD
    exact hs (hagree ω s hsD)
  rw [MeasureTheory.ae_iff]
  exact MeasureTheory.measure_mono_null hsub ((hD ω).measure_zero volume)
end AeCongr

section StoppedSupport

variable {Ω : Type*}

/-- The increment of a cut-off integrand between two times depends on the integrand only at the
times strictly between them, away from the later of the two. -/
theorem stopped_sub_congr_of_lt {K L : Ω → ℝ → ℝ} {τ₀ τ₁ : Ω → WithTop ℝ} {ω : Ω}
    (hmono : τ₀ ω ≤ τ₁ ω)
    (hagree : ∀ s : ℝ, τ₀ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) < τ₁ ω →
      K ω s = L ω s)
    {s : ℝ} (hs : ((s : ℝ) : WithTop ℝ) ≠ τ₁ ω) :
    Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s
      = Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s := by
  by_cases h₀ : ((s : ℝ) : WithTop ℝ) ≤ τ₀ ω
  · have h₁ : ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω := h₀.trans hmono
    simp [Probability.stopped, h₀, h₁]
  · have hlt : τ₀ ω < ((s : ℝ) : WithTop ℝ) := not_le.mp h₀
    by_cases h₁ : ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω
    · simp [Probability.stopped, h₀, h₁, hagree s hlt (lt_of_le_of_ne h₁ hs)]
    · simp [Probability.stopped, h₀, h₁]
/-- Strictly between two times on which a translated path agrees with a second path, and away
from the later of the two, the increment of the cut-off integrand built from the translated path
is the increment of the one built from the second path. -/
theorem stopped_sub_shift_apply_of_lt {n : ℕ} {τ₀ τ₁ : Ω → WithTop ℝ} {ω : Ω}
    (hmono : τ₀ ω ≤ τ₁ ω) (Φ : (Fin n → ℝ) → ℝ) (g : Ω → ℝ → ℝ)
    {V X : ℝ → Ω → Fin n → ℝ} {b : Ω → Fin n → ℝ}
    (hagree : ∀ s : ℝ, τ₀ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) < τ₁ ω →
      V s ω + b ω = X s ω)
    {s : ℝ} (hs : ((s : ℝ) : WithTop ℝ) ≠ τ₁ ω) :
    Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
      = Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s :=
  stopped_sub_congr_of_lt hmono (fun s h₁ h₂ => by rw [hagree s h₁ h₂]) hs
/-- The Lebesgue integral of the increment of the cut-off integrand of a path translated by a
vector agreeing with a second path strictly between two times is the integral of the increment of
the integrand built from that second path. -/
theorem integral_stopped_sub_shift_of_lt {n : ℕ} {τ₀ τ₁ : Ω → WithTop ℝ} {ω : Ω}
    (hmono : τ₀ ω ≤ τ₁ ω) (Φ : (Fin n → ℝ) → ℝ) (g : Ω → ℝ → ℝ)
    {V X : ℝ → Ω → Fin n → ℝ} {b : Ω → Fin n → ℝ}
    (hagree : ∀ s : ℝ, τ₀ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) < τ₁ ω →
      V s ω + b ω = X s ω) (A : Set ℝ) :
    (∫ s in A, (Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s) ∂volume)
      = ∫ s in A, (Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s) ∂volume := by
  refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_restrict_of_ae ?_)
  filter_upwards [ae_coe_ne (τ₁ ω)] with s hs
  exact stopped_sub_shift_apply_of_lt hmono Φ g hagree hs
end StoppedSupport

section StoppedIto

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integrals of the increments of two cut-off integrands agreeing strictly between the
two times agree almost surely.** -/
theorem stochasticIntegralBrownian_stopped_sub_congr_of_lt
    {K L : Ω → ℝ → ℝ} {τ₀ τ₁ : Ω → WithTop ℝ} (hmono : ∀ ω, τ₀ ω ≤ τ₁ ω)
    (hagree : ∀ (ω : Ω) (s : ℝ), τ₀ ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < τ₁ ω → K ω s = L ω s)
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s)
        hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s)
        hm₂ hp₂ hq₂ T := by
  refine stochasticIntegralBrownian_congr_of_countable W ℱ hℱ hm₁ hp₁ hq₁ hm₂ hp₂ hq₂
    (D := fun ω => {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ₁ ω})
    (fun ω => countable_setOf_coe_eq (τ₁ ω)) ?_ hT
  intro ω s hs
  exact stopped_sub_congr_of_lt (hmono ω) (hagree ω) hs
include hℱ in
/-- **The Itô integral of the increment of the cut-off integrand of a path translated by a vector
agreeing with a second path strictly between two times is the Itô integral of the increment of
the integrand built from that second path.** -/
theorem stochasticIntegralBrownian_stopped_sub_shift_congr_of_lt
    {n : ℕ} {τ₀ τ₁ : Ω → WithTop ℝ} (hmono : ∀ ω, τ₀ ω ≤ τ₁ ω)
    (Φ : (Fin n → ℝ) → ℝ) (g : Ω → ℝ → ℝ)
    {V X : ℝ → Ω → Fin n → ℝ} {b : Ω → Fin n → ℝ}
    (hagree : ∀ (ω : Ω) (s : ℝ), τ₀ ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < τ₁ ω → V s ω + b ω = X s ω)
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
          - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s)
        hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
          - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s)
        hm₂ hp₂ hq₂ T :=
  stochasticIntegralBrownian_stopped_sub_congr_of_lt W ℱ hℱ hmono
    (fun ω s h₁ h₂ => by rw [hagree ω s h₁ h₂]) hm₁ hp₁ hq₁ hm₂ hp₂ hq₂ hT
end StoppedIto

end LevyStochCalc.Brownian.Ito


