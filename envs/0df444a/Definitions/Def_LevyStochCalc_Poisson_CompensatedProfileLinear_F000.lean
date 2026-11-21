-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileLinear_F000
-- name    : LevyStochCalc_Poisson_CompensatedProfileLinear_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:05:54.674927+00:00
-- url     : https://prove2.me/theorems/f81b8113-61ae-4b2c-8bb6-eefdd61ba04a
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProfileLinear
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProfileLinear. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the compensated integral of a mark profile

For the compensated integral `J(f)` over the step `(a, b]` of a mark profile `f : E → ℝ` against a
Poisson random measure with intensity `ν`, and square-integrable profiles `f₁, …, fₙ`,

  `J(∑ᵢ cᵢ fᵢ) = ∑ᵢ cᵢ J(fᵢ)`   almost surely.

The defect `X = J(∑ᵢ cᵢ fᵢ) − ∑ᵢ cᵢ J(fᵢ)` is orthogonal in `L²(P)` to the compensated integral
of every square-integrable profile, because the `L²(P)` pairing
`E[J(f) J(g)] = (b − a) ∫ f g dν` is linear in `f`. The defect is itself a combination of such
integrals, so its second moment vanishes.

The compensated integral depends on the profile only through its class modulo `ν`-null sets:
the approximating sequences of simple profiles, and hence the defining limit, are the same for
two profiles equal `ν`-almost everywhere.

## Main statements

* `LevyStochCalc.Poisson.compensatedProfile_congr_ae` — profiles equal `ν`-almost everywhere
  have the same compensated integral over every step.
* `LevyStochCalc.Poisson.compensatedProfile_ae_eq_of_ae_eq` — the same, almost surely.
* `LevyStochCalc.Poisson.compensatedProfile_finsetSum_smul` — the compensated integral of a
  finite linear combination of square-integrable profiles.
* `LevyStochCalc.Poisson.compensatedProfile_finsetSum` — of a finite sum.
* `LevyStochCalc.Poisson.compensatedProfile_add`, `LevyStochCalc.Poisson.compensatedProfile_smul`,
  `LevyStochCalc.Poisson.compensatedProfile_neg`, `LevyStochCalc.Poisson.compensatedProfile_sub`
  — of a sum, a scalar multiple, a negative and a difference.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Congruence -/

/-- **Congruence.** Two mark profiles equal `ν`-almost everywhere have the same compensated
integral over every step. -/
theorem compensatedProfile_congr_ae (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hfg : f =ᵐ[ν] g) (a b : ℝ) :
    compensatedProfile N f a b = compensatedProfile N g a b := by
  have hn : ∀ G : SimpleProfile E ν, eLpNorm (fun e => G.toFun e - f e) 2 ν
      = eLpNorm (fun e => G.toFun e - g e) 2 ν := fun G =>
    eLpNorm_congr_ae (hfg.mono fun e he => by simp only [he])
  have hpred : IsCompensatedProfile N f a b = IsCompensatedProfile N g a b := by
    funext J
    simp only [IsCompensatedProfile, hn]
  unfold compensatedProfile
  rw [hpred]
/-- Two mark profiles equal `ν`-almost everywhere have almost surely equal compensated integrals
over every step. -/
theorem compensatedProfile_ae_eq_of_ae_eq (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hfg : f =ᵐ[ν] g) (a b : ℝ) :
    compensatedProfile N f a b =ᵐ[P] compensatedProfile N g a b := by
  rw [compensatedProfile_congr_ae N hfg a b]
/-! ### Linear combinations -/

end LevyStochCalc.Poisson


