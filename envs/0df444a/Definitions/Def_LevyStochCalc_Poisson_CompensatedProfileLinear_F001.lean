-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileLinear_F001
-- name    : LevyStochCalc_Poisson_CompensatedProfileLinear_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:16:55.494504+00:00
-- url     : https://prove2.me/theorems/6254df3e-5f53-4a82-af14-4a268672a234
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProfileLinear
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProfileLinear. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F001
import Definitions.Def_SourceProof_987e45c462c3ce8ce4a43332

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

/-! ### Linear combinations -/

/-- The compensated integral over the step `(a, b]` of a finite sum of square-integrable mark
profiles is almost surely the sum of their compensated integrals. -/
theorem compensatedProfile_finsetSum (N : PoissonRandomMeasure P ν) {ι : Type*}
    (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ i ∈ s, MemLp (f i) 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    compensatedProfile N (∑ i ∈ s, f i) a b =ᵐ[P] ∑ i ∈ s, compensatedProfile N (f i) a b := by
  simpa using _root_.Prove2MeSourceProof.h_987e45c462c3ce8ce4a43332 N s (fun _ => 1) hf ha hab
/-- The compensated integral over the step `(a, b]` of a sum of two square-integrable mark
profiles is almost surely the sum of their compensated integrals. -/
theorem compensatedProfile_add (N : PoissonRandomMeasure P ν) {f g : E → ℝ} (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (f + g) a b
      =ᵐ[P] compensatedProfile N f a b + compensatedProfile N g a b := by
  have h := compensatedProfile_finsetSum N (Finset.univ : Finset (Fin 2)) (f := ![f, g])
    (fun i _ => by fin_cases i <;> assumption) ha hab
  simpa [Fin.sum_univ_two] using h
/-- The compensated integral over the step `(a, b]` of a scalar multiple of a square-integrable
mark profile is almost surely the same multiple of its compensated integral. -/
theorem compensatedProfile_smul (N : PoissonRandomMeasure P ν) (c : ℝ) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (c • f) a b =ᵐ[P] c • compensatedProfile N f a b := by
  have h := _root_.Prove2MeSourceProof.h_987e45c462c3ce8ce4a43332 N (Finset.univ : Finset (Fin 1)) (fun _ => c)
    (f := fun _ => f) (fun _ _ => hf) ha hab
  simpa using h
/-- The compensated integral over the step `(a, b]` of the negative of a square-integrable mark
profile is almost surely the negative of its compensated integral. -/
theorem compensatedProfile_neg (N : PoissonRandomMeasure P ν) {f : E → ℝ} (hf : MemLp f 2 ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (-f) a b =ᵐ[P] -compensatedProfile N f a b := by
  simpa using compensatedProfile_smul N (-1) hf ha hab
/-- The compensated integral over the step `(a, b]` of a difference of two square-integrable
mark profiles is almost surely the difference of their compensated integrals. -/
theorem compensatedProfile_sub (N : PoissonRandomMeasure P ν) {f g : E → ℝ} (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (f - g) a b
      =ᵐ[P] compensatedProfile N f a b - compensatedProfile N g a b := by
  filter_upwards [compensatedProfile_add N hf hg.neg ha hab, compensatedProfile_neg N hg ha hab]
    with ω h1 h2
  simp only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply] at h1 h2 ⊢
  rw [h1, h2]
end LevyStochCalc.Poisson


