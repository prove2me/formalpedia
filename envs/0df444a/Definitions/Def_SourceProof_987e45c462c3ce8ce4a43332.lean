-- Prove2me | Definitions.Def_SourceProof_987e45c462c3ce8ce4a43332
-- name    : SourceProof_987e45c462c3ce8ce4a43332
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:15:49.81665+00:00
-- url     : https://prove2.me/theorems/d2b3476c-6067-4758-97f6-fb8f957c2ee1
-- title:
--   LevyStochCalc source module: SourceProof_987e45c462c3ce8ce4a43332
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.compensatedProfile_finsetSum_smul` comes from the `LevyStochCalc.Poisson.CompensatedProfileLinear` module. The staged Lean declaration includes its source proof and dependency references.
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

/-! ### Linear combinations -/


theorem _root_.Prove2MeSourceProof.h_987e45c462c3ce8ce4a43332 (N : PoissonRandomMeasure P ν) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) {f : ι → E → ℝ} (hf : ∀ i ∈ s, MemLp (f i) 2 ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (∑ i ∈ s, c i • f i) a b
      =ᵐ[P] ∑ i ∈ s, c i • compensatedProfile N (f i) a b := by
  set F : E → ℝ := ∑ i ∈ s, c i • f i with hFdef
  have hFe : ∀ e, F e = ∑ i ∈ s, c i * f i e := fun e => by
    simp [hFdef, Finset.sum_apply]
  have hF : MemLp F 2 ν := memLp_finsetSum' s fun i hi => (hf i hi).const_smul (c i)
  have hJ : ∀ g : E → ℝ, MemLp (LevyStochCalc.Poisson.compensatedProfile N g a b) 2 P :=
    fun g => LevyStochCalc.Poisson.memLp_compensatedProfile N g a b
  set X : Ω → ℝ := fun ω => LevyStochCalc.Poisson.compensatedProfile N F a b ω
    - ∑ i ∈ s, c i * LevyStochCalc.Poisson.compensatedProfile N (f i) a b ω with hXdef
  have hX : MemLp X 2 P :=
    (hJ F).sub (memLp_finsetSum s fun i _ => (hJ (f i)).const_mul (c i))
  have horth : ∀ g : E → ℝ, MemLp g 2 ν →
      ∫ ω, X ω * LevyStochCalc.Poisson.compensatedProfile N g a b ω ∂P = 0 := by
    intro g hg
    have hint : ∀ i ∈ s, Integrable (fun ω => c i * LevyStochCalc.Poisson.compensatedProfile N (f i) a b ω
        * LevyStochCalc.Poisson.compensatedProfile N g a b ω) P :=
      fun i _ => ((hJ (f i)).const_mul (c i)).integrable_mul (hJ g)
    have hνint : ∀ i ∈ s, Integrable (fun e => c i * f i e * g e) ν :=
      fun i hi => ((hf i hi).const_mul (c i)).integrable_mul hg
    have hνF : ∫ e, F e * g e ∂ν = ∑ i ∈ s, c i * ∫ e, f i e * g e ∂ν := by
      simp_rw [hFe, Finset.sum_mul]
      rw [integral_finsetSum s hνint]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      simp_rw [mul_assoc]
    calc ∫ ω, X ω * LevyStochCalc.Poisson.compensatedProfile N g a b ω ∂P
        = ∫ ω, LevyStochCalc.Poisson.compensatedProfile N F a b ω * LevyStochCalc.Poisson.compensatedProfile N g a b ω ∂P
          - ∑ i ∈ s, c i * ∫ ω, LevyStochCalc.Poisson.compensatedProfile N (f i) a b ω
            * LevyStochCalc.Poisson.compensatedProfile N g a b ω ∂P := by
          have h1 : Integrable (fun ω => LevyStochCalc.Poisson.compensatedProfile N F a b ω
              * LevyStochCalc.Poisson.compensatedProfile N g a b ω) P := (hJ F).integrable_mul (hJ g)
          simp only [hXdef, sub_mul, Finset.sum_mul]
          rw [integral_sub h1 (integrable_finsetSum s hint), integral_finsetSum s hint]
          refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
          rw [← integral_const_mul]
          simp_rw [mul_assoc]
      _ = (b - a) * (∫ e, F e * g e ∂ν - ∑ i ∈ s, c i * ∫ e, f i e * g e ∂ν) := by
          rw [_root_.Prove2MeSourceProof.h_b99d59281a5160eb28e462a1 N hF hg ha hab, mul_sub, Finset.mul_sum]
          refine congrArg _ (Finset.sum_congr rfl fun i hi => ?_)
          rw [_root_.Prove2MeSourceProof.h_b99d59281a5160eb28e462a1 N (hf i hi) hg ha hab]
          ring
      _ = 0 := by rw [hνF, sub_self, mul_zero]
  have hsq : ∫ ω, X ω ^ 2 ∂P = 0 := by
    have hint : ∀ i ∈ s, Integrable (fun ω => X ω * (c i * LevyStochCalc.Poisson.compensatedProfile N (f i) a b ω))
        P := fun i _ => hX.integrable_mul ((hJ (f i)).const_mul (c i))
    calc ∫ ω, X ω ^ 2 ∂P
        = ∫ ω, X ω * LevyStochCalc.Poisson.compensatedProfile N F a b ω ∂P
          - ∑ i ∈ s, c i * ∫ ω, X ω * LevyStochCalc.Poisson.compensatedProfile N (f i) a b ω ∂P := by
          have hpt : (fun ω => X ω ^ 2) = fun ω => X ω * LevyStochCalc.Poisson.compensatedProfile N F a b ω
              - ∑ i ∈ s, X ω * (c i * LevyStochCalc.Poisson.compensatedProfile N (f i) a b ω) := by
            funext ω
            rw [← Finset.mul_sum, ← mul_sub, sq]
          have h1 : Integrable (fun ω => X ω * LevyStochCalc.Poisson.compensatedProfile N F a b ω) P :=
            hX.integrable_mul (hJ F)
          rw [hpt, integral_sub h1 (integrable_finsetSum s hint), integral_finsetSum s hint]
          refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
          rw [← integral_const_mul]
          congr 1
          funext ω
          ring
      _ = 0 := by
          rw [horth F hF, Finset.sum_eq_zero fun i hi => by rw [horth (f i) (hf i hi), mul_zero],
            sub_zero]
  have hX0 : (fun ω => X ω ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (X ω)) hX.integrable_sq).1 hsq
  filter_upwards [hX0] with ω hω
  have h0 : X ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hω
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simpa [hXdef, sub_eq_zero] using h0
end LevyStochCalc.Poisson


