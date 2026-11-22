-- Prove2me | Definitions.Def_LevyStochCalc_Ito_LeftLimIntegrandRegularity_F001
-- name    : LevyStochCalc_Ito_LeftLimIntegrandRegularity_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:43:20.105565+00:00
-- url     : https://prove2.me/theorems/f7a8abdc-0db4-4403-a519-f0dcf70ec560
-- title:
--   Source declarations: LevyStochCalc.Ito.LeftLimIntegrandRegularity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.LeftLimIntegrandRegularity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_LeftLimIntegrandRegularity_F000
import Definitions.Def_SourceProof_e745eea003d521dc58279648

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Regularity of a jump coefficient read at the left limits of a path

A path having left limits everywhere meets, at each time, the limit along the dyadic grid points
below that time. The left limits are therefore a countable limit of evaluations of the path, so
they are jointly measurable when the path is, and predictable — hence progressively measurable —
when the path is adapted. Composing with a jointly measurable jump coefficient carries these to
the left-limit jump integrand. Its energy on a horizon is that of the integrand along the path
itself, because a càdlàg path meets its left limits at all but countably many positive times.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.measurable_uncurry_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_leftLimPathAt` — joint measurability
  and progressive measurability of the left limits of a path.
* `LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_comp_state` — a jointly
  measurable function of the time, a progressively measurable state and the mark is marked
  progressively measurable.
* `LevyStochCalc.Ito.JumpSplitting.measurable_jumpCoeff_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_jumpCoeff_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.lintegral_sq_jumpCoeff_leftLimPathAt_eq` — the three
  admissibility data of the left-limit jump integrand.

## References

* Protter, *Stochastic Integration and Differential Equations*, 2005, §III.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Probability

end LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {n : ℕ}

section Measurability

variable {Xp : ℝ → Ω → Fin n → ℝ}

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Measurability

section Coefficient

variable {d : ℕ} {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}

/-- **The jump coefficient read at the left limits of a jointly measurable path having left
limits everywhere is jointly measurable.** -/
theorem measurable_jumpCoeff_leftLimPathAt (hXm : Measurable fun q : ℝ × Ω => Xp q.1 q.2)
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) (i : Fin n)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i) :
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i := by
  have hΛ : Measurable fun p : Ω × ℝ × E => leftLimPathAt Xp p.2.1 p.1 :=
    (measurable_uncurry_leftLimPathAt hXm hleft).comp
      (measurable_snd.fst.prodMk measurable_fst)
  exact hγ.comp (measurable_snd.fst.prodMk (hΛ.prodMk measurable_snd.snd))
variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The jump coefficient read at the left limits of an adapted path having left limits
everywhere is marked progressively measurable.** -/
theorem markedProgressivelyMeasurable_jumpCoeff_leftLimPathAt
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) (i : Fin n)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i :=
  _root_.Prove2MeSourceProof.h_e745eea003d521dc58279648
    (fun j => progressivelyMeasurable_leftLimPathAt hℱ0 hXadapt hleft j)
    (F := fun s y e => coeffs.γ s y e i) hγ
end Coefficient

section Energy

variable {P : Measure Ω} {ν : Measure E} {d : ℕ} {coeffs : Setting.JumpDiffusionCoeffs n d E}
  {Xp : ℝ → Ω → Fin n → ℝ}

/-- The energy of a marked integrand on a horizon is unchanged when the process it is evaluated
along is replaced by one meeting it at all but countably many positive times. -/
theorem lintegral_sq_congr_of_countable_ne {V : Type*} {X Xm : ℝ → Ω → V}
    (F : ℝ → V → E → ℝ)
    (hXm : ∀ᵐ ω ∂P, {s : ℝ | 0 < s ∧ Xm s ω ≠ X s ω}.Countable) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖F s (Xm s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖F s (X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ae_forall_eq_of_countable_ne (P := P) (E := E) F hXm T] with ω hω
  refine lintegral_congr_ae ?_
  filter_upwards [hω] with s hs
  exact lintegral_congr fun e => by rw [hs e]
/-- **The left-limit jump integrand of a càdlàg path has the energy of the integrand along the
path itself.** -/
theorem lintegral_sq_jumpCoeff_leftLimPathAt_eq
    (hcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Xp s ω) (𝓝[>] t) (𝓝 (Xp t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L))
    (i : Fin n) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (leftLimPathAt Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖coeffs.γ s (Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
  lintegral_sq_congr_of_countable_ne (ν := ν) (fun s y e => coeffs.γ s y e i)
    (ae_countable_setOf_pos_ne_leftLimPathAt (P := P) Xp hcadlag) T
end Energy

end LevyStochCalc.Ito.JumpSplitting


