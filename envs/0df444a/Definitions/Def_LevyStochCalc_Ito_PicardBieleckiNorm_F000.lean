-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F000
-- name    : LevyStochCalc_Ito_PicardBieleckiNorm_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:17:05.115787+00:00
-- url     : https://prove2.me/theorems/18364b53-b2ca-42a0-9eef-3c3e4bea620e
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardBieleckiNorm
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardBieleckiNorm. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_Setting_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki norm, the process space `S²`, and the drift step of Picard iteration

The Bielecki-weighted `L²` norm `‖X‖_{β,T} = sup_{t ∈ [0,T]} e^{-βt} (𝔼‖X_t‖²)^{1/2}` of a
process on `[0, T]`, the space `SBoundedProcess` of jointly measurable, progressively measurable,
almost surely càdlàg processes of finite norm at weight `0`, and the freeze of such a process at
the horizon, which leaves the norm unchanged and is `L²`-bounded at every later time.  The drift
component `picardStep_drift` of the Picard map is defined here, with its per-component difference
identities, its `L¹` Lipschitz bound, the Cauchy-Schwarz bound `(∫_0^t f)² ≤ t ∫_0^t f²` on a
window, and the per-component `L²` Lipschitz bound that follows from them.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The Bielecki-weighted L² norm of a process `X : ℝ → Ω → (Fin n → ℝ)`
on `[0, T]`:

  `‖X‖_β,T := sup_{t ∈ [0, T]} e^{-βt} · (E[‖X_t‖²])^{1/2}`.

For `β = 0` this is the standard `S²` norm; for `β > 0` it is
equivalent to `S²` but absorbs the Grönwall constant in the Picard
contraction estimate. -/
noncomputable def bieleckiNorm
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (β T : ℝ) (X : ℝ → Ω → (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc (0 : ℝ) T,
    ENNReal.ofReal (Real.exp (-β * t)) *
      (∫⁻ ω, (∑ i, (‖X t ω i‖₊ : ℝ≥0∞) ^ 2) ∂P) ^ (1/2 : ℝ)
/-- The space of jointly measurable, `ℱ`-progressively measurable, almost-surely càdlàg
processes on `[0, T]` with values in `Fin n → ℝ` and finite Bielecki norm at weight `0`.

One difference from the literature's `S²([0, T]; ℝⁿ)`, recorded in the section note "The
`IsRegular` hypothesis and the `S²` norm" of `Ito/PicardSpaceBieleckiQuotient.lean`: the norm
here is `bieleckiNorm`, the weighted supremum over `t` of the `L²` norms, rather than the `L²`
norm of the supremum. -/
structure SBoundedProcess
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ) where
  /-- The path map. -/
  X : ℝ → Ω → (Fin n → ℝ)
  /-- Joint measurability in `(t, ω)`. -/
  measurable_path : Measurable (Function.uncurry X)
  /-- Each coordinate is progressively measurable for `ℱ`. -/
  adapted : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ (fun ω s => X s ω i)
  /-- Almost-sure càdlàg paths. -/
  cadlag_paths : ∀ᵐ ω ∂P, ∀ t : ℝ,
    Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ,
          Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds L)
  /-- Finite Bielecki-norm at the standard weight `β = 0`. -/
  sup_L2 : bieleckiNorm (P := P) 0 T X < ⊤
/-- Freezing a process at the horizon does not change its Bielecki norm on `[0, T]`, since the
supremum runs over times at which the two processes agree. -/
theorem bieleckiNorm_min {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] (β T : ℝ)
    (X : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) β T (fun s ω => X (min s T) ω) = bieleckiNorm (P := P) β T X := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun ht => ?_
  simp only [min_eq_left ht.2]
/-- The Bielecki norm at weight `0` bounds the `L²` slice energy at every time of the window,
for any path map. -/
theorem lintegral_sq_le_bieleckiNorm_sq_raw {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (Z : ℝ → Ω → (Fin n → ℝ)) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) :
    (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ (bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) := by
  have hle : (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)
      ≤ bieleckiNorm (P := P) 0 T Z := by
    unfold bieleckiNorm
    refine le_trans (le_of_eq ?_)
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
        ENNReal.ofReal (Real.exp (-0 * t))
          * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)) u hu)
    simp
  calc (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ((∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) := by
        rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ (bieleckiNorm (P := P) 0 T Z) ^ (2 : ℕ) := pow_le_pow_left' hle 2
namespace SBoundedProcess

end SBoundedProcess

end LevyStochCalc.Ito.Picard


