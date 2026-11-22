-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F001
-- name    : LevyStochCalc_Ito_PicardGlobal_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:45:39.780857+00:00
-- url     : https://prove2.me/theorems/4457ad7e-18e3-477e-b496-812d84f8acec
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardGlobal
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardGlobal. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F000
import Definitions.Def_SourceProof_3ea3d9aac16fe017a291a288
import Definitions.Def_SourceProof_48fc762eec2686f4f3c5681d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

/-! ### The glued path map -/

/-! ### Consistency of a family of window solutions -/

section Glue

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

/-- Window solutions on nested windows agree, almost surely, along whole paths. -/
theorem ae_all_windows_agree
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
    (hYcad : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω)))
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYsol : ∀ k : ℕ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ, ∀ t ∈ Set.Icc (0 : ℝ) (min ((p.1 : ℝ) + 1) ((p.2 : ℝ) + 1)),
      Y p.1 t ω = Y p.2 t ω := by
  rw [MeasureTheory.ae_all_iff]
  rintro ⟨j, k⟩
  have hTpos : (0 : ℝ) < min ((j : ℝ) + 1) ((k : ℝ) + 1) :=
    lt_min (by positivity) (by positivity)
  have hpt := _root_.Prove2MeSourceProof.h_48fc762eec2686f4f3c5681d W N ℱ hℱW hℱN coeffs x₀ hReg hLip (hYm j) (hYm k)
    (hYS j) (hYS k) hTpos
    (SolvesOn.mono W N ℱ hℱW hℱN coeffs x₀ (min_le_left _ _) (hYsol j))
    (SolvesOn.mono W N ℱ hℱW hℱN coeffs x₀ (min_le_right _ _) (hYsol k))
  refine _root_.Prove2MeSourceProof.h_3ea3d9aac16fe017a291a288 (hYcad j) (hYcad k) fun t ht => ?_
  filter_upwards [hpt t ht] with ω hω
  exact funext hω
omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P] in
/-- The glued path map coincides, almost surely, with each member of a consistent family on that
member's window. -/
theorem ae_globalPatch_eq {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hcons : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ,
      ∀ t ∈ Set.Icc (0 : ℝ) (min ((p.1 : ℝ) + 1) ((p.2 : ℝ) + 1)), Y p.1 t ω = Y p.2 t ω) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1), globalPatch Y t ω = Y k t ω := by
  filter_upwards [hcons] with ω hω
  intro k t ht
  refine hω (⌈t⌉₊, k) t ⟨ht.1, le_min ?_ ht.2⟩
  exact (Nat.le_ceil t).trans (by linarith)
omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P] in
/-- The glued path map has a finite `S²` norm on every window. -/
theorem lintegral_sq_iSup_globalPatch_lt_top {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      globalPatch Y t ω = Y k t ω)
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (T' : ℝ) (hT' : 0 < T') :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i,
      (‖globalPatch Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) (hYS ⌈T'⌉₊ T' hT')
  filter_upwards [hagree] with ω hω
  refine le_of_eq (iSup_congr fun t => ?_)
  rw [hω ⌈T'⌉₊ (t : ℝ) ⟨t.2.1, t.2.2.trans ((Nat.le_ceil T').trans (by linarith))⟩]
omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P] in
/-- The glued path map is almost surely càdlàg on the SDE time domain. -/
theorem cadlag_globalPatch {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      globalPatch Y t ω = Y k t ω)
    (hYcad : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω))
        ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
            Filter.Tendsto (fun s => Y k s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => globalPatch Y s ω) (nhdsWithin t (Set.Ioi t))
          (nhds (globalPatch Y t ω))
        ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
            Filter.Tendsto (fun s => globalPatch Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ) := by
  filter_upwards [hagree, MeasureTheory.ae_all_iff.mpr hYcad] with ω hω hcad
  intro t ht
  set k := ⌈t⌉₊ + 1 with hk
  have htk : t < (k : ℝ) := by
    have := Nat.le_ceil t
    push_cast [hk]
    linarith
  have hpatch : ∀ s : ℝ, 0 ≤ s → s ≤ (k : ℝ) + 1 → globalPatch Y s ω = Y k s ω :=
    fun s hs0 hs1 => hω k s ⟨hs0, hs1⟩
  constructor
  · have hev : ∀ᶠ s in nhdsWithin t (Set.Ioi t), globalPatch Y s ω = Y k s ω := by
      have hmem : Set.Iio ((k : ℝ) + 1) ∈ nhdsWithin t (Set.Ioi t) :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
      filter_upwards [hmem, self_mem_nhdsWithin] with s hs hs'
      exact hpatch s (ht.trans (le_of_lt hs')) (le_of_lt hs)
    refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) ?_
    rw [hpatch t ht (by linarith)]
    exact (hcad k t).1
  · intro i
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · obtain ⟨ℓ, hℓ⟩ := (hcad 0 t).2 i
      refine ⟨ℓ, Filter.Tendsto.congr' ?_ hℓ⟩
      have hmem : Set.Iio t ∈ nhdsWithin t (Set.Iio t) := self_mem_nhdsWithin
      filter_upwards [hmem] with s hs
      have : ⌈s⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by simp only [Set.mem_Iio] at hs; linarith [ht0])
      simp [globalPatch, this]
    · obtain ⟨ℓ, hℓ⟩ := (hcad k t).2 i
      refine ⟨ℓ, Filter.Tendsto.congr' ?_ hℓ⟩
      have hmem : Set.Ioo (0 : ℝ) t ∈ nhdsWithin t (Set.Iio t) := by
        refine Filter.inter_mem ?_ self_mem_nhdsWithin
        exact nhdsWithin_le_nhds (Ioi_mem_nhds ht0)
      filter_upwards [hmem] with s hs
      rw [hpatch s hs.1.le (by linarith [hs.2])]
end Glue

end LevyStochCalc.Ito.Picard


