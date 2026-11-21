-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoVersionExists_F000
-- name    : LevyStochCalc_Brownian_ItoVersionExists_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:46.852319+00:00
-- url     : https://prove2.me/theorems/dda6cdb1-5442-471c-994e-f26f9bff4aec
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoVersionExists
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoVersionExists. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Existence of a continuous adapted version of an Itô process

The Itô integral has an a.e.-continuous modification by Kolmogorov–Chentsov. Zeroing its paths
on a null set makes them continuous everywhere, and the resulting process stays adapted when the
filtration contains the null sets. Adding a measurable initial value and the drift's
(Lipschitz, hence continuous) window integral gives an `IsItoVersion`.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_of_ae_eq_of_null_mem` — a σ-algebra of the filtration
  containing the null sets does not distinguish a.e.-equal functions.
* `LevyStochCalc.Brownian.Ito.dyadicApprox` — the dyadic approximation from below, whose values
  lie in a countable set.
* `LevyStochCalc.Brownian.Ito.exists_continuousAdapted_modification` — the Itô integral has a
  continuous adapted modification.
* `LevyStochCalc.Brownian.Ito.exists_isItoVersion` — a continuous adapted version exists.
* `LevyStochCalc.Brownian.Ito.exists_isItoVersion_aug` — the same over the augmented
  filtration, with no side conditions.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- If a sub-σ-algebra of a filtration contains every `μ`-null set, a function a.e.-equal to a
measurable function for it is itself measurable for it. -/
theorem measurable_of_ae_eq_of_null_mem {μ : Measure Ω}
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (u : ℝ)
    (hnull : ∀ s : Set Ω, (∃ N, MeasurableSet N ∧ μ N = 0 ∧ s ⊆ N) → MeasurableSet[ℱ u] s)
    {f g : Ω → ℝ} (hg : Measurable[ℱ u] g) (hfg : f =ᵐ[μ] g) : Measurable[ℱ u] f := by
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hfg)
  have hNm : MeasurableSet[ℱ u] N := hnull N ⟨N, hNmeas, hNzero, Set.Subset.rfl⟩
  intro A hA
  have hset : f ⁻¹' A = (g ⁻¹' A \ N) ∪ (f ⁻¹' A ∩ N) := by
    ext ω
    by_cases hω : ω ∈ N
    · simp [hω]
    · have hfgω : f ω = g ω := by
        by_contra hne
        exact hω (hNsub hne)
      simp [hω, hfgω]
  rw [hset]
  exact MeasurableSet.union (MeasurableSet.diff (hg hA) hNm)
    (hnull _ ⟨N, hNmeas, hNzero, Set.inter_subset_right⟩)
/-- A measurable null set outside which an almost-everywhere property holds. -/
theorem exists_measurable_null_of_ae {μ : Measure Ω} {p : Ω → Prop} (h : ∀ᵐ ω ∂μ, p ω) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧ ∀ ω, ω ∉ N → p ω := by
  obtain ⟨N, hsub, hmeas, hzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp h)
  exact ⟨N, hmeas, hzero, fun ω hω => by_contra fun hp => hω (hsub hp)⟩
/-- The `n`-th dyadic approximation from below of a nonnegative real. -/
noncomputable def dyadicApprox (n : ℕ) (u : ℝ) : ℝ := (⌊u * 2 ^ n⌋₊ : ℝ) / 2 ^ n
theorem dyadicApprox_nonneg (n : ℕ) (u : ℝ) : 0 ≤ dyadicApprox n u := by
  unfold dyadicApprox
  positivity
theorem dyadicApprox_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : dyadicApprox n u ≤ u := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicApprox, div_le_iff₀ h2]
  exact Nat.floor_le (by positivity)
theorem sub_dyadicApprox_lt (u : ℝ) (n : ℕ) : u - dyadicApprox n u < 1 / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfl := Nat.lt_floor_add_one (u * 2 ^ n)
  rw [dyadicApprox, sub_lt_iff_lt_add,
    show (1 : ℝ) / 2 ^ n + (⌊u * 2 ^ n⌋₊ : ℝ) / 2 ^ n
      = ((⌊u * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n by ring, lt_div_iff₀ h2]
  linarith
theorem tendsto_dyadicApprox {u : ℝ} (hu : 0 ≤ u) :
    Filter.Tendsto (fun n : ℕ => dyadicApprox n u) Filter.atTop (nhds u) := by
  have hlo : ∀ n : ℕ, u - 1 / 2 ^ n ≤ dyadicApprox n u := fun n => by
    have := sub_dyadicApprox_lt u n
    linarith
  have hhi : ∀ n : ℕ, dyadicApprox n u ≤ u := dyadicApprox_le hu
  have hpow : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) Filter.atTop (nhds 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
  have hsub : Filter.Tendsto (fun n : ℕ => u - 1 / 2 ^ n) Filter.atTop (nhds u) := by
    simpa using (tendsto_const_nhds (x := u) (f := Filter.atTop (α := ℕ))).sub hpow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hsub tendsto_const_nhds hlo hhi
theorem dyadicApprox_eq (n : ℕ) (u : ℝ) :
    dyadicApprox n u = ((⌊u * 2 ^ n⌋₊ : ℕ) : ℝ) / 2 ^ n := rfl
section Exists

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end Exists

end LevyStochCalc.Brownian.Ito


