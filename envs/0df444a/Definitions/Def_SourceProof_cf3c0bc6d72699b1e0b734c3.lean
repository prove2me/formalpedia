-- Prove2me | Definitions.Def_SourceProof_cf3c0bc6d72699b1e0b734c3
-- name    : SourceProof_cf3c0bc6d72699b1e0b734c3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:25:01.751415+00:00
-- url     : https://prove2.me/theorems/22022ee4-c86f-43a8-85f6-d959e244be0e
-- title:
--   LevyStochCalc source module: SourceProof_cf3c0bc6d72699b1e0b734c3
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_continuousAdapted_modification` comes from the `LevyStochCalc.Brownian.ItoVersionExists` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoVersionExists_F000
import Definitions.Def_SourceProof_1e4a5244ae2a7fe3cb105b9a

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

section Exists

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_cf3c0bc6d72699b1e0b734c3
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    ∃ Y : ℝ → Ω → ℝ, (∀ ω : Ω, Continuous fun t => Y t ω)
      ∧ (∀ u : ℝ, Measurable[ℱ u] (Y u))
      ∧ ∀ t : ℝ, 0 ≤ t → Y t =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
  classical
  obtain ⟨Y, hYcont, hYmod⟩ :=
    _root_.Prove2MeSourceProof.h_1e4a5244ae2a7fe3cb105b9a W ℱ hℱ H hm hp hq hC0 hCH
  obtain ⟨N₁, hN₁meas, hN₁zero, hN₁cont⟩ := LevyStochCalc.Brownian.Ito.exists_measurable_null_of_ae hYcont
  -- the modification agrees with the integral at every nonnegative dyadic time
  have hdnn : ∀ p : ℕ × ℕ, (0 : ℝ) ≤ ((p.1 : ℝ) / 2 ^ p.2) := fun p => by positivity
  choose Nd hNdmeas hNdzero hNdout using fun p : ℕ × ℕ =>
    LevyStochCalc.Brownian.Ito.exists_measurable_null_of_ae (hYmod ((p.1 : ℝ) / 2 ^ p.2) (hdnn p))
  set N : Set Ω := N₁ ∪ ⋃ p : ℕ × ℕ, Nd p with hNdef
  have hNmeas : MeasurableSet N :=
    hN₁meas.union (MeasurableSet.iUnion fun p => hNdmeas p)
  have hNzero : P N = 0 :=
    MeasureTheory.measure_union_null hN₁zero
      (MeasureTheory.measure_iUnion_null fun p => hNdzero p)
  have hNcont : ∀ ω : Ω, ω ∉ N → Continuous fun t => Y t ω := fun ω hω =>
    hN₁cont ω fun h => hω (Or.inl h)
  have hNdyad : ∀ (p : ℕ × ℕ) (ω : Ω), ω ∉ N →
      Y ((p.1 : ℝ) / 2 ^ p.2) ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq ((p.1 : ℝ) / 2 ^ p.2) ω :=
    fun p ω hω => hNdout p ω fun h => hω (Or.inr (Set.mem_iUnion.mpr ⟨p, h⟩))
  -- `ℱ t` contains `ℱ 0` at every time, hence contains `N`
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  have hNm : ∀ t : ℝ, MeasurableSet[ℱ t] N := fun t =>
    hle0 t N (hnull N hNmeas hNzero)
  -- the truncated modification is adapted, as a pointwise limit along dyadic times
  have hYind : ∀ u : ℝ, 0 ≤ u →
      Measurable[ℱ u] fun ω => if ω ∈ N then (0 : ℝ) else Y u ω := by
    intro u hu
    have hstep : ∀ n : ℕ, Measurable[ℱ u] fun ω => if ω ∈ N then (0 : ℝ)
        else LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω := by
      intro n
      have hSI : Measurable[ℱ u]
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.dyadicApprox n u)) := by
        have h1 := (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq
          (LevyStochCalc.Brownian.Ito.dyadicApprox n u)).measurable
        exact fun A hA => ℱ.mono (LevyStochCalc.Brownian.Ito.dyadicApprox_le hu n) _ (h1 hA)
      exact Measurable.ite (hNm u) measurable_const hSI
    have hlim : Filter.Tendsto (fun (n : ℕ) (ω : Ω) => if ω ∈ N then (0 : ℝ)
          else LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω)
        Filter.atTop (nhds fun ω => if ω ∈ N then (0 : ℝ) else Y u ω) := by
      rw [tendsto_pi_nhds]
      intro ω
      by_cases hω : ω ∈ N
      · simp only [hω, if_true]
        exact tendsto_const_nhds
      · simp only [hω, if_false]
        have heq : (fun n : ℕ => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
            (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω) = fun n => Y (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω := by
          funext n
          exact (hNdyad (⌊u * 2 ^ n⌋₊, n) ω hω).symm
        rw [heq]
        exact Filter.Tendsto.comp ((hNcont ω hω).continuousAt (x := u))
          (LevyStochCalc.Brownian.Ito.tendsto_dyadicApprox hu)
    letI : MeasurableSpace Ω := ℱ u
    exact measurable_of_tendsto_metrizable hstep hlim
  refine ⟨fun t ω => if ω ∈ N then 0 else Y (max t 0) ω, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simpa [hω] using continuous_const
    · simp only [hω, if_false]
      exact (hNcont ω hω).comp (continuous_id.max continuous_const)
  · intro u
    rcases le_or_gt 0 u with hu | hu
    · simp only [max_eq_left hu]
      exact hYind u hu
    · simp only [max_eq_right hu.le]
      exact fun A hA => hle0 u _ (hYind 0 le_rfl hA)
  · intro t ht
    filter_upwards [hYmod t ht,
      MeasureTheory.compl_mem_ae_iff.mpr hNzero] with ω hω hωN
    rw [if_neg hωN, max_eq_left ht]
    exact hω
end Exists

end LevyStochCalc.Brownian.Ito


