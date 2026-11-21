-- Prove2me | Definitions.Def_SourceProof_adfa01854b07ed0ea603550e
-- name    : SourceProof_adfa01854b07ed0ea603550e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:04:25.052049+00:00
-- url     : https://prove2.me/theorems/ea173cf6-bbf3-4219-a801-58ac9d645e35
-- title:
--   LevyStochCalc source module: SourceProof_adfa01854b07ed0ea603550e
-- statement:
--   The original source theorem `LevyStochCalc.Driver.pairing_joint_value_characterMultidim_eq_zero` comes from the `LevyStochCalc.Driver.JointMultidim` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointMultidim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mixed cell lemma for a multidimensional Brownian motion

A character of a vector of Brownian increments across a cell is the character of the increment
of a unit combination, scaled by the length of the weight vector, so the mixed cell lemma for a
single Brownian motion carries over to the multidimensional driver with the Poisson character
riding along unchanged.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Cell

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

end Cell

section Grid

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)


theorem _root_.Prove2MeSourceProof.h_adfa01854b07ed0ea603550e (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {T : ℝ} (hT : 0 < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (c : ℕ → Fin d → ℝ) (n : ℕ)
    (hlt : ∀ k, k < n → τ k < τ (k + 1)) (hTn : τ n < T) :
    ∫ ω, ((Z ω : ℝ) : ℂ)
        * (Complex.exp (Complex.I * ((∑ i, ∑ k ∈ Finset.Ico 1 (n + 1),
            c k i * (W.W i).W (τ k) ω : ℝ) : ℂ))
          * charAt N w Bfam (τ n) ω) ∂P = 0 := by
  have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => (hlt k hk).le
  have hkey := LevyStochCalc.Driver.pairing_jointGridCharacterMultidim_eq_zero W N ℱ hd hℱi hℱB hℱN hℱ0 hnull hτ0
    hT hA hAν w hBm hBsub he₀ hZ2 hperp hZcomp hZ0
    (fun k i => ∑ j ∈ Finset.Ico (k + 1) (n + 1), c j i) n hlt hTn
  refine Eq.trans (integral_congr_ae ?_) hkey
  have hinit : ∀ᵐ ω ∂P, ∀ i : Fin d, (W.W i).W 0 ω = 0 :=
    ae_all_iff.mpr fun i => (W.W i).initial_zero
  filter_upwards [hinit, _root_.Prove2MeSourceProof.h_9515dd3e42bfbfd6da3f4172 N w hBm hA hAν hBsub hτ0 hle'] with ω hω hprod
  have heq : (∑ k ∈ Finset.range n, ∑ i, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j i)
        * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω))
      = ∑ i, ∑ k ∈ Finset.Ico 1 (n + 1), c k i * (W.W i).W (τ k) ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      _root_.Prove2MeSourceProof.h_3bb40c5e7df4a1af88374480 (fun k => c k i) (Wv := fun k => (W.W i).W (τ k) ω)
        (by rw [hτ0]; exact hω i) n
  rw [← heq, hprod, LevyStochCalc.Driver.jointGridCharacterMultidim, Finset.prod_mul_distrib, ← Complex.exp_sum,
    Complex.ofReal_sum, Finset.mul_sum]
end Grid

end LevyStochCalc.Driver


