-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F000
-- name    : LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:57:24.291176+00:00
-- url     : https://prove2.me/theorems/f996c1cb-26fb-497a-b5f8-4a2503d0638f
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaUnboundedLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaUnboundedLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F001
import Definitions.Def_SourceProof_7c1e051c1c1f9aebd6c80fa9
import Definitions.Def_SourceProof_cfcb430e396d5e0dfbf97052

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula without a pointwise bound on the coefficients

Passing to the limit along the clamped approximation gives Itô's formula for a vector Itô process
whose diffusion matrix and drift carry no pointwise bound, first for a function with bounded first
and second derivatives and then, by localisation, for an arbitrary `C²` function.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded_coeff` — Itô's formula with unbounded
  coefficients, for a function with bounded first and second derivatives.
* `LevyStochCalc.Brownian.Ito.itoFormula_of_unbounded` — Itô's formula for a `C²` function of a
  vector Itô process, with no bound on either the coefficients or the derivatives.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Limits

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)

variable (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

/-- **The stochastic integrals of the clamped approximation converge in `L²`.** -/
theorem tendsto_lintegral_sq_norm_stochInt_clamp
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ} (hT : 0 < T)
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (hmY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s))
    (hpY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
    (hqY : ∀ (i : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmX : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpX : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqX : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p : Fin n) (k : Fin d) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω,
        (‖stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
              (hmY i p k) (hpY i p k) (hqY i p k) T ω
            - stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmX p k) (hpX p k) (hqX p k) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (𝓝 0) := by
  refine Filter.Tendsto.congr (fun i => ?_)
    (_root_.Prove2MeSourceProof.h_cfcb430e396d5e0dfbf97052 hf'c hK₁0 hf'bd hm hq hYm hXm hge hae p k)
  exact (_root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 (W.W k) ℱ' (hcoord k)
    (fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
    (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hmY i p k) (hmX p k) (hpY i p k) (hpX p k) (hqY i p k) (hqX p k) hT).symm
/-- **Along a further subsequence the stochastic integrals of the clamped approximation converge
almost surely.** -/
theorem exists_seq_ae_tendsto_stochInt_clamp
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ} (hT : 0 < T)
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (hmY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s))
    (hpY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
    (hqY : ∀ (i : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmX : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpX : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqX : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧ ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      Filter.Tendsto (fun i : ℕ => stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => coordDeriv f' p (Y (ms i) s ω) * clampCoeff H (ns (ms i)) p k ω s)
          (hmY (ms i) p k) (hpY (ms i) p k) (hqY (ms i) p k) T ω) Filter.atTop
        (𝓝 (stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
          (hmX p k) (hpX p k) (hqX p k) T ω)) := by
  classical
  obtain ⟨ms, hmsge, hms⟩ := _root_.Prove2MeSourceProof.h_7c1e051c1c1f9aebd6c80fa9 (μ := P)
    (ι := Fin n × Fin d)
    (u := fun i c ω => stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
      (fun ω s => coordDeriv f' c.1 (Y i s ω) * clampCoeff H (ns i) c.1 c.2 ω s)
      (hmY i c.1 c.2) (hpY i c.1 c.2) (hqY i c.1 c.2) T ω)
    (v := fun c ω => stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
      (fun ω s => coordDeriv f' c.1 (X s ω) * H c.1 c.2 ω s)
      (hmX c.1 c.2) (hpX c.1 c.2) (hqX c.1 c.2) T ω)
    (fun i c => ((stochasticIntegralBrownian_stronglyAdapted (W.W c.2) ℱ' (hcoord c.2) _
      (hmY i c.1 c.2) (hpY i c.1 c.2) (hqY i c.1 c.2) T).mono (ℱ'.le T)).measurable)
    (fun c => ((stochasticIntegralBrownian_stronglyAdapted (W.W c.2) ℱ' (hcoord c.2) _
      (hmX c.1 c.2) (hpX c.1 c.2) (hqX c.1 c.2) T).mono (ℱ'.le T)).measurable)
    (fun c => tendsto_lintegral_sq_norm_stochInt_clamp W ℱ' hcoord hf'c hK₁0 hf'bd hm hT hq
      hYm hXm hge hae hmY hpY hqY hmX hpX hqX c.1 c.2)
  refine ⟨ms, hmsge, ?_⟩
  filter_upwards [hms] with ω hω
  intro p k
  exact hω (p, k)
end Limits

end Clamped

end LevyStochCalc.Brownian.Ito


