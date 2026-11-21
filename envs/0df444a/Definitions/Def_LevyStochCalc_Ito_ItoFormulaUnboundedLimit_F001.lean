-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F001
-- name    : LevyStochCalc_Ito_ItoFormulaUnboundedLimit_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:04:51.543265+00:00
-- url     : https://prove2.me/theorems/4c0772b4-13a1-4b3b-9a89-871c447efe0c
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaUnboundedLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaUnboundedLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F001
import Definitions.Def_SourceProof_ef93b78d487d6b1fdb99d88f

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

/-- **Itô's formula for a twice continuously differentiable function of a vector Itô process
with unbounded coefficients.** -/
theorem itoFormula_of_unbounded
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume :=
  (_root_.Prove2MeSourceProof.h_0db69f59829c3456e5fb46d0 h) hfC hf hf' hmg hpg hqg hT
    (fun _g _g' _g'' _K₁ _K₂ hgf hgf' hK₁ hK₂0 hK₂ hg'c hg''c hunif hmG hpG hqG =>
      _root_.Prove2MeSourceProof.h_ef93b78d487d6b1fdb99d88f W ℱ' hcoord h hℱ0 hnull hX₀ hbm hbp hbq hgf hgf'
        (le_trans (norm_nonneg _) (hK₁ 0)) hK₁ hK₂0 hK₂ hg'c hg''c hunif hmG hpG hqG hT)
end Limits

end Clamped

end LevyStochCalc.Brownian.Ito


