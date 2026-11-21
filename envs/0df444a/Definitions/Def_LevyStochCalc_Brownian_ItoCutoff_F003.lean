-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F003
-- name    : LevyStochCalc_Brownian_ItoCutoff_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:57:48.422959+00:00
-- url     : https://prove2.me/theorems/64a7e1e9-48db-4e70-8d7d-12ce841ada96
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoCutoff
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoCutoff. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
import Definitions.Def_LevyStochCalc_Brownian_SmoothCutoff_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoFormula_F000
import Definitions.Def_LevyStochCalc_Probability_ExitTime_F001
import Definitions.Def_SourceProof_0db69f59829c3456e5fb46d0
import Definitions.Def_SourceProof_8e283c77eae519d37a5460ab

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a twice continuously differentiable function

Multiplying `f` by a smooth box cutoff leaves it, together with its first two derivatives,
unchanged on a cube and makes them bounded and uniformly continuous. Along a path stopped before
it leaves that cube the two functions therefore give the same integrands, and the local property
of the Itô integral transfers the stochastic terms.

## Main statements

* `LevyStochCalc.cutoffFun` — the cut-off function.
* `LevyStochCalc.fderiv_cutoffFun` — its first two derivatives agree with `f`'s on the cube.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_of_contDiff` — Itô's formula for a
  twice continuously differentiable function, with no bound on its derivatives.
-/

namespace LevyStochCalc

open scoped Topology

section Cutoff

variable {n : ℕ}

end Cutoff

namespace Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Bounded

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Bounded

section Formula

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

include hC0 hCH in
/-- **Itô's formula for a twice continuously differentiable function of a vector Itô process.**
No bound is placed on the derivatives of `f`. -/
theorem IsVectorItoVersion.itoFormula_of_contDiff
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume :=
  (_root_.Prove2MeSourceProof.h_0db69f59829c3456e5fb46d0 h) hfC hf hf' hmg hpg hqg hT
    (fun _g _g' _g'' _K₁ _K₂ hgf hgf' hK₁ hK₂0 hK₂ _hg'c hg''c hunif hmG hpG hqG =>
      (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_8e283c77eae519d37a5460ab p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hX₀ hbm hB0 hB hma hpa hqa hgf hgf' hK₁ hK₂0 hK₂ hg''c hunif
        hmG hpG hqG hT)
end Formula

end Brownian.Ito

end LevyStochCalc


