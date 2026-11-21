-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F002
-- name    : LevyStochCalc_Ito_SecondMomentWeighted_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:02:47.092291+00:00
-- url     : https://prove2.me/theorems/9e8d94dc-4fe1-4799-b24a-86a870cf3133
-- title:
--   Source declarations: LevyStochCalc.Ito.SecondMomentWeighted
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SecondMomentWeighted. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CrossElementary_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000
import Definitions.Def_SourceProof_0122a571e95691a0e466a41c
import Definitions.Def_SourceProof_0148088f6982519d0fc05ef5
import Definitions.Def_SourceProof_6dd322ce0bda402186214738
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The exponentially weighted second moment of an Itô–Lévy process

The map `t ↦ 𝔼[X_t²]` is the initial value plus the time integral of the rate
`2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)`, so integration by parts against the
weight `e^{βs}` gives

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`,

the form in which the a-priori estimates for BSDEs with jumps read the quadratic formula. The
weighting of an absolutely continuous function by an exponential is isolated first, as a real
identity. The vector form follows coordinatewise, and the cross witness carried by the driver
gives the bilinear and the weighted forms over its augmented joint natural filtration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Weight

/-! ### The exponential weight: integration by parts against `e^{βs}` -/

end Weight

section Weighted

/-! ### The exponentially weighted second moment -/

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end Weighted

section WeightedVector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

/-- **The exponentially weighted second moment of a vector Itô–Lévy process**, coordinate by
coordinate: the weighted expected squared norm at the horizon is the sum of the weighted scalar
identities of the coordinates. -/
theorem integral_exp_mul_sum_mul_self_eq_of_isItoLevyProcess
    (h : ∀ i, LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN (X i) (X₀ i) (b i)
      (σ i) (γ i))
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : ∀ i, StronglyMeasurable[ℱ 0] (X₀ i)) (hX₀2 : ∀ i, MemLp (X₀ i) 2 P)
    (hbm : ∀ i, Measurable (Function.uncurry fun ω s => b i s ω))
    (hbp : ∀ i, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b i s ω)
    (hbq : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b i s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (β : ℝ) {T : ℝ} (hT : 0 < T) :
    Real.exp (β * T) * ∫ ω, ∑ i, X i T ω * X i T ω ∂P
      = ∑ i, (∫ ω, X₀ i ω * X₀ i ω ∂P
        + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
            * (β * ∫ ω, X i s ω * X i s ω ∂P + 2 * ∫ ω, X i s ω * b i s ω ∂P
              + (∑ j : Fin d, (∫⁻ ω, (‖σ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
              + (∫⁻ ω, ∫⁻ e, (‖γ i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)) := by
  have hX2 : ∀ i, MemLp (X i T) 2 P := fun i =>
    _root_.Prove2MeSourceProof.h_0122a571e95691a0e466a41c (h i) (hX₀2 i) (hbm i) (hbq i) hT.le
  have hint : ∀ i, Integrable (fun ω => X i T ω * X i T ω) P := fun i =>
    (hX2 i).integrable_mul (hX2 i)
  rw [integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    _root_.Prove2MeSourceProof.h_0148088f6982519d0fc05ef5 (h i) 𝒲 (hX₀ i) (hX₀2 i) (hbm i) (hbp i)
      (hbq i) β hT
end WeightedVector

section AugmentedMore

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

/-- The bilinear second moment of two Itô–Lévy processes over the augmented joint natural
filtration of the driver, where the driver itself supplies the cross witness. -/
theorem integral_mul_eq_of_isItoLevyProcess_aug
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N
      (LevyStochCalc.Brownian.augFiltration D.filtration P) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug X X₀ b σ γ)
    {Y : ℝ → Ω → ℝ} {Y₀ : Ω → ℝ} {b' : ℝ → Ω → ℝ} {σ' : ℝ → Ω → Fin d → ℝ}
    {γ' : Ω → ℝ → E → ℝ}
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N
      (LevyStochCalc.Brownian.augFiltration D.filtration P) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug Y Y₀ b' σ' γ')
    (hX₀ : StronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P 0] X₀)
    (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable
      (LevyStochCalc.Brownian.augFiltration D.filtration P) fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hY₀ : StronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P 0] Y₀)
    (hY₀2 : MemLp Y₀ 2 P)
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hb'p : LevyStochCalc.Probability.ProgressivelyMeasurable
      (LevyStochCalc.Brownian.augFiltration D.filtration P) fun ω s => b' s ω)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, X T ω * Y T ω ∂P
      = ∫ ω, X₀ ω * Y₀ ω ∂P
        + (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b' s ω + Y s ω * b s ω ∂P)
        + (∑ j : Fin d, ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, σ s ω j * σ' s ω j ∂volume ∂P)
        + ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, γ ω s e * γ' ω s e ∂ν ∂volume ∂P :=
  _root_.Prove2MeSourceProof.h_6dd322ce0bda402186214738 h h' D.crossWitness.aug hX₀ hX₀2 hbm hbp hbq hY₀ hY₀2
    hb'm hb'p hb'q hT
/-- The exponentially weighted second moment of an Itô–Lévy process over the augmented joint
natural filtration of the driver, where the driver itself supplies the cross witness. -/
theorem integral_exp_mul_self_eq_of_isItoLevyProcess_aug
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N
      (LevyStochCalc.Brownian.augFiltration D.filtration P) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug X X₀ b σ γ)
    (hX₀ : StronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P 0] X₀)
    (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable
      (LevyStochCalc.Brownian.augFiltration D.filtration P) fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (β : ℝ) {T : ℝ} (hT : 0 < T) :
    Real.exp (β * T) * ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, X₀ ω * X₀ ω ∂P
        + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
            * (β * ∫ ω, X s ω * X s ω ∂P + 2 * ∫ ω, X s ω * b s ω ∂P
              + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
              + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) :=
  _root_.Prove2MeSourceProof.h_0148088f6982519d0fc05ef5 h D.crossWitness.aug hX₀ hX₀2 hbm hbp hbq β hT
end AugmentedMore

end LevyStochCalc.Ito.SecondMoment


