-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F000
-- name    : LevyStochCalc_Poisson_PoissonSplitting_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:59:53.018335+00:00
-- url     : https://prove2.me/theorems/5dc49760-74ef-4695-996c-9d708cb2501a
-- title:
--   Source declarations: LevyStochCalc.Poisson.PoissonSplitting
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Poisson.PoissonSplitting, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Poisson splitting

A Poisson number `K` of independent marks `X₀, X₁, …` with common law `ρ`, independent of `K`,
scattered over pairwise disjoint measurable sets `B₁, …, Bₙ`: the counts
`Nᵢ = ∑_{j < K} 1_{Bᵢ}(Xⱼ)` are independent, and `Nᵢ` is Poisson with mean `r ρ(Bᵢ)`.

The joint characteristic function is computed by conditioning on `K`: given `K = m`, the
marks are independent, so `𝔼 exp(i ∑ᵢ tᵢ Nᵢ) = ∑ₘ P(K = m) cₘ` with
`c = ∑ᵢ ρ(Bᵢ) e^{i tᵢ} + (1 − ∑ᵢ ρ(Bᵢ))`, and the exponential series gives
`exp(r (c − 1)) = ∏ᵢ exp(r ρ(Bᵢ) (e^{i tᵢ} − 1))`, the characteristic function of the product of
the Poisson laws.
-/

open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ρ : Measure 𝓧} [IsProbabilityMeasure ρ]
  {K : Ω → ℕ} {X : ℕ → Ω → 𝓧} {r : ℝ≥0}

/-- The number of the first `K` marks that fall in `B`. -/
noncomputable def markCount (K : Ω → ℕ) (X : ℕ → Ω → 𝓧) (B : Set 𝓧) (ω : Ω) : ℕ :=
  ∑ j ∈ Finset.range (K ω), B.indicator (1 : 𝓧 → ℕ) (X j ω)
lemma markCount_measurable (mK : Measurable K) (mX : ∀ j, Measurable (X j)) {B : Set 𝓧}
    (hB : MeasurableSet B) : Measurable (markCount K X B) := by
  have h : Measurable
      (fun p : Ω × ℕ => ∑ j ∈ Finset.range p.2, B.indicator (1 : 𝓧 → ℕ) (X j p.1)) := by
    refine measurable_from_prod_countable_left fun m => ?_
    change Measurable fun ω : Ω => ∑ j ∈ Finset.range m, B.indicator (1 : 𝓧 → ℕ) (X j ω)
    exact Finset.measurable_sum _ fun j _ => (measurable_one.indicator hB).comp (mX j)
  exact h.comp (measurable_id.prodMk mK)
lemma markCount_cast_real (B : Set 𝓧) (ω : Ω) :
    (markCount K X B ω : ℝ) = ∑ j ∈ Finset.range (K ω), B.indicator (1 : 𝓧 → ℝ) (X j ω) := by
  unfold markCount
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : X j ω ∈ B <;> simp [h]
lemma markCount_measurable_real (mK : Measurable K) (mX : ∀ j, Measurable (X j)) {B : Set 𝓧}
    (hB : MeasurableSet B) : Measurable (fun ω => (markCount K X B ω : ℝ)) :=
  (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (markCount_measurable mK mX hB)
section CharFun

variable {n : ℕ} (B : Fin n → Set 𝓧) (t : Fin n → ℝ)

/-- The factor contributed by one mark to the joint characteristic function of the counts. -/
noncomputable def markPhase (x : 𝓧) : ℂ :=
  exp ((∑ i, t i * (B i).indicator (1 : 𝓧 → ℝ) x : ℝ) * I)
lemma markPhase_measurable (hB : ∀ i, MeasurableSet (B i)) : Measurable (markPhase B t) := by
  unfold markPhase
  refine Complex.measurable_exp.comp (Measurable.mul_const ?_ I)
  refine Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ => ?_)
  exact measurable_const.mul (measurable_const.indicator (hB i))
lemma norm_markPhase (x : 𝓧) : ‖markPhase B t x‖ = 1 := by
  unfold markPhase
  rw [Complex.norm_exp_ofReal_mul_I]
/-- The exponential of the joint phase of the counts is the product of the mark phases. -/
lemma exp_sum_markCount (ω : Ω) :
    exp ((∑ i, (markCount K X (B i) ω : ℝ) * t i : ℝ) * I)
      = ∏ j ∈ Finset.range (K ω), markPhase B t (X j ω) := by
  have hreal : (∑ i, (markCount K X (B i) ω : ℝ) * t i)
      = ∑ j ∈ Finset.range (K ω), ∑ i, t i * (B i).indicator (1 : 𝓧 → ℝ) (X j ω) := by
    simp_rw [markCount_cast_real, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
  unfold markPhase
  rw [← Complex.exp_sum]
  congr 1
  rw [hreal]
  push_cast
  rw [Finset.sum_mul]
variable {B t}

end CharFun

section Law

variable {n : ℕ} {B : Fin n → Set 𝓧}

end Law

end LevyStochCalc.Poisson


