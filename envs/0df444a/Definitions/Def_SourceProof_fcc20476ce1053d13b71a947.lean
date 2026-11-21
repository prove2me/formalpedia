-- Prove2me | Definitions.Def_SourceProof_fcc20476ce1053d13b71a947
-- name    : SourceProof_fcc20476ce1053d13b71a947
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:19:01.426697+00:00
-- url     : https://prove2.me/theorems/8eedceee-e079-41ce-9f20-49f6593a0d8e
-- title:
--   LevyStochCalc source module: SourceProof_fcc20476ce1053d13b71a947
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.setIntegral_exp_mul_setIntegral` comes from the `LevyStochCalc.Ito.SecondMomentWeighted` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentWeighted_F000

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


theorem _root_.Prove2MeSourceProof.h_fcc20476ce1053d13b71a947 {g : ℝ → ℝ} {T : ℝ}
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) T)) (β : ℝ) :
    ∫ s in Set.Icc (0 : ℝ) T, β * Real.exp (β * s) * ∫ r in Set.Icc (0 : ℝ) s, g r
      = Real.exp (β * T) * (∫ r in Set.Icc (0 : ℝ) T, g r)
        - ∫ r in Set.Icc (0 : ℝ) T, Real.exp (β * r) * g r := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  have hwi : IntegrableOn (fun s : ℝ => β * Real.exp (β * s)) (Set.Icc (0 : ℝ) T) :=
    (by fun_prop : Continuous fun s : ℝ => β * Real.exp (β * s)).integrableOn_Icc
  have hprod : Integrable (fun p : ℝ × ℝ => g p.1 * (β * Real.exp (β * p.2))) (μ.prod μ) :=
    hg.mul_prod hwi
  set F : ℝ × ℝ → ℝ :=
    {p : ℝ × ℝ | p.1 ≤ p.2}.indicator fun p => g p.1 * (β * Real.exp (β * p.2)) with hF
  have hle : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hFint : Integrable F (μ.prod μ) := hprod.indicator hle
  -- sliced at the second coordinate: the running integral against the weight
  have hinner : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ r, F (r, s) ∂μ = (∫ r in Set.Icc (0 : ℝ) s, g r) * (β * Real.exp (β * s)) := by
    intro s hs
    have h1 : (fun r => F (r, s))
        = fun r => (Set.Iic s).indicator (fun r => g r * (β * Real.exp (β * s))) r := by
      funext r
      simp only [hF, Set.indicator, Set.mem_setOf_eq, Set.mem_Iic]
    have hset : Set.Iic s ∩ Set.Icc (0 : ℝ) T = Set.Icc (0 : ℝ) s := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, h2, h1.trans hs.2⟩
    rw [h1, integral_indicator measurableSet_Iic, integral_mul_const, hμ,
      Measure.restrict_restrict measurableSet_Iic, hset]
  have hFeq : ∫ p, F p ∂(μ.prod μ)
      = ∫ s in Set.Icc (0 : ℝ) T, (∫ r in Set.Icc (0 : ℝ) s, g r) * (β * Real.exp (β * s)) := by
    rw [integral_prod_symm F hFint]
    exact setIntegral_congr_fun measurableSet_Icc fun s hs => hinner s hs
  -- sliced at the first coordinate: the weight integrated from `r` to `T`
  have hinner' : ∀ r ∈ Set.Icc (0 : ℝ) T,
      ∫ s, F (r, s) ∂μ = g r * (Real.exp (β * T) - Real.exp (β * r)) := by
    intro r hr
    have h1 : (fun s => F (r, s))
        = fun s => (Set.Ici r).indicator (fun s => g r * (β * Real.exp (β * s))) s := by
      funext s
      simp only [hF, Set.indicator, Set.mem_setOf_eq, Set.mem_Ici]
    have hset : Set.Ici r ∩ Set.Icc (0 : ℝ) T = Set.Icc r T := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, hr.1.trans h1, h3⟩
    rw [h1, integral_indicator measurableSet_Ici, integral_const_mul, hμ,
      Measure.restrict_restrict measurableSet_Ici, hset, LevyStochCalc.Ito.SecondMoment.setIntegral_mul_exp_mul β hr.2]
  have hFeq' : ∫ p, F p ∂(μ.prod μ)
      = ∫ r in Set.Icc (0 : ℝ) T, g r * (Real.exp (β * T) - Real.exp (β * r)) := by
    rw [integral_prod F hFint]
    exact setIntegral_congr_fun measurableSet_Icc fun r hr => hinner' r hr
  have hge : IntegrableOn (fun r => g r * Real.exp (β * r)) (Set.Icc (0 : ℝ) T) :=
    hg.mul_continuousOn (by fun_prop : Continuous fun r : ℝ => Real.exp (β * r)).continuousOn
      isCompact_Icc
  calc ∫ s in Set.Icc (0 : ℝ) T, β * Real.exp (β * s) * ∫ r in Set.Icc (0 : ℝ) s, g r
      = ∫ s in Set.Icc (0 : ℝ) T, (∫ r in Set.Icc (0 : ℝ) s, g r) * (β * Real.exp (β * s)) :=
        setIntegral_congr_fun measurableSet_Icc fun s _ => mul_comm _ _
    _ = ∫ r in Set.Icc (0 : ℝ) T, g r * (Real.exp (β * T) - Real.exp (β * r)) := by
        rw [← hFeq, hFeq']
    _ = Real.exp (β * T) * (∫ r in Set.Icc (0 : ℝ) T, g r)
        - ∫ r in Set.Icc (0 : ℝ) T, Real.exp (β * r) * g r := by
        have e : (fun r => g r * (Real.exp (β * T) - Real.exp (β * r)))
            = fun r => Real.exp (β * T) * g r - g r * Real.exp (β * r) := by
          funext r
          ring
        rw [e, integral_sub (hg.const_mul _) hge, integral_const_mul]
        congr 1
        exact setIntegral_congr_fun measurableSet_Icc fun r _ => mul_comm _ _
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

end WeightedVector

section AugmentedMore

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

end AugmentedMore

end LevyStochCalc.Ito.SecondMoment


