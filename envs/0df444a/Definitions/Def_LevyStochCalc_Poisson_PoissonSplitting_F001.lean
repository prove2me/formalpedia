-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F001
-- name    : LevyStochCalc_Poisson_PoissonSplitting_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:18:47.284527+00:00
-- url     : https://prove2.me/theorems/be82276a-e136-4bcb-8f26-8bf8deae84a9
-- title:
--   Source declarations: LevyStochCalc.Poisson.PoissonSplitting
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.PoissonSplitting. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PoissonSplitting_F000

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

section CharFun

variable {n : ℕ} (B : Fin n → Set 𝓧) (t : Fin n → ℝ)

variable {B t}

omit [IsProbabilityMeasure P] [IsProbabilityMeasure ρ] in
/-- For independent marks with common law `ρ`, the expectation of the product of the first `m`
mark phases is the `m`-th power of the integral of the phase. -/
lemma integral_prod_markPhase (hB : ∀ i, MeasurableSet (B i)) (hX : ∀ j, HasLaw (X j) ρ P)
    (mX : ∀ j, Measurable (X j)) (hXi : iIndepFun X P) (m : ℕ) :
    ∫ ω, ∏ j ∈ Finset.range m, markPhase B t (X j ω) ∂P = (∫ x, markPhase B t x ∂ρ) ^ m := by
  have hg := markPhase_measurable B t hB
  have hind : iIndepFun (fun j : Fin m => fun ω => markPhase B t (X j ω)) P :=
    (hXi.comp (fun _ => markPhase B t) (fun _ => hg)).precomp Fin.val_injective
  have h := hind.integral_fun_prod_eq_prod_integral
    (fun j => (hg.comp (mX j)).aestronglyMeasurable)
  have hone : ∀ j : Fin m, ∫ ω, markPhase B t (X j ω) ∂P = ∫ x, markPhase B t x ∂ρ := by
    intro j
    rw [← (hX j).map_eq, integral_map (mX j).aemeasurable hg.aestronglyMeasurable]
  calc ∫ ω, ∏ j ∈ Finset.range m, markPhase B t (X j ω) ∂P
      = ∫ ω, ∏ j : Fin m, markPhase B t (X j ω) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        exact (Fin.prod_univ_eq_prod_range (fun j => markPhase B t (X j ω)) m).symm
    _ = ∏ j : Fin m, ∫ ω, markPhase B t (X j ω) ∂P := h
    _ = (∫ x, markPhase B t x ∂ρ) ^ m := by
        rw [Finset.prod_congr rfl fun j _ => hone j, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
end CharFun

section Law

variable {n : ℕ} {B : Fin n → Set 𝓧}

end Law

end LevyStochCalc.Poisson


