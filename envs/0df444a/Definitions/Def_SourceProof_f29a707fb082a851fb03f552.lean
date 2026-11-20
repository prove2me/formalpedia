-- Prove2me | Definitions.Def_SourceProof_f29a707fb082a851fb03f552
-- name    : SourceProof_f29a707fb082a851fb03f552
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:05:23.438017+00:00
-- url     : https://prove2.me/theorems/5e371595-73b9-4a51-beb8-82e7adf52c96
-- title:
--   LevyStochCalc source module: SourceProof_f29a707fb082a851fb03f552
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_exists_nat_superposition` comes from the `LevyStochCalc.Poisson.PoissonSuperposition` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PoissonSuperposition_F000
import Definitions.Def_SourceProof_c2748d972d70936ce8379f88

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Superposition of independent Poisson pieces

Given weights `r p ≥ 0` and probability laws `ρ p` on a measurable space `𝓧`, indexed by a
countable type, the *superposition* is the random measure `N = ∑ₚ Nₚ` where the pieces
`Nₚ = ∑_{j < Kₚ} δ_{X_{p,j}}` are independent, `Kₚ` is Poisson with mean `r p`, and the marks
`X_{p,j}` are independent with law `ρ p`. Its intensity is `Λ = ∑ₚ r p • ρ p`.

The sample space is the product `ι → ULift ℕ × (ℕ → 𝓧)` with the product law, and the
distributional facts about a single piece reduce to Poisson splitting.
-/

open MeasureTheory ProbabilityTheory Complex Filter Function Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u

section Piece

variable {𝓧 : Type u} [MeasurableSpace 𝓧]

variable {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧) [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable {r ρ}

variable (r ρ)

variable [Countable ι]

end Piece

section Exhaustion

end Exhaustion

section Law

variable {𝓧 : Type u} [MeasurableSpace 𝓧] {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧)
  [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable [Countable ι]


theorem _root_.Prove2MeSourceProof.h_f29a707fb082a851fb03f552 {B : Set 𝓧} (hB : MeasurableSet B)
    (hfin : superIntensity r ρ B ≠ ⊤) :
    ∀ᵐ ω ∂(superLaw r ρ), ∃ n : ℕ, superposition ω B = n := by
  have hmeas : MeasurableSet (Set.range (Nat.cast : ℕ → ℝ≥0∞)) :=
    (Set.countable_range _).measurableSet
  have h : (LevyStochCalc.Poisson.superLaw r ρ)
      ((fun ω => LevyStochCalc.Poisson.superposition ω B) ⁻¹' (Set.range (Nat.cast : ℕ → ℝ≥0∞))ᶜ) = 0 := by
    rw [← Measure.map_apply (LevyStochCalc.Poisson.measurable_superposition hB) hmeas.compl,
      _root_.Prove2MeSourceProof.h_c2748d972d70936ce8379f88 r ρ hB hfin, Measure.map_apply Measurable.of_discrete hmeas.compl]
    have : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' (Set.range (Nat.cast : ℕ → ℝ≥0∞))ᶜ = ∅ := by
      ext n
      simp
    rw [this, measure_empty]
  rw [ae_iff]
  convert h using 2
  ext ω
  simp [eq_comm]
end Law

end LevyStochCalc.Poisson


