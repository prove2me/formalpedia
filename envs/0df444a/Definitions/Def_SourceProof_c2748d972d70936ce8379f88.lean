-- Prove2me | Definitions.Def_SourceProof_c2748d972d70936ce8379f88
-- name    : SourceProof_c2748d972d70936ce8379f88
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T10:59:17.602591+00:00
-- url     : https://prove2.me/theorems/2d6bf8a5-c651-4cde-8c21-adcc68552ce4
-- title:
--   LevyStochCalc source module: SourceProof_c2748d972d70936ce8379f88
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.map_superposition` comes from the `LevyStochCalc.Poisson.PoissonSuperposition` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PoissonSuperposition_F000
import Definitions.Def_SourceProof_31c73cd44d056a474cdcae67

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


theorem _root_.Prove2MeSourceProof.h_c2748d972d70936ce8379f88 {B : Set 𝓧} (hB : MeasurableSet B)
    (hfin : superIntensity r ρ B ≠ ⊤) :
    (superLaw r ρ).map (fun ω => superposition ω B)
      = Po((superIntensity r ρ B).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  have hae : (fun ω : ι → LevyStochCalc.Poisson.PieceSpace 𝓧 => LevyStochCalc.Poisson.superposition ω B)
      =ᵐ[LevyStochCalc.Poisson.superLaw r ρ] fun ω => ENNReal.ofReal (LevyStochCalc.Poisson.superposition ω B).toReal := by
    filter_upwards [LevyStochCalc.Poisson.ae_lt_top_superposition r ρ hB hfin] with ω hω
    rw [ENNReal.ofReal_toReal hω.ne]
  rw [Measure.map_congr hae,
    show (fun ω : ι → LevyStochCalc.Poisson.PieceSpace 𝓧 => ENNReal.ofReal (LevyStochCalc.Poisson.superposition ω B).toReal)
      = ENNReal.ofReal ∘ fun ω => (LevyStochCalc.Poisson.superposition ω B).toReal from rfl,
    ← Measure.map_map ENNReal.measurable_ofReal (LevyStochCalc.Poisson.measurable_superposition hB).ennreal_toReal,
    _root_.Prove2MeSourceProof.h_31c73cd44d056a474cdcae67 r ρ hB hfin,
    Measure.map_map ENNReal.measurable_ofReal Measurable.of_discrete]
  congr 1
  funext k
  simp [ENNReal.ofReal_natCast]
end Law

end LevyStochCalc.Poisson


