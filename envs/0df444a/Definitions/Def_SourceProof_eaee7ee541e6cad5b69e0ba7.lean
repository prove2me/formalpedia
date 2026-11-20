-- Prove2me | Definitions.Def_SourceProof_eaee7ee541e6cad5b69e0ba7
-- name    : SourceProof_eaee7ee541e6cad5b69e0ba7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:57:30.11276+00:00
-- url     : https://prove2.me/theorems/43ac357f-5478-4266-b4ea-373f085b1266
-- title:
--   LevyStochCalc source module: SourceProof_eaee7ee541e6cad5b69e0ba7
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.iIndepFun_superposition` comes from the `LevyStochCalc.Poisson.PoissonSuperposition` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_PoissonSuperposition_F000

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


theorem _root_.Prove2MeSourceProof.h_eaee7ee541e6cad5b69e0ba7 {ι' : Type*} {B : ι' → Set 𝓧} (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) :
    iIndepFun (fun i ω => superposition ω (B i)) (superLaw r ρ) := by
  set Y : ι → ι' → (ι → LevyStochCalc.Poisson.PieceSpace 𝓧) → ℝ≥0∞ :=
    fun p i ω => (LevyStochCalc.Poisson.pieceCountOn (B i) (ω p) : ℝ≥0∞) with hY
  have hm : ∀ p i, Measurable (Y p i) := fun p i => LevyStochCalc.Poisson.measurable_pieceCountOn_eval p (hB i)
  have h1 : iIndepFun (fun p ω i => Y p i ω) (LevyStochCalc.Poisson.superLaw r ρ) :=
    (LevyStochCalc.Poisson.iIndepFun_eval r ρ).comp (fun _ θ i => (LevyStochCalc.Poisson.pieceCountOn (B i) θ : ℝ≥0∞)) fun _ =>
      measurable_pi_lambda _ fun i => (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ≥0∞))).comp
        (LevyStochCalc.Poisson.measurable_pieceCountOn (hB i))
  have h2 : ∀ p, iIndepFun (fun i => Y p i) (LevyStochCalc.Poisson.superLaw r ρ) := fun p =>
    LevyStochCalc.Poisson.iIndepFun_pieceCountOn_ennreal r ρ p hB hdisj
  have heq : (fun (i : ι') (ω : ι → LevyStochCalc.Poisson.PieceSpace 𝓧) => LevyStochCalc.Poisson.superposition ω (B i))
      = fun i => (fun v : ι → ℝ≥0∞ => ∑' p, v p) ∘ fun ω p => Y p i ω := by
    funext i ω
    rw [LevyStochCalc.Poisson.superposition_apply ω (hB i)]
    rfl
  clear_value Y
  have h3 : iIndepFun (fun q : ι × ι' => Y q.1 q.2) (LevyStochCalc.Poisson.superLaw r ρ) := iIndepFun_uncurry' hm h1 h2
  have h4 : iIndepFun (fun i ω p => Y p i ω) (LevyStochCalc.Poisson.superLaw r ρ) :=
    LevyStochCalc.Probability.iIndepFun_fiber (𝓧 := fun _ => ℝ≥0∞) (fun q => hm q.1 q.2) h3
  have h5 : iIndepFun (fun i => (fun v : ι → ℝ≥0∞ => ∑' p, v p) ∘ fun ω p => Y p i ω)
      (LevyStochCalc.Poisson.superLaw r ρ) :=
    h4.comp _ fun _ => Measurable.tsum fun p => measurable_pi_apply p
  rw [heq]
  exact h5
end Law

end LevyStochCalc.Poisson


