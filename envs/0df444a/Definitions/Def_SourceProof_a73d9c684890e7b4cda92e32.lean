-- Prove2me | Definitions.Def_SourceProof_a73d9c684890e7b4cda92e32
-- name    : SourceProof_a73d9c684890e7b4cda92e32
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:50:20.133671+00:00
-- url     : https://prove2.me/theorems/44eaecf1-bb4c-4799-8a90-9af70886bd7b
-- title:
--   LevyStochCalc source module: SourceProof_a73d9c684890e7b4cda92e32
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.measurable_uncurry_cadlagRep` comes from the `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The càdlàg representative of a solution path

The Itô–Lévy formula at bounded derivatives asks for left limits of the solution at every sample
point and every time, while the well-posedness theorem produces paths that are càdlàg only on a
measurable set `G` of full measure. `cadlagRep G X` is the path map that agrees with `X` on `G` at
nonnegative times, is the constant zero path off `G`, and is frozen at the zero state before time
zero. It is càdlàg at every sample point and every time, adapted whenever `G` belongs to the
initial σ-algebra, progressively measurable because it is right-continuous everywhere, and solves
the equation on every window, because both stochastic integrals depend only on the class of their
integrand.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section CadlagRep

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

variable {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}


theorem _root_.Prove2MeSourceProof.h_a73d9c684890e7b4cda92e32 (hGm : MeasurableSet G)
    (hX : Measurable (Function.uncurry X)) :
    Measurable (Function.uncurry (cadlagRep G X)) := by
  have hrep := LevyStochCalc.Ito.JumpFormula.measurable_uncurry_repairOn hGm hX
  have heq : Function.uncurry (LevyStochCalc.Ito.JumpFormula.cadlagRep G X)
      = {q : ℝ × Ω | 0 ≤ q.1}.indicator (Function.uncurry (LevyStochCalc.Ito.JumpFormula.repairOn G X)) := by
    funext q
    by_cases hq : 0 ≤ q.1
    · change LevyStochCalc.Ito.JumpFormula.cadlagRep G X q.1 q.2 = _
      rw [LevyStochCalc.Ito.JumpFormula.cadlagRep_of_nonneg hq, Set.indicator_of_mem (show q ∈ {q : ℝ × Ω | 0 ≤ q.1} from hq)]
      rfl
    · change LevyStochCalc.Ito.JumpFormula.cadlagRep G X q.1 q.2 = _
      rw [LevyStochCalc.Ito.JumpFormula.cadlagRep_of_neg (not_le.mp hq),
        Set.indicator_of_notMem (show q ∉ {q : ℝ × Ω | 0 ≤ q.1} from hq)]
  rw [heq]
  exact hrep.indicator (measurableSet_le measurable_const measurable_fst)
variable (hGp : ∀ ω ∈ G, ∀ t : ℝ, 0 ≤ t →
  Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
    ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))

end CadlagRep

section Representative

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (coeffs : JumpDiffusionCoeffs n d E) {x₀ : Fin n → ℝ}
  {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}

end Representative

end LevyStochCalc.Ito.JumpFormula


