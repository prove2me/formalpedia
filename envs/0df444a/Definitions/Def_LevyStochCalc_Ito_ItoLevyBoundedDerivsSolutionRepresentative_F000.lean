-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F000
-- name    : LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:46:04.410575+00:00
-- url     : https://prove2.me/theorems/78ed4447-1b83-47f6-92c0-0c65ae5d01d3
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivs_F000
import Definitions.Def_LevyStochCalc_Ito_PicardWellPosed_F000
import Definitions.Def_LevyStochCalc_Ito_SdeDataOfSolvesOn_F000

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

/-- A path map replaced by the constant zero path off a set of sample points and frozen at the
zero state before time zero. -/
noncomputable def cadlagRep (G : Set Ω) (X : ℝ → Ω → Fin n → ℝ) (s : ℝ) (ω : Ω) : Fin n → ℝ :=
  (Set.Ici (0 : ℝ)).indicator (fun r => repairOn G X r ω) s
variable {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}

omit [MeasurableSpace Ω] in
theorem cadlagRep_of_nonneg {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    cadlagRep G X s ω = repairOn G X s ω :=
  Set.indicator_of_mem (Set.mem_Ici.mpr hs) _
omit [MeasurableSpace Ω] in
theorem cadlagRep_of_neg {s : ℝ} (hs : s < 0) (ω : Ω) : cadlagRep G X s ω = 0 :=
  Set.indicator_of_notMem (fun h => absurd (Set.mem_Ici.mp h) (not_le.mpr hs)) _
omit [MeasurableSpace Ω] in
/-- On the good set and at nonnegative times the representative is the original path. -/
theorem cadlagRep_eq_of_mem {s : ℝ} (hs : 0 ≤ s) {ω : Ω} (hω : ω ∈ G) :
    cadlagRep G X s ω = X s ω := by
  rw [cadlagRep_of_nonneg hs, repairOn_of_mem hω]
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


