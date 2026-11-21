-- Prove2me | Definitions.Def_SourceProof_194396c8b70b364460393af6
-- name    : SourceProof_194396c8b70b364460393af6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:32:01.095952+00:00
-- url     : https://prove2.me/theorems/d78572a2-f67f-4695-8c24-077660cd969e
-- title:
--   LevyStochCalc source module: SourceProof_194396c8b70b364460393af6
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.aestronglyMeasurable_vectorIntegral` comes from the `LevyStochCalc.Brownian.PRPMultidimRange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPMultidimRange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The closed range of the multidimensional Brownian Itô integral

The multidimensional Itô integral is the sum over the coordinates of the scalar integrals, so its
range in `L²` is the supremum of the scalar ranges. Those are closed, and orthogonal to one
another, so the supremum is closed: a point of its closure is the sum of its orthogonal
projections, each of which lies in the corresponding scalar range. The orthogonal decomposition
along the supremum then represents every square-integrable weight of mean zero, measurable before
the horizon, as a sum of coordinate Itô integrals, given the separation hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

open LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

section Range

variable (W : MultidimBrownianMotion P d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

theorem _root_.Prove2MeSourceProof.h_194396c8b70b364460393af6 (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) :
    AEStronglyMeasurable[ℱ T] (vectorIntegral W hcoord G) P := by
  set F : Fin d → Ω → ℝ := fun i => (G i).integral (W.W i) (hcoord i) with hF
  have hcomp : ∀ i : Fin d, AEStronglyMeasurable[ℱ T] (F i) P := fun i =>
    LevyStochCalc.Brownian.Ito.HorizonIntegrand.aestronglyMeasurable (W.W i) (hcoord i) (G i)
  have key : ∀ s : Finset (Fin d),
      AEStronglyMeasurable[ℱ T] (fun ω => ∑ i ∈ s, F i ω) P := by
    intro s
    induction s using Finset.cons_induction with
    | empty =>
      refine ⟨fun _ => 0, stronglyMeasurable_const, ?_⟩
      filter_upwards with ω
      simp
    | cons i s hi ih =>
      have hsum : (fun ω => ∑ j ∈ Finset.cons i s hi, F j ω)
          = fun ω => F i ω + ∑ j ∈ s, F j ω := by
        funext ω
        rw [Finset.sum_cons]
      rw [hsum]
      exact (hcomp i).add ih
  have hgoal : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.vectorIntegral W hcoord G
      = fun ω => ∑ i ∈ (Finset.univ : Finset (Fin d)), F i ω := rfl
  rw [hgoal]
  exact key Finset.univ
end Range

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion


