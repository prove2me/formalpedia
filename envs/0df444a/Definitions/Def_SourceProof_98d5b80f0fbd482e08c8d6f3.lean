-- Prove2me | Definitions.Def_SourceProof_98d5b80f0fbd482e08c8d6f3
-- name    : SourceProof_98d5b80f0fbd482e08c8d6f3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:40:34.819077+00:00
-- url     : https://prove2.me/theorems/11cc5a11-1597-4cfe-b32d-1d7e3d6917f4
-- title:
--   LevyStochCalc source module: SourceProof_98d5b80f0fbd482e08c8d6f3
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.isPoissonFiltration` comes from the `LevyStochCalc.Driver.Joint` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Joint_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint filtration of an independent Brownian motion and Poisson random measure

A `LevyDriver` is a `d`-dimensional Brownian motion `W` and a Poisson random measure `N` on one
probability space, with `σ(W)` independent of `σ(N)`. Its joint natural filtration
`(⨆ i, ℱ^{Wⁱ}) ⊔ ℱ^N` is one for which every coordinate `Wⁱ` is a Brownian motion and `N` a
Poisson random measure (`LevyDriver.isBrownianFiltration`, `LevyDriver.isPoissonFiltration`):
the increments of `Wⁱ` after `s` are independent of `ℱ^{Wⁱ} s`, and the rest of the joint
filtration at time `s` is independent of `σ(Wⁱ)` altogether, so the join stays independent
(`indep_sup_left_of_indep`); likewise for the future counts of `N`.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)


theorem _root_.Prove2MeSourceProof.h_98d5b80f0fbd482e08c8d6f3 : Poisson.IsPoissonFiltration D.N D.filtration where
  measurable _ _ hB hBm :=
    ((LevyStochCalc.Poisson.isPoissonFiltration_natural D.N).measurable hB hBm).mono
      (D.naturalFiltration_poisson_le _) le_rfl
  indep_future := by
    intro s hs
    rw [LevyStochCalc.Driver.LevyDriver.filtration_apply, sup_comm]
    have hfut : (⨆ B ∈ {B : Set (ℝ × E) | B ⊆ Set.Ioi s ×ˢ Set.univ ∧ MeasurableSet B},
        MeasurableSpace.comap (fun ω => D.N.N ω B) inferInstance) ≤ LevyStochCalc.Driver.sigmaPoisson D.N :=
      iSup₂_le fun B hB => LevyStochCalc.Driver.comap_count_le_sigmaPoisson D.N hB.2
    refine _root_.Prove2MeSourceProof.h_fa5eb32f3be3b75875b08ef5
      ((LevyStochCalc.Driver.naturalFiltration_le_sigmaPoisson _ s).trans (LevyStochCalc.Driver.sigmaPoisson_le _))
      (D.W.naturalFiltration.le s) (hfut.trans (LevyStochCalc.Driver.sigmaPoisson_le _))
      ((LevyStochCalc.Poisson.isPoissonFiltration_natural D.N).indep_future hs) ?_
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left D.indep (D.W.naturalFiltration_le_iSup_sigmaBrownian s))
      (sup_le (LevyStochCalc.Driver.naturalFiltration_le_sigmaPoisson _ s) hfut)
end LevyDriver

end LevyStochCalc.Driver


