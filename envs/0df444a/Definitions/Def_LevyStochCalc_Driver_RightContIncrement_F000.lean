-- Prove2me | Definitions.Def_LevyStochCalc_Driver_RightContIncrement_F000
-- name    : LevyStochCalc_Driver_RightContIncrement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:44:16.483832+00:00
-- url     : https://prove2.me/theorems/b9673020-2fab-4c1d-b213-4d6bddf4263d
-- title:
--   Source declarations: LevyStochCalc.Driver.RightContIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.RightContIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Joint_F000
import Definitions.Def_SourceProof_3d27237b32316a1fa19a9df4
import Definitions.Def_SourceProof_98d5b80f0fbd482e08c8d6f3
import Definitions.Def_SourceProof_cbb0fd7558e885b374c4446f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Increments of a Lévy driver against its right-continuous filtration

Each coordinate of the Brownian motion is a Brownian motion for the driver's joint filtration and
the Poisson random measure is a Poisson random measure for it, so both remain so for the
right-continuous filtration: an increment of a coordinate after a time `s ≥ 0`, and a count of the
Poisson random measure over a mark set after `s`, are independent of the σ-algebra of the
immediate future of `s`.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

/-- Every coordinate is a Brownian motion for the right-continuous joint filtration. -/
theorem isBrownianFiltration_rightCont (j : Fin d) :
    Brownian.IsBrownianFiltration (D.W.W j) D.filtration.rightCont :=
  (_root_.Prove2MeSourceProof.h_3d27237b32316a1fa19a9df4 (D.isBrownianFiltration j))
/-- The Poisson random measure is one for the right-continuous joint filtration. -/
theorem isPoissonFiltration_rightCont :
    Poisson.IsPoissonFiltration D.N D.filtration.rightCont :=
  (_root_.Prove2MeSourceProof.h_cbb0fd7558e885b374c4446f (_root_.Prove2MeSourceProof.h_98d5b80f0fbd482e08c8d6f3 D))
/-- A Brownian increment after `s` is independent of the immediate future of `s`. -/
theorem indep_increment_rightCont (j : Fin d) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    Indep (D.filtration.rightCont s)
      (MeasurableSpace.comap (fun ω => (D.W.W j).W t ω - (D.W.W j).W s ω) inferInstance) P :=
  (D.isBrownianFiltration_rightCont j).indep hs hst
/-- A Poisson count over a mark set after `s` is independent of the immediate future of `s`. -/
theorem indep_count_rightCont {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) :
    Indep (D.filtration.rightCont s)
      (MeasurableSpace.comap (fun ω => D.N.N ω (Set.Ioc s t ×ˢ A)) inferInstance) P :=
  D.isPoissonFiltration_rightCont.indep hs hst hA hAν
end LevyDriver

end LevyStochCalc.Driver


