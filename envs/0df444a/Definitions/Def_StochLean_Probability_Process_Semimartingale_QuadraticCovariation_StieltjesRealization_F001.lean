-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_StieltjesRealization_F001
-- name    : StochLean_Probability_Process_Semimartingale_QuadraticCovariation_StieltjesRealization_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:24:26.908387+00:00
-- url     : https://prove2.me/theorems/0f06216c-0460-41d1-86d3-76afb87cd473
-- title:
--   StochLean: Probability.Process.Semimartingale.QuadraticCovariation.StieltjesRealization F001

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_StieltjesRealization_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable Stieltjes realizations of the canonical raw brackets

These are null-event versions of the already constructed brackets, not another
definition of stochastic quadratic variation. All three path identifications
are indistinguishability statements. Their canonical variation/energy integrals
will therefore have measurable random versions without assumptions on moments.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace SemimartingaleBracketRealization

variable {hX : IsSemimartingale X F P} {hY : IsSemimartingale Y F P} {hF : F.IsUsual P}
  (D : SemimartingaleBracketRealization hX hY hF)

noncomputable def variation (ω : Ω) : StieltjesFunction ℝ≥0 :=
  totalVariationStieltjes (fun t ↦ D.mixed t ω) (D.mixed_bv ω) (D.mixed_rc ω)
end SemimartingaleBracketRealization

end ProbabilityTheory


