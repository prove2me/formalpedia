-- Prove2me | Definitions.Def_StochLean_Probability_Process_FiniteVariation_IntegrableAlgebra_F000
-- name    : StochLean_Probability_Process_FiniteVariation_IntegrableAlgebra_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:02.167812+00:00
-- url     : https://prove2.me/theorems/868ea800-032c-4436-be09-a163572cf370
-- title:
--   StochLean: Probability.Process.FiniteVariation.IntegrableAlgebra F000

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F000
import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Integrable_F001
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of integrable variation

Negation and real constant multiplication have exact extended-variation
formulas, so they preserve integrable variation without process measurability
or path regularity assumptions. The zero scalar is included.

For sums, variation domination alone does not establish measurability of the
actual total variation. The basic result therefore explicitly requires its
almost-everywhere measurability. Adapted cadlag processes on a usual filtration
provide this hypothesis through the existing whole-half-line variation owner.
The subtraction results use the same argument and exact negation invariance.

Initial values remain arbitrary: no initial integrability or zero initial
condition is assumed. Extended variation is proved finite before converting
its order bounds to real values.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → ℝ}

private theorem eVariationOn_const_mul_path (c : ℝ) (x : ℝ≥0 → ℝ) :
    eVariationOn (fun t ↦ c * x t) univ = ENNReal.ofReal |c| * eVariationOn x univ := by
  have he (a b : ℝ) : edist (c * a) (c * b) = ENNReal.ofReal |c| * edist a b := by
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
      ENNReal.ofReal_mul (abs_nonneg c)]
  simp only [eVariationOn, he, ← Finset.mul_sum, ← ENNReal.mul_iSup]
variable {F : Filtration ℝ≥0 mΩ}

end ProbabilityTheory


