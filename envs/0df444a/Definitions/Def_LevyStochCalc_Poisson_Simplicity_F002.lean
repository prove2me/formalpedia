-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_Simplicity_F002
-- name    : LevyStochCalc_Poisson_Simplicity_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:54:18.215823+00:00
-- url     : https://prove2.me/theorems/20c5a8c9-210e-4f68-a523-fb8344fd754f
-- title:
--   Source declarations: LevyStochCalc.Poisson.Simplicity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.Simplicity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F001
import Definitions.Def_SourceProof_b53022bf4ec47748c83ffa9f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Time-simplicity of a Poisson random measure on a finite-intensity set

On a set of finite reference intensity the count of a Poisson random measure exceeds one with
probability at most the square of the intensity. The reference intensity is a product with
Lebesgue measure in time, so the masses of the dyadic time slabs of such a set are the integrals
of an integrable density over intervals of vanishing length, and therefore have vanishing
supremum. A union bound then makes the probability that some slab of level `n` carries two or
more points tend to zero, so almost surely no two points share a time and every point is simple.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Tail

end Tail

section Mesh

end Mesh

section Simple

theorem lintegral_sectionDensity {B : Set (ℝ × E)} (hB : MeasurableSet B) :
    ∫⁻ x, sectionDensity ν B x = referenceIntensity ν B := by
  rw [← setLIntegral_univ, ← _root_.Prove2MeSourceProof.h_b53022bf4ec47748c83ffa9f hB MeasurableSet.univ,
    Set.univ_prod_univ, Set.inter_univ]
end Simple

end LevyStochCalc.Poisson


