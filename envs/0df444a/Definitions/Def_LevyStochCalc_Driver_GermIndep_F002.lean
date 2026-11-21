-- Prove2me | Definitions.Def_LevyStochCalc_Driver_GermIndep_F002
-- name    : LevyStochCalc_Driver_GermIndep_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:46:14.54787+00:00
-- url     : https://prove2.me/theorems/2729f41d-eaf0-4d25-872e-bdb5602d400a
-- title:
--   Source declarations: LevyStochCalc.Driver.GermIndep
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.GermIndep. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_ValueSigma_F000
import Definitions.Def_LevyStochCalc_Poisson_ZeroIntensity_F000
import Definitions.Def_SourceProof_4056caec4402ab97b0c897e1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The germ field of a Lévy driver

`Driver/ValueSigma.lean` gives the independence of `ℱ₊ 0` from the driver's data along a strictly
increasing grid of positive times. An arbitrary finite family of positive times is put in that
form by sorting it (`gridOf`), which turns the statement into one about arbitrary finite tuples.
Independence then passes to the supremum over finite subfamilies of the generators of `ℱ T`
(`indep_iSup_of_finset`), the two generators outside reach — Brownian values at non-positive times
and the part of a region in negative time — being almost surely constant and so dropping out.

## Main statements

* `LevyDriver.indep_valueTuple` — `ℱ₊ 0` against an arbitrary finite tuple of the driver's data.
* `LevyDriver.indep_rightCont_zero_filtration` — `ℱ₊ 0` against `ℱ T` for every `T > 0`.
* `LevyDriver.isTrivialSigma_rightCont_zero` — Blumenthal's 0-1 law itself.
* `LevyDriver.condExp_rightCont_nonpos` — the conditional expectation on `ℱ₊ s`, `s ≤ 0`, is the
  mean.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

/-- The germ field is independent of everything the driver generates. -/
theorem indep_rightCont_zero_sigma :
    Indep (D.filtration.rightCont 0)
      ((⨆ j, Brownian.sigmaBrownian (D.W.W j)) ⊔ sigmaPoisson D.N) P :=
  (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_9267402571d266701735a6c9 p2mMethodArg0 (_root_.Prove2MeSourceProof.h_4056caec4402ab97b0c897e1 D)) (D.filtration.rightCont.le 0)
/-- **The conditional expectation on the germ field is the mean.** -/
theorem condExp_rightCont_zero {ξ : Ω → ℝ} (hξ : StronglyMeasurable ξ) :
    P[ξ | D.filtration.rightCont 0] =ᵐ[P] fun _ => ∫ ω, ξ ω ∂P :=
  condExp_indep_eq le_rfl (D.filtration.rightCont.le 0) hξ
    ((fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_9267402571d266701735a6c9 p2mMethodArg0 (_root_.Prove2MeSourceProof.h_4056caec4402ab97b0c897e1 D)) (D.filtration.rightCont.le 0)).symm
/-- The same at every non-positive time, by the tower property. -/
theorem condExp_rightCont_nonpos {ξ : Ω → ℝ} (hξ : StronglyMeasurable ξ) {s : ℝ} (hs : s ≤ 0) :
    P[ξ | D.filtration.rightCont s] =ᵐ[P] fun _ => ∫ ω, ξ ω ∂P := by
  calc P[ξ | D.filtration.rightCont s]
      =ᵐ[P] P[P[ξ | D.filtration.rightCont 0] | D.filtration.rightCont s] :=
        (condExp_condExp_of_le (D.filtration.rightCont.mono hs)
          (D.filtration.rightCont.le 0)).symm
    _ =ᵐ[P] P[(fun _ => ∫ ω, ξ ω ∂P) | D.filtration.rightCont s] :=
        condExp_congr_ae (D.condExp_rightCont_zero hξ)
    _ = fun _ => ∫ ω, ξ ω ∂P := condExp_const (D.filtration.rightCont.le s) _
end LevyDriver

end LevyStochCalc.Driver


