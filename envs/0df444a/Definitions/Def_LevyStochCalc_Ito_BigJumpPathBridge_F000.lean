-- Prove2me | Definitions.Def_LevyStochCalc_Ito_BigJumpPathBridge_F000
-- name    : LevyStochCalc_Ito_BigJumpPathBridge_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:52:45.129412+00:00
-- url     : https://prove2.me/theorems/4efd8183-10a3-4170-949f-c30d4e37bc89
-- title:
--   Source declarations: LevyStochCalc.Ito.BigJumpPathBridge
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.BigJumpPathBridge. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaClosure_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaClosure_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The big-jump path as a member of the big-jump sequence

The path of a jump diffusion with the jumps carried by one measurable mark set removed is the
corresponding member of the sequence of big-jump processes built from the jump-integrand data of
its SDE, and the two constructions coincide coordinatewise at the level of the subtracted
compensated integrals as well.

## Main statements

* `LevyStochCalc.Ito.BigJump.cutJumpIntegral_eq_smallJumpIntegral` — the truncated compensated
  integral at the `m`-th mark set is the `m`-th small-jump integral of the jump-integrand data.
* `LevyStochCalc.Ito.BigJump.bigJumpPath_eq_bigJumpProcess` — the big-jump path at the `m`-th
  mark set is the `m`-th big-jump process of the jump-integrand data.
* `LevyStochCalc.Ito.BigJump.bigJumpPath_smallMarks_eq_bigJumpProcess` — the same identity along
  the complements of a spanning family of the intensity.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.BigJump

universe u v

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.SmallJump

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

/-- The filtration of the jump-integrand data of the SDE is the filtration of the SDE data. -/
@[simp] theorem SdeData.toJumpIntegrand_ℱ (S : SdeData X) : S.toJumpIntegrand.ℱ = S.ℱ := rfl
variable (S : SdeData X) {A : ℕ → Set E} (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)

/-- The truncated compensated integral at the `m`-th member of a measurable family of mark sets
is the `m`-th small-jump integral of the jump-integrand data of the SDE. -/
theorem cutJumpIntegral_eq_smallJumpIntegral (m : ℕ) (i : Fin n) :
    cutJumpIntegral S (hA m) hℱ0 hnull0 i
      = smallJumpIntegral S.toJumpIntegrand hA hℱ0 hnull0 m i :=
  rfl
/-- The big-jump path at the `m`-th member of a measurable family of mark sets is the `m`-th
big-jump process of the jump-integrand data of the SDE. -/
theorem bigJumpPath_eq_bigJumpProcess (m : ℕ) :
    bigJumpPath S (hA m) hℱ0 hnull0 = bigJumpProcess S.toJumpIntegrand hA hℱ0 hnull0 m :=
  rfl
/-- The big-jump path at the `m`-th complement of a spanning family of the intensity is the
`m`-th big-jump process of the jump-integrand data of the SDE along that family. -/
theorem bigJumpPath_smallMarks_eq_bigJumpProcess (m : ℕ) :
    bigJumpPath S (JumpFormula.measurableSet_smallMarks ν m) hℱ0 hnull0
      = bigJumpProcess S.toJumpIntegrand (JumpFormula.measurableSet_smallMarks ν) hℱ0 hnull0 m :=
  rfl
end LevyStochCalc.Ito.BigJump


