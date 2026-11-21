-- Prove2me | Definitions.Def_SourceProof_255c56796ae34c821a34d963
-- name    : SourceProof_255c56796ae34c821a34d963
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:31:20.633633+00:00
-- url     : https://prove2.me/theorems/d91bb4bb-0909-4b54-abb1-e775a8938171
-- title:
--   LevyStochCalc source module: SourceProof_255c56796ae34c821a34d963
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_eq_of_tendsto_stepIntegral` comes from the `LevyStochCalc.Poisson.CompensatedProfile` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F000

open private eLpNorm_sub_le_three from Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of a deterministic mark profile over a step

The compensated step integrals of simple mark profiles obey the isometry
`‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`, so an `L²(P)` limit of the compensated step
integrals of simple profiles converging in `L²(ν)` is determined, up to a null set, by the limit
profile alone. That limit is the compensated integral over the step `(a, b]` of a
square-integrable deterministic mark profile `f : E → ℝ` against a Poisson random measure with
intensity `ν`. It agrees with the compensated step integral at a simple profile and carries the
Lévy character

  `E[exp (i u J(f))] = exp ((b − a) ∫ (exp (i u f) − 1 − i u f) dν)`.

## Main definitions

* `LevyStochCalc.Poisson.IsCompensatedProfile` — being a strongly measurable `L²(P)` limit at a
  step of the compensated step integrals of every sequence of simple mark profiles converging to
  a mark profile in `L²(ν)`.
* `LevyStochCalc.Poisson.compensatedProfile` — the compensated integral of a square-integrable
  deterministic mark profile over a step.

## Main statements

* `LevyStochCalc.Poisson.ae_eq_of_tendsto_stepIntegral` — an `L²(P)` limit of the compensated
  step integrals of simple profiles converging in `L²(ν)` depends only on the limit profile.
* `LevyStochCalc.Poisson.stronglyMeasurable_compensatedProfile`,
  `LevyStochCalc.Poisson.memLp_compensatedProfile` — measurability and square integrability.
* `LevyStochCalc.Poisson.tendsto_stepIntegral_compensatedProfile` — the compensated step
  integrals of simple profiles converging to a profile in `L²(ν)` converge to its compensated
  integral in `L²(P)`.
* `LevyStochCalc.Poisson.compensatedProfile_toFun` — agreement with the compensated step
  integral at a simple mark profile.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile` — the Lévy character of the
  compensated integral of a mark profile over a step.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Independence of the approximating sequence -/


theorem _root_.Prove2MeSourceProof.h_255c56796ae34c821a34d963 (N : PoissonRandomMeasure P ν)
    {G G' : ℕ → SimpleProfile E ν} {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) {J J' : Ω → ℝ} (hJ : MemLp J 2 P) (hJ' : MemLp J' 2 P)
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0))
    (hG' : Tendsto (fun n => eLpNorm (fun e => (G' n).toFun e - f e) 2 ν) atTop (nhds 0))
    (hJlim : Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P)
      atTop (nhds 0))
    (hJ'lim : Tendsto (fun n => eLpNorm (fun ω => (G' n).stepIntegral N a b ω - J' ω) 2 P)
      atTop (nhds 0)) :
    J =ᵐ[P] J' := by
  have hmid : ∀ n, eLpNorm (fun ω => (G n).stepIntegral N a b ω
      - (G' n).stepIntegral N a b ω) 2 P
      ≤ ENNReal.ofReal (Real.sqrt (b - a))
        * (eLpNorm (fun e => (G n).toFun e - f e) 2 ν
          + eLpNorm (fun e => (G' n).toFun e - f e) 2 ν) := by
    intro n
    rw [LevyStochCalc.Poisson.SimpleProfile.eLpNorm_stepIntegral_sub N (G n) (G' n) ha hab]
    gcongr
    calc eLpNorm (fun e => (G n).toFun e - (G' n).toFun e) 2 ν
        = eLpNorm ((fun e => (G n).toFun e - f e) - fun e => (G' n).toFun e - f e) 2 ν := by
          refine eLpNorm_congr_ae (Eventually.of_forall fun e => ?_)
          simp only [Pi.sub_apply]
          ring
      _ ≤ _ := eLpNorm_sub_le ((G n).memLp_toFun.sub hf).aestronglyMeasurable
          ((G' n).memLp_toFun.sub hf).aestronglyMeasurable one_le_two
  have hbound : ∀ n, eLpNorm (fun ω => J ω - J' ω) 2 P
      ≤ eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P
        + ENNReal.ofReal (Real.sqrt (b - a))
          * (eLpNorm (fun e => (G n).toFun e - f e) 2 ν
            + eLpNorm (fun e => (G' n).toFun e - f e) 2 ν)
        + eLpNorm (fun ω => (G' n).stepIntegral N a b ω - J' ω) 2 P := by
    intro n
    refine (eLpNorm_sub_le_three
      (((G n).memLp_stepIntegral N ha b).sub hJ).aestronglyMeasurable
      (((G n).memLp_stepIntegral N ha b).sub
        ((G' n).memLp_stepIntegral N ha b)).aestronglyMeasurable
      (((G' n).memLp_stepIntegral N ha b).sub hJ').aestronglyMeasurable).trans ?_
    gcongr
    exact hmid n
  have hzero : Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P
      + ENNReal.ofReal (Real.sqrt (b - a))
        * (eLpNorm (fun e => (G n).toFun e - f e) 2 ν
          + eLpNorm (fun e => (G' n).toFun e - f e) 2 ν)
      + eLpNorm (fun ω => (G' n).stepIntegral N a b ω - J' ω) 2 P) atTop (nhds 0) := by
    have hprod : Tendsto (fun n => ENNReal.ofReal (Real.sqrt (b - a))
        * (eLpNorm (fun e => (G n).toFun e - f e) 2 ν
          + eLpNorm (fun e => (G' n).toFun e - f e) 2 ν)) atTop (nhds 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.sqrt (b - a)))
        (hG.add hG') (Or.inr ENNReal.ofReal_ne_top)
      simpa using h
    simpa using (hJlim.add hprod).add hJ'lim
  have h0 : eLpNorm (fun ω => J ω - J' ω) 2 P = 0 :=
    le_antisymm (ge_of_tendsto hzero (Eventually.of_forall hbound)) zero_le
  have hae := (eLpNorm_eq_zero_iff (hJ.sub hJ').aestronglyMeasurable (by norm_num)).1 h0
  filter_upwards [hae] with ω hω
  simpa [sub_eq_zero] using hω
/-! ### The compensated integral of a mark profile over a step -/

/-! ### Agreement at a simple mark profile -/

/-! ### The character -/

end LevyStochCalc.Poisson


