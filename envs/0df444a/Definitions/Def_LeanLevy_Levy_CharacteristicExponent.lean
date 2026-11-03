-- Prove2me | Definitions.Def_LeanLevy_Levy_CharacteristicExponent
-- name    : LeanLevy_Levy_CharacteristicExponent
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T22:02:52.402528+00:00
-- url     : https://prove2.me/theorems/eaa2d524-41a4-4d52-921f-b6b11ab27bc1
-- title:
--   LeanLevy source module: Levy.CharacteristicExponent
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.Levy.CharacteristicExponent`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Local Characteristic Exponent

The characteristic exponent of a Lévy process requires taking `Complex.log` of the characteristic
function. Since `Complex.log` has a branch cut on the negative real axis, we construct the
exponent locally near `ξ = 0` where the characteristic function is near 1 (and hence in mathlib's
`slitPlane`).

## Design

We use a **general framework + Lévy specialisation**:

1. `LocalLog` defines the local log construction for any continuous function `φ` with `φ(0) = 1`.
2. `ProbabilityTheory.IsLevyProcess` applies it to the time-1 characteristic function.

## Main definitions

* `LocalLog.goodDomain` — the preimage of `slitPlane` under `φ`, where `Complex.log ∘ φ` is
  well-defined and continuous.
* `LocalLog.localCharExponent` — `Complex.log ∘ φ`.
* `IsLevyProcess.levyGoodDomain` — the good domain for the time-1 characteristic function.
* `IsLevyProcess.levyLocalCharExponent` — the local characteristic exponent.
* `DensityExtension.ceilApprox` — ceiling-sequence approximation of `ℝ≥0` by ℕ/ℕ rationals.
* `IsLevyProcess.levyExpFormula` — the exponential formula `F(t, ξ) := exp(t · Ψ(ξ))`.

## Main results

* `LocalLog.continuousOn_localCharExponent` — `log ∘ φ` is continuous on the good domain.
* `LocalLog.exists_ball_subset_goodDomain` — an open ball around 0 lies in the good domain.
* `IsLevyProcess.continuousOn_levyLocalCharExponent` — continuity of the local exponent.
* `DensityExtension.eq_of_rightCts_of_continuous_of_eqOn_ratNNReal` — if a right-continuous
  and a continuous function on `ℝ≥0` agree on all ℕ/ℕ rationals, they are equal.
* `IsLevyProcess.continuous_levyExpFormula_t` — continuity of the exponential formula in `t`.
* `IsLevyProcess.continuous_charFun_marginal_t` — the characteristic function is continuous in `t`.
* `IsLevyProcess.charFun_eq_levyExpFormula` — `φ_t(ξ) = exp(t · Ψ(ξ))` (clean restatement).
-/

open MeasureTheory Complex Filter Topology
open scoped NNReal

set_option linter.unusedSectionVars false

/-! ### Continuity of the characteristic function -/

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure E} [IsFiniteMeasure ν]

/-- The characteristic function of a finite measure is continuous. -/
theorem continuous_charFun : Continuous (charFun ν) := by
  show Continuous (fun ξ => ∫ x, cexp (↑(@inner ℝ E _ x ξ) * I) ∂ν)
  apply continuous_of_dominated
  · intro ξ
    exact (by fun_prop : Measurable (fun x => cexp (↑(@inner ℝ E _ x ξ) * I))).aestronglyMeasurable
  · intro ξ; apply Eventually.of_forall; intro x
    simp only [Complex.norm_exp_ofReal_mul_I]; exact le_refl _
  · exact integrable_const 1
  · apply Eventually.of_forall; intro x
    exact (by fun_prop : Continuous (fun ξ => cexp (↑(@inner ℝ E _ x ξ) * I)))

end MeasureTheory

/-! ### General LocalLog framework -/

namespace LocalLog

variable {E : Type*} [TopologicalSpace E] [Zero E]

/-- The good domain where `φ` lands in the slit plane (avoids the branch cut). -/
def goodDomain (φ : E → ℂ) : Set E := φ ⁻¹' Complex.slitPlane





/-- The local characteristic exponent: `Complex.log ∘ φ`. -/
noncomputable def localCharExponent (φ : E → ℂ) (ξ : E) : ℂ :=
  Complex.log (φ ξ)



section MetricBall
variable {E : Type*} [SeminormedAddCommGroup E]





end MetricBall

end LocalLog

/-! ### Density extension from rationals to reals

A general-purpose ceiling-sequence construction and density lemma for extending
equality from ℕ/ℕ rationals in `ℝ≥0` to all of `ℝ≥0`, given right-continuity
on one side and continuity on the other. Independent of Lévy processes. -/

namespace DensityExtension

open Filter Topology

/-- Ceiling approximation from above: `ceilApprox t m = ⌈t * (m+1)⌉₊ / (m+1)` as `ℝ≥0`.
This gives a sequence of ℕ/ℕ rationals converging to `t` from above. -/
noncomputable def ceilApprox (t : ℝ≥0) (m : ℕ) : ℝ≥0 :=
  (⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)









-- The final `tendsto_nhds_unique` step became markedly slower after the mathlib bump
-- (heavier `isDefEq` on the `ℝ≥0`/`Nat.ceil` sequence); the proof is unchanged, only the
-- elaboration budget is raised to accommodate it.


end DensityExtension

/-! ### Lévy process specialisation -/

namespace ProbabilityTheory.IsLevyProcess

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]







/-- The good domain for the time-1 characteristic function. -/
def levyGoodDomain (_h : IsLevyProcess X μ) (_hX : ∀ t, Measurable (X t)) : Set E :=
  LocalLog.goodDomain (fun ξ => charFun (μ.map (X 1)) ξ)





/-- The local characteristic exponent of the Lévy process. -/
noncomputable def levyLocalCharExponent
    (_h : IsLevyProcess X μ) (_hX : ∀ t, Measurable (X t)) : E → ℂ :=
  LocalLog.localCharExponent (fun ξ => charFun (μ.map (X 1)) ξ)



/-! ### Semigroup properties

All derived as short corollaries of `charFun_eq_exp_mul`. -/

section Semigroup

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]









/-! ### Characteristic exponent at origin -/



/-! ### Local-global exponent connection -/



/-! ### Complex power formulation -/



end Semigroup

/-! ### Lévy exponential formula

The function `F(t, ξ) := exp(t · Ψ(ξ))` packaged as a named definition,
with continuity in `t` and the equivalence with the characteristic function. -/

section LevyExpFormula

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Lévy exponential formula: `F(t, ξ) := exp(t · Ψ(ξ))` where `Ψ` is the
characteristic exponent. -/
noncomputable def levyExpFormula (h : IsLevyProcess X μ)
    (_hX : ∀ t, Measurable (X t)) (t : ℝ≥0) (ξ : E) : ℂ :=
  exp (↑(t : ℝ) * h.charExponent ξ)







end LevyExpFormula

end ProbabilityTheory.IsLevyProcess


