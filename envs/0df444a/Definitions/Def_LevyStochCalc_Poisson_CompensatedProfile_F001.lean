-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F001
-- name    : LevyStochCalc_Poisson_CompensatedProfile_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:32:35.812371+00:00
-- url     : https://prove2.me/theorems/3debaefc-2a69-4fe9-a8c1-4ac51b5fdb13
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProfile
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProfile. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F002
import Definitions.Def_SourceProof_1aa328a9a0337e8548a6f052
import Definitions.Def_SourceProof_255c56796ae34c821a34d963
import Definitions.Def_SourceProof_abfa6819f153687cc685dc62

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

/-! ### The compensated integral of a mark profile over a step -/

/-- The property of being a strongly measurable square-integrable `L²(P)` limit over the step
`(a, b]` of the compensated step integrals of every sequence of simple mark profiles converging
to `f` in `L²(ν)`. -/
def IsCompensatedProfile (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b : ℝ) (J : Ω → ℝ) :
    Prop :=
  StronglyMeasurable J ∧ MemLp J 2 P ∧ ∀ G : ℕ → SimpleProfile E ν,
    Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0) →
    Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P) atTop (nhds 0)
open scoped Classical in
/-- The compensated integral over the step `(a, b]` of a square-integrable deterministic mark
profile `f` against a Poisson random measure with intensity `ν`: the `L²(P)` limit of the
compensated step integrals of any sequence of simple mark profiles converging to `f` in `L²(ν)`.
Where no such sequence exists the value is unspecified. -/
noncomputable def compensatedProfile (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b : ℝ) :
    Ω → ℝ :=
  if h : ∃ J : Ω → ℝ, IsCompensatedProfile N f a b J then h.choose else 0
/-- The compensated integral of a mark profile over a step is strongly measurable. -/
theorem stronglyMeasurable_compensatedProfile (N : PoissonRandomMeasure P ν) (f : E → ℝ)
    (a b : ℝ) : StronglyMeasurable (compensatedProfile N f a b) := by
  by_cases h : ∃ J : Ω → ℝ, IsCompensatedProfile N f a b J
  · rw [show compensatedProfile N f a b = h.choose from dif_pos h]
    exact h.choose_spec.1
  · rw [show compensatedProfile N f a b = 0 from dif_neg h]
    exact stronglyMeasurable_const
/-- The compensated integral of a mark profile over a step is measurable. -/
theorem measurable_compensatedProfile (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b : ℝ) :
    Measurable (compensatedProfile N f a b) :=
  (stronglyMeasurable_compensatedProfile N f a b).measurable
/-- The compensated integral of a mark profile over a step is square integrable. -/
theorem memLp_compensatedProfile (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b : ℝ) :
    MemLp (compensatedProfile N f a b) 2 P := by
  by_cases h : ∃ J : Ω → ℝ, IsCompensatedProfile N f a b J
  · rw [show compensatedProfile N f a b = h.choose from dif_pos h]
    exact h.choose_spec.2.1
  · rw [show compensatedProfile N f a b = 0 from dif_neg h]
    exact MemLp.zero
/-- The compensated integral of a square-integrable mark profile approximated in `L²(ν)` by
simple mark profiles is an `L²(P)` limit of their compensated step integrals. -/
theorem isCompensatedProfile_compensatedProfile (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (G : ℕ → SimpleProfile E ν)
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0)) :
    IsCompensatedProfile N f a b (compensatedProfile N f a b) := by
  have hex : ∃ J : Ω → ℝ, IsCompensatedProfile N f a b J := by
    obtain ⟨J₀, hJ₀, hJ₀lim⟩ := _root_.Prove2MeSourceProof.h_1aa328a9a0337e8548a6f052 N G hf ha hab hG
    set J := hJ₀.1.mk J₀
    have hJae : J₀ =ᵐ[P] J := hJ₀.1.ae_eq_mk
    have hJ : MemLp J 2 P := MemLp.ae_eq hJae hJ₀
    have hJlim : Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P)
        atTop (nhds 0) := by
      refine hJ₀lim.congr fun n => eLpNorm_congr_ae ?_
      filter_upwards [hJae] with ω hω
      simp [hω]
    refine ⟨J, hJ₀.1.stronglyMeasurable_mk, hJ, fun G' hG' => ?_⟩
    obtain ⟨J', hJ', hJ'lim⟩ := _root_.Prove2MeSourceProof.h_1aa328a9a0337e8548a6f052 N G' hf ha hab hG'
    have hJJ' : J' =ᵐ[P] J :=
      _root_.Prove2MeSourceProof.h_255c56796ae34c821a34d963 N hf ha hab hJ' hJ hG' hG hJ'lim hJlim
    refine hJ'lim.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [hJJ'] with ω hω
    simp [hω]
  rw [show compensatedProfile N f a b = hex.choose from dif_pos hex]
  exact hex.choose_spec
/-- **The defining convergence.** The compensated step integrals of simple mark profiles
converging to a square-integrable mark profile in `L²(ν)` converge in `L²(P)` to its compensated
integral over the step. -/
theorem tendsto_stepIntegral_compensatedProfile (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (G : ℕ → SimpleProfile E ν)
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω
      - compensatedProfile N f a b ω) 2 P) atTop (nhds 0) :=
  (isCompensatedProfile_compensatedProfile N hf ha hab G hG).2.2 G hG
/-- The compensated integral of a square-integrable mark profile over a step is an `L²(P)`
limit of the compensated step integrals of any sequence of simple mark profiles converging to the
profile in `L²(ν)`. -/
theorem isCompensatedProfile_compensatedProfile_of_memLp (N : PoissonRandomMeasure P ν)
    {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IsCompensatedProfile N f a b (compensatedProfile N f a b) := by
  obtain ⟨G, hG⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hf
  exact isCompensatedProfile_compensatedProfile N hf ha hab G hG
/-! ### Agreement at a simple mark profile -/

/-! ### The character -/

end LevyStochCalc.Poisson


