-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
-- name    : KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:57:52.804478+00:00
-- url     : https://prove2.me/theorems/72535c27-d629-4e7e-a905-7159f038535f
-- title:
--   Independence and integrability of compensated Poisson boxes
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `indepFun_past_compensated_box` states that an $\mathcal F_a$-strongly measurable real function is independent of the compensated mass on $(a,b]\times A$ when $0\le a<b$ and $A$ is measurable with finite $\nu$-measure. `compensated_cross_integrable` states that the product of two compensated masses on finite-intensity measurable sets is $P$-integrable. These are technical box-level results for increment and isometry calculations.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedMartingaleIncrement.lean#L381-L586 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.CompensatedMartingaleIncrement`, definition bundle `KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleAdapted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedMartingaleIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- **Past-independence of a future box increment.** For a box `B = Ioc a b ×ˢ A`
(`0 ≤ a`, `A` measurable with finite `ν`-mass) and any `f` measurable w.r.t. the
"past at `a`" σ-algebra, `f` and `Ñ(B)` are independent. Repackages
`joint_past_future_independent` at the level of `IndepFun`. -/
lemma indepFun_past_compensated_box
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAf : ν A ≠ ⊤)
    {f : Ω → ℝ}
    (hf : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) f) :
    ProbabilityTheory.IndepFun f (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) P := by
  have h_box_meas : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hf_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ a :=
    hf.measurable.comap_le
  have hÑ_comap_le :
      MeasurableSpace.comap (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) inferInstance ≤
        MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc a b ×ˢ A)) inferInstance := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨(fun x : ℝ≥0∞ => x.toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal) ⁻¹' v, ?_, ?_⟩
    · exact (ENNReal.measurable_toReal.sub_const _) hv
    · ext ω; rfl
  rw [ProbabilityTheory.IndepFun_iff]
  intro u v hu hv
  have h_indep := hℱ.indep ha hab hA hAf
  rw [ProbabilityTheory.Indep_iff] at h_indep
  exact h_indep u v (hf_comap_le u hu) (hÑ_comap_le v hv)
/-- Cross-integrability of two compensated masses: `Ñ(B)·Ñ(C)` is `P`-integrable
when both `B`, `C` have finite intensity (each `Ñ ∈ L²`, dominated by
`½(Ñ(B)² + Ñ(C)²)`). -/
lemma compensated_cross_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBf : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hCf : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => N.compensated B ω * N.compensated C ω) P := by
  have hBsq := compensated_sq_integrable N hB hBf
  have hCsq := compensated_sq_integrable N hC hCf
  have hmeas : Measurable (fun ω => N.compensated B ω * N.compensated C ω) := by
    unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
    exact ((ENNReal.measurable_toReal.comp (N.measurable_eval hB)).sub_const _).mul
      ((ENNReal.measurable_toReal.comp (N.measurable_eval hC)).sub_const _)
  refine MeasureTheory.Integrable.mono'
    (hBsq.add hCsq) hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  change ‖N.compensated B ω * N.compensated C ω‖ ≤ (N.compensated B ω)^2 + (N.compensated C ω)^2
  rw [Real.norm_eq_abs]
  rcases abs_cases (N.compensated B ω * N.compensated C ω) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
    nlinarith [two_mul_le_add_sq (N.compensated B ω) (N.compensated C ω),
      two_mul_le_add_sq (N.compensated B ω) (-N.compensated C ω),
      sq_nonneg (N.compensated B ω), sq_nonneg (N.compensated C ω)]
end Compensated
end Poisson
end LevyStochCalc


