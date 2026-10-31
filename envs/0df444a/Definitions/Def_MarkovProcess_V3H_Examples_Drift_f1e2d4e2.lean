-- Prove2me | Definitions.Def_MarkovProcess_V3H_Examples_Drift_f1e2d4e2
-- name    : MarkovProcess_V3H_Examples_Drift_f1e2d4e2
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:18:07.145418+00:00
-- url     : https://prove2.me/theorems/3870c1d9-d1d6-4a6d-9adf-5e5c55452f6c
-- title:
--   MarkovProcess: MarkovProcess_V3H_Examples_Drift_f1e2d4e2
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_C0_dfad2e28
import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The deterministic drift semigroup and its continuous-path process

On a finite-dimensional real normed space the transition semigroup that translates by `t • v` in
time `t` is a conservative Feller semigroup satisfying the Kolmogorov moment criterion with
exponents `p = q = 2` and constant `‖v‖²`.  The existence-and-uniqueness theorem of
`MarkovProcess.Main` therefore applies, and the process it produces is identified: from every
starting point `x` its law is the Dirac mass at the straight line `t ↦ x + t • v`.

Together with `MarkovProcess.Examples.Identity` this shows that the hypotheses of the main
theorem are satisfiable by a semigroup that genuinely moves.  Nothing here is claimed about a
semigroup with a nonzero diffusion part; for that see `MarkovProcess.Examples.HeatSemigroup`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Definition

omit [FiniteDimensional ℝ E] in
/-- Translation by `t • v` is measurable. -/
theorem measurable_driftTranslate (v : E) (t : NNReal) :
    Measurable (fun x : E ↦ x + (t : ℝ) • v) := by
  fun_prop

/-- The deterministic drift semigroup with velocity `v`: at time `t` it moves every point by
`t • v`. -/
def driftSemigroup (v : E) : SubMarkovKernelSemigroup E where
  kernel := fun t ↦ Kernel.deterministic (fun x ↦ x + (t : ℝ) • v) (measurable_driftTranslate v t)
  measurable_kernel := by
    have hg : Measurable (fun p : NNReal × E ↦ p.2 + (p.1 : ℝ) • v) := by fun_prop
    exact (Kernel.deterministic (fun p : NNReal × E ↦ p.2 + (p.1 : ℝ) • v) hg).measurable
  kernel_zero := by
    refine Kernel.ext fun x ↦ ?_
    rw [Kernel.deterministic_apply, Kernel.id_apply, NNReal.coe_zero, zero_smul, add_zero]
  kernel_add := fun s t ↦ by
    rw [Kernel.deterministic_comp_deterministic]
    refine Kernel.ext fun x ↦ ?_
    rw [Kernel.deterministic_apply, Kernel.deterministic_apply, Function.comp_apply,
      NNReal.coe_add, add_smul, add_assoc]
  isSubMarkovKernel := fun _ ↦ IsSubMarkovKernel.of_isMarkovKernel _

/-- The transition measure of the drift semigroup is the Dirac mass at the translated point. -/
theorem driftSemigroup_apply (v : E) (t : NNReal) (x : E) :
    (driftSemigroup v) t x = Measure.dirac (x + (t : ℝ) • v) := rfl

/-- The drift semigroup is conservative: every transition measure has total mass one. -/
theorem isConservative_driftSemigroup (v : E) : (driftSemigroup v).IsConservative := by
  intro t x
  rw [driftSemigroup_apply]
  exact measure_univ

end Definition

section Feller

/-- Integrating a `C₀` function against the drift semigroup evaluates it at the translated
point. -/
theorem kernelIntegral_driftSemigroup_apply (v : E) (t : NNReal) (f : C₀(E, ℝ)) (x : E) :
    kernelIntegral ((driftSemigroup v) t) f x = f (x + (t : ℝ) • v) := by
  rw [kernelIntegral, driftSemigroup_apply]
  exact integral_dirac' (f : E → ℝ) _ f.continuous.stronglyMeasurable

/-- The `C₀` kernel integral of the drift semigroup is the translate of the function. -/
theorem kernelIntegral_driftSemigroup (v : E) (t : NNReal) (f : C₀(E, ℝ)) :
    kernelIntegral ((driftSemigroup v) t) f = fun x ↦ f (x + (t : ℝ) • v) :=
  funext (kernelIntegral_driftSemigroup_apply v t f)

/-- The drift semigroup maps `C₀` into itself: translating a continuous function vanishing at
infinity gives another one, because translation is a cocompact map. -/
theorem mapsC0_driftSemigroup (v : E) : (driftSemigroup v).MapsC0 := by
  intro t f
  rw [kernelIntegral_driftSemigroup]
  refine ⟨f.continuous.comp (continuous_id.add continuous_const), ?_⟩
  have htranslate : Filter.Tendsto (fun x : E ↦ x + (t : ℝ) • v)
      (Filter.cocompact E) (Filter.cocompact E) :=
    CocompactMapClass.cocompact_tendsto
      ((Homeomorph.addRight ((t : ℝ) • v)).toCocompactMap)
  exact (f.zero_at_infty').comp htranslate





end Feller

section Moments



end Moments

section Process





/-- The straight line started at `x` with velocity `v`, as a continuous path. -/
def driftPath (v : E) (x : E) : ContinuousPath E where
  toFun := fun t ↦ x + (t : ℝ) • v
  continuous_toFun := by fun_prop







end Process

end

end MarkovProcess


