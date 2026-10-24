-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
-- name    : KLS408915f_LevyStochCalc_Brownian_Multidim
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:18:11.631568+00:00
-- url     : https://prove2.me/theorems/1412848c-4b6f-483a-b7bc-9e9fce88bda1
-- title:
--   Finite-dimensional Brownian motion structure
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `MultidimBrownianMotion P d` packages a Fin d-indexed family of one-dimensional Brownian motions on the same probability space, with mutually independent component processes and almost-sure continuity of the joint path t ↦ (W i t ω)ᵢ. The auxiliary definition `project_BM` lifts a one-dimensional Brownian motion on (Ω₀, P₀) to the product space Fin d → Ω₀ by evaluating at one coordinate, with the product probability measure.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/Multidim.lean#L47-L166 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.Multidim`, definition bundle `KLS408915f_LevyStochCalc_Brownian_Multidim`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_Chaining
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_CoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_IsKolmogorovProcess
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsov
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsovInequality
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_LimitModification
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Multidim.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Brownian
namespace Multidim
universe u
section Definition
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A `d`-dimensional Brownian motion: a `Fin d`-tuple of independent
1-dimensional Brownian motions on the same probability space. -/
structure MultidimBrownianMotion (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) where
  /-- The component-wise Brownian motions. -/
  W : Fin d → LevyStochCalc.Brownian.BrownianMotion P
  /-- The components are mutually independent — each component, viewed as a
  random variable into the path space `ℝ → ℝ` (with the product measurable
  structure), is jointly independent across `i : Fin d`. -/
  components_independent :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin d) (ω : Ω) (t : ℝ) => (W i).W t ω) P
  /-- The joint d-dim
  path `t ↦ (W i ω t)_{i ∈ Fin d}` is continuous a.s. P. Follows from
  the component-wise `continuous_paths` + the finite-intersection-of-
  a.s.-sets being a.s., plus `continuous_pi_iff`: a `Fin d → ℝ`-valued
  map is continuous iff each component is. Previously this was implicit
  (a downstream caller had to derive it from `(W i).continuous_paths`
  for each i); now made explicit per Karatzas-Shreve §2.5's definition
  of multidim BM as "vector-valued process with continuous paths". -/
  joint_continuous_paths :
    ∀ᵐ ω ∂P, Continuous (fun (t : ℝ) (i : Fin d) => (W i).W t ω)
end Definition
section MeasurePreserving
variable {Ω : Type u} [MeasurableSpace Ω]
/-- Lift a 1-dimensional Brownian motion `W₀` on `(Ω₀, P₀)` to a 1-D BM on the
product space `(Fin d → Ω₀, Measure.pi)` along the `i`-th coordinate. -/
 noncomputable def project_BM
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    (W₀ : LevyStochCalc.Brownian.BrownianMotion P₀)
    (d : ℕ) (i : Fin d) :
    @LevyStochCalc.Brownian.BrownianMotion (Fin d → Ω₀) MeasurableSpace.pi
      (MeasureTheory.Measure.pi (fun _ => P₀))
      (by infer_instance) where
  W := fun t (ω : Fin d → Ω₀) => W₀.W t (ω i)
  measurable_eval := fun t =>
    (W₀.measurable_eval t).comp (measurable_pi_apply i)
  joint_measurable := by
    -- Joint measurability inherits from 1D BM's joint measurability via
    -- the measurable evaluation map at coordinate i.
    have h₀ := W₀.joint_measurable
    -- Function.uncurry (fun t ω => W₀.W t (ω i)) = (fun p => W₀.W p.1 (p.2 i))
    -- = h₀ ∘ (fun p => (p.1, p.2 i))
    have h_eval_meas : Measurable (fun (p : ℝ × (Fin d → Ω₀)) => (p.1, p.2 i)) := by
      refine Measurable.prodMk (measurable_fst) ?_
      exact (measurable_pi_apply i).comp measurable_snd
    exact h₀.comp h_eval_meas
  initial_zero := by
    -- W₀.initial_zero : ∀ᵐ ω₀ ∂P₀, W₀.W 0 ω₀ = 0; lift via
    --   measure-preserving eval i.
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae W₀.initial_zero
  increment_gaussian := by
    intro s t hs hst
    -- Pushforward through eval_i preserves the Gaussian increment law.
    have h_eval : (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)).map
        (Function.eval i) = P₀ :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin d => P₀) i).map_eq
    have h_inc := W₀.increment_gaussian hs hst
    rw [show (fun ω : Fin d → Ω₀ => W₀.W t (ω i) - W₀.W s (ω i))
        = (W₀.W t - W₀.W s) ∘ Function.eval i from rfl,
      ← MeasureTheory.Measure.map_map
        ((W₀.measurable_eval t).sub (W₀.measurable_eval s))
        (measurable_pi_apply i),
      h_eval]
    exact h_inc
  continuous_paths := by
    -- W₀.continuous_paths lifts via measure-preserving eval i.
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae W₀.continuous_paths
  negative_zero := by
    -- W₀.negative_zero lifts via measure-preserving eval i.
    intro s hs
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae (W₀.negative_zero s hs)
  joint_increment_independent := by
    -- W₀.joint_increment_independent + `indep_comap_of_measurePreserving`.
    intro s t hs hst
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    have h_inc_comap :
        MeasurableSpace.comap
          (fun (ω : Fin d → Ω₀) => W₀.W t (ω i) - W₀.W s (ω i)) inferInstance
        = (MeasurableSpace.comap (fun ω => W₀.W t ω - W₀.W s ω) inferInstance).comap
            (Function.eval i) := by
      rw [MeasurableSpace.comap_comp]
      rfl
    have h_past_comap :
        (⨆ j ∈ Set.Iic s, MeasurableSpace.comap
          (fun (ω : Fin d → Ω₀) => W₀.W j (ω i)) inferInstance)
        = (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W₀.W j) inferInstance).comap
            (Function.eval i) := by
      rw [MeasurableSpace.comap_iSup]
      refine iSup_congr (fun j => ?_)
      rw [MeasurableSpace.comap_iSup]
      refine iSup_congr (fun _ => ?_)
      rw [MeasurableSpace.comap_comp]
      rfl
    rw [h_past_comap, h_inc_comap]
    apply Probability.indep_comap_of_measurePreserving mp
    · -- past σ-algebra ≤ ambient
      refine iSup₂_le ?_
      intro j _ u hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact (W₀.measurable_eval j) hv
    · -- increment σ-algebra ≤ ambient
      intro u hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact ((W₀.measurable_eval t).sub (W₀.measurable_eval s)) hv
    · exact W₀.joint_increment_independent hs hst
end MeasurePreserving
end Multidim
end Brownian
end LevyStochCalc


