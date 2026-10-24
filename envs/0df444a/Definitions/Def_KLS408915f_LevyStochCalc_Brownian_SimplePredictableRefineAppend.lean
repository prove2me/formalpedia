-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
-- name    : KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:26:41.451853+00:00
-- url     : https://prove2.me/theorems/f484e5c9-6a7c-4c83-ba3c-8b62fd1791b8
-- title:
--   Zero extension of a simple predictable integrand
-- statement:
--   Vendored from LevyStochCalc (https://github.com/cgarryZA/LevyStochCalc), with the locally recorded port patch. `SimplePredictable.appendInterval` appends a final interval from the old endpoint to a larger endpoint $T'$ and assigns it coefficient $0$. The appended object remains strictly partitioned and bounded measurable; its evaluation and `simpleIntegral` agree pointwise with the original, and adaptedness is preserved. The auxiliary lemmas identify the appended partition and coefficient values.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/SimplePredictableRefineAppend.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.SimplePredictableRefineAppend`, definition bundle `KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/SimplePredictableRefineAppend.lean, lines 28-162). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
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
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
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
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/SimplePredictableRefineAppend.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- `Fin.snoc f a` is strictly monotone when `f` is and `f (last) < a`. -/
lemma strictMono_snoc {n : ℕ} {α : Type*} [Preorder α] {f : Fin (n + 1) → α}
    (hf : StrictMono f) {a : α} (ha : f (Fin.last n) < a) :
    StrictMono (Fin.snoc f a) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hf (by rwa [Fin.castSucc_lt_castSucc_iff] at hij)
    · exact absurd hij (not_lt.mpr (Fin.le_last _))
  · rw [Fin.snoc_last]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      exact lt_of_le_of_lt (hf.monotone (Fin.le_last i')) ha
    · exact absurd hij (lt_irrefl _)
/-- **Zero-extension to a larger horizon.** Append one interval `(H_last, T']`
carrying coefficient `0`, producing a `SimplePredictable` on the larger horizon
`T'` whose `eval` and `simpleIntegral` are unchanged. Lets two different-horizon
approximants be put on a common endpoint for the difference isometry. -/
noncomputable def SimplePredictable.appendInterval
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') : SimplePredictable Ω T' where
  N := H.N + 1
  partition := Fin.snoc H.partition T'
  partition_zero := by rw [Fin.snoc_apply_zero]; exact H.partition_zero
  partition_le_T := by rw [Fin.snoc_last]
  partition_strictMono := strictMono_snoc H.partition_strictMono hlt
  ξ := Fin.snoc H.ξ (fun _ => 0)
  ξ_bounded := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · obtain ⟨M, hM⟩ := H.ξ_bounded i'
      exact ⟨M, fun ω => by rw [Fin.snoc_castSucc]; exact hM ω⟩
    · exact ⟨0, fun ω => by rw [Fin.snoc_last]; simp⟩
  ξ_measurable := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]; exact H.ξ_measurable i'
    · rw [Fin.snoc_last]; exact measurable_const
lemma SimplePredictable.appendInterval_partition_eq
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).partition = Fin.snoc H.partition T' := rfl
lemma SimplePredictable.appendInterval_xi_eq
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).ξ = Fin.snoc H.ξ (fun _ => 0) := rfl
lemma SimplePredictable.appendInterval_partition_last
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).partition (Fin.last (H.N + 1)) = T' := by
  rw [H.appendInterval_partition_eq hlt]
  exact Fin.snoc_last (α := fun _ => ℝ) T' H.partition
/-- Index identity used to relate the appended partition's `castSucc`/`succ`
to the original partition. -/
 lemma appendInterval_succ_castSucc {n : ℕ} (i : Fin n) :
    (Fin.castSucc i).succ = Fin.castSucc i.succ := Fin.ext rfl
/-- Pointwise values of the appended partition / coefficients. -/
lemma SimplePredictable.appendInterval_partition_castSucc
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (j : Fin (H.N + 1)) :
    (H.appendInterval hlt).partition (Fin.castSucc j) = H.partition j := by
  rw [H.appendInterval_partition_eq hlt]; exact Fin.snoc_castSucc (α := fun _ => ℝ) _ _ _
lemma SimplePredictable.appendInterval_xi_castSucc
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (j : Fin H.N) :
    (H.appendInterval hlt).ξ (Fin.castSucc j) = H.ξ j := by
  rw [H.appendInterval_xi_eq hlt]; simp only [Fin.snoc_castSucc]
lemma SimplePredictable.appendInterval_xi_last
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') :
    (H.appendInterval hlt).ξ (Fin.last H.N) = (fun _ : Ω => (0 : ℝ)) := by
  rw [H.appendInterval_xi_eq hlt]; simp only [Fin.snoc_last]
/-- The `eval` of the zero-extension equals the original `eval`. -/
lemma SimplePredictable.appendInterval_eval
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (s : ℝ) (ω : Ω) :
    (H.appendInterval hlt).eval s ω = H.eval s ω := by
  unfold SimplePredictable.eval
  change (∑ i : Fin (H.N + 1),
      if (Fin.snoc (α := fun _ => ℝ) H.partition T') i.castSucc < s
          ∧ s ≤ (Fin.snoc (α := fun _ => ℝ) H.partition T') i.succ
        then (Fin.snoc (α := fun _ => Ω → ℝ) H.ξ (fun _ : Ω => (0 : ℝ))) i ω else 0)
    = ∑ i : Fin H.N,
        if H.partition i.castSucc < s ∧ s ≤ H.partition i.succ then H.ξ i ω else 0
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, ite_self, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LevyStochCalc.Brownian.Ito.appendInterval_succ_castSucc]
  simp only [Fin.snoc_castSucc]
/-- The `simpleIntegral` of the zero-extension equals the original `simpleIntegral`. -/
lemma SimplePredictable.appendInterval_simpleIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (t : ℝ) (ω : Ω) :
    simpleIntegral W (H.appendInterval hlt) t ω = simpleIntegral W H t ω := by
  unfold simpleIntegral
  change (∑ i : Fin (H.N + 1),
      (Fin.snoc (α := fun _ => Ω → ℝ) H.ξ (fun _ : Ω => (0 : ℝ))) i ω
        * (W.W (min ((Fin.snoc (α := fun _ => ℝ) H.partition T') i.succ) t) ω
            - W.W (min ((Fin.snoc (α := fun _ => ℝ) H.partition T') i.castSucc) t) ω))
    = ∑ i : Fin H.N, H.ξ i ω
        * (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω)
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, zero_mul, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LevyStochCalc.Brownian.Ito.appendInterval_succ_castSucc]
  simp only [Fin.snoc_castSucc]
/-- Adaptedness is preserved by the zero-extension. -/
lemma SimplePredictable.appendInterval_adapt
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T')
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∀ i : Fin (H.appendInterval hlt).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((H.appendInterval hlt).partition i.castSucc)) ((H.appendInterval hlt).ξ i) := by
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · rw [H.appendInterval_xi_castSucc hlt i',
        H.appendInterval_partition_castSucc hlt (Fin.castSucc i')]
    exact h_adapt i'
  · rw [H.appendInterval_xi_last hlt]; exact MeasureTheory.stronglyMeasurable_const
end Ito
end Brownian
end LevyStochCalc


