-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Gaussian_BrownianMotion
-- name    : KLS408915f_BrownianMotion_Gaussian_BrownianMotion
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:14:18.362366+00:00
-- url     : https://prove2.me/theorems/df5d3c5c-8c04-4f67-93af-96161b231838
-- title:
--   Canonical Brownian motion from a Gaussian projective limit
-- statement:
--   Vendored from the BrownianMotion library, repository https://github.com/RemyDegenne/brownian-motion, commit a7ad7af662044313bc80a7c0756360fb3745f931. A process satisfying `IsPreBrownianReal` has the finite-dimensional laws of the canonical nonnegative-time Gaussian process; `preBrownian` is the coordinate process on `gaussianLimit`, and `brownian` is a noncomputably chosen continuous modification of it. `HasLaw.IsPreBrownianReal` transfers the canonical finite-dimensional law condition, while `IsPreBrownianReal.isAEKolmogorovProcess` supplies the stated even-moment increment bound for positive integer exponents. The result `IsPreBrownianReal.exists_continuous_modification` gives a measurable modification whose paths are locally β-Hölder for β in the explicitly specified range below 1/2, and the file also supplies the Borel and measurable-space instances for continuous maps.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Gaussian/BrownianMotion.lean#L188-L633 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Gaussian.BrownianMotion`, definition bundle `KLS408915f_BrownianMotion_Gaussian_BrownianMotion`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
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
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
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
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
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

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Gaussian/BrownianMotion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
namespace ProbabilityTheory
section IsPreBrownianReal
variable (X : ℝ≥0 → Ω → ℝ)
variable {X} {P : Measure Ω}
lemma HasLaw.IsPreBrownianReal (hX : HasLaw (fun ω ↦ (X · ω)) gaussianLimit P) :
    IsPreBrownianReal X P where
  hasLaw _ := hasLaw_restrict_gaussianLimit.comp hX
lemma IsPreBrownianReal.isAEKolmogorovProcess {n : ℕ} (hn : 0 < n) (h : IsPreBrownianReal X P) :
    IsAEKolmogorovProcess X P (2 * n) n (Nat.doubleFactorial (2 * n - 1)) := by
  let Y t ω := (h.aemeasurable t).mk (X t) ω
  have hXY t := (h.aemeasurable t).ae_eq_mk
  have hY := h.congr hXY
  refine ⟨Y, ?_, ?_⟩
  constructor
  · intro s t
    rw [← BorelSpace.measurable_eq]
    refine Measurable.prodMk (h.aemeasurable s).measurable_mk (h.aemeasurable t).measurable_mk
  rotate_left
  · positivity
  · positivity
  · exact fun t ↦ (h.aemeasurable t).ae_eq_mk
  refine fun s t ↦ Eq.le ?_
  norm_cast
  simp_rw [edist_dist, Real.dist_eq]
  change ∫⁻ ω, (fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    ((Y s - Y t) ω) ∂_ = _
  rw [(hY.hasLaw_sub s t).lintegral_comp (f := fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    (by fun_prop)]
  simp_rw [← fun x ↦ ENNReal.ofReal_pow (abs_nonneg x)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [pow_two_mul_abs]
    rw [← centralMoment_of_integral_id_eq_zero _ (by simp), ← NNReal.sq_sqrt (nndist _ _),
    centralMoment_fun_two_mul_gaussianReal, ENNReal.ofReal_mul (by positivity), mul_comm]
    norm_cast
    congr
    rw [pow_mul, NNReal.sq_sqrt]
    simp only [val_eq_coe, NNReal.coe_pow, coe_nndist, dist_nonneg, ENNReal.ofReal_pow]
    congr
  · simp_rw [← Real.norm_eq_abs]
    apply MemLp.integrable_norm_pow'
    exact IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top (2 * n))
  · exact ae_of_all _ fun _ ↦ by positivity
/-- If `X` is a pre-Brownian process then there exists a modification of `X` which is measurable
and locally β-Hölder for `0 < β < 1/2` (and thus continuous). See `IsPreBrownianReal.mk`. -/
lemma IsPreBrownianReal.exists_continuous_modification (h : IsPreBrownianReal X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U :=
  haveI := h.isGaussianProcess.isProbabilityMeasure
  exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ h.isAEKolmogorovProcess (by positivity : 0 < n + 2))
    (fun n ↦ by finiteness) zero_lt_one (fun n ↦ by simp; norm_cast; omega)
/-- If `h : IsPreBrownianReal X P`, then `h.mk X` is a continuous modification of `X`. -/
protected noncomputable def IsPreBrownianReal.mk (X) (h : IsPreBrownianReal X P) : ℝ≥0 → Ω → ℝ :=
  h.exists_continuous_modification.choose
end IsPreBrownianReal
def preBrownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω ↦ ω t
@[fun_prop]
lemma measurable_preBrownian (t : ℝ≥0) : Measurable (preBrownian t) := by
  unfold preBrownian
  fun_prop
lemma hasLaw_preBrownian : HasLaw (fun ω ↦ (preBrownian · ω)) gaussianLimit gaussianLimit where
  aemeasurable := (measurable_pi_lambda _ measurable_preBrownian).aemeasurable
  map_eq := Measure.map_id
lemma isPreBrownianReal_preBrownian : IsPreBrownianReal preBrownian gaussianLimit :=
  hasLaw_preBrownian.IsPreBrownianReal
noncomputable
def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := isPreBrownianReal_preBrownian.mk
section Measure
section ContinuousMap.MeasurableSpace
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
instance : MeasurableSpace C(X, Y) := borel _
instance : BorelSpace C(X, Y) where
  measurable_eq := rfl
end ContinuousMap.MeasurableSpace
end Measure
end ProbabilityTheory


