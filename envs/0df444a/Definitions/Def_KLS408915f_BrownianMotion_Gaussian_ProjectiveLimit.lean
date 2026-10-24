-- Prove2me | Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
-- name    : KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:12:54.42354+00:00
-- url     : https://prove2.me/theorems/4127c811-dea8-492d-b12f-3913c7c288bc
-- title:
--   Gaussian projective family and its projective-limit measure
-- statement:
--   Vendored from the BrownianMotion library, repository https://github.com/RemyDegenne/brownian-motion, commit a7ad7af662044313bc80a7c0756360fb3745f931. For a finite set I of nonnegative real times, `brownianCovMatrix I` is the matrix with entries min(s, t), and `gaussianProjectiveFamily I` is the pushforward of the centered multivariate Gaussian with this covariance matrix to functions I → ℝ; `posSemidef_brownianCovMatrix` establishes positive semidefiniteness, and the family is Gaussian and projective. The measure `gaussianLimit` is the projective-limit measure on ℝ≥0 → ℝ, is a probability measure, and has each finite restriction `I.restrict` distributed according to `gaussianProjectiveFamily I`, as recorded by `isProjectiveLimit_gaussianLimit` and `hasLaw_restrict_gaussianLimit`. The auxiliary `L2.posSemidef_interMatrix` result states that the matrix of measures of pairwise intersections of finitely many measurable finite-measure sets is positive semidefinite.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Gaussian/ProjectiveLimit.lean#L32-L200 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Gaussian.ProjectiveLimit`, definition bundle `KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Data.NNReal.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.MetricSeparated

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Gaussian/ProjectiveLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory NormedSpace Set
open scoped ENNReal NNReal
namespace L2
variable {ι : Type*} [Finite ι]
variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
lemma posSemidef_interMatrix {μ : Measure α} {v : ι → (Set α)}
    (hv₁ : ∀ j, MeasurableSet (v j)) (hv₂ : ∀ j, μ (v j) ≠ ∞ := by finiteness) :
    Matrix.PosSemidef (Matrix.of fun i j : ι ↦ μ.real (v i ∩ v j)) := by
  simp only [hv₁, ne_eq, hv₂, not_false_eq_true,
    ← L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
  exact Matrix.posSemidef_gram ℝ _
end L2
namespace ProbabilityTheory
variable {ι : Type*} {d : ℕ}
def brownianCovMatrix (I : Finset ℝ≥0) : Matrix I I ℝ := Matrix.of fun s t ↦ min s.1 t.1
lemma posSemidef_brownianCovMatrix (I : Finset ℝ≥0) :
    (brownianCovMatrix I).PosSemidef := by
  have h : brownianCovMatrix I =
      fun s t ↦ volume.real ((Icc 0 s.1.toReal) ∩ (Icc 0 t.1.toReal)) := by
    simp [Icc_inter_Icc, max_self, Real.volume_real_Icc, sub_zero, le_inf_iff,
      NNReal.zero_le_coe, and_self, sup_of_le_left]
    rfl
  exact h ▸ L2.posSemidef_interMatrix (fun j ↦ measurableSet_Icc)
    (fun j ↦ isCompact_Icc.measure_ne_top)
variable [DecidableEq ι]
noncomputable
def gaussianProjectiveFamily (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  multivariateGaussian 0 (brownianCovMatrix I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm
lemma measurePreserving_equiv_multivariateGaussian (I : Finset ℝ≥0) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (I → ℝ)).symm
      (multivariateGaussian 0 (brownianCovMatrix I)) (gaussianProjectiveFamily I) where
  measurable := by fun_prop
  map_eq := rfl
instance isGaussian_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (gaussianProjectiveFamily I) := by
  unfold gaussianProjectiveFamily
  rw [MeasurableEquiv.coe_toLp_symm_eq]
  infer_instance
lemma isProjectiveMeasureFamily_gaussianProjectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ ↦ ℝ) gaussianProjectiveFamily := by
  intro I J hJI
  nth_rw 2 [gaussianProjectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        (MeasurableEquiv.toLp 2 (J → ℝ)).symm ∘ (EuclideanSpace.restrict₂ hJI) := by
      ext; simp
    rw [this, ((measurePreserving_equiv_multivariateGaussian J).comp
      (measurePreserving_restrict₂_multivariateGaussian
        (posSemidef_brownianCovMatrix I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _ -- fun_prop fails
  · fun_prop
noncomputable
def gaussianLimit : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit gaussianProjectiveFamily isProjectiveMeasureFamily_gaussianProjectiveFamily
instance IsProbabilityMeasure_gaussianLimit :
    IsProbabilityMeasure gaussianLimit :=
  isProbabilityMeasure_projectiveLimit isProjectiveMeasureFamily_gaussianProjectiveFamily
lemma isProjectiveLimit_gaussianLimit :
    IsProjectiveLimit gaussianLimit gaussianProjectiveFamily :=
  isProjectiveLimit_projectiveLimit isProjectiveMeasureFamily_gaussianProjectiveFamily
lemma _root_.MeasureTheory.IsProjectiveLimit.hasLaw_restrict {ι : Type*} {X : ι → Type*}
    {mX : ∀ i, MeasurableSpace (X i)} {μ : Measure (Π i, X i)}
    {P : (I : Finset ι) → Measure (Π i : I, X i)} (h : IsProjectiveLimit μ P) {I : Finset ι} :
    HasLaw I.restrict (P I) μ where
  map_eq := h I
lemma hasLaw_restrict_gaussianLimit {I : Finset ℝ≥0} :
    HasLaw I.restrict (gaussianProjectiveFamily I) gaussianLimit :=
  isProjectiveLimit_gaussianLimit.hasLaw_restrict
end ProbabilityTheory


