-- Prove2me | Definitions.Def_OAIE3v2B071
-- name    : OAIE3v2B071
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:16:30.963487+00:00
-- url     : https://prove2.me/theorems/cd3e2461-31fc-4f93-81af-97c81e874246
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 72 of 311
-- statement:
--   Definitions bundle 72 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B042`, `OAIE3v2B043`, `OAIE3v2B044`, `OAIE3v2B045` of this split.
--
--   Modules: `Dynamics/CubeModeUniformBudget.lean`, `Estimates/CanonicalCoefficientCoverLift.lean`, `Estimates/CocycleHorizontalNormalization.lean`, `Estimates/CoefficientDeckImageCongruence.lean`, `Estimates/CoefficientPairCover.lean`, `Estimates/CoefficientRowEvaluation.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/EmbeddedFiniteConditioning.lean`, `Estimates/FiniteFiberTest.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/LinearQuotientCoverAverage.lean`, `Estimates/MixedBooleanSiteValues.lean`, `Estimates/PartialComplexScaledQuadrature.lean`, `Estimates/PeriodicIsometricAction.lean`, `Estimates/RationalRowReduction.lean`, `Estimates/RealifiedReconstruction.lean`, `Estimates/SplitSmoothProductProfile.lean`, `Estimates/WeightedPatchReparam.lean`, `FixedDensity/GeneratorCells.lean`, `Fourier/AnchoredCoefficientFourierNormalization.lean`, `Fourier/EuclideanCoefficientTorus.lean`, `Fourier/EuclideanJetTorus.lean`, `Geometry/CoefficientDeckChartRecovery.lean`, `Geometry/CoefficientJetCoordinates.lean`, `Geometry/GeometricRetainedCommonCover.lean`, `Lattices/CommonIntegerSiteResidual.lean`, `Lattices/IntegerBoxCoordinateEquiv.lean`, `Lattices/RetainedAffineCommonCover.lean`, `Lattices/SelectedResidueApproximation.lean`, `Lattices/SelectedResidueConstantMean.lean`, `Linear/BooleanJetMatrixFactor.lean`, `Linear/FixedKernelSiteImage.lean`, `Linear/ModeRankLogBudget.lean`, `Linear/TruncatedProjectionError.lean`, `Linear/WeightedLieUpperSpan.lean`, `Polynomial/BooleanJetHighDegree.lean`, `Polynomial/ModeLogPolynomials.lean`, `Probability/FiniteConditionedMass.lean`, `Probability/FiniteDensityMassBound.lean`, `Probability/FiniteProbabilityLipschitz.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B040
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B043
import Definitions.Def_OAIE3v2B044
import Definitions.Def_OAIE3v2B045

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

theorem mean_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : p.mean f ≤ p.mean g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x))

theorem mean_const (c : ℝ) : p.mean (fun _ => c) = c := by
  rw [mean, ← Finset.sum_mul, p.total, one_mul]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω H : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

theorem complexMean_mul_left (a : ℂ) (v : Ω → ℂ) :
    p.complexMean (fun x => a * v x) = a * p.complexMean v := by
  unfold complexMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace FiniteProbabilityWeights

variable (p : FiniteProbabilityWeights Ω) (G : Finset Ω)

omit [DecidableEq Ω] in
theorem mean_const_mul (c : ℝ) (f : Ω → ℝ) :
    p.mean (fun x => c * f x) = c * p.mean f := by
  simp only [mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_sub (f g : X → ℂ) :
    p.complexMean (fun x => f x - g x) = p.complexMean f - p.complexMean g := by
  simp only [complexMean, mul_sub, Finset.sum_sub_distrib]

theorem complexMean_ofReal (f : X → ℝ) :
    p.complexMean (fun x => (f x : ℂ)) = (p.mean f : ℂ) := by
  simp only [complexMean, mean, Complex.ofReal_sum, Complex.ofReal_mul]

theorem norm_complexMean_le_mean_norm (f : X → ℂ) :
    ‖p.complexMean f‖ ≤ p.mean (fun x => ‖f x‖) := by
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro x _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (p.nonneg x)]

theorem norm_complexMean_sub_le (f g : X → ℂ) (e : X → ℝ)
    (h : ∀ x, p.weight x ≠ 0 → ‖f x - g x‖ ≤ e x) :
    ‖p.complexMean f - p.complexMean g‖ ≤ p.mean e := by
  rw [← p.complexMean_sub]
  apply (p.norm_complexMean_le_mean_norm _).trans
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (h x hx) (p.nonneg x)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem uniform_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).mean f = 𝔼 x, f x := by
  simp only [mean, uniform, ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmbeddedFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def ofPositiveWeights {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) : FiniteProbabilityWeights X where
  weight x := w x / ∑ y, w y
  nonneg x := div_nonneg (hw x) hmass.le
  total := by rw [← Finset.sum_div, div_self hmass.ne']

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalRowReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_bounded_rational_right_inverse (A : Matrix ι ι ℚ) (hdet : A.det ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ B : Matrix ι ι ℚ, A * B = 1 ∧
      ∀ i j, RationalHeightLE (B i j) (rationalSolveHeight (Fintype.card ι) H) := by
  let B : Matrix ι ι ℚ := fun i j => rationalCramerSolution A (Pi.single j 1) i
  refine ⟨B, ?_, ?_⟩
  · ext i j
    have h := congrFun (rationalCramerSolution_solves A (Pi.single j 1) hdet) i
    change (A *ᵥ rationalCramerSolution A (Pi.single j 1)) i = (1 : Matrix ι ι ℚ) i j
    simpa only [Pi.single_apply, Matrix.one_apply, eq_comm] using h
  · intro i j
    apply rationalCramerSolution_height A (Pi.single j 1) hdet hA
    intro k
    by_cases hkj : k = j
    · simpa [Pi.single_apply, hkj] using rationalHeightLE_one hH
    · simpa [Pi.single_apply, hkj, Ne.symm hkj] using rationalHeightLE_zero hH

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rationalHeightLE_matrix_mul {ι κ ν : Type*}
    [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℚ) (B : Matrix κ ν ℚ)
    {H K : ℕ} (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hB : ∀ i j, RationalHeightLE (B i j) K) (i : ι) (j : ν) :
    RationalHeightLE ((A * B) i j) ((Fintype.card κ + 1) * (H * K) ^ Fintype.card κ) :=
  rationalHeightLE_sum (fun k => A i k * B k j) (fun k => (hA i k).mul (hB k j))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem exists_bounded_rational_section (A : Matrix ι κ ℚ)
    (hsurj : Function.Surjective A.mulVec) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ S : Matrix κ ι ℚ, A * S = 1 ∧
      ∀ i j, RationalHeightLE (S i j) (rationalSolveHeight (Fintype.card ι) H) := by
  obtain ⟨c, hc, hdet⟩ := exists_nonsingular_columns A hsurj
  obtain ⟨B, hB, hBH⟩ := exists_bounded_rational_right_inverse (A.submatrix id c) hdet
    hH (fun i j => hA i (c j))
  refine ⟨extendRows c B, ?_, ?_⟩
  · rw [mul_extendRows, hB]
  · intro k j
    by_cases hk : k ∈ Set.range c
    · obtain ⟨i, rfl⟩ := hk
      rw [extendRows_apply c hc]
      exact hBH i j
    · rw [extendRows_apply_of_not_mem c B k hk]
      exact rationalHeightLE_zero (rationalSolveHeight_pos _ hH)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*}

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixDenominator_pos (A : Matrix ι κ ℚ) : 0 < matrixDenominator A :=
  arrayDenominator_pos _

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixDenominator_le (A : Matrix ι κ ℚ) {H : ℕ}
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    matrixDenominator A ≤ H ^ (Fintype.card ι * Fintype.card κ) := by
  simpa only [matrixDenominator, Fintype.card_prod] using
    arrayDenominator_le (fun ij : ι × κ => A ij.1 ij.2) (fun ij => (hA ij.1 ij.2).2)

theorem clearedMatrix_cast (A : Matrix ι κ ℚ) :
    (clearedMatrix A).map (Int.castRingHom ℚ) = (matrixDenominator A : ℚ) • A := by
  ext i j
  exact clearedArray_cast (fun ij : ι × κ => A ij.1 ij.2) (i, j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def rectangularWeightHistogram (f : (J → ℝ) → ℝ) (a S : J → ℝ) (R : ℝ) :
    (J → ℝ) → ℝ :=
  finiteRectangularHistogram (rectangularWeightIndices a S R) (rectangularWeight f a S) a S

theorem rectangularWeightHistogram_eq (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) (x : J → ℝ) :
    rectangularWeightHistogram f a S R x = f (rectangularLatticeSample a S x) :=
  finiteRectangularHistogram_eq_round _ _ (rectangularWeight_zero_off_indices f a S hS hsupport)
    a S hS x

theorem rectangularWeightHistogram_integrable (f : (J → ℝ) → ℝ) (a S : J → ℝ) (R : ℝ) :
    Integrable (rectangularWeightHistogram f a S R) := finiteRectangularHistogram_integrable _ _ a S

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

theorem rectangularWeightHistogram_error (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hδ : 0 ≤ δ) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (x : J → ℝ) :
    ‖rectangularWeightHistogram f a S R x - f x‖ ≤ (L : ℝ) * δ := by
  rw [rectangularWeightHistogram_eq f a S hS hsupport]
  exact (hLip.norm_sub_le _ _).trans
    (mul_le_mul_of_nonneg_left (rectangularLatticeSample_error a S hS hδ hmesh x) L.coe_nonneg)

theorem rectangularWeightHistogram_zero_outside (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) (hmesh : ∀ j, 1 / S j ≤ 1) {R : ℝ}
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (x : J → ℝ) (hx : R + 1 < ‖x‖) :
    rectangularWeightHistogram f a S R x = 0 := by
  have he := rectangularLatticeSample_error a S hS zero_le_one hmesh x
  have ht : ‖x‖ ≤ ‖rectangularLatticeSample a S x‖ + ‖rectangularLatticeSample a S x - x‖ := by
    calc
      ‖x‖ = ‖rectangularLatticeSample a S x + (x - rectangularLatticeSample a S x)‖ := by
        congr 1
        abel
      _ ≤ ‖rectangularLatticeSample a S x‖ + ‖x - rectangularLatticeSample a S x‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev x (rectangularLatticeSample a S x)]
  rw [rectangularWeightHistogram_eq f a S hS hsupport]
  exact hsupport _ (by linarith)

theorem rectangularWeightHistogram_l1_error (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    (∫ x, ‖rectangularWeightHistogram f a S R x - f x‖) ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  have hz : ∀ x, R + 1 < ‖x‖ → rectangularWeightHistogram f a S R x - f x = 0 := by
    intro x hx
    rw [rectangularWeightHistogram_zero_outside f a S hS (fun j => (hmesh j).trans hδ1)
      hsupport x hx, hsupport x (by linarith), sub_self]
  have he := integral_norm_le_box (fun x => rectangularWeightHistogram f a S R x - f x)
    (R := R + 1) (C := (L : ℝ) * δ) (by linarith) hz
    (fun x _ => rectangularWeightHistogram_error f hLip a S hS hδ hmesh hsupport x)
  exact he.trans_eq (by rw [mul_add, mul_one]; ring)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem smoothProductProfile_eq_cutoff (I : Type*) [Fintype I] :
    smoothProductProfile I = coordinateBoxCutoff smoothProbabilityProfile 1 := by
  funext x
  simp [smoothProductProfile, coordinateBoxCutoff]

theorem smoothProductProfile_integral (I : Type*) [Fintype I] :
    (∫ x, smoothProductProfile I x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun _ : I => smoothProbabilityProfile) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [smoothProbabilityProfile_integral, Finset.prod_const_one]

theorem smoothProductProfile_lipschitz (I : Type*) [Fintype I] :
    LipschitzWith (Fintype.card I * probabilityProfileLipschitz) (smoothProductProfile I) := by
  rw [smoothProductProfile_eq_cutoff]
  simpa only [div_one, NNReal.coe_one] using
    lipschitz_coordinateBoxCutoff smoothProbabilityProfile probabilityProfileLipschitz 1
      zero_lt_one smoothProbabilityProfile_range smoothProbabilityProfile_lipschitz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TruncatedProjectionError
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_sum {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (f : J → X → ℂ) :
    p.complexMean (fun x => ∑ j, f j x) = ∑ j, p.complexMean (f j) := by
  simp only [complexMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem norm_weighted_complexMean_sub_le_mean_norm {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (w f g : X → ℂ) {ρ : ℝ}
    (he : ∀ x, p.weight x ≠ 0 → ‖f x - g x‖ ≤ ρ) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * g x)‖ ≤
      ρ * p.mean (fun x => ‖w x‖) := by
  apply (p.norm_complexMean_sub_le _ _ (fun x => ρ * ‖w x‖) ?_).trans_eq
    (p.mean_const_mul ρ _)
  intro x hx
  rw [← mul_sub, norm_mul, mul_comm ρ]
  exact mul_le_mul_of_nonneg_left (he x hx) (norm_nonneg _)

theorem complexMean_weighted_expansion {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (w : X → ℂ) (c : J → ℂ) (u : J → X → ℂ) :
    p.complexMean (fun x => w x * ∑ j, c j * u j x) =
      ∑ j, c j * p.complexMean (fun x => w x * u j x) := by
  simp only [Finset.mul_sum]
  rw [p.complexMean_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← p.complexMean_mul_left]
  congr 1
  funext x
  ring

theorem weighted_expansion_discard_error {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (w : X → ℂ) (c : J → ℂ) (u : J → X → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hdiscard : ∀ j, ¬ keep j → ‖p.complexMean (fun x => w x * u j x)‖ ≤ τ) :
    ‖p.complexMean (fun x => w x * ∑ j, c j * u j x) -
      p.complexMean (fun x => w x * ∑ j, if keep j then c j * u j x else 0)‖ ≤ C * τ := by
  have he : (fun x => w x * ∑ j, if keep j then c j * u j x else 0) =
      (fun x => w x * ∑ j, (if keep j then c j else 0) * u j x) := by
    funext x
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : keep j <;> simp [hj]
  rw [he, p.complexMean_weighted_expansion, p.complexMean_weighted_expansion,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j, ‖c j‖ * τ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : keep j
      · simp only [hj, ite_true, sub_self, norm_zero]
        exact mul_nonneg (norm_nonneg _) hτ
      · simp only [hj, ite_false, zero_mul, sub_zero, norm_mul]
        exact mul_le_mul_of_nonneg_left (hdiscard j hj) (norm_nonneg _)
    _ = (∑ j, ‖c j‖) * τ := (Finset.sum_mul _ _ _).symm
    _ ≤ C * τ := mul_le_mul_of_nonneg_right hc hτ

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem weighted_projection_comparison {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (w f F G g : X → ℂ) {B η ε : ℝ}
    (hη : 0 ≤ η) (hw : p.mean (fun x => ‖w x‖) ≤ B)
    (hF : ∀ x, p.weight x ≠ 0 → ‖f x - F x‖ ≤ η)
    (hG : ∀ x, p.weight x ≠ 0 → ‖G x - g x‖ ≤ η)
    (hprojection : ‖p.complexMean (fun x => w x * F x) -
      p.complexMean (fun x => w x * G x)‖ ≤ ε) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * g x)‖ ≤
      2 * B * η + ε := by
  have hfirst := (p.norm_weighted_complexMean_sub_le_mean_norm w f F hF).trans
    (mul_le_mul_of_nonneg_left hw hη)
  have hlast := (p.norm_weighted_complexMean_sub_le_mean_norm w G g hG).trans
    (mul_le_mul_of_nonneg_left hw hη)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * f x)) (p.complexMean (fun x => w x * F x))
    (p.complexMean (fun x => w x * g x))
  have htri' := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * F x)) (p.complexMean (fun x => w x * G x))
    (p.complexMean (fun x => w x * g x))
  linarith

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteDensityMassBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteSupportProbability_complexMean {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (f : X → ℂ) :
    (finiteSupportProbability w S hw0 hw hZ).complexMean (fun x => f x.val) =
      ∑' x, ((w x / (∑' y, w y) : ℝ) : ℂ) * f x := by
  change (∑ x : S, ((w x.val / (∑' y, w y) : ℝ) : ℂ) * f x.val) = _
  calc
    _ = ∑ x ∈ S, ((w x / (∑' y, w y) : ℝ) : ℂ) * f x :=
      Finset.sum_coe_sort S _
    _ = _ := (finite_normalized_test_sum w S hw _ f).symm

theorem normalized_finite_weight_discard_error {X J : Type*} [Fintype J]
    (v : X → ℝ) (S : Finset X) (hv0 : ∀ x, 0 ≤ v x)
    (hv : ∀ x ∉ S, v x = 0) (hZ : 0 < ∑' x, v x)
    (w : X → ℂ) (c : J → ℂ) (u : J → X → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hdiscard : ∀ j, ¬keep j →
      ‖∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * u j x)‖ ≤ τ) :
    ‖(∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * ∑ j, c j * u j x)) -
      ∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * ∑ j, if keep j then c j * u j x else 0)‖ ≤ C * τ := by
  have hdiscard' (j) (hj : ¬keep j) :
      ‖(finiteSupportProbability v S hv0 hv hZ).complexMean (fun x => w x.val * u j x.val)‖ ≤ τ := by
    rw [finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * u j x)]
    exact hdiscard j hj
  have h := (finiteSupportProbability v S hv0 hv hZ).weighted_expansion_discard_error
    (fun x => w x.val) c (fun j x => u j x.val) keep hc hτ hdiscard'
  rw [finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * ∑ j, c j * u j x),
    finiteSupportProbability_complexMean v S hv0 hv hZ
      (fun x => w x * ∑ j, if keep j then c j * u j x else 0)] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

theorem residueSmoothWeight_at {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (V : K × I → ℝ) (x : K × I → ℤ) :
    residueSmoothWeight residue modulus V (residueLatticeArray residue modulus x) =
      smoothProductProfile (K × I) (fun z => (residueLatticeArray residue modulus x z : ℝ) / V z) := by
  have hc := (residueLatticeArray_range residue modulus _).mp ⟨x, rfl⟩
  simp [residueSmoothWeight, hc]

theorem residueSmoothWeight_mass {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) :
    shiftedSmoothProductMass (residueProfileCenter residue modulus) (residueProfileWidth modulus V) =
      ∑' y, residueSmoothWeight residue modulus V y := by
  have hs : Function.support (residueSmoothWeight residue modulus V) ⊆
      Set.range (residueLatticeArray residue modulus) := by
    intro y hy
    apply (residueLatticeArray_range residue modulus y).mpr
    by_contra hn
    exact hy (by simp only [residueSmoothWeight, hn, ite_false])
  have he := (residueLatticeArray_injective residue modulus hmodulus).tsum_eq hs
  simpa only [shiftedSmoothProductMass, rectangularWeight,
    residueProfile_point residue modulus hmodulus V hV, residueSmoothWeight_at] using he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueSmoothWeight_mass {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) :
    (∑' x, selectedResidueSmoothWeight modulus G V x) =
      ∑ r : G, ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x := by
  simp_rw [selectedResidueSmoothWeight_eq_sum]
  exact finite_supported_weight_sum_tsum _ (rectangularWeightIndices 0 V 1)
    (fun r => residueSmoothWeight_zero_off _ modulus V hV)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueSmoothWeight_summable {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z) : Summable (selectedResidueSmoothWeight modulus G V) :=
  (hasSum_sum_of_ne_finset_zero (selectedResidueSmoothWeight_zero_off modulus G V hV)).summable

theorem selectedResidueSmoothWeight_mass_pos {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus)) (hG : G.Nonempty)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hc : ∀ r : G, 0 < ∑' x, residueSmoothWeight (columnResidueRepresentative modulus r.val) modulus V x) :
    0 < ∑' x, selectedResidueSmoothWeight modulus G V x := by
  obtain ⟨r, hr⟩ := hG
  rw [selectedResidueSmoothWeight_mass modulus G V hV]
  exact (hc ⟨r, hr⟩).trans_le
    (Finset.single_le_sum (fun s _ => (hc s).le) (Finset.mem_univ (⟨r, hr⟩ : G)))

noncomputable def selectedResidueSmoothPMF {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) : PMF (K × I → ℤ) :=
  realWeightPMF (selectedResidueSmoothWeight modulus G V)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_summable modulus G V hV) hZ

theorem selectedResidueSmoothPMF_toReal {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (x : K × I → ℤ) :
    (selectedResidueSmoothPMF modulus G V hV hZ x).toReal =
      selectedResidueSmoothWeight modulus G V x / ∑' y, selectedResidueSmoothWeight modulus G V y :=
  realWeightPMF_apply _ _ _ _ x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_bounded_rational_image_section {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ S : Matrix κ ι ℚ, A * S * A = A ∧
      ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H) := by
  classical
  obtain ⟨r, hr, rows, _, hsurj, hker⟩ := exists_independent_defining_rows A
  let R := A.submatrix rows id
  let T := (1 : Matrix ι ι ℚ).submatrix rows id
  have hTA : T * A = R := by
    ext i j
    simp [T, R, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply]
  obtain ⟨U, hU, hUH⟩ := exists_bounded_rational_section R hsurj hH (fun i j => hA (rows i) j)
  let S := U * T
  have hpoint (x : κ → ℚ) : A *ᵥ (S *ᵥ (A *ᵥ x)) = A *ᵥ x := by
    have hzero : R *ᵥ (S *ᵥ (A *ᵥ x) - x) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      have hm : R * S * A = R := by
        dsimp [S]
        rw [← Matrix.mul_assoc, hU, Matrix.one_mul, hTA]
      rw [hm, sub_self]
    have hmem : S *ᵥ (A *ᵥ x) - x ∈ LinearMap.ker A.mulVecLin := by
      rw [← hker]
      exact hzero
    change A *ᵥ (S *ᵥ (A *ᵥ x) - x) = 0 at hmem
    rw [Matrix.mulVec_sub, sub_eq_zero] at hmem
    exact hmem
  refine ⟨S, Matrix.ext_iff_mulVec.mpr (fun x => by
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hpoint x), ?_⟩
  have hT : ∀ i j, RationalHeightLE (T i j) 1 := by
    intro i j
    by_cases hij : rows i = j
    · simpa [T, Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
    · simpa [T, Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
  intro i j
  have hs := rationalHeightLE_matrix_mul U T hUH hT i j
  apply hs.mono
  simp only [Fintype.card_fin, mul_one]
  apply le_trans _ (rationalKernelHeight_mono hH hr)
  unfold rationalKernelHeight
  apply Nat.mul_le_mul (by omega)
  apply pow_le_pow_left₀ (Nat.zero_le _)
  exact le_mul_of_one_le_right (Nat.zero_le _) hH

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeriodicIsometricAction
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators NNReal

variable {X : Type*} [TopologicalSpace X] [AddAction Circle X] [ContinuousVAdd Circle X]

noncomputable def circleFejerSum (N : ℕ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ h ∈ fejerFrequencies N, (fejerCoefficient N h : ℂ) * circleFourierComponent (-h) f x

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal BigOperators

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def smooth (A : IsometricCircleAction X) (N : ℕ) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  circleFejerSum N f

end IsometricCircleAction
end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct NNReal

theorem matrixDenominator_allowance_le_exp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (l H : ℕ) (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((l * matrixDenominator A : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hD : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply (Nat.cast_le.mpr (matrixDenominator_le A hA)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg H) hH _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [Nat.cast_mul]
    calc
      (Fintype.card ι : ℝ) * Fintype.card κ * p ≤ (p + 2) * (p + 2) * (p + 2) := by
        gcongr <;> linarith
      _ = (p + 2) ^ 3 := by ring
  rw [Nat.cast_mul]
  calc
    (l : ℝ) * matrixDenominator A ≤ Real.exp p * Real.exp ((p + 2) ^ 3) :=
      mul_le_mul hl hD (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (p + (p + 2) ^ 3) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ 4) := by
      apply Real.exp_le_exp.mpr
      have hp3 := le_power_budget hp (by decide : 1 ≤ 3)
      nlinarith [mul_nonneg hp (pow_nonneg (by linarith : (0 : ℝ) ≤ p + 2) 3)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ModeRankLogBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem modeRemovalRankThreshold_le_exp (m n d : ℕ) {P C D S ρ ε : ℝ}
    (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) (hd : (d : ℝ) ≤ P)
    (hC : 0 ≤ C) (hCP : C ≤ Real.exp P) (hD : 0 ≤ D) (hDP : D ≤ Real.exp P)
    (hS : 0 ≤ S) (hSP : S ≤ Real.exp P) (hρ : 0 < ρ) (hρInv : 1 / ρ ≤ Real.exp P)
    (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    modeRemovalRankThreshold m n d C D S ρ ε ≤ Real.exp (modeRankLog m P) := by
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε)
  let A := 2 * modeRemovalShrink m d D ρ ε
  have hB : B ≤ Real.exp (modeBiasLog m P) := chosenBiasBudget_le_exp m hP hε hεInv
  have hB0 : 0 ≤ B := zero_le_one.trans (finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε))
  have hT0 := modeRemovalShrink_one_le m d hD hρ hε
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hT := modeRemovalShrink_le_exp m d hP hd hD hDP hρ hρInv hε hεInv
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hA : A ≤ Real.exp (modeShrinkLog m P + 2) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (modeShrinkLog m P) := by dsimp [A]; gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hnp : (n : ℝ) ≤ Real.exp P := hn.trans (by linarith [Real.add_one_le_exp P])
  have hBL := modeBiasLog_nonneg m hP
  have hTL := modeShrinkLog_nonneg m hP
  let cost (i : Fin m) := ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) +
    (B * S ^ (i.val + 1)) ^ (n ^ (i.val + 1)) +
    (n : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B)
  let bound (i : Fin m) :=
    ((((i.val + 1).factorial : ℝ) + P + (i.val + 1 : ℕ) * P) +
      P ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P) +
      ((i.val + 1 : ℕ) * P + (i.val + 1 : ℕ) * (modeShrinkLog m P + 2) + modeBiasLog m P) + 2)
  have hbound i : 0 ≤ bound i := by dsimp [bound]; positivity
  have hcost (i : Fin m) : cost i ≤ Real.exp (bound i) := by
    have hf : ((i.val + 1).factorial : ℝ) ≤ Real.exp ((i.val + 1).factorial : ℝ) := by
      linarith [Real.add_one_le_exp ((i.val + 1).factorial : ℝ)]
    have hrow : ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) ≤
        Real.exp (((i.val + 1).factorial : ℝ) + P + (i.val + 1 : ℕ) * P) := by
      calc
        _ ≤ Real.exp ((i.val + 1).factorial : ℝ) * (Real.exp P * (Real.exp P) ^ (i.val + 1)) := by gcongr
        _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hden : (B * S ^ (i.val + 1)) ^ (n ^ (i.val + 1)) ≤
        Real.exp (P ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P)) := by
      calc
        _ ≤ (Real.exp (modeBiasLog m P) * (Real.exp P) ^ (i.val + 1)) ^ (n ^ (i.val + 1)) := by gcongr
        _ = Real.exp ((n : ℝ) ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul, Nat.cast_pow]
        _ ≤ _ := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hn _) (by positivity))
    have hcoeff : (n : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B) ≤
        Real.exp ((i.val + 1 : ℕ) * P + (i.val + 1 : ℕ) * (modeShrinkLog m P + 2) + modeBiasLog m P) := by
      calc
        _ ≤ (Real.exp P) ^ (i.val + 1) * ((Real.exp (modeShrinkLog m P + 2)) ^ (i.val + 1) *
          Real.exp (modeBiasLog m P)) := by gcongr
        _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsum := add_le_exp_add_one (by positivity) (by positivity) hrow hden
    have hsum' := add_le_exp_add_one (by positivity) (by positivity) hsum hcoeff
    convert hsum' using 1
    congr 1
    dsimp [bound]
    ring
  have hsum := sum_le_exp_card_add_sum cost bound hbound hcost
  have hout := one_add_le_exp_succ (by positivity) hsum
  change 1 + ∑ i : Fin m, cost i ≤ _
  convert hout using 1
  congr 1
  simp only [modeRankLog, Fintype.card_fin]
  dsimp [bound]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ModeLogPolynomials
namespace OAI

section

namespace Erdos3

open Polynomial
open scoped BigOperators

theorem exists_mode_threshold_exp_budget (m : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F D S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ D → D ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeRemovalSideThreshold m d D S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F D S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget (modeSideLogPolynomial m + modeRankLogPolynomial m)
  refine ⟨K, hK, ?_⟩
  intro n d P F D S ρ ε hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP
  have hp : modeSideLog m P + modeRankLog m P ≤ (P + K) ^ K := by
    simpa only [Polynomial.eval₂_add, modeSideLogPolynomial_eval, modeRankLogPolynomial_eval] using hpoly P hP
  have hs := modeSideLog_nonneg m hP
  have hr := modeRankLog_nonneg m hP
  constructor
  · exact (modeRemovalSideThreshold_le_exp m d hP hd hD hDP hS hSP hρ hρP hε hεP).trans
      (Real.exp_le_exp.mpr (by linarith))
  · exact (modeRemovalRankThreshold_le_exp m n d hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP).trans
      (Real.exp_le_exp.mpr (by linarith))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CubeModeUniformBudget
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Polynomial

theorem exists_cube_mode_threshold_exp_budget (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F L S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ L → L ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeRemovalSideThreshold m d (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K₀, _, hthreshold⟩ := exists_mode_threshold_exp_budget m
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget ((cubeInputLogPolynomial q + C K₀) ^ K₀)
  refine ⟨K, hK, ?_⟩
  intro n d P F L S ρ ε hP hn hd hF hFP hL hLP hS hSP hρ hρP hε hεP
  let P' := (cubeInputLogPolynomial q).eval₂ (Nat.castRingHom ℝ) P
  have hPP : P ≤ P' := cubeInputLogPolynomial_ge q hP
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  obtain ⟨hs, hr⟩ := hthreshold n d P' F (cubeModePolynomialBudget q L) S ρ ε
    (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hF (hFP.trans hEP)
    (cubeModePolynomialBudget_pos q hL).le (cubeModePolynomialBudget_le_exp_input q hP hL hLP)
    hS (hSP.trans hEP) hρ (hρP.trans hEP) hε (hεP.trans hEP)
  have hb : (P' + K₀) ^ K₀ ≤ (P + K) ^ K := by
    simpa [P', Polynomial.eval₂_pow] using hpoly P hP
  exact ⟨hs.trans (Real.exp_le_exp.mpr hb), hr.trans (Real.exp_le_exp.mpr hb)⟩

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)

theorem linearQuotientAverage_character [MeasurableSpace (V ⧸ Γ)] [MeasurableAdd₂ (V ⧸ Γ)]
    (μ : Measure (V ⧸ Γ)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : V →ₗ[ℝ] ℝ) (hL : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (x : V ⧸ Γ) :
    linearQuotientAverage Γ R hR μ (quotientLinearCharacter Γ L hL) x =
      if L.comp R = 0 then quotientLinearCharacter Γ L hL x else 0 := by
  have hr : ∀ y ∈ Γ, ∃ n : ℤ, L.comp R y = n := fun y hy => hL (R y) (hR y hy)
  have he (y : V ⧸ Γ) :
      quotientLinearCharacter Γ L hL (linearQuotientEndomorphism Γ R hR y) =
        quotientLinearCharacter Γ (L.comp R) hr y := by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective Γ y
    rfl
  unfold linearQuotientAverage
  simp_rw [quotientLinearCharacter_add, he]
  rw [integral_const_mul, quotientLinearCharacter_integral]
  split_ifs <;> simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
namespace OAI

section

open scoped Matrix NNReal

namespace Erdos3

theorem real_image_section_denominator_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix κ ι ℚ) (H l : ℕ)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator S * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 36) := by
  have hpq : p ≤ (p + 2) ^ 7 := le_power_budget hp (by decide)
  have h := matrixDenominator_allowance_le_exp S l (rationalKernelHeight (Fintype.card ι) H)
    hS (by positivity : 0 ≤ (p + 2) ^ 7) (hκ.trans hpq) (hι.trans hpq)
    (rationalKernelHeight_le_budget (Fintype.card ι) H hp hι hH)
    (hl.trans (Real.exp_le_exp.mpr hpq))
  rw [Nat.mul_comm] at h
  exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 7 4))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem booleanJetExtractionMatrix_mul_boundedSite {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α) :
    booleanJetExtractionMatrix rows *
        VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) =
      boundedCoefficientJetMatrix root D h rows := by
  ext o e
  change (booleanJetExtractionMatrix rows *ᵥ
    (fun t => VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) t e)) o = _
  rw [booleanJetExtractionMatrix_mulVec]
  change booleanCoefficient _ (rows o) = booleanCoefficient _ (rows o)
  congr 1
  funext t
  simp [VectorPolynomial.boundedSiteMatrix, MvPolynomial.eval_monomial, Finsupp.prod,
    boundedCoefficientIntegerExponentEquiv]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem coefficientCoordinateTorus_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Continuous (coefficientCoordinateTorus (K := K) U) := by
  apply continuous_pi
  intro s
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (coefficientCoordinateArray U s).continuous_of_finiteDimensional

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

noncomputable def coefficientSiteTorusMap {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) :
    CoefficientTorus (K := K) U →+ SiteTorus S U :=
  AddMonoidHom.pi (fun j => (integerMatrixTorusMap (U j) (boundedSiteMatrix (j.val + 1) site)).comp
    (coefficientLayerTorus U j))

theorem coefficientSiteTorusMap_mk {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ)
    (x : CoefficientArray (K := K) U) (j : Fin m) :
    coefficientSiteTorusMap U site (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) j =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice S (U j))
        (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
          (coefficientLayerArray U j x)) := rfl

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem matrixModuleAction_surjective_of_period {I S W : Type*}
    [Fintype I] [Fintype S] [AddCommGroup W] [Module ℝ W]
    (E : Matrix S I ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice S a ≤ E.mulVecLin.range) :
    Function.Surjective (matrixModuleAction (W := W) (fun s i => (E s i : ℝ))) := by
  classical
  obtain ⟨n, hn⟩ := exists_integer_kernel_dual E a hperiod
  let e : S → I → ℤ := E
  let A : Matrix S I ℝ := Matrix.of (fun s i => (e s i : ℝ))
  let T : Matrix I S ℝ := fun i s => (n s i : ℝ) / a
  have hET : A * T = 1 := by
    ext s r
    have hsum : (∑ i, (n r i : ℝ) * (e s i : ℝ)) = if r = s then (a : ℝ) else 0 := by
      exact_mod_cast hn r s
    change (∑ i, (e s i : ℝ) * ((n r i : ℝ) / a)) = _
    have hswap : (∑ i, (e s i : ℝ) * ((n r i : ℝ) / a)) =
        (∑ i, (n r i : ℝ) * (e s i : ℝ)) / a := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hswap, hsum]
    by_cases hrs : r = s
    · subst r
      simp [ha]
    · simp [hrs, Ne.symm hrs]
  intro y
  refine ⟨matrixModuleAction T y, ?_⟩
  change matrixModuleAction A (matrixModuleAction T y) = y
  calc
    _ = matrixModuleAction (A * T) y := matrixModuleAction_mul A T y
    _ = matrixModuleAction (1 : Matrix S S ℝ) y := congrArg (fun M => matrixModuleAction M y) hET
    _ = y := by ext s; simp [matrixModuleAction_apply, Matrix.one_apply]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

noncomputable def coefficientBooleanJetTorusMap {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) : CoefficientTorus (K := K) U →+ BooleanJetTorus O U :=
  (siteBooleanJetTorusMap U rows).comp (coefficientSiteTorusMap U (integerAffineCube root D))

theorem coefficientBooleanJetTorusMap_mk {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) (x : CoefficientArray (K := K) U) (j : Fin m) :
    coefficientBooleanJetTorusMap U root D rows
        (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) j =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice (O j) (U j))
        (matrixModuleAction
          (fun o e => (boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e : ℝ))
          (coefficientLayerArray U j x)) := by
  change integerMatrixTorusMap (U j) (booleanJetExtractionMatrix (rows j))
    (integerMatrixTorusMap (U j) (boundedSiteMatrix (j.val + 1) (integerAffineCube root D))
      (QuotientAddGroup.mk' _ (coefficientLayerArray U j x))) = _
  rw [integerMatrixTorusMap_comp, booleanJetExtractionMatrix_mul_boundedSite]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def euclideanJetEquiv : BooleanJetTorus O U ≃+ EuclideanJetLayers U O where
  toFun x j o := (euclideanSubspaceTorusEquiv (U j)).symm (arrayCoordinateEquiv (U j) (x j) o)
  invFun y j := (arrayCoordinateEquiv (U j)).symm (fun o => euclideanSubspaceTorusEquiv (U j) (y j o))
  left_inv x := by
    funext j
    apply (arrayCoordinateEquiv (U j)).injective
    rw [AddEquiv.apply_symm_apply]
    funext o
    exact (euclideanSubspaceTorusEquiv (U j)).apply_symm_apply _
  right_inv y := by
    funext j o
    dsimp only
    rw [AddEquiv.apply_symm_apply]
    exact (euclideanSubspaceTorusEquiv (U j)).symm_apply_apply _
  map_add' x y := by
    funext j o
    simp only [map_add, Pi.add_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanCoefficientTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem euclideanCoefficientEquiv_apply (x : CoefficientTorus (K := K) U)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U x j d = (euclideanSubspaceTorusEquiv (U j)).symm
      (coefficientCoordinateTorus U x ⟨j, d⟩) := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCoefficientCoverLift
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def canonicalCoefficientCoverLift (d : ℕ)
    (x : CoefficientSamplerArrays (K := K) I n) : CoefficientTorus (K := K) U :=
  (euclideanCoefficientEquiv U).symm (fun j e =>
    normalizedCoverLift (euclideanSubspace (U j)) (b j) (hb j) d
      (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanJetHighDegree
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem normalSpan_high_jet_zero {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P ∈ normalSpan h)
    (s : Finset α) (hs : h < s.card) :
    booleanCoefficient (fun t => eval (site t) P) s = 0 := by
  change ((coefficientLinear s).comp siteEvaluation) P = 0
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨t, ht, rfl⟩ := hP
    change booleanCoefficient (fun u => eval (site u) (normalMonomial h t)) s = 0
    rw [normalMonomial_jet, if_neg]
    intro he
    subst t
    omega
  | zero => exact map_zero _
  | add P Q _ _ hP hQ => rw [map_add, hP, hQ, add_zero]
  | smul a P _ hP => rw [map_smul, hP, smul_zero]

theorem homogeneous_high_jet_zero {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P.IsHomogeneous h)
    (s : Finset α) (hs : h < s.card) :
    booleanCoefficient (fun t => eval (site t) P) s = 0 := by
  obtain ⟨A, hA, B, hB, rfl⟩ := Submodule.mem_sup.mp (homogeneous_mem_reductionSpace hP)
  simp_rw [map_add, vanishingSpan_eval_zero hA, zero_add]
  exact normalSpan_high_jet_zero hB s hs

theorem frameLift_eval_site {α K R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (root : K → R) (D : α → K → R) (P : MvPolynomial (Option K) R) (s : Finset α) :
    eval (site s) (frameLift root D P) = eval (affineSite root D s) P := by
  have he : (aeval (site (β := K) s)).comp (frameLift root D) =
      aeval (affineSite root D s) := by
    apply algHom_ext
    intro v
    cases v with
    | none => simp [frameLift, liftCoordinate, site, affineSite]
    | some k =>
      simp [frameLift, liftCoordinate, site, affineSite, Finset.sum_ite_mem]
  exact AlgHom.congr_fun he P

theorem boundedSiteMatrix_high_jet_zero {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ)
    (e : VectorPolynomial.BoundedCoefficientExponent K h) (s : Finset α) (hs : h < s.card) :
    booleanCoefficient (fun t => VectorPolynomial.boundedSiteMatrix h
      (integerAffineCube root D) t e) s = 0 := by
  let d : α → K → ℤ := D
  change booleanCoefficient (fun t => VectorPolynomial.boundedSiteMatrix h
    (integerAffineCube root d) t e) s = 0
  have hp := homogeneous_high_jet_zero
    (frameLift_homogeneous root d (homogenizingMonomial_homogeneous (R := ℤ) h e.val e.property)) s hs
  simp_rw [frameLift_eval_site] at hp
  convert hp using 1
  apply congrArg (fun f => booleanCoefficient f s)
  funext t
  simp [homogenizingMonomial, affineSite, VectorPolynomial.boundedSiteMatrix,
    MvPolynomial.eval_rename, MvPolynomial.eval_monomial, integerAffineCube, Finsupp.prod]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

theorem boundedBooleanReconstruction_siteMatrix {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) :
    boundedBooleanReconstructionMatrix α h *
        booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α h → Finset α) *
        VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) =
      VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) := by
  let E := VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D)
  let F := booleanJetExtractionMatrix (id : Finset α → Finset α) * E
  have hz (r : Finset α) (hr : h < r.card) (e) : F r e = 0 := by
    change (booleanJetExtractionMatrix id *ᵥ (fun t => E t e)) r = 0
    rw [booleanJetExtractionMatrix_mulVec]
    exact BooleanCubeKernel.boundedSiteMatrix_high_jet_zero root D h e r hr
  rw [Matrix.mul_assoc]
  ext s e
  change (∑ r : BoundedBooleanJet α h, booleanReconstructionMatrix α s r.val * F r.val e) = E s e
  calc
    _ = ∑ r ∈ Finset.univ.filter (fun r : Finset α => r.card ≤ h),
        booleanReconstructionMatrix α s r * F r e :=
      (Finset.sum_subtype _ (by simp) _).symm
    _ = ∑ r : Finset α, booleanReconstructionMatrix α s r * F r e := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r _ hr
      have hh : h < r.card := by simpa using hr
      rw [hz r hh, mul_zero]
    _ = (booleanReconstructionMatrix α * F) s e := rfl
    _ = E s e := by
      dsimp only [F]
      rw [← Matrix.mul_assoc, booleanReconstruction_mul_extraction, Matrix.one_mul]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

noncomputable def euclideanCoefficientJetMap {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α) :
    CoefficientTorus (K := K) U →+ EuclideanJetLayers U O :=
  (euclideanJetEquiv U).toAddMonoidHom.comp (coefficientBooleanJetTorusMap U root D rows)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientJetCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

theorem arrayCoordinateTorus_coefficientLayer {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientTorus (K := K) U)
    (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
    arrayCoordinateTorus (U j) (coefficientLayerTorus U j x) e =
      coefficientCoordinateTorus U x ⟨j, e⟩ := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rfl

theorem coefficientBooleanJetTorusMap_layer {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) (x : CoefficientTorus (K := K) U) (j : Fin m) :
    coefficientBooleanJetTorusMap U root D rows x j =
      integerMatrixTorusMap (U j) (boundedCoefficientJetMatrix root D (j.val + 1) (rows j))
        (coefficientLayerTorus U j x) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [coefficientBooleanJetTorusMap_mk]
  rfl

theorem euclideanCoefficientJetMap_apply {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (x : CoefficientTorus (K := K) U) (j : Fin m) (o : O j) :
    euclideanCoefficientJetMap U root D rows x j o =
      ∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e •
        euclideanCoefficientEquiv U x j e := by
  change (euclideanSubspaceTorusEquiv (U j)).symm
    (arrayCoordinateTorus (U j) (coefficientBooleanJetTorusMap U root D rows x j) o) = _
  rw [coefficientBooleanJetTorusMap_layer, arrayCoordinateTorus_integerMatrix, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, arrayCoordinateTorus_coefficientLayer]
  rfl

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonIntegerSiteResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

theorem clearedMatrix_real {I S : Type*} [Fintype I] [Fintype S]
    (T : Matrix I S ℚ) (i : I) (s : S) :
    (clearedMatrix T i s : ℝ) = (matrixDenominator T : ℝ) * (T i s : ℝ) := by
  have h := congrFun (congrFun (clearedMatrix_cast T) i) s
  change (clearedMatrix T i s : ℚ) = (matrixDenominator T : ℚ) * T i s at h
  exact_mod_cast h

theorem matrixModuleAction_cleared {I S W : Type*} [Fintype I] [Fintype S]
    [AddCommGroup W] [Module ℝ W] (T : Matrix I S ℚ) (x : S → W) :
    matrixModuleAction (fun i s => (clearedMatrix T i s : ℝ)) x =
      (matrixDenominator T : ℝ) • matrixModuleAction (fun i s => (T i s : ℝ)) x := by
  funext i
  change (∑ s, (clearedMatrix T i s : ℝ) • x s) =
    (matrixDenominator T : ℝ) • ∑ s, (T i s : ℝ) • x s
  simp only [clearedMatrix_real, mul_smul, Finset.smul_sum]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix Classical

theorem cleared_image_section_entry_bound {I S : Type*} [Fintype I] [Fintype S]
    (T : Matrix I S ℚ) (H : ℕ)
    (hT : ∀ i s, RationalHeightLE (T i s) (rationalKernelHeight (Fintype.card S) H))
    {P : ℝ} (hP : 0 ≤ P) (hI : (Fintype.card I : ℝ) ≤ P)
    (hS : (Fintype.card S : ℝ) ≤ P) (hH : (H : ℝ) ≤ Real.exp P) (i : I) (s : S) :
    |(clearedMatrix T i s : ℝ)| ≤ Real.exp (2 * (P + 2) ^ 36) := by
  have hden : (matrixDenominator T : ℝ) ≤ Real.exp ((P + 2) ^ 36) := by
    simpa only [Nat.mul_one] using real_image_section_denominator_bound T H 1 hT hP hS hI hH
      (by simpa using Real.one_le_exp hP)
  have hentry := (hT i s).abs_real_le.trans
    (rationalKernelHeight_le_budget (Fintype.card S) H hP hS hH)
  have hpow : (P + 2) ^ 7 ≤ (P + 2) ^ 36 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  rw [clearedMatrix_real, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ Real.exp ((P + 2) ^ 36) * Real.exp ((P + 2) ^ 7) :=
      mul_le_mul hden hentry (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((P + 2) ^ 36 + (P + 2) ^ 7) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2 * (P + 2) ^ 36) := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelSiteImage
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem boundedSiteMatrix_fixed_kernel_factor {α K I : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype I]
    (root₀ : K → ℤ) (D₀ : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D₀.mulVecLin.range)
    (h : ℕ) (root : I → ℤ) (D : Matrix α I ℤ) :
    ∃ R : Matrix (VectorPolynomial.BoundedCoefficientExponent K h)
        (VectorPolynomial.BoundedCoefficientExponent I h) ℝ,
      Matrix.of (fun s d => (VectorPolynomial.boundedSiteMatrix h (integerAffineCube root₀ D₀) s d : ℝ)) * R =
        Matrix.of (fun s d => (VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) s d : ℝ)) := by
  classical
  let B := boundedBooleanReconstructionMatrix α h
  let T := booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α h → Finset α)
  let E₀ := VectorPolynomial.boundedSiteMatrix h (integerAffineCube root₀ D₀)
  let E := VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D)
  let B' := Matrix.of (fun s j => (B s j : ℝ))
  let T' := Matrix.of (fun j s => (T j s : ℝ))
  let E₀' := Matrix.of (fun s d => (E₀ s d : ℝ))
  let E' := Matrix.of (fun s d => (E s d : ℝ))
  have h₀ : B' * T' * E₀' = E₀' := by
    ext s d
    have hz := congrArg (fun z : ℤ => (z : ℝ))
      (congrFun (congrFun (boundedBooleanReconstruction_siteMatrix root₀ D₀ h) s) d)
    simpa only [B', T', E₀', B, T, E₀, Matrix.mul_apply, Matrix.of_apply,
      Int.cast_sum, Int.cast_mul] using hz
  have hE : B' * T' * E' = E' := by
    ext s d
    have hz := congrArg (fun z : ℤ => (z : ℝ))
      (congrFun (congrFun (boundedBooleanReconstruction_siteMatrix root D h) s) d)
    simpa only [B', T', E', B, T, E, Matrix.mul_apply, Matrix.of_apply,
      Int.cast_sum, Int.cast_mul] using hz
  have hjet : T' * E₀' = Matrix.of (fun j d => (boundedCoefficientJetMatrix root₀ D₀ h
      (Subtype.val : BoundedBooleanJet α h → Finset α) j d : ℝ)) := by
    ext j d
    have hz := congrArg (fun z : ℤ => (z : ℝ))
      (congrFun (congrFun (booleanJetExtractionMatrix_mul_boundedSite root₀ D₀ h
        (Subtype.val : BoundedBooleanJet α h → Finset α)) j) d)
    simpa only [T', E₀', T, E₀, Matrix.mul_apply, Matrix.of_apply, Int.cast_sum, Int.cast_mul] using hz
  apply exists_matrix_factor_of_common_reconstruction E₀' E' B' T' h₀ hE
  rw [hjet]
  intro v
  obtain ⟨x, hx⟩ := matrixModuleAction_surjective_of_period (W := ℝ)
    (boundedCoefficientJetMatrix root₀ D₀ h (Subtype.val : BoundedBooleanJet α h → Finset α))
    (a ^ h) (pow_ne_zero _ ha)
    (boundedCoefficientJetMatrix_period root₀ D₀ a hperiod h
      (Subtype.val : BoundedBooleanJet α h → Finset α) Subtype.val_injective (fun j => j.property)) v
  refine ⟨x, ?_⟩
  ext j
  exact congrFun hx j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Polynomial

theorem exists_cube_residue_threshold_exp_budget (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F L S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ L → L ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeResidueSideThreshold m d (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K₀, _, hbase⟩ := exists_cube_mode_threshold_exp_budget m q
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget
    ((X + C K₀) ^ K₀ + (2 * X + modeProfileLogPolynomial + 3) + 1)
  refine ⟨K, hK, ?_⟩
  intro n d P F L S ρ ε hP hn hd hF hFP hL hLP hS hSP hρ hρP hε hεP
  obtain ⟨hs, hr⟩ := hbase n d P F L S ρ ε hP hn hd hF hFP hL hLP hS hSP hρ hρP hε hεP
  have hprof := modeProfileLog_nonneg hP
  have hδ := modeRemovalMesh_pos d
  have he : S / (ρ * modeRemovalMesh d) ≤ Real.exp (2 * P + modeProfileLog P + 3) := by
    calc
      _ = S * (1 / ρ) * (1 / modeRemovalMesh d) := by ring
      _ ≤ Real.exp P * Real.exp P * Real.exp (modeProfileLog P + 3) := by
        gcongr
        exact modeRemovalMesh_inv_le_exp d hP hd
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp : (P + K₀) ^ K₀ + (2 * P + modeProfileLog P + 3) + 1 ≤ (P + K) ^ K := by
    simpa [Polynomial.eval₂_pow, modeProfileLogPolynomial_eval] using hpoly P hP
  have hb0 : 0 ≤ (P + K₀) ^ K₀ := by positivity
  constructor
  · exact (add_le_exp_add_one hb0 (by linarith) hs he).trans (Real.exp_le_exp.mpr hp)
  · exact hr.trans (Real.exp_le_exp.mpr (by linarith))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueConstantMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueSmoothPMF_discard_error {K I J : Type*}
    [Fintype K] [Fintype I] [Fintype J]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w : (K × I → ℤ) → ℂ) (c : J → ℂ) (u : J → (K × I → ℤ) → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hdiscard : ∀ j, ¬keep j →
      ‖∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * u j x)‖ ≤ τ) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * ∑ j, c j * u j x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * ∑ j, if keep j then c j * u j x else 0)‖ ≤ C * τ := by
  simp_rw [selectedResidueSmoothPMF_toReal] at hdiscard ⊢
  exact normalized_finite_weight_discard_error _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ w c u keep hc hτ hdiscard

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization
namespace OAI

section

namespace Erdos3

open Polynomial

theorem exists_fourier_uniform_budget (A B : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      Real.exp ((2 * P + 2 + A) ^ A) ≤ Real.exp ((P + C) ^ C) ∧
      Real.exp ((2 * P + 2 + B) ^ B) ≤ Real.exp ((P + C) ^ C) := by
  obtain ⟨C, hC, hp⟩ := exists_natPolynomial_eval_budget
    (((2 * X + 2 + Polynomial.C A) ^ A) + ((2 * X + 2 + Polynomial.C B) ^ B))
  refine ⟨C, hC, ?_⟩
  intro P hP
  have hh : (2 * P + 2 + A) ^ A + (2 * P + 2 + B) ^ B ≤ (P + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hp P hP
  have ha : 0 ≤ (2 * P + 2 + A) ^ A := by positivity
  have hb : 0 ≤ (2 * P + 2 + B) ^ B := by positivity
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem boundedSiteMatrix_natAbs_le {K S : Type*} (h : ℕ) (site : S → K → ℤ)
    {L : ℕ} (hL : 1 ≤ L) (hsite : ∀ s k, (site s k).natAbs ≤ L)
    (s : S) (d : BoundedCoefficientExponent K h) :
    (boundedSiteMatrix h site s d).natAbs ≤ L ^ h := by
  classical
  change (∏ k ∈ d.val.support, site s k ^ d.val k).natAbs ≤ L ^ h
  rw [show (∏ k ∈ d.val.support, site s k ^ d.val k).natAbs =
      ∏ k ∈ d.val.support, (site s k ^ d.val k).natAbs from
    map_prod Int.natAbsHom _ _]
  simp only [Int.natAbs_pow]
  calc
    _ ≤ ∏ k ∈ d.val.support, L ^ d.val k :=
      Finset.prod_le_prod' (fun k _ => Nat.pow_le_pow_left (hsite s k) _)
    _ = L ^ d.val.degree := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ L ^ h := Nat.pow_le_pow_right hL d.property

theorem boundedSiteMatrix_height {K S : Type*} (h : ℕ) (site : S → K → ℤ)
    {L : ℕ} (hL : 1 ≤ L) (hsite : ∀ s k, (site s k).natAbs ≤ L)
    (s : S) (d : BoundedCoefficientExponent K h) :
    RationalHeightLE (boundedSiteMatrix h site s d : ℚ) (L ^ h) := by
  constructor
  · simpa using boundedSiteMatrix_natAbs_le h site hL hsite s d
  · simpa using Nat.one_le_pow h L hL

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricRetainedCommonCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem boundedSiteMatrix_height_of_exp {K S : Type*} (m : ℕ) {h : ℕ} (hh : h ≤ m)
    (site : S → K → ℤ) {P : ℝ}
    (hsite : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (s : S) (d : BoundedCoefficientExponent K h) :
    RationalHeightLE (boundedSiteMatrix h site s d : ℚ) (exponentialSiteHeight m P) := by
  have hceil : 1 ≤ ⌈Real.exp P⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hb : ∀ s k, (site s k).natAbs ≤ ⌈Real.exp P⌉₊ := by
    intro s k
    have he : ((site s k).natAbs : ℝ) ≤ (⌈Real.exp P⌉₊ : ℝ) := by
      simpa using (hsite s k).trans (Nat.le_ceil (Real.exp P))
    exact_mod_cast he
  exact (boundedSiteMatrix_height h site hceil hb s d).mono
    (Nat.pow_le_pow_right hceil hh)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

theorem insertSubstitution_degree (I : SlotInterleaving D E) (k : Fin (D + E))
    (i : Fin E) (a : (σ ⊕ Fin D) ⊕ Fin i.val) :
    insertSubstitution I k i a ∈ weightedSupportLE (patchVariableWeight (I.fill w v) k)
      (weightedPatchVariableWeight (Sum.elim (fun _ : σ => 1) w) v i a) := by
  rcases a with (a | j) | j
  · exact weightedSupportLE_X _ (Sum.inl a)
  · simp only [insertSubstitution, Sum.elim_inl, Sum.elim_inr]
    split_ifs with h
    · have hX := weightedSupportLE_X (R := ℝ) (patchVariableWeight (σ := σ) (I.fill w v) k)
        (Sum.inr (⟨(I.left j).val, h⟩ : Fin k.val))
      change _ ∈ weightedSupportLE _ (I.fill w v (I.left j)) at hX
      rw [I.fill_left] at hX
      exact hX
    · exact (weightedSupportLE _ _).zero_mem
  · exact PolynomialSlots.placementSubstitution_degree I.right
      (fun j => I.fill_right w v j) k i (Sum.inr j)

noncomputable def insertCenter
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (k : Fin (D + E)) (i : Fin E) :
    MvPolynomial (σ ⊕ Fin k.val) ℝ := aeval (insertSubstitution I k i) (B.center i)

theorem insertCenter_degree
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) (k : Fin (D + E)) (i : Fin E) :
    B.insertCenter I k i ∈ weightedSupportLE (patchVariableWeight (I.fill w v) k) (v i) :=
  weightedSupportLE_aeval _ _ _ (insertSubstitution_degree I k i) (B.degree i)

end WeightedParameterSlots

namespace PolynomialSlots

variable {σ : Type*} {D E : ℕ} {w : Fin D → ℕ} {v : Fin E → ℕ}

noncomputable def insertLifts (A : PolynomialSlots σ D w)
    (B : WeightedParameterSlots (σ ⊕ Fin D) (Sum.elim (fun _ => 1) w) E v)
    (I : SlotInterleaving D E) : PolynomialSlots σ (D + E) (I.fill w v) where
  center k := Fin.addCases (A.placeCenter I.left k) (B.insertCenter I k) (I.perm k)
  degree k := by
    change Fin.addCases (A.placeCenter I.left k) (B.insertCenter I k) (I.perm k) ∈
      weightedSupportLE (patchVariableWeight (I.fill w v) k) (Fin.append w v (I.perm k))
    generalize I.perm k = z
    refine Fin.addCases (fun i => ?_) (fun i => ?_) z
    · simpa only [Fin.addCases_left, Fin.append_left] using
        A.placeCenter_degree I.left (fun j => I.fill_left w v j) k i
    · simpa only [Fin.addCases_right, Fin.append_right] using B.insertCenter_degree I k i

end PolynomialSlots
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def canonicalCoefficientDeckSample (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d) :
    CoefficientTorus (K := K) U :=
  canonicalCoefficientCoverLift U b hb o d x + (coefficientDeckKernelEquiv U bW d hd r).val

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientPairCover
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory

variable {K : Type*} [finiteK : Fintype K] {m : ℕ} {J : Fin m → Type*}
  [finiteCoordinates : ∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientAmbientTorus_continuous : Continuous (coefficientAmbientTorus (K := K) U) := by
  apply continuous_pi
  intro a
  exact (continuous_apply a.2).comp ((subspaceAmbientTorus_continuous (U a.1.1)).comp
    ((continuous_apply a.1).comp (coefficientCoordinateTorus_continuous U)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace BooleanCutTest

omit [Fintype Ω] in
@[simp]
theorem eval_of_mem (A : BooleanCutTest Ω) {x : Ω} (hx : x ∈ A) :
    A.eval x = 1 :=
  finsetIndicator_of_mem hx

end BooleanCutTest

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def coefficientSamplerAmbientPoint
    (x : CoefficientSamplerArrays (K := K) I n) : CoefficientAmbientIndex K J → ℝ :=
  fun a => normalizedLatticePoint (euclideanSubspace (U a.1.1)) (b a.1.1)
    (orthonormalMixedChart (o a.1.1) (mixedArrayRegroup _ _ _ (x a.1.1) a.1.2)) a.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCoordinateEquiv
namespace OAI

section

namespace Erdos3

variable {X Y : Type*}

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

@[simp] theorem integerPointCoordinateEquiv_mem_integerBox (e : X ≃ Y)
    (N : X → ℕ) (x : X → ℤ) :
    integerPointCoordinateEquiv e x ∈ integerBox (coordinateReindexedSides e N) ↔
      x ∈ integerBox N := by
  rw [coordinateReindexedSides_mem_integerBox]
  simp only [integerPointCoordinateEquiv_apply, e.symm_apply_apply]

def integerBoxCoordinateEquiv (e : X ≃ Y) (N : X → ℕ) :
    integerBox N ≃ integerBox (coordinateReindexedSides e N) where
  toFun x := ⟨integerPointCoordinateEquiv e x.val,
    (integerPointCoordinateEquiv_mem_integerBox e N x.val).mpr x.property⟩
  invFun y := ⟨(integerPointCoordinateEquiv e).symm y.val,
    (coordinateReindexedSides_mem_integerBox e N y.val).mp y.property⟩
  left_inv x := by apply Subtype.ext; exact (integerPointCoordinateEquiv e).left_inv x.val
  right_inv y := by apply Subtype.ext; exact (integerPointCoordinateEquiv e).right_inv y.val

@[simp] theorem integerBoxCoordinateEquiv_val (e : X ≃ Y) (N : X → ℕ)
    (x : integerBox N) :
    (integerBoxCoordinateEquiv e N x).val = integerPointCoordinateEquiv e x.val := rfl

@[simp] theorem integerBoxCoordinateEquiv_symm_val (e : X ≃ Y) (N : X → ℕ)
    (y : integerBox (coordinateReindexedSides e N)) :
    ((integerBoxCoordinateEquiv e N).symm y).val =
      (integerPointCoordinateEquiv e).symm y.val := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedLieUpperSpan
namespace OAI

section

namespace Erdos3

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem weightedLieUpperSpan_leaf (v : I → L) (w : I → ℕ) (i : I) :
    v i ∈ weightedLieUpperSpan v w (w i) :=
  Submodule.subset_span ⟨.of i, le_rfl, rfl⟩

end Erdos3

end

end OAI
end


