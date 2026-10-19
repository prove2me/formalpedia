-- Prove2me | Definitions.Def_OAIE3v2B072
-- name    : OAIE3v2B072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:18:46.684932+00:00
-- url     : https://prove2.me/theorems/f9c27f05-f073-4d57-951a-c34fef8faaf9
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 73 of 311
-- statement:
--   Definitions bundle 73 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B041`, `OAIE3v2B042`, `OAIE3v2B043`, `OAIE3v2B044`, `OAIE3v2B045` of this split.
--
--   Modules: `Estimates/BoundedExtendedSiteSection.lean`, `Estimates/BoundedFreeWords.lean`, `Estimates/CircleFejerAverage.lean`, `Estimates/CoefficientRowEvaluation.lean`, `Estimates/DenseProductApproximation.lean`, `Estimates/FiniteFiberTest.lean`, `Estimates/LinearQuotientCoverAverage.lean`, `Estimates/MixedBooleanSiteValues.lean`, `Estimates/PeriodicIsometricAction.lean`, `Estimates/PhysicalCubeNativeDetection.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/RationalApproximationScaling.lean`, `Estimates/UniformCommutingCircleDecomposition.lean`, `Estimates/VectorCoefficientScaling.lean`, `FixedDensity/Energy.lean`, `Fourier/BohrTorusApproximation.lean`, `Fourier/CanonicalDensityFourier.lean`, `Fourier/CircleActionFourierMetric.lean`, `Fourier/CommonCoveredSiteCharacter.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/SiteFourierHaarMean.lean`, `Fourier/TorusCircleActions.lean`, `Geometry/AllocatedSpatialProxyCap.lean`, `Geometry/BoxBlockBudget.lean`, `Geometry/CoefficientAmbientCoordinates.lean`, `Geometry/PhysicalRowsStandardCoordinates.lean`, `Lattices/CommonIntegerSiteResidual.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/SelectedResidueApproximation.lean`, `Linear/CircleFejerKernel.lean`, `Linear/MatrixModuleAction.lean`, `Linear/MatrixSupInverse.lean`, `Polynomial/MonomialCoordinateRows.lean`, `Probability/CanonicalCoverLaw.lean`, `Probability/DensityMixtureAELaw.lean`, `Probability/FiniteConditionedMass.lean`, `Probability/FiniteDensityMassBound.lean`, `Probability/FiniteProbabilityLipschitz.lean`, `Sampling/SmoothSplitSampling.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B040
import Definitions.Def_OAIE3v2B041
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B043
import Definitions.Def_OAIE3v2B044
import Definitions.Def_OAIE3v2B045

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixModuleAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem matrixModuleAction_image_section {I J W : Type*} [Fintype I] [Fintype J]
    [AddCommGroup W] [Module ℝ W] (A : Matrix I J ℝ) (S : Matrix J I ℝ)
    (hS : A * S * A = A) (x : J → W) :
    matrixModuleAction A (matrixModuleAction S (matrixModuleAction A x)) = matrixModuleAction A x := by
  rw [matrixModuleAction_mul, matrixModuleAction_mul, hS]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

theorem mean_nonneg {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ p.mean f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf x))

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped Classical BigOperators NNReal

theorem mean_lipschitz_uniform_emetric {A X : Type*} [Fintype A] [PseudoEMetricSpace X]
    (p : FiniteProbabilityWeights A) (f : A → X → ℝ) {L : ℝ≥0}
    (hf : ∀ a, LipschitzWith L (f a)) :
    LipschitzWith L (fun x => p.mean (fun a => f a x)) := by
  let w : A → ℝ≥0 := fun a => ⟨p.weight a, p.nonneg a⟩
  have hmul (a : A) : LipschitzWith (w a) (fun x : ℝ => p.weight a * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (p.nonneg a)]
    exact le_rfl
  have hsum (s : Finset A) :
      LipschitzWith (∑ a ∈ s, w a * L) (fun x => ∑ a ∈ s, p.weight a * f a x) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simpa only [Finset.sum_insert ha, Function.comp_def] using ((hmul a).comp (hf a)).add ih
  have hw : (∑ a, w a) = 1 := by
    apply NNReal.coe_injective
    change (↑(∑ a, w a) : ℝ) = 1
    rw [NNReal.coe_sum]
    exact p.total
  simpa only [← Finset.sum_mul, hw, one_mul, mean] using hsum Finset.univ

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_finset_expect {V : Type*} (s : Finset V) (f : X → V → ℂ) :
    p.complexMean (fun x => 𝔼 v ∈ s, f x v) = 𝔼 v ∈ s, p.complexMean (fun x => f x v) := by
  unfold complexMean
  simp_rw [Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators

variable {X C : Type*} [Fintype X] [MeasurableSpace C] (p : FiniteProbabilityWeights X)

theorem mean_measurable (f : C → X → ℝ) (hf : ∀ x, Measurable (fun c => f c x)) :
    Measurable (fun c => p.mean (f c)) :=
  Finset.measurable_sum _ (fun x _ => (hf x).const_mul (p.weight x))

theorem integral_mean (μ : Measure C) (f : C → X → ℝ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    (∫ c, p.mean (f c) ∂μ) = p.mean (fun x => ∫ c, f c x ∂μ) := by
  unfold mean
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x))]
  simp only [integral_const_mul]

theorem complexMean_measurable (f : C → X → ℂ) (hf : ∀ x, Measurable (fun c => f c x)) :
    Measurable (fun c => p.complexMean (f c)) :=
  Finset.measurable_sum _ (fun x _ => (hf x).const_mul (p.weight x : ℂ))

theorem complexMean_integrable (μ : Measure C) (f : C → X → ℂ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    Integrable (fun c => p.complexMean (f c)) μ :=
  integrable_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x : ℂ))

theorem integral_complexMean (μ : Measure C) (f : C → X → ℂ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    (∫ c, p.complexMean (f c) ∂μ) = p.complexMean (fun x => ∫ c, f c x ∂μ) := by
  unfold complexMean
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x : ℂ))]
  simp only [integral_const_mul]

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

theorem uniform_complexMean {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℂ) :
    (uniform Ω).complexMean f = 𝔼 x, f x := by
  simp only [complexMean, uniform, Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact mul_comm _ _

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxBlockBudget
namespace OAI

section

namespace Erdos3.BoxProgressionPartition

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

theorem card_cell (a : ∀ i, (P i).Label) :
    (partitionCell (cell P) a).card = ∏ i, (P i).length (a i) := by
  simpa only [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin] using
    (Fintype.card_congr (pointEquiv P a)).symm

end Erdos3.BoxProgressionPartition

end

section

namespace Erdos3.BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

noncomputable def normalizedStart (a : ∀ i, (P i).Label) : ι → ℝ :=
  fun i => ((P i).start (a i) : ℝ) / N i

end Erdos3.BoxProgressionPartition

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_inverse_entry_abs_le (A : Matrix ι ι ℝ) {H κ : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) (hκ : 0 < κ) (hdet : κ ≤ |A.det|)
    (i j : ι) :
    |A⁻¹ i j| ≤ ((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) / κ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_inv]
  have hcof := matrix_adjugate_entry_abs_le A hA i j
  have hinv : |A.det|⁻¹ ≤ κ⁻¹ := inv_anti₀ hκ hdet
  calc
    _ ≤ κ⁻¹ * ((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) :=
      mul_le_mul hinv hcof (abs_nonneg _) (inv_nonneg.mpr hκ.le)
    _ = _ := by rw [div_eq_mul_inv]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem matrixSupCLM_inverse_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {H κ : ℝ} (hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H)
    (hκ : 0 < κ) (hdet : κ ≤ |A.det|) :
    (matrixSupCLM A).IsInvertible ∧
      ‖(matrixSupCLM A).inverse‖ ≤
        Fintype.card ι * (((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) / κ) := by
  have hne : A.det ≠ 0 := abs_pos.mp (hκ.trans_le hdet)
  obtain ⟨hinv, heq⟩ := matrixSupCLM_inverse_spec A hne
  refine ⟨hinv, ?_⟩
  rw [heq]
  exact matrixSupCLM_norm_le A⁻¹ (by positivity) (matrix_inverse_entry_abs_le A hA hκ hdet)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem card_trimmedIntegerBox (N R : I → ℕ) :
    (trimmedIntegerBox N R).card = ∏ i, (N i - 2 * R i) := by
  rw [trimmedIntegerBox, Finset.card_image_of_injective _ (fun _ _ h => add_left_cancel h),
    card_integerBox]

theorem trimmedIntegerBox_nonempty (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i) :
    (trimmedIntegerBox N R).Nonempty := by
  apply Finset.Nonempty.image
  refine ⟨0, (mem_integerBox _ _).mpr ?_⟩
  intro i
  have h : 0 < N i - 2 * R i := Nat.sub_pos_of_lt (hR i)
  simpa using h

theorem trimmedIntegerBox_add_mem (N R : I → ℕ) (hR : ∀ i, 2 * R i ≤ N i)
    {x : I → ℤ} (hx : x ∈ trimmedIntegerBox N R) (y : I → ℤ)
    (hy : ∀ i, |y i| ≤ (R i : ℤ)) : x + y ∈ integerBox N := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_integerBox N _).mpr
  intro i
  have hi := (mem_integerBox _ _).mp ha i
  have hyi := abs_le.mp (hy i)
  have hRi := hR i
  simp only [Pi.add_apply]
  omega

theorem trimmedIntegerBox_card_deficit (N R : I → ℕ)
    (hN : ∀ i, 0 < N i) (hR : ∀ i, 2 * R i ≤ N i) :
    1 - ((trimmedIntegerBox N R).card : ℝ) / (integerBox N).card ≤
      ∑ i, 2 * (R i : ℝ) / N i := by
  have hNR (i : I) : 0 < (N i : ℝ) := by exact_mod_cast hN i
  have he (i : I) : 2 * (R i : ℝ) / N i ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (hNR i)).mpr
      exact_mod_cast hR i
  have hi (i : I) : 1 - 2 * (R i : ℝ) / N i = ((N i - 2 * R i : ℕ) : ℝ) / N i := by
    rw [Nat.cast_sub (hR i)]
    push_cast
    field_simp [ne_of_gt (hNR i)]
  have hp := one_sub_sum_le_positive_prod Finset.univ
    (fun i => ((N i - 2 * R i : ℕ) : ℝ) / N i) (fun i => 2 * (R i : ℝ) / N i)
    (fun i _ => by positivity) (fun i _ => he i) (fun i _ => (hi i).le)
  rw [card_trimmedIntegerBox, card_integerBox, Nat.cast_prod, Nat.cast_prod,
    ← Finset.prod_div_distrib]
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem complexMean_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X) (z : ℂ) :
    p.complexMean (fun _ => z) = z := by
  unfold complexMean
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, p.total, Complex.ofReal_one, one_mul]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem measurePreserving_realDensity_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (π : X → Y) (hπ : MeasurePreserving π μ ν)
    (f : Y → ℝ) (hf : Measurable f) (hfi : Integrable f ν) (hf0 : ∀ y, 0 ≤ f y) :
    (realDensityMeasure μ (fun x => f (π x))).map π = realDensityMeasure ν f := by
  have hi := hπ.integrable_comp_of_integrable hfi
  let _ := realDensityMeasure_finite μ (fun x => f (π x)) hi (fun x => hf0 _)
  let _ := realDensityMeasure_finite ν f hfi hf0
  apply finiteMeasure_eq_of_integrals
  intro φ hφ
  rw [integral_map hπ.measurable.aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral μ (fun x => f (π x)) (hf.comp hπ.measurable)
      (fun x => hf0 _) (fun x => φ (π x)),
    realDensityMeasure_integral ν f hf hf0 φ]
  have he := integral_map (μ := μ) hπ.measurable.aemeasurable (hf.mul hφ).aestronglyMeasurable
  simpa only [hπ.map_eq, Pi.mul_apply] using he.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem coefficientArrayFunctional_single {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (s : CoefficientSlot K m) (w : U s.1) :
    coefficientArrayFunctional U frequency (Pi.single s w) =
      ∑ a, (frequency s.1 s.2.val a : ℝ) * w.val a := by
  classical
  change (∑ t : CoefficientSlot K m, ∑ a, (frequency t.1 t.2.val a : ℝ) *
    ((Pi.single s w : CoefficientArray (K := K) U) t).val a) = _
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    simp [Pi.single_eq_of_ne hts]
  · simp

theorem coefficientArrayFunctional_eq_zero_iff {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    coefficientArrayFunctional U frequency = 0 ↔
      ∀ (s : CoefficientSlot K m) (w : U s.1), ∑ a, (frequency s.1 s.2.val a : ℝ) * w.val a = 0 := by
  constructor
  · intro hz s w
    have he := DFunLike.congr_fun hz (Pi.single s w)
    simpa only [coefficientArrayFunctional_single, LinearMap.zero_apply] using he
  · intro hz
    apply LinearMap.ext
    intro x
    change (∑ s, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a) = 0
    exact Finset.sum_eq_zero (fun s _ => hz s (x s))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem exists_homogeneous_monomial_nonzero {K W : Type*}
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) {h : ℕ}
    (hnonzero : ∃ p, Homogeneous h p ∧ L p ≠ 0) :
    ∃ d : K →₀ ℕ, d.degree = h ∧ ∃ w : W, L (monomial d w) ≠ 0 := by
  obtain ⟨p, hp, hLp⟩ := hnonzero
  by_contra hn
  push Not at hn
  apply hLp
  rw [← sum_monomial_coefficients p, Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  exact hn d (homogeneous_support_degree hp hd) (coefficients p d)

theorem homogeneous_empty_factorization_iff {K W : Type*}
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (h : ℕ) (site : Empty → K → ℝ) :
    (∃ M : (Empty → W) →ₗ[ℝ] ℝ,
      ∀ p, Homogeneous h p → L p = M (siteEvaluation site p)) ↔
      ∀ p, Homogeneous h p → L p = 0 := by
  constructor
  · rintro ⟨M, hM⟩ p hp
    have he := hM p hp
    rwa [Subsingleton.elim (siteEvaluation site p) 0, map_zero] at he
  · intro hz
    exact ⟨0, fun p hp => by simpa using hz p hp⟩

theorem exists_restricted_coefficient_nonzero {K J : Type*} [Fintype J]
    (W : Submodule ℝ (J → ℝ)) (frequency : (K →₀ ℕ) → J → ℤ) {h : ℕ}
    (hnonzero : ∃ p, Homogeneous h p ∧
      coefficientFunctional (fun d j => (frequency d j : ℝ)) (map W.subtype p) ≠ 0) :
    ∃ d : K →₀ ℕ, d.degree = h ∧ ∃ w : W,
      (∑ j, (frequency d j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨d, hd, w, hw⟩ := exists_homogeneous_monomial_nonzero
    ((coefficientFunctional (fun d j => (frequency d j : ℝ))).comp (map W.subtype)) hnonzero
  refine ⟨d, hd, w, ?_⟩
  simpa only [LinearMap.comp_apply, map_monomial, Submodule.subtype_apply,
    coefficientFunctional_monomial] using hw

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem shiftedSmoothCoefficientPMF_apply (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (k : ℤ) :
    (shiftedSmoothCoefficientPMF a S hS hZ k).toReal =
      smoothProbabilityProfile (((k : ℝ) - a) / S) / shiftedSmoothSampleSum a S :=
  realWeightPMF_apply _ _ _ _ k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedFreeWords
namespace OAI

section

namespace Erdos3

def BoundedFreeWord (X : Type*) (s : ℕ) := {w : FreeSemigroup X // w.length ≤ s}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CircleFejerKernel
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real
open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

def fejerPolynomial (N : ℕ) (x : Circle) : ℝ :=
  (∑ h ∈ fejerFrequencies N,
    (fejerCoefficient N h : ℂ) * character (h • x)).re

lemma fejer_grouped (N : ℕ) (x : Circle) :
    ∑ h ∈ fejerFrequencies N,
        (∑ p ∈ (Finset.univ.filter fun p : Fin N × Fin N =>
          fejerPairFrequency p = h), character (fejerPairFrequency p • x)) =
      ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) := by
  classical
  rw [Finset.sum_fiberwise_eq_sum_filter]
  rw [Finset.filter_eq_self.2]
  intro p hp
  simp only [fejerFrequencies, Finset.mem_image]
  exact ⟨p, Finset.mem_univ _, rfl⟩

lemma fejer_fin_sum_eq_geo (N : ℕ) (x : Circle) :
    (∑ k : Fin N, character ((k.val : ℤ) • x)) =
      geometricCharacterSum N x := by
  rw [geometricCharacterSum_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro k hk
  rw [natCast_zsmul]

lemma fejer_pair_sum_eq_norm_sq (N : ℕ) (x : Circle) :
    ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) =
      (‖geometricCharacterSum N x‖ ^ 2 : ℝ) := by
  rw [fejer_pair_sum_eq, fejer_neg_sum_eq_conj, fejer_fin_sum_eq_geo]
  change geometricCharacterSum N x *
    (starRingEnd ℂ) (geometricCharacterSum N x) = _
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.sq_norm _ |>.symm

lemma complex_fejerPolynomial_eq (N : ℕ) (x : Circle) :
    ∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x) =
      ((‖geometricCharacterSum N x‖ ^ 2 / N : ℝ) : ℂ) := by
  classical
  rw [Complex.ofReal_div]
  push_cast
  have hpair := fejer_pair_sum_eq_norm_sq N x
  rw [← Complex.ofReal_pow, ← hpair, ← fejer_grouped N x, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h hh
  rw [fejerCoefficient, Complex.ofReal_div]
  push_cast
  rw [div_mul_eq_mul_div]
  congr 1
  calc
    (#{p : Fin N × Fin N | fejerPairFrequency p = h} : ℂ) *
        character (h • x) =
        ∑ p with fejerPairFrequency p = h, character (h • x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ p with fejerPairFrequency p = h,
        character (fejerPairFrequency p • x) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

lemma fejerPolynomial_eq (N : ℕ) (x : Circle) :
    fejerPolynomial N x = ‖geometricCharacterSum N x‖ ^ 2 / N := by
  have h := congrArg Complex.re (complex_fejerPolynomial_eq N x)
  simpa only [fejerPolynomial, Complex.ofReal_re] using h

lemma fejerPolynomial_nonneg (N : ℕ) (x : Circle) :
    0 ≤ fejerPolynomial N x := by
  rw [fejerPolynomial_eq]
  positivity

lemma fejerPolynomial_le_of_distance {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) {x : Circle} (hx : η ≤ integerDistance x) :
    fejerPolynomial N x ≤ 1 / (4 * N * η ^ 2) := by
  rw [fejerPolynomial_eq]
  have hgeom :=
    two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one N x
  have hnorm := norm_nonneg (geometricCharacterSum N x)
  have hdist := integerDistance_nonneg x
  have hbound : 2 * η * ‖geometricCharacterSum N x‖ ≤ 1 := by nlinarith
  have hsquare : 4 * η ^ 2 * ‖geometricCharacterSum N x‖ ^ 2 ≤ 1 := by
    have hs := mul_self_le_mul_self (mul_nonneg (by positivity) hnorm) hbound
    nlinarith
  have hn2 : ‖geometricCharacterSum N x‖ ^ 2 ≤ 1 / (4 * η ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * η ^ 2)]
    nlinarith
  calc
    ‖geometricCharacterSum N x‖ ^ 2 / (N : ℝ) ≤
        (1 / (4 * η ^ 2)) / N := by gcongr
    _ = 1 / (4 * N * η ^ 2) := by field_simp

lemma integral_character (h : ℤ) :
    ∫ x : Circle, character (h • x) ∂circleHaar = if h = 0 then 1 else 0 := by
  by_cases hh : h = 0
  · subst h
    simp
  · simp only [hh, ↓reduceIte]
    exact integral_eq_zero_of_add_right_eq_neg (μ := circleHaar)
      (fourier_add_half_inv_index hh (by norm_num))

lemma integral_fejerPolynomial {N : ℕ} (hN : 0 < N) :
    ∫ x : Circle, fejerPolynomial N x ∂circleHaar = 1 := by
  simp_rw [fejerPolynomial]
  have hterm : ∀ h ∈ fejerFrequencies N,
      Integrable (fun x : Circle =>
        (fejerCoefficient N h : ℂ) * character (h • x)) circleHaar := by
    intro h hh
    apply Integrable.const_mul
    apply Integrable.of_bound (fourier h).continuous.aestronglyMeasurable 1
    exact ae_of_all _ fun x => (norm_character (h • x)).le
  have hint : Integrable (fun x : Circle =>
      ∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x)) circleHaar := by
    have hi := integrable_finsetSum' (fejerFrequencies N) hterm
    have heq : (∑ h ∈ fejerFrequencies N,
        fun x : Circle => (fejerCoefficient N h : ℂ) * character (h • x)) =
        fun x : Circle => ∑ h ∈ fejerFrequencies N,
          (fejerCoefficient N h : ℂ) * character (h • x) := by
      funext x
      exact Finset.sum_apply x (fejerFrequencies N) _
    rw [← heq]
    exact hi
  calc
    (∫ x : Circle, (∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x)).re ∂circleHaar) =
        (∫ x : Circle, ∑ h ∈ fejerFrequencies N,
          (fejerCoefficient N h : ℂ) * character (h • x) ∂circleHaar).re :=
      integral_re hint
    _ = 1 := by
      rw [integral_finsetSum (fejerFrequencies N) hterm]
      simp_rw [integral_const_mul, integral_character]
      rw [Finset.sum_eq_single 0]
      · rw [if_pos rfl, mul_one]
        unfold fejerCoefficient fejerPairFrequency
        have hdiag : (Finset.univ.filter fun p : Fin N × Fin N =>
            (p.1.val : ℤ) - p.2.val = 0).card = N := by
          rw [show (Finset.univ.filter fun p : Fin N × Fin N =>
              (p.1.val : ℤ) - p.2.val = 0) =
              Finset.univ.image (fun j : Fin N => (j, j)) by
            ext p
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_image]
            constructor
            · intro hp
              have : p.1 = p.2 := by
                apply Fin.ext
                omega
              exact ⟨p.1, by ext <;> simp [this]⟩
            · rintro ⟨j, -, rfl⟩
              simp]
          calc
            (Finset.univ.image (fun j : Fin N => (j, j))).card =
                (Finset.univ : Finset (Fin N)).card :=
              Finset.card_image_of_injective _ fun i j h => by
                simpa using congrArg Prod.fst h
            _ = N := by simp
        rw [hdiag, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]
        norm_num
      · intro h hh hne
        rw [if_neg hne, mul_zero]
      · intro hz
        exfalso
        apply hz
        unfold fejerFrequencies
        apply Finset.mem_image.2
        exact ⟨(⟨0, hN⟩, ⟨0, hN⟩), Finset.mem_univ _,
          by simp [fejerPairFrequency]⟩

lemma continuous_fejerPolynomial (N : ℕ) : Continuous (fejerPolynomial N) := by
  rw [show fejerPolynomial N = fun x =>
      ‖geometricCharacterSum N x‖ ^ 2 / N by
    funext x
    exact fejerPolynomial_eq N x]
  apply Continuous.div_const
  apply Continuous.pow
  apply Continuous.norm
  unfold geometricCharacterSum
  apply continuous_finsetSum
  intro n hn
  unfold character
  exact continuous_subtype_val.comp
    (AddCircle.continuous_toCircle.comp (continuous_nsmul n))

end
end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CircleFejerAverage
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators

theorem abs_lt_of_mem_fejerFrequencies {N : ℕ} {h : ℤ} (hh : h ∈ fejerFrequencies N) :
    |h| < (N : ℤ) := by
  classical
  obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hh
  unfold fejerPairFrequency
  rw [abs_lt]
  constructor <;> omega

theorem card_fejerFrequencies_le (N : ℕ) : (fejerFrequencies N).card ≤ N ^ 2 := by
  classical
  exact (Finset.card_image_le).trans_eq (by simp [pow_two])

noncomputable def fejerFirstMoment (N : ℕ) : ℝ :=
  ∫ x : Circle, ‖x‖ * fejerPolynomial N x ∂circleHaar

theorem fejerFirstMoment_le {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    fejerFirstMoment N ≤ η + 1 / (8 * N * η ^ 2) := by
  have hpoint (x : Circle) : ‖x‖ * fejerPolynomial N x ≤
      η * fejerPolynomial N x + 1 / (8 * N * η ^ 2) := by
    by_cases hx : ‖x‖ < η
    · have h := mul_le_mul_of_nonneg_right hx.le (fejerPolynomial_nonneg N x)
      exact h.trans (le_add_of_nonneg_right (by positivity))
    · have htail := fejerPolynomial_le_of_distance hN hη (le_of_not_gt hx)
      have hnorm : ‖x‖ ≤ 1 / 2 := integerDistance_le_half x
      have hprod := mul_le_mul hnorm htail (fejerPolynomial_nonneg N x) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have heq : (1 / 2 : ℝ) * (1 / (4 * N * η ^ 2)) = 1 / (8 * N * η ^ 2) := by ring
      rw [heq] at hprod
      exact hprod.trans (le_add_of_nonneg_left (mul_nonneg hη.le (fejerPolynomial_nonneg N x)))
  have hi : Integrable (fun x : Circle => ‖x‖ * fejerPolynomial N x) circleHaar :=
    circle_integrable_of_continuous (continuous_norm.mul (continuous_fejerPolynomial N))
  have hj : Integrable (fun x : Circle => η * fejerPolynomial N x + 1 / (8 * N * η ^ 2)) circleHaar :=
    circle_integrable_of_continuous ((continuous_const.mul (continuous_fejerPolynomial N)).add continuous_const)
  calc
    fejerFirstMoment N ≤ ∫ x : Circle,
        η * fejerPolynomial N x + 1 / (8 * N * η ^ 2) ∂circleHaar := integral_mono hi hj hpoint
    _ = η + 1 / (8 * N * η ^ 2) := by
      have hk : Integrable (fun x : Circle => η * fejerPolynomial N x) circleHaar :=
        circle_integrable_of_continuous (continuous_const.mul (continuous_fejerPolynomial N))
      rw [integral_add hk (integrable_const _),
        integral_const_mul, integral_fejerPolynomial hN]
      simp

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def fejerAverage (N : ℕ) (f : Circle → E) : E :=
  ∫ t : Circle, fejerPolynomial N t • f t ∂circleHaar

theorem fejerAverage_sub_const {N : ℕ} (hN : 0 < N) {f : Circle → E}
    (hf : Continuous f) (c : E) :
    fejerAverage N f - c = fejerAverage N (fun t => f t - c) := by
  unfold fejerAverage
  simp only [smul_sub]
  have hi : Integrable (fun t : Circle => fejerPolynomial N t • f t) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul hf)
  have hc : Integrable (fun t : Circle => fejerPolynomial N t • c) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul continuous_const)
  rw [integral_sub hi hc,
    integral_smul_const, integral_fejerPolynomial hN, one_smul]

theorem norm_fejerAverage_sub_le {N : ℕ} (hN : 0 < N) {f : Circle → E}
    (hf : Continuous f) {L : ℝ} (_hL : 0 ≤ L)
    (hbound : ∀ t, ‖f t - f 0‖ ≤ L * ‖t‖) :
    ‖fejerAverage N f - f 0‖ ≤ L * fejerFirstMoment N := by
  rw [fejerAverage_sub_const hN hf (f 0)]
  calc
    ‖fejerAverage N (fun t => f t - f 0)‖ ≤
        ∫ t : Circle, ‖fejerPolynomial N t • (f t - f 0)‖ ∂circleHaar :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : Circle, L * (‖t‖ * fejerPolynomial N t) ∂circleHaar := by
      apply integral_mono
      · exact circle_integrable_of_continuous
          (((continuous_fejerPolynomial N).smul (hf.sub continuous_const)).norm)
      · exact circle_integrable_of_continuous
          (continuous_const.mul (continuous_norm.mul (continuous_fejerPolynomial N)))
      · intro t
        dsimp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fejerPolynomial_nonneg N t)]
        nlinarith [mul_le_mul_of_nonneg_left (hbound t) (fejerPolynomial_nonneg N t)]
    _ = L * fejerFirstMoment N := integral_const_mul L _

theorem norm_fejerAverage_sub_le_explicit {N : ℕ} (hN : 0 < N) {f : Circle → E}
    (hf : Continuous f) {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hbound : ∀ t, ‖f t - f 0‖ ≤ L * ‖t‖) :
    ‖fejerAverage N f - f 0‖ ≤ L * (η + 1 / (8 * N * η ^ 2)) :=
  (norm_fejerAverage_sub_le hN hf hL hbound).trans
    (mul_le_mul_of_nonneg_left (fejerFirstMoment_le hN hη) hL)

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CircleActionFourierMetric
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {X : Type*} [AddAction Circle X]

theorem circleFourierComponent_vadd (n : ℤ) (f : X → ℂ) (a : Circle) (x : X) :
    circleFourierComponent n f (a +ᵥ x) = character (n • a) * circleFourierComponent n f x := by
  unfold circleFourierComponent
  calc
    _ = ∫ t : Circle, character (n • a) *
        (character ((-n) • (t + a)) * f ((t + a) +ᵥ x)) ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [← add_vadd]
      have hchar : character ((-n) • t) = character (n • a) * character ((-n) • (t + a)) := by
        rw [← character_add]
        congr 1
        simp only [smul_add, neg_smul]
        abel
      rw [hchar, mul_assoc]
    _ = character (n • a) * ∫ t : Circle,
        character ((-n) • (t + a)) * f ((t + a) +ᵥ x) ∂circleHaar := integral_const_mul _ _
    _ = _ := by rw [integral_add_right_eq_self
      (fun t : Circle => character ((-n) • t) * f (t +ᵥ x)) a]

end Erdos3.CircleFourier

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

theorem ofReal_fejerPolynomial_eq (N : ℕ) (t : Circle) :
    (fejerPolynomial N t : ℂ) =
      ∑ h ∈ fejerFrequencies N, (fejerCoefficient N h : ℂ) * character (h • t) := by
  rw [fejerPolynomial_eq, complex_fejerPolynomial_eq]

theorem fejerAverage_eq_sum (N : ℕ) {f : Circle → ℂ} (hf : Continuous f) :
    fejerAverage N f = ∑ h ∈ fejerFrequencies N,
      (fejerCoefficient N h : ℂ) * ∫ t : Circle, character (h • t) * f t ∂circleHaar := by
  classical
  unfold fejerAverage
  simp_rw [Complex.real_smul, ofReal_fejerPolynomial_eq, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro h _
    exact circle_integrable_of_continuous
      (continuous_const.mul ((fourier h).continuous.mul hf))

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X : Type*} [AddAction Circle X]

theorem fejerComponent_vadd (N : ℕ) (h : ℤ) (f : X → ℂ) (a : Circle) (x : X) :
    fejerComponent N h f (a +ᵥ x) = character ((-h) • a) * fejerComponent N h f x := by
  unfold fejerComponent
  rw [circleFourierComponent_vadd]
  ring

theorem norm_fejerComponent_le {N : ℕ} (hN : 0 < N) (h : ℤ) {f : X → ℂ} {B : ℝ≥0}
    (hf : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖fejerComponent N h f x‖ ≤ B := by
  unfold fejerComponent
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerCoefficient_nonneg N h)]
  exact (mul_le_mul (fejerCoefficient_le_one hN h) (norm_circleFourierComponent_le (-h) f hf x)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

variable [PseudoMetricSpace X] [ContinuousVAdd Circle X]

theorem lipschitz_fejerComponent {N : ℕ} (hN : 0 < N) (h : ℤ) {f : X → ℂ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hact : ∀ t : Circle, Isometry (fun x : X => t +ᵥ x)) :
    LipschitzWith L (fejerComponent N h f) := by
  have hc := lipschitz_circleFourierComponent (-h) hf hact
  apply LipschitzWith.of_dist_le_mul
  intro x y
  unfold fejerComponent
  rw [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejerCoefficient_nonneg N h), ← dist_eq_norm]
  exact (mul_le_mul (fejerCoefficient_le_one hN h) (hc.dist_le_mul x y)
    dist_nonneg zero_le_one).trans_eq (one_mul _)

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_fejerAverage_le {N : ℕ} (hN : 0 < N) (f : Circle → E) {B : ℝ}
    (hf : ∀ t, ‖f t‖ ≤ B) : ‖fejerAverage N f‖ ≤ B := by
  apply (norm_integral_le_integral_norm _).trans
  have hi : Integrable (fun t : Circle => fejerPolynomial N t * B) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).mul continuous_const)
  have h := integral_mono_of_nonneg
    (ae_of_all circleHaar (fun t : Circle => norm_nonneg (fejerPolynomial N t • f t))) hi
    (ae_of_all circleHaar (fun t : Circle => by
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fejerPolynomial_nonneg N t)]
      exact mul_le_mul_of_nonneg_left (hf t) (fejerPolynomial_nonneg N t)))
  simpa only [integral_mul_const, integral_fejerPolynomial hN, one_mul] using h

theorem fejerAverage_sub (N : ℕ) {f g : Circle → E} (hf : Continuous f) (hg : Continuous g) :
    fejerAverage N (fun t => f t - g t) = fejerAverage N f - fejerAverage N g := by
  unfold fejerAverage
  simp only [smul_sub]
  have hi : Integrable (fun t : Circle => fejerPolynomial N t • f t) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul hf)
  have hj : Integrable (fun t : Circle => fejerPolynomial N t • g t) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul hg)
  exact integral_sub hi hj

theorem norm_fejerAverage_sub_average_le {N : ℕ} (hN : 0 < N) {f g : Circle → E}
    (hf : Continuous f) (hg : Continuous g) {B : ℝ} (hfg : ∀ t, ‖f t - g t‖ ≤ B) :
    ‖fejerAverage N f - fejerAverage N g‖ ≤ B := by
  rw [← fejerAverage_sub N hf hg]
  exact norm_fejerAverage_le hN _ hfg

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped NNReal BigOperators

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

theorem component_character (A : IsometricCircleAction X) (N : ℕ) (h : ℤ) (f : X → ℂ)
    (t : Circle) (x : X) :
    A.component N h f (A.act t x) = character ((-h) • t) * A.component N h f x := by
  let := A.toAddAction
  exact fejerComponent_vadd N h f t x

theorem component_lipschitz (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    (h : ℤ) {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (A.component N h f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_fejerComponent hN h hf A.isometry_act

theorem component_norm_le (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    (h : ℤ) {f : X → ℂ} {B : ℝ≥0} (hf : ∀ x, ‖f x‖ ≤ B) (x : X) :
    ‖A.component N h f x‖ ≤ B := by
  let := A.toAddAction
  exact norm_fejerComponent_le hN h hf x

end IsometricCircleAction
end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCircleActions
namespace OAI

section

namespace Erdos3.CircleFourier.IsometricCircleAction

open MeasureTheory
open scoped BigOperators

variable {X : Type*} [PseudoMetricSpace X]

theorem component_equivariant (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    {f : X → ℂ} (g : X → X) (z : ℂ)
    (hg : ∀ t x, A.act t (g x) = g (A.act t x))
    (hf : ∀ x, f (g x) = z * f x) (x : X) :
    A.component N h f (g x) = z * A.component N h f x := by
  unfold component fejerComponent circleFourierComponent
  change (fejerCoefficient N h : ℂ) *
      (∫ t : Circle, character ((-(-h)) • t) * f (A.act t (g x)) ∂circleHaar) =
    z * ((fejerCoefficient N h : ℂ) *
      (∫ t : Circle, character ((-(-h)) • t) * f (A.act t x) ∂circleHaar))
  have heq : (∫ t : Circle, character ((-(-h)) • t) * f (A.act t (g x)) ∂circleHaar) =
      z * (∫ t : Circle, character ((-(-h)) • t) * f (A.act t x) ∂circleHaar) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [hg, hf]
    ring
  rw [heq]
  ring

theorem component_preserves_character (A B : IsometricCircleAction X) (hAB : A.Commutes B)
    (N : ℕ) (h n : ℤ) {f : X → ℂ}
    (hf : ∀ t x, f (B.act t x) = character (n • t) * f x) (t : Circle) (x : X) :
    A.component N h f (B.act t x) = character (n • t) * A.component N h f x :=
  A.component_equivariant N h (B.act t) (character (n • t)) (fun u x => hAB u t x) (hf t) x

theorem component_sum {ι : Type*} (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    (s : Finset ι) (f : ι → X → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) (x : X) :
    A.component N h (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, A.component N h (f i) x := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  unfold component fejerComponent circleFourierComponent
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · exact Finset.mul_sum s _ _
  · intro i hi
    exact integrable_circleFourierComponent (-h) (hf i hi) x

end Erdos3.CircleFourier.IsometricCircleAction

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage
namespace OAI

section

namespace Erdos3

open MeasureTheory CircleFourier
open scoped Classical

theorem quotientLinearCharacter_integrable {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] (Γ : AddSubgroup E)
    [MeasurableSpace (E ⧸ Γ)] [BorelSpace (E ⧸ Γ)]
    (L : E →ₗ[ℝ] ℝ) (hint : ∀ x ∈ Γ, ∃ n : ℤ, L x = n) (hL : Continuous L)
    (μ : Measure (E ⧸ Γ)) [IsFiniteMeasure μ] :
    Integrable (quotientLinearCharacter Γ L hint) μ := by
  apply Integrable.of_bound (quotientLinearCharacter_continuous Γ L hint hL).aestronglyMeasurable 1
  exact ae_of_all μ (fun x => (quotientLinearCharacter_norm Γ L hint x).le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalApproximationScaling
namespace OAI

section

namespace Erdos3

theorem PolynomialRationalApproximation.nat_smul {I : Type*} {T : I → ℝ} {R : ℝ}
    {P : MvPolynomial I ℝ} (h : PolynomialRationalApproximation T R P)
    (q : ℕ) (hq : 0 < q) :
    PolynomialRationalApproximation T ((q : ℝ) * R) ((q : ℝ) • P) := by
  obtain ⟨D, hD, hDR, Q, hQ⟩ := h
  have hR : 0 ≤ R := (Nat.cast_nonneg D).trans hDR
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨D, hD, hDR.trans (by nlinarith), (q : ℤ) • Q, ?_⟩
  intro α
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  calc
    |(q : ℝ) * P.coeff α - ((q : ℝ) * ((Q.coeff α : ℤ) : ℝ)) / D| =
        (q : ℝ) * |P.coeff α - ((Q.coeff α : ℤ) : ℝ) / D| := by
      rw [mul_div_assoc, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
    _ ≤ (q : ℝ) * (R / monomialScale T α) :=
      mul_le_mul_of_nonneg_left (hQ α) (Nat.cast_nonneg q)
    _ = ((q : ℝ) * R) / monomialScale T α := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorCoefficientScaling
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem integerRowPolynomial_smul {I J : Type*} [Fintype J]
    (a : J → ℤ) (p : VectorPolynomial I ℝ (J → ℝ)) (r : ℝ) :
    integerRowPolynomial a (r • p) = r • integerRowPolynomial a p := by
  ext α
  simp only [integerRowPolynomial_coeff, MvPolynomial.coeff_smul, map_smul,
    Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def subspaceArrayCharacter {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ) : SubspaceArrayTorus I U → ℂ :=
  quotientLinearCharacter (subspaceArrayIntegerLattice I U)
    (subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)))
    (subspaceArrayFunctional_integral U frequency)

end Erdos3

end

section

namespace Erdos3

theorem arrayCoordinateEquiv_continuous {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) : Continuous (arrayCoordinateEquiv (I := I) U) := by
  apply continuous_pi
  intro i
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice I U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (arrayCoordinateLinear U i).continuous_of_finiteDimensional

end Erdos3

end

section

namespace Erdos3

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))

theorem euclideanSubspaceTorusEquiv_continuous : Continuous (euclideanSubspaceTorusEquiv U) := by
  apply (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (euclideanSubspaceArrayEquiv U).continuous

theorem euclideanSubspaceTorusEquiv_symm_continuous :
    Continuous (euclideanSubspaceTorusEquiv U).symm := by
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice Unit U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (euclideanSubspaceArrayEquiv U).symm.continuous

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

theorem scaledSiteResidual_preserves_lattice {I S J : Type*} [Fintype I] [Fintype S]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (T : Matrix I S ℤ) (q : ℕ)
    (x : I → U) (hx : x ∈ subspaceArrayIntegerLattice I U) :
    scaledLinearResidual (matrixModuleAction (fun s i => (E s i : ℝ)))
      (matrixModuleAction (fun i s => (T i s : ℝ))) (q : ℝ) x ∈ subspaceArrayIntegerLattice I U := by
  apply (subspaceArrayIntegerLattice I U).sub_mem ?_
    (integerMatrix_preserves_array_lattice U T _ (integerMatrix_preserves_array_lattice U E x hx))
  intro i a
  obtain ⟨z, hz⟩ := hx i a
  refine ⟨(q : ℤ) * z, ?_⟩
  change (q : ℝ) * (x i).val a = _
  rw [hz, Int.cast_mul, Int.cast_natCast]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedExtendedSiteSection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerSiteResidual_extend_columns {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S]
    (E₀ : Matrix S K ℤ) (E : Matrix S I ℤ) (e : K → I)
    (hcolumns : E.submatrix id e = E₀) (R : Matrix K I ℝ)
    (himage : Matrix.of (fun s k => (E₀ s k : ℝ)) * R = Matrix.of (fun s i => (E s i : ℝ)))
    (T : Matrix K S ℤ) (q : ℕ)
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (hT : ∀ (x : K → W),
      matrixModuleAction (fun s k => (E₀ s k : ℝ))
        (matrixModuleAction (fun k s => (T k s : ℝ))
          (matrixModuleAction (fun s k => (E₀ s k : ℝ)) x)) =
        (q : ℝ) • matrixModuleAction (fun s k => (E₀ s k : ℝ)) x)
    (x : I → W) :
    matrixModuleAction (fun s i => (E s i : ℝ))
      (matrixModuleAction (fun i s => (extendIntegerSiteSection e T i s : ℝ))
        (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
      (q : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x := by
  let E₀' := Matrix.of (fun s k => (E₀ s k : ℝ))
  let E' := Matrix.of (fun s i => (E s i : ℝ))
  let T' := Matrix.of (fun k s => (T k s : ℝ))
  let U' := Matrix.of (fun i s => (extendIntegerSiteSection e T i s : ℝ))
  have hc : E'.submatrix id e = E₀' := by
    ext s k
    exact congrArg (fun z : ℤ => (z : ℝ)) (congrFun (congrFun hcolumns s) k)
  have hET : E' * U' = E₀' * T' := by
    change E' * Matrix.of (fun i s => (extendIntegerSiteSection e T i s : ℝ)) = E₀' * T'
    rw [extendIntegerSiteSection_cast, ← Matrix.mul_assoc, matrix_mul_columnInclusion, hc]
  have hact (v : S → W) : matrixModuleAction E' (matrixModuleAction U' v) =
      matrixModuleAction E₀' (matrixModuleAction T' v) := by
    rw [matrixModuleAction_mul, hET, ← matrixModuleAction_mul]
  have hfactor : matrixModuleAction E₀' (matrixModuleAction R x) = matrixModuleAction E' x := by
    rw [matrixModuleAction_mul]
    exact congrArg (fun A => matrixModuleAction A x) himage
  change matrixModuleAction E' (matrixModuleAction U' (matrixModuleAction E' x)) =
    (q : ℝ) • matrixModuleAction E' x
  rw [hact, ← hfactor]
  exact hT (matrixModuleAction R x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteDensityMassBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteDensityTiltPMF_toReal {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < finiteDensityMass w D) (x : X) :
    (finiteDensityTiltPMF w S hw0 hw hZ D hD0 hD x).toReal =
      (w x / ∑' y, w y) * D x / finiteDensityMass w D := by
  rw [finiteDensityTiltPMF, realWeightPMF_apply]
  have he := (eq_div_iff hZ.ne').mp (finiteDensityMass_eq_div w D)
  rw [← he]
  field_simp

theorem finiteDensityTiltPMF_complexMean {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < finiteDensityMass w D) (f : X → ℂ) :
    (∑' x, ((finiteDensityTiltPMF w S hw0 hw hZ D hD0 hD x).toReal : ℂ) * f x) =
      (∑' x, ((w x / ∑' y, w y : ℝ) : ℂ) * ((D x : ℂ) * f x)) /
        (finiteDensityMass w D : ℂ) := by
  simp only [finiteDensityTiltPMF_toReal, Complex.ofReal_div, Complex.ofReal_mul,
    div_mul_eq_mul_div, mul_assoc, tsum_div_const]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

noncomputable def boundedColumnResidueRepresentative {K X : Type*} (modulus : X → ℕ)
    (r : ColumnResiduePattern K X modulus) : K × X → ℤ :=
  fun z => columnResidueRepresentative modulus r z % (modulus z.2 : ℤ)

theorem boundedColumnResidueRepresentative_bounds {K X : Type*} (modulus : X → ℕ)
    (hmodulus : ∀ x, 0 < modulus x) (r : ColumnResiduePattern K X modulus) (z : K × X) :
    0 ≤ boundedColumnResidueRepresentative modulus r z ∧
      boundedColumnResidueRepresentative modulus r z < (modulus z.2 : ℤ) := by
  have hq : (0 : ℤ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  exact ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialCoordinateRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem rowPolynomial_single {K : Type*} [Fintype K] (k : K) :
    rowPolynomial (Pi.single k (1 : ℤ)) = MvPolynomial.X k := by
  simp [rowPolynomial, Pi.single_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem coefficientTorusCharacter_integrable {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ] :
    Integrable (coefficientTorusCharacter U frequency) μ :=
  quotientLinearCharacter_integrable _ _ _
    (coefficientArrayFunctional U frequency).continuous_of_finiteDimensional μ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem coefficientLayerTorus_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    Continuous (coefficientLayerTorus (K := K) U j) := by
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (coefficientLayerArray U j).continuous_of_finiteDimensional

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem integerMatrixTorusMap_continuous {I S J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) :
    Continuous (integerMatrixTorusMap U E) := by
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice I U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp
    (matrixModuleAction (W := U) (fun s i => (E s i : ℝ))).continuous_of_finiteDimensional

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

theorem siteBooleanJetTorusMap_continuous {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (rows : ∀ j, O j → Finset α) :
    Continuous (siteBooleanJetTorusMap U rows) :=
  continuous_pi (fun j => (integerMatrixTorusMap_continuous _ _).comp (continuous_apply j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

instance euclideanJetLayers_borel [∀ j, Fintype (O j)] : BorelSpace (EuclideanJetLayers U O) := by
  let : ∀ j, BorelSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  let : ∀ j, BorelSpace (O j → euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => Pi.borelSpace
  exact Pi.borelSpace

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}
  (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientLayerEndomorphism
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j)) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U :=
  LinearMap.pi (fun s => (LinearMap.proj s.2).comp ((R s.1).comp (coefficientLayerArray U s.1)))

theorem coefficientLayerEndomorphism_insertion
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j)) (j : Fin m)
    (v : BoundedCoefficientExponent K (j.val + 1) → U j) :
    coefficientLayerEndomorphism U R (coefficientLayerInsertion U j v) =
      coefficientLayerInsertion U j (R j v) := by
  funext s
  rcases s with ⟨k, d⟩
  by_cases hk : k = j
  · subst k
    change R j (fun e => coefficientLayerInsertion U j v ⟨j, e⟩) d = _
    simp only [coefficientLayerInsertion_same]
  · change R k (fun e => coefficientLayerInsertion U j v ⟨k, e⟩) d = _
    simp only [coefficientLayerInsertion_ne U j k hk]
    change R k 0 d = 0
    rw [map_zero, Pi.zero_apply]

theorem coefficientLayerEndomorphism_preserves_lattice
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j))
    (hR : ∀ j x, x ∈ subspaceArrayIntegerLattice _ (U j) →
      R j x ∈ subspaceArrayIntegerLattice _ (U j))
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientLayerEndomorphism U R x ∈ coefficientIntegerLattice U := by
  intro s a
  exact hR s.1 (coefficientLayerArray U s.1 x)
    (coefficientLayerArray_preserves_lattice U s.1 x hx) s.2 a

theorem coefficientArrayFunctional_endomorphism_zero_iff [Fintype K] [∀ j, Fintype (J j)]
    (R : ∀ j, (BoundedCoefficientExponent K (j.val + 1) → U j) →ₗ[ℝ]
      (BoundedCoefficientExponent K (j.val + 1) → U j))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    (coefficientArrayFunctional U frequency).comp (coefficientLayerEndomorphism U R) = 0 ↔
      ∀ j, (subspaceArrayFunctional (U j) (fun d => fun a => (frequency j d.val a : ℝ))).comp
        (R j) = 0 := by
  constructor
  · intro h j
    apply LinearMap.ext
    intro v
    have hv := DFunLike.congr_fun h (coefficientLayerInsertion U j v)
    simpa only [LinearMap.comp_apply, coefficientLayerEndomorphism_insertion,
      coefficientArrayFunctional_layerInsertion, LinearMap.zero_apply] using hv
  · intro h
    apply LinearMap.ext
    intro x
    change (∑ s : CoefficientSlot K m, ∑ a,
      (frequency s.1 s.2.val a : ℝ) * ((coefficientLayerEndomorphism U R x) s).val a) = 0
    rw [Fintype.sum_sigma]
    apply Finset.sum_eq_zero
    intro j _
    exact DFunLike.congr_fun (h j) (coefficientLayerArray U j x)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
  {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientSiteResidual (site : S → K → ℤ) (q : Fin m → ℕ)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ) :
    CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U :=
  coefficientLayerEndomorphism U (fun j =>
    scaledLinearResidual (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ)))
      (matrixModuleAction (fun d s => (T j d s : ℝ))) (q j : ℝ))

theorem coefficientSiteResidual_preserves_lattice (site : S → K → ℤ) (q : Fin m → ℕ)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientSiteResidual U site q T x ∈ coefficientIntegerLattice U :=
  coefficientLayerEndomorphism_preserves_lattice U _
    (fun j x hx => scaledSiteResidual_preserves_lattice (U j) _ (T j) (q j) x hx) x hx

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

abbrev LowBooleanJetTorus (α : Type*) {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :=
  BooleanJetTorus (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) U

noncomputable def siteFromLowBooleanJets {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    LowBooleanJetTorus α U →+ SiteTorus (Finset α) U where
  toFun y j := integerMatrixTorusMap (U j) (boundedBooleanReconstructionMatrix α (j.val + 1)) (y j)
  map_zero' := funext (fun j => map_zero (integerMatrixTorusMap (U j) _))
  map_add' x y := funext (fun j => map_add (integerMatrixTorusMap (U j) _) (x j) (y j))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem coefficientTorusFourierSum_integrable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ] :
    Integrable (coefficientTorusFourierSum U frequency c) μ := by
  apply integrable_finsetSum
  intro a _
  exact (coefficientTorusCharacter_integrable U (frequency a) μ).const_mul (c a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem coefficientTorusCharacter_slot_product {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ s : CoefficientSlot K m, J s.1 → ℤ) (x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U (coefficientSlotFrequency frequency) x =
      ∏ s : CoefficientSlot K m, subspaceArrayCharacter (U s.1) (fun _ a => frequency s a)
        (coefficientCoordinateTorus U x s) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [coefficientTorusCharacter_mk]
  change CircleFourier.character ((∑ s : CoefficientSlot K m, ∑ a,
    (coefficientSlotFrequency frequency s.1 s.2.val a : ℝ) * (y s).val a : ℝ) :
      CircleFourier.Circle) = _
  simp only [coefficientSlotFrequency_apply]
  rw [character_real_sum]
  apply Finset.prod_congr rfl
  intro s _
  rw [coefficientCoordinateTorus_mk]
  change _ = CircleFourier.character
    ((∑ _u : Unit, ∑ a, (frequency s a : ℝ) * (y s).val a : ℝ) : CircleFourier.Circle)
  simp only [Fintype.sum_unique]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedCircleComponent (N : ℕ) (A : α → IsometricCircleAction X) :
    (is : List α) → (Fin is.length → ℤ) → (X → ℂ) → X → ℂ
  | [], _, f => f
  | i :: is, k, f => (A i).component N (k 0)
      (iteratedCircleComponent N A is (fun j => k j.succ) f)

theorem iteratedCircleComponent_lipschitz {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (iteratedCircleComponent N A is k f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).component_lipschitz hN (k 0) (ih (fun j => k j.succ))

theorem iteratedCircleComponent_norm_le {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    {f : X → ℂ} {B : ℝ≥0} (hf : ∀ x, ‖f x‖ ≤ B) :
    ∀ x, ‖iteratedCircleComponent N A is k f x‖ ≤ B := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).component_norm_le hN (k 0) (ih (fun j => k j.succ))

theorem iteratedCircleComponent_character (N : ℕ)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j)) (f : X → ℂ)
    (j : Fin is.length) : ∀ (t : Circle) x,
    iteratedCircleComponent N A is k f ((A (is.get j)).act t x) =
      character ((-k j) • t) * iteratedCircleComponent N A is k f x := by
  induction is with
  | nil => exact Fin.elim0 j
  | cons i is ih =>
    have ht : ∀ a ∈ is, ∀ b ∈ is, (A a).Commutes (A b) :=
      fun a ha b hb => hcomm a (List.mem_cons_of_mem i ha) b (List.mem_cons_of_mem i hb)
    refine Fin.cases ?_ (fun q => ?_) j
    · exact (A i).component_character N (k 0) (iteratedCircleComponent N A is (fun q => k q.succ) f)
    · have hm : is.get q ∈ is := List.get_mem is q
      exact (A i).component_preserves_character (A (is.get q))
        (hcomm i (List.mem_cons_self) (is.get q) (List.mem_cons_of_mem i hm))
        N (k 0) (-(k q.succ)) (ih (fun r => k r.succ) ht q)

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

abbrev FejerChoice (N : ℕ) := ↥(fejerFrequencies N)

variable {X α : Type*} [PseudoMetricSpace X]

theorem card_fejerChoices (N d : ℕ) :
    Fintype.card (Fin d → FejerChoice N) ≤ N ^ (2 * d) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  apply (Nat.pow_le_pow_left (card_fejerFrequencies_le N) d).trans_eq
  rw [pow_mul]

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X α : Type*} [PseudoMetricSpace X]

theorem iteratedCircleComponent_equivariant (N : ℕ) (A : α → IsometricCircleAction X)
    (is : List α) (k : Fin is.length → ℤ) (g : X → X) (z : ℂ)
    (hg : ∀ i ∈ is, ∀ t x, (A i).act t (g x) = g ((A i).act t x))
    {f : X → ℂ} (hf : ∀ x, f (g x) = z * f x) :
    ∀ x, iteratedCircleComponent N A is k f (g x) = z * iteratedCircleComponent N A is k f x := by
  induction is with
  | nil => exact hf
  | cons i is ih =>
    exact (A i).component_equivariant N (k 0) g z (hg i List.mem_cons_self)
      (ih (fun j => k j.succ) (fun a ha => hg a (List.mem_cons_of_mem i ha)))

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CanonicalDensityFourier
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem subspaceAmbientTorus_character {J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : J → ℤ) (x : SubspaceArrayTorus Unit U) :
    (∏ j, CircleFourier.character (frequency j • subspaceAmbientTorus U x j)) =
      subspaceArrayCharacter U (Matrix.of (fun (_ : Unit) j => frequency j)) x := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice Unit U) x
  simp only [subspaceAmbientTorus_mk]
  change _ = CircleFourier.character
    ((∑ _u : Unit, ∑ j, (frequency j : ℝ) * (y ()).val j : ℝ) : UnitAddCircle)
  rw [Fintype.sum_unique, character_real_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientAmbientCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}

variable [Fintype K] [∀ j, Fintype (J j)]

theorem coefficientAmbientTorus_character (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : CoefficientAmbientIndex K J → ℤ) (x : CoefficientTorus (K := K) U) :
    (∏ t, CircleFourier.character (frequency t • coefficientAmbientTorus U x t)) =
      coefficientTorusCharacter U (coefficientSlotFrequency (fun s i => frequency ⟨s, i⟩)) x := by
  rw [coefficientTorusCharacter_slot_product, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro s _
  exact subspaceAmbientTorus_character (U s.1) (fun i => frequency ⟨s, i⟩)
    (coefficientCoordinateTorus U x s)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalCoverLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem coefficientCover_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 0 < q) :
    MeasurePreserving (quotientIntegerCover (coefficientIntegerLattice U) q) μ μ := by
  have : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving
    (quotientIntegerCover_continuous (coefficientIntegerLattice U) q)
    (quotientIntegerCover_surjective (coefficientIntegerLattice U) q hq) rfl

theorem coefficientCover_integrable {K E : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [NormedAddCommGroup E]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 0 < q) (f : CoefficientTorus (K := K) U → E) (hf : Integrable f μ) :
    Integrable (fun x => f (quotientIntegerCover (coefficientIntegerLattice U) q x)) μ :=
  (coefficientCover_measurePreserving U μ q hq).integrable_comp_of_integrable hf

theorem coefficientCover_integral {K E : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (q : ℕ) (hq : 0 < q) (f : CoefficientTorus (K := K) U → E)
    (hf : AEStronglyMeasurable f μ) :
    (∫ x, f (quotientIntegerCover (coefficientIntegerLattice U) q x) ∂μ) = ∫ x, f x ∂μ := by
  have hp := coefficientCover_measurePreserving U μ q hq
  have hf' : AEStronglyMeasurable f (Measure.map (quotientIntegerCover (coefficientIntegerLattice U) q) μ) := by
    rwa [hp.map_eq]
  simpa only [hp.map_eq] using (integral_map hp.measurable.aemeasurable hf').symm

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrTorusApproximation
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open _root_.Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

def ndilate (B : Set N) (t : ℝ≥0) : Set N := B.dilate t

end Erdos3.CyclicBohr.Set

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCubeNativeDetection
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

noncomputable def integerSelfSiteTest {X : Type*} (q : ℕ) (f : (X → ℤ) → ℂ)
    (site : Finset (Fin q)) (y : X → ℝ) : ℂ :=
  conjugationPower site.card (f (fun x => ⌊y x⌋))

theorem integerSelfSiteTest_norm_le {X : Type*} (q : ℕ) (f : (X → ℤ) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (site : Finset (Fin q)) (y : X → ℝ) :
    ‖integerSelfSiteTest q f site y‖ ≤ 1 := by
  rw [integerSelfSiteTest, conjugationPower_norm]
  exact hf _

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

theorem mean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  rw [mean, mean, Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun x _ => hfg x) (Nat.cast_nonneg _)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem narrowTrimmedSpatialWidths_le {G J X : Type*}
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (z : Option (G ⊕ J) × X) :
    narrowTrimmedSpatialWidths W τ ξ N z ≤ trimmedSpatialWidths W τ N z := by
  rcases z with ⟨_ | (g | j), x⟩
  · exact le_rfl
  · exact le_rfl
  · exact mul_le_of_le_one_left (trimmedSpatialWidths_pos hW hτ N hN _).le hξ1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalRowsStandardCoordinates
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})

noncomputable def physicalRowsToStandard
    (z : EuclideanJetLayers U Row) :
    EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) :=
  fun j s => z j ((boundedBooleanJetRowsEquiv (Fin q) (j.val + 1)).symm s)

end Erdos3.BooleanCubeKernel

end

end OAI
end


