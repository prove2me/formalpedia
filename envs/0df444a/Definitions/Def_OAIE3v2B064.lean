-- Prove2me | Definitions.Def_OAIE3v2B064
-- name    : OAIE3v2B064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:17:02.189853+00:00
-- url     : https://prove2.me/theorems/20c6f5b3-2a80-45bc-a195-a2875b4af198
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 65 of 311
-- statement:
--   Definitions bundle 65 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B004`, `OAIE3v2B006`, `OAIE3v2B007`, `OAIE3v2B008`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B013`, `OAIE3v2B014`, `OAIE3v2B015`, `OAIE3v2B016`, `OAIE3v2B017`, `OAIE3v2B024`, `OAIE3v2B025`, `OAIE3v2B029`, `OAIE3v2B030`, `OAIE3v2B031`, `OAIE3v2B032`, `OAIE3v2B036` of this split.
--
--   Modules: `Dynamics/IdealSiteEnvelopeBudget.lean`, `Dynamics/PreparedModularCanonicalDetectorPeriodBudget.lean`, `Estimates/AllocatedAmbientLogBounds.lean`, `Estimates/AllocatedCanonicalPeriodPrimitiveBounds.lean`, `Estimates/AllocatedFullSiteRadius.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/BufferedSiteExpansion.lean`, `Estimates/CanonicalScalarSourceEnvelope.lean`, `Estimates/ComplexFiniteMeans.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/CubeTranslation.lean`, `Estimates/FiniteInnerProgressionFamily.lean`, `Estimates/InactiveShortLogBounds.lean`, `Estimates/MixedArrayReference.lean`, `Estimates/MixedCoefficientCounting.lean`, `Estimates/MixedPairComparison.lean`, `Estimates/NativeCommonModelQuadruples.lean`, `Estimates/PhysicalActiveIdealSite.lean`, `Estimates/SmallWeightedPhysicalReplacement.lean`, `Estimates/SplitSmoothProductProfile.lean`, `Estimates/WeightedSummandCorrelation.lean`, `Fourier/CanonicalDensityFourier.lean`, `Fourier/IntegerPeriodicTorusLift.lean`, `Fourier/QuadraticFrequencyCoordinates.lean`, `Fourier/RealQuarterTorusExtension.lean`, `Geometry/AllocatedInactiveSupportBudget.lean`, `Geometry/BoxCyclicEncoding.lean`, `Geometry/BoxDetectionExponents.lean`, `Geometry/BoxDifferenceHom.lean`, `Geometry/IdealSiteBoxRadius.lean`, `Geometry/PartitionedIdealSupport.lean`, `Geometry/ScalarReferenceNativeDetectionCoordinateEquiv.lean`, `Geometry/SmallBoxCutoff.lean`, `Geometry/SpatialTupleErrorBudget.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Geometry/WeightedBlockSupportScale.lean`, `Lattices/IntegerPeriodPivot.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/LatticeSheetHaar.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/PositiveIntegerPeriodization.lean`, `Lattices/ShortIntegerCubeBudget.lean`, `Linear/AllocatedFixedDensityProjection.lean`, `Linear/AllocatedFixedKernelReplacement.lean`, `Linear/FixedKernelDensityProjection.lean`, `Linear/SharedFreeComparisonBasis.lean`, `Probability/BinaryDensity.lean`, `Probability/FiniteArrayMeasure.lean`, `Probability/SampledWeightCellLaw.lean`, `Sampling/AllocatedSlicedGridGeometryBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B008
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B014
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B016
import Definitions.Def_OAIE3v2B017
import Definitions.Def_OAIE3v2B024
import Definitions.Def_OAIE3v2B025
import Definitions.Def_OAIE3v2B029
import Definitions.Def_OAIE3v2B030
import Definitions.Def_OAIE3v2B031
import Definitions.Def_OAIE3v2B032
import Definitions.Def_OAIE3v2B036

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem expect_prod_boolean_pow_le {Ω : Type*} [Fintype Ω]
    (n : ℕ) (F : (Fin n → Bool) → Ω → ℝ) (hF : ∀ ω x, 0 ≤ F ω x) :
    (𝔼 x, ∏ ω, F ω x) ^ (2 ^ n) ≤ ∏ ω, 𝔼 x, F ω x ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let A (b : Bool) (x : Ω) := ∏ ω : Fin n → Bool, F (Fin.cons b ω) x
    have hprod (x : Ω) : (∏ ω, F ω x) = A false x * A true x :=
      prod_bool_tuple_succ _
    have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (A false) (A true)
    have hpart (b : Bool) : (𝔼 x, A b x ^ 2) ^ (2 ^ n) ≤
        ∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons b ω) x ^ (2 ^ (n + 1)) := by
      have h := ih (fun ω x ↦ F (Fin.cons b ω) x ^ 2) (fun _ _ ↦ sq_nonneg _)
      simpa only [A, ← Finset.prod_pow, ← pow_mul, ← pow_succ'] using h
    calc
      (𝔼 x, ∏ ω, F ω x) ^ (2 ^ (n + 1)) =
          ((𝔼 x, A false x * A true x) ^ 2) ^ (2 ^ n) := by
        simp_rw [hprod]
        rw [← pow_mul, pow_succ']
      _ ≤ ((𝔼 x, A false x ^ 2) * (𝔼 x, A true x ^ 2)) ^ (2 ^ n) :=
        pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ = (𝔼 x, A false x ^ 2) ^ (2 ^ n) * (𝔼 x, A true x ^ 2) ^ (2 ^ n) :=
        mul_pow _ _ _
      _ ≤ (∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons false ω) x ^ (2 ^ (n + 1))) *
          (∏ ω : Fin n → Bool, 𝔼 x, F (Fin.cons true ω) x ^ (2 ^ (n + 1))) := by
        apply mul_le_mul (hpart false) (hpart true)
        · exact pow_nonneg (Finset.expect_nonneg (fun _ _ ↦ sq_nonneg _)) _
        · exact Finset.prod_nonneg (fun ω _ ↦ Finset.expect_nonneg
            (fun x _ ↦ pow_nonneg (hF _ x) _))
      _ = ∏ ω, 𝔼 x, F ω x ^ (2 ^ (n + 1)) :=
        (prod_bool_tuple_succ (fun ω ↦ 𝔼 x, F ω x ^ (2 ^ (n + 1)))).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BinaryDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem binaryDensity_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (binaryDensity f g) := (hf.comp measurable_fst).mul (hg.comp measurable_snd)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem binaryDensity_measure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) :
    (realDensityMeasure μ f).prod (realDensityMeasure ν g) =
      realDensityMeasure (μ.prod ν) (binaryDensity f g) := by
  unfold realDensityMeasure
  rw [prod_withDensity hf.ennreal_ofReal hg.ennreal_ofReal]
  congr 1
  funext p
  exact (ENNReal.ofReal_mul (hf0 p.1)).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteSiteExtension_test_mean {T X : Type*} [Nonempty T] [DecidableEq X]
    (e : T → X) (he : Function.Injective e) (A : Finset T)
    (f w : T → ℂ) (ψ : X → ℂ) (hw : ∀ t ∈ A, w t = star (ψ (e t))) :
    (𝔼 t ∈ A, f t * w t) = finiteCorrelation (A.image e) (finiteSiteExtension e f) ψ := by
  unfold finiteCorrelation
  rw [Finset.expect_image he.injOn]
  apply Finset.expect_congr rfl
  intro t ht
  rw [finiteSiteExtension_apply e he, hw t ht]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem lipschitz_real_mul_of_bounds {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) :
    LipschitzWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) := by
  have hfc : LipschitzWith Kf (fun x => (f x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hf.dist_le_mul x y
  have hgc : LipschitzWith Kg (fun x => (g x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hg.dist_le_mul x y
  have h := lipschitz_mul_of_bounds _ _ hfc hgc
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hBf x)
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hBg x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [← Complex.ofReal_mul, Complex.isometry_ofReal.dist_eq] using h.dist_le_mul x y

theorem bounded_lipschitz_real_prod {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (f : ι → X → ℝ) {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ i, LipschitzWith K (f i)) (hn : ∀ i x, |f i x| ≤ B) :
    (∀ x, |∏ i, f i x| ≤ (B : ℝ)^Fintype.card ι) ∧
      LipschitzWith (Fintype.card ι * K * B^Fintype.card ι) (fun x => ∏ i, f i x) := by
  have hfc (i : ι) : LipschitzWith K (fun x => (f i x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact (hf i).dist_le_mul x y
  obtain ⟨hb, hl⟩ := bounded_lipschitz_fintype_prod (fun i x => (f i x : ℂ)) hB hfc
    (fun i x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hn i x)
  constructor
  · intro x
    simpa only [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs] using hb x
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [← Complex.ofReal_prod, Complex.isometry_ofReal.dist_eq] using hl.dist_le_mul x y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem gowersMoment_const_one (j : ℕ) : gowersMoment j (fun _ : H ↦ 1) = 1 := by
  induction j with
  | zero => simp [gowersMoment]
  | succ j ih =>
    change (𝔼 h : H, gowersMoment j (multiplicativeDerivative (fun _ : H ↦ 1) h)) = 1
    have hder (h : H) : multiplicativeDerivative (fun _ : H ↦ 1) h = (fun _ : H ↦ 1) := by
      funext x
      simp [multiplicativeDerivative]
    simp_rw [hder, ih]
    exact Fintype.expect_one (ι := H)

theorem gowersNorm_const_one (j : ℕ) : gowersNorm j (fun _ : H ↦ 1) = 1 := by
  simp [gowersNorm, gowersMoment_const_one]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

variable [Fintype H]

omit [AddCommGroup H] in

theorem cubeAverage_eq_expect_tuple {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
    (j : ℕ) (F : List H → M) :
    cubeAverage j F = 𝔼 h : Fin j → H, F (List.ofFn h) := by
  induction j generalizing F with
  | zero => simp [cubeAverage]
  | succ j ih =>
    rw [cubeAverage, expect_fin_cons]
    apply Finset.expect_congr rfl
    intro h hh
    rw [ih]
    apply Finset.expect_congr rfl
    intro hs hhs
    simp

omit [AddCommGroup H] in
theorem cubeAverage_re (j : ℕ) (F : List H → ℂ) :
    (cubeAverage j F).re = cubeAverage j (fun hs ↦ (F hs).re) := by
  simp only [cubeAverage_eq_expect_tuple, expect_re]

omit [AddCommGroup H] in
theorem cubeAverage_comm_expect {Ω : Type*} [Fintype Ω]
    {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (j : ℕ) (F : List H → Ω → M) :
    cubeAverage j (fun hs ↦ 𝔼 x, F hs x) = 𝔼 x, cubeAverage j (fun hs ↦ F hs x) := by
  simp only [cubeAverage_eq_expect_tuple]
  exact Finset.expect_comm _ _ _

omit [AddCommGroup H] in
theorem cubeAverage_norm_inner_sq_le (j : ℕ) (F G : List H → ℂ) :
    ‖cubeAverage j (fun hs ↦ F hs * star (G hs))‖ ^ 2 ≤
      cubeAverage j (fun hs ↦ ‖F hs‖ ^ 2) * cubeAverage j (fun hs ↦ ‖G hs‖ ^ 2) := by
  simp only [cubeAverage_eq_expect_tuple]
  exact norm_expect_mul_star_sq_le _ _

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
open scoped BigOperators

theorem tensorCutoffWeight_nonneg {ι : Type*} {E : ι → Type*} [Fintype ι]
    (w : ∀ i, E i → ℝ) (hw : ∀ i x, 0 ≤ w i x) (x : ∀ i, E i) :
    0 ≤ tensorCutoffWeight w x := Finset.prod_nonneg (fun i _ => hw i (x i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDetectionExponents
namespace OAI

section

namespace Erdos3

def boxInductionInputBudget (a b : ℕ) (p : ℝ) : ℝ :=
  (p + 1 + b) ^ b + 2 * boxModeBudget a p + 2 * p + 3

def boxRetainedBudget (a : ℕ) (p : ℝ) : ℝ := 2 * boxModeBudget a p + 2 * p + 6

def boxDetectionStepBudget (s a b c : ℕ) (p : ℝ) : ℝ :=
  ((s + 2) ^ (s + 2) : ℕ) * p + (s + 1 : ℕ) * (boxRetainedBudget a p + p) +
    (2 ^ (s + 1) : ℕ) * (boxInductionInputBudget a b p + c) ^ c + boxRetainedBudget a p

theorem boxModeBudget_nonneg (a : ℕ) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ boxModeBudget a p := by
  unfold boxModeBudget
  positivity

theorem boxInductionInputBudget_bounds (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + 1 + b) ^ b ≤ boxInductionInputBudget a b p ∧
    2 * boxModeBudget a p + 1 ≤ boxInductionInputBudget a b p ∧
    p ≤ boxInductionInputBudget a b p := by
  have hmode := boxModeBudget_nonneg a hp
  have hpow : 0 ≤ (p + 1 + b) ^ b := by positivity
  unfold boxInductionInputBudget
  constructor
  · linarith
  constructor <;> linarith

theorem boxDetectionStepBudget_nonneg (s a b c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ boxDetectionStepBudget s a b c p := by
  unfold boxDetectionStepBudget boxRetainedBudget boxInductionInputBudget boxModeBudget
  positivity

theorem exists_boxDetectionStepBudget_bound (s a b c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → boxDetectionStepBudget s a b c p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 1 + Polynomial.C a) ^ a + 2
  let K := (X + 1 + Polynomial.C b) ^ b + 2 * R + 2 * X + 3
  let V := 2 * R + 2 * X + 6
  let P := Polynomial.C ((s + 2) ^ (s + 2)) * X + Polynomial.C (s + 1) * (V + X) +
    Polynomial.C (2 ^ (s + 1)) * (K + Polynomial.C c) ^ c + V
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, V, K, R, X, Polynomial.eval₂_pow, boxDetectionStepBudget,
    boxRetainedBudget, boxInductionInputBudget, boxModeBudget] using hbound p hp

end Erdos3

end

section

namespace Erdos3

theorem box_detection_exponential_product (s a b c d : ℕ) {p : ℝ} (hd : (d : ℝ) ≤ p) :
    Real.exp (-boxDetectionStepBudget s a b c p) ≤
      ((1 : ℝ) / ((s : ℝ) + 2) ^ (s + 2)) ^ d *
        Real.exp (-(boxRetainedBudget a p + p)) ^ (s + 1) *
        Real.exp (-((boxInductionInputBudget a b p + c) ^ c)) ^ (2 ^ (s + 1)) *
        Real.exp (-boxRetainedBudget a p) := by
  have hc : Real.exp (-(((s + 2) ^ (s + 2) : ℕ) : ℝ) * p) ≤
      ((1 : ℝ) / ((s : ℝ) + 2) ^ (s + 2)) ^ d := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using
      exp_neg_nat_mul_le_inverse_pow ((s + 2) ^ (s + 2)) d (by positivity) hd
  calc
    _ = Real.exp (-(((s + 2) ^ (s + 2) : ℕ) : ℝ) * p) *
        Real.exp (-(boxRetainedBudget a p + p)) ^ (s + 1) *
        Real.exp (-((boxInductionInputBudget a b p + c) ^ c)) ^ (2 ^ (s + 1)) *
        Real.exp (-boxRetainedBudget a p) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold boxDetectionStepBudget
      ring
    _ ≤ _ := by gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def mixedGowersMoment : (j : ℕ) → ((Fin j → Bool) → H → ℂ) → ℂ
  | 0, F => 𝔼 x, F default x
  | j + 1, F => 𝔼 h, mixedGowersMoment j
      (fun ω ↦ crossDerivative (F (Fin.cons false ω)) (F (Fin.cons true ω)) h)

theorem mixedGowersMoment_const (j : ℕ) (f : H → ℂ) :
    mixedGowersMoment j (fun _ ↦ f) = gowersMoment j f := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih => simp only [mixedGowersMoment, crossDerivative_self, ih, gowersMoment]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem norm_gowersMoment_le_mean_norm (j : ℕ) (f : H → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) : ‖gowersMoment j f‖ ≤ 𝔼 x, ‖f x‖ := by
  induction j generalizing f with
  | zero => exact RCLike.norm_expect_le (K := ℂ)
  | succ j ih =>
    have hunit (h x : H) : ‖multiplicativeDerivative f h x‖ ≤ 1 := by
      simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
        mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hnorm (h x : H) : ‖multiplicativeDerivative f h x‖ ≤ ‖f x‖ := by
      simpa only [multiplicativeDerivative, norm_mul, norm_star, mul_one] using
        mul_le_mul_of_nonneg_left (hf (x + h)) (norm_nonneg (f x))
    calc
      _ ≤ 𝔼 h, ‖gowersMoment j (multiplicativeDerivative f h)‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 𝔼 _h : H, 𝔼 x, ‖f x‖ := by
        apply Finset.expect_le_expect
        intro h _
        exact (ih _ (hunit h)).trans (Finset.expect_le_expect (fun x _ => hnorm h x))
      _ = _ := Fintype.expect_const _

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [AddCommGroup H] in
theorem norm_expect_restrict_one (Q : Finset H) :
    ‖𝔼 x, restrictTo Q (fun _ ↦ 1) x‖ = (Q.card : ℝ) / Fintype.card H := by
  rw [expect_restrictTo]
  simp

noncomputable def restrictedGowersNorm (j : ℕ) (Q : Finset H) (f : H → ℂ) : ℝ :=
  gowersNorm j (restrictTo Q f) / gowersNorm j (restrictTo Q (fun _ ↦ 1))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def groupCubeSet (j : ℕ) (Q : Finset H) : Finset ((Fin j → H) × H) :=
  Finset.univ.filter (fun p ↦ ∀ ω : Fin j → Bool, p.2 + cubeShift p.1 ω ∈ Q)

def groupCubeCount (j : ℕ) (Q : Finset H) : ℕ := (groupCubeSet j Q).card

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A]

section FiniteAmbient

variable [Fintype A] [DecidableEq A]

noncomputable def supportedCubeFinsetEquiv (j : ℕ) (Q : Finset A) :
    SupportedCube j (Q : Set A) ≃ (groupCubeSet j Q) :=
  Equiv.subtypeEquivRight (fun p ↦ by simp [groupCubeSet])

theorem card_supportedCube (j : ℕ) (Q : Finset A) :
    Nat.card (SupportedCube j (Q : Set A)) = groupCubeCount j Q := by
  rw [Nat.card_congr (supportedCubeFinsetEquiv j Q), Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

end FiniteAmbient

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

variable [Fintype B] [DecidableEq B]

omit [Fintype B] in
theorem restrictTo_imageExtension (φ : A →+ B) (Q : Finset A) (f : A → ℂ) :
    restrictTo (Q.image φ) (imageExtension φ Q f) = imageExtension φ Q f := by
  classical
  funext y
  by_cases hy : y ∈ Q.image φ
  · simp only [restrictTo, if_pos hy]
  · rw [restrictTo, if_neg hy]
    exact (imageExtension_eq_zero f (by
      rintro ⟨a, ha, he⟩
      exact hy (Finset.mem_image.mpr ⟨a, ha, he⟩))).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeTranslation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [DecidableEq A]

def supportedCubeTranslateEquiv (j : ℕ) (Q : Finset A) (a : A) :
    SupportedCube j (Q : Set A) ≃ SupportedCube j (translateSupport a Q : Set A) where
  toFun p := ⟨(p.val.1, a + p.val.2), fun ω ↦ by
    apply (mem_translateSupport a Q _).mpr
    simpa only [Finset.mem_coe, add_sub_cancel_left, add_assoc, add_sub_cancel_right] using p.property ω⟩
  invFun p := ⟨(p.val.1, p.val.2 - a), fun ω ↦ by
    have h := (mem_translateSupport a Q _).mp (p.property ω)
    simpa only [Finset.mem_coe, sub_add_eq_add_sub] using h⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val.1, (a + p.val.2) - a) = p.val
    apply Prod.ext
    · rfl
    · simp
  right_inv p := by
    apply Subtype.ext
    change (p.val.1, a + (p.val.2 - a)) = p.val
    apply Prod.ext
    · rfl
    · simp

theorem card_supportedCube_translate (j : ℕ) (Q : Finset A) (a : A) :
    Nat.card (SupportedCube j (translateSupport a Q : Set A)) =
      Nat.card (SupportedCube j (Q : Set A)) :=
  (Nat.card_congr (supportedCubeTranslateEquiv j Q a)).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def boxReduction (T : ι → ℕ) : (ι → ℤ) →+ BoxAmbient T where
  toFun x i := x i
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem boxReduction_apply (T : ι → ℕ) (x : ι → ℤ) (i : ι) :
    boxReduction T x i = (x i : ZMod (4 * T i)) := rfl

theorem boxReduction_reflectsPairSums (T : ι → ℕ) :
    ReflectsPairSums (boxReduction T) (integerBox T : Set (ι → ℤ)) := by
  intro a ha b hb c hc d hd he
  have ha' := (mem_integerBox T a).mp ha
  have hb' := (mem_integerBox T b).mp hb
  have hc' := (mem_integerBox T c).mp hc
  have hd' := (mem_integerBox T d).mp hd
  funext i
  change a i + b i = c i + d i
  apply int_eq_of_zmod_eq_of_bounds (m := 4 * T i)
  · have h1 := ha' i
    have h2 := hb' i
    constructor <;> push_cast <;> omega
  · have h1 := hc' i
    have h2 := hd' i
    constructor <;> push_cast <;> omega
  · have hi := congrFun he i
    simpa only [Pi.add_apply, boxReduction_apply, Int.cast_add] using hi

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def integerBoxCubeCount (T : ι → ℕ) (j : ℕ) : ℕ :=
  Nat.card (SupportedCube j (integerBox T : Set (ι → ℤ)))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem small_increments_supported (j : ℕ) (x : ι → ℤ)
    (hx : x ∈ integerBox (smallCubeSide T j)) (ds : Fin j → (ι → ℤ))
    (hds : ∀ k, ds k ∈ integerBox (smallCubeSide T j)) (ω : Fin j → Bool) :
    x + cubeShift ds ω ∈ integerBox T := by
  apply (mem_integerBox T _).mpr
  intro i
  let m := (T i - 1) / (j + 1)
  have hxi : 0 ≤ x i ∧ x i ≤ (m : ℤ) := by
    have h := (mem_integerBox _ _).mp hx i
    change 0 ≤ x i ∧ x i < ((m + 1 : ℕ) : ℤ) at h
    push_cast at h
    omega
  have hdi (k : Fin j) : 0 ≤ ds k i ∧ ds k i ≤ (m : ℤ) := by
    have h := (mem_integerBox _ _).mp (hds k) i
    change 0 ≤ ds k i ∧ ds k i < ((m + 1 : ℕ) : ℤ) at h
    push_cast at h
    omega
  have hlo : 0 ≤ ∑ k, if ω k then ds k i else (0 : ℤ) := by
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact (hdi k).1
    · exact le_rfl
  have hhi : (∑ k, if ω k then ds k i else (0 : ℤ)) ≤ (j : ℤ) * m := by
    calc
      _ ≤ ∑ _k : Fin j, (m : ℤ) := by
        apply Finset.sum_le_sum
        intro k hk
        split_ifs
        · exact (hdi k).2
        · exact Int.natCast_nonneg _
      _ = _ := by simp
  have hm : ((j : ℤ) + 1) * (m : ℤ) < T i := by
    have hmul := Nat.mul_div_le (T i - 1) (j + 1)
    have hT := Nat.pos_of_ne_zero (NeZero.ne (T i))
    have hlt : (j + 1) * m < T i := hmul.trans_lt (Nat.sub_lt hT (by omega))
    exact_mod_cast hlt
  simp only [Pi.add_apply, cubeShift, Finset.sum_apply, ite_apply, Pi.zero_apply]
  constructor <;> nlinarith [hxi.1, hxi.2]

noncomputable def smallBoxCubeMap (j : ℕ) :
    ((Fin j → integerBox (smallCubeSide T j)) × integerBox (smallCubeSide T j)) →
      SupportedCube j (integerBox T : Set (ι → ℤ)) :=
  fun p ↦ ⟨(fun k ↦ (p.1 k).val, p.2.val),
    small_increments_supported T j p.2.val p.2.property
      (fun k ↦ (p.1 k).val) (fun k ↦ (p.1 k).property)⟩

theorem smallBoxCubeMap_injective (j : ℕ) : Function.Injective (smallBoxCubeMap T j) := by
  intro p q he
  apply Prod.ext
  · funext k
    apply Subtype.ext
    exact congrArg (fun r ↦ r.val.1 k) he
  · apply Subtype.ext
    exact congrArg (fun r ↦ r.val.2) he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDifferenceHom
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteBoxCorrelation_re_eq_mean_square {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℂ) :
    (finiteBoxCorrelation F).re = 𝔼 x, 𝔼 x', ‖𝔼 y, F x y * star (F x' y)‖ ^ 2 := by
  unfold finiteBoxCorrelation
  simp_rw [square_norm_mean_eq_cross_re, ← expect_re]
  congr 1
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro x' _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro y' _
  simp only [star_mul, star_star]
  ring

theorem norm_weighted_expect_sq_le {X : Type*} [Fintype X] [Nonempty X]
    (a f : X → ℂ) (ha : ∀ x, ‖a x‖ ≤ 1) :
    ‖𝔼 x, a x * f x‖ ^ 2 ≤ 𝔼 x, ‖f x‖ ^ 2 := by
  have hcs := norm_expect_mul_star_sq_le a (fun x => star (f x))
  simp only [star_star, norm_star] at hcs
  have ha2 : (𝔼 x, ‖a x‖ ^ 2) ≤ 1 := by
    exact (Finset.expect_le_expect (fun x _ =>
      pow_le_pow_left₀ (norm_nonneg _) (ha x) 2)).trans_eq (by simp)
  exact hcs.trans ((mul_le_mul_of_nonneg_right ha2
    (Finset.expect_nonneg (fun _ _ => sq_nonneg _))).trans_eq (one_mul _))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boxSliceEquiv (X : Type*) : ((Fin 2 → X) × (Fin 2 → X)) ≃ (Fin 4 → X) where
  toFun p := boxSlice p.1 p.2
  invFun x := (![x 1, x 3], ![x 0, x 2])
  left_inv p := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

theorem expect_boxSlice {X M : Type*} [Fintype X] [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (Fin 4 → X) → M) :
    (𝔼 x, F x) = 𝔼 a : Fin 2 → X, 𝔼 z : Fin 2 → X, F (boxSlice a z) := by
  calc
    _ = 𝔼 p : (Fin 2 → X) × (Fin 2 → X), F (boxSlice p.1 p.2) :=
      (Fintype.expect_equiv (boxSliceEquiv X) _ F (fun _ => rfl)).symm
    _ = _ := by
      simpa using (Finset.expect_product' Finset.univ Finset.univ
        (fun a z => F (boxSlice a z)))

theorem boxKernel_slice {X : Type*} (K : X → X → ℂ) (a z : Fin 2 → X) :
    boxKernel K (boxSlice a z) = K (z 0) (z 1) * boxAnchorFactor K a z := by
  simp [boxKernel, boxSlice, boxAnchorFactor, mul_assoc]

theorem boxKernel_mean {X : Type*} [Fintype X] (K : X → X → ℂ) :
    (𝔼 x : Fin 4 → X, boxKernel K x) = finiteBoxCorrelation K := by
  simp_rw [expect_fin_cons]
  unfold finiteBoxCorrelation
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro b _
  change (𝔼 _ : Fin 0 → X, K x y * star (K a y) * star (K x b) * K a b) = _
  rw [Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_box_anchor_correlation {X : Type*} [Fintype X] [Nonempty X]
    (K : X → X → ℂ) :
    ∃ a : Fin 2 → X, (finiteBoxCorrelation K).re ≤
      ‖𝔼 z : Fin 2 → X, K (z 0) (z 1) * boxAnchorFactor K a z‖ := by
  have hmean : (finiteBoxCorrelation K).re =
      𝔼 a : Fin 2 → X, (𝔼 z : Fin 2 → X,
        K (z 0) (z 1) * boxAnchorFactor K a z).re := by
    rw [← boxKernel_mean, expect_boxSlice, expect_re]
    simp_rw [boxKernel_slice]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.le
  exact ⟨a, ha.trans (Complex.re_le_norm _)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteArrayMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finiteArrayTranspose_measurePreserving {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : I → J → Measure X) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (finiteArrayTranspose I J X)
      (Measure.pi (fun i => Measure.pi (μ i))) (Measure.pi (fun j => Measure.pi (fun i => μ i j))) := by
  have h₁ := finiteArray_uncurry_measurePreserving μ
  have h₂ := measurePreserving_piCongrLeft (fun ji : J × I => μ ji.2 ji.1) (Equiv.prodComm I J)
  have h₃ := (finiteArray_uncurry_measurePreserving (fun j i => μ i j)).symm
    (MeasurableEquiv.curry J I X).symm
  exact h₃.comp (h₂.comp h₁)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem profileWidthFactor_le {I : Type*} [Fintype I] (w : I → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hw : ∀ i, δ ≤ w i) :
    profileWidthFactor w ≤ δ⁻¹ ^ Fintype.card I := by
  calc
    _ ≤ ∏ _i : I, δ⁻¹ := Finset.prod_le_prod
      (fun i _ => inv_nonneg.mpr (hδ.le.trans (hw i))) (fun i _ => inv_anti₀ hδ (hw i))
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

theorem integerMassTent_grid (K : ℝ) (hK : 0 < K) (a k : ℤ) :
    integerMassTent K a ((k : ℝ) / K) = K * ((PMF.pure a) k).toReal := by
  classical
  unfold integerMassTent
  rw [mul_div_cancel₀ _ hK.ne']
  by_cases h : k = a
  · subst k
    simp
  · have hn : (1 : ℤ) ≤ |k-a| := Int.one_le_abs (sub_ne_zero.mpr h)
    have hn' : (1 : ℝ) ≤ |(k : ℝ) - a| := by exact_mod_cast hn
    have hz : max 0 (1 - 2 * |(k : ℝ) - a|) = 0 := max_eq_left (by linarith)
    simp [hz, h]

theorem integerMassTent_range (K : ℝ) (hK : 0 ≤ K) (a : ℤ) (x : ℝ) :
    0 ≤ integerMassTent K a x ∧ integerMassTent K a x ≤ K := by
  refine ⟨mul_nonneg hK (le_max_left _ _), ?_⟩
  have ht : max 0 (1 - 2 * |K*x-a|) ≤ (1 : ℝ) :=
    max_le (by norm_num) (by linarith [abs_nonneg (K*x-a)])
  exact (mul_le_mul_of_nonneg_left ht hK).trans_eq (mul_one K)

theorem integerMassTent_difference (K : ℝ) (hK : 0 ≤ K) (a : ℤ) (x y : ℝ) :
    |integerMassTent K a x - integerMassTent K a y| ≤ (2 * K ^ 2) * |x-y| := by
  have hm : |max 0 (1 - 2 * |K*x-a|) - max 0 (1 - 2 * |K*y-a|)| ≤
      |(1 - 2 * |K*x-a|) - (1 - 2 * |K*y-a|)| := by
    simpa only [max_comm] using abs_max_sub_max_le_abs (1 - 2 * |K*x-a|) (1 - 2 * |K*y-a|) (0 : ℝ)
  have ha := abs_abs_sub_abs_le_abs_sub (K*x-a) (K*y-a)
  rw [sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_nonneg hK] at ha
  have he : (1 - 2 * |K*x-a|) - (1 - 2 * |K*y-a|) =
      -(2 * (|K*x-a| - |K*y-a|)) := by ring
  rw [he, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hm
  unfold integerMassTent
  rw [← mul_sub, abs_mul, abs_of_nonneg hK]
  calc
    _ ≤ K * (2 * abs (|K*x-a| - |K*y-a|)) := mul_le_mul_of_nonneg_left hm hK
    _ ≤ K * (2 * (K * |x-y|)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ha (by norm_num)) hK
    _ = _ := by ring

theorem integerMassTent_spec (K : ℝ) (hK : 0 < K) (a : ℤ) :
    IsIntegerMassInterpolation K (PMF.pure a) K (2 * K ^ 2) (integerMassTent K a) :=
  ⟨integerMassTent_grid K hK a, integerMassTent_range K hK.le a, integerMassTent_difference K hK.le a⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteInnerProgressionFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem piFinset_inner_card_loss {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} (A B : ∀ i, Finset (X i))
    (hB : ∀ i, (B i).Nonempty) (hsub : ∀ i, A i ⊆ B i) :
    1 - ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card ≤
      ∑ i, (1 - ((A i).card : ℝ) / (B i).card) := by
  let r : I → ℝ := fun i => ((A i).card : ℝ) / (B i).card
  have hr (i : I) : r i ∈ Set.Icc (0 : ℝ) 1 := by
    have hpos : (0 : ℝ) < (B i).card := by exact_mod_cast (hB i).card_pos
    refine ⟨div_nonneg (Nat.cast_nonneg _) hpos.le, ?_⟩
    exact (div_le_one hpos).mpr (by exact_mod_cast Finset.card_le_card (hsub i))
  have hprod := one_sub_sum_le_positive_prod Finset.univ r (fun i => 1 - r i)
    (fun i _ => (hr i).1) (fun i _ => ⟨by linarith [(hr i).2], by linarith [(hr i).1]⟩)
    (fun i _ => by linarith)
  have he : ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card = ∏ i, r i := by
    simp only [Fintype.card_piFinset, Nat.cast_prod, Finset.prod_div_distrib, r]
  rw [he]
  change 1 - ∏ i, r i ≤ ∑ i, (1 - r i)
  linarith

theorem piFinset_inner_normalized_loss {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} (A B : ∀ i, Finset (X i))
    (hB : ∀ i, (B i).Nonempty) (hsub : ∀ i, A i ⊆ B i) (ε : I → ℝ)
    (hloss : ∀ i, 2 * (1 - ((A i).card : ℝ) / (B i).card) ≤ ε i) :
    2 * (1 - ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card) ≤ ∑ i, ε i := by
  calc
    _ ≤ 2 * ∑ i, (1 - ((A i).card : ℝ) / (B i).card) :=
      mul_le_mul_of_nonneg_left (piFinset_inner_card_loss A B hB hsub) (by norm_num)
    _ = ∑ i, 2 * (1 - ((A i).card : ℝ) / (B i).card) := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hloss i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedBlockSupportScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem blockJetScaleBound_nonneg (q h b : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ blockJetScaleBound q h b A := by unfold blockJetScaleBound; positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem scalarCubePrimitiveEnvelope_nonneg (I : Type*) [Fintype I]
    (A B T : ℝ≥0) (M : ℕ) : 0 ≤ scalarCubePrimitiveEnvelope I A B T M := by
  unfold scalarCubePrimitiveEnvelope scalarCubeGridBoundaryConstant
    scalarCubeCutoffDerivativeNumerator paddedResidueDensityCap scalarCubeResidueDensityCap
  positivity

theorem paddedResidueDensityCap_scale (I : Type*) [Fintype I] (M : ℕ) :
    paddedResidueDensityCap I M =
      paddedResidueDensityCap I 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
  simp only [paddedResidueDensityCap, scalarCubeResidueDensityCap, Nat.cast_one, mul_one, mul_pow]
  ring

theorem scalarCubePrimitiveEnvelope_split (I : Type*) [Fintype I]
    (A B T : ℝ≥0) (M : ℕ) :
    scalarCubePrimitiveEnvelope I A B T M =
      scalarCubePrimitiveEnvelope I A B T 0 + M + paddedResidueDensityCap I M := by
  simp only [scalarCubePrimitiveEnvelope, paddedResidueDensityCap, scalarCubeResidueDensityCap,
    Nat.cast_zero, mul_zero, zero_pow (Nat.succ_ne_zero _), add_zero]
  ring

theorem scalarCubePrimitiveEnvelope_le_scaled (I : Type*) [Fintype I]
    (A B T : ℝ≥0) {M : ℕ} (hM : 1 ≤ M) :
    scalarCubePrimitiveEnvelope I A B T M ≤
      scalarCubePrimitiveEnvelope I A B T 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpow : (1 : ℝ) ≤ (M : ℝ) ^ (Fintype.card I + 1) := one_le_pow₀ hM'
  have hMp : (M : ℝ) ≤ (M : ℝ) ^ (Fintype.card I + 1) := by
    calc
      _ = 1 * (M : ℝ) := (one_mul _).symm
      _ ≤ (M : ℝ) ^ Fintype.card I * M :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hM') (Nat.cast_nonneg _)
      _ = _ := (pow_succ _ _).symm
  have hzero := scalarCubePrimitiveEnvelope_nonneg I A B T 0
  have hc : scalarCubePrimitiveEnvelope I A B T 0 ≤
      scalarCubePrimitiveEnvelope I A B T 0 * (M : ℝ) ^ (Fintype.card I + 1) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hzero
  calc
    _ = scalarCubePrimitiveEnvelope I A B T 0 + M +
        paddedResidueDensityCap I 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
      rw [scalarCubePrimitiveEnvelope_split I A B T M, paddedResidueDensityCap_scale]
    _ ≤ scalarCubePrimitiveEnvelope I A B T 0 * (M : ℝ) ^ (Fintype.card I + 1) +
        (M : ℝ) ^ (Fintype.card I + 1) +
        paddedResidueDensityCap I 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
      gcongr
    _ = _ := by rw [scalarCubePrimitiveEnvelope_split I A B T 1]; push_cast; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ShortIntegerCubeBudget
namespace OAI

section

namespace Erdos3

theorem natCeil_le_exp_succ {x P : ℝ} (hx : 0 ≤ x) (hP : 0 ≤ P)
    (h : x ≤ Real.exp P) : (⌈x⌉₊ : ℝ) ≤ Real.exp (P+1) := by
  apply (Nat.ceil_lt_add_one hx).le.trans
  simpa only [add_comm x 1] using one_add_le_exp_succ hP h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedCoefficientCounting
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem integerCoordinate_count {J : Type*} [Fintype J] :
    Measure.pi (fun _ : J => (Measure.count : Measure ℤ)) = (Measure.count : Measure (J → ℤ)) := by
  apply Measure.ext_of_singleton
  intro z
  simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mixedArrayRegroup_measurePreserving {I Z J : Type*}
    [Fintype I] [Fintype Z] [Fintype J]
    (μ : I → J → Measure ℝ) (ν : Z → J → Measure ℤ)
    [∀ i j, SigmaFinite (μ i j)] [∀ z j, SigmaFinite (ν z j)] :
    MeasurePreserving (mixedArrayRegroup I Z J)
      ((Measure.pi (fun i => Measure.pi (μ i))).prod (Measure.pi (fun z => Measure.pi (ν z))))
      (Measure.pi (fun j => (Measure.pi (fun i => μ i j)).prod (Measure.pi (fun z => ν z j)))) := by
  have h₁ := (finiteArrayTranspose_measurePreserving μ).prod (finiteArrayTranspose_measurePreserving ν)
  have h₂ := (measurePreserving_arrowProdEquivProdArrow (I → ℝ) (Z → ℤ) J
    (fun j => Measure.pi (fun i => μ i j)) (fun j => Measure.pi (fun z => ν z j))).symm
      (MeasurableEquiv.arrowProdEquivProdArrow (I → ℝ) (Z → ℤ) J)
  exact h₂.comp h₁

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeSheetHaar
namespace OAI

section

namespace Erdos3

open MeasureTheory Module

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_quotient_scaled_haar (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] :
    ENNReal.ofReal (ZLattice.covolume Λ) • μ =
      Measure.map (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup)
        (volume.restrict (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ))) := by
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)
  let : Countable Λ.toAddSubgroup := b.repr.injective.countable
  let : Countable Λ.toAddSubgroup.op := Λ.toAddSubgroup.equivOp.symm.injective.countable
  have hF : IsAddFundamentalDomain Λ.toAddSubgroup F volume :=
    ZLattice.isAddFundamentalDomain b volume
  have hop := additiveFundamentalDomain_op Λ.toAddSubgroup hF
  let : HasAddFundamentalDomain Λ.toAddSubgroup.op E volume := ⟨F, hop⟩
  have hclosed : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  let : IsClosed (Λ.toAddSubgroup : Set E) := hclosed
  let c := ENNReal.ofReal (ZLattice.covolume Λ)
  let : IsFiniteMeasure (c • μ) := μ.smul_finite ENNReal.ofReal_ne_top
  have hscale : addCovolume Λ.toAddSubgroup.op E volume = (c • μ) Set.univ := by
    rw [hop.covolume_eq_volume volume, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact lattice_fundamentalDomain_volume Λ b
  let : AddQuotientMeasureEqMeasurePreimage volume (c • μ) :=
    leftInvariantIsAddQuotientMeasureEqMeasurePreimage (ν := volume) hscale
  exact hop.addProjection_respects_measure (c • μ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module _root_.Set

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

theorem lattice_quotient_haar_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
    (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {A : Set E} (hAm : MeasurableSet A)
    (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) A) :
    μ ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) '' A) =
      volume A / ENNReal.ofReal (ZLattice.covolume Λ) := by
  let : Countable Λ.toAddSubgroup := b.repr.injective.countable
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  have hq : Continuous (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) :=
    continuous_quotient_mk'
  have him := hAm.image_of_continuousOn_injOn hq.continuousOn hA
  have he := congrArg
    (fun ν : Measure (E ⧸ Λ.toAddSubgroup) => ν
      ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) '' A))
    (lattice_quotient_scaled_haar Λ b μ)
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hq.measurable him,
    Measure.restrict_apply (him.preimage hq.measurable)] at he
  rw [quotient_injective_lift_measure Λ.toAddSubgroup volume
    (ZLattice.isAddFundamentalDomain b volume)
    (ZSpan.fundamentalDomain_measurableSet _) hAm hA] at he
  exact (ENNReal.eq_div_iff (ENNReal.ofReal_pos.mpr (ZLattice.covolume_pos Λ volume)).ne'
    ENNReal.ofReal_ne_top).mpr he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem sum_le_exp_of_card_and_uniform_bound {I : Type*} [Fintype I]
    (f : I → ℝ) {P Q : ℝ} (hQ : 0 ≤ Q) (hcard : (Fintype.card I : ℝ) ≤ P)
    (hf : ∀ i, f i ≤ Real.exp Q) : (∑ i, f i) ≤ Real.exp (P + P * Q) := by
  have h := sum_le_exp_card_add_sum f (fun _ => Q) (fun _ => hQ) hf
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact h.trans (Real.exp_le_exp.mpr (add_le_add hcard (mul_le_mul_of_nonneg_right hcard hQ)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PositiveIntegerPeriodization
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

theorem positiveIntegerPeriodization_lipschitz (H : (D → ℝ) → ℝ) {L : ℝ≥0}
    (hH : LipschitzWith L H) (h0 : ∀ x, 0 ≤ H x)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith L (positiveIntegerPeriodization H) := by
  apply separated_tsum_lipschitz
  · intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hH.dist_le_mul (x + fun i => (n i : ℝ)) (y + fun i => (n i : ℝ))
    rw [dist_add_right] at h
    exact h
  · intro n x
    exact h0 _
  · intro x n m hn hm
    exact integer_shifts_small_box_injective x n m (hs _ hn) (hs _ hm)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmallBoxCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

theorem smallBoxCutoff_range (x : D → ℝ) :
    0 ≤ smallBoxCutoff x ∧ smallBoxCutoff x ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem smallBoxCutoff_one (x : D → ℝ) (hx : ∀ i, |x i| ≤ 1/4) :
    smallBoxCutoff x = 1 := by
  have hn : ‖x‖ ≤ 1/4 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    (by simpa only [Real.norm_eq_abs] using hx)
  rw [smallBoxCutoff, min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem smallBoxCutoff_zero (x : D → ℝ) (hx : 3/8 ≤ ‖x‖) :
    smallBoxCutoff x = 0 := by
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem smallBoxCutoff_support (x : D → ℝ) (hx : smallBoxCutoff x ≠ 0) :
    ∀ i, |x i| < 1/2 := by
  have hn : ‖x‖ < 3/8 := lt_of_not_ge (fun h => hx (smallBoxCutoff_zero x h))
  intro i
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  linarith

theorem smallBoxCutoff_lipschitz : LipschitzWith 8 (smallBoxCutoff (D := D)) := by
  have h : LipschitzWith 8 (fun x : D → ℝ => 3 - 8 * ‖x‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have he : (3 - 8 * ‖x‖) - (3 - 8 * ‖y‖) = -8 * (‖x‖ - ‖y‖) := by ring
    rw [he, abs_mul]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8), NNReal.coe_ofNat]
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y)
      (by norm_num)
  exact (h.const_min 1).const_max 0

theorem smallBoxCutoff_mul_lipschitz (f : (D → ℝ) → ℝ) {L B : ℝ≥0}
    (hf : LipschitzWith L f) (hb : ∀ x, |f x| ≤ B) :
    LipschitzWith (L + B * 8) (fun x => smallBoxCutoff x * f x) := by
  simpa only [one_mul] using lipschitz_real_mul_of_bounds (Bf := 1) (Bg := B) smallBoxCutoff f
    smallBoxCutoff_lipschitz hf
    (fun x => by rw [abs_of_nonneg (smallBoxCutoff_range x).1]; exact (smallBoxCutoff_range x).2) hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerPeriodicTorusLift
namespace OAI

section

namespace Erdos3

variable {ι : Type*}

theorem integerPeriodicTorusLift_coe (F : (ι → ℝ) → ℂ)
    (hF : ∀ (x : ι → ℝ) (n : ι → ℤ), F (fun i => x i + (n i : ℝ)) = F x)
    (x : ι → ℝ) : integerPeriodicTorusLift F (fun i => (x i : UnitAddCircle)) = F x := by
  classical
  let y : ι → ℝ := fun i => (AddCircle.equivIoc 1 0 (x i : UnitAddCircle)).val
  have hzero (i : ι) : (((y i - x i : ℝ) : UnitAddCircle)) = 0 := by
    simp [y]
  choose n hn using fun i => (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp (hzero i)
  have hy : y = fun i => x i + (n i : ℝ) := by
    funext i
    have hi : (n i : ℝ) = y i - x i := by simpa only [zsmul_eq_mul, mul_one] using hn i
    linarith
  change F y = F x
  rw [hy, hF]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension
namespace OAI

section

namespace Erdos3

open Module

theorem coe_centeredCircleLift (z : AddCircle (1 : ℝ)) :
    (centeredCircleLift z : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco

end Erdos3

end

section

namespace Erdos3

theorem centeredCircleLift_abs_le_half (z : AddCircle (1 : ℝ)) :
    |centeredCircleLift z| ≤ 1 / 2 := by
  have h := (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) z).property
  change -(1 / 2 : ℝ) ≤ centeredCircleLift z ∧ centeredCircleLift z < -(1 / 2) + 1 at h
  exact abs_le.mpr ⟨h.1, by linarith [h.2]⟩

theorem norm_eq_abs_centeredCircleLift (z : AddCircle (1 : ℝ)) :
    ‖z‖ = |centeredCircleLift z| := by
  calc
    ‖z‖ = ‖(centeredCircleLift z : AddCircle (1 : ℝ))‖ :=
      congrArg norm (coe_centeredCircleLift z).symm
    _ = _ := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num : (1 : ℝ) ≠ 0)).mpr
      (by simpa only [abs_one] using centeredCircleLift_abs_le_half z)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {D : Type*} [Fintype D]

omit [Fintype D] in
theorem realPeriodicTorusLift_coe (F : (D → ℝ) → ℝ)
    (hF : ∀ (x : D → ℝ) (n : D → ℤ), F (fun i => x i + (n i : ℝ)) = F x) (x : D → ℝ) :
    realPeriodicTorusLift F (fun i => (x i : UnitAddCircle)) = F x := by
  unfold realPeriodicTorusLift
  rw [integerPeriodicTorusLift_coe _ (fun x n => congrArg Complex.ofReal (hF x n))]
  rfl

theorem realPeriodicTorusLift_lipschitz (F : (D → ℝ) → ℝ) {L : ℝ≥0}
    (hL : LipschitzWith L F)
    (hF : ∀ (x : D → ℝ) (n : D → ℤ), F (fun i => x i + (n i : ℝ)) = F x) :
    LipschitzWith L (realPeriodicTorusLift F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let a : D → ℝ := fun i => centeredCircleLift (x i)
  let b : D → ℝ := fun i => a i + centeredCircleLift (y i - x i)
  have ha : (fun i => (a i : UnitAddCircle)) = x := funext (fun i => coe_centeredCircleLift _)
  have hb : (fun i => (b i : UnitAddCircle)) = y := by
    funext i
    change ((a i + centeredCircleLift (y i - x i) : ℝ) : UnitAddCircle) = y i
    rw [AddCircle.coe_add, coe_centeredCircleLift, coe_centeredCircleLift]
    change x i + (y i - x i) = y i
    abel
  have hd : dist a b ≤ dist x y := by
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    change dist (a i) (a i + centeredCircleLift (y i - x i)) ≤ dist x y
    rw [Real.dist_eq, sub_add_cancel_left, abs_neg, ← norm_eq_abs_centeredCircleLift, ← dist_eq_norm]
    exact (dist_le_pi_dist y x i).trans_eq (dist_comm y x)
  have heA : realPeriodicTorusLift F x = F a := by
    rw [← ha]
    exact realPeriodicTorusLift_coe F hF a
  have heB : realPeriodicTorusLift F y = F b := by
    rw [← hb]
    exact realPeriodicTorusLift_coe F hF b
  rw [heA, heB]
  exact (hL.dist_le_mul a b).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)

omit [Fintype D] in
theorem realPeriodicTorusLift_range (F : (D → ℝ) → ℝ) {B : ℝ}
    (hB : ∀ x, 0 ≤ F x ∧ F x ≤ B) (x : D → UnitAddCircle) :
    0 ≤ realPeriodicTorusLift F x ∧ realPeriodicTorusLift F x ≤ B := by
  exact hB _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CanonicalDensityFourier
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D]

noncomputable def smallBoxTorusKernel (H : (D → ℝ) → ℝ) : (D → UnitAddCircle) → ℝ :=
  realPeriodicTorusLift (positiveIntegerPeriodization H)

theorem smallBoxTorusKernel_lipschitz (H : (D → ℝ) → ℝ) {L : ℝ≥0}
    (hL : LipschitzWith L H) (h0 : ∀ x, 0 ≤ H x)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith L (smallBoxTorusKernel H) :=
  realPeriodicTorusLift_lipschitz _ (positiveIntegerPeriodization_lipschitz H hL h0 hs)
    (positiveIntegerPeriodization_periodic H)

omit [Fintype D] in
theorem smallBoxTorusKernel_range (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, 0 ≤ H x ∧ H x ≤ B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → UnitAddCircle) :
    0 ≤ smallBoxTorusKernel H x ∧ smallBoxTorusKernel H x ≤ B :=
  realPeriodicTorusLift_range _ (positiveIntegerPeriodization_range H hB hH hs) x

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem exists_coordinate_integer_translate (u v : EuclideanSpace ℝ D)
    (hv : u - v ∈ standardEuclideanLattice D) :
    ∃ z : D → ℤ, (fun i => v i) = fun i => u i + (z i : ℝ) := by
  choose z hz using (mem_standardEuclideanLattice D _).mp hv
  refine ⟨fun i => -z i, ?_⟩
  funext i
  have hi : (z i : ℝ) = u i - v i := hz i
  push_cast
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedAmbientLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem ambientInterpolation_constants_exp_bounds (n : ℕ) {M J C V : ℝ≥0} {P Q : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hn : (n : ℝ) ≤ P)
    (hM : (M : ℝ) ≤ Real.exp Q) (hJ : (J : ℝ) ≤ Real.exp Q)
    (hC : (C : ℝ) ≤ Real.exp P) (hV : (V : ℝ) ≤ Real.exp P) :
    ((V*M : ℝ≥0) : ℝ) ≤ Real.exp (Q+P) ∧
      ((V*(J*(C*n))+(V*M)*8 : ℝ≥0) : ℝ) ≤ Real.exp (2*Q+4*P+9) := by
  have hnE : (n : ℝ) ≤ Real.exp P := hn.trans (by linarith [Real.add_one_le_exp P])
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  constructor
  · simp only [NNReal.coe_mul]
    calc
      _ ≤ Real.exp P * Real.exp Q := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  · simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat]
    have hfirst : (V : ℝ) * (J * (C * n)) ≤ Real.exp (Q+3*P) := by
      calc
        _ ≤ Real.exp P * (Real.exp Q * (Real.exp P * Real.exp P)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsecond : ((V : ℝ)*M)*8 ≤ Real.exp (Q+P+8) := by
      calc
        _ ≤ (Real.exp P * Real.exp Q) * Real.exp 8 := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    exact (add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond).trans_eq
      (congrArg Real.exp (by ring))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem spatialWidthFraction_inv_le {P τ : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτP : τ⁻¹ ≤ Real.exp P) : 1/spatialWidthFraction P τ ≤ Real.exp (spatialSamplingBudget P) := by
  have h1 : 1 ≤ Real.exp (2*P) := Real.one_le_exp_iff.mpr (by positivity)
  have h16 : (16 : ℝ) ≤ Real.exp 128 := by linarith [Real.add_one_le_exp (128 : ℝ)]
  calc
    _ = (8*(1+Real.exp (2*P)))*τ⁻¹ := by unfold spatialWidthFraction; field_simp
    _ ≤ (16*Real.exp (2*P))*Real.exp P :=
      mul_le_mul (by nlinarith) hτP (inv_nonneg.mpr hτ.le) (by positivity)
    _ = 16*Real.exp (3*P) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp 128 * Real.exp (3*P) := mul_le_mul_of_nonneg_right h16 (by positivity)
    _ = Real.exp (128+3*P) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by unfold spatialSamplingBudget; linarith)

theorem spatialWidthFraction_mul_le_width {K X : Type*} (P : ℝ) {τ : ℝ}
    (hτ1 : τ ≤ 1) (N : X → ℕ) (z : Option K × X) :
    spatialWidthFraction P τ * (N z.2 : ℝ) ≤
      centeredSpatialWidths (Real.exp (2*P)) τ N z := by
  have hfrac : spatialWidthFraction P τ ≤ 1/8 := by
    unfold spatialWidthFraction
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8*(1+Real.exp (2*P)))).mpr
    nlinarith [Real.exp_pos (2*P)]
  rcases z with ⟨k,i⟩
  cases k with
  | none =>
    change spatialWidthFraction P τ * (N i : ℝ) ≤ (N i : ℝ)/8
    exact (mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg _)).trans_eq (by ring)
  | some k =>
    dsimp only [spatialWidthFraction, centeredSpatialWidths]
    apply le_of_eq
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem spatialWidthFraction_le_trimmed_width {K I : Type*} (P : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (N : I → ℕ) (z : Option K × I) :
    spatialWidthFraction P τ * (N z.2 : ℝ) ≤ trimmedSpatialWidths (Real.exp (2*P)) τ N z := by
  have h := mul_le_mul_of_nonneg_left
    (spatialWidthFraction_mul_le_width (K := K) P (by norm_num : (1 : ℝ) ≤ 1) N z) hτ
  have he : spatialWidthFraction P τ = τ * spatialWidthFraction P 1 := by
    unfold spatialWidthFraction
    ring
  rw [he, mul_assoc]
  exact h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

noncomputable def unconditionedSpatialWidthCutoff (B τ L : ℝ) : ℝ :=
  max (4 / τ) (8 * (1 + B) * max (8 * (probabilityProfileLipschitz : ℝ)) L / τ)

theorem unconditionedSpatialTrimFraction_bounds (d : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    0 < unconditionedSpatialTrimFraction d σ ∧
      unconditionedSpatialTrimFraction d σ ≤ 1/2 ∧
      2 * (d : ℝ) * unconditionedSpatialTrimFraction d σ ≤ σ / 8 := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hden : 0 < 32 * ((d : ℝ) + 1) := by positivity
  unfold unconditionedSpatialTrimFraction
  refine ⟨div_pos hσ hden, ?_, ?_⟩
  · apply (div_le_iff₀ hden).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PartitionedIdealSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem partitionedIdealRadius_nonneg (α : Type*) [Fintype α] (degree : ℕ) :
    0 ≤ partitionedIdealRadius α degree := by
  unfold partitionedIdealRadius
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalActiveIdealSite
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem partitionedIdealRadius_add_one_le_exp (α : Type*) [Fintype α] (degree : ℕ) :
    partitionedIdealRadius α degree + 1 ≤
      Real.exp (((degree : ℝ) + 1) * (Fintype.card α : ℝ) + 2) := by
  let n : ℝ := Fintype.card α
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ Fintype.card α ≤ Real.exp n := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one, n]
  have hbase : n + 1 ≤ Real.exp n := Real.add_one_le_exp n
  have hmain : (2 : ℝ) ^ Fintype.card α * (n + 1) ^ degree ≤
      Real.exp (((degree : ℝ) + 1) * n) := by
    calc
      _ ≤ Real.exp n * (Real.exp n) ^ degree := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hone : 1 ≤ Real.exp (((degree : ℝ) + 1) * n) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 3 * Real.exp (((degree : ℝ) + 1) * n) := by
      unfold partitionedIdealRadius
      change 1 / 4 + 2 ^ Fintype.card α * (n + 1) ^ degree + 1 ≤ _
      linarith
    _ ≤ Real.exp 2 * Real.exp (((degree : ℝ) + 1) * n) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IdealSiteBoxRadius
namespace OAI

section

namespace Erdos3

noncomputable def idealSiteBoxRadius (α : Type*) [Fintype α] (degree : ℕ) : ℝ :=
  (2 : ℝ) ^ Fintype.card α * (partitionedIdealRadius α degree + 1)

theorem idealSiteBoxRadius_pos (α : Type*) [Fintype α] (degree : ℕ) :
    0 < idealSiteBoxRadius α degree := by
  have h := partitionedIdealRadius_nonneg α degree
  unfold idealSiteBoxRadius
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.IdealSiteEnvelopeBudget
namespace OAI

section

namespace Erdos3

noncomputable def idealSiteEnvelopeRadius (α : Type*) [Fintype α] (degree : ℕ) : ℝ :=
  (2 : ℝ) ^ Fintype.card α * (2 * idealSiteBoxRadius α degree)

theorem idealSiteEnvelopeRadius_pos (α : Type*) [Fintype α] (degree : ℕ) :
    0 < idealSiteEnvelopeRadius α degree := by
  have h := idealSiteBoxRadius_pos α degree
  unfold idealSiteEnvelopeRadius
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

theorem layerKernelIndexBound_le_exp (m : ℕ) {B : ℕ} {p : ℝ}
    (hB : (B : ℝ) ≤ Real.exp p) :
    (layerKernelIndexBound m B : ℝ) ≤ Real.exp ((m*2^(m+1) : ℕ)*p) := by
  unfold layerKernelIndexBound
  rw [Nat.cast_pow, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hB _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalPeriodPrimitiveBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem canonicalPeriod_primitive_bounds {m M period : ℕ} [NeZero period]
    (A : Type*) [Fintype A] (n : Fin m → ℕ) (O Q : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (Q j)] {Pk : ℝ}
    (hM : (M : ℝ) ≤ Real.exp Pk) (hperiod : period ≤ M ^ (m + 1)) :
    let L := ((m + 1 : ℕ) : ℝ) * Pk
    let maskLog := (Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
    let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
    (period : ℝ) ≤ Real.exp L ∧
    (layerKernelIndexBound m M : ℝ) ^ Fintype.card A * coefficientDeckPeriodCap O Q period ≤
      Real.exp maskLog ∧
    (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤
      Real.exp labelLog := by
  intro L maskLog labelLog
  have hp : (period : ℝ) ≤ Real.exp L := by
    calc
      _ ≤ ((M ^ (m + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hperiod
      _ = (M : ℝ) ^ (m + 1) := Nat.cast_pow _ _
      _ ≤ (Real.exp Pk) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hk : (layerKernelIndexBound m M : ℝ) ^ Fintype.card A ≤
      Real.exp ((Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (layerKernelIndexBound_le_exp m hM) _
  have hd := canonicalCoefficientDeckPeriodCap_le_exp O Q hp
  have hleft := periodFunctionLabelCard_le_exp (fun j => Fin (n j)) hp
  have hright := periodFunctionLabelCard_le_exp Q hp
  refine ⟨hp, ?_, ?_⟩
  · calc
      _ ≤ Real.exp ((Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk)) *
          Real.exp (∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)) :=
        mul_le_mul hk hd (coefficientDeckPeriodCap_nonneg O Q period) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  · have hh := mul_le_mul hleft hright (Nat.cast_nonneg
        (Fintype.card (∀ j, Q j → ZMod period))) (Real.exp_nonneg _)
    rw [Fintype.card_prod, Nat.cast_mul]
    simpa only [Nat.card_fin, ← Real.exp_add, labelLog,
      ← Nat.card_eq_fintype_card] using hh

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPeriodPivot
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerPeriod_exists_pivot {O J : Type*} [Fintype O] [DecidableEq O] [Fintype J]
    (A : Matrix O J ℤ) {a : ℤ} (ha : a ≠ 0)
    (hperiod : integerScalarLattice O a ≤ A.mulVecLin.range) :
    ∃ s : O ↪ J, (A.submatrix id s).det ≠ 0 := by
  classical
  have hcol (i : O) : ∃ v : J → ℤ, A *ᵥ v = a • Pi.single i 1 :=
    hperiod ((integerScalarLattice_mem a _).mpr ⟨Pi.single i 1, rfl⟩)
  choose v hv using hcol
  let B : Matrix J O ℤ := fun j i => v i j
  have hAB : A * B = a • (1 : Matrix O O ℤ) := by
    ext i k
    change (A *ᵥ v k) i = (a • (1 : Matrix O O ℤ)) i k
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply,
      Pi.single_apply, eq_comm] using congrFun (hv k) i
  have hdet : (A * B).det ≠ 0 := by
    rw [hAB, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ ha
  rw [rectangular_det_expansion] at hdet
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hminor : (A.submatrix id s).det ≠ 0 := left_ne_zero_of_mul hs
  refine ⟨⟨s, ?_⟩, hminor⟩
  intro i j hij
  by_contra hne
  apply hminor
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.submatrix_apply, hij])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelDensityProjection
namespace OAI


namespace Erdos3

theorem linearIndependent_of_fixed_kernel_period {O K₀ K : Type*}
    [Fintype O] [DecidableEq O] [Fintype K₀]
    (A₀ : Matrix O K₀ ℤ) (A : Matrix O K ℤ) (e : K₀ → K)
    (he : ∀ i k, A i (e k) = A₀ i k) {a : ℤ} (ha : a ≠ 0)
    (hperiod : integerScalarLattice O a ≤ A₀.mulVecLin.range) :
    LinearIndependent ℝ (fun i k => (A i k : ℝ)) := by
  classical
  obtain ⟨s, hs⟩ := integerPeriod_exists_pivot A₀ ha hperiod
  have hdet : ((A₀.submatrix id s).map (fun z => (z : ℝ))).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast hs
  let restrict : (K → ℝ) →ₗ[ℝ] (O → ℝ) :=
    { toFun := fun v j => v (e (s j))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  change LinearIndependent ℝ (fun i j => (A₀ i (s j) : ℝ)) at hrows
  apply LinearIndependent.of_comp restrict
  simpa only [Function.comp_def, restrict, LinearMap.coe_mk, AddHom.coe_mk,
    he] using hrows

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem character_relation_of_quadruple_pos (χ : G → AddChar G ℂ) (a h k : G)
    (hpos : 0 < additiveQuadrupleCorrelation (fun h x => χ h x) a h k) :
    χ (h - a) + χ k = χ h + χ (k - a) := by
  let ψ := χ (h - a) + χ k - χ h - χ (k - a)
  let c := χ (h - a) a * star (χ (k - a) a)
  have hfactor (x : G) :
      star (χ h x) * χ (h - a) (x + a) * χ k x * star (χ (k - a) (x + a)) =
        c * ψ x := by
    simp only [ψ, c, AddChar.sub_apply, AddChar.add_apply, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_conj, Complex.star_def, map_mul]
    ring
  have hmean : (𝔼 x, star (χ h x) * χ (h - a) (x + a) * χ k x *
      star (χ (k - a) (x + a))) = c * (𝔼 x, ψ x) := by
    simp_rw [hfactor]
    exact (Finset.mul_expect _ _ _).symm
  have hψ : ψ = 0 := by
    by_contra hn
    have hz : (𝔼 x, ψ x) = 0 := AddChar.expect_eq_zero_iff_ne_zero.mpr hn
    change 0 < ‖𝔼 x, star (χ h x) * χ (h - a) (x + a) * χ k x *
      star (χ (k - a) (x + a))‖ at hpos
    rw [hmean, hz, mul_zero, norm_zero] at hpos
    exact (lt_irrefl 0) hpos
  apply sub_eq_zero.mp
  calc
    (χ (h - a) + χ k) - (χ h + χ (k - a)) = ψ := by dsimp [ψ]; abel
    _ = 0 := hψ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem mean_norm_le_fourier_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) : (𝔼 x, ‖f x‖) ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ := by
  have hpoint (x : G) : ‖f x‖ ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = ‖∑ χ : AddChar G ℂ, finiteFourierCoeff f χ * χ x‖ := by rw [finiteFourier_inversion]
      _ ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ * χ x‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, AddChar.norm_apply, mul_one]
  exact (Finset.expect_le_expect (fun x _ => hpoint x)).trans_eq (Fintype.expect_const _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeComparisonBasis
namespace OAI

section

namespace Erdos3

theorem preimageBasisBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    preimageBasisBudget p ≤ preimageBasisBudget q := by
  have hq : 0 ≤ q := hp.trans hpq
  unfold preimageBasisBudget sparseGeneratorBudget
  gcongr

theorem fourRefinementBasisBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    fourRefinementBasisBudget p ≤ fourRefinementBasisBudget q :=
  add_le_add hpq (preimageBasisBudget_mono (by positivity)
    (mul_le_mul_of_nonneg_left hpq (by norm_num)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairComparison
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem productNiltestBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    productNiltestBudget p ≤ productNiltestBudget q := by
  unfold productNiltestBudget productObservableLipBudget
  gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedDensityProjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem trimmedSpatialWidths_antitone_budget {K X : Type*} {W W' τ : ℝ}
    (hW : 0 ≤ W) (hWW' : W ≤ W') (hτ : 0 ≤ τ) (N : X → ℕ)
    (z : Option K × X) :
    trimmedSpatialWidths W' τ N z ≤ trimmedSpatialWidths W τ N z := by
  rcases z with ⟨k, i⟩
  cases k with
  | none => exact le_rfl
  | some k =>
    dsimp only [trimmedSpatialWidths, centeredSpatialWidths]
    gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCyclicEncoding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boxIntegerCode_bounds {n : ℕ} (T : Fin n → ℕ) (x : Fin n → ℤ)
    (hx : x ∈ integerBox T) :
    0 ≤ boxIntegerCode T x ∧ boxIntegerCode T x < (boxCodeModulus T : ℤ) := by
  apply integerRadixValue_bounds
  intro i
  have h := (mem_integerBox T x).mp hx i
  constructor
  · exact h.1
  · push_cast
    omega

theorem boxCyclicCode_reflectsPairSums {n : ℕ} (T : Fin n → ℕ) :
    ReflectsPairSums (boxCyclicCode T) (integerBox T : Set (Fin n → ℤ)) := by
  intro a ha b hb c hc d hd he
  have hab : ∀ i, 0 ≤ (a + b) i ∧ (a + b) i < ((4 * T i : ℕ) : ℤ) := by
    intro i
    have h1 := (mem_integerBox T a).mp ha i
    have h2 := (mem_integerBox T b).mp hb i
    simp only [Pi.add_apply, Nat.cast_mul, Nat.cast_ofNat]
    constructor <;> omega
  have hcd : ∀ i, 0 ≤ (c + d) i ∧ (c + d) i < ((4 * T i : ℕ) : ℤ) := by
    intro i
    have h1 := (mem_integerBox T c).mp hc i
    have h2 := (mem_integerBox T d).mp hd i
    simp only [Pi.add_apply, Nat.cast_mul, Nat.cast_ofNat]
    constructor <;> omega
  have he' : ((boxIntegerCode T (a + b) : ℤ) : ZMod (boxCodeModulus T)) =
      ((boxIntegerCode T (c + d) : ℤ) : ZMod (boxCodeModulus T)) := by
    change ((boxIntegerCode T a : ℤ) : ZMod (boxCodeModulus T)) +
      ((boxIntegerCode T b : ℤ) : ZMod (boxCodeModulus T)) =
      ((boxIntegerCode T c : ℤ) : ZMod (boxCodeModulus T)) +
      ((boxIntegerCode T d : ℤ) : ZMod (boxCodeModulus T)) at he
    simpa only [map_add, Int.cast_add] using he
  have hh := int_eq_of_zmod_eq_of_bounds
    (integerRadixValue_bounds (fun i => 4 * T i) (a + b) hab)
    (integerRadixValue_bounds (fun i => 4 * T i) (c + d) hcd) he'
  exact integerRadixValue_injective_on_digits (fun i => 4 * T i) (a + b) (c + d) hab hcd hh

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialTupleErrorBudget
namespace OAI

section

namespace Erdos3

theorem spatialTupleTolerance_inv_bound (n : ℕ) {G V ε P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hε : 0 < ε) (hP : 0 ≤ P)
    (hn : (n : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    (spatialTupleTolerance n G V ε)⁻¹ ≤ Real.exp (spatialTupleToleranceLog P) := by
  have hone : 1 ≤ Real.exp P := Real.one_le_exp hP
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hbase : 2 + G ≤ Real.exp (P + 2) := by
    calc
      _ ≤ 3 * Real.exp P := by linarith
      _ ≤ Real.exp P * Real.exp 2 := by nlinarith [Real.exp_pos P]
      _ = _ := (Real.exp_add _ _).symm
  have hpower := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 + G) hbase
    (by positivity : 0 ≤ P + 2) n hn
  have hn1 : (n : ℝ) + 1 ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have hV1 : 1 + V ≤ Real.exp (P + 1) := one_add_le_exp_succ hP hVP
  have hden : 2 * (n + 1 : ℝ) * (2 + G) ^ n * (1 + V) ≤
      Real.exp (P ^ 2 + 4 * P + 3) := by
    calc
      _ ≤ Real.exp 2 * Real.exp P * Real.exp (P * (P + 2)) * Real.exp (P + 1) := by
        gcongr
        linarith
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  unfold spatialTupleTolerance
  apply inv_min_le_of_inv_le
  · norm_num only [one_div, inv_inv]
    have h := Real.add_one_le_exp (spatialTupleToleranceLog P)
    unfold spatialTupleToleranceLog at *
    nlinarith
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp (P ^ 2 + 4 * P + 3) * Real.exp P := by gcongr
      _ = Real.exp (P ^ 2 + 5 * P + 3) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold spatialTupleToleranceLog; linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

theorem allocatedSiteCoefficientLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedSiteCoefficientLog D := by unfold allocatedSiteCoefficientLog; positivity

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFullSiteRadius
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def allocatedSiteRootAllowance (α : Type*) [Fintype α] (m : ℕ) : ℝ :=
  1 + (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (m + 1) + idealSiteEnvelopeRadius α m

theorem allocatedSiteRootAllowance_one_le (α : Type*) [Fintype α] (m : ℕ) :
    1 ≤ allocatedSiteRootAllowance α m := by
  have h := (idealSiteEnvelopeRadius_pos α m).le
  unfold allocatedSiteRootAllowance
  have hp : 0 ≤ (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (m + 1) := by positivity
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
namespace OAI

section

namespace Erdos3

theorem exists_denseSliceThreshold (c q : ℕ) {δ D v w : ℝ}
    (hδ : 0 < δ) (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hc : (c : ℝ) ≤ D) (hq : (q : ℝ) ≤ Real.exp v) (hδw : δ⁻¹ ≤ Real.exp w) :
    ∃ T : ℕ, (((c + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
      (T : ℝ) ≤ Real.exp (D + v + w + 1) := by
  let T : ℕ := ⌈(((c + 1) * q : ℕ) : ℝ) / δ⌉₊
  have hcp : ((c + 1 : ℕ) : ℝ) ≤ Real.exp D := by
    push_cast
    linarith [Real.add_one_le_exp D]
  have hb : (((c + 1) * q : ℕ) : ℝ) / δ ≤ Real.exp (D + v + w) := by
    rw [Nat.cast_mul, div_eq_mul_inv]
    exact (mul_le_mul (mul_le_mul hcp hq (Nat.cast_nonneg _) (Real.exp_nonneg _))
      hδw (inv_nonneg.mpr hδ.le) (by positivity)).trans_eq (by rw [← Real.exp_add, ← Real.exp_add])
  exact ⟨T, Nat.le_ceil _, natCeil_le_exp_succ (by positivity) (by positivity) hb⟩

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

theorem exists_slicedGridParameters (dim : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {F Q δ : ℝ} {q step : ℕ},
      0 ≤ F → 0 ≤ Q → 0 < δ → δ⁻¹ ≤ Real.exp F → 0 < q →
      (q : ℝ) ≤ Real.exp Q → (step : ℝ) ≤ 4 * Real.exp F →
      ∃ T : ℕ, (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
        (T : ℝ) ≤ Real.exp (dim + Q + F + 1) ∧
        let Pg := Real.exp (C + ((dim + 1 : ℕ) : ℝ) * Q + F + 4)
        1 ≤ Pg ∧ scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Pg ∧ ((step * q : ℕ) : ℝ) ≤ Pg := by
  let fixed := scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 +
    scalarCubePrimitiveEnvelope (Fin dim) A 1 0 1 + 2
  obtain ⟨C₀, hC₀⟩ := exists_nat_ge fixed
  let C := max 2 C₀
  have hC : fixed ≤ (C : ℝ) := hC₀.trans (Nat.cast_le.mpr (le_max_right _ _))
  have hc0 := scalarCubePrimitiveEnvelope_nonneg Empty A 16 (128 * probabilityProfileLipschitz) 1
  have hs0 := scalarCubePrimitiveEnvelope_nonneg (Fin dim) A 1 0 1
  have hc : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ C := by
    dsimp only [fixed] at hC
    linarith
  have hs : scalarCubePrimitiveEnvelope (Fin dim) A 1 0 1 ≤ C := by
    dsimp only [fixed] at hC
    linarith
  refine ⟨C, le_max_left _ _, ?_⟩
  intro F Q δ q step hF hQ hδ hδF hq hqQ hstep
  obtain ⟨T, hT, hTb⟩ := exists_denseSliceThreshold dim q hδ (Nat.cast_nonneg dim)
    hQ hF le_rfl hqQ hδF
  refine ⟨T, hT, hTb, ?_⟩
  let logPg := (C : ℝ) + ((dim + 1 : ℕ) : ℝ) * Q + F + 4
  have hlog : 0 ≤ logPg := by dsimp only [logPg]; positivity
  have hCexp : (C : ℝ) ≤ Real.exp C := by linarith [Real.add_one_le_exp (C : ℝ)]
  have hCLog : (C : ℝ) ≤ logPg := by
    dsimp only [logPg]
    linarith [mul_nonneg (Nat.cast_nonneg (dim + 1) : (0 : ℝ) ≤ ((dim + 1 : ℕ) : ℝ)) hQ]
  refine ⟨Real.one_le_exp hlog, hc.trans (hCexp.trans (Real.exp_le_exp.mpr hCLog)), ?_, ?_⟩
  · have hpow : (q : ℝ) ^ (dim + 1) ≤ Real.exp (((dim + 1 : ℕ) : ℝ) * Q) := by
      calc
        _ ≤ (Real.exp Q) ^ (dim + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hqQ _
        _ = _ := (Real.exp_nat_mul _ _).symm
    have hscalar := scalarCubePrimitiveEnvelope_le_scaled (Fin dim) A 1 0 hq
    simp only [Fintype.card_fin] at hscalar
    apply hscalar.trans
    calc
      _ ≤ Real.exp C * Real.exp (((dim + 1 : ℕ) : ℝ) * Q) :=
        mul_le_mul (hs.trans hCexp) hpow (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
      _ = Real.exp (C + ((dim + 1 : ℕ) : ℝ) * Q) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    rw [Nat.cast_mul]
    calc
      _ ≤ (Real.exp 4 * Real.exp F) * Real.exp Q :=
        mul_le_mul (hstep.trans (mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)))
          hqQ (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (4 + F + Q) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        push_cast
        nlinarith only [hQ, mul_nonneg (Nat.cast_nonneg dim : (0 : ℝ) ≤ dim) hQ,
          Nat.cast_nonneg (α := ℝ) C])

theorem exists_uniform_slicedGridParameters (dim : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {F Q : ℝ}, 0 ≤ F → 0 ≤ Q →
      ∃ T : ℕ, (T : ℝ) ≤ Real.exp (dim + Q + F + 1) ∧
      ∀ {δ : ℝ} {q step : ℕ}, 0 < δ → δ⁻¹ ≤ Real.exp F → 0 < q →
        (q : ℝ) ≤ Real.exp Q → (step : ℝ) ≤ 4 * Real.exp F →
        (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
        let Pg := Real.exp (C + ((dim + 1 : ℕ) : ℝ) * Q + F + 4)
        1 ≤ Pg ∧ scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Pg ∧ ((step * q : ℕ) : ℝ) ≤ Pg := by
  obtain ⟨C, hC, hparameters⟩ := exists_slicedGridParameters dim A
  refine ⟨C, hC, ?_⟩
  intro F Q hF hQ
  let T : ℕ := ⌈Real.exp (dim + Q + F)⌉₊
  refine ⟨T, natCeil_le_exp_succ (Real.exp_nonneg _) (by positivity) le_rfl, ?_⟩
  intro δ q step hδ hδF hq hqQ hstep
  obtain ⟨_, _, _, hprimitive⟩ := hparameters hF hQ hδ hδF hq hqQ hstep
  refine ⟨?_, hprimitive⟩
  have hdim : ((dim + 1 : ℕ) : ℝ) ≤ Real.exp dim := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (dim : ℝ)
  have hbound : (((dim + 1) * q : ℕ) : ℝ) / δ ≤ Real.exp (dim + Q + F) := by
    rw [Nat.cast_mul, div_eq_mul_inv]
    exact (mul_le_mul (mul_le_mul hdim hqQ (Nat.cast_nonneg _) (Real.exp_nonneg _))
      hδF (inv_nonneg.mpr hδ.le) (by positivity)).trans_eq
      (by rw [← Real.exp_add, ← Real.exp_add])
  exact hbound.trans (Nat.le_ceil _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorPeriodBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_preparedModularCanonicalDetector_grid_parameters (m dim : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {nX : ℕ} {Pk Qstride p : ℝ},
      0 ≤ Pk → 0 ≤ Qstride → 0 ≤ p →
      let Q := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let tg := (dim : ℝ) + Q + (p + 1) + 1
      let pg := (C : ℝ) + ((dim + 1 : ℕ) : ℝ) * Q + (p + 1) + 4
      let δ := Real.exp (-(p + 1))
      0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp (p + 1) ∧ 0 ≤ tg ∧ 0 ≤ pg ∧
      ∃ T : ℕ, (T : ℝ) ≤ Real.exp tg ∧
      ∀ {M period : ℕ} (stride : Fin nX → ℕ),
        (M : ℝ) ≤ Real.exp Pk → 0 < period → period ≤ M ^ (m + 1) →
        (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp Qstride) →
        let q := residueRefinedPeriod period stride
        (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
        1 ≤ Real.exp pg ∧
        scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Real.exp pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Real.exp pg ∧
        ∀ {Y : Type*} (step : Y → ℕ),
          (∀ y, (step y : ℝ) ≤ 4 * Real.exp (p + 1)) →
          ∀ y, ((step y * q : ℕ) : ℝ) ≤ Real.exp pg := by
  obtain ⟨C, hC, hparameters⟩ := exists_uniform_slicedGridParameters dim A
  refine ⟨C, hC, ?_⟩
  intro nX Pk Qstride p hPk hQstride hp Q tg pg δ
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hF : 0 ≤ p + 1 := by positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hδF : δ⁻¹ ≤ Real.exp (p + 1) := by
    simp only [δ, Real.exp_neg, inv_inv, le_refl]
  obtain ⟨T, hT, hgrid⟩ := hparameters hF hQ
  refine ⟨hδ, Real.exp_le_one_iff.mpr (by linarith), hδF,
    by dsimp only [tg]; positivity, by dsimp only [pg]; positivity, T, hT, ?_⟩
  intro M period stride hM hperiod hperiodBound hstride hstrideBound q
  have hperiodLog : (period : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * Pk) := by
    calc
      _ ≤ ((M ^ (m + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hperiodBound
      _ = (M : ℝ) ^ (m + 1) := Nat.cast_pow _ _
      _ ≤ (Real.exp Pk) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hq : 0 < q := residueRefinedPeriod_pos hperiod stride hstride
  have hqQ : (q : ℝ) ≤ Real.exp Q := by
    simpa only [Fintype.card_fin] using residueRefinedPeriod_exp_bound period stride hperiodLog hstrideBound
  have hstepZero : ((0 : ℕ) : ℝ) ≤ 4 * Real.exp (p + 1) := by
    simpa only [Nat.cast_zero] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_nonneg (p + 1))
  obtain ⟨hQT, hPg, hcP, hsP, _⟩ := hgrid (step := 0) hδ hδF hq hqQ hstepZero
  refine ⟨hQT, hPg, hcP, hsP, ?_⟩
  intro Y step hstep y
  exact (hgrid hδ hδF hq hqQ (hstep y)).2.2.2.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

noncomputable def weightedReplacementTolerance (F E epsilon : ℝ) : ℝ :=
  replacementAccuracy (F ^ 2 * (1 + E)) (epsilon ^ 2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarReferenceNativeDetectionCoordinateEquiv
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K K' X : Type*}

def scalarNoiseIndexEquiv (e : K ≃ K') : Option K × X ≃ Option K' × X :=
  (Equiv.optionCongr e).prodCongr (Equiv.refl X)

@[simp] theorem scalarNoiseIndexEquiv_none (e : K ≃ K') (x : X) :
    scalarNoiseIndexEquiv e (none, x) = (none, x) := rfl

@[simp] theorem scalarNoiseIndexEquiv_some (e : K ≃ K') (k : K) (x : X) :
    scalarNoiseIndexEquiv e (some k, x) = (some (e k), x) := rfl

@[simp] theorem scalarNoiseIndexEquiv_symm (e : K ≃ K') :
    (scalarNoiseIndexEquiv (X := X) e).symm = scalarNoiseIndexEquiv e.symm := rfl

end Erdos3

end

end OAI
end


