-- Prove2me | Definitions.Def_OAIE3v2B048
-- name    : OAIE3v2B048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:13:14.254965+00:00
-- url     : https://prove2.me/theorems/d39522a9-e438-4bb4-9f13-de22a908d123
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 49 of 311
-- statement:
--   Definitions bundle 49 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B007`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B012`, `OAIE3v2B013`, `OAIE3v2B014`, `OAIE3v2B015` of this split.
--
--   Modules: `Dynamics/CoefficientProfileBudget.lean`, `Estimates/CoefficientRowEvaluation.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/CubeSignalAlgebra.lean`, `Estimates/CubeTranslation.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/DenseProgressionInnerFamily.lean`, `Estimates/DependentPatchValue.lean`, `Estimates/FourSlicedProductSmoothing.lean`, `Estimates/LinearCutoff.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/NestedProgressionReindex.lean`, `Estimates/PhysicalSliceCost.lean`, `Estimates/PrincipalBlockExponent.lean`, `Estimates/PrincipalCoefficientMarginal.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Estimates/ScalarCubeCokernelCutoff.lean`, `Estimates/SplitSmoothProductProfile.lean`, `Estimates/TranslationMajorTwistedCorrelationStepDrop.lean`, `Fourier/UniformScaledRetainedCharacters.lean`, `Fourier/UniformSpectrumAbsoluteCap.lean`, `Fourier/UniformSpectrumSize.lean`, `Geometry/BoxCornerMean.lean`, `Geometry/BoxImageComparison.lean`, `Geometry/CertifiedFullChartFrozenTerminal.lean`, `Geometry/CommonStrideCoordinates.lean`, `Geometry/CoveredJetChart.lean`, `Geometry/CubeSignalCoordinates.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/RealCoordinateFunctionals.lean`, `Geometry/SampledCommonBox.lean`, `Lattices/AffineLowestLayer.lean`, `Lattices/AffineWindowGoodKernelBound.lean`, `Lattices/CommonIntegerIntervalCorrelation.lean`, `Lattices/IntegerFrozenChart.lean`, `Lattices/IntegerIntervalCyclicAverage.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/LayerSamplingRankAffine.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/RandomAffinePair.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Linear/FixedSpatialKernelSliceDensity.lean`, `Linear/OrthogonalBasisChart.lean`, `Polynomial/CoefficientPolynomialLift.lean`, `Polynomial/DenseRowPhaseAlignment.lean`, `Polynomial/IntegerPolynomialActiveProfileSupport.lean`, `Polynomial/LowestPolynomialLayer.lean`, `Polynomial/MonomialArrayJet.lean`, `Polynomial/PiCoordinatePolynomialCoefficients.lean`, `Polynomial/PolynomialTranslationSeries.lean`, `Probability/AllocatedSlicedIdealDensity.lean`, `Probability/DensityMixtureAELaw.lean`, `Probability/PairedProductDensity.lean`, `Probability/ScaledArrayLaw.lean`, `Probability/ShiftedSmoothLawBounds.lean`, `Probability/SlicedPairDensity.lean`, `Probability/SlicedRemainderDensityFamily.lean`, `Sampling/CanonicalSamplerTuple.lean`, `Sampling/CyclicIntervalSampling.lean`, `Sampling/LayerSamplerWitnessScale.lean`.
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
import Definitions.Def_OAIE3v2B005
import Definitions.Def_OAIE3v2B007
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B012
import Definitions.Def_OAIE3v2B013
import Definitions.Def_OAIE3v2B014
import Definitions.Def_OAIE3v2B015

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientProfileBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coefficientProfileWidth_pos {J : Type*} (P : Finset J) (j₀ : J)
    {ρ γ ε : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε) (j : J) :
    0 < coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  unfold coefficientProfileWidth
  split_ifs <;> positivity

theorem allocatedProfile_budget {R σ : ℝ} (hR : 0 ≤ R) (hσ1 : σ ≤ 1) (b m : ℕ) :
    R / 4 + 2 * principalProfileSize R b * b + tailProfileSize R σ m * m ≤ 3 * R / 4 := by
  have hb : (b : ℝ) / ((b : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hm : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hp : 2 * principalProfileSize R b * b ≤ R / 4 := by
    calc
      _ = (R / 4) * ((b : ℝ) / ((b : ℝ) + 1)) := by
        unfold principalProfileSize
        field_simp; ring
      _ ≤ (R / 4) * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := mul_one _
  have ht : tailProfileSize R σ m * m ≤ R / 4 := by
    calc
      _ = σ * (R / 4) * ((m : ℝ) / ((m : ℝ) + 1)) := by
        unfold tailProfileSize
        field_simp
      _ ≤ 1 * (R / 4) * 1 := by gcongr
      _ = _ := by ring
  linarith

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

omit [Fintype H] in
theorem multiplicativeDerivative_comm (f : H → ℂ) (h k : H) :
    multiplicativeDerivative (multiplicativeDerivative f h) k =
      multiplicativeDerivative (multiplicativeDerivative f k) h := by
  funext x
  simp only [multiplicativeDerivative, star_mul, star_star]
  rw [show x + k + h = x + h + k by abel]
  ring

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

def cubeProduct (f : H → ℂ) (hs : List H) (x : H) : ℂ :=
  (hs.sublists'.map fun ks ↦ conjugationPower ks.length (f (x + ks.sum))).prod

@[simp] theorem cubeProduct_nil (f : H → ℂ) (x : H) : cubeProduct f [] x = f x := by
  simp [cubeProduct, conjugationPower]

theorem cubeProduct_cons (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct f (h :: hs) x = cubeProduct f hs x * star (cubeProduct f hs (x + h)) := by
  simp only [cubeProduct, List.sublists'_cons, List.map_append, List.prod_append,
    List.map_map, Function.comp_def, List.length_cons, List.sum_cons,
    conjugationPower, RingHom.comp_apply]
  congr 1
  change _ = (starRingEnd ℂ) _
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def, add_assoc]

theorem cubeProduct_derivative (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct (multiplicativeDerivative f h) hs x =
      cubeProduct f hs x * star (cubeProduct f hs (x + h)) := by
  induction hs generalizing x with
  | nil => simp [multiplicativeDerivative]
  | cons k hs ih =>
    simp only [cubeProduct_cons, ih, star_mul, star_star]
    rw [show x + k + h = x + h + k by abel]
    ring

theorem cubeProduct_cons_eq_derivative (f : H → ℂ) (h : H) (hs : List H) (x : H) :
    cubeProduct f (h :: hs) x = cubeProduct (multiplicativeDerivative f h) hs x := by
  rw [cubeProduct_cons, cubeProduct_derivative]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3.TriangularSlots

variable {D E d : ℕ}

def takePrefix (A : TriangularSlots (D + E)) : TriangularSlots D where
  center x i := A.center (Fin.append x 0) (i.castAdd E)
  lower i x y hxy := by
    apply A.lower
    intro j
    refine Fin.addCases (fun k hj => ?_) (fun k hj => ?_) j
    · simp only [Fin.append_left]
      apply hxy
      simpa only [Fin.lt_def, Fin.val_castAdd] using hj
    · simp only [Fin.append_right]

end Erdos3.TriangularSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineLowestLayer
namespace OAI

section

namespace Erdos3

namespace TriangularSlots

variable {D : ℕ}

noncomputable def affineBlock (M : Matrix (Fin D) (Fin D) ℝ)
    (hM : ∀ i j, i ≤ j → M i j = 0) (P : Fin D → ℝ) : TriangularSlots D where
  center x := P + M.mulVec (x - P)
  lower i x y hxy := by
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j < i
    · simp only [Pi.sub_apply, hxy j hji]
    · simp [hM i j (le_of_not_gt hji)]

end TriangularSlots

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxImageComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

def ImageTranslationBound (μ : Measure Ω) (U : Ω → (ι → ℝ)) (H : ℝ≥0) : Prop :=
  ∀ (φ : (ι → ℝ) → ℝ), Measurable φ → (∀ x, ‖φ x‖ ≤ 1) → ∀ z,
    |mappedTest μ U (fun x => φ (x + z)) - mappedTest μ U φ| ≤ H * dist z 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PairedProductDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def randomIntervalDensity {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (ℓ s : T → ℝ) : ℝ → ℝ :=
  densityMixture μ (fun t => normalizedIntervalWindow (ℓ t) (s t))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {T : Type*} [MeasurableSpace T]

noncomputable def independentShiftDensity (μ : Measure T) (z : T → ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  densityMixture μ (fun t x => f (x - z t))

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

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

noncomputable def sigmaAxisWeight (w : ∀ d, (I d → ℝ) → ℝ) (x : (Σ d, I d) → ℝ) : ℝ :=
  tensorCutoffWeight w (sigmaAxisCoordinates I x)

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

theorem card_translateSupport (a : A) (Q : Finset A) : (translateSupport a Q).card = Q.card :=
  Finset.card_image_of_injective Q (fun _ _ h ↦ add_left_cancel h)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [AddCommGroup H] [Fintype H] in
theorem finiteIndicator_norm_le_one (I : Finset H) (x : H) : ‖finiteIndicator I x‖ ≤ 1 := by
  simp only [finiteIndicator]
  split_ifs <;> norm_num

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem finiteCorrelation_mul_indicator (I : Finset H) (f u : H → ℂ) :
    finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x) =
      ((I.card : ℂ) / Fintype.card H) * finiteCorrelation I f u := by
  have he : (fun x => f x * star (u x * finiteIndicator I x)) =
      restrictTo I (fun x => f x * star (u x)) := by
    funext x
    by_cases hx : x ∈ I <;> simp [finiteIndicator, restrictTo, hx]
  unfold finiteCorrelation
  rw [he, expect_restrictTo, Finset.expect_eq_sum_div_card]
  by_cases hI : I.card = 0
  · simp [Finset.card_eq_zero.mp hI]
  · have hi : (I.card : ℂ) ≠ 0 := by exact_mod_cast hI
    have hn : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSliceCost
namespace OAI

section

namespace Erdos3

def ResidueSliceLogCostLE {σ : Type*} (H : σ → ℕ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (P : ℝ) : Prop :=
  ∀ j, Real.exp (-P) * (H j : ℝ) ≤ (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

theorem integerInterval_reflectsPairSums (N : ℕ) (a b : ℤ)
    (hdiam : 2 * (b - a - 1) < (N : ℤ)) :
    ReflectsPairSums (integerCyclicMap N) (Finset.Ico a b : Set ℤ) := by
  intro x hx y hy z hz t ht he
  have hx' := Finset.mem_Ico.mp hx
  have hy' := Finset.mem_Ico.mp hy
  have hz' := Finset.mem_Ico.mp hz
  have ht' := Finset.mem_Ico.mp ht
  have hxy : 0 ≤ x + y - 2 * a ∧ x + y - 2 * a < N := by omega
  have hzt : 0 ≤ z + t - 2 * a ∧ z + t - 2 * a < N := by omega
  have he' : ((x + y - 2 * a : ℤ) : ZMod N) = ((z + t - 2 * a : ℤ) : ZMod N) := by
    change (x : ZMod N) + y = (z : ZMod N) + t at he
    push_cast
    exact congrArg (fun v : ZMod N => v - 2 * (a : ZMod N)) he
  have hh := int_eq_of_zmod_eq_of_bounds hxy hzt he'
  omega

theorem integerInterval_image_cyclicInterval (N : ℕ) (a : ℤ) (L : ℕ) :
    (Finset.Ico a (a + L)).image (integerCyclicMap N) = cyclicInterval (a : ZMod N) L := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_Ico.mp hy
    refine Finset.mem_image.mpr ⟨(y - a).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · change (a : ZMod N) + ((y - a).toNat : ZMod N) = (y : ZMod N)
      have he : (((y - a).toNat : ℕ) : ℤ) = y - a := Int.toNat_of_nonneg (by omega)
      rw [← Int.cast_natCast, he]
      push_cast
      ring
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨a + k, Finset.mem_Ico.mpr ?_, ?_⟩
    · have hk' := Finset.mem_range.mp hk
      omega
    · change ((a + k : ℤ) : ZMod N) = (a : ZMod N) + k
      push_cast
      rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialArrayJet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def monomialArrayPolynomial {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) : MvPolynomial K ℝ :=
  ∑ j, MvPolynomial.monomial (e j) (a j)

theorem monomialArrayPolynomial_eval {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (x : K → ℝ) :
    MvPolynomial.eval x (monomialArrayPolynomial e a) =
      ∑ j, a j*∏ k ∈ (e j).support, x k^e j k := by
  simp only [monomialArrayPolynomial, map_sum, MvPolynomial.eval_monomial, Finsupp.prod]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped ContDiff

abbrev JointBlockParameter {D : Type*} (B : D → Type*) (h : D → ℕ) (α : Type*) :=
  Σ d, BlockParameter (B d) (Fin (h d)) α

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Function _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_apply (e : X → Y) (he : Function.Injective e)
    (c : ℝ) (f : X → ℝ) (x : X) : embeddingDensity e c f (e x) = c * f x := by
  simp only [embeddingDensity, he.extend_apply]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_zero (e : X → Y) (c : ℝ) (f : X → ℝ) (y : Y)
    (hy : y ∉ Set.range e) : embeddingDensity e c f y = 0 := by
  simp only [embeddingDensity, Function.extend_apply' f (fun _ => 0) y hy, mul_zero]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem embeddingDensity_nonneg (e : X → Y) (he : Function.Injective e)
    {c : ℝ} (hc : 0 ≤ c) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (y : Y) :
    0 ≤ embeddingDensity e c f y := by
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingDensity_apply e he]
    exact mul_nonneg hc (hf x)
  · rw [embeddingDensity_zero e c f y hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RandomAffinePair
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {T : Type*} [MeasurableSpace T]

noncomputable def affinePairDensity (μ : Measure T) (a b c : T → ℝ) : ℝ → ℝ :=
  randomIntervalDensity (μ.prod unitScalarMeasure) (affinePairWidth a b) (affinePairShift a b c)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedPairDensity
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def pairDensity (A B : SlicedProductBlock ι) : ℝ → ℝ :=
  affinePairDensity ((unitBoxMeasure ι).prod (unitBoxMeasure ι))
    (fun p => A.slope p.1) (fun p => B.slope p.2) (fun p => A.base p.1 + B.base p.2)

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FourSlicedProductSmoothing
namespace OAI

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def fourDensity (A B C D : SlicedProductBlock ι) : ℝ → ℝ :=
  scalarDensityConvolution (pairDensity A B) (pairDensity C D)

end Erdos3.SlicedProductBlock

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq J] [DecidableEq ι]

noncomputable def principalFourRemainderDensity (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ) : ℝ → ℝ :=
  independentShiftDensity (unitBoxMeasure (J × Option ι))
    (principalSliceValue (fun b => c (.inr b))
      (fun p => lower (.inr p.1, p.2)) (fun p => width (.inr p.1, p.2)))
    (SlicedProductBlock.fourDensity
      (principalSliceBlock c lower width (.inl 0))
      (principalSliceBlock c lower width (.inl 1))
      (principalSliceBlock c lower width (.inl 2))
      (principalSliceBlock c lower width (.inl 3)))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def reindexedSlicedPrincipalDensity
    {B F J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (eB : Fin 4 ⊕ J ≃ B) (eF : Option I ≃ F)
    (c : B → ℝ) (lower width : B × F → ℝ) : ℝ → ℝ :=
  principalFourRemainderDensity (fun b => c (eB b))
    (fun p => lower (eB p.1, eF p.2)) (fun p => width (eB p.1, eF p.2))

noncomputable def canonicalSlicedPrincipalDensity
    {B F : Type*} [Fintype B] [Fintype F] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F) (c : B → ℝ) (lower width : B × F → ℝ) : ℝ → ℝ :=
  reindexedSlicedPrincipalDensity (fourBlockDecomposition B hB) (Equiv.optionSubtypeNe i) c lower width

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalBlockExponent
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem canonicalPrincipalExponent_apply {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [DecidableEq (B d)] (b b' : B d) (v : Fin (h d)) :
    canonicalPrincipalExponent (G := G) h d b (.inr ⟨d, b', v⟩) = if b = b' then 1 else 0 := by
  classical
  by_cases hb : b = b' <;>
    simp [canonicalPrincipalExponent, productBlockExponent, Finsupp.single_apply, hb]

theorem canonicalPrincipalExponent_ne_zero {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) (b : B d) :
    canonicalPrincipalExponent (G := G) h d b ≠ 0 := by
  classical
  intro he
  have hv := congrArg (fun e : SamplerTupleIndex G B h →₀ ℕ => e (.inr ⟨d, b, ⟨0, hd⟩⟩)) he
  simp [canonicalPrincipalExponent_apply] at hv

theorem canonicalPrincipalExponent_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (canonicalPrincipalExponent (G := G) (B := B) h d) := by
  classical
  intro b b' he
  by_contra hne
  have hv := congrArg (fun e : SamplerTupleIndex G B h →₀ ℕ => e (.inr ⟨d, b', ⟨0, hd⟩⟩)) he
  simp [canonicalPrincipalExponent_apply, hne] at hv

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem principalCoefficientSlot_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (principalCoefficientSlot (G := G) (B := B) h d) := by
  intro b b' he
  exact canonicalPrincipalExponent_injective h d hd (congrArg Subtype.val he)

theorem mem_principalCoefficientSlots {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] (e) :
    e ∈ principalCoefficientSlots (G := G) (B := B) h d ↔
      ∃ b, principalCoefficientSlot h d b = e := by
  classical
  simp [principalCoefficientSlots]

theorem principalCoefficientSlots_card {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] (hd : 0 < h d) :
    (principalCoefficientSlots (G := G) (B := B) h d).card = Fintype.card (B d) := by
  classical
  exact (Finset.card_image_of_injective _ (principalCoefficientSlot_injective h d hd)).trans
    (Finset.card_univ)

theorem constantCoefficientSlot_not_principal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) [Fintype (B d)] (hd : 0 < h d) :
    constantCoefficientSlot (SamplerTupleIndex G B h) (h d) ∉ principalCoefficientSlots h d := by
  intro he
  obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d _).mp he
  exact canonicalPrincipalExponent_ne_zero h d hd b (congrArg Subtype.val hb)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCornerMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem conjugationPower_eq_if_mod (n : ℕ) (z : ℂ) :
    conjugationPower n z = if n % 2 = 0 then z else star z := by
  induction n with
  | zero => simp [conjugationPower]
  | succ n ih =>
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hn with hn | hn <;>
      simp [conjugationPower, ih, Nat.add_mod, hn]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedSmoothLawBounds
namespace OAI

section

namespace Erdos3

theorem shiftedSmoothCoefficientPMF_support (a : ℝ) {S : ℝ} (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) {k : ℤ}
    (hk : k ∈ (shiftedSmoothCoefficientPMF a S hS hZ).support) :
    |(k : ℝ) - a| < 3 * S / 4 := by
  by_contra! h
  have hz : smoothProbabilityProfile (((k : ℝ) - a) / S) = 0 := by
    apply smoothProbabilityProfile_zero
    rw [abs_div, abs_of_pos hS]
    apply (le_div_iff₀ hS).mpr
    linarith
  apply hk
  change ENNReal.ofReal (smoothProbabilityProfile (((k : ℝ) - a) / S) /
    shiftedSmoothSampleSum a S) = 0
  simp only [hz, zero_div, ENNReal.ofReal_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeCokernelCutoff
namespace OAI


namespace Erdos3

def HasBoundedScalarPeriod {I : Type*} [Fintype I] (L : Submodule ℤ (I → ℤ)) (B : ℕ) : Prop :=
  ∃ a : ℕ, 0 < a ∧ a ≤ B ∧ integerScalarLattice I (a : ℤ) ≤ L

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

structure PolynomialPotentialRelation (σ : Type*) [Fintype σ] where
  space : Submodule ℚ ((σ → ℚ) × MvPolynomial σ ℚ)
  bracket_mem : ∀ x P z Q, (x, P) ∈ space → (z, Q) ∈ space →
    (0, scalarDirectionalDerivative x Q - scalarDirectionalDerivative z P) ∈ space
  pure_constant_zero : ∀ Q, (0, Q) ∈ space → Q.coeff 0 = 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.OrthogonalBasisChart
namespace OAI

section

namespace Erdos3

open Module

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem orthogonalBasisChart_apply (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) (x : E) :
    orthogonalBasisChart W b x =
      (W.orthogonalProjectionOnto x, b.equivFun (Wᗮ.orthogonalProjectionOnto x)) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem latticeBasisEquiv_coordinates (Λ : Submodule ℤ E) (b : Basis I ℝ E)
    (hb : span ℤ (Set.range b) = Λ) (z : I → ℤ) (i : I) :
    b.equivFun (latticeBasisEquiv Λ b hb z).val i = (z i : ℝ) := by
  change b.repr (((b.restrictScalars ℤ).equivFun.symm z) : E) i = _
  have h := b.restrictScalars_repr_apply ℤ ((b.restrictScalars ℤ).equivFun.symm z) i
  change (algebraMap ℤ ℝ)
    ((b.restrictScalars ℤ).equivFun ((b.restrictScalars ℤ).equivFun.symm z) i) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  simpa using h.symm

end Erdos3

end

section

namespace Erdos3

variable (J : Type*) [Fintype J]

theorem standardLatticeSmallBox_isOpen : IsOpen (standardLatticeSmallBox J) := by
  unfold standardLatticeSmallBox
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by fun_prop) continuous_const

theorem standardLatticeSmallBox_separates
    {x y : EuclideanSpace ℝ J} (hx : x ∈ standardLatticeSmallBox J)
    (hy : y ∈ standardLatticeSmallBox J) (hxy : x - y ∈ standardEuclideanLattice J) : x = y := by
  ext i
  obtain ⟨n, hn⟩ := (mem_standardEuclideanLattice J (x - y)).mp hxy i
  change (n : ℝ) = x i - y i at hn
  have hxi := abs_lt.mp (hx i)
  have hyi := abs_lt.mp (hy i)
  have hnlo : (-1 : ℝ) < n := by linarith
  have hnhi : (n : ℝ) < 1 := by linarith
  have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
  have hn0 : n = 0 := by omega
  exact sub_eq_zero.mp (by simpa only [hn0, Int.cast_zero] using hn.symm)

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem projectedLatticeLift_projection (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) :
    Wᗮ.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val = z.val :=
  congrArg Subtype.val (orthogonalLatticeProjection_surjective Λ Wᗮ z).choose_spec

noncomputable def latticeSheetQuotient (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) (u : W) : W ⧸ (latticeSection Λ W).toAddSubgroup :=
  QuotientAddGroup.mk (u - projectedLatticeShift Λ W z)

theorem latticeSheetPoint_reconstruction (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    (z : orthogonalLatticeImage Λ Wᗮ) (u : W) :
    latticeSheetPoint W z.val u =
      (u - projectedLatticeShift Λ W z).val + (projectedLatticeLift Λ W z).val := by
  have hs := W.starProjection_add_starProjection_orthogonal (projectedLatticeLift Λ W z).val
  change (projectedLatticeShift Λ W z).val +
    (Wᗮ.orthogonalProjectionOnto (projectedLatticeLift Λ W z).val).val = _ at hs
  rw [projectedLatticeLift_projection] at hs
  change u.val + z.val.val = (u.val - (projectedLatticeShift Λ W z).val) + _
  calc
    _ = (u.val - (projectedLatticeShift Λ W z).val) +
        ((projectedLatticeShift Λ W z).val + z.val.val) := by abel
    _ = _ := by rw [hs]

theorem latticeSheetPoint_sub_mem_of_quotient_eq (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    {z w : orthogonalLatticeImage Λ Wᗮ} {u v : W}
    (h : latticeSheetQuotient Λ W z u = latticeSheetQuotient Λ W w v) :
    latticeSheetPoint W z.val u - latticeSheetPoint W w.val v ∈ Λ := by
  have hm := QuotientAddGroup.eq_iff_sub_mem.mp h
  change ((u - projectedLatticeShift Λ W z) - (v - projectedLatticeShift Λ W w)).val ∈ Λ at hm
  have hl := Λ.sub_mem (projectedLatticeLift Λ W z).property (projectedLatticeLift Λ W w).property
  rw [latticeSheetPoint_reconstruction, latticeSheetPoint_reconstruction]
  convert Λ.add_mem hm hl using 1
  simp only [Submodule.coe_sub]
  abel

theorem latticeSheetQuotient_injective_on_region (Λ : Submodule ℤ E) (W : Submodule ℝ E)
    {Ω : Set E}
    (hΩ : ∀ x ∈ Ω, ∀ y ∈ Ω, x - y ∈ Λ → x = y)
    {z w : orthogonalLatticeImage Λ Wᗮ} {u v : W}
    (hu : latticeSheetPoint W z.val u ∈ Ω) (hv : latticeSheetPoint W w.val v ∈ Ω)
    (h : latticeSheetQuotient Λ W z u = latticeSheetQuotient Λ W w v) : z = w ∧ u = v := by
  have he := hΩ _ hu _ hv (latticeSheetPoint_sub_mem_of_quotient_eq Λ W h)
  constructor
  · apply Subtype.ext
    simpa only [latticeSheetPoint_projection_orthogonal] using
      congrArg Wᗮ.orthogonalProjectionOnto he
  · simpa only [latticeSheetPoint_projection] using congrArg W.orthogonalProjectionOnto he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LayerSamplingRankAffine
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem monomialScale_const_mul_degree {I : Type*} (T : I → ℝ) (c : ℝ) (α : I →₀ ℕ) :
    monomialScale (fun i => c * T i) α = c ^ α.degree * monomialScale T α := by
  classical
  simp only [monomialScale, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

theorem monomialScale_le_const_mul {I : Type*} (N L : I → ℝ)
    (hN : ∀ i, 0 ≤ N i) (c : ℝ) (hNL : ∀ i, N i ≤ c * L i) (α : I →₀ ℕ) :
    monomialScale N α ≤ c ^ α.degree * monomialScale L α := by
  rw [← monomialScale_const_mul_degree]
  exact Finset.prod_le_prod (fun i _ => pow_nonneg (hN i) _)
    (fun i _ => pow_le_pow_left₀ (hN i) (hNL i) _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped ContDiff

theorem normalizedIntegerPMF_support (K c δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) {k : ℤ}
    (hk : k ∈ (normalizedIntegerPMF K c δ hK hδ hlarge).support) :
    |(k : ℝ) / K - c| < 3 * δ / 4 := by
  have hb := shiftedSmoothCoefficientPMF_support (c * K) (mul_pos hδ hK)
    (shiftedSmoothSampleSum_pos (c * K) hlarge) hk
  rw [show (k : ℝ) / K - c = ((k : ℝ) - c * K) / K by field_simp,
    abs_div, abs_of_pos hK]
  apply (div_lt_iff₀ hK).mpr
  nlinarith

end Erdos3

end

section

namespace Erdos3

theorem constantIntegerPMF_large (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ δ * K) :
    constantIntegerPMF K δ hK hδ = normalizedIntegerPMF K 0 δ hK hδ hlarge := by
  simp [constantIntegerPMF, hlarge]

theorem constantIntegerPMF_small (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ)
    (hsmall : δ * K < 8 * (probabilityProfileLipschitz : ℝ)) :
    constantIntegerPMF K δ hK hδ = PMF.pure 0 ∧
      K < 8 * (probabilityProfileLipschitz : ℝ) / δ := by
  refine ⟨by simp [constantIntegerPMF, not_le.mpr hsmall], ?_⟩
  apply (lt_div_iff₀ hδ).mpr
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module _root_.Set
open scoped ENNReal

variable {E T I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] [Fintype I]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T] in
theorem translatedQuotientChart_image (Λ : Submodule ℤ E) (v : T → E) (S : Set (E × T)) :
    translatedQuotientChart Λ v '' S =
      ⋃ t, (fun x => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) ''
        ((fun x => (x, t)) ⁻¹' S) := by
  ext q
  constructor
  · rintro ⟨⟨x, t⟩, hx, rfl⟩
    exact mem_iUnion.mpr ⟨t, x, hx, rfl⟩
  · intro h
    obtain ⟨t, x, hx, rfl⟩ := mem_iUnion.mp h
    exact ⟨(x,t), hx, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerMonomialArrayPolynomial {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) : MvPolynomial V ℤ :=
  ∑ j, MvPolynomial.monomial (e j) (a j)

theorem integerMonomialArrayPolynomial_map {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) :
    MvPolynomial.map (Int.castRingHom ℝ) (integerMonomialArrayPolynomial e a) =
      monomialArrayPolynomial e (fun j => (a j : ℝ)) := by
  simp only [integerMonomialArrayPolynomial, monomialArrayPolynomial, map_sum,
    MvPolynomial.map_monomial, Int.coe_castRingHom]

theorem integerMonomialArrayPolynomial_degree {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) {s : ℕ} (he : ∀ j, (e j).sum (fun _ n => n) ≤ s) :
    (integerMonomialArrayPolynomial e a).totalDegree ≤ s := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (he j)

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

noncomputable def modularBoundedCoefficientPolynomial {K R : Type*}
    [Fintype K] [CommRing R] (h : ℕ)
    (c : BoundedCoefficientExponent K h → R) : MvPolynomial K R :=
  ∑ e, monomial e.val (c e)

noncomputable def modularUnselectedCoefficientPolynomial {K R A : Type*}
    [Fintype K] [Fintype A] [CommRing R] (h : ℕ)
    (slot : A → BoundedCoefficientExponent K h)
    (fixed : BoundedCoefficientExponent K h → R) : MvPolynomial K R :=
  ∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot), monomial e.val (fixed e)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledArrayLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

noncomputable def mixedArrayQuotient (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (o : OrthonormalBasis I ℝ W) (x : (I → J → ℝ) × (Fin n → J → ℤ)) :
    J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  fun j => normalizedLatticeQuotient W b hb (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CoefficientPolynomialLift
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def coefficientRowPolynomial (c : CoefficientArray (K := K) U) (j : Fin m) (i : J j) :
    MvPolynomial K ℝ :=
  monomialArrayPolynomial Subtype.val (fun d : BoundedCoefficientExponent K (j.val + 1) => (c ⟨j, d⟩).val i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientRowPolynomial_sub (c d : CoefficientArray (K := K) U) (j : Fin m) (i : J j) :
    coefficientRowPolynomial U (c - d) j i =
      coefficientRowPolynomial U c j i - coefficientRowPolynomial U d j i := by
  simp only [coefficientRowPolynomial, monomialArrayPolynomial, Pi.sub_apply,
    Submodule.coe_sub, map_sub, Finset.sum_sub_distrib]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem linearCutoff_range (a : ℝ) (h : ℝ≥0) (t : ℝ) :
    0 ≤ linearCutoff a h t ∧ linearCutoff a h t ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem linearCutoff_eq_zero (a : ℝ) (h : ℝ≥0) {t : ℝ} (ht : a + (h : ℝ) ≤ t) :
    linearCutoff a h t = 0 := by
  have hfrac : (a + (h : ℝ) - t) / h ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) h.coe_nonneg
  exact max_eq_left ((min_le_right _ _).trans hfrac)

theorem linearCutoff_lipschitz (a : ℝ) (h : ℝ≥0) (hh : 0 < h) :
    LipschitzWith h⁻¹ (linearCutoff a h) := by
  have hhR : (0 : ℝ) < h := hh
  have haff : LipschitzWith h⁻¹ (fun t : ℝ => (a + (h : ℝ) - t) / h) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, ← sub_div]
    have heq : (a + (h : ℝ) - x) - (a + (h : ℝ) - y) = -(x - y) := by ring
    rw [heq, abs_div, abs_neg, abs_of_pos hhR]
    simp only [NNReal.coe_inv]
    exact le_of_eq (by ring)
  exact (haff.const_min 1).const_max 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CyclicIntervalSampling
namespace OAI

section

namespace Erdos3

theorem finiteCorrelation_image_of_injOn {A B : Type*} [DecidableEq B]
    (Q : Finset A) (φ : A → B) (hφ : Set.InjOn φ (Q : Set A)) (f u : B → ℂ) :
    finiteCorrelation (Q.image φ) f u =
      finiteCorrelation Q (fun x => f (φ x)) (fun x => u (φ x)) := by
  unfold finiteCorrelation
  exact Finset.expect_image hφ

theorem cyclicInterval_representative_correlation {N : ℕ} [NeZero N]
    (a len : ℕ) (hbound : a + len ≤ N) (hshort : 2 * ((len : ℤ) - 1) < N)
    (f : ZMod N → ℂ) (u : ℤ → ℂ) :
    finiteCorrelation (cyclicInterval (a : ZMod N) len) f (fun x => u (x.val : ℤ)) =
      finiteCorrelation (Finset.Ico (a : ℤ) (a + len)) (fun x => f (x : ZMod N)) u := by
  have he := integerInterval_reflectsPairSums N (a : ℤ) (a + len) (by omega)
  rw [← Int.cast_natCast a, ← integerInterval_image_cyclicInterval,
    finiteCorrelation_image_of_injOn _ _ he.injOn]
  unfold finiteCorrelation
  apply Finset.expect_congr rfl
  intro x hx
  have hx' := Finset.mem_Ico.mp hx
  have hrep : (((x : ZMod N).val : ℕ) : ℤ) = x := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (by omega) (by omega)]
  change f (x : ZMod N) * star (u (((x : ZMod N).val : ℕ) : ℤ)) = _
  rw [hrep]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonIntegerIntervalCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerGridEnd_bounds (b : ℕ) {L : ℕ} (hL : 0 < L) :
    integerGridEnd b L ≤ b ∧ b < integerGridEnd b L + L := by
  exact ⟨by simpa only [integerGridEnd, Nat.mul_comm] using Nat.div_mul_le_self b L,
    Nat.lt_mul_div_self_add hL⟩

theorem integer_grid_interval_geometry (a len : ℕ) {L : ℕ} (hL : 0 < L)
    (hsmall : 4 * L ≤ len) :
    a ≤ integerGridStart a L ∧ integerGridEnd (a + len) L ≤ a + len ∧
      integerGridStart a L < integerGridEnd (a + len) L ∧
      integerGridEnd (a + len) L - integerGridStart a L ≤ len ∧
      len ≤ 2 * (integerGridEnd (a + len) L - integerGridStart a L) ∧
      len ≤ (integerGridEnd (a + len) L - integerGridStart a L) + 2 * L := by
  have hs := integerGridStart_bounds a hL
  have he := integerGridEnd_bounds (a + len) hL
  omega

theorem integer_grid_interval_correlation (a len : ℕ) {L : ℕ} (hL : 0 < L)
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hsmall : 4 * (L : ℝ) ≤ ρ * len)
    (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), f n‖) :
    ρ / 2 ≤ ‖𝔼 n ∈ Finset.Ico (integerGridStart a L : ℤ)
      (integerGridEnd (a + len) L : ℤ), f n‖ := by
  have hsmallNat : 4 * L ≤ len := by
    have h := hsmall.trans (mul_le_of_le_one_left (Nat.cast_nonneg len) hρone)
    exact_mod_cast h
  obtain ⟨hstart, hend, hpos, hlenle, _, hloss⟩ := integer_grid_interval_geometry a len hL hsmallNat
  let S := Finset.Ico (a : ℤ) (a + len)
  let T := Finset.Ico (integerGridStart a L : ℤ) (integerGridEnd (a + len) L : ℤ)
  let d := integerGridEnd (a + len) L - integerGridStart a L
  have hTS : T ⊆ S := by
    intro n hn
    simp only [S, T, Finset.mem_Ico] at hn ⊢
    constructor <;> omega
  have hScard : S.card = len := by simp [S, Int.card_Ico]
  have hTcard : T.card = d := by
    simp only [T, Int.card_Ico]
    rw [← Int.natCast_sub hpos.le, Int.toNat_natCast]
  have hbound := norm_sum_subset_card_loss hTS f (fun n _ => hf n)
  rw [← Finset.card_mul_expect S f, ← Finset.card_mul_expect T f] at hbound
  simp only [norm_mul, Complex.norm_natCast, hScard, hTcard] at hbound
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.sub_pos_of_lt hpos
  have hdlen : (d : ℝ) ≤ len := by exact_mod_cast hlenle
  have hlossR : (len : ℝ) ≤ d + 2 * L := by exact_mod_cast hloss
  have hcor := mul_le_mul_of_nonneg_left hcorr (Nat.cast_nonneg len : (0 : ℝ) ≤ len)
  change ρ / 2 ≤ ‖𝔼 n ∈ T, f n‖
  nlinarith only [hbound, hcor, hsmall, hd, hdlen, hlossR, hρ]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_common_integer_interval {G : Type*} {p : ℝ} (hp : 0 ≤ p) {N : ℕ}
    (hN : Real.exp (2 * p + 8) ≤ (N : ℝ))
    (H : Finset G) (hH : H.Nonempty) (start len : G → ℕ)
    (hend : ∀ t ∈ H, start t + len t ≤ N)
    (hshort : ∀ t ∈ H, 2 * ((len t : ℤ) - 1) < N)
    (hlength : ∀ t ∈ H, Real.exp (-p) * N ≤ (len t : ℝ))
    (f : G → ℤ → ℂ) (hf : ∀ t ∈ H, ∀ n, ‖f t n‖ ≤ 1)
    (hcorr : ∀ t ∈ H, Real.exp (-p) ≤
      ‖𝔼 n ∈ Finset.Ico (start t : ℤ) (start t + len t), f t n‖) :
    ∃ S : Finset G, S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-(4 * p + 10)) * (H.card : ℝ) ≤ (S.card : ℝ) ∧
      ∃ a d : ℕ, 0 < d ∧ a + d ≤ N ∧ 2 * ((d : ℤ) - 1) < N ∧
        Real.exp (-(p + 1)) * N ≤ (d : ℝ) ∧
        ∀ t ∈ S, Real.exp (-(p + 1)) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + d), f t n‖ := by
  classical
  obtain ⟨L, hL, hscale, hgrid⟩ := exists_exp_integer_grid_scale hp hN
  have hrho : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hp])
  have hsmall (t : G) (ht : t ∈ H) : 4 * (L : ℝ) ≤ Real.exp (-p) * len t := by
    apply hscale.trans
    calc
      _ = Real.exp (-p) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlength t ht) (Real.exp_nonneg _)
  have hsmallNat (t : G) (ht : t ∈ H) : 4 * L ≤ len t := by
    exact_mod_cast (hsmall t ht).trans (mul_le_of_le_one_left (Nat.cast_nonneg _) hrho)
  let P := Fin (N / L + 2) × Fin (N / L + 2)
  let rel (t : G) (_ : Unit) (c : P) : Prop :=
    start t / L + 1 = c.1.val ∧ (start t + len t) / L = c.2.val
  have hchoice : ∀ t ∈ H, ∀ u, ∃ c, rel t u c := by
    intro t ht _
    have hs : start t ≤ N := by have hh := hend t ht; omega
    have hsd : start t / L ≤ N / L := Nat.div_le_div_right hs
    have hed : (start t + len t) / L ≤ N / L := Nat.div_le_div_right (hend t ht)
    exact ⟨(⟨start t / L + 1, by omega⟩, ⟨(start t + len t) / L, by omega⟩), rfl, rfl⟩
  have hcount : (Fintype.card P : ℝ) ≤ Real.exp (4 * p + 10) := by
    simp only [P, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ Real.exp (2 * p + 5) * Real.exp (2 * p + 5) :=
        mul_le_mul hgrid hgrid (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨c, S, hSH, hS, hSdense, hfixed⟩ := exists_large_fixed_choices H hH rel hchoice hcount
  let a := L * (c ()).1.val
  let b := L * (c ()).2.val
  let d := b - a
  have hround (t : G) (ht : t ∈ S) :
      integerGridStart (start t) L = a ∧ integerGridEnd (start t + len t) L = b := by
    obtain ⟨hs, he⟩ := hfixed t ht ()
    constructor
    · dsimp only [integerGridStart, a]
      rw [hs]
    · dsimp only [integerGridEnd, b]
      rw [he]
  obtain ⟨t0, ht0⟩ := hS
  have ht0H := hSH ht0
  have hgeom := integer_grid_interval_geometry (start t0) (len t0) hL (hsmallNat t0 ht0H)
  rw [(hround t0 ht0).1, (hround t0 ht0).2] at hgeom
  obtain ⟨_, hb, hab, hdlen, hhalf, _⟩ := hgeom
  have had : a + d = b := Nat.add_sub_of_le hab.le
  have hd : 0 < d := Nat.sub_pos_of_lt hab
  have hbN : b ≤ N := hb.trans (hend t0 ht0H)
  have hdshort : 2 * ((d : ℤ) - 1) < N := by
    have hs := hshort t0 ht0H
    change d ≤ len t0 at hdlen
    omega
  have hhalfR : (len t0 : ℝ) ≤ 2 * d := by exact_mod_cast hhalf
  have hvol : Real.exp (-p) / 2 * N ≤ (d : ℝ) := by
    have hv := hlength t0 ht0H
    nlinarith only [hv, hhalfR]
  have hthreshold : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    simpa only [show -(p + 1) = -p - 1 by ring] using exp_sub_one_le_half_exp (-p)
  refine ⟨S, hSH, ⟨t0, ht0⟩, ?_, a, d, hd, ?_, hdshort, ?_, ?_⟩
  · simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hSdense
  · omega
  · exact (mul_le_mul_of_nonneg_right hthreshold (Nat.cast_nonneg _)).trans hvol
  · intro t ht
    have hc := integer_grid_interval_correlation (start t) (len t) hL
      (Real.exp_pos (-p)) hrho (hsmall t (hSH ht)) (f t) (hf t (hSH ht)) (hcorr t (hSH ht))
    rw [(hround t ht).1, (hround t ht).2] at hc
    have hupp : (a : ℤ) + d = b := by exact_mod_cast had
    simpa only [hupp] using hthreshold.trans hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

def majorArcBiasExponent (n : ℕ) : ℕ := 2 ^ n * (denseProductExponent n + 1)

noncomputable def majorArcBiasConstant (n : ℕ) (U : ℝ) : ℝ :=
  ((denseProductDensityConstant n : ℝ) * (2 * 3 ^ n) ^ denseProductExponent n) *
    (2 * U ^ 2) ^ ((n + 1) * majorArcBiasExponent n)

def majorArcLengthExponent (n : ℕ) : ℕ := majorArcBiasExponent n + 2

noncomputable def majorArcLengthConstant (n : ℕ) (U : ℝ) : ℝ :=
  majorArcLocalizationConstant n U * (majorArcBiasConstant n U + 1)

def majorArcErrorExponent (n : ℕ) : ℕ := majorArcBiasExponent n + 2 * (n + 1)

noncomputable def majorArcErrorConstant (n : ℕ) (U : ℝ) : ℝ :=
  majorArcBiasConstant n U * majorArcLocalizationConstant n U ^ (n + 1)

end Erdos3

end

section

namespace Erdos3

def majorArcCoverExponent (n j : ℕ) : ℕ :=
  majorArcBiasExponent n * j + majorArcErrorExponent n

noncomputable def majorArcCoverConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  1 + (majorArcBiasConstant n U * U ^ (n + 1)) ^ j + V * majorArcErrorConstant n U

def majorArcSpectrumExponent (n j : ℕ) : ℕ := 4 * majorArcCoverExponent n j * j

noncomputable def majorArcSpectrumConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  (195 * majorArcCoverConstant n j U V ^ 4) ^ j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def uniformSpectrumBlockCount (n j t : ℕ) : ℕ :=
  max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) + 1

noncomputable def uniformBlockSpectrumAccuracyConstant (n j t : ℕ) (U V W : ℝ) : ℝ :=
  2 * majorArcSpectrumConstant n j U V * 2 ^ majorArcSpectrumExponent n j +
    W * (2 ^ majorArcLengthExponent n * majorArcLengthConstant n U) ^ t

end Erdos3

end

section

namespace Erdos3

noncomputable def uniformScaledRetainedFrequencyBound (n d : ℕ) (U V ζ : ℝ) : ℝ :=
  (⌈majorArcCoverConstant n d U V / ζ ^ majorArcCoverExponent n d⌉₊ : ℝ)

noncomputable def uniformScaledRetainedDenominatorBound (n d t : ℕ) (U V W ζ : ℝ) : ℝ :=
  max ((uniformScaledRetainedFrequencyBound n d U V ζ + 1) ^ d)
    (W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumSize
namespace OAI

section

namespace Erdos3

noncomputable def uniformBlockRetainedBias (n j t : ℕ) (U V W ε : ℝ) : ℝ :=
  min 1 (ε / (uniformBlockSpectrumAccuracyConstant n j t U V W + 1))

end Erdos3

end

section

namespace Erdos3

noncomputable def uniformSpectrumSizeConstant (n j t : ℕ) (U V W : ℝ) : ℝ :=
  (majorArcSpectrumConstant n j U V + W * majorArcLengthConstant n U ^ t) *
    (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) ^
      max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineWindowGoodKernelBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerProgressionSupport (c m : ℤ) (L : ℕ) : Finset ℤ :=
  translateSupport c ((Finset.Ico (0 : ℤ) (L : ℤ)).image (integerStrideHom m))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

theorem card_integerProgressionSupport (c : ℤ) (m H : ℕ) (hm : 0 < m) :
    (integerProgressionSupport c (m : ℤ) H).card = H := by
  unfold integerProgressionSupport
  rw [card_translateSupport, Finset.card_image_of_injective]
  · simp
  · intro x y h
    apply mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0)
    exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonStrideCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def commonStrideBox {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (m : ℕ) (H : I → ℕ) : Finset (I → ℤ) :=
  Fintype.piFinset (fun i => integerProgressionSupport (c i) m (H i))

theorem commonStrideBox_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) {m : ℕ} (hm : 0 < m) (H : I → ℕ) (hH : ∀ i, 0 < H i) :
    (commonStrideBox c m H).Nonempty := by
  apply Fintype.piFinset_nonempty.mpr
  intro i
  apply Finset.card_pos.mp
  simpa only [card_integerProgressionSupport _ _ _ hm] using hH i

theorem commonStrideBox_eq_image {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℤ) (m : ℕ) (H : I → ℕ) :
    commonStrideBox c m H = (integerBox H).image (fun x i => c i + (m : ℤ) * x i) := by
  simp only [commonStrideBox, integerProgressionSupport, translateSupport, Finset.image_image]
  exact Fintype.piFinset_image (fun i x => c i + (m : ℤ) * x) (fun i => Finset.Ico (0 : ℤ) (H i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NestedProgressionReindex
namespace OAI

section

namespace Erdos3

theorem mem_integerProgressionSupport_iff_parameter (c m x : ℤ) (H : ℕ) :
    x ∈ integerProgressionSupport c m H ↔
      ∃ j : ℤ, 0 ≤ j ∧ j < H ∧ x = c + m * j := by
  rw [integerProgressionSupport, mem_translateSupport, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, he⟩
    have hb := Finset.mem_Ico.mp hj
    change m * j = x - c at he
    exact ⟨j, hb.1, hb.2, by omega⟩
  · rintro ⟨j, hj0, hjH, rfl⟩
    exact ⟨j, Finset.mem_Ico.mpr ⟨hj0, hjH⟩, by simp [integerStrideHom]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealCoordinateFunctionals
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def realifyCoordinateMap (ℓ : V →ₗ[ℚ] (J → ℚ)) :
    (ℝ ⊗[ℚ] V) →ₗ[ℝ] (J → ℝ) :=
  LinearMap.pi (fun j => realifyFunctional ((LinearMap.proj j).comp ℓ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def uniformSpectrumAbsoluteCap (n j t : ℕ) (U V W : ℝ) : ℝ :=
  uniformSpectrumSizeConstant n j t U V W + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ}

variable {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem layerIntegerPrincipalSlots_card (j : Fin m) (i : Fin (n j)) :
    (layerIntegerPrincipalSlots (G := G) B j i).card = Fintype.card (B ⟨j, Sum.inr i⟩) :=
  principalCoefficientSlots_card _ _ (Nat.zero_lt_succ _)

theorem layerContinuousPrincipalSlots_not_constant (j : Fin m) (i : I j) :
    constantCoefficientSlot _ (j.val + 1) ∉ layerContinuousPrincipalSlots (G := G) B j i :=
  constantCoefficientSlot_not_principal _ _ (Nat.zero_lt_succ _)

theorem layerIntegerPrincipalSlots_not_constant (j : Fin m) (i : Fin (n j)) :
    constantCoefficientSlot _ (j.val + 1) ∉ layerIntegerPrincipalSlots (G := G) B j i :=
  constantCoefficientSlot_not_principal _ _ (Nat.zero_lt_succ _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SampledCommonBox
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def IsDenseCommonStrideBox {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) (p : ℝ) (A : Finset (I → ℤ)) : Prop :=
  ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ), 0 < m ∧ (∀ i, 0 < H i) ∧
    (∀ i, integerProgressionSupport (c i) m (H i) ⊆ Finset.Ico (0 : ℤ) (N i)) ∧
    (∀ i, Real.exp (-p) * N i ≤ (H i : ℝ)) ∧ A = commonStrideBox c m H

theorem IsDenseCommonStrideBox.nonempty {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p : ℝ} {A : Finset (I → ℤ)} (h : IsDenseCommonStrideBox N p A) :
    A.Nonempty := by
  obtain ⟨c, m, H, hm, hH, _, _, rfl⟩ := h
  exact commonStrideBox_nonempty c hm H hH

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3

theorem IsDenseCommonStrideBox.mono {U : Type*} [Fintype U] [DecidableEq U]
    {N : U → ℕ} {p p' : ℝ} {A : Finset (U → ℤ)}
    (hA : IsDenseCommonStrideBox N p A) (hpp' : p ≤ p') :
    IsDenseCommonStrideBox N p' A := by
  obtain ⟨c, m, H, hm, hH, hinside, hlength, heq⟩ := hA
  refine ⟨c, m, H, hm, hH, hinside, ?_, heq⟩
  intro i
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg hpp')) (Nat.cast_nonneg (N i))).trans (hlength i)

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem commonStrideBox_axis_card (c : I → ℤ) (m : ℕ) (H : I → ℕ)
    (hm : 0 < m) (hH : ∀ i, 0 < H i) (i : I) :
    ((commonStrideBox c m H).image (fun x => x i)).card = H i := by
  classical
  have hnonempty (j : I) : (integerProgressionSupport (c j) m (H j)).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_integerProgressionSupport _ _ _ hm]
    exact hH j
  have hproject := Fintype.eval_image_piFinset
    (fun j => integerProgressionSupport (c j) m (H j)) i (fun j _ => hnonempty j)
  exact (congrArg Finset.card hproject).trans (card_integerProgressionSupport _ _ _ hm)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeSignalAlgebra
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem conjugationPower_next_self (n : ℕ) (z : ℂ) :
    conjugationPower (n + 1) (conjugationPower n z) = star z := by
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn <;> simp [conjugationPower_eq_if_mod, Nat.add_mod, hn]

theorem norm_expect_conjugationPower {X : Type*} (S : Finset X) (n : ℕ) (f : X → ℂ) :
    ‖𝔼 x ∈ S, conjugationPower n (f x)‖ = ‖𝔼 x ∈ S, f x‖ := by
  by_cases hn : n % 2 = 0
  · simp only [conjugationPower_eq_if_mod, hn, ite_true]
  · simp only [conjugationPower_eq_if_mod, hn, ite_false]
    have hs : (𝔼 x ∈ S, star (f x)) = star (𝔼 x ∈ S, f x) := by
      simp [Finset.expect_eq_sum_div_card]
    rw [hs, norm_star]

theorem cubeProduct_swap_head {G : Type*} [AddCommGroup G]
    (f : G → ℂ) (h k : G) (hs : List G) (x : G) :
    cubeProduct f (h :: k :: hs) x = cubeProduct f (k :: h :: hs) x := by
  simp only [cubeProduct_cons_eq_derivative, multiplicativeDerivative_comm f h k]

theorem cubeProduct_comp_addHom {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (f : H → ℂ) (hs : List G) (x : G) :
    cubeProduct (fun y => f (φ y)) hs x = cubeProduct f (hs.map φ) (φ x) := by
  induction hs generalizing x with
  | nil => simp only [cubeProduct_nil, List.map_nil]
  | cons h hs ih => simp only [List.map_cons, cubeProduct_cons, ih, map_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerIntervalCyclicAverage
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem cyclicInterval_zeroExtension_average {N : ℕ} [NeZero N]
    (a len : ℕ) (hbound : a + len ≤ N) (hshort : 2 * ((len : ℤ) - 1) < N)
    (f : ℤ → ℂ) :
    (𝔼 n : ZMod N, finiteIndicator (cyclicInterval (a : ZMod N) len) n * f (n.val : ℤ)) =
      (((len : ℝ) / N : ℝ) : ℂ) * (𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), f n) := by
  let I := cyclicInterval (a : ZMod N) len
  have hrep : (𝔼 n ∈ I, f (n.val : ℤ)) =
      𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), f n := by
    simpa only [finiteCorrelation, one_mul, star_star] using
      cyclicInterval_representative_correlation a len hbound hshort
        (fun _ : ZMod N => (1 : ℂ)) (fun n => star (f n))
  have hstar (n : ZMod N) : star (finiteIndicator I n) = finiteIndicator I n := by
    by_cases hn : n ∈ I <;> simp [finiteIndicator, hn]
  have h := finiteCorrelation_mul_indicator I (fun _ : ZMod N => (1 : ℂ))
    (fun n => star (f (n.val : ℤ)))
  simp only [finiteCorrelation, one_mul, star_mul, star_star, hstar, hrep] at h
  have hcard : I.card = len := cyclicInterval_card _ (by omega)
  simpa only [hcard, ZMod.card, Complex.ofReal_div, Complex.ofReal_natCast, mul_comm] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DenseRowPhaseAlignment
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_row_phase_alignment {G X : Type*} [Fintype G] [Nonempty G]
    (Q : Finset G) (S : Finset X) (f : G → X → ℂ) {δ ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdense : δ * Fintype.card G ≤ (Q.card : ℝ))
    (hcorr : ∀ t ∈ Q, ρ ≤ ‖𝔼 x ∈ S, f t x‖) :
    ∃ w : G → ℂ, (∀ t, ‖w t‖ ≤ 1) ∧ (∀ t, t ∉ Q → w t = 0) ∧
      δ * ρ ≤ (𝔼 t, 𝔼 x ∈ S, w t * f t x).re := by
  classical
  choose c hc hphase using fun t => exists_complex_unit_phase (𝔼 x ∈ S, f t x)
  let w (t : G) := if t ∈ Q then c t else 0
  have hpoint (t : G) : (𝔼 x ∈ S, w t * f t x).re =
      if t ∈ Q then ‖𝔼 x ∈ S, f t x‖ else 0 := by
    rw [← Finset.mul_expect]
    by_cases ht : t ∈ Q
    · simp only [w, ht, ite_true, hphase, Complex.ofReal_re]
    · simp only [w, ht, ite_false, zero_mul, Complex.zero_re]
  have hsum : ρ * (Q.card : ℝ) ≤
      ∑ t : G, if t ∈ Q then ‖𝔼 x ∈ S, f t x‖ else 0 := by
    calc
      _ = ∑ t : G, if t ∈ Q then ρ else 0 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun t _ => by
        by_cases ht : t ∈ Q
        · simpa only [ht, ite_true] using hcorr t ht
        · simp only [ht, ite_false, le_refl]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ Q <;> simp [w, ht, hc]
  · intro t ht
    simp only [w, ht, ite_false]
  · rw [expect_re]
    simp_rw [hpoint]
    rw [Fintype.expect_eq_sum_div_card]
    apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mpr
    calc
      _ = (δ * Fintype.card G) * ρ := by ring
      _ ≤ (Q.card : ℝ) * ρ := mul_le_mul_of_nonneg_right hdense hρ
      _ = ρ * (Q.card : ℝ) := mul_comm _ _
      _ ≤ _ := hsum

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CubeSignalCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def fullCubeSignal {G : Type*} [AddCommGroup G] {d : ℕ}
    (f : G → ℂ) (x : Fin (d + 3) → G) : ℂ :=
  cubeProduct f (List.ofFn (fun j => x ((1 : Fin (d + 3)).succAbove j))) (x 1)

theorem cubeShift_true {G : Type*} [AddCommGroup G] {d : ℕ} (k : Fin d → G) :
    cubeShift k (fun _ => true) = ∑ i, k i := by simp [cubeShift]

theorem cubeShift_congr_selected {G : Type*} [AddCommGroup G] {d : ℕ}
    (k l : Fin d → G) (ω : Fin d → Bool) (h : ∀ i, ω i = true → k i = l i) :
    cubeShift k ω = cubeShift l ω := by
  unfold cubeShift
  apply Finset.sum_congr rfl
  intro i _
  cases hi : ω i with
  | false => simp only [Bool.false_eq_true, ite_false]
  | true => simp only [ite_true]; exact h i hi

theorem fullCube_input_independent {G : Type*} [AddCommGroup G] {d : ℕ}
    (ω : Fin (d + 2) → Bool) (j : Fin (d + 2)) (hj : ω j = false)
    (x y : Fin (d + 3) → G)
    (hxy : ∀ k, k ≠ (1 : Fin (d + 3)).succAbove j → x k = y k) :
    x 1 + cubeShift (fun k => x ((1 : Fin (d + 3)).succAbove k)) ω =
      y 1 + cubeShift (fun k => y ((1 : Fin (d + 3)).succAbove k)) ω := by
  rw [hxy 1 (Fin.ne_succAbove 1 j)]
  congr 1
  apply cubeShift_congr_selected
  intro k hk
  apply hxy
  intro heq
  have hkj : k = j := Fin.succAbove_right_injective heq
  subst k
  simp only [hj, Bool.false_eq_true] at hk

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_mixed_interval_cutoff_weights {d N : ℕ} [NeZero N]
    (I : Finset (ZMod N)) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ)
    (hA : ∀ i x, ‖A i x‖ ≤ 1)
    (hAi : ∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) :
    ∃ B : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ,
      (∀ i x, ‖B i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y) ∧
      (∀ x, (∏ i, B i x) = finiteIndicator I (x 1 : ZMod N) * ∏ i, A i x) := by
  classical
  let B (i : Fin (d + 3)) (x : Fin (d + 3) → ℤ) :=
    (if i = 0 then finiteIndicator I (x 1 : ZMod N) else 1) * A i x
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i x
    by_cases hi : i = 0
    · simp only [B, hi, ite_true, norm_mul]
      exact (mul_le_mul_of_nonneg_right (finiteIndicator_norm_le_one I _)
        (norm_nonneg _)).trans (by simpa only [one_mul] using hA 0 x)
    · simpa only [B, hi, ite_false, one_mul] using hA i x
  · intro i x y hxy
    by_cases hi : i = 0
    · subst i
      simp only [B, ite_true]
      rw [hAi 0 x y hxy, hxy 1 (by
        intro e
        have he := congrArg Fin.val e
        norm_num only [Fin.val_one, Fin.val_zero] at he)]
    · simpa only [B, hi, ite_false, one_mul] using hAi i x y hxy
  · intro x
    simp only [B, Finset.prod_mul_distrib]
    simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev CoveredJetChartSource (O B : Fin m → Type*) (n : Fin m → ℕ) (d : ℕ) :=
  ∀ j, O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop
namespace OAI

universe u

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}

abbrev PairAlgebra (L M : Type u) := ∀ i : Bool, BoolLieFamily L M i

end RationalFilteredNilmanifold

open RationalFilteredNilmanifold

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSlicedIdealDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {B F : D → Type*}
variable [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
variable (hB : ∀ d, 4 ≤ Fintype.card (B d)) (i : ∀ d, F d)

noncomputable def jointSlicedPrincipalDensity (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) (shift : D → ℝ) : ((Σ _d : D, Unit) → ℝ) → ℝ :=
  sigmaAxisWeight (fun d (v : Unit → ℝ) => canonicalSlicedPrincipalDensity (hB d) (i d)
    (c d) (lower d) (width d) (v () - shift d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PiCoordinatePolynomialCoefficients
namespace OAI

section

namespace Erdos3.VectorPolynomial

@[simp] theorem coefficients_ofCoordinates_pi_apply {X K : Type*} [Fintype K]
    (p : K → MvPolynomial X ℝ) (α : X →₀ ℕ) (i : K) :
    coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ K) p) α i =
      (p i).coeff α := by
  have h := congrArg (fun polynomial : MvPolynomial X ℝ => polynomial.coeff α)
    (coordinate_ofCoordinates (R := ℝ) (Pi.basisFun ℝ K) p i)
  rw [coeff_coordinate] at h
  exact h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

noncomputable def lowTaggedVariableEmbedding (d : ℕ) :
    (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ↪ (X ⊕ (Σ j, J j)) :=
  (Function.Embedding.refl X).sumMap ⟨lowTaggedIndex J d, lowTaggedIndex_injective J d⟩

@[simp] theorem lowTaggedVariableEmbedding_inl (d : ℕ) (x : X) :
    lowTaggedVariableEmbedding (X := X) J d (Sum.inl x) = Sum.inl x := rfl

@[simp] theorem lowTaggedVariableEmbedding_inr (d : ℕ)
    (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedVariableEmbedding (X := X) J d (Sum.inr i) =
      Sum.inr (lowTaggedIndex J d i) := rfl

@[simp] theorem lowTaggedVariableEmbedding_weight (d : ℕ)
    (v : X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) :
    fullTaggedVariableWeight J (lowTaggedVariableEmbedding J d v) =
      lowTaggedVariableWeight J d v := by
  cases v <;> rfl

@[simp] theorem lowTaggedVariableEmbedding_slot (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (k : J j) :
    lowTaggedVariableEmbedding (X := X) J d (Sum.inr (lowTaggedSlot J d j hj k)) =
      Sum.inr ⟨j, k⟩ := by
  simp only [lowTaggedVariableEmbedding_inr, lowTaggedIndex_slot]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowestPolynomialLayer
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

namespace PolynomialPatch

variable {σ : Type*} {s D E h : ℕ}

structure LowestLayerModel (A : PolynomialPatch σ s (D + E)) (h : ℕ) where
  matrix : Matrix (Fin D) (Fin D) ℝ
  strict : ∀ i j, i ≤ j → matrix i j = 0
  origin : Fin D → MvPolynomial σ ℝ
  degree : ∀ i, origin i ∈ weightedSupportLE (fun _ : σ => 1) h
  weights : ∀ i : Fin D, A.weight (i.castAdd E) = h
  form_eq : ∀ t : σ → ℝ, (A.form.slots t).takePrefix =
    TriangularSlots.affineBlock matrix strict (fun i => aeval t (origin i))

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFrozenChart
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

theorem freezePolynomial_eval (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    (P : MvPolynomial I R) (x : {i // keep i} → R) :
    eval x (freezePolynomial keep fixed P) = eval (finiteSplitPoint keep x fixed) P := by
  calc
    _ = eval (fun i => eval x (frozenCoordinate keep fixed i)) P :=
      MvPolynomial.comp_aeval_apply _ (MvPolynomial.aeval x) P
    _ = _ := by
      apply congrArg (fun y => eval y P)
      funext i
      by_cases hi : keep i <;> simp [frozenCoordinate, finiteSplitPoint, hi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial BooleanCubeKernel
open scoped BigOperators Classical

theorem integerSampledSpatial_freeze {m : ℕ} {X V : Type*} {J : Fin m → Type*}
    (β : X ⊕ (Σ j, J j) → MvPolynomial V ℤ) (keep : V → Prop)
    (fixed : {i // ¬keep i} → ℤ) (u : {i // keep i} → ℤ) :
    integerSampledSpatial (fun z => freezePolynomial keep fixed (β z)) u =
      integerSampledSpatial β (finiteSplitPoint keep u fixed) := by
  funext i
  exact freezePolynomial_eval keep fixed (β (Sum.inl i)) u

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedSpatialKernelSliceDensity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)

noncomputable def fixedSpatialKernelBlockEquiv (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) : (X → ℝ) ≃L[ℝ] (X → ℝ) :=
  Classical.choose (matrixSupCLM_inverse_spec (fixedSpatialKernelBlock e W L z b) h).1

end Erdos3

end

end OAI
end


