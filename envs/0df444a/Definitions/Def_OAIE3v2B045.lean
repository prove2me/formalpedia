-- Prove2me | Definitions.Def_OAIE3v2B045
-- name    : OAIE3v2B045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:12:24.005094+00:00
-- url     : https://prove2.me/theorems/51c4973f-2d92-4894-b08c-a18e1433b432
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 46 of 311
-- statement:
--   Definitions bundle 46 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B004`, `OAIE3v2B005`, `OAIE3v2B006`, `OAIE3v2B008`, `OAIE3v2B009`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B013` of this split.
--
--   Modules: `Dynamics/AllocatedFixedScaleCollisionBudget.lean`, `Estimates/AllocatedReferenceJetWindow.lean`, `Estimates/AllocatedRowsAmbientProjectedFamilyMultiple.lean`, `Estimates/BooleanCubeProduct.lean`, `Estimates/BufferedSiteExpansion.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/FiniteInnerProgressionFamily.lean`, `Estimates/IteratedCircleAverageIntegral.lean`, `Estimates/LinearQuotientCoverAverage.lean`, `Estimates/LowJetAmbientReconstruction.lean`, `Estimates/NativePhysicalHaarExpansion.lean`, `Estimates/PhysicalCubeNativeDetection.lean`, `Estimates/PhysicalRowsSiteReconstruction.lean`, `Estimates/QuantitativeNoninjectivity.lean`, `Estimates/RationalRowReduction.lean`, `Estimates/SampledCommonSlice.lean`, `Estimates/SiteTwistCommonModulus.lean`, `Estimates/VectorCoefficientScaling.lean`, `FixedDensity/OrderedRemoval.lean`, `Fourier/CommonCoveredSiteCharacter.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/RectangularGridCharacter.lean`, `Fourier/SiteFourierHaarMean.lean`, `Fourier/TorusCircleActions.lean`, `Geometry/CoordinateProductCap.lean`, `Geometry/NativeTernaryCoordinate.lean`, `Geometry/PhysicalNormalizedSpatialFactor.lean`, `Geometry/PhysicalSpatialScales.lean`, `Geometry/PhysicalSupportedCubes.lean`, `Geometry/RelativePatchBoxRestriction.lean`, `Geometry/SupportedCubeEquivTransport.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/AffineOneSiteNormalizedLaw.lean`, `Lattices/CommonIntegerSiteResidual.lean`, `Lattices/IntegerBoxObservedMean.lean`, `Lattices/IntegerColumnMinor.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/PhysicalResidueOffsetShift.lean`, `Lattices/PhysicalResidueWindowSiteMask.lean`, `Lattices/PhysicalSpatialResidueSupport.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/RoundedAffineLifts.lean`, `Lattices/SmoothResidueWindowMass.lean`, `Linear/CircleFejerKernel.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Probability/AllocatedReferenceJetMass.lean`, `Probability/ComplexPartitionMixture.lean`, `Probability/DensityMixtureAELaw.lean`, `Probability/DiagonalImageDensity.lean`, `Probability/FiniteDensityMassBound.lean`, `Probability/PairedProductDensity.lean`, `Probability/SampledWeightCellLaw.lean`, `Probability/ShiftedSmoothLawBounds.lean`, `Probability/SlicedRemainderDensityFamily.lean`, `Probability/SmoothProbabilityProfile.lean`, `Probability/UniformSelectedCoefficientProductLaw.lean`, `Sampling/AmbientL1SamplingBudget.lean`, `Sampling/FrozenPartitionScore.lean`, `Sampling/JointMeasureProductiveNarrowSampler.lean`.
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
import Definitions.Def_OAIE3v2B006
import Definitions.Def_OAIE3v2B008
import Definitions.Def_OAIE3v2B009
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B013

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem siteFactorTensor_factor_lipschitz {D U : Type*} [Fintype D] [PseudoMetricSpace U]
    (f : D → U → ℂ) {K : ℝ≥0} (hf : ∀ d, LipschitzWith K (f d))
    (hn : ∀ d x, ‖f d x‖ ≤ 1) :
    LipschitzWith (Fintype.card D * K) (fun x : D → U => ∏ d, f d (x d)) := by
  have hcoord (d : D) : LipschitzWith K (fun x : D → U => f d (x d)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hf d).dist_le_mul _ _ |>.trans (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y d) K.coe_nonneg)
  simpa only [one_pow, mul_one] using
    (bounded_lipschitz_fintype_prod (fun d (x : D → U) => f d (x d))
      (B := 1) le_rfl hcoord (fun d x => hn d (x d))).2

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

theorem conjugationPower_star (n : ℕ) (z : ℂ) :
    conjugationPower n (star z) = star (conjugationPower n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change star (conjugationPower n (star z)) = star (star (conjugationPower n z))
    exact congrArg star ih

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

@[simp] theorem booleanWeight_cons_false {j : ℕ} (ω : Fin j → Bool) :
    booleanWeight (Fin.cons false ω) = booleanWeight ω := by
  unfold booleanWeight
  rw [Fin.sum_univ_succ]
  simp

@[simp] theorem booleanWeight_cons_true {j : ℕ} (ω : Fin j → Bool) :
    booleanWeight (Fin.cons true ω) = booleanWeight ω + 1 := by
  unfold booleanWeight
  rw [Fin.sum_univ_succ]
  simp [Nat.add_comm]

variable {H : Type*} [AddCommGroup H]

def mixedCubeProduct {j : ℕ} (F : (Fin j → Bool) → H → ℂ) (hs : Fin j → H) (x : H) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω) (F ω (x + cubeShift hs ω))

@[simp] theorem mixedCubeProduct_zero (F : (Fin 0 → Bool) → H → ℂ)
    (hs : Fin 0 → H) (x : H) : mixedCubeProduct F hs x = F default x := by
  unfold mixedCubeProduct
  rw [Fintype.prod_subsingleton _ (default : Fin 0 → Bool)]
  simp [booleanWeight, cubeShift, conjugationPower]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

theorem integerDistance_le_half (x : Circle) : integerDistance x ≤ 1 / 2 := by
  simpa [integerDistance] using AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero (x := x)

end
end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FrozenPartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

theorem sum_partitionCell (cell : Ω → ι) (f : Ω → ℝ) :
    (∑ i, ∑ x ∈ partitionCell cell i, f x) = ∑ x, f x := by
  classical
  simp only [partitionCell, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem card_partitionCell_sum (cell : Ω → ι) :
    (∑ i, ((partitionCell cell i).card : ℝ)) = (Fintype.card Ω : ℝ) := by
  simpa using sum_partitionCell cell (fun _ => 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

def SlotAffine [Fintype τ] (h : ℕ) (p : MvPolynomial (σ ⊕ τ) R) : Prop :=
  ∃ (C₀ : MvPolynomial σ R) (m : τ → R),
    C₀ ∈ weightedSupportLE (fun _ : σ => 1) h ∧
    ∀ (t : σ → R) (x : τ → R),
      aeval (Sum.elim t x) p = aeval t C₀ + ∑ j, m j * x j

namespace SlotAffine

variable [Fintype τ] {h : ℕ}

theorem add {p q : MvPolynomial (σ ⊕ τ) R}
    (hp : SlotAffine h p) (hq : SlotAffine h q) : SlotAffine h (p + q) := by
  obtain ⟨Cp, mp, hCp, heqp⟩ := hp
  obtain ⟨Cq, mq, hCq, heqq⟩ := hq
  refine ⟨Cp + Cq, mp + mq, (weightedSupportLE _ _).add_mem hCp hCq, ?_⟩
  intro t x
  simp only [map_add, heqp, heqq, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  abel

end SlotAffine

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

theorem SupportedCube.points_injective (j : ℕ) (Q : Set A) :
    Function.Injective (SupportedCube.points : SupportedCube j Q → _) := by
  intro p q he
  have hx : p.val.2 = q.val.2 := congrArg (fun r ↦ r.1.val) he
  have hd (i : Fin j) : p.val.1 i = q.val.1 i := by
    have hi : p.val.2 + p.val.1 i = q.val.2 + q.val.1 i :=
      congrArg (fun r ↦ (r.2 i).val) he
    rw [hx] at hi
    exact add_left_cancel hi
  apply Subtype.ext
  exact Prod.ext (funext hd) hx

instance supportedCubeFinite (j : ℕ) (Q : Set A) [Finite Q] : Finite (SupportedCube j Q) :=
  Finite.of_injective SupportedCube.points (SupportedCube.points_injective j Q)

noncomputable instance supportedCubeFintype (j : ℕ) (Q : Set A) [Finite Q] :
    Fintype (SupportedCube j Q) := Fintype.ofFinite _

noncomputable def supportedCubeSum (j : ℕ) (Q : Set A) [Finite Q]
    (F : (Fin j → Bool) → A → ℂ) : ℂ :=
  ∑ p : SupportedCube j Q, mixedCubeProduct F p.val.1 p.val.2

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

noncomputable def finiteSupportGowersNorm (j : ℕ) (Q : Finset A) (f : A → ℂ) : ℝ :=
  ((supportedCubeSum j (Q : Set A) (fun _ ↦ f)).re /
    Nat.card (SupportedCube j (Q : Set A))) ^ (((2 ^ j : ℕ) : ℝ)⁻¹)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ComplexPartitionMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_partitionCell_complex {X K : Type*} [Fintype X] [Fintype K]
    (cell : X → K) (f : X → ℂ) :
    (∑ k, ∑ x ∈ partitionCell cell k, f x) = ∑ x, f x := by
  classical
  simp only [partitionCell, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem complex_expect_partition_mixture {X K : Type*} [Fintype X] [Fintype K]
    (cell : X → K) (f : X → ℂ) :
    (𝔼 x, f x) = ∑ k, ((partitionCell cell k).card : ℂ) / Fintype.card X *
      (𝔼 x ∈ partitionCell cell k, f x) := by
  classical
  have hcell (k : K) : ((partitionCell cell k).card : ℂ) / Fintype.card X *
      (𝔼 x ∈ partitionCell cell k, f x) =
      (∑ x ∈ partitionCell cell k, f x) / Fintype.card X := by
    rw [Finset.expect_eq_sum_div_card]
    by_cases hc : (partitionCell cell k).card = 0
    · have hempty := Finset.card_eq_zero.mp hc
      simp only [hempty, Finset.card_empty, Nat.cast_zero, Finset.sum_empty, zero_div, mul_zero]
    · have hc' : ((partitionCell cell k).card : ℂ) ≠ 0 := by exact_mod_cast hc
      calc
        _ = (((partitionCell cell k).card : ℂ) / (partitionCell cell k).card) *
            ((∑ x ∈ partitionCell cell k, f x) / Fintype.card X) := by ring
        _ = _ := by rw [div_self hc', one_mul]
  simp_rw [hcell]
  rw [← Finset.sum_div, sum_partitionCell_complex, Fintype.expect_eq_sum_div_card]

theorem complex_expect_partition_count_weights {X K : Type*} [Fintype X] [Fintype K]
    (cell : X → K) (f : X → ℂ) :
    (𝔼 x, f x) = ∑ k,
      (((partitionCell cell k).card : ℝ) / (∑ j, ((partitionCell cell j).card : ℝ)) : ℂ) *
      (𝔼 x ∈ partitionCell cell k, f x) := by
  rw [card_partitionCell_sum]
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using complex_expect_partition_mixture cell f

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

theorem card_integerBox (T : ι → ℕ) : (integerBox T).card = ∏ i, T i := by
  simp [integerBox]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerColumnMinor
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integerCramerSolution_height (A : Matrix ι ι ℤ) (b : ι → ℤ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H) (i : ι) :
    RationalHeightLE
      (rationalCramerSolution (A.map (Int.castRingHom ℚ)) (fun j => (b j : ℚ)) i)
      ((Fintype.card ι).factorial * H ^ Fintype.card ι) := by
  rw [integerCramerSolution_apply]
  exact rationalHeightLE_fraction _ _ hdet (integer_cramer_natAbs_le A b hA hb i)
    (integer_det_natAbs_le A hA)

theorem exists_bounded_integer_system_solution (A : Matrix ι ι ℤ) (b : ι → ℤ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H) :
    ∃ x : ι → ℚ, (A.map (Int.castRingHom ℚ)) *ᵥ x = (fun i => (b i : ℚ)) ∧
      ∀ i, RationalHeightLE (x i)
        ((Fintype.card ι).factorial * H ^ Fintype.card ι) := by
  refine ⟨rationalCramerSolution _ _, rationalCramerSolution_solves _ _ ?_,
    integerCramerSolution_height A b hdet hA hb⟩
  have h : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det A).symm
  rw [h]
  exact_mod_cast hdet

end Erdos3

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

theorem exists_bounded_rational_system_solution (A : Matrix ι ι ℚ) (b : ι → ℚ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hb : ∀ i, RationalHeightLE (b i) H) :
    ∃ x : ι → ℚ, A *ᵥ x = b ∧
      ∀ i, RationalHeightLE (x i) (rationalSolveHeight (Fintype.card ι) H) := by
  let q : (ι × ι) ⊕ ι → ℚ := Sum.elim (fun p => A p.1 p.2) b
  have hq : ∀ u, RationalHeightLE (q u) H := by
    intro u
    cases u with
    | inl p => exact hA p.1 p.2
    | inr i => exact hb i
  obtain ⟨D, hDpos, _, a, ha, hbound⟩ := exists_bounded_integer_array q hq
  let Z : Matrix ι ι ℤ := fun i j => a (.inl (i, j))
  let c : ι → ℤ := fun i => a (.inr i)
  have hD : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hZ : Z.map (Int.castRingHom ℚ) = (D : ℚ) • A := by
    ext i j
    exact ha (.inl (i, j))
  have hc : (fun i => (c i : ℚ)) = (D : ℚ) • b := by
    funext i
    exact ha (.inr i)
  have hZdet : Z.det ≠ 0 := by
    have hcast : (Z.det : ℚ) = (D : ℚ) ^ Fintype.card ι * A.det := by
      calc
        (Z.det : ℚ) = (Z.map (Int.castRingHom ℚ)).det :=
          (Int.castRingHom ℚ).map_det Z
        _ = _ := by rw [hZ, Matrix.det_smul]
    have hn := mul_ne_zero (pow_ne_zero (Fintype.card ι) hD) hdet
    rw [← hcast] at hn
    exact_mod_cast hn
  have hZA : ∀ i j, (Z i j).natAbs ≤ H ^ (Fintype.card ι * Fintype.card ι +
      Fintype.card ι) := by
    intro i j
    simpa only [Fintype.card_sum, Fintype.card_prod] using hbound (.inl (i, j))
  have hcA : ∀ i, (c i).natAbs ≤ H ^ (Fintype.card ι * Fintype.card ι +
      Fintype.card ι) := by
    intro i
    simpa only [Fintype.card_sum, Fintype.card_prod] using hbound (.inr i)
  obtain ⟨x, hx, hxH⟩ := exists_bounded_integer_system_solution Z c hZdet hZA hcA
  refine ⟨x, ?_, hxH⟩
  rw [hZ, hc, Matrix.smul_mulVec] at hx
  funext i
  have hi := congrFun hx i
  change (D : ℚ) * (A *ᵥ x) i = (D : ℚ) * b i at hi
  exact mul_left_cancel₀ hD hi

theorem rationalCramerSolution_height (A : Matrix ι ι ℚ) (b : ι → ℚ)
    (hdet : A.det ≠ 0) {H : ℕ} (hA : ∀ i j, RationalHeightLE (A i j) H)
    (hb : ∀ i, RationalHeightLE (b i) H) (i : ι) :
    RationalHeightLE (rationalCramerSolution A b i)
      (rationalSolveHeight (Fintype.card ι) H) := by
  obtain ⟨x, hx, hheight⟩ := exists_bounded_rational_system_solution A b hdet hA hb
  rw [← rationalCramerSolution_unique A b x hdet hx]
  exact hheight i

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

theorem realDensityMeasure_apply {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) {s : Set X} (hs : MeasurableSet s) :
    realDensityMeasure μ f s = ENNReal.ofReal (∫ x in s, f x ∂μ) := by
  rw [realDensityMeasure, withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hf0)).symm

theorem realDensityMeasure_probability {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1) :
    IsProbabilityMeasure (realDensityMeasure μ f) := by
  constructor
  rw [realDensityMeasure_apply μ f hf hf0 MeasurableSet.univ, Measure.restrict_univ,
    hmass, ENNReal.ofReal_one]

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
open scoped NNReal

theorem densityMixture_joint_integrable {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [IsProbabilityMeasure μ] [SFinite ν]
    (F : T → X → ℝ) (hm : Measurable (Function.uncurry F))
    (hF : ∀ᵐ t ∂μ, (∀ x, 0 ≤ F t x) ∧ Integrable (F t) ν ∧ (∫ x, F t x ∂ν) = 1) :
    Integrable (Function.uncurry F) (μ.prod ν) := by
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨hF.mono (fun _ ht => ht.2.1), ?_⟩
  apply (integrable_const (1 : ℝ)).congr
  filter_upwards [hF] with t ht
  simp only [Function.uncurry_apply_pair, Real.norm_of_nonneg (ht.1 _)]
  exact ht.2.2.symm

theorem densityMixture_probability_density {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [IsProbabilityMeasure μ] [SFinite ν]
    (F : T → X → ℝ) (hm : Measurable (Function.uncurry F))
    (hF : ∀ᵐ t ∂μ, (∀ x, 0 ≤ F t x) ∧ Integrable (F t) ν ∧ (∫ x, F t x ∂ν) = 1) :
    (∀ x, 0 ≤ densityMixture μ F x) ∧ Integrable (densityMixture μ F) ν ∧
      (∫ x, densityMixture μ F x ∂ν) = 1 := by
  have hi := densityMixture_joint_integrable μ ν F hm hF
  refine ⟨fun x => integral_nonneg_of_ae (hF.mono (fun _ ht => ht.1 x)),
    hi.integral_prod_right, ?_⟩
  change (∫ x, ∫ t, F t x ∂μ ∂ν) = 1
  rw [← integral_integral_swap hi]
  calc
    (∫ t, ∫ x, F t x ∂ν ∂μ) = ∫ _, (1 : ℝ) ∂μ :=
      integral_congr_ae (hF.mono (fun _ ht => ht.2.2))
    _ = 1 := by simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

theorem haarShiftDensity_probability (μ : Measure G) [μ.IsAddLeftInvariant]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    [SFinite μ] (hfi : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1) :
    (∀ x, 0 ≤ haarShiftDensity ν z f x) ∧ Integrable (haarShiftDensity ν z f) μ ∧
      (∫ x, haarShiftDensity ν z f x ∂μ) = 1 := by
  apply densityMixture_probability_density ν μ _
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · exact ae_of_all ν (fun t => ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem realDensityMeasure_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℝ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, f x * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]

theorem realDensityMeasure_finite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    IsFiniteMeasure (realDensityMeasure μ f) := by
  constructor
  rw [realDensityMeasure_apply μ f hf hf0 MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top

theorem mappedTest_eq_density {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ν : Measure X) (U : Ω → X) (hU : Measurable U)
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hmap : Measure.map U μ = realDensityMeasure ν f)
    (φ : X → ℝ) (hφ : Measurable φ) : mappedTest μ U φ = ∫ x, f x * φ x ∂ν := by
  change (∫ a, φ (U a) ∂μ) = _
  rw [← integral_map hU.aemeasurable hφ.aestronglyMeasurable, hmap,
    realDensityMeasure_integral ν f hf hf0]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SmoothProbabilityProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff

theorem smoothProbabilityProfile_pos_zero : 0 < smoothProbabilityProfile 0 := by
  have h : probabilityProfileBump 0 = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simp [probabilityProfileBump])
  change 0 < probabilityProfileBump 0 / ∫ x, probabilityProfileBump x
  rw [h]
  exact one_div_pos.mpr probabilityProfileBump.integral_pos

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
open scoped BigOperators

theorem realDensityMeasure_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (f : X → ℝ) :
    Measure.map e (realDensityMeasure μ f) =
      realDensityMeasure (Measure.map e μ) (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, realDensityMeasure, realDensityMeasure,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    e.restrict_map, e.measurableEmbedding.lintegral_map]
  simp only [e.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem densityMixture_mappedTest {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U : T × Ω → X) (hU : Measurable U) (D : T → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hprob : ∀ t, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ξ ∧ (∫ x, D t x ∂ξ) = 1)
    (hlaw : ∀ t, ν.map (fun a => U (t, a)) = realDensityMeasure ξ (D t))
    (φ : X → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    mappedTest (μ.prod ν) U φ = ∫ x, densityMixture μ D x*φ x ∂ξ := by
  have hi : Integrable (fun p => φ (U p)) (μ.prod ν) :=
    (integrable_const C).mono' (hφ.comp hU).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound (U p)))
  change (∫ p, φ (U p) ∂μ.prod ν) = _
  rw [integral_prod _ hi, densityMixture_test_integral μ ξ D
    (densityMixture_joint_integrable μ ξ D hD (Filter.Eventually.of_forall hprob)) φ hφ hbound]
  apply integral_congr_ae
  filter_upwards [] with t
  exact mappedTest_eq_density ν ξ (fun a => U (t, a))
    (hU.comp (measurable_const.prodMk measurable_id)) (D t)
    (hD.comp (measurable_const.prodMk measurable_id)) (hprob t).1 (hlaw t) φ hφ

theorem densityMixture_image_law {T Ω X : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure Ω) (ξ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SFinite ξ]
    (U : T × Ω → X) (hU : Measurable U) (D : T → X → ℝ)
    (hD : Measurable (Function.uncurry D))
    (hprob : ∀ t, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ξ ∧ (∫ x, D t x ∂ξ) = 1)
    (hlaw : ∀ t, ν.map (fun a => U (t, a)) = realDensityMeasure ξ (D t)) :
    (μ.prod ν).map U = realDensityMeasure ξ (densityMixture μ D) := by
  have hp := densityMixture_probability_density μ ξ D hD (Filter.Eventually.of_forall hprob)
  have hm : Measurable (densityMixture μ D) :=
    hD.stronglyMeasurable.integral_prod_left'.measurable
  let : IsProbabilityMeasure ((μ.prod ν).map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  let : IsFiniteMeasure (realDensityMeasure ξ (densityMixture μ D)) :=
    realDensityMeasure_finite ξ _ hp.2.1 hp.1
  ext s hs
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hb : ∀ x, ‖s.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  have ht := densityMixture_mappedTest μ ν ξ U hU D hD hprob hlaw
    (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs) hb
  have himage : mappedTest (μ.prod ν) U (s.indicator (fun _ => (1 : ℝ))) =
      ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂(μ.prod ν).map U :=
    (integral_map hU.aemeasurable (measurable_const.indicator hs).aestronglyMeasurable).symm
  rw [himage, ← realDensityMeasure_integral ξ _ hm hp.1] at ht
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using ht

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

omit [MeasurableNeg G] in
theorem realDensityMeasure_map_add_right (μ : Measure G) [μ.IsAddLeftInvariant]
    (f : G → ℝ) (a : G) :
    (realDensityMeasure μ f).map (fun u => u + a) =
      realDensityMeasure μ (fun y => f (y - a)) := by
  have h := realDensityMeasure_map_equiv (MeasurableEquiv.addRight a) μ f
  simpa only [MeasurableEquiv.symm_addRight, MeasurableEquiv.coe_addRight,
    map_add_right_eq_self, sub_eq_add_neg] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedSmoothLawBounds
namespace OAI

section

namespace Erdos3

theorem smoothSamplingScale_pos {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) : 0 < S := by
  have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  linarith

theorem shiftedSmoothSampleSum_bounds (a : ℝ) {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) :
    S / 2 ≤ shiftedSmoothSampleSum a S ∧ shiftedSmoothSampleSum a S ≤ 3 * S / 2 := by
  have hA : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hS1 : 1 ≤ S := by linarith
  have hS0 := smoothSamplingScale_pos hS
  have he := shiftedSmoothSampleSum_error a hS1
  have hsmall : 4 * (probabilityProfileLipschitz : ℝ) / S ≤ 1 / 2 :=
    (div_le_iff₀ hS0).mpr (by linarith)
  have hb := abs_le.mp (he.trans hsmall)
  have hlo : (1 / 2 : ℝ) ≤ shiftedSmoothSampleSum a S / S := by linarith [hb.1]
  have hhi : shiftedSmoothSampleSum a S / S ≤ (3 / 2 : ℝ) := by linarith [hb.2]
  constructor
  · linarith [(le_div_iff₀ hS0).mp hlo]
  · linarith [(div_le_iff₀ hS0).mp hhi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped ENNReal Classical

theorem pmf_map_injective_cap {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) {C : ℝ≥0∞} (hp : ∀ x, p x ≤ C) (y : Y) :
    p.map f y ≤ C := by
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    rw [pmf_map_injective_at p f hf]
    exact hp x
  · rw [pmf_map_zero_off_range p f y hy]
    exact bot_le

theorem pmf_bind_injective_toReal_cap {X Y Z : Type*} (p : PMF X) (q : PMF Y)
    (f : Y → X → Z) (hf : ∀ y, Function.Injective (f y))
    {C : ℝ} (hC : 0 ≤ C) (hp : ∀ x, (p x).toReal ≤ C) (z : Z) :
    ((q.bind (fun y => p.map (f y))) z).toReal ≤ C := by
  have hp' (x : X) : p x ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal (p.apply_ne_top x)]
    exact ENNReal.ofReal_le_ofReal (hp x)
  have h := pmf_bind_point_cap q (fun y => p.map (f y)) z
    (fun y => pmf_map_injective_cap p (f y) (hf y) hp' z)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hC)

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

lemma fejer_pair_sum_eq (N : ℕ) (x : Circle) :
    ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) =
      (∑ j : Fin N, character ((j.val : ℤ) • x)) *
        (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) := by
  calc
    _ = ∑ j : Fin N, ∑ k : Fin N,
        character (fejerPairFrequency (j, k) • x) := by
      exact Fintype.sum_prod_type (γ := ℂ)
        (fun p : Fin N × Fin N => character (fejerPairFrequency p • x))
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← character_add]
      congr 2
      simp only [fejerPairFrequency, sub_eq_add_neg, add_smul]

lemma fejer_neg_sum_eq_conj (N : ℕ) (x : Circle) :
    (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) =
      star (∑ k : Fin N, character ((k.val : ℤ) • x)) := by
  change (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) =
    (starRingEnd ℂ) (∑ k : Fin N, character ((k.val : ℤ) • x))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change AddCircle.toCircle ((-(k.val : ℤ)) • x) =
    (starRingEnd ℂ) (AddCircle.toCircle ((k.val : ℤ) • x))
  rw [neg_smul, AddCircle.toCircle_neg]
  exact _root_.Circle.coe_inv_eq_conj _

lemma fejer_fiber_card_le (N : ℕ) (h : ℤ) :
    (Finset.univ.filter fun p : Fin N × Fin N =>
      fejerPairFrequency p = h).card ≤ N := by
  let s := Finset.univ.filter fun p : Fin N × Fin N => fejerPairFrequency p = h
  calc
    s.card ≤ (Finset.univ : Finset (Fin N)).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        exact Finset.mem_univ _
      · intro p hp q hq hpq
        apply Prod.ext hpq
        apply Fin.ext
        have hpf := (Finset.mem_filter.mp hp).2
        have hqf := (Finset.mem_filter.mp hq).2
        unfold fejerPairFrequency at hpf hqf
        omega
    _ = N := by simp

lemma fejerCoefficient_nonneg (N : ℕ) (h : ℤ) :
    0 ≤ fejerCoefficient N h := by
  unfold fejerCoefficient
  positivity

lemma fejerCoefficient_le_one {N : ℕ} (hN : 0 < N) (h : ℤ) :
    fejerCoefficient N h ≤ 1 := by
  unfold fejerCoefficient
  rw [div_le_one (Nat.cast_pos.mpr hN)]
  exact_mod_cast fejer_fiber_card_le N h

end
end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCircleActions
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped BigOperators

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]
  [AddAction (ι → Circle) X] [ContinuousVAdd (ι → Circle) X]

def torusCoordinateAction (hact : ∀ t : ι → Circle, Isometry (fun x : X => t +ᵥ x))
    (i : ι) : IsometricCircleAction X where
  act t x := (Pi.single i t : ι → Circle) +ᵥ x
  zero_act x := by simp
  add_act t u x := by simp only [Pi.single_add, add_vadd]
  continuous_act := by
    have hs : Continuous (fun p : Circle × X => (Pi.single i p.1 : ι → Circle)) := by
      apply continuous_pi
      intro j
      by_cases h : j = i
      · subst j
        simpa only [Pi.single_eq_same] using (continuous_fst : Continuous (fun p : Circle × X => p.1))
      · simpa only [Pi.single_eq_of_ne h] using
          (continuous_const : Continuous (fun _p : Circle × X => (0 : Circle)))
    exact hs.vadd continuous_snd
  isometry_act t := hact (Pi.single i t)

omit [Fintype ι] in
theorem torusCoordinateAction_commutes
    (hact : ∀ t : ι → Circle, Isometry (fun x : X => t +ᵥ x)) (i j : ι) :
    (torusCoordinateAction hact i).Commutes (torusCoordinateAction hact j) := by
  intro t u x
  change (Pi.single i t : ι → Circle) +ᵥ ((Pi.single j u : ι → Circle) +ᵥ x) =
    (Pi.single j u : ι → Circle) +ᵥ ((Pi.single i t : ι → Circle) +ᵥ x)
  rw [← add_vadd, ← add_vadd, add_comm]

omit [PseudoMetricSpace X] [ContinuousVAdd (ι → Circle) X] in

theorem torus_character_of_coordinate_characters (f : X → ℂ) (n : ι → ℤ)
    (hf : ∀ (i : ι) (t : Circle) x,
      f ((Pi.single i t : ι → Circle) +ᵥ x) = character (n i • t) * f x)
    (t : ι → Circle) (x : X) :
    f (t +ᵥ x) = (∏ i, character (n i • t i)) * f x := by
  have hs (s : Finset ι) : ∀ x, f ((∑ i ∈ s, Pi.single i (t i) : ι → Circle) +ᵥ x) =
      (∏ i ∈ s, character (n i • t i)) * f x := by
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | @insert i s hi ih =>
      intro x
      rw [Finset.sum_insert hi, add_vadd, hf, ih, Finset.prod_insert hi, mul_assoc]
  simpa only [Finset.univ_sum_single] using hs Finset.univ x

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorCoefficientScaling
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem DegreeLE.smul {I V : Type*} [AddCommGroup V] [Module ℝ V]
    {w : I → ℕ} {d : ℕ} {p : VectorPolynomial I ℝ V}
    (hp : DegreeLE w d p) (r : ℝ) : DegreeLE w d (r • p) := by
  intro α hα
  simp only [map_smul, Finsupp.smul_apply, hp α hα, smul_zero]

theorem coefficients_smul_mem {I J : Type*} (U : Submodule ℝ (J → ℝ))
    (p : VectorPolynomial I ℝ (J → ℝ)) (hm : ∀ d, coefficients p d ∈ U) (r : ℝ) :
    ∀ d, coefficients (r • p) d ∈ U := by
  intro d
  simpa only [map_smul, Finsupp.smul_apply] using U.smul_mem r (hm d)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def relativeBoxInput {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (x : X → ℤ) : ℝ :=
  if x ∈ integerBox N then f x else 0

@[simp] theorem relativeBoxInput_eq {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) {x : X → ℤ} (hx : x ∈ integerBox N) :
    relativeBoxInput N f x = f x := by
  simp only [relativeBoxInput, if_pos hx]

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

theorem finiteDensityMass_eq_div {X : Type*} (w D : X → ℝ) :
    finiteDensityMass w D = (∑' x, w x * D x) / ∑' x, w x := by
  simp only [finiteDensityMass, div_mul_eq_mul_div, tsum_div_const]

theorem finiteDensityMass_complex {X : Type*} (w D : X → ℝ) :
    (finiteDensityMass w D : ℂ) = ∑' x, ((w x / ∑' y, w y : ℝ) : ℂ) * (D x : ℂ) := by
  simp only [finiteDensityMass, Complex.ofReal_tsum, Complex.ofReal_mul]

theorem finiteDensityMass_raw_pos {X : Type*} (w D : X → ℝ)
    (hw : 0 < ∑' x, w x) (hD : 0 < finiteDensityMass w D) :
    0 < ∑' x, w x * D x := by
  have he := (eq_div_iff hw.ne').mp (finiteDensityMass_eq_div w D)
  rw [← he]
  exact mul_pos hD hw

noncomputable def finiteDensityTiltPMF {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < finiteDensityMass w D) : PMF X :=
  realWeightPMF (fun x => w x * D x) (fun x => mul_nonneg (hw0 x) (hD0 x))
    (hasSum_sum_of_ne_finset_zero (s := S) (fun x hx => by rw [hw x hx, zero_mul])).summable
    (finiteDensityMass_raw_pos w D hZ hD)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteDensityMass_sum_le_of_weight_lower {X : Type*}
    (w D : X → ℝ) (support window : Finset X)
    (hw : ∀ x, 0 ≤ w x) (hoff : ∀ x ∉ support, w x = 0)
    (hD : ∀ x, 0 ≤ D x) (hZ : 0 < ∑' x, w x)
    {b : ℝ} (hb : 0 < b) (hlower : ∀ x ∈ window, b ≤ w x) :
    (∑ x ∈ window, D x) ≤ ((∑' x, w x) / b) * finiteDensityMass w D := by
  classical
  have hsub : window ⊆ support := by
    intro x hx
    by_contra h
    have hh := hlower x hx
    rw [hoff x h] at hh
    exact (not_le_of_gt hb) hh
  have hsum : (∑' x, w x * D x) = ∑ x ∈ support, w x * D x :=
    tsum_eq_sum (fun x hx => by rw [hoff x hx, zero_mul])
  have hbound : b * (∑ x ∈ window, D x) ≤ ∑' x, w x * D x := by
    rw [hsum, Finset.mul_sum]
    apply (Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right (hlower x hx) (hD x))).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => mul_nonneg (hw x) (hD x))
  have he : finiteDensityMass w D * (∑' x, w x) = ∑' x, w x * D x :=
    (eq_div_iff hZ.ne').mp (finiteDensityMass_eq_div w D)
  rw [← he] at hbound
  calc
    (∑ x ∈ window, D x) ≤ (finiteDensityMass w D * (∑' x, w x)) / b :=
      (le_div_iff₀ hb).mpr (by simpa only [mul_comm b] using hbound)
    _ = ((∑' x, w x) / b) * finiteDensityMass w D := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem smoothProbabilityProfile_plateau (x : ℝ) (hx : |x| ≤ 1 / 2) :
    smoothProbabilityProfile x = smoothProbabilityProfile 0 := by
  have hx' : probabilityProfileBump x = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simpa [probabilityProfileBump, Real.dist_eq] using hx)
  have h0 : probabilityProfileBump 0 = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simp [probabilityProfileBump])
  simp only [smoothProbabilityProfile, ContDiffBump.normed_def, hx', h0]

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

theorem norm_expect_subset_sub_le {X : Type*} [DecidableEq X]
    (A B : Finset X) (hA : A.Nonempty) (hAB : A ⊆ B)
    (f : X → ℂ) (hf : ∀ x ∈ B, ‖f x‖ ≤ 1) :
    ‖(𝔼 x ∈ A, f x) - 𝔼 x ∈ B, f x‖ ≤ 2 * (1 - (A.card : ℝ) / B.card) := by
  have hB : B.Nonempty := hA.mono hAB
  have hB0 : (B.card : ℂ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  have hBR : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hmean := norm_finset_expect_le_one A f (fun x hx => hf x (hAB hx))
  have hsum : (∑ x ∈ B \ A, f x) + ∑ x ∈ A, f x = ∑ x ∈ B, f x :=
    Finset.sum_sdiff hAB
  have hc : ((B \ A).card : ℂ) + (A.card : ℂ) = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hAB
  have heq : (𝔼 x ∈ A, f x) - 𝔼 x ∈ B, f x =
      (∑ x ∈ B \ A, ((𝔼 a ∈ A, f a) - f x)) / (B.card : ℂ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [sub_div, mul_div_assoc, Finset.expect_eq_sum_div_card B]
    have hAeq := Finset.card_mul_expect A f
    field_simp
    linear_combination hAeq + hsum - (𝔼 a ∈ A, f a) * hc
  have hnorm : ‖∑ x ∈ B \ A, ((𝔼 a ∈ A, f a) - f x)‖ ≤
      2 * ((B \ A).card : ℝ) := by
    calc
      _ ≤ ∑ x ∈ B \ A, ‖(𝔼 a ∈ A, f a) - f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ B \ A, (2 : ℝ) := Finset.sum_le_sum (fun x hx =>
        (norm_sub_le _ _).trans (by linarith [hf x (Finset.mem_sdiff.mp hx).1]))
      _ = _ := by simp [mul_comm]
  rw [heq, norm_div, Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right hnorm hBR.le).trans_eq
  have hcR : ((B \ A).card : ℝ) + (A.card : ℝ) = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hAB
  field_simp
  nlinarith

theorem norm_expect_injective_sub_le {X Y : Type*} [DecidableEq Y]
    (A : Finset X) (B : Finset Y) (hA : A.Nonempty) (g : X → Y)
    (hg : Set.InjOn g A) (hB : ∀ x ∈ A, g x ∈ B)
    (f : Y → ℂ) (hf : ∀ y ∈ B, ‖f y‖ ≤ 1) :
    ‖(𝔼 x ∈ A, f (g x)) - 𝔼 y ∈ B, f y‖ ≤ 2 * (1 - (A.card : ℝ) / B.card) := by
  have h := norm_expect_subset_sub_le (A.image g) B (hA.image g)
    (Finset.image_subset_iff.mpr hB) f hf
  simpa only [Finset.expect_image hg, Finset.card_image_of_injOn hg] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IteratedCircleAverageIntegral
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory

variable {α : Type*}

def CircleAverageTuple : List α → Type
  | [] => Unit
  | _ :: is => Circle × CircleAverageTuple is

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

open Submodule _root_.Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

instance latticeSection_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (W : Submodule ℝ E) : DiscreteTopology (latticeSection Λ W) :=
  ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective

end Erdos3

end

section

namespace Erdos3

variable (ι : Type*) [Fintype ι]

instance standardEuclideanLattice_discrete : DiscreteTopology (standardEuclideanLattice ι) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage
namespace OAI

section

namespace Erdos3

theorem quotientIntegerCover_surjective {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Γ : AddSubgroup E) (q : ℕ) (hq : 0 < q) :
    Function.Surjective (quotientIntegerCover Γ q) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective Γ y
  refine ⟨QuotientAddGroup.mk' Γ ((q : ℝ)⁻¹ • x), ?_⟩
  rw [quotientIntegerCover_mk, smul_smul, mul_inv_cancel₀ hq0, one_smul]

theorem quotientIntegerCover_continuous {E : Type*} [AddCommGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (Γ : AddSubgroup E) (q : ℕ) :
    Continuous (quotientIntegerCover Γ q) := continuous_id.nsmul q

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)

theorem linearQuotientAverage_probability [MeasurableSpace (V ⧸ Γ)]
    [MeasurableAdd₂ (V ⧸ Γ)] [MeasurableNeg (V ⧸ Γ)]
    (μ : Measure (V ⧸ Γ)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (hRm : Measurable (linearQuotientEndomorphism Γ R hR))
    (f : (V ⧸ Γ) → ℝ) (hfm : Measurable f) (hfi : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hfmass : (∫ x, f x ∂μ) = 1) :
    (∀ x, 0 ≤ linearQuotientAverage Γ R hR μ f x) ∧
      Integrable (linearQuotientAverage Γ R hR μ f) μ ∧
      (∫ x, linearQuotientAverage Γ R hR μ f x ∂μ) = 1 := by
  have h := haarShiftDensity_probability μ μ hRm.neg hfm hfi hf0 hfmass
  have he : haarShiftDensity μ (-⇑(linearQuotientEndomorphism Γ R hR)) f =
      linearQuotientAverage Γ R hR μ f := by
    funext x
    simp only [haarShiftDensity, densityMixture, Pi.neg_apply, sub_neg_eq_add, linearQuotientAverage]
  rwa [he] at h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Γ : AddSubgroup V)
  (R : V →ₗ[ℝ] V) (hR : ∀ x ∈ Γ, R x ∈ Γ)
  [MeasurableSpace (V ⧸ Γ)]

theorem linearQuotientAverage_cover {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) (q : ℕ)
    (hcover : MeasurePreserving (quotientIntegerCover Γ q) μ μ)
    (f : (V ⧸ Γ) → W) (x : V ⧸ Γ)
    (hf : AEStronglyMeasurable
      (fun y => f (quotientIntegerCover Γ q x + linearQuotientEndomorphism Γ R hR y)) μ) :
    linearQuotientAverage Γ R hR μ f (quotientIntegerCover Γ q x) =
      linearQuotientAverage Γ R hR μ (fun z => f (quotientIntegerCover Γ q z)) x := by
  have hf' : AEStronglyMeasurable
      (fun y => f (quotientIntegerCover Γ q x + linearQuotientEndomorphism Γ R hR y))
      (μ.map (quotientIntegerCover Γ q)) := by rwa [hcover.map_eq]
  have he := integral_map hcover.measurable.aemeasurable hf'
  rw [hcover.map_eq] at he
  change (∫ y, f (quotientIntegerCover Γ q x + linearQuotientEndomorphism Γ R hR y) ∂μ) = _
  rw [he]
  apply integral_congr_ae
  exact ae_of_all μ (fun y => by
    change f (q • x + linearQuotientEndomorphism Γ R hR (q • y)) =
      f (q • (x + linearQuotientEndomorphism Γ R hR y))
    rw [map_nsmul, nsmul_add])

theorem linearQuotientAverage_cover_eq_of_map_eq [MeasurableAdd₂ (V ⧸ Γ)]
    {Y W : Type*} [AddCommGroup Y] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (V ⧸ Γ)) [μ.IsAddLeftInvariant] (q : ℕ) (E : (V ⧸ Γ) →+ Y)
    (hker : ∀ z, E z = 0 → linearQuotientEndomorphism Γ R hR z = quotientIntegerCover Γ q z)
    (f : (V ⧸ Γ) → W) (x y : V ⧸ Γ) (hxy : E x = E y) :
    linearQuotientAverage Γ R hR μ f (quotientIntegerCover Γ q x) =
      linearQuotientAverage Γ R hR μ f (quotientIntegerCover Γ q y) := by
  have hz : E (y - x) = 0 := by rw [map_sub, hxy, sub_self]
  have he := linearQuotientAverage_invariant Γ R hR μ f (quotientIntegerCover Γ q x) (y - x)
  rw [hker _ hz, map_sub, ← add_sub_assoc, add_sub_cancel_left] at he
  exact he.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem subspaceArrayFunctional_integral {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ)
    (x : I → U) (hx : x ∈ subspaceArrayIntegerLattice I U) :
    ∃ n : ℤ, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x = n := by
  change ∀ i a, ∃ n : ℤ, (x i).val a = n at hx
  choose z hz using hx
  refine ⟨∑ i, ∑ a, frequency i a * z i a, ?_⟩
  change (∑ i, ∑ a, (frequency i a : ℝ) * (x i).val a) = _
  simp only [hz, Int.cast_sum, Int.cast_mul]

end Erdos3

end

section

namespace Erdos3

theorem subspaceAmbientTorus_mk {J : Type*} (U : Submodule ℝ (J → ℝ)) (x : Unit → U) (a : J) :
    subspaceAmbientTorus U (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U) x) a =
      ((x ()).val a : UnitAddCircle) := rfl

end Erdos3

end

section

namespace Erdos3

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))

instance euclideanSubspaceLattice_discrete :
    DiscreteTopology (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup :=
  latticeSection_discrete (standardEuclideanLattice D) (euclideanSubspace U)

instance euclideanSubspaceLattice_closed :
    IsClosed ((latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup :
      Set (euclideanSubspace U)) := AddSubgroup.isClosed_of_discrete

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module

instance coefficientIntegerLattice_closed {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    IsClosed (coefficientIntegerLattice (K := K) U : Set (CoefficientArray (K := K) U)) := by
  change IsClosed {x : CoefficientArray (K := K) U | ∀ s a, ∃ n : ℤ, (x s).val a = n}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro a
  have h₁ : Continuous (fun x : CoefficientArray (K := K) U => x s) := continuous_apply s
  have h₂ : Continuous (fun x : CoefficientArray (K := K) U => (x s).val) :=
    continuous_subtype_val.comp h₁
  have h₃ : Continuous (fun x : CoefficientArray (K := K) U => (x s).val a) :=
    (continuous_apply a).comp h₂
  have h : IsClosed {x : CoefficientArray (K := K) U | ∃ n : ℤ, (n : ℝ) = (x s).val a} :=
    Real.isClosedEmbedding_intCast.isClosed_range.preimage h₃
  simpa only [eq_comm] using h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonIntegerSiteResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem matrixModuleAction_int_smul {I S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℝ W] (T : Matrix I S ℤ) (d : ℕ) (x : S → W) :
    matrixModuleAction (fun i s => (((d : ℤ) * T i s : ℤ) : ℝ)) x =
      (d : ℝ) • matrixModuleAction (fun i s => (T i s : ℝ)) x := by
  funext i
  change (∑ s, (((d : ℤ) * T i s : ℤ) : ℝ) • x s) =
    (d : ℝ) • ∑ s, (T i s : ℝ) • x s
  simp only [Int.cast_mul, Int.cast_natCast, mul_smul, Finset.smul_sum]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def coefficientSlotFrequency {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (frequency : ∀ s : CoefficientSlot K m, J s.1 → ℤ) :
    ∀ j, (K →₀ ℕ) → J j → ℤ := fun j d a =>
  if h : d.degree ≤ j.val + 1 then frequency ⟨j, ⟨d, h⟩⟩ a else 0

theorem coefficientSlotFrequency_apply {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (frequency : ∀ s : CoefficientSlot K m, J s.1 → ℤ)
    (s : CoefficientSlot K m) (a : J s.1) :
    coefficientSlotFrequency frequency s.1 s.2.val a = frequency s a := by
  simp only [coefficientSlotFrequency, dif_pos s.2.property]

theorem coefficientSlotFrequency_bound {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (frequency : ∀ s : CoefficientSlot K m, J s.1 → ℤ) {C : ℝ}
    (hfrequency : ∀ s a, |(frequency s a : ℝ)| ≤ C) :
    ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(coefficientSlotFrequency frequency j d a : ℝ)| ≤ C := by
  intro j d hd a
  simpa only [coefficientSlotFrequency, dif_pos hd] using hfrequency ⟨j, ⟨d, hd⟩⟩ a

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineOneSiteNormalizedLaw
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem integerSiteValue_oneSite {I K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ) (z : Option K × I → ℤ) :
    integerSiteValue (affineSite root difference ∅) (fun k j => (z (k,j) : ℝ)) =
      physicalAffineSite root z := by
  have hs : affineSite root difference ∅ = (fun k => match k with | none => 1 | some k => root k) := by
    funext k
    cases k <;> simp [affineSite]
  rw [hs]
  rfl

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxObservedMean
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem integerPhysicalSite_abs_bound {K I : Type*} [Fintype K]
    (root : K → ℤ) (W : Option K × I → ℝ) (z : Option K × I → ℤ)
    (hz : ∀ a, |(z a : ℝ)| ≤ W a) (i : I) :
    |(integerPhysicalSite root z i : ℝ)| ≤ physicalSiteWidth root W i := by
  simp only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul, physicalSiteWidth]
  calc
    _ ≤ |(z (none,i) : ℝ)| + |∑ k, (root k : ℝ) * (z (some k,i) : ℝ)| := abs_add_le _ _
    _ ≤ |(z (none,i) : ℝ)| + ∑ k, |(root k : ℝ) * (z (some k,i) : ℝ)| :=
      add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
    _ ≤ _ := add_le_add (hz _) (Finset.sum_le_sum (fun k _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hz _) (abs_nonneg _)))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem centeredSpatialWidths_pos {K I : Type*} {B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 < σ)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (z : Option K × I) :
    0 < centeredSpatialWidths B σ N z := by
  have hn : (0 : ℝ) < N z.2 := by exact_mod_cast hN z.2
  rcases z with ⟨k,i⟩
  cases k <;> dsimp only [centeredSpatialWidths] <;> positivity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem trimmedSpatialWidths_pos {K I : Type*} {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (z : Option K × I) :
    0 < trimmedSpatialWidths B τ N z :=
  mul_pos hτ (centeredSpatialWidths_pos hB (by norm_num) N hN z)

namespace BooleanCubeKernel

theorem trimmedSpatialWidths_fit {K I : Type*} [Fintype K] {B τ : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (root : K → ℤ)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ B) (N : I → ℕ) (i : I) :
    physicalSiteWidth root (trimmedSpatialWidths B τ N) i ≤ τ * (N i : ℝ) / 4 := by
  have h := mul_le_mul_of_nonneg_left
    (centeredSpatialWidths_fit hB (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)
      root hroot N i) hτ
  have he : physicalSiteWidth root (trimmedSpatialWidths B τ N) i =
      τ * physicalSiteWidth root (centeredSpatialWidths B 1 N) i := by
    simp only [physicalSiteWidth, trimmedSpatialWidths, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  nlinarith

end BooleanCubeKernel

theorem spatialTrimMargin_fits {K I : Type*} [Fintype K] {B τ : ℝ}
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (root : K → ℤ)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ B) (N : I → ℕ) (i : I) :
    BooleanCubeKernel.physicalSiteWidth root (trimmedSpatialWidths B τ N) i ≤
      (spatialTrimMargin τ N i : ℝ) :=
  (BooleanCubeKernel.trimmedSpatialWidths_fit hB hτ root hroot N i).trans (Nat.le_ceil _)

theorem spatialTrimMargin_bound {I : Type*} {τ : ℝ} (N : I → ℕ)
    (hsize : ∀ i, 4 ≤ τ * (N i : ℝ)) (i : I) :
    (spatialTrimMargin τ N i : ℝ) ≤ τ * (N i : ℝ) / 2 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ τ * (N i : ℝ) / 4 by linarith [hsize i])
  dsimp only [spatialTrimMargin]
  linarith [hsize i]

theorem spatialTrimMargin_proper {I : Type*} {τ : ℝ} (hτ : τ ≤ 1/2)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (hsize : ∀ i, 4 ≤ τ * (N i : ℝ)) (i : I) :
    2 * spatialTrimMargin τ N i < N i := by
  have hn : (0 : ℝ) < N i := by exact_mod_cast hN i
  have h := spatialTrimMargin_bound N hsize i
  have hi : (2 : ℝ) * (spatialTrimMargin τ N i : ℝ) < N i := by nlinarith
  exact_mod_cast hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateProductCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem independentProductPMF_coordinate_split {D X : Type*} [Fintype D] [DecidableEq D]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : D → PMF X) (j : D) :
    independentProductPMF p =
      (independentProductPMF (fun d : {d : D // d ≠ j} => p d.val)).bind
        (fun tail => (p j).map (coordinateJoin j tail)) := by
  ext z
  let tail := fun d : {d : D // d ≠ j} => z d.val
  have hz : coordinateJoin j tail (z j) = z := coordinateJoin_eta j z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (coordinateJoin_injective j tail)]
    simp only [independentProductPMF_apply]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
    simp only [coordinateJoin_pivot, coordinateJoin_other]
    exact mul_comm _ _
  · intro other hother
    have hr : coordinateJoin j tail (z j) ∉ Set.range (coordinateJoin j other) := by
      rintro ⟨x, he⟩
      apply hother
      funext d
      simpa only [coordinateJoin_other] using congrFun he d.val
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

theorem independentProductPMF_coordinate_cap {D X Y : Type*} [Fintype D] [DecidableEq D]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : D → PMF X) (j : D) (f : (D → X) → Y)
    (hf : ∀ tail, Function.Injective (fun x => f (coordinateJoin j tail x)))
    {C : ℝ} (hC : 0 ≤ C) (hp : ∀ x, (p j x).toReal ≤ C) (y : Y) :
    ((independentProductPMF p).map f y).toReal ≤ C := by
  rw [independentProductPMF_coordinate_split p j, PMF.map_bind]
  simp_rw [PMF.map_comp]
  exact pmf_bind_injective_toReal_cap _ _ _ hf hC hp y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem rowDifferenceCoefficients_linear {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (r s : K → ℤ) (i : I) (z : Option K × I → ℤ) :
    integerArrayLinearForm (rowDifferenceCoefficients r s i) z =
      integerPhysicalSite r z i - integerPhysicalSite s z i := by
  have he : integerArrayLinearForm (rowDifferenceCoefficients r s i) z =
      ∑ k, (r k - s k) * z (some k,i) := by
    simp [integerArrayLinearForm, rowDifferenceCoefficients, Fintype.sum_prod_type,
      Fintype.sum_option, ite_mul]
  rw [he]
  simp only [integerPhysicalSite, sub_mul, Finset.sum_sub_distrib]
  ring

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledCommonSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedSupportedCubeSum {A : Type*} [AddCommGroup A]
    (j : ℕ) (Q : Finset A) (F : (Fin j → Bool) → A → ℂ) : ℂ :=
  supportedCubeSum j (Q : Set A) F / Nat.card (SupportedCube j (Q : Set A))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

theorem physicalCubeCoefficient_pivot {α K : Type*}
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) :
    (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s) =
      selectedSpatialPivot root D s := by
  ext i j
  cases i <;> cases j <;> rfl

theorem physicalCube_normalized_columns {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) {A R L : ℝ}
    (hA : A ≠ 0) (hR : R ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerColumns (physicalCubeCoefficient root D)
        (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L) =
      fun i k => match i, k with
      | .inl _, none => 1
      | .inl _, some k => (root k : ℝ) * R / A
      | .inr _, none => 0
      | .inr i, some k => (D i k : ℝ) / L := by
  ext i k
  rw [normalizedIntegerColumns_entry_div]
  cases i <;> cases k <;>
    simp [physicalCubeCoefficient, physicalSpatialInputScale, physicalSpatialOutputScale, hA]
  field_simp

theorem physicalCube_normalized_pivot {α K : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L : ℝ}
    (hA : A ≠ 0) (hR : R ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerPivot ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s))
        (fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i))
        (physicalSpatialOutputScale α A R L) =
      rootDifferenceMatrix (fun i => (root (s i) : ℝ) * R / A)
        (Matrix.of (fun i j => (D i (s j) : ℝ) / L)) := by
  ext i j
  rw [normalizedIntegerPivot_entry]
  cases i <;> cases j <;>
    simp [physicalCubePivotIndex_inl, physicalCubePivotIndex_inr,
      physicalCubeCoefficient, physicalSpatialInputScale,
      physicalSpatialOutputScale, rootDifferenceMatrix, Matrix.fromBlocks, hA]
  field_simp

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem physicalCube_normalized_entry_bound {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) {A R L : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L) :
    ∀ i k, |normalizedIntegerColumns (physicalCubeCoefficient root D)
      (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L) i k| ≤ 1 := by
  rw [physicalCube_normalized_columns root D hA.ne' hR.ne' hL.ne']
  rintro (i | i) (k | k)
  · norm_num
  · dsimp
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_pos hR]
    exact (div_le_one hA).mpr (hr k)
  · norm_num
  · dsimp
    rw [abs_div, abs_of_pos hL]
    exact (div_le_one hL).mpr (hD i k)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem physicalSpatialInverseBound_le_exp (α : Type*) [Fintype α] {κ b : ℝ}
    (hκ : 0 < κ) (hi : κ⁻¹ ≤ Real.exp b) :
    physicalSpatialInverseBound α κ ≤
      Real.exp ((Fintype.card (Unit ⊕ α) : ℝ) ^ 2 + Fintype.card (Unit ⊕ α) + b) := by
  let j := Fintype.card (Unit ⊕ α)
  have hj : (j : ℝ) ≤ Real.exp (j : ℝ) := by linarith [Real.add_one_le_exp (j : ℝ)]
  change (j : ℝ) * j.factorial / κ ≤ _
  calc
    _ ≤ Real.exp (j : ℝ) * Real.exp ((j : ℝ) ^ 2) * Real.exp b := by
      rw [div_eq_mul_inv]
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

noncomputable def physicalCubeSiteTest {I : Type*} {q : ℕ}
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (v : I → (Unit ⊕ Fin q) → ℤ) : ℂ :=
  ∏ s, test s (fun i => (physicalCubeVertexValue v s i : ℝ))

theorem physicalCubeSiteTest_norm_le {I : Type*} {q : ℕ}
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1)
    (v : I → (Unit ⊕ Fin q) → ℤ) : ‖physicalCubeSiteTest test v‖ ≤ 1 := by
  rw [physicalCubeSiteTest, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun s _ => htest s _)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix

theorem standardPhysicalCubeFrame_injective {X : Type*} {q : ℕ} :
    Function.Injective (standardPhysicalCubeFrame (X := X) (q := q)) := by
  intro v w h
  have he := congrArg standardPhysicalCubeOutput h
  simpa only [standardPhysicalCubeOutput_frame] using he

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalResidueOffsetShift
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def physicalCubeResidueCoordinates {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (z : Option K × X → ℤ) :
    X → (Unit ⊕ α) → ℤ :=
  fun x i => physicalCubeRootDifferences root D base residue x i +
    (modulus x : ℤ) * physicalCubeRootDifferences root D 0 z x i

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def physicalResidueReconstruction {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (v : X → (Unit ⊕ α) → ℤ) :
    X → (Unit ⊕ α) → ℤ :=
  fun d i => physicalCubeRootDifferences root D base residue d i + (q d : ℤ) * v d i

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

def physicalResidueOffsetShift {K X α : Type*} [Fintype K]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) : X → (Unit ⊕ α) → ℤ :=
  fun d => residueMatrixShift (physicalCubeCoefficient root D) (physicalCubeCoefficient root₀ D₀)
    (q d) (fun k => r (k, d))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeTernaryCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def TernaryTensorIndex (I : Type*) : ℕ → Type _
  | 0 => I
  | n + 1 => TernaryTensorIndex I n × (TernaryTensorIndex I n × TernaryTensorIndex I n)

instance TernaryTensorIndex.fintype (I : Type*) [Fintype I] (n : ℕ) : Fintype (TernaryTensorIndex I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype I)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (TernaryTensorIndex I n ×
      (TernaryTensorIndex I n × TernaryTensorIndex I n)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RoundedAffineLifts
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem integerAffineMap_jointIntegerFrame {K I : Type*} [Fintype K]
    (z : (I → ℤ) × (Option K × I → ℤ)) (root : K → ℤ) :
    integerAffineMap (fun i k => jointIntegerFrame z (some k) i) (jointIntegerFrame z none) root =
      jointIntegerPhysicalSite root z := by
  funext i
  simp only [integerAffineMap, jointIntegerFrame, jointIntegerPhysicalSite,
    integerPhysicalSite, Pi.add_apply]
  rw [add_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

def translatePhysicalCube {X α : Type*} (base : X → ℤ)
    (v : X → (Unit ⊕ α) → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun x i => physicalCubeOffset base x i + v x i

theorem physicalCubeVertexValue_translate {X α : Type*} (base : X → ℤ)
    (v : X → (Unit ⊕ α) → ℤ) (s : Finset α) :
    physicalCubeVertexValue (translatePhysicalCube base v) s =
      fun x => base x + physicalCubeVertexValue v s x := by
  funext x
  simp only [physicalCubeVertexValue, translatePhysicalCube, physicalCubeOffset,
    zero_add, add_assoc]

theorem physicalResidueReconstruction_translate {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (v : X → (Unit ⊕ α) → ℤ) :
    physicalResidueReconstruction root D base r q v =
      translatePhysicalCube base (physicalResidueReconstruction root D 0 r q v) := by
  funext x i
  cases i <;> simp [physicalResidueReconstruction, physicalCubeRootDifferences,
    translatePhysicalCube, physicalCubeOffset, add_assoc]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem physicalResidueReconstruction_injective {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x) :
    Function.Injective (physicalResidueReconstruction root D base r q) := by
  intro v w h
  funext x i
  have he := congrFun (congrFun h x) i
  have hn : (q x : ℤ) ≠ 0 := by exact_mod_cast (hq x).ne'
  exact mul_left_cancel₀ hn (add_left_cancel he)

theorem physicalCube_zero_residue_bound {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (stride : X → ℕ)
    (r : Option K × X → ℤ) (hr : ∀ k x, |(r (k,x) : ℝ)| ≤ stride x)
    (H : X → ℝ)
    (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (x : X) (i : Unit ⊕ α) :
    |(physicalCubeRootDifferences root D 0 r x i : ℝ)| ≤ (stride x : ℝ) * H x := by
  have hz : physicalCubeOffset (0 : X → ℤ) x i = 0 := by cases i <;> rfl
  simp only [physicalCubeRootDifferences, hz, zero_add, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ k, |(physicalCubeCoefficient root D i k : ℝ) * (r (k,x) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |(physicalCubeCoefficient root D i k : ℝ)| * |(r (k,x) : ℝ)| := by
      simp only [abs_mul]
    _ ≤ ∑ k, |(physicalCubeCoefficient root D i k : ℝ)| * (stride x : ℝ) := by
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hr k x) (abs_nonneg _))
    _ = (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) * (stride x : ℝ) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ H x * (stride x : ℝ) := mul_le_mul_of_nonneg_right (hrows x i) (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

theorem referenceJetEnvelopeWidths_residue {X : Type*} {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H : X → ℝ) (z : Option (Fin q) × X) :
    residueProfileWidth stride (referenceJetEnvelopeWidths stride H) z = 20 * H z.2 := by
  have hn : (stride z.2 : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hs z.2)).ne'
  dsimp only [residueProfileWidth, referenceJetEnvelopeWidths]
  field_simp

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSpatialResidueSupport
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

noncomputable def physicalResidueStarFactor {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b r : ℝ) (H : X → ℝ)
    {m : ℕ} (t : X → SpatialSiteLabel α m b r) (i : Unit ⊕ α) (u : X → ℤ) : ℂ :=
  affineVectorResidueSiteWeight b r H q
    (physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) (spatialStarVertex i))
    (fun x => (t x).1 i) (fun x => (t x).2 i) u

noncomputable def physicalResidueSpatialSiteFactor {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b r : ℝ) (H : X → ℝ)
    {m : ℕ} (t : X → SpatialSiteLabel α m b r) (s : Finset α) (u : X → ℤ) : ℂ :=
  starVertexSiteFactor (physicalResidueStarFactor root D base residue q b r H t) s u

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

def physicalResidueQuotient {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (u : X → (Unit ⊕ α) → ℤ) :
    X → (Unit ⊕ α) → ℤ :=
  fun x i => (u x i - physicalCubeRootDifferences root D base r x i) / (q x : ℤ)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalNormalizedSpatialFactor
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical NNReal

variable {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ)
variable (b : ℝ) (r : ℝ≥0) (H N : X → ℝ) {m : ℕ}
variable (t : X → SpatialSiteLabel α m b r) (s : Finset α)

local notation "offset" => (fun i : Unit ⊕ α =>
  physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) (spatialStarVertex i))

noncomputable def physicalResidueSpatialMask (u : X → ℤ) : ℂ :=
  starVertexSiteFactor (fun i u => ∏ x,
    (residueSiteIndicator (m := q x * m)
      ((offset i x + (q x : ℤ) * (((t x).1 i).val : ℤ) : ℤ) : ZMod (q x * m)) (u x) : ℂ)) s u

noncomputable def physicalResidueSpatialSmooth (y : X → ℝ) : ℂ :=
  starVertexSiteFactor (fun i y => vectorIntervalSiteWeight b r (fun x => (t x).2 i)
    (fun x => (N x * y x - offset i x) / ((q x : ℝ) * H x))) s y

theorem physicalResidueSpatialSiteFactor_normalized (hN : ∀ x, N x ≠ 0) (u : X → ℤ) :
    physicalResidueSpatialSiteFactor root D base residue q b r H t s u =
      physicalResidueSpatialMask root D base residue q b r t s u *
        physicalResidueSpatialSmooth root D base residue q b r H N t s (fun x => (u x : ℝ) / N x) := by
  unfold physicalResidueSpatialSiteFactor physicalResidueSpatialMask physicalResidueSpatialSmooth
  unfold starVertexSiteFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : spatialStarVertex i = s
  · simp only [hi, ite_true, physicalResidueStarFactor]
    rw [affineVectorResidueSiteWeight_factorization]
    congr 1
    apply congrArg (vectorIntervalSiteWeight b r (fun x => (t x).2 i))
    funext x
    congr 1
    field_simp [hN x]
  · simp only [hi, ite_false, mul_one]

theorem trimmedSpatialRootScale_normalized_ratio {X : Type*}
    (N q : X → ℕ) {τ : ℝ} (hτ : 0 < τ) (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x) (x : X) :
    (N x : ℝ) / ((q x : ℝ) * trimmedSpatialRootScale τ N q x) = 8 / τ := by
  have hn : (N x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hN x).ne'
  have hq' : (q x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hq x).ne'
  unfold trimmedSpatialRootScale
  field_simp [hn, hq', hτ.ne']

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {X A V : Type*} [Fintype X] [Fintype A]
variable (spatialPeriod : ℕ) (q : X → ℕ) (e : A → ScalarSiteExpansion V)
variable (k : ∀ a, (e a).Term) (idealPeriod : ℕ)

namespace BooleanCubeKernel

variable {K α : Type*} [Fintype K] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ)
variable (b : ℝ) (r : ℝ≥0) {spatialPeriod M : ℕ}
variable (hM : ∀ x, q x * spatialPeriod ∣ M)
variable (t : X → SpatialSiteLabel α spatialPeriod b r) (s : Finset α)

noncomputable def physicalResidueSpatialMaskMod (u : X → ZMod M) : ℂ :=
  starVertexSiteFactor (fun i u => ∏ x,
    if ZMod.castHom (hM x) (ZMod (q x * spatialPeriod)) (u x) =
      ((physicalCubeVertexValue (physicalCubeRootDifferences root D base residue)
        (spatialStarVertex i) x + (q x : ℤ) * (((t x).1 i).val : ℤ) : ℤ) : ZMod (q x * spatialPeriod))
    then (1 : ℂ) else 0) s u

theorem physicalResidueSpatialMaskMod_eval (u : X → ℤ) :
    physicalResidueSpatialMaskMod root D base residue q b r hM t s (fun x => (u x : ZMod M)) =
      physicalResidueSpatialMask root D base residue q b r t s u := by
  simp only [physicalResidueSpatialMaskMod, physicalResidueSpatialMask, starVertexSiteFactor,
    residueSiteIndicator, map_intCast, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]

theorem physicalResidueSpatialMaskMod_norm (u : X → ZMod M) :
    ‖physicalResidueSpatialMaskMod root D base residue q b r hM t s u‖ ≤ 1 := by
  apply starVertexSiteFactor_bound
  intro i v
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro x _
  split_ifs <;> simp

end BooleanCubeKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedReferenceJetMass
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem referenceJetEnvelope_volume {X : Type*} [Fintype X] {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H : X → ℝ) :
    ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
      (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := q) stride H) i) /
      (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) =
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (∏ x, ∏ _i : Unit ⊕ Fin q, H x) := by
  have hprod : (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := q) stride H) i) =
      20 ^ Fintype.card (Option (Fin q) × X) * (∏ i : Option (Fin q) × X, H i.2) := by
    simp_rw [referenceJetEnvelopeWidths_residue stride hs H]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
  have hcoord : (∏ i : Option (Fin q) × X, H i.2) = ∏ x, ∏ _i : Unit ⊕ Fin q, H x := by
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_option,
      Fintype.card_fin, Fintype.card_sum, Fintype.card_unique, Nat.add_comm]
  rw [hprod, hcoord, ← mul_assoc, ← mul_pow]
  norm_num only [show (3 / 2 : ℝ) * 20 = 30 by norm_num]
  rw [mul_div_right_comm, ← div_pow]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSupportedCubes
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalCubeParametersEquiv_vertex {X : Type*} (dim : ℕ)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (ω : Fin dim → Bool) :
    physicalCubeVertexValue v (Finset.univ.filter (fun i => ω i)) =
      (physicalCubeParametersEquiv X dim v).2 +
        cubeShift (physicalCubeParametersEquiv X dim v).1 ω := by
  funext x
  change v x (.inl ()) + ∑ i ∈ Finset.univ.filter (fun i => ω i), v x (.inr i) =
    v x (.inl ()) + (∑ i, if ω i then (fun x => v x (.inr i)) else 0) x
  simp only [Finset.sum_filter, Finset.sum_apply]
  apply congrArg (fun z : ℤ => v x (.inl ()) + z)
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

theorem physicalCubeParametersEquiv_support_iff {X : Type*} (dim : ℕ)
    (Q : Set (X → ℤ)) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    (∀ s : Finset (Fin dim), physicalCubeVertexValue v s ∈ Q) ↔
      ∀ ω : Fin dim → Bool, (physicalCubeParametersEquiv X dim v).2 +
        cubeShift (physicalCubeParametersEquiv X dim v).1 ω ∈ Q := by
  classical
  constructor
  · intro hv ω
    rw [← physicalCubeParametersEquiv_vertex]
    exact hv _
  · intro hv s
    have h := hv (fun i => decide (i ∈ s))
    rw [← physicalCubeParametersEquiv_vertex] at h
    simpa using h

def physicalSupportedCubeEquiv (X : Type*) (dim : ℕ) (Q : Set (X → ℤ)) :
    {v : X → (Unit ⊕ Fin dim) → ℤ // ∀ s, physicalCubeVertexValue v s ∈ Q} ≃
      SupportedCube dim Q where
  toFun v := ⟨physicalCubeParametersEquiv X dim v.val,
    (physicalCubeParametersEquiv_support_iff dim Q v.val).mp v.property⟩
  invFun p := ⟨(physicalCubeParametersEquiv X dim).symm p.val,
    (physicalCubeParametersEquiv_support_iff dim Q _).mpr (by
      simpa only [Equiv.apply_symm_apply] using p.property)⟩
  left_inv v := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _
  right_inv p := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCubeNativeDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem conjugationPower_twice (n : ℕ) (z : ℂ) :
    conjugationPower n (conjugationPower n z) = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change star (conjugationPower n (star (conjugationPower n z))) = z
    rw [conjugationPower_star, ih, star_star]

namespace BooleanCubeKernel

theorem vertexFinsetEquiv_card {j : ℕ} (ω : Fin j → Bool) :
    (vertexFinsetEquiv j ω).card = booleanWeight ω := by
  simp only [vertexFinsetEquiv, Equiv.coe_fn_mk, booleanWeight]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem physical_twisted_cube_product {X : Type*} (j : ℕ)
    (f : (X → ℤ) → ℂ) (twist : Finset (Fin j) → (X → ℤ) → ℂ)
    (u : X → (Unit ⊕ Fin j) → ℤ) :
    (∏ s, conjugationPower s.card (f (physicalCubeVertexValue u s)) *
      twist s (physicalCubeVertexValue u s)) =
    mixedCubeProduct (fun ω x => f x * conjugationPower (booleanWeight ω)
      (twist (vertexFinsetEquiv j ω) x))
      (physicalCubeParametersEquiv X j u).1 (physicalCubeParametersEquiv X j u).2 := by
  rw [← (vertexFinsetEquiv j).prod_comp]
  apply Finset.prod_congr rfl
  intro ω _
  rw [vertexFinsetEquiv_card]
  change conjugationPower (booleanWeight ω)
      (f (physicalCubeVertexValue u (Finset.univ.filter (fun i => ω i)))) *
      twist (vertexFinsetEquiv j ω) (physicalCubeVertexValue u (Finset.univ.filter (fun i => ω i))) = _
  rw [physicalCubeParametersEquiv_vertex, map_mul, conjugationPower_twice]

theorem physical_twisted_cube_mean {X : Type*} (j : ℕ)
    (Q : Finset (X → ℤ)) (f : (X → ℤ) → ℂ)
    (twist : Finset (Fin j) → (X → ℤ) → ℂ) :
    (𝔼 cube : SupportedCube j (Q : Set (X → ℤ)),
      let u := (physicalCubeParametersEquiv X j).symm cube.val
      ∏ s, conjugationPower s.card (f (physicalCubeVertexValue u s)) *
        twist s (physicalCubeVertexValue u s)) =
      normalizedSupportedCubeSum j Q (fun ω x => f x *
        conjugationPower (booleanWeight ω) (twist (vertexFinsetEquiv j ω) x)) := by
  simp_rw [physical_twisted_cube_product, Equiv.apply_symm_apply]
  simp only [normalizedSupportedCubeSum, supportedCubeSum, Fintype.expect_eq_sum_div_card,
    Nat.card_eq_fintype_card]

end BooleanCubeKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedScaleCollisionBudget
namespace OAI

section

namespace Erdos3

theorem collision_error_of_exp_size_with_cap {F P C q ρ δ N : ℝ}
    (hC0 : 0 ≤ C) (hq0 : 0 ≤ q) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hC : C ≤ Real.exp (P*(P+5))) (hq : q ≤ Real.exp P)
    (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P)) (hδP : δ⁻¹ ≤ Real.exp P)
    (hN : Real.exp (F + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4) ≤ N) :
    2*Real.exp F*(C^2*(2*q/(ρ*N))) ≤ δ := by
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hmain : (4*Real.exp F*C^2*q*(1/ρ))/δ ≤ N := by
    calc
      _ = 4*Real.exp F*C^2*q*(1/ρ)*δ⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 4*Real.exp F*(Real.exp (P*(P+5)))^2*Real.exp P*
          Real.exp (spatialSamplingBudget P)*Real.exp P := by gcongr
      _ = Real.exp (F + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_add, ← Real.exp_add]
        congr 1
        norm_num
        ring
      _ ≤ N := hN
  have hnum := (div_le_iff₀ hδ).mp hmain
  calc
    _ = (4*Real.exp F*C^2*q*(1/ρ))/N := by ring
    _ ≤ δ := (div_le_iff₀ hN0).mpr (by simpa only [mul_comm N δ] using hnum)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowJetAmbientReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def lowJetAmbientSites
    (z : JetAmbientIndex (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) J → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => Finset α) J → UnitAddCircle :=
  fun t => ∑ r, boundedBooleanReconstructionMatrix α (t.1.val + 1) t.2.1 r • z ⟨t.1, r, t.2.2⟩

theorem lowJetAmbientSites_lipschitz :
    LipschitzWith (∑ j : Fin m, (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0))
      (lowJetAmbientSites (α := α) (J := J)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, s, i⟩
  have hterm (r : BoundedBooleanJet α (j.val + 1)) :
      dist (boundedBooleanReconstructionMatrix α (j.val + 1) s r • z ⟨j,r,i⟩)
        (boundedBooleanReconstructionMatrix α (j.val + 1) s r • w ⟨j,r,i⟩) ≤ dist z w := by
    simp only [boundedBooleanReconstructionMatrix]
    split_ifs
    · simpa only [one_zsmul] using dist_le_pi_dist z w ⟨j,r,i⟩
    · simpa only [zero_zsmul, dist_self] using (dist_nonneg : 0 ≤ dist z w)
  have hc : (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0) ≤
      ∑ j : Fin m, (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0) :=
    Finset.single_le_sum
      (f := fun j : Fin m => (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0))
      (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ ≤ ∑ _r : BoundedBooleanJet α (j.val + 1), dist z w :=
      (dist_sum_sum_le _ _ _).trans (Finset.sum_le_sum (fun r _ => hterm r))
    _ = (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ) * dist z w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
noncomputable local instance physicalRowsFintype (j : Fin m) : Fintype (Row j) :=
  Finset.Subtype.fintype (boundedBooleanJetRows (Fin q) (j.val + 1))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRowsAmbientProjectedFamilyMultiple
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped Classical BigOperators NNReal

attribute [local irreducible] boundedBooleanJetRows

variable {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
local notation "Row" => (fun j : Fin m =>
  {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})
noncomputable local instance (priority := 2000) physicalRowsAmbientFintype (j : Fin m) : Fintype (Row j) :=
  Finset.Subtype.fintype (boundedBooleanJetRows (Fin dim) (j.val + 1))
local notation "Std" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))

noncomputable def physicalRowsAmbientToStandard
    (z : JetAmbientIndex Row J → UnitAddCircle) : JetAmbientIndex Std J → UnitAddCircle :=
  fun a => z ⟨a.1, (boundedBooleanJetRowsEquiv (Fin dim) (a.1.val + 1)).symm a.2.1, a.2.2⟩

theorem physicalRowsAmbientToStandard_lipschitz :
    LipschitzWith 1 (physicalRowsAmbientToStandard (m := m) (dim := dim) (J := J)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  exact dist_le_pi_dist z w _

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) → ZMod N :=
  simplexCoordinatesOfAP r N p.1.1 0 p.2

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalResidueWindowSiteMask
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ) (H : X → ℝ) (radius : ℝ)

noncomputable def physicalResidueWindowSiteMask (s : Finset α) (u : X → ℤ) : ℂ :=
  starVertexSiteFactor (fun i v => if ∀ x,
    |(((v x - physicalCubeVertexValue (physicalCubeRootDifferences root D base residue)
      (spatialStarVertex i) x) / (q x : ℤ) : ℤ) : ℝ)| ≤ H x * radius then 1 else 0) s u

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AmbientL1SamplingBudget
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem exists_ambientL1SamplingThreshold_bound (K : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ T : ℝ, 0 ≤ T →
      (ambientL1SamplingBudget T + K) ^ K ≤ (T + A) ^ A := by
  obtain ⟨A, hA, hb⟩ := exists_natPolynomial_eval_budget
    ((ambientL1SamplingBudget Polynomial.X + Polynomial.C K) ^ K)
  refine ⟨A, hA, ?_⟩
  intro T hT
  simpa [ambientL1SamplingBudget, ambientL1FourierInput, Polynomial.eval₂_pow] using hb T hT

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSiteWidth_mono {K X : Type*} [Fintype K]
    (root : K → ℤ) {V W : Option K × X → ℝ} (h : ∀ z, V z ≤ W z) (x : X) :
    physicalSiteWidth root V x ≤ physicalSiteWidth root W x := by
  apply add_le_add (h (none,x))
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (h (some k,x)) (abs_nonneg _))

end Erdos3.BooleanCubeKernel

end

end OAI
end


