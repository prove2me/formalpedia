-- Prove2me | Definitions.Def_OAIE3v2B073
-- name    : OAIE3v2B073
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:17:15.701754+00:00
-- url     : https://prove2.me/theorems/42d1bc41-7138-4d17-8003-03dbfc349ee8
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 74 of 311
-- statement:
--   Definitions bundle 74 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B041`, `OAIE3v2B042`, `OAIE3v2B043`, `OAIE3v2B044`, `OAIE3v2B045`, `OAIE3v2B046`, `OAIE3v2B047` of this split.
--
--   Modules: `Estimates/CocycleHorizontalNormalization.lean`, `Estimates/CorrelationDerivative.lean`, `Estimates/EmbeddedFiniteConditioning.lean`, `Estimates/FiniteFiberTest.lean`, `Estimates/FinitePushforwardComplexWeights.lean`, `Estimates/FreeLieTreeCoefficientBounds.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/IndependentFiniteConditioning.lean`, `Estimates/IteratedCircleAverageIntegral.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/LocalizedSiftingAlmostPeriods.lean`, `Estimates/LowWeightFibers.lean`, `Estimates/NativeRetainedTargetCubeIntervals.lean`, `Estimates/NormalizedTwistParameterPartition.lean`, `Estimates/ProgressionPartitionComposition.lean`, `Estimates/RationalLieSubalgebra.lean`, `Estimates/RegularCylinderDecomposition.lean`, `Estimates/UniformCommutingCircleDecomposition.lean`, `FixedDensity/BooleanCutReduction.lean`, `FixedDensity/BundleCountingRecurrence.lean`, `FixedDensity/Energy.lean`, `FixedDensity/GeneratorCells.lean`, `FixedDensity/HypergraphBundleRelativeCounting.lean`, `FixedDensity/OrderedPattern.lean`, `FixedDensity/OrderedRemoval.lean`, `FixedDensity/SimplexTelescoping.lean`, `Fourier/CyclicAffineCharacterPhase.lean`, `Fourier/ExponentialBohrVolume.lean`, `Fourier/LocalSpectrumBudget.lean`, `Fourier/TranslatedBohrDifference.lean`, `Geometry/BoxBlockBudget.lean`, `Geometry/DifferenceEventSupport.lean`, `Geometry/LieStructureTransport.lean`, `Geometry/LinearMapCoordinateHeight.lean`, `Lattices/CommonAffineOrbitEvaluation.lean`, `Lattices/ComparableResidueProgressionPartition.lean`, `Lattices/ResidueSliceNormalizedCell.lean`, `Linear/NativePrescribedProjection.lean`, `Linear/RationalTaggedSpanProjection.lean`, `Polynomial/AffinePhaseBias.lean`, `Polynomial/PolynomialCoefficientGridDenominator.lean`, `Polynomial/RefinementPolynomialBound.lean`, `Probability/DifferenceEventProbability.lean`, `Probability/FiniteConditionedMass.lean`, `Probability/FiniteExcessMassCap.lean`, `Probability/FiniteProbabilityLipschitz.lean`, `Probability/FiniteProbabilityUniformResidualGood.lean`, `Sampling/IntegralGridFunctional.lean`, `Sampling/QuarticSamplingBudget.lean`.
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
import Definitions.Def_OAIE3v2B046
import Definitions.Def_OAIE3v2B047

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityLipschitz
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

theorem mean_mul_sq_le (f g : Ω → ℝ) :
    (p.mean (fun x => f x * g x)) ^ 2 ≤
      p.mean (fun x => f x ^ 2) * p.mean (fun x => g x ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => mul_nonneg (p.nonneg x) (sq_nonneg (f x)))
    (fun x _ => mul_nonneg (p.nonneg x) (sq_nonneg (g x)))
  intro x _
  exact le_of_eq (by ring)

theorem norm_correlation_sq_le (v w : Ω → ℂ) :
    ‖p.correlation v w‖ ^ 2 ≤
      p.mean (fun x => ‖v x‖ ^ 2) * p.mean (fun x => ‖w x‖ ^ 2) := by
  have hnorm : ‖p.correlation v w‖ ≤ p.mean (fun x => ‖v x‖ * ‖w x‖) := by
    unfold correlation mean
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro x _
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (p.nonneg x)]
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (p.mean_mul_sq_le (fun x => ‖v x‖) (fun x => ‖w x‖))

theorem correlation_self (v : Ω → ℂ) :
    p.correlation v v = (p.mean (fun x => ‖v x‖ ^ 2) : ℂ) := by
  unfold correlation mean
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  change v x * (starRingEnd ℂ) (v x) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem mean_single_norm [DecidableEq Ω] (x : Ω) :
    p.mean (fun y => ‖(Pi.single x (1 : ℂ) : Ω → ℂ) y‖) = p.weight x := by
  unfold mean
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

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

theorem correlation_eq_complexMean (v w : Ω → ℂ) :
    p.correlation v w = p.complexMean (fun x => v x * star (w x)) := rfl

theorem complexMean_re (v : Ω → ℂ) :
    (p.complexMean v).re = p.mean (fun x => (v x).re) := by
  simp [complexMean, mean, Complex.mul_re]

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
theorem mean_add (f g : Ω → ℝ) :
    p.mean (fun x => f x + g x) = p.mean f + p.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

omit [DecidableEq Ω] in
theorem mass_nonneg : 0 ≤ p.mass G :=
  Finset.sum_nonneg (fun x _ => p.nonneg x)

omit [DecidableEq Ω] in
theorem mass_le_one : p.mass G ≤ 1 := by
  rw [← p.total]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
    (fun x _ _ => p.nonneg x)

omit [DecidableEq Ω] in
theorem weight_le_mass {x : Ω} (hx : x ∈ G) : p.weight x ≤ p.mass G :=
  Finset.single_le_sum (fun y _ => p.nonneg y) hx

theorem mean_indicator : p.mean (fun x => if x ∈ G then 1 else 0) = p.mass G := by
  simp [mean, mass, mul_ite]

noncomputable def condition (hG : 0 < p.mass G) : FiniteProbabilityWeights Ω where
  weight x := (if x ∈ G then p.weight x else 0) / p.mass G
  nonneg x := div_nonneg (by split_ifs; exact p.nonneg x; exact le_rfl) hG.le
  total := by
    rw [← Finset.sum_div]
    have hsum : (∑ x, if x ∈ G then p.weight x else 0) = p.mass G := by
      simp [mass]
    rw [hsum, div_self hG.ne']

theorem condition_mean (hG : 0 < p.mass G) (f : Ω → ℝ) :
    (p.condition G hG).mean f =
      p.mean (fun x => if x ∈ G then f x else 0) / p.mass G := by
  unfold mean condition
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ G <;> simp [hx, div_mul_eq_mul_div]

theorem mass_mul_condition_mean (hG : 0 < p.mass G) (f : Ω → ℝ) :
    p.mass G * (p.condition G hG).mean f =
      p.mean (fun x => if x ∈ G then f x else 0) := by
  rw [condition_mean, mul_div_cancel₀ _ hG.ne']

theorem mass_mul_condition_correlation (hG : 0 < p.mass G) (v Q : Ω → ℂ) :
    (p.mass G : ℂ) * (p.condition G hG).correlation v Q =
      p.correlation (finiteMask G v) Q := by
  unfold correlation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ G
  · simp only [condition, hx, ite_true, finiteMask_apply]
    have hm : (p.mass G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    push_cast
    field_simp
  · simp [condition, hx]

theorem norm_correlation_mask (hG : 0 < p.mass G) (v Q : Ω → ℂ) :
    ‖p.correlation (finiteMask G v) Q‖ =
      p.mass G * ‖(p.condition G hG).correlation v Q‖ := by
  rw [← mass_mul_condition_correlation, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (p.mass_nonneg G)]

theorem mean_mask_zero (hG : p.mass G = 0) (f : Ω → ℝ) :
    p.mean (fun x => if x ∈ G then f x else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ G
  · have hw : p.weight x = 0 := le_antisymm
      (by simpa [hG] using p.weight_le_mass G hx) (p.nonneg x)
    simp [hx, hw]
  · simp [hx]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

noncomputable def fiberMean (F : X → R) (r : R) (f : X → ℝ) : ℝ := by
  classical
  exact p.mean (fun x => if F x = r then f x else 0)

theorem sum_fiberMean [Fintype R] (F : X → R) (f : X → ℝ) :
    (∑ r, p.fiberMean F r f) = p.mean f := by
  classical
  unfold fiberMean mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  simp

theorem complexMean_fiber_factor [Fintype R] (F : X → R) (f : X → ℝ) (a : R → ℂ) :
    p.complexMean (fun x => (f x : ℂ) * a (F x)) =
      ∑ r, (p.fiberMean F r f : ℂ) * a r := by
  classical
  unfold complexMean fiberMean mean
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have he (r : R) : ((if F x = r then f x else 0 : ℝ) : ℂ) =
      if F x = r then (f x : ℂ) else 0 := by split_ifs <;> rfl
  simp [he, mul_ite, ite_mul, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators

variable {X C : Type*} [Fintype X] [MeasurableSpace C] (p : FiniteProbabilityWeights X)

theorem mean_integrable (μ : Measure C) (f : C → X → ℝ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    Integrable (fun c => p.mean (f c)) μ :=
  integrable_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

theorem pointWeights_complexMean {Y : Type*} [Fintype Y] (y : Y) (f : Y → ℂ) :
    (pointWeights y).complexMean f = f y := by
  unfold complexMean pointWeights
  dsimp only
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz]
  · simp

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

variable {Ω R : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω) (F : Ω → R)

noncomputable def fiberTest (f : Ω → ℝ) (y : R) : ℝ :=
  p.fiberMean F y f / p.fiberMean F y (fun _ => 1)

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

theorem mean_pi_product {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (v : ∀ j, Ω j → ℝ) :
    (pi p).mean (fun x => ∏ j, v j (x j)) = ∏ j, (p j).mean (v j) := by
  classical
  change (∑ x : ∀ j, Ω j, (∏ j, (p j).weight (x j)) * (∏ j, v j (x j))) =
    ∏ j, ∑ x, (p j).weight x * v j x
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j (x : Ω j) => (p j).weight x * v j x)).symm

theorem eventProbability_pi {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (E : ∀ j, Ω j → Prop) :
    (pi p).eventProbability (fun x => ∀ j, E j (x j)) = ∏ j, (p j).eventProbability (E j) := by
  classical
  have hpoint (x : ∀ j, Ω j) :
      (@ite ℝ (∀ j, E j (x j)) (Classical.propDecidable _) 1 0) =
        ∏ j, if E j (x j) then (1 : ℝ) else 0 := by
    by_cases h : ∀ j, E j (x j)
    · simp [h]
    · rw [if_neg h]
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
  simpa only [eventProbability] using
    (congrArg (pi p).mean (funext hpoint)).trans
      (mean_pi_product p (fun j y => if E j y then (1 : ℝ) else 0))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem uniform_mass {Ω : Type*} [Fintype Ω] [Nonempty Ω] (G : Finset Ω) :
    (uniform Ω).mass G = (G.card : ℝ) / Fintype.card Ω := by
  simp [mass, uniform, div_eq_mul_inv]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem condition_mass {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G) :
    (p.condition G hG).mass R = p.mass (G ∩ R) / p.mass G := by
  simp only [mass, condition]
  rw [← Finset.sum_div, ← Finset.sum_filter]
  congr 1
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, and_comm]

theorem mass_inter_le_condition_mass {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G) :
    p.mass (G ∩ R) ≤ (p.condition G hG).mass R := by
  rw [condition_mass]
  apply (le_div_iff₀ hG).mpr
  exact mul_le_of_le_one_right (p.mass_nonneg _) (p.mass_le_one G)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LinearMapCoordinateHeight
namespace OAI

section

namespace Erdos3

open Module

variable {V W ι κ : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [Fintype ι]

theorem linearMap_coordinate_height (e : Basis ι ℚ V) (f : Basis κ ℚ W)
    (T : V →ₗ[ℚ] W) {H K : ℕ}
    (hT : ∀ i j, RationalHeightLE (f.repr (T (e i)) j) H)
    (x : V) (hx : ∀ i, RationalHeightLE (e.repr x i) K) (j : κ) :
    RationalHeightLE (f.repr (T x) j) ((Fintype.card ι + 1) * (K * H) ^ Fintype.card ι) := by
  classical
  have he : f.repr (T x) j = ∑ i, e.repr x i * f.repr (T (e i)) j := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  exact rationalHeightLE_sum _ (fun i => (hx i).mul (hT i j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem freeWordCoefficients_word (w : FreeMonoid X) :
    freeWordCoefficients (freeWord w) = Finsupp.single w 1 := by
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (freeWord w)).coeff = _
  rw [freeWord_coeff]
  rfl

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

namespace FreeCoefficientBound

variable {s D E M N : ℕ} {p q : FreeAlgebra ℚ X}

theorem word (s : ℕ) (w : FreeMonoid X) : FreeCoefficientBound s 1 1 (freeWord w) := by
  classical
  intro v _
  by_cases hv : w = v
  · refine ⟨1, ?_, by simp⟩
    simp [freeWordCoefficients_word, hv]
  · refine ⟨0, ?_, by simp⟩
    simp [freeWordCoefficients_word, hv]

theorem one (s : ℕ) : FreeCoefficientBound (X := X) s 1 1 1 := by
  simpa only [map_one] using word s (1 : FreeMonoid X)

end FreeCoefficientBound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

attribute [instance] FiniteProgressionPartition.labelFintype

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

theorem card_cell (i : P.Label) : (partitionCell P.cell i).card = P.length i := by
  simpa only [Fintype.card_coe, Fintype.card_fin] using (Fintype.card_congr (P.pointEquiv i)).symm

end FiniteProgressionPartition
end Erdos3

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

theorem expect_cell (a : ∀ i, (P i).Label) (f : (∀ i, Fin (N i)) → ℝ) :
    (𝔼 x ∈ partitionCell (cell P) a, f x) =
      𝔼 j : (∀ i, Fin ((P i).length (a i))), f (point P a j) := by
  have h := Fintype.expect_equiv (pointEquiv P a)
    (fun j => f (point P a j)) (fun x => f x.val) (fun _ => rfl)
  have hcoe : (𝔼 x : ↥(partitionCell (cell P) a), f x.val) =
      𝔼 x ∈ partitionCell (cell P) a, f x := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
      Finset.sum_coe_sort]
  exact hcoe.symm.trans h.symm

end Erdos3.BoxProgressionPartition

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_partition_cell_norm_mean_le {X K : Type*} [Fintype X] [Nonempty X]
    [Fintype K] (cell : X → K) (f : X → ℂ) :
    ∃ k, (partitionCell cell k).Nonempty ∧
      ‖𝔼 x, f x‖ ≤ ‖𝔼 x ∈ partitionCell cell k, f x‖ := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.univ.exists_max_image
    (fun x : X => ‖𝔼 y ∈ partitionCell cell (cell x), f y‖) Finset.univ_nonempty
  have hmax (k : K) : ‖𝔼 y ∈ partitionCell cell k, f y‖ ≤
      ‖𝔼 y ∈ partitionCell cell (cell x), f y‖ := by
    by_cases hk : (partitionCell cell k).Nonempty
    · obtain ⟨y, hy⟩ := hk
      have h := hx y (Finset.mem_univ _)
      simpa only [(mem_partitionCell cell k y).mp hy] using h
    · rw [Finset.not_nonempty_iff_eq_empty.mp hk]
      simp only [Finset.expect_empty, norm_zero]
      exact norm_nonneg (𝔼 y ∈ partitionCell cell (cell x), f y)
  refine ⟨cell x, ⟨x, (mem_partitionCell cell _ _).mpr rfl⟩, ?_⟩
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := X))
  rw [complex_expect_partition_count_weights cell f, card_partitionCell_sum]
  calc
    _ ≤ ∑ k, ‖(((partitionCell cell k).card : ℝ) / Fintype.card X : ℂ) *
        (𝔼 y ∈ partitionCell cell k, f y)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ((partitionCell cell k).card : ℝ) / Fintype.card X *
        ‖𝔼 y ∈ partitionCell cell (cell x), f y‖ := by
      apply Finset.sum_le_sum
      intro k _
      simp only [norm_mul, norm_div, Complex.norm_real, norm_natCast]
      exact mul_le_mul_of_nonneg_left (hmax k) (by positivity)
    _ = ‖𝔼 y ∈ partitionCell cell (cell x), f y‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_div, card_partitionCell_sum, div_self hcard,
        one_mul]

namespace BoxProgressionPartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

theorem expect_cell_complex (a : ∀ i, (P i).Label) (f : (∀ i, Fin (N i)) → ℂ) :
    (𝔼 x ∈ partitionCell (cell P) a, f x) =
      𝔼 j : (∀ i, Fin ((P i).length (a i))), f (point P a j) := by
  have h := Fintype.expect_equiv (pointEquiv P a)
    (fun j => f (point P a j)) (fun x => f x.val) (fun _ => rfl)
  have hcoe : (𝔼 x : ↥(partitionCell (cell P) a), f x.val) =
      𝔼 x ∈ partitionCell (cell P) a, f x := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
      Finset.sum_coe_sort]
  exact hcoe.symm.trans h.symm

theorem exists_positive_box_norm_mean_le (hN : ∀ i, 0 < N i) (f : (ι → ℕ) → ℂ) :
    ∃ a : ∀ i, (P i).Label, (∀ i, 0 < (P i).length (a i)) ∧
      ‖𝔼 x : (∀ i, Fin (N i)), f (fun i => (x i).val)‖ ≤
        ‖𝔼 j : (∀ i, Fin ((P i).length (a i))),
          f (fun i => (P i).start (a i) + (P i).step (a i) * (j i).val)‖ := by
  classical
  let : Nonempty (∀ i, Fin (N i)) := ⟨fun i => ⟨0, hN i⟩⟩
  obtain ⟨a, ha, hmean⟩ := exists_partition_cell_norm_mean_le (cell P)
    (fun x => f (fun i => (x i).val))
  refine ⟨a, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := ha
    let j := (pointEquiv P a).symm ⟨x, hx⟩
    exact fun i => Nat.zero_lt_of_lt (j i).isLt
  · rw [expect_cell_complex] at hmean
    simpa only [point_val] using hmean

end BoxProgressionPartition
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3

namespace FiniteProgressionPartition

theorem entireResidue_length_ge {N q H : ℕ} (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (blocks N q (N + 1) hq (Nat.succ_pos N)).Label) :
    H ≤ (blocks N q (N + 1) hq (Nat.succ_pos N)).length i := by
  have hdiv : N / q / (N + 1) = 0 :=
    Nat.div_eq_of_lt ((Nat.div_le_self N q).trans_lt (Nat.lt_succ_self N))
  have hi : i.2.val = 0 := by
    have hi := i.2.isLt
    omega
  have hHN : H ≤ N := (Nat.le_mul_of_pos_left H hq).trans hfit
  have hlast : i.1.val + q * (H - 1) < N := by
    calc
      _ < q + q * (H - 1) := Nat.add_lt_add_right i.1.isLt _
      _ = q * ((H - 1) + 1) := by ring
      _ = q * H := by rw [Nat.sub_add_cancel hH]
      _ ≤ N := hfit
  have hlen : H - 1 < truncatedProgressionLength N (progressionBlockStart i) q (N + 1) := by
    apply (lt_truncatedProgressionLength_iff hq).mpr
    refine ⟨by omega, ?_⟩
    simpa only [progressionBlockStart, hi, Nat.mul_zero, Nat.add_zero] using hlast
  change H ≤ truncatedProgressionLength N (progressionBlockStart i) q (N + 1)
  omega

noncomputable def comparableResidues (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) : FiniteProgressionPartition N :=
  (blocks N q (N + 1) hq (Nat.succ_pos N)).bind
    (fun i => mergedIntervals _ H hH (entireResidue_length_ge hq hH hfit i))

theorem comparableResidues_step (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidues N q H hq hH hfit).Label) :
    (comparableResidues N q H hq hH hfit).step i = q := by
  change q * 1 = q
  exact mul_one q

theorem comparableResidues_length (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidues N q H hq hH hfit).Label) :
    H ≤ (comparableResidues N q H hq hH hfit).length i ∧
      (comparableResidues N q H hq hH hfit).length i < 2 * H :=
  mergedIntervals_length_bounds _ H hH (entireResidue_length_ge hq hH hfit i.1) i.2

end FiniteProgressionPartition

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice
variable {X : Type*} {N : X → ℕ} {q : ℕ}

theorem residueIndex_endpoint_le (S : ResidueBoxSlice N q) (hq : 0 < q)
    (hlen : ∀ i, 0 < S.length i) (i : X) :
    S.start i / q + S.length i ≤ N i := by
  have hi := S.inside i (S.length i - 1) (by have := hlen i; omega)
  have hmul : S.length i - 1 ≤ q * (S.length i - 1) := by nlinarith
  have hdiv : S.start i / q ≤ S.start i := Nat.div_le_self _ _
  omega

end ResidueBoxSlice
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieStructureTransport
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem transportedLieConstants_height (c : ι → ι → ι → ℚ)
    (P : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) {Hc HP HS : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) Hc)
    (hP : ∀ i j, RationalHeightLE (P i j) HP)
    (hS : ∀ i j, RationalHeightLE (S i j) HS) (i j k : κ) :
    RationalHeightLE (transportedLieConstants c P S i j k)
      ((Fintype.card ι ^ 3 + 1) * (HP * Hc * HS * HS) ^ (Fintype.card ι ^ 3)) := by
  classical
  have h := rationalHeightLE_sum
    (fun abc : ι × (ι × ι) => P k abc.1 * c abc.2.1 abc.2.2 abc.1 * S abc.2.1 i * S abc.2.2 j)
    (fun abc => (((hP k abc.1).mul (hc abc.2.1 abc.2.2 abc.1)).mul (hS abc.2.1 i)).mul (hS abc.2.2 j))
  simpa only [transportedLieConstants, Fintype.card_prod, pow_succ, pow_zero, one_mul, mul_assoc] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalLieSubalgebra
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem transportedLieConstants_height_uniform (c : ι → ι → ι → ℚ)
    (P : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (hP : ∀ i j, RationalHeightLE (P i j) H)
    (hS : ∀ i j, RationalHeightLE (S i j) H) (i j k : κ) :
    RationalHeightLE (transportedLieConstants c P S i j k) (rationalLieStructureHeight (Fintype.card ι) H) := by
  have h := transportedLieConstants_height c P S hc hP hS i j k
  simpa only [rationalLieStructureHeight, pow_succ, pow_zero, one_mul] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmbeddedFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eq_of_weight_eq {X : Type*} [Fintype X] {p q : FiniteProbabilityWeights X}
    (h : ∀ x, p.weight x = q.weight x) : p = q := by
  cases p with
  | mk wp hp tp =>
    cases q with
    | mk wq hq tq =>
      have he : wp = wq := funext h
      subst wq
      rfl

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffinePhaseBias
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace CircleFourier

theorem linearPhaseMean_eq_product {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → ℕ) (a : ι → Circle) :
    linearPhaseMean T a = ∏ i, geometricCharacterMean (T i) (a i) := by
  simp only [linearPhaseMean, character_fintype_sum, geometricCharacterMean]
  exact expect_pi_product (fun i (n : Fin (T i)) => character ((n : ℕ) • a i))

end CircleFourier
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem ext_weight {Ω : Type*} [Fintype Ω] {p q : FiniteProbabilityWeights Ω}
    (h : p.weight = q.weight) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem mass_inter_pos_of_condition {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G)
    (hR : 0 < (p.condition G hG).mass R) : 0 < p.mass (G ∩ R) := by
  rw [condition_mass] at hR
  exact (div_pos_iff_of_pos_right hG).mp hR

theorem condition_condition {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (G R : Finset Ω) (hG : 0 < p.mass G)
    (hR : 0 < (p.condition G hG).mass R) :
    (p.condition G hG).condition R hR =
      p.condition (G ∩ R) (mass_inter_pos_of_condition p G R hG hR) := by
  have hw : ((p.condition G hG).condition R hR).weight =
      (p.condition (G ∩ R) (mass_inter_pos_of_condition p G R hG hR)).weight := by
    funext x
    change (if x ∈ R then (if x ∈ G then p.weight x else 0) / p.mass G else 0) /
        (p.condition G hG).mass R =
      (if x ∈ G ∩ R then p.weight x else 0) / p.mass (G ∩ R)
    rw [condition_mass]
    by_cases hxG : x ∈ G <;> by_cases hxR : x ∈ R <;>
      simp [hxG, hxR, div_div_div_cancel_right₀ hG.ne']
  exact ext_weight hw

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eventProbability_mem {X : Type*} [Fintype X] [DecidableEq X]
    (p : FiniteProbabilityWeights X) (G : Finset X) :
    p.eventProbability (fun x => x ∈ G) = p.mass G := by
  classical
  simp [eventProbability, mean, mass, mul_ite]

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]

theorem piRestriction_mass (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) : (pi p).mass (piRestrictionSet G) = ∏ j, (p j).mass (G j) := by
  classical
  rw [← eventProbability_mem]
  have hE : (fun x : ∀ j, Ω j => x ∈ piRestrictionSet G) =
      (fun x => ∀ j, x j ∈ G j) := by
    funext x
    exact propext (mem_piRestrictionSet G x)
  rw [hE, eventProbability_pi]
  exact Finset.prod_congr rfl (fun j _ => eventProbability_mem (p j) (G j))

theorem piRestriction_mass_pos (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) (hG : ∀ j, 0 < (p j).mass (G j)) :
    0 < (pi p).mass (piRestrictionSet G) := by
  rw [piRestriction_mass]
  exact Finset.prod_pos (fun j _ => hG j)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

noncomputable def integralRealPolynomialSubring (σ : Type*) : Subring (MvPolynomial σ ℝ) :=
  (MvPolynomial.map (Int.castRingHom ℝ)).range

theorem C_int_mem_integralRealPolynomialSubring (z : ℤ) :
    C (z : ℝ) ∈ integralRealPolynomialSubring σ :=
  ⟨C z, by simp⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.IntegralGridFunctional
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem coordinateGrid_bracket_divisible (e : Basis ι ℚ L) (B D : ℕ)
    (hc : ∀ i j k, ∃ n : ℤ, (B : ℚ) * lieStructureConstants e i j k = (D : ℚ) * n)
    {a b : L} (ha : a ∈ coordinateGridModule e B) (hb : b ∈ coordinateGridModule e B) :
    ∃ z ∈ coordinateGridModule e B, ⁅a, b⁆ = (D : ℚ) • z := by
  classical
  choose c hc using hc
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  let w : ι → ℤ := fun k => ∑ ij : ι × ι, c ij.1 ij.2 k * u ij.1 * v ij.2
  let z : L := e.equivFun.symm ((B : ℚ) • fun k => (w k : ℚ))
  have hz : e.equivFun z = (B : ℚ) • fun k => (w k : ℚ) := e.equivFun.apply_symm_apply _
  refine ⟨z, ⟨w, hz⟩, ?_⟩
  apply e.equivFun.injective
  ext k
  rw [map_smul, hz]
  change e.repr ⁅a, b⁆ k = (D : ℚ) * ((B : ℚ) * (w k : ℚ))
  rw [lie_coordinate_formula]
  have hu' (i : ι) : e.repr a i = (B : ℚ) * (u i : ℚ) := congrFun hu i
  have hv' (i : ι) : e.repr b i = (B : ℚ) * (v i : ℚ) := congrFun hv i
  simp only [w, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [hu', hv']
  calc
    _ = (B : ℚ) * (((B : ℚ) * lieStructureConstants e ij.1 ij.2 k) * u ij.1 * v ij.2) := by ring
    _ = (D : ℚ) * ((B : ℚ) * ((c ij.1 ij.2 k : ℚ) * u ij.1 * v ij.2)) := by
      rw [hc]
      ring

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem coordinateGrid_functional_integral {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] (b : Basis ι ℚ L) (η : L →ₗ[ℚ] ℚ)
    (l B : ℕ) (hdiv : l ∣ B)
    (hη : ∀ i, ∃ n : ℤ, (l : ℚ) * η (b i) = n)
    {x : L} (hx : x ∈ coordinateGridModule b B) : ∃ n : ℤ, η x = n := by
  classical
  obtain ⟨k, hk⟩ := hdiv
  obtain ⟨z, hz⟩ := hx
  choose n hn using hη
  refine ⟨∑ i, (k : ℤ) * z i * n i, ?_⟩
  rw [← b.sum_repr x, map_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : b.repr x i = (B : ℚ) * (z i : ℚ) := congrFun hz i
  rw [map_smul, smul_eq_mul, hi, hk, Nat.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_natCast]
  calc
    _ = (k : ℚ) * (z i : ℚ) * ((l : ℚ) * η (b i)) := by ring
    _ = _ := by rw [hn i]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

def weightedLieTreeGenerators (v : I → L) (w : I → ℕ) (d r : ℕ) : Set L :=
  {x | ∃ a : FreeMagma I, lieTreeWeight w a = d ∧ r ≤ a.length ∧ lieTreeEval v a = x}

def weightedLieTreeSpan (v : I → L) (w : I → ℕ) (d r : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ (weightedLieTreeGenerators v w d r)

theorem weightedLieTreeSpan_lie_mem (v : I → L) (w : I → ℕ) {d e r t : ℕ} {x y : L}
    (hx : x ∈ weightedLieTreeSpan v w d r) (hy : y ∈ weightedLieTreeSpan v w e t) :
    ⁅x, y⁆ ∈ weightedLieTreeSpan v w (d + e) (r + t) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, hi, rfl⟩ := hx
    obtain ⟨b, hb, hj, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, congrArg₂ (· + ·) ha hb, Nat.add_le_add hi hj, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem span_weighted_leaves_le (v : I → L) (w : I → ℕ) (d : ℕ) :
    Submodule.span ℚ (v '' {i | w i = d}) ≤ weightedLieTreeSpan v w d 1 := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, hi, rfl⟩
  exact Submodule.subset_span ⟨.of i, hi, le_rfl, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

omit [Fintype ι] in
theorem basis_repr_height_one (e : Basis ι ℚ L) (i j : ι) :
    RationalHeightLE (e.repr (e i) j) 1 := by
  classical
  simp only [Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact rationalHeightLE_one (by omega)
  · exact rationalHeightLE_zero (by omega)

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

theorem real_image_section_norm_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix κ ι ℚ) (H : ℕ)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (x : ι → ℝ) :
    ‖(fun i j => (S i j : ℝ)) *ᵥ x‖ ≤ Real.exp ((p + 2) ^ 18) * ‖x‖ := by
  have hnorm := norm_matrix_mulVec_le (fun i j => (S i j : ℝ))
    (rationalKernelHeight (Fintype.card ι) H : ℝ≥0) (fun i j => (hS i j).abs_real_le) x
  have hfac : ((Fintype.card ι : ℝ) + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1) ≤
      (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι)
        (rationalKernelHeight (Fintype.card ι) H) : ℝ) := by
    change _ ≤ ((Fintype.card κ : ℝ) + Fintype.card ι + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1)
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact hnorm.trans (mul_le_mul_of_nonneg_right
    (hfac.trans (imageSection_bound_le_exp (Fintype.card κ) (Fintype.card ι) H hp hκ hι hH))
    (norm_nonneg _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FinitePushforwardComplexWeights
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {U T : Type*} [Fintype U] [Fintype T]

noncomputable def finitePushforward (p : FiniteProbabilityWeights U) (f : U → T) :
    FiniteProbabilityWeights T := by
  classical
  refine ⟨fun t => ∑ u, if f u = t then p.weight u else 0, ?_, ?_⟩
  · intro t
    exact Finset.sum_nonneg (fun u _ => by split <;> simp_all only [p.nonneg, le_refl])
  · rw [Finset.sum_comm]
    simpa using p.total

theorem mean_finitePushforward (p : FiniteProbabilityWeights U) (f : U → T) (g : T → ℝ) :
    (p.finitePushforward f).mean g = p.mean (fun u => g (f u)) := by
  classical
  simp only [mean, finitePushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [ite_mul, zero_mul]
  simp

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {U T : Type*} [Fintype U] [Fintype T]

theorem complexMean_finitePushforward (p : FiniteProbabilityWeights U)
    (f : U → T) (g : T → ℂ) :
    (p.finitePushforward f).complexMean g = p.complexMean (fun u => g (f u)) := by
  classical
  simp only [complexMean, finitePushforward, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul]
  simp

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IteratedCircleAverageIntegral
namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators NNReal

theorem integral_circleCharacter (n : ℤ) :
    (∫ t : Circle, character (n • t) ∂circleHaar) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [hn, ite_false]
    exact integral_eq_zero_of_add_right_eq_neg (μ := circleHaar)
      (fourier_add_half_inv_index hn (by norm_num))

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

theorem average_eq_integral (A : IsometricCircleAction X) (f : X → ℂ) (x : X) :
    A.average f x = ∫ t : Circle, f (A.act t x) ∂circleHaar := by
  simp [average, circleFourierComponent]
  rfl

theorem average_const (A : IsometricCircleAction X) (c : ℂ) (x : X) :
    A.average (fun _ => c) x = c := by
  simp [average_eq_integral]

theorem average_unit_interval (A : IsometricCircleAction X) {f : X → ℂ}
    (hf : Continuous f) (hb : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1) (x : X) :
    (A.average f x).im = 0 ∧ 0 ≤ (A.average f x).re ∧ (A.average f x).re ≤ 1 := by
  have hcont : Continuous (fun t : Circle => f (A.act t x)) :=
    hf.comp (A.continuous_act.comp (continuous_id.prodMk continuous_const))
  have hi := circle_integrable_of_continuous hcont
  have him : (∫ t : Circle, f (A.act t x) ∂circleHaar).im =
      ∫ t : Circle, (f (A.act t x)).im ∂circleHaar := (integral_im hi).symm
  have hre : (∫ t : Circle, f (A.act t x) ∂circleHaar).re =
      ∫ t : Circle, (f (A.act t x)).re ∂circleHaar := (integral_re hi).symm
  rw [average_eq_integral, him, hre]
  refine ⟨?_, integral_nonneg (fun t => (hb (A.act t x)).2.1), ?_⟩
  · simp_rw [(hb _).1]
    simp
  · have hle := integral_mono (circle_integrable_of_continuous (Complex.continuous_re.comp hcont))
      (integrable_const (1 : ℝ)) (fun t => (hb (A.act t x)).2.2)
    simpa using hle

theorem average_sub (A : IsometricCircleAction X) {f g : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) (x : X) :
    A.average (fun y => f y - g y) x = A.average f x - A.average g x := by
  simp only [average_eq_integral]
  apply integral_sub
  · exact circle_integrable_of_continuous
      (hf.comp (A.continuous_act.comp (continuous_id.prodMk continuous_const)))
  · exact circle_integrable_of_continuous
      (hg.comp (A.continuous_act.comp (continuous_id.prodMk continuous_const)))

theorem average_sub_norm_le (A : IsometricCircleAction X) {f g : X → ℂ} {B : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x, ‖f x - g x‖ ≤ B) (x : X) :
    ‖A.average f x - A.average g x‖ ≤ B := by
  rw [← A.average_sub hf hg]
  exact A.average_norm_le hfg x

theorem average_sum {ι : Type*} (A : IsometricCircleAction X) (s : Finset ι)
    (f : ι → X → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) (x : X) :
    A.average (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, A.average (f i) x := by
  simp only [average_eq_integral]
  apply integral_finsetSum
  intro i hi
  exact circle_integrable_of_continuous
    ((hf i hi).comp (A.continuous_act.comp (continuous_id.prodMk continuous_const)))

theorem average_equivariant (A : IsometricCircleAction X) {f : X → ℂ}
    (g : X → X) (z : ℂ) (hcomm : ∀ t x, A.act t (g x) = g (A.act t x))
    (hf : ∀ x, f (g x) = z * f x) (x : X) :
    A.average f (g x) = z * A.average f x := by
  simp only [average_eq_integral]
  simp_rw [hcomm, hf]
  exact integral_const_mul z _

theorem average_eigenfunction (A : IsometricCircleAction X) {f : X → ℂ} (n : ℤ)
    (hf : ∀ t x, f (A.act t x) = character (n • t) * f x) (x : X) :
    A.average f x = if n = 0 then f x else 0 := by
  rw [average_eq_integral]
  simp_rw [hf]
  rw [integral_mul_const, integral_circleCharacter]
  split_ifs <;> simp

end IsometricCircleAction
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X α : Type*} [PseudoMetricSpace X]

theorem iteratedCircleAverage_unit_interval (A : α → IsometricCircleAction X) (is : List α)
    {f : X → ℂ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hb : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1) :
    ∀ x, (iteratedCircleAverage A is f x).im = 0 ∧
      0 ≤ (iteratedCircleAverage A is f x).re ∧ (iteratedCircleAverage A is f x).re ≤ 1 := by
  induction is with
  | nil => exact hb
  | cons i is ih =>
    exact (A i).average_unit_interval (iteratedCircleAverage_lipschitz A is hf).continuous ih

theorem iteratedCircleAverage_sub_norm_le (A : α → IsometricCircleAction X) (is : List α)
    {f g : X → ℂ} {Lf Lg : ℝ≥0} {B : ℝ} (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hfg : ∀ x, ‖f x - g x‖ ≤ B) :
    ∀ x, ‖iteratedCircleAverage A is f x - iteratedCircleAverage A is g x‖ ≤ B := by
  induction is with
  | nil => exact hfg
  | cons i is ih =>
    exact (A i).average_sub_norm_le (iteratedCircleAverage_lipschitz A is hf).continuous
      (iteratedCircleAverage_lipschitz A is hg).continuous ih

theorem iteratedCircleAverage_sum {ι : Type*} (A : α → IsometricCircleAction X) (is : List α)
    (s : Finset ι) (f : ι → X → ℂ) (L : ι → ℝ≥0) (hf : ∀ i ∈ s, LipschitzWith (L i) (f i)) :
    ∀ x, iteratedCircleAverage A is (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, iteratedCircleAverage A is (f i) x := by
  induction is with
  | nil => intro x; rfl
  | cons i is ih =>
    have heq : iteratedCircleAverage A is (fun y => ∑ j ∈ s, f j y) =
        fun y => ∑ j ∈ s, iteratedCircleAverage A is (f j) y := funext ih
    intro x
    change (A i).average (iteratedCircleAverage A is (fun y => ∑ j ∈ s, f j y)) x = _
    rw [heq]
    exact (A i).average_sum s _ (fun j hj => (iteratedCircleAverage_lipschitz A is (hf j hj)).continuous) x

theorem iteratedCircleAverage_eigenfunction (A : α → IsometricCircleAction X) (is : List α)
    (n : α → ℤ) (f : X → ℂ)
    (hf : ∀ i ∈ is, ∀ t x, f ((A i).act t x) = character (n i • t) * f x) :
    iteratedCircleAverage A is f = if ∀ i ∈ is, n i = 0 then f else fun _ => 0 := by
  classical
  induction is with
  | nil => simp [iteratedCircleAverage]
  | cons i is ih =>
    have ht := ih (fun j hj => hf j (by simp [hj]))
    rw [iteratedCircleAverage, ht]
    by_cases htail : ∀ j ∈ is, n j = 0
    · have htail' : (∀ j ∈ is, n j = 0) = True := eq_true htail
      simp only [List.forall_mem_cons, htail', ite_true, and_true]
      funext x
      rw [(A i).average_eigenfunction (n i) (hf i (by simp))]
      split_ifs <;> rfl
    · have htail' : (∀ j ∈ is, n j = 0) = False := eq_false htail
      simp only [List.forall_mem_cons, htail', ite_false, and_false]
      funext x
      exact (A i).average_const 0 x

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory

variable {α : Type*}

instance circleAverageTupleMeasurableSpace : (is : List α) → MeasurableSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (MeasurableSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleMeasurableSpace is
      inferInstanceAs (MeasurableSpace (Circle × CircleAverageTuple is))

instance circleAverageTupleTopologicalSpace : (is : List α) → TopologicalSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (TopologicalSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleTopologicalSpace is
      inferInstanceAs (TopologicalSpace (Circle × CircleAverageTuple is))

instance circleAverageTupleSecondCountableTopology :
    (is : List α) → SecondCountableTopology (CircleAverageTuple is)
  | [] => inferInstanceAs (SecondCountableTopology Unit)
  | _ :: is =>
      let _ := circleAverageTupleSecondCountableTopology is
      inferInstanceAs (SecondCountableTopology (Circle × CircleAverageTuple is))

instance circleAverageTupleBorelSpace : (is : List α) → BorelSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (BorelSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleBorelSpace is
      inferInstanceAs (BorelSpace (Circle × CircleAverageTuple is))

instance circleAverageTupleCompactSpace : (is : List α) → CompactSpace (CircleAverageTuple is)
  | [] => inferInstanceAs (CompactSpace Unit)
  | _ :: is =>
      let _ := circleAverageTupleCompactSpace is
      inferInstanceAs (CompactSpace (Circle × CircleAverageTuple is))

noncomputable def circleAverageTupleMeasure : (is : List α) → Measure (CircleAverageTuple is)
  | [] => Measure.dirac ()
  | _ :: is => circleHaar.prod (circleAverageTupleMeasure is)

instance circleAverageTupleMeasure_probability :
    (is : List α) → IsProbabilityMeasure (circleAverageTupleMeasure is)
  | [] => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | _ :: is =>
      let _ := circleAverageTupleMeasure_probability is
      inferInstanceAs (IsProbabilityMeasure (circleHaar.prod (circleAverageTupleMeasure is)))

variable {X : Type*} [PseudoMetricSpace X]

def iteratedCircleAction (A : α → IsometricCircleAction X) :
    (is : List α) → CircleAverageTuple is → X → X
  | [], _, x => x
  | i :: is, t, x => iteratedCircleAction A is t.2 ((A i).act t.1 x)

theorem continuous_iteratedCircleAction (A : α → IsometricCircleAction X) (is : List α) :
    Continuous (fun p : CircleAverageTuple is × X =>
      iteratedCircleAction A is p.1 p.2) := by
  induction is with
  | nil => exact continuous_snd
  | cons i is ih =>
      change Continuous (fun p : (Circle × CircleAverageTuple is) × X =>
        iteratedCircleAction A is p.1.2 ((A i).act p.1.1 p.2))
      exact ih.comp (continuous_fst.snd.prodMk
        ((A i).continuous_act.comp (continuous_fst.fst.prodMk continuous_snd)))

theorem continuous_iteratedCircleAction_parameter (A : α → IsometricCircleAction X)
    (is : List α) (x : X) : Continuous (fun t => iteratedCircleAction A is t x) :=
  (continuous_iteratedCircleAction A is).comp (continuous_id.prodMk continuous_const)

theorem integrable_iteratedCircleAction (A : α → IsometricCircleAction X)
    (is : List α) {f : X → ℂ} (hf : Continuous f) (x : X) :
    Integrable (fun t => f (iteratedCircleAction A is t x))
      (circleAverageTupleMeasure is) :=
  (hf.comp (continuous_iteratedCircleAction_parameter A is x)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem iteratedCircleAverage_eq_integral (A : α → IsometricCircleAction X)
    (is : List α) {f : X → ℂ} (hf : Continuous f) (x : X) :
    iteratedCircleAverage A is f x =
      ∫ t, f (iteratedCircleAction A is t x) ∂circleAverageTupleMeasure is := by
  induction is generalizing x with
  | nil =>
      change f x = ∫ _ : CircleAverageTuple ([] : List α), f x
        ∂circleAverageTupleMeasure ([] : List α)
      simp
  | cons i is ih =>
      change (A i).average (iteratedCircleAverage A is f) x =
        ∫ t : Circle × CircleAverageTuple is,
          f (iteratedCircleAction A is t.2 ((A i).act t.1 x))
          ∂circleHaar.prod (circleAverageTupleMeasure is)
      rw [(A i).average_eq_integral]
      have hint : Integrable
          (fun t : Circle × CircleAverageTuple is =>
            f (iteratedCircleAction A is t.2 ((A i).act t.1 x)))
          (circleHaar.prod (circleAverageTupleMeasure is)) :=
        integrable_iteratedCircleAction A (i :: is) hf x
      rw [integral_prod _ hint]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun t => ih ((A i).act t x)))

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
namespace OAI

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

noncomputable def argumentCode (B : Set N) (m : ℕ) (x : ZMod N) :
    (r : ↥B.frequencies) → Fin (m + 1) :=
  fun r ↦ argBin m (character r.1 x)

lemma abs_arg_character_le_two_radius (B : Set N) {x r : ZMod N}
    (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    |(character r x).arg| ≤ 2 * B.radius := by
  have hnorm := Set.mem_iff.mp hx r hr
  have hangle := Complex.angle_le_mul_norm_sub
    (norm_character r x) (by norm_num : ‖(1 : ℂ)‖ = 1)
  calc
    |(character r x).arg| = InnerProductGeometry.angle (character r x) 1 :=
      (Complex.angle_one_right (norm_ne_zero_iff.mp (by
        rw [norm_character]
        norm_num))).symm
    _ ≤ Real.pi / 2 * ‖character r x - 1‖ := hangle
    _ = Real.pi / 2 * ‖1 - character r x‖ := by rw [norm_sub_rev]
    _ ≤ Real.pi / 2 * B.radius :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ 2 * B.radius := by
      apply mul_le_mul_of_nonneg_right _ B.radius_nonneg
      linarith [Real.pi_lt_four]

noncomputable def localScaledArg (B : Set N) (z : ℂ) : ℝ :=
  2 * (z.arg + 2 * B.radius) / B.radius

lemma localScaledArg_nonneg (B : Set N) {x r : ZMod N}
    (hB : 0 < B.radius) (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    0 ≤ localScaledArg B (character r x) := by
  have harg := abs_arg_character_le_two_radius B hx hr
  rw [abs_le] at harg
  unfold localScaledArg
  have hsum : 0 ≤ (character r x).arg + 2 * B.radius := by linarith [harg.1]
  exact div_nonneg (mul_nonneg (by norm_num) hsum) hB.le

lemma localScaledArg_le_eight (B : Set N) {x r : ZMod N}
    (hB : 0 < B.radius) (hx : x ∈ B) (hr : r ∈ B.frequencies) :
    localScaledArg B (character r x) ≤ 8 := by
  have harg := abs_arg_character_le_two_radius B hx hr
  rw [abs_le] at harg
  unfold localScaledArg
  rw [div_le_iff₀ hB]
  linarith

noncomputable def localArgBin (B : Set N) (hB : 0 < B.radius)
    (x : ↥B.carrier) (r : ↥B.frequencies) : Fin 9 :=
  ⟨⌊localScaledArg B (character r.1 x.1)⌋₊, by
    rw [Nat.floor_lt' (by norm_num : (9 : ℕ) ≠ 0)]
    exact (localScaledArg_le_eight B hB x.2 r.2).trans_lt (by norm_num)⟩

noncomputable def localArgumentCode (B : Set N) (hB : 0 < B.radius)
    (x : ↥B.carrier) : (r : ↥B.frequencies) → Fin 9 :=
  fun r ↦ localArgBin B hB x r

lemma abs_localScaledArg_sub_lt_one_of_localArgBin_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    {r : ↥B.frequencies}
    (hbin : localArgBin B hB x r = localArgBin B hB y r) :
    |localScaledArg B (character r.1 x.1) -
      localScaledArg B (character r.1 y.1)| < 1 := by
  have hfloor :
      ⌊localScaledArg B (character r.1 x.1)⌋₊ =
        ⌊localScaledArg B (character r.1 y.1)⌋₊ :=
    congrArg Fin.val hbin
  have hfloorR :
      (⌊localScaledArg B (character r.1 x.1)⌋₊ : ℝ) =
        ⌊localScaledArg B (character r.1 y.1)⌋₊ := by
    exact_mod_cast hfloor
  have hxlow :
      (⌊localScaledArg B (character r.1 x.1)⌋₊ : ℝ) ≤
        localScaledArg B (character r.1 x.1) :=
    Nat.floor_le (localScaledArg_nonneg B hB x.2 r.2)
  have hylow :
      (⌊localScaledArg B (character r.1 y.1)⌋₊ : ℝ) ≤
        localScaledArg B (character r.1 y.1) :=
    Nat.floor_le (localScaledArg_nonneg B hB y.2 r.2)
  have hxup := Nat.lt_floor_add_one
    (localScaledArg B (character r.1 x.1))
  have hyup := Nat.lt_floor_add_one
    (localScaledArg B (character r.1 y.1))
  rw [abs_lt]
  constructor <;> nlinarith

lemma abs_arg_sub_lt_half_radius_of_localArgBin_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    {r : ↥B.frequencies}
    (hbin : localArgBin B hB x r = localArgBin B hB y r) :
    |(character r.1 x.1).arg - (character r.1 y.1).arg| < B.radius / 2 := by
  have h := abs_localScaledArg_sub_lt_one_of_localArgBin_eq B hB hbin
  have hscale :
      |localScaledArg B (character r.1 x.1) -
        localScaledArg B (character r.1 y.1)| =
      2 * |(character r.1 x.1).arg - (character r.1 y.1).arg| / B.radius := by
    have heq :
        localScaledArg B (character r.1 x.1) -
          localScaledArg B (character r.1 y.1) =
        2 * ((character r.1 x.1).arg - (character r.1 y.1).arg) /
          B.radius := by
      unfold localScaledArg
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hB]
    norm_num
  rw [hscale] at h
  rw [div_lt_iff₀ hB] at h
  linarith

lemma sub_mem_half_dilate_of_localArgumentCode_eq
    (B : Set N) (hB : 0 < B.radius) {x y : ↥B.carrier}
    (hcode : localArgumentCode B hB x = localArgumentCode B hB y) :
    x.1 - y.1 ∈ B.dilate (1 / 2 : ℝ) := by
  rw [Set.mem_iff]
  intro r hr
  have hbin : localArgBin B hB x ⟨r, hr⟩ =
      localArgBin B hB y ⟨r, hr⟩ := congrFun hcode ⟨r, hr⟩
  calc
    ‖1 - character r (x.1 - y.1)‖ =
        ‖character r x.1 - character r y.1‖ :=
      norm_one_sub_character_sub r x.1 y.1
    _ ≤ |(character r x.1).arg - (character r y.1).arg| :=
      norm_sub_le_abs_arg_sub_of_norm_eq_one
        (norm_character r x.1) (norm_character r y.1)
    _ ≤ B.radius / 2 :=
      (abs_arg_sub_lt_half_radius_of_localArgBin_eq B hB hbin).le
    _ = (B.dilate (1 / 2 : ℝ)).radius := by
      simp [div_eq_mul_inv, mul_comm]

theorem card_carrier_le_nine_pow_rank_mul_card_half
    (B : Set N) (hB : 0 < B.radius) :
    B.carrier.card ≤ 9 ^ B.rank * (B.dilate (1 / 2 : ℝ)).carrier.card := by
  let Q := (r : ↥B.frequencies) → Fin 9
  let code : ↥B.carrier → Q := localArgumentCode B hB
  have hQ : Fintype.card Q = 9 ^ B.rank := by
    simpa [Q] using card_localArgumentCodeSpace B
  have hmain : Fintype.card ↥B.carrier ≤
      Fintype.card Q * (B.dilate (1 / 2 : ℝ)).carrier.card := by
    by_contra hbound
    rw [not_le] at hbound
    obtain ⟨q, hq⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := code) hbound
    let S : Finset ↥B.carrier := Finset.univ.filter fun x ↦ code x = q
    have hScard : (B.dilate (1 / 2 : ℝ)).carrier.card < S.card := by
      simpa [S] using hq
    have hSnonempty : S.Nonempty := Finset.card_pos.mp
      (lt_of_le_of_lt (Nat.zero_le _) hScard)
    obtain ⟨x₀, hx₀⟩ := hSnonempty
    let e : ↥B.carrier ↪ ZMod N :=
      ⟨fun x ↦ x.1 - x₀.1, by
        intro x y hxy
        apply Subtype.ext
        exact (Equiv.subRight x₀.1).injective hxy⟩
    have hmap : S.map e ⊆ (B.dilate (1 / 2 : ℝ)).carrier := by
      intro z hz
      rw [Finset.mem_map] at hz
      obtain ⟨x, hxS, rfl⟩ := hz
      have hcodex : code x = q := by simpa [S] using hxS
      have hcodex₀ : code x₀ = q := by simpa [S] using hx₀
      exact sub_mem_half_dilate_of_localArgumentCode_eq B hB
        (hcodex.trans hcodex₀.symm)
    have hle : S.card ≤ (B.dilate (1 / 2 : ℝ)).carrier.card := by
      calc
        S.card = (S.map e).card := (Finset.card_map e).symm
        _ ≤ (B.dilate (1 / 2 : ℝ)).carrier.card := Finset.card_le_card hmap
    omega
  rw [hQ] at hmain
  have hcardcoe : Fintype.card ↥B.carrier = B.carrier.card :=
    Fintype.card_coe B.carrier
  rw [hcardcoe] at hmain
  exact hmain

end CyclicBohr
end Erdos3

end

section

namespace Erdos3.CyclicBohr

open _root_.Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

theorem card_two_le_nine_pow_three_rank_mul_card_quarter (B : Set N) (hB : 0 < B.radius) :
    (B.dilate 2).carrier.card ≤ 9 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card := by
  have h₂ := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate 2)
    (show 0 < (B.dilate 2).radius by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hB)
  have h₁ := card_carrier_le_nine_pow_rank_mul_card_half B hB
  have hh := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate (1 / 2))
    (show 0 < (B.dilate (1 / 2)).radius by simpa using mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hB)
  simp only [Set.rank_dilate, Set.dilate_dilate] at h₂ hh
  norm_num at h₂ hh
  calc
    _ ≤ 9 ^ B.rank * B.carrier.card := h₂
    _ ≤ 9 ^ B.rank * (9 ^ B.rank * (B.dilate (1 / 2)).carrier.card) := Nat.mul_le_mul_left _ h₁
    _ ≤ 9 ^ B.rank * (9 ^ B.rank * (9 ^ B.rank * (B.dilate (1 / 4)).carrier.card)) := by
      gcongr
    _ = _ := by
      rw [← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add]
      congr 2
      omega

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

theorem card_le_dyadic_dilate (B : Set N) (hB : 0 < B.radius) (k : ℕ) :
    B.carrier.card ≤ 9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < (B.dilate ((1 / 2 : ℝ) ^ k)).radius := by
      simp only [Set.radius_dilate, abs_of_nonneg (pow_nonneg (by norm_num) _)]
      positivity
    have hh := card_carrier_le_nine_pow_rank_mul_card_half (B.dilate ((1 / 2 : ℝ) ^ k)) hpos
    have heq : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ k = (1 / 2 : ℝ) ^ (k + 1) := by
      rw [pow_succ, mul_comm]
    simp only [Set.rank_dilate, Set.dilate_dilate, heq] at hh
    calc
      _ ≤ 9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := ih
      _ ≤ 9 ^ (k * B.rank) *
          (9 ^ B.rank * (B.dilate ((1 / 2 : ℝ) ^ (k + 1))).carrier.card) := Nat.mul_le_mul_left _ hh
      _ = _ := by simp only [Nat.add_mul, Nat.one_mul, pow_add, mul_assoc]

theorem relative_card_lower_bound (B : Set N) (hB : 0 < B.radius)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (r / 2) ^ (4 * B.rank) * (B.carrier.card : ℝ) ≤ (B.dilate r).carrier.card := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  let k := n + 1
  have hk : (1 / 2 : ℝ) ^ k ≤ r := hn.le
  have hhalf : r / 2 ≤ (1 / 2 : ℝ) ^ k := by
    dsimp [k]
    rw [pow_succ]
    nlinarith
  have hd := card_le_dyadic_dilate B hB k
  have hdR : (B.carrier.card : ℝ) ≤
      (9 : ℝ) ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card := by exact_mod_cast hd
  have hcoef : ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) * 9 ^ (k * B.rank) ≤ 1 := by
    calc
      _ = ((1 / 2 : ℝ) ^ 4) ^ (k * B.rank) * 9 ^ (k * B.rank) := by
        congr 1
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      _ = ((1 / 2 : ℝ) ^ 4 * 9) ^ (k * B.rank) := (mul_pow _ _ _).symm
      _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    _ ≤ ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) * B.carrier.card :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf _) (Nat.cast_nonneg _)
    _ ≤ ((1 / 2 : ℝ) ^ k) ^ (4 * B.rank) *
        (9 ^ (k * B.rank) * (B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card) :=
      mul_le_mul_of_nonneg_left hdR (by positivity)
    _ ≤ 1 * ((B.dilate ((1 / 2 : ℝ) ^ k)).carrier.card : ℝ) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    _ ≤ (B.dilate r).carrier.card := by
      rw [one_mul]
      exact_mod_cast Finset.card_le_card (B.dilate_mono (pow_nonneg (by norm_num) _) hk)

end Erdos3.CyclicBohr

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CyclicAffineCharacterPhase
namespace OAI

section

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

theorem exists_real_frequency_phase (r : ZMod N) :
    ∃ theta : ℝ, ∀ x : ZMod N,
      CircleFourier.character (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) = character r x := by
  obtain ⟨theta, htheta⟩ := CircleFourier.exists_real_character_phase (norm_character r 1)
  refine ⟨theta, ?_⟩
  intro x
  have hphase : (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) =
      x.val • (theta : CircleFourier.Circle) := by
    simpa only [nsmul_eq_mul] using
      (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := x.val) (x := theta))
  rw [hphase, CircleFourier.character_nsmul, htheta]
  calc
    _ = character r (x.val • (1 : ZMod N)) := (AddChar.map_nsmul_eq_pow _ _ _).symm
    _ = character r x := by simp

end Erdos3.CyclicBohr

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TranslatedBohrDifference
namespace OAI

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem norm_massCoeff_realUniformMass_lt_half_of_not_mem_largeSpectrum
    (A : Finset G) (hA : A.Nonempty) (ψ : AddChar G ℂ)
    (hψ : ψ ∉ Chang.largeSpectrum A (1 / 2)) :
    ‖massCoeff (realUniformMass A) ψ‖ < 1 / 2 := by
  have hcard : (0 : ℝ) < A.card := by
    exact_mod_cast hA.card_pos
  have hspectrum :
      ‖Chang.spectrumSum A ψ‖ < (1 / 2 : ℝ) * A.card := by
    apply lt_of_not_ge
    intro h
    exact hψ (Chang.mem_largeSpectrum.mpr h)
  calc
    ‖massCoeff (realUniformMass A) ψ‖ =
        (A.card : ℝ)⁻¹ * ‖Chang.spectrumSum A ψ‖ := by
      rw [massCoeff_realUniformMass, norm_mul]
      simp [norm_inv]
    _ < (A.card : ℝ)⁻¹ *
        ((1 / 2 : ℝ) * A.card) :=
      mul_lt_mul_of_pos_left hspectrum (inv_pos.mpr hcard)
    _ = 1 / 2 := by field_simp

end

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DifferenceEventProbability
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

noncomputable def smoothedDifferenceEventProbability
    (A₁ A₂ K R : Finset (ZMod N)) : ℝ :=
  𝔼 t ∈ R, differenceEventProbability A₁ A₂ K t

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DifferenceEventSupport
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

theorem mem_fourfold_difference_of_probability_pos (A : Finset (ZMod N)) (t : ZMod N)
    (h : 0 < differenceEventProbability A A (A - A) t) : t ∈ 2 • A - 2 • A := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_difference_event_of_probability_pos A A (A - A) t h
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_sub.mp hab
  have htwo : 2 • A = A + A := two_nsmul A
  rw [htwo]
  apply Finset.mem_sub.mpr
  refine ⟨c + b, Finset.mem_add.mpr ⟨c, hc, b, hb, rfl⟩,
    d + a, Finset.mem_add.mpr ⟨d, hd, a, ha, rfl⟩, ?_⟩
  calc
    (c + b) - (d + a) = (c - d) - (a - b) := by abel
    _ = (a - b + t) - (a - b) := by rw [hcd]
    _ = t := by abel

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LocalSpectrumBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal Pointwise

theorem samplingDensity_le_of_smallDoubling
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A S T : Finset G} (hA : A.Nonempty) (hS : S.Nonempty) (k : ℕ)
    {K : ℝ} (hK : 0 < K) (hdoubling : ((A + S).card : ℝ) ≤ K * A.card)
    (hcount : (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card)) :
    (S.card : ℝ) / (2 * K ^ k) ≤ T.card := by
  have hsumpos : (0 : ℝ) < (A + S).card := by exact_mod_cast (hA.add hS).card_pos
  have hden : 0 < ((A + S).card : ℝ) ^ k := pow_pos hsumpos _
  have hKden : 0 < 2 * K ^ k := mul_pos (by norm_num) (pow_pos hK _)
  apply le_trans _ hcount
  apply (div_le_div_iff₀ hKden hden).mpr
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hdoubling k
  calc
    _ ≤ (S.card : ℝ) * (K * A.card) ^ k :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.QuarticSamplingBudget
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

theorem local_sample_size_le_cubic {N : ℕ} (M L : Finset (ZMod N))
    {epsilon p : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p)
    (hratio : (M.card : ℝ) / L.card ≤ Real.exp (2 * p)) :
    (crootSisaskSampleSize (convolutionMomentOrder M L)
      (((epsilon / 8) / spectralIterations epsilon p) / Real.exp 1) : ℝ) ≤
        samplingCubicFactor epsilon * (p + 1) ^ 3 := by
  let q := spectralIterations epsilon p
  let H := 256 * Real.exp 1 ^ 2 / (epsilon / 8) ^ 2
  have hH : 0 ≤ H := by positivity
  have hq := spectralIterations_le hepsilon hepsilon1 hp
  have hraw := localBoostedSampleSize_le M L (p := 2 * p) (by positivity) hratio
    (by positivity : 0 < epsilon / 8) q (spectralIterations_pos epsilon p)
  have hp1 : 1 ≤ p + 1 := by linarith
  have hp3 : 1 ≤ (p + 1) ^ 3 := one_le_pow₀ hp1
  calc
    _ ≤ H * (2 * p + 2) * (q : ℝ) ^ 2 + 1 := hraw
    _ ≤ H * (2 * p + 2) * (spectralIterationFactor epsilon * (p + 1)) ^ 2 + 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg q) hq 2) (mul_nonneg hH (by positivity))) le_rfl
    _ = (2 * H * spectralIterationFactor epsilon ^ 2) * (p + 1) ^ 3 + 1 := by ring
    _ ≤ samplingCubicFactor epsilon * (p + 1) ^ 3 := by
      unfold samplingCubicFactor
      dsimp [H]
      nlinarith

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped NNReal Pointwise

theorem rankQuarticFactor_le_widthConstant {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    rankQuarticFactor epsilon ≤ almostPeriodicityWidthConstant epsilon := by
  have hC := rankQuarticFactor_pos epsilon
  have hprod := mul_le_mul_of_nonneg_left hepsilon1 hC.le
  have hquot : rankQuarticFactor epsilon ≤
      10240000000 * (rankQuarticFactor epsilon + 1) / epsilon := by
    rw [le_div_iff₀ hepsilon]
    nlinarith
  unfold almostPeriodicityWidthConstant
  linarith

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise NNReal

theorem quarticBogolyubovConstant_pos : 0 < quarticBogolyubovConstant := by
  exact mul_pos (by norm_num) (almostPeriodicityWidthConstant_pos (by norm_num))

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise

noncomputable def quarticBogolyubovProgressionConstant : ℝ :=
  11 * (quarticBogolyubovConstant + 2) ^ 2

theorem quarticBogolyubovProgressionConstant_pos :
    0 < quarticBogolyubovProgressionConstant := by
  have h := quarticBogolyubovConstant_pos
  unfold quarticBogolyubovProgressionConstant
  positivity

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowWeightFibers
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def reweight {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : p.mean w = 1) : FiniteProbabilityWeights X where
  weight x := p.weight x * w x
  nonneg x := mul_nonneg (p.nonneg x) (hw x)
  total := htotal

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem matrixDenominator_le_exp_power {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : Matrix ι κ ℚ) {p : ℝ} (hp : 0 ≤ p) (a : ℕ)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hD : ∀ i j, ((D i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    (matrixDenominator D : ℝ) ≤ Real.exp ((p + 2) ^ (a + 2)) := by
  have hcard : (Fintype.card (ι × κ) : ℝ) ≤ (p + 2) ^ 2 := by
    rw [Fintype.card_prod, Nat.cast_mul, pow_two]
    exact mul_le_mul (hι.trans (by linarith)) (hκ.trans (by linarith))
      (Nat.cast_nonneg _) (by linarith)
  simpa only [matrixDenominator, arrayDenominator, Nat.cast_prod] using
    product_exponential_budget Finset.univ (fun ij : ι × κ => ((D ij.1 ij.2).den : ℝ))
      hp a 2 (fun _ _ => Nat.cast_nonneg _) (fun ij _ => hD ij.1 ij.2) hcard

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ComparableResidueProgressionPartition
namespace OAI

section

namespace Erdos3.FiniteProgressionPartition

theorem comparableResidueProgressions_length_bounds (N q H : ℕ) (hq : 0 < q) (hH : 0 < H)
    (hfit : q * H ≤ N) (i : (comparableResidueProgressions N q H hq hH hfit).Label) :
    H ≤ (comparableResidueProgressions N q H hq hH hfit).length i ∧
      (comparableResidueProgressions N q H hq hH hfit).length i < 2 * H :=
  mergedIntervals_length_bounds _ H hH (residues_length_lower hq hH hfit i.1) i.2

end Erdos3.FiniteProgressionPartition

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistParameterPartition
namespace OAI

section

namespace Erdos3.FiniteProgressionPartition

theorem normalized_point_sub_point_le {N q H : ℕ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (j l : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - ((P.point k l).val : ℝ) / N| ≤
      2 * q * H / N := by
  have hj : (j.val : ℝ) ≤ 2 * H := by exact_mod_cast (by omega : j.val ≤ 2 * H)
  have hl : (l.val : ℝ) ≤ 2 * H := by exact_mod_cast (by omega : l.val ≤ 2 * H)
  have hj0 : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
  have hl0 : 0 ≤ (l.val : ℝ) := Nat.cast_nonneg _
  have hdiff : |(j.val : ℝ) - l.val| ≤ 2 * H :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hfactor : 0 ≤ (q : ℝ) / N := by positivity
  calc
    _ = (q : ℝ) / N * |(j.val : ℝ) - l.val| := by
      rw [P.point_val, P.point_val, hstep]
      push_cast
      rw [← sub_div, show ((P.start k : ℝ) + q * j.val) -
        (P.start k + q * l.val) = q * ((j.val : ℝ) - l.val) by ring]
      simp only [abs_div, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q),
        abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      ring
    _ ≤ (q : ℝ) / N * (2 * H) := mul_le_mul_of_nonneg_left hdiff hfactor
    _ = 2 * q * H / N := by ring

theorem normalized_point_sub_point_le_of_bound {N q H : ℕ} {ε : ℝ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (hbound : (2 : ℝ) * q * H / N ≤ ε) (j l : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - ((P.point k l).val : ℝ) / N| ≤ ε :=
  (normalized_point_sub_point_le P k hstep hlen hN j l).trans hbound

theorem normalized_point_sub_start_le {N q H : ℕ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (j : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - (P.start k : ℝ) / N| ≤ 2 * q * H / N := by
  let z : Fin (P.length k) := ⟨0, Nat.zero_lt_of_lt j.isLt⟩
  have hz : (P.point k z).val = P.start k := by simp [z]
  simpa only [hz] using normalized_point_sub_point_le P k hstep hlen hN j z

theorem normalized_point_sub_start_le_of_bound {N q H : ℕ} {ε : ℝ}
    (P : FiniteProgressionPartition N) (k : P.Label)
    (hstep : P.step k = q) (hlen : P.length k < 2 * H) (hN : 0 < N)
    (hbound : (2 : ℝ) * q * H / N ≤ ε) (j : Fin (P.length k)) :
    |((P.point k j).val : ℝ) / N - (P.start k : ℝ) / N| ≤ ε :=
  (normalized_point_sub_start_le P k hstep hlen hN j).trans hbound

end Erdos3.FiniteProgressionPartition

end

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProgressionPartition

theorem label_card_mul_le_of_length_lower {N : ℕ} (P : FiniteProgressionPartition N)
    {H : ℝ} (hlength : ∀ a, H ≤ (P.length a : ℝ)) :
    (Fintype.card P.Label : ℝ) * H ≤ N := by
  have hsum : (∑ a, P.length a) = N := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr P.equiv
  calc
    _ = ∑ _a : P.Label, H := by simp
    _ ≤ ∑ a : P.Label, (P.length a : ℝ) := Finset.sum_le_sum (fun a _ => hlength a)
    _ = N := by exact_mod_cast hsum

theorem label_card_le_exp_of_length_lower {N : ℕ} (P : FiniteProgressionPartition N)
    (hN : 0 < N) {A : ℝ} (hlength : ∀ a, (N : ℝ) * Real.exp (-A) ≤ P.length a) :
    (Fintype.card P.Label : ℝ) ≤ Real.exp A := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  apply (mul_le_mul_iff_left₀ (mul_pos hNr (Real.exp_pos (-A)))).mp
  calc
    _ ≤ (N : ℝ) := P.label_card_mul_le_of_length_lower hlength
    _ = (N : ℝ) * (Real.exp A * Real.exp (-A)) := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ = Real.exp A * ((N : ℝ) * Real.exp (-A)) := by ring

end FiniteProgressionPartition

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition
namespace OAI

section

namespace Erdos3.CircleFourier
open MeasureTheory
open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

namespace IsometricCircleAction

theorem component_sub (A : IsometricCircleAction X) (N : ℕ) (h : ℤ)
    {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g) (x : X) :
    A.component N h (fun y => f y - g y) x =
      A.component N h f x - A.component N h g x := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  change (fejerCoefficient N h : ℂ) *
    (∫ t : Circle, character ((-(-h)) • t) * (f (t +ᵥ x) - g (t +ᵥ x)) ∂circleHaar) = _
  simp_rw [mul_sub]
  rw [integral_sub (integrable_circleFourierComponent (-h) hf x)
    (integrable_circleFourierComponent (-h) hg x)]
  exact mul_sub _ _ _

theorem component_norm_sub_le (A : IsometricCircleAction X) {N : ℕ} (hN : 0 < N)
    (h : ℤ) {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g) {ε : ℝ}
    (hfg : ∀ x, ‖f x - g x‖ ≤ ε) (x : X) :
    ‖A.component N h f x - A.component N h g x‖ ≤ ε := by
  rw [← A.component_sub N h hf hg x]
  let := A.toAddAction
  change ‖(fejerCoefficient N h : ℂ) *
    circleFourierComponent (-h) (fun y => f y - g y) x‖ ≤ ε
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejerCoefficient_nonneg N h)]
  exact (mul_le_mul (fejerCoefficient_le_one hN h)
    (norm_circleFourierComponent_le (-h) _ hfg x) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul _)

end IsometricCircleAction

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteExcessMassCap
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem excessMass_le_of_mass_le {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) {C ε : ℝ}
    (h : ∀ G : Finset X, q.mass G ≤ C * p.mass G + ε) : p.excessMass q C ≤ ε := by
  let G := Finset.univ.filter (fun x => 0 < q.weight x - C * p.weight x)
  have he : p.excessMass q C = q.mass G - C * p.mass G := by
    have hsum : (∑ x, max (q.weight x - C * p.weight x) 0) =
        ∑ x ∈ G, (q.weight x - C * p.weight x) := by
      simp only [G, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : 0 < q.weight x - C * p.weight x
      · simp only [hx, ite_true, max_eq_left hx.le]
      · simp only [hx, ite_false, max_eq_right (le_of_not_gt hx)]
    rw [excessMass, hsum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  rw [he]
  linarith [h G]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativePrescribedProjection
namespace OAI

section

namespace Erdos3.CircleFourier.IsometricCircleAction

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

noncomputable def project (A : IsometricCircleAction X) (n : ℤ) (f : X → ℂ) : X → ℂ :=
  let := A.toAddAction
  circleFourierComponent n f

theorem project_lipschitz (A : IsometricCircleAction X) (n : ℤ) {f : X → ℂ}
    {K : ℝ≥0} (hf : LipschitzWith K f) : LipschitzWith K (A.project n f) := by
  let := A.toAddAction
  let := A.toContinuousVAdd
  exact lipschitz_circleFourierComponent n hf A.isometry_act

theorem project_norm_le (A : IsometricCircleAction X) (n : ℤ) {f : X → ℂ}
    {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖A.project n f x‖ ≤ B := by
  let := A.toAddAction
  exact norm_circleFourierComponent_le n f hf x

theorem project_equivariant (A : IsometricCircleAction X) (n : ℤ) {f : X → ℂ}
    (g : X → X) (z : ℂ) (hg : ∀ t x, A.act t (g x) = g (A.act t x))
    (hf : ∀ x, f (g x) = z * f x) (x : X) :
    A.project n f (g x) = z * A.project n f x := by
  unfold project circleFourierComponent
  change (∫ t : Circle, character ((-n) • t) * f (A.act t (g x)) ∂circleHaar) =
    z * (∫ t : Circle, character ((-n) • t) * f (A.act t x) ∂circleHaar)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hg, hf]
  ring

theorem project_eq_at (A : IsometricCircleAction X) (n : ℤ) (f : X → ℂ) (x : X)
    (hx : ∀ t, f (A.act t x) = character (n • t) * f x) : A.project n f x = f x := by
  unfold project circleFourierComponent
  change (∫ t : Circle, character ((-n) • t) * f (A.act t x) ∂circleHaar) = _
  have heq (t : Circle) : character ((-n) • t) * f (A.act t x) = f x := by
    rw [hx, ← mul_assoc, ← character_add, ← add_smul]
    simp only [neg_add_cancel, zero_smul, character_zero, one_mul]
  simp_rw [heq]
  simp

end Erdos3.CircleFourier.IsometricCircleAction

end

section

namespace Erdos3.CircleFourier

open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

noncomputable def iteratedExactProjection (A : α → IsometricCircleAction X) (n : α → ℤ) :
    List α → (X → ℂ) → X → ℂ
  | [], f => f
  | i :: is, f => (A i).project (n i) (iteratedExactProjection A n is f)

theorem iteratedExactProjection_lipschitz (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) {f : X → ℂ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (iteratedExactProjection A n is f) := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).project_lipschitz (n i) ih

theorem iteratedExactProjection_norm_le (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) {f : X → ℂ} {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    ∀ x, ‖iteratedExactProjection A n is f x‖ ≤ B := by
  induction is with
  | nil => exact hf
  | cons i is ih => exact (A i).project_norm_le (n i) ih

theorem iteratedExactProjection_eq_on (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) (S : Set X) (f : X → ℂ)
    (hstable : ∀ i ∈ is, ∀ t x, x ∈ S → (A i).act t x ∈ S)
    (hchar : ∀ i ∈ is, ∀ t x, x ∈ S → f ((A i).act t x) = character (n i • t) * f x) :
    ∀ x ∈ S, iteratedExactProjection A n is f x = f x := by
  induction is with
  | nil => exact fun _ _ => rfl
  | cons i is ih =>
    have htail := ih (fun j hj => hstable j (List.mem_cons_of_mem i hj))
      (fun j hj => hchar j (List.mem_cons_of_mem i hj))
    intro x hx
    change (A i).project (n i) (iteratedExactProjection A n is f) x = f x
    rw [(A i).project_eq_at (n i) _ x]
    · exact htail x hx
    · intro t
      rw [htail _ (hstable i List.mem_cons_self t x hx), htail x hx]
      exact hchar i List.mem_cons_self t x hx

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

@[simp] theorem correlationExponent_apply (h n : ℕ) (i : Fin 2) :
    correlationExponent h n i = correlationInput h n i := by
  fin_cases i
  · change correlationExponent h n 0 = h
    simp [correlationExponent]
  · change correlationExponent h n 1 = n
    simp [correlationExponent]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedTargetCubeIntervals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedDifferenceShifts {d N : ℕ} (t : (Fin (d + 1) → ZMod N) × ZMod N) :
    Fin (d + 1) → ZMod N := Fin.cons t.2 (Fin.tail t.1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} {X : ι → Type*}

noncomputable def erase (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) : ℝ := by
  classical
  exact if c.Contains (F z) then 0 else w z

end Erdos3.ProductCylinder

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  exact Finset.expect_add_distrib Finset.univ f g

theorem mean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g := by
  exact Finset.expect_sub_distrib Finset.univ f g

theorem mean_smul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  exact (Finset.mul_expect Finset.univ f c).symm

noncomputable def mean₂ {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) : ℝ :=
  mean (fun x => mean (f x))

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def cyclicAPCount (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  mean₂ (fun a d => cyclicAPProduct k N f a d)

@[simp]
theorem cyclicAPCount_const (k N : ℕ) [NeZero N] (c : ℝ) :
    cyclicAPCount k N (fun _ => c) = c ^ k := by
  simp [cyclicAPCount, mean₂]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    mean (conditionalMean P f) = mean f := by
  change (𝔼 x, conditionalMean P f x) = 𝔼 x, f x
  rw [Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card, sum_conditionalMean P f]

noncomputable def partitionEnergy {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) : ℝ :=
  mean fun x => conditionalMean P f x ^ 2

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem mean_conditionalMean_mul_eq_sq_of_le
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    mean (fun x =>
      conditionalMean P f x * conditionalMean Q f x) =
      mean (fun x => conditionalMean Q f x ^ 2) := by
  calc
    mean (fun x =>
        conditionalMean P f x * conditionalMean Q f x) =
        mean (conditionalMean Q (fun x =>
          conditionalMean P f x * conditionalMean Q f x)) :=
      (mean_conditionalMean Q _).symm
    _ =
        mean (fun x =>
          conditionalMean Q (conditionalMean P f) x *
            conditionalMean Q f x) := by
      apply congrArg mean
      funext x
      exact conditionalMean_mul_conditionalMean_right
        Q (conditionalMean P f) f x
    _ =
        mean (fun x =>
          conditionalMean Q f x * conditionalMean Q f x) := by
      apply congrArg mean
      funext x
      rw [conditionalMean_tower_of_le P Q hPQ]
    _ = mean (fun x => conditionalMean Q f x ^ 2) := by
      apply congrArg mean
      funext x
      rw [pow_two]

theorem partitionEnergy_pythagorean
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy P f =
      partitionEnergy Q f +
        mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2) := by
  have hcross :=
    mean_conditionalMean_mul_eq_sq_of_le P Q hPQ f
  have hdiff :
      mean (fun x =>
        (conditionalMean P f x -
          conditionalMean Q f x) ^ 2) =
        mean (fun x => conditionalMean P f x ^ 2) -
          2 * mean (fun x =>
            conditionalMean P f x * conditionalMean Q f x) +
          mean (fun x => conditionalMean Q f x ^ 2) := by
    calc
      mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2) =
          mean (fun x =>
            conditionalMean P f x ^ 2 -
              2 * (conditionalMean P f x *
                conditionalMean Q f x) +
              conditionalMean Q f x ^ 2) := by
        apply congrArg mean
        funext x
        ring
      _ =
          mean (fun x => conditionalMean P f x ^ 2) -
            2 * mean (fun x =>
              conditionalMean P f x * conditionalMean Q f x) +
            mean (fun x => conditionalMean Q f x ^ 2) := by
        rw [mean_add, mean_sub, mean_smul]
  change
    mean (fun x => conditionalMean P f x ^ 2) =
      mean (fun x => conditionalMean Q f x ^ 2) +
        mean (fun x =>
          (conditionalMean P f x -
            conditionalMean Q f x) ^ 2)
  rw [hdiff, hcross]
  ring

theorem partitionEnergy_sub_eq_mean_sq
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy P f - partitionEnergy Q f =
      mean (fun x =>
        (conditionalMean P f x -
          conditionalMean Q f x) ^ 2) := by
  rw [partitionEnergy_pythagorean P Q hPQ f]
  ring

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SimplexTelescoping
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace WeightedSimplexSystem

noncomputable def simplexCount {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] (H : WeightedSimplexSystem V) : ℝ :=
  mean H.simplexWeight

end WeightedSimplexSystem

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BooleanCutReduction
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def cutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x : Fin r → G =>
    (f (∑ i, x i) - g (∑ i, x i)) *
      ∏ i, u i (eraseCoordinate i x)

def CutDiscrepancyLe
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    (∀ i x, 0 ≤ u i x) →
    (∀ i x, u i x ≤ 1) →
    |cutCorrelation r f g u| ≤ ε

@[simp]
theorem cutCorrelation_self
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f f u = 0 := by
  simp [cutCorrelation]

theorem cutCorrelation_swap
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r g f u = -cutCorrelation r f g u := by
  calc
    cutCorrelation r g f u =
        mean (fun x : Fin r → G =>
          (-1 : ℝ) *
            ((f (∑ i, x i) - g (∑ i, x i)) *
              ∏ i, u i (eraseCoordinate i x))) := by
      apply congrArg mean
      funext x
      ring
    _ = (-1 : ℝ) *
        mean (fun x : Fin r → G =>
          (f (∑ i, x i) - g (∑ i, x i)) *
            ∏ i, u i (eraseCoordinate i x)) :=
      mean_smul _ _
    _ = -cutCorrelation r f g u := by
      simp [cutCorrelation]

theorem CutDiscrepancyLe.symm
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε) :
    CutDiscrepancyLe r g f ε := by
  intro u hu0 hu1
  rw [cutCorrelation_swap, abs_neg]
  exact h u hu0 hu1

@[simp]
theorem cutCorrelation_one
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean (fun x : Fin r → G =>
      f (∑ i, x i) - g (∑ i, x i)) := by
  simp [cutCorrelation]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def cutTestProduct {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) : ℝ :=
  ∏ i, u i (eraseCoordinate i x)

@[simp]
theorem cutTestProduct_one {G : Type*} {r : ℕ} (x : Fin r → G) :
    cutTestProduct
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) x = 1 := by
  simp [cutTestProduct]

@[simp]
theorem cutTestProduct_mul
    {G : Type*} {r : ℕ} (u v : CutTestFamily G r)
    (x : Fin r → G) :
    cutTestProduct (fun i y => u i y * v i y) x =
      cutTestProduct u x * cutTestProduct v x := by
  simp [cutTestProduct, Finset.prod_mul_distrib]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators Polynomial

def cutTestFamilyOfBooleanAssignment
    {G : Type*} {r : ℕ}
    (b : BooleanCutAssignment G r) :
    CutTestFamily G r :=
  fun i y => booleanValue b ⟨i, y⟩

def cutTestCoordinateValue
    {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) :
    CutTestCoordinate G r → ℝ :=
  fun q => u q.1 q.2

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BundleCountingRecurrence
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

noncomputable def bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (B.bundleProduct A)

noncomputable def edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun x : K → G =>
    q (edgeTuple g₀ x) * B.edgeRemainder g₀ A x)

noncomputable def edgeRemainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  mean (B.edgeRemainderFiber g₀ A y)

noncomputable def frozenEdgeCorrelation
    [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (z : EdgeComplement g₀ → G) : ℝ :=
  mean (fun y =>
    q y * B.edgeRemainderFiber g₀ A y z)

noncomputable def doubledRemainderMoment
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun y =>
    B.edgeRemainderAverage g₀ A y ^ 2)

end HypergraphBundle

end Erdos3.FixedDensity

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

namespace IsPartitionMeasurable

theorem of_le {P Q : FacePartition Ω} {g : Ω → ℝ}
    (hPQ : P ≤ Q) (hg : IsPartitionMeasurable Q g) :
    IsPartitionMeasurable P g := by
  intro x y hy
  exact hg x y (FacePartition.part_subset_of_le hPQ x hy)

end IsPartitionMeasurable

namespace FaceRegularityState

noncomputable def energy (S : FaceRegularityState Ω)
    (f : Ω → ℝ) : ℝ :=
  partitionEnergy S.partition f

end FaceRegularityState

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleRelativeCounting
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

universe uJ uG

variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}

def HasTaoBundleCountingStep
    (A : HypergraphBundle.BaseEdgeWeight J G)
    (p : Finset J → ℝ)
    (β : ℕ → ℝ) (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle J K H),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, g₀ ∈ B.edges →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      |B.bundleCount (B.pullbackBaseEdgeWeight A) -
          p (g₀.image B.projection) *
            (B.eraseEdge g₀).bundleCount
              ((B.eraseEdge g₀).pullbackBaseEdgeWeight A)| ≤
        Real.sqrt
            (β g₀.card *
              (B.strictBoundary g₀).bundleCount
                ((B.strictBoundary g₀).pullbackBaseEdgeWeight A) *
              ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                  A)) +
          τ

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedPattern
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace WeightedOrderedPattern

noncomputable def patternCount
    {G : Type*} [Fintype G] {k r : ℕ}
    (H : WeightedOrderedPattern G k r) : ℝ :=
  mean H.patternWeight

end WeightedOrderedPattern

def HasUniformOrderedPatternRemoval (k r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
        ∀ H : OrderedPattern G k r,
          H.toWeighted.patternCount < c →
            ∃ D : OrderedPattern.DeletionFamily
                (G := G) k r,
              H.IsCover D ∧
                ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ε

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

def HasDenseAPCount (k N : ℕ) [NeZero N]
    (δ c : ℝ) : Prop :=
  ∀ A : Finset (ZMod N),
    δ ≤ mean (finsetIndicator A) →
      c ≤ cyclicAPCount k N (finsetIndicator A)

def HasUniformDenseAPCount (k : ℕ) (δ c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N], HasDenseAPCount k N δ c

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefinementPolynomialBound
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution Polynomial

noncomputable def refinementRankPolynomial (C : ℕ) : Polynomial ℕ :=
  Polynomial.C C * (1 + (3 * Polynomial.C C + 1) * X ^ 2) ^ 4 + 1

noncomputable def refinementDepthPolynomial (C : ℕ) : Polynomial ℕ := Polynomial.C C * X + 1

noncomputable def refinementFinalRankPolynomial (C : ℕ) : Polynomial ℕ :=
  1 + refinementDepthPolynomial C * refinementRankPolynomial C

noncomputable def refinementMatchPolynomial (C : ℕ) : Polynomial ℕ :=
  5 * refinementFinalRankPolynomial C + 13 * X + 2 * Polynomial.C C + 8020

noncomputable def refinementUnbalancedPolynomial (C : ℕ) : Polynomial ℕ :=
  2 * refinementFinalRankPolynomial C +
    Polynomial.C C * (1 + (3 * Polynomial.C C + 1) * X ^ 2) ^ 4 +
    2 * Polynomial.C C * X ^ 2 + 2 * X + 2 * Polynomial.C C + 3209 +
    Polynomial.C C * (3 + (3 * Polynomial.C C + 1) * X ^ 2 + refinementFinalRankPolynomial C)

noncomputable def refinementRoundPolynomial (C : ℕ) : Polynomial ℕ :=
  refinementMatchPolynomial C + refinementFinalRankPolynomial C + 3 * X + 1602 +
    refinementUnbalancedPolynomial C

noncomputable def refinementWidthPolynomial (C : ℕ) : Polynomial ℕ :=
  refinementDepthPolynomial C * refinementRoundPolynomial C

noncomputable def refinementCostPolynomial (C : ℕ) : Polynomial ℕ :=
  (2 * refinementFinalRankPolynomial C + 4 * X + refinementWidthPolynomial C +
    refinementMatchPolynomial C + 1612) +
  (3 * X + 2 + refinementFinalRankPolynomial C *
    (refinementWidthPolynomial C + refinementMatchPolynomial C + 10))

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityUniformResidualGood
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

theorem uniformResidualGood_exp_budget {Branch : Type*} [Fintype Branch]
    {mass massLog branchLog Eres u : ℝ}
    (hmass : Real.exp (-massLog) ≤ mass)
    (hcard : (Fintype.card Branch : ℝ) ≤ Real.exp branchLog)
    (hu : branchLog + Eres + massLog + 2 ≤ u) :
    (Fintype.card Branch : ℝ) * Real.exp (-u) ≤ Real.exp (-Eres) * mass / 2 := by
  calc
    _ ≤ Real.exp branchLog * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = Real.exp (branchLog - u) := by rw [← Real.exp_add]; rfl
    _ ≤ Real.exp (-(Eres + massLog + 2)) := Real.exp_le_exp.mpr (by linarith only [hu])
    _ ≤ Real.exp (-(Eres + massLog)) / 2 := by
      simpa using VectorPolynomial.precenter_native_selection_model_error_budget 0 (Eres + massLog)
    _ = Real.exp (-Eres) * Real.exp (-massLog) / 2 := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)) (by norm_num)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end


