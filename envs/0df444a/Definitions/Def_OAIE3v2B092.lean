-- Prove2me | Definitions.Def_OAIE3v2B092
-- name    : OAIE3v2B092
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:22:27.718072+00:00
-- url     : https://prove2.me/theorems/b76596db-7363-4d62-84f5-116ef06ac9c2
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 93 of 311
-- statement:
--   Definitions bundle 93 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069`, `OAIE3v2B070`, `OAIE3v2B071`, `OAIE3v2B072`, `OAIE3v2B073`, `OAIE3v2B074` of this split.
--
--   Modules: `Dynamics/NativeHorizontalLiftBudget.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AllocatedFixedScaleJointMarginal.lean`, `Estimates/BoundedFreeWords.lean`, `Estimates/CocycleHorizontalNormalization.lean`, `Estimates/FiniteDependentPMFBind.lean`, `Estimates/FiniteFiberTest.lean`, `Estimates/FiniteInnerProgressionFamily.lean`, `Estimates/FinitePushforwardComplexWeights.lean`, `Estimates/FreeLieTreeCoefficientBounds.lean`, `Estimates/IndependentFiniteConditioning.lean`, `Estimates/IteratedCircleAverageIntegral.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/ModularMultilinearAmbientSublevel.lean`, `Estimates/NativeRetainedTargetCubeIntervals.lean`, `Estimates/NormalizedCoefficientRemainder.lean`, `Estimates/ObservedSourceEquivalence.lean`, `Estimates/PreparationSliceComposition.lean`, `Estimates/QuotientInducedMark.lean`, `Estimates/RationalLieSubalgebra.lean`, `Estimates/RelativePatchAmplification.lean`, `Estimates/ScalarDominatedSlack.lean`, `Estimates/SquarefreePermutationFiltration.lean`, `Estimates/UniformCommutingCircleDecomposition.lean`, `FixedDensity/Energy.lean`, `Fourier/BoundedFrequencyKernel.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Geometry/CubeSignalCoordinates.lean`, `Geometry/LieTreeSupport.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/MixedCoveredChart.lean`, `Geometry/MixedProfileCoordinates.lean`, `Geometry/PhysicalSpatialScales.lean`, `Lattices/LayerSamplingRankAffine.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Lattices/ResidueSliceUpperFailure.lean`, `Lattices/SmoothResidueWindowMass.lean`, `Linear/AdaptedBasisGeometry.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/ExternalFamilyCircleProjection.lean`, `Linear/NativePrescribedProjection.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/RationalMatrixSeparation.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/BCHOuterGridChangeBasis.lean`, `Nilpotent/FreeNilpotentSourceBounds.lean`, `Nilpotent/RationalBCHProducts.lean`, `Polynomial/AdaptedBinomialFactorization.lean`, `Polynomial/AffinePhaseBias.lean`, `Polynomial/CRTPolynomialChargeBound.lean`, `Polynomial/CoefficientPolynomialLift.lean`, `Polynomial/DegreeRankSunflower.lean`, `Polynomial/MixedPolynomialChart.lean`, `Polynomial/WeightedLieDegreeLengthSpan.lean`, `Probability/EmptyCoefficientDensity.lean`, `Probability/FiniteConditionedMass.lean`, `Probability/FiniteProbabilityLipschitz.lean`, `Probability/RelativeFullSliceLaw.lean`, `Probability/ScaledArrayLaw.lean`, `Probability/ShiftedSmoothLawBounds.lean`, `Sampling/CoveredJetSampler.lean`, `Sampling/FiniteWeightedScorePerturbation.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B068
import Definitions.Def_OAIE3v2B069
import Definitions.Def_OAIE3v2B070
import Definitions.Def_OAIE3v2B071
import Definitions.Def_OAIE3v2B072
import Definitions.Def_OAIE3v2B073
import Definitions.Def_OAIE3v2B074

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

namespace FreeCoefficientBound

variable {s D E M N : ℕ} {p q : FreeAlgebra ℚ X}

theorem pow (hp : FreeCoefficientBound s D M p) (n : ℕ) :
    FreeCoefficientBound s (D ^ n) (((s + 1) * M) ^ n) (p ^ n) := by
  induction n with
  | zero => simpa using one s
  | succ n ih =>
    simpa only [pow_succ, mul_assoc, Nat.mul_left_comm] using ih.mul hp

theorem list_prod (f : List (FreeAlgebra ℚ X)) (hf : ∀ p ∈ f, FreeCoefficientBound s D M p) :
    FreeCoefficientBound s (D ^ f.length) (((s + 1) * M) ^ f.length) f.prod := by
  induction f with
  | nil => simpa using one s
  | cons p ps ih =>
    have h := (hf p List.mem_cons_self).mul (ih (fun q hq => hf q (List.mem_cons_of_mem p hq)))
    simpa only [List.prod_cons, List.length_cons, pow_succ', mul_assoc] using h

end FreeCoefficientBound

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

theorem commutatorTree_coefficient_bound (s : ℕ) (a : FreeMagma X) :
    FreeCoefficientBound s 1 ((2 * (s + 1)) ^ (a.length - 1))
      (wordPolynomialEmbedding (commutatorTree a)) := by
  induction a using FreeMagma.rec with
  | of x =>
    simpa only [commutatorTree, wordPolynomialEmbedding_generator, freeWord_of,
      FreeMagma.length, Nat.sub_self, pow_zero] using
      FreeCoefficientBound.word s (FreeMonoid.of x)
  | mul a b ha hb =>
    have h := (ha.mul hb).add_same (hb.mul ha).neg
    have he : (s + 1) * (2 * (s + 1)) ^ (a.length - 1) * (2 * (s + 1)) ^ (b.length - 1) +
        (s + 1) * (2 * (s + 1)) ^ (b.length - 1) * (2 * (s + 1)) ^ (a.length - 1) =
        (2 * (s + 1)) ^ ((a * b).length - 1) := by
      have ha0 := a.length_pos
      have hb0 := b.length_pos
      rw [show (a * b).length - 1 = (a.length - 1) + (b.length - 1) + 1 by
        change a.length + b.length - 1 = _; omega, pow_succ, pow_add]
      ring
    simpa only [commutatorTree, FreeMagma.length, map_sub, map_add, map_neg, map_mul,
      one_mul, sub_eq_add_neg, he] using h

theorem commutatorTree_coefficient_height (s : ℕ) (a : FreeMagma X)
    (w : FreeSemigroup X) (hw : w.length ≤ s) :
    RationalHeightLE ((commutatorTree a).coeff w) ((2 * (s + 1)) ^ (a.length - 1)) := by
  have h := (commutatorTree_coefficient_bound s a).rationalHeight (by omega)
    w.toFreeMonoid (by simpa only [freeSemigroup_toFreeMonoid_length] using hw)
  have hpow : 1 ≤ (2 * (s + 1)) ^ (a.length - 1) := one_le_pow₀ (by omega)
  simpa only [freeWordCoefficients_embedding, max_eq_right hpow] using h

theorem commutatorTree_coefficient_integral (s : ℕ) (a : FreeMagma X)
    (w : FreeSemigroup X) (hw : w.length ≤ s) :
    ∃ z : ℤ, (z : ℚ) = (commutatorTree a).coeff w ∧ z.natAbs ≤ (2 * (s + 1)) ^ (a.length - 1) := by
  obtain ⟨z, hz, hbound⟩ := commutatorTree_coefficient_bound s a w.toFreeMonoid
    (by simpa only [freeSemigroup_toFreeMonoid_length] using hw)
  exact ⟨z, by simpa only [Nat.cast_one, one_mul, freeWordCoefficients_embedding] using hz, hbound⟩

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

theorem mean_square_le (f : Ω → ℝ) : (p.mean f) ^ 2 ≤ p.mean (fun x => f x ^ 2) := by
  have h := p.mean_mul_sq_le f (fun _ => 1)
  simpa only [mul_one, one_pow, p.mean_const] using h

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem fiberMean_nonneg (F : X → R) (r : R) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ p.fiberMean F r f := by
  classical
  apply p.mean_nonneg
  intro x
  split_ifs
  · exact hf x
  · exact le_rfl

noncomputable def fiberLaw [Fintype R] (F : X → R) : FiniteProbabilityWeights R where
  weight r := p.fiberMean F r (fun _ => 1)
  nonneg r := p.fiberMean_nonneg F r (fun _ => 1) (fun _ => zero_le_one)
  total := by rw [p.sum_fiberMean, p.mean_const]

theorem fiberLaw_weight [Fintype R] (F : X → R) (r : R) :
    (p.fiberLaw F).weight r = p.fiberMean F r (fun _ => 1) := rfl

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

theorem eventProbability_union_bound {Ω C : Type*} [Fintype Ω] [Fintype C]
    (p : FiniteProbabilityWeights Ω) (E : Ω → Prop) (F : C → Ω → Prop)
    (hEF : ∀ x, E x → ∃ c, F c x) :
    p.eventProbability E ≤ ∑ c, p.eventProbability (F c) := by
  classical
  have hpoint (x) : (if E x then (1 : ℝ) else 0) ≤ ∑ c, if F c x then (1 : ℝ) else 0 := by
    by_cases hE : E x
    · obtain ⟨c, hc⟩ := hEF x hE
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun c => if F c x then (1 : ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ c)
      simpa only [hE, hc, ite_true] using h
    · simp only [hE, ite_false]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  apply (p.mean_mono hpoint).trans_eq
  simp only [eventProbability, mean, Finset.mul_sum]
  exact Finset.sum_comm

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem uniform_condition_mean {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (G : Finset Ω) (hG : 0 < (uniform Ω).mass G) (f : Ω → ℝ) :
    ((uniform Ω).condition G hG).mean f = 𝔼 x : G, f x := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hg : (G.card : ℝ) ≠ 0 := by
    intro hz
    rw [uniform_mass, hz, zero_div] at hG
    exact (lt_irrefl _ hG)
  rw [condition_mean, uniform_mean, uniform_mass, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card, Finset.sum_coe_sort G f, Fintype.card_coe]
  have hsum : (∑ x, if x ∈ G then f x else 0) = ∑ x ∈ G, f x := by simp
  rw [hsum]
  field_simp

end Erdos3.FiniteProbabilityWeights

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

theorem exists_bounded_rational_left_inverse (B : Matrix ι κ ℚ)
    (hli : LinearIndependent ℚ B.col) {H : ℕ} (hH : 1 ≤ H)
    (hB : ∀ i j, RationalHeightLE (B i j) H) :
    ∃ C : Matrix κ ι ℚ, C * B = 1 ∧
      ∀ i j, RationalHeightLE (C i j) (rationalSolveHeight (Fintype.card κ) H) := by
  have hsurj : Function.Surjective Bᵀ.mulVec :=
    mulVec_surjective_of_independent_rows Bᵀ hli
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section Bᵀ hsurj hH (fun i j => hB j i)
  refine ⟨Sᵀ, ?_, fun i j => hSH j i⟩
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using
    congrArg Matrix.transpose hS

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalMatrixSeparation
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem real_matrix_denominator_grid (Q : Matrix ι κ ℚ) (l : ℕ) (x : κ → ℝ)
    (hx : x ∈ realDenominatorGrid l) :
    (fun i j => (Q i j : ℝ)) *ᵥ x ∈ realDenominatorGrid (matrixDenominator Q * l) := by
  classical
  obtain ⟨z, hz⟩ := hx
  have hcoef (i : ι) (j : κ) :
      ((clearedMatrix Q i j : ℤ) : ℝ) = (matrixDenominator Q : ℝ) * (Q i j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast Q) i) j
    change ((clearedMatrix Q i j : ℤ) : ℚ) = (matrixDenominator Q : ℚ) * Q i j at h
    exact_mod_cast h
  refine ⟨clearedMatrix Q *ᵥ z, funext fun i => ?_⟩
  change (((clearedMatrix Q *ᵥ z) i : ℤ) : ℝ) =
    ((matrixDenominator Q * l : ℕ) : ℝ) * ((fun i j => (Q i j : ℝ)) *ᵥ x) i
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (z j : ℝ) = (l : ℝ) * x j := congrFun hz j
  rw [hcoef, hj]
  ring

theorem rational_matrix_kernel_separation (Q : Matrix ι κ ℚ) (H : ℝ≥0)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ H) (l : ℕ) (hl : 0 < l) (x y : κ → ℝ)
    (hx : x ∈ realDenominatorGrid l)
    (hy : (fun i j => (Q i j : ℝ)) *ᵥ y = 0)
    (hnear : ((matrixDenominator Q * l : ℕ) : ℝ) *
      (((Fintype.card κ : ℝ) + 1) * (H + 1)) * dist x y < 1) :
    (fun i j => (Q i j : ℝ)) *ᵥ x = 0 := by
  have hD : 0 < matrixDenominator Q * l := Nat.mul_pos (matrixDenominator_pos Q) hl
  apply eq_zero_of_mem_realDenominatorGrid_of_abs_lt hD (real_matrix_denominator_grid Q l x hx)
  intro i
  have hbound := abs_matrix_mulVec_le (fun i j => (Q i j : ℝ)) H hQ (x - y) i
  have heq := Matrix.mulVec_sub (fun i j => (Q i j : ℝ)) x y
  rw [hy, sub_zero] at heq
  rw [heq, ← dist_eq_norm] at hbound
  apply (lt_div_iff₀ (show (0 : ℝ) < ((matrixDenominator Q * l : ℕ) : ℝ) by exact_mod_cast hD)).mpr
  calc
    |((fun i j => (Q i j : ℝ)) *ᵥ x) i| * ((matrixDenominator Q * l : ℕ) : ℝ) ≤
        (((Fintype.card κ : ℝ) + 1) * (H + 1) * dist x y) * ((matrixDenominator Q * l : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ < 1 := by nlinarith [hnear]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem bch_linear_words_sum {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    ∑ w ∈ (bchBracketSupport s).filter (fun w => w.tail = []),
      bchBracketCoefficient s w • dynkinWord ![a, b] w = a + b := by
  classical
  let : LieRing (ℚ × ℚ) := LieRing.ofAssociativeRing
  let : IsLieAbelian (ℚ × ℚ) :=
    ⟨fun x y => by rw [LieRing.of_associative_ring_bracket, mul_comm x y, sub_self]⟩
  let φ : (ℚ × ℚ) →ₗ[ℚ] L :=
    (LinearMap.fst ℚ ℚ ℚ).smulRight a + (LinearMap.snd ℚ ℚ ℚ).smulRight b
  let x : ℚ × ℚ := (1, 0)
  let y : ℚ × ℚ := (0, 1)
  have hxy (i : Fin 2) : φ (![x, y] i) = ![a, b] i := by
    fin_cases i <;> simp [φ, x, y]
  have hterm (w : FreeSemigroup (Fin 2)) :
      φ (dynkinWord ![x, y] w) = if w.tail = [] then dynkinWord ![a, b] w else 0 := by
    by_cases hw : w.tail = []
    · simp only [hw, if_pos, dynkinWord, rightBracketList_nil, Module.End.one_apply]
      exact hxy w.head
    · rw [dynkinWord_eq_zero_of_abelian _ _ hw, map_zero, if_neg hw]
  have h := congrArg φ (lieBCH_eq_add_of_isLieAbelian hs x y)
  rw [lieBCH_bracket_formula] at h
  simp only [map_sum, map_smul, hterm, smul_ite, smul_zero] at h
  simpa only [Finset.sum_filter, map_add, hxy 0, hxy 1, φ, x, y,
    LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    one_smul, zero_smul, add_zero, zero_add] using h

theorem lieBCH_eq_add_nonlinear_sum {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    lieBCH s a b = a + b +
      ∑ w ∈ (bchBracketSupport s).filter (fun w => w.tail ≠ []),
        bchBracketCoefficient s w • dynkinWord ![a, b] w := by
  classical
  rw [lieBCH_bracket_formula, ← bch_linear_words_sum hs a b]
  exact (Finset.sum_filter_add_sum_filter_not (bchBracketSupport s)
    (fun w => w.tail = []) (fun w => bchBracketCoefficient s w • dynkinWord ![a, b] w)).symm

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

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [DecidableEq ι] [DecidableEq κ]

theorem exists_bounded_lie_embedding_retraction (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hB : ∀ i j, RationalHeightLE (LinearMap.toMatrix b e φ.toLinearMap i j) H) :
    ∃ P : Matrix κ ι ℚ, P * LinearMap.toMatrix b e φ.toLinearMap = 1 ∧
      (∀ i j, RationalHeightLE (P i j) (rationalSolveHeight (Fintype.card κ) H)) ∧
      ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
        (rationalLieStructureHeight (Fintype.card ι) (max H (rationalSolveHeight (Fintype.card κ) H))) := by
  have hli := Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ.toLinearMap hφ)
  obtain ⟨P, hP, hPH⟩ := exists_bounded_rational_left_inverse (LinearMap.toMatrix b e φ.toLinearMap) hli hH hB
  refine ⟨P, hP, hPH, ?_⟩
  intro i j k
  rw [lieStructureConstants_embedding b e φ P hP]
  exact transportedLieConstants_height_uniform _ _ _
    (fun u v w => (hc u v w).mono (le_max_left _ _))
    (fun u v => (hPH u v).mono (le_max_right _ _))
    (fun u v => (hB u v).mono (le_max_left _ _)) i j k

end Erdos3

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

theorem geometric_mean_norm_ge_of_linear_bias {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (hT : ∀ i, 0 < T i) (a : ι → Circle) {δ : ℝ}
    (hbias : δ ≤ ‖linearPhaseMean T a‖) (i : ι) :
    δ ≤ ‖geometricCharacterMean (T i) (a i)‖ := by
  classical
  rw [linearPhaseMean_eq_product, norm_prod] at hbias
  apply hbias.trans
  have h := Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
    (fun j _ => norm_nonneg (geometricCharacterMean (T j) (a j)))
    (fun j _ _ => norm_geometricCharacterMean_le_one (T j) (hT j) (a j))
  simpa only [Finset.prod_singleton] using h

theorem linear_phase_near_integers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℕ) (hT : ∀ i, 0 < T i) (a : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (a i : Circle))‖) :
    ∀ i, |a i - round (a i)| ≤ 1 / (2 * T i * δ) := by
  intro i
  rw [← integerDistance_coe]
  exact integerDistance_le_of_geometric_mean (hT i) _ hδ
    (geometric_mean_norm_ge_of_linear_bias T hT _ hbias i)

end CircleFourier
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ShiftedSmoothLawBounds
namespace OAI

section

namespace Erdos3

theorem shiftedSmoothCoefficientPMF_le (a : ℝ) {S : ℝ}
    (hS : 8 * (probabilityProfileLipschitz : ℝ) ≤ S) (k : ℤ) :
    (shiftedSmoothCoefficientPMF a S (smoothSamplingScale_pos hS)
      (shiftedSmoothSampleSum_pos a hS) k).toReal ≤ 2 / S := by
  rw [shiftedSmoothCoefficientPMF_apply]
  have hZ := shiftedSmoothSampleSum_pos a hS
  calc
    _ ≤ 1 / shiftedSmoothSampleSum a S :=
      div_le_div_of_nonneg_right (smoothProbabilityProfile_range _).2 hZ.le
    _ ≤ 2 / S := (div_le_div_iff₀ hZ (smoothSamplingScale_pos hS)).mpr
      (by linarith [(shiftedSmoothSampleSum_bounds a hS).1])

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

theorem uniform_condition_condition_mean {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    [Nonempty Ω] (G R : Finset Ω) (hG : 0 < (uniform Ω).mass G)
    (hR : 0 < ((uniform Ω).condition G hG).mass R) (f : Ω → ℝ) :
    (((uniform Ω).condition G hG).condition R hR).mean f = 𝔼 x : ↥(G ∩ R), f x := by
  rw [condition_condition]
  exact uniform_condition_mean _ _ f

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

noncomputable def crtPrimePowerPolynomialLaw (p A : L → ℕ) [∀ l, NeZero (p l)] :
    FiniteProbabilityWeights (∀ l, V → ZMod (p l ^ A l)) :=
  FiniteProbabilityWeights.pi (fun l => FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lieBCH_mem_of_divisible_brackets (M : Submodule ℤ L) (D : ℕ) {s : ℕ}
    (hs : 1 ≤ s)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ∃ z ∈ M, ⁅a, b⁆ = (D : ℚ) • z)
    (hc : ∀ w ∈ bchBracketSupport s, ∃ n : ℤ, (D : ℚ) * bchBracketCoefficient s w = (n : ℚ))
    {a b : L} (ha : a ∈ M) (hb : b ∈ M) : lieBCH s a b ∈ M := by
  classical
  rw [lieBCH_eq_add_nonlinear_sum hs]
  apply M.add_mem (M.add_mem ha hb)
  apply M.sum_mem
  intro w hw
  obtain ⟨hw, htail⟩ := Finset.mem_filter.mp hw
  have hf : ∀ i : Fin 2, ![a, b] i ∈ M := by
    intro i
    fin_cases i <;> assumption
  obtain ⟨z, hz, heq⟩ := dynkinWord_mem_multiple M D hbr ![a, b] hf w htail
  obtain ⟨n, hn⟩ := hc w hw
  rw [heq, smul_smul, mul_comm _ (D : ℚ), hn, Int.cast_smul_eq_zsmul ℚ]
  exact M.smul_mem n hz

theorem lieBCH_mem_of_divisible_brackets_nilpotent (M : Submodule ℤ L) (D : ℕ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hbr : ∀ a ∈ M, ∀ b ∈ M, ∃ z ∈ M, ⁅a, b⁆ = (D : ℚ) • z)
    (hc : ∀ w ∈ bchBracketSupport s, ∃ n : ℤ, (D : ℚ) * bchBracketCoefficient s w = (n : ℚ))
    {a b : L} (ha : a ∈ M) (hb : b ∈ M) : lieBCH s a b ∈ M := by
  by_cases hs : 1 ≤ s
  · exact lieBCH_mem_of_divisible_brackets M D hs hbr hc ha hb
  · have hs0 : s = 0 := by omega
    subst s
    have hz : a = 0 := by
      have h : a ∈ LieModule.lowerCentralSeries ℚ L L 0 := by simp
      simpa only [hnil, LieSubmodule.mem_bot] using h
    rw [hz, lieBCH_zero_left hnil]
    exact hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedFreeWords
namespace OAI

section

namespace Erdos3

variable {X : Type*} {s : ℕ}

def boundedFreeWordCode (w : BoundedFreeWord X s) : Σ n : Fin (s + 1), Fin n.val → X :=
  ⟨⟨w.val.toFreeMonoid.toList.length, by
      exact Nat.lt_succ_of_le ((freeSemigroup_toFreeMonoid_length w.val).le.trans w.property)⟩,
    w.val.toFreeMonoid.toList.get⟩

theorem boundedFreeWordCode_injective : Function.Injective (boundedFreeWordCode (X := X) (s := s)) := by
  intro u v huv
  have he := congrArg (fun z : Σ n : Fin (s + 1), Fin n.val → X => List.ofFn z.2) huv
  change List.ofFn u.val.toFreeMonoid.toList.get = List.ofFn v.val.toFreeMonoid.toList.get at he
  rw [List.ofFn_get, List.ofFn_get] at he
  apply Subtype.ext
  apply FreeSemigroup.toFreeMonoid_injective
  exact congrArg FreeMonoid.ofList he

noncomputable instance boundedFreeWordFintype [Fintype X] : Fintype (BoundedFreeWord X s) :=
  Fintype.ofInjective boundedFreeWordCode boundedFreeWordCode_injective

theorem boundedFreeWord_card_le [Fintype X] :
    Fintype.card (BoundedFreeWord X s) ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  have hc := Fintype.card_le_of_injective (boundedFreeWordCode (X := X) (s := s))
    boundedFreeWordCode_injective
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  calc
    _ ≤ ∑ n : Fin (s + 1), Fintype.card X ^ n.val := hc
    _ ≤ ∑ _n : Fin (s + 1), (Fintype.card X + 1) ^ s := by
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedBinomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial Module
open scoped Manifold ContDiff TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)

theorem polynomialOrbitRealEval_integer (w : σ → ℕ) (p : F.PolynomialOrbit w)
    (x : σ → ℤ) :
    F.polynomialOrbitRealEval w (fun i => (x i : ℝ)) p = F.polynomialOrbitEval w x p := by
  apply NilpotentLieBCHGroup.ext
  simpa only [polynomialOrbitRealEval_coord, polynomialOrbitEval_coord,
    map_intCast] using
    eval₂_algebraMap (S := ℝ) (fun i => (x i : ℚ)) p.log

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieTreeSupport
namespace OAI

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

theorem lieTreeEval_pi (v : I → J → L) (a : FreeMagma I) (j : J) :
    lieTreeEval v a j = lieTreeEval (fun i => v i j) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change ⁅lieTreeEval v a j, lieTreeEval v b j⁆ =
      ⁅lieTreeEval (fun i => v i j) a, lieTreeEval (fun i => v i j) b⁆
    rw [ha, hb]

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

theorem weightedLieTreeSpan_antitone (v : I → L) (w : I → ℕ) (d : ℕ) :
    Antitone (weightedLieTreeSpan v w d) := by
  intro r t hrt
  apply Submodule.span_mono
  rintro x ⟨a, ha, ht, hx⟩
  exact ⟨a, ha, hrt.trans ht, hx⟩

theorem FilteredLieTree.eval_mem_weighted_span {s : ℕ} {F : NilpotentLieFiltration L s}
    (v : I → L) (w : I → ℕ)
    (hspan : ∀ d, 0 < d → F.layer d ≤ Submodule.span ℚ (v '' {i | w i = d}))
    {d r : ℕ} (a : FilteredLieTree F d r) : a.eval ∈ weightedLieTreeSpan v w d r := by
  induction a with
  | leaf hd x hx => exact span_weighted_leaves_le v w _ (hspan _ hd hx)
  | bracket a b ha hb => exact weightedLieTreeSpan_lie_mem v w ha hb

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s)

theorem lieTreeEval_mem_rankLayer (v : I → L) (w : I → ℕ) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i)) (a : FreeMagma I) :
    lieTreeEval v a ∈ F.rankLayer (lieTreeWeight w a) a.length := by
  induction a using FreeMagma.rec with
  | of i => exact F.tree_eval_mem_rankLayer (.leaf (hw i) (v i) (hv i)) le_rfl
  | mul a b ha hb => exact F.rankLayer_lie_mem ha hb

theorem rankLayer_eq_weighted_tree_span (v : I → L) (w : I → ℕ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i))
    (hspan : ∀ d, 0 < d → F.layer d ≤ Submodule.span ℚ (v '' {i | w i = d})) (d r : ℕ) :
    F.rankLayer d r = F.layer (d + 1) ⊔ weightedLieTreeSpan v w d r := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro x ⟨k, hrk, a, rfl⟩
    have h := weightedLieTreeSpan_antitone v w d hrk (a.eval_mem_weighted_span v w hspan)
    exact (show weightedLieTreeSpan v w d r ≤ F.layer (d + 1) ⊔ weightedLieTreeSpan v w d r from
      le_sup_right) h
  · apply sup_le (F.layer_succ_le_rankLayer d r)
    apply Submodule.span_le.mpr
    rintro x ⟨a, ha, hr, rfl⟩
    have h := F.lieTreeEval_mem_rankLayer v w hw hv a
    rw [ha] at h
    exact F.rankLayer_rank_antitone d hr h

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3

variable (I : Type*) [Fintype I]

variable {I} {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem weightedLieTreeSpan_eq_finite_span (v : I → L) (w : I → ℕ) (hw : ∀ i, 0 < w i)
    (d r : ℕ) : weightedLieTreeSpan v w d r =
      Submodule.span ℚ (finiteWeightedLieValues v w d r : Set L) := by
  classical
  unfold weightedLieTreeSpan
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, hr, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨?_, ha, hr⟩, rfl⟩
    apply mem_finiteLieTrees_of_length_le
    exact (lieTree_length_le_weight w hw a).trans_eq ha
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_, hd, hr⟩ := Finset.mem_filter.mp ha
    exact ⟨a, hd, hr, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
namespace OAI

section

namespace Erdos3

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

namespace DegreeRankLieFiltration

variable {L} {s r : ℕ} (F : DegreeRankLieFiltration L s r)

theorem layer_le_associatedDegree (d i : ℕ) : F.layer d i ≤ F.associatedDegree.layer d :=
  F.rank_antitone d (Nat.zero_le i)

end DegreeRankLieFiltration

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem rankFlag_antitone : Antitone F.rankFlag := by
  intro i j hij
  have hd : i / (s + 1) ≤ j / (s + 1) := Nat.div_le_div_right hij
  rcases lt_or_eq_of_le hd with h | h
  · exact F.lex_antitone (Or.inl h)
  · apply F.lex_antitone (Or.inr ⟨h, ?_⟩)
    have hi := Nat.mod_add_div i (s + 1)
    have hj := Nat.mod_add_div j (s + 1)
    rw [h] at hi
    omega

theorem rankFlag_mul (d : ℕ) : F.rankFlag (d * (s + 1)) = F.layer d 0 := by
  simp [rankFlag, Nat.mul_mod_left]

theorem rankFlag_terminal : F.rankFlag ((s + 1) * (s + 1)) = ⊥ := by
  rw [F.rankFlag_mul]
  exact F.layer_eq_bot_of_past_top (Or.inl (by omega))

theorem rankFlag_lie_mem {n : ℕ} {x y : L} (hy : y ∈ F.rankFlag n) :
    ⁅x, y⁆ ∈ F.rankFlag (n + 1) := by
  have hx : x ∈ F.layer 1 0 := by simp only [F.one_eq_top, Submodule.mem_top]
  have hbr : ⁅x, y⁆ ∈ F.layer (n / (s + 1) + 1) (n % (s + 1)) := by
    simpa only [add_comm 1, zero_add] using F.lie_mem hx hy
  have hzero : ⁅x, y⁆ ∈ F.layer (n / (s + 1) + 1) 0 :=
    F.rank_antitone _ (Nat.zero_le _) hbr
  rw [← F.rankFlag_mul] at hzero
  apply F.rankFlag_antitone _ hzero
  have hmod : n % (s + 1) < s + 1 := Nat.mod_lt n (by omega)
  have heq := Nat.mod_add_div n (s + 1)
  rw [add_mul, one_mul, Nat.mul_comm (n / (s + 1)) (s + 1)]
  omega

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem rankFlag_encode (i j : ℕ) (hj : j ≤ s) :
    F.rankFlag (i * (s + 1) + j) = F.layer i j := by
  have hA : 0 < s + 1 := by omega
  have hjA : j < s + 1 := by omega
  unfold rankFlag
  rw [Nat.mul_comm i (s + 1), Nat.mul_add_div hA, Nat.div_eq_of_lt hjA,
    add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hjA]

theorem layer_eq_rankFlag (i j : ℕ) :
    ∃ k : Fin ((s + 1) * (s + 1) + 1), F.layer i j = F.rankFlag k.val := by
  by_cases hi : i ≤ s
  · by_cases hj : j ≤ s
    · exact ⟨⟨i * (s + 1) + j, by have := rankFlag_encode_lt i j hi hj; omega⟩,
        (F.rankFlag_encode i j hj).symm⟩
    · rw [F.overshoot i j (by omega)]
      refine ⟨⟨(i + 1) * (s + 1), ?_⟩, (F.rankFlag_mul (i + 1)).symm⟩
      have h := Nat.mul_le_mul_right (s + 1) (show i + 1 ≤ s + 1 by omega)
      omega
  · refine ⟨⟨(s + 1) * (s + 1), by omega⟩, ?_⟩
    rw [F.rankFlag_terminal, F.layer_eq_bot_of_past_top (Or.inl (by omega))]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem higherHorizontalMk_eq (i : ℕ) (x y : F.layer i 1) :
    F.higherHorizontalMk i x = F.higherHorizontalMk i y ↔ x.val - y.val ∈ F.layer i 2 :=
  Submodule.Quotient.eq (F.higherHorizontalKernel i)

theorem higherHorizontalMk_representative (i : ℕ) (v : F.HigherHorizontal i) :
    F.higherHorizontalMk i (F.higherHorizontalRepresentative i v) = v := by
  classical
  by_cases hv : v = 0
  · simp [higherHorizontalRepresentative, hv]
  · simpa [higherHorizontalRepresentative, hv] using
      Classical.choose_spec (F.higherHorizontalMk_surjective i v)

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem rank_zero_top_eq_bot (F : DegreeRankLieFiltration L s 0) :
    F.associatedDegree.layer s = ⊥ := by
  change F.layer s 0 = ⊥
  rw [F.rank_zero_eq_one]
  exact F.terminal

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem imageDefiningDenominator_le_exp {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℚ) (d H m : ℕ)
    (hQ : ∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight d (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) :
    ((matrixDenominator Q * m : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 48) := by
  have hpp := le_power_budget hp (by decide : 1 ≤ 10)
  have h := matrixDenominator_allowance_le_exp Q m (imageDefiningHeight d (Fintype.card ι) H) hQ
    (by positivity : 0 ≤ (p + 2) ^ 10) (hn.trans hpp) (hn.trans hpp)
    (imageDefiningHeight_le_exp d _ H hp hd hn hH) (hm.trans (Real.exp_le_exp.mpr hpp))
  rw [Nat.mul_comm] at h
  exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 10 4))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem complexMean_prod (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X × Y → ℂ) :
    (p.prod q).complexMean F = p.complexMean (fun x => q.complexMean (fun y => F (x, y))) := by
  simp only [complexMean, prod, Fintype.sum_prod_type, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem ofSupportedPMF_map_mean {X Y : Type*} [Fintype Y]
    (p : PMF X) (T : Finset X) (hT : ∀ x ∉ T, (p x).toReal = 0)
    (f : X → Y) (g : Y → ℝ) :
    (ofSupportedPMF p T hT).mean (fun x => g (f x.val)) =
      (ofPMF (p.map f)).mean g := by
  have hmap (y : Y) : (p.map f y).toReal =
      ∑ x : T, (p x.val).toReal * (if f x.val = y then 1 else 0) := by
    rw [pmf_map_toReal_indicator,
      Finset.sum_coe_sort T (fun x => (p x).toReal * (if f x = y then 1 else 0))]
    exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hT x hx, zero_mul])).tsum_eq
  symm
  simp only [mean, ofPMF_weight, ofSupportedPMF_weight, hmap, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem ofSupportedPMF_map_event {X Y : Type*} [Fintype Y]
    (p : PMF X) (T : Finset X) (hT : ∀ x ∉ T, (p x).toReal = 0)
    (f : X → Y) (E : Y → Prop) :
    (ofSupportedPMF p T hT).eventProbability (fun x => E (f x.val)) =
      (ofPMF (p.map f)).eventProbability E :=
  ofSupportedPMF_map_mean p T hT f (fun y => if E y then 1 else 0)

end FiniteProbabilityWeights

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

namespace FiniteProbabilityWeights

theorem translated_subset_mixture_compare {X Y Z : Type*} [Fintype Z] [DecidableEq Y]
    (p : FiniteProbabilityWeights Z) (A : Finset X) (B : Finset Y) (hA : A.Nonempty)
    (g : Z → X → Y) (hg : ∀ z, Set.InjOn (g z) A)
    (hB : ∀ z x, x ∈ A → g z x ∈ B)
    (f : Y → ℂ) (hf : ∀ y ∈ B, ‖f y‖ ≤ 1) :
    ‖(𝔼 x ∈ A, p.complexMean (fun z => f (g z x))) - 𝔼 y ∈ B, f y‖ ≤
      2 * (1 - (A.card : ℝ) / B.card) := by
  rw [← p.complexMean_finset_expect]
  have hc : p.complexMean (fun _ => 𝔼 y ∈ B, f y) = 𝔼 y ∈ B, f y := by
    simp only [complexMean, ← Finset.sum_mul, ← Complex.ofReal_sum, p.total,
      Complex.ofReal_one, one_mul]
  rw [← hc]
  exact (p.norm_complexMean_sub_le _ _ (fun _ => 2 * (1 - (A.card : ℝ) / B.card))
    (fun z _ => norm_expect_injective_sub_le A B hA (g z) (hg z) (hB z) f hf)).trans_eq
    (p.mean_const _)

end FiniteProbabilityWeights
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
namespace OAI

section

namespace Erdos3

theorem selectedResidueDensityMass_complex {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x) (D : (K × I → ℤ) → ℝ) :
    (selectedResidueDensityMass modulus G V D : ℂ) =
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (D x : ℂ) := by
  simp only [selectedResidueDensityMass, finiteDensityMass_complex, selectedResidueSmoothPMF_toReal]

noncomputable def selectedResidueDensityPMF {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) : PMF (K × I → ℤ) :=
  finiteDensityTiltPMF _ (rectangularWeightIndices 0 V 1)
    (selectedResidueSmoothWeight_nonneg modulus G V)
    (selectedResidueSmoothWeight_zero_off modulus G V hV) hZ D hD0 hD

theorem selectedResidueDensityPMF_complexMean {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D) (f : (K × I → ℤ) → ℂ) :
    (∑' x, ((selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal : ℂ) * f x) =
      (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * ((D x : ℂ) * f x)) /
        (selectedResidueDensityMass modulus G V D : ℂ) := by
  unfold selectedResidueDensityMass at hD ⊢
  simp only [selectedResidueDensityPMF, finiteDensityTiltPMF_complexMean,
    selectedResidueSmoothPMF_toReal]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem selectedResidueDensityMass_integral {K I : Type*} [Fintype K] [Fintype I]
    (stride : I → ℕ) (cells : Finset (ColumnResiduePattern K I stride))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight stride cells V x)
    (f : (K × I → ℤ) → ℝ)
    (hf : Integrable f (selectedResidueSmoothPMF stride cells V hV hZ).toMeasure) :
    selectedResidueDensityMass stride cells V f =
      ∫ x, f x ∂(selectedResidueSmoothPMF stride cells V hV hZ).toMeasure := by
  apply Complex.ofReal_injective
  rw [selectedResidueDensityMass_complex stride cells V hV hZ,
    ← integral_complex_ofReal, PMF.integral_eq_tsum _ _ hf.ofReal]
  simp only [Complex.real_smul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem uniform_injective_mean_le {B X : Type*}
    [Fintype B] [Nonempty B] [Fintype X] [Nonempty X]
    (F : B → X) (hF : Function.Injective F) (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x) :
    (uniform B).mean (fun b => φ (F b)) ≤
      ((Fintype.card X : ℝ) / Fintype.card B) * (uniform X).mean φ := by
  have hsum : (∑ b, φ (F b)) ≤ ∑ x, φ x :=
    Finset.sum_le_sum_of_injOn F hF.injOn (Finset.subset_univ _)
      (fun _ _ => le_rfl) (fun x _ _ => hφ x)
  rw [uniform_mean, uniform_mean, Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card]
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (∑ x, φ x) / Fintype.card B := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
    _ = _ := by field_simp

end Erdos3.FiniteProbabilityWeights

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

theorem uniform_finitePushforward_mean [Nonempty U] (f : U → T) (g : T → ℝ) :
    ((uniform U).finitePushforward f).mean g = 𝔼 u, g (f u) := by
  rw [mean_finitePushforward, uniform_mean]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RationalBCHProducts
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realDenominatorGrid_subset_of_dvd {ι : Type*} {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m) :
    (realDenominatorGrid l : Set (ι → ℝ)) ⊆ realDenominatorGrid m := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := realDenominatorGrid_exists_rational l hl x hx
  exact (real_cast_mem_denominatorGrid_iff m y).mpr (denominatorGrid_subset_of_dvd hlm hy)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientInducedMark
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
  (hI : F.layer (t + 1) ≤ I.toSubmodule)

noncomputable def realQuotientStepHom :
    F.realification.Group →* (F.quotientLie I hI).realification.Group :=
  realificationMap (hnil := F.lowerCentralSeries_eq_bot)
    (hM := (F.quotientLie I hI).lowerCentralSeries_eq_bot) (lieQuotientMap I)

theorem realQuotientStep_mem_layer {j : ℕ} {x : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realification.layer j) :
    realificationLieHom (lieQuotientMap I) x ∈ (F.quotientLie I hI).realification.layer j := by
  have hmap : (F.layer j).baseChange ℝ ≤
      (((F.layer j).map (lieQuotientMap I).toLinearMap).baseChange ℝ).comap
        (realificationLieHom (lieQuotientMap I)).toLinearMap := by
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change (1 : ℝ) ⊗ₜ[ℚ] (lieQuotientMap I a) ∈
      ((F.layer j).map (lieQuotientMap I).toLinearMap).baseChange ℝ
    exact Submodule.tmul_mem_baseChange_of_mem 1 ⟨a, ha, rfl⟩
  exact hmap hx

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

open scoped Matrix

namespace Erdos3

theorem exists_real_span_defining_matrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ Q : Matrix ι ι ℚ,
      (∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H)) ∧
      LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) =
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  let Q : Matrix ι ι ℚ := 1 - A * S
  have hSr := real_matrix_image_section A S hS
  have hQr : Matrix.of (fun i j => (Q i j : ℝ)) =
      1 - Matrix.of (fun i j => (A i j : ℝ)) * Matrix.of (fun i j => (S i j : ℝ)) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Q, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, hij]
  refine ⟨Q, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix ι ι ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul A S hA hSH i j
    simpa only [Q, Matrix.sub_apply, imageDefiningHeight, mul_one] using hI.sub hprod
  · ext x
    change Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0 ↔
      ∃ y, Matrix.of (fun i j => (A i j : ℝ)) *ᵥ y = x
    rw [hQr, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro hx
      exact ⟨(fun i j => (S i j : ℝ)) *ᵥ x, (sub_eq_zero.mp hx).symm⟩
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSr, sub_self]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AdaptedBasisGeometry
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

theorem inverse_basis_entries_height (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ j i, RationalHeightLE (e.repr (b j) i) H) :
    ∀ i j, RationalHeightLE (b.repr (e i) j) (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  let A := LinearMap.toMatrix b e (LinearMap.id : L →ₗ[ℚ] L)
  let C := LinearMap.toMatrix e b (LinearMap.id : L →ₗ[ℚ] L)
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact hb j i
  have hli : LinearIndependent ℚ A.col :=
    Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e LinearMap.id Function.injective_id)
  obtain ⟨P, hPA, hPH⟩ := exists_bounded_rational_left_inverse A hli hH hA
  have hAC : A * C = 1 := by
    dsimp only [A, C]
    rw [← LinearMap.toMatrix_comp, LinearMap.id_comp, LinearMap.toMatrix_id]
  have hPC : P = C := by
    calc
      P = P * 1 := (Matrix.mul_one P).symm
      _ = P * (A * C) := by rw [hAC]
      _ = (P * A) * C := (Matrix.mul_assoc P A C).symm
      _ = C := by rw [hPA, Matrix.one_mul]
  intro i j
  have h := hPH j i
  rw [hPC] at h
  simpa only [C, LinearMap.toMatrix_apply, LinearMap.id_apply] using h

theorem basis_change_structure_height (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ j i, RationalHeightLE (e.repr (b j) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
      (rationalLieStructureHeight (Fintype.card ι) (max H (rationalSolveHeight (Fintype.card κ) H))) := by
  classical
  obtain ⟨_, _, _, h⟩ := exists_bounded_lie_embedding_retraction b e
    (LieHom.id : L →ₗ⁅ℚ⁆ L) Function.injective_id hH hc (by
      intro i j
      rw [LinearMap.toMatrix_apply]
      exact hb j i)
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LayerSamplingRankAffine
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residueAffinePolynomial_eval_real {I : Type*} (q : ℕ) (r : I → ℤ)
    (x : I → ℝ) (P : MvPolynomial I ℝ) :
    MvPolynomial.eval x (residueAffinePolynomial q r P) =
      MvPolynomial.eval (fun i => (r i : ℝ) + (q : ℝ)*x i) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [residueAffinePolynomial]
  | add P Q hP hQ =>
    simpa only [residueAffinePolynomial, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [residueAffinePolynomial, map_mul, MvPolynomial.eval₂Hom_X', map_add,
      MvPolynomial.eval_C, MvPolynomial.eval_X] at *
    rw [hP]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

def identity (N : I → ℕ) : ResidueBoxSlice N 1 where
  start _ := 0
  length := N
  inside _ _ hj := by simpa using hj

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeFullSliceLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
namespace ResidueBoxSlice
variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q s d : ℕ}

def fullSlicePointInIntegerBox (S : ResidueBoxSlice N q) (u : ∀ i, Fin (S.length i)) : integerBox N :=
  ⟨fun i => ((S.point u i).val : ℤ), (mem_integerBox _ _).mpr
    (fun i => ⟨Int.natCast_nonneg _, by exact_mod_cast (S.point u i).isLt⟩)⟩

end ResidueBoxSlice

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

theorem controlled_real_column_span_separation
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    {α : σ →₀ ℕ} (hα : α ≠ 0) (a b : ι → ℝ)
    (ha : ‖a‖ ≤ Real.exp p / monomialScale T α)
    (hb : b ∈ realDenominatorGrid l)
    (hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ)))) :
    a ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ∧
      b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
  obtain ⟨Q, hQ, hker⟩ := exists_real_span_defining_matrix A hH hA
  have hscale : Real.exp (separationBudget p) ≤ monomialScale T α :=
    le_monomialScale_of_ne_zero T (Real.one_le_exp (separationBudget_nonneg hp)) hT hα
  have hasmall : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p) :=
    ha.trans (div_le_div_of_nonneg_left (Real.exp_nonneg p) (Real.exp_pos _) hscale)
  have hden := imageDefiningDenominator_le_exp Q (Fintype.card κ) H l hQ hp hκ hι hHp hlp
  have hrow := imageDefiningRow_bound_le_exp (Fintype.card κ) (Fintype.card ι) H hp hκ hι hHp
  have hnear : ((matrixDenominator Q * l : ℕ) : ℝ) *
      (((Fintype.card ι : ℝ) + 1) *
        ((imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H : ℝ) + 1)) *
      dist b (a + b) < 1 := by
    have he : b - (a + b) = -a := by abel
    rw [dist_eq_norm, he, norm_neg]
    exact separationBudget_small hden hrow (by positivity) (norm_nonneg _) hasmall
  have hsumker : (fun i j => (Q i j : ℝ)) *ᵥ (a + b) = 0 := by
    have h := (real_column_span_mem_iff A (a + b)).mp hsum
    rw [← hker] at h
    exact h
  have hbker := rational_matrix_kernel_separation Q
    (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H : ℝ≥0)
    (fun i j => (hQ i j).abs_real_le) l hl b (a + b) hb hsumker hnear
  have hbrange : b ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
    rw [← hker]
    exact hbker
  have hbspan := (real_column_span_mem_iff A b).mpr hbrange
  refine ⟨?_, hbspan⟩
  simpa only [add_sub_cancel_right] using
    (Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ)))).sub_mem hsum hbspan

end Erdos3

end

section

open scoped Matrix

namespace Erdos3

theorem exists_controlled_linear_splitting
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ (S : Matrix κ ι ℚ) (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a b : ι → ℝ) (v : κ → ℝ),
      ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
      (fun i j => (A i j : ℝ)) *ᵥ v = a + b →
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ a) = a ∧
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ b) = b ∧
      ‖(fun i j => (S i j : ℝ)) *ᵥ a‖ ≤
        Real.exp ((p + 2) ^ 18 + p) / monomialScale T α ∧
      (fun i j => (S i j : ℝ)) *ᵥ b ∈ realDenominatorGrid m ∧
      (fun i j => (A i j : ℝ)) *ᵥ
        (v - (fun i j => (S i j : ℝ)) *ᵥ a - (fun i j => (S i j : ℝ)) *ᵥ b) = 0 := by
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  refine ⟨S, matrixDenominator S * l, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hSH hp hι hκ hHp hlp, ?_⟩
  intro α hα a b v ha hb hv
  have hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) :=
    (real_column_span_mem_iff A (a + b)).mpr ⟨v, hv⟩
  obtain ⟨haspan, hbspan⟩ := controlled_real_column_span_separation A hH hl hA hp hι hκ
    hHp hlp T hT hα a b ha hb hsum
  have hSa := real_matrix_image_section_apply A S hS a ((real_column_span_mem_iff A a).mp haspan)
  have hSb := real_matrix_image_section_apply A S hS b ((real_column_span_mem_iff A b).mp hbspan)
  refine ⟨hSa, hSb, ?_, real_matrix_denominator_grid S l b hb, ?_⟩
  · calc
      _ ≤ Real.exp ((p + 2) ^ 18) * ‖a‖ := real_image_section_norm_bound S H hSH hp hι hκ hHp a
      _ ≤ Real.exp ((p + 2) ^ 18) * (Real.exp p / monomialScale T α) :=
        mul_le_mul_of_nonneg_left ha (Real.exp_nonneg _)
      _ = _ := by rw [← mul_div_assoc, ← Real.exp_add]
  · change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
      (v - Matrix.of (fun i j => (S i j : ℝ)) *ᵥ a -
        Matrix.of (fun i j => (S i j : ℝ)) *ᵥ b) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    exact (congrArg₂ (fun x y : ι → ℝ => x - y)
      (congrArg₂ (fun x y : ι → ℝ => x - y) hv hSa) hSb).trans (by abel)

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

theorem translatedQuotientChart_measurable (Λ : Submodule ℤ E) (v : T → E) :
    Measurable (translatedQuotientChart Λ v) := by
  have hq : Measurable (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) := measurable_quotient_mk''
  exact hq.comp (measurable_fst.sub ((measurable_of_countable v).comp measurable_snd))

omit [MeasurableSingletonClass T] in
theorem translatedQuotientChart_measurable_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    MeasurableSet (translatedQuotientChart Λ v '' S) := by
  let : IsClosed (Λ.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  rw [translatedQuotientChart_image]
  apply MeasurableSet.iUnion
  intro t
  have hq : Continuous (fun x : E => (QuotientAddGroup.mk (x - v t) : E ⧸ Λ.toAddSubgroup)) :=
    continuous_quotient_mk'.comp (continuous_id.sub continuous_const)
  apply (hS.preimage (measurable_id.prodMk measurable_const)).image_of_continuousOn_injOn
    hq.continuousOn
  intro x hx y hy he
  exact congrArg Prod.fst (hinj hx hy he)

theorem translatedQuotientChart_embedding (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (v : T → E) {S : Set (E × T)} (hS : MeasurableSet S)
    (hinj : InjOn (translatedQuotientChart Λ v) S) :
    MeasurableEmbedding (fun x : S => translatedQuotientChart Λ v x.val) := by
  refine ⟨fun x y he => Subtype.ext (hinj x.property y.property he),
    (translatedQuotientChart_measurable Λ v).comp measurable_subtype_coe, ?_⟩
  intro A hA
  have hm := (MeasurableEmbedding.subtype_coe hS).measurableSet_image' hA
  have hi := hinj.mono (show ((↑) : S → E × T) '' A ⊆ S by rintro x ⟨y, hy, rfl⟩; exact y.property)
  have he := translatedQuotientChart_measurable_image Λ v hm hi
  simpa only [image_image] using he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

theorem normalizedLatticeQuotient_embedding (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    MeasurableEmbedding
      (fun x : normalizedLatticePoint W b ⁻¹' Ω => normalizedLatticeQuotient W b hb x.val) :=
  translatedQuotientChart_embedding _ _ (hΩm.preimage (normalizedLatticePoint_continuous W b).measurable)
    (normalizedLatticeQuotient_injOn W b hb hΩ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedPolynomialChart
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

noncomputable def mixedPolynomialPoint (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W) (e : J → V →₀ ℕ)
    (a : I → J → ℝ) (z : Fin n → J → ℤ) (x : V → ℝ) : EuclideanSpace ℝ D :=
  (normalizedOrthogonalChart W b).symm
    (orthonormalChart o (fun i => MvPolynomial.eval x (monomialArrayPolynomial e (a i))),
      fun i => MvPolynomial.eval x
        (monomialArrayPolynomial e (fun j => (z i j : ℝ) / basisAxisScale b i)))

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

variable {D : Type*} [Fintype D] {n : ℕ}

theorem normalizedQuotientDensity_nonneg (W : Submodule ℝ (EuclideanSpace ℝ D))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    {Ω : Set (EuclideanSpace ℝ D)} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ standardLatticeSmallBox D)
    (f : W × (Fin n → ℤ) → ℝ) (hf : ∀ x, 0 ≤ f x) (y) :
    0 ≤ normalizedQuotientDensity W b hb Ω f y :=
  embeddingDensity_nonneg _ (normalizedLatticeQuotient_embedding W b hb hΩm hΩ).injective
    (ZLattice.covolume_pos (latticeSection (standardEuclideanLattice D) W) volume).le _
    (fun x => hf x.val) y

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalMixedDensity_nonneg
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (p : Fin n → PMF ℤ) (y) :
    0 ≤ canonicalMixedDensity W b hb o c w p y :=
  normalizedQuotientDensity_nonneg W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Subset.rfl) _ (orthonormalMixedDensity_nonneg o c w hw p) y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EmptyCoefficientDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalArrayDensity_nonneg
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Fin n → J → PMF ℤ) (y) :
    0 ≤ canonicalArrayDensity W b hb o c w p y :=
  Finset.prod_nonneg (fun j _ => canonicalMixedDensity_nonneg W b hb o _ _ (fun i => hw i j) _ _)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem canonicalCoefficientDensity_nonneg (hw : ∀ j i d, 0 < w j i d)
    (y : CoefficientTorus (K := K) U) : 0 ≤ canonicalCoefficientDensity U b hb o c w p y :=
  Finset.prod_nonneg (fun j _ => canonicalArrayDensity_nonneg _ (b j) (hb j) (o j)
    (c j) (w j) (hw j) (p j) _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedCoefficientRemainder
namespace OAI

section

namespace Erdos3

open Module Submodule

namespace VectorPolynomial

theorem euclideanCoefficientEquiv_mk {K : Type*} {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (c : CoefficientArray (K := K) U) (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U (QuotientAddGroup.mk' (coefficientIntegerLattice U) c) j d =
      QuotientAddGroup.mk' _ ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, d⟩)) := by
  apply (euclideanSubspaceTorusEquiv (U j)).injective
  rw [euclideanCoefficientEquiv_apply, AddEquiv.apply_symm_apply,
    euclideanSubspaceTorusEquiv_mk, ContinuousLinearEquiv.apply_symm_apply]
  rfl

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CoefficientPolynomialLift
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedPolynomialPoint_sum (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (x : V → ℝ) :
    mixedPolynomialPoint W b o e a.1 a.2 x =
      ∑ j, monomialScale x (e j) • mixedLiftCoefficient W b o a j := by
  change mixedRealPoint W b o
    (fun i => MvPolynomial.eval x (monomialArrayPolynomial e (a.1 i)),
      fun i => MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a.2 i j : ℝ) / basisAxisScale b i))) = _
  simp only [mixedLiftCoefficient, ← map_smul, ← map_sum]
  congr 1
  ext i <;> simp [monomialArrayPolynomial_eval, monomialScale, Finsupp.prod,
    Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, mul_comm]

theorem mixedLiftPolynomial_eval (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (x : V → ℝ) (d : D) :
    MvPolynomial.eval x (mixedLiftPolynomial W b o e a d) = mixedPolynomialPoint W b o e a.1 a.2 x d := by
  change _ = (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : D => ℝ) d) (mixedPolynomialPoint W b o e a.1 a.2 x)
  rw [mixedPolynomialPoint_sum, map_sum]
  simp [mixedLiftPolynomial, monomialArrayPolynomial_eval, monomialScale, Finsupp.prod, mul_comm]

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

theorem iteratedCircleComponent_norm_sub_le {N : ℕ} (hN : 0 < N)
    (A : α → IsometricCircleAction X) (is : List α) (k : Fin is.length → ℤ)
    {f g : X → ℂ} {K H : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith H g)
    {ε : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ ε) (x : X) :
    ‖iteratedCircleComponent N A is k f x - iteratedCircleComponent N A is k g x‖ ≤ ε := by
  induction is generalizing x with
  | nil => exact hfg x
  | cons i is ih =>
    apply (A i).component_norm_sub_le hN (k 0)
      (iteratedCircleComponent_lipschitz hN A is (fun j => k j.succ) hf).continuous
      (iteratedCircleComponent_lipschitz hN A is (fun j => k j.succ) hg).continuous
    intro y
    exact ih (fun j => k j.succ) y

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CoveredJetSampler
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical Matrix

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedCoveredJetCoordinates (d : ℕ)
    (p : (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ×
      (∀ j, O j → B j → ZMod d)) : CoveredJetChartSource U O B n d :=
  fun j t => (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (p.1 j) t), p.2 j t)

end VectorPolynomial

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
open scoped BigOperators NNReal

namespace IsometricCircleAction

variable {X : Type*} [PseudoMetricSpace X]

theorem average_invariant (A : IsometricCircleAction X) (f : X → ℂ) (t : Circle) (x : X) :
    A.average f (A.act t x) = A.average f x := by
  let := A.toAddAction
  change circleFourierComponent 0 f (t +ᵥ x) = circleFourierComponent 0 f x
  simpa only [neg_zero, zero_smul, character_zero, one_mul] using
    circleFourierComponent_vadd 0 f t x

end IsometricCircleAction
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X α : Type*} [PseudoMetricSpace X]

theorem iteratedCircleAverage_invariant (A : α → IsometricCircleAction X) (is : List α)
    (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j)) (f : X → ℂ)
    (j : α) (hj : j ∈ is) (t : Circle) (x : X) :
    iteratedCircleAverage A is f ((A j).act t x) = iteratedCircleAverage A is f x := by
  induction is generalizing x with
  | nil => simp at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with hji | hj
    · subst j
      exact (A i).average_invariant _ t x
    · have htcomm : ∀ a ∈ is, ∀ b ∈ is, (A a).Commutes (A b) :=
        fun a ha b hb => hcomm a (by simp [ha]) b (by simp [hb])
      have ht : ∀ y, iteratedCircleAverage A is f ((A j).act t y) =
          (1 : ℂ) * iteratedCircleAverage A is f y := by
        intro y
        simpa using ih htcomm hj y
      simpa only [iteratedCircleAverage, one_mul] using (A i).average_equivariant ((A j).act t) 1
        (fun u y => hcomm i (by simp) j (by simp [hj]) u t y) ht x

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalFamilyCircleProjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

namespace FiniteProbabilityWeights

variable {G : Type*} [Fintype G] (p : FiniteProbabilityWeights G)

theorem norm_tested_difference_le (w f g : G → ℂ) {B rho : ℝ} (hB : 0 ≤ B)
    (hw : ∀ x, ‖w x‖ ≤ B) (hfg : ∀ x, ‖f x - g x‖ ≤ rho) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * g x)‖ ≤ B * rho := by
  apply (p.norm_complexMean_sub_le _ _ (fun _ => B * rho) ?_).trans_eq (p.mean_const _)
  intro x _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul (hw x) (hfg x) (norm_nonneg _) hB

theorem finite_projection_tested_error {J : Type*} [Fintype J]
    (w f projected : G → ℂ) (v : J → G → ℂ) (keep : J → Prop) [DecidablePred keep]
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau) (hw : ∀ x, ‖w x‖ ≤ B)
    (hfull : ∀ x, ‖f x - ∑ j, v j x‖ ≤ rho)
    (hprojected : ∀ x, ‖(∑ j, if keep j then v j x else 0) - projected x‖ ≤ rho)
    (hdiscard : ∀ j, ¬ keep j → ‖p.complexMean (fun x => w x * v j x)‖ ≤ tau) :
    ‖p.complexMean (fun x => w x * f x) - p.complexMean (fun x => w x * projected x)‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  have hfirst := p.norm_tested_difference_le w f (fun x => ∑ j, v j x) hB hw hfull
  have hlast := p.norm_tested_difference_le w
    (fun x => ∑ j, if keep j then v j x else 0) projected hB hw hprojected
  have hid : p.complexMean (fun x => w x * ∑ j, v j x) -
      p.complexMean (fun x => w x * ∑ j, if keep j then v j x else 0) =
      ∑ j, if keep j then 0 else p.complexMean (fun x => w x * v j x) := by
    rw [← p.complexMean_sub]
    calc
      _ = ∑ x, ∑ j, if keep j then 0 else (p.weight x : ℂ) * (w x * v j x) := by
        apply Finset.sum_congr rfl
        intro x _
        dsimp only
        rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj]
      _ = ∑ j, ∑ x, if keep j then 0 else (p.weight x : ℂ) * (w x * v j x) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : keep j <;> simp [hj, complexMean]
  have hmiddle : ‖p.complexMean (fun x => w x * ∑ j, v j x) -
      p.complexMean (fun x => w x * ∑ j, if keep j then v j x else 0)‖ ≤ Fintype.card J * tau := by
    rw [hid]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : J, tau := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : keep j
        · simpa only [hj, ite_true, norm_zero] using htau
        · simpa only [hj, ite_false] using hdiscard j hj
      _ = _ := by simp
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * f x)) (p.complexMean (fun x => w x * ∑ j, v j x))
    (p.complexMean (fun x => w x * projected x))
  have htriangle' := norm_sub_le_norm_sub_add_norm_sub
    (p.complexMean (fun x => w x * ∑ j, v j x))
    (p.complexMean (fun x => w x * ∑ j, if keep j then v j x else 0))
    (p.complexMean (fun x => w x * projected x))
  linarith

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

theorem iteratedCircleAverage_family_tested_weighted_error
    {X Y α G J : Type*} [PseudoMetricSpace Y] [Fintype G] [Fintype J]
    (p : FiniteProbabilityWeights G)
    (A : α → IsometricCircleAction Y) (is : List α) (f : X → Y → ℂ)
    (v : J → X → Y → ℂ) (n : J → α → ℤ)
    (physical : G → X) (path : G → Y) (weight : G → ℂ)
    (Lf : X → ℝ≥0) (Lv : J → X → ℝ≥0)
    (hf : ∀ x, LipschitzWith (Lf x) (f x))
    (hv : ∀ j x, LipschitzWith (Lv j x) (v j x))
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ g, ‖weight g‖ ≤ B)
    (happrox : ∀ x y, ‖f x y - ∑ j, v j x y‖ ≤ rho)
    (heigen : ∀ j i, i ∈ is → ∀ t x y,
      v j x ((A i).act t y) = character (n j i • t) * v j x y)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖p.complexMean (fun g => weight g * v j (physical g) (path g))‖ ≤ tau) :
    ‖p.complexMean (fun g => weight g * f (physical g) (path g)) -
      p.complexMean (fun g =>
        weight g * iteratedCircleAverage A is (f (physical g)) (path g))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  classical
  let keep : J → Prop := fun j => ∀ i ∈ is, n j i = 0
  have hsum (x : X) (y : Y) :
      iteratedCircleAverage A is (fun z => ∑ j, v j x z) y =
        ∑ j, if keep j then v j x y else 0 := by
    rw [iteratedCircleAverage_sum A is Finset.univ
      (fun j => v j x) (fun j => Lv j x) (fun j _ => hv j x)]
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedCircleAverage_eigenfunction A is (n j) (v j x)
      (fun i hi t y => heigen j i hi t x y)]
    dsimp only [keep]
    split_ifs <;> rfl
  apply p.finite_projection_tested_error weight
    (fun g => f (physical g) (path g))
    (fun g => iteratedCircleAverage A is (f (physical g)) (path g))
    (fun j g => v j (physical g) (path g)) keep hB htau hweight
    (fun g => happrox (physical g) (path g)) _ hdiscard
  intro g
  rw [← hsum, norm_sub_rev]
  exact iteratedCircleAverage_sub_norm_le A is (hf (physical g))
    (lipschitz_finite_complex_sum (fun j => v j (physical g))
      (fun j => Lv j (physical g)) (fun j => hv j (physical g)))
    (happrox (physical g)) (path g)

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeNilpotentSourceBounds
namespace OAI

section

namespace Erdos3

variable (X : Type*) (s : ℕ)

noncomputable def freeLieBoundedCoordinates : FreeLieAlgebra ℚ X →ₗ[ℚ] (BoundedFreeWord X s → ℚ) where
  toFun p w := (freeLieWordExpansion p).coeff w.val
  map_add' p q := by ext w; simp
  map_smul' c p := by ext w; simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realifyFunctional_eq_rid (η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional η x = TensorProduct.rid ℚ ℝ (η.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r v =>
    simp only [realifyFunctional_tmul, LinearMap.baseChange_tmul, TensorProduct.rid_tmul,
      Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_realified_frequency_kernel_iff (η : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker η).baseChange ℝ ↔ realifyFunctional η x = 0 := by
  rw [realification_ker, LinearMap.mem_ker, realifyFunctional_eq_rid]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply (TensorProduct.rid ℚ ℝ).injective
    simpa only [map_zero] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {U : Type*} {N : U → ℕ} {q : ℕ}

theorem integerPoint_injective (A : ResidueBoxSlice N q) (hq : 0 < q) :
    Function.Injective A.integerPoint := by
  intro j k h
  have hi := congrArg (commonStrideIndex (fun i => (A.start i : ℤ)) q) h
  rw [A.commonStrideIndex_integerPoint hq, A.commonStrideIndex_integerPoint hq] at hi
  funext i
  apply Fin.ext
  exact_mod_cast congrFun hi i

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BoundedFrequencyKernel
namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

theorem realifyFunctional_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (x : ℝ ⊗[ℚ] V) : realifyFunctional (0 : V →ₗ[ℚ] ℚ) x = 0 := by
  apply (mem_realified_frequency_kernel_iff (0 : V →ₗ[ℚ] ℚ) x).mp
  rw [LinearMap.ker_zero, Submodule.baseChange_top]
  trivial

end Erdos3

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

theorem project_character (A : IsometricCircleAction X) (n : ℤ) (f : X → ℂ)
    (t : Circle) (x : X) :
    A.project n f (A.act t x) = character (n • t) * A.project n f x := by
  let := A.toAddAction
  exact circleFourierComponent_vadd n f t x

end Erdos3.CircleFourier.IsometricCircleAction

end

section

namespace Erdos3.CircleFourier

open scoped NNReal

variable {X α : Type*} [PseudoMetricSpace X]

theorem iteratedExactProjection_character (A : α → IsometricCircleAction X) (n : α → ℤ)
    (is : List α) (hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j)) (f : X → ℂ)
    (j : α) (hj : j ∈ is) (t : Circle) (x : X) :
    iteratedExactProjection A n is f ((A j).act t x) =
      character (n j • t) * iteratedExactProjection A n is f x := by
  induction is generalizing x with
  | nil => simp only [List.not_mem_nil] at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with rfl | hj
    · exact (A j).project_character (n j) _ t x
    · apply (A i).project_equivariant (n i) ((A j).act t) (character (n j • t))
      · exact fun u y => hcomm i List.mem_cons_self j (List.mem_cons_of_mem i hj) u t y
      · intro y
        exact ih (fun a ha b hb => hcomm a (List.mem_cons_of_mem i ha) b
          (List.mem_cons_of_mem i hb)) hj y

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped NNReal

theorem exists_prescribed_circle_projection {X α : Type*} [PseudoMetricSpace X] [Fintype α]
    (A : α → IsometricCircleAction X) (n : α → ℤ)
    (hcomm : ∀ i j, (A i).Commutes (A j)) (S : Set X) (f : X → ℂ)
    (hstable : ∀ i t x, x ∈ S → (A i).act t x ∈ S)
    (hchar : ∀ i t x, x ∈ S → f ((A i).act t x) = character (n i • t) * f x)
    {K : ℝ≥0} {B : ℝ} (hf : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ B) :
    ∃ g : X → ℂ, LipschitzWith K g ∧ (∀ x, ‖g x‖ ≤ B) ∧
      (∀ i t x, g ((A i).act t x) = character (n i • t) * g x) ∧
      ∀ x ∈ S, g x = f x := by
  classical
  let is := (Finset.univ : Finset α).toList
  refine ⟨iteratedExactProjection A n is f, iteratedExactProjection_lipschitz A n is hf,
    iteratedExactProjection_norm_le A n is hb, ?_, ?_⟩
  · intro j t x
    exact iteratedExactProjection_character A n is (fun i _ j _ => hcomm i j) f j
      (by simp [is]) t x
  · exact iteratedExactProjection_eq_on A n is S f (fun i _ => hstable i) (fun i _ => hchar i)

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteWeightedScorePerturbation
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

variable {J : Type*} [Fintype J] (p : FiniteProbabilityWeights J)

theorem norm_complexMean_weighted_sub_le (c f g : J → ℂ) {B ε : ℝ}
    (hB : 0 ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hfg : ∀ j, ‖f j - g j‖ ≤ ε) :
    ‖p.complexMean (fun j => c j * f j) - p.complexMean (fun j => c j * g j)‖ ≤
      B * ε := by
  apply (p.norm_complexMean_sub_le _ _ (fun _ => B * ε) ?_).trans_eq
    (p.mean_const (B * ε))
  intro j _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul (hc j) (hfg j) (norm_nonneg _) hB

theorem norm_complexMean_weighted_lower_of_perturbation (c f g : J → ℂ) {B ε δ : ℝ}
    (hB : 0 ≤ B) (hc : ∀ j, ‖c j‖ ≤ B) (hfg : ∀ j, ‖f j - g j‖ ≤ ε)
    (hscore : δ ≤ ‖p.complexMean (fun j => c j * g j)‖) :
    δ - B * ε ≤ ‖p.complexMean (fun j => c j * f j)‖ := by
  have he := p.norm_complexMean_weighted_sub_le c f g hB hc hfg
  have ht := norm_le_norm_sub_add (p.complexMean (fun j => c j * g j))
    (p.complexMean (fun j => c j * f j))
  rw [norm_sub_rev] at ht
  linarith

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

def allocatedGridAxis (L : ℕ) : LayerSamplerAxis I n → Prop
  | ⟨_, .inl _⟩ => False
  | ⟨j, .inr i⟩ => basisAxisScale (basis j) i ≤ L^(layerTailDegree m+1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

theorem physicalCube_pivot_control {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)).det ≠ 0 ∧
      ‖(matrixSupCLM (normalizedIntegerPivot
        ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s))
        (fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i))
        (physicalSpatialOutputScale α A R L))).inverse‖ ≤
        (Fintype.card (Unit ⊕ α) : ℝ) * (Fintype.card (Unit ⊕ α)).factorial / κ := by
  let M := (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)
  let S := fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i)
  let P := physicalSpatialOutputScale α A R L
  have hS : ∀ i, 0 < S i := fun i => physicalSpatialInputScale_pos K hA hR _
  have hP : ∀ i, 0 < P i := physicalSpatialOutputScale_pos α hA hR hL
  have he : normalizedIntegerPivot M S P =
      rootDifferenceMatrix (fun i => (root (s i) : ℝ) * R / A)
        (Matrix.of (fun i j => (D i (s j) : ℝ) / L)) :=
    physicalCube_normalized_pivot root D s hA.ne' hR.ne' hL.ne'
  have hd : κ ≤ |(normalizedIntegerPivot M S P).det| := by
    rw [he, rootDifferenceMatrix_det (fun i => (root (s i) : ℝ) * R / A)
      (Matrix.of (fun i j => (D i (s j) : ℝ) / L))]
    exact hminor
  have hb : ∀ i j, |normalizedIntegerPivot M S P i j| ≤ 1 := by
    intro i j
    have h := physicalCube_normalized_entry_bound root D hA hR hL hr hD i (physicalCubePivotIndex s j)
    simpa only [M, S, P, normalizedIntegerPivot_entry, normalizedIntegerColumns_entry_div,
      Matrix.submatrix_apply, id_eq] using h
  have hn : M.det ≠ 0 := by
    intro hz
    have hdet := normalizedIntegerPivot_abs_det M S P hS hP
    rw [hz, Int.natAbs_zero, Nat.cast_zero, zero_mul, zero_div] at hdet
    rw [hdet] at hd
    exact (not_le_of_gt hκ) hd
  refine ⟨hn, ?_⟩
  have h := (matrixSupCLM_inverse_norm_le (normalizedIntegerPivot M S P) zero_le_one hb hκ hd).2
  simpa only [one_pow, mul_one, mul_div_assoc] using h

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [∀ j, Fintype (E j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

noncomputable def mixedCoveredJetChart : MixedCoveredJetSource I O E n d → EuclideanJetLayers U O :=
  fun z => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d z)

def mixedCoveredJetRegion (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    Set (MixedCoveredJetSource I O E n d) :=
  mixedCoveredJetCoordinates U o d ⁻¹' coveredJetSourceRegion U b d Ω

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLieDegreeLengthSpan
namespace OAI

section

namespace Erdos3

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

def weightedLieDegreeLengthSpan (v : I → L) (w : I → ℕ) (d k : ℕ) : Submodule ℚ L :=
  Submodule.span ℚ {x | ∃ a : FreeMagma I, d ≤ lieTreeWeight w a ∧ k ≤ a.length ∧ lieTreeEval v a = x}

theorem weightedLieDegreeLengthSpan_antitone (v : I → L) (w : I → ℕ)
    {d e k l : ℕ} (hde : d ≤ e) (hkl : k ≤ l) :
    weightedLieDegreeLengthSpan v w e l ≤ weightedLieDegreeLengthSpan v w d k := by
  apply Submodule.span_mono
  rintro x ⟨a, ha, hk, rfl⟩
  exact ⟨a, hde.trans ha, hkl.trans hk, rfl⟩

theorem weightedLieDegreeLengthSpan_lie_mem (v : I → L) (w : I → ℕ)
    {d e k l : ℕ} {x y : L}
    (hx : x ∈ weightedLieDegreeLengthSpan v w d k)
    (hy : y ∈ weightedLieDegreeLengthSpan v w e l) :
    ⁅x, y⁆ ∈ weightedLieDegreeLengthSpan v w (d + e) (k + l) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨a, ha, hk, rfl⟩ := hx
    obtain ⟨b, hb, hl, rfl⟩ := hy
    exact Submodule.subset_span ⟨a * b, Nat.add_le_add ha hb, Nat.add_le_add hk hl, rfl⟩
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem weightedLieUpperSpan_map_le_degreeLengthSpan (φ : L →ₗ⁅ℚ⁆ M)
    (v : I → L) (w : I → ℕ) (d : ℕ) :
    (weightedLieUpperSpan v w d).map φ.toLinearMap ≤
      weightedLieDegreeLengthSpan (fun i => φ (v i)) w d 1 := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  change φ (lieTreeEval v a) ∈ weightedLieDegreeLengthSpan (fun i => φ (v i)) w d 1
  rw [map_lieTreeEval]
  exact Submodule.subset_span ⟨a, ha, a.length_pos, rfl⟩

theorem FilteredLieTree.map_eval_mem_degreeLengthSpan {s : ℕ}
    {F : NilpotentLieFiltration L s} (φ : L →ₗ⁅ℚ⁆ M) (v : I → M) (w : I → ℕ)
    (hspan : ∀ d, 0 < d → ∀ x ∈ F.layer d, φ x ∈ weightedLieDegreeLengthSpan v w d 1)
    {d k : ℕ} (a : FilteredLieTree F d k) :
    φ a.eval ∈ weightedLieDegreeLengthSpan v w d k := by
  induction a with
  | leaf hd x hx => exact hspan _ hd x hx
  | bracket a b ha hb =>
    rw [FilteredLieTree.eval_bracket, φ.map_lie]
    exact weightedLieDegreeLengthSpan_lie_mem v w ha hb

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

def mixedDifferencePoint {d N : ℕ} (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
    Fin (d + 3) → ℤ :=
  Fin.cons ((t.1 0).val : ℤ) (Fin.cons n (fun j => ((mixedDifferenceShifts t j).val : ℤ)))

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

theorem fullCubeSignal_profile {d N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
    fullCubeSignal (fun z : ℤ => f (z : ZMod N)) (mixedDifferencePoint t n) =
      cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) := by
  have htuple : (fun j => ((mixedDifferencePoint t n ((1 : Fin (d + 3)).succAbove j) : ℤ) : ZMod N)) =
      Fin.cons (t.1 0) (mixedDifferenceShifts t) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [mixedDifferencePoint]
    · simp [Fin.one_succAbove_succ, mixedDifferencePoint]
  have hbase : mixedDifferencePoint t n 1 = n := rfl
  have hlist : List.ofFn t.1 = t.1 0 :: List.ofFn (Fin.tail t.1) := by
    rw [List.ofFn_succ]
    rfl
  unfold fullCubeSignal
  have hmap := cubeProduct_comp_addHom (Int.castAddHom (ZMod N)) f
    (List.ofFn (fun j => mixedDifferencePoint t n ((1 : Fin (d + 3)).succAbove j)))
    (mixedDifferencePoint t n 1)
  simp only [Int.coe_castAddHom] at hmap
  rw [hmap, List.map_ofFn]
  change cubeProduct f
    (List.ofFn (fun j => ((mixedDifferencePoint t n ((1 : Fin (d + 3)).succAbove j) : ℤ) : ZMod N)))
    ((mixedDifferencePoint t n 1 : ℤ) : ZMod N) = _
  rw [htuple, hbase, List.ofFn_cons, mixedDifferenceShifts, List.ofFn_cons, hlist]
  exact cubeProduct_swap_head f (t.1 0) t.2 _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedProfileCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedProfileFromCoordinates_point {d N : ℕ} [NeZero N]
    (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
    mixedProfileFromCoordinates (fun i => (mixedDifferencePoint t n i : ZMod N)) = t := by
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [mixedProfileFromCoordinates, mixedDifferencePoint, mixedDifferenceShifts]
  · change ((t.2.val : ℤ) : ZMod N) = t.2
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem mixedProfileEquiv_point {d N : ℕ}
    (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ZMod N) :
    (fun i => ((mixedProfileEquiv d (ZMod N) (t, n) i).val : ℤ)) =
      mixedDifferencePoint t (n.val : ℤ) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun _ => rfl) k

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

def HasPositiveMixedTargetInterval {J : Type*} {d N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
        (𝔼 t : (Fin (d + 1) → ZMod N) × ZMod N,
          𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)).re

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedInterval_zeroExtension_average {d N : ℕ} [NeZero N]
    (a len : ℕ) (hend : a + len ≤ N) (hshort : 2 * ((len : ℤ) - 1) < N)
    (F : (Fin (d + 3) → ℤ) → ℂ) :
    (𝔼 x : Fin (d + 3) → ZMod N,
      finiteIndicator (cyclicInterval (a : ZMod N) len) (x 1) * F (fun k => ((x k).val : ℤ))) =
      (((len : ℝ) / N : ℝ) : ℂ) *
        (𝔼 t : (Fin (d + 1) → ZMod N) × ZMod N,
          𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F (mixedDifferencePoint t n)) := by
  let I := cyclicInterval (a : ZMod N) len
  have hbase (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ZMod N) :
      mixedProfileEquiv d (ZMod N) (t, n) 1 = n := rfl
  have hrow (t : (Fin (d + 1) → ZMod N) × ZMod N) :
      (𝔼 n : ZMod N, finiteIndicator I (mixedProfileEquiv d (ZMod N) (t, n) 1) *
        F (fun k => ((mixedProfileEquiv d (ZMod N) (t, n) k).val : ℤ))) =
      (((len : ℝ) / N : ℝ) : ℂ) * (𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F (mixedDifferencePoint t n)) := by
    simpa only [hbase, mixedProfileEquiv_point] using
      cyclicInterval_zeroExtension_average a len hend hshort (fun n => F (mixedDifferencePoint t n))
  rw [mixedProfile_average]
  change (𝔼 t, 𝔼 n : ZMod N, finiteIndicator I (mixedProfileEquiv d (ZMod N) (t, n) 1) *
    F (fun k => ((mixedProfileEquiv d (ZMod N) (t, n) k).val : ℤ))) = _
  simp_rw [hrow]
  rw [← Finset.mul_expect]

theorem HasPositiveMixedTargetInterval.cyclic {J : Type*} {d N : ℕ} [NeZero N] {q : ℝ}
    {f : ZMod N → ℂ} {η : J → (Fin (d + 3) → ℤ) → ℂ}
    (H : HasPositiveMixedTargetInterval f η q) : HasCyclicMixedTargetCorrelation f η (2 * q) := by
  classical
  obtain ⟨j, A, hA, hAi, a, len, _, hend, hshort, hvol, hpositive⟩ := H
  let I := cyclicInterval (a : ZMod N) len
  obtain ⟨B, hB, hBi, hprod⟩ := exists_mixed_interval_cutoff_weights I A hA hAi
  let F (x : Fin (d + 3) → ℤ) := star (f ((∑ k, x k : ℤ) : ZMod N)) * star (η j x) * ∏ i, A i x
  let R (x : Fin (d + 3) → ZMod N) :=
    star (f (∑ k, x k)) * star (η j (fun k => ((x k).val : ℤ))) * ∏ i, B i (fun k => ((x k).val : ℤ))
  have hpoint (x : Fin (d + 3) → ZMod N) :
      R x = finiteIndicator I (x 1) * F (fun k => ((x k).val : ℤ)) := by
    dsimp only [R]
    rw [hprod]
    simp only [F, Int.cast_sum, Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  have hmean : (𝔼 x, R x).re = (len : ℝ) / N *
      (𝔼 t : (Fin (d + 1) → ZMod N) × ZMod N,
        𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F (mixedDifferencePoint t n)).re := by
    simp_rw [hpoint]
    rw [mixedInterval_zeroExtension_average a len hend hshort F]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  refine ⟨j, (fun i x => B i (fun k => ((x k).val : ℤ))), (fun i x => hB i _), ?_, ?_⟩
  · intro i x y hxy
    exact hBi i _ _ (fun k hk => congrArg (fun z : ZMod N => (z.val : ℤ)) (hxy k hk))
  · change Real.exp (-(2 * q)) ≤ ‖𝔼 x, R x‖
    apply le_trans ?_ (Complex.re_le_norm _)
    rw [hmean]
    calc
      _ = Real.exp (-q) * Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul hvol hpositive (Real.exp_nonneg _) (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFixedScaleJointMarginal
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

theorem narrowTrimmedSpatial_site_width {G J X : Type*}
    [Fintype G] [Fintype J] {W τ ξ : ℝ}
    (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (root : G ⊕ J → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (i : X) :
    physicalSiteWidth root (narrowTrimmedSpatialWidths W τ ξ N) i ≤
      (spatialTrimMargin τ N i : ℝ) := by
  apply le_trans _ (spatialTrimMargin_fits hW hτ.le root hroot N i)
  unfold physicalSiteWidth
  exact add_le_add (narrowTrimmedSpatialWidths_le hW hτ hξ N hN _)
    (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
      (narrowTrimmedSpatialWidths_le hW hτ hξ N hN _) (abs_nonneg _)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModularMultilinearAmbientSublevel
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical BigOperators

variable {I J R : Type*} [CommRing R]

noncomputable def conditionPolynomial (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) : MvPolynomial J R :=
  killCompl hf (polynomialTranslate (fun i => if i ∈ Set.range f then 0 else v i) P)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ObservedSourceEquivalence
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem uniform_mean_equiv {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (e : X ≃ Y) (f : Y → ℝ) :
    (uniform X).mean (fun x => f (e x)) = (uniform Y).mean f := by
  simp only [uniform_mean]
  exact Fintype.expect_equiv e _ f (fun _ => rfl)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparationSliceComposition
namespace OAI

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

@[simp] theorem identity_point (x : ∀ i, Fin (N i)) : (identity N).point x = x := by
  ext i
  simp [identity, point]

noncomputable def integerPolynomial (S : ResidueBoxSlice N q) (i : I) : MvPolynomial I ℤ :=
  MvPolynomial.C (S.start i : ℤ) + MvPolynomial.C (q : ℤ) * MvPolynomial.X i

@[simp] theorem integerPolynomial_eval (S : ResidueBoxSlice N q)
    (x : ∀ i, Fin (S.length i)) (i : I) :
    MvPolynomial.aeval (R := ℤ) (fun i => ((x i).val : ℤ)) (S.integerPolynomial i) =
      ((S.point x i).val : ℤ) := by
  simp [integerPolynomial, point, Nat.cast_add, Nat.cast_mul]

noncomputable def reindexInteger (S : ResidueBoxSlice N q) (P : MvPolynomial I ℤ) : MvPolynomial I ℤ :=
  MvPolynomial.aeval (R := ℤ) S.integerPolynomial P

@[simp] theorem reindexInteger_eval (S : ResidueBoxSlice N q) (P : MvPolynomial I ℤ)
    (x : ∀ i, Fin (S.length i)) :
    MvPolynomial.eval (fun i => ((x i).val : ℤ)) (S.reindexInteger P) =
      MvPolynomial.eval (fun i => ((S.point x i).val : ℤ)) P := by
  change MvPolynomial.aeval (R := ℤ) (fun i => ((x i).val : ℤ))
    (MvPolynomial.aeval (R := ℤ) S.integerPolynomial P) = _
  rw [MvPolynomial.comp_aeval_apply]
  simp only [integerPolynomial_eval, MvPolynomial.aeval_eq_eval]

end ResidueBoxSlice

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem mean_le_of_le_const {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) :
    mean f ≤ c := by
  simpa using mean_mono (f := f) (g := fun _ => c) hf

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem partitionEnergy_nonneg {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    0 ≤ partitionEnergy P f := by
  exact mean_nonneg fun x => sq_nonneg _

theorem partitionEnergy_le_mean_sq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    partitionEnergy P f ≤ mean fun x => f x ^ 2 := by
  calc
    partitionEnergy P f ≤
        mean (conditionalMean P fun x => f x ^ 2) :=
      mean_mono fun x => conditionalMean_sq_le P f x
    _ = mean (fun x => f x ^ 2) :=
      mean_conditionalMean P fun x => f x ^ 2

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem partitionEnergy_mono
    (P Q : FacePartition Ω) (hPQ : P ≤ Q)
    (f : Ω → ℝ) :
    partitionEnergy Q f ≤ partitionEnergy P f := by
  rw [partitionEnergy_pythagorean P Q hPQ f]
  exact le_add_of_nonneg_right
    (mean_nonneg fun x => sq_nonneg _)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def ResidueSliceUpperComparison {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h g : (σ → ℤ) → ℂ) (parent : σ → ℤ) (H : σ → ℕ) (P level ε : ℝ) : Prop :=
  ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u : σ → ℤ), 0 < M →
    PhysicalSubbox parent H lo N → ResidueSliceLogCostLE H lo N M u P →
    (physicalResidueMean h lo N M u).re ≤ level * (physicalResidueMean g lo N M u).re + ε

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

namespace VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {E : Fin m → Type*} {N : ℕ}

noncomputable def modularDeckPolynomial (r : CoefficientDeckResidues (K := K) E N)
    (j : Fin m) (i : E j) : MvPolynomial K (ZMod N) :=
  modularBoundedCoefficientPolynomial (j.val + 1) (fun e => r j e i)

end VectorPolynomial

end Erdos3

end

end OAI
end


