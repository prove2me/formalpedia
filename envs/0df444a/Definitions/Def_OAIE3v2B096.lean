-- Prove2me | Definitions.Def_OAIE3v2B096
-- name    : OAIE3v2B096
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:24:35.105817+00:00
-- url     : https://prove2.me/theorems/23f40c67-64cf-466f-930a-c53e1410e94d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 98 of 311
-- statement:
--   Definitions bundle 98 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069`, `OAIE3v2B070`, `OAIE3v2B071`, `OAIE3v2B073`, `OAIE3v2B074`, `OAIE3v2B075`, `OAIE3v2B078`, `OAIE3v2B079`, `OAIE3v2B080` of this split.
--
--   Modules: `Dynamics/LieSubalgebraRepresentativeBudget.lean`, `Dynamics/RationalConstraintCountBudget.lean`, `Dynamics/RealProjectedPotentialGroupIdentity.lean`, `Dynamics/RestrictedGradePathMembership.lean`, `Dynamics/ScalarCubeProductRiemannBudget.lean`, `Estimates/AllocatedLongMixedCoefficientBound.lean`, `Estimates/AllocatedNormalizedCoefficientBounds.lean`, `Estimates/ControlledLinearSubspaceLift.lean`, `Estimates/JointRationalSpaceGenerators.lean`, `Estimates/LinearRestrictionDenominatorSize.lean`, `Estimates/MixedRealPoint.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Estimates/RealifiedReconstruction.lean`, `Estimates/ScalarCubeDomain.lean`, `Estimates/VectorAlgebraicMajorDecomposition.lean`, `Estimates/WeightedAxisScaling.lean`, `Estimates/WeightedTranslationShearExponential.lean`, `Fourier/MajorPhaseLowFourierExtraction.lean`, `Fourier/NormalizedTwistLocalizedFourierSelection.lean`, `Geometry/AllocatedArraySupport.lean`, `Geometry/CoordinateFiberPatch.lean`, `Lattices/AlgebraicMajorIntegerRestoration.lean`, `Lattices/AlgebraicMajorWeightedAffineTopPullback.lean`, `Lattices/ResidueSliceNormalizedCell.lean`, `Lattices/SpatialAffineFullMass.lean`, `Lattices/StandardLatticeCoordinates.lean`, `Linear/RationalClearedMatrixReal.lean`, `Linear/RealCoordinateImageSpan.lean`, `Nilpotent/RealFunctionalBCH.lean`, `Polynomial/CRTPolynomialChargeBound.lean`, `Polynomial/CoefficientPolynomialLift.lean`, `Polynomial/FrozenPolynomialAffineRange.lean`, `Polynomial/MajorTranslationPolynomialSymbolDegree.lean`, `Polynomial/MajorWeightedDegreeTools.lean`, `Polynomial/OrdinaryPolynomialPhaseAffineInverse.lean`, `Polynomial/PolynomialCoefficientGridDenominator.lean`, `Polynomial/PolynomialCoefficientNormalization.lean`, `Polynomial/PolynomialIntegerInputs.lean`, `Polynomial/PolynomialPatchShearOrbitConverse.lean`, `Polynomial/PolynomialPatchTaggedBufferedScore.lean`, `Polynomial/PolynomialSymbolicShearWeightedDegree.lean`, `Polynomial/RealPolynomialEvaluationMass.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Probability/AllocatedMixedLiftNormalizedMass.lean`, `Probability/ScalarCubeDomainDensity.lean`, `Sampling/ScalarFunctionalCoefficientGrid.lean`.
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
import Definitions.Def_OAIE3v2B073
import Definitions.Def_OAIE3v2B074
import Definitions.Def_OAIE3v2B075
import Definitions.Def_OAIE3v2B078
import Definitions.Def_OAIE3v2B079
import Definitions.Def_OAIE3v2B080

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalClearedMatrixReal
namespace OAI

section

namespace Erdos3

open scoped Classical

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem matrixDenominator_mul_entry_real (S : Matrix ι κ ℚ) (i : ι) (j : κ) :
    (matrixDenominator S : ℝ) * (S i j : ℝ) = (clearedMatrix S i j : ℝ) := by
  classical
  have h : (clearedMatrix S i j : ℚ) = (matrixDenominator S : ℚ) * S i j :=
    congrFun (congrFun (clearedMatrix_cast S) i) j
  exact_mod_cast h.symm

theorem matrixDenominator_mul_entry_real_integral (S : Matrix ι κ ℚ) (i : ι) (j : κ) :
    ∃ z : ℤ, (matrixDenominator S : ℝ) * (S i j : ℝ) = (z : ℝ) :=
  ⟨clearedMatrix S i j, matrixDenominator_mul_entry_real S i j⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_comparable_residueBoxSlice {I : Type*} [Fintype I] [DecidableEq I]
    (N H : I → ℕ) {q : ℕ} (hq : 0 < q) (hH : ∀ i, 0 < H i)
    (hfit : ∀ i, q * H i ≤ N i) (f : (∀ i, Fin (N i)) → ℝ) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, H i ≤ A.length i ∧ A.length i < 2 * H i) ∧
      (𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j) := by
  classical
  let P := fun i => FiniteProgressionPartition.comparableResidues (N i) q (H i) hq (hH i) (hfit i)
  let : ∀ i, NeZero (N i) := fun i => ⟨ne_of_gt ((Nat.mul_pos hq (hH i)).trans_le (hfit i))⟩
  obtain ⟨k, _, hk⟩ := exists_partition_cell_average (BoxProgressionPartition.cell P) f
  let A : ResidueBoxSlice N q := {
    start := fun i => (P i).start (k i)
    length := fun i => (P i).length (k i)
    inside := fun i j hj => by
      have hp := (P i).point_lt (k i) hj
      rwa [FiniteProgressionPartition.comparableResidues_step] at hp }
  refine ⟨A, ?_, ?_⟩
  · intro i
    exact FiniteProgressionPartition.comparableResidues_length (N i) q (H i) hq (hH i) (hfit i) (k i)
  · rw [BoxProgressionPartition.expect_cell] at hk
    convert hk using 1
    apply Finset.expect_congr rfl
    intro j _
    congr 1
    ext i
    simp only [ResidueBoxSlice.point, BoxProgressionPartition.point_val,
      FiniteProgressionPartition.comparableResidues_step, A, P]

theorem exists_narrow_residueBoxSlice {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) {q : ℕ} (hq : 0 < q) {ρ : ℝ} (_hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hlarge : ∀ i, 4 * (q : ℝ) ≤ ρ * N i) (f : (∀ i, Fin (N i)) → ℝ) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i ∧
        (q : ℝ) * A.length i ≤ ρ * N i) ∧
      (𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j) := by
  let H : I → ℕ := fun i => ⌊ρ * N i / (2 * q)⌋₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htwoq : (0 : ℝ) < 2 * q := by positivity
  have harg (i : I) : 2 ≤ ρ * N i / (2 * q) :=
    (le_div_iff₀ htwoq).mpr (by nlinarith [hlarge i])
  have hH (i : I) : 0 < H i := Nat.floor_pos.mpr (by linarith [harg i])
  have hupper (i : I) : (H i : ℝ) * (2 * q) ≤ ρ * N i :=
    (le_div_iff₀ htwoq).mp (Nat.floor_le (by linarith [harg i]))
  have hlower (i : I) : ρ * N i ≤ 4 * q * H i := by
    have hn : ρ * N i / (2 * q) < (H i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hh : 1 ≤ (H i : ℝ) := by exact_mod_cast hH i
    have hquot : ρ * N i / (2 * q) ≤ 2 * H i := by linarith
    have hm := (div_le_iff₀ htwoq).mp hquot
    nlinarith
  have hfit (i : I) : q * H i ≤ N i := by
    have hn : ρ * (N i : ℝ) ≤ N i := mul_le_of_le_one_left (Nat.cast_nonneg _) hρ1
    have hm : (q : ℝ) * H i ≤ N i := by
      nlinarith [hupper i, mul_nonneg (Nat.cast_nonneg (α := ℝ) q) (Nat.cast_nonneg (α := ℝ) (H i))]
    exact_mod_cast hm
  obtain ⟨A, hA, hscore⟩ := exists_comparable_residueBoxSlice N H hq hH hfit f
  refine ⟨A, ?_, hscore⟩
  intro i
  have hlow : (H i : ℝ) ≤ A.length i := by exact_mod_cast (hA i).1
  have hhigh : (A.length i : ℝ) < 2 * H i := by exact_mod_cast (hA i).2
  refine ⟨(hH i).trans_le (hA i).1, ?_, ?_⟩
  · exact (hlower i).trans (mul_le_mul_of_nonneg_left hlow (by positivity))
  · have hm := mul_le_mul_of_nonneg_left hhigh.le hqR.le
    nlinarith [hupper i]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialIntegerInputs
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem polynomialDenominator_le (P : MvPolynomial σ ℚ) {H : ℕ}
    (hP : RationalPolynomialHeightLE P H) : polynomialDenominator P ≤ H ^ P.support.card := by
  simpa only [polynomialDenominator, Fintype.card_coe] using
    arrayDenominator_le (fun m : P.support => P.coeff m.val) (fun m => (hP m.val).2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem slowPolynomial_oscillation_on_slice {I : Type*} [Fintype I]
    (N : I → ℕ) {q : ℕ} (A : ResidueBoxSlice N q)
    (hA : ∀ i, 0 < A.length i) {ρ M : ℝ} {s : ℕ}
    (hρ : 0 ≤ ρ) (hM : 0 ≤ M) (hwidth : ∀ i, (q : ℝ) * A.length i ≤ ρ * N i)
    (P : MvPolynomial I ℝ) (hdegree : P.totalDegree ≤ s)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (j : ∀ i, Fin (A.length i)) :
    |MvPolynomial.eval (fun i => ((A.point j i).val : ℝ)) P -
        MvPolynomial.eval (fun i => (A.start i : ℝ)) P| ≤
      ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s * M * Fintype.card I * s * ρ := by
  have hstart (i : I) : A.start i < N i := by
    simpa only [Nat.mul_zero, Nat.add_zero] using A.inside i 0 (hA i)
  have hN (i : I) : (0 : ℝ) < N i := by exact_mod_cast (Nat.zero_le _).trans_lt (hstart i)
  have hv (i : I) : |((A.point j i).val : ℝ)| ≤ (N i : ℝ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (A.point j i).isLt.le
  have hw (i : I) : |(A.start i : ℝ)| ≤ (N i : ℝ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (hstart i).le
  have hvw (i : I) : |((A.point j i).val : ℝ) - (A.start i : ℝ)| ≤ (N i : ℝ) * ρ := by
    change |((A.start i + q * (j i).val : ℕ) : ℝ) - (A.start i : ℝ)| ≤ _
    rw [Nat.cast_add, Nat.cast_mul, add_sub_cancel_left, abs_of_nonneg (by positivity)]
    have hj : ((j i).val : ℝ) ≤ A.length i := by exact_mod_cast (j i).isLt.le
    exact (mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg q)).trans (by simpa [mul_comm] using hwidth i)
  have hbound := abs_eval_sub_eval_scaled_box_bound P (fun i => (N i : ℝ))
    (fun i => ((A.point j i).val : ℝ)) (fun i => (A.start i : ℝ)) hN hM hρ hcoeff hv hw hvw hdegree
  have hcard : (P.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le P hdegree
  exact hbound.trans (by gcongr)

theorem exists_slowPolynomial_residueSlice {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) {q : ℕ} (hq : 0 < q) {ρ M : ℝ} {s : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hM : 0 ≤ M)
    (hlarge : ∀ i, 4 * (q : ℝ) ≤ ρ * N i)
    (P : MvPolynomial I ℝ) (hdegree : P.totalDegree ≤ s)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (∀ i, Fin (N i)) → ℝ) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j)) ∧
      ∀ j : (∀ i, Fin (A.length i)),
        |MvPolynomial.eval (fun i => ((A.point j i).val : ℝ)) P -
            MvPolynomial.eval (fun i => (A.start i : ℝ)) P| ≤
          ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s * M * Fintype.card I * s * ρ := by
  obtain ⟨A, hA, hscore⟩ := exists_narrow_residueBoxSlice N hq hρ hρ1 hlarge f
  exact ⟨A, fun i => ⟨(hA i).1, (hA i).2.1⟩, hscore,
    slowPolynomial_oscillation_on_slice N A (fun i => (hA i).1) hρ.le hM
      (fun i => (hA i).2.2) P hdegree hcoeff⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem realPolynomialMass_substitution_le {I J : Type*}
    (p : MvPolynomial I ℝ) (f : I → MvPolynomial J ℝ) {M : ℝ} (hM : 1 ≤ M)
    (hf : ∀ i, realPolynomialMass (f i) ≤ M) {d : ℕ} (hd : p.totalDegree ≤ d) :
    realPolynomialMass (MvPolynomial.eval₂Hom MvPolynomial.C f p) ≤
      realPolynomialMass p * M ^ d := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  calc
    _ ≤ ∑ m ∈ p.support, realPolynomialMass
        (MvPolynomial.C (p.coeff m) * ∏ i ∈ m.support, f i ^ m i) :=
      realPolynomialMass_sum_le _ _
    _ ≤ ∑ m ∈ p.support, |p.coeff m| * M ^ d := by
      apply Finset.sum_le_sum
      intro m hm
      apply (realPolynomialMass_C_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ ≤ ∏ i ∈ m.support, realPolynomialMass (f i ^ m i) := realPolynomialMass_prod_le _ _
        _ ≤ ∏ i ∈ m.support, M ^ m i := by
          apply Finset.prod_le_prod (fun _ _ => realPolynomialMass_nonneg _)
          intro i _
          exact (realPolynomialMass_pow_le _ _).trans
            (pow_le_pow_left₀ (realPolynomialMass_nonneg _) (hf i) _)
        _ = M ^ (m.sum fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
        _ ≤ M ^ d := pow_le_pow_right₀ hM ((MvPolynomial.le_totalDegree hm).trans hd)
    _ = realPolynomialMass p * M ^ d := by rw [← Finset.sum_mul]; rfl

theorem realPolynomialMass_rename_le {I J : Type*} (p : MvPolynomial I ℝ) (f : I → J) :
    realPolynomialMass (MvPolynomial.rename f p) ≤ realPolynomialMass p := by
  have he : (MvPolynomial.rename f : MvPolynomial I ℝ →ₐ[ℝ] MvPolynomial J ℝ).toRingHom =
      MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X (f i)) := by ext <;> simp
  change realPolynomialMass ((MvPolynomial.rename f).toRingHom p) ≤ _
  rw [he]
  have h := realPolynomialMass_substitution_le p (fun i => MvPolynomial.X (f i))
    (M := 1) le_rfl (fun i => (realPolynomialMass_X (f i)).le) le_rfl
  simpa only [one_pow, mul_one] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeDomain
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

theorem scalarCubeFace_contDiff {α : Type*} [Fintype α] [DecidableEq α] (i : Bool × Finset α) :
    ContDiff ℝ ∞ (scalarCubeFace i) := by
  rcases i with ⟨b, t⟩
  cases b with
  | false => exact scalarCubeValue_contDiff t
  | true => exact contDiff_const.sub (scalarCubeValue_contDiff t)

theorem scalarCubeDomain_isOpen (α : Type*) [Fintype α] [DecidableEq α] :
    IsOpen (scalarCubeDomain α) := by
  rw [← positiveInequalityDomain_scalarCubeFace α]
  exact positiveInequalityDomain_isOpen _ (fun i => (scalarCubeFace_contDiff i).continuous)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomain_volume_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < volume (scalarCubeDomain α) :=
  (scalarCubeDomain_isOpen α).measure_pos volume (scalarCubeDomain_nonempty α)

theorem scalarCubeDomain_volumeReal_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < volume.real (scalarCubeDomain α) :=
  ENNReal.toReal_pos (scalarCubeDomain_volume_pos α).ne' (scalarCubeDomain_volume_lt_top α).ne

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialChargeBound
namespace OAI


namespace Erdos3


open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I R : Type*} [Fintype I] [CommRing R] [Fintype R]

omit [Fintype I] [Fintype R] in

theorem totalDegree_sub_top_component_le (n : ℕ) (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ n + 1) :
    (P - homogeneousComponent (n + 1) P).totalDegree ≤ n := by
  apply (mem_weightedSupportLE_one_iff _ n).mp
  intro a ha
  have hcoeff : (P - homogeneousComponent (n + 1) P).coeff a ≠ 0 :=
    Finsupp.mem_support_iff.mp ha
  rw [coeff_sub, coeff_homogeneousComponent] at hcoeff
  have hne : a.degree ≠ n + 1 := by
    intro h
    exact hcoeff (by simp [h])
  have haP : a ∈ P.support := by
    apply mem_support_iff.mpr
    simpa only [if_neg hne, sub_zero] using hcoeff
  have hbound := (mem_weightedSupportLE_one_iff P (n + 1)).mpr hP haP
  change Finsupp.weight (fun _ : I => 1) a ≤ n + 1 at hbound
  change Finsupp.weight (fun _ : I => 1) a ≤ n
  rw [← Finsupp.degree_eq_weight_one] at hbound ⊢
  omega

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem rename_mem_integralRealPolynomialSubring {τ : Type*} (f : σ → τ)
    {P : MvPolynomial σ ℝ} (hP : P ∈ integralRealPolynomialSubring σ) :
    rename f P ∈ integralRealPolynomialSubring τ := by
  obtain ⟨Q, rfl⟩ := hP
  exact ⟨rename f Q, MvPolynomial.map_rename _ _ _⟩

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommRing R]

theorem majorShiftCoordinates_mass_le (e : B → MvPolynomial U ℝ)
    {M : ℝ} (he : ∀ i, realPolynomialMass (e i) ≤ M) (j : B) :
    realPolynomialMass (majorShiftCoordinates e j) ≤ 1 + M := by
  apply (realPolynomialMass_add_le _ _).trans
  exact add_le_add (realPolynomialMass_X _).le
    ((realPolynomialMass_rename_le (e j) Sum.inl).trans (he j))

theorem majorShiftSubstitution_mass_le (e : B → MvPolynomial U ℝ)
    {M : ℝ} (hM : 0 ≤ M) (he : ∀ i, realPolynomialMass (e i) ≤ M)
    (j : U ⊕ B) :
    realPolynomialMass (majorShiftSubstitution e j) ≤ 1 + M := by
  cases j with
  | inl i =>
    change realPolynomialMass (X (Sum.inl i) : MvPolynomial (U ⊕ B) ℝ) ≤ _
    rw [realPolynomialMass_X]
    exact le_add_of_nonneg_right hM
  | inr i => exact majorShiftCoordinates_mass_le e he i

theorem majorSlowPolynomial_mass_le (D0 : MvPolynomial B ℝ)
    (E : MvPolynomial (U ⊕ B) ℝ) (V : MvPolynomial B ℝ)
    (e : B → MvPolynomial U ℝ) {M : ℝ} (hM : 0 ≤ M)
    (he : ∀ i, realPolynomialMass (e i) ≤ M) {d : ℕ}
    (hE : E.totalDegree ≤ d) (hV : V.totalDegree ≤ d) :
    realPolynomialMass (majorSlowPolynomial D0 E V e) ≤
      realPolynomialMass D0 +
        (realPolynomialMass E + realPolynomialMass V) * (1 + M) ^ d := by
  have hE' := realPolynomialMass_substitution_le E (majorShiftSubstitution e)
    (show 1 ≤ 1 + M by linarith) (majorShiftSubstitution_mass_le e hM he) hE
  have hV' := realPolynomialMass_substitution_le V (majorShiftCoordinates e)
    (show 1 ≤ 1 + M by linarith) (majorShiftCoordinates_mass_le e he) hV
  unfold majorSlowPolynomial
  exact (realPolynomialMass_sub_le _ _).trans
    (((add_le_add ((realPolynomialMass_add_le _ _).trans
      (add_le_add (realPolynomialMass_rename_le D0 Sum.inr) hE')) hV')).trans
      (by ring_nf; rfl))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorAlgebraicMajorDecomposition
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R T : Type*} [CommRing R] [CommRing T]

theorem algebraic_major_normalized_slow_mass
    (D₀ : MvPolynomial B ℝ) (E : MvPolynomial (U ⊕ B) ℝ)
    (V : MvPolynomial B ℚ) (e : B → MvPolynomial U ℝ)
    {M : ℝ} (hM : 0 ≤ M) (he : ∀ j, realPolynomialMass (e j) ≤ M) {d : ℕ}
    (hE : E.totalDegree ≤ d) (hV : (map (algebraMap ℚ ℝ) V).totalDegree ≤ d) :
    realPolynomialMass (majorSlowPolynomial D₀ E (map (algebraMap ℚ ℝ) V) e) ≤
      realPolynomialMass D₀ +
        (realPolynomialMass E + realPolynomialMass (map (algebraMap ℚ ℝ) V)) * (1 + M) ^ d :=
  majorSlowPolynomial_mass_le D₀ E (map (algebraMap ℚ ℝ) V) e hM he hE hV

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommRing R]

theorem specializeMajorParameters_zero_weightedSupportLE (w : B → ℕ)
    {v : U → ℕ} {d : ℕ} {P : MvPolynomial (U ⊕ B) R}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) d) :
    specializeMajorParameters (RingHom.id R) P (fun _ => 0) ∈
      weightedSupportLE w d := by
  change aeval (Sum.elim (fun _ : U => C (0 : R)) X) P ∈ weightedSupportLE w d
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro i
  cases i with
  | inl i => exact weightedSupportLE_C w (v i) 0
  | inr i => exact weightedSupportLE_X w i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorWeightedDegreeTools
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem coordinateShearHom_mass (i : τ) (f : σ → τ) (Q : MvPolynomial σ ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hQ : realPolynomialMass (rename f Q) ≤ M)
    {P : MvPolynomial τ ℝ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    realPolynomialMass (coordinateShearHom i f Q P) ≤ realPolynomialMass P * (1 + M) ^ n := by
  classical
  apply realPolynomialMass_substitution_le P _ (by linarith) _ hP
  intro j
  by_cases hj : j = i
  · subst j
    rw [Function.update_self]
    exact (realPolynomialMass_add_le _ _).trans (by simpa only [realPolynomialMass_X] using add_le_add (le_refl (1 : ℝ)) hQ)
  · rw [Function.update_of_ne hj, realPolynomialMass_X]
    linarith

theorem coordinateShearEquiv_inverse_mass (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hQ : realPolynomialMass (rename f Q) ≤ M)
    {P : MvPolynomial τ ℝ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    realPolynomialMass ((coordinateShearEquiv i f hf Q).symm P) ≤
      realPolynomialMass P * (1 + M) ^ n := by
  exact coordinateShearHom_mass i f (-Q) hM (by simpa only [map_neg, realPolynomialMass_neg] using hQ) hP

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem weightedSupportLE_of_map_injective (φ : R →+* S)
    (hφ : Function.Injective φ) {w : σ → ℕ} {d : ℕ}
    {P : MvPolynomial σ R} (hP : map φ P ∈ weightedSupportLE w d) :
    P ∈ weightedSupportLE w d := by
  intro α hα
  apply hP
  change α ∈ (map φ P).support
  change α ∈ P.support at hα
  rwa [support_map_of_injective P hφ]

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem roundedIntegerPolynomial_real_degree (P : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (hP : P ∈ weightedSupportLE w d) :
    MvPolynomial.map (Int.castRingHom ℝ) (roundedIntegerPolynomial P) ∈ weightedSupportLE w d := by
  intro a ha
  apply hP
  change a ∈ (MvPolynomial.map (Int.castRingHom ℝ) (roundedIntegerPolynomial P)).support at ha
  change a ∈ P.support
  rw [MvPolynomial.mem_support_iff] at ha ⊢
  intro hp
  apply ha
  change (round (P.coeff a) : ℝ) = 0
  rw [hp, round_zero, Int.cast_zero]

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} {d : ℕ}

noncomputable def polynomialSlotShear [CommRing R] (t : σ → R) (i : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin i.val) R) : (Fin d → R) ≃ (Fin d → R) :=
  slotAddShearEquiv i (fun b => MvPolynomial.eval (slotPolynomialInput t b i) Q)
    (fun b c => by rw [slotPolynomialInput_update])

theorem polynomialSlotShear_apply [CommRing R] (t : σ → R) (i : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin i.val) R) (b : Fin d → R) :
    polynomialSlotShear t i Q b =
      Function.update b i (b i + MvPolynomial.eval (slotPolynomialInput t b i) Q) := rfl

theorem polynomialSlotShear_cast (t : σ → ℤ) (i : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin i.val) ℤ) (b : Fin d → ℤ) :
    (fun j => (polynomialSlotShear t i Q b j : ℝ)) =
      polynomialSlotShear (fun a => (t a : ℝ)) i (MvPolynomial.map (Int.castRingHom ℝ) Q)
        (fun j => (b j : ℝ)) := by
  have hi : (fun a => ((slotPolynomialInput t b i a : ℤ) : ℝ)) =
      slotPolynomialInput (fun a => (t a : ℝ)) (fun j => (b j : ℝ)) i := by
    funext a
    cases a <;> rfl
  have heval := MvPolynomial.map_eval (Int.castRingHom ℝ) (slotPolynomialInput t b i) Q
  change ((MvPolynomial.eval (slotPolynomialInput t b i) Q : ℤ) : ℝ) = _ at heval
  simp only [Function.comp_def, Int.coe_castRingHom] at heval
  rw [hi] at heval
  funext j
  rw [polynomialSlotShear_apply, polynomialSlotShear_apply]
  by_cases h : j = i
  · subst j
    simp only [Function.update_self, Int.cast_add]
    rw [heval]
  · simp only [Function.update_of_ne h]

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem finsupp_weight_add_function (v w : σ → ℕ) (a : σ →₀ ℕ) :
    Finsupp.weight (v + w) a = Finsupp.weight v a + Finsupp.weight w a := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.add_apply, smul_add,
    Finset.sum_add_distrib]

theorem weightedSupportLE_of_weight_le {v w : σ → ℕ} (hvw : ∀ i, v i ≤ w i)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    p ∈ weightedSupportLE v d := by
  intro a ha
  change Finsupp.weight v a ≤ d
  apply le_trans _ (hp ha)
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (a i) (hvw i))

theorem weightedTopPart_remainder_lt (w : σ → ℕ)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    p - weightedHomogeneousComponent w d p ∈ weightedSupportLT w d := by
  intro a ha
  change a ∈ (p - weightedHomogeneousComponent w d p).support at ha
  have hc := MvPolynomial.mem_support_iff.mp ha
  rw [MvPolynomial.coeff_sub, coeff_weightedHomogeneousComponent] at hc
  by_cases he : Finsupp.weight w a = d
  · exact (hc (by rw [if_pos he, sub_self])).elim
  · have hpa : p.coeff a ≠ 0 := by simpa only [if_neg he, sub_zero] using hc
    have hle : Finsupp.weight w a ≤ d := hp (MvPolynomial.mem_support_iff.mpr hpa)
    change Finsupp.weight w a < d
    omega

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ}

theorem slotPrefixLift_degree (w : Fin d → ℕ) (k i : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    slotPrefixLift k i R ∈ weightedSupportLE (patchVariableWeight w i) (w k) :=
  weightedSupportLE_aeval _ _ _
    (PolynomialSlots.placementSubstitution_degree id (fun _ => rfl) i k) hR

theorem slotShearSubstitution_degree (w : Fin d → ℕ) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k))
    (i : Fin d) (v : σ ⊕ Fin i.val) :
    slotShearSubstitution k R i v ∈
      weightedSupportLE (patchVariableWeight w i) (patchVariableWeight w i v) := by
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
      change X (Sum.inr j) + (if earlierSlot i j = k then slotPrefixLift k i R else 0) ∈
        weightedSupportLE (patchVariableWeight w i) (w (earlierSlot i j))
      apply (weightedSupportLE _ _).add_mem (weightedSupportLE_X _ (Sum.inr j))
      by_cases h : earlierSlot i j = k
      · rw [if_pos h]
        simpa only [patchVariableWeight, Sum.elim_inr, h] using slotPrefixLift_degree w k i R hR
      · rw [if_neg h]
        exact Submodule.zero_mem _

theorem slotShearSubstitution_eval (k i : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ) (t : σ → ℝ) (b : Fin d → ℝ)
    (v : σ ⊕ Fin i.val) :
    aeval (slotPolynomialInput t b i) (slotShearSubstitution k R i v) =
      slotPolynomialInput t (polynomialSlotShear t k R b) i v := by
  cases v with
  | inl a => simp only [slotShearSubstitution, Sum.elim_inl, aeval_X, slotPolynomialInput]
  | inr j =>
      by_cases h : earlierSlot i j = k
      · have hki : k.val ≤ i.val := by
          have hj : (earlierSlot i j).val < i.val := j.isLt
          rw [h] at hj
          exact hj.le
        change aeval (slotPolynomialInput t b i)
          (X (Sum.inr j) + if earlierSlot i j = k then slotPrefixLift k i R else 0) = _
        rw [if_pos h, map_add, aeval_X, slotPrefixLift_eval k i hki]
        simp only [slotPolynomialInput, Sum.elim_inr, polynomialSlotShear_apply,
          h, Function.update_self, MvPolynomial.aeval_eq_eval]
      · simp only [slotShearSubstitution, Sum.elim_inr, if_neg h, add_zero,
          aeval_X, slotPolynomialInput, polynomialSlotShear_apply, Function.update_of_ne h]

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shear (A : PolynomialSlots σ d w) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    PolynomialSlots σ d w where
  center i := aeval (slotShearSubstitution k R i) (A.center i) -
    if i = k then slotPrefixLift k i R else 0
  degree i := by
    apply (weightedSupportLE _ _).sub_mem
    · exact weightedSupportLE_aeval _ _ _ (slotShearSubstitution_degree w k R hR i)
        (A.degree i)
    · by_cases h : i = k
      · subst i
        rw [if_pos rfl]
        exact slotPrefixLift_degree w k k R hR
      · rw [if_neg h]
        exact Submodule.zero_mem _

theorem shear_center_before (A : PolynomialSlots σ d w) (k i : Fin d)
    (hik : i.val < k.val) (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    (A.shear k R hR).center i = A.center i := by
  have hne : i ≠ k := by intro h; subst i; exact (lt_irrefl _ hik)
  change aeval (slotShearSubstitution k R i) (A.center i) -
    (if i = k then slotPrefixLift k i R else 0) = _
  rw [slotShearSubstitution_before k i hik.le, MvPolynomial.aeval_X_left_apply,
    if_neg hne, sub_zero]

theorem shear_center_self (A : PolynomialSlots σ d w) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k)) :
    (A.shear k R hR).center k = A.center k - R := by
  change aeval (slotShearSubstitution k R k) (A.center k) -
    (if k = k then slotPrefixLift k k R else 0) = _
  rw [slotShearSubstitution_before k k le_rfl, MvPolynomial.aeval_X_left_apply,
    if_pos rfl, slotPrefixLift_self]

theorem shear_center_eval (A : PolynomialSlots σ d w) (k : Fin d)
    (R : MvPolynomial (σ ⊕ Fin k.val) ℝ)
    (hR : R ∈ weightedSupportLE (patchVariableWeight w k) (w k))
    (t : σ → ℝ) (b : Fin d → ℝ) (i : Fin d) :
    ((A.shear k R hR).slots t).center b i =
      (A.slots t).center (polynomialSlotShear t k R b) i -
        if i = k then MvPolynomial.eval (slotPolynomialInput t b k) R else 0 := by
  change aeval (slotPolynomialInput t b i)
      (aeval (slotShearSubstitution k R i) (A.center i) -
        if i = k then slotPrefixLift k i R else 0) = _
  rw [map_sub, MvPolynomial.comp_aeval_apply]
  have he : (fun v => aeval (slotPolynomialInput t b i) (slotShearSubstitution k R i v)) =
      slotPolynomialInput t (polynomialSlotShear t k R b) i :=
    funext (slotShearSubstitution_eval k i R t b)
  rw [he]
  congr 1
  by_cases h : i = k
  · subst i
    rw [if_pos rfl, if_pos rfl, slotPrefixLift_self, MvPolynomial.aeval_eq_eval]
  · rw [if_neg h, if_neg h, map_zero]

theorem shear_integer_residual (A : PolynomialSlots σ d w) (k : Fin d)
    (Q : MvPolynomial (σ ⊕ Fin k.val) ℤ)
    (hQ : MvPolynomial.map (Int.castRingHom ℝ) Q ∈
      weightedSupportLE (patchVariableWeight w k) (w k))
    (t : σ → ℤ) (b : Fin d → ℤ) :
    ((A.shear k (MvPolynomial.map (Int.castRingHom ℝ) Q) hQ).slots
      (fun a => (t a : ℝ))).residual b =
    (A.slots (fun a => (t a : ℝ))).residual (polynomialSlotShear t k Q b) := by
  funext i
  change (b i : ℝ) - _ = (polynomialSlotShear t k Q b i : ℝ) - _
  rw [shear_center_eval]
  have he := polynomialSlotShear_cast t k Q b
  rw [← he]
  have hi := congrFun he i
  rw [polynomialSlotShear_apply (R := ℝ)] at hi
  by_cases h : i = k
  · subst i
    simp only [Function.update_self, ite_true] at hi ⊢
    linarith
  · simp only [Function.update_of_ne h, if_neg h, sub_zero] at hi ⊢
    rw [hi]

end PolynomialSlots

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem exists_coefficient_normalized_prefix (A : PolynomialSlots σ d w) (n : ℕ) :
    n ≤ d → ∃ B : PolynomialSlots σ d w,
      (∀ i : Fin d, i.val < n → ∀ a, |(B.center i).coeff a| ≤ 1 / 2) ∧
      ∀ t : σ → ℤ, ∃ e : (Fin d → ℤ) ≃ (Fin d → ℤ),
        ∀ b, (B.slots (fun a => (t a : ℝ))).residual b =
          (A.slots (fun a => (t a : ℝ))).residual (e b) := by
  induction n with
  | zero =>
      intro _
      refine ⟨A, ?_, ?_⟩
      · intro i hi
        exact (Nat.not_lt_zero _ hi).elim
      · intro t
        exact ⟨Equiv.refl _, fun _ => rfl⟩
  | succ n ih =>
      intro hn
      obtain ⟨B, hB, hBA⟩ := ih (Nat.le_of_succ_le hn)
      let k : Fin d := ⟨n, Nat.lt_of_succ_le hn⟩
      let Q := roundedIntegerPolynomial (B.center k)
      have hQ : MvPolynomial.map (Int.castRingHom ℝ) Q ∈
          weightedSupportLE (patchVariableWeight w k) (w k) :=
        roundedIntegerPolynomial_real_degree (B.center k) _ _ (B.degree k)
      refine ⟨B.shear k (MvPolynomial.map (Int.castRingHom ℝ) Q) hQ, ?_, ?_⟩
      · intro i hi a
        by_cases hik : i = k
        · subst i
          rw [shear_center_self]
          exact roundedIntegerPolynomial_remainder_bound (B.center k) a
        · have hine : i.val ≠ n := by
            intro he
            apply hik
            exact Fin.ext he
          have hil : i.val < n := by omega
          rw [shear_center_before B k i hil]
          exact hB i hil a
      · intro t
        obtain ⟨e, he⟩ := hBA t
        refine ⟨(polynomialSlotShear t k Q).trans e, ?_⟩
        intro b
        rw [shear_integer_residual]
        exact he _

theorem exists_coefficient_normalized (A : PolynomialSlots σ d w) :
    ∃ B : PolynomialSlots σ d w,
      (∀ i a, |(B.center i).coeff a| ≤ 1 / 2) ∧
      ∀ t : σ → ℤ, ∃ e : (Fin d → ℤ) ≃ (Fin d → ℤ),
        ∀ b, (B.slots (fun a => (t a : ℝ))).residual b =
          (A.slots (fun a => (t a : ℝ))).residual (e b) := by
  obtain ⟨B, hB, hBA⟩ := A.exists_coefficient_normalized_prefix d le_rfl
  exact ⟨B, fun i => hB i i.isLt, hBA⟩

end PolynomialSlots

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R]

theorem weightedSupportLE_moduleFinite [Finite σ] (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (n : ℕ) : Module.Finite R (weightedSupportLE (R := R) w n) := by
  let : Fintype {a : σ →₀ ℕ | Finsupp.weight w a ≤ n} :=
    (Finsupp.finite_of_nat_weight_le w (fun i => (hw i).ne') n).fintype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport R
    {a : σ →₀ ℕ | Finsupp.weight w a ≤ n})

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {U X : Type*}

theorem residueAffinePolynomial_eval (q : ℕ) (r v : U → ℤ)
    (P : MvPolynomial U ℝ) :
    eval (fun i => (v i : ℝ)) (residueAffinePolynomial q r P) =
      eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [residueAffinePolynomial]
  | add P Q hP hQ => simpa only [residueAffinePolynomial, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [residueAffinePolynomial, map_mul, eval₂Hom_X', map_add, eval_C,
      eval_X, Int.cast_add, Int.cast_mul, Int.cast_natCast] at *
    rw [hP]

theorem residueAffinePolynomial_totalDegree_le (q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) (n : ℕ) (hP : P.totalDegree ≤ n) :
    (residueAffinePolynomial q r P).totalDegree ≤ n := by
  have hf (i : U) : (C (r i : ℝ) + C (q : ℝ) * MvPolynomial.X i).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp only [totalDegree_C]; omega
    · exact (totalDegree_mul _ _).trans (by
        simp only [totalDegree_C, totalDegree_X, Nat.zero_add, le_refl])
  simpa only [residueAffinePolynomial, Nat.mul_one] using
    polynomial_substitution_totalDegree_le P _ hf hP

noncomputable def localMajorLowerPhase (n q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) : MvPolynomial U ℝ :=
  residueAffinePolynomial q r (P - homogeneousComponent (n + 1) P)

theorem localMajorLowerPhase_totalDegree_le (n q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1) :
    (localMajorLowerPhase n q r P).totalDegree ≤ n :=
  residueAffinePolynomial_totalDegree_le q r _ n (totalDegree_sub_top_component_le n P hP)

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*}

theorem fractionalCoefficientPolynomial_fourierChar (D : MvPolynomial σ ℝ) (z : σ → ℤ) :
    Real.fourierChar (eval (fun i => (z i : ℝ)) (fractionalCoefficientPolynomial D)) =
      Real.fourierChar (eval (fun i => (z i : ℝ)) D) := by
  have h := congrArg (fun P => Real.fourierChar (eval (fun i => (z i : ℝ)) P))
    (floorIntegerPolynomial_add_fractionalCoefficientPolynomial D)
  have hz : Real.fourierChar ((eval z (floorIntegerPolynomial D) : ℤ) : ℝ) = 1 := by
    apply Subtype.ext
    change (Circle.exp (2 * Real.pi * ((eval z (floorIntegerPolynomial D) : ℤ) : ℝ)) : ℂ) = 1
    rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
    simp
  simpa only [map_add, eval_integer_polynomial_real, Real.fourierChar.map_add_eq_mul,
    hz, one_mul] using h

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedAxisScaling
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*} [Fintype B]

theorem realPolynomialMass_translationDirectionalDerivative
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, realPolynomialMass (b i) ≤ M) :
    realPolynomialMass (translationDirectionalDerivative b P) ≤
      ((Fintype.card B : ℝ) * d * M) * realPolynomialMass P := by
  classical
  rw [translationDirectionalDerivative_apply]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : B, M * ((d : ℝ) * realPolynomialMass P) := by
      apply Finset.sum_le_sum
      intro i _
      exact (realPolynomialMass_mul_le _ _).trans
        (mul_le_mul ((realPolynomialMass_rename_le _ _).trans (hb i))
          (realPolynomialMass_pderiv_degreeOf P (Sum.inr i) (hP i))
          (realPolynomialMass_nonneg _) hM)
    _ = _ := by simp; ring

theorem realPolynomialMass_translationDirectionalDerivative_pow
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, realPolynomialMass (b i) ≤ M) (k : ℕ) :
    realPolynomialMass (((translationDirectionalDerivative b) ^ k) P) ≤
      ((Fintype.card B : ℝ) * d * M) ^ k * realPolynomialMass P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    apply (realPolynomialMass_translationDirectionalDerivative b _ d
      (translationDirectionalDerivative_pow_degreeOf_le b P d hP k) hM hb).trans
    calc
      _ ≤ ((Fintype.card B : ℝ) * d * M) *
          (((Fintype.card B : ℝ) * d * M) ^ k * realPolynomialMass P) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ']; ring

theorem realPolynomialMass_translationDirectionalSeries
    (d : ℕ) (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, realPolynomialMass (b i) ≤ M)
    (hmass : realPolynomialMass P ≤ M) :
    realPolynomialMass (translationDirectionalSeries d b P) ≤
      ((d : ℝ) + 1) * M * (1 + (Fintype.card B : ℝ) * d * M) ^ d := by
  classical
  let A : ℝ := (Fintype.card B : ℝ) * d * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hterm (i : ℕ) (hi : i ∈ Finset.range d) :
      realPolynomialMass (((-1 : ℝ) ^ i / ((i + 1).factorial : ℝ)) •
        ((translationDirectionalDerivative b) ^ i) P) ≤ M * (1 + A) ^ d := by
    rw [realPolynomialMass_smul]
    calc
      _ ≤ 1 * (A ^ i * realPolynomialMass P) :=
        mul_le_mul (translationDirectionalSeries_coefficient_abs_le_one i)
          (realPolynomialMass_translationDirectionalDerivative_pow b P d hP hM hb i)
          (realPolynomialMass_nonneg _) (by norm_num)
      _ ≤ A ^ i * M := by simpa using mul_le_mul_of_nonneg_left hmass (pow_nonneg hA i)
      _ ≤ (1 + A) ^ d * M := by
        apply mul_le_mul_of_nonneg_right _ hM
        exact (pow_le_pow_left₀ hA (by linarith) i).trans
          (pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hi).le)
      _ = _ := mul_comm _ _
  unfold translationDirectionalSeries
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range d, M * (1 + A) ^ d := Finset.sum_le_sum hterm
    _ = (d : ℝ) * (M * (1 + A) ^ d) := by simp
    _ ≤ ((d : ℝ) + 1) * (M * (1 + A) ^ d) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by dsimp [A]; ring

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem weightedHomogeneousComponent_eq_of_sub_lower (w : σ → ℕ)
    {p q : MvPolynomial σ R} {n : ℕ}
    (hpq : p - q ∈ weightedSupportLT w n) (hq : q.IsWeightedHomogeneous w n) :
    weightedHomogeneousComponent w n p = q := by
  have hzero : weightedHomogeneousComponent w n (p - q) = 0 := by
    apply MvPolynomial.ext
    intro a
    rw [coeff_weightedHomogeneousComponent, MvPolynomial.coeff_zero]
    split_ifs with ha
    · by_contra hc
      have hlt := hpq (mem_support_iff.mpr hc)
      change Finsupp.weight w a < n at hlt
      omega
    · rfl
  rw [map_sub, hq.weightedHomogeneousComponent_same, sub_eq_zero] at hzero
  exact hzero

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
variable {σ : Type*} {d : ℕ} (p : σ → ℕ) (w : Fin d → ℕ)

theorem weighted_symbolic_rename_degree {ι κ : Type*} (v : ι → ℕ) (z : κ → ℕ)
    (f : ι → κ) (hf : ∀ i, z (f i) = v i)
    {P : MvPolynomial ι ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE v n) :
    rename f P ∈ weightedSupportLE z n := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval v z _ _ hP
  intro i
  simpa only [Function.comp_apply, hf] using weightedSupportLE_X (R := ℝ) z (f i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

namespace PolynomialTranslationLie

noncomputable def weightedCoordinates (w : σ → ℕ) (d : ℕ) :
    weightedSubalgebra w d →ₗ[ℚ] (σ → ℚ) × weightedSupportLE (R := ℚ) w d where
  toFun x := (x.val.base, ⟨x.val.polynomial, weightedSupportDrop_le x.property.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem weightedCoordinates_injective (w : σ → ℕ) (d : ℕ) :
    Function.Injective (weightedCoordinates w d) := by
  intro x y h
  apply Subtype.ext
  apply PolynomialTranslationLie.ext
  · exact congrArg Prod.fst h
  · exact congrArg (fun z => (z.2 : MvPolynomial σ ℚ)) h

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]

theorem exists_controlled_coordinate_leftInverse
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) :
    ∃ B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ), (∀ x, B (A x) = x) ∧
      ∀ i j, RationalHeightLE (B (Pi.single i 1) j)
        (rationalKernelHeight (Fintype.card σ) H) := by
  let D := LinearMap.toMatrix' A
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section D hH
    (fun i j => hentries j i)
  refine ⟨S.mulVecLin, ?_, ?_⟩
  · intro x
    apply hA
    have hx : D *ᵥ (S *ᵥ (D *ᵥ x)) = D *ᵥ x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS]
    simpa only [D, LinearMap.toMatrix'_mulVec, Matrix.mulVecLin_apply] using hx
  · intro i j
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using hSH j i

theorem exists_controlled_weighted_leftInverse
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hA : Function.Injective A) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) :
    ∃ B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ),
      (∀ x, B (A x) = x) ∧
      (∀ i j, w i ≠ v j → B (Pi.single i 1) j = 0) ∧
      (∀ i j, RationalHeightLE (B (Pi.single i 1) j)
        (rationalKernelHeight (Fintype.card σ) H)) := by
  obtain ⟨B, hBA, hBH⟩ := exists_controlled_coordinate_leftInverse A hA hH hentries
  refine ⟨weightedLinearInverseMask B v w, ?_, ?_, ?_⟩
  · exact weightedLinearInverseMask_apply A B v w hweight hBA
  · exact weightedLinearInverseMask_weighted B v w
  · exact weightedLinearInverseMask_height B v w (fun j i => hBH i j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LieSubalgebraRepresentativeBudget
namespace OAI

section

namespace Erdos3

theorem rational_matrix_entry_budget {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℚ) {p : ℝ} (hp : 0 ≤ p) (a : ℕ)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hS : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ a) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    (∀ i j, |(S i j : ℝ)| ≤ Real.exp ((p + 2) ^ a)) ∧
    0 < matrixDenominator S ∧
    (matrixDenominator S : ℝ) ≤ Real.exp ((p + 2) ^ (a + 2)) ∧
    ∀ i j, ∃ z : ℤ, (matrixDenominator S : ℝ) * (S i j : ℝ) = z := by
  refine ⟨?_, matrixDenominator_pos S, ?_, ?_⟩
  · intro i j
    exact (rational_abs_real_le_numerator (S i j)).trans (hS i j).1
  · apply matrixDenominator_le_exp_power S hp a hι hκ
    intro i j
    exact (hS i j).2
  · exact matrixDenominator_mul_entry_real_integral S

theorem rational_section_entry_budget {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hS : ∀ i j, ((S i j).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 45) ∧
      ((S i j).den : ℝ) ≤ Real.exp ((p + 2) ^ 45)) :
    (∀ i j, |(S i j : ℝ)| ≤ Real.exp ((p + 2) ^ 45)) ∧
    ∃ q : ℕ, q = matrixDenominator S ∧ 0 < q ∧
      (q : ℝ) ≤ Real.exp ((p + 2) ^ 47) ∧
      ∀ i j, ∃ z : ℤ, (q : ℝ) * (S i j : ℝ) = z := by
  obtain ⟨hentry, hpos, hden, hint⟩ := rational_matrix_entry_budget S hp 45 hι hκ hS
  exact ⟨hentry, matrixDenominator S, rfl, hpos, hden, hint⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationPolynomialSymbolDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem polynomialSlotCoefficient_monomial [DecidableEq τ] (α : σ →₀ ℕ) (β γ : τ →₀ ℕ) (c : R) :
    polynomialSlotCoefficient β (monomial (α.sumElim γ) c) =
      if γ = β then monomial α c else 0 := by
  classical
  ext δ
  rw [polynomialSlotCoefficient_coeff]
  by_cases hγ : γ = β
  · subst γ
    simp only [ite_true, coeff_monomial]
    simp only [(sumExponent_injective β).eq_iff]
  · have hne : α.sumElim γ ≠ δ.sumElim β := by
      intro h
      apply hγ
      ext i
      exact congrArg (fun a : σ ⊕ τ →₀ ℕ => a (Sum.inr i)) h
    simp only [hγ, ite_false, MvPolynomial.coeff_zero,
      coeff_monomial, hne]

theorem polynomialSlotCoefficient_eval (t : σ → R) (β : τ →₀ ℕ)
    (P : MvPolynomial (σ ⊕ τ) R) :
    aeval t (polynomialSlotCoefficient β P) =
      (aeval (Sum.elim (fun i => C (t i)) X) P).coeff β := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    let e : (σ ⊕ τ →₀ ℕ) ≃ (σ →₀ ℕ) × (τ →₀ ℕ) := Finsupp.sumFinsuppEquivProdFinsupp
    obtain ⟨⟨α, γ⟩, hm⟩ := e.symm.surjective m
    change α.sumElim γ = m at hm
    rw [← hm, polynomialSlotCoefficient_monomial, polynomialParameterEval_monomial]
    by_cases h : γ = β <;> simp [h, coeff_monomial]
  | add P Q hP hQ =>
    simp only [map_add, MvPolynomial.coeff_add, hP, hQ]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorTranslationTopCoordinates_degree (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (j : B) :
    (majorTranslationTopCoordinates w A j).totalDegree ≤ w j := by
  apply (mem_weightedSupportLE_one_iff _ _).mp
  intro α hα
  exact (majorTranslationTopCoordinates_homogeneous w A j (mem_support_iff.mp hα)).le

theorem majorTranslationTopCoordinates_remainder (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) (j : B) :
    A j - majorTranslationTopCoordinates w A j ∈ weightedSupportLT (fun _ : U => 1) (w j) :=
  weightedTopPart_remainder_lt (fun _ : U => 1)
    ((mem_weightedSupportLE_one_iff _ _).mpr (hA j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbitConverse
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem realPolynomialMass_zeroParameterEval_le (P : MvPolynomial (σ ⊕ τ) ℝ) :
    realPolynomialMass (aeval (Sum.elim (fun _ : σ => (0 : MvPolynomial τ ℝ)) X) P) ≤
      realPolynomialMass P := by
  have h := realPolynomialMass_substitution_le P
    (Sum.elim (fun _ : σ => (0 : MvPolynomial τ ℝ)) X) (M := 1) le_rfl (by
      intro a
      cases a with
      | inl i => simpa only [Sum.elim_inl, realPolynomialMass_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
      | inr i => simp only [Sum.elim_inr, realPolynomialMass_X, le_refl]) le_rfl
  rw [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
  simpa only [one_pow, mul_one, MvPolynomial.coe_eval₂Hom] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RationalConstraintCountBudget
namespace OAI

section

namespace Erdos3

theorem rationalConstraint_list_count_le_exp (m n d N : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : (N : ℝ) ≤ p) :
    (((m * (n + 1) * (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d)) + 1) ^
      (N + 1) : ℕ) : ℝ) ≤ Real.exp ((p + 8) ^ 8) := by
  let M := m * (n + 1) * (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d))
  let F := 2 * p + 3 * p ^ 2 * (p + 2)
  have hM : (M : ℝ) ≤ Real.exp F := rationalConstraint_base_count_le_exp m n d hp hm hn hd
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have h1 : 1 ≤ Real.exp F := Real.one_le_exp hF
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ Real.exp (F + 1) := by
    calc
      _ ≤ 2 * Real.exp F := by push_cast; linarith
      _ ≤ Real.exp 1 * Real.exp F := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hpoly : F + 1 ≤ (p + 8) ^ 4 := by
    dsimp only [F]
    nlinarith [pow_nonneg hp 3, pow_nonneg hp 4]
  have hN1 : ((N + 1 : ℕ) : ℝ) ≤ p + 8 := by push_cast; linarith
  have ht : 1 ≤ p + 8 := by linarith
  change (((M + 1) ^ (N + 1) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (F + 1)) ^ (N + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM1 _
    _ = Real.exp (((N + 1 : ℕ) : ℝ) * (F + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((p + 8) ^ 5) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (p + 8) * (p + 8) ^ 4 := mul_le_mul hN1 hpoly (by positivity) (by positivity)
        _ = _ := by ring
    _ ≤ _ := Real.exp_le_exp.mpr (pow_le_pow_right₀ ht (by norm_num))

theorem rationalConstraint_list_count_le_exp_of_le (M m n d N : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : (N : ℝ) ≤ p)
    (hM : M ≤ m * (n + 1) *
      (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (n * d))) :
    (((M + 1) ^ (N + 1) : ℕ) : ℝ) ≤ Real.exp ((p + 8) ^ 8) := by
  apply le_trans _ (rationalConstraint_list_count_le_exp m n d N hp hm hn hd hN)
  exact_mod_cast Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) (N + 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RestrictedGradePathMembership
namespace OAI

section

namespace Erdos3

theorem reset_splitting_in_quotient {G Q : Type*} [Group G] [Group Q]
    (φ : G →* Q) (H : Subgroup G) (E P R E₀ R₀ A D : G)
    (hP : P ∈ H) (hA : A ∈ H) (hD : D ∈ H)
    (hAq : φ A = φ (E₀⁻¹ * E)) (hDq : φ D = φ (R * R₀⁻¹)) :
    (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
      A * P * D ∈ H ∧ φ (E * A⁻¹) = φ E₀ ∧ φ (D⁻¹ * R) = φ R₀ := by
  refine ⟨?_, H.mul_mem (H.mul_mem hA hP) hD, ?_, ?_⟩
  · group
  · rw [map_mul, map_inv, hAq, map_mul, map_inv]
    group
  · rw [map_mul, map_inv, hDq, map_mul, map_inv]
    group

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledLinearSubspaceLift
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

variable {η ι δ : Type*} [Fintype ι]

theorem jointMatrixImages_grid [Fintype η] (Q : η → Matrix ι ι ℚ) (l : ℕ)
    (x : η → ι → ℝ) (hx : ∀ b, x b ∈ realDenominatorGrid l) :
    jointMatrixImages Q x ∈ realDenominatorGrid (matrixDenominator (jointMatrix Q) * l) := by
  classical
  choose z hz using hx
  let A := jointMatrix Q
  have hcoef (bi : Σ _ : η, ι) (j : ι) :
      ((clearedMatrix A bi j : ℤ) : ℝ) = (matrixDenominator A : ℝ) * (Q bi.1 bi.2 j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast A) bi) j
    change ((clearedMatrix A bi j : ℤ) : ℚ) = (matrixDenominator A : ℚ) * Q bi.1 bi.2 j at h
    exact_mod_cast h
  refine ⟨fun bi => ∑ j, clearedMatrix A bi j * z bi.1 j, ?_⟩
  funext bi
  change ((∑ j, clearedMatrix A bi j * z bi.1 j : ℤ) : ℝ) =
    ((matrixDenominator A * l : ℕ) : ℝ) * ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ x bi.1) bi.2
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (z bi.1 j : ℝ) = (l : ℝ) * x bi.1 j := congrFun (hz bi.1) j
  rw [hcoef, hj]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealCoordinateImageSpan
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J B : Type*} [AddCommGroup V] [Module ℚ V]

theorem realifyCoordinateMap_image_eq_span (U : Submodule ℚ V) (g : J → V)
    (hg : Submodule.span ℚ (Set.range g) = U) (ℓ : V →ₗ[ℚ] (B → ℚ)) :
    (U.baseChange ℝ).map (realifyCoordinateMap ℓ) =
      Submodule.span ℝ (Set.range (fun j i => (ℓ (g j) i : ℝ))) := by
  rw [← hg, Submodule.baseChange_span, Submodule.map_span, Set.image_image, ← Set.range_comp]
  apply congrArg (Submodule.span ℝ)
  apply congrArg Set.range
  funext j i
  exact (realifyCoordinateMap_tmul ℓ 1 (g j) i).trans (one_mul _)

theorem realifyCoordinateMap_mem_span (U : Submodule ℚ V) (g : J → V)
    (hg : Submodule.span ℚ (Set.range g) = U) (ℓ : V →ₗ[ℚ] (B → ℚ))
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ U.baseChange ℝ) :
    realifyCoordinateMap ℓ x ∈
      Submodule.span ℝ (Set.range (fun j i => (ℓ (g j) i : ℝ))) := by
  rw [← realifyCoordinateMap_image_eq_span U g hg ℓ]
  exact ⟨x, hx, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RealProjectedPotentialGroupIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
theorem realification_pair_eq_of_rational
    {V Y : Type*} [AddCommGroup V] [Module ℚ V]
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [TopologicalSpace Y] [T2Space Y]
    (U : Submodule ℚ V)
    {f g : (ℝ ⊗[ℚ] V) × (ℝ ⊗[ℚ] V) → Y}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x y : U, f ((1 : ℝ) ⊗ₜ[ℚ] (x : V), (1 : ℝ) ⊗ₜ[ℚ] (y : V)) =
      g ((1 : ℝ) ⊗ₜ[ℚ] (x : V), (1 : ℝ) ⊗ₜ[ℚ] (y : V)))
    {x y : ℝ ⊗[ℚ] V} (hx : x ∈ U.baseChange ℝ) (hy : y ∈ U.baseChange ℝ) :
    f (x, y) = g (x, y) := by
  apply realification_submodule_eq_of_rational U
    (hf.comp (continuous_const.prodMk continuous_id))
    (hg.comp (continuous_const.prodMk continuous_id)) _ hy
  intro y
  exact realification_submodule_eq_of_rational U
    (hf.comp (continuous_id.prodMk continuous_const))
    (hg.comp (continuous_id.prodMk continuous_const)) (fun x => h x y) hx

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateFiberPatch
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def PolynomialPatch.coordinateFiber {s d : ℕ} (A : PolynomialPatch I s d)
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ) : PolynomialPatch {i // keep i} s d :=
  A.reparam (coordinateFiberParameters keep fixed) (coordinateFiberParameters_degree keep fixed)

theorem PolynomialPatch.coordinateFiber_value {s d : ℕ} (A : PolynomialPatch I s d)
    (keep : I → Prop) (fixed : {i // ¬keep i} → ℤ) (x : {i // keep i} → ℤ) :
    (A.coordinateFiber keep fixed).value (fun i => (x i : ℝ)) =
      A.value (fun i => ((finiteSplitPoint keep x fixed i : ℤ) : ℝ)) := by
  let _ : Fintype I := inferInstance
  let _ : DecidableEq I := inferInstance
  rw [coordinateFiber, reparam_value]
  congr 1
  funext i
  by_cases hi : keep i <;> simp [coordinateFiberParameters, finiteSplitPoint, hi]

theorem PolynomialPatch.exists_coordinate_fiber_score {s d : ℕ} (A : PolynomialPatch I s d)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (keep : I → Prop)
    (score : (I → ℤ) → ℝ) {a : ℝ}
    (hmean : a ≤ 𝔼 x ∈ integerBox N, score x * A.value (fun i => (x i : ℝ))) :
    ∃ fixed : {i // ¬keep i} → ℤ,
      (∀ i, 0 ≤ fixed i ∧ fixed i < N i) ∧
      a ≤ 𝔼 x ∈ integerBox (fun i : {i // keep i} => N i),
        score (finiteSplitPoint keep x fixed) *
          (A.coordinateFiber keep fixed).value (fun i => (x i : ℝ)) := by
  obtain ⟨fixed, hfixed, hscore⟩ := exists_integerBox_coordinate_fiber N hN keep
    (fun x => score x * A.value (fun i => (x i : ℝ))) hmean
  exact ⟨fixed, hfixed, by simpa only [coordinateFiber_value] using hscore⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AlgebraicMajorWeightedAffineTopPullback
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorSlowDilationPullback_mem_weightedSupportLE
    (q : ℕ) (H T : U → ℝ) (S : MvPolynomial (U ⊕ B) ℝ)
    (w : U ⊕ B → ℕ) (d : ℕ) (hS : S ∈ weightedSupportLE w d) :
    majorSlowDilationPullback q H T S ∈ weightedSupportLE w d :=
  scaleMvPolynomialAxes_mem_weightedSupportLE _ w d hS

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem jointResidueAffine_variables_degree (w : B → ℕ) (q : ℕ) (r : U → ℤ)
    (i : U ⊕ B) :
    Sum.elim (fun j => C (r j : ℝ) + C (q : ℝ) * X (Sum.inl j))
      (fun j => X (Sum.inr j)) i ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) (Sum.elim (fun _ : U => 1) w i) := by
  cases i with
  | inl i =>
    apply (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    simpa only [zero_add] using weightedSupportLE_mul
      (weightedSupportLE_C (Sum.elim (fun _ : U => 1) w) 0 (q : ℝ))
      (weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inl i))
  | inr j => exact weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inr j)

theorem jointResidueAffinePolynomial_degree (w : B → ℕ) (q : ℕ) (r : U → ℤ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    jointResidueAffinePolynomial q r D ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
  weightedSupportLE_aeval _ _ _ (jointResidueAffine_variables_degree w q r) hD

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeGrid_small_error_of_length (I : Type*) [Fintype I] [DecidableEq I]
    {L M : ℕ} (hL : 0 < L)
    (hlarge : 2 * scalarCubeGridBoundaryConstant I * M / volume.real (scalarCubeDomain I) ≤ L) :
    scalarCubeGridBoundaryConstant I * ((M : ℝ)/L) < volume.real (scalarCubeDomain I) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hV := scalarCubeDomain_volumeReal_pos I
  have h := (div_le_iff₀ hV).mp hlarge
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hLp).mpr
  nlinarith [mul_pos hLp hV]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointRationalSpaceGenerators
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_real_kernel_generators {J V : Type*} [Fintype J] [Fintype V]
    (A : Matrix V J ℚ) {H : ℕ} (hH : 1 ≤ H) (hA : ∀ v j, RationalHeightLE (A v j) H) :
    ∃ P : Matrix J J ℚ,
      (∀ i j, RationalHeightLE (P i j) (imageDefiningHeight (Fintype.card V) (Fintype.card V) H)) ∧
      LinearMap.range (Matrix.of (fun i j => (P i j : ℝ))).mulVecLin =
        LinearMap.ker (Matrix.of (fun v j => (A v j : ℝ))).mulVecLin := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  let P : Matrix J J ℚ := 1 - S * A
  have hSr := real_matrix_image_section A S hS
  have hPr : Matrix.of (fun i j => (P i j : ℝ)) =
      1 - Matrix.of (fun i v => (S i v : ℝ)) * Matrix.of (fun v j => (A v j : ℝ)) := by
    ext i j
    by_cases hij : i = j <;> simp [P, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, hij]
  refine ⟨P, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix J J ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul S A hSH hA i j
    simpa only [P, Matrix.sub_apply, imageDefiningHeight, mul_one, one_mul, mul_comm] using hI.sub hprod
  · ext x
    change (∃ y, Matrix.of (fun i j => (P i j : ℝ)) *ᵥ y = x) ↔
      Matrix.of (fun v j => (A v j : ℝ)) *ᵥ x = 0
    rw [hPr]
    constructor
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSr,
        sub_self, Matrix.zero_mulVec]
    · intro hx
      refine ⟨x, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory

theorem standardEuclideanLattice_covolume (J : Type*) [Fintype J] :
    ZLattice.covolume (standardEuclideanLattice J) = 1 := by
  classical
  let b := EuclideanSpace.basisFun J ℝ
  have hg : Matrix.gram ℝ b.toBasis = 1 :=
    Matrix.gram_eq_one_iff_orthonormal.mpr b.orthonormal
  have hs := zspan_covolume_sq_eq_det_gram_fintype b.toBasis
  rw [hg, Matrix.det_one] at hs
  have hp := ZLattice.covolume_pos (standardEuclideanLattice J) volume
  change ZLattice.covolume (standardEuclideanLattice J) ^ 2 = 1 at hs
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedRealPoint
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedRealPoint_scaled_coordinate_bound {C R S : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hS : 0 < S)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (u : I → ℝ) (z : Fin n → ℝ) (hu : ∀ i, |u i| * S ≤ R) (hz : ∀ i, |z i| * S ≤ R) (d : D) :
    |mixedRealPoint W b o (u, z) d| ≤ C * (((Fintype.card I : ℝ) + 1) * R) / S := by
  apply (le_div_iff₀ hS).mpr
  have hscale := mixedRealPoint_norm_le W b o hC hR hchart (S • u) (S • z)
    (fun i => by simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hS, mul_comm] using hu i)
    (fun i => by simpa only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hS, mul_comm] using hz i)
  have he : mixedRealPoint W b o (S • u, S • z) = S • mixedRealPoint W b o (u, z) :=
    (mixedRealPoint W b o).map_smul S (u, z)
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hS] at hscale
  have hd : |mixedRealPoint W b o (u, z) d| ≤ ‖mixedRealPoint W b o (u, z)‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (mixedRealPoint W b o (u, z)) d
  exact (mul_le_mul_of_nonneg_right hd hS.le).trans (by simpa only [mul_comm] using hscale)

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

theorem mixedLiftPolynomial_degree (e : J → V →₀ ℕ)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) {h : ℕ}
    (he : ∀ j, (e j).sum (fun _ k => k) ≤ h) (d : D) :
    (mixedLiftPolynomial W b o e a d).totalDegree ≤ h := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (he j)

theorem mixedLiftPolynomial_coeff (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (d : D) (j : J) :
    (mixedLiftPolynomial W b o e a d).coeff (e j) = mixedLiftCoefficient W b o a j d :=
  monomialArrayPolynomial_coeff e he _ j

theorem mixedLiftPolynomial_coefficient_bound (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ)) (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {M : ℝ} (hM : 0 ≤ M)
    (hbnd : ∀ j d, |mixedLiftCoefficient W b o a j d| ≤ M / monomialScale T (e j))
    (α : V →₀ ℕ) (d : D) :
    |(mixedLiftPolynomial W b o e a d).coeff α| ≤ M / monomialScale T α := by
  classical
  by_cases hα : ∃ j, e j = α
  · obtain ⟨j, rfl⟩ := hα
    rw [mixedLiftPolynomial_coeff W b o e he]
    exact hbnd j d
  · rw [mixedLiftPolynomial, monomialArrayPolynomial_coeff_zero_of_not_mem e _ α
      (fun j hj => hα ⟨j, hj⟩), abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedArraySupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem allocatedProfile_term_bound {J : Type*} [Fintype J] (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (j : J) :
    |coefficientProfileCenter P (principalProfileSize R P.card) j| +
      coefficientProfileWidth P j₀ (R / 4) (principalProfileSize R P.card)
        (tailProfileSize R σ (Fintype.card J)) j ≤ 3 * R / 4 := by
  classical
  apply (Finset.single_le_sum (s := Finset.univ)
    (fun i _ => add_nonneg (abs_nonneg _) (continuousPolynomialDensity_width_pos P j₀ hR hσ i).le)
    (Finset.mem_univ j)).trans
  exact (coefficientProfile_budget P j₀ hj₀ (principalProfileSize_pos hR _).le
    (tailProfileSize_pos hR hσ _).le).trans (allocatedProfile_budget hR.le hσ1 _ _)

theorem allocatedIntegerCoefficient_bound {J V : Type*} [Fintype J]
    (P : Finset J) (j₀ : J) (h K L s : ℕ) (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
    (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
    (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hgap : L ^ h < K → (principalSamplingGapRatio (principalProfileSize R P.card) * L) ^ h ≤ K)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) =
      (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ) ^ h)
    (j : J) {k : ℤ}
    (hk : k ∈ (allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
      R σ hR hσ hgap hεL j).support) :
    |(k : ℝ) / K| * monomialScale T (e j) ≤ 3 * R / 4 := by
  have hb := integerPolynomialCoordinatePMF_bound P j₀ h K L s hh hK hL T hT hTL e he
    (R / 4) (principalProfileSize R P.card) (tailProfileSize R σ (Fintype.card J))
    (by positivity) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _)
    hgap hεL hj₀ he₀ hprincipal j hk
  exact hb.trans (allocatedProfile_term_bound P j₀ hj₀ hR hσ hσ1 j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedLongMixedCoefficientBound
namespace OAI

section

namespace Erdos3

theorem continuousPolynomialDensity_coefficient_bound {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0) (j : J) :
    |a j| * monomialScale T (e j) ≤ 3 * R / 4 :=
  (scaledCoefficientDensity_coefficient_bound e T hT _ _
    (continuousPolynomialDensity_width_pos P j₀ hR hσ) ha j).trans
      (allocatedProfile_term_bound P j₀ hj₀ hR hσ hσ1 j)

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)

include hσ1 in
theorem allocatedLayerCoefficient_scaled_bounds (j : Fin m)
    (a : (I j → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ) ×
      (Fin (n j) → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ))
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j)
      (allocatedLayerIntegerPMFs B U b hR hσ S j) a) (d) :
    (∀ i, |a.1 i d| * monomialScale (layerSamplerBox B U b S) d.val ≤ R j) ∧
      (∀ i, |(a.2 i d : ℝ) / basisAxisScale (b j) i| *
        monomialScale (layerSamplerBox B U b S) d.val ≤ R j) := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have hs := (allocatedArraySupported_iff_rows Subtype.val (layerSamplerBox B U b S)
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (R j) (σ j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) a).mp ha
  constructor
  · intro i
    exact (continuousPolynomialDensity_coefficient_bound Subtype.val _ hT _ _
      (layerContinuousPrincipalSlots_not_constant B j i) (hR j) (hσ j) (hσ1 j) (hs.1 i) d).trans
        (by linarith [hR j])
  · intro i
    exact (allocatedIntegerCoefficient_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
      (j.val + 1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (Nat.zero_lt_succ _) (basisAxisScale_pos (b j) i)
      S.positive (layerSamplerBox B U b S) hT (layerSamplerBox_le B U b S) Subtype.val
      (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (hσ1 j) (S.gap j i) (S.width j)
      (layerIntegerPrincipalSlots_not_constant B j i) rfl
      (layerSamplerSides_integer_principal B U b R S.value j i) d (hs.2 i d)).trans (by linarith [hR j])

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)

include hσ1

theorem allocatedLayerLiftCoefficient_radius_bound
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (j : Fin m) {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C * ‖v‖)
    (a) (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) (i : J j) :
    |mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) a d i| ≤
      (C * (((Fintype.card (I j) : ℝ) + 1) * R j)) /
        monomialScale (layerSamplerBox B U b S) d.val := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have h := allocatedLayerCoefficient_scaled_bounds B U b hR hσ S hσ1 j a ha d
  exact mixedRealPoint_scaled_coordinate_bound _ (b j) (o j) hC (hR j).le
    (monomialScale_pos _ hT d.val) hchart _ _ h.1 h.2 i

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNormalizedCoefficientBounds
namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem continuousPolynomialDensity_coefficient_le_radius {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0) (j : J) :
    |a j| * monomialScale T (e j) ≤ R :=
  (continuousPolynomialDensity_coefficient_bound e T hT P j₀ hj₀ hR hσ hσ1 ha j).trans
    (by linarith)

theorem allocatedIntegerCoefficient_le_radius {J V : Type*} [Fintype J]
    (P : Finset J) (j₀ : J) (h K L s : ℕ) (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
    (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
    (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hgap : L ^ h < K → (principalSamplingGapRatio (principalProfileSize R P.card) * L) ^ h ≤ K)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) =
      (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ) ^ h)
    (j : J) {k : ℤ}
    (hk : k ∈ (allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
      R σ hR hσ hgap hεL j).support) :
    |(k : ℝ) / K| * monomialScale T (e j) ≤ R :=
  (allocatedIntegerCoefficient_bound P j₀ h K L s hh hK hL T hT hTL e he R σ hR hσ hσ1
    hgap hεL hj₀ he₀ hprincipal j hk).trans (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearRestrictionDenominatorSize
namespace OAI

section

namespace Erdos3

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

theorem polynomialLinearRestriction_denominator_pos
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) (d : ℕ) :
    0 < polynomialDenominator P *
      matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d :=
  Nat.mul_pos (polynomialDenominator_pos P)
    (pow_pos (matrixDenominator_pos _) _)

theorem polynomialLinearRestriction_denominator_le
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (P : MvPolynomial σ ℚ) {d K H : ℕ}
    (hd : P.totalDegree ≤ d) (hP : RationalPolynomialHeightLE P K)
    (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H) :
    polynomialDenominator P * matrixDenominator (fun i j => A (Pi.single j 1) i) ^ d ≤
      K ^ ((Fintype.card σ + 1) ^ d) * H ^ ((Fintype.card σ * Fintype.card τ) * d) := by
  have hcard : P.support.card ≤ (Fintype.card σ + 1) ^ d :=
    boundedExponentSet_card_le P.support d
      (fun _ hm => (MvPolynomial.le_totalDegree hm).trans hd)
  have hpoly : polynomialDenominator P ≤ K ^ ((Fintype.card σ + 1) ^ d) :=
    (polynomialDenominator_le P hP).trans (Nat.pow_le_pow_right hP.one_le hcard)
  have hmatrix := Nat.pow_le_pow_left
    (matrixDenominator_le (fun i j => A (Pi.single j 1) i) hA) d
  rw [← pow_mul] at hmatrix
  exact Nat.mul_le_mul hpoly hmatrix

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealFunctionalBCH
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

attribute [local instance] LieRing.ofAssociativeRing

theorem realifyFunctional_lieBCH (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x y : L, η ⁅x, y⁆ = 0) {s : ℕ} (hs : 1 ≤ s)
    (x y : ℝ ⊗[ℚ] L) :
    realifyFunctional η (lieBCH s x y) = realifyFunctional η x + realifyFunctional η y := by
  change realifyFunctionalLie η hη (lieBCH s x y) = _
  rw [map_lieBCH, lieBCH_eq_add_of_lie_eq_zero_pos hs
    (by simp only [Ring.lie_def, mul_comm, sub_self])]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ScalarFunctionalCoefficientGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

theorem scalarFunctionalDenominator_pos (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ) :
    0 < matrixDenominator (fun (_ : Unit) i => θ (b i)) :=
  matrixDenominator_pos _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NormalizedTwistLocalizedFourierSelection
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem highest_nonannihilating_tag (d : ℕ)
    (W : ∀ j, Submodule ℝ (J j → ℝ)) (a : (Σ j, J j) → ℤ) :
    (∀ j : Fin m, d < j.val + 1 →
      W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))) ∨
    ∃ h : Fin m, d < h.val + 1 ∧
      (∃ w ∈ W h, integerRowLinear (fun i => a ⟨h, i⟩) w ≠ 0) ∧
      ∀ j : Fin m, h < j → W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)) := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun j => d < j.val + 1 ∧
    ¬ W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)))
  by_cases hs : S.Nonempty
  · let h := S.max' hs
    have hh : h ∈ S := Finset.max'_mem S hs
    have hh' := (Finset.mem_filter.mp hh).2
    refine Or.inr ⟨h, hh'.1, ?_, ?_⟩
    · by_contra! hn
      apply hh'.2
      intro w hw
      exact hn w hw
    · intro j hj
      by_contra hn
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨hh'.1.trans (Nat.add_lt_add_right hj 1), hn⟩⟩
      exact (not_le_of_gt hj) (Finset.le_max' S j hjS)
  · refine Or.inl ?_
    intro j hj
    by_contra hn
    exact hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hn⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AlgebraicMajorIntegerRestoration
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem weightedHomogeneousComponent_fractional_restoration
    (F : MvPolynomial σ ℝ) (w : σ → ℕ) (d : ℕ) :
    weightedHomogeneousComponent w d F =
      weightedHomogeneousComponent w d (fractionalCoefficientPolynomial F) +
        MvPolynomial.map (Int.castRingHom ℝ)
          (weightedHomogeneousComponent w d (floorIntegerPolynomial F)) := by
  classical
  conv_lhs => rw [← floorIntegerPolynomial_add_fractionalCoefficientPolynomial F]
  rw [map_add, add_comm]
  congr 1
  ext a
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem restoredMajorRemainder_degree (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ)
    (hR : R ∈ weightedSupportLE w d) :
    restoredMajorRemainder F w d R ∈ weightedSupportLE w d := by
  apply (weightedSupportLE w d).add_mem hR
  intro a ha
  have hi : (MvPolynomial.map (Int.castRingHom ℚ)
      (weightedHomogeneousComponent w d (floorIntegerPolynomial F))).IsWeightedHomogeneous w d := by
    intro a ha
    apply weightedHomogeneousComponent_isWeightedHomogeneous
      (w := w) d (floorIntegerPolynomial F)
    intro hz
    apply ha
    simp only [coeff_map, hz, map_zero]
  exact (hi (mem_support_iff.mp ha)).le

theorem algebraic_major_restore_integer_coefficients
    {U B : Type*} (F : MvPolynomial (U ⊕ B) ℝ)
    (w : U ⊕ B → ℕ) (d : ℕ) (K : Submodule ℝ (B → ℝ))
    (A : B → MvPolynomial U ℝ) (H : U → ℝ)
    (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ) (q : ℕ)
    (hgrid : (fun a => R.coeff a) ∈ denominatorGrid q)
    (hdegree : R ∈ weightedSupportLE w d)
    (hidentity : ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b)
          (weightedHomogeneousComponent w d (fractionalCoefficientPolynomial F)) =
        eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R) :
    let R' := restoredMajorRemainder F w d R
    (fun a => R'.coeff a) ∈ denominatorGrid q ∧ R' ∈ weightedSupportLE w d ∧
      ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b) (weightedHomogeneousComponent w d F) =
          eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S +
            eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R' := by
  refine ⟨restoredMajorRemainder_coefficientGrid F w d R q hgrid,
    restoredMajorRemainder_degree F w d R hdegree, ?_⟩
  intro u b hb
  rw [weightedHomogeneousComponent_fractional_restoration, map_add, hidentity u b hb,
    restoredMajorRemainder_eval, add_assoc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse
namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open _root_.MvPolynomial PolynomialTranslationLie
open scoped TensorProduct NNReal

variable {U : Type*}

theorem phaseSlotCoefficient_rename (P : MvPolynomial U ℝ) :
    polynomialSlotCoefficient (0 : Fin 0 →₀ ℕ)
      (rename (Sum.inl : U → U ⊕ Fin 0) P) = P := by
  ext α
  rw [polynomialSlotCoefficient_coeff, Finsupp.sumElim_eq_add]
  simp only [Finsupp.mapDomain_zero, add_zero]
  exact coeff_rename_mapDomain _ Sum.inl_injective P α

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MajorPhaseLowFourierExtraction
namespace OAI

section

namespace Erdos3

theorem exists_majorPhaseLowFourierExtraction_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + a) ^ a + p + 1
      q ≤ (p + C) ^ C ∧ (q + b) ^ b ≤ (p + C) ^ C ∧
        3 * q + 16 ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C b) ^ b + 3 * Q + 16)
  refine ⟨C, hC, ?_⟩
  intro p hp
  dsimp only
  let q : ℝ := (p + a) ^ a + p + 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 0 ≤ (q + b) ^ b := by positivity
  have htotal : q + (q + b) ^ b + 3 * q + 16 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  change q ≤ _ ∧ (q + b) ^ b ≤ _ ∧ 3 * q + 16 ≤ _
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R : Type*} [CommRing R]

 theorem lowTaggedRestrictionVariables_isWeightedHomogeneous (k : ℕ)
    (i : X ⊕ (Σ j, J j)) :
    (lowTaggedRestrictionVariables (R := R) J k i).IsWeightedHomogeneous
      (lowTaggedVariableWeight J k) (fullTaggedVariableWeight J i) := by
  classical
  cases i with
  | inl x => exact isWeightedHomogeneous_X (R := R) (lowTaggedVariableWeight J k) (Sum.inl x)
  | inr a =>
    by_cases h : a.1.val + 1 ≤ k
    · simp only [lowTaggedRestrictionVariables, Sum.elim_inr, dif_pos h]
      have he : lowTaggedVariableWeight (X := X) J k (Sum.inr (lowTaggedSlot J k a.1 h a.2)) =
          a.1.val + 1 := by
        simp only [lowTaggedVariableWeight, Sum.elim_inr, lowTaggedWeight, lowTaggedIndex_slot]
      exact he ▸ isWeightedHomogeneous_X (R := R) (lowTaggedVariableWeight J k)
        (Sum.inr (lowTaggedSlot J k a.1 h a.2))
    · simp only [lowTaggedRestrictionVariables, Sum.elim_inr, dif_neg h]
      exact isWeightedHomogeneous_zero R _ _

 theorem rename_lowTaggedRestrictionVariables_of_weight_le (k : ℕ)
    (i : X ⊕ (Σ j, J j)) (hi : fullTaggedVariableWeight J i ≤ k) :
    rename (lowTaggedVariableEmbedding J k) (lowTaggedRestrictionVariables (R := R) J k i) = MvPolynomial.X i := by
  classical
  cases i with
  | inl x => simp only [lowTaggedRestrictionVariables, Sum.elim_inl, rename_X,
      lowTaggedVariableEmbedding_inl]
  | inr a =>
    have ha : a.1.val + 1 ≤ k := hi
    simp only [lowTaggedRestrictionVariables, Sum.elim_inr, dif_pos ha, rename_X,
      lowTaggedVariableEmbedding_slot]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialAffineFullMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {K X R : Type*} [Fintype K] [CommRing R] [Nontrivial R]

omit [Nontrivial R] in
theorem affineFramePolynomial_map {S : Type*} [CommRing S] [Nontrivial S] (φ : R →+* S)
    (frame : Option K → X → R) (i : X) :
    MvPolynomial.map φ (affineFramePolynomial frame i) =
      affineFramePolynomial (fun k i => φ (frame k i)) i := by
  simp [affineFramePolynomial]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem affineFramePolynomial_top_one (frame : Option K → X → ℝ) (x : X) :
    homogeneousComponent 1 (affineFramePolynomial frame x) =
      ∑ k, C (frame (some k) x) * MvPolynomial.X k := by
  rw [affineFramePolynomial, map_add,
    homogeneousComponent_eq_zero 1 (C (frame none x)) (by simp), zero_add,
    map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [homogeneousComponent_C_mul,
    homogeneousComponent_eq_self (isHomogeneous_X ℝ k)]

theorem scaleMvPolynomialAxes_affineFrame_top_one
    (frame : Option K → X → ℝ) (T : K → ℝ) (x : X) :
    scaleMvPolynomialAxes T (homogeneousComponent 1 (affineFramePolynomial frame x)) =
      ∑ k, C (frame (some k) x * T k) * MvPolynomial.X k := by
  apply MvPolynomial.funext
  intro y
  rw [scaleMvPolynomialAxes_eval, affineFramePolynomial_top_one]
  simp only [eval_sum, map_mul, eval_C, eval_X]
  apply Finset.sum_congr rfl
  intro k _
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FrozenPolynomialAffineRange
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem longChart_freezePolynomial_zero_eq_killCompl {I R : Type*} [CommRing R]
    (keep : I → Prop) :
    freezePolynomial keep (0 : {i // ¬ keep i} → R) =
      killCompl (Subtype.val_injective (p := keep)) := by
  classical
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : keep i
  · let a : {i // keep i} := ⟨i, hi⟩
    have hk := killCompl_rename_app (R := R) (Subtype.val_injective (p := keep))
      (MvPolynomial.X a)
    simp only [rename_X] at hk
    simpa only [freezePolynomial, aeval_X, frozenCoordinate, dif_pos hi] using hk.symm
  · have hrange : i ∉ Set.range (Subtype.val : {i // keep i} → I) := by
      rintro ⟨a, rfl⟩
      exact hi a.property
    simp only [freezePolynomial, aeval_X, frozenCoordinate, dif_neg hi,
      Pi.zero_apply, map_zero, killCompl, aeval_X, dif_neg hrange]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMixedLiftNormalizedMass
namespace OAI

section

namespace Erdos3
open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedLiftPolynomial_scaled_coefficients [Fintype V]
    (e : J → V →₀ ℕ) (he : Function.Injective e)
    (a : (I → J → ℝ) × (Fin n → J → ℤ))
    (T : V → ℝ) (hT : ∀ v, 0 < T v) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hc : ∀ i j, |a.1 i j| * monomialScale T (e j) ≤ R)
    (hz : ∀ i j, |(a.2 i j : ℝ) / basisAxisScale b i| * monomialScale T (e j) ≤ R)
    (α : V →₀ ℕ) (d : D) :
    |(mixedLiftPolynomial W b o e a d).coeff α| ≤
      C * (((Fintype.card I : ℝ) + 1) * R) / monomialScale T α := by
  apply mixedLiftPolynomial_coefficient_bound W b o e he a T hT (by positivity)
  intro j d
  exact mixedRealPoint_scaled_coordinate_bound W b o hC hR
    (monomialScale_pos T hT (e j)) hchart _ _ (fun i => hc i j) (fun i => hz i j) d

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchTaggedBufferedScore
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open VectorPolynomial

variable {X : Type*} {m n : ℕ} {J : Fin m → Type*}

noncomputable def taggedShearOrbitReindexChart (e : Fin n ≃ Sigma J) :
    X ⊕ Sigma J → MvPolynomial (X ⊕ Fin n) ℝ :=
  fun v => MvPolynomial.X (Sum.map id e.symm v)

end Erdos3

end

end OAI
end


