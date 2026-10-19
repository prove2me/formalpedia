-- Prove2me | Definitions.Def_OAIE3v2B115
-- name    : OAIE3v2B115
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:37:39.755401+00:00
-- url     : https://prove2.me/theorems/50950d8c-5762-492a-b2a4-c30571c650fe
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 117 of 311
-- statement:
--   Definitions bundle 117 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102`, `OAIE3v2B104` of this split.
--
--   Modules: `Estimates/CoefficientFiberOrthogonality.lean`, `Estimates/MajorTranslationPureFactorValues.lean`, `Estimates/OneSiteCoefficientFactorization.lean`, `Estimates/OneSiteResidualFactor.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/ProductOrbitCongruence.lean`, `Estimates/RationalCentralCircle.lean`, `Estimates/RationalPowerHeight.lean`, `Estimates/RelativePatchAmplification.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/TranslationShearExponentialOver.lean`, `Estimates/WeightedTranslationShearExponential.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/OneSiteFourierAverage.lean`, `Fourier/SectionRetainedFourier.lean`, `Geometry/CoordinateQuotientModel.lean`, `Geometry/WeightedTranslationBufferedCoordinates.lean`, `Geometry/WeightedTranslationIntegralCoordinates.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Linear/BasisFamilyLogHeight.lean`, `Linear/RankQuotientHeightBudget.lean`, `Linear/WeightedTranslationBasisHeight.lean`, `Nilpotent/AdaptedBasisNilmanifold.lean`, `Nilpotent/CurrentBracketInductionStep.lean`, `Nilpotent/FreeWeightedNilpotentLieAlgebra.lean`, `Nilpotent/IdealInvariantNiltestBudget.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Nilpotent/NiltestProbabilityProjection.lean`, `Nilpotent/RealifiedBCHProductEquiv.lean`, `Polynomial/PolynomialPatchShearOrbit.lean`, `Polynomial/PolynomialShearAffineExponential.lean`, `Polynomial/PolynomialShearFactorialIntegrality.lean`, `Polynomial/PolynomialShearParameterBudget.lean`, `Polynomial/PolynomialShearRealGroup.lean`, `Polynomial/RealAdaptedPolynomialGroup.lean`, `Polynomial/RealCoordinatePolynomialSymbol.lean`, `Polynomial/RealPositivePolynomialEvaluation.lean`, `Polynomial/ScaledPolynomialDualBounds.lean`, `Sampling/SupportedQuotientExactGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B102
import Definitions.Def_OAIE3v2B104

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

theorem polynomialShear_X_mass_of_coordinates (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {s : ℕ} (hw : ∀ i, w i ≤ s)
    {δ : ℝ} (hδ : 0 ≤ δ) (hD : ∀ a, |(polynomialShearBasis (R := ℝ) w).repr D a| ≤ δ) (i : σ) :
    realPolynomialMass (D.val (X i)) ≤ ((s + 1) * (Fintype.card σ + 1) ^ s : ℕ) * δ := by
  classical
  have hdegree : (D.val (X i)).totalDegree ≤ s :=
    totalDegree_le_of_positive_weightedSupport w hpos
      (weightedSupportLE_mono (hw i) (weightedSupportDrop_le (D.property i)))
  calc
    _ ≤ ∑ _a ∈ (D.val (X i)).support, δ := by
      apply Finset.sum_le_sum
      intro a ha
      exact hD ⟨i, a, D.property i ha⟩
    _ = ((D.val (X i)).support.card : ℝ) * δ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast polynomial_support_card_le _ hdegree) hδ

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

theorem polynomialShearExp_degree (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    polynomialShearExp D P ∈ weightedSupportLE w n := by
  rw [polynomialShearExp_eq_on D hP]
  exact (polynomialShearExpOn D n ⟨P, hP⟩).property

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

theorem polynomialShearExp_eq_add_of_sq_eq_zero (D : PolynomialShearLieAlgebra w R)
    {P : MvPolynomial σ R} (hP : (D.val.toLinearMap ^ 2) P = 0) :
    polynomialShearExp D P = P + D.val P := by
  let n := max (P.weightedTotalDegree w) 1
  have hdeg : P ∈ weightedSupportLE w n :=
    (mem_weightedSupportLE_iff w n P).mpr (le_max_left _ _)
  have htwo : 2 ≤ n + 1 := Nat.succ_le_succ (le_max_right _ _)
  rw [polynomialShearExp_eq_sum D hdeg]
  have hsum :
      (∑ k ∈ Finset.range 2, (k.factorial : ℚ)⁻¹ • (D.val.toLinearMap ^ k) P) =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : ℚ)⁻¹ • (D.val.toLinearMap ^ k) P := by
    apply Finset.sum_subset (Finset.range_mono htwo)
    intro k _ hk
    have hk2 : 2 ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
    rw [Module.End.pow_map_zero_of_le hk2 hP, smul_zero]
  rw [← hsum]
  simp [Finset.sum_range_succ]

theorem polynomialShearExp_X_of_derivation_eq_C (D : PolynomialShearLieAlgebra w R)
    (i : σ) (b : R) (hD : D.val (X i) = C b) :
    polynomialShearExp D (X i) = X i + C b := by
  have hsq : (D.val.toLinearMap ^ 2) (X i) = 0 := by
    change D.val (D.val (X i)) = 0
    rw [hD, MvPolynomial.derivation_C]
  rw [polynomialShearExp_eq_add_of_sq_eq_zero D hsq, hD]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearFactorialIntegrality
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem polynomialShear_factorial_exp_integral (s : ℕ) (hw : ∀ i, w i ≤ s)
    (D : PolynomialShearLieAlgebra w ℚ)
    (hD : ∀ i, D.val (X i) ∈ integerCoefficientPolynomials σ) :
    polynomialShearExpAut ((s.factorial : ℚ) • D) ∈ integerWeightedLoweringSubgroup w := by
  intro i
  rw [polynomialShearExpAut_apply, polynomialShearExp_eq_sum _
    (weightedSupportLE_mono (hw i) (weightedSupportLE_X w i))]
  apply (integerCoefficientPolynomials σ).sum_mem
  intro k hk
  rw [polynomialShear_scaled_pow, smul_smul]
  exact integerCoefficientPolynomials_rat_smul
    (factorial_exp_scalar_integer s k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    (integerPolynomialDerivation_pow D.val hD (integerCoefficientPolynomials_X i) k)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRealGroup
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {σ : Type*} (w : σ → ℕ)

variable [Fintype σ]

theorem polynomialShearRealificationEquiv_tmul (r : ℝ) (D : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearRealificationEquiv w (r ⊗ₜ[ℚ] D) =
      r • polynomialShearMap (algebraMap ℚ ℝ) D := rfl

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] {w : σ → ℕ}

variable [Algebra ℚ R] [Algebra ℚ S]

theorem polynomialShearExp_map (f : R →+* S) (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) :
    map f (polynomialShearExp D P) = polynomialShearExp (polynomialShearMap f D) (map f P) := by
  have hp : P ∈ weightedSupportLE w (P.weightedTotalDegree w) :=
    (mem_weightedSupportLE_iff w _ P).mpr le_rfl
  rw [polynomialShearExp_eq_sum D hp,
    polynomialShearExp_eq_sum (polynomialShearMap f D) (weightedSupportLE_map f hp), map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_rat_smul, polynomialShearMap_pow_apply]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

theorem polynomialShearRealAutEquiv_rational (s : ℕ) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).Group) (P : MvPolynomial σ ℚ) :
    (polynomialShearRealAutEquiv w s hw (NilpotentLieBCHGroup.realificationHom g)).val
        (MvPolynomial.map (algebraMap ℚ ℝ) P) =
      MvPolynomial.map (algebraMap ℚ ℝ) ((polynomialShearBCHEquiv w s hw g).val P) := by
  change polynomialShearExp (polynomialShearRealificationEquiv w ((1 : ℝ) ⊗ₜ[ℚ] g.coord))
      (MvPolynomial.map (algebraMap ℚ ℝ) P) =
    MvPolynomial.map (algebraMap ℚ ℝ) (polynomialShearExp g.coord P)
  rw [polynomialShearRealificationEquiv_tmul, one_smul]
  exact (polynomialShearExp_map (algebraMap ℚ ℝ) g.coord P).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

theorem weightedShearRealEmbedding_injective (w : σ → ℕ) (d : ℕ) :
    Function.Injective (realificationLieHom (weightedShearEmbedding w d)) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
    (weightedShearEmbedding w d).toLinearMap (weightedShearEmbedding_injective w d)

theorem weightedShearRealGroupHom_injective (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    Function.Injective (weightedShearRealGroupHom w d hw) := by
  intro g h heq
  apply NilpotentLieBCHGroup.ext
  apply weightedShearRealEmbedding_injective w d
  have hh := (polynomialShearRealAutEquiv _ d (shearWeight_le w d hw)).injective heq
  exact congrArg NilpotentLieBCHGroup.coord hh

theorem weightedShearRealGroupHom_rational (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, w i ≤ d) (g : (weightedFiltration w d hw).Group)
    (P : MvPolynomial (σ ⊕ Unit) ℚ) :
    (weightedShearRealGroupHom w d hw (NilpotentLieBCHGroup.realificationHom g)).val
      (MvPolynomial.map (algebraMap ℚ ℝ) P) =
    MvPolynomial.map (algebraMap ℚ ℝ) ((weightedShearGroupHom w d hw g).val P) := by
  exact polynomialShearRealAutEquiv_rational (shearWeight w d) d
    (shearWeight_le w d hw) (NilpotentLieBCHGroup.map (weightedShearEmbedding w d) g) P

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

theorem realShearEmbedding_shape (w : σ → ℕ) (d : ℕ)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) :
    ∃ b : σ → ℝ, ∃ P : MvPolynomial σ ℝ,
      (∀ i, (realShearEmbedding w d x).val (X (Sum.inl i)) = C (b i)) ∧
      (realShearEmbedding w d x).val (X (Sum.inr ())) = rename Sum.inl P := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, ZeroMemClass.coe_zero]
    first
      | exact ⟨fun _ => 0, 0, fun _ => by simp, by simp⟩
      | (simp; exact ⟨⟨0, fun _ => by simp⟩, 0, by simp⟩)
  | tmul r x =>
      refine ⟨fun i => r * (x.val.base i : ℝ),
        r • MvPolynomial.map (algebraMap ℚ ℝ) x.val.polynomial, ?_, ?_⟩
      · intro i
        rw [realShearEmbedding_tmul]
        change r • (polynomialShearMap (algebraMap ℚ ℝ)
          (weightedShearEmbedding w d x)).val (X (Sum.inl i)) = _
        rw [polynomialShearMap_X]
        change r • MvPolynomial.map (algebraMap ℚ ℝ)
          (x.val.shearDerivation (X (Sum.inl i))) = _
        rw [shearDerivation_X_inl, map_C]
        simp [Algebra.smul_def]
      · rw [realShearEmbedding_tmul]
        change r • (polynomialShearMap (algebraMap ℚ ℝ)
          (weightedShearEmbedding w d x)).val (X (Sum.inr ())) = _
        rw [polynomialShearMap_X]
        change r • MvPolynomial.map (algebraMap ℚ ℝ)
          (x.val.shearDerivation (X (Sum.inr ()))) = _
        rw [shearDerivation_X_inr]
        simp [MvPolynomial.map_rename]
  | add x y hx hy =>
      obtain ⟨bx, Px, hbx, hPx⟩ := hx
      obtain ⟨by', Py, hby, hPy⟩ := hy
      refine ⟨bx + by', Px + Py, ?_, ?_⟩
      · intro i
        rw [map_add]
        change (realShearEmbedding w d x).val (X (Sum.inl i)) +
          (realShearEmbedding w d y).val (X (Sum.inl i)) = _
        rw [hbx, hby]
        simp
      · rw [map_add]
        change (realShearEmbedding w d x).val (X (Sum.inr ())) +
          (realShearEmbedding w d y).val (X (Sum.inr ())) = _
        rw [hPx, hPy, map_add]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem shearDerivation_pow_X_inr (x : PolynomialTranslationLie σ) (n : ℕ) :
    (x.shearDerivation.toLinearMap ^ (n+1)) (X (Sum.inr ())) =
      rename Sum.inl ((scalarDirectionalDerivative x.base).toLinearMap ^ n $ x.polynomial) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      change shearDerivation x (rename Sum.inl _) = _
      rw [shearDerivation_rename, pow_succ', Module.End.mul_apply]
      rfl

omit [Fintype σ] in
theorem shearDerivation_pow_X_inl (x : PolynomialTranslationLie σ) (n : ℕ) (i : σ) :
    (x.shearDerivation.toLinearMap ^ (n+2)) (X (Sum.inl i)) = 0 := by
  induction n with
  | zero =>
      rw [show 0+2=1+1 by omega, pow_succ', Module.End.mul_apply]
      simp [MvPolynomial.derivation_C]
  | succ n ih =>
      rw [show n+1+2=(n+2)+1 by omega, pow_succ', Module.End.mul_apply, ih, map_zero]

theorem weightedShearExp_X_inr (w : σ → ℕ) (d : ℕ)
    (x : weightedSubalgebra w d) (N : ℕ) (hN : d ≤ N) :
    (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inr ())) =
      X (Sum.inr ()) + rename Sum.inl
        (∑ k ∈ Finset.range N, ((k+1).factorial : ℚ)⁻¹ •
          ((scalarDirectionalDerivative x.val.base).toLinearMap ^ k) x.val.polynomial) := by
  rw [polynomialShearExpAut_apply,
    polynomialShearExp_eq_sum _ (weightedSupportLE_mono hN
      (weightedSupportLE_X (shearWeight w d) (Sum.inr ()))), Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    Module.End.one_apply, one_smul, map_sum, map_smul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact shearDerivation_pow_X_inr x.val k

theorem weightedShearExp_X_inl (w : σ → ℕ) (d : ℕ)
    (x : weightedSubalgebra w d) (i : σ) :
    (polynomialShearExpAut (weightedShearEmbedding w d x)).val (X (Sum.inl i)) =
      X (Sum.inl i) + C (x.val.base i) := by
  rw [polynomialShearExpAut_apply,
    polynomialShearExp_eq_sum _ (weightedSupportLE_mono (Nat.le_add_right (w i) 2)
      (weightedSupportLE_X (shearWeight w d) (Sum.inl i))),
    Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∑ k ∈ Finset.range (w i + 1),
      ((k+1+1).factorial : ℚ)⁻¹ •
      ((weightedShearEmbedding w d x).val.toLinearMap ^ (k+1+1)) (X (Sum.inl i)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    change ((k+1+1).factorial : ℚ)⁻¹ •
      (x.val.shearDerivation.toLinearMap ^ (k+2)) (X (Sum.inl i)) = 0
    rw [shearDerivation_pow_X_inl, smul_zero]
  rw [hz]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, pow_zero,
    pow_one, Module.End.one_apply, one_smul, zero_add]
  change x.val.shearDerivation (X (Sum.inl i)) + X (Sum.inl i) = _
  rw [shearDerivation_X_inl, add_comm]

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ]

theorem weightedFiltration_layer_eq_span (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (j : ℕ) :
    (weightedFiltration w d hwd).layer j =
      Submodule.span ℚ (weightedBasis w d hw '' {i | j ≤ weightedBasisGrade w d i}) := by
  ext x
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx a ha
    change (∀ i, w i < j → x.val.base i = 0) ∧
      x.val.polynomial ∈ weightedSupportDrop w d j at hx
    cases a with
    | inl i =>
        rw [weightedBasis_repr_inl]
        exact hx.1 i (by change ¬ j ≤ w i at ha; omega)
    | inr a =>
        rw [weightedBasis_repr_inr]
        by_contra hne
        have hh := hx.2 (MvPolynomial.mem_support_iff.mpr hne)
        change Finsupp.weight w a.val + j ≤ d at hh
        change ¬ j ≤ d - Finsupp.weight w a.val at ha
        omega
  · intro hx
    change (∀ i, w i < j → x.val.base i = 0) ∧
      x.val.polynomial ∈ weightedSupportDrop w d j
    constructor
    · intro i hi
      exact (weightedBasis_repr_inl w d hw x i) ▸ hx (Sum.inl i) (by
        change ¬ j ≤ w i
        omega)
    · intro a ha
      have hb := x.property.2 ha
      change Finsupp.weight w a + 1 ≤ d at hb
      change Finsupp.weight w a + j ≤ d
      by_contra hnot
      have haLT : Finsupp.weight w a < d := by omega
      have hh := hx (Sum.inr ⟨a, haLT⟩) (by
        change ¬ j ≤ d - Finsupp.weight w a
        omega)
      rw [weightedBasis_repr_inr] at hh
      exact (MvPolynomial.mem_support_iff.mp ha) hh

theorem weightedBasisIndex_finite (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) :
    Finite (WeightedBasisIndex w d) := by
  let : Finite {a : σ →₀ ℕ | Finsupp.weight w a < d} :=
    (Finsupp.finite_of_nat_weight_lt w (fun i => (hw i).ne') d).to_subtype
  infer_instance

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem degreeLE_dehomogenize {K W : Type*} [AddCommGroup W] [Module ℝ W]
    {h : ℕ} {p : VectorPolynomial (Option K) ℝ W}
    (hp : DegreeLE (1 : Option K → ℕ) h p) :
    DegreeLE (1 : K → ℕ) h (substitute dehomogenizingSubstitution p) := by
  apply degreeLE_substitute_affine _ _ p hp
  intro k
  cases k <;> simp [dehomogenizingSubstitution]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineSampleCoefficientTorus {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (b : Option K → I → ℝ) : CoefficientTorus (K := K) U :=
  QuotientAddGroup.mk' (coefficientIntegerLattice U) (affineSampleCoefficientArray U p hm b)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def realificationLieSubalgebra (K : LieSubalgebra ℚ L) :
    LieSubalgebra ℝ (ℝ ⊗[ℚ] L) := (realificationLieHom K.incl).range

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (f : L →ₗ⁅ℚ⁆ M) (hf : ∀ j, ∀ x ∈ F.layer j, f x ∈ G.layer j)
  (w : σ → ℕ)

theorem filteredPolynomialMap_surjective
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, f x = y) :
    Function.Surjective (F.filteredPolynomialMap G f hf w) := by
  classical
  intro q
  let v (α : σ →₀ ℕ) : L := if coefficients q.val α = 0 then 0 else
    Classical.choose (hsurj (Finsupp.weight w α) (coefficients q.val α) (q.property α))
  have hv (α : σ →₀ ℕ) : f (v α) = coefficients q.val α := by
    dsimp only [v]
    split_ifs with hz
    · rw [map_zero, hz]
    · exact (Classical.choose_spec (hsurj _ _ (q.property α))).2
  have hmem (α : σ →₀ ℕ) : v α ∈ F.layer (Finsupp.weight w α) := by
    dsimp only [v]
    split_ifs
    · exact Submodule.zero_mem _
    · exact (Classical.choose_spec (hsurj _ _ (q.property α))).1
  let c : (σ →₀ ℕ) →₀ L := Finsupp.onFinset (coefficients q.val).support v (by
    intro α hα
    apply Finsupp.mem_support_iff.mpr
    intro hz
    exact hα (by simp only [v, hz, ite_true]))
  let p : F.adaptedLieSubalgebra w := ⟨coefficients.symm c, by
    intro α
    simpa only [LinearEquiv.apply_symm_apply, c, Finsupp.onFinset_apply] using hmem α⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [F.filteredPolynomialMap_coefficient G f hf w]
  simpa only [p, LinearEquiv.apply_symm_apply, c, Finsupp.onFinset_apply] using hv α

theorem filteredPolynomialSymbolMap_surjective
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, f x = y) :
    Function.Surjective (F.filteredPolynomialSymbolMap G f hf w) := by
  intro y
  obtain ⟨q, rfl⟩ := G.polynomialSymbolMap_surjective w y
  obtain ⟨p, rfl⟩ := F.filteredPolynomialMap_surjective G f hf w hsurj q
  exact ⟨F.polynomialSymbolMap w p, rfl⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem stepOne_lie_eq_zero (F : NilpotentLieFiltration L 1) (a b : L) : ⁅a, b⁆ = 0 := by
  have ha : a ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hb : b ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have h := F.lie_mem ha hb
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem stepOne_coord_mul (F : NilpotentLieFiltration L 1) (a b : F.Group) :
    (a * b).coord = a.coord + b.coord :=
  lieBCH_eq_add_of_lie_eq_zero F.lowerCentralSeries_eq_bot (F.stepOne_lie_eq_zero a.coord b.coord)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

def RealAdaptedCoefficientBound (T : σ → ℝ) (M : ℝ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) : Prop :=
  ∀ z : AdaptedBasisIndex w ω,
    |((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x z| ≤ M / monomialScale T z.val.1

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

namespace RationalFilteredNilmanifold

variable {L} {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

theorem GeometryComplexityLE.mono {p q : ℝ} (hp : D.GeometryComplexityLE p) (hpq : p ≤ q) :
    D.GeometryComplexityLE q :=
  ⟨hp.1.trans hpq, hp.2.1.trans (Real.exp_le_exp.mpr hpq),
    fun i j k => (hp.2.2.1 i j k).trans hpq,
    fun i j k => (hp.2.2.2 i j k).trans hpq⟩

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem realLattice_closed_discrete :
    IsClosed (D.realLattice : Set D.RealGroup) ∧ IsDiscrete (D.realLattice : Set D.RealGroup) :=
  NilpotentLieBCHGroup.realification_subgroup_closed_discrete
    D.basis D.lattice D.grid D.grid_pos D.outer_grid

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

namespace Niltest

variable {D} {w : σ → ℕ}

theorem norm_eval_le (T : D.Niltest w) (x : σ → ℤ) : ‖T.eval x‖ ≤ T.normBound :=
  T.norm_le _

theorem ComplexityLE.mono {T : D.Niltest w} {p q : ℝ}
    (hp : T.ComplexityLE p) (hpq : p ≤ q) : T.ComplexityLE q :=
  ⟨GeometryComplexityLE.mono D hp.1 hpq, hp.2.trans hpq⟩

theorem observable_budget {T : D.Niltest w} {p : ℝ} (hp : T.ComplexityLE p) :
    2 + (T.normBound : ℝ) + (T.lipBound : ℝ) ≤ Real.exp p := by
  have hpos : 0 < 2 + (T.normBound : ℝ) + (T.lipBound : ℝ) := by positivity
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hp.2

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

namespace MultidegreeStructure

variable {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem ComplexityLE.mono {p q : ℝ} (hM : M.ComplexityLE p) (hpq : p ≤ q) : M.ComplexityLE q :=
  ⟨hM.1.mono D hpq, fun a j k => (hM.2 a j k).trans hpq⟩

noncomputable def realSubgroup (a : σ → ℕ) : Subgroup D.RealGroup := M.filtration.realification.subgroup a

end MultidegreeStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def replicatedLiePermute (e : ReplicatedPermutation bound) :
    F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) ≃ₗ⁅ℚ⁆
      F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) :=
  F.squarefreeBlockPermute _ (replicatedPermutation bound e) (replicatedPermutation_block bound e)

theorem replicatedLiePermute_one (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedLiePermute 1 x = x := by
  unfold replicatedLiePermute
  simp only [replicatedPermutation_one]
  exact F.squarefreeBlockPermute_one _ x

theorem replicatedLiePermute_mul (e f : ReplicatedPermutation bound)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedLiePermute (e * f) x = F.replicatedLiePermute e (F.replicatedLiePermute f x) := by
  apply Subtype.ext
  change squarefreePermute (replicatedPermutation bound (e * f)) x.val =
    squarefreePermute (replicatedPermutation bound e)
      (squarefreePermute (replicatedPermutation bound f) x.val)
  rw [replicatedPermutation_mul, squarefreePermute_mul]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3

theorem rationalLogHeight_le_iff (q : ℚ) (p : ℝ) :
    rationalLogHeight q ≤ p ↔
      (q.num.natAbs : ℝ) ≤ Real.exp p ∧ (q.den : ℝ) ≤ Real.exp p := by
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [rationalLogHeight, Real.log_le_iff_le_exp (lt_of_lt_of_le hd (le_max_right _ _)), max_le_iff]

theorem rationalHeightLE_ceil_exp {q : ℚ} {p : ℝ} (h : rationalLogHeight q ≤ p) :
    RationalHeightLE q ⌈Real.exp p⌉₊ := by
  obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff q p).mp h
  exact ⟨Nat.cast_le.mp (hn.trans (Nat.le_ceil _)), Nat.cast_le.mp (hd.trans (Nat.le_ceil _))⟩

theorem rationalLogHeight_le_of_height {q : ℚ} {H : ℕ} {p : ℝ}
    (hq : RationalHeightLE q H) (hH : (H : ℝ) ≤ Real.exp p) :
    rationalLogHeight q ≤ p :=
  (rationalLogHeight_le_iff q p).mpr
    ⟨(Nat.cast_le.mpr hq.1).trans hH, (Nat.cast_le.mpr hq.2).trans hH⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {τ : Type*} [Fintype τ] (w : τ → ℕ)

theorem polynomialShearRealificationEquiv_repr (D : ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) :
    (polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w D) =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr D := by
  have he : polynomialShearRealificationEquiv w D = polynomialShearRealificationLinearEquiv w D :=
    DFunLike.congr_fun (polynomialShearRealificationMap_eq w) D
  rw [he]
  change (polynomialShearBasis (R := ℝ) w).repr
    ((polynomialShearBasis (R := ℝ) w).repr.symm
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr D)) = _
  exact LinearEquiv.apply_symm_apply _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

theorem polynomialShearExp_sub_mass (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hD : ∀ i, realPolynomialMass (D.val (X i)) ≤ A * δ)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    realPolynomialMass (polynomialShearExp D P - P) ≤
      n * δ * (1 + Fintype.card σ * A * n) ^ n * realPolynomialMass P := by
  classical
  let B : ℝ := Fintype.card σ * A * n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpow (k : ℕ) (hk : k < n) :
      realPolynomialMass ((D.val.toLinearMap ^ (k + 1)) P) ≤
        δ * (1 + B) ^ n * realPolynomialMass P := by
    have hmass := polynomialShear_pow_mass D hpos (mul_nonneg hA hδ) hD hP (k + 1)
    have he : (Fintype.card σ : ℝ) * (A * δ) * n = B * δ := by dsimp [B]; ring
    rw [he, mul_pow] at hmass
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ (realPolynomialMass_nonneg P)
    have hd : δ ^ (k + 1) ≤ δ := by
      rw [pow_succ]
      exact mul_le_of_le_one_left hδ (pow_le_one₀ hδ hδone)
    have hb : B ^ (k + 1) ≤ (1 + B) ^ n :=
      (pow_le_pow_left₀ hB (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    calc
      _ ≤ (1 + B) ^ n * δ := mul_le_mul hb hd (pow_nonneg hδ _) (by positivity)
      _ = _ := mul_comm _ _
  rw [polynomialShearExp_eq_sum D hP, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply,
    one_smul, add_sub_cancel_right]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range n, δ * (1 + B) ^ n * realPolynomialMass P := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← Rat.cast_smul_eq_qsmul ℝ, realPolynomialMass_smul]
      simp only [Rat.cast_inv, Rat.cast_natCast]
      have hf : (1 : ℝ) ≤ (k + 1).factorial := by exact_mod_cast Nat.factorial_pos (k + 1)
      have hc : |((k + 1).factorial : ℝ)⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
        exact inv_le_one_of_one_le₀ hf
      calc
        _ ≤ 1 * realPolynomialMass ((D.val.toLinearMap ^ (k + 1)) P) :=
          mul_le_mul_of_nonneg_right hc (realPolynomialMass_nonneg _)
        _ ≤ _ := by simpa only [one_mul] using hpow k (Finset.mem_range.mp hk)
    _ = _ := by simp [B]; ring

theorem polynomialShearExp_displacement (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {A δ B : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hδone : δ ≤ 1) (hB : 1 ≤ B)
    (hD : ∀ i, realPolynomialMass (D.val (X i)) ≤ A * δ)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) :
    |aeval x (polynomialShearExp D P) - aeval x P| ≤
      n * δ * (1 + Fintype.card σ * A * n) ^ n * realPolynomialMass P * B ^ n := by
  rw [← map_sub]
  have hdegree := totalDegree_le_of_positive_weightedSupport w hpos
    ((weightedSupportLE w n).sub_mem (polynomialShearExp_degree D hP) hP)
  exact (abs_aeval_le_mass_box _ x hB hx hdegree).trans
    (mul_le_mul_of_nonneg_right (polynomialShearExp_sub_mass D hpos hA hδ hδone hD hP)
      (pow_nonneg (by linarith) _))

theorem polynomialShearExp_X_displacement (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {s : ℕ} (hw : ∀ i, w i ≤ s)
    {δ B : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hB : 1 ≤ B)
    (hD : ∀ a, |(polynomialShearBasis (R := ℝ) w).repr D a| ≤ δ)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ B) (i : σ) :
    |aeval x (polynomialShearExp D (X i)) - x i| ≤
      s * δ * (1 + Fintype.card σ * ((s + 1) * (Fintype.card σ + 1) ^ s : ℕ) * s) ^ s * B ^ s := by
  have h := polynomialShearExp_displacement D hpos (by positivity) hδ hδone hB
    (polynomialShear_X_mass_of_coordinates D hpos hw hδ hD)
    (weightedSupportLE_mono (hw i) (weightedSupportLE_X w i)) x hx
  simpa only [aeval_X, realPolynomialMass_X, mul_one] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def relativePatchComplexity {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : ℝ :=
  (d : ℝ) + Real.log (1 + (A.kernel.lip : ℝ))

noncomputable def relativePatchSliceScore {X : Type*} [Fintype X] {s d q : ℕ}
    {N : X → ℕ} (S : ResidueBoxSlice N q) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) : ℝ :=
  𝔼 x : ∀ i, Fin (S.length i),
    (f (fun i => ((S.point x i).val : ℤ)) - a) * A.value (fun i => ((x i).val : ℝ))

def RelativePatchSliceConclusion {X : Type*} [Fintype X] (s : ℕ)
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ) (rankBound : ℕ) (cost : ℝ) : Prop :=
  ∃ (q : ℕ), 0 < q ∧ ∃ (S : ResidueBoxSlice N q) (d : ℕ)
    (A : PolynomialPatch X s d),
    (∀ i, Real.exp (-cost) * (N i : ℝ) ≤ (S.length i : ℝ)) ∧
    d ≤ rankBound ∧ relativePatchComplexity A ≤ cost ∧
    Real.exp (-cost) ≤ relativePatchSliceScore S f target A

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem relativePatchSliceScore_comp {X : Type*} [Fintype X]
    {s d q r : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    (T : ResidueBoxSlice S.length r) (f : (X → ℤ) → ℝ)
    (a : ℝ) (A : PolynomialPatch X s d) :
    relativePatchSliceScore T (S.integerPullback f) a A =
      relativePatchSliceScore (S.comp T) f a A := by
  unfold relativePatchSliceScore
  apply Finset.expect_congr rfl
  intro x _
  simp only [ResidueBoxSlice.integerPullback, ResidueBoxSlice.integerAffine_finPoint,
    ResidueBoxSlice.comp_point]

theorem RelativePatchSliceConclusion.comp {X : Type*} [Fintype X]
    {s q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q) (hq : 0 < q)
    {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound : ℕ} {u v : ℝ}
    (hu : 0 ≤ u)
    (hlength : ∀ i, Real.exp (-u) * (N i : ℝ) ≤ S.length i)
    (h : RelativePatchSliceConclusion s S.length (S.integerPullback f)
      target rankBound v) :
    RelativePatchSliceConclusion s N f target rankBound (u + v) := by
  obtain ⟨r, hr, T, d, A, hT, hd, hcomplexity, hscore⟩ := h
  refine ⟨q * r, Nat.mul_pos hq hr, S.comp T, d, A,
    S.comp_length_exp_lower T hlength hT, hd, ?_, ?_⟩
  · exact hcomplexity.trans (by linarith)
  · rw [← relativePatchSliceScore_comp]
    exact (Real.exp_le_exp.mpr (by linarith : -(u + v) ≤ -v)).trans hscore

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SectionRetainedFourier
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

noncomputable def affineCubeFourierSum {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (c : F → ℂ) (b : Option K → I → ℝ) : ℂ :=
  ∑ a, c a * layeredCoefficientCharacter
    (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ)))) p b

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneSiteCoefficientFactorization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem coefficientArray_factor_to_bounded_site {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (s₀ : S) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (M : CoefficientArray (K := Empty) U →ₗ[ℝ] ℝ)
    (hM : coefficientArrayFunctional U frequency = M.comp (coefficientEvaluationArray U t))
    (j : Fin m) :
    ∃ Mj : (S → U j) →ₗ[ℝ] ℝ,
      ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
          Mj (siteEvaluation (fun _ : S => fun k => (t k : ℝ)) p) := by
  let A : (S → U j) →ₗ[ℝ] (BoundedCoefficientExponent Empty (j.val + 1) → U j) :=
    LinearMap.pi (fun _ => LinearMap.proj s₀)
  let Mj := M.comp ((coefficientLayerInsertion U j).comp A)
  refine ⟨Mj, ?_⟩
  intro p hp
  let v : BoundedCoefficientExponent K (j.val + 1) → U j := fun d => coefficients p d.val
  have hv : boundedArrayPolynomial (j.val + 1) v = p := boundedArrayPolynomial_reconstruct p hp
  have he := DFunLike.congr_fun hM (coefficientLayerInsertion U j v)
  rw [LinearMap.comp_apply, coefficientArrayFunctional_layerInsertion,
    coefficientEvaluationArray_layerInsertion] at he
  rw [← hv, coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial]
  exact he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientFiberOrthogonality
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

theorem coefficientTorusCharacter_fiber_integrable {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => coefficientTorusCharacter U frequency (coefficientFiberMap U t y x)) μ := by
  have hc : Continuous (coefficientTorusCharacter U frequency) :=
    quotientLinearCharacter_continuous _ _ _
      (coefficientArrayFunctional U frequency).continuous_of_finiteDimensional
  apply Integrable.of_bound (hc.comp (coefficientFiberMap_continuous U t y)).aestronglyMeasurable 1
  exact ae_of_all μ (fun x => (quotientLinearCharacter_norm _ _ _ _).le)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslationShearExponentialOver
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {R σ : Type*} [CommRing R] [Algebra ℚ R]
  {w : σ ⊕ Unit → ℕ}

theorem translationShear_exp_extra_coordinate
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    ∃ Q : MvPolynomial σ R,
      polynomialShearExp D (X (Sum.inr ())) = X (Sum.inr ()) + rename Sum.inl Q := by
  classical
  let S : Submodule R (MvPolynomial (σ ⊕ Unit) R) :=
    LinearMap.range (rename (R := R) (Sum.inl : σ → σ ⊕ Unit)).toLinearMap
  have hpow (k : ℕ) : (D.val.toLinearMap ^ (k + 1)) (X (Sum.inr ())) ∈ S := by
    induction k with
    | zero => exact ⟨P, by simpa using hP.symm⟩
    | succ k ih =>
        obtain ⟨Q, hQ⟩ := ih
        obtain ⟨Q', hQ'⟩ := translationShear_derivation_rename D b hb Q
        refine ⟨Q', ?_⟩
        rw [pow_succ', Module.End.mul_apply, ← hQ]
        exact hQ'.symm
  have hmem : polynomialShearExp D (X (Sum.inr ())) - X (Sum.inr ()) ∈ S := by
    rw [polynomialShearExp_eq_sum D (weightedSupportLE_X w (Sum.inr ())),
      Finset.sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, Module.End.one_apply,
      one_smul, add_sub_cancel_right]
    apply (S.restrictScalars ℚ).sum_mem
    intro k hk
    exact (S.restrictScalars ℚ).smul_mem _ (hpow k)
  obtain ⟨Q, hQ⟩ := hmem
  refine ⟨Q, ?_⟩
  change rename Sum.inl Q = polynomialShearExp D (X (Sum.inr ())) - X (Sum.inr ()) at hQ
  rw [hQ]
  abel

theorem existsUnique_translation_of_shear_exp
    (D : PolynomialShearLieAlgebra w R) (b : σ → R) (P : MvPolynomial σ R)
    (hb : ∀ i, D.val (X (Sum.inl i)) = C (b i))
    (hP : D.val (X (Sum.inr ())) = rename Sum.inl P) :
    ∃! g : PolynomialTranslationGroupOver R σ,
      PolynomialTranslationGroupOver.actionMonoidHom g = (polynomialShearExpAut D).val := by
  obtain ⟨Q, hQ⟩ := translationShear_exp_extra_coordinate D b P hb hP
  apply PolynomialTranslationGroupOver.existsUnique_action_of_shape
    (polynomialShearExpAut D).val b Q
  · intro i
    exact polynomialShearExp_X_of_derivation_eq_C D (Sum.inl i) (b i) (hb i)
  · exact hQ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

def UnitIntervalValued (T : D.Niltest w) : Prop :=
  ∀ z, (T.observable z).im = 0 ∧ 0 ≤ (T.observable z).re ∧ (T.observable z).re ≤ 1

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realPolynomialSymbolMap_surjective :
    Function.Surjective (F.realPolynomialSymbolMap b ω hlayers w) :=
  fun x => ⟨F.realAdaptedSymbolRepresentative b ω hlayers w x,
    F.realPolynomialSymbolMap_representative b ω hlayers w x⟩

theorem realPolynomialSymbolMap_eq_zero_iff (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hlayers w p = 0 ↔
      F.realification.polynomialSymbolMap w p = 0 := by
  rw [F.realPolynomialSymbolMap_apply, F.realSymbolOfPolynomial_eq_zero_iff,
    F.realification.polynomialSymbolMap_eq_zero_iff]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

section General

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

theorem BasisHomogeneousBrackets.projection_lie (b : Basis ι R L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) {i j : ℕ} {x y : L}
    (hx : basisGradeProjection b w i x = x) (hy : basisGradeProjection b w j y = y) :
    basisGradeProjection b w (i + j) ⁅x, y⁆ = ⁅x, y⁆ := by
  apply basisCoordinateProjection_eq_self
  apply hb.lie_mem_span b w
  · rw [← hx]
    exact basisCoordinateProjection_mem_span b _ _
  · rw [← hy]
    exact basisCoordinateProjection_mem_span b _ _

end General

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ]

@[simp] theorem weightedBasis_inl_base [DecidableEq σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (i : σ) : (weightedBasis w d hw (Sum.inl i)).val.base = Pi.single i 1 := by
  classical
  unfold weightedBasis
  erw [Basis.map_apply]
  rw [Basis.prod_apply]
  simp [weightedCoordinatesEquiv]
  rfl

@[simp] theorem weightedBasis_inl_polynomial (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (i : σ) :
    (weightedBasis w d hw (Sum.inl i)).val.polynomial = 0 := by
  unfold weightedBasis
  erw [Basis.map_apply]
  rw [Basis.prod_apply]
  simp [weightedCoordinatesEquiv]
  rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalCentralCircle
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)

noncomputable def rationalDirectionPeriod (v : L) : ℕ :=
  D.grid * arrayDenominator (D.basis.equivFun v)

noncomputable def periodicRealDirection (v : L) : ℝ ⊗[ℚ] L :=
  rationalLieInclusion ((D.rationalDirectionPeriod v : ℚ) • v)

theorem periodicRealDirection_eq (v : L) :
    D.periodicRealDirection v = (D.rationalDirectionPeriod v : ℝ) • rationalLieInclusion v := by
  simp only [periodicRealDirection, Nat.cast_smul_eq_nsmul, map_nsmul]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestProbabilityProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {σ α L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def averageCircles (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α) : D.Niltest w := by
  let := D.metricSpace
  exact {
    orbit := T.orbit
    observable := iteratedCircleAverage A is T.observable
    normBound := T.normBound
    lipBound := T.lipBound
    norm_le := iteratedCircleAverage_norm_le A is T.norm_le
    lipschitz := iteratedCircleAverage_lipschitz A is T.lipschitz }

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MajorTranslationPureFactorValues
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped TensorProduct

theorem translationShear_derivation_rename_eq_zero
    {σ : Type*} {w : σ ⊕ Unit → ℕ}
    (D : PolynomialShearLieAlgebra w ℝ)
    (hD : ∀ i, D.val (X (Sum.inl i)) = 0) (P : MvPolynomial σ ℝ) :
    D.val (rename Sum.inl P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]
  | mul_X P i hP =>
    simp only [map_mul, rename_X, D.val.leibniz, hD, hP, smul_zero, add_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneSiteResidualFactor
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem coefficientResidualFunctional_eq_zero_iff_oneSite {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    coefficientResidualFunctional U t frequency = 0 ↔
      affineCubeModeFactors U t difference frequency := by
  change (coefficientArrayFunctional U frequency).comp (coefficientResidualArray U t) = 0 ↔ _
  rw [coefficientResidualArray_factor_iff]
  have hsite : (fun s : Finset (Fin 0) => affineSite (fun k => (t k : ℝ))
      (fun i k => (difference i k : ℝ)) s) =
      (fun (_s : Finset (Fin 0)) (k : Option K) => k.elim (1 : ℝ) (fun k => (t k : ℝ))) := by
    funext s k
    have hs : s = ∅ := Subsingleton.elim _ _
    subst s
    cases k <;> simp [affineSite]
  constructor
  · rintro ⟨M, hM⟩ j
    obtain ⟨Mj, hMj⟩ := coefficientArray_factor_to_bounded_site U t (∅ : Finset (Fin 0)) frequency M hM j
    refine ⟨Mj, ?_⟩
    let L := (coefficientFunctional (fun d a => (frequency j d a : ℝ))).comp (map (U j).subtype)
    have hb : ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
        L p = Mj (VectorPolynomial.siteEvaluation (fun _ : Finset (Fin 0) => fun k => (t k : ℝ)) p) := hMj
    have hh := (homogeneous_site_factorization_iff (j.val + 1)
      (fun _ : Finset (Fin 0) => fun k => (t k : ℝ)) L Mj).mpr hb
    change ∀ p, Homogeneous (j.val + 1) p → affineModeLift L p = _ at hh
    simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply, hsite] using hh
  · intro hf
    apply coefficientArray_factor_of_bounded_site (S := Finset (Fin 0)) U t frequency
    intro j
    obtain ⟨Mj, hMj⟩ := affineCubeModeFactors_bounded U t difference frequency hf j
    refine ⟨Mj, ?_⟩
    have he : (fun (s : Finset (Fin 0)) k => ((affineSite t difference s (some k) : ℤ) : ℝ)) =
        (fun (_s : Finset (Fin 0)) k => (t k : ℝ)) := by
      funext s k
      have hs : s = ∅ := Subsingleton.elim _ _
      subst s
      simp [affineSite]
    simpa only [he] using hMj

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem realProductSingle_projection (i : ι) (x : ℝ ⊗[ℚ] L i) :
    realificationLieHom (liePiEval i) (realProductSingle i x) = x := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    change r ⊗ₜ[ℚ] (Pi.single i x i) = r ⊗ₜ[ℚ] x
    rw [Pi.single_eq_same]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realProductSingle_projection_ne {i j : ι} (hij : j ≠ i) (x : ℝ ⊗[ℚ] L i) :
    realificationLieHom (liePiEval j) (realProductSingle i x) = 0 := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    change r ⊗ₜ[ℚ] (Pi.single i x j) = 0
    rw [Pi.single_eq_of_ne hij, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeWeightedNilpotentLieAlgebra
namespace OAI

section

namespace Erdos3

namespace FreeWeightedNilpotentLieAlgebra

variable (X : Type*) (s : ℕ) (w : X → ℕ)

noncomputable def filtration (hw : ∀ i, 0 < w i) :
    NilpotentLieFiltration (FreeWeightedNilpotentLieAlgebra X s w) s where
  layer d := (FreeNilpotentLieAlgebra.weightedLayer X s w d).map (mk X s w).toLinearMap
  antitone := fun _ _ h => Submodule.map_mono (FreeNilpotentLieAlgebra.weightedLayer_antitone X s w h)
  one_eq_top := by
    rw [FreeNilpotentLieAlgebra.weightedLayer_one X s w hw, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (mk_surjective X s w)
  lie_mem := by
    rintro d e x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨⁅a, b⁆, FreeNilpotentLieAlgebra.weightedLayer_lie_mem X s w ha hb, (mk X s w).map_lie a b⟩
  terminal := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (mk_eq_zero X s w a).mpr ha

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module

variable {ν L : Type*} [AddCommGroup L] [Module ℚ L] [FiniteDimensional ℚ L]
  (e : Basis ν ℚ L) (H : ℕ)

noncomputable def chosenBoundedSubmoduleBasis (U : Submodule ℚ L) :
    Basis (Fin (finrank ℚ U)) ℚ U := by
  classical
  exact if h : ∃ b : Basis (Fin (finrank ℚ U)) ℚ U,
      ∀ j k, RationalHeightLE (e.repr (b j).val k) H then h.choose else Module.finBasis ℚ U

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AdaptedBasisNilmanifold
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

noncomputable def adaptedLayerBasis (j : ℕ) :
    Basis (Fin (finrank ℚ (F.layer j))) ℚ (F.layer j) := by
  classical
  let c := supportedSubmoduleBasis b (F.layer j) {i | j ≤ w i} (hlayers j)
  exact c.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis c).symm)

noncomputable def ofAdaptedBasis (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    RationalFilteredNilmanifold L s d where
  filtration := F
  basis := b
  layerBasis i := F.adaptedLayerBasis b w hlayers (i.val + 1)
  lattice := Γ
  grid := N
  grid_pos := hN
  inner_grid := hin
  outer_grid := hout

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SupportedQuotientExactGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

theorem quotientStep_inner_grid_supported (Γ : Subgroup F.Group) {N : ℕ}
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) :
    scaledIntegerGrid N ⊆ bchSubgroupCoordinates (supportedQuotientBasis b I.toSubmodule S hspan)
      (Γ.map (F.quotientStepHom I hI)) := by
  classical
  rintro x ⟨z, rfl⟩
  let y : ι → ℚ := fun i => if hi : i ∈ S then 0 else (N : ℚ) * (z ⟨i, hi⟩ : ℚ)
  have hy : y ∈ scaledIntegerGrid N := by
    refine ⟨fun i => if hi : i ∈ S then 0 else z ⟨i, hi⟩, ?_⟩
    funext i
    dsimp [y]
    split_ifs <;> simp
  have hg : (⟨b.equivFun.symm y⟩ : F.Group) ∈ Γ := hin hy
  apply Subgroup.mem_map.mpr
  refine ⟨⟨b.equivFun.symm y⟩, hg, ?_⟩
  apply NilpotentLieBCHGroup.ext
  apply (supportedQuotientBasis b I.toSubmodule S hspan).equivFun.injective
  funext i
  rw [LinearEquiv.apply_symm_apply]
  change (supportedQuotientBasis b I.toSubmodule S hspan).repr
    (I.toSubmodule.mkQ (b.equivFun.symm y)) i = _
  rw [supportedQuotientBasis_repr_mk, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [y, i.property, dite_false, Pi.smul_apply, smul_eq_mul]

theorem quotientStep_outer_grid_supported (Γ : Subgroup F.Group) {N : ℕ}
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    bchSubgroupCoordinates (supportedQuotientBasis b I.toSubmodule S hspan)
      (Γ.map (F.quotientStepHom I hI)) ⊆ denominatorGrid N := by
  classical
  intro x hx
  obtain ⟨g, hg, he⟩ := Subgroup.mem_map.mp hx
  have hgc : b.equivFun g.coord ∈ bchSubgroupCoordinates b Γ := by
    change (⟨b.equivFun.symm (b.equivFun g.coord)⟩ : F.Group) ∈ Γ
    simpa only [LinearEquiv.symm_apply_apply] using hg
  obtain ⟨z, hz⟩ := hout hgc
  have hxrepr (i : {i // i ∉ S}) : x i = b.equivFun g.coord i := by
    have hec := congrArg NilpotentLieBCHGroup.coord he
    have hr := congrArg (fun v => (supportedQuotientBasis b I.toSubmodule S hspan).equivFun v i) hec
    rw [LinearEquiv.apply_symm_apply] at hr
    change (supportedQuotientBasis b I.toSubmodule S hspan).repr
      (I.toSubmodule.mkQ g.coord) i = x i at hr
    rw [supportedQuotientBasis_repr_mk] at hr
    exact hr.symm
  refine ⟨fun i => z i, fun i => ?_⟩
  change (N : ℚ) * x i = (z i : ℚ)
  rw [hxrepr]
  exact hz i

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateQuotientModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

include hlayers in
theorem quotientFinBasis_layers (j : ℕ) :
    (F.quotientLie I hI).layer j = Submodule.span ℚ
      (quotientFinBasis b I S hspan '' {i | j ≤ quotientFinWeight w S i}) := by
  rw [F.supportedQuotientBasis_layers b w hlayers I hI S hspan]
  exact (basis_reindex_span_weights (L := L ⧸ I)
    (supportedQuotientBasis b I.toSubmodule S hspan) (Fintype.equivFin _)
    (fun i => w i) j).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

noncomputable def approximationComplexity (B : Set N) (rho : ℝ≥0) : ℝ :=
  max (B.rank : ℝ) (Real.log (3 + (B.approximationLipBound rho : ℝ)))

end Erdos3.CyclicBohr.Set

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.OneSiteFourierAverage
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem coefficientTorusFourierSum_fiberAverage {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (x : CoefficientTorus (K := K) U) :
    coefficientFiberAverage U μ t (coefficientTorusFourierSum U frequency c) (coefficientEvaluationTorus U t x) =
      ∑ a, if affineCubeModeFactors U t difference (frequency a) then
        c a * coefficientTorusCharacter U (frequency a) x else 0 := by
  change (∫ z, ∑ a, c a * coefficientTorusCharacter U (frequency a)
    (coefficientFiberMap U t (coefficientEvaluationTorus U t x) z) ∂μ) = _
  rw [integral_finsetSum _ (fun a _ =>
    (coefficientTorusCharacter_fiber_integrable U t (frequency a) μ _).const_mul (c a))]
  simp only [integral_const_mul]
  change (∑ a, c a * coefficientFiberAverage U μ t (coefficientTorusCharacter U (frequency a))
    (coefficientEvaluationTorus U t x)) = _
  simp only [coefficientTorusCharacter_fiberAverage_evaluation,
    coefficientResidualFunctional_eq_zero_iff_oneSite U t difference, mul_ite, mul_zero]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedTranslationIntegralCoordinates
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]
variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)

theorem weightedShearEmbedding_integral_iff (x : weightedSubalgebra w d) :
    (∀ i, (weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit)) ↔
    (∀ i, ∃ z : ℤ, x.val.base i = (z : ℚ)) ∧
      x.val.polynomial ∈ integerCoefficientPolynomials σ := by
  have hgen (i : σ ⊕ Unit) : (weightedShearEmbedding w d x).val (X i) =
      shearDerivation x.val (X i) := rfl
  simp only [hgen]
  constructor
  · intro h
    constructor
    · intro i
      exact (integral_C_iff (τ := σ ⊕ Unit) _).mp (by simpa only [shearDerivation_X_inl] using h (Sum.inl i))
    · exact (integral_rename_iff (Sum.inl : σ → σ ⊕ Unit) Sum.inl_injective _).mp (by
        simpa only [shearDerivation_X_inr] using h (Sum.inr ()))
  · rintro ⟨hb, hp⟩ i
    cases i with
    | inl i =>
        rw [shearDerivation_X_inl]
        exact (integral_C_iff _).mpr (hb i)
    | inr u =>
        rw [shearDerivation_X_inr]
        exact (integral_rename_iff Sum.inl Sum.inl_injective _).mpr hp

theorem weightedBasis_integral_iff (x : weightedSubalgebra w d) :
    (∀ i, (weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit)) ↔
      ∀ a, ∃ z : ℤ, (weightedBasis w d hw).repr x a = (z : ℚ) := by
  rw [weightedShearEmbedding_integral_iff]
  constructor
  · rintro ⟨hb, hp⟩ a
    cases a with
    | inl i => simpa only [weightedBasis_repr_inl] using hb i
    | inr a => exact (mem_integerCoefficientPolynomials_iff _).mp hp a.val
  · intro h
    constructor
    · intro i
      simpa only [weightedBasis_repr_inl] using h (Sum.inl i)
    · apply (mem_integerCoefficientPolynomials_iff _).mpr
      intro a
      by_cases ha : Finsupp.weight w a < d
      · exact h (Sum.inr ⟨a, ha⟩)
      · refine ⟨0, ?_⟩
        apply not_ne_iff.mp
        intro hc
        have hs := x.property.2 (MvPolynomial.mem_support_iff.mpr hc)
        change Finsupp.weight w a + 1 ≤ d at hs
        omega

variable [Finite (WeightedBasisIndex w d)]

theorem weightedBasis_integralVector_iff (x : weightedSubalgebra w d) :
    (∀ i, (weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit)) ↔
      IntegralVector ((weightedBasis w d hw).equivFun x) := by
  rw [weightedBasis_integral_iff w d hw]
  constructor
  · intro h
    choose z hz using h
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩ a
    exact ⟨z a, hz a⟩

theorem weightedBasis_denominatorGrid_iff (B : ℕ) (x : weightedSubalgebra w d) :
    (weightedBasis w d hw).equivFun x ∈ denominatorGrid B ↔
      ∀ i, ((B : ℚ) • weightedShearEmbedding w d x).val (X i) ∈
        integerCoefficientPolynomials (σ ⊕ Unit) := by
  change IntegralVector ((B : ℚ) • (weightedBasis w d hw).equivFun x) ↔ _
  rw [← map_smul]
  simpa only [map_smul] using (weightedBasis_integralVector_iff w d hw ((B : ℚ) • x)).symm

theorem weightedBasis_scaledGrid_normalize (B : ℕ) (hB : 0 < B)
    (x : weightedSubalgebra w d)
    (hx : (weightedBasis w d hw).equivFun x ∈ scaledIntegerGrid B) :
    ∀ i, ((B : ℚ)⁻¹ • weightedShearEmbedding w d x).val (X i) ∈
      integerCoefficientPolynomials (σ ⊕ Unit) := by
  obtain ⟨z, hz⟩ := hx
  have hBq : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
  have hi : IntegralVector ((weightedBasis w d hw).equivFun ((B : ℚ)⁻¹ • x)) := by
    refine ⟨z, ?_⟩
    have hv : (weightedBasis w d hw).equivFun ((B : ℚ)⁻¹ • x) =
        fun i => (z i : ℚ) := by
      rw [map_smul, hz, smul_smul, inv_mul_cancel₀ hBq, one_smul]
    exact congrFun hv
  simpa only [map_smul] using (weightedBasis_integralVector_iff w d hw _).mpr hi

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedTranslationBufferedCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem realificationLieHom_repr_zero (e : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (k : κ) (h : ∀ x, e.repr (φ x) k = 0) (x : ℝ ⊗[ℚ] L) :
    (e.baseChange ℝ).repr (realificationLieHom φ x) k = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul, h, zero_smul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]

theorem realificationLieHom_repr_coordinate (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (k : κ) (i : ι)
    (h : ∀ x, f.repr (φ x) k = e.repr x i) (x : ℝ ⊗[ℚ] L) :
    (f.baseChange ℝ).repr (realificationLieHom φ x) k = (e.baseChange ℝ).repr x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realificationLieHom_tmul, Basis.baseChange_repr_tmul, h]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisFamilyLogHeight
namespace OAI

section

namespace Erdos3

def BasisFamilyLogHeight {ι κ V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Module.Basis ι ℚ V) (v : κ → V) (p : ℝ) : Prop :=
  ∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHProductEquiv
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

theorem realification_piRight_apply (x : ℝ ⊗[ℚ] (∀ i, L i)) (i : ι) :
    TensorProduct.piRight ℚ ℝ ℝ L x i = realificationLieHom (liePiEval i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

noncomputable def realBCHPiEquiv (F : ∀ i, NilpotentLieFiltration (L i) s) :
    (NilpotentLieFiltration.pi F).realification.Group ≃* (∀ i, (F i).realification.Group) where
  toFun g i := realificationMap (hnil := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot)
    (hM := (F i).lowerCentralSeries_eq_bot) (liePiEval i) g
  invFun g := ⟨(TensorProduct.piRight ℚ ℝ ℝ L).symm (fun i => (g i).coord)⟩
  left_inv g := by
    apply NilpotentLieBCHGroup.ext
    change (TensorProduct.piRight ℚ ℝ ℝ L).symm
      (fun i => realificationLieHom (liePiEval i) g.coord) = g.coord
    have h : (fun i => realificationLieHom (liePiEval i) g.coord) =
        TensorProduct.piRight ℚ ℝ ℝ L g.coord := funext (fun i => (realification_piRight_apply g.coord i).symm)
    rw [h, LinearEquiv.symm_apply_apply]
  right_inv g := by
    funext i
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom (liePiEval i)
      ((TensorProduct.piRight ℚ ℝ ℝ L).symm (fun i => (g i).coord)) = (g i).coord
    rw [← realification_piRight_apply, LinearEquiv.apply_symm_apply]
  map_mul' g h := by
    funext i
    exact (realificationMap (hnil := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot)
      (hM := (F i).lowerCentralSeries_eq_bot) (liePiEval i)).map_mul g h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPositivePolynomialEvaluation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialAlgebra : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | F.Adapted p ∧ coefficients p 0 = 0}
  zero_mem' := by constructor <;> simp [Adapted]
  add_mem' hp hq := ⟨F.adaptedSubmodule.add_mem hp.1 hq.1, by simp [hp.2, hq.2]⟩
  smul_mem' c p hp := ⟨F.adaptedSubmodule.smul_mem c hp.1, by simp [hp.2]⟩
  lie_mem' hp hq := by
    refine ⟨F.lie_mem_adaptedSubmodule hp.1 hq.1, ?_⟩
    rw [← eval_zero_eq_coefficient]
    change evalLie (fun _ : σ => (0 : ℚ)) ⁅_, _⁆ = 0
    rw [LieHom.map_lie]
    simp only [evalLie_apply, eval_zero_eq_coefficient, hp.2, zero_lie]

@[simp] theorem mem_positivePolynomialAlgebra (p : VectorPolynomial σ ℚ L) :
    p ∈ F.positivePolynomialAlgebra ↔ F.Adapted p ∧ coefficients p 0 = 0 := Iff.rfl

@[simp] theorem positivePolynomial_constant (p : F.positivePolynomialAlgebra) :
    coefficients p.val 0 = 0 := p.property.2

end Erdos3.MultidegreeLieFiltration

end

end OAI
end


