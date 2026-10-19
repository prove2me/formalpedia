-- Prove2me | Definitions.Def_OAIE3v2B027
-- name    : OAIE3v2B027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:14.223976+00:00
-- url     : https://prove2.me/theorems/66a3b5ed-744c-4d92-9cbd-858639a9acf1
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 28 of 311
-- statement:
--   Definitions bundle 28 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/ModeThresholdLogBudget.lean`, `Dynamics/RealProjectedPotentialGroupIdentity.lean`, `Dynamics/TranslationMajorDetectedPotential.lean`, `Dynamics/TranslationMajorDetectedPotentialBudget.lean`, `Dynamics/TranslationMajorDimensionBudget.lean`, `Estimates/AllocatedCandidateCommonFastGeometry.lean`, `Estimates/DependentPatchValue.lean`, `Estimates/FiniteFiberRepresentatives.lean`, `Estimates/LinearRestrictionHeight.lean`, `Estimates/MajorRationalLiftInputScale.lean`, `Estimates/NormalizedTwistParameterPartition.lean`, `Estimates/RealifiedReconstruction.lean`, `Estimates/TriangularCorrectionRows.lean`, `Estimates/VectorAlgebraicMajorDecomposition.lean`, `Estimates/WeightedAxisScaling.lean`, `Estimates/WeightedPlateauSiteApproximation.lean`, `Fourier/NormalizedTwistLocalizedFourierSelection.lean`, `Fourier/RationalLiftCharacterTwist.lean`, `Geometry/CommonRefilteredFactorsSymbolTransport.lean`, `Geometry/ControlledGradedBaseCoordinates.lean`, `Geometry/FiniteNormalizedChartCorrection.lean`, `Geometry/FullTaggedChartCoefficientRange.lean`, `Geometry/TranslationLogCoordinateInputBounds.lean`, `Geometry/TranslationShearCoordinateSeries.lean`, `Lattices/AlgebraicMajorIntegerRestoration.lean`, `Linear/FiniteDescendingRankOrder.lean`, `Linear/FiniteRankTriangularFinset.lean`, `Linear/RealCoordinateImageSpan.lean`, `Nilpotent/LocalMajorDenseSliceNiltest.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/MajorPhaseCoordinateDenominator.lean`, `Polynomial/MajorTranslationPolynomialSymbolDegree.lean`, `Polynomial/PolynomialCoefficientGridDenominator.lean`, `Polynomial/PolynomialDerivativeSeparation.lean`, `Polynomial/PolynomialParameterContinuity.lean`, `Polynomial/PolynomialTagRestrictionBudget.lean`, `Polynomial/TranslationParameterPolynomialPacking.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Polynomial/TranslationPolynomialPackingDerivative.lean`, `Polynomial/WeightedPolynomialPotential.lean`, `Polynomial/WeightedPolynomialPotentialExtension.lean`, `Probability/RealificationRationalDensity.lean`, `Sampling/BoundedKernelGridEnumerationBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalLiftCharacterTwist
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {m : ℕ}

noncomputable def rationalLiftCharacterTwist (M : ℕ) (a : Fin m → ℤ) (c : Fin m → ℝ)
    (y : Fin m → ℝ) (r : Fin m → ZMod M) : ℂ :=
  Real.fourierChar ((∑ i, (a i : ℝ) * (y i + (r i).val + c i)) / (M : ℝ))

noncomputable def rationalLiftCharacterTwistLip (M : ℕ) (a : Fin m → ℤ) : ℝ≥0 :=
  ⟨2 * Real.pi * (∑ i, |(a i : ℝ)|) / (M : ℝ), by positivity⟩

theorem rationalLiftCharacterTwist_norm (M : ℕ) (a : Fin m → ℤ) (c y : Fin m → ℝ)
    (r : Fin m → ZMod M) : ‖rationalLiftCharacterTwist M a c y r‖ = 1 :=
  Circle.norm_coe _

theorem rationalLiftCharacterTwistLip_le (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ)
    (A : ℝ) (ha : ∀ i, |(a i : ℝ)| ≤ A) :
    (rationalLiftCharacterTwistLip M a : ℝ) ≤ 2 * Real.pi * m * A := by
  have hs : (∑ i, |(a i : ℝ)|) ≤ (m : ℝ) * A := by
    calc
      _ ≤ ∑ _i : Fin m, A := Finset.sum_le_sum (fun i _ => ha i)
      _ = _ := by simp
  change 2 * Real.pi * (∑ i, |(a i : ℝ)|) / (M : ℝ) ≤ _
  apply (div_le_self (by positivity)
    (show (1 : ℝ) ≤ M by exact_mod_cast Nat.succ_le_of_lt hM)).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ 2 * Real.pi)

theorem rationalLiftCharacterTwist_residual (M : ℕ) (hM : 0 < M)
    (a : Fin m → ℤ) (c x : Fin m → ℝ) (β : Fin m → ℤ) :
    rationalLiftCharacterTwist M a c (fun i => x i - (β i : ℝ))
      (fun i => (β i : ZMod M)) =
        (Real.fourierChar ((∑ i, (a i : ℝ) * (x i + c i)) / (M : ℝ)) : ℂ) := by
  let : NeZero M := ⟨hM.ne'⟩
  have hzexists (i : Fin m) : ∃ z : ℤ,
      β i = ((β i : ZMod M).val : ℤ) + (M : ℤ) * z :=
    (ZMod.intCast_eq_iff M (β i) (β i : ZMod M)).mp rfl
  choose z hz using hzexists
  have hβ (i : Fin m) : (β i : ℝ) = ((β i : ZMod M).val : ℝ) + (M : ℝ) * (z i : ℝ) := by
    exact_mod_cast hz i
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hphase : (∑ i, (a i : ℝ) * (x i - (β i : ℝ) + (β i : ZMod M).val + c i)) / (M : ℝ) =
      (∑ i, (a i : ℝ) * (x i + c i)) / (M : ℝ) - ((∑ i, a i * z i : ℤ) : ℝ) := by
    calc
      _ = ∑ i, ((a i : ℝ) * (x i + c i) / (M : ℝ) - ((a i * z i : ℤ) : ℝ)) := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [hβ i, Int.cast_mul]
        field_simp
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Int.cast_sum]
        simp only [div_eq_mul_inv, Finset.sum_mul]
  have hzchar : Real.fourierChar (((∑ i, a i * z i : ℤ) : ℝ)) = 1 := by
    apply Subtype.ext
    change (Circle.exp (2 * Real.pi * (((∑ i, a i * z i : ℤ) : ℝ))) : ℂ) = 1
    rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
    simp
  unfold rationalLiftCharacterTwist
  rw [hphase, Real.fourierChar.map_sub_eq_div, hzchar, div_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DependentPatchValue
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem rationalLiftCharacterTwistLip_le_exp {m : ℕ}
    (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ) (p q : ℝ)
    (hm : (m : ℝ) ≤ Real.exp p) (ha : ∀ i, |(a i : ℝ)| ≤ Real.exp q) :
    (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp (p + q + 8) := by
  have hpi : 2 * Real.pi ≤ Real.exp (8 : ℝ) := by
    linarith [Real.pi_lt_four, Real.add_one_le_exp (8 : ℝ)]
  calc
    _ ≤ 2 * Real.pi * m * Real.exp q := rationalLiftCharacterTwistLip_le M hM a _ ha
    _ ≤ Real.exp 8 * Real.exp p * Real.exp q := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hpi hm (Nat.cast_nonneg m) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem rationalLiftCharacterTwistLip_le_exp_of_dim {m : ℕ}
    (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ) (p q : ℝ)
    (hm : (m : ℝ) ≤ p) (ha : ∀ i, |(a i : ℝ)| ≤ Real.exp q) :
    (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp (p + q + 8) :=
  rationalLiftCharacterTwistLip_le_exp M hM a p q
    (hm.trans (by linarith [Real.add_one_le_exp p])) ha

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_pderiv_degreeOf_le {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j i : I) {d : ℕ} (hd : p.degreeOf i ≤ d) :
    (MvPolynomial.pderiv j p).degreeOf i ≤ d := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro m hm
  have hc : p.coeff (m + Finsupp.single j 1) ≠ 0 := by
    intro hz
    apply MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  have hb := MvPolynomial.degreeOf_le_iff.mp hd _ (MvPolynomial.mem_support_iff.mpr hc)
  have hi : m i ≤ (m + Finsupp.single j 1 : I →₀ ℕ) i := by simp only [Finsupp.add_apply]; omega
  exact hi.trans hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget
namespace OAI

section

namespace Erdos3

theorem algebraicMajor_denominator_le_exp (d qV qNat : ℕ) {p : ℝ}
    (hqV : (qV : ℝ) ≤ Real.exp p) (hqNat : (qNat : ℝ) ≤ Real.exp p) :
    (((qV*qNat)^(d+1) : ℕ) : ℝ) ≤
      Real.exp (2*((d : ℝ)+1)*p) := by
  have hprod : ((qV*qNat : ℕ) : ℝ) ≤ Real.exp (2*p) := by
    rw [Nat.cast_mul, two_mul, Real.exp_add]
    exact mul_le_mul hqV hqNat (Nat.cast_nonneg _) (Real.exp_nonneg _)
  calc
    _ = (((qV*qNat : ℕ) : ℝ))^(d+1) := by rw [Nat.cast_pow]
    _ ≤ (Real.exp (2*p))^(d+1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hprod _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem cleared_substitution_term
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (qV qA d : ℕ) (m : σ →₀ ℕ) (hm : m.sum (fun _ n => n) ≤ d) :
    C ((qV * qA ^ d : ℕ) : ℝ) *
        (C (V.coeff m) * ∏ i ∈ m.support, A i ^ m i) =
      C ((qV : ℝ) * V.coeff m) * C ((qA : ℝ) ^ (d - m.sum (fun _ n => n))) *
        ∏ i ∈ m.support, (C (qA : ℝ) * A i) ^ m i := by
  classical
  rw [show (∏ i ∈ m.support, (C (qA : ℝ) * A i) ^ m i) =
      C (qA : ℝ) ^ m.sum (fun _ n => n) * ∏ i ∈ m.support, A i ^ m i by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rfl]
  simp only [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
  calc
    _ = (C (qV : ℝ) * C (V.coeff m)) * C (qA : ℝ) ^ d *
        (∏ i ∈ m.support, A i ^ m i) := by ring
    _ = _ := by
      rw [show C (qA : ℝ) ^ d =
        C (qA : ℝ) ^ (d - m.sum (fun _ n => n)) * C (qA : ℝ) ^ m.sum (fun _ n => n) by
        rw [← pow_add, Nat.sub_add_cancel hm]]
      ring

theorem polynomial_substitution_cleared_mem
    (S : Subring (MvPolynomial τ ℝ))
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (qV qA d : ℕ) (hdegree : V.totalDegree ≤ d)
    (hV : ∀ m ∈ V.support, C ((qV : ℝ) * V.coeff m) ∈ S)
    (hA : ∀ i, C (qA : ℝ) * A i ∈ S)
    (hqA : C (qA : ℝ) ∈ S) :
    C ((qV * qA ^ d : ℕ) : ℝ) * aeval A V ∈ S := by
  classical
  rw [aeval_def, eval₂_eq, Finset.mul_sum]
  apply S.sum_mem
  intro m hm
  change C ((qV * qA ^ d : ℕ) : ℝ) *
    (C (V.coeff m) * ∏ i ∈ m.support, A i ^ m i) ∈ S
  rw [cleared_substitution_term V A qV qA d m ((le_totalDegree hm).trans hdegree)]
  apply S.mul_mem
  · apply S.mul_mem (hV m hm)
    simpa only [map_pow] using S.pow_mem hqA (d - m.sum (fun _ n => n))
  · exact S.prod_mem fun i _ => S.pow_mem (hA i) (m i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDerivativeSeparation
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem polynomial_eq_zero_of_pderiv_closed
    (S : Set (MvPolynomial σ ℚ))
    (hderiv : ∀ p ∈ S, ∀ i, pderiv i p ∈ S)
    (hconstant : ∀ p ∈ S, p.coeff 0 = 0) : ∀ p ∈ S, p = 0 := by
  classical
  have hcoeff : ∀ α : σ →₀ ℕ, ∀ p ∈ S, p.coeff α = 0 := by
    intro α
    induction α using Finsupp.induction with
    | zero => exact hconstant
    | @single_add i n α hi hn ih =>
      have hsteps : ∀ m : ℕ, ∀ p ∈ S, p.coeff (Finsupp.single i m + α) = 0 := by
        intro m
        induction m with
        | zero => simpa using ih
        | succ m ihm =>
          intro p hp
          have h := ihm (pderiv i p) (hderiv p hp i)
          rw [coeff_pderiv] at h
          have hindex : Finsupp.single i (m + 1) + α =
              (Finsupp.single i m + α) + Finsupp.single i 1 := by
            rw [Finsupp.single_add]
            abel
          rw [hindex]
          apply (mul_eq_zero.mp h).resolve_right
          exact_mod_cast Nat.succ_ne_zero ((Finsupp.single i m + α) i)
      exact hsteps n
  intro p hp
  ext α
  simpa only [MvPolynomial.coeff_zero] using hcoeff α p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialPotential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

noncomputable def weightedPolynomialPotential (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  (d : ℚ)⁻¹ • ∑ i, w i • (X i * P i)

theorem weightedPolynomialPotential_pderiv_formula (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ) (i : σ) :
    pderiv i (weightedPolynomialPotential w d P) =
      (d : ℚ)⁻¹ • (w i • P i + ∑ j, w j • (X j * pderiv i (P j))) := by
  classical
  have hterm (j : σ) : pderiv i (w j • (X j * P j)) =
      (if j = i then w i • P i else 0) + w j • (X j * pderiv i (P j)) := by
    by_cases hji : j = i
    · subst j
      simp
      ring
    · simp [pderiv_X_of_ne hji, hji]
  rw [weightedPolynomialPotential, (pderiv i).map_smul, map_sum]
  simp only [hterm, Finset.sum_add_distrib]
  simp

theorem weightedPolynomialPotential_pderiv (w : σ → ℕ) {d : ℕ} (hd : 0 < d)
    (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i))
    (hclosed : ∀ i j, pderiv i (P j) = pderiv j (P i)) (i : σ) :
    pderiv i (weightedPolynomialPotential w d P) = P i := by
  rw [weightedPolynomialPotential_pderiv_formula]
  simp only [hclosed i]
  rw [(hhom i).sum_weight_X_mul_pderiv, ← add_nsmul, Nat.add_sub_of_le (hweight i)]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'), one_smul]

theorem weightedPolynomialPotential_homogeneous (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i)) :
    (weightedPolynomialPotential w d P).IsWeightedHomogeneous w d := by
  change weightedPolynomialPotential w d P ∈ weightedHomogeneousSubmodule ℚ w d
  apply (weightedHomogeneousSubmodule ℚ w d).smul_mem
  apply (weightedHomogeneousSubmodule ℚ w d).sum_mem
  intro i _
  have hprod : (X i * P i).IsWeightedHomogeneous w d := by
    have h := (isWeightedHomogeneous_X (R := ℚ) w i).mul (hhom i)
    simpa only [Nat.add_sub_of_le (hweight i)] using h
  exact (weightedHomogeneousSubmodule ℚ w d).nsmul_mem hprod (w i)

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

theorem majorFunctionAdd {B R : Type*} [Add R] (f g : B → R) :
    f + g = fun i => f i + g i := rfl

theorem majorFunctionSub {B R : Type*} [Sub R] (f g : B → R) :
    f - g = fun i => f i - g i := rfl

theorem majorFunctionNeg {B R : Type*} [Neg R] (f : B → R) :
    -f = fun i => -f i := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {U X : Type*}

theorem real_fourierChar_add_integer (t : ℝ) (k : ℤ) :
    (Real.fourierChar (t + (k : ℝ)) : ℂ) = (Real.fourierChar t : ℂ) := by
  rw [Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
  have hk : (Real.fourierChar (k : ℝ) : ℂ) = 1 := by
    change (Circle.exp (2 * Real.pi * (k : ℝ)) : ℂ) = 1
    rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
    simp
  rw [hk, mul_one]

theorem real_fourierChar_sub_star (a b : ℝ) :
    (Real.fourierChar (a - b) : ℂ) =
      (Real.fourierChar a : ℂ) * star (Real.fourierChar b : ℂ) := by
  rw [Real.fourierChar.map_sub_eq_div, div_eq_mul_inv, Circle.coe_mul,
    Circle.coe_inv_eq_conj]
  rfl

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

noncomputable def translationDirectionalDerivative (b : B → MvPolynomial U ℝ) :
    MvPolynomial (U ⊕ B) ℝ →ₗ[ℝ] MvPolynomial (U ⊕ B) ℝ :=
  ∑ i, (LinearMap.mulLeft ℝ (rename Sum.inl (b i))).comp (pderiv (Sum.inr i)).toLinearMap

theorem translationDirectionalDerivative_apply (b : B → MvPolynomial U ℝ)
    (P : MvPolynomial (U ⊕ B) ℝ) :
    translationDirectionalDerivative b P =
      ∑ i, rename Sum.inl (b i) * pderiv (Sum.inr i) P := by
  simp [translationDirectionalDerivative]

noncomputable def translationDirectionalSeries (d : ℕ) (b : B → MvPolynomial U ℝ)
    (P : MvPolynomial (U ⊕ B) ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  ∑ i ∈ Finset.range d, ((-1 : ℝ) ^ i / ((i + 1).factorial : ℝ)) •
    ((translationDirectionalDerivative b) ^ i) P

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*} [Fintype B]

omit [Fintype B] in
theorem degreeOf_rename_inl_inr (P : MvPolynomial U ℝ) (i : B) :
    (rename (Sum.inl : U → U ⊕ B) P).degreeOf (Sum.inr i) = 0 := by
  classical
  by_contra h
  obtain ⟨j, _, hj⟩ := mem_vars_rename (Sum.inl : U → U ⊕ B) P
    (mem_vars_iff_degreeOf_ne_zero.mpr h)
  cases hj

theorem translationDirectionalDerivative_degreeOf_le
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d) (j : B) :
    (translationDirectionalDerivative b P).degreeOf (Sum.inr j) ≤ d := by
  classical
  rw [translationDirectionalDerivative_apply]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro i _
  apply (degreeOf_mul_le _ _ _).trans
  rw [degreeOf_rename_inl_inr, zero_add]
  exact mvPolynomial_pderiv_degreeOf_le P (Sum.inr i) (Sum.inr j) (hP j)

theorem translationDirectionalDerivative_pow_degreeOf_le
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    (d : ℕ) (hP : ∀ j, P.degreeOf (Sum.inr j) ≤ d) (k : ℕ) (j : B) :
    (((translationDirectionalDerivative b) ^ k) P).degreeOf (Sum.inr j) ≤ d := by
  induction k generalizing j with
  | zero => simpa using hP j
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact translationDirectionalDerivative_degreeOf_le b _ d ih j

theorem translationDirectionalSeries_coefficient_abs_le_one (i : ℕ) :
    |(-1 : ℝ) ^ i / ((i + 1).factorial : ℝ)| ≤ 1 := by
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (Nat.cast_nonneg _)]
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (i + 1))

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialPotentialExtension
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def coordinateWeightProjection (w : σ → ℕ) (n : ℕ) :
    (σ → ℚ) →ₗ[ℚ] (σ → ℚ) where
  toFun x i := if w i = n then x i else 0
  map_add' x y := by funext i; by_cases hi : w i = n <;> simp [hi]
  map_smul' r x := by funext i; by_cases hi : w i = n <;> simp [hi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3

variable {σ τ : Type*}

noncomputable def weightedLinearInverseMask
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ) :
    (σ → ℚ) →ₗ[ℚ] (τ → ℚ) where
  toFun x j := B (coordinateWeightProjection w (v j) x) j
  map_add' x y := by funext j; simp only [map_add, Pi.add_apply]
  map_smul' r x := by funext j; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem weightedLinearInverseMask_entry [DecidableEq σ]
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (i : σ) (j : τ) :
    weightedLinearInverseMask B v w (Pi.single i 1) j =
      if w i = v j then B (Pi.single i 1) j else 0 := by
  have hproj : coordinateWeightProjection w (v j) (Pi.single i 1) =
      if w i = v j then Pi.single i 1 else 0 := by
    funext k
    by_cases hk : k = i
    · subst k
      by_cases hij : w i = v j <;> simp [coordinateWeightProjection, hij]
    · by_cases hij : w i = v j <;>
        simp [coordinateWeightProjection, hij, Pi.single_eq_of_ne hk]
  change B (coordinateWeightProjection w (v j) (Pi.single i 1)) j = _
  rw [hproj]
  split_ifs <;> simp

theorem weightedLinearInverseMask_weighted [DecidableEq σ]
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (i : σ) (j : τ) (hij : w i ≠ v j) :
    weightedLinearInverseMask B v w (Pi.single i 1) j = 0 := by
  rw [weightedLinearInverseMask_entry, if_neg hij]

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

variable {U B : Type*}

noncomputable def majorTranslationTopCoordinates (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (j : B) : MvPolynomial U ℝ :=
  weightedHomogeneousComponent (fun _ : U => 1) (w j) (A j)

theorem majorTranslationTopCoordinates_homogeneous (w : B → ℕ)
    (A : B → MvPolynomial U ℝ) (j : B) :
    (majorTranslationTopCoordinates w A j).IsWeightedHomogeneous (fun _ : U => 1) (w j) :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

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

theorem coordinateImage_eq_span (U : Submodule ℚ V) (g : J → V)
    (hg : Submodule.span ℚ (Set.range g) = U) (ℓ : V →ₗ[ℚ] (B → ℚ)) :
    U.map ℓ = Submodule.span ℚ (Set.range (fun j => ℓ (g j))) := by
  rw [← hg, Submodule.map_span, ← Set.range_comp]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RealificationRationalDensity
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realification_rational_denseRange
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] :
    DenseRange (fun v : V => (1 : ℝ) ⊗ₜ[ℚ] v) := by
  let S := (LinearMap.range ((TensorProduct.mk ℚ ℝ V) 1)).toAddSubgroup
  have htmul (r : ℝ) (v : V) : r ⊗ₜ[ℚ] v ∈ S.topologicalClosure := by
    have hc : Continuous (fun r : ℝ => r • ((1 : ℝ) ⊗ₜ[ℚ] v)) :=
      (continuous_id : Continuous (fun r : ℝ => r)).smul
        (continuous_const : Continuous (fun _ : ℝ => ((1 : ℝ) ⊗ₜ[ℚ] v)))
    have hq (q : ℚ) : (q : ℝ) • ((1 : ℝ) ⊗ₜ[ℚ] v) ∈ S.topologicalClosure := by
      apply S.le_topologicalClosure
      refine ⟨q • v, ?_⟩
      simp only [TensorProduct.mk_apply, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Rat.smul_def, smul_eq_mul, mul_one]
    have h : r • ((1 : ℝ) ⊗ₜ[ℚ] v) ∈ S.topologicalClosure :=
      (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q : ℝ))).induction_on r
      (S.isClosed_topologicalClosure.preimage hc) hq
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  intro x
  change x ∈ S.topologicalClosure
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r v => exact htmul r v
  | add x y hx hy => exact S.topologicalClosure.add_mem hx hy

theorem realification_submodule_mem_closure_rational
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] (P : Submodule ℚ V)
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ P.baseChange ℝ) :
    x ∈ closure (Set.range (fun v : P => (1 : ℝ) ⊗ₜ[ℚ] (v : V))) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] P)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] P) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  have hc : Continuous (P.subtype.baseChange ℝ) :=
    IsModuleTopology.continuous_of_linearMap (P.subtype.baseChange ℝ)
  obtain ⟨z, rfl⟩ := hx
  have hz := realification_rational_denseRange (V := P) z
  have h := image_closure_subset_closure_image hc ⟨z, hz, rfl⟩
  simpa only [← Set.range_comp, Function.comp_def, LinearMap.baseChange_tmul,
    Submodule.subtype_apply] using h

theorem realification_submodule_property_of_rational
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] (P : Submodule ℚ V)
    {C : Set (ℝ ⊗[ℚ] V)} (hC : IsClosed C)
    (h : ∀ v : P, (1 : ℝ) ⊗ₜ[ℚ] (v : V) ∈ C)
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ P.baseChange ℝ) : x ∈ C := by
  exact closure_minimal (Set.range_subset_iff.mpr h) hC
    (realification_submodule_mem_closure_rational P hx)

theorem realification_submodule_eq_of_rational
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] (P : Submodule ℚ V)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : (ℝ ⊗[ℚ] V) → Y} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ v : P, f ((1 : ℝ) ⊗ₜ[ℚ] (v : V)) = g ((1 : ℝ) ⊗ₜ[ℚ] (v : V)))
    {x : ℝ ⊗[ℚ] V} (hx : x ∈ P.baseChange ℝ) : f x = g x :=
  realification_submodule_property_of_rational P (isClosed_eq hf hg) h hx

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
theorem continuous_pair_pullback {X B : Type*} [TopologicalSpace X]
    [TopologicalSpace B] {f : X × B → ℝ} {b : X → B}
    (hf : Continuous f) (hb : Continuous b) :
    Continuous (fun z : X × X => f (z.1, b z.2)) :=
  hf.comp (continuous_id.prodMap hb)

omit [Fintype σ] in
theorem continuous_pair_potential_difference {X B : Type*}
    [TopologicalSpace X] [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] {a b : X → B} {v : B → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hv : Continuous v) :
    Continuous (fun z : X × X => v (b z.2) - v (b z.2 - a z.1)) :=
  (hv.comp (hb.comp continuous_snd)).sub
    (hv.comp ((hb.comp continuous_snd).sub (ha.comp continuous_fst)))

omit [Fintype σ] in
theorem eval_real_map_at_rational (P : MvPolynomial σ ℚ) (z : σ → ℚ) :
    eval (fun i => (z i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) P) =
      (eval z P : ℝ) := by
  rw [eval_map]
  exact (eval₂_comp (algebraMap ℚ ℝ) z P).symm

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledGradedBaseCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [fintypeSigma : Fintype σ]

noncomputable def submoduleBasisCoordinates {τ : Type*} [Fintype τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) : (τ → ℚ) →ₗ[ℚ] (σ → ℚ) :=
  K.subtype.comp b.equivFun.symm.toLinearMap

omit fintypeSigma in
theorem submoduleBasisCoordinates_injective [Fintype σ] {τ : Type*} [Fintype τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) :
    Function.Injective (submoduleBasisCoordinates K b) :=
  Subtype.val_injective.comp b.equivFun.symm.injective

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistParameterPartition
namespace OAI

section

namespace Erdos3

noncomputable def exponentialProgressionScale (N q : ℕ) (p : ℝ) : ℕ :=
  ⌊(N : ℝ) / (8 * q * Real.exp (2 * p))⌋₊

theorem exponentialProgressionScale_bounds (N q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : Real.exp (3 * p + 16) ≤ (N : ℝ)) :
    0 < exponentialProgressionScale N q p ∧
      q * exponentialProgressionScale N q p ≤ N ∧
      (N : ℝ) * Real.exp (-(3 * p + 16)) ≤ exponentialProgressionScale N q p ∧
      2 * (q : ℝ) * exponentialProgressionScale N q p / N ≤
        Real.exp (-(2 * p)) / 4 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < Real.exp (2 * p) := Real.exp_pos _
  have he1 : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by positivity)
  have hden : 0 < 8 * (q : ℝ) * Real.exp (2 * p) := by positivity
  have hexp16 : (16 : ℝ) ≤ Real.exp 16 := by
    have := Real.add_one_le_exp (16 : ℝ)
    linarith
  have hlarge : 16 * (q : ℝ) * Real.exp (2 * p) ≤ Real.exp (3 * p + 16) := by
    calc
      16 * (q : ℝ) * Real.exp (2 * p) ≤
          Real.exp 16 * Real.exp p * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hexp16 hqexp (by positivity) (Real.exp_nonneg _)) he.le
      _ = Real.exp (3 * p + 16) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hnr : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
  let x : ℝ := N / (8 * q * Real.exp (2 * p))
  have hx2 : 2 ≤ x := (le_div_iff₀ hden).mpr (by nlinarith [hlarge.trans hN])
  have hfloor : (exponentialProgressionScale N q p : ℝ) ≤ x :=
    Nat.floor_le (le_trans (by norm_num) hx2)
  have hhalf : x / 2 ≤ (exponentialProgressionScale N q p : ℝ) := by
    have := Nat.lt_floor_add_one x
    change x < (exponentialProgressionScale N q p : ℝ) + 1 at this
    linarith
  have hH : 0 < exponentialProgressionScale N q p := by
    have : (0 : ℝ) < exponentialProgressionScale N q p := by linarith
    exact_mod_cast this
  have hupper : (exponentialProgressionScale N q p : ℝ) *
      (8 * q * Real.exp (2 * p)) ≤ N := (le_div_iff₀ hden).mp hfloor
  have hfit : q * exponentialProgressionScale N q p ≤ N := by
    have : (q : ℝ) * exponentialProgressionScale N q p ≤ N := by
      have hnonneg : (0 : ℝ) ≤ exponentialProgressionScale N q p := by positivity
      nlinarith
    exact_mod_cast this
  refine ⟨hH, hfit, ?_, ?_⟩
  · calc
      (N : ℝ) * Real.exp (-(3 * p + 16)) = N / Real.exp (3 * p + 16) := by
        rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ N / (16 * q * Real.exp (2 * p)) :=
        div_le_div_of_nonneg_left hnr.le (by positivity) hlarge
      _ = x / 2 := by dsimp [x]; ring
      _ ≤ _ := hhalf
  · apply (div_le_iff₀ hnr).mpr
    rw [Real.exp_neg]
    have heq : (Real.exp (2 * p))⁻¹ / 4 * (N : ℝ) = N / (4 * Real.exp (2 * p)) := by ring
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.exp (2 * p))).mpr
    nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U : Type*}
  [Fintype U]
  [DecidableEq U]
  {n : ℕ}

theorem major_phase_nine_tenths :
    1 - 2 * Real.pi * (1 / (20 * Real.pi)) = (9 / 10 : ℝ) := by
  field_simp
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MajorRationalLiftInputScale
namespace OAI

section

namespace Erdos3

def majorRationalLiftInputScale (d : ℕ) (p : ℝ) : ℝ :=
  ((d + 2 : ℕ) : ℝ) * (p + 1) + 8

theorem majorRationalLiftInputScale_bounds (d : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ majorRationalLiftInputScale d p ∧
      p ≤ majorRationalLiftInputScale d p ∧
      2 * p + 8 ≤ majorRationalLiftInputScale d p := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdp : 0 ≤ (d : ℝ) * p := mul_nonneg hd hp
  dsimp [majorRationalLiftInputScale]
  push_cast
  constructor
  · positivity
  constructor <;> nlinarith

theorem majorRationalLiftInputScale_mass (d : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (n m : ℕ) (hnm : ((n + m : ℕ) : ℝ) ≤ p) :
    ((n + m + 1 : ℕ) : ℝ) ^ d ≤ Real.exp (majorRationalLiftInputScale d p) := by
  have hbase : ((n + m + 1 : ℕ) : ℝ) ≤ p + 1 := by
    push_cast at hnm ⊢
    linarith
  have hexp : p + 1 ≤ Real.exp (p + 1) := by
    linarith [Real.add_one_le_exp (p + 1)]
  have hscale : (d : ℝ) * (p + 1) ≤ majorRationalLiftInputScale d p := by
    dsimp [majorRationalLiftInputScale]
    push_cast
    nlinarith
  calc
    _ ≤ Real.exp (p + 1) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hbase.trans hexp) d
    _ = Real.exp ((d : ℝ) * (p + 1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hscale

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearRestrictionHeight
namespace OAI

section

namespace Erdos3

def linearRestrictionHeight (n m d H K : ℕ) : ℕ :=
  (((n + 1) ^ d * K) * (m * H + 1) ^ d) *
    (K ^ ((n + 1) ^ d) * H ^ ((n * m) * d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem weightedPolynomialPotential_coeff (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    (weightedPolynomialPotential w d P).coeff m =
      ∑ i, ((w i : ℚ) / d) * (X i * P i).coeff m := by
  classical
  rw [weightedPolynomialPotential, Finset.smul_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, coeff_smul]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

end Erdos3

end

section

namespace Erdos3

theorem potential_integration_height_le_exp (n d K : ℕ) {p P : ℝ}
    (hP : 0 ≤ P) (hn : (n : ℝ) ≤ p)
    (hK : (K : ℝ) ≤ Real.exp P) :
    (((n + 1) * (d * K) ^ n : ℕ) : ℝ) ≤
      Real.exp (p + p * ((d : ℝ) + P)) := by
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p :=
    (add_le_add hn (le_refl 1)).trans (Real.add_one_le_exp p)
  have hd : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hbase : (d : ℝ) * K ≤ Real.exp ((d : ℝ) + P) := by
    rw [Real.exp_add]
    exact mul_le_mul hd hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg K)) hbase n
  rw [← Real.exp_nat_mul] at hpow
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp ((n : ℝ) * ((d : ℝ) + P)) :=
      mul_le_mul hn1 hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + (n : ℝ) * ((d : ℝ) + P)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr
      (add_le_add (le_refl p) (mul_le_mul_of_nonneg_right hn (by positivity)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotentialBudget
namespace OAI

section

namespace Erdos3

theorem translationMajor_initial_budget_bounds (a : ℕ) (ha : 2 ≤ a)
    (p : ℝ) (hp : 0 ≤ p) :
    0 ≤ (p + a)^a ∧ p ≤ (p + a)^a ∧ 1 ≤ (p + a)^a := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbase : (1 : ℝ) ≤ p + a := by linarith
  have hpow : p + a ≤ (p + a)^a := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ a by omega)
  exact ⟨(zero_le_one.trans hbase).trans hpow,
    (le_add_of_nonneg_right (Nat.cast_nonneg a)).trans hpow, hbase.trans hpow⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDimensionBudget
namespace OAI

section

universe level

namespace Erdos3

open Module

theorem two_mul_le_translation_major_budget {p : ℝ} (hp : 0 ≤ p) {a : ℕ} (ha : 2 ≤ a) :
    2 * p ≤ (p + (a : ℝ)) ^ a := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hsq : 2 * p ≤ (p + (a : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (p + (a : ℝ) - 1)]
  exact hsq.trans (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + (a : ℝ)) ha)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
namespace OAI

section

namespace Erdos3

open Module
open scoped Classical TensorProduct

def allocatedCandidateCommonFastSectionInput (p : ℝ) : ℝ := (p + 2) ^ 4 + 1

def allocatedCandidateCommonFastGeometryLog (p : ℝ) : ℝ :=
  (allocatedCandidateCommonFastSectionInput p + 2) ^ 47 + 1

noncomputable def allocatedCandidateCommonFastCoordinateHeight (p : ℝ) : ℕ :=
  ⌈Real.exp ((allocatedCandidateCommonFastSectionInput p + 2) ^ 7)⌉₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberRepresentatives
namespace OAI

section

namespace Erdos3

theorem exists_finite_fiber_representatives {α β : Type*} {n : ℕ}
    (f : α → β) (P : α → Prop) (c : Fin n → β)
    (hc : ∀ a, P a → ∃ i, c i = f a) :
    ∃ m : ℕ, m ≤ n ∧ ∃ d : Fin m → α,
      (∀ j, P (d j)) ∧
      ∀ a, P a → ∃ j, f (d j) = f a := by
  classical
  let I := {i : Fin n // ∃ a, P a ∧ f a = c i}
  let choose : I → α := fun i => Classical.choose i.property
  have hchoose (i : I) : P (choose i) ∧ f (choose i) = c i.val :=
    Classical.choose_spec i.property
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, ?_, fun j => choose (e.symm j), ?_, ?_⟩
  · simpa only [Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin n => ∃ a, P a ∧ f a = c i)
  · intro j
    exact (hchoose _).1
  · intro a ha
    obtain ⟨i, hi⟩ := hc a ha
    let i' : I := ⟨i, a, ha, hi.symm⟩
    refine ⟨e i', ?_⟩
    change f (choose (e.symm (e i'))) = f a
    rw [Equiv.symm_apply_apply]
    exact (hchoose i').2.trans hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TriangularCorrectionRows
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def triangularCorrectionSolutions {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (B : ℝ) (q : ℕ) :
    Set ((Fin n → ℝ) × (Fin n → ℚ)) :=
  {sr | (∀ i, |sr.1 i| ≤ B) ∧
    (∀ i, ∃ z : ℤ, sr.2 i = (z : ℚ) / q) ∧
    ∀ i, c i = ∑ j, A i j * sr.1 j + (sr.2 i : ℝ)}

theorem triangularCorrectionSolutions_prefix {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c : Fin (n + 1) → ℝ} {B : ℝ} {q : ℕ}
    {sr : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)}
    (htri : ∀ i j, i < j → A i j = 0)
    (hsr : sr ∈ triangularCorrectionSolutions A c B q) :
    ((fun i : Fin n => sr.1 i.castSucc), (fun i : Fin n => sr.2 i.castSucc)) ∈
      triangularCorrectionSolutions (fun i j => A i.castSucc j.castSucc)
        (fun i => c i.castSucc) B q := by
  refine ⟨fun i => hsr.1 i.castSucc, fun i => hsr.2.1 i.castSucc, ?_⟩
  intro i
  have hi := hsr.2.2 i.castSucc
  rw [Fin.sum_univ_castSucc] at hi
  simpa only [htri i.castSucc (Fin.last n) i.castSucc_lt_last, zero_mul, add_zero]
    using hi

theorem triangularCorrectionSolutions_last_eq {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c : Fin (n + 1) → ℝ} {B : ℝ} {q : ℕ}
    {sr : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)}
    (hsr : sr ∈ triangularCorrectionSolutions A c B q)
    (hdiag : A (Fin.last n) (Fin.last n) ≠ 0) :
    sr.1 (Fin.last n) =
      (c (Fin.last n) - ∑ j : Fin n, A (Fin.last n) j.castSucc * sr.1 j.castSucc -
        (sr.2 (Fin.last n) : ℝ)) / A (Fin.last n) (Fin.last n) := by
  apply (eq_div_iff hdiag).2
  have hi := hsr.2.2 (Fin.last n)
  rw [Fin.sum_univ_castSucc] at hi
  linarith

theorem triangularCorrectionSolutions_last_window {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c : Fin (n + 1) → ℝ} {B : ℝ} {q : ℕ}
    {sr : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)}
    (hsr : sr ∈ triangularCorrectionSolutions A c B q)
    (_hB : 0 ≤ B) (hdiag : |A (Fin.last n) (Fin.last n)| ≤ 1) :
    |(sr.2 (Fin.last n) : ℝ) -
      (c (Fin.last n) - ∑ j : Fin n, A (Fin.last n) j.castSucc * sr.1 j.castSucc)| ≤ B := by
  have hi := hsr.2.2 (Fin.last n)
  rw [Fin.sum_univ_castSucc] at hi
  have heq : (sr.2 (Fin.last n) : ℝ) -
      (c (Fin.last n) - ∑ j : Fin n, A (Fin.last n) j.castSucc * sr.1 j.castSucc) =
      -(A (Fin.last n) (Fin.last n) * sr.1 (Fin.last n)) := by linarith
  rw [heq, abs_neg, abs_mul]
  calc
    _ ≤ 1 * |sr.1 (Fin.last n)| :=
      mul_le_mul_of_nonneg_right hdiag (abs_nonneg _)
    _ ≤ B := by simpa only [one_mul] using hsr.1 (Fin.last n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

abbrev PlateauSiteIndex (α A : Type*) (n : A → ℕ) :=
  Σ a, (Finset α × Unit → Fin (n a))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorPhaseCoordinateDenominator
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {η σ : Type*} [Fintype η]

theorem majorPhaseCoordinateDenominator_pos (q : η → ℕ)
    (hq : ∀ i, 0 < q i) : 0 < ∏ i, q i :=
  Finset.prod_pos (fun i _ => hq i)

theorem majorPhaseCoordinateDenominator_le_exp (q : η → ℕ) (B : ℝ)
    (hq : ∀ i, (q i : ℝ) ≤ Real.exp B) :
    ((∏ i, q i : ℕ) : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * B) := by
  classical
  rw [Nat.cast_prod]
  calc
    (∏ i, (q i : ℝ)) ≤ ∏ _i : η, Real.exp B :=
      Finset.prod_le_prod (fun i _ => Nat.cast_nonneg (q i)) (fun i _ => hq i)
    _ = Real.exp ((Fintype.card η : ℝ) * B) := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]

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

noncomputable def taggedScalarLowPolynomial (d : ℕ) (F : Fin m → MvPolynomial X ℝ) :
    MvPolynomial X ℝ := ∑ j, if j.val + 1 ≤ d then F j else 0

noncomputable def taggedScalarHighConstant (d : ℕ) (F : Fin m → MvPolynomial X ℝ) : ℝ :=
  ∑ j, if d < j.val + 1 then (F j).coeff 0 else 0

theorem taggedScalar_sum_eq_low_add_constant (d : ℕ) (F : Fin m → MvPolynomial X ℝ)
    (hhigh : ∀ j, d < j.val + 1 → F j = C ((F j).coeff 0)) :
    (∑ j, F j) = taggedScalarLowPolynomial d F + C (taggedScalarHighConstant d F) := by
  classical
  unfold taggedScalarLowPolynomial taggedScalarHighConstant
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val + 1 ≤ d
  · simp only [hj, Nat.not_lt.mpr hj, ite_true, ite_false, map_zero, add_zero]
  · have hj' : d < j.val + 1 := Nat.lt_of_not_ge hj
    simp only [hj, hj', ite_false, ite_true, zero_add]
    exact hhigh j hj'

theorem taggedScalarLowPolynomial_degree (d : ℕ) (F : Fin m → MvPolynomial X ℝ)
    (hdegree : ∀ j, (F j).totalDegree ≤ j.val + 1) :
    (taggedScalarLowPolynomial d F).totalDegree ≤ d := by
  classical
  apply totalDegree_finsetSum_le
  intro j _
  split_ifs with hj
  · exact (hdegree j).trans hj
  · simp only [totalDegree_zero, Nat.zero_le]

theorem taggedScalar_sum_degree (h : Fin m) (F : Fin m → MvPolynomial X ℝ)
    (hdegree : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (hhigh : ∀ j, h < j → F j = C ((F j).coeff 0)) :
    (∑ j, F j).totalDegree ≤ h.val + 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  by_cases hj : j ≤ h
  · exact (hdegree j).trans (Nat.add_le_add_right hj 1)
  · rw [hhigh j (lt_of_not_ge hj), totalDegree_C]
    omega

theorem taggedScalar_sum_top (h : Fin m) (F : Fin m → MvPolynomial X ℝ)
    (hdegree : ∀ j, (F j).totalDegree ≤ j.val + 1)
    (hhigh : ∀ j, h < j → F j = C ((F j).coeff 0)) :
    homogeneousComponent (h.val + 1) (∑ j, F j) =
      homogeneousComponent (h.val + 1) (F h) := by
  classical
  rw [map_sum]
  apply Finset.sum_eq_single h
  · intro j _ hj
    apply homogeneousComponent_eq_zero
    by_cases hjh : j < h
    · exact (hdegree j).trans_lt (Nat.add_lt_add_right hjh 1)
    · have hlt : h < j := lt_of_le_of_ne (le_of_not_gt hjh) (Ne.symm hj)
      rw [hhigh j hlt, totalDegree_C]
      omega
  · simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationShearCoordinateSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def translationBaseDerivative (b : σ → R) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R (fun i => C (b i))

@[simp] theorem translationBaseDerivative_C (b : σ → R) (r : R) :
    translationBaseDerivative b (C r) = 0 := MvPolynomial.derivation_C _ _

@[simp] theorem translationBaseDerivative_X (b : σ → R) (i : σ) :
    translationBaseDerivative b (X i) = C (b i) := mkDerivation_X _ _ _

theorem translationBaseDerivative_apply [Fintype σ] (b : σ → R)
    (P : MvPolynomial σ R) :
    translationBaseDerivative b P = ∑ i, b i • pderiv i P := by
  classical
  have h : translationBaseDerivative b = ∑ i, b i • pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    rw [translationBaseDerivative_X]
    change _ = (Derivation.coeFnAddMonoidHom (∑ i, b i • pderiv i)) (X j)
    rw [map_sum]
    simp [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
      MvPolynomial.pderiv_X, Pi.single_apply,
      MvPolynomial.C_eq_smul_one]
  rw [h]
  change (Derivation.coeFnAddMonoidHom (∑ i, b i • pderiv i)) P = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationParameterPolynomialPacking
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommSemiring R]

noncomputable def packTranslationPolynomial :
    MvPolynomial B (MvPolynomial U R) ≃ₐ[R] MvPolynomial (U ⊕ B) R :=
  (commAlgEquiv R B U).trans (sumAlgEquiv R U B).symm

@[simp] theorem packTranslationPolynomial_X (i : B) :
    packTranslationPolynomial (R := R) (U := U) (X i) = X (Sum.inr i) := by
  simp [packTranslationPolynomial]

@[simp] theorem packTranslationPolynomial_C_X (i : U) :
    packTranslationPolynomial (R := R) (B := B) (C (X i)) = X (Sum.inl i) := by
  simp only [packTranslationPolynomial, AlgEquiv.trans_apply, commAlgEquiv_C_X,
    sumAlgEquiv_symm_X]

@[simp] theorem packTranslationPolynomial_C (P : MvPolynomial U R) :
    packTranslationPolynomial (B := B) (C P) = rename Sum.inl P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [packTranslationPolynomial]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, rename_X]
    rw [packTranslationPolynomial_C_X]

theorem packTranslationPolynomial_specialize (u : U → R)
    (Q : MvPolynomial B (MvPolynomial U R)) :
    aeval (Sum.elim (fun i => C (u i)) X) (packTranslationPolynomial Q) =
      MvPolynomial.map (eval u) Q := by
  induction Q using MvPolynomial.induction_on with
  | C P =>
    rw [packTranslationPolynomial_C, map_C]
    induction P using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P i hP => simp only [map_mul, rename_X, aeval_X, Sum.elim_inl, eval_X, hP]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, packTranslationPolynomial_X, aeval_X,
      Sum.elim_inr, map_X, hP]

theorem packTranslationPolynomial_eval (u : U → R) (b : B → R)
    (Q : MvPolynomial B (MvPolynomial U R)) :
    eval (Sum.elim u b) (packTranslationPolynomial Q) =
      eval b (MvPolynomial.map (eval u) Q) := by
  rw [← packTranslationPolynomial_specialize u Q]
  change (aeval (Sum.elim u b)) _ = (aeval b) ((aeval _) _)
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  cases i <;> simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationLogCoordinateInputBounds
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem packTranslationPolynomial_map_C {U B R : Type*} [CommSemiring R]
    (P : MvPolynomial B R) :
    packTranslationPolynomial (U := U) (MvPolynomial.map C P) = rename Sum.inr P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, map_X, packTranslationPolynomial_X, rename_X, hP]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPolynomialPackingDerivative
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*}

theorem pderiv_inr_rename_inl (i : B) (P : MvPolynomial U ℝ) :
    pderiv (Sum.inr i) (rename Sum.inl P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp]

theorem packTranslationPolynomial_pderiv (Q : MvPolynomial B (MvPolynomial U ℝ)) (i : B) :
    packTranslationPolynomial (pderiv i Q) =
      pderiv (Sum.inr i) (packTranslationPolynomial Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C P => simp [pderiv_inr_rename_inl]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
      packTranslationPolynomial_X, hP, pderiv_X, Pi.single_apply]
    by_cases h : j = i <;> simp [h]

theorem packTranslationPolynomial_directional_sum [Fintype B]
    (b : B → MvPolynomial U ℝ) (Q : MvPolynomial B (MvPolynomial U ℝ)) :
    packTranslationPolynomial (∑ i, b i • pderiv i Q) =
      translationDirectionalDerivative b (packTranslationPolynomial Q) := by
  classical
  rw [translationDirectionalDerivative_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← MvPolynomial.C_mul', map_mul, packTranslationPolynomial_C,
    packTranslationPolynomial_pderiv]

theorem packTranslationPolynomial_baseDerivative [Fintype B]
    (b : B → MvPolynomial U ℝ) (Q : MvPolynomial B (MvPolynomial U ℝ)) :
    packTranslationPolynomial (translationBaseDerivative b Q) =
      translationDirectionalDerivative b (packTranslationPolynomial Q) := by
  rw [translationBaseDerivative_apply, packTranslationPolynomial_directional_sum]

theorem packTranslationPolynomial_baseDerivative_pow [Fintype B]
    (b : B → MvPolynomial U ℝ) (Q : MvPolynomial B (MvPolynomial U ℝ)) (k : ℕ) :
    packTranslationPolynomial (((translationBaseDerivative b).toLinearMap ^ k) Q) =
      ((translationDirectionalDerivative b) ^ k) (packTranslationPolynomial Q) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    change packTranslationPolynomial (translationBaseDerivative b
      (((translationBaseDerivative b).toLinearMap ^ k) Q)) = _
    rw [packTranslationPolynomial_baseDerivative, ih]

end Erdos3

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

theorem integerPolynomial_map_rat_real (I : MvPolynomial σ ℤ) :
    MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.map (Int.castRingHom ℚ) I) =
      MvPolynomial.map (Int.castRingHom ℝ) I := by
  ext a
  simp only [coeff_map]
  simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullTaggedChartCoefficientRange
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

noncomputable def polynomialTagLinearEmbedding (E : B → I → ℝ) :
    U ⊕ B → MvPolynomial (U ⊕ I) ℝ :=
  Sum.elim (fun u => X (Sum.inl u))
    (fun b => ∑ i, C (E b i) * X (Sum.inr i))

@[simp] theorem polynomialTagLinearEmbedding_inl (E : B → I → ℝ) (u : U) :
    polynomialTagLinearEmbedding E (Sum.inl u) = X (Sum.inl u) := rfl

@[simp] theorem polynomialTagLinearEmbedding_inr (E : B → I → ℝ) (b : B) :
    polynomialTagLinearEmbedding (U := U) E (Sum.inr b) =
      ∑ i, C (E b i) * X (Sum.inr i) := rfl

theorem polynomialTagLinearEmbedding_rename (E : B → I → ℝ)
    (p : MvPolynomial U ℝ) :
    aeval (R := ℝ) (polynomialTagLinearEmbedding E)
      (rename (Sum.inl : U → U ⊕ B) p) = rename (Sum.inl : U → U ⊕ I) p := by
  rw [aeval_rename, rename_eq_aeval]
  rfl

theorem polynomialTagLinearEmbedding_eval (E : B → I → ℝ)
    (u : U → ℝ) (v : I → ℝ) (p : MvPolynomial (U ⊕ B) ℝ) :
    eval (Sum.elim u v) (aeval (R := ℝ) (polynomialTagLinearEmbedding E) p) =
      eval (Sum.elim u (fun b => ∑ i, E b i * v i)) p := by
  change aeval (R := ℝ) (Sum.elim u v)
    (aeval (R := ℝ) (polynomialTagLinearEmbedding E) p) =
      aeval (R := ℝ) (Sum.elim u (fun b => ∑ i, E b i * v i)) p
  rw [comp_aeval_apply]
  congr 1
  ext j : 1
  cases j <;> simp [polynomialTagLinearEmbedding]

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype B] [Fintype I]

noncomputable def polynomialSubspaceRestriction (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) : MvPolynomial (U ⊕ B) ℝ →ₐ[ℝ] MvPolynomial (U ⊕ I) ℝ :=
  aeval (R := ℝ) (polynomialTagLinearEmbedding (fun b i => (e i : B → ℝ) b))

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eval (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (v : I → ℝ) :
    eval (Sum.elim u v) (polynomialSubspaceRestriction K e p) =
      eval (Sum.elim u (fun b => ∑ i, (e i : B → ℝ) b * v i)) p :=
  polynomialTagLinearEmbedding_eval _ u v p

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eq_of_eval (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p q : MvPolynomial (U ⊕ B) ℝ)
    (h : ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) p = eval (Sum.elim u b) q) :
    polynomialSubspaceRestriction K e p = polynomialSubspaceRestriction K e q := by
  classical
  apply MvPolynomial.funext
  intro x
  let u : U → ℝ := fun a => x (Sum.inl a)
  let v : I → ℝ := fun a => x (Sum.inr a)
  have hx : x = Sum.elim u v := by funext a; cases a <;> rfl
  rw [hx, polynomialSubspaceRestriction_eval, polynomialSubspaceRestriction_eval]
  apply h
  have he : (fun b => ∑ i, (e i : B → ℝ) b * v i) =
      ((∑ i, v i • e i : K) : B → ℝ) := by
    ext b
    simp [mul_comm]
  rw [he]
  exact (∑ i, v i • e i : K).property

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eval_basis (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (b : K) :
    eval (Sum.elim u (fun i => e.repr b i)) (polynomialSubspaceRestriction K e p) =
      eval (Sum.elim u (b : B → ℝ)) p := by
  rw [polynomialSubspaceRestriction_eval]
  have he : (fun c => ∑ i, (e i : B → ℝ) c * e.repr b i) = (b : B → ℝ) := by
    funext c
    have h := congrArg (fun z : K => (z : B → ℝ) c) (e.sum_repr b)
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, mul_comm] using h
  rw [he]

omit [Fintype B] in
theorem polynomialSubspaceRestriction_eval_eq (K : Submodule ℝ (B → ℝ))
    (e : Basis I ℝ K) (p q : MvPolynomial (U ⊕ B) ℝ)
    (h : polynomialSubspaceRestriction K e p = polynomialSubspaceRestriction K e q)
    (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim u b) p = eval (Sum.elim u b) q := by
  rw [← polynomialSubspaceRestriction_eval_basis K e p u ⟨b, hb⟩, h,
    polynomialSubspaceRestriction_eval_basis]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
section ScalarTop
variable {σ τ R : Type*} [CommRing R]

theorem sampledTopPhase_coordinate_homogeneous (k : ℕ) (P : MvPolynomial τ R) :
    (homogeneousComponent k P).IsWeightedHomogeneous (fun _ : τ => 1) k :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

end ScalarTop

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonRefilteredFactorsSymbolTransport
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Classical

variable {σ R : Type*} [CommRing R]

noncomputable def nestedFrozenCoordinate
    (keepLong keepLater : σ → Prop)
    (fixed : {i : {i // keepLong i} // ¬keepLater i.val} → R)
    (i : {i // keepLong i}) : MvPolynomial {i // keepLater i} R :=
  if hi : keepLater i.val then X ⟨i.val, hi⟩ else C (fixed ⟨i, hi⟩)

def nestedFrozenVariableEquiv
    (keepLong keepLater : σ → Prop) (hsub : ∀ i, keepLater i → keepLong i) :
    {i // keepLater i} ≃ {i : {i // keepLong i} // keepLater i.val} where
  toFun i := ⟨⟨i.val, hsub i.val i.property⟩, i.property⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BoundedKernelGridEnumerationBudget
namespace OAI

section

namespace Erdos3

theorem real_grid_shifted_integer_bound {m N : ℕ} {B x c : ℝ} {z : ℤ}
    (hz : (m : ℝ) * x = z) (hxc : |x - c| ≤ B) (hN : (m : ℝ) * B ≤ N) :
    |((z - ⌊(m : ℝ) * c⌋ : ℤ) : ℝ)| ≤ (N : ℝ) + 1 := by
  have hfloor : |(m : ℝ) * c - (⌊(m : ℝ) * c⌋ : ℤ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
    linarith [Int.lt_floor_add_one ((m : ℝ) * c)]
  calc
    _ = |(m : ℝ) * (x - c) + ((m : ℝ) * c - (⌊(m : ℝ) * c⌋ : ℤ))| := by
      push_cast
      rw [← hz]
      congr 1
      ring
    _ ≤ |(m : ℝ) * (x - c)| + |(m : ℝ) * c - (⌊(m : ℝ) * c⌋ : ℤ)| := abs_add_le _ _
    _ ≤ (m : ℝ) * B + 1 := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      exact add_le_add (mul_le_mul_of_nonneg_left hxc (Nat.cast_nonneg m)) hfloor
    _ ≤ _ := by linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteDescendingRankOrder
namespace OAI

section

namespace Erdos3

theorem exists_finite_descending_rank_equiv {I : Type*} [Fintype I]
    (rank : I → ℕ) :
    ∃ e : Fin (Fintype.card I) ≃ I, ∀ i j, i ≤ j → rank (e j) ≤ rank (e i) := by
  classical
  let key : I → OrderDual ℕ ×ₗ Fin (Fintype.card I) :=
    fun i => toLex (rank i, Fintype.equivFin I i)
  have hkey : Function.Injective key := by
    intro i j hij
    apply (Fintype.equivFin I).injective
    exact congrArg (fun z => (ofLex z).2) hij
  let _ : LinearOrder I := LinearOrder.lift' key hkey
  let e : Fin (Fintype.card I) ≃o I := Fintype.orderIsoFinOfCardEq I rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  have hle : key (e i) ≤ key (e j) := e.monotone hij
  exact Prod.Lex.monotone_fst _ _ hle

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteRankTriangularFinset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_rank_triangular_equiv {I : Type*} [Fintype I]
    (rank : I → ℕ) (A : Matrix I I ℝ)
    (htri : ∀ i j, rank j ≤ rank i → j ≠ i → A i j = 0) :
    ∃ e : Fin (Fintype.card I) ≃ I,
      (∀ i j, i ≤ j → rank (e j) ≤ rank (e i)) ∧
      ∀ i j, i < j → A (e i) (e j) = 0 := by
  obtain ⟨e, he⟩ := exists_finite_descending_rank_equiv rank
  refine ⟨e, he, ?_⟩
  intro i j hij
  exact htri (e i) (e j) (he i j hij.le)
    (fun h => hij.ne (e.injective h).symm)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteNormalizedChartCorrection
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {U B : Type*}

theorem aeval_coordinate_scaling_monomial {I : Type*}
    (c : I → ℝ) (α : I →₀ ℕ) :
    aeval (R := ℝ) (fun i => C (c i) * X i) (monomial α 1) =
      monomial α (α.prod (fun i n => c i ^ n)) := by
  classical
  rw [aeval_monomial]
  simp only [map_one, one_mul, Finsupp.prod,
    mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, monomial_eq]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTagRestrictionBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

theorem polynomialTagLinearEmbedding_totalDegree_le (E : B → I → ℝ)
    (j : U ⊕ B) : (polynomialTagLinearEmbedding E j).totalDegree ≤ 1 := by
  classical
  cases j with
  | inl u => simp
  | inr b =>
      rw [polynomialTagLinearEmbedding_inr]
      apply totalDegree_finsetSum_le
      intro i _
      exact (totalDegree_mul _ _).trans (by simp)

end Erdos3

end

end OAI
end


