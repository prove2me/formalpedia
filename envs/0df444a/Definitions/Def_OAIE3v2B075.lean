-- Prove2me | Definitions.Def_OAIE3v2B075
-- name    : OAIE3v2B075
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:17:57.693873+00:00
-- url     : https://prove2.me/theorems/84d3f9ba-535c-414f-acdd-df7faf9d6352
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 76 of 311
-- statement:
--   Definitions bundle 76 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B041`, `OAIE3v2B043`, `OAIE3v2B045`, `OAIE3v2B046`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B050`, `OAIE3v2B051`, `OAIE3v2B052` of this split.
--
--   Modules: `Dynamics/ComparisonEquivalenceBudget.lean`, `Dynamics/CompatibleReducedFastReset.lean`, `Dynamics/FrozenCorrelationBudget.lean`, `Dynamics/MultilinearityBudgets.lean`, `Dynamics/SharedFreeRecoveryBudget.lean`, `Estimates/BoundedFreeWords.lean`, `Estimates/CocycleHorizontalNormalization.lean`, `Estimates/DenseSubboxCost.lean`, `Estimates/DerivativeHorizontalLifts.lean`, `Estimates/DetectedCanonicalEarlyRadiusModelBounds.lean`, `Estimates/FrozenCosetVariation.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/PowerSubgroup.lean`, `Estimates/RationalImageIntersections.lean`, `Estimates/RationalLieSubalgebra.lean`, `Estimates/RealSubquotientEquiv.lean`, `Estimates/RealSubspaceIntersectionCorrections.lean`, `Estimates/RealifiedDilationMultidegree.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/WeightedOverlapCorrelation.lean`, `Estimates/WeightedSummandCorrelation.lean`, `Geometry/BoxOverlapSize.lean`, `Geometry/DerivativeVerticalCoordinates.lean`, `Geometry/FilteredSubalgebraCoordinates.lean`, `Geometry/LieStructureTransport.lean`, `Geometry/MultidegreeCoordinateFreezing.lean`, `Geometry/SubmoduleQuotientCoordinates.lean`, `Lattices/EuclideanDerivativeLattice.lean`, `Lattices/LatticeMinorNormBound.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Linear/CommonRankCoefficientCorrections.lean`, `Linear/GradeProjectionRemainder.lean`, `Linear/QuotientProjectionCoordinates.lean`, `Linear/RankIntervalFactorization.lean`, `Linear/RankUnadaptedFactorization.lean`, `Linear/RealDualRationalBounds.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/LieCoordinatePolynomials.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/PolynomialIntegerInputs.lean`, `Polynomial/RationalPolynomialGrid.lean`, `Polynomial/SquarefreeBlockDegree.lean`, `Polynomial/UniformPolynomialPeriodBudget.lean`, `Polynomial/WeightedPolynomialRestriction.lean`, `Sampling/RationalSpanGrid.lean`.
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
import Definitions.Def_OAIE3v2B043
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B046
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B050
import Definitions.Def_OAIE3v2B051
import Definitions.Def_OAIE3v2B052

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Pointwise

variable {σ : Type*}

theorem polynomialDegreeGap_translate_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) ∈ polynomialDegreeGap 0 (Finsupp.weight (fun _ => 1) α) := by
  intro β hβ
  simpa only [Nat.add_zero] using
    (polynomialTranslate_monomial_bounds h (fun _ => 1) (by simp) α).1 hβ

theorem polynomialDegreeGap_translate_sub_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) - monomial α 1 ∈
      polynomialDegreeGap 1 (Finsupp.weight (fun _ => 1) α) := by
  intro β hβ
  exact Nat.succ_le_of_lt ((polynomialTranslate_monomial_bounds h (fun _ => 1) (by simp) α).2 hβ)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

theorem scalarTaylorRemainder_apply (h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    scalarTaylorRemainder h p = polynomialTranslate h p - p - scalarDirectionalDerivative h p := rfl

@[simp] theorem scalarTaylorRemainder_C (h : σ → ℚ) (c : ℚ) :
    scalarTaylorRemainder h (C c) = 0 := by
  rw [scalarTaylorRemainder_apply, polynomialTranslate_C, scalarDirectionalDerivative_C, sub_self, sub_zero]

@[simp] theorem scalarTaylorRemainder_X (h : σ → ℚ) (i : σ) :
    scalarTaylorRemainder h (X i) = 0 := by
  rw [scalarTaylorRemainder_apply, polynomialTranslate_X, scalarDirectionalDerivative_X]
  ring

theorem scalarTaylorRemainder_mul (h : σ → ℚ) (p q : MvPolynomial σ ℚ) :
    scalarTaylorRemainder h (p * q) =
      scalarTaylorRemainder h p * polynomialTranslate h q +
        scalarDirectionalDerivative h p * (polynomialTranslate h q - q) +
        p * scalarTaylorRemainder h q := by
  simp only [scalarTaylorRemainder_apply, map_mul, scalarDirectionalDerivative_mul]
  ring

theorem remainder_monomial_add (h : σ → ℚ) (α β : σ →₀ ℕ)
    (hα : scalarTaylorRemainder h (monomial α 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) α))
    (hβ : scalarTaylorRemainder h (monomial β 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) β)) :
    scalarTaylorRemainder h (monomial (α + β) 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) (α + β)) := by
  rw [map_add]
  have he : (monomial (α + β) 1 : MvPolynomial σ ℚ) = monomial α 1 * monomial β 1 := by simp
  rw [he, scalarTaylorRemainder_mul]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact polynomialDegreeGap_mul (i := 2) (j := 0) hα (polynomialDegreeGap_translate_monomial h β)
    · exact polynomialDegreeGap_mul (i := 1) (j := 1)
        (polynomialDegreeGap_directionalDerivative h (k := 0) (polynomialDegreeGap_monomial α 1))
        (polynomialDegreeGap_translate_sub_monomial h β)
  · exact polynomialDegreeGap_mul (i := 0) (j := 2) (polynomialDegreeGap_monomial α 1) hβ

theorem scalarTaylorRemainder_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    scalarTaylorRemainder h (monomial α 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) α) := by
  classical
  have hz : scalarTaylorRemainder h (monomial (0 : σ →₀ ℕ) 1) = 0 :=
    scalarTaylorRemainder_C h 1
  have hsingle (i : σ) (n : ℕ) : scalarTaylorRemainder h (monomial (Finsupp.single i n) 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) (Finsupp.single i n)) := by
    induction n with
    | zero => rw [Finsupp.single_zero, hz]; exact Submodule.zero_mem _
    | succ n ih =>
      rw [show Finsupp.single i (n + 1) = Finsupp.single i n + Finsupp.single i 1 from Finsupp.single_add _ _ _]
      apply remainder_monomial_add h _ _ ih
      change scalarTaylorRemainder h (X i) ∈ _
      rw [scalarTaylorRemainder_X]
      exact Submodule.zero_mem _
  induction α using Finsupp.induction with
  | zero => rw [hz]; exact Submodule.zero_mem _
  | @single_add i n α _ _ ih => exact remainder_monomial_add h _ _ (hsingle i n) ih

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedSummandCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem norm_finiteCorrelation_sub_le {Ω : Type*} {Q : Finset Ω} (hQ : Q.Nonempty)
    (f u v : Ω → ℂ) {δ : ℝ} (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (huv : ∀ x ∈ Q, ‖u x - v x‖ ≤ δ) :
    ‖finiteCorrelation Q f u - finiteCorrelation Q f v‖ ≤ δ := by
  rw [← finiteCorrelation_sub_right]
  exact norm_finiteCorrelation_le hQ f _ hf huv

theorem exists_correlating_summand {Ω J : Type*} [Fintype J]
    {Q : Finset Ω} (hQ : Q.Nonempty) (f u : Ω → ℂ) (v : J → Ω → ℂ)
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M) (hcard : (Fintype.card J : ℝ) ≤ M)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1)
    (happrox : ∀ x ∈ Q, ‖(∑ j, v j x) - u x‖ ≤ ρ / 2)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ∃ j, ρ / (2 * M) ≤ ‖finiteCorrelation Q f (v j)‖ := by
  classical
  have herr := norm_finiteCorrelation_sub_le hQ f (fun x => ∑ j, v j x) u hf happrox
  rw [finiteCorrelation_sum_right] at herr
  have htriangle := norm_le_norm_add_norm_sub
    (∑ j, finiteCorrelation Q f (v j)) (finiteCorrelation Q f u)
  have hsum : ρ / 2 ≤ ∑ j, ‖finiteCorrelation Q f (v j)‖ := by
    have hn := norm_sum_le (Finset.univ : Finset J) (fun j => finiteCorrelation Q f (v j))
    linarith
  have hJ : (Finset.univ : Finset J).Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sum_empty] at hsum
    linarith
  have hthreshold : 0 ≤ ρ / (2 * M) := le_of_lt (div_pos hρ (by positivity))
  have hconstants : (∑ _j : J, ρ / (2 * M)) ≤ ρ / 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ ≤ M * (ρ / (2 * M)) := mul_le_mul_of_nonneg_right hcard hthreshold
      _ = ρ / 2 := by field_simp
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le hJ (hconstants.trans hsum)
  exact ⟨j, hj⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalImageIntersections
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

section Coordinates

variable [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem rationalQuotientEquiv_apply_mk (D : Matrix ι κ ℚ)
    (K : Submodule ℚ (κ → ℚ)) (hker : LinearMap.ker D.mulVecLin = K)
    (hsurj : Function.Surjective D.mulVec) (x : κ → ℚ) :
    rationalQuotientEquiv D K hker hsurj (Submodule.Quotient.mk x) = D *ᵥ x := by
  simp only [rationalQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact D.mulVecLin.quotKerEquivOfSurjective_apply_mk hsurj x

end Coordinates

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]

noncomputable def rationalSpanGridStep (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) : ℕ :=
  l * matrixDenominator (spanningCoordinateMatrix e v)

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

noncomputable def polynomialDenominator (P : MvPolynomial σ ℚ) : ℕ :=
  arrayDenominator (fun m : P.support => P.coeff m.val)

theorem polynomialDenominator_pos (P : MvPolynomial σ ℚ) : 0 < polynomialDenominator P :=
  arrayDenominator_pos _

noncomputable def integralNumeratorPolynomial (P : MvPolynomial σ ℚ) (q s : ℕ) :
    MvPolynomial σ ℤ := by
  classical
  exact ∑ m : P.support, monomial m.val
    (clearedArray (fun n : P.support => P.coeff n.val) m * (q : ℤ) ^ (s - m.val.sum (fun _ n => n)))

theorem integralNumeratorPolynomial_eval [Fintype σ] (P : MvPolynomial σ ℚ) (q s : ℕ)
    (hdegree : P.totalDegree ≤ s) (x : σ → ℚ) (z : σ → ℤ)
    (hz : ∀ i, (q : ℚ) * x i = (z i : ℚ)) :
    ((eval z (integralNumeratorPolynomial P q s) : ℤ) : ℚ) =
      (polynomialDenominator P : ℚ) * (q : ℚ) ^ s * eval x P := by
  classical
  rw [integralNumeratorPolynomial, map_sum]
  push_cast
  simp only [eval_monomial, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [eval_eq']
  rw [← Finset.sum_coe_sort P.support]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hm : m.val.sum (fun _ n => n) ≤ s := (le_totalDegree m.property).trans hdegree
  rw [clearedArray_cast]
  have hprod : ((m.val.prod (fun i n => z i ^ n) : ℤ) : ℚ) =
      (q : ℚ) ^ m.val.sum (fun _ n => n) * ∏ i, x i ^ m.val i := by
    rw [Finsupp.prod_pow]
    simp only [Int.cast_prod, Int.cast_pow]
    simp_rw [← hz]
    exact product_scaled_powers x (q : ℚ) m.val
  rw [hprod]
  change ((polynomialDenominator P : ℚ) * P.coeff m.val) * (q : ℚ) ^ (s - m.val.sum (fun _ n => n)) *
      ((q : ℚ) ^ m.val.sum (fun _ n => n) * ∏ i, x i ^ m.val i) = _
  calc
    _ = (polynomialDenominator P : ℚ) *
        ((q : ℚ) ^ (s - m.val.sum (fun _ n => n)) * (q : ℚ) ^ m.val.sum (fun _ n => n)) *
        (P.coeff m.val * ∏ i, x i ^ m.val i) := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hm]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem abs_aeval_le_box_bound {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℚ)
    (v : σ → ℝ) {A B : ℝ} {s : ℕ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hcoeff : ∀ m, |((P.coeff m : ℚ) : ℝ)| ≤ A) (hv : ∀ i, |v i| ≤ B)
    (hdegree : P.totalDegree ≤ s) :
    |aeval v P| ≤ P.support.card * A * B ^ s := by
  classical
  change |P.eval₂ (algebraMap ℚ ℝ) v| ≤ _
  rw [eval₂_eq']
  calc
    _ ≤ ∑ m ∈ P.support, |algebraMap ℚ ℝ (P.coeff m) * ∏ i, v i ^ m i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ P.support, A * B ^ s := by
      apply Finset.sum_le_sum
      intro m hm
      rw [abs_mul, Finset.abs_prod]
      have hprod : (∏ i, |v i ^ m i|) ≤ B ^ s := by
        calc
          _ = ∏ i, |v i| ^ m i := by simp only [abs_pow]
          _ ≤ ∏ i, B ^ m i :=
            Finset.prod_le_prod (fun _ _ => by positivity)
              (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hv i) _)
          _ = B ^ (∑ i, m i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ B ^ s := by
            apply pow_le_pow_right₀ hB
            have hmdegree := (le_totalDegree hm).trans hdegree
            rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hmdegree
      exact mul_le_mul (hcoeff m) hprod (by positivity) hA
    _ = _ := by simp [mul_assoc]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem abs_eval_le_scaled_box_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (T v : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α)
    (hv : ∀ i, |v i| ≤ T i) :
    |eval v P| ≤ P.support.card * M := by
  classical
  have hv' (i : σ) : |v i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i), div_le_one (hT i)]
    exact hv i
  change |P.eval₂ (RingHom.id ℝ) v| ≤ _
  rw [eval₂_eq']
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _α ∈ P.support, M := by
      apply Finset.sum_le_sum
      intro α _
      change |P.coeff α * ∏ i, v i ^ α i| ≤ M
      rw [← monomialScale_mul_normalized_prod T v hT α, abs_mul,
        abs_mul, abs_of_pos (monomialScale_pos T hT α)]
      have hprod : |∏ i, (v i / T i) ^ α i| ≤ 1 := by
        rw [Finset.abs_prod]
        apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
        intro i _
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (hv' i)
      calc
        _ ≤ (M / monomialScale T α) * (monomialScale T α * 1) :=
          mul_le_mul (hcoeff α)
            (mul_le_mul_of_nonneg_left hprod (monomialScale_pos T hT α).le)
            (mul_nonneg (monomialScale_pos T hT α).le (abs_nonneg _))
            (div_nonneg hM (monomialScale_pos T hT α).le)
        _ = M := by rw [mul_one, div_mul_cancel₀ _ (monomialScale_pos T hT α).ne']
    _ = _ := by simp

theorem abs_eval_sub_eval_scaled_box_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (T v w : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M δ : ℝ} {s : ℕ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α)
    (hv : ∀ i, |v i| ≤ T i) (hw : ∀ i, |w i| ≤ T i)
    (hvw : ∀ i, |v i - w i| ≤ T i * δ) (hdegree : P.totalDegree ≤ s) :
    |eval v P - eval w P| ≤ P.support.card * M * Fintype.card σ * s * δ := by
  classical
  have hunit (u : σ → ℝ) (hu : ∀ i, |u i| ≤ T i) (i : σ) :
      |u i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i), div_le_one (hT i)]
    exact hu i
  have hdiff (i : σ) : |v i / T i - w i / T i| ≤ δ := by
    rw [← sub_div, abs_div, abs_of_pos (hT i), div_le_iff₀ (hT i), mul_comm]
    exact hvw i
  have hmonomial (α : σ →₀ ℕ) (hα : α ∈ P.support) :
      |(∏ i, (v i / T i) ^ α i) - ∏ i, (w i / T i) ^ α i| ≤
        Fintype.card σ * (δ * s) := by
    have hdeg (i : σ) : α i ≤ s :=
      (monomial_le_degreeOf i hα).trans ((degreeOf_le_totalDegree P i).trans hdegree)
    have hpow (u : σ → ℝ) (hu : ∀ i, |u i| ≤ T i) (i : σ) :
        |(u i / T i) ^ α i| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hunit u hu i)
    have hp (i : σ) : |(v i / T i) ^ α i - (w i / T i) ^ α i| ≤ δ * s := by
      simpa only [one_pow, mul_one] using abs_pow_sub_pow_box_bound
        (le_refl (1 : ℝ)) hδ (hunit v hv i) (hunit w hw i) (hdiff i) (hdeg i)
    simpa only [Finset.card_univ, one_pow, mul_one] using
      abs_finset_prod_sub_prod_le Finset.univ
        (fun i => (v i / T i) ^ α i) (fun i => (w i / T i) ^ α i)
        (le_refl (1 : ℝ)) (mul_nonneg hδ (Nat.cast_nonneg s))
        (fun i _ => hpow v hv i) (fun i _ => hpow w hw i) (fun i _ => hp i)
  change |P.eval₂ (RingHom.id ℝ) v - P.eval₂ (RingHom.id ℝ) w| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _α ∈ P.support, M * (Fintype.card σ * (δ * s)) := by
      apply Finset.sum_le_sum
      intro α hα
      change |P.coeff α * ∏ i, v i ^ α i - P.coeff α * ∏ i, w i ^ α i| ≤ _
      rw [← mul_sub, ← monomialScale_mul_normalized_prod T v hT α,
        ← monomialScale_mul_normalized_prod T w hT α, ← mul_sub,
        abs_mul, abs_mul, abs_of_pos (monomialScale_pos T hT α)]
      calc
        _ ≤ (M / monomialScale T α) *
            (monomialScale T α * (Fintype.card σ * (δ * s))) :=
          mul_le_mul (hcoeff α)
            (mul_le_mul_of_nonneg_left (hmonomial α hα) (monomialScale_pos T hT α).le)
            (mul_nonneg (monomialScale_pos T hT α).le (abs_nonneg _))
            (div_nonneg hM (monomialScale_pos T hT α).le)
        _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ (monomialScale_pos T hT α).ne']
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem rational_polynomial_eval_sub_integer_multiple {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) (q s l : ℕ) (hq : 0 < q) (hdegree : P.totalDegree ≤ s)
    (x y : σ → ℚ) (hx : x ∈ denominatorGrid q) (hy : y ∈ denominatorGrid q)
    (hxy : x - y ∈ scaledIntegerGrid (l * polynomialDenominator P * q ^ s)) :
    ∃ k : ℤ, eval x P - eval y P = (l : ℚ) * k := by
  classical
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := hy
  obtain ⟨v, hv⟩ := hxy
  let T := l * polynomialDenominator P * q ^ s
  let Q := integralNumeratorPolynomial P q s
  have hdiff : ∀ i, (T : ℤ) ∣ z i - w i := by
    intro i
    refine ⟨(q : ℤ) * v i, ?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    have hi := congrFun hv i
    change x i - y i = (T : ℚ) * (v i : ℚ) at hi
    have hzi : (q : ℚ) * x i = (z i : ℚ) := hz i
    have hwi : (q : ℚ) * y i = (w i : ℚ) := hw i
    rw [← hzi, ← hwi, ← mul_sub, hi]
    ring
  obtain ⟨k, hk⟩ := integer_polynomial_sub_dvd Q z w (T : ℤ) hdiff
  refine ⟨k, ?_⟩
  have hD : (polynomialDenominator P : ℚ) ≠ 0 := by exact_mod_cast (polynomialDenominator_pos P).ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  apply mul_left_cancel₀ (mul_ne_zero hD (pow_ne_zero s hq'))
  calc
    (polynomialDenominator P : ℚ) * (q : ℚ) ^ s * (eval x P - eval y P) =
        ((eval z Q - eval w Q : ℤ) : ℚ) := by
      push_cast
      rw [integralNumeratorPolynomial_eval P q s hdegree x z hz,
        integralNumeratorPolynomial_eval P q s hdegree y w hw]
      ring
    _ = ((T : ℤ) * k : ℤ) := by rw [hk]
    _ = (polynomialDenominator P : ℚ) * (q : ℚ) ^ s * ((l : ℚ) * k) := by
      push_cast
      dsimp [T]
      push_cast
      ring

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {ι σ : Type*} [Fintype ι]

noncomputable def polynomialFamilyDenominator (P : ι → MvPolynomial σ ℚ) : ℕ :=
  ∏ i, polynomialDenominator (P i)

theorem polynomialFamilyDenominator_pos (P : ι → MvPolynomial σ ℚ) :
    0 < polynomialFamilyDenominator P :=
  Finset.prod_pos (fun i _ => polynomialDenominator_pos (P i))

theorem polynomialDenominator_dvd_family (P : ι → MvPolynomial σ ℚ) (i : ι) :
    polynomialDenominator (P i) ∣ polynomialFamilyDenominator P :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem polynomialDenominator_exp_bound (P : MvPolynomial σ ℚ) {p : ℝ}
    (hp : 0 ≤ p) (a c : ℕ)
    (hcoeff : ∀ m, ((P.coeff m).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hcard : (P.support.card : ℝ) ≤ (p + 2) ^ c) :
    (polynomialDenominator P : ℝ) ≤ Real.exp ((p + 2) ^ (a + c)) := by
  classical
  unfold polynomialDenominator arrayDenominator
  rw [Nat.cast_prod]
  apply product_exponential_budget _ _ hp a c
  · intro i _
    positivity
  · intro i _
    exact hcoeff i.val
  · simpa only [Finset.card_univ, Fintype.card_coe] using hcard

theorem polynomialFamilyDenominator_exp_bound (P : ι → MvPolynomial σ ℚ) {p : ℝ}
    (hp : 0 ≤ p) (a b c : ℕ)
    (hcoeff : ∀ i m, (((P i).coeff m).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hcard : ∀ i, ((P i).support.card : ℝ) ≤ (p + 2) ^ c)
    (hι : (Fintype.card ι : ℝ) ≤ (p + 2) ^ b) :
    (polynomialFamilyDenominator P : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + b)) := by
  classical
  unfold polynomialFamilyDenominator
  rw [Nat.cast_prod]
  apply product_exponential_budget _ _ hp (a + c) b
  · intro i _
    positivity
  · intro i _
    exact polynomialDenominator_exp_bound (P i) hp a c (hcoeff i) (hcard i)
  · simpa only [Finset.card_univ] using hι

theorem rational_polynomial_family_eval_sub_mem_grid [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (q s l : ℕ) (hq : 0 < q)
    (hdegree : ∀ i, (P i).totalDegree ≤ s) (x y : σ → ℚ)
    (hx : x ∈ denominatorGrid q) (hy : y ∈ denominatorGrid q)
    (hxy : x - y ∈ scaledIntegerGrid (l * polynomialFamilyDenominator P * q ^ s)) :
    (fun i => eval x (P i) - eval y (P i)) ∈ scaledIntegerGrid l := by
  classical
  have h (i : ι) : ∃ k : ℤ, eval x (P i) - eval y (P i) = (l : ℚ) * k := by
    apply rational_polynomial_eval_sub_integer_multiple (P i) q s l hq (hdegree i) x y hx hy
    apply scaledIntegerGrid_subset_of_dvd _ hxy
    exact mul_dvd_mul (mul_dvd_mul dvd_rfl (polynomialDenominator_dvd_family P i)) dvd_rfl
  choose z hz using h
  exact ⟨z, funext hz⟩

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem polynomialFamilyDenominator_degree_budget {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (r : ℕ) {p : ℝ}
    (hdegree : ∀ i, (P i).totalDegree ≤ r) (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hcoeff : ∀ i m, (((P i).coeff m).den : ℝ) ≤ Real.exp p) :
    (polynomialFamilyDenominator P : ℝ) ≤ Real.exp ((p + (r + 3)) ^ (r + 3)) := by
  let t := p + (r + 3 : ℕ)
  have ht : 3 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hpT : p ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hr : (r : ℝ) + 1 ≤ t := by dsimp [t]; push_cast; linarith
  have hvars : (Fintype.card σ : ℝ) + 1 ≤ t := by
    dsimp [t]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hcard : ∀ i, ((P i).support.card : ℝ) ≤ t ^ (r + 1) := by
    intro i
    have h := (Nat.cast_le (α := ℝ)).mpr (polynomial_support_card_le (P i) (hdegree i))
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at h
    apply h.trans
    calc
      _ ≤ t * t ^ r := mul_le_mul hr (pow_le_pow_left₀ (by positivity) hvars r) (by positivity) (by linarith)
      _ = t ^ (r + 1) := (pow_succ' _ _).symm
  have hD := polynomialFamilyDenominator_exp_bound P (p := t - 2) (by linarith) 1 1 (r + 1)
    (by intro i m; rw [sub_add_cancel, pow_one]; exact (hcoeff i m).trans (Real.exp_le_exp.mpr hpT))
    (by simpa only [sub_add_cancel] using hcard)
    (by rw [sub_add_cancel, pow_one]; exact hι.trans hpT)
  simpa only [sub_add_cancel, show 1 + (r + 1) + 1 = r + 3 by omega, t, Nat.cast_add, Nat.cast_ofNat] using hD

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

theorem polynomial_integer_value_denominator {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) (z : σ → ℤ) :
    ∃ a : ℤ, (polynomialDenominator P : ℚ) * eval (fun i => (z i : ℚ)) P = (a : ℚ) := by
  refine ⟨eval z (integralNumeratorPolynomial P 1 P.totalDegree), ?_⟩
  have h := integralNumeratorPolynomial_eval P 1 P.totalDegree le_rfl
    (fun i => (z i : ℚ)) z (by simp)
  simpa only [Nat.cast_one, one_pow, mul_one] using h.symm

theorem polynomial_family_integer_values_grid {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (z : σ → ℤ) :
    (fun i => eval (fun j => (z j : ℚ)) (P i)) ∈ denominatorGrid (polynomialFamilyDenominator P) := by
  classical
  have h (i : ι) : ∃ a : ℤ,
      (polynomialFamilyDenominator P : ℚ) * eval (fun j => (z j : ℚ)) (P i) = (a : ℚ) := by
    obtain ⟨k, hk⟩ := polynomialDenominator_dvd_family P i
    obtain ⟨a, ha⟩ := polynomial_integer_value_denominator (P i) z
    refine ⟨(k : ℤ) * a, ?_⟩
    rw [hk, Nat.cast_mul]
    calc
      _ = (k : ℚ) * ((polynomialDenominator (P i) : ℚ) * eval (fun j => (z j : ℚ)) (P i)) := by ring
      _ = _ := by rw [ha]; push_cast; rfl
  choose a ha using h
  exact ⟨a, ha⟩

theorem polynomial_family_integer_congruence {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (r l : ℕ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (x y : σ → ℤ) (hxy : ∀ j, ((l * polynomialFamilyDenominator P : ℕ) : ℤ) ∣ x j - y j) :
    (fun i => eval (fun j => (x j : ℚ)) (P i) - eval (fun j => (y j : ℚ)) (P i)) ∈
      scaledIntegerGrid l := by
  apply rational_polynomial_family_eval_sub_mem_grid P 1 r l (by omega) hdegree
  · exact ⟨x, by simp⟩
  · exact ⟨y, by simp⟩
  · simpa only [one_pow, mul_one] using integer_difference_mem_grid x y _ hxy

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LieCoordinatePolynomials
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {ι X L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem coordinateRightBracket_eval (e : Basis ι ℚ L) (f : X → L)
    (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (x : X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (coordinateRightBracket (lieStructureConstants e) x p k) = e.repr ⁅a, f x⁆ k := by
  simp only [coordinateRightBracket, map_sum, map_mul, aeval_C, aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply, hp]
  exact (lie_coordinate_formula e a (f x) k).symm

theorem coordinateBracketList_eval (e : Basis ι ℚ L) (f : X → L) (xs : List X)
    (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (coordinateBracketList (lieStructureConstants e) xs p k) =
      e.repr (rightBracketList f xs a) k := by
  induction xs generalizing p a with
  | nil => exact hp k
  | cons x xs ih =>
    exact ih (coordinateRightBracket (lieStructureConstants e) x p) ⁅a, f x⁆
      (coordinateRightBracket_eval e f p a hp x)

theorem dynkinCoordinatePolynomial_eval (e : Basis ι ℚ L) (f : X → L)
    (w : FreeSemigroup X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (dynkinCoordinatePolynomial (lieStructureConstants e) w k) =
      e.repr (dynkinWord f w) k := by
  apply coordinateBracketList_eval
  intro i
  simp only [aeval_X]

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

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

variable [DecidableEq ι] [DecidableEq κ]

theorem lieStructureConstants_section (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (σ : M →ₗ[ℚ] L) (hσ : ∀ x, φ (σ x) = x) (i j k : κ) :
    lieStructureConstants b i j k = transportedLieConstants (lieStructureConstants e)
      (LinearMap.toMatrix e b φ.toLinearMap) (LinearMap.toMatrix b e σ) i j k := by
  have hbracket : ⁅b i, b j⁆ = φ ⁅σ (b i), σ (b j)⁆ := by rw [LieHom.map_lie, hσ, hσ]
  rw [lieStructureConstants, hbracket]
  change (b.repr (φ.toLinearMap ⁅σ (b i), σ (b j)⁆)) k = _
  rw [← congrFun (LinearMap.toMatrix_mulVec_repr e b φ.toLinearMap ⁅σ (b i), σ (b j)⁆) k]
  apply transportedLieConstants_formula
  · intro u
    exact (LinearMap.toMatrix_apply b e σ u i).symm
  · intro u
    exact (LinearMap.toMatrix_apply b e σ u j).symm

theorem lieStructureConstants_quotient_matrix (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (S : Matrix ι κ ℚ)
    (hS : LinearMap.toMatrix e b φ.toLinearMap * S = 1) (i j k : κ) :
    lieStructureConstants b i j k = transportedLieConstants (lieStructureConstants e)
      (LinearMap.toMatrix e b φ.toLinearMap) S i j k := by
  simpa only [LinearMap.toMatrix_toLin] using
    lieStructureConstants_section e b φ (Matrix.toLin b e S)
      (basisMatrix_section e b φ.toLinearMap S hS) i j k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialGrid
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem polynomial_rational_value_denominator {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) (q s : ℕ) (hdegree : P.totalDegree ≤ s)
    (x : σ → ℚ) (hx : x ∈ denominatorGrid q) :
    ∃ a : ℤ, ((polynomialDenominator P * q ^ s : ℕ) : ℚ) * eval x P = (a : ℚ) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨eval z (integralNumeratorPolynomial P q s), ?_⟩
  have h := integralNumeratorPolynomial_eval P q s hdegree x z hz
  simpa only [Nat.cast_mul, Nat.cast_pow] using h.symm

theorem polynomial_family_rational_values_grid {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (q s : ℕ) (hdegree : ∀ i, (P i).totalDegree ≤ s)
    (x : σ → ℚ) (hx : x ∈ denominatorGrid q) :
    (fun i => eval x (P i)) ∈ denominatorGrid (polynomialFamilyDenominator P * q ^ s) := by
  classical
  have h (i : ι) : ∃ a : ℤ,
      ((polynomialFamilyDenominator P * q ^ s : ℕ) : ℚ) * eval x (P i) = (a : ℚ) := by
    obtain ⟨k, hk⟩ := polynomialDenominator_dvd_family P i
    obtain ⟨a, ha⟩ := polynomial_rational_value_denominator (P i) q s (hdegree i) x hx
    refine ⟨(k : ℤ) * a, ?_⟩
    simp only [Nat.cast_mul, Nat.cast_pow] at ha
    rw [hk]
    simp only [Nat.cast_mul, Nat.cast_pow, Int.cast_mul, Int.cast_natCast]
    calc
      _ = (k : ℚ) * ((polynomialDenominator (P i) : ℚ) * (q : ℚ) ^ s * eval x (P i)) := by ring
      _ = _ := by rw [ha]
  choose a ha using h
  exact ⟨a, ha⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem lieBCH_sub_right_mem_of_mem_ideal
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (I : LieIdeal ℚ L)
    {a : L} (ha : a ∈ I) (b : L) : lieBCH s a b - b ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_lieBCH, (lieQuotientMap_eq_zero I a).mpr ha,
    lieBCH_zero_left (lie_quotient_lowerCentralSeries_eq_bot hnil I), sub_self]

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

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L]

noncomputable def lieQuotientCoordinateEquiv (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) : (L ⧸ I) ≃ₗ[ℚ] (κ → ℚ) :=
  (Submodule.Quotient.equiv I.toSubmodule (I.toSubmodule.map e.equivFun.toLinearMap)
    e.equivFun rfl).trans (rationalQuotientEquiv D _ hker hsurj)

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem lieQuotientCoordinateEquiv_apply_mk (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) (x : L) :
    lieQuotientCoordinateEquiv e I D hker hsurj (lieQuotientMap I x) = D *ᵥ e.equivFun x := by
  change rationalQuotientEquiv D _ hker hsurj (Submodule.Quotient.mk (e.equivFun x)) = _
  exact rationalQuotientEquiv_apply_mk D _ hker hsurj _

noncomputable def lieQuotientCoordinateBasis (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) : Basis κ ℚ (L ⧸ I) :=
  Basis.ofEquivFun (lieQuotientCoordinateEquiv e I D hker hsurj)

omit [DecidableEq κ] in
theorem lieQuotientCoordinateBasis_matrix (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) :
    LinearMap.toMatrix e (lieQuotientCoordinateBasis e I D hker hsurj) (lieQuotientMap I).toLinearMap = D := by
  ext i j
  rw [LinearMap.toMatrix_apply, lieQuotientCoordinateBasis, Basis.ofEquivFun_repr_apply]
  change (lieQuotientCoordinateEquiv e I D hker hsurj (lieQuotientMap I (e j))) i = _
  rw [lieQuotientCoordinateEquiv_apply_mk]
  simp [Basis.equivFun_self, Matrix.mulVec, dotProduct]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice
namespace OAI

section

namespace Erdos3

open Module

variable {σ κ : Type*} [Fintype σ] [Fintype κ]
  (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

theorem exists_bounded_euclideanDerivativeLattice_family [DecidableEq κ]
    (R : ℝ) (P : Finset ((σ → ℝ) × (κ → ℝ)))
    (hP : ∀ v ∈ P,
      v ∈ derivativeGridPoints T scale Y (LinearMap.toMatrix' A.toLinearMap) l ∧ ‖v‖ ≤ R) :
    ∃ Q : Finset (EuclideanSpace ℝ (σ ⊕ κ)), Q.card = P.card ∧
      ∀ v ∈ Q, v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl ∧
        ‖v‖ ≤ ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R := by
  classical
  refine ⟨P.image productEuclideanEquiv, Finset.card_image_of_injective _
    productEuclideanEquiv.injective, ?_⟩
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  constructor
  · apply (productEuclideanEquiv_mem_derivativeLattice T hT scale hscale Y A l hl w).mpr
    rw [← SetLike.mem_coe, derivativeLattice_carrier]
    exact (hP w hw).1
  · exact (productEuclideanEquiv_norm_le w).trans
      (mul_le_mul_of_nonneg_left (hP w hw).2 (Nat.cast_nonneg _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedOverlapCorrelation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem norm_overlapCorrelation_le {Q : Finset A} (f u : A → ℂ) {B : ℝ}
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B)
    {h : A} (hh : h ∈ cubeDifferenceSupport Q) :
    ‖finiteCorrelation (derivativeSupport Q h)
      (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ≤ B ^ 2 := by
  apply norm_finiteCorrelation_le ((mem_cubeDifferenceSupport Q h).mp hh)
  · intro x hx
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
      mul_le_mul (hf x hx) (hf (x + h) hxh) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · intro x hx
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    have hB : 0 ≤ B := (norm_nonneg (u x)).trans (hu x hx)
    simpa only [multiplicativeDerivative, norm_mul, norm_star, pow_two] using
      mul_le_mul (hu x hx) (hu (x + h) hxh) (norm_nonneg _) hB

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem weight_correlating_overlaps {Q : Finset A} (hQ : Q.Nonempty)
    (f u : A → ℂ) {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ρ ^ 2 / (2 * B ^ 2) ≤ ∑ h ∈ cubeDifferenceSupport Q,
      (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ then (1 : ℝ) else 0) := by
  apply weight_large_values_of_sum _ _ _ (sq_nonneg ρ) (sq_pos_of_pos hB)
    (fun _ _ => by positivity) (sum_overlap_weights hQ)
    (fun _ hh => norm_overlapCorrelation_le f u hf hu hh)
  exact (pow_le_pow_left₀ hρ hcorr 2).trans (correlation_sq_le_sum_overlap_norm hQ f u)

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

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

theorem translatedIntegerBox_nonempty (a : ι → ℤ) : (translatedIntegerBox a T).Nonempty :=
  (integerBox_nonempty T).image (fun x ↦ a + x)

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_box_differenceSupport_le (a : ι → ℤ) (T : ι → ℕ) :
    (cubeDifferenceSupport (translatedIntegerBox a T)).card ≤
      2 ^ Fintype.card ι * (translatedIntegerBox a T).card := by
  apply (Finset.card_le_card (box_differenceSupport_subset a T)).trans_eq
  simp only [translatedIntegerBox, card_translateSupport, card_integerBox,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

section Rational

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem eval_lieBCH (x : σ → ℚ) (s : ℕ) (p q : VectorPolynomial σ ℚ L) :
    eval x (lieBCH s p q) = lieBCH s (eval x p) (eval x q) :=
  map_lieBCH (evalLie x) s p q

end Rational
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreeBlockDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι]

theorem blockDegree_total [Fintype σ] (π : ι → σ) (a : ι →₀ ℕ) :
    ∑ i, blockDegree π a i = ∑ j, a j := by
  classical
  simp only [blockDegree_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℚ E] (P Q : Submodule ℚ E)

theorem realSubquotientEquiv_project (x : ℝ ⊗[ℚ] P) :
    realSubquotientEquiv P Q ((Q.comap P.subtype).mkQ.baseChange ℝ x) =
      ((Q.baseChange ℝ).comap (P.baseChange ℝ).subtype).mkQ (realificationSubmoduleEquiv P x) := by
  have hx : (Q.comap P.subtype).mkQ.baseChange ℝ x =
      realSubquotientProjection P Q (realificationSubmoduleEquiv P x) := by
    simp only [realSubquotientProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  rw [hx]
  dsimp only [realSubquotientEquiv, LinearEquiv.trans_apply]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisCoordinateProjection_idempotent (b : Basis ι K V) (S : Set ι) (x : V) :
    basisCoordinateProjection b S (basisCoordinateProjection b S x) = basisCoordinateProjection b S x :=
  basisCoordinateProjection_eq_self b S _ (basisCoordinateProjection_mem_span b S x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PowerSubgroup
namespace OAI

section

namespace Erdos3

variable {G : Type*} [Group G]

instance subgroupPowerCover_characteristic (Γ : Subgroup G) (m : ℕ) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).Characteristic := by
  rw [subgroupPowerCover_subgroupOf]
  infer_instance

instance subgroupPowerCover_normal (Γ : Subgroup G) (m : ℕ) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).Normal := inferInstance

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedFreeWords
namespace OAI

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem freeWordSet_card_le (t : Finset (FreeMonoid X)) (s : ℕ)
    (ht : ∀ w ∈ t, w.length ≤ s) :
    t.card ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  classical
  let code : t → (Σ n : Fin (s + 1), Fin n.val → X) := fun w =>
    ⟨⟨w.val.toList.length, Nat.lt_succ_of_le (ht w w.property)⟩, w.val.toList.get⟩
  have hinj : Function.Injective code := by
    intro u v huv
    have hl := congrArg (fun z : Σ n : Fin (s + 1), Fin n.val → X => List.ofFn z.2) huv
    change List.ofFn u.val.toList.get = List.ofFn v.val.toList.get at hl
    rw [List.ofFn_get, List.ofFn_get] at hl
    exact Subtype.ext (congrArg FreeMonoid.ofList hl)
  have hcard := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hcard
  calc
    t.card ≤ ∑ n : Fin (s + 1), Fintype.card X ^ n.val := hcard
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenCosetVariation
namespace OAI

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H]

open scoped NNReal

variable [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

theorem lipschitz_frozenCosetMap (Γ : Subgroup G) (Λ : Subgroup H)
    (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
    (φ : G →* H) (a r : H) (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ)
    {A C : ℝ≥0} (hφ : LipschitzWith C φ) (ha : LipschitzWith A (fun x => a * x)) :
    letI := rightCosetMetricSpace Γ hΓ
    letI := rightCosetMetricSpace Λ hΛ
    LipschitzWith (A * C) (frozenCosetMap Γ Λ φ a r h) := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  apply rightCosetMetricSpace_lipschitz_lift Γ hΓ
  have hf : LipschitzWith (A * C) (fun x : G => a * φ x * r) := by
    simpa only [one_mul, Function.comp_def] using
      (isometry_mul_right r).lipschitz.comp (ha.comp hφ)
  simpa only [one_mul, Function.comp_def, frozenCosetMap_mk] using
    (rightCosetMetricSpace_lipschitz_mk Λ hΛ).comp hf

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
open scoped TensorProduct

theorem layerRoundingBound_le_exp (d H l n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    (layerRoundingBound d H l n : ℝ) ≤ Real.exp ((p + 2) ^ (3 * n + 5)) := by
  let t := p + 2
  let a := 3 * n + 2
  have ht : 2 ≤ t := by dsimp [t]; linarith
  have hK := lieCoordinateHeight_le_exp d H n hp hd hH
  have hdim : ((d * d + 1 : ℕ) : ℝ) ≤ t ^ 2 := by
    push_cast
    dsimp [t]
    nlinarith [mul_self_le_mul_self (Nat.cast_nonneg d) hd]
  have hpow : (lieCoordinateHeight d H n : ℝ) ^ (d * d + 1) ≤
      Real.exp (t ^ (a + 2)) := by
    calc
      _ ≤ (Real.exp (t ^ a)) ^ (d * d + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hK _
      _ = Real.exp (((d * d + 1 : ℕ) : ℝ) * t ^ a) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (t ^ 2 * t ^ a) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdim (by positivity))
      _ = _ := by rw [← pow_add]; congr 2; omega
  have hdp : (d : ℝ) ≤ Real.exp p := hd.trans (by linarith [Real.add_one_le_exp p])
  have hpA : p ≤ t ^ a := le_power_budget hp (by dsimp [a]; omega)
  have htwo : (2 : ℝ) ≤ t ^ 2 := by nlinarith
  have hp2 : 2 * p ≤ t ^ (a + 2) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left htwo (by positivity : 0 ≤ t ^ a)]
  unfold layerRoundingBound
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp p * Real.exp (t ^ (a + 2)) :=
      mul_le_mul (mul_le_mul hdp hl (by positivity) (by positivity)) hpow
        (by positivity) (by positivity)
    _ = Real.exp (2 * p + t ^ (a + 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t ^ (a + 3)) := by
      apply Real.exp_le_exp.mpr
      rw [show a + 3 = (a + 2) + 1 by omega, pow_succ t (a + 2)]
      nlinarith [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ t ^ (a + 2))]
    _ = _ := by rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealDualRationalBounds
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem dualStructureConstants_height (c : ι → ι → ι → ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (i j k : ι ⊕ ι) :
    RationalHeightLE (dualStructureConstants c i j k) H := by
  cases i <;> cases j <;> cases k <;>
    first | exact hc _ _ _ | exact rationalHeightLE_zero hH

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

noncomputable def splitCoordinatePolynomial (i : σ) (u : MvPolynomial (Option σ) ℚ) :
    σ → MvPolynomial (Option σ) ℚ :=
  Function.update (fun j => MvPolynomial.X (some j)) i u

theorem splitCoordinatePolynomial_eval (i j : σ) (u : MvPolynomial (Option σ) ℚ)
    (x : Option σ → ℚ) :
    MvPolynomial.aeval (R := ℚ) x (splitCoordinatePolynomial i u j) =
      Function.update (fun k => x (some k)) i (MvPolynomial.aeval (R := ℚ) x u) j := by
  by_cases hj : j = i <;> simp [splitCoordinatePolynomial, hj, Function.update_of_ne]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeCoordinateFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

noncomputable def freezingPolynomial (S : Finset σ) (b : σ → ℤ) (i : σ) :
    MvPolynomial S ℚ :=
  if h : i ∈ S then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i : ℚ)

theorem freezingPolynomial_eval (S : Finset σ) (b : σ → ℤ) (x : S → ℤ) (i : σ) :
    MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (freezingPolynomial S b i) =
      (freezeCoordinates S b x i : ℚ) := by
  by_cases hi : i ∈ S <;> simp [freezingPolynomial, freezeCoordinates, hi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι κ δ : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem blockSpanningFamily_span [Fintype ι] (b : Basis ι K V) (c : ι → δ)
    (U : Submodule K V) (v : κ → V) (hspan : Submodule.span K (Set.range v) = U)
    (hU : BasisBlockInvariant b c U) :
    Submodule.span K (Set.range (blockSpanningFamily b c v)) = U := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    apply hU (c z.1) (v z.2)
    rw [← hspan]
    exact Submodule.subset_span ⟨z.2, rfl⟩
  · rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [← sum_basisBlockProjection b c (v j)]
    apply Submodule.sum_mem
    intro d hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    exact Submodule.subset_span ⟨(i, j), rfl⟩

theorem blockSpanningFamily_height {V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (c : ι → δ) (v : κ → V) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∀ z i, RationalHeightLE (b.repr (blockSpanningFamily b c v z) i) H := by
  classical
  intro z i
  rw [blockSpanningFamily_repr]
  split_ifs
  · exact hv z.2 i
  · exact rationalHeightLE_zero hH

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*}

theorem replicated_blockDegree_apply [Fintype σ] (bound : σ → ℕ)
    (a : ReplicatedIndex bound →₀ ℕ) (i : σ) :
    blockDegree (fun j : ReplicatedIndex bound => j.1) a i = ∑ j : Fin (bound i), a ⟨i, j⟩ := by
  classical
  change (∑ j : ReplicatedIndex bound, if j.1 = i then a j else 0) = _
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [hji, ite_false, Finset.sum_const_zero]
  · simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.GradeProjectionRemainder
namespace OAI

section

namespace Erdos3

open Module

section Coordinates

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basisGradeProjection_eq_zero_of_mem_higher (b : Basis ι K V)
    (w : ι → ℕ) (k : ℕ) (x : V)
    (hx : x ∈ Submodule.span K (b '' {i | k + 1 ≤ w i})) :
    basisGradeProjection b w k x = 0 := by
  apply (basisCoordinateProjection_eq_zero_iff b {i | w i = k} x).mpr
  apply Submodule.span_mono (Set.image_mono ?_) hx
  intro i hi
  change w i ≠ k
  change k + 1 ≤ w i at hi
  omega

end Coordinates

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

theorem real_image_section_weighted_bound {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (S : Matrix κ ι ℚ) (H : ℕ)
    (hblock : ∀ i j, c i ≠ r j → S i j = 0)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (W : δ → ℝ) (hW : ∀ d, 0 < W d) {M : ℝ} (hM : 0 ≤ M)
    (x : ι → ℝ) (hx : ∀ j, |x j| ≤ M / W (r j)) (i : κ) :
    |((fun i j => (S i j : ℝ)) *ᵥ x) i| ≤
      Real.exp ((p + 2) ^ 18) * M / W (c i) := by
  have hbound := weighted_matrix_mulVec_bound c r (fun i j => (S i j : ℝ))
    (fun i j h => by rw [hblock i j h, Rat.cast_zero])
    (rationalKernelHeight (Fintype.card ι) H : ℝ≥0) (fun i j => (hS i j).abs_real_le)
    W hW hM x hx i
  have hfac : ((Fintype.card ι : ℝ) + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1) ≤
      (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι)
        (rationalKernelHeight (Fintype.card ι) H) : ℝ) := by
    change _ ≤ ((Fintype.card κ : ℝ) + Fintype.card ι + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1)
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (hW _).le
  exact mul_le_mul_of_nonneg_right
    (hfac.trans (imageSection_bound_le_exp (Fintype.card κ) (Fintype.card ι) H hp hκ hι hH)) hM

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FilteredSubalgebraCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

omit [Fintype ι] in
theorem subalgebraLayerFamily_height (e : Basis ι ℚ L) (v : κ → L)
    (ω : ι → ℕ) (j : ℕ) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H) (z : κ ⊕ ι) (i : ι) :
    RationalHeightLE (e.repr (subalgebraLayerFamily e v ω j z) i) H := by
  classical
  cases z with
  | inl z => exact hv z i
  | inr z =>
    by_cases h : j ≤ ω z
    · by_cases he : z = i
      · subst i
        simpa [subalgebraLayerFamily, h] using rationalHeightLE_one hH
      · simpa [subalgebraLayerFamily, h, he] using rationalHeightLE_zero hH
    · simpa [subalgebraLayerFamily, h] using rationalHeightLE_zero hH

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubspaceIntersectionCorrections
namespace OAI

section

namespace Erdos3

open scoped Matrix NNReal

theorem kernel_split_factor_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((n : ℝ) + 1) * (H + 1) * Real.exp ((p + 2) ^ 18) ≤ Real.exp ((p + 2) ^ 19) := by
  have hfac : ((n : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    calc
      _ ≤ ((n : ℝ) + 1) * (Real.exp ((p + 2) ^ 1) + 1) := by
        gcongr
        exact hH.trans (Real.exp_le_exp.mpr (by simp))
      _ ≤ _ := matrix_weighted_factor_le_exp_power n hp hn 1 (by decide)
  have hpow : (p + 2) ^ 3 ≤ (p + 2) ^ 18 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hsum : (p + 2) ^ 3 + (p + 2) ^ 18 ≤ (p + 2) ^ 19 := by
    calc
      _ ≤ (p + 2) ^ 18 + (p + 2) ^ 18 := add_le_add hpow (le_refl ((p + 2) ^ 18))
      _ = 2 * (p + 2) ^ 18 := by ring
      _ ≤ (p + 2) * (p + 2) ^ 18 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := (pow_succ' (p + 2) 18).symm
  calc
    _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp ((p + 2) ^ 18) :=
      mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg _)
    _ = Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hsum

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SubmoduleQuotientCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
  (b : Basis ι ℚ V) (U : Submodule ℚ V) (D : Matrix κ ι ℚ)
  (hker : LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap)
  (hsurj : Function.Surjective D.mulVec)

noncomputable def submoduleQuotientCoordinateEquiv : (V ⧸ U) ≃ₗ[ℚ] (κ → ℚ) :=
  (Submodule.Quotient.equiv U (U.map b.equivFun.toLinearMap) b.equivFun rfl).trans
    (rationalQuotientEquiv D _ hker hsurj)

omit [Fintype κ] in
theorem submoduleQuotientCoordinateEquiv_mk (x : V) :
    submoduleQuotientCoordinateEquiv b U D hker hsurj (U.mkQ x) = D *ᵥ b.equivFun x :=
  rationalQuotientEquiv_apply_mk D _ hker hsurj _

noncomputable def submoduleQuotientCoordinateBasis : Basis κ ℚ (V ⧸ U) :=
  Basis.ofEquivFun (submoduleQuotientCoordinateEquiv b U D hker hsurj)

theorem submoduleQuotientCoordinateBasis_matrix [DecidableEq ι] [DecidableEq κ] :
    LinearMap.toMatrix b (submoduleQuotientCoordinateBasis b U D hker hsurj) U.mkQ = D := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, submoduleQuotientCoordinateBasis, Basis.ofEquivFun_repr_apply]
  change (submoduleQuotientCoordinateEquiv b U D hker hsurj (U.mkQ (b j))) i = _
  rw [submoduleQuotientCoordinateEquiv_mk]
  simp [Basis.equivFun_self, Matrix.mulVec, dotProduct]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FrozenCorrelationBudget
namespace OAI

section

namespace Erdos3

theorem exists_frozen_correlation_budget (c b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      let L := (P + c) ^ c + 2 * P + 40
      let Q := P + (L + b) ^ b + 2
      L ≤ (P + C) ^ C ∧
        productNiltestBudget (raisedNiltestBudget (P + Q + 2)) ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let L := (X + Polynomial.C c) ^ c + 2 * X + 40
  let Q := X + (L + Polynomial.C b) ^ b + 2
  let R := X + Q + 2
  let A := R + (R + 2) ^ 2 + 3
  let U := (A + 2) ^ 2 + A + (A + (A ^ 2 + A + 3) ^ 2) + A ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (L + U)
  refine ⟨C, hC, ?_⟩
  intro P hP L' Q'
  have hL : 0 ≤ L' := by dsimp only [L']; positivity
  have hU : 0 ≤ productNiltestBudget (raisedNiltestBudget (P + Q' + 2)) := by
    dsimp only [productNiltestBudget, productObservableLipBudget, raisedNiltestBudget, Q', L']
    positivity
  have htotal : L' + productNiltestBudget (raisedNiltestBudget (P + Q' + 2)) ≤ (P + C) ^ C := by
    simpa [X, L, Q, R, A, U, L', Q', Polynomial.eval₂_pow,
      productNiltestBudget, productObservableLipBudget, raisedNiltestBudget] using hbudget P hP
  exact ⟨by linarith only [htotal, hU], by linarith only [htotal, hL]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UniformPolynomialPeriodBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem polynomialDenominator_dvd_power {σ : Type*} (P : MvPolynomial σ ℚ)
    (q N : ℕ) (hden : ∀ α, (P.coeff α).den ∣ q) (hcard : P.support.card ≤ N) :
    polynomialDenominator P ∣ q ^ N := by
  classical
  have h : polynomialDenominator P ∣ q ^ P.support.card := by
    unfold polynomialDenominator arrayDenominator
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] using
      Finset.prod_dvd_prod_of_dvd (s := Finset.univ) (fun α : P.support => (P.coeff α.val).den)
        (fun _ : P.support => q) (fun α _ => hden α.val)
  exact h.trans (pow_dvd_pow q hcard)

theorem polynomialFamilyDenominator_dvd_power {ι σ : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (q N : ℕ)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q) (hcard : ∀ i, (P i).support.card ≤ N) :
    polynomialFamilyDenominator P ∣ q ^ (N * Fintype.card ι) := by
  classical
  unfold polynomialFamilyDenominator
  simpa only [Finset.prod_const, Finset.card_univ, ← pow_mul] using
    Finset.prod_dvd_prod_of_dvd (s := Finset.univ) (fun i => polynomialDenominator (P i))
      (fun _ : ι => q ^ N) (fun i _ => polynomialDenominator_dvd_power (P i) q N (hden i) (hcard i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedSquareObservableBudget_nonneg (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ normalizedSquareObservableBudget a b p := by
  have h1 := normalizedSquareProjectionBudget_nonneg p
  have h2 := normalizedSquareLeftBudget_nonneg a b hp
  unfold normalizedSquareObservableBudget
  linarith

theorem normalizedSquareReconstructionBudget_nonneg (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ normalizedSquareReconstructionBudget a b p := by
  have h1 := squareGeometryBudget_nonneg hp
  have h2 := normalizedSquareObservableBudget_nonneg a b hp
  unfold normalizedSquareReconstructionBudget
  linarith

theorem exists_normalizedSquareComplexityBudget_bound (a b c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → normalizedSquareComplexityBudget a b c p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := ((X + 3) ^ 11 + 2 * X + 5) ^ 11
  let U := 2 * X + (Q + X + 4) ^ 2 + (X + Polynomial.C a + 2 + Polynomial.C b) ^ b + 1
  let R := Q + 1 + U + 2 * X
  let P := Q + 2 * X + (R + Polynomial.C c) ^ c + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, R, U, Q, X, Polynomial.eval₂_pow, normalizedSquareComplexityBudget, normalizedSquareReconstructionBudget,
    normalizedSquareObservableBudget, normalizedSquareProjectionBudget,
    normalizedSquareLeftBudget, squareGeometryBudget] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CompatibleReducedFastReset
namespace OAI

section

namespace Erdos3

theorem exists_reduced_reset_budget (a cs cr : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (reducedResetParameter a p + cs) ^ cs ≤ (p + C) ^ C ∧
      (reducedResetParameter a p + cr) ^ cr ≤ (p + C) ^ C := by
  let Z : Polynomial ℕ := ((Polynomial.X + 2) ^ 10 + 2) ^ 36 +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let B := (Z + Polynomial.C cs) ^ cs + (Z + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hz := reducedResetParameter_nonneg a hp
  have hs : 0 ≤ (reducedResetParameter a p + cs) ^ cs := by positivity
  have hr : 0 ≤ (reducedResetParameter a p + cr) ^ cr := by positivity
  have hh : (reducedResetParameter a p + cs) ^ cs +
      (reducedResetParameter a p + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Z, reducedResetParameter, Polynomial.eval₂_pow] using hbound p hp
  exact ⟨(le_add_of_nonneg_right hr).trans hh, (le_add_of_nonneg_left hs).trans hh⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MultilinearityBudgets
namespace OAI

section

namespace Erdos3.MultilinearityBudget

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped NNReal

theorem exists_total_bound (C N : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ p : ℝ, 0 ≤ p → total C N p ≤ (p + Z) ^ Z := by
  let X : Polynomial ℕ := Polynomial.X
  let co : Polynomial ℕ := ((X + 4) ^ 2 + 2) ^ 63 + 3
  let geom : Polynomial ℕ := ((X + 6) ^ 2 + ((X + 4) ^ 2 + 2) ^ 63 + 6) ^ 11
  let R := X + geom + co
  let Q := (R + 3) ^ 11
  let O := X + (X + Polynomial.C C) ^ C + (R + 3) ^ 2 + 2
  let B := R + Q + O + 1
  obtain ⟨Z, hZ, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (B + Polynomial.C N) ^ N + 4)
  refine ⟨Z, hZ, fun p hp => ?_⟩
  simpa [total, reconstruction, observable, quotient, ambient, coordinates,
    additiveTripleGeometryBudget, X, co, geom, R, Q, O, B, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3.MultilinearityBudget

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedDilationMultidegree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

theorem realPairEquiv_mem_scaledPairLayer (P Q : Submodule ℚ L) (q : ℚ)
    (x : ℝ ⊗[ℚ] (L × L)) :
    realPairEquiv x ∈ scaledPairLayer ((P.baseChange ℝ).restrictScalars ℚ)
        ((Q.baseChange ℝ).restrictScalars ℚ) q ↔
      x ∈ (scaledPairLayer P Q q).baseChange ℝ := by
  change ((realPairEquiv x).1 ∈ P.baseChange ℝ ∧
    (realPairEquiv x).2 ∈ P.baseChange ℝ ∧
    scaledPairDifference q (realPairEquiv x) ∈ Q.baseChange ℝ) ↔ _
  rw [realPairEquiv_difference, realPairEquiv_first, realPairEquiv_second]
  simp only [scaledPairLayer_eq_inf, realification_inf, realification_comap,
    Submodule.mem_inf, Submodule.mem_comap]

noncomputable def realifiedScaledPairLayerEquiv (P Q : Submodule ℚ L) (q : ℚ) :
    ((scaledPairLayer P Q q).baseChange ℝ) ≃ₗ[ℚ]
      scaledPairLayer ((P.baseChange ℝ).restrictScalars ℚ)
        ((Q.baseChange ℝ).restrictScalars ℚ) q where
  toFun x := ⟨realPairEquiv x.val, (realPairEquiv_mem_scaledPairLayer P Q q x.val).mpr x.property⟩
  invFun x := ⟨realPairEquiv.symm x.val, (realPairEquiv_mem_scaledPairLayer P Q q _).mp (by
    simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext (realPairEquiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext (realPairEquiv.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (realPairEquiv.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((realPairEquiv.restrictScalars ℚ).map_smul r x.val)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DerivativeVerticalCoordinates
namespace OAI

section

namespace Erdos3

theorem euclideanDerivative_vertical_grid_coordinates
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hv : v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl)
    (hzero : euclideanDerivativeShiftMap T hT v = 0) :
    ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧ v = euclideanVerticalMap scale hscale A r := by
  have hv' := (euclideanDerivativeLattice_mem_iff T hT scale hscale Y A l hl v).mp hv
  rw [← SetLike.mem_coe, derivativeLattice_carrier] at hv'
  obtain ⟨h, r, hr, he⟩ := hv'
  have hh : h = 0 := by
    funext i
    have hi := congrFun hzero i
    change T i * (productEuclideanEquiv.symm v).1 i = 0 at hi
    rw [he] at hi
    change T i * ((h i : ℝ) / T i) = 0 at hi
    rw [mul_div_cancel₀ _ (hT i)] at hi
    exact_mod_cast hi
  subst h
  refine ⟨-r, realDenominatorGrid_neg l hr, ?_⟩
  apply productEuclideanEquiv.symm.injective
  rw [he]
  change derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) 0 r =
    (0, fun j => scale j * A (-r) j)
  simp only [derivativeGridPoint, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe,
    Pi.zero_apply, Int.cast_zero]
  change ((fun i : σ => (0 : ℝ) / T i),
    fun j => scale j * (Y (0 : σ → ℝ) - A r) j) = (0, fun j => scale j * A (-r) j)
  simp only [map_zero, zero_sub, map_neg, Pi.neg_apply, zero_div]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeMinorNormBound
namespace OAI

section

namespace Erdos3

theorem lattice_projection_all_minors_bound {ι κ E : Type*} [Fintype ι] {k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : κ → ι) (he : Function.Injective e)
    (H : Matrix κ (Fin k) ℝ) (hH : ∀ i j, H i j = f (b j).val (e i)) :
    ∀ q : Fin k → κ, |(H.submatrix q id).det| ≤ ZLattice.covolume Λ := by
  intro q
  by_cases hq : Function.Injective q
  · have h := abs_isometric_lattice_basis_det_le_covolume Λ b f (e ∘ q) (he.comp hq)
    have hm : Matrix.of (fun i j => f (b i).val ((e ∘ q) j)) =
        (H.submatrix q id).transpose := by
      ext i j
      exact (hH (q j) i).symm
    simpa only [hm, Matrix.det_transpose] using h
  · have hd : (H.submatrix q id).det = 0 := by
      by_contra hd
      exact hq (nonzero_row_minor_injective H q hd)
    rw [hd, abs_zero]
    exact (ZLattice.covolume_pos Λ MeasureTheory.volume).le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeHorizontalLifts
namespace OAI

section

namespace Erdos3

theorem euclideanVerticalMap_norm_eq {σ κ : Type*} [Fintype σ] [Fintype κ]
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (x : κ → ℝ) :
    ‖euclideanVerticalMap (σ := σ) scale hscale A x‖ =
      ‖(EuclideanSpace.equiv κ ℝ).symm (fun j => scale j * A x j)‖ := by
  have hs : ‖euclideanVerticalMap (σ := σ) scale hscale A x‖ ^ 2 =
      ‖(EuclideanSpace.equiv κ ℝ).symm (fun j => scale j * A x j)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fintype.sum_sum_type, euclideanVerticalMap_apply_inl,
      euclideanVerticalMap_apply_inr, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, zero_add]
    rfl
  nlinarith [norm_nonneg (euclideanVerticalMap (σ := σ) scale hscale A x),
    norm_nonneg ((EuclideanSpace.equiv κ ℝ).symm (fun j => scale j * A x j))]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxOverlapSize
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem weight_correlating_large_overlaps {A : Type*} [AddCommGroup A] [DecidableEq A]
    {Q : Finset A} (hQ : Q.Nonempty) (f u : A → ℂ) {ρ B δ : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 < B) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ρ ^ 2 / (2 * B ^ 2) - δ * (cubeDifferenceSupport Q).card / Q.card ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
            (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ∧
          δ * Q.card < ((derivativeSupport Q h).card : ℝ) then (1 : ℝ) else 0) := by
  classical
  let I := cubeDifferenceSupport Q
  let w := fun h => ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2
  let good := fun h => ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
    (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖
  let small := fun h => ((derivativeSupport Q h).card : ℝ) ≤ δ * Q.card
  have hw (h : A) : 0 ≤ w h := by dsimp [w]; positivity
  have hpoint (h : A) : w h * (if good h then (1 : ℝ) else 0) ≤
      w h * (if good h ∧ ¬small h then (1 : ℝ) else 0) + (if small h then w h else 0) := by
    by_cases hg : good h <;> by_cases hs : small h <;> simp [hg, hs, hw]
  have hsplit := Finset.sum_le_sum (fun h (_ : h ∈ I) => hpoint h)
  rw [Finset.sum_add_distrib] at hsplit
  have hgood := weight_correlating_overlaps hQ f u hρ hB hf hu hcorr
  change ρ ^ 2 / (2 * B ^ 2) ≤ ∑ h ∈ I, w h * (if good h then (1 : ℝ) else 0) at hgood
  have hsmall : (∑ h ∈ I, if small h then w h else 0) ≤ δ * I.card / Q.card := by
    rw [← Finset.sum_filter]
    exact weight_small_overlaps hQ hδ
  have hresult : ρ ^ 2 / (2 * B ^ 2) - δ * I.card / Q.card ≤
      ∑ h ∈ I, w h * (if good h ∧ ¬small h then (1 : ℝ) else 0) := by linarith
  simpa only [I, w, good, small, not_le] using hresult

theorem weight_correlating_large_box_overlaps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) [∀ i, NeZero (T i)] (f u : (ι → ℤ) → ℂ)
    {ρ B δ : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B) (hδ : 0 ≤ δ)
    (hf : ∀ x ∈ translatedIntegerBox a T, ‖f x‖ ≤ 1)
    (hu : ∀ x ∈ translatedIntegerBox a T, ‖u x‖ ≤ B)
    (hcorr : ρ ≤ ‖finiteCorrelation (translatedIntegerBox a T) f u‖) :
    let Q := translatedIntegerBox a T
    ρ ^ 2 / (2 * B ^ 2) - 2 ^ Fintype.card ι * δ ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
            (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ∧
          δ * Q.card < ((derivativeSupport Q h).card : ℝ) then (1 : ℝ) else 0) := by
  let Q := translatedIntegerBox a T
  have hQ : Q.Nonempty := translatedIntegerBox_nonempty T a
  have hq : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  have hd : ((cubeDifferenceSupport Q).card : ℝ) ≤ (2 : ℝ) ^ Fintype.card ι * Q.card := by
    exact_mod_cast card_box_differenceSupport_le a T
  have hloss : δ * (cubeDifferenceSupport Q).card / Q.card ≤ 2 ^ Fintype.card ι * δ := by
    apply (div_le_iff₀ hq).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd hδ]
  exact le_trans (by linarith) (weight_correlating_large_overlaps hQ f u hρ hB hδ hf hu hcorr)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem box_overlap_side_gt_of_card_gt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) (hT : ∀ i, 0 < T i) (h : ι → ℤ) {δ : ℝ}
    (hcard : δ * (translatedIntegerBox a T).card <
      ((derivativeSupport (translatedIntegerBox a T) h).card : ℝ)) (i : ι) :
    δ * T i < (((T i : ℤ) - |h i|).toNat : ℝ) := by
  have hlen (j : ι) : ((T j : ℤ) - |h j|).toNat ≤ T j := by
    have ha := abs_nonneg (h j)
    omega
  apply side_gt_of_prod_gt (fun j => (((T j : ℤ) - |h j|).toNat : ℝ))
    (fun j => (T j : ℝ)) (fun j => Nat.cast_nonneg _) (fun j => by exact_mod_cast hT j)
    (fun j => by exact_mod_cast hlen j) _ i
  rw [derivativeSupport_translatedIntegerBox] at hcard
  simpa only [translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod] using hcard

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankUnadaptedFactorization
namespace OAI

section

namespace Erdos3

theorem exists_rank_adapted_factorization_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      rankAdaptedNiltestBudget p ≤ (p + C) ^ C ∧
      (rankAdaptedNiltestBudget p + c) ^ c ≤ (p + C) ^ C ∧
      p + 1 ≤ (p + C) ^ C ∧ (p + 3) ^ 5 ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let A := (X + 3) ^ 11 + X + 2
  let B := A + (A + 2) ^ 2
  let P := B + (B + Polynomial.C c) ^ c + (X + 3) ^ 5 + X + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hB : 0 ≤ rankAdaptedNiltestBudget p := hp.trans (le_rankAdaptedNiltestBudget hp)
  have hpow : 0 ≤ (rankAdaptedNiltestBudget p + c) ^ c := by positivity
  have hinv : 0 ≤ (p + 3) ^ 5 := by positivity
  have htotal : rankAdaptedNiltestBudget p + (rankAdaptedNiltestBudget p + c) ^ c +
      (p + 3) ^ 5 + p + 1 ≤ (p + C) ^ C := by
    simpa [P, B, A, X, Polynomial.eval₂_pow, rankAdaptedNiltestBudget,
      rankAdaptedNiltestBase] using hbound p hp
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankIntervalFactorization
namespace OAI

section

namespace Erdos3

theorem exists_rank_interval_product_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      productNiltestBudget (rankIntervalInputBudget c p) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C c) ^ c + (X + (X + 2) ^ 2 + 3) + X + 5
  let P := (U + 2) ^ 2 + U + (U + (U ^ 2 + U + 3) ^ 2) + U ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, U, X, Polynomial.eval₂_pow, productNiltestBudget, productObservableLipBudget,
    rankIntervalInputBudget, raisedNiltestBudget] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonRankCoefficientCorrections
namespace OAI

section

namespace Erdos3

theorem exists_rank_common_data_budget (s c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + c) ^ c ≤ (p + C) ^ C ∧
      3 * (4 * p) * (4 * p) * (refiltrationCoordinateBudget ((p + c) ^ c) + 2) * (s + 1) ≤
        (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C c) ^ c
  let A := ((Y + 1 + (Y + 3) ^ 7 + 2) ^ 9 + Y + 4) ^ 4
  let P := Y + 3 * (4 * X) * (4 * X) * (A + 2) * Polynomial.C (s + 1)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hY : 0 ≤ (p + c) ^ c := by positivity
  have hA := refiltrationCoordinateBudget_nonneg hY
  have hcost : 0 ≤ 3 * (4 * p) * (4 * p) *
      (refiltrationCoordinateBudget ((p + c) ^ c) + 2) * (s + 1) := by positivity
  have hsum : (p + c) ^ c + 3 * (4 * p) * (4 * p) *
      (refiltrationCoordinateBudget ((p + c) ^ c) + 2) * (s + 1) ≤ (p + C) ^ C := by
    simpa [P, A, Y, X, refiltrationCoordinateBudget, Polynomial.eval₂_pow] using hbound p hp
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedFreeRecoveryBudget
namespace OAI

section

namespace Erdos3

theorem exists_sharedFreeRecoveryThreshold_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeRecoveryThreshold s q p ≤ (p + C) ^ C := by
  let R (X : Polynomial ℕ) := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let H (X : Polynomial ℕ) := X + R X + 2
  let G (X : Polynomial ℕ) := X + X * ((X + 2) ^ 7 + X)
  let V (X : Polynomial ℕ) := G (X + (X + (X + 3) ^ 7 + 2) ^ 4 + 1)
  let F (X : Polynomial ℕ) := (4 * X + (X + V (4 * X)) + 3) ^ 7
  let B : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X
  let I : Polynomial ℕ := Polynomial.X + H B +
    ((B + 3) ^ 2 + Polynomial.C s * Polynomial.X) + ((Polynomial.X + 2) ^ 3 + Polynomial.X)
  let Z : Polynomial ℕ := 8 * I + 1
  let A : Polynomial ℕ := 4 * Polynomial.X + (F (Polynomial.X + H Polynomial.X) + 1) +
    (Z + ((Z + 2) ^ 3 + (Z + 2) ^ 36))
  let T : Polynomial ℕ := (Z + 2) ^ 48 + (Z + 2) ^ 24 + Z + 1 + (A + 2) ^ 5
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hH : 0 ≤ coefficientFourHeightBudget p := coefficientFourHeightBudget_nonneg hp
  have hF : fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) ≤
      fourRefinementAnnihilatorBudget (p + coefficientFourHeightBudget p) := by
    unfold fourRefinementAnnihilatorBudget fourRefinementBasisBudget preimageBasisBudget
      sparseGeneratorBudget
    gcongr
  have hA : sharedFreeEquationInputBudget s q p ≤ sharedFreeEquationInputBudget s p p := by
    unfold sharedFreeEquationInputBudget
    linarith
  have hA0 := (sharedFreeEquationInputBudget_bounds s hq hp).1
  have hAp0 := (sharedFreeEquationInputBudget_bounds s hp hp).1
  have hz : 0 ≤ 8 * sharedRefinementInputBudget s p + 1 := by
    have h := (sharedRefinementInputBudget_bounds s hp).2.2.1
    linarith
  have hsep := separationBudget_nonneg hz
  have hupper : sharedFreeRecoveryThreshold s q p ≤
      separationBudget (8 * sharedRefinementInputBudget s p + 1) +
        (sharedFreeEquationInputBudget s p p + 2) ^ 5 := by
    unfold sharedFreeRecoveryThreshold
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · apply le_trans (pow_le_pow_left₀ (by positivity) (by linarith :
        sharedFreeEquationInputBudget s q p + 2 ≤ sharedFreeEquationInputBudget s p p + 2) 5)
      exact le_add_of_nonneg_left hsep
  apply hupper.trans
  simpa [T, A, Z, I, B, F, V, G, H, R, sharedFreeEquationInputBudget,
    sharedRefinementInputBudget, coefficientFourHeightBudget, refiltrationCoordinateBudget,
    fourRefinementAnnihilatorBudget, fourRefinementBasisBudget, preimageBasisBudget,
    sparseGeneratorBudget, separationBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseSubboxCost
namespace OAI

section

namespace Erdos3

theorem IsDenseCommonStrideBox.of_large_subbox {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p : ℝ} {A B : Finset (I → ℤ)} (hB : IsDenseCommonStrideBox N p B)
    (hshape : ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
      0 < m ∧ (∀ i, 0 < H i) ∧ A = commonStrideBox c m H)
    (hsub : A ⊆ B) (hloss : 2 * (1 - (A.card : ℝ) / B.card) ≤ 1) :
    IsDenseCommonStrideBox N (p + 1) A := by
  obtain ⟨c, m, H, hm, hH, hBsub, hBdense, rfl⟩ := hB
  obtain ⟨c', m', H', hm', hH', rfl⟩ := hshape
  have haxis (i : I) : (integerProgressionSupport (c i) m (H i)).Nonempty :=
    Finset.card_pos.mp (by simpa only [card_integerProgressionSupport _ _ _ hm] using hH i)
  have haxis' (i : I) : (integerProgressionSupport (c' i) m' (H' i)).Nonempty :=
    Finset.card_pos.mp (by simpa only [card_integerProgressionSupport _ _ _ hm'] using hH' i)
  refine ⟨c', m', H', hm', hH', ?_, ?_, rfl⟩
  · intro i
    exact (piFinset_axis_subset _ _ haxis' hsub i).trans (hBsub i)
  · intro i
    have hi := piFinset_card_ratio_le_axis _ _ haxis' haxis hsub i
    simp only [card_integerProgressionSupport _ _ _ hm, card_integerProgressionSupport _ _ _ hm'] at hi
    have hhalf : (1 / 2 : ℝ) ≤ (H' i : ℝ) / H i := by
      change ((commonStrideBox c' m' H').card : ℝ) / (commonStrideBox c m H).card ≤ _ at hi
      linarith
    have hlen : (H i : ℝ) ≤ 2 * H' i := by
      have ht := (le_div_iff₀ (by exact_mod_cast hH i : (0 : ℝ) < H i)).mp hhalf
      linarith
    have he : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
      simpa only [show -(p + 1) = -p - 1 by ring] using exp_sub_one_le_half_exp (-p)
    have hmul := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (N i))
    nlinarith [hBdense i]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DetectedCanonicalEarlyRadiusModelBounds
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem IsDenseCommonStrideBox.mono_parameter {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p q : ℝ} {A : Finset (I → ℤ)}
    (h : IsDenseCommonStrideBox N p A) (hpq : p ≤ q) :
    IsDenseCommonStrideBox N q A := by
  obtain ⟨c, step, H, hstep, hH, hsub, hdense, heq⟩ := h
  refine ⟨c, step, H, hstep, hH, hsub, fun i => ?_, heq⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg _)).trans (hdense i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

open CyclicCrootSisask

noncomputable def properAffineRankBound (P : ℝ) (n : ℕ) : ℝ :=
  2 + quarticBogolyubovConstant * (roundedModelLogBudget P n + 1) ^ 4

end Erdos3

end

end OAI
end


