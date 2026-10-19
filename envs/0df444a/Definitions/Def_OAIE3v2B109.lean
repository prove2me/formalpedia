-- Prove2me | Definitions.Def_OAIE3v2B109
-- name    : OAIE3v2B109
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:40:41.764517+00:00
-- url     : https://prove2.me/theorems/c787046d-5470-4912-bc88-642f66cec56d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 111 of 311
-- statement:
--   Definitions bundle 111 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B089`, `OAIE3v2B090`, `OAIE3v2B092`, `OAIE3v2B093`, `OAIE3v2B298`, `OAIE3v2B095`, `OAIE3v2B096` of this split.
--
--   Modules: `Dynamics/PreparedFiniteStageNativeBudget.lean`, `Dynamics/TranslationMajorDetectedPotential.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/MajorTranslationJointLower.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Estimates/VectorAlgebraicMajorDecomposition.lean`, `Estimates/WeightedAxisScaling.lean`, `Estimates/WeightedTranslationShearExponential.lean`, `Geometry/FiniteNormalizedChartCorrection.lean`, `Geometry/RealCoordinateFunctionals.lean`, `Geometry/TranslationShearCoordinateSeries.lean`, `Lattices/AlgebraicMajorWeightedAffineTopPullback.lean`, `Lattices/RealSpanIntegerDefiningRows.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Nilpotent/WeightedTranslationRealBCHCoordinates.lean`, `Polynomial/ControlledLinearPolynomialRestriction.lean`, `Polynomial/JointPolynomialDilationGrid.lean`, `Polynomial/MajorTranslationPolynomialSymbolDegree.lean`, `Polynomial/MajorWeightedDegreeTools.lean`, `Polynomial/PolynomialCoefficientGridDenominator.lean`, `Polynomial/PolynomialTagRestrictionBudget.lean`, `Polynomial/RealPolynomialChartSubstitution.lean`, `Polynomial/ShiftedPolynomialBasis.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Polynomial/VectorPolynomialAffineSubspace.lean`, `Polynomial/VectorPolynomialSubspaceSeparation.lean`, `Sampling/FiniteNormalizedRealGridCorrection.lean`, `Sampling/SamplingRankProjectedContainment.lean`, `Sampling/TranslationLogCoordinateInputGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B089
import Definitions.Def_OAIE3v2B090
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B093
import Definitions.Def_OAIE3v2B298
import Definitions.Def_OAIE3v2B095
import Definitions.Def_OAIE3v2B096

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem realPolynomialCoefficientGrid_iff (q : ℕ) (P : MvPolynomial σ ℝ) :
    realPolynomialCoefficientGrid q P ↔
      C (q : ℝ) * P ∈ integralRealPolynomialSubring σ := by
  rw [mem_integralRealPolynomialSubring_iff]
  simp only [coeff_C_mul]
  constructor
  · rintro ⟨z, hz⟩ m
    exact ⟨z m, congrFun hz m⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext hz⟩

theorem realPolynomialCoefficientGrid_add {q : ℕ} {P Q : MvPolynomial σ ℝ}
    (hP : realPolynomialCoefficientGrid q P) (hQ : realPolynomialCoefficientGrid q Q) :
    realPolynomialCoefficientGrid q (P + Q) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  rw [mul_add]
  exact (integralRealPolynomialSubring σ).add_mem
    ((realPolynomialCoefficientGrid_iff q P).mp hP)
    ((realPolynomialCoefficientGrid_iff q Q).mp hQ)

theorem realPolynomialCoefficientGrid_neg {q : ℕ} {P : MvPolynomial σ ℝ}
    (hP : realPolynomialCoefficientGrid q P) : realPolynomialCoefficientGrid q (-P) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  rw [mul_neg]
  exact (integralRealPolynomialSubring σ).neg_mem
    ((realPolynomialCoefficientGrid_iff q P).mp hP)

theorem realPolynomialCoefficientGrid_X (q : ℕ) (i : σ) :
    realPolynomialCoefficientGrid q (X i) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  exact (integralRealPolynomialSubring σ).mul_mem
    ⟨C (q : ℤ), by simp⟩
    (X_mem_integralRealPolynomialSubring i)

theorem realPolynomialCoefficientGrid_rename {τ : Type*} (f : σ → τ)
    {q : ℕ} {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid q (rename f P) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  simpa using rename_mem_integralRealPolynomialSubring f
    ((realPolynomialCoefficientGrid_iff q P).mp hP)

theorem realPolynomialCoefficientGrid_mono {q r : ℕ} (hqr : q ∣ r)
    {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid r P := by
  obtain ⟨k, rfl⟩ := hqr
  apply (realPolynomialCoefficientGrid_iff (q * k) _).mpr
  have hk : C (k : ℝ) ∈ integralRealPolynomialSubring σ := ⟨C (k : ℤ), by simp⟩
  have h := (integralRealPolynomialSubring σ).mul_mem
    hk
    ((realPolynomialCoefficientGrid_iff q P).mp hP)
  simpa [Nat.cast_mul, map_mul, mul_assoc, mul_left_comm] using h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem realPolynomialCoefficientGrid_substitute
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (qV qA d : ℕ) (hdegree : V.totalDegree ≤ d)
    (hV : realPolynomialCoefficientGrid qV V)
    (hA : ∀ i, realPolynomialCoefficientGrid qA (A i)) :
    realPolynomialCoefficientGrid (qV * qA ^ d) (aeval A V) := by
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  apply polynomial_substitution_cleared_mem (integralRealPolynomialSubring τ)
    V A qV qA d hdegree
  · obtain ⟨z, hz⟩ := hV
    intro m _
    have hm : (z m : ℝ) = (qV : ℝ) * V.coeff m := congrFun hz m
    rw [← hm]
    exact C_int_mem_integralRealPolynomialSubring (z m)
  · exact fun i => (realPolynomialCoefficientGrid_iff _ _).mp (hA i)
  · exact ⟨C (qA : ℤ), by simp⟩

theorem realPolynomialCoefficientGrid_substitute_common
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (q d : ℕ) (hdegree : V.totalDegree ≤ d)
    (hV : realPolynomialCoefficientGrid q V)
    (hA : ∀ i, realPolynomialCoefficientGrid q (A i)) :
    realPolynomialCoefficientGrid (q ^ (d + 1)) (aeval A V) := by
  simpa only [pow_succ'] using
    realPolynomialCoefficientGrid_substitute V A q q d hdegree hV hA

theorem majorShiftCoordinates_coefficientGrid {U B : Type*}
    (a : B → MvPolynomial U ℝ) (q : ℕ)
    (ha : ∀ b, realPolynomialCoefficientGrid q (a b)) (b : B) :
    realPolynomialCoefficientGrid q (majorShiftCoordinates a b) := by
  exact realPolynomialCoefficientGrid_add (realPolynomialCoefficientGrid_X q _)
    (realPolynomialCoefficientGrid_rename Sum.inl (ha b))

theorem majorRationalPolynomial_coefficientGrid {U B : Type*}
    (Q : MvPolynomial (U ⊕ B) ℝ) (V : MvPolynomial B ℝ)
    (a : B → MvPolynomial U ℝ) (q d : ℕ)
    (hdegree : V.totalDegree ≤ d)
    (hQ : realPolynomialCoefficientGrid q Q)
    (hV : realPolynomialCoefficientGrid q V)
    (ha : ∀ b, realPolynomialCoefficientGrid q (a b)) :
    realPolynomialCoefficientGrid (q ^ (d + 1)) (majorRationalPolynomial Q V a) := by
  apply realPolynomialCoefficientGrid_add
  · exact realPolynomialCoefficientGrid_mono (dvd_pow_self q (by omega)) hQ
  · exact realPolynomialCoefficientGrid_substitute_common V
      (majorShiftCoordinates (-a)) q d hdegree hV
      (majorShiftCoordinates_coefficientGrid (-a) q
        (fun b => realPolynomialCoefficientGrid_neg (ha b)))

theorem majorRationalPolynomial_denominatorGrid {U B : Type*}
    (Q : MvPolynomial (U ⊕ B) ℚ) (V : MvPolynomial B ℚ)
    (a : B → MvPolynomial U ℚ) (q d : ℕ)
    (hdegree : V.totalDegree ≤ d)
    (hQ : (fun m => Q.coeff m) ∈ denominatorGrid q)
    (hV : (fun m => V.coeff m) ∈ denominatorGrid q)
    (ha : ∀ b, (fun m => (a b).coeff m) ∈ denominatorGrid q) :
    (fun m => (majorRationalPolynomial Q V a).coeff m) ∈ denominatorGrid (q ^ (d + 1)) := by
  apply (realPolynomialCoefficientGrid_ratCast_iff _ _).mp
  rw [majorRationalPolynomial_map]
  apply majorRationalPolynomial_coefficientGrid
  · apply le_trans (b := V.totalDegree) ?_ hdegree
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) V hm)
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr hQ
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr hV
  · exact fun b => (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr (ha b)

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem realPolynomialCoefficientGrid_aeval_integral
    (P : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ) (q : ℕ)
    (hP : realPolynomialCoefficientGrid q P)
    (hA : ∀ i, realPolynomialCoefficientGrid 1 (A i)) :
    realPolynomialCoefficientGrid q (aeval A P) := by
  simpa only [one_pow, mul_one] using
    realPolynomialCoefficientGrid_substitute P A q 1 P.totalDegree le_rfl hP hA

theorem realPolynomialCoefficientGrid_intCast (P : MvPolynomial σ ℤ) :
    realPolynomialCoefficientGrid 1 (map (Int.castRingHom ℝ) P) := by
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  simpa only [Nat.cast_one, map_one, one_mul] using
    (show map (Int.castRingHom ℝ) P ∈ integralRealPolynomialSubring σ from ⟨P, rfl⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ υ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

theorem realChartSubstitute_comp (f : σ → MvPolynomial τ ℝ)
    (g : τ → MvPolynomial υ ℝ) (p : VectorPolynomial σ ℚ V) :
    realChartSubstitute g (realChartSubstitute f p) =
      realChartSubstitute (fun i => MvPolynomial.aeval g (f i)) p := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub, eval₂_realChartSubstitute, eval₂_realChartSubstitute,
    eval₂_realChartSubstitute]
  apply sub_eq_zero.mpr
  congr 2
  funext i
  change MvPolynomial.aeval (fun j => MvPolynomial.eval x (g j)) (f i) =
    MvPolynomial.aeval x (MvPolynomial.aeval g (f i))
  rw [MvPolynomial.comp_aeval_apply]
  rfl

theorem eval₂_normalizedRealPolynomialChart {U B : Type*}
    (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (u : U → ℝ) (b : B → ℝ) (p : VectorPolynomial (U ⊕ B) ℚ V) :
    eval₂ (Sum.elim u b) (realChartSubstitute (normalizedRealPolynomialChart H A) p) =
      eval₂ (Sum.elim (fun i => u i / H i) (fun j => b j - MvPolynomial.eval u (A j))) p := by
  rw [eval₂_realChartSubstitute]
  simp only [normalizedRealPolynomialChart_eval]

end Erdos3.VectorPolynomial

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

noncomputable def normalizedMajorLeft (E : MvPolynomial (U ⊕ B) ℝ)
    (e : B → MvPolynomial U ℝ) (H u : U → ℝ) : PolynomialTranslationGroupOver ℝ B :=
  ⟨fun j => eval (fun i => u i / H i) (e j),
    specializeMajorParameters (RingHom.id ℝ) E (fun i => u i / H i)⟩

noncomputable def rationalMajorRight (Q : MvPolynomial (U ⊕ B) ℚ)
    (a : B → MvPolynomial U ℚ) (u : U → ℝ) : PolynomialTranslationGroupOver ℝ B :=
  ⟨fun j => eval₂ (algebraMap ℚ ℝ) u (a j),
    specializeMajorParameters (algebraMap ℚ ℝ) Q u⟩

noncomputable def algebraicMajorSymbol (D : MvPolynomial (U ⊕ B) ℝ)
    (D₀ : MvPolynomial B ℝ) (A : B → MvPolynomial U ℝ) (u : U → ℝ) :
    PolynomialTranslationGroupOver ℝ B :=
  ⟨fun j => eval u (A j), specializeMajorParameters (RingHom.id ℝ) D u -
    polynomialTranslate (fun j => -eval u (A j)) D₀⟩

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

theorem weightedSupportLT_map (v : σ → ℕ) (w : τ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p ∈ weightedSupportLT v n) :
    F p ∈ weightedSupportLT w n := by
  cases n with
  | zero =>
      rw [weightedSupportLT_zero_eq hp, map_zero]
      exact Submodule.zero_mem _
  | succ n =>
      exact weightedSupportLE_lt_succ (polynomialHom_preserves_weightedDegree v w F hF
        (weightedSupportLT_succ_le hp))

theorem weightedComparison_monomial_one (v : σ → ℕ) (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    (hG : ∀ i, G (X i) ∈ weightedSupportLE w (v i))
    (hD : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT w (v i)) (a : σ →₀ ℕ) :
    F (monomial a 1) - G (monomial a 1) ∈ weightedSupportLT w (Finsupp.weight v a) := by
  classical
  have hsingle (i : σ) (n : ℕ) :
      F (monomial (Finsupp.single i n) 1) - G (monomial (Finsupp.single i n) 1) ∈
        weightedSupportLT w (n * v i) := by
    induction n with
    | zero =>
        simp only [Finsupp.single_zero, zero_mul]
        change F 1 - G 1 ∈ _
        rw [map_one, map_one, sub_self]
        exact Submodule.zero_mem _
    | succ n ih =>
        have hp := weightedSupportLE_monomial v (Finsupp.single i n) (1 : R)
        simp only [Finsupp.weight_single, smul_eq_mul] at hp
        have hh := weightedComparison_mul w F G (monomial (Finsupp.single i n) 1)
          (X i) (n * v i) (v i) (polynomialHom_preserves_weightedDegree v w G hG hp)
          (hF i) ih (hD i)
        simpa only [X, MvPolynomial.monomial_mul, one_mul, ← Finsupp.single_add, Nat.succ_mul]
          using hh
  induction a using Finsupp.induction with
  | zero =>
      change F 1 - G 1 ∈ weightedSupportLT w 0
      rw [map_one, map_one, sub_self]
      exact Submodule.zero_mem _
  | @single_add i n a hi hn ih =>
      have hp := weightedSupportLE_monomial v (Finsupp.single i n) (1 : R)
      have hq := weightedSupportLE_monomial v a (1 : R)
      have hh := weightedComparison_mul w F G (monomial (Finsupp.single i n) 1)
        (monomial a 1) (Finsupp.weight v (Finsupp.single i n)) (Finsupp.weight v a)
        (polynomialHom_preserves_weightedDegree v w G hG hp)
        (polynomialHom_preserves_weightedDegree v w F hF hq)
        (by simpa only [Finsupp.weight_single, smul_eq_mul] using hsingle i n) ih
      simpa only [MvPolynomial.monomial_mul, one_mul, map_add] using hh

theorem weightedComparison_monomial (v : σ → ℕ) (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    (hG : ∀ i, G (X i) ∈ weightedSupportLE w (v i))
    (hD : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT w (v i)) (a : σ →₀ ℕ) (r : R) :
    F (monomial a r) - G (monomial a r) ∈ weightedSupportLT w (Finsupp.weight v a) := by
  have hFc : F (C r) = C r := F.commutes r
  have hGc : G (C r) = C r := G.commutes r
  have hm : C r * monomial a (1 : R) = monomial a r := by
    change monomial 0 r * monomial a 1 = monomial a r
    rw [MvPolynomial.monomial_mul, zero_add, mul_one]
  rw [← hm, map_mul, map_mul, hFc, hGc, ← mul_sub]
  simpa only [zero_add] using weightedSupportLE_mul_LT (weightedSupportLE_C w 0 r)
    (weightedComparison_monomial_one v w F G hF hG hD a)

theorem weightedComparison_difference (v : σ → ℕ) (w : τ → ℕ)
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, F (X i) ∈ weightedSupportLE w (v i))
    (hG : ∀ i, G (X i) ∈ weightedSupportLE w (v i))
    (hD : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p ∈ weightedSupportLE v n) :
    F p - G p ∈ weightedSupportLT w n := by
  classical
  change (F.toLinearMap - G.toLinearMap : MvPolynomial σ R →ₗ[R] MvPolynomial τ R) p ∈
    weightedSupportLT w n
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLT w n).sum_mem
  intro a ha
  exact weightedSupportLT_mono (hp ha)
    (weightedComparison_monomial v w F G hF hG hD a (p.coeff a))

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem weightedSupportLE_totalDegree_le_of_pos {w : σ → ℕ}
    (hw : ∀ i, 0 < w i) {P : MvPolynomial σ R} {d : ℕ}
    (hP : P ∈ weightedSupportLE w d) : P.totalDegree ≤ d := by
  exact totalDegree_le_of_positive_weightedSupport w hw hP

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R]

theorem weightedSupportLE_finrank_le {K : Type*} [Field K] [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (n : ℕ) :
    finrank K (weightedSupportLE (R := K) w n) ≤ (Fintype.card σ + 1) ^ n := by
  classical
  let hs := Finsupp.finite_of_nat_weight_le w (fun i => (hw i).ne') n
  let : Fintype {a : σ →₀ ℕ | Finsupp.weight w a ≤ n} := hs.fintype
  have hcard := boundedExponentSet_card_le hs.toFinset n (fun a ha =>
    (exponentSum_le_positive_weight w hw a).trans (hs.mem_toFinset.mp ha))
  change finrank K (MvPolynomial.restrictSupport K
    {a : σ →₀ ℕ | Finsupp.weight w a ≤ n}) ≤ _
  rw [finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K
    {a : σ →₀ ℕ | Finsupp.weight w a ≤ n})]
  simpa only [Set.Finite.card_toFinset] using hcard

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {B U : Type*}

noncomputable def translationPhaseFunction (D₀ : MvPolynomial B ℝ)
    (g : PolynomialTranslationGroupOver ℝ B) : ℂ :=
  Real.fourierChar (translationPhaseArgument D₀ g (fun i => (⌊g.base i + 1 / 2⌋ : ℝ)))

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {U X : Type*}

theorem real_grid_polynomial_residue_difference (R : MvPolynomial U ℝ)
    (q : ℕ) (hq : 0 < q) (hR : realPolynomialCoefficientGrid q R)
    (r v : U → ℤ) :
    ∃ k : ℤ,
      eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) R -
        eval (fun i => (r i : ℝ)) R = (k : ℝ) := by
  obtain ⟨S, hS⟩ := (realPolynomialCoefficientGrid_iff q R).mp hR
  have heval (y : U → ℤ) : (eval y S : ℝ) =
      (q : ℝ) * eval (fun i => (y i : ℝ)) R := by
    rw [← eval_integer_polynomial_real, hS, map_mul, eval_C]
  obtain ⟨k, hk⟩ := integer_polynomial_sub_dvd S
    (fun i => r i + (q : ℤ) * v i) r (q : ℤ) (fun i => by
      exact ⟨v i, by ring⟩)
  refine ⟨k, ?_⟩
  apply mul_left_cancel₀ (show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne')
  calc
    (q : ℝ) * (eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) R -
        eval (fun i => (r i : ℝ)) R) =
        ((eval (fun i => r i + (q : ℤ) * v i) S - eval r S : ℤ) : ℝ) := by
      rw [Int.cast_sub, heval, heval, mul_sub]
    _ = (q : ℝ) * (k : ℝ) := by exact_mod_cast hk

theorem localMajorLowerPhase_cancellation (n q : ℕ) (hq : 0 < q)
    (r v : U → ℤ) (P E R : MvPolynomial U ℝ)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R) :
    (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) P) : ℂ) *
        star (Real.fourierChar (eval (fun i => (v i : ℝ))
          (localMajorLowerPhase n q r P)) : ℂ) =
      (Real.fourierChar
        (eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) E +
          eval (fun i => (r i : ℝ)) R) : ℂ) := by
  rw [show localMajorLowerPhase n q r P =
    residueAffinePolynomial q r (P - homogeneousComponent (n + 1) P) from rfl,
    residueAffinePolynomial_eval, map_sub, htop, map_add]
  rw [← real_fourierChar_sub_star]
  rw [sub_sub_cancel]
  obtain ⟨k, hk⟩ := real_grid_polynomial_residue_difference R q hq hR r v
  have hr : eval (fun i => ((r i + (q : ℤ) * v i : ℤ) : ℝ)) R =
      eval (fun i => (r i : ℝ)) R + (k : ℝ) := by linarith
  rw [hr, ← add_assoc, real_fourierChar_add_integer]

theorem localMajorPhaseCorrelation [Fintype X]
    (p : FiniteProbabilityWeights X) (v : X → U → ℤ)
    (n q : ℕ) (hq : 0 < q) (r : U → ℤ)
    (P E R : MvPolynomial U ℝ) (hP : P.totalDegree ≤ n + 1)
    (htop : homogeneousComponent (n + 1) P = E + R)
    (hR : realPolynomialCoefficientGrid q R) (a ε : ℝ)
    (hslow : ∀ x, 0 < p.weight x →
      |eval (fun i => ((r i + (q : ℤ) * v x i : ℤ) : ℝ)) E - a| ≤ ε) :
    (localMajorLowerPhase n q r P).totalDegree ≤ n ∧
    1 - 2 * Real.pi * ε ≤ ‖p.complexMean (fun x =>
      (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * v x i : ℤ) : ℝ)) P) : ℂ) *
        star (Real.fourierChar (eval (fun i => (v x i : ℝ))
          (localMajorLowerPhase n q r P)) : ℂ))‖ := by
  refine ⟨localMajorLowerPhase_totalDegree_le n q r P hP, ?_⟩
  let f : X → ℂ := fun x =>
    (Real.fourierChar (eval (fun i => ((r i + (q : ℤ) * v x i : ℤ) : ℝ)) P) : ℂ) *
      star (Real.fourierChar (eval (fun i => (v x i : ℝ))
        (localMajorLowerPhase n q r P)) : ℂ)
  let c : ℂ := Real.fourierChar (a + eval (fun i => (r i : ℝ)) R)
  have hpoint (x : X) (hx : p.weight x ≠ 0) : ‖f x - c‖ ≤ 2 * Real.pi * ε := by
    dsimp only [f, c]
    rw [localMajorLowerPhase_cancellation n q hq r (v x) P E R htop hR]
    refine (real_fourierChar_norm_sub_le _ _).trans ?_
    rw [add_sub_add_right_eq_sub]
    exact mul_le_mul_of_nonneg_left (hslow x (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)))
      (by positivity)
  have havg := p.norm_complexMean_sub_le f (fun _ => c) (fun _ => 2 * Real.pi * ε) hpoint
  rw [p.complexMean_const, p.mean_const] at havg
  have hc : ‖c‖ = 1 := Circle.norm_coe _
  have hnorm := norm_le_norm_add_norm_sub (p.complexMean f) c
  rw [hc] at hnorm
  change 1 - 2 * Real.pi * ε ≤ ‖p.complexMean f‖
  linarith

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointPolynomialDilationGrid
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem jointPolynomialDilation_coefficientGrid
    (R : MvPolynomial (U ⊕ B) ℝ) (q l d : ℕ) (hq : 0 < q)
    (hdegree : R.totalDegree ≤ d) (hR : realPolynomialCoefficientGrid l R) :
    realPolynomialCoefficientGrid (q ^ d * l)
      (scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)⁻¹) (fun _ : B => 1)) R) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [scaleMvPolynomialAxes_eq_aeval, Nat.mul_comm (q ^ d) l]
  apply realPolynomialCoefficientGrid_substitute R _ l q d hdegree hR
  intro i
  cases i with
  | inl u =>
    apply (realPolynomialCoefficientGrid_iff _ _).mpr
    simp only [Sum.elim_inl]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_mul]
    exact X_mem_integralRealPolynomialSubring _
  | inr b =>
    simpa only [Sum.elim_inr, map_one, one_mul] using
      realPolynomialCoefficientGrid_X q (Sum.inr b : U ⊕ B)

theorem jointRationalPolynomialDilation_denominatorGrid
    (R : MvPolynomial (U ⊕ B) ℚ) (q l d : ℕ) (hq : 0 < q)
    (hdegree : R.totalDegree ≤ d)
    (hR : (fun α => R.coeff α) ∈ denominatorGrid l) :
    (fun α => (jointRationalPolynomialDilation q R).coeff α) ∈
      denominatorGrid (q ^ d * l) := by
  apply (realPolynomialCoefficientGrid_ratCast_iff _ _).mp
  rw [jointRationalPolynomialDilation_map]
  apply jointPolynomialDilation_coefficientGrid _ q l d hq
  · apply le_trans (b := R.totalDegree) ?_ hdegree
    unfold totalDegree
    apply Finset.sup_le
    intro α hα
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) R hα)
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr hR

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedAxisScaling
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem isWeightedHomogeneous_algHom (v : σ → ℕ) (w : τ → ℕ)
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, (F (X i)).IsWeightedHomogeneous w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsWeightedHomogeneous v n) :
    (F p).IsWeightedHomogeneous w n := by
  classical
  rw [MvPolynomial.aeval_unique F]
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply IsWeightedHomogeneous.sum
  intro a ha
  have hweight : Finsupp.weight v a = n := hp (mem_support_iff.mp ha)
  rw [← hweight]
  exact isWeightedHomogeneous_aeval_monomial v w (fun i => F (X i)) hF a _

theorem aeval_isWeightedHomogeneous (v : σ → ℕ) (w : τ → ℕ)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (v i))
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsWeightedHomogeneous v n) :
    (aeval f p).IsWeightedHomogeneous w n := by
  apply isWeightedHomogeneous_algHom v w (aeval f) _ hp
  intro i
  simpa only [aeval_X] using hf i

end Erdos3


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U B : Type*} [Fintype B]

theorem translationDirectionalDerivative_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous v (w i))
    {P : MvPolynomial (U ⊕ B) ℝ} {d : ℕ}
    (hP : P.IsWeightedHomogeneous (Sum.elim v w) d) :
    (translationDirectionalDerivative b P).IsWeightedHomogeneous (Sum.elim v w) d := by
  classical
  rw [translationDirectionalDerivative_apply]
  apply (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).sum_mem
  intro i _
  apply isWeightedHomogeneous_mul_pderiv (Sum.elim v w) (Sum.inr i) _ hP
  rw [rename_eq_aeval]
  exact aeval_isWeightedHomogeneous v (Sum.elim v w) (X ∘ Sum.inl)
    (fun j => isWeightedHomogeneous_X ℝ (Sum.elim v w) (Sum.inl j)) (hb i)

theorem translationDirectionalDerivative_pow_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous v (w i))
    {P : MvPolynomial (U ⊕ B) ℝ} {d : ℕ}
    (hP : P.IsWeightedHomogeneous (Sum.elim v w) d) (n : ℕ) :
    (((translationDirectionalDerivative b) ^ n) P).IsWeightedHomogeneous
      (Sum.elim v w) d := by
  induction n with
  | zero => simpa using hP
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact translationDirectionalDerivative_isWeightedHomogeneous v w b hb ih

theorem translationDirectionalSeries_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (N : ℕ) (b : B → MvPolynomial U ℝ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous v (w i))
    {P : MvPolynomial (U ⊕ B) ℝ} {d : ℕ}
    (hP : P.IsWeightedHomogeneous (Sum.elim v w) d) :
    (translationDirectionalSeries N b P).IsWeightedHomogeneous (Sum.elim v w) d := by
  classical
  apply (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).sum_mem
  intro i _
  exact (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).smul_mem _
    (translationDirectionalDerivative_pow_isWeightedHomogeneous v w b hb hP i)

end Erdos3


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

theorem weightedSubalgebra_finrank_le (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) :
    Module.finrank ℚ (weightedSubalgebra w d) ≤
      Fintype.card σ + (Fintype.card σ + 1)^d := by
  let := weightedSupportLE_moduleFinite (R := ℚ) w hw d
  have h := LinearMap.finrank_le_finrank_of_injective (weightedCoordinates_injective w d)
  calc
    Module.finrank ℚ (weightedSubalgebra w d) ≤
      Module.finrank ℚ ((σ → ℚ) × weightedSupportLE (R := ℚ) w d) := h
    _ = Fintype.card σ + Module.finrank ℚ (weightedSupportLE (R := ℚ) w d) := by
      rw [Module.finrank_prod, Module.finrank_pi_fintype]
      simp
    _ ≤ _ := Nat.add_le_add_left (weightedSupportLE_finrank_le w hw d) _

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem polynomialSymbolDilation_mul (w : σ → ℕ) (a b : ℚ) (x : F.PolynomialSymbol w) :
    F.polynomialSymbolDilation w (a * b) x =
      F.polynomialSymbolDilation w a (F.polynomialSymbolDilation w b x) := by
  apply F.polynomialSymbol_ext w
  intro α
  simp only [F.polynomialSymbolCoefficient_dilation, mul_pow, smul_smul]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (v : σ → ℕ)

theorem truncateRealSymbol_slow (j : ℕ) (g : F.RealPolynomialSymbolGroup v)
    (T : σ → ℝ) (M : ℝ) (hg : F.SymbolSlowBound b w hlayers v T M g) :
    F.SymbolSlowBound b w hlayers v T M (F.truncateRealSymbol b w hlayers v j g) := by
  intro z
  exact (basisCoordinateProjection_abs_repr_le
    ((F.polynomialSymbolBasis b w hlayers v).baseChange ℝ) {z | w z.val.2 < j} g.coord z).trans (hg z)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationPolynomialSymbolDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem polynomialSlotCoefficient_weightedHomogeneousComponent
    {U B R : Type*} [CommRing R] (v : U → ℕ) (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial (U ⊕ B) R}
    (hP : P ∈ weightedSupportLE (Sum.elim v w) d) (α : B →₀ ℕ) :
    weightedHomogeneousComponent v (d - Finsupp.weight w α) (polynomialSlotCoefficient α P) =
      polynomialSlotCoefficient α (weightedHomogeneousComponent (Sum.elim v w) d P) := by
  classical
  ext β
  rw [coeff_weightedHomogeneousComponent, polynomialSlotCoefficient_coeff,
    polynomialSlotCoefficient_coeff, coeff_weightedHomogeneousComponent, sumExponent_weight]
  by_cases hc : P.coeff (β.sumElim α) = 0
  · simp only [hc, ite_self]
  · have hdegree : Finsupp.weight (Sum.elim v w) (β.sumElim α) ≤ d :=
      hP (mem_support_iff.mpr hc)
    rw [sumExponent_weight] at hdegree
    have heq : Finsupp.weight v β = d - Finsupp.weight w α ↔
        Finsupp.weight v β + Finsupp.weight w α = d := by omega
    simp only [heq]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem specializeMajorParameters_mem_weightedSupportLT (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial (U ⊕ B) ℝ}
    (hP : P ∈ weightedSupportLT (Sum.elim (fun _ : U => 0) w) d)
    (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) P u ∈ weightedSupportLT w d := by
  change aeval (Sum.elim (fun i => C (u i)) X) P ∈ weightedSupportLT w d
  apply weightedSupportLT_aeval _ _ _ _ hP
  intro i
  cases i with
  | inl j => exact weightedSupportLE_C w 0 (u j)
  | inr j => exact weightedSupportLE_X w j

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorParameterRename_degree (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial U ℝ} {d : ℕ} (hP : P ∈ weightedSupportLE v d) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) d := by
  apply polynomialHom_preserves_weightedDegree v (Sum.elim v w) (rename Sum.inl) _ hP
  intro i
  simpa only [rename_X, Sum.elim_inl] using
    weightedSupportLE_X (R := ℝ) (Sum.elim v w) (Sum.inl i)

theorem majorParameterRename_slot_degree_zero (w : B → ℕ) (P : MvPolynomial U ℝ) :
    rename (Sum.inl : U → U ⊕ B) P ∈
      weightedSupportLE (Sum.elim (fun _ : U => 0) w) 0 := by
  apply majorParameterRename_degree
  intro α _
  simp [Finsupp.weight_apply]

theorem majorTranslationJointPolynomial_degree (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) (hx : ∀ j, (x j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D x ∈
      weightedSupportLE (Sum.elim (fun _ : U => 1) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply (weightedSupportLE _ _).sub_mem hD
  apply weightedSupportLE_aeval _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr j =>
      exact (weightedSupportLE _ _).sub_mem
        (weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inr j))
        (majorParameterRename_degree (fun _ => 1) w
          ((mem_weightedSupportLE_one_iff (x j) (w j)).mpr (hx j)))

theorem majorTranslationJointPolynomial_slot_lower (w : B → ℕ) (hw : ∀ j, 0 < w j)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) :
    majorTranslationJointPolynomial D x ∈
      weightedSupportLT (Sum.elim (fun _ : U => 0) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply weightedComparison_difference (Sum.elim (fun _ : U => 1) w)
    (Sum.elim (fun _ : U => 0) w) (AlgHom.id ℝ _)
    (aeval (Sum.elim (fun _ : U => 0)
      (fun j => X (Sum.inr j) - rename Sum.inl (x j)))) _ _ _ hD
  · intro i
    cases i with
    | inl i =>
        exact weightedSupportLE_mono (by decide : 0 ≤ 1)
          (weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inl i))
    | inr j => exact weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inr j)
  · intro i
    simp only [aeval_X]
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr j =>
        exact (weightedSupportLE _ _).sub_mem
          (weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inr j))
          (weightedSupportLE_mono (Nat.zero_le _) (majorParameterRename_slot_degree_zero w (x j)))
  · intro i
    simp only [AlgHom.id_apply, aeval_X]
    cases i with
    | inl i =>
        simp only [Sum.elim_inl, sub_zero]
        exact weightedSupportLE_lt_succ
          (weightedSupportLE_X (Sum.elim (fun _ : U => 0) w) (Sum.inl i))
    | inr j =>
        simp only [Sum.elim_inr, sub_sub_cancel]
        intro α hα
        exact (majorParameterRename_slot_degree_zero w (x j) hα).trans_lt (hw j)

theorem majorTranslationJointPolynomial_specialize_lower (w : B → ℕ)
    (hw : ∀ j, 0 < w j) {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (x : B → MvPolynomial U ℝ) (u : U → ℝ) :
    specializeMajorParameters (RingHom.id ℝ) (majorTranslationJointPolynomial D x) u ∈
      weightedSupportLT w d :=
  specializeMajorParameters_mem_weightedSupportLT w
    (majorTranslationJointPolynomial_slot_lower w hw hD x) u

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorParameterRename_lower (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial U ℝ} {d : ℕ} (hP : P ∈ weightedSupportLT v d) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLT (Sum.elim v w) d := by
  apply weightedSupportLT_map v (Sum.elim v w) (rename Sum.inl) _ hP
  intro i
  simpa only [rename_X, Sum.elim_inl] using
    weightedSupportLE_X (R := ℝ) (Sum.elim v w) (Sum.inl i)

theorem majorParameterRename_homogeneous (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial U ℝ} {d : ℕ} (hP : P.IsWeightedHomogeneous v d) :
    (rename (Sum.inl : U → U ⊕ B) P).IsWeightedHomogeneous (Sum.elim v w) d := by
  rw [rename_eq_aeval]
  exact aeval_isWeightedHomogeneous v (Sum.elim v w) (X ∘ Sum.inl)
    (fun i => isWeightedHomogeneous_X (R := ℝ) (Sum.elim v w) (Sum.inl i)) hP

theorem majorTranslationJointPolynomial_top_homogeneous (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) :
    (majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A)).IsWeightedHomogeneous
      (Sum.elim (fun _ : U => 1) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply hD.sub
  apply aeval_isWeightedHomogeneous _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact isWeightedHomogeneous_zero ℝ _ _
  | inr j =>
      exact (isWeightedHomogeneous_X (R := ℝ) (Sum.elim (fun _ : U => 1) w) (Sum.inr j)).sub
        (majorParameterRename_homogeneous (fun _ => 1) w
          (majorTranslationTopCoordinates_homogeneous w A j))

theorem majorTranslationJointPolynomial_sub_top_lower (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D A -
      majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A) ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  let v := Sum.elim (fun _ : U => 1) w
  let F := aeval (R := ℝ) (Sum.elim (fun _ : U => 0)
    (fun j => X (Sum.inr j) - rename Sum.inl (A j)))
  let G := aeval (R := ℝ) (Sum.elim (fun _ : U => 0)
    (fun j => X (Sum.inr j) - rename Sum.inl (majorTranslationTopCoordinates w A j)))
  have hF : ∀ i, F (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simp only [F, aeval_X]
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr j =>
        exact (weightedSupportLE _ _).sub_mem (weightedSupportLE_X v (Sum.inr j))
          (majorParameterRename_degree (fun _ => 1) w
            ((mem_weightedSupportLE_one_iff _ _).mpr (hA j)))
  have hG : ∀ i, G (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simp only [G, aeval_X]
    cases i with
    | inl i => exact Submodule.zero_mem _
    | inr j =>
        exact (weightedSupportLE _ _).sub_mem (weightedSupportLE_X v (Sum.inr j))
          (majorParameterRename_degree (fun _ => 1) w
            ((mem_weightedSupportLE_one_iff _ _).mpr (majorTranslationTopCoordinates_degree w A j)))
  have hdiff : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT v (v i) := by
    intro i
    simp only [F, G, aeval_X]
    cases i with
    | inl i => simp only [Sum.elim_inl, sub_self]; exact Submodule.zero_mem _
    | inr j =>
        have h := (weightedSupportLT v (w j)).neg_mem
          (majorParameterRename_lower (fun _ => 1) w (majorTranslationTopCoordinates_remainder w A hA j))
        change (X (Sum.inr j) - rename Sum.inl (A j)) -
          (X (Sum.inr j) - rename Sum.inl (majorTranslationTopCoordinates w A j)) ∈
            weightedSupportLT v (w j)
        have he : (X (Sum.inr j) - rename Sum.inl (A j)) -
            (X (Sum.inr j) - rename Sum.inl (majorTranslationTopCoordinates w A j)) =
            -rename (Sum.inl : U → U ⊕ B) (A j - majorTranslationTopCoordinates w A j) := by
          rw [map_sub]
          abel
        rw [he]
        exact h
  have h := (weightedSupportLT v d).neg_mem (weightedComparison_difference v v F G hF hG hdiff hD)
  rw [majorTranslationJointPolynomial_eq_sub_aeval, majorTranslationJointPolynomial_eq_sub_aeval]
  change (D - F D) - (D - G D) ∈ weightedSupportLT v d
  convert h using 1
  abel

theorem majorTranslationJointPolynomial_weightedHomogeneousComponent (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (majorTranslationJointPolynomial D A) =
      majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A) := by
  have hle : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
    fun _ hα => (hD (mem_support_iff.mp hα)).le
  have hlower := majorTranslationJointPolynomial_sub_top_lower w hle A hA
  have hzero : weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
      (majorTranslationJointPolynomial D A -
        majorTranslationJointPolynomial D (majorTranslationTopCoordinates w A)) = 0 :=
    weightedHomogeneousComponent_eq_zero' d _ (fun α hα => (hlower hα).ne)
  rw [map_sub, (majorTranslationJointPolynomial_top_homogeneous w hD A).weightedHomogeneousComponent_same,
    sub_eq_zero] at hzero
  exact hzero

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

theorem algebraic_major_weighted_dilation_pullback_decomposition
    (w : B → ℕ) (hw : ∀ i, 0 < w i)
    (K : Submodule ℝ (B → ℝ)) (D : MvPolynomial (U ⊕ B) ℝ)
    (A : B → MvPolynomial U ℝ) (S : MvPolynomial (U ⊕ B) ℝ)
    (R : MvPolynomial (U ⊕ B) ℚ) (q : ℕ) (hq : 0 < q)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim (fun i => (q : ℝ) * v i) b) D =
        eval (Sum.elim (fun i => v i / T i)
          (fun j => b j - eval (fun i => (q : ℝ) * v i) (A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (c C : ℝ) (hc : 1 ≤ c) (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i)
    (d l : ℕ)
    (hS : S ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hR : R ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (hSmass : realPolynomialMass S ≤ C)
    (hRgrid : (fun α => R.coeff α) ∈ denominatorGrid l) :
    ∃ (S' : MvPolynomial (U ⊕ B) ℝ) (R' : MvPolynomial (U ⊕ B) ℚ),
      S' = majorSlowDilationPullback q H T S ∧
      R' = jointRationalPolynomialDilation q R ∧
      (∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
        eval (Sum.elim u b) D =
          eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j))) S' +
          eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) R') ∧
      realPolynomialMass S' ≤ c^d * C ∧
      S' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      R' ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d ∧
      S'.totalDegree ≤ d ∧ R'.totalDegree ≤ d ∧
      (fun α => R'.coeff α) ∈ denominatorGrid (q^d*l) := by
  have hpos : ∀ i : U ⊕ B, 0 < Sum.elim (fun _ : U => 1) w i :=
    Sum.rec (fun _ => Nat.zero_lt_one) hw
  have hSdeg := weightedSupportLE_totalDegree_le_of_pos hpos hS
  have hRdeg := weightedSupportLE_totalDegree_le_of_pos hpos hR
  have hS' := majorSlowDilationPullback_mem_weightedSupportLE q H T S _ d hS
  have hR' := jointRationalPolynomialDilation_mem_weightedSupportLE q R _ d hR
  refine ⟨majorSlowDilationPullback q H T S, jointRationalPolynomialDilation q R,
    rfl, rfl,
    algebraic_major_dilation_pullback_identity K D A S R q hq H T hH hT hsource,
    ?_, hS', hR', weightedSupportLE_totalDegree_le_of_pos hpos hS',
    weightedSupportLE_totalDegree_le_of_pos hpos hR', ?_⟩
  · exact (majorSlowDilationPullback_mass_le q hq H T hH hT S hc hHT hSdeg).trans
      (mul_le_mul_of_nonneg_left hSmass (pow_nonneg (le_trans zero_le_one hc) d))
  · exact jointRationalPolynomialDilation_denominatorGrid R q l d hq hRdeg hRgrid

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem jointResidueAffinePolynomial_sub_axes_lower (w : B → ℕ) (q : ℕ) (r : U → ℤ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    jointResidueAffinePolynomial q r D -
      scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1)) D ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  let v := Sum.elim (fun _ : U => 1) w
  let F : MvPolynomial (U ⊕ B) ℝ →ₐ[ℝ] MvPolynomial (U ⊕ B) ℝ := aeval (R := ℝ) (Sum.elim
    (fun i => C (r i : ℝ) + C (q : ℝ) * X (Sum.inl i)) (fun j => X (Sum.inr j)))
  let T := Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1)
  let G := aeval (R := ℝ) (fun i : U ⊕ B => C (T i) * X i)
  have hF : ∀ i, F (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simpa only [F, aeval_X] using jointResidueAffine_variables_degree w q r i
  have hG : ∀ i, G (X i) ∈ weightedSupportLE v (v i) := by
    intro i
    simpa only [G, aeval_X, zero_add] using
      weightedSupportLE_mul (weightedSupportLE_C v 0 (T i)) (weightedSupportLE_X v i)
  have hdiff : ∀ i, F (X i) - G (X i) ∈ weightedSupportLT v (v i) := by
    intro i
    cases i with
    | inl i =>
      simp only [F, G, T, aeval_X, Sum.elim_inl, add_sub_cancel_right]
      exact weightedSupportLE_lt_succ (weightedSupportLE_C v 0 (r i : ℝ))
    | inr j =>
      simp only [F, G, T, aeval_X, Sum.elim_inr, map_one, one_mul, sub_self]
      exact Submodule.zero_mem _
  rw [scaleMvPolynomialAxes_eq_aeval]
  exact weightedComparison_difference v v F G hF hG hdiff hD

theorem jointResidueAffinePolynomial_weightedHomogeneousComponent (w : B → ℕ)
    (q d : ℕ) (r : U → ℤ) (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d) :
    weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (jointResidueAffinePolynomial q r D) =
      scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1))
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) := by
  have hlower := jointResidueAffinePolynomial_sub_axes_lower w q r hD
  have hzero : weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
      (jointResidueAffinePolynomial q r D -
        scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)) (fun _ : B => 1)) D) = 0 :=
    weightedHomogeneousComponent_eq_zero' d _ (fun α hα => (hlower hα).ne)
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero, scaleMvPolynomialAxes_weightedHomogeneousComponent]

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial

variable {U B : Type*}

 theorem jointResidueAffinePolynomial_weightedHomogeneousComponent_eval
    (w : B → ℕ) (q d : ℕ) (r : U → ℤ) (D : MvPolynomial (U ⊕ B) ℝ)
    (hD : D ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (v : U → ℝ) (b : B → ℝ) :
    eval (Sum.elim v b)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
        (jointResidueAffinePolynomial q r D)) =
    eval (Sum.elim (fun i => (q : ℝ) * v i) b)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d D) := by
  rw [jointResidueAffinePolynomial_weightedHomogeneousComponent w q d r D hD,
    scaleMvPolynomialAxes_eval]
  apply congrArg (fun x : U ⊕ B → ℝ => eval x _)
  funext i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealSpanIntegerDefiningRows
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_real_span_integer_defining_matrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ C : Matrix ι ι ℤ,
      (∀ i j, |(C i j : ℝ)| ≤
        (realSpanIntegerRowBound (Fintype.card κ) (Fintype.card ι) H : ℝ)) ∧
      LinearMap.ker (Matrix.mulVecLin (fun i j => (C i j : ℝ))) =
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  classical
  obtain ⟨Q, hQ, hker⟩ := exists_real_span_defining_matrix A hH hA
  have hcast (i j : ι) :
      (clearedMatrix Q i j : ℝ) = (matrixDenominator Q : ℝ) * (Q i j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast Q) i) j
    change (clearedMatrix Q i j : ℚ) = (matrixDenominator Q : ℚ) * Q i j at h
    exact_mod_cast h
  refine ⟨clearedMatrix Q, ?_, ?_⟩
  · intro i j
    rw [hcast, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hd := Nat.cast_le (α := ℝ).mpr (matrixDenominator_le Q hQ)
    have hentry := (hQ i j).abs_real_le
    exact (mul_le_mul hd hentry (abs_nonneg _) (Nat.cast_nonneg _)).trans_eq
      (by simp only [realSpanIntegerRowBound, Nat.cast_mul])
  · have hden : (matrixDenominator Q : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (matrixDenominator_pos Q)).ne'
    have hmatrix : Matrix.of (fun i j => (clearedMatrix Q i j : ℝ)) =
        (matrixDenominator Q : ℝ) • Matrix.of (fun i j => (Q i j : ℝ)) := by
      ext i j
      exact hcast i j
    calc
      LinearMap.ker (Matrix.mulVecLin (fun i j => (clearedMatrix Q i j : ℝ))) =
          LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) := by
        ext x
        change (Matrix.of (fun i j => (clearedMatrix Q i j : ℝ)) *ᵥ x = 0) ↔
          (Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0)
        rw [hmatrix, Matrix.smul_mulVec]
        simp [hden]
      _ = _ := hker

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

open VectorPolynomial

theorem integerRowPolynomial_coefficientGrid {σ J : Type*} [Fintype J]
    (a : J → ℤ) (Q : VectorPolynomial σ ℝ (J → ℝ)) (q : ℕ)
    (hQ : ∀ α, coefficients Q α ∈ realDenominatorGrid q) :
    realPolynomialCoefficientGrid q (integerRowPolynomial a Q) := by
  classical
  have hz : ∀ α, ∃ z : J → ℤ, ∀ j, (z j : ℝ) = (q : ℝ) * coefficients Q α j := by
    intro α
    obtain ⟨z, hz⟩ := hQ α
    exact ⟨z, fun j => congrFun hz j⟩
  choose z hz using hz
  refine ⟨fun α => ∑ j, a j * z α j, funext fun α => ?_⟩
  change ((∑ j, a j * z α j : ℤ) : ℝ) = (q : ℝ) * (integerRowPolynomial a Q).coeff α
  simp only [Int.cast_sum, Int.cast_mul, integerRowPolynomial_coeff, Finset.mul_sum, hz]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NormalizedScalarCubeSource

abbrev CoefficientDomain (s : NormalizedScalarCubeSource Empty) :=
  ↥(coefficientResidueSet s.length (s.modulus none) (s.residue none))

theorem weight_empty_coordinate (s : NormalizedScalarCubeSource Empty)
    (x : IntegerScalarCubeBox Empty s.length) :
    s.weight (fun i => (x i : ℝ) / s.length) = s.weight (fun _ => (x none : ℝ) / s.length) := by
  congr 1
  funext i
  cases i with
  | none => rfl
  | some a => exact a.elim

noncomputable def coefficientDensity (s : NormalizedScalarCubeSource Empty) (z : s.CoefficientDomain) : ℝ :=
  s.weight (fun _ => (z.val : ℝ) / s.length)

end NormalizedScalarCubeSource

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

theorem realifyCoordinateMap_comp {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ℓ : W →ₗ[ℚ] (J → ℚ)) (f : V →ₗ[ℚ] W) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap (ℓ.comp f) x = realifyCoordinateMap ℓ (f.baseChange ℝ x) := by
  funext j
  exact realifyFunctional_comp ((LinearMap.proj j).comp ℓ) f x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationRealBCHCoordinates
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem eval_translate_rational {σ : Type*} (z h : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    eval z (polynomialTranslate h P) = eval (z + h) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Pi.add_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MajorTranslationJointLower
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem majorTranslationJointPolynomial_lower (w : B → ℕ)
    {d : ℕ} {D : MvPolynomial (U ⊕ B) ℝ}
    (hD : D ∈ weightedSupportLT (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ j, (A j).totalDegree ≤ w j) :
    majorTranslationJointPolynomial D A ∈
      weightedSupportLT (Sum.elim (fun _ : U => 1) w) d := by
  rw [majorTranslationJointPolynomial_eq_sub_aeval]
  apply (weightedSupportLT _ _).sub_mem hD
  apply weightedSupportLT_aeval _ _ _ _ hD
  intro i
  cases i with
  | inl i => exact Submodule.zero_mem _
  | inr j =>
      exact (weightedSupportLE _ _).sub_mem
        (weightedSupportLE_X (Sum.elim (fun _ : U => 1) w) (Sum.inr j))
        (majorParameterRename_degree (fun _ => 1) w
          ((mem_weightedSupportLE_one_iff (A j) (w j)).mpr (hA j)))

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

theorem exp_neg_affineRecoveryLogLoss_card_le (P : ℝ) (n a b : ℕ)
    (h : Real.exp (-(quarticBogolyubovProgressionConstant *
        (roundedModelLogBudget P n + 1) ^ 8)) *
      ((2 ^ 4 : ℝ)⁻¹ * (Real.exp (P + 13 * n))⁻¹ * a) ≤
        16 ^ (n + 2) * (b : ℝ)) :
    Real.exp (-affineRecoveryLogLoss P n) * a ≤ (b : ℝ) := by
  let C := quarticBogolyubovProgressionConstant * (roundedModelLogBudget P n + 1) ^ 8
  let E := P + 13 * n
  let L := 16 * ((n : ℝ) + 3)
  have hmain : Real.exp (-(C + E)) * a ≤ (16 : ℝ) ^ (n + 3) * b := by
    calc
      _ = 16 * (Real.exp (-C) * ((2 ^ 4 : ℝ)⁻¹ * (Real.exp E)⁻¹ * a)) := by
        simp only [neg_add, Real.exp_add, Real.exp_neg]
        norm_num
        ring
      _ ≤ 16 * (16 ^ (n + 2) * (b : ℝ)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by rw [show n + 3 = n + 2 + 1 by omega, pow_succ]; ring
  have h16 : (16 : ℝ) ^ (n + 3) ≤ Real.exp L := by
    calc
      _ ≤ (Real.exp 16) ^ (n + 3) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (16 : ℝ)]) _
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [L]
        push_cast
        ring
  calc
    _ = Real.exp (-L) * (Real.exp (-(C + E)) * a) := by
      change Real.exp (-(C + E + L)) * a = _
      rw [show -(C + E + L) = -L + -(C + E) by ring, Real.exp_add, mul_assoc]
    _ ≤ Real.exp (-L) * ((16 : ℝ) ^ (n + 3) * b) :=
      mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
    _ ≤ Real.exp (-L) * (Real.exp L * b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h16 (Nat.cast_nonneg _))
        (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

theorem properAffineSelection_bounds {P : ℝ} (hP : 0 ≤ P) (n r V A B C : ℕ)
    (hB : 0 < B) (hr : (r : ℝ) ≤ properAffineRankBound P n)
    (hV : (V : ℝ) ≤
      2 * ((2 ^ 14 : ℝ) * (Real.exp (P + 13 * n)) ^ 6 * 16 ^ (n + 1)) ^ 16 * A)
    (hdense : Real.exp (-affineRecoveryLogLoss P n) * A ≤ (B : ℝ))
    (hcell : B ≤ (4 * (2 ^ r * V / B + 1)) ^ r * C) :
    ((2 ^ r * V / B + 1 : ℕ) : ℝ) ≤ Real.exp (properAffineScaleLog P n) ∧
      Real.exp (-properAffineRecoveryLogLoss P n) * A ≤ (C : ℝ) := by
  have hR : 0 ≤ properAffineRankBound P n := by
    have hc := quarticBogolyubovConstant_pos.le
    unfold properAffineRankBound
    positivity
  have hD : 0 ≤ properAffineVolumeLog P n := by unfold properAffineVolumeLog; positivity
  have hS : 0 ≤ affineRecoveryLogLoss P n := by
    have hc := quarticBogolyubovProgressionConstant_pos.le
    unfold affineRecoveryLogLoss
    positivity
  have hT : 0 ≤ properAffineScaleLog P n := by unfold properAffineScaleLog; positivity
  have hV' : (V : ℝ) ≤ Real.exp (properAffineVolumeLog P n) * A :=
    hV.trans (mul_le_mul_of_nonneg_right (properAffineVolume_bound P n) (Nat.cast_nonneg _))
  have hk := affineBoxScale_le_exp hB hR hD hS hr hV' hdense
  have hcount := affineBoxCellCount_le_exp hT hr hk
  refine ⟨hk, ?_⟩
  have hcellR : (B : ℝ) ≤ ((4 * (2 ^ r * V / B + 1)) ^ r : ℕ) * (C : ℝ) := by
    exact_mod_cast hcell
  have hBC : (B : ℝ) ≤ Real.exp ((4 + properAffineScaleLog P n) * properAffineRankBound P n) * C :=
    hcellR.trans (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _))
  let T := (4 + properAffineScaleLog P n) * properAffineRankBound P n
  calc
    _ = Real.exp (-T) * (Real.exp (-affineRecoveryLogLoss P n) * A) := by
      unfold properAffineRecoveryLogLoss
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      dsimp [T]
      ring
    _ ≤ Real.exp (-T) * (Real.exp T * C) :=
      mul_le_mul_of_nonneg_left (hdense.trans hBC) (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedFiniteForwardParameterPolynomial_succ (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) :
    preparedFiniteForwardParameterPolynomial A stageCountConstant (n + 1) =
      preparedFiniteForwardParameterPolynomial A stageCountConstant n +
        preparedFiniteForwardCapPolynomial A stageCountConstant n +
        preparedFiniteForwardBranchPolynomial A stageCountConstant n + 1 := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem linearCoordinatePolynomial_realCoefficientGrid [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) :
    realPolynomialCoefficientGrid
      (matrixDenominator (fun i j => A (Pi.single j 1) i))
      (map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i)) := by
  classical
  let M : Matrix σ τ ℚ := fun i j => A (Pi.single j 1) i
  have hc (j : τ) : ((clearedMatrix M i j : ℤ) : ℝ) =
      (matrixDenominator M : ℝ) * (M i j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast M) i) j
    change ((clearedMatrix M i j : ℤ) : ℚ) = (matrixDenominator M : ℚ) * M i j at h
    exact_mod_cast h
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  refine ⟨∑ j, C (clearedMatrix M i j) * X j, ?_⟩
  simp only [linearCoordinatePolynomial, ← C_mul', map_sum, map_mul, map_C, map_X,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hcast (q : ℚ) : algebraMap ℚ ℝ q = (q : ℝ) := by norm_num
  simp only [hcast, Int.coe_castRingHom]
  rw [hc, map_mul, mul_assoc]
  simp only [M]
  congr 3
  apply congrArg (fun x : τ → ℚ => (A x i : ℝ))
  ext k
  simp [Pi.single_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential
namespace OAI

section

namespace MvPolynomial
open scoped _root_.MvPolynomial

theorem IsWeightedHomogeneous.totalDegree_le_of_positive_weights
    {σ R : Type*} [CommRing R] {w : σ → ℕ} {d : ℕ}
    {P : MvPolynomial σ R} (hP : P.IsWeightedHomogeneous w d)
    (hw : ∀ i, 0 < w i) : P.totalDegree ≤ d := by
  apply Erdos3.totalDegree_le_of_positive_weightedSupport w hw
  intro α hα
  exact (hP (MvPolynomial.mem_support_iff.mp hα)).le

end MvPolynomial

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

theorem normalizedRealPolynomialChart_tag_support
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    normalizedRealPolynomialChart H A i ∈
      weightedSupportLE normalizedChartTagWeight (normalizedChartTagWeight i) := by
  cases i with
  | inl i =>
    change C ((H i)⁻¹) * X (Sum.inl i) ∈ weightedSupportLE
      (normalizedChartTagWeight (U := U) (B := B)) 0
    exact weightedSupportLE_mul
      (w := normalizedChartTagWeight (U := U) (B := B)) (d := 0) (e := 0)
      (weightedSupportLE_C _ 0 ((H i)⁻¹)) (weightedSupportLE_X _ (Sum.inl i))
  | inr i =>
    change X (Sum.inr i) - rename Sum.inl (A i) ∈ weightedSupportLE
      (normalizedChartTagWeight (U := U) (B := B)) 1
    exact (weightedSupportLE (normalizedChartTagWeight (U := U) (B := B)) 1).sub_mem
      (weightedSupportLE_X _ (Sum.inr i))
      (weightedSupportLE_mono (Nat.zero_le 1) (normalizedChart_spatial_support (A i)))

theorem normalizedRealPolynomialChart_tag_coordinate_difference
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    normalizedRealPolynomialChart H A i -
      normalizedRealPolynomialChart H (fun _ => 0) i ∈
        weightedSupportLT normalizedChartTagWeight (normalizedChartTagWeight i) := by
  cases i with
  | inl i =>
    simp only [normalizedRealPolynomialChart_inl, sub_self]
    exact Submodule.zero_mem _
  | inr i =>
    change (X (Sum.inr i) - rename Sum.inl (A i)) -
      (X (Sum.inr i) - rename Sum.inl (0 : MvPolynomial U ℝ)) ∈
        weightedSupportLT (normalizedChartTagWeight (U := U) (B := B)) 1
    rw [map_zero, sub_zero, sub_sub_cancel_left]
    exact (weightedSupportLT (normalizedChartTagWeight (U := U) (B := B)) 1).neg_mem
      (weightedSupportLE_lt_succ (normalizedChart_spatial_support (A i)))

theorem normalizedChart_hom_tag_support
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A)) (X i) ∈
      weightedSupportLE normalizedChartTagWeight (normalizedChartTagWeight i) := by
  rw [aeval_X]
  exact normalizedRealPolynomialChart_tag_support H A i

theorem normalizedChart_hom_tag_difference
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A)) (X i) -
      (aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0))) (X i) ∈
        weightedSupportLT normalizedChartTagWeight (normalizedChartTagWeight i) := by
  rw [aeval_X, aeval_X]
  exact normalizedRealPolynomialChart_tag_coordinate_difference H A i

theorem normalizedRealPolynomialChart_tag_difference
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (α : (U ⊕ B) →₀ ℕ) :
    aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α 1) -
      aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0)) (monomial α 1) ∈
        weightedSupportLT normalizedChartTagWeight (Finsupp.weight normalizedChartTagWeight α) :=
  weightedComparison_monomial_one
    (normalizedChartTagWeight (U := U) (B := B)) normalizedChartTagWeight
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A))
    (aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0)))
    (normalizedChart_hom_tag_support H A)
    (normalizedChart_hom_tag_support H (fun _ => 0))
    (normalizedChart_hom_tag_difference H A) α

theorem normalizedChart_coeff_of_tag_le (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (α β : (U ⊕ B) →₀ ℕ)
    (h : Finsupp.weight normalizedChartTagWeight α ≤ Finsupp.weight normalizedChartTagWeight β) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α 1)).coeff β =
      if α = β then normalizedChartDiagonal H α else 0 := by
  classical
  have hd := normalizedRealPolynomialChart_tag_difference H A α
  have hz : (aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α 1) -
      aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0)) (monomial α 1)).coeff β = 0 := by
    by_contra hn
    exact (not_lt_of_ge h) (hd (mem_support_iff.mpr hn))
  rw [coeff_sub, normalizedChart_zero_monomial, coeff_monomial] at hz
  exact sub_eq_zero.mp hz

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {U V : Type*}

theorem normalizedChartCoefficientMatrix_triangular
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (α β : S)
    (h : Finsupp.weight normalizedChartTagWeight β.val ≤
      Finsupp.weight normalizedChartTagWeight α.val) (hne : β ≠ α) :
    normalizedChartCoefficientMatrix H A S α β = 0 := by
  classical
  have hval : β.val ≠ α.val := fun he => hne (Subtype.ext he)
  simp only [normalizedChartCoefficientMatrix, normalizedChart_coeff_of_tag_le H A β.val α.val h,
    hval, ite_false]

theorem normalizedChartCoefficientMatrix_diagonal
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (α : S) :
    normalizedChartCoefficientMatrix H A S α α ≠ 0 ∧
      |normalizedChartCoefficientMatrix H A S α α| ≤ 1 := by
  classical
  rw [normalizedChartCoefficientMatrix,
    normalizedChart_coeff_of_tag_le H A α.val α.val le_rfl]
  simp only [ite_true]
  obtain ⟨hpos, hle⟩ := normalizedChartDiagonal_pos_le_one H hH α.val
  exact ⟨hpos.ne', (abs_of_pos hpos).trans_le hle⟩

theorem exists_finite_normalized_chart_corrections
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ S.card ∧
      ∃ candidate : Fin m → (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ),
        (∀ j, candidate j ∈ normalizedChartCorrectionSolutions H A S P B q) ∧
        ∀ sr, sr ∈ normalizedChartCorrectionSolutions H A S P B q →
          ∃ j, candidate j = sr := by
  classical
  let rank := fun α : S => Finsupp.weight normalizedChartTagWeight α.val
  obtain ⟨n, hn, vectors, _, hcover⟩ :=
    exists_finite_rank_triangular_correction_enumeration q hq B hB rank
      (normalizedChartCoefficientMatrix H A S) (fun α : S => P.coeff α.val)
      (normalizedChartCoefficientMatrix_triangular H A S)
      (fun α => (normalizedChartCoefficientMatrix_diagonal H hH A S α).1)
      (fun α => (normalizedChartCoefficientMatrix_diagonal H hH A S α).2)
  let polynomials := fun j : Fin n =>
    (polynomialOfFiniteCoefficientVector S (vectors j).1,
      polynomialOfFiniteCoefficientVector S (vectors j).2)
  have hpolynomials (sr) (hsr : sr ∈ normalizedChartCorrectionSolutions H A S P B q) :
      ∃ j, polynomials j = sr := by
    obtain ⟨j, hj⟩ := hcover _
      (normalizedChartCorrectionSolutions_coefficients H A S P B q sr hsr)
    refine ⟨j, ?_⟩
    dsimp only [polynomials]
    rw [hj]
    exact Prod.ext (polynomialOfFiniteCoefficientVector_reconstruct S sr.1 hsr.1)
      (polynomialOfFiniteCoefficientVector_reconstruct S sr.2 hsr.2.1)
  obtain ⟨m, hm, candidate, hvalid, _, hcomplete⟩ :=
    exists_filtered_finite_enumeration polynomials
      (fun sr => sr ∈ normalizedChartCorrectionSolutions H A S P B q)
  refine ⟨m, ?_, candidate, hvalid, ?_⟩
  · exact hm.trans (by simpa only [Fintype.card_coe] using hn)
  · intro sr hsr
    exact hcomplete sr hsr (hpolynomials sr hsr)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TranslationShearCoordinateSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

omit [Algebra ℚ R] in
theorem PolynomialTranslationGroupOver.action_inverse_X_inr
    (g : PolynomialTranslationGroupOver R σ) :
    (actionMonoidHom g).symm (X (Sum.inr ())) =
      X (Sum.inr ()) - rename Sum.inl g.polynomial := by
  have he : (actionMonoidHom g).symm = actionMonoidHom g⁻¹ :=
    (map_inv actionMonoidHom g).symm
  rw [he]
  change actionHom g⁻¹ (X (Sum.inr ())) = _
  rw [actionHom_X_inr]
  simp only [base_inv, polynomial_inv, map_neg, polynomialTranslate_comp_ring,
    neg_add_cancel, polynomialTranslate_zero_ring, sub_eq_add_neg]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialSubspaceSeparation
namespace OAI

section

namespace Erdos3

theorem exists_polynomial_subspace_separation (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {ι κ σ : Type*} [Fintype ι] [Fintype κ]
      (A : Matrix ι κ ℚ) (H l : ℕ), 1 ≤ H → 0 < l →
      (∀ i j, RationalHeightLE (A i j) H) →
      ∀ p : ℝ, 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      (Fintype.card κ : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      (H : ℝ) ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p) →
      (l : ℝ) ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ α : σ →₀ ℕ, α ≠ 0 → ∀ a b : ι → ℝ,
      ‖a‖ ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p) / monomialScale T α →
      b ∈ realDenominatorGrid l →
      a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) →
      a ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ∧
        b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
  let R := (P + 2) ^ 48 + (P + 2) ^ 24 + P + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro ι κ σ _ _ A H l hH hl hA p hp hι hκ hHp hlp T hT α hα a b ha hb hsum
  have hbudget : separationBudget (P.eval₂ (Nat.castRingHom ℝ) p) ≤ (p + C) ^ C := by
    simpa [R, separationBudget, Polynomial.eval₂_pow] using hbound p hp
  exact controlled_real_column_span_separation A hH hl hA (natPolynomial_eval_nonneg P hp)
    hι hκ hHp hlp T (fun i => (Real.exp_le_exp.mpr hbudget).trans (hT i)) hα a b ha hb hsum

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

theorem exists_vectorPolynomial_subspace_separation (budget : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {J I σ : Type*} [Fintype J] [Fintype I]
      (B : Matrix J I ℚ) (H q : ℕ), 1 ≤ H → 0 < q →
      (∀ j i, RationalHeightLE (B j i) H) →
      ∀ p : ℝ, 0 ≤ p →
      (Fintype.card J : ℝ) ≤ budget.eval₂ (Nat.castRingHom ℝ) p →
      (Fintype.card I : ℝ) ≤ budget.eval₂ (Nat.castRingHom ℝ) p →
      (H : ℝ) ≤ Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) →
      (q : ℝ) ≤ Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ A E P Q : VectorPolynomial σ ℝ (J → ℝ),
      A = E + P + Q →
      (∀ α, coefficients A α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) →
      (∀ α, coefficients P α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) →
      coefficients E 0 = 0 → coefficients Q 0 = 0 →
      (∀ α j, |coefficients E α j| ≤
        Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) / monomialScale T α) →
      (∀ α, coefficients Q α ∈ realDenominatorGrid q) →
      (∀ α, coefficients E α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) ∧
      (∀ α, coefficients Q α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) ∧
      (∀ x, eval x E ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) ∧
      (∀ x, eval x Q ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) := by
  obtain ⟨C, hC, hsep⟩ := exists_polynomial_subspace_separation budget
  refine ⟨C, hC, ?_⟩
  intro J I σ _ _ B H q hH hq hB p hp hJ hI hHp hqp T hT A E P Q
    hdecomp hA hP hE0 hQ0 hE hQ
  let K := Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hcoeff (α : σ →₀ ℕ) : coefficients E α ∈ K ∧ coefficients Q α ∈ K := by
    by_cases hα : α = 0
    · subst α
      rw [hE0, hQ0]
      exact ⟨K.zero_mem, K.zero_mem⟩
    · have hsum : coefficients E α + coefficients Q α ∈ K := by
        have hm := K.sub_mem (hA α) (hP α)
        have heq : coefficients A α - coefficients P α =
            coefficients E α + coefficients Q α := by
          rw [hdecomp]
          simp only [map_add, Finsupp.add_apply]
          abel
        rwa [heq] at hm
      have hnorm : ‖coefficients E α‖ ≤
          Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) / monomialScale T α := by
        apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.exp_nonneg _)
          (monomialScale_pos T hTpos α).le)).mpr
        intro j
        simpa only [Real.norm_eq_abs] using hE α j
      exact hsep B H q hH hq hB p hp hJ hI hHp hqp T hT α hα
        (coefficients E α) (coefficients Q α) hnorm (hQ α) hsum
  have hEK : ∀ α, coefficients E α ∈ K := fun α => (hcoeff α).1
  have hQK : ∀ α, coefficients Q α ∈ K := fun α => (hcoeff α).2
  refine ⟨hEK, hQK, ?_, ?_⟩
  · intro x
    rw [← eval_restrictCoefficients K E hEK x]
    exact (eval (V := K) x (restrictCoefficients K E hEK)).property
  · intro x
    rw [← eval_restrictCoefficients K Q hQK x]
    exact (eval (V := K) x (restrictCoefficients K Q hQK)).property

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.TranslationLogCoordinateInputGrid
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ U B : Type*}

theorem realPolynomialCoefficientGrid_zero (q : ℕ) :
    realPolynomialCoefficientGrid q (0 : MvPolynomial σ ℝ) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  simp

theorem realPolynomialCoefficientGrid_sum {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) {q : ℕ}
    (hP : ∀ i ∈ s, realPolynomialCoefficientGrid q (P i)) :
    realPolynomialCoefficientGrid q (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using realPolynomialCoefficientGrid_zero q
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact realPolynomialCoefficientGrid_add (hP i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem realPolynomialCoefficientGrid_mul {q r : ℕ} {P Q : MvPolynomial σ ℝ}
    (hP : realPolynomialCoefficientGrid q P) (hQ : realPolynomialCoefficientGrid r Q) :
    realPolynomialCoefficientGrid (q * r) (P * Q) := by
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  have h := (integralRealPolynomialSubring σ).mul_mem
    ((realPolynomialCoefficientGrid_iff _ _).mp hP)
    ((realPolynomialCoefficientGrid_iff _ _).mp hQ)
  simpa only [Nat.cast_mul, map_mul, mul_mul_mul_comm] using h

theorem realPolynomialCoefficientGrid_pderiv (i : σ) {q : ℕ}
    {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid q (pderiv i P) := by
  obtain ⟨I, hI⟩ := (realPolynomialCoefficientGrid_iff _ _).mp hP
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  refine ⟨pderiv i I, ?_⟩
  rw [← pderiv_map, hI, pderiv_C_mul]

theorem realPolynomialCoefficientGrid_rat_smul (z : ℤ) {t r : ℕ} (ht : 0 < t)
    {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid r P) :
    realPolynomialCoefficientGrid (t * r) (((z : ℝ) / (t : ℝ)) • P) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  have h := (integralRealPolynomialSubring σ).mul_mem
    (C_int_mem_integralRealPolynomialSubring z)
    ((realPolynomialCoefficientGrid_iff _ _).mp hP)
  have heq : C ((t * r : ℕ) : ℝ) * (((z : ℝ) / (t : ℝ)) • P) =
      C (z : ℝ) * (C (r : ℝ) * P) := by
    rw [← C_mul', ← mul_assoc, ← map_mul]
    have hs : ((t * r : ℕ) : ℝ) * ((z : ℝ) / (t : ℝ)) = (z : ℝ) * (r : ℝ) := by
      push_cast
      field_simp
    rw [hs, map_mul, mul_assoc]
  rw [heq]
  exact h

variable [Fintype B]

theorem translationDirectionalDerivative_coefficientGrid
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    {q r : ℕ} (hb : ∀ i, realPolynomialCoefficientGrid q (b i))
    (hP : realPolynomialCoefficientGrid r P) :
    realPolynomialCoefficientGrid (q * r) (translationDirectionalDerivative b P) := by
  rw [translationDirectionalDerivative_apply]
  exact realPolynomialCoefficientGrid_sum Finset.univ _ fun i _ =>
    realPolynomialCoefficientGrid_mul (realPolynomialCoefficientGrid_rename Sum.inl (hb i))
      (realPolynomialCoefficientGrid_pderiv (Sum.inr i) hP)

theorem translationDirectionalDerivative_pow_coefficientGrid
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    {q : ℕ} (hb : ∀ i, realPolynomialCoefficientGrid q (b i))
    (hP : realPolynomialCoefficientGrid q P) (i : ℕ) :
    realPolynomialCoefficientGrid (q ^ (i + 1)) (((translationDirectionalDerivative b) ^ i) P) := by
  induction i with
  | zero => simpa using hP
  | succ i ih =>
      simpa only [pow_succ', Module.End.mul_apply] using
        translationDirectionalDerivative_coefficientGrid b _ hb ih

theorem translationDirectionalSeries_coefficientGrid (d : ℕ)
    (b : B → MvPolynomial U ℝ) (P : MvPolynomial (U ⊕ B) ℝ)
    {q : ℕ} (hb : ∀ i, realPolynomialCoefficientGrid q (b i))
    (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid (d.factorial * q ^ (d + 1))
      (translationDirectionalSeries d b P) := by
  unfold translationDirectionalSeries
  apply realPolynomialCoefficientGrid_sum
  intro i hi
  have hid : i + 1 ≤ d := Finset.mem_range.mp hi
  have hterm := realPolynomialCoefficientGrid_rat_smul ((-1 : ℤ) ^ i)
    (Nat.factorial_pos (i + 1))
    (translationDirectionalDerivative_pow_coefficientGrid b P hb hP i)
  have hdiv : (i + 1).factorial * q ^ (i + 1) ∣ d.factorial * q ^ (d + 1) :=
    Nat.mul_dvd_mul (Nat.factorial_dvd_factorial hid) (pow_dvd_pow q (by omega))
  apply realPolynomialCoefficientGrid_mono hdiv
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hterm

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped BigOperators

variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem constant_coefficientGrid {l : ℕ} {a : ℝ}
    (ha : ∃ z : ℤ, (z : ℝ) = (l : ℝ) * a) :
    realPolynomialCoefficientGrid l (C a : MvPolynomial U ℝ) := by
  obtain ⟨z, hz⟩ := ha
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  rw [← map_mul, ← hz]
  exact C_int_mem_integralRealPolynomialSubring z

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialAffineSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {I K R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_substitute_nonzero_mem (W : Submodule R V)
    (f : I → MvPolynomial K R) (P : VectorPolynomial I R V)
    (hP : ∀ β, β ≠ 0 → coefficients P β ∈ W)
    (α : K →₀ ℕ) (hα : α ≠ 0) :
    coefficients (substitute f P) α ∈ W := by
  classical
  rw [coefficients_substitute]
  apply Submodule.sum_mem
  intro β hβ
  by_cases hβ0 : β = 0
  · subst β
    simp [MvPolynomial.coeff_one, Ne.symm hα]
  · exact W.smul_mem _ (hP β hβ0)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTagRestrictionBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

theorem polynomialTagLinearEmbedding_coefficientGrid (E : B → I → ℝ)
    (d : ℕ) (hE : ∀ b i, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * E b i)
    (j : U ⊕ B) :
    realPolynomialCoefficientGrid d (polynomialTagLinearEmbedding E j) := by
  classical
  cases j with
  | inl u => exact realPolynomialCoefficientGrid_X d _
  | inr b =>
      apply (realPolynomialCoefficientGrid_iff d _).mpr
      change C (d : ℝ) * (∑ i, C (E b i) * X (Sum.inr i)) ∈
        integralRealPolynomialSubring (U ⊕ I)
      rw [Finset.mul_sum]
      apply (integralRealPolynomialSubring (U ⊕ I)).sum_mem
      intro i _
      obtain ⟨z, hz⟩ := hE b i
      rw [← mul_assoc, ← map_mul, ← hz]
      exact (integralRealPolynomialSubring (U ⊕ I)).mul_mem
        (C_int_mem_integralRealPolynomialSubring z) (X_mem_integralRealPolynomialSubring _)

theorem polynomialTagRestriction_coefficientGrid (E : B → I → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) (q d s : ℕ)
    (hE : ∀ b i, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * E b i)
    (hp : p.totalDegree ≤ s) (hq : realPolynomialCoefficientGrid q p) :
    realPolynomialCoefficientGrid (q * d ^ s)
      (aeval (polynomialTagLinearEmbedding E) p) :=
  realPolynomialCoefficientGrid_substitute p (polynomialTagLinearEmbedding E)
    q d s hp hq (polynomialTagLinearEmbedding_coefficientGrid E d hE)

theorem polynomialSubspaceRestriction_coefficientGrid
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) (q d s : ℕ)
    (he : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (hp : p.totalDegree ≤ s) (hq : realPolynomialCoefficientGrid q p) :
    realPolynomialCoefficientGrid (q * d ^ s) (polynomialSubspaceRestriction K e p) :=
  polynomialTagRestriction_coefficientGrid _ p q d s (fun b i => he i b) hp hq

theorem polynomialSubspaceRestriction_coeff_div
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) (q d s : ℕ) (hq : 0 < q) (hd : 0 < d)
    (he : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (hp : p.totalDegree ≤ s) (hgrid : realPolynomialCoefficientGrid q p)
    (α : (U ⊕ I) →₀ ℕ) :
    ∃ z : ℤ, (polynomialSubspaceRestriction K e p).coeff α =
      (z : ℝ) / (q * d ^ s : ℕ) := by
  obtain ⟨z, hz⟩ := polynomialSubspaceRestriction_coefficientGrid K e p q d s he hp hgrid
  refine ⟨z α, (eq_div_iff ?_).mpr ?_⟩
  · exact_mod_cast (Nat.mul_pos hq (pow_pos hd s)).ne'
  · simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (congrFun hz α).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteNormalizedRealGridCorrection
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U V : Type*}

theorem exists_finite_normalized_real_grid_corrections
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ S.card ∧
      ∃ candidate : Fin m → (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℝ),
        (∀ j, candidate j ∈ normalizedRealGridCorrectionSolutions H A S P B q) ∧
        ∀ sr, sr ∈ normalizedRealGridCorrectionSolutions H A S P B q →
          ∃ j, candidate j = sr := by
  obtain ⟨m, hm, candidate, hvalid, hcomplete⟩ :=
    exists_finite_normalized_chart_corrections H hH A S P B hB q hq
  refine ⟨m, hm, (fun j => ((candidate j).1,
    MvPolynomial.map (Rat.castHom ℝ) (candidate j).2)), ?_, ?_⟩
  · intro j
    exact normalizedChartCorrectionSolutions_map H A S P B q (candidate j) (hvalid j)
  · intro sr hsr
    obtain ⟨r, hrsupport, hrgrid, hrmap⟩ :=
      exists_finiteSupport_rationalGridLift S sr.2 q hsr.2.1 hsr.2.2.2.1
    have hr : (sr.1, r) ∈ normalizedChartCorrectionSolutions H A S P B q := by
      refine ⟨hsr.1, hrsupport, hsr.2.2.1, hrgrid, ?_⟩
      rw [hrmap]
      exact hsr.2.2.2.2
    obtain ⟨j, hj⟩ := hcomplete (sr.1, r) hr
    refine ⟨j, ?_⟩
    change ((candidate j).1, MvPolynomial.map (Rat.castHom ℝ) (candidate j).2) = sr
    rw [hj]
    exact Prod.ext rfl hrmap

end Erdos3

end

end OAI
end


