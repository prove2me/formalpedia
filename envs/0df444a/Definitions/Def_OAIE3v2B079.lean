-- Prove2me | Definitions.Def_OAIE3v2B079
-- name    : OAIE3v2B079
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:19:00.381245+00:00
-- url     : https://prove2.me/theorems/f7f4597a-850d-4dd1-8a29-89e83d1fd8c8
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 80 of 311
-- statement:
--   Definitions bundle 80 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B042`, `OAIE3v2B045`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B050`, `OAIE3v2B054`, `OAIE3v2B057`, `OAIE3v2B058`, `OAIE3v2B059` of this split.
--
--   Modules: `Dynamics/MajorTranslationPartnerBudget.lean`, `Dynamics/PointwiseSymbolBudget.lean`, `Dynamics/TranslationMajorCorrelationBudget.lean`, `Dynamics/TranslationMajorDetectedPotential.lean`, `Estimates/CurrentLayerSplitting.lean`, `Estimates/NativeFixedVerticalPower.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Estimates/RealifiedReconstruction.lean`, `Estimates/ScalarCubeDomain.lean`, `Estimates/UnitExpansionCorrelation.lean`, `Estimates/VectorRealSubstitutionBound.lean`, `Estimates/WeightedAxisScaling.lean`, `Geometry/DetectedTranslationCoordinateBudget.lean`, `Geometry/DetectedTranslationUniformCoordinateBounds.lean`, `Lattices/AlgebraicMajorIntegerRestoration.lean`, `Lattices/AlgebraicMajorWeightedAffineTopPullback.lean`, `Lattices/RealSpanIntegerDefiningRows.lean`, `Lattices/ResidueSliceNormalizedCell.lean`, `Lattices/SpatialAffineFullMass.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Nilpotent/AllocatedKeptCommonCurrentGradeLocalNiltest.lean`, `Polynomial/ControlledLinearPolynomialRestriction.lean`, `Polynomial/DetectedTranslationPhaseBudget.lean`, `Polynomial/JointPolynomialDilationGrid.lean`, `Polynomial/LowTaggedPolynomialCoordinates.lean`, `Polynomial/MajorPhaseCoordinateDenominator.lean`, `Polynomial/MonomialArrayJet.lean`, `Polynomial/NormalizedFrozenPolynomialMass.lean`, `Polynomial/PolynomialCoefficientGridDenominator.lean`, `Polynomial/PolynomialShearRealGroup.lean`, `Polynomial/PolynomialTranslationSeries.lean`, `Polynomial/RationalPolynomialFromRealGrid.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Polynomial/WeightedLinearPolynomialRestriction.lean`, `Probability/AllocatedMixedLiftNormalizedMass.lean`, `Sampling/DetectedTranslationMajorSamplingContainment.lean`, `Sampling/FiniteNormalizedRealGridCorrection.lean`, `Sampling/NormalizedRealBoxHalfGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B040
import Definitions.Def_OAIE3v2B042
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B050
import Definitions.Def_OAIE3v2B054
import Definitions.Def_OAIE3v2B057
import Definitions.Def_OAIE3v2B058
import Definitions.Def_OAIE3v2B059

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid
namespace OAI

section

namespace Erdos3

noncomputable def normalizedRealBoxGrid {σ : Type*} (T : σ → ℝ) (M : ℕ)
    (j : σ → Fin (M + 1)) : σ → ℝ :=
  fun i => T i * uniformBoxGrid 1 M j i

theorem normalizedRealBoxGrid_bound {σ : Type*} (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℕ} (hM : 0 < M)
    (j : σ → Fin (M + 1)) (i : σ) :
    |normalizedRealBoxGrid T M j i| ≤ T i := by
  rw [normalizedRealBoxGrid, abs_mul, abs_of_pos (hT i)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (uniformBoxGrid_mem (by norm_num : (0 : ℝ) ≤ 1) hM j i) (hT i).le

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

theorem exists_partition_cell_average {Ω K : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype K] (cell : Ω → K) (f : Ω → ℝ) :
    ∃ k, (partitionCell cell k).Nonempty ∧
      (𝔼 x, f x) ≤ 𝔼 x ∈ partitionCell cell k, f x := by
  classical
  by_contra! hnone
  have hstrict (k : K) (hk : (partitionCell cell k).Nonempty) :
      (∑ x ∈ partitionCell cell k, f x) < (partitionCell cell k).card * (𝔼 x, f x) := by
    have hcard : (0 : ℝ) < (partitionCell cell k).card := by exact_mod_cast hk.card_pos
    have h := mul_lt_mul_of_pos_left (hnone k hk) hcard
    rwa [Finset.card_mul_expect] at h
  have hle (k : K) : (∑ x ∈ partitionCell cell k, f x) ≤
      (partitionCell cell k).card * (𝔼 x, f x) := by
    by_cases hk : (partitionCell cell k).Nonempty
    · exact (hstrict k hk).le
    · simp [Finset.not_nonempty_iff_eq_empty.mp hk]
  obtain ⟨x₀⟩ := ‹Nonempty Ω›
  have hk : (partitionCell cell (cell x₀)).Nonempty :=
    ⟨x₀, (mem_partitionCell cell (cell x₀) x₀).mpr rfl⟩
  have hsum := Finset.sum_lt_sum (fun k (_ : k ∈ (Finset.univ : Finset K)) => hle k)
    ⟨cell x₀, Finset.mem_univ _, hstrict _ hk⟩
  rw [sum_partitionCell, ← Finset.sum_mul, card_partitionCell_sum,
    Fintype.expect_eq_sum_div_card] at hsum
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_div_cancel₀ _ hcard] at hsum
  exact lt_irrefl _ hsum

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlating_components_on_finset {X I J : Type*} [Fintype I] [Fintype J]
    (s : Finset X) (hs : s.Nonempty) (U Q R : X → ℂ) (V : I → X → ℂ) (W : J → X → ℂ)
    {delta C D rho eta : ℝ} (hdelta : 0 < delta) (hC : 0 < C) (hD : 0 < D)
    (hrho : 0 ≤ rho) (_heta : 0 ≤ eta)
    (hI : (Fintype.card I : ℝ) ≤ C) (hJ : (Fintype.card J : ℝ) ≤ D)
    (hU : ∀ x ∈ s, ‖U x‖ ≤ 1) (hR : ∀ x ∈ s, ‖R x‖ ≤ 1)
    (hV : ∀ i x, x ∈ s → ‖V i x‖ ≤ 1)
    (hQa : ∀ x ∈ s, ‖Q x - ∑ i, V i x‖ ≤ rho)
    (hRa : ∀ x ∈ s, ‖R x - ∑ j, W j x‖ ≤ eta)
    (hsmall : rho + C * eta ≤ delta / 2)
    (hcorr : delta ≤ ‖𝔼 x ∈ s, U x * Q x * R x‖) :
    ∃ i j, (delta / 2) / (C * D) ≤ ‖𝔼 x ∈ s, U x * V i x * W j x‖ := by
  have hpoint (x : X) (hx : x ∈ s) :
      ‖U x * Q x * R x - ∑ i, ∑ j, U x * V i x * W j x‖ ≤ rho + C * eta := by
    have hsum : ‖∑ i, V i x‖ ≤ C := by
      apply (norm_sum_le _ _).trans
      exact (Finset.sum_le_sum (fun i _ => hV i x hx)).trans (by simpa using hI)
    have hid : U x * Q x * R x - ∑ i, ∑ j, U x * V i x * W j x =
        U x * (Q x - ∑ i, V i x) * R x +
          U x * (∑ i, V i x) * (R x - ∑ j, W j x) := by
      rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
      ring
    rw [hid]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simp only [norm_mul]
      calc
        _ ≤ 1 * rho * 1 := mul_le_mul
          (mul_le_mul (hU x hx) (hQa x hx) (norm_nonneg _) (by norm_num))
          (hR x hx) (norm_nonneg _) (by positivity)
        _ = rho := by ring
    · simp only [norm_mul]
      calc
        _ ≤ 1 * C * eta := mul_le_mul
          (mul_le_mul (hU x hx) hsum (norm_nonneg _) (by norm_num))
          (hRa x hx) (norm_nonneg _) (by positivity)
        _ = C * eta := by ring
  have hsum : (𝔼 x ∈ s, ∑ i, ∑ j, U x * V i x * W j x) =
      ∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x := by
    simp_rw [Finset.expect_sum_comm]
  have herr : ‖(𝔼 x ∈ s, U x * Q x * R x) -
      (∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x)‖ ≤ delta / 2 := by
    rw [← hsum, ← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans ((Finset.expect_le hs hpoint).trans hsmall)
  apply exists_large_weighted_pair (fun _ : I => (1 : ℂ)) (fun (_ : I) (_ : J) => (1 : ℂ))
    (fun i j => 𝔼 x ∈ s, U x * V i x * W j x) (by positivity) hC hD
  · simpa using hI
  · intro _
    simpa using hJ
  · simp only [one_mul]
    have htri := norm_add_le
      ((𝔼 x ∈ s, U x * Q x * R x) - (∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x))
      (∑ i, ∑ j, 𝔼 x ∈ s, U x * V i x * W j x)
    rw [sub_add_cancel] at htri
    linarith

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

theorem scalarCubeValue_contDiff {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    ContDiff ℝ ∞ (fun a : Option α → ℝ => scalarCubeValue a t) := by
  unfold scalarCubeValue
  apply ContDiff.sum
  intro r _
  exact contDiff_const.mul (ContinuousLinearMap.proj r : (Option α → ℝ) →L[ℝ] ℝ).contDiff

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

theorem monomialArrayPolynomial_coeff {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (he : Function.Injective e) (a : J → ℝ) (j : J) :
    (monomialArrayPolynomial e a).coeff (e j) = a j := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    he.eq_iff]
  simp

theorem monomialArrayPolynomial_coeff_zero_of_not_mem {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (m : K →₀ ℕ) (hm : ∀ j, e j ≠ m) :
    (monomialArrayPolynomial e a).coeff m = 0 := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  exact Finset.sum_eq_zero (fun j _ => if_neg (hm j))

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
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem basisGradeProjection_pi_apply (w : σ → ℕ) (j : ℕ)
    (x : σ → ℚ) (i : σ) :
    basisGradeProjection (Pi.basisFun ℚ σ) w j x i =
      if w i = j then x i else 0 := by
  simpa only [Pi.basisFun_repr] using
    basisGradeProjection_repr (Pi.basisFun ℚ σ) w j x i

theorem sum_basisGradeProjection_pi (w : σ → ℕ) (x : σ → ℚ) :
    ∑ j ∈ Finset.univ.image w, basisGradeProjection (Pi.basisFun ℚ σ) w j x = x := by
  classical
  funext i
  simp only [Finset.sum_apply, basisGradeProjection_pi_apply]
  simp

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

theorem realPolynomialCoefficientGrid_weightedHomogeneousComponent
    {M : Type*} [AddCommMonoid M] (w : σ → M) (d : M)
    (q : ℕ) (P : MvPolynomial σ ℝ) (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid q (weightedHomogeneousComponent w d P) := by
  classical
  obtain ⟨z, hz⟩ := hP
  refine ⟨fun m => if Finsupp.weight w m = d then z m else 0, funext (fun m => ?_)⟩
  change ((if Finsupp.weight w m = d then z m else 0 : ℤ) : ℝ) =
    (q : ℝ) * (weightedHomogeneousComponent w d P).coeff m
  by_cases hm : Finsupp.weight w m = d
  · have hzm : (z m : ℝ) = (q : ℝ) * P.coeff m := congrFun hz m
    simpa [coeff_weightedHomogeneousComponent, hm] using hzm
  · simp [coeff_weightedHomogeneousComponent, hm]

end Erdos3

end

section

namespace Erdos3

theorem den_dvd_of_mem_denominatorGrid {ι : Type*} {q : ℕ} (hq : 0 < q)
    {x : ι → ℚ} (hx : x ∈ denominatorGrid q) (i : ι) :
    (x i).den ∣ q := by
  obtain ⟨z, hz⟩ := (mem_denominatorGrid_iff q hq x).mp hx
  rw [hz i]
  have h := Rat.den_dvd (z i) (q : ℤ)
  rw [Rat.divInt_eq_div, Int.cast_natCast] at h
  exact Int.natCast_dvd_natCast.mp h

theorem den_le_of_mem_denominatorGrid {ι : Type*} {q : ℕ} (hq : 0 < q)
    {x : ι → ℚ} (hx : x ∈ denominatorGrid q) (i : ι) :
    (x i).den ≤ q :=
  Nat.le_of_dvd hq (den_dvd_of_mem_denominatorGrid hq hx i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*}

theorem polynomialExponentialPath_potential [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    polynomialExponentialPath x (scalarDirectionalDerivative x V) =
      Polynomial.C V - polynomialTranslationPath x V := by
  apply polynomialExponentialPath_unique
  · rw [Polynomial.derivative_sub, Polynomial.derivative_C,
      polynomialTranslationPath_derivative, zero_sub, neg_neg]
  · simp

theorem polynomialExponentialPath_eval_potential [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) (t : ℚ) :
    (polynomialExponentialPath x (scalarDirectionalDerivative x V)).eval (C t) =
      V - polynomialTranslate (fun i => -(t * x i)) V := by
  rw [polynomialExponentialPath_potential, Polynomial.eval_sub, Polynomial.eval_C,
    polynomialTranslationPath_eval]

theorem polynomialExponentialCoordinate_potential [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    polynomialExponentialCoordinate x (scalarDirectionalDerivative x V) =
      V - polynomialTranslate (-x) V := by
  have h := polynomialExponentialPath_eval_potential x V 1
  have hx : (fun i => -(1 * x i)) = -x := by funext i; simp
  rw [map_one, hx] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

namespace PolynomialPotentialRelation

variable [DecidableEq σ] (A : PolynomialPotentialRelation σ)
  (P : σ → MvPolynomial σ ℚ)
  (hlift : ∀ i, (Pi.single i 1, P i) ∈ A.space)

include hlift

theorem pure_eq_zero (Q : MvPolynomial σ ℚ) (hQ : (0, Q) ∈ A.space) : Q = 0 := by
  apply polynomial_eq_zero_of_pderiv_closed {Q | (0, Q) ∈ A.space} ?_ ?_ Q hQ
  · intro R hR i
    change (0, pderiv i R) ∈ A.space
    have h := A.bracket_mem (Pi.single i 1) (P i) 0 R (hlift i) hR
    simpa only [scalarDirectionalDerivative_single, scalarDirectionalDerivative_zero,
      sub_zero] using h
  · exact A.pure_constant_zero

theorem compatible_partials (i j : σ) : pderiv i (P j) = pderiv j (P i) := by
  have h := A.bracket_mem (Pi.single i 1) (P i) (Pi.single j 1) (P j) (hlift i) (hlift j)
  simp only [scalarDirectionalDerivative_single] at h
  exact sub_eq_zero.mp (A.pure_eq_zero P hlift _ h)

theorem linear_combination_mem (x : σ → ℚ) : (x, ∑ i, x i • P i) ∈ A.space := by
  have h : (∑ i, x i • (Pi.single i 1, P i)) ∈ A.space :=
    A.space.sum_mem (fun i _ => A.space.smul_mem (x i) (hlift i))
  have heq : (∑ i, x i • (Pi.single i 1, P i)) = (x, ∑ i, x i • P i) := by
    apply Prod.ext
    · ext j
      simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  rwa [heq] at h

theorem polynomial_eq_linear_combination (x : σ → ℚ) (Q : MvPolynomial σ ℚ)
    (hQ : (x, Q) ∈ A.space) : Q = ∑ i, x i • P i := by
  have h := A.space.sub_mem hQ (A.linear_combination_mem P hlift x)
  have hpure : (0, Q - ∑ i, x i • P i) ∈ A.space := by simpa using h
  exact sub_eq_zero.mp (A.pure_eq_zero P hlift _ hpure)

theorem weighted_potential_derivative (w : σ → ℕ) {d : ℕ} (hd : 0 < d)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i))
    (x : σ → ℚ) (Q : MvPolynomial σ ℚ) (hQ : (x, Q) ∈ A.space) :
    scalarDirectionalDerivative x (weightedPolynomialPotential w d P) = Q := by
  rw [scalarDirectionalDerivative_apply]
  simp only [weightedPolynomialPotential_pderiv w hd P hweight hhom
    (A.compatible_partials P hlift)]
  exact (A.polynomial_eq_linear_combination P hlift x Q hQ).symm

end PolynomialPotentialRelation
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*}

theorem fractionalCoefficientPolynomial_bounds (D : MvPolynomial σ ℝ) (a : σ →₀ ℕ) :
    0 ≤ (fractionalCoefficientPolynomial D).coeff a ∧
      (fractionalCoefficientPolynomial D).coeff a < 1 := by
  rw [fractionalCoefficientPolynomial_coeff]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem fractionalCoefficientPolynomial_mass_le_card (D : MvPolynomial σ ℝ) :
    realPolynomialMass (fractionalCoefficientPolynomial D) ≤
      ((fractionalCoefficientPolynomial D).support.card : ℝ) := by
  classical
  calc
    _ ≤ ∑ _a ∈ (fractionalCoefficientPolynomial D).support, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_of_nonneg (fractionalCoefficientPolynomial_bounds D a).1]
      exact (fractionalCoefficientPolynomial_bounds D a).2.le
    _ = _ := by simp

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointPolynomialDilationGrid
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem scaleMvPolynomialAxes_mass_le {σ : Type*} (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (P : MvPolynomial σ ℝ) {M : ℝ}
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤ P.support.card * M := by
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support
    (scaleMvPolynomialAxes_support_subset T P)]
  calc
    _ ≤ ∑ _α ∈ P.support, M := by
      apply Finset.sum_le_sum
      intro α _
      rw [scaleMvPolynomialAxes_coeff, abs_mul, abs_of_pos (monomialScale_pos T hT α)]
      exact (le_div_iff₀ (monomialScale_pos T hT α)).mp (hcoeff α)
    _ = P.support.card * M := by simp

end Erdos3


namespace Erdos3

open scoped BigOperators

theorem scaleMvPolynomialAxes_mass_le_of_abs_le {σ : Type*}
    (T : σ → ℝ) (P : MvPolynomial σ ℝ) {K : ℝ} (hK : 1 ≤ K)
    (hT : ∀ i, |T i| ≤ K) {d : ℕ} (hP : P.totalDegree ≤ d) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤ K ^ d * realPolynomialMass P := by
  classical
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support
    (scaleMvPolynomialAxes_support_subset T P)]
  calc
    _ ≤ ∑ α ∈ P.support, |P.coeff α| * K ^ d := by
      apply Finset.sum_le_sum
      intro α hα
      rw [scaleMvPolynomialAxes_coeff, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (abs_monomialScale_le_pow T hT α).trans
        (pow_le_pow_right₀ hK ((MvPolynomial.le_totalDegree hα).trans hP))
    _ = K ^ d * realPolynomialMass P := by
      rw [← Finset.sum_mul]
      exact mul_comm _ _

theorem jointPolynomialDilation_mass_le {U B : Type*}
    (c : U → ℝ) (S : MvPolynomial (U ⊕ B) ℝ) {K : ℝ} (hK : 1 ≤ K)
    (hc : ∀ i, |c i| ≤ K) {d : ℕ} (hS : S.totalDegree ≤ d) :
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim c (fun _ => 1)) S) ≤
      K ^ d * realPolynomialMass S := by
  apply scaleMvPolynomialAxes_mass_le_of_abs_le _ S hK _ hS
  intro i
  cases i with
  | inl i => exact hc i
  | inr i => simpa only [Sum.elim_inr, abs_one] using hK

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

theorem scaleMvPolynomialAxes_eq_aeval {σ : Type*} (T : σ → ℝ)
    (P : MvPolynomial σ ℝ) :
    scaleMvPolynomialAxes T P =
      MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P := by
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval]
  change aeval (fun i => T i * x i) P = aeval x (aeval _ P)
  rw [comp_aeval_apply]
  simp

theorem rationalAxisScaling_map_real {σ : Type*} (T : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    MvPolynomial.map (algebraMap ℚ ℝ)
        (MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P) =
      scaleMvPolynomialAxes (fun i => (T i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) P) := by
  rw [scaleMvPolynomialAxes_eq_aeval]
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, aeval_X, map_X, map_C, hP]; rfl

theorem rationalAxisScaling_support_subset {σ : Type*} (T : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P).support ⊆
      P.support := by
  intro α hα
  have hreal : α ∈ (MvPolynomial.map (algebraMap ℚ ℝ)
      (MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P)).support := by
    rw [mem_support_iff, coeff_map]
    change ((((aeval fun i => C (T i) * X i) P).coeff α : ℚ) : ℝ) ≠ 0
    exact_mod_cast (mem_support_iff.mp hα)
  rw [rationalAxisScaling_map_real] at hreal
  have hsource := scaleMvPolynomialAxes_support_subset (fun i => (T i : ℝ))
    (MvPolynomial.map (algebraMap ℚ ℝ) P) hreal
  apply mem_support_iff.mpr
  intro hz
  rw [mem_support_iff, coeff_map, hz, map_zero] at hsource
  exact hsource rfl

theorem rationalAxisScaling_mem_weightedSupportLE {σ : Type*} (T : σ → ℚ)
    (w : σ → ℕ) (d : ℕ) {P : MvPolynomial σ ℚ}
    (hP : P ∈ weightedSupportLE w d) :
    MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P ∈
      weightedSupportLE w d := by
  intro α hα
  exact hP (rationalAxisScaling_support_subset T P hα)

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem jointRationalPolynomialDilation_map (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ) :
    map (algebraMap ℚ ℝ) (jointRationalPolynomialDilation q R) =
      scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)⁻¹) (fun _ : B => 1))
        (map (algebraMap ℚ ℝ) R) := by
  rw [jointRationalPolynomialDilation, rationalAxisScaling_map_real]
  congr 1
  funext i
  cases i <;> simp

theorem jointRationalPolynomialDilation_eval₂ (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ)
    (u : U → ℝ) (b : B → ℝ) :
    eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) (jointRationalPolynomialDilation q R) =
      eval₂ (algebraMap ℚ ℝ) (Sum.elim (fun i => u i / (q : ℝ)) b) R := by
  rw [← eval_map, jointRationalPolynomialDilation_map, scaleMvPolynomialAxes_eval, eval_map]
  congr 1
  funext i
  cases i <;> simp [div_eq_mul_inv, mul_comm]

theorem jointRationalPolynomialDilation_mem_weightedSupportLE
    (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ) (w : U ⊕ B → ℕ) (d : ℕ)
    (hR : R ∈ weightedSupportLE w d) :
    jointRationalPolynomialDilation q R ∈ weightedSupportLE w d :=
  rationalAxisScaling_mem_weightedSupportLE _ w d hR

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedAxisScaling
namespace OAI


namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

theorem isWeightedHomogeneous_mul_pderiv {σ R : Type*} [CommRing R]
    (w : σ → ℕ) (i : σ) {Q P : MvPolynomial σ R} {d : ℕ}
    (hQ : Q.IsWeightedHomogeneous w (w i)) (hP : P.IsWeightedHomogeneous w d) :
    (Q * pderiv i P).IsWeightedHomogeneous w d := by
  classical
  rw [← P.support_sum_monomial_coeff, map_sum, Finset.mul_sum]
  apply (weightedHomogeneousSubmodule R w d).sum_mem
  intro a ha
  change (Q * pderiv i (monomial a (P.coeff a))).IsWeightedHomogeneous w d
  rw [pderiv_monomial]
  by_cases hi : a i = 0
  · simp only [hi, Nat.cast_zero, mul_zero, monomial_zero]
    exact (weightedHomogeneousSubmodule R w d).zero_mem
  · have hweight := Finsupp.weight_sub_single_add (w := w) hi
    rw [hP (MvPolynomial.mem_support_iff.mp ha)] at hweight
    have hm := hQ.mul (isWeightedHomogeneous_monomial w
      (a - Finsupp.single i 1) (P.coeff a * (a i : R)) rfl)
    simpa only [Nat.add_comm (w i), hweight] using hm

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

theorem scaleMvPolynomialAxes_weightedHomogeneousComponent
    (w : σ → ℕ) (T : σ → ℝ) (d : ℕ) (P : MvPolynomial σ ℝ) :
    weightedHomogeneousComponent w d (scaleMvPolynomialAxes T P) =
      scaleMvPolynomialAxes T (weightedHomogeneousComponent w d P) := by
  classical
  ext α
  simp only [coeff_weightedHomogeneousComponent, scaleMvPolynomialAxes_coeff]
  split_ifs <;> simp

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRealGroup
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {R S T I : Type*} [CommRing R] [CommRing S] [CommRing T] {w : I → ℕ}

theorem polynomialShearMap_zero (f : R →+* S) :
    polynomialShearMap (w := w) f 0 = 0 := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  simp only [polynomialShearMap_X]
  exact map_zero _

theorem polynomialShearMap_sum {κ : Type*} (f : R →+* S)
    (t : Finset κ) (D : κ → PolynomialShearLieAlgebra w R) :
    polynomialShearMap f (∑ k ∈ t, D k) = ∑ k ∈ t, polynomialShearMap f (D k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, polynomialShearMap_zero]
  | @insert k t hk ih =>
    simp only [Finset.sum_insert hk, polynomialShearMap_add, ih]

theorem polynomialShearMap_comp (f : R →+* S) (g : S →+* T)
    (D : PolynomialShearLieAlgebra w R) :
    polynomialShearMap g (polynomialShearMap f D) = polynomialShearMap (g.comp f) D := by
  apply Subtype.ext
  apply MvPolynomial.derivation_ext
  intro i
  simp only [polynomialShearMap_X, MvPolynomial.map_map]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem polynomialTranslationPath_linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (i : σ) :
    polynomialTranslationPath z (linearCoordinatePolynomial A i) =
      Polynomial.C (linearCoordinatePolynomial A i) -
        Polynomial.C (C (A z i)) * Polynomial.X := by
  classical
  have hsum : (∑ j, A (Pi.single j 1) i • C (z j)) = (C (A z i) : MvPolynomial τ ℚ) := by
    simp only [← C_mul', ← map_mul, ← map_sum, linearMap_apply_sum_coordinates]
  rw [linearCoordinatePolynomial, map_sum]
  simp only [map_smul, polynomialTranslationPath_X, smul_sub,
    Finset.sum_sub_distrib, ← smul_mul_assoc, Polynomial.smul_C]
  rw [← map_sum, ← Finset.sum_mul, ← map_sum, hsum]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

theorem linearCoordinatePolynomial_eq_sum [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) :
    linearCoordinatePolynomial A i = ∑ j, A (Pi.single j 1) i • (X j : MvPolynomial τ ℚ) := by
  unfold linearCoordinatePolynomial
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun c : ℚ => c • (X j : MvPolynomial τ ℚ))
  apply congrArg (fun x : τ → ℚ => A x i)
  funext k
  by_cases hk : k = j
  · subst k
    simp
  · simp [hk]

theorem linearCoordinatePolynomial_isWeightedHomogeneous [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hA : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0) (i : σ) :
    (linearCoordinatePolynomial A i).IsWeightedHomogeneous v (w i) := by
  rw [linearCoordinatePolynomial_eq_sum]
  apply (weightedHomogeneousSubmodule ℚ v (w i)).sum_mem
  intro j _
  by_cases hj : v j = w i
  · exact hj ▸ (weightedHomogeneousSubmodule ℚ v (v j)).smul_mem
      (A (Pi.single j 1) i) (isWeightedHomogeneous_X (R := ℚ) v j)
  · rw [hA j i hj, zero_smul]
    exact isWeightedHomogeneous_zero ℚ v (w i)

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

theorem weightedLinearInverseMask_height [DecidableEq σ]
    (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    {H : ℕ} (hB : ∀ j i, RationalHeightLE (B (Pi.single i 1) j) H)
    (i : σ) (j : τ) :
    RationalHeightLE (weightedLinearInverseMask B v w (Pi.single i 1) j) H := by
  rw [weightedLinearInverseMask_entry]
  split_ifs
  · exact hB j i
  · exact rationalHeightLE_zero ((B (Pi.single i 1) j).den_pos.trans_le (hB j i).2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MajorTranslationPartnerBudget
namespace OAI

section

namespace Erdos3

theorem exists_majorTranslationPartnerBudget_bound (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      productNiltestBudget ((p + a) ^ a + raisedNiltestBudget p + 2) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a + (X + (X + 2) ^ 2 + 3) + 2
  let P := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, Q, X, Polynomial.eval₂_pow, productNiltestBudget,
    productObservableLipBudget, raisedNiltestBudget] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PointwiseSymbolBudget
namespace OAI

section

namespace Erdos3

theorem exists_symbol_extension_budget (a c₀ c₁ c₂ c₃ c₄ : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q₁ := (p + c₀) ^ c₀ + (p + 2) ^ a + p + 2
      let q₂ := (q₁ + c₁) ^ c₁ + (q₁ + c₂) ^ c₂ + q₁ + 2
      let q₃ := (q₂ + c₃) ^ c₃ + q₂ + 2
      (p + c₀) ^ c₀ + (q₂ + c₃) ^ c₃ + (q₃ + c₄) ^ c₄ ≤ (p + 2) ^ C := by
  let Q₁ : Polynomial ℕ := (Polynomial.X + Polynomial.C c₀) ^ c₀ +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let Q₂ : Polynomial ℕ := (Q₁ + Polynomial.C c₁) ^ c₁ + (Q₁ + Polynomial.C c₂) ^ c₂ + Q₁ + 2
  let Q₃ : Polynomial ℕ := (Q₂ + Polynomial.C c₃) ^ c₃ + Q₂ + 2
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C c₀) ^ c₀ +
    (Q₂ + Polynomial.C c₃) ^ c₃ + (Q₃ + Polynomial.C c₄) ^ c₄
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨(C + 1) * C, by nlinarith, ?_⟩
  intro p hp
  apply le_trans _ (shifted_self_power_le_base_power hp C)
  simpa [B, Q₁, Q₂, Q₃, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorCorrelationBudget
namespace OAI

section

namespace Erdos3

theorem exists_translationMajorCorrelationBudget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      translationMajorPairBudget a p ≤ (p + C) ^ C ∧
        (translationMajorPairBudget a p + (b : ℝ)) ^ b ≤ (p + C) ^ C := by
  let R : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + 2) ^ 2 + 3 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have htotal : translationMajorPairBudget a p +
      (translationMajorPairBudget a p + (b : ℝ)) ^ b ≤ (p + C) ^ C := by
    simpa [R, translationMajorPairBudget, raisedNiltestBudget, Polynomial.eval₂_pow]
      using hbound p hp
  have hr : 0 ≤ translationMajorPairBudget a p := by
    unfold translationMajorPairBudget raisedNiltestBudget
    positivity
  have hproduct : 0 ≤ (translationMajorPairBudget a p + (b : ℝ)) ^ b := by positivity
  exact ⟨(le_add_of_nonneg_right hproduct).trans htotal,
    (le_add_of_nonneg_left hr).trans htotal⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CurrentLayerSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem inv_mul_coord_mem_layer_of_quotient_eq (k : ℕ) (a b : F.Group)
    (h : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) a =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) b) :
    (a⁻¹ * b).coord ∈ F.layer k := by
  apply (lieQuotientMap_eq_zero (F.layerIdeal k) _).mp
  have hq : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  exact congrArg NilpotentLieBCHGroup.coord hq

theorem mul_inv_coord_mem_layer_of_quotient_eq (k : ℕ) (a b : F.Group)
    (h : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) a =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) b) :
    (a * b⁻¹).coord ∈ F.layer k := by
  apply (lieQuotientMap_eq_zero (F.layerIdeal k) _).mp
  have hq : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  exact congrArg NilpotentLieBCHGroup.coord hq

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealSpanIntegerDefiningRows
namespace OAI

section

namespace Erdos3

open scoped Matrix

def realSpanIntegerRowBound (n m H : ℕ) : ℕ :=
  imageDefiningHeight n m H ^ (m * m) * imageDefiningHeight n m H

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

noncomputable def majorSlowDilationPullback (q : ℕ) (H T : U → ℝ)
    (S : MvPolynomial (U ⊕ B) ℝ) : MvPolynomial (U ⊕ B) ℝ :=
  scaleMvPolynomialAxes
    (Sum.elim (fun i => H i / ((q : ℝ) * T i)) (fun _ : B => 1)) S

 theorem majorSlowDilationPullback_eval (q : ℕ) (hq : 0 < q) (H T : U → ℝ)
    (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (S : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (z : B → ℝ) :
    eval (Sum.elim (fun i => u i / H i) z) (majorSlowDilationPullback q H T S) =
      eval (Sum.elim (fun i => (u i / (q : ℝ)) / T i) z) S := by
  rw [majorSlowDilationPullback, scaleMvPolynomialAxes_eval]
  apply congrArg (fun x : U ⊕ B → ℝ => eval x S)
  funext j
  cases j with
  | inl i =>
    dsimp only [Sum.elim_inl]
    field_simp [(hH i).ne', (hT i).ne', (Nat.cast_pos.mpr hq : (0 : ℝ) < q).ne']
  | inr j => simp only [Sum.elim_inr, one_mul]

theorem algebraic_major_dilation_pullback_identity
    (K : Submodule ℝ (B → ℝ)) (D : MvPolynomial (U ⊕ B) ℝ)
    (A : B → MvPolynomial U ℝ) (S : MvPolynomial (U ⊕ B) ℝ)
    (R : MvPolynomial (U ⊕ B) ℚ) (q : ℕ) (hq : 0 < q)
    (H T : U → ℝ) (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (hsource : ∀ (v : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim (fun i => (q : ℝ) * v i) b) D =
        eval (Sum.elim (fun i => v i / T i)
          (fun j => b j - eval (fun i => (q : ℝ) * v i) (A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim v b) R)
    (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
    eval (Sum.elim u b) D =
      eval (Sum.elim (fun i => u i / H i) (fun j => b j - eval u (A j)))
        (majorSlowDilationPullback q H T S) +
      eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) (jointRationalPolynomialDilation q R) := by
  rw [majorSlowDilationPullback_eval q hq H T hH hT,
    jointRationalPolynomialDilation_eval₂]
  have hcancel : (fun i => (q : ℝ) * (u i / (q : ℝ))) = u := by
    funext i
    exact mul_div_cancel₀ (u i) (Nat.cast_ne_zero.mpr hq.ne')
  simpa only [hcancel] using hsource (fun i => u i / (q : ℝ)) b hb

 theorem majorSlowDilationPullback_mass_le (q : ℕ) (hq : 0 < q) (H T : U → ℝ)
    (hH : ∀ i, 0 < H i) (hT : ∀ i, 0 < T i)
    (S : MvPolynomial (U ⊕ B) ℝ) {c : ℝ} (hc : 1 ≤ c)
    (hHT : ∀ i, H i ≤ c * (q : ℝ) * T i) {d : ℕ} (hS : S.totalDegree ≤ d) :
    realPolynomialMass (majorSlowDilationPullback q H T S) ≤ c^d * realPolynomialMass S := by
  apply jointPolynomialDilation_mass_le _ S hc _ hS
  intro i
  have hqT : 0 < (q : ℝ) * T i := mul_pos (Nat.cast_pos.mpr hq) (hT i)
  rw [abs_of_nonneg (div_nonneg (hH i).le hqT.le)]
  apply (div_le_iff₀ hqT).mpr
  simpa only [mul_assoc] using hHT i

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B : Type*}

theorem jointResidueAffinePolynomial_eval (q : ℕ) (r : U → ℤ)
    (D : MvPolynomial (U ⊕ B) ℝ) (u : U → ℝ) (b : B → ℝ) :
    eval (Sum.elim u b) (jointResidueAffinePolynomial q r D) =
      eval (Sum.elim (fun i => (r i : ℝ) + (q : ℝ) * u i) b) D := by
  induction D using MvPolynomial.induction_on with
  | C c => simp [jointResidueAffinePolynomial]
  | add D E hD hE => simpa only [jointResidueAffinePolynomial, map_add] using congrArg₂ (· + ·) hD hE
  | mul_X D i hD =>
    cases i <;> simp [jointResidueAffinePolynomial, map_mul] at hD ⊢ <;> rw [hD] <;> simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeFixedVerticalPower
namespace OAI

section

namespace Erdos3

theorem exists_vertical_pair_precision :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∃ q r rho eta : ℝ,
      p ≤ q ∧ p ≤ r ∧ q ≤ (p + C) ^ C ∧ r ≤ (p + C) ^ C ∧
      verticalDecompositionBudget q ≤ (p + C) ^ C ∧
      verticalDecompositionBudget r ≤ (p + C) ^ C ∧
      0 < rho ∧ 0 < eta ∧ rho⁻¹ ≤ Real.exp q ∧ eta⁻¹ ≤ Real.exp r ∧
      rho + Real.exp (verticalDecompositionBudget q) * eta ≤ Real.exp (-p) / 2 ∧
      Real.exp (-((p + C) ^ C)) ≤ (Real.exp (-p) / 2) /
        (Real.exp (verticalDecompositionBudget q) * Real.exp (verticalDecompositionBudget r)) := by
  obtain ⟨c, _, hV⟩ := exists_verticalDecompositionBudget_bound
  let Q : Polynomial ℕ := Polynomial.X + 4
  let R : Polynomial ℕ := Q + (Q + Polynomial.C c) ^ c
  let P : Polynomial ℕ := R + (R + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  let q := p + 4
  let r := q + (q + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hf : 0 ≤ (q + c) ^ c := by positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hg : 0 ≤ (r + c) ^ c := by positivity
  have hb : r + (r + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, R, Q, r, q, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  have hVq := hV q hq
  have hVr := hV r hr
  have hVqC : verticalDecompositionBudget q ≤ (p + C) ^ C := by
    have hfR : (q + c) ^ c ≤ r := by dsimp [r]; linarith
    exact hVq.trans (hfR.trans hrC)
  have hVrC : verticalDecompositionBudget r ≤ (p + C) ^ C := by linarith
  have hscaled : Real.exp (verticalDecompositionBudget q) * Real.exp (-r) ≤ Real.exp (-q) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [r]
    linarith
  have he4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hsplit : Real.exp (-q) * Real.exp 4 = Real.exp (-p) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [q]
    ring
  have hfour : Real.exp (-q) * 4 ≤ Real.exp (-p) := by
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_left he4 (Real.exp_nonneg _)
  have hsmall : Real.exp (-q) + Real.exp (verticalDecompositionBudget q) * Real.exp (-r) ≤
      Real.exp (-p) / 2 := by linarith
  refine ⟨q, r, Real.exp (-q), Real.exp (-r), hpq, hpq.trans hqr, hqr.trans hrC, hrC,
    hVqC, hVrC, Real.exp_pos _, Real.exp_pos _, ?_, ?_, hsmall, ?_⟩
  · simp only [Real.exp_neg, inv_inv, le_refl]
  · simp only [Real.exp_neg, inv_inv, le_refl]
  · apply (le_div_iff₀ (mul_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
    have hloss : q + verticalDecompositionBudget q + verticalDecompositionBudget r ≤ (p + C) ^ C := by
      have hstep : q + verticalDecompositionBudget q ≤ r := by dsimp [r]; linarith
      linarith
    calc
      _ ≤ Real.exp (-(q + verticalDecompositionBudget q + verticalDecompositionBudget r)) *
          (Real.exp (verticalDecompositionBudget q) * Real.exp (verticalDecompositionBudget r)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      _ = Real.exp (-q) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-p) / 2 := by linarith [Real.exp_pos (-q)]

end Erdos3

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

theorem rationalPolynomial_realMass_le {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) {K d : ℕ}
    (hP : RationalPolynomialHeightLE P K) (hd : P.totalDegree ≤ d) :
    realPolynomialMass (map (algebraMap ℚ ℝ) P) ≤
      ((Fintype.card σ + 1) ^ d * K : ℕ) := by
  classical
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support
    (support_map_subset (algebraMap ℚ ℝ) P)]
  have hc : P.support.card ≤ (Fintype.card σ + 1) ^ d :=
    boundedExponentSet_card_le P.support d (fun _ hm => (le_totalDegree hm).trans hd)
  calc
    _ ≤ ∑ _m ∈ P.support, (K : ℝ) := by
      apply Finset.sum_le_sum
      intro m _
      rw [coeff_map]
      exact (hP m).abs_real_le
    _ = (P.support.card : ℝ) * K := by simp
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_right K hc

theorem linearCoordinatePolynomial_realMass_le
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) {H : ℕ}
    (hA : ∀ i j, RationalHeightLE (A (Pi.single j 1) i) H) (i : σ) :
    realPolynomialMass (map (algebraMap ℚ ℝ) (linearCoordinatePolynomial A i)) ≤
      (Fintype.card τ * H : ℕ) := by
  classical
  have hcast (q : ℚ) : algebraMap ℚ ℝ q = (q : ℝ) := by norm_num
  rw [linearCoordinatePolynomial, map_sum]
  simp only [← C_mul', map_mul, map_C, map_X, hcast]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : τ, (H : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      apply (realPolynomialMass_C_mul_le _ _).trans
      rw [realPolynomialMass_X, mul_one]
      convert (hA i j).abs_real_le using 1 <;> first | rfl | congr!
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential
namespace OAI

section

namespace Erdos3

noncomputable def linearRestrictionLogPolynomial (d : ℕ) (P Q : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C d * Polynomial.X + Q +
    Polynomial.C d * (Polynomial.X + P + 1) +
    (Polynomial.X + 1) ^ d * Q +
    Polynomial.X * Polynomial.X * Polynomial.C d * P

noncomputable def projectedPotentialLogPolynomial (d : ℕ) : Polynomial ℕ :=
  let U := linearRestrictionLogPolynomial d Polynomial.X Polynomial.X
  let V := Polynomial.X + Polynomial.X * (Polynomial.C d + U)
  linearRestrictionLogPolynomial d ((Polynomial.X + 2) ^ 7) V

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

theorem majorPhaseCoordinateDenominator_grid (q : η → ℕ)
    (R : η → MvPolynomial σ ℚ)
    (hR : ∀ i, (fun α => (R i).coeff α) ∈ denominatorGrid (q i)) (i : η) :
    (fun α => (R i).coeff α) ∈ denominatorGrid (∏ j, q j) := by
  classical
  exact denominatorGrid_subset_of_dvd (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    (hR i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

variable {X : Type*}

theorem lowTaggedFrequency_bound (d : ℕ) (a : (Σ j, J j) → ℤ) (B : ℝ)
    (ha : ∀ i, |(a i : ℝ)| ≤ B) :
    ∀ i, |(lowTaggedFrequency J d a i : ℝ)| ≤ B := fun i => ha (lowTaggedIndex J d i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationCoordinateBudget
namespace OAI

section

namespace Erdos3

theorem detectedTranslationCoordinate_denominator_le_exp (n k m q : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hk : (k : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ Real.exp p)
    (hq : q ≤ ⌈Real.exp p⌉₊ ^ (n * k) * m) :
    (q : ℝ) ≤ Real.exp ((p + 3) ^ 3) := by
  have hnk : (n : ℝ) * k ≤ p * p :=
    mul_le_mul hn hk (Nat.cast_nonneg _) hp
  have hnk' := mul_le_mul_of_nonneg_right hnk (show 0 ≤ p + 1 by positivity)
  have hlog : ((n * k : ℕ) : ℝ) * (p + 1) + p ≤ (p + 3) ^ 3 := by
    rw [Nat.cast_mul]
    nlinarith [sq_nonneg p]
  calc
    (q : ℝ) ≤ ((⌈Real.exp p⌉₊ ^ (n * k) * m : ℕ) : ℝ) := Nat.cast_le.mpr hq
    _ ≤ Real.exp (((n * k : ℕ) : ℝ) * (p + 1)) * Real.exp p := by
      rw [Nat.cast_mul]
      exact mul_le_mul (ceil_exp_power_le_exp hp (n * k)) hm
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((n * k : ℕ) : ℝ) * (p + 1) + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DetectedTranslationMajorSamplingContainment
namespace OAI

section

namespace Erdos3

theorem realSpanIntegerRowBound_le_exp_of_imageHeight (n m H : ℕ) {p a : ℝ}
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hm : (m : ℝ) ≤ p)
    (himage : (imageDefiningHeight n m H : ℝ) ≤ Real.exp a) :
    (realSpanIntegerRowBound n m H : ℝ) ≤ Real.exp ((p * p + 1) * a) := by
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (imageDefiningHeight n m H)) himage (m * m)
  rw [← Real.exp_nat_mul] at hpow
  rw [realSpanIntegerRowBound, Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp ((m * m : ℕ) * a) * Real.exp a :=
      mul_le_mul hpow himage (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp ((((m : ℝ) * m) + 1) * a) := by
      rw [← Real.exp_add, Nat.cast_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ ha
      have hsq := mul_le_mul hm hm (Nat.cast_nonneg _) hp
      linarith

theorem samplingProjectedImage_row_le_exp (n m : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) :
    (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
      Real.exp ((p * p + 1) * (((p + 2) ^ 4 + 3) ^ 10)) := by
  have hpq : p ≤ (p + 2) ^ 4 + 1 :=
    (le_power_budget hp (by decide : 1 ≤ 4)).trans (le_add_of_nonneg_right (by norm_num))
  have hheight := imageDefiningHeight_le_exp n m ⌈Real.exp ((p + 2) ^ 4)⌉₊
    (by positivity : 0 ≤ (p + 2) ^ 4 + 1) (hn.trans hpq) (hm.trans hpq)
    (ceil_exp_le_exp_add_one (by positivity : 0 ≤ (p + 2) ^ 4))
  apply realSpanIntegerRowBound_le_exp_of_imageHeight n m _ hp (by positivity) hm
  convert hheight using 1
  congr 2
  ring

theorem exists_samplingProjectedImage_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n m : ℕ) (p : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (m : ℝ) ≤ p →
      (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
        Real.exp ((p + C) ^ C) ∧
      (m : ℝ) * realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ *
          Real.exp ((p + 3) ^ 3) ≤ Real.exp ((p + C) ^ C) := by
  let T : Polynomial ℕ := Polynomial.X +
    (Polynomial.X * Polynomial.X + 1) * (((Polynomial.X + 2) ^ 4 + 3) ^ 10) +
      (Polynomial.X + 3) ^ 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro n m p hp hn hm
  let R : ℝ := (p * p + 1) * (((p + 2) ^ 4 + 3) ^ 10)
  have htotal : p + R + (p + 3) ^ 3 ≤ (p + C) ^ C := by
    simpa only [T, R, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_one, Polynomial.eval₂_ofNat]
      using hbudget p hp
  have hrow := samplingProjectedImage_row_le_exp n m hp hn hm
  change (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp R at hrow
  have hR : R ≤ (p + C) ^ C := by
    have hcubic : 0 ≤ (p + 3) ^ 3 := by positivity
    linarith
  refine ⟨hrow.trans (Real.exp_le_exp.mpr hR), ?_⟩
  have hmexp : (m : ℝ) ≤ Real.exp p := hm.trans (by linarith [Real.add_one_le_exp p])
  calc
    _ ≤ Real.exp p * Real.exp R * Real.exp ((p + 3) ^ 3) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hmexp hrow (Nat.cast_nonneg _) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (p + R + (p + 3) ^ 3) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr htotal

end Erdos3

end

section

namespace Erdos3

theorem exists_samplingProjectedImage_complete_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n m : ℕ) (p : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (m : ℝ) ≤ p →
      Real.exp ((p + 3) ^ 3) ≤ Real.exp ((p + C) ^ C) ∧
      (realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ : ℝ) ≤
        Real.exp ((p + C) ^ C) ∧
      (m : ℝ) * realSpanIntegerRowBound n m ⌈Real.exp ((p + 2) ^ 4)⌉₊ *
        Real.exp ((p + 3) ^ 3) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨a, ha, hbudget⟩ := exists_samplingProjectedImage_budget
  refine ⟨a + 3, by omega, ?_⟩
  intro n m p hp hn hm
  have hbase : (1 : ℝ) ≤ p + (a + 3 : ℕ) := by
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    push_cast
    linarith
  have haC : p + a ≤ p + (a + 3 : ℕ) := by push_cast; linarith
  have hthreeC : p + 3 ≤ p + (a + 3 : ℕ) := by
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    push_cast
    linarith
  have hlarge : (p + a) ^ a ≤ (p + (a + 3 : ℕ)) ^ (a + 3) :=
    (pow_le_pow_left₀ (by positivity) haC a).trans
      (pow_le_pow_right₀ hbase (by omega))
  have hsmall : (p + 3) ^ 3 ≤ (p + (a + 3 : ℕ)) ^ (a + 3) :=
    (pow_le_pow_left₀ (by positivity) hthreeC 3).trans
      (pow_le_pow_right₀ hbase (by omega))
  obtain ⟨hrow, herror⟩ := hbudget n m p hp hn hm
  exact ⟨Real.exp_le_exp.mpr hsmall,
    hrow.trans (Real.exp_le_exp.mpr hlarge),
    herror.trans (Real.exp_le_exp.mpr hlarge)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DetectedTranslationPhaseBudget
namespace OAI

section

namespace Erdos3

theorem exists_detectedTranslationPhase_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n t k b m q : ℕ) (p H A : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (t : ℝ) ≤ p → (k : ℝ) ≤ p →
      (b : ℝ) ≤ p → 0 ≤ H → H ≤ Real.exp p →
      0 ≤ A → A ≤ Real.exp p → (m : ℝ) ≤ Real.exp p →
      q ≤ ⌈Real.exp p⌉₊ ^ (t * k) * m →
      let Z : ℝ := ((n : ℝ) + 1) ^ d * k * H * A
      Z ≤ Real.exp ((p + C) ^ C) ∧
      ((d : ℝ) + 1) * ((t : ℝ) * Z) *
          (1 + (b : ℝ) * d * t * Z) ^ d ≤ Real.exp ((p + C) ^ C) ∧
      (d.factorial * q ^ (d + 1) : ℕ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨a, _, hcoordinate⟩ := exists_translationCoordinate_budget d
  let S : Polynomial ℕ :=
    Polynomial.C (d + 3) * (Polynomial.X + 1) + (Polynomial.X + 3) ^ 3
  let Q : Polynomial ℕ := S + (S + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro n t k b m q p H A hp hn ht hk hb hH hHp hA hAp hm hq
  let Z : ℝ := ((n : ℝ) + 1) ^ d * k * H * A
  let s : ℝ := ((d : ℝ) + 3) * (p + 1) + (p + 3) ^ 3
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsbudget : s + (s + a) ^ a ≤ (p + C) ^ C := by
    simpa [Q, S, s, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hsp : p ≤ s := by
    dsimp [s]
    have hdp := mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hp
    have hc : 0 ≤ (p + 3) ^ 3 := by positivity
    nlinarith
  have hsZ : ((d : ℝ) + 3) * p + d ≤ s := by
    dsimp [s]
    have hc : 0 ≤ (p + 3) ^ 3 := by positivity
    nlinarith
  have hsq : (p + 3) ^ 3 ≤ s := by
    exact le_add_of_nonneg_left (by positivity)
  have hnp : (n : ℝ) + 1 ≤ Real.exp (p + 1) := by
    linarith [Real.add_one_le_exp (p + 1)]
  have hkp : (k : ℝ) ≤ Real.exp p := hk.trans (by linarith [Real.add_one_le_exp p])
  have hZ : Z ≤ Real.exp s := by
    apply le_trans _ (Real.exp_le_exp.mpr hsZ)
    calc
      Z ≤ Real.exp (p + 1) ^ d * Real.exp p * Real.exp p * Real.exp p := by
        dsimp [Z]
        gcongr
      _ = Real.exp (((d : ℝ) + 3) * p + d) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hqexp : (q : ℝ) ≤ Real.exp s :=
    (detectedTranslationCoordinate_denominator_le_exp t k m q hp ht hk hm hq).trans
      (Real.exp_le_exp.mpr hsq)
  have hts : (t : ℝ) ≤ Real.exp s :=
    (ht.trans hsp).trans (by linarith [Real.add_one_le_exp s])
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  obtain ⟨hmass, hdenom⟩ := hcoordinate b t q s Z 1 hs (hb.trans hsp) hts
    hZ0 hZ zero_le_one (Real.one_le_exp_iff.mpr hs) hqexp
  have hpow : (s + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left hs).trans hsbudget
  have hsle : s ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) a)).trans hsbudget
  refine ⟨hZ.trans (Real.exp_le_exp.mpr hsle), ?_, hdenom.trans (Real.exp_le_exp.mpr hpow)⟩
  have hmass' := hmass.trans (Real.exp_le_exp.mpr hpow)
  simpa only [Z, mul_one, mul_assoc] using hmass'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DetectedTranslationUniformCoordinateBounds
namespace OAI

section

namespace Erdos3

noncomputable def detectedTranslationCoordinateConstant (d : ℕ) : ℕ :=
  (exists_detectedTranslationPhase_budget d).choose

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

noncomputable def restoredMajorRemainder (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  R + MvPolynomial.map (Int.castRingHom ℚ)
    (weightedHomogeneousComponent w d (floorIntegerPolynomial F))

theorem restoredMajorRemainder_coefficientGrid (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ) (q : ℕ)
    (hR : (fun a => R.coeff a) ∈ denominatorGrid q) :
    (fun a => (restoredMajorRemainder F w d R).coeff a) ∈ denominatorGrid q :=
  add_integerPolynomial_coefficientGrid R
    (weightedHomogeneousComponent w d (floorIntegerPolynomial F)) q hR

theorem restoredMajorRemainder_eval (F : MvPolynomial σ ℝ)
    (w : σ → ℕ) (d : ℕ) (R : MvPolynomial σ ℚ) (z : σ → ℝ) :
    eval₂ (algebraMap ℚ ℝ) z (restoredMajorRemainder F w d R) =
      eval₂ (algebraMap ℚ ℝ) z R +
        eval z (MvPolynomial.map (Int.castRingHom ℝ)
          (weightedHomogeneousComponent w d (floorIntegerPolynomial F))) := by
  rw [restoredMajorRemainder, eval₂_add]
  congr 1
  rw [← eval_map, integerPolynomial_map_rat_real]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialFromRealGrid
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem exists_rationalPolynomial_of_realCoefficientGrid
    {σ : Type*} (P : MvPolynomial σ ℝ) {q : ℕ} (hq : 0 < q)
    (hP : realPolynomialCoefficientGrid q P) :
    ∃ Q : MvPolynomial σ ℚ,
      MvPolynomial.map (algebraMap ℚ ℝ) Q = P ∧
      (fun α => Q.coeff α) ∈ denominatorGrid q ∧ Q.totalDegree = P.totalDegree := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  obtain ⟨z, hz⟩ := hP
  have hrange : P ∈ (MvPolynomial.map (algebraMap ℚ ℝ)).range := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨α, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    refine ⟨(z α : ℚ) / (q : ℚ), ?_⟩
    have hα : (z α : ℝ) = (q : ℝ) * P.coeff α := congrFun hz α
    simp only [map_div₀, map_intCast, map_natCast, hα, mul_div_cancel_left₀ _ hq0]
  obtain ⟨Q, hQ⟩ := hrange
  refine ⟨Q, hQ, ?_, ?_⟩
  · apply (realPolynomialCoefficientGrid_ratCast_iff q Q).mp
    rw [hQ]
    exact ⟨z, hz⟩
  · rw [← hQ]
    unfold totalDegree
    rw [MvPolynomial.support_map_of_injective Q (algebraMap ℚ ℝ).injective]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

theorem lowTaggedVariableEmbedding_eval_coordinates (d : ℕ)
    (u : X → ℝ) (z : ∀ j, J j → ℝ) :
    (Sum.elim u (fun i : Σ j, J j => z i.1 i.2)) ∘ lowTaggedVariableEmbedding J d =
      Sum.elim u (lowTaggedCoordinates J d z) := by
  funext v
  cases v <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorRealSubstitutionBound
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

theorem scaleMvPolynomialAxes_substitution {I J : Type*}
    (T : J → ℝ) (f : I → MvPolynomial J ℝ) (p : MvPolynomial I ℝ) :
    scaleMvPolynomialAxes T (eval₂Hom C f p) =
      eval₂Hom C (fun i => scaleMvPolynomialAxes T (f i)) p := by
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval]
  simp only [coe_eval₂Hom, ← eval_assoc, Function.comp_def, scaleMvPolynomialAxes_eval]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialAffineFullMass
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem scaleMvPolynomialAxes_C_mul {ι : Type*}
    (T : ι → ℝ) (c : ℝ) (p : MvPolynomial ι ℝ) :
    scaleMvPolynomialAxes T (C c * p) = C c * scaleMvPolynomialAxes T p := by
  apply MvPolynomial.funext
  intro y
  simp only [scaleMvPolynomialAxes_eval, map_mul, eval_C]

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

theorem exists_finiteSupport_rationalGridLift {V : Type*}
    (S : Finset (V →₀ ℕ)) (P : MvPolynomial V ℝ) (q : ℕ)
    (hsupport : P.support ⊆ S)
    (hgrid : ∀ α : V →₀ ℕ, ∃ z : ℤ, P.coeff α = (z : ℝ) / (q : ℝ)) :
    ∃ r : MvPolynomial V ℚ, r.support ⊆ S ∧
      (∀ α : V →₀ ℕ, ∃ z : ℤ, r.coeff α = (z : ℚ) / (q : ℚ)) ∧
      MvPolynomial.map (Rat.castHom ℝ) r = P := by
  classical
  let z : S → ℤ := fun α => Classical.choose (hgrid α.val)
  let c : S → ℚ := fun α => (z α : ℚ) / (q : ℚ)
  let r := polynomialOfFiniteCoefficientVector S c
  have hcoeff (α : S) : r.coeff α.val = c α :=
    polynomialOfFiniteCoefficientVector_coeff S c α
  have hzero (α : V →₀ ℕ) (hα : α ∉ S) : r.coeff α = 0 :=
    polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem S c α hα
  refine ⟨r, polynomialOfFiniteCoefficientVector_support_subset S c, ?_, ?_⟩
  · intro α
    by_cases hα : α ∈ S
    · exact ⟨z ⟨α, hα⟩, hcoeff ⟨α, hα⟩⟩
    · refine ⟨0, ?_⟩
      rw [hzero α hα]
      simp only [Int.cast_zero, zero_div]
  · ext α
    rw [MvPolynomial.coeff_map]
    by_cases hα : α ∈ S
    · rw [hcoeff ⟨α, hα⟩]
      change (Rat.castHom ℝ) ((z ⟨α, hα⟩ : ℚ) / (q : ℚ)) = P.coeff α
      simp only [map_div₀, map_intCast, map_natCast]
      exact (Classical.choose_spec (hgrid α)).symm
    · rw [hzero α hα, map_zero]
      exact (MvPolynomial.notMem_support_iff.mp (fun h => hα (hsupport h))).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMixedLiftNormalizedMass
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

theorem scaleMvPolynomialAxes_neg {V : Type*} (T : V → ℝ) (p : MvPolynomial V ℝ) :
    scaleMvPolynomialAxes T (-p) = -scaleMvPolynomialAxes T p := by
  ext α
  simp only [scaleMvPolynomialAxes_coeff, coeff_neg, neg_mul]

theorem normalizedAxes_homogeneousComponent_commute {V : Type*}
    (T : V → ℝ) (w : V → ℕ) (n : ℕ) (p : MvPolynomial V ℝ) :
    scaleMvPolynomialAxes T (weightedHomogeneousComponent w n p) =
      weightedHomogeneousComponent w n (scaleMvPolynomialAxes T p) := by
  classical
  ext α
  simp only [scaleMvPolynomialAxes_coeff, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedFrozenPolynomialMass
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial

theorem scaleMvPolynomialAxes_freezePolynomial {I : Type*} (keep : I → Prop)
    (T : I → ℝ) (hT : ∀ i, T i ≠ 0) (fixed : {i // ¬ keep i} → ℝ)
    (P : MvPolynomial I ℝ) :
    scaleMvPolynomialAxes (fun i : {i // keep i} => T i.val) (freezePolynomial keep fixed P) =
      freezePolynomial keep (fun i => fixed i / T i.val) (scaleMvPolynomialAxes T P) := by
  classical
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval, freezePolynomial_eval,
    freezePolynomial_eval, scaleMvPolynomialAxes_eval]
  apply congrArg (fun y => MvPolynomial.eval y P)
  funext i
  by_cases hi : keep i
  · simp only [finiteSplitPoint, dif_pos hi]
  · simp only [finiteSplitPoint, dif_neg hi]
    field_simp [hT i]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AllocatedKeptCommonCurrentGradeLocalNiltest
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped BigOperators TensorProduct

theorem realPolynomialCoefficientGrid_homogeneousComponent {σ : Type*}
    {q : ℕ} {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P)
    (k : ℕ) : realPolynomialCoefficientGrid q (homogeneousComponent k P) := by
  classical
  obtain ⟨z, hz⟩ := hP
  refine ⟨fun α => if α.degree = k then z α else 0, funext fun α => ?_⟩
  change ((if α.degree = k then z α else 0 : ℤ) : ℝ) =
    (q : ℝ) * (homogeneousComponent k P).coeff α
  rw [coeff_homogeneousComponent]
  split_ifs with h
  · exact congrFun hz α
  · simp

end Erdos3

end

end OAI
end


