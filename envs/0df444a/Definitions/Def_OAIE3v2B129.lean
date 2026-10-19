-- Prove2me | Definitions.Def_OAIE3v2B129
-- name    : OAIE3v2B129
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:46:16.251886+00:00
-- url     : https://prove2.me/theorems/1b4bdefc-e2d5-433f-87cf-b231472a9fca
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 131 of 311
-- statement:
--   Definitions bundle 131 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B116` of this split.
--
--   Modules: `Estimates/CoefficientModeLowerTerms.lean`, `Estimates/CoefficientModeRationalDecomposition.lean`, `Estimates/FastCoefficientImage.lean`, `Estimates/FreeWeightedEvaluationBounds.lean`, `Estimates/NativeEquivalenceTransitivity.lean`, `Estimates/NativeProductCoefficient.lean`, `Estimates/OptionMarkedSurjective.lean`, `Estimates/ProductOrbitCongruence.lean`, `Estimates/QuantitativeNoninjectivity.lean`, `Estimates/QuotientTopSymbol.lean`, `Estimates/RationalCentralCircle.lean`, `Estimates/ReducedNativeFactorization.lean`, `Estimates/ReducedSquareSymbol.lean`, `Estimates/ShiftedGradedCalculus.lean`, `Estimates/SiteTwistCommonModulus.lean`, `Estimates/SquareRationalModel.lean`, `Estimates/SubspaceLayeredModeSmoothRemoval.lean`, `Estimates/SymbolFastMembership.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/EuclideanJetTorus.lean`, `Fourier/HomogeneousGradedProjectionFrequency.lean`, `Fourier/OneSiteFourierAverage.lean`, `Fourier/SectionRetainedFourier.lean`, `Lattices/AffineCoefficientCoverTilt.lean`, `Lattices/AffineCoefficientResidueWidths.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Lattices/AffineOneSiteNormalizedLaw.lean`, `Lattices/AnchoredCubeResidueWidths.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Lattices/RetainedAffineCommonCover.lean`, `Linear/AssociatedGradedBasisIndependence.lean`, `Linear/CoefficientModeRankContradiction.lean`, `Linear/DualLogarithmicDifferential.lean`, `Linear/ProductOneSiteProjectionCap.lean`, `Linear/SquareBasisGeometry.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/FreeWeightedNilpotentLieAlgebra.lean`, `Nilpotent/NativeNilsequenceExpansion.lean`, `Polynomial/CoefficientModeDiagonalPolynomial.lean`, `Polynomial/FreeDegreeRankAdaptedBounds.lean`, `Polynomial/RaisedDegreeRank.lean`, `Polynomial/ShiftedGradedPolynomial.lean`, `Probability/CanonicalCoverLaw.lean`, `Probability/CommonSectionAmbientDensityMultiple.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B116

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

noncomputable def integerContractedRow {σ J : Type*}
    (frequency : (σ →₀ ℕ) → J → ℤ) (P : MvPolynomial σ ℤ) : J → ℤ :=
  fun j => ∑ d ∈ P.support, P.coeff d * frequency d j

theorem integerContractedRow_cast {σ J : Type*}
    (Λ : VectorPolynomial σ ℝ (J → ℝ) →ₗ[ℝ] ℝ)
    (frequency : (σ →₀ ℕ) → J → ℤ) {h : ℕ}
    (hfrequency : ∀ d : σ →₀ ℕ, d.degree = h → ∀ j,
      Λ (MvPolynomial.monomial d 1 ⊗ₜ[ℝ] Pi.single j 1) = (frequency d j : ℝ))
    {P : MvPolynomial σ ℤ} (hP : P.IsHomogeneous h) (j : J) :
    (integerContractedRow frequency P j : ℝ) = contractedRow Λ (MvPolynomial.map (Int.castRingHom ℝ) P) j := by
  change _ = ((TensorProduct.curry Λ).flip (Pi.single j 1)) (MvPolynomial.map (Int.castRingHom ℝ) P)
  rw [polynomialFunctional_map_expansion]
  simp only [integerContractedRow, Int.cast_sum, Int.cast_mul, Int.coe_castRingHom]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d.degree = h := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hP (MvPolynomial.mem_support_iff.mp hd)
  change _ = ((P.coeff d : ℤ) : ℝ) * Λ (MvPolynomial.monomial d 1 ⊗ₜ[ℝ] Pi.single j 1)
  rw [hfrequency d hdeg j]

theorem integerContractedRow_coefficientFunctional {σ J : Type*} [Fintype J]
    (frequency : (σ →₀ ℕ) → J → ℤ) {P : MvPolynomial σ ℤ} {h : ℕ}
    (hP : P.IsHomogeneous h) (j : J) :
    (integerContractedRow frequency P j : ℝ) = contractedRow
      (coefficientFunctional (fun d j => (frequency d j : ℝ)))
      (MvPolynomial.map (Int.castRingHom ℝ) P) j :=
  integerContractedRow_cast _ frequency (fun d _ j => coefficientFunctional_unit _ d j) hP j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_bounded_integer_mode_witness {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {H D C : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (frequency : ((Option K) →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ))
          (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ P : Fin h → MvPolynomial (Option K) ℤ,
      (∀ i, (P i).IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) (P i)) ≤ integerCubeWitnessBound q H D) ∧
      (∀ s : Finset (Fin q), ∃ i, eval (affineSite root difference s) (P i) = 0) ∧
      (∀ j, |(VectorPolynomial.integerContractedRow frequency (∏ i, P i) j : ℝ)| ≤
        C * integerCubeWitnessBound q H D ^ h) ∧
      ∃ w : W, (∑ j, (VectorPolynomial.integerContractedRow frequency (∏ i, P i) j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨P, hP, hz, hb, w, hw⟩ := exists_bounded_ambient_mode_witness W root difference hlin
    hH hD hC hroot hdiff (VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ)))
    h (VectorPolynomial.coefficientFunctional_rowBound _ hbound) hnonfactor
  have hp : (∏ i, P i).IsHomogeneous h := by
    simpa using IsHomogeneous.prod Finset.univ P (fun _ => 1) (fun i _ => (hP i).1)
  have hcast (j : J) := VectorPolynomial.integerContractedRow_coefficientFunctional frequency hp j
  refine ⟨P, hP, hz, ?_, w, ?_⟩
  · intro j
    rw [hcast j]
    exact hb j
  · simp_rw [hcast]
    exact hw

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem VectorPolynomial.integerContractedRow_apply {σ J : Type*} [Fintype J]
    (frequency : (σ →₀ ℕ) → J → ℤ) {P : MvPolynomial σ ℤ} {h : ℕ}
    (hP : P.IsHomogeneous h) (w : J → ℝ) :
    (∑ j, (integerContractedRow frequency P j : ℝ) * w j) =
      coefficientFunctional (fun d j => (frequency d j : ℝ))
        ((MvPolynomial.map (Int.castRingHom ℝ) P) ⊗ₜ[ℝ] w) := by
  simp_rw [integerContractedRow_coefficientFunctional frequency hP]
  exact contractedRow_apply _ _ w

namespace BooleanCubeKernel

theorem exists_bounded_integer_mode_rows {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {H D C : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (frequency : ((Option K) →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ))
          (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ integerCubeWitnessBound q H D) ∧
      (∀ s : Finset (Fin q), ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      (∀ j, |(VectorPolynomial.integerContractedRow frequency (∏ i, rowPolynomial (rows i)) j : ℝ)| ≤
        C * integerCubeWitnessBound q H D ^ h) ∧
      ∃ w : W, (∑ j, (VectorPolynomial.integerContractedRow frequency
        (∏ i, rowPolynomial (rows i)) j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨P, hP, hz, hb, hw⟩ := exists_bounded_integer_mode_witness W root difference hlin
    hH hD hC hroot hdiff frequency h hbound hnonfactor
  let rows := fun i => polynomialLinearRow (P i)
  have hp (i : Fin h) : rowPolynomial (rows i) = P i :=
    (homogeneous_eq_rowPolynomial _ (hP i).1).symm
  have hprod : (∏ i, rowPolynomial (rows i)) = ∏ i, P i := by simp_rw [hp]
  refine ⟨rows, ?_, ?_, ?_, ?_⟩
  · intro i k
    exact (integer_coefficient_le_mass (P i) (Finsupp.single k 1)).trans (hP i).2
  · intro s
    obtain ⟨i, hi⟩ := hz s
    refine ⟨i, ?_⟩
    change (∑ k, polynomialLinearRow (P i) k * affineSite root difference s k) = 0
    rw [← homogeneous_eval_eq_row _ (hP i).1]
    exact hi
  · rw [hprod]
    exact hb
  · rw [hprod]
    exact hw

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_vertex_bounded_integer_mode {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ((Option K) →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, VectorPolynomial.Homogeneous h p →
        VectorPolynomial.coefficientFunctional (fun d j => (frequency d j : ℝ))
          (VectorPolynomial.map W.subtype p) = M (VectorPolynomial.siteEvaluation
          (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ cubeModePolynomialBudget q L) ∧
      (∀ s : Finset (Fin q), ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      (∀ j, |(VectorPolynomial.integerContractedRow frequency (∏ i, rowPolynomial (rows i)) j : ℝ)| ≤
        C * cubeModePolynomialBudget q L ^ h) ∧
      ∃ w : W, (∑ j, (VectorPolynomial.integerContractedRow frequency
        (∏ i, rowPolynomial (rows i)) j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨rows, hr, hz, hb, hw⟩ := exists_bounded_integer_mode_rows W root difference hlin
    hL (show 0 ≤ 2 * L by positivity) hC
    (integer_cube_root_bound root difference hsite)
    (integer_cube_difference_bound root difference hsite) frequency h hbound hnonfactor
  have hbudget := integerCubeWitnessBound_le_vertex_budget q hL
  refine ⟨rows, (fun i k => (hr i k).trans hbudget), hz, ?_, hw⟩
  intro j
  exact (hb j).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (integerCubeWitnessBound_nonneg q hL (by positivity)) hbudget h) hC)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

theorem affineModeLift_factorization_iff {K S W : Type*} [AddCommGroup W] [Module ℝ W]
    (h : ℕ) (site : S → K → ℝ) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (M : (S → W) →ₗ[ℝ] ℝ) :
    (∀ q, Homogeneous h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ↔
    (∀ q, DegreeLE (1 : Option K → ℕ) h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) := by
  constructor
  · intro hf q hq
    have ho := (homogeneous_site_factorization_iff h site L M).mp hf
    change L (substitute dehomogenizingSubstitution q) = _
    rw [← siteEvaluation_dehomogenize]
    exact ho _ (degreeLE_dehomogenize hq)
  · intro hf q hq
    exact hf q (homogeneous_degreeLE hq)

theorem affineModeLift_exists_factorization_iff {K S W : Type*}
    [AddCommGroup W] [Module ℝ W]
    (h : ℕ) (site : S → K → ℝ) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) :
    (∃ M : (S → W) →ₗ[ℝ] ℝ, ∀ q, Homogeneous h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ↔
    (∃ M : (S → W) →ₗ[ℝ] ℝ, ∀ q, DegreeLE (1 : Option K → ℕ) h q → affineModeLift L q =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) :=
  exists_congr (fun M => affineModeLift_factorization_iff h site L M)

theorem exists_highest_affine_nonfactor {K S : Type*} {m : ℕ} {W : Fin m → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (site : S → K → ℝ) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (hbad : ∃ i, ¬∃ M : (S → W i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) q =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) :
    ∃ i, (¬∃ M : (S → W i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) q =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ∧
      ∀ j, i < j → ∃ M : (S → W j) →ₗ[ℝ] ℝ,
        ∀ q, DegreeLE (1 : Option K → ℕ) (j.val + 1) q → affineModeLift (L j) q =
          M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q) := by
  obtain ⟨i, hi, hh⟩ := exists_highest_exceptional_layer _ hbad
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact (affineModeLift_exists_factorization_iff (j.val + 1) site (L j)).mp (hh j hj)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_highest_affine_subspace_nonfactor {K S : Type*} {m : ℕ}
    {V : Fin m → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]
    (U : ∀ j, Submodule ℝ (V j)) (site : S → K → ℝ)
    (L : ∀ j, VectorPolynomial K ℝ (V j) →ₗ[ℝ] ℝ)
    (hbad : ∃ i, ¬∃ M : (S → U i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) (map (U i).subtype q) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) :
    ∃ i, (¬∃ M : (S → U i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) (map (U i).subtype q) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q)) ∧
      ∀ j, i < j → ∃ M : (S → U j) →ₗ[ℝ] ℝ,
        ∀ q, DegreeLE (1 : Option K → ℕ) (j.val + 1) q →
          affineModeLift (L j) (map (U j).subtype q) =
            M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) q) := by
  have hh := exists_highest_affine_nonfactor site (fun j => (L j).comp (map (U j).subtype))
    (by simpa only [affineModeLift_comp_map, LinearMap.comp_apply] using hbad)
  simpa only [affineModeLift_comp_map, LinearMap.comp_apply] using hh

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientModeLowerTerms
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

theorem coefficientModePolynomial_top_integer_row {I K J : Type*} [Fintype K] [Fintype J]
    {h : ℕ} (frequency : (K →₀ ℕ) → J → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous h p)
    (a : Fin h → K → ℤ) (w : I → ℝ) :
    polynomialTopSymbol h (coefficientModePolynomial
      (coefficientFunctional (fun d j => (frequency d j : ℝ))) p)
      (fun i z => (a i z.1 : ℝ) * w z.2) =
      (h.factorial : ℝ) * ∑ j,
        (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * eval w p j := by
  have hprod : (∏ i, rowPolynomial (a i)).IsHomogeneous h := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => rowPolynomial (a i))
      (fun _ => 1) (fun i _ => rowPolynomial_homogeneous (a i))
  have hmap : MvPolynomial.map (Int.castRingHom ℝ) (∏ i, rowPolynomial (a i)) =
      ∏ i, rowPolynomial (fun k => (a i k : ℝ)) := by
    simp only [map_prod, rowPolynomial_map, Int.coe_castRingHom]
  rw [coefficientModePolynomial_top_diagonal
    (coefficientFunctional (fun d j => (frequency d j : ℝ))) p hp
    (fun i k => (a i k : ℝ)) w, ← hmap, integerContractedRow_apply frequency hprod]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CoefficientModeDiagonalPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def factorialContractedRow {K J : Type*} [Fintype K] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ) : J → ℤ :=
  fun j => (h.factorial : ℤ) * integerContractedRow frequency (∏ i, rowPolynomial (a i)) j

theorem factorialContractedRow_eval {I K J : Type*} [Fintype K] [Fintype J] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (w : I → ℝ) :
    MvPolynomial.eval w (integerRowPolynomial (factorialContractedRow frequency a) p) =
      (h.factorial : ℝ) * ∑ j,
        (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * eval w p j := by
  simp [integerRowPolynomial_eval, factorialContractedRow, Finset.mul_sum, mul_assoc]

theorem coefficientMode_diagonal_polynomial {I K J : Type*} [Fintype K] [Fintype J] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous h p) (w : I → ℝ) :
    MvPolynomial.eval w (integerRowPolynomial (factorialContractedRow frequency a) p) =
      polynomialTopSymbol h (coefficientModePolynomial
        (coefficientFunctional (fun d j => (frequency d j : ℝ))) p)
        (fun i z => (a i z.1 : ℝ) * w z.2) := by
  rw [factorialContractedRow_eval]
  exact (coefficientModePolynomial_top_integer_row frequency p hp a w).symm

theorem factorialContractedRow_bound {K J : Type*} [Fintype K] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ) {B : ℝ}
    (hb : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B) :
    ∀ j, |(factorialContractedRow frequency a j : ℝ)| ≤ (h.factorial : ℝ) * B := by
  intro j
  simpa only [factorialContractedRow, Int.cast_mul, Int.cast_natCast, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg h.factorial : (0 : ℝ) ≤ _)] using
    mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg h.factorial : (0 : ℝ) ≤ _)

theorem factorialContractedRow_nonzero {K J : Type*} [Fintype K] [Fintype J] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ) (w : J → ℝ)
    (hw : (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w j) ≠ 0) :
    (∑ j, (factorialContractedRow frequency a j : ℝ) * w j) ≠ 0 := by
  have he : (∑ j, (factorialContractedRow frequency a j : ℝ) * w j) =
      (h.factorial : ℝ) * ∑ j,
        (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w j := by
    simp [factorialContractedRow, Finset.mul_sum, mul_assoc]
  rw [he]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h)) hw

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientModeRationalDecomposition
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators Classical

theorem coefficientMode_integer_row_decomposition {I K J : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype J] {n : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin (n + 1) → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous (n + 1) p)
    (N s : I → ℕ) (hs : ∀ k, 0 < s k) {ζ : ℝ} (hζ : 0 < ζ)
    (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((s k : ℝ) * (N k : ℝ)))
    (hbias : ζ ≤ ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((polynomialTopSymbol (n + 1) (coefficientModePolynomial
          (coefficientFunctional (fun d j => (frequency d j : ℝ))) p)
          (fun i z => (a i z.1 : ℝ) *
            ((s z.2 : ℝ) * ((x i z.2).val : ℝ) - (s z.2 : ℝ) * ((y i z.2).val : ℝ))) : ℝ) :
              CircleFourier.Circle)‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ ∏ j : Fin (n + 1) → I, (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ)) ∧
      ∃ E : MvPolynomial I ℝ, ∃ Q : MvPolynomial I ℤ,
        integerRowPolynomial (factorialContractedRow frequency a) p =
          E + MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q ∧
        ∀ α, |E.coeff α| ≤ (Fintype.card I : ℝ) ^ (n + 1) *
          (A ^ (n + 1) * multiaffineBiasBudget n ζ) / monomialScale H α := by
  let P := coefficientModePolynomial (coefficientFunctional (fun d j => (frequency d j : ℝ))) p
  let F := rowTopSymbolMultilinear (n + 1) P (coefficientModePolynomial_degree _ p hp)
    (fun i k => (a i k : ℝ))
  have hdiag (w : I → ℝ) :
      MvPolynomial.eval w (integerRowPolynomial (factorialContractedRow frequency a) p) =
        F (fun _ => w) := by
    simpa only [F, P, rowTopSymbolMultilinear_apply] using
      coefficientMode_diagonal_polynomial frequency a p hp w
  apply paired_multilinear_polynomial_approximation F
    (integerRowPolynomial (factorialContractedRow frequency a) p) hdiag N s hs hζ hN H hH hA hscale
  simpa only [F, P, rowTopSymbolMultilinear_apply] using hbias

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientTopSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem quotientTopSymbolMap_surjective : Function.Surjective (F.quotientTopSymbolMap w) :=
  F.filteredPolynomialSymbolMap_surjective _ _ _ w (fun _ _ hy => hy)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualLogarithmicDifferential
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogarithmicDifferential_smul_real [LieAlgebra ℝ L] (x y : L) (r : ℝ) :
    dualLogarithmicDifferential (hnil := hnil) x (r • y) =
      r • dualLogarithmicDifferential (hnil := hnil) x y := by
  let T : L →ₗ[ℚ] L := r • LinearMap.id
  have hT : ∀ a b : L, b ∈ (⊤ : LieIdeal ℚ L) →
      T ⁅a, b⁆ = ⁅(LieHom.id : L →ₗ⁅ℚ⁆ L) a, T b⁆ := by
    intro a b _
    change r • ⁅a, b⁆ = ⁅a, r • b⁆
    exact (lie_smul r a b).symm
  have he := dualLinearLift_logDerivative_eq (hL := hnil) hnil ⊤ LieHom.id T hT
    (⟨dualConstantLie x + dualInfinitesimal y⟩ : DualGroup hnil) (by trivial)
    (⟨dualConstantLie x + dualInfinitesimal (r • y)⟩ : DualGroup hnil)
    (by simp only [map_add, dualLinearLift_constant, dualLinearLift_infinitesimal]; rfl)
  exact he.symm

noncomputable def dualRealLogarithmicDifferential [LieAlgebra ℝ L] (x : L) : L →ₗ[ℝ] L where
  toFun := dualLogarithmicDifferential (hnil := hnil) x
  map_add' := (dualLogarithmicDifferential x).map_add
  map_smul' r y := dualLogarithmicDifferential_smul_real x y r

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AssociatedGradedBasisIndependence
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem gradedPieceProjection_coordinate (j : ℕ) (v : L) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.gradedPieceProjection b ω hlayers j v) i =
      if ω i = j then b.repr v i else 0 := by
  simp only [gradedPieceProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, basisGradeProjection_repr]

theorem gradedPieceProjection_eq_pieceMap (j : ℕ) (v : F.layer j) :
    F.gradedPieceProjection b ω hlayers j v = F.associatedGradedPieceMap j v := by
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [F.gradedPieceProjection_coordinate, F.associatedGradedPieceMap_coordinate]
  simp only [eq_comm]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedGradedPolynomial
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem shiftedGradedPolynomial_coefficient_of_mem (k : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w k) (α : σ →₀ ℕ) :
    coefficients (F.shiftedGradedPolynomial b ω hlayers w k p) α =
      F.associatedGradedPieceMap (Finsupp.weight w α + k) ⟨coefficients p α, hp α⟩ := by
  rw [F.shiftedGradedPolynomial_coefficient]
  exact F.gradedPieceProjection_eq_pieceMap b ω hlayers (Finsupp.weight w α + k)
    ⟨coefficients p α, hp α⟩

theorem shiftedGradedPolynomial_eq_zero_iff (k : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w k) :
    F.shiftedGradedPolynomial b ω hlayers w k p = 0 ↔
      p ∈ F.shiftedAdaptedSubmodule w (k + 1) := by
  constructor
  · intro hz α
    have hc := congrArg (fun q : VectorPolynomial σ ℚ F.AssociatedGraded => coefficients q α) hz
    rw [F.shiftedGradedPolynomial_coefficient_of_mem b ω hlayers w k hp,
      map_zero, Finsupp.zero_apply] at hc
    have hh := (F.associatedGradedPieceMap_eq_zero_iff _ _).mp hc
    simpa only [Nat.add_assoc] using hh
  · intro hp'
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [F.shiftedGradedPolynomial_coefficient_of_mem b ω hlayers w k hp, map_zero, Finsupp.zero_apply]
    apply (F.associatedGradedPieceMap_eq_zero_iff _ _).mpr
    simpa only [Nat.add_assoc] using hp' α

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedGradedCalculus
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedDirectionalTangent
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (σ → ℚ) →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1) where
  toFun h := F.adaptedDirectionalDerivative h p
  map_add' h k := Subtype.ext (directionalDerivative_direction_add h k p.val)
  map_smul' r h := Subtype.ext (directionalDerivative_direction_smul r h p.val)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedSquareSymbol
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

variable (F : NilpotentLieFiltration L (s + 1))

noncomputable def quotientTopGradedMap : F.AssociatedGraded →ₗ⁅ℚ⁆ F.quotientTop.AssociatedGraded :=
  F.quotientGradedMap (F.layerIdeal (s + 1)) le_rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem squareBasis_repr_inl (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2))
    (x : F.squareLieSubalgebra) (i : ι) :
    (F.squareBasis b c).repr x (Sum.inl i) = b.repr x.val.2 i := by
  simp [squareBasis, Basis.map_repr, squareCoordinates]

theorem squareBasis_repr_inr (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2))
    (x : F.squareLieSubalgebra) (i : κ) :
    (F.squareBasis b c).repr x (Sum.inr i) =
      c.repr ⟨x.val.1 - x.val.2, (F.mem_squareLieSubalgebra x.val).mp x.property⟩ i := by
  simp [squareBasis, Basis.map_repr, squareCoordinates]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem mem_squareLayer_iff_second_and_difference (j : ℕ) (x : L × L) :
    x ∈ F.squareLayer j ↔ x.2 ∈ F.layer j ∧ x.1 - x.2 ∈ F.layer (j + 1) := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h.1, h.2⟩
    have hx := (F.layer j).add_mem (F.antitone (Nat.le_succ j) h.2) h.1
    simpa only [sub_add_cancel] using hx

theorem adaptedSquareBasis_layers (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (j : ℕ) :
    F.squareFiltration.layer j = Submodule.span ℚ
      (F.adaptedSquareBasis b w (hlayers 2) '' {i | j ≤ squareBasisWeight w i}) := by
  have hmem (k : ℕ) (x : L) : x ∈ F.layer k ↔ ∀ i, ¬ k ≤ w i → b.repr x i = 0 := by
    rw [hlayers k, basis_mem_span_image_iff]
    rfl
  ext x
  rw [F.mem_squareFiltration_layer, F.mem_squareLayer_iff_second_and_difference,
    basis_mem_span_image_iff, hmem, hmem]
  constructor
  · rintro ⟨hy, hz⟩ i hi
    cases i with
    | inl i =>
      change (F.squareBasis b _).repr x (Sum.inl i) = 0
      rw [F.squareBasis_repr_inl]
      exact hy i hi
    | inr i =>
      change (F.squareBasis b _).repr x (Sum.inr i) = 0
      rw [F.squareBasis_repr_inr, supportedSubmoduleBasis_repr]
      exact hz i (by change ¬ j ≤ w i - 1 at hi; have := i.property; omega)
  · intro hx
    constructor
    · intro i hi
      have hh := hx (Sum.inl i) hi
      change (F.squareBasis b _).repr x (Sum.inl i) = 0 at hh
      simpa only [F.squareBasis_repr_inl] using hh
    · intro i hi
      by_cases h2 : 2 ≤ w i
      · have hsmall : ¬ j ≤ squareBasisWeight w (Sum.inr (⟨i, h2⟩ : {i // 2 ≤ w i})) := by
          change ¬ j ≤ w i - 1
          omega
        have hh := hx (Sum.inr ⟨i, h2⟩) hsmall
        change (F.squareBasis b _).repr x
          (Sum.inr (⟨i, h2⟩ : {i // 2 ≤ w i})) = 0 at hh
        rw [F.squareBasis_repr_inr] at hh
        exact (supportedSubmoduleBasis_repr b (F.layer 2) {i | 2 ≤ w i}
          (hlayers 2) _ (⟨i, h2⟩ : {i // 2 ≤ w i})).symm.trans hh
      · exact (hmem 2 (x.val.1 - x.val.2)).mp
          ((F.mem_squareLieSubalgebra x.val).mp x.property) i h2

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem quotientTopBasis_layers (j : ℕ) :
    F.quotientTop.layer j = Submodule.span ℚ
      (F.quotientTopBasis e ω hF '' {i | j ≤ ω i.val}) :=
  F.supportedQuotientBasis_layers e ω hF (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ ω i} (hF (s + 1)) j

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

theorem reducedSquareDiagonalPolynomialMap_quotient (p : F.adaptedLieSubalgebra w) :
    F.reducedSquareDiagonalPolynomialMap w (F.quotientTopPolynomialMap w p) =
      F.reducedSquarePolynomialMap w (F.squareDiagonalPolynomialMap w p) := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  change coefficients (VectorPolynomial.map F.reducedSquareDiagonal.toLinearMap
      (VectorPolynomial.map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap p.val)) α =
    coefficients (VectorPolynomial.map (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap
      (VectorPolynomial.map F.squareDiagonalLie.toLinearMap p.val)) α
  simp only [coefficients_map]
  rfl

theorem reducedSquareDiagonalSymbolMap_quotient (x : F.PolynomialSymbol w) :
    F.reducedSquareDiagonalSymbolMap w (F.quotientTopSymbolMap w x) =
      F.reducedSquareSymbolMap w (F.squareDiagonalSymbolMap w x) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.quotientTopSymbolMap_symbol, F.reducedSquareDiagonalSymbolMap_symbol,
    F.squareDiagonalSymbolMap_symbol, F.reducedSquareSymbolMap_symbol,
    F.reducedSquareDiagonalPolynomialMap_quotient]

theorem reducedSquareSymbolMap_surjective : Function.Surjective (F.reducedSquareSymbolMap w) :=
  F.squareFiltration.quotientTopSymbolMap_surjective w

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev ReducedSquareBasisIndex (s : ℕ) (ω : ι → ℕ) :=
  QuotientTopBasisIndex s (squareBasisWeight ω)

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def reducedSquareBasis :
    Basis (ReducedSquareBasisIndex s ω) ℚ
      (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :=
  F.squareFiltration.quotientTopBasis (F.adaptedSquareBasis e ω (hF 2))
    (squareBasisWeight ω) (F.adaptedSquareBasis_layers e ω hF)

theorem reducedSquareBasis_layers (j : ℕ) :
    F.squareFiltration.quotientTop.layer j = Submodule.span ℚ
      (F.reducedSquareBasis e ω hF '' {i | j ≤ squareBasisWeight ω i.val}) :=
  F.squareFiltration.quotientTopBasis_layers (F.adaptedSquareBasis e ω (hF 2))
    (squareBasisWeight ω) (F.adaptedSquareBasis_layers e ω hF) j

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastCoefficientImage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev FirstCoefficientIndex (w : σ → ℕ) (ω : ι → ℕ) :=
  {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 + 1 = ω z.2}

def firstCoefficientSurvivorEquiv (w : σ → ℕ) (ω : ι → ℕ) :
    {z : ShiftedMonomialIndex w ω 1 //
      ¬ Finsupp.weight w z.val.val.1 + 2 ≤ ω z.val.val.2} ≃ FirstCoefficientIndex w ω where
  toFun z := ⟨z.val.val.val, by
    have h : Finsupp.weight w z.val.val.val.1 + 1 ≤ ω z.val.val.val.2 := z.val.property
    have hn : ¬ Finsupp.weight w z.val.val.val.1 + 2 ≤ ω z.val.val.val.2 := z.property
    omega⟩
  invFun z := ⟨⟨⟨z.val, by have h := z.property; omega⟩, z.property.le⟩, by
    change ¬ Finsupp.weight w z.val.1 + 2 ≤ ω z.val.2
    have h := z.property
    omega⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

end Erdos3.NilpotentLieFiltration

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

theorem of_mem_layer (hw : ∀ i, 0 < w i) (x : X) :
    of X s w x ∈ (filtration X s w hw).layer (w x) :=
  ⟨FreeNilpotentLieAlgebra.of X s x,
    weightedLieUpperSpan_leaf (FreeNilpotentLieAlgebra.of X s) w x, rfl⟩

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeWeightedEvaluationBounds
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : X → ℕ) (f : X → L)
  (hf : ∀ x, f x ∈ F.layer (w x))

namespace FreeWeightedNilpotentLieAlgebra

theorem lift_mem_layer (hw : ∀ i, 0 < w i) {d : ℕ} {x : FreeWeightedNilpotentLieAlgebra X s w}
    (hx : x ∈ (filtration X s w hw).layer d) : lift F w f hf x ∈ F.layer d := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact FreeNilpotentLieAlgebra.lift_weightedLayer F w f hf ha

end FreeWeightedNilpotentLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3.NilpotentLieFiltration

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

theorem piRealOrbit_eval (p : ∀ i, (F i).realification.PolynomialOrbit w)
    (x : σ → ℤ) (i : ι) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (pi F).lowerCentralSeries_eq_bot) (hM := (F i).lowerCentralSeries_eq_bot) (liePiEval i)
      ((pi F).realification.polynomialOrbitEval w x (piRealOrbit F p)) =
        (F i).realification.polynomialOrbitEval w x (p i) := by
  classical
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieBCHGroup.realificationMap_coord, polynomialOrbitEval_coord,
    piRealOrbit, polynomialOrbitOfLog_log, map_sum, VectorPolynomial.eval_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

open Module
open scoped BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productLayerBasis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hD : ∀ i, (D i).GeometryComplexityLE p) (j : Fin (s + 1))
    (k : Σ i, Fin (finrank ℚ ((D i).filtration.layer (j.val + 1)))) (l : Σ i, Fin (d i)) :
    rationalLogHeight ((Pi.basis (fun i => (D i).basis)).repr ((productLayerBasis D j k).val) l) ≤ p := by
  classical
  rcases k with ⟨a, k⟩
  rcases l with ⟨b, l⟩
  simp only [productLayerBasis, Basis.map_apply, Pi.basis_repr]
  change rationalLogHeight ((D b).basis.repr
    (((Pi.basis (fun i => (D i).layerBasis j)) ⟨a, k⟩ b).val) l) ≤ p
  rw [Pi.basis_apply]
  by_cases hab : a = b
  · subst b
    rw [Pi.single_eq_same]
    exact (hD a).2.2.2 j k l
  · rw [Pi.single_eq_of_ne (Ne.symm hab)]
    simpa [rationalLogHeight] using hp

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeNilsequenceExpansion
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

namespace NativeNilsequenceExpansion

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}

noncomputable def mono (E : NativeNilsequenceExpansion s N p f) (hpq : p ≤ q) :
    NativeNilsequenceExpansion s N q f :=
  { E with
    count_bound := E.count_bound.trans (Real.exp_le_exp.mpr hpq)
    complexity := fun i => (E.complexity i).mono hpq
    cost := E.cost.trans (Real.exp_le_exp.mpr hpq) }

noncomputable def conjugate (E : NativeNilsequenceExpansion s N p f) :
    NativeNilsequenceExpansion s N p (fun x => star (f x)) :=
  { E with
    test := fun i => (E.test i).conjugate
    complexity := E.complexity
    coefficient := fun i => star (E.coefficient i)
    cost := by simpa only [norm_star] using E.cost
    eval := by
      intro x
      have h := congrArg star (E.eval x)
      simpa only [star_sum, star_mul, mul_comm, RationalFilteredNilmanifold.Niltest.evalCyclic,
        RationalFilteredNilmanifold.Niltest.eval_conjugate] using h }

end NativeNilsequenceExpansion

structure NativeVectorEquivalence {J K : Type*} [Fintype J] [Fintype K]
    (s N : ℕ) [NeZero N] (p : ℝ) (chi : J → ZMod N → ℂ) (chi' : K → ZMod N → ℂ) : Prop where
  left_dimension : (Fintype.card J : ℝ) ≤ Real.exp p
  right_dimension : (Fintype.card K : ℝ) ≤ Real.exp p
  expansion : ∀ j k, Nonempty (NativeNilsequenceExpansion s N p
    (fun x => chi j x * star (chi' k x)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeEquivalenceTransitivity
namespace OAI

section

namespace Erdos3.NativeVectorEquivalence

variable {J K : Type*} [Fintype J] [Fintype K] {s N : ℕ} [NeZero N] {p q : ℝ}
  {chi : J → ZMod N → ℂ} {chi' : K → ZMod N → ℂ}

theorem symm (E : NativeVectorEquivalence s N p chi chi') :
    NativeVectorEquivalence s N p chi' chi where
  left_dimension := E.right_dimension
  right_dimension := E.left_dimension
  expansion k j := by
    obtain ⟨R⟩ := E.expansion j k
    have h : Nonempty (NativeNilsequenceExpansion s N p
        (fun x => star (chi j x * star (chi' k x)))) := ⟨R.conjugate⟩
    simpa only [star_mul, star_star, mul_comm] using h

end Erdos3.NativeVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareRationalModel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def squareFinBasis (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) :
    Basis (Fin (Fintype.card (ι ⊕ {i // 2 ≤ w i}))) ℚ F.squareLieSubalgebra :=
  (F.adaptedSquareBasis b w h).reindex (Fintype.equivFin _)

theorem squareFinBasis_layers (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (j : ℕ) :
    F.squareFiltration.layer j = Submodule.span ℚ
      (F.squareFinBasis b w (hlayers 2) '' {i | j ≤ squareFinWeight w i}) := by
  rw [F.adaptedSquareBasis_layers b w hlayers j]
  exact (basis_reindex_span_weights _ _ _ _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.HomogeneousGradedProjectionFrequency
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedFrequency (η : L →ₗ[ℚ] ℚ) : F.AssociatedGraded →ₗ[ℚ] ℚ :=
  η.comp (b.repr.symm.toLinearMap.comp (F.associatedGradedBasis b ω hF).repr.toLinearMap)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolFastMembership
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def ControlledSymbolFactorization (η : L →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) : Prop :=
  ∃ (m : ℕ) (E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : ι → F.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ E * P * R = X ∧
    F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
    F.SymbolRationalGrid b ω hF (fun _ => 1) m R ∧
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule ∧
    (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v i) j) ≤ p) ∧
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0) ∧
    P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def SymbolFactorizationIn (T : σ → ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded) : Prop :=
  ∃ E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
    E * P * R = X ∧ F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
    F.SymbolRationalGrid b ω hF (fun _ => 1) l R ∧
    P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def SymbolFastIn {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (g : F.RealPolynomialSymbolGroup w) : Prop :=
  g.coord ∈ realificationLieSubalgebra U

end Erdos3.NilpotentLieFiltration

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

theorem rationalDirectionPeriod_mem_lattice (v : L) :
    (⟨(D.rationalDirectionPeriod v : ℚ) • v⟩ : D.filtration.Group) ∈ D.lattice := by
  have hc : D.basis.equivFun ((D.rationalDirectionPeriod v : ℚ) • v) ∈
      scaledIntegerGrid D.grid := by
    refine ⟨clearedArray (D.basis.equivFun v), ?_⟩
    rw [map_smul]
    ext i
    change (D.rationalDirectionPeriod v : ℚ) * D.basis.equivFun v i =
      (D.grid : ℚ) * (clearedArray (D.basis.equivFun v) i : ℚ)
    rw [clearedArray_cast]
    simp only [rationalDirectionPeriod, Nat.cast_mul, mul_assoc]
  have h := D.inner_grid hc
  change (⟨D.basis.equivFun.symm (D.basis.equivFun
    ((D.rationalDirectionPeriod v : ℚ) • v))⟩ : D.filtration.Group) ∈ D.lattice at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem periodicRealDirection_mem_lattice (v : L) :
    (⟨D.periodicRealDirection v⟩ : D.RealGroup) ∈ D.realLattice := by
  exact Subgroup.mem_map.mpr ⟨⟨(D.rationalDirectionPeriod v : ℚ) • v⟩,
    D.rationalDirectionPeriod_mem_lattice v, rfl⟩

theorem periodicRealDirection_central (v : L) (hv : v ∈ D.filtration.layer s)
    (w : ℝ ⊗[ℚ] L) : ⁅D.periodicRealDirection v, w⁆ = 0 := by
  rw [D.periodicRealDirection_eq, smul_lie,
    rationalLieInclusion_central v (D.filtration.top_layer_central hv), smul_zero]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def centralRationalCircle (v : L) (hv : v ∈ D.filtration.layer s) :
    let := D.metricSpace
    IsometricCircleAction D.Space := by
  let := D.metricSpace
  exact centralBCHCircleAction (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 (D.periodicRealDirection v)
    (D.periodicRealDirection_central v hv) (D.periodicRealDirection_mem_lattice v)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FreeDegreeRankAdaptedBounds
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def quotientLie (I : LieIdeal ℚ L) {t : ℕ} (ht : t ≤ s)
    (hI : F.layer s (t + 1) ≤ I.toSubmodule) : DegreeRankLieFiltration (L ⧸ I) s t where
  rank_le_degree := ht
  layer d i := (F.layer d i).map (lieQuotientMap I).toLinearMap
  lex_antitone := fun h => Submodule.map_mono (F.lex_antitone h)
  one_eq_top := by
    rw [F.one_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective I)
  rank_zero_eq_one := fun d => congrArg (Submodule.map (lieQuotientMap I).toLinearMap)
    (F.rank_zero_eq_one d)
  overshoot := fun d i h => congrArg (Submodule.map (lieQuotientMap I).toLinearMap)
    (F.overshoot d i h)
  lie_mem := by
    rintro d e i j x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨⁅a, b⁆, F.lie_mem ha hb, (lieQuotientMap I).map_lie a b⟩
  terminal := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (lieQuotientMap_eq_zero I a).mpr (hI ha)

def quotientRank (t : ℕ) (ht : t ≤ s) :
    DegreeRankLieFiltration (L ⧸ F.layerIdeal s (t + 1)) s t :=
  F.quotientLie (F.layerIdeal s (t + 1)) ht le_rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

def FreeDegreeRankLieAlgebra (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x) :=
  FreeWeightedNilpotentLieAlgebra X s w ⧸
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)

namespace FreeDegreeRankLieAlgebra

variable (X : Type*) (s r : ℕ) (w : X → ℕ) (hw : ∀ x, 0 < w x)

noncomputable instance instLieRing : LieRing (FreeDegreeRankLieAlgebra X s r w hw) :=
  inferInstanceAs (LieRing (FreeWeightedNilpotentLieAlgebra X s w ⧸
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)))

noncomputable instance instLieAlgebra : LieAlgebra ℚ (FreeDegreeRankLieAlgebra X s r w hw) :=
  inferInstanceAs (LieAlgebra ℚ (FreeWeightedNilpotentLieAlgebra X s w ⧸
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1)))

noncomputable def mk : FreeWeightedNilpotentLieAlgebra X s w →ₗ⁅ℚ⁆ FreeDegreeRankLieAlgebra X s r w hw :=
  lieQuotientMap ((FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1))

noncomputable def of (x : X) : FreeDegreeRankLieAlgebra X s r w hw :=
  mk X s r w hw (FreeWeightedNilpotentLieAlgebra.of X s w x)

noncomputable def filtration (hr : r ≤ s) : DegreeRankLieFiltration (FreeDegreeRankLieAlgebra X s r w hw) s r :=
  (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.quotientRank r hr

theorem of_mem_layer (hr : r ≤ s) (x : X) :
    of X s r w hw x ∈ (filtration X s r w hw hr).layer (w x) 1 := by
  refine ⟨FreeWeightedNilpotentLieAlgebra.of X s w x, ?_, rfl⟩
  change FreeWeightedNilpotentLieAlgebra.of X s w x ∈
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).rankLayer (w x) 1
  rw [NilpotentLieFiltration.rankLayer_one]
  exact FreeWeightedNilpotentLieAlgebra.of_mem_layer X s w hw x

end FreeDegreeRankLieAlgebra

end Erdos3

end

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (G : DegreeRankLieFiltration L s r) (w : X → ℕ) (hw : ∀ x, 0 < w x)
  (f : X → L) (hf : ∀ x, f x ∈ G.layer (w x) 0)

theorem FreeWeightedNilpotentLieAlgebra.lift_mem_degreeRank {d i : ℕ}
    {x : FreeWeightedNilpotentLieAlgebra X s w}
    (hx : x ∈ (FreeWeightedNilpotentLieAlgebra.filtration X s w hw).rankLayer d i) :
    FreeWeightedNilpotentLieAlgebra.lift G.associatedDegree w f hf x ∈ G.layer d i := by
  apply NilpotentLieFiltration.map_rankLayer
    (FreeWeightedNilpotentLieAlgebra.filtration X s w hw) G
    (FreeWeightedNilpotentLieAlgebra.lift G.associatedDegree w f hf) ?_ hx
  intro d x hx
  exact FreeWeightedNilpotentLieAlgebra.lift_mem_layer G.associatedDegree w f hf hw hx

namespace FreeDegreeRankLieAlgebra

noncomputable def lift : FreeDegreeRankLieAlgebra X s r w hw →ₗ⁅ℚ⁆ L :=
  lieQuotientDescend
    ((FreeWeightedNilpotentLieAlgebra.filtration X s w hw).canonicalDegreeRank.layerIdeal s (r + 1))
    (FreeWeightedNilpotentLieAlgebra.lift G.associatedDegree w f hf)
    (fun x hx => by
      have h := FreeWeightedNilpotentLieAlgebra.lift_mem_degreeRank G w hw f hf hx
      simpa only [G.terminal, Submodule.mem_bot] using h)

@[simp] theorem lift_of (x : X) : lift G w hw f hf (of X s r w hw x) = f x :=
  FreeWeightedNilpotentLieAlgebra.lift_of G.associatedDegree w f hf x

end FreeDegreeRankLieAlgebra

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open Module

theorem basis_equivFun_symm (d : ℕ) (x : Fin d → ℚ) : (basis d).equivFun.symm x = x := by
  have h := basis_equivFun d ((basis d).equivFun.symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end Erdos3.RationalTorus

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CoefficientModeRankContradiction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators Classical

theorem coefficientMode_paired_bias_lt_of_rank {I K J : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype J] {n : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin (n + 1) → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous (n + 1) p)
    (W : Submodule ℝ (J → ℝ)) (N s : I → ℕ) (hs : ∀ k, 0 < s k)
    {ζ R B : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((s k : ℝ) * (N k : ℝ)))
    (hrank : HasLayerSamplingRank (n + 1) H R W p)
    (hrow : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B)
    (hrowBudget : ((n + 1).factorial : ℝ) * B ≤ R)
    (hnonzero : ∃ w : W,
      (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w.val j) ≠ 0)
    (hdenom : (∏ j : Fin (n + 1) → I,
      (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ))) ≤ R)
    (hcoeff : (Fintype.card I : ℝ) ^ (n + 1) * (A ^ (n + 1) * multiaffineBiasBudget n ζ) ≤ R) :
    ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      𝔼 y : Fin (n + 1) → ∀ k, Fin (N k),
        character ((polynomialTopSymbol (n + 1) (coefficientModePolynomial
          (coefficientFunctional (fun d j => (frequency d j : ℝ))) p)
          (fun i z => (a i z.1 : ℝ) *
            ((s z.2 : ℝ) * ((x i z.2).val : ℝ) - (s z.2 : ℝ) * ((y i z.2).val : ℝ))) : ℝ) :
              CircleFourier.Circle)‖ < ζ := by
  by_contra hn
  obtain ⟨D, hD, hDb, E, Q, heq, he⟩ := coefficientMode_integer_row_decomposition
    frequency a p hp N s hs hζ hN H hH hA hscale (le_of_not_gt hn)
  have ha (j : J) : |(factorialContractedRow frequency a j : ℝ)| ≤ R :=
    (factorialContractedRow_bound frequency a hrow j).trans hrowBudget
  obtain ⟨w, hw⟩ := hnonzero
  apply hrank.not_approximation hp (factorialContractedRow frequency a) ha
    ⟨w, factorialContractedRow_nonzero frequency a w.val hw⟩
  apply polynomialRationalApproximation_of_decomposition _ R _ E Q D hD
    (hDb.trans hdenom) heq
  intro α
  exact (he α).trans (div_le_div_of_nonneg_right hcoeff (monomialScale_pos _ hH α).le)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SubspaceLayeredModeSmoothRemoval
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators Classical

theorem coefficient_mode_finite_removal {I K J S : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype J] [Fintype S] {n : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin (n + 1) → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous (n + 1) p)
    (W : Submodule ℝ (J → ℝ)) (N s : I → ℕ) (hs : ∀ k, 0 < s k)
    {ζ R B : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((s k : ℝ) * (N k : ℝ)))
    (hrank : HasLayerSamplingRank (n + 1) H R W p)
    (hrow : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B)
    (hrowBudget : ((n + 1).factorial : ℝ) * B ≤ R)
    (hnonzero : ∃ w : W,
      (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w.val j) ≠ 0)
    (hdenom : (∏ j : Fin (n + 1) → I,
      (multiaffineBiasBudget n ζ * ∏ i, (s (j i) : ℝ))) ≤ R)
    (hcoeff : (Fintype.card I : ℝ) ^ (n + 1) * (A ^ (n + 1) * multiaffineBiasBudget n ζ) ≤ R)
    (site : S → K → ℤ) (hzero : ∀ t, ∃ i, (∑ k, a i k * site t k) = 0)
    (base : K → I → ℝ) (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < n + 1)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1) :
    let shift : (∀ k, Fin (N k)) → I → ℝ := fun x k => (s k : ℝ) * ((x k).val : ℝ)
    let L := coefficientFunctional (fun d j => (frequency d j : ℝ))
    ‖𝔼 x : Fin (n + 1) → ∀ k, Fin (N k),
      character ((L (substitute (fun j => rowPolynomial
        (fun k => rowShiftedTuple base a shift x k j)) p) +
        MvPolynomial.eval (fun z => rowShiftedTuple base a shift x z.1 z.2) Q : ℝ) :
          CircleFourier.Circle) *
      ∏ t, test t (integerSiteValue (site t) (rowShiftedTuple base a shift x))‖ ^ (2 ^ (n + 1)) < ζ := by
  have hNp (k : I) : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos n hζ).trans_le (hN k)
  let : ∀ k, Nonempty (Fin (N k)) := fun k => ⟨⟨0, hNp k⟩⟩
  have hcs := coefficient_mode_with_lower_site_cauchySchwarz (Nat.succ_pos n) site a hzero base
    (fun (x : ∀ k, Fin (N k)) k => (s k : ℝ) * ((x k).val : ℝ))
    (coefficientFunctional (fun d j => (frequency d j : ℝ))) p hp Q hQ test htest
  exact hcs.trans_lt (coefficientMode_paired_bias_lt_of_rank frequency a p hp W N s hs hζ hN
    H hH hA hscale hrank hrow hrowBudget hnonzero hdenom hcoeff)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem inhomogeneous_coefficient_mode_local_removal {I K J T : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Fintype J] [Fintype T] {n : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin (n + 1) → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : DegreeLE (1 : I → ℕ) (n + 1) p)
    (W : Submodule ℝ (J → ℝ)) (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R B : ℝ} (hζ : 0 < ζ) (hN : ∀ k, multiaffineBiasBudget n ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : HasLayerSamplingRank (n + 1) H R W p)
    (hrow : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B)
    (hrowBudget : ((n + 1).factorial : ℝ) * B ≤ R)
    (hnonzero : ∃ w : W,
      (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w.val j) ≠ 0)
    (hdenom : (∏ j : Fin (n + 1) → I,
      (multiaffineBiasBudget n ζ * ∏ i, (stride (j i) : ℝ))) ≤ R)
    (hcoeff : (Fintype.card I : ℝ) ^ (n + 1) * (A ^ (n + 1) * multiaffineBiasBudget n ζ) ≤ R)
    (site : T → K → ℤ) (hzero : ∀ t, ∃ i, (∑ k, a i k * site t k) = 0)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < n + 1)
    (test : T → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    {β : ℝ} (hβ : 0 ≤ β) (hpower : ζ ≤ β ^ (2 ^ (n + 1)))
    (base : K → I → ℝ) :
    ‖𝔼 x : Fin (n + 1) → ∀ j, Fin (N j),
      coefficientModeTestedPhase (coefficientFunctional (fun d j => (frequency d j : ℝ)))
        p Q site test (rowShiftedTuple base a
          (fun (y : ∀ j, Fin (N j)) j => (stride j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ β := by
  have he (b : K → I → ℝ) := coefficientModeTestedPhase_top
    (coefficientFunctional (fun d j => (frequency d j : ℝ))) (n + 1) p Q site test b
  simp_rw [he]
  apply le_of_pow_le_pow_left₀ (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hβ
  exact (coefficient_mode_finite_removal frequency a (homogeneousPart (n + 1) p)
    (homogeneousPart_homogeneous _ _) W N stride hs hζ hN H hH hA hscale
    ((hasLayerSamplingRank_homogeneousPart_iff _ _ _ _ _).mpr hrank)
    hrow hrowBudget hnonzero hdenom hcoeff site hzero base
    (lowerModePolynomial _ (n + 1) p Q) (lowerModePolynomial_degree _ p hp Q hQ)
    test htest).le.trans hpower

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientResidueWidths
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem integerContractedRow_monomial {K J : Type*}
    (frequency : (K →₀ ℕ) → J → ℤ) (d : K →₀ ℕ) (j : J) :
    integerContractedRow frequency (MvPolynomial.monomial d 1) j = frequency d j := by
  simp [integerContractedRow]

theorem exists_unit_integer_mode_rows {K J : Type*} [Fintype K] [Fintype J]
    (W : Submodule ℝ (J → ℝ)) (frequency : (K →₀ ℕ) → J → ℤ) {h : ℕ} {C : ℝ}
    (hbound : ∀ d, d.degree = h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonzero : ∃ p, Homogeneous h p ∧
      coefficientFunctional (fun d j => (frequency d j : ℝ)) (map W.subtype p) ≠ 0) :
    ∃ rows : Fin h → K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ 1) ∧
      (∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (rows i)) j : ℝ)| ≤ C) ∧
      ∃ w : W, (∑ j, (integerContractedRow frequency
        (∏ i, rowPolynomial (rows i)) j : ℝ) * w.val j) ≠ 0 := by
  obtain ⟨d, hd, w, hw⟩ := exists_restricted_coefficient_nonzero W frequency hnonzero
  obtain ⟨rows, hrows, hprod⟩ := exists_monomial_coordinate_rows d hd
  refine ⟨rows, hrows, ?_, ?_⟩
  · simpa only [hprod, integerContractedRow_monomial] using hbound d hd
  · exact ⟨w, by simpa only [hprod, integerContractedRow_monomial] using hw⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem affineModeLift_zero_of_homogeneous {K W : Type*}
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) {h : ℕ}
    (hz : ∀ P, Homogeneous h P → affineModeLift L P = 0)
    (P : VectorPolynomial (Option K) ℝ W) (hP : DegreeLE (1 : Option K → ℕ) h P) :
    affineModeLift L P = 0 := by
  have hf := (affineModeLift_factorization_iff h (Empty.elim : Empty → K → ℝ)
    L (0 : (Empty → W) →ₗ[ℝ] ℝ)).mp (by simpa only [LinearMap.zero_apply] using hz)
  exact hf P hP

theorem layeredCoefficientCharacter_eq_one_of_trivial {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hz : affineCoefficientModeTrivial U frequency)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))) p b = 1 := by
  have hzero (j : Fin m) :
      affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
        (substitute (fun u => rowPolynomial (fun k => b k u)) (p j)) = 0 := by
    let p' := restrictCoefficients (U j) (p j) (hm j)
    have hp' := degreeLE_restrictCoefficients (U j) (p j) (hm j) (hp j)
    have he := affineModeLift_zero_of_homogeneous
      ((coefficientFunctional (fun d a => (frequency j d a : ℝ))).comp (map (U j).subtype))
      (by simpa only [affineModeLift_comp_map, LinearMap.comp_apply] using hz j)
      (substitute (fun u => rowPolynomial (fun k => b k u)) p')
      (degreeLE_substitute_affine _ (fun u => (rowPolynomial_homogeneous (fun k => b k u)).totalDegree_le) p' hp')
    simpa only [affineModeLift_comp_map, LinearMap.comp_apply, map_substitute,
      p', map_restrictCoefficients] using he
  simp only [layeredCoefficientCharacter, hzero, Finset.sum_const_zero,
    AddCircle.coe_zero, CircleFourier.character_zero]

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

theorem coefficientTorusCharacter_sample {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    coefficientTorusCharacter U frequency (affineSampleCoefficientTorus U p hm b) =
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))) p b := by
  rw [affineSampleCoefficientTorus, coefficientTorusCharacter_mk, coefficientArrayFunctional_sample U frequency p hp hm]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AnchoredCubeResidueWidths
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators
open VectorPolynomial

theorem exists_affine_bounded_integer_mode {K J : Type*} [Fintype K] [Fintype J] {q : ℕ}
    (W : Submodule ℝ (J → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : (K →₀ ℕ) → J → ℤ) (h : ℕ)
    (hbound : ∀ d, d.degree ≤ h → ∀ j, |(frequency d j : ℝ)| ≤ C)
    (hnonfactor : ¬ ∃ M : (Finset (Fin q) → W) →ₗ[ℝ] ℝ,
      ∀ p, Homogeneous h p →
        affineModeLift (coefficientFunctional (fun d j => (frequency d j : ℝ))) (map W.subtype p) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) p)) :
    ∃ rows : Fin h → Option K → ℤ,
      (∀ i k, |(rows i k : ℝ)| ≤ cubeModePolynomialBudget q L) ∧
      (∀ s : Finset (Fin q), ∃ i, (∑ k, rows i k * affineSite root difference s k) = 0) ∧
      (∀ j, |(integerContractedRow (affineLiftFrequency frequency) (∏ i, rowPolynomial (rows i)) j : ℝ)| ≤
        C * cubeModePolynomialBudget q L ^ h) ∧
      ∃ w : W, (∑ j, (integerContractedRow (affineLiftFrequency frequency)
        (∏ i, rowPolynomial (rows i)) j : ℝ) * w.val j) ≠ 0 := by
  apply exists_vertex_bounded_integer_mode W root difference hlin hL hC hsite
    (affineLiftFrequency frequency) h (affineLiftFrequency_bound frequency hbound)
  simpa only [affineModeLift_integerFrequency] using hnonfactor

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_selected_affine_mode_rows {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ p, Homogeneous (i.val + 1) p →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype p) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) p)) :
    ∃ (i : Fin m) (rows : Fin (i.val + 1) → Option K → ℤ),
      (∀ j, i < j → ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
        ∀ p, DegreeLE (1 : Option K → ℕ) (j.val + 1) p →
          affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))) (map (U j).subtype p) =
            M (VectorPolynomial.siteEvaluation
              (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) p)) ∧
      (∀ r k, |(rows r k : ℝ)| ≤ cubeModePolynomialBudget q L) ∧
      (∀ s : Finset (Fin q), ∃ r, (∑ k, rows r k * affineSite root difference s k) = 0) ∧
      (∀ a, |(integerContractedRow (affineLiftFrequency (frequency i))
        (∏ r, rowPolynomial (rows r)) a : ℝ)| ≤ C * cubeModePolynomialBudget q L ^ (i.val + 1)) ∧
      ∃ w : U i, (∑ a, (integerContractedRow (affineLiftFrequency (frequency i))
        (∏ r, rowPolynomial (rows r)) a : ℝ) * w.val a) ≠ 0 := by
  let site : Finset (Fin q) → K → ℝ :=
    fun s k => (root k : ℝ) + ∑ r ∈ s, (difference r k : ℝ)
  have he : (fun s (k : Option K) => k.elim 1 (site s)) =
      (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) := by
    funext s k
    cases k <;> rfl
  obtain ⟨i, hi, hh⟩ := exists_highest_affine_subspace_nonfactor U site
    (fun j => coefficientFunctional (fun d a => (frequency j d a : ℝ))) (by rwa [he])
  rw [he] at hi hh
  obtain ⟨rows, hr, hz, hb, hw⟩ := exists_affine_bounded_integer_mode (U i) root difference hlin
    hL hC hsite (frequency i) (i.val + 1) (hbound i) hi
  exact ⟨i, rows, hh, hr, hz, hb, hw⟩

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_local_removal {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m,
      ((i.val + 1).factorial : ℝ) * (C * cubeModePolynomialBudget q L ^ (i.val + 1)) ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    {β : ℝ} (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ∃ i : Fin m, ∃ rows : Fin (i.val + 1) → Option K → ℤ,
      (∀ a k, |(rows a k : ℝ)| ≤ cubeModePolynomialBudget q L) ∧
      ∀ base : Option K → I → ℝ,
        ‖𝔼 x : Fin (i.val + 1) → ∀ j, Fin (N j),
          layeredModeTestedPhase
            (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
            p Q (fun s => affineSite root difference s) test
            (rowShiftedTuple base rows
              (fun (y : ∀ j, Fin (N j)) j => (stride j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ β := by
  classical
  obtain ⟨i, rows, hfactor, hrows, hzero, hcontract, hnonzero⟩ :=
    exists_selected_affine_mode_rows U root difference hlin hL hC hsite frequency hbound hbad
  have hcast : (fun s k => ((affineSite root difference s k : ℤ) : ℝ)) =
      (fun s => affineSite (fun k => (root k : ℝ)) (fun a k => (difference a k : ℝ)) s) := by
    funext s
    exact affineSite_intCast root difference s
  obtain ⟨Q', hQ', test', ht, he⟩ := exists_subspace_layered_mode_reduction i U
    (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
    p hm hp (fun s => affineSite root difference s)
    (by rw [hcast]; exact hfactor) Q (hQ.trans_lt (Nat.zero_lt_succ _)) test htest
  refine ⟨i, rows, hrows, ?_⟩
  intro base
  simp_rw [he, affineModeLift_integerFrequency]
  exact inhomogeneous_coefficient_mode_local_removal (affineLiftFrequency (frequency i)) rows
    (p i) (hp i) (U i) N stride hs hζ (hN i) H hH hA hscale (hrank i)
    hcontract (hrowBudget i) hnonzero (hdenom i) (hcoeff i)
    (fun s => affineSite root difference s) hzero Q' hQ' test' ht hβ (hpower i) base

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem affine_cube_mode_residue_removal {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m,
      ((i.val + 1).factorial : ℝ) * (C * cubeModePolynomialBudget q L ^ (i.val + 1)) ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth stride V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / residueProfileWidth stride V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {r β : ℝ} (hr : 0 ≤ r)
    (hmove : ∀ i : Fin m, ∀ z,
      ((i.val + 1 : ℕ) : ℝ) * cubeModePolynomialBudget q L *
        ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  obtain ⟨i, rows, hrows, hlocal⟩ := exists_affine_cube_local_removal
    U root difference hlin hL hC hsite frequency hbound hbad p hp hm N stride hs hζ hN
    H hH hA hscale hrank hrowBudget hdenom hcoeff Q hQ test htest hβ hpower
  have hNp k : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos i.val hζ).trans_le (hN i k)
  exact residue_smooth_row_shift_transfer N stride hNp hs rows residue V hV hZ hV1
    hδ hδ1 hmesh hsmall (cubeModePolynomialBudget_pos q hL).le hrows hr (hmove i)
    _ (layeredModeTestedPhase_norm_le _ p Q _ test htest) hlocal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators NNReal

theorem affine_cube_residue_removal_of_widths {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R T S : ℝ} (hζ : 0 < ζ) (hT : 0 < T) (hS : 0 ≤ S)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (hH : ∀ k, 0 < H k)
    (hsize : ∀ k, (stride k : ℝ) * T * (finiteLayerBiasBudget m ζ + 1) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : layerRemovalRankBudget m (Fintype.card I) C (cubeModePolynomialBudget q L)
      (finiteLayerBiasBudget m ζ) (2 * T) S ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (hV1 : ∀ z, 1 ≤ residueProfileWidth stride V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / residueProfileWidth stride V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {ρ r β : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (hmove : (m : ℝ) * cubeModePolynomialBudget q L ≤ r * ρ * T)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  let B := finiteLayerBiasBudget m ζ
  let D := cubeModePolynomialBudget q L
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m hζ
  have hD : 0 ≤ D := (cubeModePolynomialBudget_pos q hL).le
  have hA : 0 ≤ 2 * T := by positivity
  have hb (i : Fin m) : multiaffineBiasBudget i.val ζ ≤ B :=
    multiaffineBiasBudget_le_finite i hζ
  obtain ⟨N, hN, hscale, hshift⟩ := exists_mode_shift_lengths m hT hB hρ hr hmove H stride hs hsize V hwidth
  have hbud (i : Fin m) := layerRemovalRankBudget_bounds i (Fintype.card I) hC hD
    (zero_le_one.trans hB) hA hS
  apply affine_cube_mode_residue_removal U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm N stride hs hζ (fun i k => (hb i).trans (hN k)) H hH hA hscale hrank
    (fun i => (hbud i).1.trans hR) _ _ Q hQ test htest residue V hV hZ hV1 hδ hδ1 hmesh hsmall hr _ hβ hpower
  · intro i
    have hi := tensorDenominatorBound_le (H := Fin (i.val + 1))
      (multiaffineBiasBudget_pos i.val hζ).le (fun k => (stride k : ℝ))
      (fun k => Nat.cast_nonneg _) hstride
    have hi' : (∏ j : Fin (i.val + 1) → I,
        (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤
        (multiaffineBiasBudget i.val ζ * S ^ (i.val + 1)) ^ (Fintype.card I ^ (i.val + 1)) := by
      simpa only [Fintype.card_fin] using hi
    apply hi'.trans
    apply le_trans _ ((hbud i).2.1.trans hR)
    exact pow_le_pow_left₀
      (mul_nonneg (multiaffineBiasBudget_pos i.val hζ).le (pow_nonneg hS _))
      (mul_le_mul_of_nonneg_right (hb i) (pow_nonneg hS _)) _
  · intro i
    apply le_trans _ ((hbud i).2.2.trans hR)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hb i) (pow_nonneg hA _))
      (pow_nonneg (Nat.cast_nonneg _) _)
  · intro i z
    have hi : ((i.val + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    apply le_trans _ (hshift z)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hD)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineCommonCover
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem affine_cube_residue_removal_at_error {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (hsize : ∀ k, modeResidueSideThreshold m (Fintype.card (Option K × I))
      (cubeModePolynomialBudget q L) S ρ ε ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : modeRemovalRankThreshold m (Fintype.card I) (Fintype.card (Option K × I))
      C (cubeModePolynomialBudget q L) S ρ ε ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤ ε := by
  classical
  let d := Fintype.card (Option K × I)
  let D := cubeModePolynomialBudget q L
  let T := modeRemovalShrink m d D ρ ε
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε)
  have hD : 0 ≤ D := (cubeModePolynomialBudget_pos q hL).le
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (modeRemovalShrink_one_le m d hD hρ hε)
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hside := modeRemovalSideThreshold_bounds m d hD hS hρ hε
  have hsizeBase k : modeRemovalSideThreshold m d D S ρ ε ≤ H k :=
    (modeResidueSideThreshold_bounds m d hD hS hρ hε).1.trans (hsize k)
  have hH k : 0 < H k := hside.1.trans_le (hsizeBase k)
  have hsize' k : (stride k : ℝ) * T * (B + 1) ≤ H k := by
    calc
      _ ≤ S * T * (B + 1) := by gcongr; exact hstride k
      _ ≤ H k := hside.2.1.trans (hsizeBase k)
  have hv z : 1 ≤ residueProfileWidth stride V z ∧
      1 / residueProfileWidth stride V z ≤ modeRemovalMesh d :=
    modeResidueWidth_mesh m d hD hS hρ hε (hs z.2) (hstride z.2) (hsize z.2) (hV z) (hwidth z)
  have hmass := shiftedSmoothProductMass_lower (residueProfileCenter residue stride)
    (residueProfileWidth stride V) (residueProfileWidth_pos stride V hs hV)
    (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d) (fun z => (hv z).2) (modeRemovalMesh_small d)
  have hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V) :=
    (div_pos (Finset.prod_pos (fun z _ => residueProfileWidth_pos stride V hs hV z)) (by norm_num)).trans_le hmass
  refine ⟨hZ, ?_⟩
  have hout := affine_cube_residue_removal_of_widths U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm stride hs (modeRemovalBias_pos m hε) hT hS hstride H hH hsize' hrank hR
    Q hQ test htest residue V hV hZ (fun z => (hv z).1) (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d)
    (fun z => (hv z).2) (modeRemovalMesh_small d) hρ (modeRemovalRadius_pos d hε).le hwidth
    (modeRemovalShrink_move m d hρ hε) (modeRemovalBeta_pos hε).le (fun i => modeRemovalBias_le i hε)
  exact hout.trans (modeRemovalError_bound d hε)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_residue_uniform_removal (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hbudget⟩ := exists_cube_residue_threshold_exp_budget m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest residue V hV hwidth
  obtain ⟨hside, hrankBudget⟩ := hbudget (Fintype.card I) (Fintype.card (Option K × I))
    P C L S ρ ε hP hn hd hC hCP hL hLP hS hSP hρ hρP hε hεP
  exact affine_cube_residue_removal_at_error U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm stride hs hS hρ hε hstride H (fun k => hside.trans (hsize k)) hrank
    (hrankBudget.trans hR) Q hQ test htest residue V hV hwidth

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_ambient_residue_removal (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (residue : Option K × I → ℤ)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
        (residueProfileWidth stride V),
    ‖∑' z : Option K × I → ℤ, ((residueSmoothPMF residue stride _hs V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_cube_residue_uniform_removal m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest residue V hV hwidth
  obtain ⟨hZ, hrem⟩ := hremove hP hn hd U root difference hlin hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest residue V hV hwidth
  refine ⟨hZ, ?_⟩
  rw [residueSmoothPMF_expectation]
  exact hrem

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_congruence_removal (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hremove⟩ := exists_affine_cube_ambient_residue_removal m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  have hh (r : G) := hremove hP hn hd U root difference hlin hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest (columnResidueRepresentative stride r.val) V hV hwidth
  choose hZ hrem using hh
  exact selectedResidueSmoothPMF_bound_of_cells stride hs G hG V hV hZ _ hrem

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientCoverTilt
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem affineCoefficientCoverSample_eq_scaled {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (b : Option K → I → ℝ) :
    affineCoefficientCoverSample U p hm q b =
      affineSampleCoefficientTorus U (fun j => (q : ℝ)⁻¹ • p j)
        (fun j => coefficients_smul_mem (U j) (p j) (hm j) (q : ℝ)⁻¹) b := by
  rw [affineSampleCoefficientTorus, affineSampleCoefficientArray_smul]
  rfl

theorem affineCoefficientCoverSample_projection {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (hq : 0 < q) (b : Option K → I → ℝ) :
    quotientIntegerCover (coefficientIntegerLattice U) q (affineCoefficientCoverSample U p hm q b) =
      affineSampleCoefficientTorus U p hm b := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [affineCoefficientCoverSample, quotientIntegerCover_mk,
    smul_smul, mul_inv_cancel₀ hq0, one_smul]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SectionRetainedFourier
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_fourier_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          affineCubeFourierSum frequency p c (fun k j => (z (k, j) : ℝ)))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          affineCubeFourierProjection U root difference frequency p c (fun k j => (z (k, j) : ℝ))))‖ ≤ ε := by
  obtain ⟨A₀, _, hremove⟩ := exists_affine_cube_congruence_removal m q
  obtain ⟨A₁, _, hthreshold⟩ := exists_cube_residue_threshold_exp_budget m q
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound c B hB hBP hcoefficients p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  classical
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C L S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    hL (hLP.trans hEP) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m (cubeModePolynomialBudget_pos q hL).le
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  apply le_trans ?_ (fourierModeError_cost_le hB hε)
  unfold affineCubeFourierSum affineCubeFourierProjection
  apply selectedResidueSmoothPMF_discard_error stride G V hV hZ
    (fun z => layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)))
    c (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (fun k j => (z (k, j) : ℝ)))
    (fun a => affineCubeModeFactors U root difference (frequency a)) hcoefficients hδ.le
  intro a hbad
  obtain ⟨_, hr⟩ := hremove (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
    U root difference hlin hL hC (hLP.trans hEP) (hCP.trans hEP) hsite (frequency a) (hbound a)
    ((not_affineCubeModeFactors_iff U root difference (frequency a)).mp hbad)
    p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
    H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) Q hQ test htest G hG V hV hwidth
  simpa only [layeredModeTestedPhase_eq_weight_mul] using hr

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CanonicalCoverLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory

instance subspaceArrayIntegerLattice_closed {I D : Type*} (U : Submodule ℝ (D → ℝ)) :
    IsClosed (subspaceArrayIntegerLattice I U : Set (I → U)) := by
  change IsClosed {x : I → U | ∀ i a, ∃ n : ℤ, (x i).val a = n}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro a
  have hc : Continuous (fun x : I → U => (x i).val a) :=
    (continuous_apply a).comp (continuous_subtype_val.comp (continuous_apply i))
  have h : IsClosed {x : I → U | ∃ n : ℤ, (n : ℝ) = (x i).val a} :=
    Real.isClosedEmbedding_intCast.isClosed_range.preimage hc
  simpa only [eq_comm] using h

end Erdos3

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

theorem coefficientTorusFourierSum_fiber_integrable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => coefficientTorusFourierSum U frequency c (coefficientFiberMap U t y x)) μ := by
  apply integrable_finsetSum
  intro a _
  exact (coefficientTorusCharacter_fiber_integrable U t (frequency a) μ y).const_mul (c a)

theorem affineCubeFourierProjection_eq_fiberAverage {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    affineCubeFourierProjection U t difference frequency p c b =
      coefficientFiberAverage U μ t (coefficientTorusFourierSum U frequency c)
        (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm b)) := by
  rw [coefficientTorusFourierSum_fiberAverage U t difference]
  simp only [coefficientTorusCharacter_sample U _ p hp hm b, affineCubeFourierProjection]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductOneSiteProjectionCap
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

theorem affineCubeFourierProjection_approx {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η : ℝ}
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ)
    (hD : Integrable (fun x => D (coefficientFiberMap U t
      (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm b)) x)) μ) :
    ‖affineCubeFourierProjection U t difference frequency p c b -
      ((coefficientFiberAverage U μ t D
        (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm b)) : ℝ) : ℂ)‖ ≤ η := by
  rw [affineCubeFourierProjection_eq_fiberAverage U t difference frequency c μ p hp hm b]
  have he := coefficientFiberAverage_approx U μ t (coefficientTorusFourierSum U frequency c)
    (fun x => (D x : ℂ)) happrox _
    (coefficientTorusFourierSum_fiber_integrable U t frequency c μ _) hD.ofReal
  simpa only [coefficientFiberAverage, integral_complex_ofReal] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

theorem oneSiteDensity_projection_error {X I K F : Type*} [Fintype X] [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η ε B : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (prob : FiniteProbabilityWeights X) (b : X → Option K → I → ℝ) (w : X → ℂ)
    (hD : ∀ x, prob.weight x ≠ 0 → Integrable (fun z => D (coefficientFiberMap U t
      (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm (b x))) z)) μ)
    (hw : prob.mean (fun x => ‖w x‖) ≤ B)
    (hprojection : ‖prob.complexMean (fun x => w x * affineCubeFourierSum frequency p c (b x)) -
      prob.complexMean (fun x => w x * affineCubeFourierProjection U t difference frequency p c (b x))‖ ≤ ε) :
    ‖prob.complexMean (fun x => w x * (D (affineSampleCoefficientTorus U p hm (b x)) : ℂ)) -
      prob.complexMean (fun x => w x * ((coefficientFiberAverage U μ t D
        (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm (b x))) : ℝ) : ℂ))‖ ≤
      2 * B * η + ε := by
  apply prob.weighted_projection_comparison w _
    (fun x => affineCubeFourierSum frequency p c (b x))
    (fun x => affineCubeFourierProjection U t difference frequency p c (b x)) _ hη hw
  · intro x _
    rw [norm_sub_rev]
    simpa only [affineCubeFourierSum, coefficientTorusFourierSum,
      coefficientTorusCharacter_sample U _ p hp hm] using happrox (affineSampleCoefficientTorus U p hm (b x))
  · intro x hx
    exact affineCubeFourierProjection_approx U t difference frequency c μ D happrox p hp hm (b x) (hD x hx)
  · exact hprojection

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineOneSiteNormalizedLaw
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

theorem selectedResidue_oneSite_density_error {I K F : Type*} [Fintype I] [Fintype K] [Fintype F]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η ε : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U t y x)) μ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (G : Finset (ColumnResiduePattern (Option K) I stride))
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x)
    (w : (Option K × I → ℤ) → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (hprojection : ‖(∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
      (w x * affineCubeFourierSum frequency p c (fun k j => (x (k, j) : ℝ)))) -
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
        (w x * affineCubeFourierProjection U t difference frequency p c (fun k j => (x (k, j) : ℝ)))‖ ≤ ε) :
    ‖(∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
      (w x * (D (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ))) : ℂ))) -
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
        (w x * ((coefficientFiberAverage U μ t D (coefficientEvaluationTorus U t
          (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ)))) : ℝ) : ℂ))‖ ≤ 2 * η + ε := by
  let prob := selectedResidueFiniteLaw stride G V hV hZ
  have hmean (f : (Option K × I → ℤ) → ℂ) : prob.complexMean (fun x => f x.val) =
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) * f x :=
    selectedResidueFiniteLaw_complexMean stride G V hV hZ f
  have hw' : prob.mean (fun x => ‖w x.val‖) ≤ 1 :=
    (prob.mean_mono (fun x => hw x.val)).trans_eq (prob.mean_const 1)
  have he := oneSiteDensity_projection_error (ε := ε) U t difference frequency c μ D hη happrox p hp hm
    prob (fun x k j => (x.val (k, j) : ℝ)) (fun x => w x.val) (fun _ _ => hD _) hw'
    (by
      rw [hmean (fun x => w x * affineCubeFourierSum frequency p c (fun k j => (x (k, j) : ℝ))),
        hmean (fun x => w x * affineCubeFourierProjection U t difference frequency p c (fun k j => (x (k, j) : ℝ)))]
      exact hprojection)
  rw [hmean (fun x => w x * (D (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ))) : ℂ)),
    hmean (fun x => w x * ((coefficientFiberAverage U μ t D (coefficientEvaluationTorus U t
      (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ)))) : ℝ) : ℂ))] at he
  simpa only [mul_one] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem exists_affine_oneSite_density_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ)
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin 0)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin 0) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ)
    (_hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U root y x)) μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          (D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))) : ℂ))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          ((coefficientFiberAverage U μ root D (coefficientEvaluationTorus U root
            (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) : ℝ) : ℂ)))‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hprojection⟩ := exists_affine_cube_fourier_projection m 0
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ root difference
    L C hL hC hLP hCP hsite frequency hbound c B hB hBP hcoefficients p hp hm
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR Q hQ test htest
    G hG V hV hwidth D hD η hη happrox
  obtain ⟨hZ, he⟩ := hprojection hP hn hd U root difference linearIndependent_empty_type
    hL hC hLP hCP hsite frequency hbound c hB hBP hcoefficients p hp hm stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  exact selectedResidue_oneSite_density_error U root difference frequency c μ D hη happrox hD p hp hm
    stride G V hV hZ
    (fun z => layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)))
    (fun z => layeredSiteWeight_norm_le Q _ test htest _) he

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem mean_fintype_sum {Ω J : Type*} [Fintype Ω] [Fintype J]
    (p : FiniteProbabilityWeights Ω) (f : J → Ω → ℝ) :
    p.mean (fun x => ∑ j, f j x) = ∑ j, p.mean (f j) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

end FiniteProbabilityWeights
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

variable [Fintype U] [DecidableEq U]

noncomputable def integerPoints (A : ResidueBoxSlice N q) : Finset (U → ℤ) :=
  Finset.univ.image A.integerPoint

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionMarkedSurjective
namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct

variable {ι : Type v} {L₀ M₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

namespace NilpotentLieFiltration

def optionFiltrations (F₀ : NilpotentLieFiltration L₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) :
    ∀ i : Option ι, NilpotentLieFiltration (optionLieSpace L₀ L i) s
  | none => F₀
  | some i => F i

@[simp] theorem optionFiltrations_none (F₀ : NilpotentLieFiltration L₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) : optionFiltrations F₀ F none = F₀ := rfl

@[simp] theorem optionFiltrations_some (F₀ : NilpotentLieFiltration L₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) (i : ι) :
    optionFiltrations F₀ F (some i) = F i := rfl

end NilpotentLieFiltration

open NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RaisedDegreeRank
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem realLayer_one : F.realLayer 1 0 = ⊤ := by
  have h : F.layerIdeal 1 0 = ⊤ := by
    ext x
    change x ∈ F.layer 1 0 ↔ x ∈ (⊤ : Submodule ℚ L)
    rw [F.one_eq_top]
  simp only [realLayer, h, LieSubmodule.baseChange_top]

noncomputable def realification : DegreeRankLieFiltration (ℝ ⊗[ℚ] L) s r where
  rank_le_degree := F.rank_le_degree
  layer d i := (F.realLayer d i).toSubmodule.restrictScalars ℚ
  lex_antitone := F.realLayer_lex_antitone
  one_eq_top := by rw [F.realLayer_one]; rfl
  rank_zero_eq_one d := by rw [F.realLayer_rank_zero_eq_one]
  overshoot d i h := by rw [F.realLayer_overshoot d i h]
  lie_mem := F.realLayer_lie_mem
  terminal := by rw [F.realLayer_terminal]; rfl

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

def reducedNativeIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ)
    (z : SymbolBasisIndex w (fun i : QuotientTopBasisIndex s ω => ω i.val)) :
    AdaptedBasisIndex w ω :=
  ⟨(z.val.1, z.val.2.val), z.property.le⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductCoefficient
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def realHorizontalMap :
    (F.layer d 1).baseChange ℝ →ₗ[ℝ] ℝ ⊗[ℚ] F.HigherHorizontal d :=
  ((F.higherHorizontalMk d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (F.layer d 1)).symm.toLinearMap

@[simp] theorem realHorizontalMap_baseChange (v : ℝ ⊗[ℚ] F.layer d 1) :
    F.realHorizontalMap d (realificationSubmoduleEquiv (F.layer d 1) v) =
      (F.higherHorizontalMk d).baseChange ℝ v := by
  exact congrArg ((F.higherHorizontalMk d).baseChange ℝ)
    ((realificationSubmoduleEquiv (F.layer d 1)).symm_apply_apply v)

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ)

noncomputable def realFourLayerComponent (k : Fin 4) :
    (F.fourHorizontalLayer d).baseChange ℝ →ₗ[ℝ] (F.layer d 1).baseChange ℝ :=
  (((LinearMap.proj k).baseChange ℝ).comp ((F.fourHorizontalLayer d).baseChange ℝ).subtype).codRestrict
    ((F.layer d 1).baseChange ℝ) (fun x => baseChange_mem_of_mapsTo
      (F.fourHorizontalLayer d) (F.layer d 1) (LinearMap.proj k)
      (fun v hv => (F.mem_fourHorizontalLayer d v).mp hv k) x.property)

@[simp] theorem realFourLayerComponent_coe (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) :
    (F.realFourLayerComponent d k x).val = (LinearMap.proj k).baseChange ℝ x.val := rfl

end DegreeRankLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

universe u v

attribute [local instance] ScalarSiteExpansion.termFinite

namespace ScalarSiteExpansion

variable {S : Type u} [Fintype S]

structure Bounds (e : ScalarSiteExpansion.{u,v} S) (T D C : ℝ) (L : ℝ≥0) (H : ℝ) : Prop where
  card_le : (Fintype.card e.Term : ℝ) ≤ T
  period_pos : ∀ i, 0 < e.period i
  period_le : ∀ i, (e.period i : ℝ) ≤ D
  coefficient_le : (∑ i, ‖e.coefficient i‖) ≤ C
  factor_bound : ∀ i s r x, ‖e.factor i s r x‖ ≤ 1
  lipschitz : ∀ i s r, LipschitzWith L (e.factor i s r)
  support : ∀ i s r x, H ≤ |x| → e.factor i s r x = 0

end ScalarSiteExpansion
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CommonSectionAmbientDensityMultiple
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (R : CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U)
variable (hR : ∀ x ∈ coefficientIntegerLattice U, R x ∈ coefficientIntegerLattice U)
variable (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ]

theorem coefficientResidualAmbientDensity_lipschitz
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) {C : ℝ} (hfb : ∀ z, ‖f z‖ ≤ C) :
    LipschitzWith L (coefficientResidualAmbientDensity U R hR μ f) := by
  have hRc := linearQuotientEndomorphism_continuous (coefficientIntegerLattice U) R hR
    R.continuous_of_finiteDimensional
  have hi (z : CoefficientAmbientIndex K J → UnitAddCircle) :
      Integrable (fun y => f (z + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))) μ := by
    apply Integrable.of_bound (C := C)
    · exact (hf.continuous.comp (continuous_const.add
        ((coefficientAmbientTorus_continuous U).comp hRc))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun _ => hfb _)
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  change ‖(∫ y, f (z + coefficientAmbientTorus U
      (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) ∂μ) -
    ∫ y, f (w + coefficientAmbientTorus U
      (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) ∂μ‖ ≤ _
  rw [← integral_sub (hi z) (hi w)]
  calc
    _ ≤ ((L : ℝ) * dist z w) * μ.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with y
      have h := hf.dist_le_mul (z + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))
        (w + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))
      rw [dist_add_right] at h
      exact h
    _ = _ := by rw [probReal_univ, mul_one]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) (q : ℕ)
variable (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)

local notation "R" => coefficientSiteResidual U site (fun _ => q) T
local notation "hR" => coefficientSiteResidual_preserves_lattice U site (fun _ => q) T

variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ]

theorem coefficientSectionAmbientDensity_lipschitz
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L A : ℝ≥0}
    (hf : LipschitzWith L f) {C : ℝ} (hfb : ∀ z, ‖f z‖ ≤ C)
    (hT : ∀ j e, ∑ s, ‖T j e s‖ ≤ A) :
    LipschitzWith (L * A) (coefficientSectionAmbientDensity U site q T μ f) :=
  (coefficientResidualAmbientDensity_lipschitz U R hR μ f hf hfb).comp
    (coefficientAmbientSiteSection_lipschitz T hT)

end Erdos3.VectorPolynomial

end

end OAI
end


