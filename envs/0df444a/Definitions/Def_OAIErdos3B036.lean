-- Prove2me | Definitions.Def_OAIErdos3B036
-- name    : OAIErdos3B036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T23:24:55.743829+00:00
-- url     : https://prove2.me/theorems/fc880866-21b4-493e-9180-eabbf89123df
-- title:
--   OpenAI Erdős-3 split, definitions bundle 37 of 130
-- statement:
--   Definitions bundle 37 of 130 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B035`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 37 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.affineSite_intCast`, `OAI.Erdos3.BooleanCubeKernel.affine_cube_mode_residue_removal`, `OAI.Erdos3.BooleanCubeKernel.affine_cube_residue_removal_of_widths`, `OAI.Erdos3.BooleanCubeKernel.boundedSiteMatrix_high_jet_zero`, `OAI.Erdos3.BooleanCubeKernel.cubeInputLogPolynomial`, `OAI.Erdos3.BooleanCubeKernel.cubeInputLogPolynomial_ge`, `OAI.Erdos3.BooleanCubeKernel.cubeModePolynomialBudget_le_exp_input`, `OAI.Erdos3.BooleanCubeKernel.cubeModePolynomialBudget_pos`, `OAI.Erdos3.BooleanCubeKernel.exists_affine_bounded_integer_mode`, `OAI.Erdos3.BooleanCubeKernel.exists_affine_cube_local_removal`, `OAI.Erdos3.BooleanCubeKernel.exists_cube_mode_threshold_exp_budget`, `OAI.Erdos3.BooleanCubeKernel.exists_selected_affine_mode_rows`, `OAI.Erdos3.BooleanCubeKernel.frameLift_eval_site`, `OAI.Erdos3.BooleanCubeKernel.homogeneous_high_jet_zero`, `OAI.Erdos3.BooleanCubeKernel.normalSpan_high_jet_zero`, `OAI.Erdos3.BoundedBooleanJet`, `OAI.Erdos3.VectorPolynomial.BooleanJetTorus`, `OAI.Erdos3.VectorPolynomial.CoefficientCoordinateTori`, `OAI.Erdos3.VectorPolynomial.CoefficientTorus`, `OAI.Erdos3.VectorPolynomial.EuclideanCoefficientLayers`, `OAI.Erdos3.VectorPolynomial.EuclideanJetLayers`, `OAI.Erdos3.VectorPolynomial.LowBooleanJetTorus`, `OAI.Erdos3.VectorPolynomial.SiteTorus`, `OAI.Erdos3.VectorPolynomial.affineCoefficientModeTrivial`, `OAI.Erdos3.VectorPolynomial.affineModeLift_zero_iff_bounded`, `OAI.Erdos3.VectorPolynomial.affineModeLift_zero_of_homogeneous`, `OAI.Erdos3.VectorPolynomial.affineSampleCoefficientArray`, `OAI.Erdos3.VectorPolynomial.affineSampleCoefficientArray_val`, `OAI.Erdos3.VectorPolynomial.affineSampleCoefficientTorus`, `OAI.Erdos3.VectorPolynomial.affine_coefficient_mode_residue_removal`, `OAI.Erdos3.VectorPolynomial.affine_coefficient_mode_residue_removal_lipschitz_amplitude`, `OAI.Erdos3.VectorPolynomial.affine_coefficient_residue_removal_of_widths`, `OAI.Erdos3.VectorPolynomial.affine_coefficient_residue_removal_of_widths_lipschitz_amplitude`, `OAI.Erdos3.VectorPolynomial.boundedArrayPolynomial`, `OAI.Erdos3.VectorPolynomial.boundedArrayPolynomial_coeff`, `OAI.Erdos3.VectorPolynomial.boundedArrayPolynomial_degreeLE`, `OAI.Erdos3.VectorPolynomial.boundedArrayPolynomial_reconstruct`, `OAI.Erdos3.VectorPolynomial.boundedSiteMatrix`, `OAI.Erdos3.VectorPolynomial.bounded_site_factorization_to_array`, `OAI.Erdos3.VectorPolynomial.coefficientArrayFunctional_eq_zero_iff_trivial`, `OAI.Erdos3.VectorPolynomial.coefficientArrayFunctional_integral`, `OAI.Erdos3.VectorPolynomial.coefficientArrayFunctional_sample`, `OAI.Erdos3.VectorPolynomial.coefficientBooleanJetTorusMap`, `OAI.Erdos3.VectorPolynomial.coefficientBooleanJetTorusMap_continuous`, `OAI.Erdos3.VectorPolynomial.coefficientBooleanJetTorusMap_mk`, `OAI.Erdos3.VectorPolynomial.coefficientBooleanJetTorusMap_surjective`, `OAI.Erdos3.VectorPolynomial.coefficientCoordinateArray`, `OAI.Erdos3.VectorPolynomial.coefficientCoordinateEquiv`, `OAI.Erdos3.VectorPolynomial.coefficientCoordinateTori_compact`, `OAI.Erdos3.VectorPolynomial.coefficientCoordinateTorus`, `OAI.Erdos3.VectorPolynomial.coefficientCoordinateTorus_continuous`, `OAI.Erdos3.VectorPolynomial.coefficientCoordinateTorus_injective`, `OAI.Erdos3.VectorPolynomial.coefficientCoordinateTorus_measurePreserving`, `OAI.Erdos3.VectorPolynomial.coefficientCoordinateTorus_mk`, `OAI.Erdos3.VectorPolynomial.coefficientCoordinateTorus_surjective`, `OAI.Erdos3.VectorPolynomial.coefficientFunctional_boundedArrayPolynomial`, `OAI.Erdos3.VectorPolynomial.coefficientFunctional_bounded_expansion`, `OAI.Erdos3.VectorPolynomial.coefficientIntegerLattice`, `OAI.Erdos3.VectorPolynomial.coefficientIntegerLattice_closed`, `OAI.Erdos3.VectorPolynomial.coefficientLayerArray`, `OAI.Erdos3.VectorPolynomial.coefficientLayerArray_preserves_lattice`, `OAI.Erdos3.VectorPolynomial.coefficientLayerTorus`, `OAI.Erdos3.VectorPolynomial.coefficientLayerTorus_continuous`, `OAI.Erdos3.VectorPolynomial.coefficientModeTestedPhase`, `OAI.Erdos3.VectorPolynomial.coefficientModeTestedPhase_map`, `OAI.Erdos3.VectorPolynomial.coefficientModeTestedPhase_top`, `OAI.Erdos3.VectorPolynomial.coefficientMode_integer_row_decomposition`, `OAI.Erdos3.VectorPolynomial.coefficientMode_paired_bias_lt_of_rank`, `OAI.Erdos3.VectorPolynomial.coefficientSiteImage_lowJet_injective`, `OAI.Erdos3.VectorPolynomial.coefficientSiteImage_lowJet_surjective`, `OAI.Erdos3.VectorPolynomial.coefficientSiteTorusMap`, `OAI.Erdos3.VectorPolynomial.coefficientSiteTorusMap_continuous`, `OAI.Erdos3.VectorPolynomial.coefficientSiteTorusMap_mk`, `OAI.Erdos3.VectorPolynomial.coefficientSlotFrequency`, `OAI.Erdos3.VectorPolynomial.coefficientSlotFrequency_apply`, `OAI.Erdos3.VectorPolynomial.coefficientSlotFrequency_bound`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_integrable`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_integral`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_mk`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_norm`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_sample`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_slot_product`, `OAI.Erdos3.VectorPolynomial.coefficientTorusFourierSum`, `OAI.Erdos3.VectorPolynomial.coefficientTorusFourierSum_integrable`, `OAI.Erdos3.VectorPolynomial.coefficientTorusFourierSum_integral`, `OAI.Erdos3.VectorPolynomial.coefficientTorusHaar`, `OAI.Erdos3.VectorPolynomial.coefficientTorusHaar_invariant`, `OAI.Erdos3.VectorPolynomial.coefficientTorusHaar_probability`, `OAI.Erdos3.VectorPolynomial.coefficientTorus_compact_of_basis`, `OAI.Erdos3.VectorPolynomial.coefficient_mode_finite_removal`, `OAI.Erdos3.VectorPolynomial.degreeLE_monomial_of_degree_le`, `OAI.Erdos3.VectorPolynomial.degreeLE_restrictCoefficients`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientEquiv`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientEquiv_apply`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientEquiv_continuous`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientHomeomorph`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientJetMap`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientJetMap_continuous`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientJetMap_measurePreserving`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientJetMap_surjective`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientLayers_borel`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficientMeasurableEquiv`, `OAI.Erdos3.VectorPolynomial.euclideanCoefficient_measurePreserving`, `OAI.Erdos3.VectorPolynomial.euclideanJetEquiv`, `OAI.Erdos3.VectorPolynomial.euclideanJetEquiv_continuous`, `OAI.Erdos3.VectorPolynomial.euclideanJetLayers_borel`, `OAI.Erdos3.VectorPolynomial.euclideanSiteImageEquiv`, `OAI.Erdos3.VectorPolynomial.euclideanSiteImageEquiv_continuous`, `OAI.Erdos3.VectorPolynomial.euclideanSiteImageHomeomorph`, `OAI.Erdos3.VectorPolynomial.euclideanSiteImageHomeomorph_haar`, `OAI.Erdos3.VectorPolynomial.exists_affine_coefficient_local_removal`, `OAI.Erdos3.VectorPolynomial.exists_layered_mode_reduction`, `OAI.Erdos3.VectorPolynomial.exists_subspace_layered_mode_reduction`, `OAI.Erdos3.VectorPolynomial.exists_unit_integer_mode_rows`, `OAI.Erdos3.VectorPolynomial.inhomogeneous_coefficient_mode_local_removal`, `OAI.Erdos3.VectorPolynomial.integerContractedRow_monomial`, `OAI.Erdos3.VectorPolynomial.layeredCoefficientCharacter`, `OAI.Erdos3.VectorPolynomial.layeredCoefficientCharacter_eq_one_of_trivial`, `OAI.Erdos3.VectorPolynomial.layeredCoefficientCharacter_norm`, `OAI.Erdos3.VectorPolynomial.layeredModeTestedPhase`, `OAI.Erdos3.VectorPolynomial.layeredModeTestedPhase_empty_zero`, `OAI.Erdos3.VectorPolynomial.layeredModeTestedPhase_eq_weight_mul`, `OAI.Erdos3.VectorPolynomial.layeredModeTestedPhase_map`, `OAI.Erdos3.VectorPolynomial.layeredModeTestedPhase_norm_le`, `OAI.Erdos3.VectorPolynomial.layeredSiteWeight`, `OAI.Erdos3.VectorPolynomial.layeredSiteWeight_norm_le`, `OAI.Erdos3.VectorPolynomial.lowerLayerPolynomial`, `OAI.Erdos3.VectorPolynomial.lowerLayerPolynomial_degree`, `OAI.Erdos3.VectorPolynomial.lowerLayerPolynomial_eval`, `OAI.Erdos3.VectorPolynomial.lowerModePolynomial`, `OAI.Erdos3.VectorPolynomial.lowerModePolynomial_degree`, `OAI.Erdos3.VectorPolynomial.lowerModePolynomial_eval`, `OAI.Erdos3.VectorPolynomial.not_affineCoefficientModeTrivial_iff`, `OAI.Erdos3.VectorPolynomial.siteBooleanJetTorusMap`, `OAI.Erdos3.VectorPolynomial.siteBooleanJetTorusMap_continuous`, `OAI.Erdos3.VectorPolynomial.siteEvaluation_boundedArrayPolynomial`, `OAI.Erdos3.VectorPolynomial.siteEvaluation_bounded_coefficients`, `OAI.Erdos3.VectorPolynomial.siteFromLowBooleanJets`, `OAI.Erdos3.VectorPolynomial.siteFromLowBooleanJets_coefficient`, `OAI.Erdos3.VectorPolynomial.sum_bounded_monomial_coefficients`, `OAI.Erdos3.VectorPolynomial.zeroCoefficientExponent`, `OAI.Erdos3.booleanJetExtractionMatrix`, `OAI.Erdos3.booleanJetExtractionMatrix_mulVec`, `OAI.Erdos3.booleanJetExtractionMatrix_mul_boundedSite`, `OAI.Erdos3.booleanJetExtraction_mul_reconstruction`, `OAI.Erdos3.booleanReconstructionMatrix`, `OAI.Erdos3.booleanReconstruction_mul_extraction`, `OAI.Erdos3.boundedBooleanJetRows`, `OAI.Erdos3.boundedBooleanJetRowsEquiv`, `OAI.Erdos3.boundedBooleanReconstructionMatrix`, `OAI.Erdos3.boundedBooleanReconstruction_siteMatrix`, `OAI.Erdos3.boundedCoefficientIntegerExponentEquiv`, `OAI.Erdos3.boundedCoefficientJetMatrix`, `OAI.Erdos3.boundedCoefficientJetMatrix_period`, `OAI.Erdos3.integerMatrixTorusMap_comp`, `OAI.Erdos3.integerMatrixTorusMap_continuous`, `OAI.Erdos3.matrixModuleAction_surjective_of_period`, `OAI.Erdos3.mem_boundedBooleanJetRows`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B032

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

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

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

open CircleFourier
open scoped BigOperators NNReal Classical

noncomputable def coefficientModeTestedPhase {I K W S : Type*} [Fintype K] [Fintype S]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (Q : MvPolynomial (K × I) ℝ) (site : S → K → ℤ)
    (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) : ℂ :=
  character ((L (substitute (fun j => rowPolynomial (fun k => b k j)) p) +
    MvPolynomial.eval (fun z => b z.1 z.2) Q : ℝ) : CircleFourier.Circle) *
      ∏ t, test t (integerSiteValue (site t) b)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def lowerModePolynomial {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (h : ℕ) (p : VectorPolynomial I ℝ W) (Q : MvPolynomial (K × I) ℝ) :
    MvPolynomial (K × I) ℝ := coefficientModePolynomial L (p - homogeneousPart h p) + Q

theorem lowerModePolynomial_degree {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    {n : ℕ} (p : VectorPolynomial I ℝ W) (hp : DegreeLE (1 : I → ℕ) (n + 1) p)
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < n + 1) :
    (lowerModePolynomial L (n + 1) p Q).totalDegree < n + 1 := by
  apply lt_of_le_of_lt (MvPolynomial.totalDegree_add _ _)
  apply max_lt
  · exact (coefficientModePolynomial_degreeLE L _ (sub_homogeneousPart_degreeLE hp)).trans_lt
      (Nat.lt_succ_self n)
  · exact hQ

theorem lowerModePolynomial_eval {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (h : ℕ) (p : VectorPolynomial I ℝ W) (Q : MvPolynomial (K × I) ℝ) (b : K → I → ℝ) :
    L (substitute (fun j => rowPolynomial (fun k => b k j)) (homogeneousPart h p)) +
      MvPolynomial.eval (fun z => b z.1 z.2) (lowerModePolynomial L h p Q) =
    L (substitute (fun j => rowPolynomial (fun k => b k j)) p) +
      MvPolynomial.eval (fun z => b z.1 z.2) Q := by
  rw [lowerModePolynomial, map_add, coefficientModePolynomial_eval, map_sub, map_sub]
  ring

theorem coefficientModeTestedPhase_top {I K W S : Type*} [Fintype K] [Fintype S]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (h : ℕ)
    (p : VectorPolynomial I ℝ W) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    coefficientModeTestedPhase L p Q site test b =
      coefficientModeTestedPhase L (homogeneousPart h p) (lowerModePolynomial L h p Q) site test b := by
  unfold coefficientModeTestedPhase
  rw [lowerModePolynomial_eval]

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

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

noncomputable def lowerLayerPolynomial {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (i : Fin m) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) : MvPolynomial (K × I) ℝ :=
  ∑ j, if j < i then coefficientModePolynomial (L j) (p j) else 0

theorem lowerLayerPolynomial_degree {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (i : Fin m) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) :
    (lowerLayerPolynomial i L p).totalDegree < i.val + 1 := by
  apply lt_of_le_of_lt (b := i.val) _ (Nat.lt_succ_self _)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  by_cases hji : j < i
  · rw [if_pos hji]
    exact (coefficientModePolynomial_degreeLE (L j) (p j) (hp j)).trans
      (Nat.succ_le_of_lt hji)
  · simp [hji]

theorem lowerLayerPolynomial_eval {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (i : Fin m) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) :
    MvPolynomial.eval (fun z => b z.1 z.2) (lowerLayerPolynomial i L p) =
      ∑ j, if j < i then L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j)) else 0 := by
  rw [lowerLayerPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j < i <;> simp [hji, coefficientModePolynomial_eval]

noncomputable def layeredModeTestedPhase {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) : ℂ :=
  character (((∑ j, L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j))) +
    MvPolynomial.eval (fun z => b z.1 z.2) Q : ℝ) : CircleFourier.Circle) *
      ∏ s, test s (integerSiteValue (site s) b)

theorem exists_layered_mode_reduction {I K S : Type*} [Fintype K] [Fintype S] [DecidableEq S]
    {m : ℕ} {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)] (i : Fin m)
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (site : S → K → ℤ)
    (hfactor : ∀ j, i < j → ∃ M : (S → W j) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (j.val + 1) q →
        L j q = M (siteEvaluation (fun s k => (site s k : ℝ)) q))
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < i.val + 1)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ Q' : MvPolynomial (K × I) ℝ, Q'.totalDegree < i.val + 1 ∧
      ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
        layeredModeTestedPhase L p Q site test b =
          coefficientModeTestedPhase (L i) (p i) Q' site test' b := by
  classical
  let Q' := lowerLayerPolynomial i L p + Q
  have hQ' : Q'.totalDegree < i.val + 1 :=
    lt_of_le_of_lt (MvPolynomial.totalDegree_add _ _)
      (max_lt (lowerLayerPolynomial_degree i L p hp) hQ)
  let low (b : K → I → ℝ) :=
    L i (substitute (fun u => rowPolynomial (fun k => b k u)) (p i)) +
      MvPolynomial.eval (fun z => b z.1 z.2) Q'
  obtain ⟨test', ht, he⟩ := exists_absorbed_integer_site_tests
    (fun j : {j : Fin m // i < j} => j.val.val + 1) site
    (fun j => L j.val) (fun j => hfactor j.val j.property)
    (fun j => p j.val) (fun j => hp j.val) low test htest
  refine ⟨Q', hQ', test', ht, ?_⟩
  intro b
  have hsplit : (∑ j, L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j))) +
      MvPolynomial.eval (fun z => b z.1 z.2) Q = low b +
      ∑ j : {j : Fin m // i < j},
        L j.val (substitute (fun u => rowPolynomial (fun k => b k u)) (p j.val)) := by
    rw [sum_split_at_layer i]
    dsimp [low, Q']
    rw [map_add, lowerLayerPolynomial_eval]
    ring
  unfold layeredModeTestedPhase
  rw [hsplit]
  exact he b

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem layeredModeTestedPhase_norm_le {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ)
    (htest : ∀ s x, ‖test s x‖ ≤ 1) (b : K → I → ℝ) :
    ‖layeredModeTestedPhase L p Q site test b‖ ≤ 1 := by
  rw [layeredModeTestedPhase, norm_mul, norm_character, one_mul, norm_prod]
  exact Finset.prod_le_one (fun s _ => norm_nonneg _) (fun s _ => htest s _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem degreeLE_restrictCoefficients {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (U : Submodule ℝ V) (p : VectorPolynomial I ℝ V) (hm : ∀ d, coefficients p d ∈ U)
    {w : I → ℕ} {h : ℕ} (hp : DegreeLE w h p) : DegreeLE w h (restrictCoefficients U p hm) := by
  apply (degreeLE_map_iff w h U.subtype Subtype.val_injective _).mp
  simpa only [map_restrictCoefficients] using hp

theorem coefficientModeTestedPhase_map {I K S V W : Type*} [Fintype K] [Fintype S]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ)
    (p : VectorPolynomial I ℝ V) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    coefficientModeTestedPhase (L.comp (map f)) p Q site test b =
      coefficientModeTestedPhase L (map f p) Q site test b := by
  simp only [coefficientModeTestedPhase, LinearMap.comp_apply, map_substitute]

theorem layeredModeTestedPhase_map {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {V W : Fin m → Type*}
    [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)]
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (f : ∀ j, V j →ₗ[ℝ] W j) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (V j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    layeredModeTestedPhase (fun j => (L j).comp (map (f j))) p Q site test b =
      layeredModeTestedPhase L (fun j => map (f j) (p j)) Q site test b := by
  simp only [layeredModeTestedPhase, LinearMap.comp_apply, map_substitute]

theorem exists_subspace_layered_mode_reduction {I K S : Type*}
    [Fintype K] [Fintype S] [DecidableEq S] {m : ℕ}
    {V : Fin m → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module ℝ (V j)] (i : Fin m)
    (U : ∀ j, Submodule ℝ (V j)) (L : ∀ j, VectorPolynomial K ℝ (V j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (V j)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (site : S → K → ℤ)
    (hfactor : ∀ j, i < j → ∃ M : (S → U j) →ₗ[ℝ] ℝ,
      ∀ q, DegreeLE (1 : K → ℕ) (j.val + 1) q →
        L j (map (U j).subtype q) = M (siteEvaluation (fun s k => (site s k : ℝ)) q))
    (Q : MvPolynomial (K × I) ℝ) (hQ : Q.totalDegree < i.val + 1)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ Q' : MvPolynomial (K × I) ℝ, Q'.totalDegree < i.val + 1 ∧
      ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
        layeredModeTestedPhase L p Q site test b =
          coefficientModeTestedPhase (L i) (p i) Q' site test' b := by
  let p' := fun j => restrictCoefficients (U j) (p j) (hm j)
  have hp' j : DegreeLE (1 : I → ℕ) (j.val + 1) (p' j) :=
    degreeLE_restrictCoefficients (U j) (p j) (hm j) (hp j)
  obtain ⟨Q', hQ', test', ht, he⟩ := exists_layered_mode_reduction i
    (fun j => (L j).comp (map (U j).subtype)) p' hp' site hfactor Q hQ test htest
  refine ⟨Q', hQ', test', ht, ?_⟩
  intro b
  simpa only [layeredModeTestedPhase_map, coefficientModeTestedPhase_map, p',
    map_restrictCoefficients] using he b

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators NNReal Classical

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

theorem cubeModePolynomialBudget_pos (q : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    0 < cubeModePolynomialBudget q L := by
  unfold cubeModePolynomialBudget
  positivity

theorem affineSite_intCast {K : Type*} {q : ℕ}
    (root : K → ℤ) (difference : Fin q → K → ℤ) (s : Finset (Fin q)) :
    (fun k => ((affineSite root difference s k : ℤ) : ℝ)) =
      affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s := by
  exact (affineSite_map (Int.castRingHom ℝ) root difference s).symm

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
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators NNReal

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

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators NNReal

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CubeModeUniformBudget
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Polynomial

noncomputable def cubeInputLogPolynomial (q : ℕ) : Polynomial ℕ :=
  X + C q.factorial + C (2 + q * (q + 1)) + C (q + 2) * (X + 4)

theorem cubeInputLogPolynomial_ge (q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    P ≤ (cubeInputLogPolynomial q).eval₂ (Nat.castRingHom ℝ) P := by
  have hrest := natPolynomial_eval_nonneg
    (C q.factorial + C (2 + q * (q + 1)) + C (q + 2) * (X + 4)) hP
  simpa [cubeInputLogPolynomial, add_assoc] using le_add_of_nonneg_right hrest (a := P)

theorem cubeModePolynomialBudget_le_exp_input (q : ℕ) {P L : ℝ}
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hLP : L ≤ Real.exp P) :
    cubeModePolynomialBudget q L ≤ Real.exp ((cubeInputLogPolynomial q).eval₂ (Nat.castRingHom ℝ) P) := by
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have h3L : 3 * L ≤ Real.exp (P + 3) := by
    calc
      _ ≤ Real.exp 3 * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hbase : 1 + 3 * L ≤ Real.exp (P + 4) := by
    convert one_add_le_exp_succ (by positivity) h3L using 1
    congr 1
    ring
  have hf : (q.factorial : ℝ) ≤ Real.exp (q.factorial : ℝ) := by
    linarith [Real.add_one_le_exp (q.factorial : ℝ)]
  have ha : 2 + (q : ℝ) * (q + 1) ≤ Real.exp (2 + (q : ℝ) * (q + 1)) := by
    linarith [Real.add_one_le_exp (2 + (q : ℝ) * (q + 1))]
  unfold cubeModePolynomialBudget
  calc
    _ ≤ Real.exp (q.factorial : ℝ) * Real.exp (2 + (q : ℝ) * (q + 1)) *
        (Real.exp (P + 4)) ^ (q + 2) := by gcongr
    _ = Real.exp ((q.factorial : ℝ) + (2 + (q : ℝ) * (q + 1)) + (q + 2 : ℕ) * (P + 4)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      simp [cubeInputLogPolynomial]
      linarith

theorem exists_cube_mode_threshold_exp_budget (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F L S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ L → L ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeRemovalSideThreshold m d (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K₀, _, hthreshold⟩ := exists_mode_threshold_exp_budget m
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget ((cubeInputLogPolynomial q + C K₀) ^ K₀)
  refine ⟨K, hK, ?_⟩
  intro n d P F L S ρ ε hP hn hd hF hFP hL hLP hS hSP hρ hρP hε hεP
  let P' := (cubeInputLogPolynomial q).eval₂ (Nat.castRingHom ℝ) P
  have hPP : P ≤ P' := cubeInputLogPolynomial_ge q hP
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  obtain ⟨hs, hr⟩ := hthreshold n d P' F (cubeModePolynomialBudget q L) S ρ ε
    (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hF (hFP.trans hEP)
    (cubeModePolynomialBudget_pos q hL).le (cubeModePolynomialBudget_le_exp_input q hP hL hLP)
    hS (hSP.trans hEP) hρ (hρP.trans hEP) hε (hεP.trans hEP)
  have hb : (P' + K₀) ^ K₀ ≤ (P + K) ^ K := by
    simpa [P', Polynomial.eval₂_pow] using hpoly P hP
  exact ⟨hs.trans (Real.exp_le_exp.mpr hb), hr.trans (Real.exp_le_exp.mpr hb)⟩

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LayeredFourierCharacter
namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

noncomputable def layeredCoefficientCharacter {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) : ℂ :=
  character (((∑ j, L j (substitute (fun u => rowPolynomial (fun k => b k u)) (p j))) : ℝ) :
    CircleFourier.Circle)

noncomputable def layeredSiteWeight {I K S : Type*} [Fintype K] [Fintype S]
    (Q : MvPolynomial (K × I) ℝ) (site : S → K → ℤ)
    (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) : ℂ :=
  character ((MvPolynomial.eval (fun z => b z.1 z.2) Q : ℝ) : CircleFourier.Circle) *
    ∏ s, test s (integerSiteValue (site s) b)

theorem layeredCoefficientCharacter_norm {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) :
    ‖layeredCoefficientCharacter L p b‖ = 1 := norm_character _

theorem layeredSiteWeight_norm_le {I K S : Type*} [Fintype K] [Fintype S]
    (Q : MvPolynomial (K × I) ℝ) (site : S → K → ℤ)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) (b : K → I → ℝ) :
    ‖layeredSiteWeight Q site test b‖ ≤ 1 := by
  rw [layeredSiteWeight, norm_mul, norm_character, one_mul, norm_prod]
  exact Finset.prod_le_one (fun s _ => norm_nonneg _) (fun s _ => htest s _)

theorem layeredModeTestedPhase_eq_weight_mul {I K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (Q : MvPolynomial (K × I) ℝ)
    (site : S → K → ℤ) (test : S → (I → ℝ) → ℂ) (b : K → I → ℝ) :
    layeredModeTestedPhase L p Q site test b =
      layeredSiteWeight Q site test b * layeredCoefficientCharacter L p b := by
  unfold layeredModeTestedPhase layeredSiteWeight layeredCoefficientCharacter
  rw [AddCircle.coe_add, character_add]
  ring

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

theorem layeredModeTestedPhase_empty_zero {I K : Type*} [Fintype K] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j)) (b : K → I → ℝ) :
    layeredModeTestedPhase L p 0 (Empty.elim : Empty → K → ℤ) Empty.elim b =
      layeredCoefficientCharacter L p b := by
  simp [layeredModeTestedPhase, layeredCoefficientCharacter]

theorem exists_affine_coefficient_local_removal {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) {C : ℝ}
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m, ((i.val + 1).factorial : ℝ) * C ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
    {β : ℝ} (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ∃ i : Fin m, ∃ rows : Fin (i.val + 1) → Option K → ℤ,
      (∀ a k, |(rows a k : ℝ)| ≤ 1) ∧
      ∀ base : Option K → I → ℝ,
        ‖𝔼 x : Fin (i.val + 1) → ∀ j, Fin (N j),
          layeredCoefficientCharacter
            (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
            p (rowShiftedTuple base rows
              (fun (y : ∀ j, Fin (N j)) j => (stride j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ β := by
  classical
  let L := fun j => coefficientFunctional (fun d a => (frequency j d a : ℝ))
  let site : Empty → K → ℝ := Empty.elim
  have hf (i : Fin m) := homogeneous_empty_factorization_iff
    ((affineModeLift (L i)).comp (map (U i).subtype)) (i.val + 1)
    (fun s (k : Option K) => k.elim 1 (site s))
  have hbad' : ∃ i, ¬∃ M : (Empty → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P → affineModeLift (L i) (map (U i).subtype P) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) P) := by
    obtain ⟨i, P, hP, hn⟩ := hbad
    exact ⟨i, fun h => hn ((hf i).mp h P hP)⟩
  obtain ⟨i, hi, hfactor⟩ := exists_highest_affine_subspace_nonfactor U site L hbad'
  have hn := mt (hf i).mpr hi
  simp only [not_forall, LinearMap.comp_apply] at hn
  obtain ⟨P, hP, hnP⟩ := hn
  obtain ⟨rows, hrows, hcontract, hnonzero⟩ := exists_unit_integer_mode_rows (U i)
    (affineLiftFrequency (frequency i)) (affineLiftFrequency_bound _ (hbound i))
    (by exact ⟨P, hP, by simpa only [L, affineModeLift_integerFrequency] using hnP⟩)
  have hsite : (fun (s : Empty) (k : Option K) => (((Empty.elim s : Option K → ℤ) k : ℤ) : ℝ)) =
      (fun s (k : Option K) => k.elim 1 (site s)) := Subsingleton.elim _ _
  obtain ⟨Q', hQ', test', ht, he⟩ := exists_subspace_layered_mode_reduction i U
    (fun j => affineModeLift (L j)) p hm hp (Empty.elim : Empty → Option K → ℤ)
    (by rw [hsite]; exact hfactor) 0 (by simp) Empty.elim (fun s => s.elim)
  have he' (b : Option K → I → ℝ) :
      layeredCoefficientCharacter (fun j => affineModeLift (L j)) p b =
        coefficientModeTestedPhase
          (coefficientFunctional (fun d a => ((affineLiftFrequency (frequency i) d a : ℤ) : ℝ)))
          (p i) Q' Empty.elim test' b := by
    simpa only [layeredModeTestedPhase_empty_zero, L, affineModeLift_integerFrequency] using he b
  refine ⟨i, rows, hrows, ?_⟩
  intro base
  change ‖𝔼 x : Fin (i.val + 1) → ∀ j, Fin (N j),
    layeredCoefficientCharacter (fun j => affineModeLift (L j)) p
      (rowShiftedTuple base rows
        (fun (y : ∀ j, Fin (N j)) j => (stride j : ℝ) * ((y j).val : ℝ)) x)‖ ≤ β
  simp_rw [he']
  exact inhomogeneous_coefficient_mode_local_removal (affineLiftFrequency (frequency i)) rows
    (p i) (hp i) (U i) N stride hs hζ (hN i) H hH hA hscale (hrank i)
    hcontract (hrowBudget i) hnonzero (hdenom i) (hcoeff i)
    Empty.elim (fun s => s.elim) Q' hQ' test' ht hβ (hpower i) base

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem affine_coefficient_mode_residue_removal_lipschitz_amplitude {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) {C : ℝ}
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m, ((i.val + 1).factorial : ℝ) * C ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
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
      ((i.val + 1 : ℕ) : ℝ) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1)))
    (F : (Option K × I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (residueLatticeArray residue stride z t : ℝ) / V t) *
        layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ)))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + (Lip : ℝ) * r + β := by
  obtain ⟨i, rows, hrows, hlocal⟩ := exists_affine_coefficient_local_removal
    U frequency hbound hbad p hp hm N stride hs hζ hN
    H hH hA hscale hrank hrowBudget hdenom hcoeff hβ hpower
  have hNp k : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos i.val hζ).trans_le (hN i k)
  exact residue_smooth_row_shift_transfer_lipschitz_amplitude N stride hNp hs rows residue V hV hZ hV1
    hδ hδ1 hmesh hsmall zero_le_one hrows hr (by simpa only [mul_one] using hmove i)
    _ (fun b => (layeredCoefficientCharacter_norm _ p b).le) hlocal F hF hLip

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem affine_coefficient_mode_residue_removal {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) {C : ℝ}
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (N stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R : ℝ} (hζ : 0 < ζ) (hN : ∀ i : Fin m, ∀ k, multiaffineBiasBudget i.val ζ ≤ N k)
    (H : I → ℝ) (hH : ∀ k, 0 < H k) {A : ℝ} (hA : 0 ≤ A)
    (hscale : ∀ k, H k ≤ A * ((stride k : ℝ) * (N k : ℝ)))
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hrowBudget : ∀ i : Fin m, ((i.val + 1).factorial : ℝ) * C ≤ R)
    (hdenom : ∀ i : Fin m, (∏ j : Fin (i.val + 1) → I,
      (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤ R)
    (hcoeff : ∀ i : Fin m, (Fintype.card I : ℝ) ^ (i.val + 1) *
      (A ^ (i.val + 1) * multiaffineBiasBudget i.val ζ) ≤ R)
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
      ((i.val + 1 : ℕ) : ℝ) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  obtain ⟨i, rows, hrows, hlocal⟩ := exists_affine_coefficient_local_removal
    U frequency hbound hbad p hp hm N stride hs hζ hN
    H hH hA hscale hrank hrowBudget hdenom hcoeff hβ hpower
  have hNp k : 0 < N k := by
    exact_mod_cast (multiaffineBiasBudget_pos i.val hζ).trans_le (hN i k)
  exact residue_smooth_row_shift_transfer N stride hNp hs rows residue V hV hZ hV1
    hδ hδ1 hmesh hsmall zero_le_one hrows hr (by simpa only [mul_one] using hmove i)
    _ (fun b => (layeredCoefficientCharacter_norm _ p b).le) hlocal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

def affineCoefficientModeTrivial {K : Type*} {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : Prop :=
  ∀ j, ∀ P, Homogeneous (j.val + 1) P →
    affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
      (map (U j).subtype P) = 0

theorem not_affineCoefficientModeTrivial_iff {K : Type*} {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    ¬affineCoefficientModeTrivial U frequency ↔
      ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
          (map (U i).subtype P) ≠ 0 := by
  simp only [affineCoefficientModeTrivial, not_forall, exists_prop]

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

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem affine_coefficient_residue_removal_of_widths_lipschitz_amplitude {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R T S : ℝ} (hζ : 0 < ζ) (hT : 0 < T) (hS : 0 ≤ S)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (hH : ∀ k, 0 < H k)
    (hsize : ∀ k, (stride k : ℝ) * T * (finiteLayerBiasBudget m ζ + 1) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : layerRemovalRankBudget m (Fintype.card I) C 1
      (finiteLayerBiasBudget m ζ) (2 * T) S ≤ R)
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
    (hmove : (m : ℝ) * 1 ≤ r * ρ * T)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1)))
    (F : (Option K × I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    {Lip : ℝ≥0} (hLip : LipschitzWith Lip F) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      (F (fun t => (residueLatticeArray residue stride z t : ℝ) / V t) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ)))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + (Lip : ℝ) * r + β := by
  classical
  let B := finiteLayerBiasBudget m ζ
  let D : ℝ := 1
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m hζ
  have hD : 0 ≤ D := zero_le_one
  have hA : 0 ≤ 2 * T := by positivity
  have hb (i : Fin m) : multiaffineBiasBudget i.val ζ ≤ B :=
    multiaffineBiasBudget_le_finite i hζ
  obtain ⟨N, hN, hscale, hshift⟩ := exists_mode_shift_lengths m hT hB hρ hr hmove H stride hs hsize V hwidth
  have hbud (i : Fin m) := layerRemovalRankBudget_bounds i (Fintype.card I) hC hD
    (zero_le_one.trans hB) hA hS
  apply affine_coefficient_mode_residue_removal_lipschitz_amplitude U frequency hbound hbad
    p hp hm N stride hs hζ (fun i k => (hb i).trans (hN k)) H hH hA hscale hrank
    (fun i => by simpa only [D, one_pow, mul_one] using (hbud i).1.trans hR) _ _ residue V hV hZ hV1 hδ hδ1 hmesh hsmall hr _ hβ hpower F hF hLip
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
    have hs' : (m : ℝ) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z := by
      simpa only [mul_one] using hshift z
    exact (mul_le_mul_of_nonneg_right hi
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans hs'

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

theorem affine_coefficient_residue_removal_of_widths {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i : Fin m, ∃ P, Homogeneous (i.val + 1) P ∧
      affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ)))
        (map (U i).subtype P) ≠ 0)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R T S : ℝ} (hζ : 0 < ζ) (hT : 0 < T) (hS : 0 ≤ S)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (hH : ∀ k, 0 < H k)
    (hsize : ∀ k, (stride k : ℝ) * T * (finiteLayerBiasBudget m ζ + 1) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : layerRemovalRankBudget m (Fintype.card I) C 1
      (finiteLayerBiasBudget m ζ) (2 * T) S ≤ R)
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
    (hmove : (m : ℝ) * 1 ≤ r * ρ * T)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((residueSmoothIndexPMF residue stride hs V hV hZ z).toReal : ℂ) *
      layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p (fun k j => (residueLatticeArray residue stride z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  let B := finiteLayerBiasBudget m ζ
  let D : ℝ := 1
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m hζ
  have hD : 0 ≤ D := zero_le_one
  have hA : 0 ≤ 2 * T := by positivity
  have hb (i : Fin m) : multiaffineBiasBudget i.val ζ ≤ B :=
    multiaffineBiasBudget_le_finite i hζ
  obtain ⟨N, hN, hscale, hshift⟩ := exists_mode_shift_lengths m hT hB hρ hr hmove H stride hs hsize V hwidth
  have hbud (i : Fin m) := layerRemovalRankBudget_bounds i (Fintype.card I) hC hD
    (zero_le_one.trans hB) hA hS
  apply affine_coefficient_mode_residue_removal U frequency hbound hbad
    p hp hm N stride hs hζ (fun i k => (hb i).trans (hN k)) H hH hA hscale hrank
    (fun i => by simpa only [D, one_pow, mul_one] using (hbud i).1.trans hR) _ _ residue V hV hZ hV1 hδ hδ1 hmesh hsmall hr _ hβ hpower
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
    have hs' : (m : ℝ) * ((stride z.2 : ℝ) * (N z.2 : ℝ)) ≤ r * V z := by
      simpa only [mul_one] using hshift z
    exact (mul_le_mul_of_nonneg_right hi
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans hs'

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedCoefficientExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem degreeLE_monomial_of_degree_le {K W : Type*} [AddCommGroup W] [Module ℝ W]
    {d : K →₀ ℕ} {h : ℕ} (hd : d.degree ≤ h) (w : W) :
    DegreeLE (1 : K → ℕ) h (monomial (R := ℝ) d w) := by
  classical
  intro e he
  rw [coefficients_monomial]
  by_cases hed : e = d
  · subst e
    have hh : h < d.degree := by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using he
    exact False.elim ((not_lt_of_ge hd) hh)
  · simp [Ne.symm hed]

theorem affineModeLift_zero_iff_bounded {K W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (h : ℕ) :
    (∀ P, Homogeneous h P → affineModeLift L P = 0) ↔
      ∀ P, DegreeLE (1 : K → ℕ) h P → L P = 0 := by
  simpa only [affineModeLift, LinearMap.comp_apply, LinearMap.zero_apply] using
    homogeneous_site_factorization_iff h (Empty.elim : Empty → K → ℝ) L
      (0 : (Empty → W) →ₗ[ℝ] ℝ)

theorem coefficientArrayFunctional_eq_zero_iff_trivial {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    coefficientArrayFunctional U frequency = 0 ↔ affineCoefficientModeTrivial U frequency := by
  rw [coefficientArrayFunctional_eq_zero_iff]
  constructor
  · intro hz j P hP
    by_contra hn
    have hn' : coefficientFunctional
        (fun d a => ((affineLiftFrequency (frequency j) d a : ℤ) : ℝ)) (map (U j).subtype P) ≠ 0 := by
      rwa [← affineModeLift_integerFrequency]
    obtain ⟨d, hd, w, hw⟩ := exists_restricted_coefficient_nonzero (U j)
      (affineLiftFrequency (frequency j)) ⟨P, hP, hn'⟩
    exact hw (hz ⟨j, ⟨d.some, (some_degree_le d).trans hd.le⟩⟩ w)
  · intro hz s w
    let L := (coefficientFunctional (fun d a => (frequency s.1 d a : ℝ))).comp (map (U s.1).subtype)
    have hlift : ∀ P, Homogeneous (s.1.val + 1) P → affineModeLift L P = 0 := by
      simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply] using hz s.1
    have he := (affineModeLift_zero_iff_bounded L (s.1.val + 1)).mp hlift
      (monomial s.2.val w) (degreeLE_monomial_of_degree_le s.2.property w)
    simpa only [L, LinearMap.comp_apply, map_monomial, Submodule.subtype_apply,
      coefficientFunctional_monomial] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem sum_bounded_monomial_coefficients {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ}
    (p : VectorPolynomial K ℝ W) (hp : DegreeLE (1 : K → ℕ) h p) :
    (∑ d : BoundedCoefficientExponent K h, monomial d.val (coefficients p d.val)) = p := by
  apply coefficients.injective
  ext e
  simp only [map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  by_cases he : e.degree ≤ h
  · rw [Finset.sum_eq_single (⟨e, he⟩ : BoundedCoefficientExponent K h)]
    · simp
    · intro d _ hd
      have hde : d.val ≠ e := fun h => hd (Subtype.ext h)
      simp [hde]
    · simp
  · have hz : coefficients p e = 0 := hp e (by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using lt_of_not_ge he)
    rw [hz]
    apply Finset.sum_eq_zero
    intro d _
    have hde : d.val ≠ e := fun h => he (h ▸ d.property)
    simp [hde]

theorem coefficientFunctional_bounded_expansion {K J : Type*} [Fintype K] [Fintype J]
    (frequency : (K →₀ ℕ) → J → ℝ) {h : ℕ}
    (p : VectorPolynomial K ℝ (J → ℝ)) (hp : DegreeLE (1 : K → ℕ) h p) :
    coefficientFunctional frequency p =
      ∑ d : BoundedCoefficientExponent K h, ∑ a, frequency d.val a * coefficients p d.val a := by
  conv_lhs => rw [← sum_bounded_monomial_coefficients p hp]
  simp only [map_sum, coefficientFunctional_monomial]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedArrayPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def boundedArrayPolynomial {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (x : BoundedCoefficientExponent K h → W) :
    VectorPolynomial K ℝ W := ∑ d, monomial d.val (x d)

theorem boundedArrayPolynomial_degreeLE {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (x : BoundedCoefficientExponent K h → W) :
    DegreeLE (1 : K → ℕ) h (boundedArrayPolynomial h x) := by
  intro e he
  rw [boundedArrayPolynomial, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro d _
  exact degreeLE_monomial_of_degree_le d.property (x d) e he

theorem boundedArrayPolynomial_coeff {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (x : BoundedCoefficientExponent K h → W)
    (d : BoundedCoefficientExponent K h) :
    coefficients (boundedArrayPolynomial h x) d.val = x d := by
  simp only [boundedArrayPolynomial, map_sum, Finsupp.finsetSum_apply, coefficients_monomial]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e _ hed
    have he : e.val ≠ d.val := fun h => hed (Subtype.ext h)
    simp [he]
  · simp

theorem boundedArrayPolynomial_reconstruct {K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ} (p : VectorPolynomial K ℝ W)
    (hp : DegreeLE (1 : K → ℕ) h p) :
    boundedArrayPolynomial h (fun d => coefficients p d.val) = p :=
  sum_bounded_monomial_coefficients p hp

theorem coefficientFunctional_boundedArrayPolynomial {K J : Type*} [Fintype K] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (frequency : (K →₀ ℕ) → J → ℝ)
    (x : BoundedCoefficientExponent K h → U) :
    coefficientFunctional frequency (map U.subtype (boundedArrayPolynomial h x)) =
      subspaceArrayFunctional U (fun d a => frequency d.val a) x := by
  simp only [boundedArrayPolynomial, map_sum, map_monomial, coefficientFunctional_monomial]
  rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def boundedSiteMatrix {K S : Type*} (h : ℕ) (site : S → K → ℤ) :
    Matrix S (BoundedCoefficientExponent K h) ℤ :=
  fun s d => d.val.prod (fun k n => site s k ^ n)

theorem siteEvaluation_boundedArrayPolynomial {K S W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (site : S → K → ℤ)
    (x : BoundedCoefficientExponent K h → W) :
    siteEvaluation (fun s k => (site s k : ℝ)) (boundedArrayPolynomial h x) =
      matrixModuleAction (fun s d => (boundedSiteMatrix h site s d : ℝ)) x := by
  funext s
  change eval (fun k => (site s k : ℝ)) (boundedArrayPolynomial h x) =
    ∑ d : BoundedCoefficientExponent K h, (boundedSiteMatrix h site s d : ℝ) • x d
  simp only [boundedArrayPolynomial, map_sum, eval_monomial,
    boundedSiteMatrix, Finsupp.prod, Int.cast_prod, Int.cast_pow]

theorem siteEvaluation_bounded_coefficients {K S W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W] {h : ℕ} (site : S → K → ℤ)
    (p : VectorPolynomial K ℝ W) (hp : DegreeLE (1 : K → ℕ) h p) :
    siteEvaluation (fun s k => (site s k : ℝ)) p =
      matrixModuleAction (fun s d => (boundedSiteMatrix h site s d : ℝ))
        (fun d => coefficients p d.val) := by
  rw [← boundedArrayPolynomial_reconstruct p hp, siteEvaluation_boundedArrayPolynomial]
  simp only [boundedArrayPolynomial_coeff]

theorem bounded_site_factorization_to_array {K S J : Type*} [Fintype K] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (site : S → K → ℤ)
    (frequency : (K →₀ ℕ) → J → ℝ) (M : (S → U) →ₗ[ℝ] ℝ)
    (hf : ∀ p : VectorPolynomial K ℝ U, DegreeLE (1 : K → ℕ) h p →
      coefficientFunctional frequency (map U.subtype p) = M (siteEvaluation (fun s k => (site s k : ℝ)) p)) :
    ∀ x, subspaceArrayFunctional U (fun d : BoundedCoefficientExponent K h => frequency d.val) x =
      M (matrixModuleAction (fun s d => (boundedSiteMatrix h site s d : ℝ)) x) := by
  intro x
  have he := hf (boundedArrayPolynomial h x) (boundedArrayPolynomial_degreeLE h x)
  rwa [coefficientFunctional_boundedArrayPolynomial, siteEvaluation_boundedArrayPolynomial] at he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def booleanJetExtractionMatrix {α O : Type*} [DecidableEq α]
    (rows : O → Finset α) : Matrix O (Finset α) ℤ :=
  fun o t => if t ⊆ rows o then (-1 : ℤ) ^ (rows o \ t).card else 0

theorem booleanJetExtractionMatrix_mulVec {α O : Type*} [Fintype α] [DecidableEq α]
    (rows : O → Finset α) (f : Finset α → ℤ) (o : O) :
    (booleanJetExtractionMatrix rows *ᵥ f) o = booleanCoefficient f (rows o) := by
  classical
  change (∑ t, (if t ⊆ rows o then (-1 : ℤ) ^ (rows o \ t).card else 0) * f t) = _
  simp only [ite_mul, zero_mul, ← Finset.sum_filter]
  have hsets : Finset.univ.filter (fun t : Finset α => t ⊆ rows o) = (rows o).powerset := by
    ext t
    simp
  rw [hsets]
  rfl

def boundedCoefficientIntegerExponentEquiv (K : Type*) (h : ℕ) :
    VectorPolynomial.BoundedCoefficientExponent K h ≃ BoundedIntegerExponent K h where
  toFun e := ⟨e.val, e.property⟩
  invFun e := ⟨e.val, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def boundedCoefficientJetMatrix {α K O : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α) :
    Matrix O (VectorPolynomial.BoundedCoefficientExponent K h) ℤ :=
  fun o e => boundedDegreeIntegerJetMatrix root D h rows o
    (boundedCoefficientIntegerExponentEquiv K h e)

theorem booleanJetExtractionMatrix_mul_boundedSite {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α) :
    booleanJetExtractionMatrix rows *
        VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) =
      boundedCoefficientJetMatrix root D h rows := by
  ext o e
  change (booleanJetExtractionMatrix rows *ᵥ
    (fun t => VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) t e)) o = _
  rw [booleanJetExtractionMatrix_mulVec]
  change booleanCoefficient _ (rows o) = booleanCoefficient _ (rows o)
  congr 1
  funext t
  simp [VectorPolynomial.boundedSiteMatrix, MvPolynomial.eval_monomial, Finsupp.prod,
    boundedCoefficientIntegerExponentEquiv]

theorem boundedCoefficientJetMatrix_period {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (h : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    integerScalarLattice O (a ^ h) ≤ (boundedCoefficientJetMatrix root D h rows).mulVecLin.range := by
  intro y hy
  obtain ⟨x, hx⟩ := boundedDegreeIntegerJetMatrix_period root D a hperiod h rows hinj hdegree hy
  let e := boundedCoefficientIntegerExponentEquiv K h
  refine ⟨fun d => x (e d), ?_⟩
  ext o
  change (∑ d, boundedCoefficientJetMatrix root D h rows o d * x (e d)) = y o
  calc
    _ = ∑ d, boundedDegreeIntegerJetMatrix root D h rows o d * x d :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = y o := congrFun hx o

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

def coefficientIntegerLattice {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) : AddSubgroup (CoefficientArray (K := K) U) where
  carrier := {x | ∀ s a, ∃ n : ℤ, (x s).val a = n}
  zero_mem' s a := ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy s a
    obtain ⟨n, hn⟩ := hx s a
    obtain ⟨m, hm⟩ := hy s a
    refine ⟨n + m, ?_⟩
    change (x s).val a + (y s).val a = ((n + m : ℤ) : ℝ)
    rw [hn, hm, Int.cast_add]
  neg_mem' := by
    intro x hx s a
    obtain ⟨n, hn⟩ := hx s a
    refine ⟨-n, ?_⟩
    change -(x s).val a = ((-n : ℤ) : ℝ)
    rw [hn, Int.cast_neg]

abbrev CoefficientTorus {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :=
  CoefficientArray (K := K) U ⧸ coefficientIntegerLattice U

theorem coefficientArrayFunctional_integral {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    ∃ n : ℤ, coefficientArrayFunctional U frequency x = n := by
  change ∀ s a, ∃ n : ℤ, (x s).val a = n at hx
  choose z hz using hx
  refine ⟨∑ s : CoefficientSlot K m, ∑ a, frequency s.1 s.2.val a * z s a, ?_⟩
  change (∑ s : CoefficientSlot K m, ∑ a, (frequency s.1 s.2.val a : ℝ) * (x s).val a) = _
  simp only [hz, Int.cast_sum, Int.cast_mul]

noncomputable def coefficientTorusCharacter {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    CoefficientTorus (K := K) U → ℂ :=
  quotientLinearCharacter (coefficientIntegerLattice U) (coefficientArrayFunctional U frequency)
    (coefficientArrayFunctional_integral U frequency)

theorem coefficientTorusCharacter_mk {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientArray (K := K) U) :
    coefficientTorusCharacter U frequency (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) =
      CircleFourier.character (coefficientArrayFunctional U frequency x : CircleFourier.Circle) := rfl

theorem coefficientTorusCharacter_integrable {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ] :
    Integrable (coefficientTorusCharacter U frequency) μ :=
  quotientLinearCharacter_integrable _ _ _
    (coefficientArrayFunctional U frequency).continuous_of_finiteDimensional μ

theorem coefficientTorusCharacter_integral {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [MeasurableAdd₂ (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, coefficientTorusCharacter U frequency x ∂μ) =
      if affineCoefficientModeTrivial U frequency then 1 else 0 := by
  rw [coefficientTorusCharacter, quotientLinearCharacter_integral,
    coefficientArrayFunctional_eq_zero_iff_trivial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

abbrev CoefficientCoordinateTori {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :=
  ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1)

def coefficientCoordinateArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (s : CoefficientSlot K m) :
    CoefficientArray (K := K) U →ₗ[ℝ] (Unit → U s.1) where
  toFun x _ := x s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficientCoordinateTorus {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    CoefficientTorus (K := K) U →+ CoefficientCoordinateTori (K := K) U :=
  AddMonoidHom.pi (fun s => QuotientAddGroup.map (coefficientIntegerLattice U)
    (subspaceArrayIntegerLattice Unit (U s.1)) (coefficientCoordinateArray U s).toAddMonoidHom
    (fun _x hx _ a => hx s a))

theorem coefficientCoordinateTorus_mk {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientArray (K := K) U)
    (s : CoefficientSlot K m) :
    coefficientCoordinateTorus U (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) s =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U s.1)) (fun _ => x s) := rfl

theorem coefficientCoordinateTorus_surjective {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Function.Surjective (coefficientCoordinateTorus (K := K) U) := by
  intro y
  choose v hv using fun s => QuotientAddGroup.mk'_surjective
    (subspaceArrayIntegerLattice Unit (U s.1)) (y s)
  refine ⟨QuotientAddGroup.mk' (coefficientIntegerLattice U) (fun s => v s ()), ?_⟩
  funext s
  rw [coefficientCoordinateTorus_mk]
  have he : (fun _ : Unit => v s ()) = v s := funext (fun u => by cases u; rfl)
  rw [he, hv s]

theorem coefficientCoordinateTorus_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Continuous (coefficientCoordinateTorus (K := K) U) := by
  apply continuous_pi
  intro s
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (coefficientCoordinateArray U s).continuous_of_finiteDimensional

theorem coefficientCoordinateTori_compact {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)] :
    CompactSpace (CoefficientCoordinateTori (K := K) U) := by
  have h := isCompact_univ.image (coefficientCoordinateTorus_continuous (K := K) U)
  rw [Set.image_univ, Set.range_eq_univ.mpr (coefficientCoordinateTorus_surjective U)] at h
  exact ⟨h⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def coefficientLayerArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    CoefficientArray (K := K) U →ₗ[ℝ] (BoundedCoefficientExponent K (j.val + 1) → U j) where
  toFun x d := x ⟨j, d⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficientLayerArray_preserves_lattice {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    coefficientLayerArray U j x ∈ subspaceArrayIntegerLattice
      (BoundedCoefficientExponent K (j.val + 1)) (U j) := fun d a => hx ⟨j, d⟩ a

def coefficientLayerTorus {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    CoefficientTorus (K := K) U →+
      SubspaceArrayTorus (BoundedCoefficientExponent K (j.val + 1)) (U j) :=
  QuotientAddGroup.map (coefficientIntegerLattice U)
    (subspaceArrayIntegerLattice (BoundedCoefficientExponent K (j.val + 1)) (U j))
    (coefficientLayerArray U j).toAddMonoidHom (coefficientLayerArray_preserves_lattice U j)

theorem coefficientLayerTorus_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (j : Fin m) :
    Continuous (coefficientLayerTorus (K := K) U j) := by
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (coefficientLayerArray U j).continuous_of_finiteDimensional

end Erdos3.VectorPolynomial

end

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

theorem coefficientTorus_compact_of_basis {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (b : ∀ j, Basis (B j) ℝ (U j))
    (hb : ∀ j i a, ∃ n : ℤ, (b j i).val a = n) :
    CompactSpace (CoefficientTorus (K := K) U) := by
  classical
  apply compact_quotient_of_integral_basis (coefficientIntegerLattice U)
    (Pi.basis (fun s : CoefficientSlot K m => b s.1))
  rintro ⟨s, i⟩ t a
  simp only [Pi.basis_apply]
  by_cases hts : t = s
  · subst t
    simpa only [Pi.single_eq_same] using hb s.1 i a
  · exact ⟨0, by simp [Pi.single_eq_of_ne hts]⟩

noncomputable def coefficientTorusHaar {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (b : ∀ j, Basis (B j) ℝ (U j))
    (hb : ∀ j i a, ∃ n : ℤ, (b j i).val a = n) : Measure (CoefficientTorus (K := K) U) := by
  letI := coefficientTorus_compact_of_basis (K := K) U b hb
  exact probabilityAddHaar _

instance coefficientTorusHaar_probability {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (b : ∀ j, Basis (B j) ℝ (U j))
    (hb : ∀ j i a, ∃ n : ℤ, (b j i).val a = n) :
    IsProbabilityMeasure (coefficientTorusHaar (K := K) U b hb) := by
  let _ := coefficientTorus_compact_of_basis (K := K) U b hb
  exact probabilityAddHaar_probability _

instance coefficientTorusHaar_invariant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    {B : Fin m → Type*} [∀ j, Fintype (B j)]
    (b : ∀ j, Basis (B j) ℝ (U j))
    (hb : ∀ j i a, ∃ n : ℤ, (b j i).val a = n) :
    (coefficientTorusHaar (K := K) U b hb).IsAddLeftInvariant := by
  let _ := coefficientTorus_compact_of_basis (K := K) U b hb
  exact probabilityAddHaar_invariant _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def affineSampleCoefficientArray {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (b : Option K → I → ℝ) : CoefficientArray (K := K) U :=
  fun s => coefficients (substitute (affineParameterSubstitution b)
    (restrictCoefficients (U s.1) (p s.1) (hm s.1))) s.2.val

theorem affineSampleCoefficientArray_val {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (b : Option K → I → ℝ) (s : CoefficientSlot K m) :
    (affineSampleCoefficientArray U p hm b s).val =
      coefficients (substitute (affineParameterSubstitution b) (p s.1)) s.2.val := by
  change (U s.1).subtype (coefficients _ s.2.val) = _
  rw [← coefficients_map, map_substitute, map_restrictCoefficients]

theorem coefficientArrayFunctional_sample {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    coefficientArrayFunctional U frequency (affineSampleCoefficientArray U p hm b) =
      ∑ j, affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ)))
        (substitute (fun u => rowPolynomial (fun k => b k u)) (p j)) := by
  change (∑ s : CoefficientSlot K m, ∑ a,
    (frequency s.1 s.2.val a : ℝ) * (affineSampleCoefficientArray U p hm b s).val a) = _
  simp only [affineSampleCoefficientArray_val, CoefficientSlot, Fintype.sum_sigma,
    affineModeLift_substitute]
  apply Finset.sum_congr rfl
  intro j _
  exact (coefficientFunctional_bounded_expansion (fun d a => (frequency j d a : ℝ)) (h := j.val + 1) _
    (degreeLE_substitute_affine _ (affineParameterSubstitution_degree b) (p j) (hp j))).symm

noncomputable def affineSampleCoefficientTorus {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (b : Option K → I → ℝ) : CoefficientTorus (K := K) U :=
  QuotientAddGroup.mk' (coefficientIntegerLattice U) (affineSampleCoefficientArray U p hm b)

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

section

namespace Erdos3

theorem integerMatrixTorusMap_continuous {I S J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) :
    Continuous (integerMatrixTorusMap U E) := by
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice I U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp
    (matrixModuleAction (W := U) (fun s i => (E s i : ℝ))).continuous_of_finiteDimensional

namespace VectorPolynomial

abbrev SiteTorus (S : Type*) {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) := ∀ j, SubspaceArrayTorus S (U j)

noncomputable def coefficientSiteTorusMap {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) :
    CoefficientTorus (K := K) U →+ SiteTorus S U :=
  AddMonoidHom.pi (fun j => (integerMatrixTorusMap (U j) (boundedSiteMatrix (j.val + 1) site)).comp
    (coefficientLayerTorus U j))

theorem coefficientSiteTorusMap_mk {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ)
    (x : CoefficientArray (K := K) U) (j : Fin m) :
    coefficientSiteTorusMap U site (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) j =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice S (U j))
        (matrixModuleAction (fun s d => (boundedSiteMatrix (j.val + 1) site s d : ℝ))
          (coefficientLayerArray U j x)) := rfl

theorem coefficientSiteTorusMap_continuous {K S : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) :
    Continuous (coefficientSiteTorusMap U site) :=
  continuous_pi (fun j => (integerMatrixTorusMap_continuous _ _).comp
    (coefficientLayerTorus_continuous U j))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def zeroCoefficientExponent (K : Type*) (h : ℕ) : BoundedCoefficientExponent K h :=
  ⟨0, by simp⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem matrixModuleAction_surjective_of_period {I S W : Type*}
    [Fintype I] [Fintype S] [AddCommGroup W] [Module ℝ W]
    (E : Matrix S I ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice S a ≤ E.mulVecLin.range) :
    Function.Surjective (matrixModuleAction (W := W) (fun s i => (E s i : ℝ))) := by
  classical
  obtain ⟨n, hn⟩ := exists_integer_kernel_dual E a hperiod
  let e : S → I → ℤ := E
  let A : Matrix S I ℝ := Matrix.of (fun s i => (e s i : ℝ))
  let T : Matrix I S ℝ := fun i s => (n s i : ℝ) / a
  have hET : A * T = 1 := by
    ext s r
    have hsum : (∑ i, (n r i : ℝ) * (e s i : ℝ)) = if r = s then (a : ℝ) else 0 := by
      exact_mod_cast hn r s
    change (∑ i, (e s i : ℝ) * ((n r i : ℝ) / a)) = _
    have hswap : (∑ i, (e s i : ℝ) * ((n r i : ℝ) / a)) =
        (∑ i, (n r i : ℝ) * (e s i : ℝ)) / a := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hswap, hsum]
    by_cases hrs : r = s
    · subst r
      simp [ha]
    · simp [hrs, Ne.symm hrs]
  intro y
  refine ⟨matrixModuleAction T y, ?_⟩
  change matrixModuleAction A (matrixModuleAction T y) = y
  calc
    _ = matrixModuleAction (A * T) y := matrixModuleAction_mul A T y
    _ = matrixModuleAction (1 : Matrix S S ℝ) y := congrArg (fun M => matrixModuleAction M y) hET
    _ = y := by ext s; simp [matrixModuleAction_apply, Matrix.one_apply]

theorem integerMatrixTorusMap_comp {I S T J : Type*}
    [Fintype I] [Fintype S] (U : Submodule ℝ (J → ℝ))
    (A : Matrix T S ℤ) (B : Matrix S I ℤ) (x : SubspaceArrayTorus I U) :
    integerMatrixTorusMap U A (integerMatrixTorusMap U B x) =
      integerMatrixTorusMap U (A * B) x := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
  have hcast : Matrix.of (fun t s => (A t s : ℝ)) *
      Matrix.of (fun s i => (B s i : ℝ)) =
      Matrix.of (fun t i => ((A * B) t i : ℝ)) := by
    ext t i
    simp [Matrix.mul_apply]
  exact congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice T U))
    ((matrixModuleAction_mul (Matrix.of (fun t s => (A t s : ℝ)))
      (Matrix.of (fun s i => (B s i : ℝ))) v).trans
      (congrArg (fun M => matrixModuleAction M v) hcast))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

abbrev BooleanJetTorus {m : ℕ} (O : Fin m → Type*) {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) := ∀ j, SubspaceArrayTorus (O j) (U j)

noncomputable def siteBooleanJetTorusMap {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {O J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (rows : ∀ j, O j → Finset α) : SiteTorus (Finset α) U →+ BooleanJetTorus O U where
  toFun x j := integerMatrixTorusMap (U j) (booleanJetExtractionMatrix (rows j)) (x j)
  map_zero' := funext (fun j => map_zero (integerMatrixTorusMap (U j) _))
  map_add' x y := funext (fun j => map_add (integerMatrixTorusMap (U j) _) (x j) (y j))

theorem siteBooleanJetTorusMap_continuous {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (rows : ∀ j, O j → Finset α) :
    Continuous (siteBooleanJetTorusMap U rows) :=
  continuous_pi (fun j => (integerMatrixTorusMap_continuous _ _).comp (continuous_apply j))

noncomputable def coefficientBooleanJetTorusMap {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) : CoefficientTorus (K := K) U →+ BooleanJetTorus O U :=
  (siteBooleanJetTorusMap U rows).comp (coefficientSiteTorusMap U (integerAffineCube root D))

theorem coefficientBooleanJetTorusMap_mk {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) (x : CoefficientArray (K := K) U) (j : Fin m) :
    coefficientBooleanJetTorusMap U root D rows
        (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) j =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice (O j) (U j))
        (matrixModuleAction
          (fun o e => (boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e : ℝ))
          (coefficientLayerArray U j x)) := by
  change integerMatrixTorusMap (U j) (booleanJetExtractionMatrix (rows j))
    (integerMatrixTorusMap (U j) (boundedSiteMatrix (j.val + 1) (integerAffineCube root D))
      (QuotientAddGroup.mk' _ (coefficientLayerArray U j x))) = _
  rw [integerMatrixTorusMap_comp, booleanJetExtractionMatrix_mul_boundedSite]
  rfl

theorem coefficientBooleanJetTorusMap_continuous {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α) :
    Continuous (coefficientBooleanJetTorusMap U root D rows) :=
  (siteBooleanJetTorusMap_continuous U rows).comp
    (coefficientSiteTorusMap_continuous U (integerAffineCube root D))

theorem coefficientBooleanJetTorusMap_surjective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1) :
    Function.Surjective (coefficientBooleanJetTorusMap U root D rows) := by
  intro y
  choose v hv using fun j => QuotientAddGroup.mk'_surjective
    (subspaceArrayIntegerLattice (O j) (U j)) (y j)
  choose c hc using fun j => matrixModuleAction_surjective_of_period (W := U j)
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) (a ^ (j.val + 1))
    (pow_ne_zero _ ha)
    (boundedCoefficientJetMatrix_period root D a hperiod (j.val + 1) (rows j)
      (hinj j) (hdegree j)) (v j)
  refine ⟨QuotientAddGroup.mk' (coefficientIntegerLattice U) (fun s => c s.1 s.2), ?_⟩
  funext j
  rw [coefficientBooleanJetTorusMap_mk]
  change QuotientAddGroup.mk' _ (matrixModuleAction _ (c j)) = y j
  rw [hc j, hv j]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev EuclideanJetLayers (O : Fin m → Type*) :=
  ∀ j : Fin m, O j → euclideanSubspace (U j) ⧸
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup

instance euclideanJetLayers_borel [∀ j, Fintype (O j)] : BorelSpace (EuclideanJetLayers U O) := by
  let : ∀ j, BorelSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  let : ∀ j, BorelSpace (O j → euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => Pi.borelSpace
  exact Pi.borelSpace

noncomputable def euclideanJetEquiv : BooleanJetTorus O U ≃+ EuclideanJetLayers U O where
  toFun x j o := (euclideanSubspaceTorusEquiv (U j)).symm (arrayCoordinateEquiv (U j) (x j) o)
  invFun y j := (arrayCoordinateEquiv (U j)).symm (fun o => euclideanSubspaceTorusEquiv (U j) (y j o))
  left_inv x := by
    funext j
    apply (arrayCoordinateEquiv (U j)).injective
    rw [AddEquiv.apply_symm_apply]
    funext o
    exact (euclideanSubspaceTorusEquiv (U j)).apply_symm_apply _
  right_inv y := by
    funext j o
    dsimp only
    rw [AddEquiv.apply_symm_apply]
    exact (euclideanSubspaceTorusEquiv (U j)).symm_apply_apply _
  map_add' x y := by
    funext j o
    simp only [map_add, Pi.add_apply]

theorem euclideanJetEquiv_continuous [∀ j, Fintype (O j)] :
    Continuous (euclideanJetEquiv (O := O) U) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro o
  exact (euclideanSubspaceTorusEquiv_symm_continuous (U j)).comp
    ((continuous_apply o).comp ((arrayCoordinateEquiv_continuous (U j)).comp (continuous_apply j)))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientProductHaar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

theorem coefficientCoordinateTorus_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ s : CoefficientSlot K m, MeasurableSpace (SubspaceArrayTorus Unit (U s.1))]
    [∀ s : CoefficientSlot K m, BorelSpace (SubspaceArrayTorus Unit (U s.1))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)] :
    MeasurePreserving (coefficientCoordinateTorus U) μ (Measure.pi ν) := by
  let _ := coefficientCoordinateTori_compact (K := K) U
  let _ : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let _ : (Measure.pi ν).IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := Measure.pi ν) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving (coefficientCoordinateTorus_continuous U)
    (coefficientCoordinateTorus_surjective U) (by simp)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanJetHighDegree
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem normalSpan_high_jet_zero {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P ∈ normalSpan h)
    (s : Finset α) (hs : h < s.card) :
    booleanCoefficient (fun t => eval (site t) P) s = 0 := by
  change ((coefficientLinear s).comp siteEvaluation) P = 0
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨t, ht, rfl⟩ := hP
    change booleanCoefficient (fun u => eval (site u) (normalMonomial h t)) s = 0
    rw [normalMonomial_jet, if_neg]
    intro he
    subst t
    omega
  | zero => exact map_zero _
  | add P Q _ _ hP hQ => rw [map_add, hP, hQ, add_zero]
  | smul a P _ hP => rw [map_smul, hP, smul_zero]

theorem homogeneous_high_jet_zero {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P.IsHomogeneous h)
    (s : Finset α) (hs : h < s.card) :
    booleanCoefficient (fun t => eval (site t) P) s = 0 := by
  obtain ⟨A, hA, B, hB, rfl⟩ := Submodule.mem_sup.mp (homogeneous_mem_reductionSpace hP)
  simp_rw [map_add, vanishingSpan_eval_zero hA, zero_add]
  exact normalSpan_high_jet_zero hB s hs

theorem frameLift_eval_site {α K R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (root : K → R) (D : α → K → R) (P : MvPolynomial (Option K) R) (s : Finset α) :
    eval (site s) (frameLift root D P) = eval (affineSite root D s) P := by
  have he : (aeval (site (β := K) s)).comp (frameLift root D) =
      aeval (affineSite root D s) := by
    apply algHom_ext
    intro v
    cases v with
    | none => simp [frameLift, liftCoordinate, site, affineSite]
    | some k =>
      simp [frameLift, liftCoordinate, site, affineSite, Finset.sum_ite_mem]
  exact AlgHom.congr_fun he P

theorem boundedSiteMatrix_high_jet_zero {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ)
    (e : VectorPolynomial.BoundedCoefficientExponent K h) (s : Finset α) (hs : h < s.card) :
    booleanCoefficient (fun t => VectorPolynomial.boundedSiteMatrix h
      (integerAffineCube root D) t e) s = 0 := by
  let d : α → K → ℤ := D
  change booleanCoefficient (fun t => VectorPolynomial.boundedSiteMatrix h
    (integerAffineCube root d) t e) s = 0
  have hp := homogeneous_high_jet_zero
    (frameLift_homogeneous root d (homogenizingMonomial_homogeneous (R := ℤ) h e.val e.property)) s hs
  simp_rw [frameLift_eval_site] at hp
  convert hp using 1
  apply congrArg (fun f => booleanCoefficient f s)
  funext t
  simp [homogenizingMonomial, affineSite, VectorPolynomial.boundedSiteMatrix,
    MvPolynomial.eval_rename, MvPolynomial.eval_monomial, integerAffineCube, Finsupp.prod]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

abbrev BoundedBooleanJet (α : Type*) (h : ℕ) := {s : Finset α // s.card ≤ h}

noncomputable def booleanReconstructionMatrix (α : Type*) [DecidableEq α] :
    Matrix (Finset α) (Finset α) ℤ := fun s r => if r ⊆ s then 1 else 0

theorem booleanJetExtraction_mul_reconstruction {α : Type*} [Fintype α] [DecidableEq α] :
    booleanJetExtractionMatrix (id : Finset α → Finset α) * booleanReconstructionMatrix α = 1 := by
  ext s r
  change (booleanJetExtractionMatrix id *ᵥ (fun t => if r ⊆ t then (1 : ℤ) else 0)) s = _
  rw [booleanJetExtractionMatrix_mulVec, booleanCoefficient_monomial]
  rfl

theorem booleanReconstruction_mul_extraction {α : Type*} [Fintype α] [DecidableEq α] :
    booleanReconstructionMatrix α * booleanJetExtractionMatrix (id : Finset α → Finset α) = 1 :=
  mul_eq_one_comm.mp booleanJetExtraction_mul_reconstruction

noncomputable def boundedBooleanReconstructionMatrix (α : Type*) [DecidableEq α] (h : ℕ) :
    Matrix (Finset α) (BoundedBooleanJet α h) ℤ := fun s r => if r.val ⊆ s then 1 else 0

theorem boundedBooleanReconstruction_siteMatrix {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) :
    boundedBooleanReconstructionMatrix α h *
        booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α h → Finset α) *
        VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) =
      VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D) := by
  let E := VectorPolynomial.boundedSiteMatrix h (integerAffineCube root D)
  let F := booleanJetExtractionMatrix (id : Finset α → Finset α) * E
  have hz (r : Finset α) (hr : h < r.card) (e) : F r e = 0 := by
    change (booleanJetExtractionMatrix id *ᵥ (fun t => E t e)) r = 0
    rw [booleanJetExtractionMatrix_mulVec]
    exact BooleanCubeKernel.boundedSiteMatrix_high_jet_zero root D h e r hr
  rw [Matrix.mul_assoc]
  ext s e
  change (∑ r : BoundedBooleanJet α h, booleanReconstructionMatrix α s r.val * F r.val e) = E s e
  calc
    _ = ∑ r ∈ Finset.univ.filter (fun r : Finset α => r.card ≤ h),
        booleanReconstructionMatrix α s r * F r e :=
      (Finset.sum_subtype _ (by simp) _).symm
    _ = ∑ r : Finset α, booleanReconstructionMatrix α s r * F r e := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r _ hr
      have hh : h < r.card := by simpa using hr
      rw [hz r hh, mul_zero]
    _ = (booleanReconstructionMatrix α * F) s e := rfl
    _ = E s e := by
      dsimp only [F]
      rw [← Matrix.mul_assoc, booleanReconstruction_mul_extraction, Matrix.one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def boundedBooleanJetRows (α : Type*) [Fintype α] (h : ℕ) : Finset (Finset α) :=
  Finset.univ.filter (fun s => s.card ≤ h)

theorem mem_boundedBooleanJetRows {α : Type*} [Fintype α] (h : ℕ) (s : Finset α) :
    s ∈ boundedBooleanJetRows α h ↔ s.card ≤ h := by
  simp only [boundedBooleanJetRows, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def boundedBooleanJetRowsEquiv (α : Type*) [Fintype α] (h : ℕ) :
    {s : Finset α // s ∈ boundedBooleanJetRows α h} ≃ BoundedBooleanJet α h where
  toFun s := ⟨s.val, (mem_boundedBooleanJetRows h s.val).mp s.property⟩
  invFun s := ⟨s.val, (mem_boundedBooleanJetRows h s.val).mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

abbrev LowBooleanJetTorus (α : Type*) {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :=
  BooleanJetTorus (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) U

noncomputable def siteFromLowBooleanJets {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    LowBooleanJetTorus α U →+ SiteTorus (Finset α) U where
  toFun y j := integerMatrixTorusMap (U j) (boundedBooleanReconstructionMatrix α (j.val + 1)) (y j)
  map_zero' := funext (fun j => map_zero (integerMatrixTorusMap (U j) _))
  map_add' x y := funext (fun j => map_add (integerMatrixTorusMap (U j) _) (x j) (y j))

theorem siteFromLowBooleanJets_coefficient {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (x : CoefficientTorus (K := K) U) :
    siteFromLowBooleanJets U (coefficientBooleanJetTorusMap U root D
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) x) =
      coefficientSiteTorusMap U (integerAffineCube root D) x := by
  funext j
  change integerMatrixTorusMap (U j) (boundedBooleanReconstructionMatrix α (j.val + 1))
    (integerMatrixTorusMap (U j)
      (booleanJetExtractionMatrix (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
      (integerMatrixTorusMap (U j) (boundedSiteMatrix (j.val + 1) (integerAffineCube root D))
        (coefficientLayerTorus U j x))) = _
  rw [integerMatrixTorusMap_comp, integerMatrixTorusMap_comp,
    boundedBooleanReconstruction_siteMatrix]
  rfl

theorem coefficientSiteImage_lowJet_injective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ) :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    Function.Injective (fun y : Set.range E => siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val) := by
  intro E y z hyz
  obtain ⟨x, hx⟩ := y.property
  obtain ⟨w, hw⟩ := z.property
  apply Subtype.ext
  have he := congrArg (siteFromLowBooleanJets U) hyz
  dsimp only at he
  rw [← hx, ← hw] at he ⊢
  exact (siteFromLowBooleanJets_coefficient U root D x).symm.trans
    (he.trans (siteFromLowBooleanJets_coefficient U root D w))

theorem coefficientSiteImage_lowJet_surjective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (a : ℤ) (ha : a ≠ 0) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range) :
    let E := coefficientSiteTorusMap U (integerAffineCube root D)
    Function.Surjective (fun y : Set.range E => siteBooleanJetTorusMap U
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val) := by
  intro E z
  obtain ⟨x, hx⟩ := coefficientBooleanJetTorusMap_surjective U root D a ha hperiod
    (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
    (fun _ => Subtype.val_injective) (fun _ o => o.property) z
  exact ⟨Set.rangeFactorization E x, hx⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

noncomputable def euclideanCoefficientJetMap {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α) :
    CoefficientTorus (K := K) U →+ EuclideanJetLayers U O :=
  (euclideanJetEquiv U).toAddMonoidHom.comp (coefficientBooleanJetTorusMap U root D rows)

theorem euclideanCoefficientJetMap_continuous {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α) :
    Continuous (euclideanCoefficientJetMap U root D rows) :=
  (euclideanJetEquiv_continuous U).comp (coefficientBooleanJetTorusMap_continuous U root D rows)

theorem euclideanCoefficientJetMap_surjective {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1) :
    Function.Surjective (euclideanCoefficientJetMap U root D rows) :=
  (euclideanJetEquiv U).surjective.comp
    (coefficientBooleanJetTorusMap_surjective U root D a ha hperiod rows hinj hdegree)

theorem euclideanCoefficientJetMap_measurePreserving {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    MeasurePreserving (euclideanCoefficientJetMap U root D rows) μ
      (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) := by
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
  have hc := euclideanCoefficientJetMap_continuous U root D rows
  have hs := euclideanCoefficientJetMap_surjective U root D a ha hperiod rows hinj hdegree
  let : CompactSpace (EuclideanJetLayers U O) := by
    have h := isCompact_univ.image hc
    rw [Set.image_univ, Set.range_eq_univ.mpr hs] at h
    exact ⟨h⟩
  let : ∀ j, IsProbabilityMeasure (Measure.pi (fun _ : O j => ν j)) :=
    fun _ => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure ξ := Measure.pi.instIsProbabilityMeasure _
  let : ∀ j, (Measure.pi (fun _ : O j => ν j)).IsAddLeftInvariant :=
    fun _ => Measure.pi.isAddLeftInvariant _
  let : ξ.IsAddLeftInvariant := Measure.pi.isAddLeftInvariant _
  let : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let : ξ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := ξ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving hc hs (by simp)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
variable (a : ℤ) (ha : a ≠ 0) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)

noncomputable def euclideanSiteImageEquiv :
    Set.range (coefficientSiteTorusMap U (integerAffineCube root D)) ≃
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) :=
  (Equiv.ofBijective (fun y => siteBooleanJetTorusMap U
    (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) y.val)
    ⟨coefficientSiteImage_lowJet_injective U root D,
      coefficientSiteImage_lowJet_surjective U root D a ha hperiod⟩).trans
    (euclideanJetEquiv U).toEquiv

theorem euclideanSiteImageEquiv_continuous :
    Continuous (euclideanSiteImageEquiv U root D a ha hperiod) :=
  (euclideanJetEquiv_continuous U).comp
    ((siteBooleanJetTorusMap_continuous U _).comp continuous_subtype_val)

noncomputable def euclideanSiteImageHomeomorph [CompactSpace (CoefficientTorus (K := K) U)] :
    Set.range (coefficientSiteTorusMap U (integerAffineCube root D)) ≃ₜ
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) := by
  let : CompactSpace (Set.range (coefficientSiteTorusMap U (integerAffineCube root D))) :=
    isCompact_iff_compactSpace.mp (isCompact_range (coefficientSiteTorusMap_continuous U _))
  exact Continuous.homeoOfEquivCompactToT2 (f := euclideanSiteImageEquiv U root D a ha hperiod)
    (euclideanSiteImageEquiv_continuous U root D a ha hperiod)

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (SiteTorus (Finset α) U)] [BorelSpace (SiteTorus (Finset α) U)]

theorem euclideanSiteImageHomeomorph_haar
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    (μ.map (Set.rangeFactorization (coefficientSiteTorusMap U (integerAffineCube root D)))).map
        (euclideanSiteImageHomeomorph U root D a ha hperiod) =
      Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet α (j.val + 1) => ν j)) := by
  have hπ := (coefficientSiteTorusMap_continuous U (integerAffineCube root D)).rangeFactorization.measurable
  have he := (euclideanSiteImageHomeomorph U root D a ha hperiod).continuous.measurable
  exact (Measure.map_map he hπ).trans
    (euclideanCoefficientJetMap_measurePreserving U root D a ha hperiod
      (fun j => (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α))
      (fun _ => Subtype.val_injective) (fun _ o => o.property) μ ν).map_eq

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α]

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientCoordinateEquiv
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientCoordinateTorus_injective :
    Function.Injective (coefficientCoordinateTorus (K := K) U) := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  intro s i
  have hs := QuotientAddGroup.eq_iff_sub_mem.mp (congrFun h s)
  exact hs () i

noncomputable def coefficientCoordinateEquiv :
    CoefficientTorus (K := K) U ≃+ CoefficientCoordinateTori (K := K) U :=
  AddEquiv.ofBijective (coefficientCoordinateTorus U)
    ⟨coefficientCoordinateTorus_injective U, coefficientCoordinateTorus_surjective U⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanCoefficientTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev EuclideanCoefficientLayers :=
  ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) →
    euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup

instance euclideanCoefficientLayers_borel [Fintype K] :
    BorelSpace (EuclideanCoefficientLayers (K := K) U) := by
  let : ∀ j, BorelSpace (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => QuotientAddGroup.borelSpace
  let : ∀ j, BorelSpace (BoundedCoefficientExponent K (j.val + 1) → euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) :=
    fun _ => Pi.borelSpace
  exact Pi.borelSpace

noncomputable def euclideanCoefficientEquiv :
    CoefficientTorus (K := K) U ≃+ EuclideanCoefficientLayers (K := K) U where
  toFun x j d := (euclideanSubspaceTorusEquiv (U j)).symm
    (coefficientCoordinateEquiv U x ⟨j, d⟩)
  invFun y := (coefficientCoordinateEquiv U).symm
    (fun s => euclideanSubspaceTorusEquiv (U s.1) (y s.1 s.2))
  left_inv x := by
    apply (coefficientCoordinateEquiv U).injective
    rw [AddEquiv.apply_symm_apply]
    funext s
    exact (euclideanSubspaceTorusEquiv (U s.1)).apply_symm_apply _
  right_inv y := by
    funext j d
    dsimp only
    rw [AddEquiv.apply_symm_apply]
    exact (euclideanSubspaceTorusEquiv (U j)).symm_apply_apply _
  map_add' x y := by
    funext j d
    simp only [map_add, Pi.add_apply]

theorem euclideanCoefficientEquiv_apply (x : CoefficientTorus (K := K) U)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U x j d = (euclideanSubspaceTorusEquiv (U j)).symm
      (coefficientCoordinateTorus U x ⟨j, d⟩) := rfl

theorem euclideanCoefficientEquiv_continuous [Fintype K] :
    Continuous (euclideanCoefficientEquiv (K := K) U) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro d
  exact (euclideanSubspaceTorusEquiv_symm_continuous (U j)).comp
    ((continuous_apply ⟨j, d⟩).comp (coefficientCoordinateTorus_continuous U))

noncomputable def euclideanCoefficientHomeomorph [Fintype K]
    [CompactSpace (CoefficientTorus (K := K) U)] :
    CoefficientTorus (K := K) U ≃ₜ EuclideanCoefficientLayers (K := K) U := by
  exact Continuous.homeoOfEquivCompactToT2
    (f := (euclideanCoefficientEquiv U).toEquiv) (euclideanCoefficientEquiv_continuous U)

noncomputable def euclideanCoefficientMeasurableEquiv [Fintype K]
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)] :
    CoefficientTorus (K := K) U ≃ᵐ EuclideanCoefficientLayers (K := K) U :=
  (euclideanCoefficientHomeomorph U).toMeasurableEquiv

theorem euclideanCoefficient_measurePreserving [Fintype K]
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)] :
    MeasurePreserving (euclideanCoefficientEquiv U) μ
      (Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))) := by
  let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j))
  let : CompactSpace (EuclideanCoefficientLayers (K := K) U) := by
    have hc := isCompact_univ.image (euclideanCoefficientEquiv_continuous (K := K) U)
    rw [Set.image_univ, Set.range_eq_univ.mpr (euclideanCoefficientEquiv U).surjective] at hc
    exact ⟨hc⟩
  let : ∀ j, IsProbabilityMeasure
      (Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)) :=
    fun j => Measure.pi.instIsProbabilityMeasure _
  let : IsProbabilityMeasure ξ := Measure.pi.instIsProbabilityMeasure _
  let : IsFiniteMeasure ξ := ⟨by simp [measure_univ]⟩
  let : ∀ j, (Measure.pi (fun _ : BoundedCoefficientExponent K (j.val + 1) => ν j)).IsAddLeftInvariant :=
    fun j => Measure.pi.isAddLeftInvariant _
  let : ξ.IsAddLeftInvariant := Measure.pi.isAddLeftInvariant _
  let : μ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := μ) Set.univ isCompact_univ (by simp) }
  let : ξ.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := ⟨fun _ _ => measure_lt_top ξ _⟩
      toIsAddLeftInvariant := inferInstance
      toIsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_compact
        (μ := ξ) Set.univ isCompact_univ (by simp) }
  exact AddMonoidHom.measurePreserving
    (f := (euclideanCoefficientEquiv U).toAddMonoidHom)
    (euclideanCoefficientEquiv_continuous U) (euclideanCoefficientEquiv U).surjective (by simp)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

noncomputable def coefficientTorusFourierSum {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (x : CoefficientTorus (K := K) U) : ℂ := ∑ a, c a * coefficientTorusCharacter U (frequency a) x

theorem coefficientTorusFourierSum_integrable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ] :
    Integrable (coefficientTorusFourierSum U frequency c) μ := by
  apply integrable_finsetSum
  intro a _
  exact (coefficientTorusCharacter_integrable U (frequency a) μ).const_mul (c a)

theorem coefficientTorusFourierSum_integral {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] :
    (∫ x, coefficientTorusFourierSum U frequency c x ∂μ) =
      ∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0 := by
  change (∫ x, ∑ a, c a * coefficientTorusCharacter U (frequency a) x ∂μ) = _
  rw [integral_finsetSum _ (fun a _ => (coefficientTorusCharacter_integrable U (frequency a) μ).const_mul (c a))]
  simp only [integral_const_mul, coefficientTorusCharacter_integral]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientTorusCharacter_norm (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientTorus (K := K) U) : ‖coefficientTorusCharacter U frequency x‖ = 1 :=
  quotientLinearCharacter_norm _ _ _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {K Y : Type*} [Fintype K] [Fintype Y] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (law : FiniteProbabilityWeights Y)
variable {F : Y → Type*} [∀ y, Fintype (F y)]
variable (frequency : ∀ y, F y → ∀ j, (K →₀ ℕ) → J j → ℤ)
variable (coeff : ∀ y, F y → ℂ)

end Erdos3.VectorPolynomial

end

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

theorem coefficientTorusCharacter_slot_product {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : ∀ s : CoefficientSlot K m, J s.1 → ℤ) (x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U (coefficientSlotFrequency frequency) x =
      ∏ s : CoefficientSlot K m, subspaceArrayCharacter (U s.1) (fun _ a => frequency s a)
        (coefficientCoordinateTorus U x s) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [coefficientTorusCharacter_mk]
  change CircleFourier.character ((∑ s : CoefficientSlot K m, ∑ a,
    (coefficientSlotFrequency frequency s.1 s.2.val a : ℝ) * (y s).val a : ℝ) :
      CircleFourier.Circle) = _
  simp only [coefficientSlotFrequency_apply]
  rw [character_real_sum]
  apply Finset.prod_congr rfl
  intro s _
  rw [coefficientCoordinateTorus_mk]
  change _ = CircleFourier.character
    ((∑ _u : Unit, ∑ a, (frequency s a : ℝ) * (y s).val a : ℝ) : CircleFourier.Circle)
  simp only [Fintype.sum_unique]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end


