-- Prove2me | Definitions.Def_OAIErdos3B050
-- name    : OAIErdos3B050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T15:40:52.8068+00:00
-- url     : https://prove2.me/theorems/a468e2be-262c-4e37-943e-a609e3bb971b
-- title:
--   OpenAI Erdős-3 split, definitions bundle 51 of 148
-- statement:
--   Definitions bundle 51 of 148 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B049`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 51 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.NativeCoordinateDerivativeSpec`, `OAI.Erdos3.NilpotentLieFiltration.TopGradedBasisIndex`, `OAI.Erdos3.NilpotentLieFiltration.exists_fullFast_derivative_absorption`, `OAI.Erdos3.NilpotentLieFiltration.exists_gradedHorizontalKernel_quotient_basis`, `OAI.Erdos3.NilpotentLieFiltration.exists_native_coordinate_derivative_system`, `OAI.Erdos3.NilpotentLieFiltration.exists_reducedSquareGradedRelativePiece_of_pure_kernel`, `OAI.Erdos3.NilpotentLieFiltration.fastGradedRelativeKernel`, `OAI.Erdos3.NilpotentLieFiltration.fastGradedRelativeKernel_graded`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientFastSubmodule_eq_gradedKernel`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientFastSubmodule_graded_coefficients`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientFastSubmodule_iff_graded`, `OAI.Erdos3.NilpotentLieFiltration.firstCoefficientGradedQuotientMap`, `OAI.Erdos3.NilpotentLieFiltration.fullFastDiagonalGenerators`, `OAI.Erdos3.NilpotentLieFiltration.fullFastDiagonalGenerators_card`, `OAI.Erdos3.NilpotentLieFiltration.fullFastDiagonalGenerators_height`, `OAI.Erdos3.NilpotentLieFiltration.fullFastDiagonalGenerators_span`, `OAI.Erdos3.NilpotentLieFiltration.fullFastGradedRelative`, `OAI.Erdos3.NilpotentLieFiltration.fullFastGradedRelative_graded`, `OAI.Erdos3.NilpotentLieFiltration.fullFastGradedRelative_le_second`, `OAI.Erdos3.NilpotentLieFiltration.fullFastGradedRelative_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.fullFastGradedRelative_low_projection`, `OAI.Erdos3.NilpotentLieFiltration.fullFastGradedRelative_top_frequency`, `OAI.Erdos3.NilpotentLieFiltration.fullFastHorizontalCoordinates`, `OAI.Erdos3.NilpotentLieFiltration.fullFastHorizontalGenerators`, `OAI.Erdos3.NilpotentLieFiltration.fullFastHorizontalGenerators_height`, `OAI.Erdos3.NilpotentLieFiltration.fullFastHorizontalGenerators_span`, `OAI.Erdos3.NilpotentLieFiltration.fullFastHorizontalMatrix`, `OAI.Erdos3.NilpotentLieFiltration.fullFastHorizontalMatrix_height`, `OAI.Erdos3.NilpotentLieFiltration.fullFastHorizontalMatrix_span`, `OAI.Erdos3.NilpotentLieFiltration.gradedHorizontalKernel`, `OAI.Erdos3.NilpotentLieFiltration.gradedHorizontalKernelBasis`, `OAI.Erdos3.NilpotentLieFiltration.gradedHorizontalKernelBasis_coe`, `OAI.Erdos3.NilpotentLieFiltration.gradedHorizontalKernelBasis_height`, `OAI.Erdos3.NilpotentLieFiltration.gradedHorizontalKernelBasis_span`, `OAI.Erdos3.NilpotentLieFiltration.gradedHorizontalKernelEquiv`, `OAI.Erdos3.NilpotentLieFiltration.gradedHorizontalKernel_real_mem`, `OAI.Erdos3.NilpotentLieFiltration.gradedHorizontalKernel_real_pure`, `OAI.Erdos3.NilpotentLieFiltration.gradedLayerOneProjection`, `OAI.Erdos3.NilpotentLieFiltration.gradedLayerOneProjection_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.gradedLayerOneProjection_height`, `OAI.Erdos3.NilpotentLieFiltration.gradedLayerOneProjection_rightInverse`, `OAI.Erdos3.NilpotentLieFiltration.gradedLayerOneProjection_spanning`, `OAI.Erdos3.NilpotentLieFiltration.layerOneGradedMap_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.layerOneGradedMap_coordinate_zero`, `OAI.Erdos3.NilpotentLieFiltration.layerOneGradedMap_height`, `OAI.Erdos3.NilpotentLieFiltration.layerOneGradedMap_injective`, `OAI.Erdos3.NilpotentLieFiltration.layerOneGradedMap_projection`, `OAI.Erdos3.NilpotentLieFiltration.layerOneGradedMap_pure`, `OAI.Erdos3.NilpotentLieFiltration.layerOneGradedSubmodule_eq_image`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopGradedMap_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopGradedMap_kernel`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopGradedMap_piece`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopGradedSection`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopGradedSection_basis`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopGradedSection_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopGradedSection_coordinate_zero`, `OAI.Erdos3.NilpotentLieFiltration.quotientTopGradedSection_rightInverse`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientFastSubmodule_iff_graded`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientGradedQuotient_coefficient`, `OAI.Erdos3.NilpotentLieFiltration.realLayerOneGradedMap_pure`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDifference_basis_height`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDifference_mem_second`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedDifference_relativePiece`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedPiece_kernel_relative`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedSndMap_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.reducedSquareGradedSnd_piece`, `OAI.Erdos3.NilpotentLieFiltration.square_gradedFrequency_restriction`, `OAI.Erdos3.NilpotentLieFiltration.square_mode_fullFast_top_frequency`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientAmbientDensity_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientDensity_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientDensity_continuous`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientDensity_fixedScale_le_exp`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientDensity_positive_spec`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficient_fourier_input_budget`, `OAI.Erdos3.VectorPolynomial.allocatedFourierLogBudget`, `OAI.Erdos3.VectorPolynomial.allocatedFourierLogBudget_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedFourierOutputBudget`, `OAI.Erdos3.VectorPolynomial.allocatedFourierOutputBudget_dominates`, `OAI.Erdos3.VectorPolynomial.allocatedMaskedCoefficientDensity`, `OAI.Erdos3.VectorPolynomial.allocatedMaskedFourierBudget`, `OAI.Erdos3.VectorPolynomial.allocatedMaskedFourierBudget_bounds`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDensity_continuous`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientBudgetExponent`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientBudgetExponent_bound`, `OAI.Erdos3.VectorPolynomial.exists_allocatedFourierLogBudget_bound`, `OAI.Erdos3.VectorPolynomial.exists_allocatedFourierOutputBudget_bound`, `OAI.Erdos3.VectorPolynomial.exists_allocatedMaskedFourierBudget_bound`, `OAI.Erdos3.VectorPolynomial.exists_allocated_coefficient_fourier_approximation`, `OAI.Erdos3.VectorPolynomial.exists_allocated_coefficient_uniform_fourier`, `OAI.Erdos3.VectorPolynomial.exists_positiveComparisonDataBudget_bound`, `OAI.Erdos3.VectorPolynomial.positiveComparisonDataBudget`, `OAI.Erdos3.VectorPolynomial.positiveComparisonDataBudget_bounds`, `OAI.Erdos3.canonicalArrayDensity_continuous`, `OAI.Erdos3.canonicalMixedDensity_continuous_of_ambient`, `OAI.Erdos3.exists_absorb_missing_coordinate_error`, `OAI.Erdos3.exists_controlled_derivative_absorption`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130
import Definitions.Def_OAIErdos3B133

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedCoefficientAmbientDensity_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) :
    let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
    let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
    let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    (∀ x, 0 ≤ allocatedCoefficientAmbientDensity B U b o S x ∧
      allocatedCoefficientAmbientDensity B U b o S x ≤ (A : ℝ)^N) ∧
    LipschitzWith (N * L * A^N) (allocatedCoefficientAmbientDensity B U b o S) := by
  have h := allocatedAmbientFactor_bounds B U b S o C V hC hV hR hσ
  exact coefficientAmbientDensity_bounds U b o _ _ _
    (allocatedAmbientFactorCap_one_le (G := G) B R σ S.value V)
    (fun s x => (h s).1 x) (fun s => (h s).2)

include hC hV in
theorem exists_allocated_coefficient_fourier_approximation
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ P)
    (hLP : let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
      let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
      let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
      ((N * L * A^N : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i,
        |(frequency t j d i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) *
        (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ)^
          Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) ∧
      ∀ x, ‖(allocatedCoefficientDensity B U b hb o hR hσ S x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  have h := allocatedAmbientFactor_bounds B U b S o C V hC hV hR hσ
  exact exists_coefficient_ambient_fourier_approximation U b hb o _ _ _ _
    (fun j i d => (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d).1)
    (allocatedLayerColumns_quarter_support B U b hR hσ S o hσ1 Cinv hCinv hchart hsmall)
    (allocatedAmbientFactorCap_one_le (G := G) B R σ S.value V)
    (fun s x => (h s).1 x) (fun s => (h s).2) hδ hP hdim hLP hδP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

noncomputable def coefficientAmbientBudgetExponent (m : ℕ) : ℕ :=
  (exists_natPolynomial_eval_budget (coefficientAmbientInputPolynomial m)).choose

theorem coefficientAmbientBudgetExponent_bound (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (m : ℝ) * (m+1) * (P+1)^m * (P+1) + P + 1 ≤
      (P + coefficientAmbientBudgetExponent m)^coefficientAmbientBudgetExponent m := by
  simpa [coefficientAmbientInputPolynomial, coefficientAmbientBudgetExponent, Polynomial.eval₂_pow]
    using (exists_natPolynomial_eval_budget (coefficientAmbientInputPolynomial m)).choose_spec.2 P hP

noncomputable def allocatedFourierLogBudget (m : ℕ) (P : ℝ) : ℝ :=
  (P + allocatedAmbientLog m P + coefficientAmbientBudgetExponent m)^coefficientAmbientBudgetExponent m

theorem allocatedFourierLogBudget_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedFourierLogBudget m P := by
  have h := allocatedAmbientLog_nonneg m hP
  unfold allocatedFourierLogBudget
  positivity

theorem exists_allocatedFourierLogBudget_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ P : ℝ, 0 ≤ P → allocatedFourierLogBudget m P ≤ (P+a)^a := by
  let e := coefficientAmbientBudgetExponent m
  let scalar : Polynomial ℕ := 7 * (Polynomial.C (layerTailDegree m+1) * (4 * (Polynomial.X+8)) + 8)
  let common : Polynomial ℕ := Polynomial.X + Polynomial.X * scalar + 1
  let width : Polynomial ℕ := Polynomial.C (m+4) * (Polynomial.X+8)
  let mixed : Polynomial ℕ := (2*Polynomial.X+1)*(width+common)+3*Polynomial.X+1
  let ambient : Polynomial ℕ := Polynomial.X + Polynomial.X*(2*mixed+4*Polynomial.X+9)+1
  let budget : Polynomial ℕ := (Polynomial.X+ambient+Polynomial.C e)^e
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget budget
  refine ⟨a, ha, ?_⟩
  intro P hP
  simpa [budget, ambient, mixed, width, common, scalar, e, allocatedFourierLogBudget,
    allocatedAmbientLog, allocatedMixedLog, allocatedWidthLog, allocatedCommonLog,
    allocatedScalarLog, integerInterpolationLogEnvelope, Polynomial.eval₂_pow] using hbound P hP

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedCoefficient_fourier_input_budget
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L) (C V : Fin m → ℝ≥0)
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (L : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P) :
    let A := allocatedAmbientFactorCap (G := G) B R σ L V
    let F := allocatedAmbientFactorLip (G := G) B R σ L (fun j => Fintype.card (J j)) C V
    let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    P ≤ allocatedFourierLogBudget m P ∧
      (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ allocatedFourierLogBudget m P ∧
      (A : ℝ)^N ≤ Real.exp (allocatedFourierLogBudget m P) ∧
      (N : ℝ)*F*(A : ℝ)^N ≤ Real.exp (allocatedFourierLogBudget m P) := by
  let A := allocatedAmbientFactorCap (G := G) B R σ L V
  let F := allocatedAmbientFactorLip (G := G) B R σ L (fun j => Fintype.card (J j)) C V
  let T := P + allocatedAmbientLog m P
  have hPT : P ≤ T := le_add_of_nonneg_right (allocatedAmbientLog_nonneg m hP)
  have hT : 0 ≤ T := hP.trans hPT
  obtain ⟨ha, hf⟩ := allocatedAmbientConstants_exp_bounds B R σ L hL _ C V hP hm
    hR hσ hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  have he : Real.exp (allocatedAmbientLog m P) ≤ Real.exp T :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_left hP)
  have h := coefficient_ambient_input_exp_bounds
    hT (hK.trans hPT) (fun j => (hJ j).trans hPT) A.coe_nonneg (ha.trans he) F.coe_nonneg (hf.trans he)
    (coefficientAmbientBudgetExponent_bound m hT)
  exact ⟨hPT.trans h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedFourierOutputBudget (m : ℕ) (P : ℝ) : ℝ :=
  let Q := allocatedFourierLogBudget m P
  2*Q*(2*Q+2)^4+Q+(2*Q+2)^4

theorem allocatedFourierOutputBudget_dominates (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    let Q := allocatedFourierLogBudget m P
    2*Q*(2*Q+2)^4 ≤ allocatedFourierOutputBudget m P ∧
      (2*Q+2)^4 ≤ allocatedFourierOutputBudget m P ∧
      2*Q*(2*Q+2)^4+Q ≤ allocatedFourierOutputBudget m P := by
  have hQ := allocatedFourierLogBudget_nonneg m hP
  have hpow : 0 ≤ (2*allocatedFourierLogBudget m P+2)^4 := by positivity
  have hprod : 0 ≤ 2*allocatedFourierLogBudget m P*(2*allocatedFourierLogBudget m P+2)^4 := by positivity
  dsimp only [allocatedFourierOutputBudget]
  constructor
  · linarith
  constructor <;> linarith

theorem exists_allocatedFourierOutputBudget_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ P : ℝ, 0 ≤ P → allocatedFourierOutputBudget m P ≤ (P+a)^a := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierLogBudget_bound m
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C b)^b
  let output : Polynomial ℕ := 2*q*(2*q+2)^4+q+(2*q+2)^4
  obtain ⟨a, ha, hout⟩ := exists_natPolynomial_eval_budget output
  refine ⟨a, ha, ?_⟩
  intro P hP
  have hQ := allocatedFourierLogBudget_nonneg m hP
  have hqb := hb P hP
  have hbound : 2*((P+b)^b)*(2*((P+b)^b)+2)^4+(P+b)^b+(2*((P+b)^b)+2)^4 ≤ (P+a)^a := by
    simpa [output, q, Polynomial.eval₂_pow] using hout P hP
  apply le_trans _ hbound
  dsimp only [allocatedFourierOutputBudget]
  gcongr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedMaskedFourierBudget (m : ℕ) (P : ℝ) : ℝ :=
  let Q := allocatedFourierLogBudget m P
  P + (4 * Q + 2) ^ 4 + (4 * Q * (4 * Q + 2) ^ 4 + Q)

theorem allocatedMaskedFourierBudget_bounds (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    let Q := allocatedFourierLogBudget m P
    let Ps := allocatedMaskedFourierBudget m P
    0 ≤ Ps ∧ P ≤ Ps ∧ (4 * Q + 2) ^ 4 ≤ Ps ∧
      4 * Q * (4 * Q + 2) ^ 4 + Q ≤ Ps := by
  have hQ := allocatedFourierLogBudget_nonneg m hP
  have hF : 0 ≤ (4 * allocatedFourierLogBudget m P + 2) ^ 4 := by positivity
  have hM : 0 ≤ 4 * allocatedFourierLogBudget m P *
      (4 * allocatedFourierLogBudget m P + 2) ^ 4 + allocatedFourierLogBudget m P := by positivity
  dsimp only [allocatedMaskedFourierBudget]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem exists_allocatedMaskedFourierBudget_bound (m A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      allocatedMaskedFourierBudget m P ≤ (P + C) ^ C ∧
      (allocatedMaskedFourierBudget m P + A) ^ A ≤ (P + C) ^ C := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierLogBudget_bound m
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C b) ^ b
  let f : Polynomial ℕ := Polynomial.X + (4 * q + 2) ^ 4 + (4 * q * (4 * q + 2) ^ 4 + q)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (f + (f + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro P hP
  let F : ℝ := P + (4 * (P + b) ^ b + 2) ^ 4 +
    (4 * (P + b) ^ b * (4 * (P + b) ^ b + 2) ^ 4 + (P + b) ^ b)
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hPs0 := (allocatedMaskedFourierBudget_bounds m hP).1
  have hPs : allocatedMaskedFourierBudget m P ≤ F := by
    have hQ := allocatedFourierLogBudget_nonneg m hP
    have hQB := hb P hP
    dsimp only [allocatedMaskedFourierBudget, F]
    gcongr
  have hpow : (allocatedMaskedFourierBudget m P + A) ^ A ≤ (F + A) ^ A := by gcongr
  have hpow0 : 0 ≤ (F + A) ^ A := by positivity
  have htotal : F + (F + A) ^ A ≤ (P + C) ^ C := by
    simpa [F, f, q, Polynomial.eval₂_pow] using hbound P hP
  exact ⟨by linarith, by linarith⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem exists_allocated_coefficient_uniform_fourier
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {P δ : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P) :
    let Q := allocatedFourierLogBudget m P
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2*Q*(2*Q+2)^4) ∧
      (∀ t j d, d.degree ≤ j.val+1 → ∀ i, |(frequency t j d i : ℝ)| ≤ Real.exp ((2*Q+2)^4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2*Q*(2*Q+2)^4+Q) ∧
      ∀ x, ‖(allocatedCoefficientDensity B U b hb o hR hσ S x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  have hbudget := allocatedCoefficient_fourier_input_budget B (J := J) R σ S.value S.positive C V
    hP hm hK hR hσ hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  have hLip :
      ((Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
        allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
        (allocatedAmbientFactorCap (G := G) B R σ S.value V)^
          Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ≥0) : ℝ) ≤
      Real.exp (allocatedFourierLogBudget m P) := by
    simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using hbudget.2.2.2
  obtain ⟨F, inst, frequency, a, hcard, hfreq, hsum, herr⟩ :=
    exists_allocated_coefficient_fourier_approximation B U b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall hδ (allocatedFourierLogBudget_nonneg m hP)
      hbudget.2.1 hLip (hδP.trans (Real.exp_le_exp.mpr hbudget.1))
  let _ := inst
  refine ⟨F, inst, frequency, a, hcard, hfreq, ?_, herr⟩
  exact hsum.trans ((mul_le_mul_of_nonneg_left hbudget.2.2.1 (Real.exp_nonneg _)).trans_eq
    (Real.exp_add _ _).symm)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedMaskedCoefficientDensity (q : ℕ)
    (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) : ℝ :=
  maskedIntegerTorusKernel q mask (allocatedCoefficientJointAmbientKernel B U b S o)
    (coefficientAmbientTorus U x)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PositiveComparisonDataBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def positiveComparisonDataBudget (m q : ℕ) (p : ℝ) : ℝ :=
  (2 * p + 4) + allocatedFourierOutputBudget m (2 * p + 4) +
    allocatedFourierLogBudget m (2 * p + 4) + 3 * p + (q + 1) * (4 * p + 5) + 4

theorem positiveComparisonDataBudget_bounds (m q : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let Q := positiveComparisonDataBudget m q p
    0 ≤ Q ∧ p ≤ Q ∧ 2 * p + 4 ≤ Q ∧
      allocatedFourierOutputBudget m (2 * p + 4) ≤ Q ∧
      allocatedFourierLogBudget m (2 * p + 4) + 3 * p + (q + 1) * (4 * p + 5) + 4 ≤ Q := by
  have hB := allocatedFourierLogBudget_nonneg m (by linarith : 0 ≤ 2 * p + 4)
  have hF : 0 ≤ allocatedFourierOutputBudget m (2 * p + 4) := by
    unfold allocatedFourierOutputBudget
    positivity
  have hL : 0 ≤ ((q : ℝ) + 1) * (4 * p + 5) := by positivity
  dsimp only [positiveComparisonDataBudget]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem exists_positiveComparisonDataBudget_bound (m q : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → positiveComparisonDataBudget m q p ≤ (p + a) ^ a := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierOutputBudget_bound m
  obtain ⟨a, ha, haBound⟩ := exists_natPolynomial_eval_budget
    ((2 * Polynomial.X + 4) + 2 * (2 * Polynomial.X + 4 + Polynomial.C b) ^ b +
      3 * Polynomial.X + Polynomial.C (q + 1) * (4 * Polynomial.X + 5) + 4)
  refine ⟨a, ha, ?_⟩
  intro p hp
  have hP : 0 ≤ 2 * p + 4 := by linarith
  have hB := allocatedFourierLogBudget_nonneg m hP
  have hBF : allocatedFourierLogBudget m (2 * p + 4) ≤ allocatedFourierOutputBudget m (2 * p + 4) := by
    have h := (allocatedFourierOutputBudget_dominates m hP).2.2
    have hnonneg : 0 ≤ 2 * allocatedFourierLogBudget m (2 * p + 4) *
        (2 * allocatedFourierLogBudget m (2 * p + 4) + 2) ^ 4 := by positivity
    linarith
  have hpoly : (2 * p + 4) + 2 * (2 * p + 4 + b) ^ b + 3 * p +
      (q + 1 : ℕ) * (4 * p + 5) + 4 ≤ (p + a) ^ a := by
    simpa [Polynomial.eval₂_pow] using haBound p hp
  apply le_trans _ hpoly
  unfold positiveComparisonDataBudget
  have hF := hb (2 * p + 4) hP
  push_cast
  linarith

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealGradedFastCoefficientKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

noncomputable def fastGradedRelativeKernel
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    Submodule ℚ F.squareFiltration.quotientTop.AssociatedGraded :=
  W.toSubmodule ⊓ F.reducedSquareGradedSndMap.ker.toSubmodule

noncomputable def fullFastGradedRelative
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    Submodule ℚ F.AssociatedGraded :=
  (F.fastGradedRelativeKernel W).map (F.reducedSquareGradedDifference e ω hF)

variable (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem firstCoefficientFastSubmodule_graded_coefficients (x : F.FirstCoefficientModule w)
    (hx : x ∈ F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule) :
    ∀ α, coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α ∈
      F.fullFastGradedRelative e ω hF W := by
  rw [F.firstCoefficientFastSubmodule_eq_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  intro α
  rw [F.firstCoefficientGradedPolynomial_reducedSquare_coefficient]
  refine ⟨coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w y) α, ?_, rfl⟩
  constructor
  · exact (F.squareFiltration.quotientTop.mem_symbolPointwiseSubalgebra_iff
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w W y).mp hy.1 α
  · change F.reducedSquareGradedSndMap _ = 0
    rw [F.reducedSquareGradedSnd_coefficient]
    have hz : F.reducedSquareSndSymbolMap w y = 0 := hy.2
    simp only [hz, map_zero, Finsupp.zero_apply]

theorem firstCoefficientFastSubmodule_iff_graded
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) (x : F.FirstCoefficientModule w) :
    x ∈ F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule ↔
      ∀ α, coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α ∈
        F.fullFastGradedRelative e ω hF W := by
  classical
  constructor
  · exact F.firstCoefficientFastSubmodule_graded_coefficients e ω hF w hw W x
  · intro hx
    have hex (α : σ →₀ ℕ) : ∃ y, y ∈ F.fastGradedRelativeKernel W ∧
        F.reducedSquareGradedDifference e ω hF y =
          coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α := hx α
    choose y hy hey using hex
    let q (α : σ →₀ ℕ) : F.FirstCoefficientModule w :=
      F.reducedSquareCoefficientMap w (F.squareFiltration.quotientTop.homogeneousSymbolLift
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α (y α))
    have hq (α : σ →₀ ℕ) : q α ∈
        F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule := by
      rw [F.firstCoefficientFastSubmodule_eq_image]
      refine ⟨F.squareFiltration.quotientTop.homogeneousSymbolLift
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α (y α), ?_, rfl⟩
      constructor
      · exact F.squareFiltration.quotientTop.homogeneousSymbolLift_mem_pointwise
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w W hW α (y α) (hy α).1
      · change F.reducedSquareSndSymbolMap w _ = 0
        rw [F.reducedSquareSnd_homogeneousSymbolLift]
        have hz : F.reducedSquareGradedSndMap (y α) = 0 := (hy α).2
        rw [hz, map_zero]
    have hp (α : σ →₀ ℕ) : F.firstCoefficientGradedPolynomial e ω hF w (q α) =
        monomial α (coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α) := by
      dsimp only [q]
      rw [F.firstCoefficientGradedPolynomial_reducedSquare_homogeneous, hey,
        F.firstCoefficientGradedPolynomial_homogeneous]
    have he : (∑ α ∈ (coefficients (F.firstCoefficientGradedPolynomial e ω hF w x)).support, q α) = x := by
      apply F.firstCoefficientGradedPolynomial_injective e ω hF w
      rw [map_sum]
      simp_rw [hp]
      exact sum_monomial_coefficients _
    rw [← he]
    exact Submodule.sum_mem _ (fun α _ => hq α)

noncomputable def firstCoefficientGradedQuotientMap :
    F.FirstCoefficientModule w →ₗ[ℚ] VectorPolynomial σ ℚ
      (F.AssociatedGraded ⧸ F.fullFastGradedRelative e ω hF W) :=
  (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ).comp
    (F.firstCoefficientGradedPolynomial e ω hF w)

theorem firstCoefficientFastSubmodule_eq_gradedKernel
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule =
      LinearMap.ker (F.firstCoefficientGradedQuotientMap e ω hF w W) := by
  ext x
  rw [F.firstCoefficientFastSubmodule_iff_graded e ω hF w hw W hW]
  change (∀ α, coefficients (F.firstCoefficientGradedPolynomial e ω hF w x) α ∈
    F.fullFastGradedRelative e ω hF W) ↔ F.firstCoefficientGradedQuotientMap e ω hF w W x = 0
  constructor
  · intro hx
    apply coefficients.injective
    ext α
    change coefficients (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ
      (F.firstCoefficientGradedPolynomial e ω hF w x)) α = _
    rw [coefficients_map, map_zero, Finsupp.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hx α)
  · intro hx α
    have hc := congrArg (fun p => coefficients p α) hx
    change coefficients (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ
      (F.firstCoefficientGradedPolynomial e ω hF w x)) α = _ at hc
    rw [coefficients_map, map_zero, Finsupp.zero_apply] at hc
    exact (Submodule.Quotient.mk_eq_zero _).mp hc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem realFirstCoefficientGradedQuotient_coefficient (x : ℝ ⊗[ℚ] F.FirstCoefficientModule w)
    (α : σ →₀ ℕ) :
    coefficients (realificationLinearEquiv
      ((F.firstCoefficientGradedQuotientMap e ω hF w W).baseChange ℝ x)) α =
        (F.fullFastGradedRelative e ω hF W).mkQ.baseChange ℝ
          (coefficients (F.realFirstCoefficientGradedPolynomial e ω hF w
            (F.firstCoefficientRealEquiv w x)) α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, coefficients_realificationLinearEquiv_tmul,
      F.realFirstCoefficientGradedPolynomial_tmul, LinearMap.baseChange_tmul]
    change a ⊗ₜ[ℚ] coefficients (VectorPolynomial.map (F.fullFastGradedRelative e ω hF W).mkQ
      (F.firstCoefficientGradedPolynomial e ω hF w x)) α = _
    rw [coefficients_map]

theorem realFirstCoefficientFastSubmodule_iff_graded (hw : ∀ i, 0 < w i)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) (x : F.RealFirstCoefficientModule w) :
    x ∈ F.realFirstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule ↔
      ∀ α, coefficients (F.realFirstCoefficientGradedPolynomial e ω hF w x) α ∈
        (F.fullFastGradedRelative e ω hF W).baseChange ℝ := by
  obtain ⟨y, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  have hmem : F.firstCoefficientRealEquiv w y ∈
      F.realFirstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule ↔
      y ∈ (F.firstCoefficientFastSubmodule w hw (F.fastPointwiseSquare e ω hF w W).toSubmodule).baseChange ℝ := by
    constructor
    · rintro ⟨z, hz, he⟩
      have hzy : z = y := (F.firstCoefficientRealEquiv w).injective he
      rwa [hzy] at hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  rw [hmem, F.firstCoefficientFastSubmodule_eq_gradedKernel e ω hF w hw W hW, realification_ker]
  change (F.firstCoefficientGradedQuotientMap e ω hF w W).baseChange ℝ y = 0 ↔ _
  rw [realificationLinearEquiv_eq_zero_iff]
  have hker : (F.fullFastGradedRelative e ω hF W).baseChange ℝ =
      LinearMap.ker ((F.fullFastGradedRelative e ω hF W).mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using
      realification_ker (F.fullFastGradedRelative e ω hF W).mkQ
  constructor
  · intro hy α
    rw [hker]
    change (F.fullFastGradedRelative e ω hF W).mkQ.baseChange ℝ _ = 0
    exact (F.realFirstCoefficientGradedQuotient_coefficient e ω hF w W y α).symm.trans (hy α)
  · intro hy α
    have h := hy α
    rw [hker] at h
    exact (F.realFirstCoefficientGradedQuotient_coefficient e ω hF w W y α).trans h

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastGradedRelativeInvariance
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem reducedSquareGradedDifference_basis_height (a : ReducedSquareBasisIndex s ω) (i : ι) :
    RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
      (F.reducedSquareGradedDifference e ω hF (bW a)) i) 1 := by
  rw [F.reducedSquareGradedDifference_basis]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl j =>
    simp only [Sum.elim_inl, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl
  | inr j => exact basis_repr_height_one (F.associatedGradedBasis e ω hF) j.val i

theorem reducedSquareGradedDifference_mem_second (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.reducedSquareGradedDifference e ω hF x ∈ F.associatedGradedFiltration.layer 2 := by
  have htop : (⊤ : Submodule ℚ F.squareFiltration.quotientTop.AssociatedGraded) ≤
      (F.associatedGradedFiltration.layer 2).comap (F.reducedSquareGradedDifference e ω hF) := by
    rw [← (bW).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change F.reducedSquareGradedDifference e ω hF (bW a) ∈ F.associatedGradedFiltration.layer 2
    rw [F.reducedSquareGradedDifference_basis]
    rcases a with ⟨a, ha⟩
    cases a with
    | inl i => exact (F.associatedGradedFiltration.layer 2).zero_mem
    | inr i =>
      rw [F.associatedGradedFiltration_layer e ω hF]
      exact Submodule.subset_span ⟨i.val, i.property, rfl⟩
  exact htop (by trivial)

variable (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem fastGradedRelativeKernel_graded
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule bW ωW (F.fastGradedRelativeKernel W) := by
  intro j x hx
  refine ⟨hW j x hx.1, ?_⟩
  change F.reducedSquareGradedSndMap (basisGradeProjection bW ωW j x) = 0
  unfold reducedSquareGradedSndMap
  rw [F.squareFiltration.quotientTop.associatedGradedMap_gradeProjection F.quotientTop
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem j x]
  change basisGradeProjection (F.quotientTop.associatedGradedBasis (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)) (fun i => ω i.val) j
      (F.reducedSquareGradedSndMap x) = 0
  rw [show F.reducedSquareGradedSndMap x = 0 from hx.2, map_zero]

theorem fullFastGradedRelative_le_second :
    F.fullFastGradedRelative e ω hF W ≤ F.associatedGradedFiltration.layer 2 := by
  rintro _ ⟨x, _, rfl⟩
  exact F.reducedSquareGradedDifference_mem_second e ω hF x

theorem fullFastGradedRelative_low_projection (j : ℕ) (hj : j < 2)
    (x : F.AssociatedGraded) (hx : x ∈ F.fullFastGradedRelative e ω hF W) :
    basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x = 0 := by
  have hh := F.fullFastGradedRelative_le_second e ω hF W hx
  rw [F.associatedGradedFiltration_layer e ω hF] at hh
  apply (basisCoordinateProjection_eq_zero_iff (F.associatedGradedBasis e ω hF) {i | ω i = j} x).mpr
  apply Submodule.span_mono (Set.image_mono ?_) hh
  intro i hi
  change ω i ≠ j
  change 2 ≤ ω i at hi
  omega

theorem fullFastGradedRelative_graded
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω (F.fullFastGradedRelative e ω hF W) := by
  intro j x hx
  by_cases hj : j = 0
  · subst j
    rw [F.fullFastGradedRelative_low_projection e ω hF W 0 (by decide) x hx]
    exact (F.fullFastGradedRelative e ω hF W).zero_mem
  · obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨basisGradeProjection bW ωW (j - 1) y,
      F.fastGradedRelativeKernel_graded e ω hF W hW (j - 1) y hy, ?_⟩
    have he := F.reducedSquareGradedDifference_gradeProjection e ω hF (j - 1) y
    have hdeg : j - 1 + 1 = j := by omega
    simpa only [hdeg] using he

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem fullFastGradedRelative_lie_mem {u v : F.AssociatedGraded}
    (hu : u ∈ F.fullFastGradedDiagonal W) (hv : v ∈ F.fullFastGradedRelative e ω hF W) :
    ⁅u, v⁆ ∈ F.fullFastGradedRelative e ω hF W := by
  obtain ⟨z, hz, rfl⟩ := hv
  have hz0 : z ∈ (F.reducedSquareSndSymbolMap (fun _ : Unit => 1)).ker.toSubmodule := hz.2
  obtain ⟨p, hp⟩ := (F.reducedRelativeSquareSymbolMap_range
    (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one)).ge hz0
  obtain ⟨a, ha⟩ := F.polynomialSymbolMap_surjective (fun _ : Unit => 1) u
  have hua : F.adaptedReducedSymbolMap (fun _ : Unit => 1) a ∈
      F.reducedSquareFastDiagonalSubalgebra (fun _ : Unit => 1) W := by
    change F.quotientTopSymbolMap (fun _ : Unit => 1)
      (F.polynomialSymbolMap (fun _ : Unit => 1) a) ∈ _
    rw [ha]
    exact hu
  have hz' : z ∈ F.reducedSquareFastRelativeSubmodule (fun _ : Unit => 1) W := hz
  have hbr := F.reducedSquareFastRelative_action_mem (fun _ : Unit => 1) W
    (fun _ => Nat.zero_lt_one) hua hz'
  refine ⟨⁅F.reducedSquareDiagonalSymbolMap (fun _ : Unit => 1)
    (F.adaptedReducedSymbolMap (fun _ : Unit => 1) a), z⁆, hbr, ?_⟩
  rw [← hp, F.reducedSquareGradedDifference_relative_lie, ha]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GradedTopCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωQ" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem quotientTopGradedMap_coordinate (x : F.AssociatedGraded) (i : QuotientTopBasisIndex s ω) :
    (bQ).repr (F.quotientTopGradedMap x) i = (F.associatedGradedBasis e ω hF).repr x i.val := by
  classical
  have he : ((bQ).coord i).comp F.quotientTopGradedMap.toLinearMap =
      (F.associatedGradedBasis e ω hF).coord i.val := by
    apply (F.associatedGradedBasis e ω hF).ext
    intro j
    change (bQ).repr (F.associatedGradedMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
      (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) (F.associatedGradedBasis e ω hF j)) i =
      (F.associatedGradedBasis e ω hF).repr (F.associatedGradedBasis e ω hF j) i.val
    rw [F.associatedGradedMap_basis_repr F.quotientTop e ω hF
      (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
      (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx),
      F.quotientTopBasis_repr_mk, Basis.repr_self, Basis.repr_self]
    by_cases hj : j = i.val <;> simp [hj]
  exact DFunLike.congr_fun he x

noncomputable def quotientTopGradedSection : F.quotientTop.AssociatedGraded →ₗ[ℚ] F.AssociatedGraded :=
  (bQ).constr ℚ (fun i => F.associatedGradedBasis e ω hF i.val)

@[simp] theorem quotientTopGradedSection_basis (i : QuotientTopBasisIndex s ω) :
    F.quotientTopGradedSection e ω hF ((bQ) i) = F.associatedGradedBasis e ω hF i.val :=
  Basis.constr_basis _ _ _ i

theorem quotientTopGradedSection_coordinate (x : F.quotientTop.AssociatedGraded)
    (i : QuotientTopBasisIndex s ω) :
    (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF x) i.val = (bQ).repr x i := by
  classical
  have he : ((F.associatedGradedBasis e ω hF).coord i.val).comp (F.quotientTopGradedSection e ω hF) =
      (bQ).coord i := by
    apply (bQ).ext
    intro j
    change (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF ((bQ) j)) i.val =
      (bQ).repr ((bQ) j) i
    rw [F.quotientTopGradedSection_basis, Basis.repr_self, Basis.repr_self]
    simp [Finsupp.single_apply, Subtype.ext_iff]
  exact DFunLike.congr_fun he x

theorem quotientTopGradedSection_coordinate_zero (x : F.quotientTop.AssociatedGraded)
    (i : ι) (hi : s + 1 ≤ ω i) :
    (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF x) i = 0 := by
  classical
  have he : ((F.associatedGradedBasis e ω hF).coord i).comp (F.quotientTopGradedSection e ω hF) = 0 := by
    apply (bQ).ext
    intro j
    change (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF ((bQ) j)) i = 0
    rw [F.quotientTopGradedSection_basis, Basis.repr_self]
    apply Finsupp.single_eq_of_ne
    exact fun hij => j.property (hij ▸ hi)
  exact DFunLike.congr_fun he x

theorem quotientTopGradedSection_rightInverse (x : F.quotientTop.AssociatedGraded) :
    F.quotientTopGradedMap (F.quotientTopGradedSection e ω hF x) = x := by
  apply (bQ).repr.injective
  ext i
  rw [F.quotientTopGradedMap_coordinate, F.quotientTopGradedSection_coordinate]

theorem quotientTopGradedMap_kernel :
    LinearMap.ker F.quotientTopGradedMap.toLinearMap =
      Submodule.span ℚ (F.associatedGradedBasis e ω hF '' {i | s + 1 ≤ ω i}) := by
  ext x
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx i hi
    have he := congrArg (fun y => (bQ).repr y ⟨i, hi⟩) (show F.quotientTopGradedMap x = 0 from hx)
    simpa only [F.quotientTopGradedMap_coordinate, map_zero, Finsupp.zero_apply] using he
  · intro hx
    change F.quotientTopGradedMap x = 0
    apply (bQ).repr.injective
    ext i
    rw [F.quotientTopGradedMap_coordinate, map_zero, Finsupp.zero_apply]
    exact hx i.val i.property

theorem reducedSquareGradedSndMap_coordinate (x : F.squareFiltration.quotientTop.AssociatedGraded)
    (i : QuotientTopBasisIndex s ω) :
    (bQ).repr (F.reducedSquareGradedSndMap x) i = (bW).repr x (reducedSquareDiagonalIndex s ω i) := by
  rw [F.quotientTop.associatedGradedBasis_repr, F.squareFiltration.quotientTop.associatedGradedBasis_repr]
  exact F.reducedSquareSndSymbolMap_repr e ω hF (fun _ : Unit => 1) x
    ⟨(unitMonomial (ω i.val), i), weight_unitMonomial (ω i.val)⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def gradedLayerOneProjection : F.AssociatedGraded →ₗ[ℚ] (L ⧸ F.layer 2) :=
  (F.layer 2).mkQ.comp
    (e.repr.symm.toLinearMap.comp (F.associatedGradedBasis e ω hF).repr.toLinearMap)

theorem gradedLayerOneProjection_coordinate (x : F.AssociatedGraded) (i : LayerOneBasisIndex ω) :
    (F.layerOneBasis e ω hF).repr (F.gradedLayerOneProjection e ω hF x) i =
      (F.associatedGradedBasis e ω hF).repr x i.val := by
  change (F.layerOneBasis e ω hF).repr
    ((F.layer 2).mkQ (e.repr.symm ((F.associatedGradedBasis e ω hF).repr x))) i = _
  rw [F.layerOneBasis_repr_mk, LinearEquiv.apply_symm_apply]

theorem layerOneGradedMap_coordinate (x : L ⧸ F.layer 2) (i : LayerOneBasisIndex ω) :
    (F.associatedGradedBasis e ω hF).repr (F.layerOneGradedMap e ω hF x) i.val =
      (F.layerOneBasis e ω hF).repr x i := by
  obtain ⟨v, rfl⟩ := (F.layer 2).mkQ_surjective x
  rw [F.layerOneGradedMap_mk, F.gradedPieceProjection_coordinate, F.layerOneBasis_repr_mk]
  have hpos := F.adaptedBasis_weight_pos e ω hF i.val
  have hnot := i.property
  rw [if_pos (show ω i.val = 1 by omega)]

theorem gradedLayerOneProjection_rightInverse (x : L ⧸ F.layer 2) :
    F.gradedLayerOneProjection e ω hF (F.layerOneGradedMap e ω hF x) = x := by
  apply (F.layerOneBasis e ω hF).repr.injective
  ext i
  rw [F.gradedLayerOneProjection_coordinate, F.layerOneGradedMap_coordinate]

theorem layerOneGradedMap_projection (x : F.AssociatedGraded) :
    F.layerOneGradedMap e ω hF (F.gradedLayerOneProjection e ω hF x) =
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω 1 x := by
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext i
  change (F.associatedGradedBasis e ω hF).repr
    (F.gradedPieceProjection e ω hF 1 (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i}
      (hF 2) (F.gradedLayerOneProjection e ω hF x))) i = _
  rw [F.gradedPieceProjection_coordinate, basisGradeProjection_repr]
  by_cases hi : ω i = 1
  · rw [if_pos hi, if_pos hi]
    have hni : ¬2 ≤ ω i := by omega
    rw [supportedQuotientSection_coordinate e (F.layer 2) {i | 2 ≤ ω i}
      (hF 2) _ ⟨i, hni⟩]
    exact F.gradedLayerOneProjection_coordinate e ω hF x ⟨i, hni⟩
  · rw [if_neg hi, if_neg hi]

theorem layerOneGradedSubmodule_eq_image (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule) :
    F.layerOneGradedSubmodule e ω hF U = U.toSubmodule.map (F.gradedLayerOneProjection e ω hF) := by
  ext x
  constructor
  · intro hx
    exact ⟨F.layerOneGradedMap e ω hF x, hx, F.gradedLayerOneProjection_rightInverse e ω hF x⟩
  · rintro ⟨v, hv, rfl⟩
    change F.layerOneGradedMap e ω hF (F.gradedLayerOneProjection e ω hF v) ∈ U
    rw [F.layerOneGradedMap_projection]
    exact hU 1 v hv

theorem gradedLayerOneProjection_spanning (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (v : κ → F.AssociatedGraded) (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (fun j => F.gradedLayerOneProjection e ω hF (v j))) =
      F.layerOneGradedSubmodule e ω hF U := by
  rw [F.layerOneGradedSubmodule_eq_image e ω hF U hU, ← hv, Submodule.map_span, ← Set.range_comp]
  rfl

theorem gradedLayerOneProjection_height (x : F.AssociatedGraded) {H : ℕ}
    (hx : ∀ i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr x i) H) :
    ∀ i, RationalHeightLE ((F.layerOneBasis e ω hF).repr (F.gradedLayerOneProjection e ω hF x) i) H := by
  intro i
  rw [F.gradedLayerOneProjection_coordinate]
  exact hx i.val

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "bG" => F.associatedGradedBasis e ω hF

theorem layerOneGradedMap_injective : Function.Injective (F.layerOneGradedMap e ω hF) := by
  intro x y hxy
  have h := congrArg (F.gradedLayerOneProjection e ω hF) hxy
  simpa only [F.gradedLayerOneProjection_rightInverse] using h

theorem layerOneGradedMap_pure (x : L ⧸ F.layer 2) :
    basisGradeProjection bG ω 1 (F.layerOneGradedMap e ω hF x) = F.layerOneGradedMap e ω hF x := by
  rw [← F.layerOneGradedMap_projection, F.gradedLayerOneProjection_rightInverse]

theorem layerOneGradedMap_coordinate_zero (x : L ⧸ F.layer 2) (i : ι) (hi : ω i ≠ 1) :
    (bG).repr (F.layerOneGradedMap e ω hF x) i = 0 := by
  have h := congrArg (fun y => (bG).repr y i) (F.layerOneGradedMap_pure e ω hF x)
  rw [basisGradeProjection_repr, if_neg hi] at h
  exact h.symm

theorem layerOneGradedMap_height (x : L ⧸ F.layer 2) {H : ℕ} (hH : 1 ≤ H)
    (hx : ∀ i, RationalHeightLE ((F.layerOneBasis e ω hF).repr x i) H) :
    ∀ i, RationalHeightLE ((bG).repr (F.layerOneGradedMap e ω hF x) i) H := by
  intro i
  by_cases hi : ω i = 1
  · have hni : ¬ 2 ≤ ω i := by omega
    rw [F.layerOneGradedMap_coordinate e ω hF x ⟨i, hni⟩]
    exact hx ⟨i, hni⟩
  · rw [F.layerOneGradedMap_coordinate_zero e ω hF x i hi]
    exact rationalHeightLE_zero hH

theorem realLayerOneGradedMap_pure (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    basisGradeProjection ((bG).baseChange ℝ) ω 1 ((F.layerOneGradedMap e ω hF).baseChange ℝ x) =
      (F.layerOneGradedMap e ω hF).baseChange ℝ x := by
  change basisCoordinateProjection ((bG).baseChange ℝ) {i | ω i = 1}
    ((F.layerOneGradedMap e ω hF).baseChange ℝ x) = _
  rw [← basisCoordinateProjection_baseChange]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    exact congrArg (fun y => a ⊗ₜ[ℚ] y) (F.layerOneGradedMap_pure e ω hF x)

noncomputable def gradedHorizontalKernel (K : Submodule ℚ (L ⧸ F.layer 2)) :
    Submodule ℚ F.AssociatedGraded := K.map (F.layerOneGradedMap e ω hF)

noncomputable def gradedHorizontalKernelEquiv (K : Submodule ℚ (L ⧸ F.layer 2)) :
    K ≃ₗ[ℚ] F.gradedHorizontalKernel e ω hF K :=
  Submodule.equivMapOfInjective (F.layerOneGradedMap e ω hF) (F.layerOneGradedMap_injective e ω hF) K

noncomputable def gradedHorizontalKernelBasis (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K) :
    Basis κ ℚ (F.gradedHorizontalKernel e ω hF K) := b.map (F.gradedHorizontalKernelEquiv e ω hF K)

theorem gradedHorizontalKernelBasis_coe (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K) (i : κ) :
    (F.gradedHorizontalKernelBasis e ω hF K b i : F.AssociatedGraded) =
      F.layerOneGradedMap e ω hF (b i : L ⧸ F.layer 2) := by
  rw [gradedHorizontalKernelBasis, Basis.map_apply]
  rfl

theorem gradedHorizontalKernel_real_mem (K : Submodule ℚ (L ⧸ F.layer 2))
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (hx : x ∈ K.baseChange ℝ) :
    (F.layerOneGradedMap e ω hF).baseChange ℝ x ∈ (F.gradedHorizontalKernel e ω hF K).baseChange ℝ := by
  rw [gradedHorizontalKernel, realification_map]
  exact ⟨x, hx, rfl⟩

theorem gradedHorizontalKernel_real_pure (K : Submodule ℚ (L ⧸ F.layer 2))
    (x : ℝ ⊗[ℚ] F.AssociatedGraded) (hx : x ∈ (F.gradedHorizontalKernel e ω hF K).baseChange ℝ) :
    basisGradeProjection ((bG).baseChange ℝ) ω 1 x = x := by
  rw [gradedHorizontalKernel, realification_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact F.realLayerOneGradedMap_pure e ω hF y

theorem gradedHorizontalKernelBasis_height (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ j i, RationalHeightLE ((F.layerOneBasis e ω hF).repr (b j : L ⧸ F.layer 2) i) H) :
    ∀ j i, RationalHeightLE ((bG).repr (F.gradedHorizontalKernelBasis e ω hF K b j : F.AssociatedGraded) i) H := by
  intro j i
  rw [F.gradedHorizontalKernelBasis_coe]
  exact F.layerOneGradedMap_height e ω hF _ hH (hb j) i

theorem gradedHorizontalKernelBasis_span (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K) :
    Submodule.span ℚ (Set.range (fun j =>
      (F.gradedHorizontalKernelBasis e ω hF K b j : F.AssociatedGraded))) =
        F.gradedHorizontalKernel e ω hF K := by
  change Submodule.span ℚ (Set.range ((F.gradedHorizontalKernel e ω hF K).subtype ∘
    F.gradedHorizontalKernelBasis e ω hF K b)) = _
  rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_gradedHorizontalKernel_quotient_basis [Fintype ι] [Fintype κ]
    (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ j i, RationalHeightLE ((F.layerOneBasis e ω hF).repr (b j : L ⧸ F.layer 2) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hk : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
      ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ f : Basis (Fin d) ℚ (F.AssociatedGraded ⧸ F.gradedHorizontalKernel e ω hF K),
        ∀ i j, RationalHeightLE (f.repr ((F.gradedHorizontalKernel e ω hF K).mkQ (bG j)) i) H' := by
  exact exists_submodule_quotient_basis_exp bG (F.gradedHorizontalKernel e ω hF K)
    (fun j => (F.gradedHorizontalKernelBasis e ω hF K b j : F.AssociatedGraded))
    (F.gradedHorizontalKernelBasis_span e ω hF K b) hH
    (F.gradedHorizontalKernelBasis_height e ω hF K b hH hb) hp hk hHp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

abbrev TopGradedBasisIndex (s : ℕ) (ω : ι → ℕ) := {i : ι // s + 1 ≤ ω i}

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

noncomputable def fullFastDiagonalGenerators
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) :
    κ ⊕ TopGradedBasisIndex s ω → F.AssociatedGraded :=
  Sum.elim (fun j => F.quotientTopGradedSection e ω hF (F.reducedSquareGradedSndMap (v j)))
    (fun i => F.associatedGradedBasis e ω hF i.val)

theorem fullFastDiagonalGenerators_span
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (F.fullFastDiagonalGenerators e ω hF v)) =
      (F.fullFastGradedDiagonal W).toSubmodule := by
  have himage : Submodule.span ℚ (Set.range (fun j => F.reducedSquareGradedSndMap (v j))) =
      (F.fastGradedDiagonal W).toSubmodule := by
    change _ = W.toSubmodule.map F.reducedSquareGradedSndMap.toLinearMap
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hker : Submodule.span ℚ (Set.range (fun i : TopGradedBasisIndex s ω =>
      F.associatedGradedBasis e ω hF i.val)) = LinearMap.ker F.quotientTopGradedMap.toLinearMap := by
    rw [F.quotientTopGradedMap_kernel e ω hF]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  exact split_preimage_spanning F.quotientTopGradedMap.toLinearMap
    (F.quotientTopGradedSection e ω hF) (F.quotientTopGradedSection_rightInverse e ω hF)
    (F.fastGradedDiagonal W).toSubmodule (fun j => F.reducedSquareGradedSndMap (v j)) himage
    (fun i : TopGradedBasisIndex s ω => F.associatedGradedBasis e ω hF i.val) hker

theorem fullFastDiagonalGenerators_height
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∀ j i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
      (F.fullFastDiagonalGenerators e ω hF v j) i) H := by
  intro j i
  cases j with
  | inl j =>
    change RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
      (F.quotientTopGradedSection e ω hF (F.reducedSquareGradedSndMap (v j))) i) H
    by_cases hi : s + 1 ≤ ω i
    · rw [F.quotientTopGradedSection_coordinate_zero e ω hF _ i hi]
      exact rationalHeightLE_zero hH
    · rw [F.quotientTopGradedSection_coordinate e ω hF _ ⟨i, hi⟩,
        F.reducedSquareGradedSndMap_coordinate]
      exact hv j _
  | inr j =>
    exact (basis_repr_height_one (F.associatedGradedBasis e ω hF) j.val i).mono hH

theorem fullFastDiagonalGenerators_card [Fintype κ] [Fintype ι] :
    Fintype.card (κ ⊕ TopGradedBasisIndex s ω) ≤ Fintype.card κ + Fintype.card ι := by
  rw [Fintype.card_sum]
  exact Nat.add_le_add_left (Fintype.card_le_of_injective Subtype.val Subtype.val_injective) _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

noncomputable def fullFastHorizontalGenerators
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) :
    κ ⊕ TopGradedBasisIndex s ω → L ⧸ F.layer 2 :=
  fun j => F.gradedLayerOneProjection e ω hF (F.fullFastDiagonalGenerators e ω hF v j)

theorem fullFastHorizontalGenerators_span
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (F.fullFastHorizontalGenerators e ω hF v)) =
      F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W) :=
  F.gradedLayerOneProjection_spanning e ω hF (F.fullFastGradedDiagonal W)
    (F.fullFastGradedDiagonal_graded e ω hF W hW) (F.fullFastDiagonalGenerators e ω hF v)
    (F.fullFastDiagonalGenerators_span e ω hF W v hv)

theorem fullFastHorizontalGenerators_height
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∀ j i, RationalHeightLE ((F.layerOneBasis e ω hF).repr
      (F.fullFastHorizontalGenerators e ω hF v j) i) H := by
  intro j
  exact F.gradedLayerOneProjection_height e ω hF (F.fullFastDiagonalGenerators e ω hF v j)
    (F.fullFastDiagonalGenerators_height e ω hF v hH hv j)

noncomputable def fullFastHorizontalMatrix
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) :
    Matrix (LayerOneBasisIndex ω) (κ ⊕ TopGradedBasisIndex s ω) ℚ :=
  fun i j => (F.layerOneBasis e ω hF).repr (F.fullFastHorizontalGenerators e ω hF v j) i

theorem fullFastHorizontalMatrix_height
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∀ i j, RationalHeightLE (F.fullFastHorizontalMatrix e ω hF v i j) H := by
  intro i j
  exact F.fullFastHorizontalGenerators_height e ω hF v hH hv j i

noncomputable def fullFastHorizontalCoordinates [Fintype ι]
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    Submodule ℝ (LayerOneBasisIndex ω → ℝ) :=
  ((F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ).map
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun.toLinearMap

theorem fullFastHorizontalMatrix_span [Fintype ι]
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℝ (Set.range ((F.fullFastHorizontalMatrix e ω hF v).map (Rat.castHom ℝ)).col) =
      F.fullFastHorizontalCoordinates e ω hF W := by
  have hspan : Submodule.span ℝ (Set.range (fun j => (1 : ℝ) ⊗ₜ[ℚ]
      F.fullFastHorizontalGenerators e ω hF v j)) =
      (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ := by
    rw [← F.fullFastHorizontalGenerators_span e ω hF W hW v hv,
      Submodule.baseChange_span, ← Set.range_comp]
    rfl
  rw [fullFastHorizontalCoordinates, ← hspan, Submodule.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext j i
  change ((F.layerOneBasis e ω hF).repr (F.fullFastHorizontalGenerators e ω hF v j) i : ℝ) =
    ((F.layerOneBasis e ω hF).baseChange ℝ).repr
      ((1 : ℝ) ⊗ₜ[ℚ] F.fullFastHorizontalGenerators e ω hF v j) i
  rw [Basis.baseChange_repr_tmul]
  simp only [Rat.smul_def, mul_one]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullFastHorizontalNormalization
namespace OAI

section

namespace Erdos3

theorem exists_controlled_derivative_absorption {H E V ι κ ν τ σ : Type*}
    [AddCommGroup H] [Module ℝ H] [AddCommGroup E] [Module ℝ E]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] [Fintype κ] [Fintype ν]
    (e : H ≃ₗ[ℝ] (ι → ℝ)) (U K : Submodule ℝ H)
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U.map e.toLinearMap)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K.map e.toLinearMap)
    (b : ν → K) (hb : ∀ j, e (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (P : E →ₗ[ℝ] H) (f : E →ₗ[ℝ] E) (hf : P.comp f = P)
    (S R : K →ₗ[ℝ] E) (hSR : S = f.comp R)
    (hS : P.comp S = K.subtype) (hR : P.comp R = K.subtype)
    (c : E →ₗ[ℝ] (τ → ℝ)) (N : E →ₗ[ℝ] V)
    (n rden : ℕ) (hRgrid : ∀ j, c (R (b j)) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) J) (hB : ∀ i j, RationalHeightLE (B i j) J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (M C : ℝ) (hC : 0 ≤ C) (hSbound : ∀ x, ‖N (S x)‖ ≤ C * ‖e x.val‖)
    (y small rational : σ → E) (k : σ → K)
    (hsystem : ∀ i, y i = small i + f (rational i) + S (k i))
    (hy : ∀ i, P (y i) ∈ U)
    (hsmall : ∀ i, ‖e (P (small i))‖ ≤ Real.exp p / T i)
    (hNsmall : ∀ i, ‖N (small i)‖ ≤ M / T i)
    (hrational : ∀ i, e (P (rational i)) ∈ realDenominatorGrid l)
    (hrgrid : ∀ i, c (rational i) ∈ realDenominatorGrid rden) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ ks kr : σ → K, ∀ i,
        P (small i - S (ks i)) ∈ U ∧
        P (rational i - R (kr i)) ∈ U ∧
        (k i + ks i + kr i).val ∈ U ∧
        y i = (small i - S (ks i)) + f (rational i - R (kr i)) + S (k i + ks i + kr i) ∧
        ‖e (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i ∧
        ‖N (small i - S (ks i))‖ ≤ (M + C * Real.exp ((p + 2) ^ 19) * Real.exp p) / T i ∧
        ‖e (P (small i - S (ks i)))‖ ≤ (1 + Real.exp ((p + 2) ^ 19)) * Real.exp p / T i ∧
        c (rational i - R (kr i)) ∈ realDenominatorGrid (rden * (n * m)) := by
  obtain ⟨m, hm, hmp, split, hsplit, hnorm, hgrid⟩ :=
    exists_controlled_kernel_split_equiv e U K A B hAspan hBspan b hb (c.comp R) n hRgrid
      hJ hl hA hB hp hι hcols hJp hlp
  let ks : σ → K := fun i => split (P (small i))
  let kr : σ → K := fun i => split (P (rational i))
  have hks (i : σ) : ‖e (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i := by
    calc
      _ ≤ Real.exp ((p + 2) ^ 19) * ‖e (P (small i))‖ := hnorm _
      _ ≤ Real.exp ((p + 2) ^ 19) * (Real.exp p / T i) :=
        mul_le_mul_of_nonneg_left (hsmall i) (Real.exp_nonneg _)
      _ = _ := by ring
  refine ⟨m, hm, hmp, ks, kr, fun i => ?_⟩
  have hproj : P (y i) = P (small i) + P (rational i) + (k i).val := by
    rw [hsystem i, map_add, map_add,
      show P (f (rational i)) = P (rational i) from DFunLike.congr_fun hf _,
      show P (S (k i)) = (k i).val from DFunLike.congr_fun hS _]
  have hparts := horizontal_parts_separation_equiv e U K A B hAspan hBspan
    hJ hl hA hB hp hι hcols hJp hlp T hT i
    (P (y i)) (P (small i)) (P (rational i)) (k i) hproj (hy i) (hsmall i) (hrational i)
  have habsorb := horizontal_absorption_with_split U K P f hf S R hSR hS hR split hsplit
    (y i) (small i) (rational i) (k i) (hsystem i) (hy i) hparts.1 hparts.2
  refine ⟨habsorb.1, habsorb.2.1, habsorb.2.2.1, habsorb.2.2.2, hks i, ?_, ?_, ?_⟩
  · calc
      _ ≤ ‖N (small i)‖ + ‖N (S (ks i))‖ := by rw [map_sub]; exact norm_sub_le _ _
      _ ≤ M / T i + C * (Real.exp ((p + 2) ^ 19) * Real.exp p / T i) :=
        add_le_add (hNsmall i) ((hSbound _).trans (mul_le_mul_of_nonneg_left (hks i) hC))
      _ = _ := by ring
  · rw [map_sub, map_sub, show P (S (ks i)) = (ks i).val from DFunLike.congr_fun hS _]
    calc
      _ ≤ ‖e (P (small i))‖ + ‖e (ks i).val‖ := norm_sub_le _ _
      _ ≤ Real.exp p / T i + Real.exp ((p + 2) ^ 19) * Real.exp p / T i :=
        add_le_add (hsmall i) (hks i)
      _ = _ := by ring
  · rw [map_sub]
    exact realDenominatorGrid_sub_product rden (n * m) _ _ (hrgrid i) (hgrid _ (hrational i))

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ν τ L V : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype ι] [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) Wf)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))

theorem exists_fullFast_derivative_absorption
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (g : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (Q : Matrix (LayerOneBasisIndex ω) ν ℚ)
    (hQspan : Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col) = K.map (cH).toLinearMap)
    (b : ν → K) (hb : ∀ j, cH (b j).val = (Q.map (Rat.castHom ℝ)).col j)
    (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (c : 𝓔 →ₗ[ℝ] (τ → ℝ)) (N : 𝓔 →ₗ[ℝ] V)
    (n rden : ℕ) (hRgrid : ∀ j, c (R (b j)) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) J)
    (hQ : ∀ i j, RationalHeightLE (Q i j) J)
    {p : ℝ} (hp : 0 ≤ p)
    (hsize : ((Fintype.card κ + Fintype.card ι + Fintype.card ν : ℕ) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (M C : ℝ) (hC : 0 ≤ C) (hSbound : ∀ x, ‖N (S x)‖ ≤ C * ‖cH x.val‖)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g i = small i + ρ g (rational i) + S (k i))
    (hsmall : ∀ i, ‖cH (𝓟 (small i))‖ ≤ Real.exp p / T i)
    (hNsmall : ∀ i, ‖N (small i)‖ ≤ M / T i)
    (hrational : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l)
    (hrgrid : ∀ i, c (rational i) ∈ realDenominatorGrid rden) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ ks kr : σ → K, ∀ i,
        𝓟 (small i - S (ks i)) ∈ 𝓤 ∧
        𝓟 (rational i - R (kr i)) ∈ 𝓤 ∧
        (k i + ks i + kr i).val ∈ 𝓤 ∧
        Y g i = (small i - S (ks i)) + ρ g (rational i - R (kr i)) + S (k i + ks i + kr i) ∧
        ‖cH (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i ∧
        ‖N (small i - S (ks i))‖ ≤ (M + C * Real.exp ((p + 2) ^ 19) * Real.exp p) / T i ∧
        ‖cH (𝓟 (small i - S (ks i)))‖ ≤ (1 + Real.exp ((p + 2) ^ 19)) * Real.exp p / T i ∧
        c (rational i - R (kr i)) ∈ realDenominatorGrid (rden * (n * m)) := by
  have hrow : Fintype.card (LayerOneBasisIndex ω) ≤ Fintype.card ι :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hrows : (Fintype.card (LayerOneBasisIndex ω) : ℝ) ≤ p := by
    have hle : Fintype.card (LayerOneBasisIndex ω) ≤
        Fintype.card κ + Fintype.card ι + Fintype.card ν := by omega
    exact (Nat.cast_le.mpr hle).trans hsize
  have hcol : Fintype.card ((κ ⊕ TopGradedBasisIndex s ω) ⊕ ν) ≤
      Fintype.card κ + Fintype.card ι + Fintype.card ν := by
    rw [Fintype.card_sum]
    exact Nat.add_le_add_right (fullFastDiagonalGenerators_card (κ := κ) (s := s) (ω := ω)) _
  have hf : (𝓟).comp (ρ g).toLinearMap = 𝓟 := by
    apply LinearMap.ext
    intro x
    exact F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      Wf e ω hF g x
  exact exists_controlled_derivative_absorption cH 𝓤 K (F.fullFastHorizontalMatrix e ω hF v) Q
    (F.fullFastHorizontalMatrix_span e ω hF W hW v hv) hQspan b hb 𝓟 (ρ g).toLinearMap hf
    S R hSR hS hR c N n rden hRgrid hJ hl (F.fullFastHorizontalMatrix_height e ω hF v hJ hheight)
    hQ hp hrows ((Nat.cast_le.mpr hcol).trans hsize) hJp hlp T hT M C hC hSbound
    (Y g) small rational k hsystem
    (fun i => F.fullFast_horizontal_derivative_mem e ω hF W hW g.val g.property hzero i)
    hsmall hNsmall hrational hrgrid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ν τ L V : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype ι] [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) Wf)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ReducedSquareGradedKernel
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

theorem quotientTopGradedMap_piece (j : ℕ) (x : F.layer j) :
    F.quotientTopGradedMap (F.associatedGradedPieceMap j x) =
      F.quotientTop.associatedGradedPieceMap j
        ⟨lieQuotientMap (F.layerIdeal (s + 1)) x,
          F.quotientLie_mem (F.layerIdeal (s + 1)) (t := s) le_rfl x.property⟩ :=
  F.quotientGradedMap_piece (F.layerIdeal (s + 1)) (t := s) le_rfl j x

theorem reducedSquareGradedSnd_piece (j : ℕ) (x : F.squareFiltration.layer j) :
    F.reducedSquareGradedSndMap
      (F.squareFiltration.quotientTopGradedMap (F.squareFiltration.associatedGradedPieceMap j x)) =
    F.quotientTopGradedMap (F.associatedGradedPieceMap j ⟨x.val.val.2, x.property.2.1⟩) := by
  simp only [reducedSquareGradedSndMap, quotientTopGradedMap]
  rfl

theorem reducedSquareGradedPiece_kernel_relative (j : ℕ) (hpos : 1 ≤ j) (hj : j ≤ s)
    (x : F.squareFiltration.layer j)
    (hx : F.reducedSquareGradedSndMap
      (F.squareFiltration.quotientTopGradedMap (F.squareFiltration.associatedGradedPieceMap j x)) = 0) :
    F.reducedSquareGradedRelativePiece j hpos ⟨x.val.val.1 - x.val.val.2, x.property.2.2⟩ =
      F.squareFiltration.quotientTopGradedMap (F.squareFiltration.associatedGradedPieceMap j x) := by
  rw [F.reducedSquareGradedSnd_piece] at hx
  have hsnd := (F.quotientTopGradedMap_piece_eq_zero_iff j hj _).mp hx
  have hd := (F.reducedSquareGradedDiagonalPiece_eq_zero_iff j hj
    ⟨x.val.val.2, x.property.2.1⟩).mpr hsnd
  have hdec := congrArg F.squareFiltration.quotientTopGradedMap
    (F.squareGradedPiece_decomposition j hpos x)
  rw [map_add] at hdec
  change _ = F.reducedSquareGradedDiagonalPiece j ⟨x.val.val.2, x.property.2.1⟩ +
    F.reducedSquareGradedRelativePiece j hpos ⟨x.val.val.1 - x.val.val.2, x.property.2.2⟩ at hdec
  rw [hd, zero_add] at hdec
  exact hdec.symm

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem exists_reducedSquareGradedRelativePiece_of_pure_kernel
    (j : ℕ) (hpos : 1 ≤ j) (hj : j ≤ s)
    (y : F.squareFiltration.quotientTop.AssociatedGraded)
    (hy : basisGradeProjection bW ωW j y = y) (hker : F.reducedSquareGradedSndMap y = 0) :
    ∃ x : F.layer (j + 1), F.reducedSquareGradedRelativePiece j hpos x = y := by
  obtain ⟨q, hq⟩ := F.squareFiltration.quotientTop.exists_associatedGradedPieceMap_of_pure
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) j y hy
  obtain ⟨x, hx, hxq⟩ := q.property
  have he : F.squareFiltration.quotientTopGradedMap
      (F.squareFiltration.associatedGradedPieceMap j ⟨x, hx⟩) = y := by
    rw [F.squareFiltration.quotientTopGradedMap_piece]
    refine Eq.trans ?_ hq
    apply congrArg (F.squareFiltration.quotientTop.associatedGradedPieceMap j)
    exact Subtype.ext hxq
  refine ⟨⟨x.val.1 - x.val.2, hx.2.2⟩, ?_⟩
  exact (F.reducedSquareGradedPiece_kernel_relative j hpos hj ⟨x, hx⟩
    (by rw [he]; exact hker)).trans he

theorem reducedSquareGradedDifference_relativePiece (j : ℕ) (hj : 1 ≤ j)
    (x : F.layer (j + 1)) :
    F.reducedSquareGradedDifference e ω hF (F.reducedSquareGradedRelativePiece j hj x) =
      F.associatedGradedPieceMap (j + 1) x := by
  change F.reducedSquareGradedDifference e ω hF
    (F.squareFiltration.quotientTopGradedMap
      (F.squareFiltration.associatedGradedPieceMap j (F.squareRelativeLayer j hj x))) = _
  rw [F.squareFiltration.quotientTopGradedMap_piece,
    ← F.squareFiltration.quotientTop.gradedPieceProjection_eq_pieceMap
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)]
  rw [F.reducedSquareGradedDifference_projection, F.reducedSquareDifference_mk]
  change F.gradedPieceProjection e ω hF (j + 1) ((x : L) - 0) = _
  rw [sub_zero, F.gradedPieceProjection_eq_pieceMap]

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.SquareModeGradedFrequency
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "δ" => F.reducedSquareGradedDifference e ω hF

theorem fullFastGradedRelative_top_frequency (hs : 1 ≤ s)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (ξ : F.squareFiltration.quotientTop.AssociatedGraded →ₗ[ℚ] ℚ)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (hrestriction : ∀ x : F.layer (s + 1),
      ξ (F.reducedSquareGradedRelativePiece s hs x) = η (F.associatedGradedPieceMap (s + 1) x))
    (hξ : ∀ y ∈ W, basisGradeProjection bW ωW s y = y → ξ y = 0) :
    ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0 := by
  rintro x ⟨y, hy, rfl⟩ hpure
  let ys := basisGradeProjection bW ωW s y
  have hys : ys ∈ F.fastGradedRelativeKernel W :=
    F.fastGradedRelativeKernel_graded e ω hF W hW s y hy
  have hysPure : basisGradeProjection bW ωW s ys = ys :=
    basisCoordinateProjection_idempotent bW {i | ωW i = s} y
  have hδ : δ ys = δ y := (F.reducedSquareGradedDifference_gradeProjection e ω hF s y).trans hpure
  obtain ⟨z, hz⟩ := F.exists_reducedSquareGradedRelativePiece_of_pure_kernel e ω hF
    s hs le_rfl ys hysPure hys.2
  calc
    η (δ y) = η (δ ys) := congrArg η hδ.symm
    _ = η (δ (F.reducedSquareGradedRelativePiece s hs z)) :=
      congrArg (fun u => η (δ u)) hz.symm
    _ = η (F.associatedGradedPieceMap (s + 1) z) :=
      congrArg η (F.reducedSquareGradedDifference_relativePiece e ω hF s hs z)
    _ = ξ (F.reducedSquareGradedRelativePiece s hs z) := (hrestriction z).symm
    _ = ξ ys := congrArg ξ hz
    _ = 0 := hξ ys hys.1 hysPure

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

local notation "bq" => F.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => F.reducedSquareBasis_layers b ω hF
local notation "bG" => F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq

theorem square_gradedFrequency_restriction (hs : 1 ≤ s)
    (η : L →ₗ[ℚ] ℚ)
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (hrestriction : ∀ x : F.layer (s + 1),
      ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (F.squareRelativeLayer s hs x).val) = η x)
    (x : F.layer (s + 1)) :
    F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ
        (F.reducedSquareGradedRelativePiece s hs x) =
      F.gradedFrequency b ω hF η (F.associatedGradedPieceMap (s + 1) x) := by
  change F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ
    (F.squareFiltration.quotientTopGradedMap
      (F.squareFiltration.associatedGradedPieceMap s (F.squareRelativeLayer s hs x))) = _
  rw [F.squareFiltration.quotientTopGradedMap_piece,
    F.squareFiltration.quotientTop.gradedFrequency_top_piece,
    F.gradedFrequency_top_piece]
  exact hrestriction x

theorem square_mode_fullFast_top_frequency (hs : 1 ≤ s)
    (η : L →ₗ[ℚ] ℚ)
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (hrestriction : ∀ x : F.layer (s + 1),
      ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (F.squareRelativeLayer s hs x).val) = η x)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bG ωq W.toSubmodule)
    (hξ : ∀ y ∈ W, basisGradeProjection bG ωq s y = y →
      F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ y = 0) :
    ∀ x ∈ F.fullFastGradedRelative b ω hF W,
      basisGradeProjection (F.associatedGradedBasis b ω hF) ω (s + 1) x = x →
        F.gradedFrequency b ω hF η x = 0 := by
  exact F.fullFastGradedRelative_top_frequency b ω hF hs W hW
    (F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ)
    (F.gradedFrequency b ω hF η)
    (F.square_gradedFrequency_restriction b ω hF hs η ξ hrestriction) hξ

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MissingCoordinateErrorAbsorption
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_absorb_missing_coordinate_error (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin (s + 1) => 1)), T.ComplexityLE p →
      ∀ {G X : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset X), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → X → Fin (s + 1) → ℤ) (f : G → X → ℂ),
      (∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 x ∈ S h, f h x * star (T.eval (sample h x))‖) →
      ∃ A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ,
        (∀ i x, ‖A i x‖ ≤ 1) ∧
        (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 x ∈ S h, f h x * ∏ i, A i (sample h x)‖ := by
  obtain ⟨a, _, hsplit⟩ := exists_missing_coordinate_niltest_approximation s 2
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * X + (X + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT G Ω H hH S hS sample f hf hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let U := T.expNormalize p
  let epsilon := Real.exp (-(2 * p + 1))
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 2 * p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hp, hcost]
  have hscale : 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [sq_nonneg p, hp]
  obtain ⟨m, _, hm, c, V, hc, hV, hindependent, happ⟩ :=
    hsplit U (T.expNormalize_complexity hT) (T.expNormalize_norm hT)
      epsilon (Real.exp_pos _) hscale
  have hepsilon : epsilon ≤ Real.exp (-(2 * p)) / 2 := by
    simpa only [epsilon, show -(2 * p + 1) = -(2 * p) - 1 by ring] using
      exp_sub_one_le_half_exp (-(2 * p))
  have hsmall : Real.exp (-(2 * p + q + 2)) ≤ Real.exp (-(2 * p)) / (2 * Real.exp q * 2) := by
    calc
      _ = Real.exp (-(2 * p + q) - 1 - 1) := by congr 1; ring
      _ ≤ Real.exp (-(2 * p + q) - 1) / 2 := exp_sub_one_le_half_exp _
      _ ≤ (Real.exp (-(2 * p + q)) / 2) / 2 :=
        div_le_div_of_nonneg_right (exp_sub_one_le_half_exp _) (by norm_num)
      _ = _ := by rw [show -(2 * p + q) = -(2 * p) - q by ring, Real.exp_sub]; ring
  let R (h : G) (_ : Unit) (j : Fin m) : Prop :=
    Real.exp (-(2 * p + q + 2)) ≤
      ‖𝔼 x ∈ S h, f h x * star (∏ i, V i j (sample h x))‖
  have hchoice : ∀ h ∈ H, ∀ u, ∃ j, R h u j := by
    intro h hh _
    have hmean : (𝔼 x ∈ S h, f h x * star (U.eval (sample h x))) =
        (Real.exp (-p) : ℂ) * (𝔼 x ∈ S h, f h x * star (T.eval (sample h x))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [U, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
        star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    have hnorm : Real.exp (-(2 * p)) ≤ ‖finiteCorrelation (S h) (f h)
        (fun x => U.eval (sample h x))‖ := by
      unfold finiteCorrelation
      rw [hmean, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
      calc
        _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcorr h hh) (Real.exp_nonneg _)
    obtain ⟨j, hj⟩ := exists_correlating_weighted_summand (hS h hh) (f h)
      (fun x => U.eval (sample h x)) (fun j x => ∏ i, V i j (sample h x)) c
      (Real.exp_pos (-(2 * p))) (Real.exp_pos q) (by norm_num : (0 : ℝ) < 2)
      (by simpa only [Fintype.card_fin] using hm) hc (hf h hh)
      (fun x _ => by rw [norm_sub_rev]; exact (happ (sample h x)).trans hepsilon) hnorm
    exact ⟨j, hsmall.trans hj⟩
  obtain ⟨j, H', hsub, hH', hdense, hfixed⟩ := exists_large_fixed_choices H hH R hchoice
    (by simpa only [Fintype.card_fin] using hm)
  refine ⟨(fun i x => star (V i (j ()) x)), ?_, ?_, H', hsub, hH', ?_, ?_⟩
  · intro i x
    simpa only [norm_star] using hV i (j ()) x
  · intro i x y hxy
    exact congrArg star (hindependent i (j ()) x y hxy)
  · have hdense' : Real.exp (-q) * (H.card : ℝ) ≤ (H'.card : ℝ) := by
      simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hdense
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense'
  · intro h hh
    simpa only [star_prod] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hfixed h hh ())

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeCoordinateDerivativeSystem
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) U
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U

def NativeCoordinateDerivativeSpec : Prop :=
  ∀ (b : Basis (Fin d) ℝ Q) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
    (_hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = Hq x)
    (sectionMap : (Fin d → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (Cscale : ℝ) (_hC : 0 ≤ Cscale)
    (_hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x → ∀ i,
        |b.equivFun ((J).mkQ x) i| ≤ Cscale * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Cscale * M) (sectionMap y)))
    (m : ℕ) (_hm : 0 < m)
    (_hgrid : ∀ y, y ∈ realDenominatorGrid 1 → F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (sectionMap y))
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) U)
    (bound : ℝ) (_hbound : 0 ≤ bound)
    (D : CoordinateDerivativeSystem ha T (b.equivFun.toLinearMap.comp (F.realFastCoefficientDirectionMap U g.val))
      (b.equivFun.symm.trans ((ρ g).trans b.equivFun))
      (fun i => monomialScale T (rows i).val.1) bound)
    (p : ℝ) (_hp : 0 ≤ p) (_hap : (a : ℝ) ≤ p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hCp : Cscale ≤ Real.exp p) (_hDp : (D.heightBound : ℝ) ≤ Real.exp p),
    D.k ≤ a ∧ ∃ (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin D.k) ℚ K),
      ∃ H : ℕ, 1 ≤ H ∧ (H : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
        (∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j : L ⧸ F.layer 2) i) H) ∧
        ∃ l : ℕ, 0 < l ∧ (l : ℝ) ≤ bound ^ 2 ∧
          ∃ S R : (K.baseChange ℝ) →ₗ[ℝ] Q,
            S = (ρ g).toLinearMap.comp R ∧ (Hq).comp S = (K.baseChange ℝ).subtype ∧
            (Hq).comp R = (K.baseChange ℝ).subtype ∧
            (∀ x, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) (S x)‖ ≤
              (bound * Cscale) * ‖cH x.val‖) ∧
            (∀ j, b.equivFun (R (realSubmoduleBasis K bK j)) ∈ realDenominatorGrid l) ∧
            ∃ (small rational : σ → Q) (k : σ → K.baseChange ℝ),
              (∀ i, F.realFastCoefficientDirectionMap U g.val (Pi.single i 1) =
                small i + ρ g (rational i) + S (k i)) ∧
              (∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l) ∧
              (∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
                bound / T i) ∧
              (∀ i, ‖cH (Hq (small i))‖ ≤ (Cscale * bound) / T i)

theorem exists_native_coordinate_derivative_system :
    F.NativeCoordinateDerivativeSpec (σ := σ) (a := a) (d := d) e ω hF U := by
  intro b rows ha η hη sectionMap hsection Cscale hC hweighted m hm hgrid
    T hT g bound hbound D p hp hap hmp hCp hDp
  have hone (α : σ →₀ ℕ) : monomialScale (fun _ : σ => (1 : ℝ)) α = 1 := by
    simp [monomialScale]
  have hsectionOne (y : Fin d → ℝ) (M : ℝ) (hM : 0 ≤ M) (hy : ∀ j, |y j| ≤ M) :
      F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) (fun _ => 1) (Cscale * M) (sectionMap y) := by
    apply (hweighted (fun _ => 1) (fun _ => by norm_num) M hM).2 y
    intro j
    simpa only [hone, div_one] using hy j
  have hprojOne (x : E) (M : ℝ) (hM : 0 ≤ M)
      (hx : F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) (fun _ => 1) M x) (j : Fin d) :
      |b.equivFun ((J).mkQ x) j| ≤ Cscale * M := by
    simpa only [hone, div_one] using
      (hweighted (fun _ => 1) (fun _ => by norm_num) M hM).1 x hx j
  have hraw := F.layerOne_rational_kernel_basis e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
    Uf b ha η hη sectionMap hsection 1 m hm Cscale hC hgrid hsectionOne
    D.K D.basisMatrix D.span_eq D.independent_real D.basis_height
  obtain ⟨v, hv, hspan, hli, hheight⟩ := hraw
  let K := Submodule.span ℚ (Set.range v)
  let bK : Basis (Fin D.k) ℚ K := Basis.span hli
  have hbK (j : Fin D.k) : (bK j : L ⧸ F.layer 2) = v j :=
    Basis.coe_span_apply hli j
  have hbasis (j : Fin D.k) : (1 : ℝ) ⊗ₜ[ℚ] (bK j : L ⧸ F.layer 2) =
      η ((D.basisMatrix.map (Rat.castHom ℝ)).col j) := by
    exact (congrArg (fun z : L ⧸ F.layer 2 => (1 : ℝ) ⊗ₜ[ℚ] z) (hbK j)).trans (hv j)
  have htransport := transport_coordinate_derivatives_to_rational_span ha b η Hq hη T
    (F.realFastCoefficientDirectionMap U g.val) (ρ g)
    (fun i => monomialScale T (rows i).val.1) bound D K bK hspan hbasis
  obtain ⟨S, R, hSR, hS, hR, hSnorm, hRgrid, small, rational, k, hsystem, hrgrid, hsmall⟩ := htransport
  let H₀ := (a + 1) * (max m (Nat.ceil ((m : ℝ) * Cscale)) * D.heightBound) ^ a
  have hH₀ : (H₀ : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    layerOne_basis_transport_height_le_exp a m D.heightBound Cscale p hp hap hmp hC hCp hDp
  have hH : ((max 1 H₀ : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (Real.one_le_exp (by positivity)) hH₀
  let l := D.liftDenominator * D.derivativeDenominator
  have hl : 0 < l := Nat.mul_pos D.liftDenominator_pos D.derivativeDenominator_pos
  have hlb : (l : ℝ) ≤ bound ^ 2 := by
    rw [Nat.cast_mul, pow_two]
    exact mul_le_mul D.liftDenominator_le D.derivativeDenominator_le (Nat.cast_nonneg _) hbound
  have hk : D.k ≤ a := by
    simpa using D.independent_real.fintype_card_le_finrank
  refine ⟨hk, K, bK, max 1 H₀, le_max_left _ _, hH, ?_, l, hl, hlb,
    S, R, hSR, hS, hR, ?_, ?_, small, rational, k, ?_, ?_, hsmall, ?_⟩
  · intro i j
    exact (congrArg (fun z : L ⧸ F.layer 2 =>
      RationalHeightLE ((F.layerOneBasis e ω hF).repr z i) (max 1 H₀)) (hbK j)).mpr
        ((hheight i j).mono (le_max_right 1 H₀))
  · intro x
    have hx := F.layerOne_equiv_symm_norm e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
      Uf b ha η hη Cscale hC hprojOne x.val
    calc
      _ ≤ bound * ‖η.symm x.val‖ := hSnorm x
      _ ≤ bound * (Cscale * ‖cH x.val‖) := mul_le_mul_of_nonneg_left hx hbound
      _ = (bound * Cscale) * ‖cH x.val‖ := (mul_assoc _ _ _).symm
  · intro j
    exact realDenominatorGrid_subset_of_dvd D.liftDenominator_pos
      (dvd_mul_right D.liftDenominator D.derivativeDenominator) (hRgrid j)
  · intro i
    exact hsystem i
  · intro i
    exact realDenominatorGrid_subset_of_dvd D.derivativeDenominator_pos
      (dvd_mul_left D.derivativeDenominator D.liftDenominator) (hrgrid i)
  · intro i
    have hx := F.realFastCoefficientHorizontal_section_norm_bound e ω hF (fun _ => 1)
      (fun _ => Nat.zero_lt_one) Uf b sectionMap hsection rows T hT Cscale hC
      (fun M hM => (hweighted T hT M hM).2) (small i)
    calc
      _ ≤ Cscale * ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ := hx
      _ ≤ Cscale * (bound / T i) := mul_le_mul_of_nonneg_left (hsmall i) hC
      _ = (Cscale * bound) / T i := (mul_div_assoc _ _ _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFixedPositiveDensity
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (o : OrthonormalBasis I ℝ W)

theorem canonicalMixedDensity_continuous_of_ambient
    (c w : I → ℝ) (f : Fin n → ℝ → ℝ) (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) =
      basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1 / 4)
    (hc : Continuous (canonicalAmbientTorusDensity W b o c w f)) :
    Continuous (canonicalMixedDensity W b hb o c w p) := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (latticeSection (standardEuclideanLattice D) W).toAddSubgroup).continuous_iff.mpr
  have hlift : Continuous (fun u : W => fun i => (u.val i : UnitAddCircle)) := by
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)
  have he : canonicalMixedDensity W b hb o c w p ∘ QuotientAddGroup.mk =
      fun u : W => canonicalAmbientTorusDensity W b o c w f
        (fun i => (u.val i : UnitAddCircle)) := by
    funext u
    exact (canonicalAmbientTorusDensity_eq W b hb o c w f p hf hs u).symm
  rw [he]
  exact hc.comp hlift

theorem canonicalArrayDensity_continuous {J : Type*} [Fintype J]
    (c w : I → J → ℝ) (f : J → Fin n → ℝ → ℝ) (p : Fin n → J → PMF ℤ)
    (hf : ∀ j i (k : ℤ), f j i ((k : ℝ) / basisAxisScale b i) =
      basisAxisScale b i * (p i j k).toReal)
    (hs : ∀ j x, mixedCoefficientDensity (fun i => c i j) (fun i => w i j)
      (fun i => p i j) x ≠ 0 → ∀ d,
        |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1 / 4)
    (hc : ∀ j, Continuous
      (canonicalAmbientTorusDensity W b o (fun i => c i j) (fun i => w i j) (f j))) :
    Continuous (canonicalArrayDensity W b hb o c w p) := by
  apply continuous_finsetProd
  intro j _
  exact (canonicalMixedDensity_continuous_of_ambient W b hb o _ _ (f j) _
    (hf j) (hs j) (hc j)).comp (continuous_apply j)

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

theorem canonicalCoefficientDensity_continuous
    {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
    [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (f : ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) → Fin (n j) → ℝ → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hf : ∀ j e i (k : ℤ), f j e i ((k : ℝ) / basisAxisScale (b j) i) =
      basisAxisScale (b j) i * (p j i e k).toReal)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → ∀ d,
        |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) x) d| ≤ 1 / 4)
    (hc : ∀ j e, Continuous (canonicalAmbientTorusDensity
      (euclideanSubspace (U j)) (b j) (o j) (fun i => c j i e) (fun i => w j i e) (f j e))) :
    Continuous (canonicalCoefficientDensity U b hb o c w p) := by
  apply continuous_finsetProd
  intro j _
  exact (canonicalArrayDensity_continuous _ (b j) (hb j) (o j) (c j) (w j) (f j) (p j)
    (hf j) (hs j) (hc j)).comp
      ((continuous_apply j).comp (euclideanCoefficientEquiv_continuous U))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hC hV hσ1 Cinv hCinv hchart hsmall

theorem allocatedCoefficientDensity_continuous :
    Continuous (allocatedCoefficientDensity B U b hb o hR hσ S) := by
  apply canonicalCoefficientDensity_continuous U b hb o
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (fun j e i => allocatedLayerIntegerInterpolation B U b S j i e)
    (allocatedLayerIntegerPMFs B U b hR hσ S)
    (fun j e i => (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i e).1)
    (allocatedLayerColumns_quarter_support B U b hR hσ S o hσ1 Cinv hCinv hchart hsmall)
  intro j e
  exact (allocatedAmbientFactor_bounds B U b S o C V hC hV hR hσ ⟨j, e⟩).2.continuous

theorem allocatedCoefficientDensity_bounds :
    ∀ x, allocatedCoefficientDensity B U b hb o hR hσ S x ∈
      Set.Icc (0 : ℝ) ((allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)) := by
  intro x
  rw [← allocatedCoefficientAmbientDensity_eq B U b hb o S hR hσ hσ1 Cinv hCinv hchart hsmall x]
  exact (allocatedCoefficientAmbientDensity_bounds B U b o S C V hC hV hR hσ).1 _

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem allocatedCoefficientDensity_positive_spec :
    Continuous (allocatedCoefficientDensity B U b hb o hR hσ S) ∧
      (∀ x, allocatedCoefficientDensity B U b hb o hR hσ S x ∈
        Set.Icc (0 : ℝ) ((allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
          Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))) ∧
      Integrable (allocatedCoefficientDensity B U b hb o hR hσ S) μ ∧
      (∫ x, allocatedCoefficientDensity B U b hb o hR hσ S x ∂μ) = 1 ∧
      (allocatedCoefficientSource B U b hR hσ S).map (canonicalCoefficientSample U b hb o) =
        realDensityMeasure μ (allocatedCoefficientDensity B U b hb o hR hσ S) := by
  have h := allocatedCoefficientDensity_spec B U b hb o hR hσ S hσ1 Cinv hCinv hchart hsmall μ ν
  exact ⟨allocatedCoefficientDensity_continuous B U b hb o hR hσ S C V hC hV
      hσ1 Cinv hCinv hchart hsmall,
    allocatedCoefficientDensity_bounds B U b hb o hR hσ S C V hC hV
      hσ1 Cinv hCinv hchart hsmall, h.2.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped Classical NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)

include hC hV hσ1 hCinv hchart hsmall in
theorem allocatedCoefficientDensity_fixedScale_le_exp
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hSP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    allocatedCoefficientDensity B U b hb o hR hσ S x ≤
      Real.exp (allocatedFourierLogBudget m P) := by
  have hcap := (allocatedCoefficientDensity_bounds B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall x).2
  have hbudget := allocatedCoefficient_fourier_input_budget B R σ S.value S.positive C V
    hP hm hK hR hσ hRP hσP hcount hI hn hJ hAP hSP hCP hVP
  exact hcap.trans hbudget.2.2.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end


