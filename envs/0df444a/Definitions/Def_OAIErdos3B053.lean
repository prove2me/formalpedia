-- Prove2me | Definitions.Def_OAIErdos3B053
-- name    : OAIErdos3B053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T12:49:57.121654+00:00
-- url     : https://prove2.me/theorems/a704b1f2-6e95-46aa-990c-a22834f81043
-- title:
--   OpenAI Erdős-3 split, definitions bundle 54 of 134
-- statement:
--   Definitions bundle 54 of 134 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B052`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 54 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieBCHGroup.exists_bounded_kernel_grid_enumeration`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_bounded_kernel_grid_enumeration_exp`, `OAI.Erdos3.VectorPolynomial.CoefficientAmbientIndex`, `OAI.Erdos3.VectorPolynomial.allocatedAmbientConstants_exp_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedAmbientFactorCap`, `OAI.Erdos3.VectorPolynomial.allocatedAmbientFactorCap_one_le`, `OAI.Erdos3.VectorPolynomial.allocatedAmbientFactorLip`, `OAI.Erdos3.VectorPolynomial.allocatedAmbientFactor_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedAmbientLayerLip`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientAmbientDensity`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientAmbientDensity_eq`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientDensity`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientDensity_spec`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientSource`, `OAI.Erdos3.VectorPolynomial.allocatedLayerCenters`, `OAI.Erdos3.VectorPolynomial.allocatedLayerCenters_constant`, `OAI.Erdos3.VectorPolynomial.allocatedLayerColumns_chart`, `OAI.Erdos3.VectorPolynomial.allocatedLayerColumns_quarter_support`, `OAI.Erdos3.VectorPolynomial.allocatedLayerCommonCap`, `OAI.Erdos3.VectorPolynomial.allocatedLayerCommonCap_one_le`, `OAI.Erdos3.VectorPolynomial.allocatedLayerCommonInterpolation_exp_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedLayerCommonLip`, `OAI.Erdos3.VectorPolynomial.allocatedLayerIntegerInterpolation`, `OAI.Erdos3.VectorPolynomial.allocatedLayerIntegerInterpolationCap`, `OAI.Erdos3.VectorPolynomial.allocatedLayerIntegerInterpolationLip`, `OAI.Erdos3.VectorPolynomial.allocatedLayerIntegerInterpolation_exp_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedLayerIntegerInterpolation_lipschitz`, `OAI.Erdos3.VectorPolynomial.allocatedLayerIntegerInterpolation_spec`, `OAI.Erdos3.VectorPolynomial.allocatedLayerIntegerPMFs`, `OAI.Erdos3.VectorPolynomial.allocatedLayerIntegerPMFs_constant`, `OAI.Erdos3.VectorPolynomial.allocatedLayerInterpolation_common_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedLayerMixedCap`, `OAI.Erdos3.VectorPolynomial.allocatedLayerMixedInterpolation_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedLayerMixedLip`, `OAI.Erdos3.VectorPolynomial.allocatedLayerMixed_exp_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedLayerWidthFloor`, `OAI.Erdos3.VectorPolynomial.allocatedLayerWidthFloor_inv_exp`, `OAI.Erdos3.VectorPolynomial.allocatedLayerWidthFloor_pos`, `OAI.Erdos3.VectorPolynomial.allocatedLayerWidths`, `OAI.Erdos3.VectorPolynomial.allocatedLayerWidths_constant`, `OAI.Erdos3.VectorPolynomial.allocatedLayerWidths_floor`, `OAI.Erdos3.VectorPolynomial.allocatedLayerWidths_pos`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalNormalizedSource`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample_injOn_chart`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample_injOn_smallAmbient`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckSample_residue_injective`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientSample_injOn_chart`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientDensity`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientDensity_bounds`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientDensity_eq`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientFactor`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientFactor_eq`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientHom`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientIndex_card_le_real`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientInputPolynomial`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientSlice`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientSlice_lipschitz`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientTorus`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientTorus_character`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientTorus_injective`, `OAI.Erdos3.VectorPolynomial.coefficientCoverKernelFintype`, `OAI.Erdos3.VectorPolynomial.coefficientCoverKernel_finite`, `OAI.Erdos3.VectorPolynomial.coefficientSamplerAmbientPoint`, `OAI.Erdos3.VectorPolynomial.coefficientSamplerDeckInteger`, `OAI.Erdos3.VectorPolynomial.coefficientSlot_card_le`, `OAI.Erdos3.VectorPolynomial.coefficient_ambient_input_exp_bounds`, `OAI.Erdos3.VectorPolynomial.exists_coefficient_ambient_fourier_approximation`, `OAI.Erdos3.allocatedAmbientLog`, `OAI.Erdos3.allocatedAmbientLog_nonneg`, `OAI.Erdos3.allocatedArrayColumns_quarter_support`, `OAI.Erdos3.allocatedCommonLog`, `OAI.Erdos3.allocatedCommonLog_nonneg`, `OAI.Erdos3.allocatedMixedLog`, `OAI.Erdos3.allocatedMixedLog_nonneg`, `OAI.Erdos3.allocatedScalarLog`, `OAI.Erdos3.allocatedScalarLog_nonneg`, `OAI.Erdos3.allocatedWidthLog`, `OAI.Erdos3.allocatedWidthLog_nonneg`, `OAI.Erdos3.ambientInterpolation_constants_exp_bounds`, `OAI.Erdos3.canonicalAmbientKernel`, `OAI.Erdos3.canonicalAmbientKernel_bounds`, `OAI.Erdos3.canonicalAmbientKernel_eq_of_lift`, `OAI.Erdos3.canonicalAmbientKernel_support`, `OAI.Erdos3.canonicalAmbientTorusDensity`, `OAI.Erdos3.canonicalAmbientTorusDensity_bounds`, `OAI.Erdos3.canonicalAmbientTorusDensity_eq`, `OAI.Erdos3.coordinate_integer_translate_sub_mem`, `OAI.Erdos3.exists_ambient_torus_fourier_approximation`, `OAI.Erdos3.exists_coordinate_integer_translate`, `OAI.Erdos3.exists_finite_primitive_correction_budget`, `OAI.Erdos3.exists_scalar_rational_grid_window`, `OAI.Erdos3.finite_card_real_grid_window`, `OAI.Erdos3.latticeDeckInteger`, `OAI.Erdos3.mixedCoefficient_quarter_support`, `OAI.Erdos3.normalizedCoverLift_add_deck`, `OAI.Erdos3.real_grid_window_count_le_exp`, `OAI.Erdos3.smallBoxTorusKernel`, `OAI.Erdos3.smallBoxTorusKernel_lipschitz`, `OAI.Erdos3.smallBoxTorusKernel_range`, `OAI.Erdos3.subspaceAmbientTorus_character`, `OAI.Erdos3.sum_le_exp_of_card_and_uniform_bound`, `_private.Dynamics.FinitePrimitiveCorrectionBudget.0.OAI.Erdos3.primitive_correction_denominator_bound`, `_private.Dynamics.FinitePrimitiveCorrectionBudget.0.OAI.Erdos3.primitive_correction_dimension_bound`, `_private.Sampling.BoundedKernelGridEnumerationBudget.0.OAI.Erdos3.real_grid_integer_box_count_bound`, `_private.Sampling.BoundedKernelGridEnumerationBudget.0.OAI.Erdos3.real_grid_shifted_integer_bound`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B114
import Definitions.Def_OAIErdos3B127

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedLayerCenters (j : Fin m) :
    I j → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ :=
  allocatedArrayCenters Subtype.val (layerSamplerBox B U b S) (layerContinuousPrincipalSlots B j) (R j)

noncomputable def allocatedLayerWidths (j : Fin m) :
    I j → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ :=
  allocatedArrayWidths Subtype.val (layerSamplerBox B U b S) (layerContinuousPrincipalSlots B j)
    (constantCoefficientSlot _ _) (R j) (σ j)

include hR hσ in
theorem allocatedLayerWidths_pos (j : Fin m) (i : I j) (d) :
    0 < allocatedLayerWidths B U b S j i d :=
  allocatedArrayWidths_pos _ _ (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v))
    _ _ (hR j) (hσ j) i d

noncomputable def allocatedLayerIntegerPMFs (j : Fin m) :
    Fin (n j) → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → PMF ℤ :=
  allocatedProjectionPMFs (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value (layerTailDegree m) (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include hR hσ in
theorem allocatedLayerColumns_chart (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (j : Fin m) (d) (x) (hx : mixedCoefficientDensity (fun i => allocatedLayerCenters B U b S j i d)
      (fun i => allocatedLayerWidths B U b S j i d)
      (fun i => allocatedLayerIntegerPMFs B U b hR hσ S j i d) x ≠ 0) :
    normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) ∈
      standardLatticeSmallBox (J j) := by
  exact allocatedArrayColumns_chart (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value (layerTailDegree m) (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)
    (layerContinuousPrincipalSlots B j) (o j) (layerContinuousPrincipalSlots_not_constant B j)
    (layerIntegerPrincipalSlots_not_constant B j) rfl (hσ1 j)
    (layerSamplerSides_integer_principal B U b R S.value j) (hC j) (hchart j) (hsmall j) d x hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerCenters_constant (j : Fin m) (i : I j) :
    allocatedLayerCenters B U b S j i (constantCoefficientSlot _ _) = 0 := by
  classical
  simp only [allocatedLayerCenters, allocatedArrayCenters, coefficientProfileCenter,
    if_neg (layerContinuousPrincipalSlots_not_constant B j i), zero_div]

theorem allocatedLayerWidths_constant (j : Fin m) (i : I j) :
    allocatedLayerWidths B U b S j i (constantCoefficientSlot _ _) = R j / 4 := by
  classical
  simp [allocatedLayerWidths, allocatedArrayWidths, coefficientProfileWidth,
    constantCoefficientSlot, monomialScale]

theorem allocatedLayerIntegerPMFs_constant (j : Fin m) (i : Fin (n j)) :
    allocatedLayerIntegerPMFs B U b hR hσ S j i (constantCoefficientSlot _ _) =
      latticeConstantMass (euclideanSubspace (U j)) (b j) (fun _ => R j / 4)
        (fun _ => div_pos (hR j) (by norm_num)) i := by
  classical
  simp only [allocatedLayerIntegerPMFs, allocatedProjectionPMFs,
    allocatedIntegerPolynomialCoordinatePMF, integerPolynomialCoordinatePMF,
    ite_true, latticeConstantMass]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedLayerIntegerInterpolationCap (R σ : Fin m → ℝ) (L : ℕ)
    (j : Fin m) (i : Fin (n j)) : ℝ :=
  integerPolynomialInterpolationCap (j.val+1) L (layerTailDegree m) (R j / 4)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

noncomputable def allocatedLayerIntegerInterpolationLip (R σ : Fin m → ℝ) (L : ℕ)
    (j : Fin m) (i : Fin (n j)) : ℝ :=
  integerPolynomialInterpolationLip (j.val+1) L (layerTailDegree m) (R j / 4)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedLayerIntegerInterpolation (j : Fin m) (i : Fin (n j))
    (d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ → ℝ :=
  integerPolynomialInterpolation (layerIntegerPrincipalSlots (G := G) B j i) (constantCoefficientSlot _ _)
    (j.val+1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (layerSamplerBox B U b S) Subtype.val
    (R j / 4) (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))) d

theorem allocatedLayerIntegerInterpolation_spec (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (d) :
    IsIntegerMassInterpolation (basisAxisScale (b j) i) (allocatedLayerIntegerPMFs B U b hR hσ S j i d)
      (allocatedLayerIntegerInterpolationCap (G := G) B R σ S.value j i)
      (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j i)
      (allocatedLayerIntegerInterpolation B U b S j i d) := by
  exact integerPolynomialInterpolation_spec (layerIntegerPrincipalSlots (G := G) B j i) (constantCoefficientSlot _ _)
    (j.val+1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (Nat.zero_lt_succ _) (basisAxisScale_pos (b j) i)
    S.positive (layerSamplerBox B U b S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j)) (R j / 4)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))
    (div_pos (hR j) (by norm_num)) (principalProfileSize_pos (hR j) _) (tailProfileSize_pos (hR j) (hσ j) _)
    (S.gap j i) (S.width j) d

theorem allocatedLayerIntegerInterpolation_lipschitz (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (d) :
    LipschitzWith (Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j i))
      (allocatedLayerIntegerInterpolation B U b S j i d) := by
  apply (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d).lipschitz
  unfold allocatedLayerIntegerInterpolationLip integerPolynomialInterpolationLip
    constantIntegerInterpolationLip principalAxisInterpolationLip tailAxisInterpolationLip
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "profile" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

noncomputable def allocatedPrincipalNormalizedSource : NormalizedScalarCubeSource Empty :=
  principalNormalizedSource
    (K := (basisAxisScale (basis j) i : ℝ)) (T := (S.value : ℝ) ^ (j.val + 1))
    (γ := profile)
    (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _) (principalProfileSize_pos (hR j) _)
    (integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive
      (principalProfileSize_pos (hR j) _) (S.gap j i hactive))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedLayerCommonCap (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  1 + ∑ i, Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ L j i)

noncomputable def allocatedLayerCommonLip (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  ∑ i, Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ L j i)

noncomputable def allocatedLayerWidthFloor (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  Real.toNNReal (allocatedWidthFloor (R j) (σ j) L (j.val+1)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

theorem allocatedLayerCommonCap_one_le (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) :
    1 ≤ allocatedLayerCommonCap (G := G) B R σ L j := le_add_of_nonneg_right (by positivity)

theorem allocatedLayerWidthFloor_pos {R σ : Fin m → ℝ}
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) {L : ℕ} (hL : 0 < L) (j : Fin m) :
    0 < allocatedLayerWidthFloor (G := G) B R σ L j := by
  apply Real.toNNReal_pos.mpr
  exact allocatedWidthFloor_pos (hR j) (hσ j) hL _ _

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerWidths_floor (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : I j) (d) :
    (allocatedLayerWidthFloor (G := G) B R σ S.value j : ℝ) ≤ allocatedLayerWidths B U b S j i d := by
  rw [allocatedLayerWidthFloor, Real.coe_toNNReal _ (allocatedWidthFloor_pos (hR j) (hσ j) S.positive _ _).le]
  exact allocatedArrayWidths_floor Subtype.val (layerSamplerBox B U b S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v))
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (hR j) (hσ j) S.positive
    (layerSamplerBox_le B U b S) (fun d => d.property) i d

theorem allocatedLayerInterpolation_common_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (d) :
    (∀ x, 0 ≤ allocatedLayerIntegerInterpolation B U b S j i d x ∧
      allocatedLayerIntegerInterpolation B U b S j i d x ≤ allocatedLayerCommonCap (G := G) B R σ S.value j) ∧
    LipschitzWith (allocatedLayerCommonLip (G := G) B R σ S.value j)
      (allocatedLayerIntegerInterpolation B U b S j i d) := by
  have hspec := allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d
  have hcap : Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ S.value j i) ≤
      allocatedLayerCommonCap (G := G) B R σ S.value j := by
    apply le_trans (Finset.single_le_sum
      (f := fun t : Fin (n j) => Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ S.value j t))
      (fun _ _ => zero_le) (Finset.mem_univ i))
    exact le_add_of_nonneg_left (by norm_num)
  have hlip : Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j i) ≤
      allocatedLayerCommonLip (G := G) B R σ S.value j := by
    unfold allocatedLayerCommonLip
    exact Finset.single_le_sum
      (f := fun t : Fin (n j) => Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ S.value j t))
      (fun _ _ => zero_le) (Finset.mem_univ i)
  refine ⟨?_, (allocatedLayerIntegerInterpolation_lipschitz B U b S hR hσ j i d).weaken hlip⟩
  intro x
  exact ⟨(hspec.2.1 x).1, (hspec.2.1 x).2.trans ((Real.le_coe_toNNReal _).trans (by exact_mod_cast hcap))⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem sum_le_exp_of_card_and_uniform_bound {I : Type*} [Fintype I]
    (f : I → ℝ) {P Q : ℝ} (hQ : 0 ≤ Q) (hcard : (Fintype.card I : ℝ) ≤ P)
    (hf : ∀ i, f i ≤ Real.exp Q) : (∑ i, f i) ≤ Real.exp (P + P * Q) := by
  have h := sum_le_exp_card_add_sum f (fun _ => Q) (fun _ => hQ) hf
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact h.trans (Real.exp_le_exp.mpr (add_le_add hcard (mul_le_mul_of_nonneg_right hcard hQ)))

def allocatedScalarLog (m : ℕ) (P : ℝ) : ℝ :=
  7 * integerInterpolationLogEnvelope (layerTailDegree m) (4 * (P+8))

def allocatedCommonLog (m : ℕ) (P : ℝ) : ℝ := P + P * allocatedScalarLog m P + 1

def allocatedWidthLog (m : ℕ) (P : ℝ) : ℝ := ((m : ℝ)+4)*(P+8)

theorem allocatedScalarLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedScalarLog m P := by
  unfold allocatedScalarLog integerInterpolationLogEnvelope
  positivity

theorem allocatedCommonLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedCommonLog m P := by
  have h := allocatedScalarLog_nonneg m hP
  unfold allocatedCommonLog
  positivity

theorem allocatedWidthLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedWidthLog m P := by
  unfold allocatedWidthLog
  positivity

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedLayerIntegerInterpolation_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (L : ℝ) ≤ Real.exp P)
    (i : Fin (n j)) :
    allocatedLayerIntegerInterpolationCap (G := G) B R σ L j i ≤ Real.exp (allocatedScalarLog m P) ∧
      allocatedLayerIntegerInterpolationLip (G := G) B R σ L j i ≤ Real.exp (allocatedScalarLog m P) := by
  have hprincipalCount : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ P :=
    (Nat.cast_le.mpr (layerIntegerPrincipalSlots (G := G) B j i).card_le_univ).trans hcount
  have hp := allocatedProfile_inverse_exp_bounds _ hP hR hσ hRP hσP hprincipalCount
  have ht := allocatedProfile_inverse_exp_bounds _ hP hR hσ hRP hσP hcount
  have hQ : 0 ≤ 4*(P+8) := by positivity
  have hPQ : P ≤ 4*(P+8) := by linarith
  have he := Real.exp_le_exp.mpr hPQ
  have h := integerPolynomialInterpolation_exp_bounds (layerTailDegree m) (j.val+1) L (layerTailDegree m)
    (layerDegree_le_tailDegree j) le_rfl hQ (hAP.trans he) (hLP.trans he)
    (div_pos hR (by norm_num)) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _)
    hp.1 hp.2.1 ht.2.2.2
  have henv : 0 ≤ integerInterpolationLogEnvelope (layerTailDegree m) (4*(P+8)) := by
    unfold integerInterpolationLogEnvelope
    positivity
  refine ⟨h.1.trans (Real.exp_le_exp.mpr ?_), h.2⟩
  change 3 * integerInterpolationLogEnvelope (layerTailDegree m) (4*(P+8)) ≤
    7 * integerInterpolationLogEnvelope (layerTailDegree m) (4*(P+8))
  linarith

theorem allocatedLayerCommonInterpolation_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hn : (n j : ℝ) ≤ P) (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (L : ℝ) ≤ Real.exp P) :
    (allocatedLayerCommonCap (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedCommonLog m P) ∧
      (allocatedLayerCommonLip (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedCommonLog m P) := by
  have h := allocatedLayerIntegerInterpolation_exp_bounds B R σ L j hP hR hσ hRP hσP hcount hAP hLP
  have hcard : (Fintype.card (Fin (n j)) : ℝ) ≤ P := by simpa only [Fintype.card_fin] using hn
  have hc := sum_le_exp_of_card_and_uniform_bound
    (fun i => (Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ L j i) : ℝ))
    (allocatedScalarLog_nonneg m hP) hcard (fun i => coe_toNNReal_le_exp (h i).1)
  have hl := sum_le_exp_of_card_and_uniform_bound
    (fun i => (Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ L j i) : ℝ))
    (allocatedScalarLog_nonneg m hP) hcard (fun i => coe_toNNReal_le_exp (h i).2)
  constructor
  · simp only [allocatedLayerCommonCap, NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum]
    exact one_add_le_exp_succ (by have h := allocatedScalarLog_nonneg m hP; positivity) hc
  · simp only [allocatedLayerCommonLip, NNReal.coe_sum]
    exact hl.trans (Real.exp_le_exp.mpr (by unfold allocatedCommonLog; linarith))

theorem allocatedLayerWidthFloor_inv_exp (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hLP : (L : ℝ) ≤ Real.exp P) :
    (((allocatedLayerWidthFloor (G := G) B R σ L j)⁻¹ : ℝ≥0) : ℝ) ≤ Real.exp (allocatedWidthLog m P) := by
  rw [NNReal.coe_inv, allocatedLayerWidthFloor,
    Real.coe_toNNReal _ (allocatedWidthFloor_pos hR hσ hL _ _).le]
  exact allocatedWidthFloor_inverse_exp_bound L (j.val+1) m _ (Nat.succ_le_of_lt j.isLt)
    hP hR hσ hRP hσP hcount hLP

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedLayerQuarterSupport
namespace OAI

section

namespace Erdos3

open Module Submodule

theorem mixedCoefficient_quarter_support {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) (o : OrthonormalBasis I ℝ W)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart W b).symm x‖ ≤ C * ‖x‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1/4)
    (c w : I → ℝ) (hw : ∀ i, 0 < w i) (hcw : ∀ i, |c i| + w i ≤ R)
    (p : Fin n → PMF ℤ)
    (hp : ∀ i k, k ∈ (p i).support → |(k : ℝ) / basisAxisScale b i| ≤ R)
    (x : (I → ℝ) × (Fin n → ℤ)) (hx : mixedCoefficientDensity c w p x ≠ 0) :
    ∀ d, |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4 := by
  obtain ⟨hu, hz⟩ := (mixedCoefficientDensity_support c w p x).mp hx
  have hn := mixedRealPoint_norm_le W b o hC hR hchart x.1
    (fun i => (x.2 i : ℝ) / basisAxisScale b i)
    (fun i => (affineProbabilityProfile_abs_le _ (hw i) (hu i)).trans (hcw i))
    (fun i => hp i _ (hz i))
  rw [mixedRealPoint_integer] at hn
  have hquarter : ‖normalizedLatticePoint W b (orthonormalMixedChart o x)‖ ≤ 1/4 :=
    hn.trans (by simpa only [mul_assoc] using hsmall)
  intro d
  have hd : |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤
      ‖normalizedLatticePoint W b (orthonormalMixedChart o x)‖ := by
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (normalizedLatticePoint W b (orthonormalMixedChart o x)) d
  exact hd.trans hquarter

end Erdos3

end

section

namespace Erdos3

open Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
variable (Pc : I → Finset J)

local notation "intLaws" => allocatedProjectionPMFs W b Pz j₀ h L s hh hL T hT hTL e he R σ hR hσ hgap hεL

theorem allocatedArrayColumns_quarter_support (o : OrthonormalBasis I ℝ W)
    (hc₀ : ∀ i, j₀ ∉ Pc i) (hz₀ : ∀ i, j₀ ∉ Pz i) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ i j, j ∈ Pz i → monomialScale T (e j) =
      (integerAxisSideLength h (basisAxisScale b i) L (principalProfileSize R (Pz i).card) : ℝ) ^ h)
    {C : ℝ} (hC : 0 ≤ C)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1 / 4)
    (j : J) (x : (I → ℝ) × (Fin n → ℤ))
    (hx : mixedCoefficientDensity (fun i => allocatedArrayCenters e T Pc R i j)
      (fun i => allocatedArrayWidths e T Pc j₀ R σ i j) (fun i => intLaws i j) x ≠ 0) :
    ∀ d, |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4 := by
  apply mixedCoefficient_quarter_support W b o hC hR.le hchart hsmall _ _
    (fun i => allocatedArrayWidths_pos e T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) Pc j₀ hR hσ i j)
    (fun i => allocatedArrayProfiles_bound e T hT Pc j₀ hc₀ hR hσ hσ1 i j) _ _ x hx
  intro i k hk
  apply scaledAbs_le_of_bound (one_le_monomialScale T hT (e j))
  exact (allocatedIntegerCoefficient_bound (Pz i) j₀ h (basisAxisScale b i) L s hh
    (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
    R σ hR hσ hσ1 (hgap i) hεL (hz₀ i) he₀ (hprincipal i) j hk).trans (by linarith)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem allocatedLayerColumns_quarter_support (hσ1 : ∀ j, σ j ≤ 1)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (j : Fin m) (d) (x)
    (hx : mixedCoefficientDensity (fun i => allocatedLayerCenters B U b S j i d)
      (fun i => allocatedLayerWidths B U b S j i d)
      (fun i => allocatedLayerIntegerPMFs B U b hR hσ S j i d) x ≠ 0) :
    ∀ a, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4 := by
  exact allocatedArrayColumns_quarter_support (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value (layerTailDegree m) (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)
    (layerContinuousPrincipalSlots B j) (o j) (layerContinuousPrincipalSlots_not_constant B j)
    (layerIntegerPrincipalSlots_not_constant B j) rfl (hσ1 j)
    (layerSamplerSides_integer_principal B U b R S.value j) (hC j) (hchart j) (hsmall j) d x hx

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalAmbientKernel
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalAmbientKernel (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (v : D → ℝ) : ℝ :=
  smallBoxCutoff v * mixedAmbientInterpolation W b o c w f v

theorem canonicalAmbientKernel_support (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (v : D → ℝ) (hv : canonicalAmbientKernel W b o c w f v ≠ 0) :
    ∀ i, |v i| < 1/2 :=
  smallBoxCutoff_support v (left_ne_zero_of_mul hv)

theorem canonicalAmbientKernel_eq_of_lift (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) = basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4)
    (u : W) (v : D → ℝ)
    (hv : u.val - (EuclideanSpace.equiv D ℝ).symm v ∈ standardEuclideanLattice D)
    (hsmall : ∀ d, |v d| < 1/2) :
    canonicalAmbientKernel W b o c w f v = canonicalMixedDensity W b hb o c w p
      (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) := by
  obtain ⟨y, hy, hq⟩ := exists_normalized_chart_lift W b hb u _ hv
  let x := (orthonormalMixedChart o).symm y
  have hx : normalizedLatticePoint W b (orthonormalMixedChart o x) =
      (EuclideanSpace.equiv D ℝ).symm v := by
    simpa only [x, MeasurableEquiv.apply_symm_apply] using hy
  have hqx : normalizedLatticeQuotient W b hb (orthonormalMixedChart o x) =
      QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u := by
    simpa only [x, MeasurableEquiv.apply_symm_apply] using hq
  have hgrid : mixedAmbientInterpolation W b o c w f v =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        mixedCoefficientDensity c w p x := by
    simpa only [Prod.mk.eta, hx, ContinuousLinearEquiv.apply_symm_apply] using
      mixedAmbientInterpolation_grid W b o c w f p hf x.1 x.2
  have hd : canonicalMixedDensity W b hb o c w p
      (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        mixedCoefficientDensity c w p x := by
    rw [← hqx]
    apply canonicalMixedDensity_apply W b hb o
    rw [hx]
    exact hsmall
  rw [canonicalAmbientKernel, hgrid, hd]
  by_cases hzero : mixedCoefficientDensity c w p x = 0
  · rw [hzero, mul_zero, mul_zero]
  · have hquarter : ∀ d, |v d| ≤ 1/4 := by
      have hh := hs x hzero
      rw [hx] at hh
      exact hh
    rw [smallBoxCutoff_one v hquarter, one_mul]

theorem canonicalAmbientKernel_bounds (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    {M J C V : ℝ≥0}
    (hM : ∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧ mixedDensityInterpolation c w f x ≤ M)
    (hJ : LipschitzWith J (mixedDensityInterpolation c w f))
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖)
    (hV : 0 ≤ mixedDensityCovolumeRatio W b ∧ mixedDensityCovolumeRatio W b ≤ V) :
    (∀ x, 0 ≤ canonicalAmbientKernel W b o c w f x ∧
      canonicalAmbientKernel W b o c w f x ≤ V * M) ∧
    LipschitzWith (V * (J * (C * Fintype.card D)) + (V * M) * 8)
      (canonicalAmbientKernel W b o c w f) := by
  obtain ⟨hcap, hlip⟩ := mixedAmbientInterpolation_bounds W b o c w f hM hJ hC hV
  refine ⟨?_, smallBoxCutoff_mul_lipschitz _ hlip ?_⟩
  · intro x
    refine ⟨mul_nonneg (smallBoxCutoff_range x).1 (hcap x).1, ?_⟩
    exact (mul_le_mul_of_nonneg_right (smallBoxCutoff_range x).2 (hcap x).1).trans
      (by simpa only [one_mul] using (hcap x).2)
  · intro x
    rw [abs_of_nonneg (hcap x).1]
    exact (hcap x).2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CanonicalDensityFourier
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_ambient_torus_fourier_approximation {J : Type*} [Fintype J]
    (f : (J → UnitAddCircle) → ℂ) (L B : ℝ≥0) (hf : LipschitzWith L f)
    (hB : ∀ x, ‖f x‖ ≤ B) {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hJ : (Fintype.card J : ℝ) ≤ P) (hL : (L : ℝ) ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → J → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a j, |(frequency a j : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * B ∧
      ∀ x, ‖f x - ∑ a, c a * ∏ j, CircleFourier.character (frequency a j • x j)‖ ≤ δ := by
  classical
  have hact : ∀ t : J → UnitAddCircle, Isometry (fun x : J → UnitAddCircle => t +ᵥ x) :=
    fun t => isometry_add_left t
  let A := CircleFourier.torusCoordinateAction hact
  have horbit : ∀ i (t : UnitAddCircle) x, dist ((A i).act t x) x ≤ (1 : ℝ≥0) * ‖t‖ := by
    intro i t x
    change dist ((Pi.single i t : J → UnitAddCircle) + x) x ≤ (1 : ℝ) * ‖t‖
    rw [one_mul, dist_eq_norm, add_sub_cancel_right]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg t)).mpr
    intro j
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  obtain ⟨F, inst, frequency, v, hcard, hfrequency, hv, hchar, _, herr⟩ :=
    CircleFourier.exists_controlled_commuting_circle_decomposition A
      (CircleFourier.torusCoordinateAction_commutes hact) f L B 1 hf hB horbit δ P hδ hP hJ hL
      (by simpa using Real.one_le_exp hP) hδP
  let _ := inst
  have he (a : F) (x : J → UnitAddCircle) :
      v a x = (∏ j, CircleFourier.character (frequency a j • x j)) * v a 0 := by
    have hc : ∀ i (t : UnitAddCircle) z,
        v a ((Pi.single i t : J → UnitAddCircle) +ᵥ z) = CircleFourier.character (frequency a i • t) * v a z :=
      fun i t z => hchar a i t z
    have hh := CircleFourier.torus_character_of_coordinate_characters (v a) (frequency a) hc x 0
    change v a (x + 0) = _ at hh
    simpa only [add_zero] using hh
  refine ⟨F, inst, frequency, fun a => v a 0, hcard, hfrequency, ?_, ?_⟩
  · calc
      _ ≤ ∑ _a : F, (B : ℝ) := Finset.sum_le_sum (fun a _ => (hv a).2 0)
      _ = (Fintype.card F : ℝ) * B := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard B.coe_nonneg
  · intro x
    have hs : (∑ a, v a x) = ∑ a, v a 0 * ∏ j, CircleFourier.character (frequency a j • x j) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [he a x, mul_comm]
    simpa only [hs, norm_sub_rev] using herr x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem subspaceAmbientTorus_character {J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : J → ℤ) (x : SubspaceArrayTorus Unit U) :
    (∏ j, CircleFourier.character (frequency j • subspaceAmbientTorus U x j)) =
      subspaceArrayCharacter U (Matrix.of (fun (_ : Unit) j => frequency j)) x := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice Unit U) x
  simp only [subspaceAmbientTorus_mk]
  change _ = CircleFourier.character
    ((∑ _u : Unit, ∑ j, (frequency j : ℝ) * (y ()).val j : ℝ) : UnitAddCircle)
  rw [Fintype.sum_unique, character_real_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D]

noncomputable def smallBoxTorusKernel (H : (D → ℝ) → ℝ) : (D → UnitAddCircle) → ℝ :=
  realPeriodicTorusLift (positiveIntegerPeriodization H)

theorem smallBoxTorusKernel_lipschitz (H : (D → ℝ) → ℝ) {L : ℝ≥0}
    (hL : LipschitzWith L H) (h0 : ∀ x, 0 ≤ H x)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith L (smallBoxTorusKernel H) :=
  realPeriodicTorusLift_lipschitz _ (positiveIntegerPeriodization_lipschitz H hL h0 hs)
    (positiveIntegerPeriodization_periodic H)

omit [Fintype D] in
theorem smallBoxTorusKernel_range (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, 0 ≤ H x ∧ H x ≤ B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → UnitAddCircle) :
    0 ≤ smallBoxTorusKernel H x ∧ smallBoxTorusKernel H x ≤ B :=
  realPeriodicTorusLift_range _ (positiveIntegerPeriodization_range H hB hH hs) x

end Erdos3

end

section

namespace Erdos3
open scoped Classical

variable {D : Type*} [Fintype D]

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem coordinate_integer_translate_sub_mem (u : EuclideanSpace ℝ D) (z : D → ℤ) :
    u - (EuclideanSpace.equiv D ℝ).symm (fun i => u i + (z i : ℝ)) ∈
      standardEuclideanLattice D := by
  apply (mem_standardEuclideanLattice D _).mpr
  intro i
  refine ⟨-z i, ?_⟩
  change ((-z i : ℤ) : ℝ) = u i - (u i + (z i : ℝ))
  push_cast
  ring

theorem exists_coordinate_integer_translate (u v : EuclideanSpace ℝ D)
    (hv : u - v ∈ standardEuclideanLattice D) :
    ∃ z : D → ℤ, (fun i => v i) = fun i => u i + (z i : ℝ) := by
  choose z hz using (mem_standardEuclideanLattice D _).mp hv
  refine ⟨fun i => -z i, ?_⟩
  funext i
  have hi : (z i : ℝ) = u i - v i := hz i
  push_cast
  linarith

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalAmbientTorusDensity (c w : I → ℝ) (f : Fin n → ℝ → ℝ) :
    (D → UnitAddCircle) → ℝ :=
  smallBoxTorusKernel (canonicalAmbientKernel W b o c w f)

theorem canonicalAmbientTorusDensity_eq (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) = basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4)
    (u : W) :
    canonicalAmbientTorusDensity W b o c w f (fun i => (u.val i : UnitAddCircle)) =
      canonicalMixedDensity W b hb o c w p
        (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) := by
  let H := canonicalAmbientKernel W b o c w f
  let d := canonicalMixedDensity W b hb o c w p
    (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u)
  have hsupport : ∀ v, H v ≠ 0 → ∀ i, |v i| < 1/2 :=
    canonicalAmbientKernel_support W b o c w f
  have hlocal (v : D → ℝ)
      (hv : u.val - (EuclideanSpace.equiv D ℝ).symm v ∈ standardEuclideanLattice D)
      (hvsmall : ∀ i, |v i| < 1/2) : H v = d :=
    canonicalAmbientKernel_eq_of_lift W b hb o c w f p hf hs u v hv hvsmall
  change realPeriodicTorusLift (positiveIntegerPeriodization H)
    (fun i => (u.val i : UnitAddCircle)) = d
  rw [realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic H)]
  by_cases hd : d = 0
  · rw [hd]
    have hz : ∀ z : D → ℤ, H (fun i => u.val i + (z i : ℝ)) = 0 := by
      intro z
      by_cases hz : H (fun i => u.val i + (z i : ℝ)) = 0
      · exact hz
      · exact (hlocal _ (coordinate_integer_translate_sub_mem u.val z) (hsupport _ hz)).trans hd
    simp only [positiveIntegerPeriodization, hz, tsum_zero]
  · obtain ⟨x, hxsmall, hq, _⟩ := canonicalMixedDensity_recover W b hb o c w p hd
    let v := normalizedLatticePoint W b (orthonormalMixedChart o x)
    have hv : u.val - v ∈ standardEuclideanLattice D :=
      normalizedLatticePoint_sub_mem_of_mk_eq W b hb u _ hq.symm
    obtain ⟨z, hz⟩ := exists_coordinate_integer_translate u.val v hv
    calc
      positiveIntegerPeriodization H (fun i => u.val i) =
          positiveIntegerPeriodization H (fun i => v i) := by
        rw [hz]
        exact (positiveIntegerPeriodization_periodic H _ z).symm
      _ = H (fun i => v i) := positiveIntegerPeriodization_local H hsupport _ hxsmall
      _ = d := hlocal _ hv hxsmall

theorem canonicalAmbientTorusDensity_bounds (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    {M J C V : ℝ≥0}
    (hM : ∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧ mixedDensityInterpolation c w f x ≤ M)
    (hJ : LipschitzWith J (mixedDensityInterpolation c w f))
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖)
    (hV : 0 ≤ mixedDensityCovolumeRatio W b ∧ mixedDensityCovolumeRatio W b ≤ V) :
    (∀ x, 0 ≤ canonicalAmbientTorusDensity W b o c w f x ∧
      canonicalAmbientTorusDensity W b o c w f x ≤ V * M) ∧
    LipschitzWith (V * (J * (C * Fintype.card D)) + (V * M) * 8)
      (canonicalAmbientTorusDensity W b o c w f) := by
  obtain ⟨hcap, hlip⟩ := canonicalAmbientKernel_bounds W b o c w f hM hJ hC hV
  exact ⟨smallBoxTorusKernel_range _ (mul_nonneg V.coe_nonneg M.coe_nonneg) hcap
      (canonicalAmbientKernel_support W b o c w f),
    smallBoxTorusKernel_lipschitz _ hlip (fun x => (hcap x).1)
      (canonicalAmbientKernel_support W b o c w f)⟩

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientAmbientCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}

abbrev CoefficientAmbientIndex (K : Type*) {m : ℕ} (J : Fin m → Type*) :=
  Σ s : CoefficientSlot K m, J s.1

def coefficientAmbientSlice (s : CoefficientSlot K m)
    (v : CoefficientAmbientIndex K J → UnitAddCircle) : J s.1 → UnitAddCircle :=
  fun i => v ⟨s, i⟩

noncomputable def coefficientAmbientTorus (U : ∀ j, Submodule ℝ (J j → ℝ))
    (x : CoefficientTorus (K := K) U) : CoefficientAmbientIndex K J → UnitAddCircle :=
  fun t => subspaceAmbientTorus (U t.1.1) (coefficientCoordinateTorus U x t.1) t.2

variable [Fintype K] [∀ j, Fintype (J j)]

theorem coefficientAmbientSlice_lipschitz (s : CoefficientSlot K m) :
    LipschitzWith 1 (coefficientAmbientSlice (J := J) s) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact dist_le_pi_dist x y ⟨s, i⟩

theorem coefficientAmbientTorus_character (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : CoefficientAmbientIndex K J → ℤ) (x : CoefficientTorus (K := K) U) :
    (∏ t, CircleFourier.character (frequency t • coefficientAmbientTorus U x t)) =
      coefficientTorusCharacter U (coefficientSlotFrequency (fun s i => frequency ⟨s, i⟩)) x := by
  rw [coefficientTorusCharacter_slot_product, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro s _
  exact subspaceAmbientTorus_character (U s.1) (fun i => frequency ⟨s, i⟩)
    (coefficientCoordinateTorus U x s)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientAmbientBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem coefficientSlot_card_le {K : Type*} [Fintype K] (m : ℕ) :
    Fintype.card (CoefficientSlot K m) ≤ m * (m + 1) * (Fintype.card K + 1) ^ m := by
  simp only [CoefficientSlot, Fintype.card_sigma]
  calc
    _ ≤ ∑ _j : Fin m, (m + 1) * (Fintype.card K + 1) ^ m := by
      apply Finset.sum_le_sum
      intro j _
      apply (boundedCoefficientExponent_card_le (j.val + 1)).trans
      apply Nat.mul_le_mul (by omega)
      exact Nat.pow_le_pow_right (by omega) (Nat.succ_le_of_lt j.isLt)
    _ = _ := by simp; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem coefficientAmbientIndex_card_le_real {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P) :
    (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤
      (m : ℝ) * (m + 1) * (P + 1)^m * P := by
  have hs : (Fintype.card (CoefficientSlot K m) : ℝ) ≤ (m : ℝ) * (m + 1) * (P + 1)^m := by
    have h := Nat.cast_le (α := ℝ).mpr (coefficientSlot_card_le (K := K) m)
    push_cast at h
    exact h.trans (by gcongr)
  calc
    _ = ∑ s : CoefficientSlot K m, (Fintype.card (J s.1) : ℝ) := by
      rw [Fintype.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _s : CoefficientSlot K m, P := Finset.sum_le_sum (fun s _ => hJ s.1)
    _ = (Fintype.card (CoefficientSlot K m) : ℝ) * P := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hs hP

noncomputable def coefficientAmbientInputPolynomial (m : ℕ) : Polynomial ℕ :=
  Polynomial.C (m * (m + 1)) * (Polynomial.X + 1)^m * (Polynomial.X + 1) + Polynomial.X + 1

theorem coefficient_ambient_input_exp_bounds {m : ℕ} {K : Type*} [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P A L Q : ℝ}
    (hP : 0 ≤ P) (hK : (Fintype.card K : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hA : 0 ≤ A) (hAP : A ≤ Real.exp P) (hL : 0 ≤ L) (hLP : L ≤ Real.exp P)
    (hbudget : (m : ℝ) * (m + 1) * (P + 1)^m * (P + 1) + P + 1 ≤ Q) :
    P ≤ Q ∧ (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q ∧
      A^Fintype.card (CoefficientSlot K m) ≤ Real.exp Q ∧
      (Fintype.card (CoefficientSlot K m) : ℝ) * L * A^Fintype.card (CoefficientSlot K m) ≤
        Real.exp Q := by
  let T := (m : ℝ) * (m + 1) * (P + 1)^m
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpoly' : T * (P + 1) + P + 1 ≤ Q := hbudget
  have hN : (Fintype.card (CoefficientSlot K m) : ℝ) ≤ T := by
    have h := Nat.cast_le (α := ℝ).mpr (coefficientSlot_card_le (K := K) m)
    push_cast at h
    exact h.trans (by dsimp [T]; gcongr)
  have hNP : (Fintype.card (CoefficientSlot K m) : ℝ) * P ≤ T * P :=
    mul_le_mul_of_nonneg_right hN hP
  have hcap : A^Fintype.card (CoefficientSlot K m) ≤
      Real.exp ((Fintype.card (CoefficientSlot K m) : ℝ) * P) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hA hAP (Fintype.card (CoefficientSlot K m))
  have hNexp : (Fintype.card (CoefficientSlot K m) : ℝ) ≤ Real.exp T :=
    hN.trans (by linarith [Real.add_one_le_exp T])
  refine ⟨(by nlinarith), ?_, ?_, ?_⟩
  · exact (coefficientAmbientIndex_card_le_real hP hK hJ).trans (by dsimp [T] at hpoly'; nlinarith)
  · exact hcap.trans (Real.exp_le_exp.mpr (by nlinarith))
  · calc
      _ ≤ Real.exp T * Real.exp P * Real.exp ((Fintype.card (CoefficientSlot K m) : ℝ) * P) := by gcongr
      _ = Real.exp (T + P + (Fintype.card (CoefficientSlot K m) : ℝ) * P) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BoundedKernelGridEnumerationBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

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

theorem finite_card_real_grid_window {ι : Type*} [Fintype ι]
    (S : Set (ι → ℝ)) (m N : ℕ) (hm : 0 < m) (center : ι → ℝ) {B : ℝ}
    (hgrid : S ⊆ realDenominatorGrid m)
    (hwindow : ∀ x ∈ S, ∀ i, |x i - center i| ≤ B)
    (hN : (m : ℝ) * B ≤ N) :
    S.Finite ∧ S.ncard ≤ (2 * N + 3) ^ Fintype.card ι := by
  classical
  let z : S → ι → ℤ := fun x => Classical.choose (hgrid x.property)
  have hz (x : S) (i : ι) : (m : ℝ) * x.val i = (z x i : ℝ) :=
    (congrFun (Classical.choose_spec (hgrid x.property)) i).symm
  let shift : ι → ℤ := fun i => ⌊(m : ℝ) * center i⌋
  have hzi (x : S) (i : ι) :
      z x i - shift i ∈ Set.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1) := by
    have hb := real_grid_shifted_integer_bound (hz x i) (hwindow x x.property i) hN
    apply abs_le.mp
    exact_mod_cast hb
  let f : S → (ι → Set.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)) :=
    fun x i => ⟨z x i - shift i, hzi x i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : z x i - shift i = z y i - shift i := congrArg Subtype.val (congrFun hxy i)
    have hi' : z x i = z y i := by omega
    apply mul_left_cancel₀ (show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne')
    rw [hz, hz, hi']
  let : Finite S := Finite.of_injective f hf
  have hcardI : Fintype.card (Set.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)) = 2 * N + 3 := by
    have h := Int.card_fintype_Icc_of_le (-((N : ℤ) + 1)) ((N : ℤ) + 1)
      (show -((N : ℤ) + 1) ≤ (N : ℤ) + 1 + 1 by omega)
    omega
  refine ⟨Set.toFinite S, ?_⟩
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fun, hcardI] using hc

end Erdos3

end

section

namespace Erdos3

theorem exists_scalar_rational_grid_window (q : ℕ) (hq : 0 < q) (c B : ℝ) :
    ∃ S : Finset ℚ, S.card ≤ 2 * ⌈(q : ℝ) * B⌉₊ + 3 ∧
      ∀ r : ℚ, r ∈ S ↔
        (∃ z : ℤ, (r : ℝ) = (z : ℝ) / q) ∧ |(r : ℝ) - c| ≤ B := by
  classical
  let S : Set ℚ := {r | (∃ z : ℤ, (r : ℝ) = (z : ℝ) / q) ∧ |(r : ℝ) - c| ≤ B}
  let f : ℚ → Unit → ℝ := fun r _ => r
  let V : Set (Unit → ℝ) := f '' S
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hgrid : V ⊆ realDenominatorGrid q := by
    rintro v ⟨r, ⟨⟨z, hz⟩, _⟩, rfl⟩
    refine ⟨fun _ => z, ?_⟩
    funext i
    change (z : ℝ) = (q : ℝ) * (r : ℝ)
    rw [hz]
    field_simp
  have hwindow : ∀ v ∈ V, ∀ i, |v i - c| ≤ B := by
    rintro v ⟨r, hr, rfl⟩ i
    exact hr.2
  obtain ⟨hVfin, hVcard⟩ := finite_card_real_grid_window V q ⌈(q : ℝ) * B⌉₊ hq
    (fun _ => c) hgrid hwindow (Nat.le_ceil _)
  have hinj : Function.Injective f := by
    intro r t h
    have hr : (r : ℝ) = (t : ℝ) := congrFun h ()
    exact_mod_cast hr
  have hmaps : Set.MapsTo f S V := fun r hr => ⟨r, hr, rfl⟩
  have hSfin : S.Finite := Set.Finite.of_injOn hmaps hinj.injOn hVfin
  have hcard : S.ncard ≤ 2 * ⌈(q : ℝ) * B⌉₊ + 3 := by
    have h := (Set.ncard_le_ncard_of_injOn f hmaps hinj.injOn hVfin).trans hVcard
    simpa only [Fintype.card_unit, pow_one] using h
  refine ⟨hSfin.toFinset, ?_, ?_⟩
  · simpa only [Set.ncard_eq_toFinset_card S hSfin] using hcard
  · intro r
    exact hSfin.mem_toFinset

end Erdos3

end

section

namespace Erdos3

theorem real_grid_window_count_le_exp (d m : ℕ) {B p : ℝ}
    (hp : 0 ≤ p) (hB0 : 0 ≤ B) (hd : (d : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp p) :
    (((2 * ⌈(m : ℝ) * B⌉₊ + 3) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 3) ^ 3) := by
  have hprod : (m : ℝ) * B ≤ Real.exp (2 * p) := by
    simpa only [two_mul, Real.exp_add] using
      mul_le_mul hm hB hB0 (Real.exp_nonneg p)
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) hB0)).le
  have hone : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by linarith)
  have hseven : (7 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have hbase : ((2 * ⌈(m : ℝ) * B⌉₊ + 3 : ℕ) : ℝ) ≤ Real.exp (2 * p + 6) := by
    rw [Real.exp_add]
    push_cast
    have h := mul_le_mul_of_nonneg_left hseven (Real.exp_nonneg (2 * p))
    nlinarith
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (2 * p + 6)) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = Real.exp ((d : ℝ) * (2 * p + 6)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (p * (2 * p + 6)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (by positivity))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hp (sq_nonneg p)]

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup
open Module

variable {ι L G : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [LieAlgebra ℝ L] [Group G]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_kernel_grid_enumeration [IsScalarTower ℚ ℝ L] (b : Basis ι ℝ L)
    (π : NilpotentLieBCHGroup L s hnil →* G) (m N : ℕ) (hm : 0 < m)
    {B : ℝ} (hB : 0 ≤ B) (hN : (m : ℝ) * B ≤ N) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (2 * N + 1) ^ Fintype.card ι ∧
      ∃ center : Fin n → NilpotentLieBCHGroup L s hnil,
        (∀ j, π (center j) = 1 ∧ (∀ i, |b.repr (center j).coord i| ≤ B) ∧
          b.equivFun (center j).coord ∈ realDenominatorGrid m) ∧
        ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
          (∀ i, |b.repr g.coord i| ≤ B) →
          b.equivFun g.coord ∈ realDenominatorGrid m → ∃ j, center j = g := by
  classical
  let A : Set (ι → ℝ) := {x | x ∈ realDenominatorGrid m ∧ ∀ i, |x i| ≤ B}
  obtain ⟨hAfin, hAcard⟩ := finite_card_real_grid_box A m N hm
    (fun _ hx => hx.1) (fun _ hx => hx.2) hN
  let S : Set (NilpotentLieBCHGroup L s hnil) :=
    {g | π g = 1 ∧ (∀ i, |b.repr g.coord i| ≤ B) ∧
      b.equivFun g.coord ∈ realDenominatorGrid m}
  let f : NilpotentLieBCHGroup L s hnil → (ι → ℝ) := fun g => b.equivFun g.coord
  have hf : Function.Injective f := by
    intro g h hgh
    apply NilpotentLieBCHGroup.ext
    exact b.equivFun.injective hgh
  have hmaps : Set.MapsTo f S A := by
    intro g hg
    exact ⟨hg.2.2, by simpa only [f, Basis.equivFun_apply] using hg.2.1⟩
  have hSfin : S.Finite := Set.Finite.of_injOn hmaps hf.injOn hAfin
  have hScard : S.ncard ≤ (2 * N + 1) ^ Fintype.card ι :=
    (Set.ncard_le_ncard_of_injOn f hmaps hf.injOn hAfin).trans hAcard
  let : Fintype S := hSfin.fintype
  have hone : (1 : NilpotentLieBCHGroup L s hnil) ∈ S := by
    refine ⟨map_one π, ?_, ?_⟩
    · simpa only [coord_one, map_zero, Finsupp.zero_apply, abs_zero] using fun _ : ι => hB
    · simpa only [coord_one, map_zero] using realDenominatorGrid_zero (ι := ι) m
  let : Nonempty S := ⟨⟨1, hone⟩⟩
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, Fintype.card_pos, ?_, fun j => (e.symm j).val,
    fun j => (e.symm j).property, ?_⟩
  · simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hScard
  · intro g hmark hbound hgrid
    let x : S := ⟨g, hmark, hbound, hgrid⟩
    exact ⟨e x, congrArg Subtype.val (e.symm_apply_apply x)⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

theorem real_grid_integer_box_count_bound (d m : ℕ) {B p : ℝ}
    (hp : 0 ≤ p) (hB0 : 0 ≤ B) (hd : (d : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp p) :
    (((2 * ⌈(m : ℝ) * B⌉₊ + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  have hprod : (m : ℝ) * B ≤ Real.exp (2 * p) := by
    simpa only [two_mul, Real.exp_add] using
      mul_le_mul hm hB hB0 (Real.exp_nonneg p)
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) hB0)).le
  have hone : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by linarith)
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbase : ((2 * ⌈(m : ℝ) * B⌉₊ + 1 : ℕ) : ℝ) ≤ Real.exp (2 * p + 4) := by
    rw [Real.exp_add]
    push_cast
    have h := mul_le_mul_of_nonneg_left hfive (Real.exp_nonneg (2 * p))
    nlinarith
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (2 * p + 4)) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = Real.exp ((d : ℝ) * (2 * p + 4)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (p * (2 * p + 4)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (by positivity))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hp (sq_nonneg p)]

namespace NilpotentLieBCHGroup
open Module

variable {ι L G : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L] [Group G]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_kernel_grid_enumeration_exp (b : Basis ι ℝ L)
    (π : NilpotentLieBCHGroup L s hnil →* G) (m : ℕ) (hm : 0 < m)
    {B p : ℝ} (hp : 0 ≤ p) (hB0 : 0 ≤ B) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp p) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∃ center : Fin n → NilpotentLieBCHGroup L s hnil,
        (∀ j, π (center j) = 1 ∧ (∀ i, |b.repr (center j).coord i| ≤ B) ∧
          b.equivFun (center j).coord ∈ realDenominatorGrid m) ∧
        ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
          (∀ i, |b.repr g.coord i| ≤ B) →
          b.equivFun g.coord ∈ realDenominatorGrid m → ∃ j, center j = g := by
  obtain ⟨n, hn, hcard, center, hcenters, hcover⟩ :=
    exists_bounded_kernel_grid_enumeration b π m ⌈(m : ℝ) * B⌉₊ hm hB0 (Nat.le_ceil _)
  refine ⟨n, hn, ?_, center, hcenters, hcover⟩
  exact (Nat.cast_le.mpr hcard).trans
    (real_grid_integer_box_count_bound (Fintype.card ι) m hp hB0 hd hmp hB)

end NilpotentLieBCHGroup
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FinitePrimitiveCorrectionBudget
namespace OAI

section

namespace Erdos3

theorem primitive_correction_denominator_bound (q d s : ℕ) {t : ℝ}
    (hq : (q : ℝ) ≤ Real.exp t) (hd : (d : ℝ) ≤ Real.exp t) :
    ((q * d ^ s : ℕ) : ℝ) ≤ Real.exp (((s : ℝ) + 1) * t) := by
  have hp : ((d ^ s : ℕ) : ℝ) ≤ Real.exp ((s : ℝ) * t) := by
    rw [Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg d) hd s).trans_eq (Real.exp_nat_mul t s).symm
  calc
    _ = (q : ℝ) * ((d ^ s : ℕ) : ℝ) := by rw [Nat.cast_mul]
    _ ≤ Real.exp t * Real.exp ((s : ℝ) * t) :=
      mul_le_mul hq hp (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((s : ℝ) + 1) * t) := by rw [← Real.exp_add]; congr 1; ring

theorem primitive_correction_dimension_bound (u i r s : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hu : (u : ℝ) ≤ p) (hi : (i : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) :
    ((((u + i + 1) ^ s) * r : ℕ) : ℝ) ≤ p * (2 * p + 1) ^ s := by
  have hbase : ((u + i + 1 : ℕ) : ℝ) ≤ 2 * p + 1 := by push_cast; linarith
  have hpw := pow_le_pow_left₀ (Nat.cast_nonneg (u + i + 1)) hbase s
  push_cast at hpw
  push_cast
  calc
    _ ≤ (2 * p + 1) ^ s * p :=
      mul_le_mul hpw hr (Nat.cast_nonneg _) (pow_nonneg (by positivity) s)
    _ = _ := mul_comm _ _

theorem exists_finite_primitive_correction_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (u b i r q d : ℕ) (p L M : ℝ),
      0 ≤ p → (u : ℝ) ≤ p → (b : ℝ) ≤ p → (i : ℝ) ≤ p → (r : ℝ) ≤ p →
      (q : ℝ) ≤ Real.exp ((p + a) ^ a) → (d : ℝ) ≤ Real.exp ((p + a) ^ a) →
      L ≤ Real.exp ((p + a) ^ a) → 0 ≤ M → M ≤ Real.exp ((p + a) ^ a) →
      let Rcap := ((((u + b : ℕ) : ℝ) + 1) ^ s * M) * (max 1 ((i : ℝ) * L)) ^ s
      ((((2 * ⌈((q * d ^ s : ℕ) : ℝ) * Rcap⌉₊ + 3) ^ ((u + i + 1) ^ s)) ^ r : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := X * (2 * X + 1) ^ s + Polynomial.C s * (3 * X + 1) +
    Polynomial.C (s + 1) * (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro u b i r q d p L M hp hu hb hi hr hq hd hL hM hMcap Rcap
  let t := (p + a) ^ a
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let p' := p * (2 * p + 1) ^ s + (s : ℝ) * (3 * p + 1) + ((s : ℝ) + 1) * t
  have hp' : 0 ≤ p' := by dsimp [p']; positivity
  have hfirst0 : 0 ≤ p * (2 * p + 1) ^ s := by positivity
  have hmid0 : 0 ≤ (s : ℝ) * (3 * p + 1) := by positivity
  have hlast0 : 0 ≤ ((s : ℝ) + 1) * t := by positivity
  have hdim : ((((u + i + 1) ^ s) * r : ℕ) : ℝ) ≤ p' :=
    (primitive_correction_dimension_bound u i r s hp hu hi hr).trans (by dsimp [p']; linarith)
  have hdenom : ((q * d ^ s : ℕ) : ℝ) ≤ Real.exp p' :=
    (primitive_correction_denominator_bound q d s hq hd).trans
      (Real.exp_le_exp.mpr (by dsimp [p']; linarith))
  have hR := primitiveCorrectionRadius_le_exp s u b i hp ht hu hb hi hM hMcap hL
  have hR0 : 0 ≤ Rcap := primitiveCorrectionRadius_nonneg s u b i L hM
  have hRcap : Rcap ≤ Real.exp p' := hR.trans
    (Real.exp_le_exp.mpr (by dsimp [p']; linarith))
  have hcount := real_grid_window_count_le_exp (((u + i + 1) ^ s) * r) (q * d ^ s)
    hp' hR0 hdim hdenom hRcap
  rw [pow_mul] at hcount
  exact hcount.trans (Real.exp_le_exp.mpr (by
    simpa [P, X, p', t, Polynomial.eval₂_pow] using hbudget p hp))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CoefficientAmbientDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)

noncomputable def coefficientAmbientFactor (s : CoefficientSlot K m) :
    (J s.1 → UnitAddCircle) → ℝ :=
  canonicalAmbientTorusDensity (euclideanSubspace (U s.1)) (b s.1) (o s.1)
    (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2)

noncomputable def coefficientAmbientDensity (v : CoefficientAmbientIndex K J → UnitAddCircle) : ℝ :=
  ∏ s : CoefficientSlot K m,
    coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s v)

variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
variable (hf : ∀ j i d (k : ℤ), f j i d ((k : ℝ) / basisAxisScale (b j) i) =
  basisAxisScale (b j) i * (p j i d k).toReal)
variable (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
  (fun i => p j i d) x ≠ 0 → ∀ a,
    |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4)

include hf hs in
omit [Fintype K] in
theorem coefficientAmbientFactor_eq (s : CoefficientSlot K m) (x : CoefficientTorus (K := K) U) :
    coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s (coefficientAmbientTorus U x)) =
      canonicalMixedDensity (euclideanSubspace (U s.1)) (b s.1) (hb s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => p s.1 i s.2)
        (euclideanCoefficientEquiv U x s.1 s.2) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [euclideanCoefficientEquiv_mk]
  exact canonicalAmbientTorusDensity_eq (euclideanSubspace (U s.1)) (b s.1) (hb s.1) (o s.1)
    _ _ _ _ (fun i k => hf s.1 i s.2 k) (hs s.1 s.2)
    ((euclideanSubspaceArrayEquiv (U s.1)).symm (fun _ => v s))

include hf hs in
theorem coefficientAmbientDensity_eq (x : CoefficientTorus (K := K) U) :
    coefficientAmbientDensity U b o c w f (coefficientAmbientTorus U x) =
      canonicalCoefficientDensity U b hb o c w p x := by
  unfold coefficientAmbientDensity canonicalCoefficientDensity canonicalArrayDensity
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro d _
  exact coefficientAmbientFactor_eq U b hb o c w f p hf hs ⟨j, d⟩ x

theorem coefficientAmbientDensity_bounds {B L : ℝ≥0} (hB : 1 ≤ B)
    (hcap : ∀ s x, 0 ≤ coefficientAmbientFactor U b o c w f s x ∧
      coefficientAmbientFactor U b o c w f s x ≤ B)
    (hlip : ∀ s, LipschitzWith L (coefficientAmbientFactor U b o c w f s)) :
    (∀ x, 0 ≤ coefficientAmbientDensity U b o c w f x ∧
      coefficientAmbientDensity U b o c w f x ≤ (B : ℝ)^Fintype.card (CoefficientSlot K m)) ∧
    LipschitzWith (Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m))
      (coefficientAmbientDensity U b o c w f) := by
  have hl (s : CoefficientSlot K m) : LipschitzWith L
      (fun x => coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s x)) := by
    simpa only [mul_one, Function.comp_def] using (hlip s).comp (coefficientAmbientSlice_lipschitz (J := J) s)
  obtain ⟨hbnd, hlprod⟩ := bounded_lipschitz_real_prod
    (fun s x => coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s x)) hB hl
    (fun s x => by rw [abs_of_nonneg (hcap s _).1]; exact (hcap s _).2)
  refine ⟨?_, hlprod⟩
  intro x
  have h0 : 0 ≤ coefficientAmbientDensity U b o c w f x :=
    Finset.prod_nonneg (fun s _ => (hcap s _).1)
  exact ⟨h0, (le_abs_self _).trans (hbnd x)⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientAmbientFourier
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_coefficient_ambient_fourier_approximation
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hf : ∀ j i d (k : ℤ), f j i d ((k : ℝ) / basisAxisScale (b j) i) =
      basisAxisScale (b j) i * (p j i d k).toReal)
    (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
      (fun i => p j i d) x ≠ 0 → ∀ a,
        |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4)
    {B L : ℝ≥0} (hB : 1 ≤ B)
    (hcap : ∀ s x, 0 ≤ coefficientAmbientFactor U b o c w f s x ∧
      coefficientAmbientFactor U b o c w f s x ≤ B)
    (hlip : ∀ s, LipschitzWith L (coefficientAmbientFactor U b o c w f s))
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ P)
    (hLP : ((Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m) : ℝ≥0) : ℝ)
      ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (K →₀ ℕ) → J j → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i,
        |(frequency t j d i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * (B : ℝ)^Fintype.card (CoefficientSlot K m) ∧
      ∀ x, ‖(canonicalCoefficientDensity U b hb o c w p x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  obtain ⟨hbound, hLip⟩ := coefficientAmbientDensity_bounds U b o c w f hB hcap hlip
  have hc : LipschitzWith
      (Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m))
      (fun x => (coefficientAmbientDensity U b o c w f x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hLip.dist_le_mul x y
  have hbnd (x) : ‖(coefficientAmbientDensity U b o c w f x : ℂ)‖ ≤
      (B^Fintype.card (CoefficientSlot K m) : ℝ≥0) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound x).1, NNReal.coe_pow]
      using (hbound x).2
  obtain ⟨F, inst, frequency, a, hcard, hfreq, hsum, herr⟩ :=
    exists_ambient_torus_fourier_approximation _ _ _ hc hbnd hδ hP hdim hLP hδP
  let _ := inst
  refine ⟨F, inst, fun t => coefficientSlotFrequency (fun s i => frequency t ⟨s, i⟩), a,
    hcard, ?_, hsum, ?_⟩
  · intro t
    exact coefficientSlotFrequency_bound (fun s i => frequency t ⟨s, i⟩) (fun s i => hfreq t ⟨s, i⟩)
  · intro x
    simpa only [coefficientAmbientDensity_eq U b hb o c w f p hf hs x,
      coefficientAmbientTorus_character, coefficientTorusFourierSum] using
      herr (coefficientAmbientTorus U x)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedCoefficientDensity :
    CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ :=
  canonicalCoefficientDensity U b hb o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S)

noncomputable def allocatedCoefficientSource :
    Measure (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :=
  Measure.pi (fun j => mixedScalarArrayLaw (allocatedLayerCenters B U b S j)
    (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j))

variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hσ1 C hC hchart hsmall ν

theorem allocatedCoefficientDensity_spec :
    Measurable (allocatedCoefficientDensity B U b hb o hR hσ S) ∧
      (∀ y, 0 ≤ allocatedCoefficientDensity B U b hb o hR hσ S y) ∧
      Integrable (allocatedCoefficientDensity B U b hb o hR hσ S) μ ∧
      (∫ y, allocatedCoefficientDensity B U b hb o hR hσ S y ∂μ) = 1 ∧
      Measure.map (canonicalCoefficientSample U b hb o) (allocatedCoefficientSource B U b hR hσ S) =
        realDensityMeasure μ (allocatedCoefficientDensity B U b hb o hR hσ S) := by
  have hw := allocatedLayerWidths_pos B U b hR hσ S
  have hs := allocatedLayerColumns_chart B U b hR hσ S o hσ1 C hC hchart hsmall
  have hm := canonicalCoefficientDensity_mass U b hb o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerPMFs B U b hR hσ S) μ ν hw hs
  exact ⟨canonicalCoefficientDensity_measurable U b hb o _ _ _,
    canonicalCoefficientDensity_nonneg U b hb o _ _ _ hw, hm.1, hm.2,
    canonicalCoefficientDensity_law U b hb o _ _ _ μ ν hw hs⟩

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedAmbientDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedCoefficientAmbientDensity :
    (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → UnitAddCircle) → ℝ :=
  coefficientAmbientDensity U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerInterpolation B U b S)

theorem allocatedCoefficientAmbientDensity_eq (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    allocatedCoefficientAmbientDensity B U b o S (coefficientAmbientTorus U x) =
      allocatedCoefficientDensity B U b hb o hR hσ S x := by
  exact coefficientAmbientDensity_eq U b hb o _ _ _ _
    (fun j i d => (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d).1)
    (allocatedLayerColumns_quarter_support B U b hR hσ S o hσ1 C hC hchart hsmall) x

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedAmbientLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedLayerMixedCap (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  (allocatedLayerWidthFloor (G := G) B R σ L j)⁻¹^Fintype.card (I j) *
    (allocatedLayerCommonCap (G := G) B R σ L j)^(n j)

noncomputable def allocatedLayerMixedLip (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  (allocatedLayerWidthFloor (G := G) B R σ L j)⁻¹^Fintype.card (I j) *
      (n j * allocatedLayerCommonLip (G := G) B R σ L j * (allocatedLayerCommonCap (G := G) B R σ L j)^(n j)) +
    (allocatedLayerCommonCap (G := G) B R σ L j)^(n j) *
      affineProductProfileLip (I j) (allocatedLayerWidthFloor (G := G) B R σ L j)

noncomputable def allocatedAmbientFactorCap (R σ : Fin m → ℝ) (L : ℕ) (V : Fin m → ℝ≥0) : ℝ≥0 :=
  1 + ∑ j, V j * allocatedLayerMixedCap (G := G) B R σ L j

noncomputable def allocatedAmbientLayerLip (R σ : Fin m → ℝ) (L : ℕ) (d : Fin m → ℕ)
    (C V : Fin m → ℝ≥0) (j : Fin m) : ℝ≥0 :=
  V j * (allocatedLayerMixedLip (G := G) B R σ L j * (C j * d j)) +
    (V j * allocatedLayerMixedCap (G := G) B R σ L j) * 8

noncomputable def allocatedAmbientFactorLip (R σ : Fin m → ℝ) (L : ℕ) (d : Fin m → ℕ)
    (C V : Fin m → ℝ≥0) : ℝ≥0 :=
  ∑ j, allocatedAmbientLayerLip (G := G) B R σ L d C V j

theorem allocatedAmbientFactorCap_one_le (R σ : Fin m → ℝ) (L : ℕ) (V : Fin m → ℝ≥0) :
    1 ≤ allocatedAmbientFactorCap (G := G) B R σ L V := le_add_of_nonneg_right (by positivity)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerMixedInterpolation_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (d) :
    (∀ x, 0 ≤ mixedDensityInterpolation (fun i => allocatedLayerCenters B U b S j i d)
        (fun i => allocatedLayerWidths B U b S j i d) (fun i => allocatedLayerIntegerInterpolation B U b S j i d) x ∧
      mixedDensityInterpolation (fun i => allocatedLayerCenters B U b S j i d)
        (fun i => allocatedLayerWidths B U b S j i d) (fun i => allocatedLayerIntegerInterpolation B U b S j i d) x ≤
          allocatedLayerMixedCap (G := G) B R σ S.value j) ∧
    LipschitzWith (allocatedLayerMixedLip (G := G) B R σ S.value j)
      (mixedDensityInterpolation (fun i => allocatedLayerCenters B U b S j i d)
        (fun i => allocatedLayerWidths B U b S j i d) (fun i => allocatedLayerIntegerInterpolation B U b S j i d)) := by
  have h := mixedDensityInterpolation_bounds
    (fun i => allocatedLayerCenters B U b S j i d) (fun i => allocatedLayerWidths B U b S j i d)
    (fun i => allocatedLayerIntegerInterpolation B U b S j i d)
    (allocatedLayerWidthFloor_pos (G := G) B hR hσ S.positive j)
    (fun i => allocatedLayerWidths_floor B U b S hR hσ j i d)
    (allocatedLayerCommonCap_one_le (G := G) B R σ S.value j)
    (fun i => (allocatedLayerInterpolation_common_bounds B U b S hR hσ j i d).2)
    (fun i x => (allocatedLayerInterpolation_common_bounds B U b S hR hσ j i d).1 x)
  simpa only [allocatedLayerMixedCap, allocatedLayerMixedLip, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_inv, Fintype.card_fin] using h

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedAmbientFactor_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (s : CoefficientSlot (LayerSamplerVariables G I n B) m) :
    (∀ x, 0 ≤ coefficientAmbientFactor U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerInterpolation B U b S) s x ∧
      coefficientAmbientFactor U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerInterpolation B U b S) s x ≤
          allocatedAmbientFactorCap (G := G) B R σ S.value V) ∧
    LipschitzWith (allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V)
      (coefficientAmbientFactor U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerInterpolation B U b S) s) := by
  obtain ⟨hcap, hlip⟩ := allocatedLayerMixedInterpolation_bounds B U b S hR hσ s.1 s.2
  obtain ⟨ha, hl⟩ := canonicalAmbientTorusDensity_bounds (euclideanSubspace (U s.1)) (b s.1) (o s.1)
    _ _ _ hcap hlip (hC s.1) (hV s.1)
  have hcaple : V s.1 * allocatedLayerMixedCap (G := G) B R σ S.value s.1 ≤
      allocatedAmbientFactorCap (G := G) B R σ S.value V := by
    apply le_trans (Finset.single_le_sum
      (f := fun j => V j * allocatedLayerMixedCap (G := G) B R σ S.value j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1))
    exact le_add_of_nonneg_left (by norm_num)
  have hliple : allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V s.1 ≤
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V := by
    unfold allocatedAmbientFactorLip
    exact Finset.single_le_sum
      (f := fun j => allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1)
  refine ⟨fun x => ⟨(ha x).1, (ha x).2.trans ?_⟩, hl.weaken hliple⟩
  exact_mod_cast hcaple

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

def allocatedMixedLog (m : ℕ) (P : ℝ) : ℝ :=
  (2*P+1)*(allocatedWidthLog m P + allocatedCommonLog m P)+3*P+1

theorem allocatedMixedLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedMixedLog m P := by
  have hw := allocatedWidthLog_nonneg m hP
  have hc := allocatedCommonLog_nonneg m hP
  unfold allocatedMixedLog
  positivity

namespace VectorPolynomial

open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedLayerMixed_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L) (j : Fin m)
    {P : ℝ} (hP : 0 ≤ P) (hR : 0 < R j) (hσ : 0 < σ j)
    (hRP : (R j)⁻¹ ≤ Real.exp P) (hσP : (σ j)⁻¹ ≤ Real.exp P)
    (hcount : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : (Fintype.card (I j) : ℝ) ≤ P) (hn : (n j : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (L : ℝ) ≤ Real.exp P) :
    (allocatedLayerMixedCap (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedMixedLog m P) ∧
      (allocatedLayerMixedLip (G := G) B R σ L j : ℝ) ≤ Real.exp (allocatedMixedLog m P) := by
  obtain ⟨hc, hl⟩ := allocatedLayerCommonInterpolation_exp_bounds B R σ L j
    hP hR hσ hRP hσP hcount hn hAP hLP
  have hw := allocatedLayerWidthFloor_inv_exp B R σ L hL j hP hR hσ hRP hσP hcount hLP
  have h := mixedInterpolation_constants_exp_bounds (I := I j) (n j)
    hP (allocatedWidthLog_nonneg m hP) (allocatedCommonLog_nonneg m hP) hI hn hw hc hl hAP
  refine ⟨h.1.trans (Real.exp_le_exp.mpr ?_), h.2⟩
  have hw0 := allocatedWidthLog_nonneg m hP
  have hc0 := allocatedCommonLog_nonneg m hP
  have hp := mul_nonneg hP (add_nonneg hw0 hc0)
  unfold allocatedMixedLog
  nlinarith

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem ambientInterpolation_constants_exp_bounds (n : ℕ) {M J C V : ℝ≥0} {P Q : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hn : (n : ℝ) ≤ P)
    (hM : (M : ℝ) ≤ Real.exp Q) (hJ : (J : ℝ) ≤ Real.exp Q)
    (hC : (C : ℝ) ≤ Real.exp P) (hV : (V : ℝ) ≤ Real.exp P) :
    ((V*M : ℝ≥0) : ℝ) ≤ Real.exp (Q+P) ∧
      ((V*(J*(C*n))+(V*M)*8 : ℝ≥0) : ℝ) ≤ Real.exp (2*Q+4*P+9) := by
  have hnE : (n : ℝ) ≤ Real.exp P := hn.trans (by linarith [Real.add_one_le_exp P])
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  constructor
  · simp only [NNReal.coe_mul]
    calc
      _ ≤ Real.exp P * Real.exp Q := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  · simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat]
    have hfirst : (V : ℝ) * (J * (C * n)) ≤ Real.exp (Q+3*P) := by
      calc
        _ ≤ Real.exp P * (Real.exp Q * (Real.exp P * Real.exp P)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsecond : ((V : ℝ)*M)*8 ≤ Real.exp (Q+P+8) := by
      calc
        _ ≤ (Real.exp P * Real.exp Q) * Real.exp 8 := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    exact (add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond).trans_eq
      (congrArg Real.exp (by ring))

def allocatedAmbientLog (m : ℕ) (P : ℝ) : ℝ :=
  P + P*(2*allocatedMixedLog m P+4*P+9)+1

theorem allocatedAmbientLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedAmbientLog m P := by
  have h := allocatedMixedLog_nonneg m hP
  unfold allocatedAmbientLog
  positivity

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedAmbientConstants_exp_bounds (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L)
    (d : Fin m → ℕ) (C V : Fin m → ℝ≥0) {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hd : ∀ j, (d j : ℝ) ≤ P) (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (L : ℝ) ≤ Real.exp P) (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P) :
    (allocatedAmbientFactorCap (G := G) B R σ L V : ℝ) ≤ Real.exp (allocatedAmbientLog m P) ∧
      (allocatedAmbientFactorLip (G := G) B R σ L d C V : ℝ) ≤ Real.exp (allocatedAmbientLog m P) := by
  have hmix (j : Fin m) := allocatedLayerMixed_exp_bounds (G := G) B R σ L hL j hP (hR j) (hσ j)
    (hRP j) (hσP j) (hcount j) (hI j) (hn j) hAP hLP
  have hlocal (j : Fin m) := ambientInterpolation_constants_exp_bounds (d j) hP
    (allocatedMixedLog_nonneg m hP) (hd j) (hmix j).1 (hmix j).2 (hCP j) (hVP j)
  have hcard : (Fintype.card (Fin m) : ℝ) ≤ P := by simpa only [Fintype.card_fin] using hm
  have hQ := allocatedMixedLog_nonneg m hP
  have hcap := sum_le_exp_of_card_and_uniform_bound
    (fun j => ((V j * allocatedLayerMixedCap (G := G) B R σ L j : ℝ≥0) : ℝ))
    (by positivity : 0 ≤ allocatedMixedLog m P+P) hcard (fun j => (hlocal j).1)
  have hlip := sum_le_exp_of_card_and_uniform_bound
    (fun j => (allocatedAmbientLayerLip (G := G) B R σ L d C V j : ℝ))
    (by positivity : 0 ≤ 2*allocatedMixedLog m P+4*P+9) hcard (fun j => (hlocal j).2)
  constructor
  · simp only [allocatedAmbientFactorCap, NNReal.coe_add, NNReal.coe_one, NNReal.coe_sum]
    apply (one_add_le_exp_succ (by positivity) hcap).trans
    apply Real.exp_le_exp.mpr
    unfold allocatedAmbientLog
    nlinarith
  · simp only [allocatedAmbientFactorLip, NNReal.coe_sum]
    exact hlip.trans (Real.exp_le_exp.mpr (by unfold allocatedAmbientLog; linarith))

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CoefficientCoverKernel
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientAmbientHom :
    CoefficientTorus (K := K) U →+ (CoefficientAmbientIndex K J → UnitAddCircle) where
  toFun := coefficientAmbientTorus U
  map_zero' := by
    funext t
    simp [coefficientAmbientTorus]
  map_add' x y := by
    funext t
    simp [coefficientAmbientTorus, map_add]

theorem coefficientAmbientTorus_injective :
    Function.Injective (coefficientAmbientTorus (K := K) U) := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  intro s i
  have he : ((a s).val i : UnitAddCircle) = ((b s).val i : UnitAddCircle) := congrFun h ⟨s, i⟩
  have hz : (((a s).val i - (b s).val i : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, he, sub_self]
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  exact ⟨z, by simpa using hz.symm⟩

variable [Fintype K] [∀ j, Fintype (J j)]

theorem coefficientCoverKernel_finite (d : ℕ) (hd : 0 < d) :
    Finite (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker := by
  let T := {z : UnitAddCircle // d • z = 0}
  let : Fintype T := (AddCircle.finite_torsion (1 : ℝ) hd).fintype
  let f : (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker →
      CoefficientAmbientIndex K J → T := fun x i =>
    ⟨coefficientAmbientHom U x.val i, by
      change (d • coefficientAmbientHom U x.val) i = 0
      rw [← map_nsmul]
      have hx : d • x.val = 0 := x.property
      rw [hx, map_zero]
      rfl⟩
  apply Finite.of_injective f
  intro x y hxy
  apply Subtype.ext
  apply coefficientAmbientTorus_injective U
  funext i
  exact congrArg Subtype.val (congrFun hxy i)

@[instance_reducible]
noncomputable def coefficientCoverKernelFintype (d : ℕ) (hd : 0 < d) :
    Fintype (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker := by
  let : Finite (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker :=
    coefficientCoverKernel_finite U d hd
  exact Fintype.ofFinite _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def latticeDeckInteger (z : Fin n → ℤ) (w : I → ℤ) : D → ℤ :=
  (standardLatticeCoordinates W bW b hb).symm (Sum.elim z w)

theorem normalizedCoverLift_add_deck (d : ℕ) (hd : 0 < d)
    (x : W × (Fin n → ℤ)) (w : I → ℤ) :
    normalizedCoverLift W b hb d x +
        (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
          bW d hd (integerResidueMap I d w)).val =
      QuotientAddGroup.mk' _ ((d : ℝ)⁻¹ •
        (normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val)) := by
  have hr : integerResidueMap I d w =
      latticeBasisResidue (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
        bW d (bW.equivFun.symm w) := by
    change integerResidueMap I d w = integerResidueMap I d (bW.equivFun (bW.equivFun.symm w))
    rw [LinearEquiv.apply_symm_apply]
  rw [hr, coverKernelBasisEquiv_residue, coverLatticePoint_val, smul_add, map_add]
  rfl

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def coefficientSamplerAmbientPoint
    (x : CoefficientSamplerArrays (K := K) I n) : CoefficientAmbientIndex K J → ℝ :=
  fun a => normalizedLatticePoint (euclideanSubspace (U a.1.1)) (b a.1.1)
    (orthonormalMixedChart (o a.1.1) (mixedArrayRegroup _ _ _ (x a.1.1) a.1.2)) a.2

noncomputable def coefficientSamplerDeckInteger
    (x : CoefficientSamplerArrays (K := K) I n)
    (w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ) :
    CoefficientAmbientIndex K J → ℤ :=
  fun a => latticeDeckInteger (euclideanSubspace (U a.1.1)) (bW a.1.1) (b a.1.1) (hb a.1.1)
    (fun i => (x a.1.1).2 i a.1.2) (w a.1.1 a.1.2) a.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical
attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientDeckSample_residue_injective (q : ℕ) (hq : 0 < q)
    (x : CoefficientSamplerArrays (K := K) I n) :
    Function.Injective (canonicalCoefficientDeckSample U bW b hb o q hq x) := by
  intro r s h
  apply (coefficientDeckKernelEquiv U bW q hq).injective
  apply Subtype.ext
  exact add_left_cancel h

theorem canonicalCoefficientSample_injOn_chart :
    Set.InjOn (canonicalCoefficientSample (K := K) U b hb o)
      {x | ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (x j)} := by
  intro x hx y hy h
  have h' := congrArg (euclideanCoefficientEquiv U) h
  simp only [canonicalCoefficientSample, AddEquiv.apply_symm_apply] at h'
  funext j
  exact mixedArrayQuotient_injOn_chart (euclideanSubspace (U j)) (b j) (hb j) (o j)
    (hx j) (hy j) (congrFun h' j)

theorem canonicalCoefficientDeckSample_injOn_chart (q : ℕ) (hq : 0 < q) :
    Set.InjOn (fun z : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) E q =>
      canonicalCoefficientDeckSample U bW b hb o q hq z.1 z.2)
      {z | ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (z.1 j)} := by
  rintro ⟨x, r⟩ hx ⟨y, s⟩ hy h
  have hp := congrArg (quotientIntegerCover (coefficientIntegerLattice (K := K) U) q) h
  simp only [canonicalCoefficientDeckSample_projection] at hp
  have hxy := canonicalCoefficientSample_injOn_chart U b hb o hx hy hp
  change x = y at hxy
  subst y
  have hrs := canonicalCoefficientDeckSample_residue_injective U bW b hb o q hq x h
  change r = s at hrs
  subst s
  rfl

theorem canonicalCoefficientDeckSample_injOn_smallAmbient (q : ℕ) (hq : 0 < q) :
    Set.InjOn (fun z : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) E q =>
      canonicalCoefficientDeckSample U bW b hb o q hq z.1 z.2)
      {z | ∀ a, |coefficientSamplerAmbientPoint U b o z.1 a| < 1/2} := by
  intro x hx y hy h
  apply canonicalCoefficientDeckSample_injOn_chart U bW b hb o q hq _ _ h
  · intro j e i
    exact hx ⟨⟨j, e⟩, i⟩
  · intro j e i
    exact hy ⟨⟨j, e⟩, i⟩

variable [Fintype K]

end Erdos3.VectorPolynomial

end

end OAI

end


