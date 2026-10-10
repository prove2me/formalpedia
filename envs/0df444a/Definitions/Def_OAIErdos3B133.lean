-- Prove2me | Definitions.Def_OAIErdos3B133
-- name    : OAIErdos3B133
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T12:57:06.414774+00:00
-- url     : https://prove2.me/theorems/22b5a5bb-a2ec-4d8c-9df9-4758387b3acd
-- title:
--   OpenAI Erdős-3 split, definitions bundle 134 of 135
-- statement:
--   Definitions bundle 134 of 135 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B132`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 134 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.coefficientResidualFunctional_eq_zero_iff_oneSite`, `OAI.Erdos3.PrincipalAxisParameter`, `OAI.Erdos3.PrincipalAxisTuples`, `OAI.Erdos3.VectorPolynomial.AllocatedFrozenCoefficients`, `OAI.Erdos3.VectorPolynomial.AllocatedLongCoefficients`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientAxisLaw`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientDensity_fiber_cap`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientFactor_constant_cap`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientJointAmbientKernel`, `OAI.Erdos3.VectorPolynomial.allocatedCoefficientSplit`, `OAI.Erdos3.VectorPolynomial.allocatedEnormousProfilePMF`, `OAI.Erdos3.VectorPolynomial.allocatedEnormous_active`, `OAI.Erdos3.VectorPolynomial.allocatedEnormous_constant_width`, `OAI.Erdos3.VectorPolynomial.allocatedEnormous_principalScale`, `OAI.Erdos3.VectorPolynomial.allocatedEnormous_profile_sum_pos`, `OAI.Erdos3.VectorPolynomial.allocatedEnormous_profile_width_large`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenCoefficientSource`, `OAI.Erdos3.VectorPolynomial.allocatedGridAxis`, `OAI.Erdos3.VectorPolynomial.allocatedGridAxisDecidable`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerProfileCenters`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerProfileScales`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerProfileScales_pos`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerProfileWidths`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerProfileWidths_pos`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerProfile_support`, `OAI.Erdos3.VectorPolynomial.allocatedLongCoefficientSource`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalSides`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalSides_active`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalSides_pos`, `OAI.Erdos3.VectorPolynomial.bounded_coefficient_translate_fiber_integrable`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDensity_fiber_cap`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDensity_product`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientFactor`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientFactor_measurable`, `OAI.Erdos3.VectorPolynomial.centeredAffineCoefficientTorus_eq_subtractive`, `OAI.Erdos3.VectorPolynomial.coefficientConstantCenter`, `OAI.Erdos3.VectorPolynomial.coefficientConstantCenter_add_constant`, `OAI.Erdos3.VectorPolynomial.coefficientConstantCenter_continuous`, `OAI.Erdos3.VectorPolynomial.coefficientConstantCenter_integral_add_constant`, `OAI.Erdos3.VectorPolynomial.coefficientFiberAverage`, `OAI.Erdos3.VectorPolynomial.coefficientFiberAverage_approx`, `OAI.Erdos3.VectorPolynomial.coefficientFiberAverage_bound`, `OAI.Erdos3.VectorPolynomial.coefficientFiberAverage_nonneg`, `OAI.Erdos3.VectorPolynomial.coefficientFiberMap`, `OAI.Erdos3.VectorPolynomial.coefficientFiberMap_continuous`, `OAI.Erdos3.VectorPolynomial.coefficientFiberMap_nonconstant`, `OAI.Erdos3.VectorPolynomial.coefficientFiberMap_retraction`, `OAI.Erdos3.VectorPolynomial.coefficientFourier_translate_approx`, `OAI.Erdos3.VectorPolynomial.coefficientFourier_translate_norm`, `OAI.Erdos3.VectorPolynomial.coefficientJointAmbientKernel`, `OAI.Erdos3.VectorPolynomial.coefficientMixedFiber_average`, `OAI.Erdos3.VectorPolynomial.coefficientMixedFiber_integrable`, `OAI.Erdos3.VectorPolynomial.coefficientMixedFiber_joint_integrable`, `OAI.Erdos3.VectorPolynomial.coefficientMixedFiber_joint_measurable`, `OAI.Erdos3.VectorPolynomial.coefficientProductDensity_fiberAverage_cap`, `OAI.Erdos3.VectorPolynomial.coefficientProductDensity_fiber_bound`, `OAI.Erdos3.VectorPolynomial.coefficientResidualFunctional`, `OAI.Erdos3.VectorPolynomial.coefficientResidualFunctional_integral`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_add`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_fiber`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_fiberAverage`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_fiberAverage_evaluation`, `OAI.Erdos3.VectorPolynomial.coefficientTorusCharacter_fiber_integrable`, `OAI.Erdos3.VectorPolynomial.coefficientTorusFourierSum_add`, `OAI.Erdos3.VectorPolynomial.constantCoefficientCap_product`, `OAI.Erdos3.VectorPolynomial.exists_subtractive_constant_center`, `OAI.Erdos3.VectorPolynomial.nonconstantCoefficientDensity_probability`, `OAI.Erdos3.VectorPolynomial.nonconstantCoefficientFactor`, `OAI.Erdos3.partitionedPrincipalInput`, `OAI.Erdos3.principalAxisJoin`, `OAI.Erdos3.principalAxisJoin_restrict`, `OAI.Erdos3.principalAxisLength`, `OAI.Erdos3.principalAxisPartitionEquiv`, `OAI.Erdos3.principalAxisRestrict`, `OAI.Erdos3.principalAxisRestrict_join_left`, `OAI.Erdos3.principalAxisRestrict_join_right`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B053

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedJointAmbientKernel
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)

noncomputable def coefficientJointAmbientKernel (v : CoefficientAmbientIndex K J → ℝ) : ℝ :=
  ∏ s : CoefficientSlot K m,
    canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
      (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2)
      (fun i => v ⟨s,i⟩)

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
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

noncomputable def allocatedCoefficientJointAmbientKernel
    (x : CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ℝ) : ℝ :=
  coefficientJointAmbientKernel U b o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerInterpolation B U b S) x

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def coefficientFiberMap {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U) :
    CoefficientTorus (K := K) U :=
  constantCoefficientTorusMap U y +
    (x - constantCoefficientTorusMap U (coefficientEvaluationTorus U t x))

theorem coefficientFiberMap_retraction {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientTorus (K := K) U) :
    coefficientFiberMap U t (coefficientEvaluationTorus U t x) x = x := by
  dsimp only [coefficientFiberMap]
  abel

theorem coefficientFiberMap_nonconstant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U)
    (s : CoefficientSlot K m) (hs : s.2.val ≠ 0) :
    coefficientCoordinateTorus U (coefficientFiberMap U t y x) s =
      coefficientCoordinateTorus U x s := by
  simp only [coefficientFiberMap, map_add, map_sub, Pi.add_apply, Pi.sub_apply,
    constantCoefficientTorusMap_nonconstant U _ s hs, sub_zero, zero_add]

theorem coefficientFiberMap_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) : Continuous (coefficientFiberMap U t y) :=
  continuous_const.add (continuous_id.sub ((constantCoefficientTorusMap_continuous U).comp
    (coefficientEvaluationTorus_continuous U t)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientConstantCenter :
    CoefficientTorus (K := K) U →+ CoefficientTorus (K := K) U :=
  (constantCoefficientTorusMap U).comp (coefficientEvaluationTorus U 0)

theorem coefficientConstantCenter_continuous :
    Continuous (coefficientConstantCenter (K := K) U) :=
  (constantCoefficientTorusMap_continuous U).comp (coefficientEvaluationTorus_continuous U 0)

omit [∀ j, Fintype (J j)] in
theorem coefficientConstantCenter_add_constant
    (x : CoefficientTorus (K := K) U) (y : CoefficientTorus (K := Empty) U) :
    coefficientConstantCenter U (x + constantCoefficientTorusMap U y) =
      coefficientConstantCenter U x + constantCoefficientTorusMap U y := by
  simp only [coefficientConstantCenter, AddMonoidHom.comp_apply, map_add,
    coefficientEvaluationTorus_constant]

omit [∀ j, Fintype (J j)] in
theorem coefficientConstantCenter_integral_add_constant
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant]
    (D : CoefficientTorus (K := K) U → ℝ) (y : CoefficientTorus (K := Empty) U) :
    (∫ c, D (coefficientConstantCenter U c + constantCoefficientTorusMap U y) ∂μ) =
      ∫ c, D (coefficientConstantCenter U c) ∂μ := by
  simpa only [add_comm (constantCoefficientTorusMap U y), coefficientConstantCenter_add_constant] using
    integral_add_left_eq_self (μ := μ) (fun c => D (coefficientConstantCenter U c))
      (constantCoefficientTorusMap U y)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

noncomputable def coefficientFiberAverage {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (CoefficientTorus (K := K) U)) (t : K → ℤ)
    (F : CoefficientTorus (K := K) U → E) (y : CoefficientTorus (K := Empty) U) : E :=
  ∫ x, F (coefficientFiberMap U t y x) ∂μ

theorem coefficientFiberAverage_bound {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ] (t : K → ℤ)
    (F : CoefficientTorus (K := K) U → E) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B)
    (y : CoefficientTorus (K := Empty) U) : ‖coefficientFiberAverage U μ t F y‖ ≤ B := by
  have h := norm_integral_le_of_norm_le (integrable_const B (μ := μ))
    (ae_of_all μ (fun x => hB (coefficientFiberMap U t y x)))
  simpa only [coefficientFiberAverage, integral_const, probReal_univ, one_smul] using h

theorem coefficientFiberAverage_approx {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ] (t : K → ℤ)
    (F G : CoefficientTorus (K := K) U → E) {ε : ℝ} (hε : ∀ x, ‖F x - G x‖ ≤ ε)
    (y : CoefficientTorus (K := Empty) U)
    (hF : Integrable (fun x => F (coefficientFiberMap U t y x)) μ)
    (hG : Integrable (fun x => G (coefficientFiberMap U t y x)) μ) :
    ‖coefficientFiberAverage U μ t F y - coefficientFiberAverage U μ t G y‖ ≤ ε := by
  simp only [coefficientFiberAverage]
  rw [← integral_sub hF hG]
  exact coefficientFiberAverage_bound U μ t (fun x => F x - G x) hε y

theorem coefficientFiberAverage_nonneg {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) (t : K → ℤ)
    (F : CoefficientTorus (K := K) U → ℝ) (hF : ∀ x, 0 ≤ F x)
    (y : CoefficientTorus (K := Empty) U) : 0 ≤ coefficientFiberAverage U μ t F y :=
  integral_nonneg (fun x => hF (coefficientFiberMap U t y x))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def nonconstantCoefficientFactor {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (s : CoefficientSlot K m) (x : SubspaceArrayTorus Unit (U s.1)) : ℝ :=
  if s.2.val = 0 then 1 else f s x

theorem constantCoefficientCap_product {K : Type*} [Fintype K] {m : ℕ} (C : Fin m → ℝ) :
    (∏ s : CoefficientSlot K m, if s.2.val = 0 then C s.1 else 1) = ∏ j, C j := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_eq_single (zeroCoefficientExponent K (j.val + 1))]
  · simp [zeroCoefficientExponent]
  · intro d _ hd
    have hd0 : d.val ≠ 0 := fun he => hd (Subtype.ext he)
    simp [hd0]
  · simp

theorem coefficientProductDensity_fiber_bound {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf0 : ∀ s x, 0 ≤ f s x) (C : Fin m → ℝ)
    (hC : ∀ (s : CoefficientSlot K m), s.2.val = 0 → ∀ x, f s x ≤ C s.1)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U) :
    coefficientProductDensity U f (coefficientFiberMap U t y x) ≤
      (∏ j, C j) * coefficientProductDensity U (nonconstantCoefficientFactor U f) x := by
  calc
    _ ≤ ∏ s : CoefficientSlot K m,
        (if s.2.val = 0 then C s.1 else 1) *
          nonconstantCoefficientFactor U f s (coefficientCoordinateTorus U x s) := by
      apply Finset.prod_le_prod (fun s _ => hf0 s _)
      intro s _
      by_cases hs : s.2.val = 0
      · simpa only [nonconstantCoefficientFactor, if_pos hs, mul_one] using hC s hs
          (coefficientCoordinateTorus U (coefficientFiberMap U t y x) s)
      · simp only [nonconstantCoefficientFactor, if_neg hs, one_mul,
          coefficientFiberMap_nonconstant U t y x s hs, le_refl]
    _ = _ := by rw [Finset.prod_mul_distrib, constantCoefficientCap_product]; rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem coefficientMixedFiber_joint_measurable
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Measurable (fun p : CoefficientTorus (K := K) U × CoefficientTorus (K := K) U =>
      D (coefficientConstantCenter U p.1 + coefficientFiberMap U t y p.2)) :=
  hD.comp (((coefficientConstantCenter_continuous U).measurable.comp measurable_fst).add
    ((coefficientFiberMap_continuous U t y).measurable.comp measurable_snd))

theorem coefficientMixedFiber_joint_integrable
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M) (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun p : CoefficientTorus (K := K) U × CoefficientTorus (K := K) U =>
      D (coefficientConstantCenter U p.1 + coefficientFiberMap U t y p.2)) (μ.prod μ) :=
  Integrable.of_bound (coefficientMixedFiber_joint_measurable U D hD t y).aestronglyMeasurable
    M (ae_of_all _ (fun _ => hbound _))

theorem coefficientMixedFiber_integrable
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M) (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun c => coefficientFiberAverage U μ t
      (fun x => D (coefficientConstantCenter U c+x)) y) μ :=
  (coefficientMixedFiber_joint_integrable U μ D hD hbound t y).integral_prod_left

theorem coefficientMixedFiber_average
    (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M) (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    (∫ c, coefficientFiberAverage U μ t (fun x => D (coefficientConstantCenter U c+x)) y ∂μ) =
      ∫ x, D x ∂μ := by
  have hi := coefficientMixedFiber_joint_integrable U μ D hD hbound t y
  have hi' : Integrable (fun p : CoefficientTorus (K := K) U × CoefficientTorus (K := K) U =>
      D (coefficientConstantCenter U p.1+p.2)) (μ.prod μ) :=
    Integrable.of_bound (hD.comp (((coefficientConstantCenter_continuous U).measurable.comp
      measurable_fst).add measurable_snd)).aestronglyMeasurable M (ae_of_all _ (fun _ => hbound _))
  have hshift (x : CoefficientTorus (K := K) U) :
      (∫ c, D (coefficientConstantCenter U c + coefficientFiberMap U t y x) ∂μ) =
        ∫ c, D (coefficientConstantCenter U c+x) ∂μ := by
    calc
      _ = ∫ c, D ((coefficientConstantCenter U c + constantCoefficientTorusMap U
          (y-coefficientEvaluationTorus U t x))+x) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ (fun c => by
          apply congrArg D
          simp only [coefficientFiberMap, map_sub]
          abel)
      _ = _ := coefficientConstantCenter_integral_add_constant U μ (fun z => D (z+x)) _
  change (∫ c, ∫ x, D (coefficientConstantCenter U c + coefficientFiberMap U t y x) ∂μ ∂μ) = _
  calc
    _ = ∫ x, ∫ c, D (coefficientConstantCenter U c + coefficientFiberMap U t y x) ∂μ ∂μ :=
      integral_integral_swap hi
    _ = ∫ x, ∫ c, D (coefficientConstantCenter U c+x) ∂μ ∂μ :=
      integral_congr_ae (ae_of_all μ hshift)
    _ = ∫ c, ∫ x, D (coefficientConstantCenter U c+x) ∂μ ∂μ :=
      (integral_integral_swap hi').symm
    _ = _ := by simp only [integral_add_left_eq_self, integral_const, probReal_univ, one_smul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem nonconstantCoefficientDensity_probability {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hfi : ∀ s, Integrable (f s) (ν s)) (hf0 : ∀ s x, 0 ≤ f s x)
    (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1) :
    Integrable (coefficientProductDensity U (nonconstantCoefficientFactor U f)) μ ∧
      (∀ x, 0 ≤ coefficientProductDensity U (nonconstantCoefficientFactor U f) x) ∧
      (∫ x, coefficientProductDensity U (nonconstantCoefficientFactor U f) x ∂μ) = 1 := by
  apply coefficientProductDensity_probability U μ ν
  · intro s
    change Integrable (fun x => if s.2.val = 0 then 1 else f s x) (ν s)
    by_cases hs : s.2.val = 0
    · simpa only [if_pos hs] using
        (integrable_const (1 : ℝ) (μ := ν s))
    · simpa only [if_neg hs] using hfi s
  · intro s x
    by_cases hs : s.2.val = 0
    · simp only [nonconstantCoefficientFactor, if_pos hs, zero_le_one]
    · simpa only [nonconstantCoefficientFactor, if_neg hs] using hf0 s x
  · intro s
    by_cases hs : s.2.val = 0
    · simp only [nonconstantCoefficientFactor, if_pos hs, integral_const,
        probReal_univ, one_smul]
    · simpa only [nonconstantCoefficientFactor, if_neg hs] using hmass s

theorem coefficientProductDensity_fiberAverage_cap {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s, Measurable (f s)) (hfi : ∀ s, Integrable (f s) (ν s))
    (hf0 : ∀ s x, 0 ≤ f s x) (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1)
    (C : Fin m → ℝ)
    (hC : ∀ (s : CoefficientSlot K m), s.2.val = 0 → ∀ x, f s x ≤ C s.1)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => coefficientProductDensity U f (coefficientFiberMap U t y x)) μ ∧
      coefficientFiberAverage U μ t (coefficientProductDensity U f) y ∈ Set.Icc (0 : ℝ) (∏ j, C j) := by
  have hR := nonconstantCoefficientDensity_probability U μ ν f hfi hf0 hmass
  have hD : Measurable (coefficientProductDensity U f) :=
    Finset.measurable_prod _ (fun s _ => (hf s).comp
      ((measurable_pi_apply s).comp (coefficientCoordinateTorus_continuous U).measurable))
  have hb := coefficientProductDensity_fiber_bound U f hf0 C hC t y
  have hi : Integrable (fun x => coefficientProductDensity U f (coefficientFiberMap U t y x)) μ :=
    (hR.1.const_mul (∏ j, C j)).mono'
      (hD.comp (coefficientFiberMap_continuous U t y).measurable).aestronglyMeasurable
      (ae_of_all μ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (coefficientProductDensity_nonneg U f hf0 _)]
        exact hb x))
  refine ⟨hi, coefficientFiberAverage_nonneg U μ t _ (coefficientProductDensity_nonneg U f hf0) y, ?_⟩
  calc
    _ ≤ ∫ x, (∏ j, C j) * coefficientProductDensity U (nonconstantCoefficientFactor U f) x ∂μ :=
      integral_mono hi (hR.1.const_mul _) hb
    _ = ∏ j, C j := by rw [integral_const_mul, hR.2.2, mul_one]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

noncomputable def canonicalCoefficientFactor (s : CoefficientSlot K m)
    (y : SubspaceArrayTorus Unit (U s.1)) : ℝ :=
  canonicalMixedDensity (euclideanSubspace (U s.1)) (b s.1) (hb s.1) (o s.1)
    (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => p s.1 i s.2)
    ((euclideanSubspaceTorusEquiv (U s.1)).symm y)

theorem canonicalCoefficientDensity_product :
    canonicalCoefficientDensity U b hb o c w p =
      coefficientProductDensity U (canonicalCoefficientFactor U b hb o c w p) := by
  funext x
  unfold canonicalCoefficientDensity canonicalArrayDensity coefficientProductDensity
  rw [Fintype.prod_sigma]
  rfl

variable [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
variable [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]

omit [Fintype K] in
theorem canonicalCoefficientFactor_measurable (s : CoefficientSlot K m) :
    Measurable (canonicalCoefficientFactor U b hb o c w p s) :=
  (canonicalMixedDensity_measurable _ (b s.1) (hb s.1) (o s.1) _ _ _).comp
    (euclideanSubspaceTorusMeasurableEquiv (U s.1)).symm.measurable

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem canonicalCoefficientDensity_fiber_cap (hw : ∀ j i d, 0 < w j i d)
    (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
      (fun i => p j i d) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (C : Fin m → ℝ)
    (hC : ∀ (s : CoefficientSlot K m), s.2.val = 0 → ∀ y,
      canonicalCoefficientFactor U b hb o c w p s y ≤ C s.1)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => canonicalCoefficientDensity U b hb o c w p (coefficientFiberMap U t y x)) μ ∧
      coefficientFiberAverage U μ t (canonicalCoefficientDensity U b hb o c w p) y ∈
        Set.Icc (0 : ℝ) (∏ j, C j) := by
  let ξ := fun s : CoefficientSlot K m => euclideanSubspaceTorusMeasure (U s.1) (ν s.1)
  let : ∀ s, IsProbabilityMeasure (ξ s) :=
    fun s => euclideanSubspaceTorusMeasure_probability (U s.1) (ν s.1)
  let : ∀ s, (ξ s).IsAddLeftInvariant :=
    fun s => euclideanSubspaceTorusMeasure_invariant (U s.1) (ν s.1)
  have hmass (s : CoefficientSlot K m) := canonicalMixedDensity_mass _ (b s.1) (hb s.1) (o s.1)
    (ν s.1) (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => hw s.1 i s.2)
    (fun i => p s.1 i s.2) (hs s.1 s.2)
  have hfactor (s : CoefficientSlot K m) := euclideanSubspaceTorusMeasure_mass (U s.1) (ν s.1)
    _ (hmass s).1 (hmass s).2
  rw [canonicalCoefficientDensity_product]
  exact coefficientProductDensity_fiberAverage_cap U μ ξ (canonicalCoefficientFactor U b hb o c w p)
    (canonicalCoefficientFactor_measurable U b hb o c w p) (fun s => (hfactor s).1)
    (fun s x => canonicalMixedDensity_nonneg _ (b s.1) (hb s.1) (o s.1) _ _
      (fun i => hw s.1 i s.2) _ _) (fun s => (hfactor s).2) C hC t y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))

omit [∀ j, Fintype (J j)] in
theorem exists_subtractive_constant_center (x : CoefficientTorus (K := K) U) :
    ∃ c : ∀ j, U j, coefficientConstantCenter U x =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray (K := K) U (fun s => c s.1))) := by
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U)
    (-(coefficientEvaluationTorus U 0 x))
  let c := fun j => v ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩
  have hc : (fun s : CoefficientSlot Empty m => c s.1) = v := by
    funext s
    rcases s with ⟨j,d⟩
    rw [emptyCoefficientExponent_eq (j.val + 1) d]
  refine ⟨c, ?_⟩
  rw [← constantCoefficientTorusMap_mk, hc, hv, map_neg, neg_neg]
  rfl

omit [∀ j, Fintype (J j)] in
theorem centeredAffineCoefficientTorus_eq_subtractive {V : Type*}
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (c : ∀ j, U j) (frame : Option K → V → ℝ) :
    centeredAffineCoefficientTorus U p hm c frame =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))) +
      affineSampleCoefficientTorus U p hm frame := by
  rw [centeredAffineCoefficientTorus, centeredAffineCoefficientArray, map_sub]
  exact sub_eq_neg_add _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (V : Fin m → ℝ) (hV : ∀ j, 0 ≤ V j)
variable (hv : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hV hv in
theorem allocatedCoefficientFactor_constant_cap
    (s : CoefficientSlot (LayerSamplerVariables G I n B) m) (hs : s.2.val = 0)
    (y : SubspaceArrayTorus Unit (U s.1)) :
    canonicalCoefficientFactor U b hb o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerPMFs B U b hR hσ S) s y ≤
      earlyConstantDensityCap (Fintype.card (I s.1)) (n s.1) (R s.1) (V s.1) := by
  rcases s with ⟨j, d⟩
  have hd : d = constantCoefficientSlot _ _ := Subtype.ext hs
  subst d
  simpa only [canonicalCoefficientFactor, allocatedLayerCenters_constant,
    allocatedLayerWidths_constant, allocatedLayerIntegerPMFs_constant] using
    canonicalMixedDensity_constant_cap (euclideanSubspace (U j)) (b j) (hb j) (o j)
      (hR j) (hV j) (hv j) ((euclideanSubspaceTorusEquiv (U j)).symm y)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hV hv ν hσ1 Cinv hCinv hchart hsmall

theorem allocatedCoefficientDensity_fiber_cap (t : LayerSamplerVariables G I n B → ℤ)
    (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => allocatedCoefficientDensity B U b hb o hR hσ S (coefficientFiberMap U t y x)) μ ∧
      coefficientFiberAverage U μ t (allocatedCoefficientDensity B U b hb o hR hσ S) y ∈
        Set.Icc (0 : ℝ) (∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) := by
  let : ∀ j, BorelSpace (SubspaceArrayTorus Unit (U j)) := fun _ => QuotientAddGroup.borelSpace
  exact canonicalCoefficientDensity_fiber_cap U b hb o _ _ _ μ ν
    (allocatedLayerWidths_pos B U b hR hσ S)
    (allocatedLayerColumns_chart B U b hR hσ S o hσ1 Cinv hCinv hchart hsmall)
    (fun j => earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j))
    (allocatedCoefficientFactor_constant_cap B U b hb o hR hσ S V hV hv) t y

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientResidualCharacter
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def coefficientResidualFunctional {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : CoefficientArray (K := K) U →ₗ[ℝ] ℝ :=
  (coefficientArrayFunctional U frequency).comp (coefficientResidualArray U t)

theorem coefficientResidualFunctional_integral {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientArray (K := K) U) (hx : x ∈ coefficientIntegerLattice U) :
    ∃ n : ℤ, coefficientResidualFunctional U t frequency x = n :=
  coefficientArrayFunctional_integral U frequency _
    (coefficientResidualArray_preserves_lattice U t x hx)

theorem coefficientTorusCharacter_fiber {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U frequency (coefficientFiberMap U t y x) =
      coefficientTorusCharacter U frequency (constantCoefficientTorusMap U y) *
        quotientLinearCharacter (coefficientIntegerLattice U) (coefficientResidualFunctional U t frequency)
          (coefficientResidualFunctional_integral U t frequency) x := by
  unfold coefficientFiberMap
  change quotientLinearCharacter _ _ _ (_ + _) = _
  rw [quotientLinearCharacter_add]
  congr 1
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [coefficientEvaluationTorus_mk, constantCoefficientTorusMap_mk, ← map_sub]
  rfl

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

theorem coefficientTorusCharacter_fiberAverage {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [MeasurableAdd₂ (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (y : CoefficientTorus (K := Empty) U) :
    coefficientFiberAverage U μ t (coefficientTorusCharacter U frequency) y =
      if coefficientResidualFunctional U t frequency = 0 then
        coefficientTorusCharacter U frequency (constantCoefficientTorusMap U y) else 0 := by
  unfold coefficientFiberAverage
  simp_rw [coefficientTorusCharacter_fiber]
  rw [integral_const_mul, quotientLinearCharacter_integral]
  split_ifs <;> simp

theorem coefficientTorusCharacter_fiberAverage_evaluation {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [MeasurableAdd₂ (CoefficientTorus (K := K) U)]
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (x : CoefficientTorus (K := K) U) :
    coefficientFiberAverage U μ t (coefficientTorusCharacter U frequency) (coefficientEvaluationTorus U t x) =
      if coefficientResidualFunctional U t frequency = 0 then coefficientTorusCharacter U frequency x else 0 := by
  rw [coefficientTorusCharacter_fiberAverage]
  by_cases h : coefficientResidualFunctional U t frequency = 0
  · rw [if_pos h, if_pos h]
    have he := coefficientTorusCharacter_fiber U t frequency (coefficientEvaluationTorus U t x) x
    simpa only [coefficientFiberMap_retraction, h, quotientLinearCharacter_zero, mul_one] using he.symm
  · simp only [if_neg h]

end Erdos3.VectorPolynomial

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CoefficientFourierTranslation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientTorusCharacter_add (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (y x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U frequency (y+x) =
      coefficientTorusCharacter U frequency y * coefficientTorusCharacter U frequency x :=
  quotientLinearCharacter_add _ _ _ _ _

theorem coefficientTorusFourierSum_add
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (y x : CoefficientTorus (K := K) U) :
    coefficientTorusFourierSum U frequency c (y+x) =
      coefficientTorusFourierSum U frequency
        (fun a => c a * coefficientTorusCharacter U (frequency a) y) x := by
  simp only [coefficientTorusFourierSum, coefficientTorusCharacter_add, mul_assoc]

theorem coefficientFourier_translate_norm
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (y : CoefficientTorus (K := K) U) :
    (∑ a, ‖c a * coefficientTorusCharacter U (frequency a) y‖) = ∑ a, ‖c a‖ := by
  simp only [norm_mul, coefficientTorusCharacter_norm, mul_one]

theorem coefficientFourier_translate_approx (D : CoefficientTorus (K := K) U → ℝ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ) {δ : ℝ}
    (happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ δ)
    (y x : CoefficientTorus (K := K) U) :
    ‖(D (y+x) : ℂ) - coefficientTorusFourierSum U frequency
      (fun a => c a * coefficientTorusCharacter U (frequency a) y) x‖ ≤ δ := by
  rw [← coefficientTorusFourierSum_add]
  exact happrox (y+x)

theorem bounded_coefficient_translate_fiber_integrable
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M)
    (y : CoefficientTorus (K := K) U) (t : K → ℤ)
    (z : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => D (y + coefficientFiberMap U t z x)) μ := by
  apply Integrable.of_bound
    (hD.comp (measurable_const.add (coefficientFiberMap_continuous U t z).measurable)).aestronglyMeasurable M
  exact ae_of_all μ (fun x => hbound _)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

def principalAxisLength (P : D → Prop) (L : PrincipalTupleIndex B h → ℕ) :
    PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val) → ℕ :=
  fun j => L ⟨j.1.val, j.2⟩

abbrev PrincipalAxisTuples (P : D → Prop) (L : PrincipalTupleIndex B h → ℕ) :=
  PrincipalIntegerTuples (fun d : {d // P d} => B d.val) (fun d => h d.val) α
    (principalAxisLength P L)

def principalAxisRestrict (P : D → Prop) {L : PrincipalTupleIndex B h → ℕ}
    (y : PrincipalIntegerTuples B h α L) : PrincipalAxisTuples (α := α) P L :=
  fun j => y ⟨j.1.val, j.2⟩

def principalAxisJoin (P : D → Prop) [DecidablePred P] {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) :
    PrincipalIntegerTuples B h α L :=
  fun j => if hp : P j.1 then u ⟨⟨j.1, hp⟩, j.2⟩ else v ⟨⟨j.1, hp⟩, j.2⟩

theorem principalAxisRestrict_join_left (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) :
    principalAxisRestrict P (principalAxisJoin P u v) = u := by
  funext j
  rcases j with ⟨⟨d, hd⟩, bv⟩
  simp only [principalAxisRestrict, principalAxisJoin, hd, ↓reduceDIte]

theorem principalAxisRestrict_join_right (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) :
    principalAxisRestrict (fun d => ¬P d) (principalAxisJoin P u v) = v := by
  funext j
  rcases j with ⟨⟨d, hd⟩, bv⟩
  simp only [principalAxisRestrict, principalAxisJoin, hd, ↓reduceDIte]

theorem principalAxisJoin_restrict (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ} (y : PrincipalIntegerTuples B h α L) :
    principalAxisJoin P (principalAxisRestrict P y) (principalAxisRestrict (fun d => ¬P d) y) = y := by
  funext j
  simp only [principalAxisJoin, principalAxisRestrict]
  split <;> rfl

def principalAxisPartitionEquiv (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) :
    PrincipalIntegerTuples B h α L ≃
      PrincipalAxisTuples (α := α) P L × PrincipalAxisTuples (α := α) (fun d => ¬P d) L where
  toFun y := (principalAxisRestrict P y, principalAxisRestrict (fun d => ¬P d) y)
  invFun y := principalAxisJoin P y.1 y.2
  left_inv := principalAxisJoin_restrict P
  right_inv y := Prod.ext (principalAxisRestrict_join_left P y.1 y.2)
    (principalAxisRestrict_join_right P y.1 y.2)

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

abbrev PrincipalAxisParameter (P : D → Prop) :=
  JointBlockParameter (fun d : {d // P d} => B d.val) (fun d => h d.val) α

def partitionedPrincipalInput (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) :
    SamplerTupleIndex G B h → Option α →
      (Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) ⊕
        PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d)
  | .inl g, a => .inl (.inl (extra g a))
  | .inr ⟨d, b, v⟩, a =>
      if hp : P d then .inl (.inr ⟨⟨d, hp⟩, b, v, a⟩) else .inr ⟨⟨d, hp⟩, b, v, a⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

def allocatedGridAxis (L : ℕ) : LayerSamplerAxis I n → Prop
  | ⟨_, .inl _⟩ => False
  | ⟨j, .inr i⟩ => basisAxisScale (basis j) i ≤ L^(layerTailDegree m+1)

noncomputable instance allocatedGridAxisDecidable (L : ℕ) :
    DecidablePred (allocatedGridAxis (I := I) U basis L) := Classical.decPred _

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedPrincipalSides : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ :=
  fun j => layerSamplerSides (G := G) B U basis R S.value (.inr j)

theorem allocatedPrincipalSides_pos (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    0 < allocatedPrincipalSides B U basis S j :=
  layerSamplerSides_pos B U basis R S.positive (.inr j)

local notation "gridAxes" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "degree" => layerSamplerDegree I n

section Law

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

end Law

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedPrincipalSides_active (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
    allocatedPrincipalSides B U basis S ⟨⟨j, Sum.inr i⟩, b, v⟩ = S.value := by
  simp only [allocatedPrincipalSides, layerSamplerSides, heterogeneousSamplerSides,
    layerSamplerDenominators, Sum.elim_inr, layerSamplerDegree,
    integerAxisSideLength, hactive, ↓reduceIte]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

abbrev AllocatedFrozenCoefficients := ∀ a : {a // grid a}, CoefficientAxisRow vars a.val

abbrev AllocatedLongCoefficients := ∀ a : {a // ¬grid a}, CoefficientAxisRow vars a.val

noncomputable def allocatedCoefficientSplit :
    CoefficientSamplerArrays (K := vars) I n ≃ᵐ
      AllocatedFrozenCoefficients B U basis S × AllocatedLongCoefficients B U basis S :=
  coefficientAxisSplitEquiv vars I n grid

noncomputable def allocatedCoefficientAxisLaw :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientAxisRow vars a) :=
  coefficientAxisLaw (allocatedLayerCenters B U basis S) (allocatedLayerWidths B U basis S)
    (allocatedLayerIntegerPMFs B U basis hR hσ S)

noncomputable def allocatedFrozenCoefficientSource : Measure (AllocatedFrozenCoefficients B U basis S) :=
  Measure.pi (fun a => allocatedCoefficientAxisLaw B U basis hR hσ S a.val)

noncomputable def allocatedLongCoefficientSource : Measure (AllocatedLongCoefficients B U basis S) :=
  Measure.pi (fun a => allocatedCoefficientAxisLaw B U basis hR hσ S a.val)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedIntegerProfileCenters (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileCenter (layerIntegerPrincipalSlots B j i)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)

noncomputable def allocatedIntegerProfileWidths (R σ : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  coefficientProfileWidth (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (R j/4) (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedIntegerProfileScales (j : Fin m) (i : Fin (n j)) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℝ :=
  fun d => (basisAxisScale (basis j) i : ℝ)/monomialScale (layerSamplerBox B U basis S) d.val

theorem allocatedIntegerProfileScales_pos (j : Fin m) (i : Fin (n j)) (d) :
    0 < allocatedIntegerProfileScales B U basis S j i d :=
  div_pos (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (monomialScale_pos _ (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v)) d.val)

include hR hσ in
theorem allocatedIntegerProfileWidths_pos (j : Fin m) (i : Fin (n j)) (d) :
    0 < allocatedIntegerProfileWidths (G := G) B R σ j i d :=
  coefficientProfileWidth_pos _ _ (div_pos (hR j) (by norm_num)) (principalProfileSize_pos (hR j) _)
    (tailProfileSize_pos (hR j) (hσ j) _) d

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

include henormous in
theorem allocatedEnormous_active : S.value^(j.val+1) < basisAxisScale (basis j) i :=
  (Nat.pow_le_pow_right S.positive ((layerDegree_le_tailDegree j).trans (Nat.le_succ _))).trans_lt henormous

include henormous in
theorem allocatedEnormous_principalScale (d) (hd : d ∈ layerIntegerPrincipalSlots (G := G) B j i) :
    monomialScale (layerSamplerBox B U basis S) d.val = (S.value : ℝ)^(j.val+1) := by
  rw [show monomialScale (layerSamplerBox B U basis S) d.val =
      (integerAxisSideLength (j.val+1) (basisAxisScale (basis j) i) S.value
        (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) : ℝ)^(j.val+1) from
      layerSamplerSides_integer_principal B U basis R S.value j i d hd]
  simp only [integerAxisSideLength, allocatedEnormous_active B U basis S j i henormous, ↓reduceIte]

include hR hσ1 henormous in
theorem allocatedEnormous_constant_width :
    8*(probabilityProfileLipschitz : ℝ) ≤ (R j/4)*(basisAxisScale (basis j) i : ℝ) := by
  have ht : tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))) ≤ R j/4 := by
    unfold tailProfileSize
    apply (div_le_iff₀ (by positivity)).mpr
    have hn := Nat.cast_nonneg (α := ℝ)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
    have hp := mul_nonneg (hR j).le hn
    nlinarith [mul_le_mul_of_nonneg_right hσ1 (hR j).le]
  have hLK : (S.value : ℝ) ≤ basisAxisScale (basis j) i := by
    have hpow : S.value ≤ S.value^(layerTailDegree m+1) := by
      calc
        _ = S.value^1 := by simp
        _ ≤ _ := Nat.pow_le_pow_right S.positive (by omega)
    exact_mod_cast hpow.trans henormous.le
  exact (S.width j).trans (mul_le_mul ht hLK (Nat.cast_nonneg _)
    (div_pos (hR j) (by norm_num)).le)

include hR hσ hσ1 henormous in
theorem allocatedEnormous_profile_width_large (d) :
    8*(probabilityProfileLipschitz : ℝ) ≤
      allocatedIntegerProfileWidths (G := G) B R σ j i d * allocatedIntegerProfileScales B U basis S j i d := by
  exact integerPolynomialProfile_width_large
    (P := layerIntegerPrincipalSlots B j i) (j₀ := constantCoefficientSlot _ _)
    (h := j.val+1) (K := basisAxisScale (basis j) i) (L := S.value) (s := layerTailDegree m)
    (hh := Nat.zero_lt_succ _) (hL := S.positive)
    (T := layerSamplerBox B U basis S)
    (hT := fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (hTL := layerSamplerBox_le B U basis S) (e := Subtype.val)
    (he := fun d => d.property.trans (layerDegree_le_tailDegree j))
    (ρ := R j/4) (γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (ε := tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))
    (hγ := principalProfileSize_pos (hR j) _) (hε := tailProfileSize_pos (hR j) (hσ j) _)
    (hgap := S.gap j i) (hεL := S.width j)
    (ha := allocatedEnormous_active B U basis S j i henormous) (henormous := henormous)
    (hconst := allocatedEnormous_constant_width B U basis hR S j i hσ1 henormous)
    (he₀ := rfl) (hprincipal := allocatedEnormous_principalScale B U basis S j i henormous) d

include hR hσ hσ1 in
theorem allocatedIntegerProfile_support :
    ∀ x, R j < ‖x‖ → affineProductProfile (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths B R σ j i) x = 0 := by
  apply affineProductProfile_zero_outside _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i) (hR j).le
  intro d
  exact (allocatedProfile_term_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerIntegerPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

include hR hσ hσ1 henormous in
theorem allocatedEnormous_profile_sum_pos :
    0 < coefficientWeightSum (affineProductProfile (allocatedIntegerProfileCenters (G := G) B R j i)
      (allocatedIntegerProfileWidths B R σ j i)) (allocatedIntegerProfileScales B U basis S j i) :=
  affineProductProfile_sample_sum_pos _ _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i)
    (allocatedIntegerProfileScales_pos B U basis S j i)
    (allocatedEnormous_profile_width_large B U basis hR hσ S j i hσ1 henormous)

noncomputable def allocatedEnormousProfilePMF :
    PMF (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ) :=
  coefficientPMF (affineProductProfile (allocatedIntegerProfileCenters B R j i)
    (allocatedIntegerProfileWidths B R σ j i))
    (affineProductProfile_nonneg _ _ (allocatedIntegerProfileWidths_pos B hR hσ j i))
    (allocatedIntegerProfileScales B U basis S j i) (allocatedIntegerProfileScales_pos B U basis S j i)
    (allocatedIntegerProfile_support B hR hσ j i hσ1)
    (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)

end Erdos3.VectorPolynomial

end

end OAI

end


