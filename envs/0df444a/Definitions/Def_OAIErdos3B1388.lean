-- Prove2me | Definitions.Def_OAIErdos3B1388
-- name    : OAIErdos3B1388
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T07:55:30.924267+00:00
-- url     : https://prove2.me/theorems/fb3a02a7-cc86-4f58-b79b-cfaefd544ab4
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1389 of 1413
-- statement:
--   Definitions bundle 1389 of 1413 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1387`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1389 available.
--
--   Modules: `OAI.Erdos3.FiniteProbabilityWeights.complexMean_fiber_factor_sum_image`, `OAI.Erdos3.FiniteProbabilityWeights.fiberLaw_comp`, `OAI.Erdos3.FiniteProbabilityWeights.fiberMean_eq_zero_of_not_mem_image`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.forecastPullback_lipschitz`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.forecastPullback_norm_le`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceRankOutput_card_le`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceRankOutput_sum_card_le`, `OAI.Erdos3.VectorPolynomial.allocatedFixedPathLift_lip_le_allAxis`, `OAI.Erdos3.VectorPolynomial.allocatedFixedPathLift_prod_add_one_le_allAxis`, `OAI.Erdos3.VectorPolynomial.allocatedFixedPathLift_prod_le_allAxis`, `OAI.Erdos3.VectorPolynomial.allocatedFixedPathLift_prod_le_prod_of_injOn_aux`, `OAI.Erdos3.VectorPolynomial.allocatedFixedPathLift_sum_lip_le_allAxis`, `OAI.Erdos3.VectorPolynomial.allocatedForecastPolynomial_eval₂_raw_congr`, `OAI.Erdos3.VectorPolynomial.allocatedForecastPolynomial_short_raw`, `OAI.Erdos3.VectorPolynomial.allocatedShortPrincipalRank_active`, `OAI.Erdos3.VectorPolynomial.allocatedShortPrincipalRaw_restrict`, `OAI.Erdos3.VectorPolynomial.allocatedShortRankSelectedWidth_budget`, `OAI.Erdos3.VectorPolynomial.allocatedShortRankSelectedWidth_common_gap`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerBlock_positiveModerate`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerDimension_allocation`, `OAI.Erdos3.VectorPolynomial.exists_centered_forecast_twist_model`, `OAI.Erdos3.VectorPolynomial.forecastNativeAmbientLinear_lipschitz`, `OAI.Erdos3.VectorPolynomial.forecastNativeFillAxes_lipschitz`, `OAI.Erdos3.VectorPolynomial.forecastNativeSpatialInverse_lipschitz`, `OAI.Erdos3.VectorPolynomial.forecastNativeTorusInverse_lipschitz`, `OAI.Erdos3.VectorPolynomial.spatialDegreeOutput_card`, `OAI.Erdos3.VectorPolynomial.spatialDegreeOutput_sum_card`, `OAI.Erdos3.arbitraryStepCRTModulusNeZero`, `OAI.Erdos3.canonicalZeroSpatialInputMap_apply`, `OAI.Erdos3.canonicalZeroSpatialInputMap_physicalSite`, `OAI.Erdos3.canonicalZeroSpatialNarrowInputMap_physicalSite`, `OAI.Erdos3.canonicalZeroSpatialNarrowInput_kernel`, `OAI.Erdos3.canonicalZeroSpatialNarrowInput_normalized`, `OAI.Erdos3.canonicalZeroSpatialNarrowPrincipal_difference`, `OAI.Erdos3.canonicalZeroSpatialNarrowPrincipal_norm_le`, `OAI.Erdos3.canonicalZeroSpatialPrincipal_difference`, `OAI.Erdos3.canonicalZeroSpatialPrincipal_mass_ratio_le_one`, `OAI.Erdos3.canonicalZeroSpatialPrincipal_norm_le`, `OAI.Erdos3.crtInput_intCast_apply`, `OAI.Erdos3.crtPolynomialInputLaw_arbitrary_step_divisor_affine`, `OAI.Erdos3.crtPolynomialInputLaw_arbitrary_step_divisor_complexMean`, `OAI.Erdos3.crtPolynomialInputLaw_arbitrary_step_uniform`, `OAI.Erdos3.crtPrimePowerPolynomialLaw_eq_uniform`, `OAI.Erdos3.modularInitialBlockCount_threshold`, `OAI.Erdos3.modularRankSmallBallExponent_eq`, `OAI.Erdos3.padicStepQuotientUnit_factor`, `OAI.Erdos3.prescribedCRTArbitraryStepEquiv_local_step`, `OAI.Erdos3.prescribedCRTPolynomialInput_arbitrary_step`, `OAI.Erdos3.rationalInactiveForecast_divisor_tsum_test`, `OAI.Erdos3.rationalInactiveForecast_zero_off_image`, `OAI.Erdos3.samplerSeparated_eval₂_raw_congr`, `OAI.Erdos3.tupleResidueReduction_affine`, `OAI.Erdos3.uniform_affine_tupleResidueReduction_fiberLaw`, `OAI.Erdos3.uniform_fiberLaw_surjective_hom`, `OAI.Erdos3.uniform_tupleResidueReduction_fiberLaw`, `OAI.Erdos3.uniform_tupleResidueReduction_fiberLaw_postcompose`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1397

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTsum
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem fiberMean_eq_zero_of_not_mem_image (F : X → R) (f : X → ℝ)
    (r : R) (hr : r ∉ Finset.univ.image F) : p.fiberMean F r f = 0 := by
  have hne : ∀ x, F x ≠ r := by
    intro x hx
    exact hr (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
  simp only [fiberMean, hne, ite_false, mean_const]

theorem complexMean_fiber_factor_sum_image (F : X → R) (f : X → ℝ) (a : R → ℂ) :
    p.complexMean (fun x => (f x : ℂ) * a (F x)) =
      ∑ r ∈ Finset.univ.image F, (p.fiberMean F r f : ℂ) * a r := by
  unfold complexMean fiberMean mean
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hx : F x ∈ Finset.univ.image F := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have he (r : R) : ((if F x = r then f x else 0 : ℝ) : ℂ) =
      if F x = r then (f x : ℂ) else 0 := by split_ifs <;> rfl
  simp [he, mul_ite, ite_mul, mul_assoc, hx]

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastAtom
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {A S Out : Type*} [Fintype A] [Fintype Out]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X J : Type*} [Fintype G] [Fintype X]
  [Fintype J] [DecidableEq J]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)
variable (s : Empty ↪ J) (root : J → ℤ) (D : Matrix Empty J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hR : ∀ j, R j ≠ 0) (hB : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, 4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
  (hprincipal : ∀ j : {a : LayerSamplerAxis I n // ¬P a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
  (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
  (r : ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ) (hr : ∀ e, |r e| ≤ 1)


attribute [local instance] ScalarSiteExpansion.termFinite

include hR ha hδ hprincipal hw hl hr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)

variable (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable {δ : ℝ} (hδ : 0 < δ)

/-- Backport of `Finset.prod_le_prod_of_injOn` (Mathlib d13f23b), proved as there. -/
theorem allocatedFixedPathLift_prod_le_prod_of_injOn_aux {ι α N : Type*} [CommMonoid N]
    [PartialOrder N] [IsOrderedMonoid N] [DecidableEq α]
    {f : ι → N} {g : α → N} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : Finset.image e s ⊆ t) (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ Finset.image e s → 1 ≤ g a) :
    ∏ i ∈ s, f i ≤ ∏ a ∈ t, g a := by
  refine le_trans ?_ <| Finset.prod_le_prod_of_subset_of_one_le' ht hg
  rw [Finset.prod_image he]
  exact Finset.prod_le_prod' h

theorem allocatedFixedPathLift_prod_add_one_le_allAxis :
    (∏ a, (allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a + 1)) ≤
      allocatedForecastAllAxisLiftCap B hδ := by
  classical
  apply allocatedFixedPathLift_prod_le_prod_of_injOn_aux Subtype.val
      (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact le_add_of_nonneg_left zero_le

theorem allocatedFixedPathLift_prod_le_allAxis :
    (∏ a, allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a) ≤
      allocatedForecastAllAxisLiftCap B hδ := by
  calc
    _ ≤ ∏ a, (allocatedFixedPathLiftRowCap P
        (unitProfilePrincipalLowerBound_pos B) hδ a + 1) :=
      Finset.prod_le_prod' (fun _ _ => le_add_of_nonneg_right zero_le_one)
    _ ≤ _ := allocatedFixedPathLift_prod_add_one_le_allAxis B P hδ

theorem allocatedFixedPathLift_sum_lip_le_allAxis :
    (∑ a, allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a *
      (2 * allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a)) ≤
    ∑ a, allocatedForecastAllAxisRowCap B hδ a * (2 * allocatedForecastAllAxisRowCap B hδ a) := by
  apply Finset.sum_le_sum_of_injOn Subtype.val
      (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact zero_le

theorem allocatedFixedPathLift_lip_le_allAxis :
    (∏ a, (allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a + 1)) *
      (∑ a, allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a *
        (2 * allocatedFixedPathLiftRowCap P (unitProfilePrincipalLowerBound_pos B) hδ a)) ≤
      allocatedForecastAllAxisLiftLip B hδ :=
  mul_le_mul' (allocatedFixedPathLift_prod_add_one_le_allAxis B P hδ)
    (allocatedFixedPathLift_sum_lip_le_allAxis B P hδ)

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp)

variable {G : Type*} [Fintype G] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

attribute [local instance] ScalarSiteExpansion.termFinite

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNarrowSpatialCanonicalComparison
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

variable {X Zsp : Type*} [Fintype X] [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ) (W L : ℝ)

omit [Fintype X] in
theorem canonicalZeroSpatialInputMap_apply (hW : 0 ≤ W)
    (u : Option Zsp × X → ℝ) (x : X) :
    canonicalZeroSpatialInputMap s root D W L u ⟨x, Sum.inl ()⟩ =
      u (none, x) + (∑ j, (root j : ℝ) * u (some j, x)) / (1 + W) := by
  have hsum := selectedColumn_sum s (fun j => (root j : ℝ) * u (some j, x))
  simp only [Fintype.sum_empty, zero_add] at hsum
  unfold canonicalZeroSpatialInputMap canonicalSpatialKernelMap
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, normalizedIntegerPivot_entry,
    normalizedIntegerColumns_entry_div, Fintype.sum_sum_type, Fintype.sum_empty,
    add_zero, Fintype.sum_unique, selectedSpatialPivot, rootDifferenceMatrix, Matrix.fromBlocks_apply₁₁, Matrix.one_apply_eq,
    selectedSpatialFreeColumns, Matrix.of_apply, anisotropicSpatialScale,
    physicalSpatialOutputScale, Sum.elim_inl, Int.cast_one, one_mul,
    div_self (by linarith : (1 + W : ℝ) ≠ 0)]
  congr 1
  rw [← hsum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {X G T : Type*} [Fintype X] [Fintype G] [DecidableEq G] [Fintype T]
variable (s : Empty ↪ G) (root : G → ℤ) (D : Matrix Empty G ℤ) (W L : ℝ)
variable (e : (Option G × X) ↪ T)

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem canonicalZeroSpatialNarrowInput_kernel {G N X : Type*} (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) :
    canonicalZeroSpatialNarrowInput ξ u ∘ canonicalZeroSpatialKernelEmbedding G N X =
      u ∘ canonicalZeroSpatialKernelEmbedding G N X := by
  funext a
  rcases a with ⟨a, x⟩
  cases a <;> rfl

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]
variable (s : Empty ↪ G) (sf : Empty ↪ (G ⊕ N))
  (root : G → ℤ) (principal : N → ℤ)
  (D : Matrix Empty G ℤ) (Df : Matrix Empty (G ⊕ N) ℤ) (W L : ℝ)

omit [Fintype X] in
theorem canonicalZeroSpatialPrincipal_difference (hW : 0 ≤ W)
    (u : Option (G ⊕ N) × X → ℝ) (x : X) :
    canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L u ⟨x, .inl ()⟩ -
        canonicalZeroSpatialInputMap s root D W L
          (u ∘ canonicalZeroSpatialKernelEmbedding G N X) ⟨x, .inl ()⟩ =
      (∑ n, (principal n : ℝ) * u (some (.inr n), x)) / (1 + W) := by
  rw [canonicalZeroSpatialInputMap_apply sf _ Df W L hW,
    canonicalZeroSpatialInputMap_apply s root D W L hW]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, canonicalZeroSpatialKernelEmbedding_apply,
    Option.map_none, Option.map_some]
  ring

theorem canonicalZeroSpatialPrincipal_norm_le (hW : 0 ≤ W)
    (u : Option (G ⊕ N) × X → ℝ) (hu : ‖u‖ ≤ 1) :
    ‖canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L u -
        canonicalZeroSpatialInputMap s root D W L
          (u ∘ canonicalZeroSpatialKernelEmbedding G N X)‖ ≤
      (∑ n, |(principal n : ℝ)|) / (1 + W) := by
  have hden : 0 < 1 + W := by linarith
  have hbound : 0 ≤ (∑ n, |(principal n : ℝ)|) / (1 + W) :=
    div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hden.le
  apply (pi_norm_le_iff_of_nonneg hbound).mpr
  rintro ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl a =>
    cases a
    rw [Pi.sub_apply, canonicalZeroSpatialPrincipal_difference s sf root principal D Df W L hW,
      Real.norm_eq_abs, abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      _ ≤ ∑ n, |(principal n : ℝ) * u (some (.inr n), x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n, |(principal n : ℝ)| := by
        apply Finset.sum_le_sum
        intro n _
        rw [abs_mul]
        have hn : |u (some (.inr n), x)| ≤ 1 :=
          (Real.norm_eq_abs _).symm ▸ (norm_le_pi_norm u (some (.inr n), x)).trans hu
        exact mul_le_of_le_one_right (abs_nonneg _) hn

omit [Fintype X] in
theorem canonicalZeroSpatialNarrowPrincipal_difference (hW : 0 ≤ W) (ξ : ℝ)
    (u : Option (G ⊕ N) × X → ℝ) :
    canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
        (canonicalZeroSpatialNarrowInput ξ u) -
      canonicalZeroSpatialInputMap s root D W L
        (u ∘ canonicalZeroSpatialKernelEmbedding G N X) =
    ξ • (canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L u -
      canonicalZeroSpatialInputMap s root D W L
        (u ∘ canonicalZeroSpatialKernelEmbedding G N X)) := by
  ext ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl a =>
    cases a
    have h := canonicalZeroSpatialPrincipal_difference s sf root principal D Df W L hW
      (canonicalZeroSpatialNarrowInput ξ u) x
    rw [canonicalZeroSpatialNarrowInput_kernel] at h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [h, canonicalZeroSpatialPrincipal_difference s sf root principal D Df W L hW]
    simp only [canonicalZeroSpatialNarrowInput_inr]
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    ring

theorem canonicalZeroSpatialNarrowPrincipal_norm_le (hW : 0 ≤ W) (ξ : ℝ) (hξ0 : 0 ≤ ξ)
    (u : Option (G ⊕ N) × X → ℝ) (hu : ‖u‖ ≤ 1) :
    ‖canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
        (canonicalZeroSpatialNarrowInput ξ u) -
      canonicalZeroSpatialInputMap s root D W L
        (u ∘ canonicalZeroSpatialKernelEmbedding G N X)‖ ≤
      ξ * ((∑ n, |(principal n : ℝ)|) / (1 + W)) := by
  rw [canonicalZeroSpatialNarrowPrincipal_difference s sf root principal D Df W L hW ξ,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ0]
  exact mul_le_mul_of_nonneg_left
    (canonicalZeroSpatialPrincipal_norm_le s sf root principal D Df W L hW u hu) hξ0

end Erdos3

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {X G : Type*} [Fintype X] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem canonicalZeroSpatialInputMap_physicalSite
    {X Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
    (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
    {W : ℝ} (hW : 0 ≤ W) (L τ : ℝ) (N : X → ℕ)
    (z : Option Zsp × X → ℤ) (x : X) :
    canonicalZeroSpatialInputMap s root D W L
      (fun k => (z k : ℝ) / trimmedSpatialWidths W τ N k) ⟨x, Sum.inl ()⟩ =
      (integerPhysicalSite root z x : ℝ) / (τ * (N x : ℝ) / 8) := by
  have hb : (1 + W : ℝ) ≠ 0 := by linarith
  have hn : trimmedSpatialWidths (K := Zsp) W τ N (none, x) = τ * (N x : ℝ) / 8 := by
    simp only [trimmedSpatialWidths, centeredSpatialWidths]
    ring
  have hs (j : Zsp) : trimmedSpatialWidths W τ N (some j, x) =
      (τ * (N x : ℝ) / 8) / (1 + W) := by
    simp only [trimmedSpatialWidths, centeredSpatialWidths, one_mul, div_div]
    ring
  rw [canonicalZeroSpatialInputMap_apply s root D W L hW]
  simp only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul, hn, hs,
    add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [div_div_eq_mul_div]
  by_cases ht : τ * (N x : ℝ) / 8 = 0
  · simp only [ht, div_zero, mul_zero, zero_div]
  · field_simp

theorem canonicalZeroSpatialNarrowInput_normalized
    {G J X : Type*} {ξ : ℝ} (hξ : ξ ≠ 0) (W τ : ℝ) (N : X → ℕ)
    (z : Option (G ⊕ J) × X → ℤ) :
    canonicalZeroSpatialNarrowInput ξ
      (fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ N k) =
      fun k => (z k : ℝ) / trimmedSpatialWidths W τ N k := by
  funext k
  rcases k with ⟨_ | (g | j), x⟩
  · rfl
  · rfl
  · simp only [canonicalZeroSpatialNarrowInput, narrowTrimmedSpatialWidths]
    by_cases hw : trimmedSpatialWidths (K := G ⊕ J) W τ N (some (Sum.inr j), x) = 0
    · simp only [hw, mul_zero, div_zero]
    · field_simp

theorem canonicalZeroSpatialNarrowInputMap_physicalSite
    {G J X : Type*} [Fintype G] [Fintype J] [DecidableEq G] [DecidableEq J]
    (s : Empty ↪ (G ⊕ J)) (root : G ⊕ J → ℤ) (D : Matrix Empty (G ⊕ J) ℤ)
    {W ξ : ℝ} (hW : 0 ≤ W) (hξ : ξ ≠ 0) (L τ : ℝ) (N : X → ℕ)
    (z : Option (G ⊕ J) × X → ℤ) (x : X) :
    canonicalZeroSpatialInputMap s root D W L
      (canonicalZeroSpatialNarrowInput ξ
        (fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ N k)) ⟨x, Sum.inl ()⟩ =
      (integerPhysicalSite root z x : ℝ) / (τ * (N x : ℝ) / 8) := by
  rw [canonicalZeroSpatialNarrowInput_normalized hξ W τ N z]
  exact canonicalZeroSpatialInputMap_physicalSite s root D hW L τ N z x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]
variable (s : Empty ↪ G) (sf : Empty ↪ (G ⊕ N))
  (root : G → ℤ) (principal : N → ℤ)
  (D : Matrix Empty G ℤ) (Df : Matrix Empty (G ⊕ N) ℤ) (W L : ℝ)

omit [DecidableEq G] [DecidableEq N] in
theorem canonicalZeroSpatialPrincipal_mass_ratio_le_one (hW : 0 ≤ W)
    (hbudget : (∑ k : G ⊕ N, |((Sum.elim root principal k : ℤ) : ℝ)|) ≤ W) :
    (∑ n, |(principal n : ℝ)|) / (1 + W) ≤ 1 := by
  have hroot0 : 0 ≤ ∑ g, |(root g : ℝ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at hbudget
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1 + W)).mpr
  linarith

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

variable (s : Empty ↪ G) (x : G → IntegerScalarCubeBox Empty S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
variable (τ ξ : ℝ) (box : X → ℕ)

local notation "root" => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedSmoothUniformBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem uniform_fiberLaw_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) :
    (FiniteProbabilityWeights.uniform G).fiberLaw f =
      FiniteProbabilityWeights.uniform H := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro y
  have hh := uniform_mean_surjective_hom_fiber f hf y
  change _ = (Fintype.card H : ℝ)⁻¹
  convert hh using 1
  unfold FiniteProbabilityWeights.fiberLaw FiniteProbabilityWeights.fiberMean
  congr 1

theorem uniform_tupleResidueReduction_fiberLaw {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).fiberLaw (tupleResidueReduction hMN) =
      FiniteProbabilityWeights.uniform (D → ZMod M) :=
  uniform_fiberLaw_surjective_hom (tupleResidueReduction hMN)
    (tupleResidueReduction_surjective hMN)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem FiniteProbabilityWeights.fiberLaw_comp {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (p : FiniteProbabilityWeights X) (f : X → Y) (g : Y → Z) :
    (p.fiberLaw f).fiberLaw g = p.fiberLaw (g ∘ f) := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro z
  change (p.fiberLaw f).mean (fun y => if g y = z then (1 : ℝ) else 0) =
    p.mean (fun x => if g (f x) = z then (1 : ℝ) else 0)
  exact p.fiberLaw_mean f _

theorem uniform_tupleResidueReduction_fiberLaw_postcompose {D Y : Type*}
    [Fintype D] [DecidableEq D] [Fintype Y]
    {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (f : (D → ZMod M) → Y) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).fiberLaw
        (fun x => f (tupleResidueReduction hMN x)) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).fiberLaw f := by
  rw [← uniform_tupleResidueReduction_fiberLaw hMN,
    FiniteProbabilityWeights.fiberLaw_comp]
  rfl

theorem tupleResidueReduction_affine {D : Type*} {M N : ℕ}
    (hMN : M ∣ N) (a x : D → ZMod N) (step : ℕ) :
    tupleResidueReduction hMN (fun d => a d + (step : ZMod N) * x d) =
      fun d => tupleResidueReduction hMN a d +
        (step : ZMod M) * tupleResidueReduction hMN x d := by
  funext d
  change ZMod.castHom hMN (ZMod M) (a d + (step : ZMod N) * x d) = _
  simp only [map_add, map_mul, map_natCast]
  rfl

theorem uniform_affine_tupleResidueReduction_fiberLaw {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (a : D → ZMod N) (step : ℕ) :
    ((FiniteProbabilityWeights.uniform (D → ZMod N)).fiberLaw
        (fun x d => a d + (step : ZMod N) * x d)).fiberLaw
          (tupleResidueReduction hMN) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).fiberLaw
        (fun y d => tupleResidueReduction hMN a d + (step : ZMod M) * y d) := by
  rw [FiniteProbabilityWeights.fiberLaw_comp]
  simp only [Function.comp_def, tupleResidueReduction_affine]
  exact uniform_tupleResidueReduction_fiberLaw_postcompose (D := D) hMN
    (fun y d => tupleResidueReduction hMN a d + (step : ZMod M) * y d)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastDataNativeProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X Ω Forecast : Type*} [Fintype X]
variable {Term : Forecast → Type*} {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_centered_forecast_twist_model
    {Center Ω T X Forecast : Type*} [MeasurableSpace Center] [Nonempty Forecast] [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (localBudget Pnative : ℝ) (hlocalBudget : 0 ≤ localBudget) (hPnative : 0 ≤ Pnative)
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : Measure Center) [IsProbabilityMeasure μ]
    (law : Center → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (forecast : Forecast → integerBox N → ℂ)
    {u p P massLog K C forecastCap εtail : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hmassLog : 0 ≤ massLog)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hforecastCapP : forecastCap ≤ Real.exp p)
    (hP : u + 2 * p +
      max (max localBudget (3 * Pnative + 3)) (2 * u + 4 * p + massLog + 20) + 32 ≤ P)
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp localBudget) (Real.exp localBudget)
          ⟨Real.exp localBudget, Real.exp_nonneg _⟩)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) 0 localBudget
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-localBudget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ)
    (centerConstant : Forecast → ∀ j, J j → ℝ)
    (twists : ∀ f, Term f → NormalizedPolynomialTwist X (Σ j, J j)
      (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩)
    (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ Real.exp massLog)
    (happrox : ∀ f v, ‖forecast f v - ∑ i, coefficient f i *
      (twists f i).eval N (fun j => subtractConstant (centerConstant f j) (poly j)) v.val‖ ≤
        Real.exp (-(2 * u + 4 * p + 12)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass ((centeredFiniteMarginal μ law hweight).siteLaw physical) C ≤ εtail)
    (htail : εtail ≤ 6 * positiveProjectionAccuracy P)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Q := max commonBudget (2 * u + 4 * p + massLog + 20)
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (models : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • models i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (Q + 2) ∧
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests err ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        Real.exp (-u)) ∧
      (nterms : ℝ) ≤ Real.exp (2 * Q + 2 * u + 4 * p + 34) ∧
      ∀ errLocal : Center × Ω → ℂ, Measurable errLocal →
        (∀ center z, ∃ j, errLocal (center, z) =
          𝔼 t ∈ slices z j, err (physical z t) * tests z j t) →
        Integrable errLocal (centeredFiniteProbabilityMeasure μ law) ∧
          (∫ y, ‖errLocal y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤ Real.exp (-u) := by
  intro commonBudget Q
  have hlocalCommon : localBudget ≤ commonBudget := le_max_left _ _
  have hcommon : 0 ≤ commonBudget := hlocalBudget.trans hlocalCommon
  obtain ⟨hQ, _, hcommonQ, hthreshold, hgain, _⟩ :=
    forecastAugmented_model_parameters hu hp hmassLog hcommon
  let shifted := fun f i => (twists f i).shiftConstant (centerConstant f)
  let atom := fun f i (v : integerBox N) => (shifted f i).eval N poly v.val
  have hatom (f) (i) : atom f i ∈
      twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
        (fun v : integerBox N => v.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩) v => W.eval N poly v.val) :=
    centeredForecastTwist_mem_common_family localBudget Pnative hPnative
      twists N poly centerConstant f i
  have happrox' (f) (v : integerBox N) :
      ‖forecast f v - ∑ i, coefficient f i * atom f i v‖ ≤
        forecastAugmentedUnitThreshold u p K C forecastCap / 8 := by
    have he := (happrox f v).trans (forecastAugmented_approximation_precision
      hu hp hK (zero_le_one.trans hC) hKp hCp hforecastCapP)
    change ‖forecast f v - ∑ i, coefficient f i *
      ((twists f i).shiftConstant (centerConstant f)).eval N poly v.val‖ ≤ _
    rw [centeredForecastTwist_sum_eq twists coefficient N poly centerConstant f v.val]
    exact he
  have hdetectCommon (signal : (X → ℤ) → ℂ)
      (hsignal : ∀ v, ‖signal v‖ ≤ 1)
      (hzero : ∀ v, v ∉ integerBox N → signal v = 0)
      (hlarge : forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) site slices tests signal) :
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
          (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩) (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel (1 : X → ℕ) 0 commonBudget
          (fun v : integerBox N => v.val) G) ∧
        Real.exp (-Q) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun v => signal v.val)
          (fun v => star (W.eval N poly v.val) * G v)‖ := by
    obtain ⟨W, G, hG, hc⟩ := hdetect signal hsignal hzero hlarge
    have he : Real.exp localBudget ≤ Real.exp commonBudget := Real.exp_le_exp.mpr hlocalCommon
    let W' := W.mono he he
      (show (⟨Real.exp localBudget, Real.exp_nonneg _⟩ : ℝ≥0) ≤
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩ from he)
    refine ⟨W', G, hG.map (fun model => model.mono hlocalCommon), ?_⟩
    exact hgain.trans ((Real.exp_le_exp.mpr (neg_le_neg hlocalCommon)).trans hc)
  exact exists_averaged_normalizedTwist_forecast_joint_model N poly μ law hweight
    physical site hphysical slices tests (1 : X → ℕ) 0 commonBudget forecast
    hu hp hQ hmassLog hK hC hforecastCap hKp hCp hforecastCapP hthreshold hP
    hslices hsize htests hforecast hdetectCommon Term coefficient atom hatom
    (Real.exp_nonneg massLog) le_rfl hmass happrox' hexcess htail input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

attribute [instance] ActualForecastData.fintypeTerm

namespace ActualForecastData

variable (N : X → ℕ) (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (Pnative massLog capLog E : ℝ)

end ActualForecastData

variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ} {F : Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.ActualForecastData
open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ}
variable (data : ActualForecastData N originalpoly Pnative massLog capLog E)

end Erdos3.VectorPolynomial.ActualForecastData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

section RankBounds

variable {s : ℕ} (hs : 0 < s) {J : Fin s → Type*} [∀ j, Fintype (J j)]
  (p A b e : L → ℕ) [∀ l, NeZero (p l)]
  (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
  (C : ℝ) (hC : 0 ≤ C)
  (F : ∀ j, J j → MvPolynomial V ℤ)
  (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
  (hrank : ∀ (l : L) (B : ℕ), b l < B → B ≤ A l → ∀ (j : Fin s)
    (row : J j → ZMod (p l ^ B)), (∃ i, IsUnit (row i)) →
    integerPolynomialRankProbability (p l) B j.val (F j) row ≤ (p l : ℝ) ^ (-C * B))
  (r : ∀ l, V → ZMod (p l ^ A l))

include hs hp hinj hC hF hrank

end RankBounds

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

theorem crtPrimePowerPolynomialLaw_eq_uniform (p A : L → ℕ) [∀ l, NeZero (p l)] :
    crtPrimePowerPolynomialLaw (V := V) p A =
      FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l)) := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro x
  exact FiniteProbabilityWeights.pi_uniform_weight x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CRTPolynomialInputStepLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [Fintype V]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem padicStepQuotientUnit_factor (p A step : ℕ)
    (hp : p.Prime) (hstep : step ≠ 0) :
    (p : ZMod (p ^ A)) ^ padicValNat p step *
        padicStepQuotientUnit p A step hp hstep = (step : ZMod (p ^ A)) := by
  rw [padicStepQuotientUnit_coe, ← Nat.cast_pow, ← Nat.cast_mul,
    Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := step))]

variable {L V : Type*} [Fintype L]

omit [Fintype L] in
theorem prescribedCRTArbitraryStepEquiv_local_step (p A : L → ℕ) (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (x : ∀ l, V → ZMod (p l ^ A l)) (l : L) (v : V) :
    (p l : ZMod (p l ^ A l)) ^ padicValNat (p l) step *
        prescribedCRTArbitraryStepEquiv p A step hp hstep x l v =
      (step : ZMod (p l ^ A l)) * x l v := by
  change (p l : ZMod (p l ^ A l)) ^ padicValNat (p l) step *
    ((padicStepQuotientUnit (p l) (A l) step (hp l) hstep : ZMod (p l ^ A l)) *
      x l v) = _
  rw [← mul_assoc, padicStepQuotientUnit_factor]

theorem prescribedCRTPolynomialInput_arbitrary_step (p A : L → ℕ) (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin x : ∀ l, V → ZMod (p l ^ A l)) (v : V) :
    prescribedCRTPolynomialInput p A (fun l => padicValNat (p l) step) hq origin
        (prescribedCRTArbitraryStepEquiv p A step hp hstep x) v =
      crtInput (fun l => p l ^ A l) hq origin v +
        (step : ℕ) * crtInput (fun l => p l ^ A l) hq x v := by
  apply (ZMod.prodEquivPi (fun l => p l ^ A l) hq).injective
  funext l
  rw [ZMod.prodEquivPi_apply, ZMod.prodEquivPi_apply]
  simp only [prescribedCRTPolynomialInput, map_add, map_mul, map_natCast]
  rw [crtInput_reduce (fun l => p l ^ A l) hq _ l v,
    crtInput_reduce (fun l => p l ^ A l) hq origin l v,
    crtInput_reduce (fun l => p l ^ A l) hq x l v]
  exact congrArg (origin l v + ·)
    (prescribedCRTArbitraryStepEquiv_local_step p A step hp hstep x l v)

local instance arbitraryStepCRTModulusNeZero (p A : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ A l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

variable [Fintype V]

theorem crtPolynomialInputLaw_arbitrary_step_uniform
    (p A : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l)) :
    crtPolynomialInputLaw p A (fun l => padicValNat (p l) step) hq origin =
      (FiniteProbabilityWeights.uniform (V → ZMod (∏ l, p l ^ A l))).fiberLaw
        (fun x v => crtInput (fun l => p l ^ A l) hq origin v + (step : ℕ) * x v) := by
  let E := crtInputAddEquiv (V := V) (fun l => p l ^ A l) hq
  let T := prescribedCRTArbitraryStepEquiv (V := V) p A step hp hstep
  let f : (V → ZMod (∏ l, p l ^ A l)) → (V → ZMod (∏ l, p l ^ A l)) :=
    fun x v => crtInput (fun l => p l ^ A l) hq origin v + (step : ℕ) * x v
  have hT := uniform_fiberLaw_surjective_hom T.toAddMonoidHom T.surjective
  change (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw T = _ at hT
  have hE := uniform_fiberLaw_surjective_hom E.toAddMonoidHom E.surjective
  change (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw E = _ at hE
  have heq : prescribedCRTPolynomialInput p A (fun l => padicValNat (p l) step) hq origin ∘ T =
      f ∘ E := by
    funext x v
    exact prescribedCRTPolynomialInput_arbitrary_step p A step hp hstep hq origin x v
  rw [crtPolynomialInputLaw, crtPrimePowerPolynomialLaw_eq_uniform]
  calc
    _ = ((FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw T).fiberLaw
        (prescribedCRTPolynomialInput p A (fun l => padicValNat (p l) step) hq origin) := by rw [hT]
    _ = (FiniteProbabilityWeights.uniform (∀ l, V → ZMod (p l ^ A l))).fiberLaw (f ∘ E) := by
      rw [FiniteProbabilityWeights.fiberLaw_comp, heq]
    _ = _ := by rw [← FiniteProbabilityWeights.fiberLaw_comp, hE]

omit [Fintype V] in
theorem crtInput_intCast_apply (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k))) (c : V → ℤ) (v : V) :
    crtInput q hq (fun l v => (c v : ZMod (q l))) v =
      (c v : ZMod (∏ l, q l)) := by
  exact map_intCast (ZMod.prodEquivPi q hq).symm (c v)

theorem crtPolynomialInputLaw_arbitrary_step_divisor_affine
    (p A : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (c : V → ℤ) {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l) :
    (crtPolynomialInputLaw p A (fun l => padicValNat (p l) step) hq
      (fun l v => (c v : ZMod (p l ^ A l)))).fiberLaw (tupleResidueReduction hdiv) =
      (FiniteProbabilityWeights.uniform (V → ZMod q)).fiberLaw
        (fun x v => (c v : ZMod q) + (step : ZMod q) * x v) := by
  rw [crtPolynomialInputLaw_arbitrary_step_uniform p A step hp hstep hq,
    uniform_affine_tupleResidueReduction_fiberLaw hdiv]
  congr 1
  funext x v
  change ZMod.castHom hdiv (ZMod q)
    (crtInput (fun l => p l ^ A l) hq (fun l v => (c v : ZMod (p l ^ A l))) v) + _ = _
  rw [crtInput_intCast_apply, map_intCast]

theorem crtPolynomialInputLaw_arbitrary_step_divisor_complexMean
    (p A : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (c : V → ℤ) {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ A l)
    (f : (V → ZMod q) → ℂ) :
    (crtPolynomialInputLaw p A (fun l => padicValNat (p l) step) hq
      (fun l v => (c v : ZMod (p l ^ A l)))).complexMean
        (fun x => f (tupleResidueReduction hdiv x)) =
      (FiniteProbabilityWeights.uniform (V → ZMod q)).complexMean
        (fun x => f (fun v => (c v : ZMod q) + (step : ZMod q) * x v)) := by
  rw [← FiniteProbabilityWeights.fiberLaw_complexMean,
    crtPolynomialInputLaw_arbitrary_step_divisor_affine p A step hp hstep hq c hdiv,
    FiniteProbabilityWeights.fiberLaw_complexMean]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedPeriodicGridQuadrature
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators NNReal
variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem rationalInactiveForecast_zero_off_image {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (hz : z ∉ Finset.univ.image gridPoint) (b : J → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z b = 0 := by
  rw [rationalInactiveForecast,
    inactive.fiberMean_eq_zero_of_not_mem_image gridPoint _ z hz, mul_zero]

theorem rationalInactiveForecast_divisor_tsum_test {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ)
    {q N : ℕ} [NeZero N] [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (J → ZMod q) → ℂ) :
    (∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b / gridVolume : ℝ) : ℂ) *
        test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      inactive.complexMean (fun i => (active i).complexMean
        (fun a => test (gridPoint i) (fun j => (Y i a j : ZMod q)))) := by
  classical
  rw [tsum_eq_sum (s := Finset.univ.image gridPoint) (fun z hz => by
    simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
      zero_div, Complex.ofReal_zero, zero_mul, Finset.expect_const_zero])]
  simp only [rationalInactiveForecast, mul_div_cancel_left₀ _ hV]
  rw [← Finset.expect_sum_comm]
  have hswap (b : J → ZMod N) :
      (∑ z ∈ Finset.univ.image gridPoint,
        (inactive.fiberMean gridPoint z (fun i => rationalOutputDensity (active i) (Y i) N b) : ℂ) *
          test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      inactive.complexMean (fun i => (rationalOutputDensity (active i) (Y i) N b : ℂ) *
        test (gridPoint i) (fun j => ZMod.castHom hq (ZMod q) (b j))) :=
    (inactive.complexMean_fiber_factor_sum_image gridPoint _ _).symm
  simp_rw [hswap]
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.expect_sum_comm]
  simp_rw [← Finset.mul_expect]
  apply Finset.sum_congr rfl
  intro i _
  rw [rationalOutputDensity_divisor_test (active i) (Y i) hq]
  rfl

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

variable {Aux J : Type*} [Fintype Aux] [Fintype J]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {Ω Aux J : Type*} [Fintype Ω] [Fintype Aux] [Fintype J]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {Ω Aux J V : Type*} [Fintype Ω] [Fintype Aux] [Fintype J] [Fintype V]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem enlargedPreparedCommonSamplerDimension_allocation (m M Jalloc : ℕ) :
    Jalloc ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
  unfold enlargedPreparedCommonSamplerDimension
  omega

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem enlargedPreparedCommonSamplerBlock_positiveModerate (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    positiveModerateSpectrumBlockCount a.1.val rows.card ((layerTailDegree m + 1) * rows.card) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  dsimp only
  apply le_trans _ ((le_max_left _ _).trans
    (enlargedPreparedCommonSamplerBlock_spectrum L Jalloc s hs a))
  unfold positiveModerateSpectrumBlockCount
  apply Nat.succ_le_succ
  apply max_le_max (le_refl _)
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
  {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators Classical

variable {D G A : Type*} {B : D → Type*} {h : ℕ}

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {D G : Type*} {B : D → Type*}

section TopPart

variable {I J R : Type*} [CommRing R]

end TopPart

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

variable {D G R : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R]

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem spatialDegreeOutput_card [Fintype X] (j : Fin m) :
    Fintype.card (SpatialDegreeOutput X j) = if j.val = 0 then Fintype.card X else 0 := by
  rw [Fintype.card_subtype]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, Finset.filter_true,
    Finset.filter_false, Finset.card_univ, Finset.card_empty]

theorem spatialDegreeOutput_sum_card [Fintype X] (hm : 0 < m) :
    (∑ j : Fin m, Fintype.card (SpatialDegreeOutput X j)) = Fintype.card X := by
  simp_rw [spatialDegreeOutput_card]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rfl
  · intro j _ hj
    have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
    simp only [hne, ite_false]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedCongruenceRankOutput_card_le [Fintype X] [∀ j, Fintype (E j)]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m) :
    Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤
      Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j) := by
  change Fintype.card (SpatialDegreeOutput X j ⊕
    (E j ⊕ AllocatedCongruenceIntegerAxis inactive j)) ≤ _
  simp only [Fintype.card_sum]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_left
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le
    (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)

theorem allocatedCongruenceRankOutput_sum_card_le [Fintype X] [∀ j, Fintype (E j)]
    (hm : 0 < m) (inactive : LayerSamplerAxis I n → Prop) :
    (∑ j : Fin m, Fintype.card (AllocatedCongruenceRankOutput X E inactive j)) ≤
      Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) := by
  calc
    _ ≤ ∑ j : Fin m,
        (Fintype.card (SpatialDegreeOutput X j) + (Fintype.card (E j) + n j)) :=
      Finset.sum_le_sum (fun j _ => allocatedCongruenceRankOutput_card_le inactive j)
    _ = _ := by rw [Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularRankSmallBallExponent_eq {s : ℕ} (hs : 0 < s) :
    modularRankSmallBallExponent s = 1 / (2 : ℝ) ^ (s - 1) := by
  have hexp : 1 - (s : ℝ) = -((s - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [modularRankSmallBallExponent, hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast,
    one_div]

end Erdos3

end

section

namespace Erdos3

theorem modularInitialBlockCount_threshold {s : ℕ} (hs : 0 < s) (d : ℕ) :
    ⌈2 * ((modularInitialRankStrength s d : ℝ) + d + 10) /
      modularRankSmallBallExponent s⌉₊ ≤ modularInitialBlockCount s d := by
  apply Nat.ceil_le.mpr
  rw [modularRankSmallBallExponent_eq hs, div_div_eq_mul_div, div_one]
  have hpow : 2 * (2 : ℝ) ^ (s - 1) = (2 : ℝ) ^ s := by
    rw [← pow_succ', Nat.sub_add_cancel hs]
  calc
    _ = (2 : ℝ) ^ s * ((modularInitialRankStrength s d : ℝ) + d + 10) := by
      rw [← hpow]
      ring
    _ ≤ (modularInitialBlockCount s d : ℝ) := by
      simp only [modularInitialBlockCount, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_one]
      linarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedShortPrincipalRank_active (j : Fin m)
    (i : AllocatedCongruenceIntegerAxis (allocatedShortAxis (I := I) U basis S.value) j) :
    S.value ^ (j.val + 1) < basisAxisScale (basis j) i.val := by
  exact Nat.lt_of_not_ge i.property

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

omit [Fintype X] in

theorem allocatedShortRankSelectedWidth_common_gap {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) {W : ℝ}
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
      8 * (probabilityProfileLipschitz : ℝ) * W ≤
        (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
          ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hspatial : ∀ l x, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      residueProfileWidth stride V (some (.inl (spatial l)), x)) :
    ∀ a, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      allocatedShortRankSelectedWidth B U basis S spatial stride V a := by
  rintro ⟨j, (x | i), l⟩
  · exact hspatial l x.val
  · exact hprincipal j i.val (allocatedShortPrincipalRank_active B U basis S j i)

theorem allocatedShortRankSelectedWidth_budget {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) {cap W κ : ℝ}
    (hcap : 0 < cap) (hκ : 0 < κ) (hcapW : cap ≤ W)
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
      8 * (probabilityProfileLipschitz : ℝ) * W ≤
        (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
          ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hspatial : ∀ l x, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      residueProfileWidth stride V (some (.inl (spatial l)), x))
    (hbudget : 2 * (Fintype.card (AllocatedSmoothRankCoefficientIndex X
        (allocatedShortAxis (I := I) U basis S.value) L) : ℝ) * cap / κ ≤ W) :
    (∀ a, 8 * (probabilityProfileLipschitz : ℝ) * cap ≤
      allocatedShortRankSelectedWidth B U basis S spatial stride V a) ∧
    (∑ a, 16 * (probabilityProfileLipschitz : ℝ) * cap /
      allocatedShortRankSelectedWidth B U basis S spatial stride V a) ≤ κ := by
  apply finite_residue_error_common_gap_budget
    (allocatedShortRankSelectedWidth B U basis S spatial stride V)
    (lt_of_lt_of_le zero_lt_one probabilityProfileLipschitz_one_le) hcap hκ hcapW
  · exact allocatedShortRankSelectedWidth_common_gap B U basis S spatial stride V hprincipal hspatial
  · exact hbudget

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

theorem samplerSeparated_eval₂_raw_congr
    {D G R : Type*} {B : D → Type*} [CommRing R]
    (inactive : D → Prop) (h : D → ℕ)
    (poly : MvPolynomial (SamplerTupleIndex G B h) ℤ)
    (long : SamplerLongVariables inactive G B h → R)
    (v w : PrincipalTupleIndex B h × Option Empty → R)
    (hvw : ∀ j : PrincipalTupleIndex B h, inactive j.1 → v (j, none) = w (j, none)) :
    MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long v)
        (rename (samplerSeparatedVariable inactive h) poly) =
      MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long w)
        (rename (samplerSeparatedVariable inactive h) poly) := by
  simp only [eval₂_rename]
  congr 1
  funext k
  cases k with
  | inl g => rfl
  | inr j =>
    by_cases hj : inactive j.1
    · simpa only [Function.comp_apply, samplerSeparatedVariable_inactive inactive h _ _ _ hj,
        Sum.elim_inr] using hvw j hj
    · simp only [Function.comp_apply, samplerSeparatedVariable_active inactive h _ _ _ hj,
        Sum.elim_inl]

namespace VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

omit [Fintype X] [∀ j, Fintype (E j)] in
theorem allocatedForecastPolynomial_eval₂_raw_congr
    (inactive : LayerSamplerAxis I n → Prop)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    {R : Type*} [CommRing R]
    (long : LayerSamplerLongVariables inactive G B → R)
    (v w : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → R)
    (hvw : ∀ j : PrincipalTupleIndex B (layerSamplerDegree I n),
      inactive j.1 → v (j, none) = w (j, none))
    (o : Sigma (AllocatedCongruenceRankOutput X E inactive)) :
    MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long v)
        (allocatedForecastPolynomial inactive base noise deck projection o) =
      MvPolynomial.eval₂ (Int.castRingHom R) (Sum.elim long w)
        (allocatedForecastPolynomial inactive base noise deck projection o) :=
  samplerSeparated_eval₂_raw_congr inactive (layerSamplerDegree I n)
    (allocatedUnconditionedCongruenceIntegerPolynomial inactive o.1 base noise deck
      (projection o.1) o.2) long v w hvw

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S

omit [Fintype X] [∀ j, Fintype (E j)] in
theorem allocatedShortPrincipalRaw_restrict
    (v : PrincipalIntegerTuples B degree Empty sides)
    (j : PrincipalTupleIndex B degree) (hj : short j.1) :
    allocatedShortPrincipalRaw B U basis S (principalAxisRestrict short v) (j, none) =
      (v j none : ℤ) := by
  simp only [allocatedShortPrincipalRaw, hj, dite_true, principalAxisRestrict]

omit [Fintype X] [∀ j, Fintype (E j)] in
theorem allocatedForecastPolynomial_short_raw
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ) (long : LayerSamplerLongVariables short G B → ZMod q)
    (v : PrincipalIntegerTuples B degree Empty sides)
    (o : Sigma (AllocatedCongruenceRankOutput X E short)) :
    MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim long (fun k => ((v k.1 k.2 : ℤ) : ZMod q)))
        (allocatedForecastPolynomial short base noise deck projection o) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim long (fun k => (allocatedShortPrincipalRaw B U basis S
          (principalAxisRestrict short v) k : ZMod q)))
        (allocatedForecastPolynomial short base noise deck projection o) := by
  apply allocatedForecastPolynomial_eval₂_raw_congr
  intro j hj
  rw [allocatedShortPrincipalRaw_restrict B U basis S v j hj]

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X]

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (R : Fin m → ℝ)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R : Fin m → ℝ)

theorem forecastNativeAmbientLinear_lipschitz :
    LipschitzWith (forecastNativeAmbientLip U b o R) (forecastNativeAmbientLinear U b o R) :=
  (forecastNativeAmbientLinear U b o R).toContinuousLinearMap.lipschitz

variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Active" => {a : LayerSamplerAxis I n // ¬P a}
local notation "Output" => (Σ _a : Active, Unit)

theorem forecastNativeFillAxes_lipschitz (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith 1 (forecastNativeFillAxes P frozen) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  by_cases ha : P a
  · simp only [forecastNativeFillAxes, ha, ↓reduceDIte, dist_self, dist_nonneg]
  · simpa only [forecastNativeFillAxes, ha, ↓reduceDIte] using dist_le_pi_dist v w ⟨⟨a, ha⟩, ()⟩

variable {X : Type*} [Fintype X]
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))

theorem forecastNativeSpatialInverse_lipschitz (center : X → ℝ) (τ : ℝ) :
    LipschitzWith ‖τ / 8‖₊ (forecastNativeSpatialInverse center τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (mul_nonneg (norm_nonneg _) dist_nonneg)).mpr
  intro x
  change dist (center x + τ / 8 * z ⟨x, Sum.inl ()⟩)
    (center x + τ / 8 * w ⟨x, Sum.inl ()⟩) ≤ _
  rw [dist_add_left, dist_eq_norm, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist z w _) (norm_nonneg _)

theorem forecastNativeTorusInverse_lipschitz (d : ℕ) [NeZero d]
    (deck : (Σ j, J j) → ZMod d)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith (forecastNativeAmbientLip U b o R)
      (forecastNativeTorusInverse U b o R P d deck frozen) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have h := ((forecastNativeAmbientLinear_lipschitz U b o R).comp
    (forecastNativeFillAxes_lipschitz P frozen)).dist_le_mul v w
  simp only [mul_one] at h
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
  intro a
  rw [forecastNativeTorusInverse, forecastNativeTorusInverse, dist_add_right,
    dist_eq_norm, ← AddCircle.coe_sub]
  apply QuotientAddGroup.norm_mk_le_norm.trans
  rw [← sub_div, norm_div]
  have hd : (1 : ℝ) ≤ ‖(d : ℝ)‖ := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  exact (div_le_self (norm_nonneg _) hd).trans
    ((dist_le_pi_dist _ _ a).trans h)

namespace NormalizedPolynomialTwist

variable {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem forecastPullback_norm_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (τ : ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (y : Domain) : ‖W.forecastPullback U b o R P residue deck center τ frozen y‖ ≤ 1 := by
  unfold forecastPullback
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.mask_bound _)).trans (W.smooth_bound _)

theorem forecastPullback_lipschitz
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (τ : ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith (L * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
      (W.forecastPullback U b o R P residue deck center τ frozen) := by
  let : NeZero W.cover := ⟨W.cover_pos.ne'⟩
  have hin := ((forecastNativeSpatialInverse_lipschitz center τ).comp LipschitzWith.prod_fst).prodMk
    ((forecastNativeTorusInverse_lipschitz U b o R P W.cover deck frozen).comp LipschitzWith.prod_snd)
  simp only [mul_one] at hin
  have h := W.smooth_lipschitz.comp hin
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [dist_eq_norm]
  change ‖W.mask residue * W.smooth _ - W.mask residue * W.smooth _‖ ≤ _
  rw [← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.mask_bound _)).trans
    (by simpa only [Function.comp_apply, dist_eq_norm] using h.dist_le_mul y z)

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X] {m : ℕ}
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R : Fin m → ℝ) (base : X → ℤ) (N : X → ℕ) (τ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R : Fin m → ℝ)

end Erdos3.VectorPolynomial

end

end OAI

end


