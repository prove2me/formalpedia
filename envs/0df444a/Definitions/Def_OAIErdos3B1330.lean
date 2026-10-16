-- Prove2me | Definitions.Def_OAIErdos3B1330
-- name    : OAIErdos3B1330
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T20:01:45.154979+00:00
-- url     : https://prove2.me/theorems/b942190e-01c2-41fb-bee9-7b6ce4616630
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1331 of 1351
-- statement:
--   Definitions bundle 1331 of 1351 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1329`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1331 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_Rbad`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_base`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_center`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_commonTuple`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_exponent`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_lower`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_noise`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_normalizedNoise`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_origin`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_prescribed`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_primes`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_read`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_sample`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeBudgets_width`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_base`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_center`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_commonTuple`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_exponent`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_lower`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_noise`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_origin`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_prescribed`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_primes`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_read`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_sample`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.enlargeP_width`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.normalizedNoise`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.physicalPolynomial`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.physicalPolynomial_mem`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.primeNeZero`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.target`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.target_enlargeP`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.target_weakenSliceWidth`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.weakenSliceWidth`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.weakenSliceWidth_lower`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.weakenSliceWidth_width`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.enlargeP`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.enlargeP_D`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.enlargeP_P`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.enlargeP_Pbad`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.enlargeP_Ppres`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.enlargeP_κ`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.noConfusion`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.withSliceWidth`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.withSliceWidth_P`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.withSliceWidth_Pbad`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.withSliceWidth_Ppres`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastSetup.withSliceWidth_κ`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.casesOn`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_enlargeP`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.density_weakenSliceWidth`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.enlargeP`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.enlargeP_kernelLower`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.enlargeP_kernelWidth`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.enlargeP_path`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.enlargeP_principalLaw`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.kernelLower`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.kernelWidth`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.kernelWidth_ne_zero`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.kernelWidth_pos`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.principalLaw`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.principalSupport`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.target`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.target_enlargeP`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.target_weakenSliceWidth`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.weakenSliceWidth`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.weakenSliceWidth_kernelLower`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.weakenSliceWidth_kernelWidth`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.weakenSliceWidth_path`, `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.weakenSliceWidth_principalLaw`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFrozenFullChart_low_residual`, `OAI.Erdos3.VectorPolynomial.actualForecastPrimeNeZero`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredFramedRead_bad_depth_eq`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredFramedRead_bad_product_eq`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenIntegerFullChart`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenIntegerFullChart_spatial`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenIntegerFullChart_support`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenParameterBox_bound`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenParameterBox_mem`, `OAI.Erdos3.VectorPolynomial.allocatedParameterBox_coordinate_bound`, `OAI.Erdos3.VectorPolynomial.allocatedParameterBox_root_bound`, `OAI.Erdos3.VectorPolynomial.allocatedParameterBox_side_eq`, `OAI.Erdos3.VectorPolynomial.allocatedParameterBox_slice_cost`, `OAI.Erdos3.VectorPolynomial.exists_allocated_fullBox_normalized_approximation`, `OAI.Erdos3.VectorPolynomial.integerSampledLowTags_freeze`, `OAI.Erdos3.VectorPolynomial.integerSampledRealChart_freeze`, `OAI.Erdos3.VectorPolynomial.integerSampledSpatial_freeze`, `OAI.Erdos3.VectorPolynomial.preparedCenteredActualForecastPath`, `OAI.Erdos3.VectorPolynomial.preparedCenteredGoodActualForecastPath`, `OAI.Erdos3.VectorPolynomial.preparedCenteredSupportedActualForecastPath`, `_private.Sampling.ActualFixedSpatialSlicedForecastSourceLaw.0.OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.det_ne_zero_change_decidable`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B072

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedParameterBox_coordinate_bound (t : integerBox sides)
    (k : LayerSamplerVariables G I n B) : |(t.val k : ℝ)| ≤ S.value := by
  have ht := (mem_integerBox sides t.val).mp t.property k
  have hside : sides k ≤ S.value := by
    cases k with
    | inl g => exact le_rfl
    | inr j => exact allocatedPrincipalSides_le_scale B U b S j
  have ht0 : (0 : ℝ) ≤ t.val k := by exact_mod_cast ht.1
  rw [abs_of_nonneg ht0]
  exact (by exact_mod_cast ht.2.le : (t.val k : ℝ) ≤ sides k).trans (Nat.cast_le.mpr hside)

theorem allocatedParameterBox_root_bound (t : integerBox sides) :
    (∑ k, |(t.val k : ℝ)|) ≤ allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) =>
    allocatedParameterBox_coordinate_bound B U b S t k)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, mul_zero, zero_add] using hsum

theorem allocatedParameterBox_slice_cost {p : ℝ} {A : Finset (integerBox sides)}
    (hA : IsDenseCommonStrideBox sides p (A.image Subtype.val)) :
    (Fintype.card (integerBox sides) : ℝ) / A.card ≤
      Real.exp (p * Fintype.card (LayerSamplerVariables G I n B)) := by
  exact dense_commonStride_slice_card_ratio Subtype.val Subtype.val_injective
    (by ext t; simp) hA

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedParameterBox_side_eq (i : LayerSamplerVariables G I n B) :
    layerSamplerBox B U b S i = (sides i : ℝ) := by
  cases i <;> rfl

theorem allocatedFrozenParameterBox_mem
    (keep : LayerSamplerVariables G I n B → Prop) [DecidablePred keep]
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < sides i.val)
    (u : {i // keep i} → ℤ)
    (hu : u ∈ integerBox (fun i : {i // keep i} => sides i.val)) :
    finiteSplitPoint keep u fixed ∈ integerBox sides := by
  apply (mem_integerBox sides _).mpr
  intro i
  by_cases hi : keep i
  · simpa only [finiteSplitPoint, dif_pos hi] using
      (mem_integerBox _ u).mp hu ⟨i, hi⟩
  · simpa only [finiteSplitPoint, dif_neg hi] using hfixed ⟨i, hi⟩

theorem allocatedFrozenParameterBox_bound
    (keep : LayerSamplerVariables G I n B → Prop) [DecidablePred keep]
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < sides i.val)
    (u : {i // keep i} → ℤ)
    (hu : u ∈ integerBox (fun i : {i // keep i} => sides i.val)) :
    ∀ i, |((finiteSplitPoint keep u fixed i : ℤ) : ℝ)| ≤ layerSamplerBox B U b S i := by
  intro i
  have hi := (mem_integerBox sides _).mp
    (allocatedFrozenParameterBox_mem B U b S keep fixed hfixed u hu) i
  have hnonneg : (0 : ℝ) ≤ (finiteSplitPoint keep u fixed i : ℤ) := by exact_mod_cast hi.1
  rw [abs_of_nonneg hnonneg, allocatedParameterBox_side_eq B U b S]
  exact_mod_cast hi.2.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_fullBox_normalized_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (hRootBudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτhalf : τ ≤ 1 / 2) (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((max P E + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((max P E + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedJointBaseDensity B U basis hb o hR hσ S X p hm
    let Z := selectedJointDensityMass bases stride T widths density
    ∃ (hN : ∀ x, 0 < N x) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∃ hnormalizer : |Z - 1| ≤ Real.exp (-E) ∧
      Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2,
    ∃ hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x,
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let root : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    let hrootSum := fun t => (allocatedParameterBox_root_bound B U basis S t).trans hRootBudget
      let pathLaw := allocatedOriginalPathLaw B U basis hb o hR hσ S X p hm N hN _hW _hτ _hξ
        stride T hmass bases hbases hnormalizer.2.2.1
      let physical := narrowPhysicalSiteMap (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        _hW _hτ _hξ1 N hN hmargin root hrootSum
      let Ctail := 4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
      ∀ {Tests : (bases × rectangularWeightIndices 0 widths 1) → Type*}
        [∀ z, Nonempty (Tests z)]
        (slices : ∀ z, Tests z → Finset Sites) (tests : ∀ z, Tests z → Sites → ℂ)
        (w : X → ℕ) (degree : ℕ) {u pModel budget pSlice : ℝ}
        (_hu : 0 ≤ u) (_hpModel : 0 ≤ pModel) (_hbudget : 0 ≤ budget)
        (_hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel)
        (_hCtail : Ctail ≤ Real.exp pModel)
        (_hDense : ∀ z j, IsDenseCommonStrideBox sides pSlice ((slices z j).image root))
        (_htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
        {periodCap coverCap : ℝ} {lip : ℝ≥0},
        let K := Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
        u + 2 * pModel + budget + 30 ≤ E →
        (∀ signal : (X → ℤ) → ℂ, (∀ t, ‖signal t‖ ≤ 1) →
          (∀ t, t ∉ integerBox N → signal t = 0) →
          allocatedModelUnitThreshold u pModel K Ctail ≤ sampledSliceSeminorm pathLaw
            (fun z t => jointIntegerPhysicalSite (root t) (z.1.val, z.2.val)) slices tests signal →
          ∃ (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
            (F : integerBox N → ℂ),
            Nonempty (NativeSampleModel w degree budget (fun t : integerBox N => t.val) F) ∧
            Real.exp (-budget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
              (fun t => signal t.val) (fun t => star (twist.eval N p t.val) * F t)‖) →
        ∀ (input : integerBox N → ℂ), (∀ t, ‖input t‖ ≤ Real.exp pModel) →
        ∃ (nterms : ℕ) (_ : 0 < nterms)
          (Q : Fin nterms → (integerBox N → ℂ))
          (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
          (∀ i, Q i ∈ twistedNativeSampleFunctions w degree budget
            (fun t : integerBox N => t.val)
            (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
              (t : integerBox N) => twist.eval N p t.val)) ∧
          input = (∑ i, coeff i • Q i) + err ∧
          (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
          sampledSliceSeminorm pathLaw physical slices tests err ≤ Real.exp (-u) ∧
          (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * pModel + 30) := by
  obtain ⟨A, hA, hmodel⟩ := exists_allocated_narrow_normalized_approximation m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ _ I _ _ n B _ _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P E hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hRootBudget hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density Z
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hmodel⟩ :=
    hmodel B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
      hW hWP hτ hτP hτhalf hτdim hξ hξ1 hξP N hsize hrank hRank T hT
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro sides Sites root hrootSum pathLaw physical Ctail Tests _ slices tests
    w degree u pModel budget pSlice hu hpModel hbudget hSliceLog hCtail hDense htests
    periodCap coverCap lip K htail hdetect input hinput
  have hsides (k : LayerSamplerVariables G I n B) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U basis S j
  let : ∀ k, NeZero (sides k) := fun k => ⟨(hsides k).ne'⟩
  let : Nonempty Sites := (integerBox_nonempty sides).to_subtype
  have hroot (t : Sites) (k) : |(root t k : ℝ)| ≤ Real.exp P :=
    (allocatedParameterBox_coordinate_bound B U basis S t k).trans hLP
  have hsizeModel (z) (j) : (Fintype.card Sites : ℝ) / (slices z j).card ≤ K :=
    allocatedParameterBox_slice_cost B U basis S (hDense z j)
  exact hmodel root hroot hrootSum slices tests w degree hu hpModel hbudget
    (Real.exp_nonneg _) (Real.exp_le_exp.mpr hSliceLog) hCtail hsizeModel htests
    htail hdetect input hinput

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators Classical

theorem integerSampledRealChart_freeze {A V : Type*}
    (β : A → MvPolynomial V ℤ) (keep : V → Prop)
    (fixed : {i // ¬keep i} → ℤ) (i : A) :
    integerSampledRealChart (fun z => freezePolynomial keep fixed (β z)) i =
      freezePolynomial keep (fun i => (fixed i : ℝ)) (integerSampledRealChart β i) :=
  freezePolynomial_map (Int.castRingHom ℝ) keep fixed (β i)

theorem integerSampledSpatial_freeze {m : ℕ} {X V : Type*} {J : Fin m → Type*}
    (β : X ⊕ (Σ j, J j) → MvPolynomial V ℤ) (keep : V → Prop)
    (fixed : {i // ¬keep i} → ℤ) (u : {i // keep i} → ℤ) :
    integerSampledSpatial (fun z => freezePolynomial keep fixed (β z)) u =
      integerSampledSpatial β (finiteSplitPoint keep u fixed) := by
  funext i
  exact freezePolynomial_eval keep fixed (β (Sum.inl i)) u

theorem integerSampledLowTags_freeze {m : ℕ} {X V : Type*}
    (J : Fin m → Type*) [∀ j, Fintype (J j)] (k : ℕ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial V ℤ) (keep : V → Prop)
    (fixed : {i // ¬keep i} → ℤ) (u : {i // keep i} → ℤ) :
    integerSampledLowTags J k (fun z => freezePolynomial keep fixed (β z)) u =
      integerSampledLowTags J k β (finiteSplitPoint keep u fixed) := by
  funext i
  exact freezePolynomial_eval keep fixed (β (Sum.inr (lowTaggedIndex J k i))) u

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

noncomputable def allocatedFrozenIntegerFullChart
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ) :
    X ⊕ (Σ j, J j) → MvPolynomial {i // keep i} ℤ :=
  fun z => freezePolynomial keep fixed
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)

theorem allocatedFrozenIntegerFullChart_support
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ) :
    ∀ i, integerSampledRealChart
      (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) i ∈
      weightedSupportLE (fun _ : {i // keep i} => 1) (fullTaggedVariableWeight J i) := by
  intro i
  change integerSampledRealChart (fun z => freezePolynomial keep fixed
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) i ∈ _
  rw [integerSampledRealChart_freeze]
  exact freezePolynomial_support keep _
    (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample i)

theorem allocatedFrozenIntegerFullChart_spatial
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (u : {i // keep i} → ℤ) :
    integerSampledSpatial
      (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u =
      jointIntegerPhysicalSite (finiteSplitPoint keep u fixed) (a, v) := by
  change integerSampledSpatial (fun z => freezePolynomial keep fixed
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) u = _
  rw [integerSampledSpatial_freeze, allocatedRecoveredIntegerFullChart_spatial]

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFrozenFullChart_low_residual
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val)
    (k : ℕ) (u : {i // keep i} → ℤ)
    (hu : u ∈ integerBox (fun i : {i // keep i} =>
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) i.val))
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval
      (fun z => (integerSampledSpatial
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u z : ℝ))
      (lowTaggedPolynomial J k poly i) - (c (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u i : ℝ)| ≤ 1 / 8 := by
  have hs := integerSampledSpatial_freeze
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) keep fixed u
  have ht := integerSampledLowTags_freeze J k
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) keep fixed u
  change integerSampledSpatial
    (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u = _ at hs
  change integerSampledLowTags J k
    (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) u = _ at ht
  rw [hs, ht]
  exact h.integerFullChart_low_residual B U b hb o S hR hσ poly hm hσ1 C hC hchart hsmall hp
    c a v sample read k (finiteSplitPoint keep u fixed)
    (allocatedFrozenParameterBox_bound B U b S keep fixed hfixed u hu) i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module Submodule VectorPolynomial
open scoped TensorProduct

variable {A V L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] realChartSubstitute weightedAdaptedRealChartLie weightedAdaptedRealChartHom

variable {m : ℕ} {G X : Type*} [Fintype G] {I J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom realSymbolHomogeneousPullbackHom

namespace CertifiedFullChartFiniteHistory

variable {m s : ℕ} {G X ι η L : Type} [Fintype G] [Fintype η]
  [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (Utag j))ᗮ)
  (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (Utag j)))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ Utag j)
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Kinitial : Set (X ⊕ (Σ j, J j) → ℝ)} {N : X → ℕ} {Bphase : ℝ}

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalLocalGoodForecastPath
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  (allocatedShortAxis (I := I) U b S.value) noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B → ZMod (q.val ^ Aexp q.val))

local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)

include hm hPr hDmod hbad

include hm hPr hDmod hbad

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  (allocatedShortAxis (I := I) U b S.value) noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B → ZMod (q.val ^ Aexp q.val))

local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)

include hm hPr hDmod hbad

include hm hPr hDmod hbad

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (hm : 0 < m)
variable (Pr : Finset ℕ) [∀ q : Pr, NeZero q.val]
variable (Aexp epres : ℕ → ℕ) (hPr : ∀ q ∈ Pr, q.Prime)
variable (Dmod : ℕ)
variable (hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
variable (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (rdeck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → Eout j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G) (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable (Rbad : ℕ)
variable (hbad : (∏ q : Pr, q.val ^ allocatedCongruenceBadDepth
  (allocatedShortAxis (I := I) U b S.value) noise rdeck projection spatial kernel block Pr Aexp
    (modularForecastRankConstant m Dmod : ℝ) q.val) ≤ Rbad)
variable (base : X → ℤ)
variable (origin : ∀ q : Pr, LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B → ZMod (q.val ^ Aexp q.val))

local notation "N" => (∏ q : Pr, (Subtype.val q) ^ Aexp (Subtype.val q))
local notation "poly" => allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value) base noise rdeck projection
local notation "pRat" => crtPolynomialInputLaw (fun q : Pr => (Subtype.val q))
  (fun q : Pr => Aexp (Subtype.val q)) (fun q : Pr => epres (Subtype.val q))
  (primePower_crt_coprime (fun q : Pr => (Subtype.val q)) (fun q : Pr => Aexp (Subtype.val q))
    (fun q => hPr (Subtype.val q) (Subtype.property q)) Subtype.val_injective) origin
local notation "Cmod" => (modularForecastRankConstant m Dmod : ℝ)

include hm hPr hDmod hbad

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

theorem actualForecastPrimeNeZero (Pr : Finset ℕ) (hPr : ∀ p ∈ Pr, p.Prime) :
    ∀ p : Pr, NeZero p.val :=
  fun p => ⟨(hPr p.val p.property).ne_zero⟩

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

structure ActualFixedSpatialForecastPath where
  base : X → ℤ
  noise : Option (LayerSamplerVariables G I n B) × X → ℤ
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
    (allocatedLayerWidths B U b S j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)
  read : AllocatedActualCoefficientIndex G X I Eout n B → ℤ
  readNoise : allocatedReadNoise read = noise
  readProjection : ∀ (j : Fin m) (i : Fin (n j))
    (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
    allocatedReadProjection read ⟨j, Sum.inr i⟩ e = (sample j).2 i e
  center : ∀ j, U j
  commonTuple : G → IntegerScalarCubeBox Empty S.value
  primes : Finset ℕ
  prime : ∀ p ∈ primes, p.Prime
  exponent : ℕ → ℕ
  prescribed : ℕ → ℕ
  origin : ∀ p : primes, LayerSamplerLongVariables
    (allocatedShortAxis (I := I) U b S.value) G B → ZMod (p.val ^ exponent p.val)
  Rbad : ℕ
  hbad : letI := actualForecastPrimeNeZero primes prime
    (∏ p : primes, p.val ^ allocatedCongruenceBadDepth
      (allocatedShortAxis (I := I) U b S.value) noise (allocatedReadDeck read)
      (fun j a => allocatedReadProjection read ⟨j, a.val⟩)
      spatial kernel block primes exponent (modularForecastRankConstant m Dmod : ℝ)
      p.val) ≤ Rbad
  RbadBound : (Rbad : ℝ) ≤ Real.exp Pbad
  presBound : ((∏ p : primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres
  lower : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ
  width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ
  hwidth : ∀ a p, δslice ≤ width a p
  hlower : ∀ a p, 0 ≤ lower a p
  hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1
  detFalse : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) false).det ≠ 0
  detTrue : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) true).det ≠ 0
  hjac : inverseJacobian (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) true detTrue) ≤ Real.exp P
  hinverse : ‖(fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
    (fun k : Option G × X => (noise (Option.map Sum.inl k.1, k.2) : ℝ) /
      trimmedSpatialWidths Wsp τ physicalN k) false detFalse).symm.toContinuousLinearMap‖ ≤
    Real.exp P

namespace ActualFixedSpatialForecastPath

variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def normalizedNoise (k : Option G × X) : ℝ :=
  (path.noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k

omit [Fintype Tsp] in

theorem primeNeZero : ∀ p : path.primes, NeZero p.val :=
  actualForecastPrimeNeZero path.primes path.prime

end ActualFixedSpatialForecastPath

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type}
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres P' Pbad' Ppres' : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable (hP : P ≤ P') (hPbad : Pbad ≤ Pbad') (hPpres : Ppres ≤ Ppres')

def enlargeBudgets : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
    Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P' Pbad' Ppres' :=
  { path with
    RbadBound := path.RbadBound.trans (Real.exp_le_exp.mpr hPbad)
    presBound := path.presBound.trans (Real.exp_le_exp.mpr hPpres)
    hjac := path.hjac.trans (Real.exp_le_exp.mpr hP)
    hinverse := path.hinverse.trans (Real.exp_le_exp.mpr hP) }

@[simp] theorem enlargeBudgets_center :
    (path.enlargeBudgets hP hPbad hPpres).center = path.center := rfl

@[simp] theorem enlargeBudgets_base :
    (path.enlargeBudgets hP hPbad hPpres).base = path.base := rfl

@[simp] theorem enlargeBudgets_noise :
    (path.enlargeBudgets hP hPbad hPpres).noise = path.noise := rfl

@[simp] theorem enlargeBudgets_sample :
    (path.enlargeBudgets hP hPbad hPpres).sample = path.sample := rfl

@[simp] theorem enlargeBudgets_read :
    (path.enlargeBudgets hP hPbad hPpres).read = path.read := rfl

@[simp] theorem enlargeBudgets_commonTuple :
    (path.enlargeBudgets hP hPbad hPpres).commonTuple = path.commonTuple := rfl

@[simp] theorem enlargeBudgets_primes :
    (path.enlargeBudgets hP hPbad hPpres).primes = path.primes := rfl

@[simp] theorem enlargeBudgets_exponent :
    (path.enlargeBudgets hP hPbad hPpres).exponent = path.exponent := rfl

@[simp] theorem enlargeBudgets_prescribed :
    (path.enlargeBudgets hP hPbad hPpres).prescribed = path.prescribed := rfl

@[simp] theorem enlargeBudgets_origin :
    (path.enlargeBudgets hP hPbad hPpres).origin = path.origin := rfl

@[simp] theorem enlargeBudgets_Rbad :
    (path.enlargeBudgets hP hPbad hPpres).Rbad = path.Rbad := rfl

@[simp] theorem enlargeBudgets_lower :
    (path.enlargeBudgets hP hPbad hPpres).lower = path.lower := rfl

@[simp] theorem enlargeBudgets_width :
    (path.enlargeBudgets hP hPbad hPpres).width = path.width := rfl

@[simp] theorem enlargeBudgets_normalizedNoise :
    (path.enlargeBudgets hP hPbad hPpres).normalizedNoise = path.normalizedNoise := rfl

end Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type}
variable (Dmod : ℕ) (selected : A → Σ j : Fin m, Fin (n j))
variable (τ δslice : ℝ)

structure ActualFixedSpatialForecastSetup where
  hm : 0 < m
  hDmod : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod
  hselected : Function.Injective selected
  selectedNonempty : ∀ a, Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩)
  D : ℝ
  P : ℝ
  Pcap : ℝ
  pcap : ℝ
  Pscale : ℝ
  Pbad : ℝ
  Ppres : ℝ
  Pτ : ℝ
  PK : ℝ
  PF : ℝ
  Pκ : ℝ
  κ : ℝ
  hD : AllocatedComparisonDimensions (G := G) B Empty
    (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D
  hP : 1 ≤ P
  hDP : D ≤ P
  haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D
  hdim : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ D
  hX : (Fintype.card X : ℝ) ≤ P
  hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P
  hPcap : 1 ≤ Pcap
  hpcap : 0 ≤ pcap
  hPcapp : Pcap ≤ Real.exp pcap
  hPscale : 0 ≤ Pscale
  hPbad : 0 ≤ Pbad
  hPpres : 0 ≤ Ppres
  hPτ : 0 ≤ Pτ
  hPK : 0 ≤ PK
  hPF : 0 ≤ PF
  hPκ : 0 ≤ Pκ
  hκ : 0 ≤ κ
  hκcap : κ ≤ Real.exp Pκ
  hτ : 0 < τ
  hτinv : τ⁻¹ ≤ Real.exp Pτ
  hδslice : 0 < δslice
  hδsliceInv : δslice⁻¹ ≤ Real.exp P
  hR1 : ∀ a, R (selected a).1 ≤ 1
  hσ1 : ∀ a, σ (selected a).1 ≤ 1
  hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
    S.value ^ ((selected a).1.val + 1)
  L : ℝ≥0
  hL : LipschitzWith L Real.smoothTransition
  hprimitiveCap : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Pcap
  hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
    Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)
  hRinv : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp Pscale
  hslots : ∀ a, ((layerIntegerPrincipalSlots (G := G) B
    (selected a).1 (selected a).2).card : ℝ) ≤ Pscale
  hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    4 ≤ Fintype.card (B a.val)
  forward : Fin m → ℝ≥0
  hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖
  hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF
  K : ℝ≥0
  hK : ∀ j, (R j)⁻¹ ≤ K
  hKBound : (K : ℝ) ≤ Real.exp PK
  radius : ℝ≥0
  hr3 : (3 : ℝ) ≤ radius
  hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius
  inverse : Fin m → ℝ
  hinverse : ∀ j, 0 ≤ inverse j
  hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖
  hbudget : ∀ j, inverse j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (radius : ℝ) * R j)) ≤ 1 / 4
  hexhaustive : ∀ a, allocatedShortAxis (I := I) U b S.value a → ∃ i,
    (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a

namespace ActualFixedSpatialForecastSetup
variable {B U b S Dmod selected τ δslice}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)

end ActualFixedSpatialForecastSetup
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def physicalPolynomial
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    ∀ j, VectorPolynomial X ℝ (J j → ℝ) :=
  fun j => subtractConstant (path.center j).val (originalpoly j)

omit [Fintype Tsp] in

theorem physicalPolynomial_mem
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) :
    ∀ j d, coefficients (path.physicalPolynomial originalpoly j) d ∈ U j :=
  fun j => coefficients_subtractConstant_mem (U j) (path.center j) (originalpoly j) (hmem j)

variable {A : Type} [Fintype A]

noncomputable def target
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : integerBox physicalN) : ℂ := by
  letI := path.primeNeZero
  let N := ∏ p : path.primes, p.val ^ path.exponent p.val
  letI : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let density := fixedSpatialKernelOriginalForecastDensity B U b S
    spatialEquiv Wsp Lsp path.normalizedNoise path.detFalse path.detTrue
    hBactive path.lower path.width path.sample
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    path.base path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : path.primes => p.val)
    (fun p : path.primes => path.exponent p.val) (fun p : path.primes => path.prescribed p.val)
    (primePower_crt_coprime (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val)
      (fun p => path.prime p.val p.property) Subtype.val_injective) path.origin
  exact (κ : ℂ) * forecastDensityPhysicalTarget B U b S density selected path.sample
    path.commonTuple (fun _ => pRat)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    path.base physicalN τ o hb bW (path.physicalPolynomial originalpoly)
    (path.physicalPolynomial_mem originalpoly hmem) u.val

end ActualFixedSpatialForecastPath

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

section CenteredRead
variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
variable {I E : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]

theorem allocatedCenteredFramedRead_bad_depth_eq
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (primes : Finset ℕ) [∀ p : primes, NeZero p.val] (depth : ℕ → ℕ) (C : ℝ)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = fun k => jointIntegerFrame (base, noise) k.1 k.2) (p : ℕ) :
    largestTestedBadDepth depth (allocatedActualPrimeBad inactive spatial kernel block primes C) p
      (allocatedReplaceReadNoise B noise f) =
    largestTestedBadDepth depth (allocatedActualPrimeBad inactive spatial kernel block primes C) p f := by
  have hframe : allocatedReadNoise f = integerBaseTranslation base + noise := by
    rw [hf]
    funext k
    rcases k with ⟨k,x⟩
    cases k <;> simp [jointIntegerFrame, integerBaseTranslation, baseArrayJoin]
  have hdepth (p : ℕ) : largestTestedBadDepth depth
      (allocatedActualPrimeBad inactive spatial kernel block primes C) p
        (allocatedReplaceReadNoise B noise f) =
      largestTestedBadDepth depth
        (allocatedActualPrimeBad inactive spatial kernel block primes C) p f := by
    unfold largestTestedBadDepth
    apply congrArg (fun t : Finset ℕ => t.sup id)
    apply Finset.filter_congr
    intro d _
    exact (allocatedReplaceReadNoise_primeBad B base noise f hframe
      inactive spatial kernel block primes C p d).to_iff
  exact hdepth p

theorem allocatedCenteredFramedRead_bad_product_eq
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (primes : Finset ℕ) [∀ p : primes, NeZero p.val] (depth : ℕ → ℕ) (C : ℝ)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = fun k => jointIntegerFrame (base, noise) k.1 k.2) :
    (∏ p : primes, p.val ^ allocatedCongruenceBadDepth inactive noise
      (allocatedReadDeck (allocatedReplaceReadNoise B noise f))
      (fun j a => allocatedReadProjection (allocatedReplaceReadNoise B noise f) ⟨j,a.val⟩)
      spatial kernel block primes depth C p.val) =
    ∏ p ∈ primes, p ^ largestTestedBadDepth depth
      (allocatedActualPrimeBad inactive spatial kernel block primes C) p f := by
  have hdepth := allocatedCenteredFramedRead_bad_depth_eq B inactive spatial kernel block
    primes depth C base noise f hf
  calc
    _ = ∏ p : primes, p.val ^ largestTestedBadDepth depth
        (allocatedActualPrimeBad inactive spatial kernel block primes C) p.val f := by
      apply Finset.prod_congr rfl
      intro p _
      apply congrArg (fun d : ℕ => p.val ^ d)
      exact (allocatedActualPrimeBad_depth (B := B) (G := G) (X := X) (E := E)
        inactive spatial kernel block primes C depth p.val
        (allocatedReplaceReadNoise B noise f)).symm.trans (hdepth p.val)
    _ = _ := Finset.prod_coe_sort primes (fun p => p ^ largestTestedBadDepth depth
      (allocatedActualPrimeBad inactive spatial kernel block primes C) p f)
end CenteredRead

section Path
variable {m : ℕ} {G : Type} [Fintype G]
variable {I J Eout : Fin m → Type} [∀ j, Fintype (I j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (Eout j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
local notation "inactive" => allocatedShortAxis (I := I) U b S.value

noncomputable def preparedCenteredActualForecastPath
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin Lrank ↪ B ⟨j,a.val⟩)
    {Tsp : Type} [Fintype Tsp] (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
    (Wsp Lsp : ℝ) (physicalN : X → ℕ) (τ δslice Pdim Pdet Pbad Ppres : ℝ)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (center : ∀ j, U j)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      center base noise sample f)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime)
    (exponent prescribed : ℕ → ℕ)
    (origin : ∀ p : primes, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ exponent p.val))
    (Rbad : ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth exponent
        (allocatedActualPrimeBad inactive spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p f) ≤ Rbad)
    (hRbad : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ p : primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬inactive a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    {H κ0 κ1 : ℝ} (hH : H ∈ Set.Icc 0 1) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1)
    (hi0 : κ0⁻¹ ≤ Real.exp Pdet) (hi1 : κ1⁻¹ ≤ Real.exp Pdet)
    (hentry : ∀ i j, |fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fun k : Option G × X => (noise (Option.map Sum.inl k.1,k.2) : ℝ) /
        trimmedSpatialWidths Wsp τ physicalN k) false i j| ≤ H)
    (hdet0 : κ0 ≤ |(fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fun k : Option G × X => (noise (Option.map Sum.inl k.1,k.2) : ℝ) /
        trimmedSpatialWidths Wsp τ physicalN k) false).det|)
    (hdet1 : κ1 ≤ |(fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fun k : Option G × X => (noise (Option.map Sum.inl k.1,k.2) : ℝ) /
        trimmedSpatialWidths Wsp τ physicalN k) true).det|) :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ Dmod spatial kernel block
      spatialEquiv Wsp Lsp physicalN τ δslice (Pdet + Pdim ^ 2 + Pdim) Pbad Ppres := by
  letI := actualForecastPrimeNeZero primes hprime
  let z : Option G × X → ℝ := fun k =>
    (noise (Option.map Sum.inl k.1,k.2) : ℝ) / trimmedSpatialWidths Wsp τ physicalN k
  have h0 : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp z false).det ≠ 0 :=
    abs_pos.mp (hκ0.trans_le hdet0)
  have h1 : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp z true).det ≠ 0 :=
    abs_pos.mp (hκ1.trans_le hdet1)
  have hinverses :
      inverseJacobian (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp z true h1) ≤
        Real.exp (Pdet + Pdim ^ 2 + Pdim) ∧
      ‖(fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp z false h0).symm.toContinuousLinearMap‖ ≤
        Real.exp (Pdet + Pdim ^ 2 + Pdim) := by
    obtain ⟨_, _, h⟩ := preparedCenteredForecast_cramer_bounds
      spatialEquiv Wsp Lsp z hPdim hX hH hκ0 hκ1 hi0 hi1 hentry hdet0 hdet1
    exact h
  refine {
    base := base
    noise := noise
    sample := sample
    hs := fun j => (hrecovered.2.2.1 j).2
    read := allocatedReplaceReadNoise B noise f
    readNoise := rfl
    readProjection := hrecovered.2.2.2.2
    center := center
    commonTuple := commonTuple
    primes := primes
    prime := hprime
    exponent := exponent
    prescribed := prescribed
    origin := origin
    Rbad := Rbad
    hbad := ?_
    RbadBound := hRbad
    presBound := hpres
    lower := lower
    width := width
    hwidth := hwidth
    hlower := hlower
    hcontained := hcontained
    detFalse := h0
    detTrue := h1
    hjac := hinverses.1
    hinverse := hinverses.2 }
  exact (allocatedCenteredFramedRead_bad_product_eq B inactive spatial kernel block
    primes exponent (modularForecastRankConstant m Dmod : ℝ) base noise f hrecovered.1).le.trans hgood

noncomputable def preparedCenteredSupportedActualForecastPath
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (physicalN : X → ℕ) (τ ξ δslice Pdim Pdet Pbad Ppres : ℝ)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (center : ∀ j, U j)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      center base noise sample f)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime)
    (exponent prescribed : ℕ → ℕ)
    (origin : ∀ p : primes, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ exponent p.val))
    (Rbad : ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth exponent
        (allocatedActualPrimeBad inactive spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p f) ≤ Rbad)
    (hRbad : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ p : primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬inactive a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < physicalN x)
    (hnoise : noise ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0))
        τ ξ physicalN) 1)
    {κ : ℝ} (hκ : 0 < κ) (hκinv : κ⁻¹ ≤ Real.exp Pdet)
    (hdet : ∀ t : Fin 2, κ ≤ |Matrix.det (fun i j : X =>
      spatialMatrixNormalizedEntries e
        (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0))
          τ ξ physicalN) noise (t,j,i))|) :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ Dmod spatial kernel block
      (spatialTwoBlockEquiv e) (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      S.value physicalN τ δslice
      (Pdim * (Pdim + 1) + Pdet + Pdim ^ 2 + Pdim) Pbad Ppres := by
  let W : ℝ := allocatedPhysicalRootBudget B U b S (fun _ => 0)
  let scale : ℝ := (S.value : ℝ) / (1 + W)
  have hW : 0 ≤ W := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hscale : 0 < scale := div_pos hS (by positivity)
  have hinv : scale⁻¹ ≤ Real.exp (Pdim + 1) := by
    rw [show scale⁻¹ = (1 + W) / S.value by simp [scale]]
    exact (allocatedPhysicalRootBudget_zero_ratio B U b S hPdim hvars).trans
      (allocatedPrimitiveRootRatio_bounds hPdim).2.2
  have hscaled := preparedCenteredForecast_scaled_det_reciprocal
    (Fintype.card X) hscale hκ (by linarith only [hPdim]) hX hinv hκinv
  apply preparedCenteredActualForecastPath B U b S hR hσ hb o poly hm Dmod spatial kernel block
    (spatialTwoBlockEquiv e) W S.value physicalN τ δslice Pdim
    (Pdim * (Pdim + 1) + Pdet) Pbad Ppres base noise center sample f hrecovered
    commonTuple primes hprime exponent prescribed origin Rbad hgood hRbad hpres
    lower width hwidth hlower hcontained hPdim hX (H := 1)
    (κ0 := scale ^ Fintype.card X * κ) (κ1 := scale ^ Fintype.card X * κ)
    ⟨zero_le_one, le_rfl⟩ hscaled.1 hscaled.1 hscaled.2 hscaled.2
  · intro i j
    have hcard : (1 : ℝ) ≤ Fintype.card (LayerSamplerVariables G I n B) := by
      have hc : 0 < Fintype.card (LayerSamplerVariables G I n B) :=
        Fintype.card_pos_iff.mpr ⟨Sum.inl (e (0,i))⟩
      exact_mod_cast hc
    have hSle : (S.value : ℝ) ≤ W := by
      dsimp [W]
      rw [allocatedPhysicalRootBudget_zero]
      exact (one_mul (S.value : ℝ)).symm.le.trans
        (mul_le_mul_of_nonneg_right hcard hS.le)
    have hscale1 : scale ≤ 1 :=
      (div_le_one (show 0 < 1 + W by positivity)).mpr (by linarith only [hSle])
    exact preparedCenteredForecast_spatialBlock_entry_le_one e physicalN noise hnoise
      hW hτ hξ hN ⟨hscale.le,hscale1⟩ false i j
  · rw [preparedCenteredForecast_spatialBlock_abs_det e W S.value τ ξ physicalN
      noise false hscale.le]
    exact mul_le_mul_of_nonneg_left (hdet 0) (pow_nonneg hscale.le _)
  · rw [preparedCenteredForecast_spatialBlock_abs_det e W S.value τ ξ physicalN
      noise true hscale.le]
    exact mul_le_mul_of_nonneg_left (hdet 1) (pow_nonneg hscale.le _)

noncomputable def preparedCenteredGoodActualForecastPath
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (physicalN : X → ℕ) (τ ξ δslice Pdim Pdet Ppres gainLog Qstride : ℝ)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (center : ∀ j, U j)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      center base noise sample f)
    (commonTuple : G → IntegerScalarCubeBox Empty S.value)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime)
    (exponent prescribed : ℕ → ℕ)
    (origin : ∀ p : primes, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ exponent p.val))
    (stride : X → ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth exponent
        (allocatedActualPrimeBad inactive spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p f) ≤ ((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
      quantitativeBadPrimeRadius (gainLog + 8))))
    (hpres : ((∏ p : primes, p.val ^ prescribed p.val : ℕ) : ℝ) ≤ Real.exp Ppres)
    (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬inactive a},
      B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    (hwidth : ∀ a p, δslice ≤ width a p) (hlower : ∀ a p, 0 ≤ lower a p)
    (hcontained : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hτ : 0 < τ) (hξ : 0 < ξ) (hN : ∀ x, 0 < physicalN x)
    (hnoise : noise ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0))
        τ ξ physicalN) 1)
    (hnX : 0 < Fintype.card X)
    (hgainLog : 0 ≤ gainLog) (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hκinv : (spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog))⁻¹ ≤
      Real.exp Pdet)
    (hdet : ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 < |Matrix.det (fun i j : X =>
      spatialMatrixNormalizedEntries e
        (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0))
          τ ξ physicalN) noise (t,j,i))|) :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ Dmod spatial kernel block
      (spatialTwoBlockEquiv e) (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      S.value physicalN τ δslice
      (Pdim * (Pdim + 1) + (Pdet + 2) + Pdim ^ 2 + Pdim)
      (2 * Fintype.card X * Qstride +
        (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11) Ppres := by
  have hκ : 0 < spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) :=
    spatialMatrixBlockThreshold_pos hnX (jointSpatialError_pos gainLog)
  have hinv : (spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2)⁻¹ ≤
      Real.exp (Pdet + 2) := by
    rw [inv_div]
    calc
      _ = (spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog))⁻¹ * 2 := by ring
      _ ≤ Real.exp Pdet * Real.exp 2 :=
        mul_le_mul hκinv (by linarith [Real.add_one_le_exp (2 : ℝ)]) (by norm_num)
          (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  exact preparedCenteredSupportedActualForecastPath B U b S hR hσ hb o poly hm Dmod
    spatial kernel block e physicalN τ ξ δslice Pdim (Pdet + 2)
    (2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11)
    Ppres base noise center sample f hrecovered commonTuple primes hprime exponent prescribed origin
    ((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
      quantitativeBadPrimeRadius (gainLog + 8))) hgood
    (preparedCenteredForecast_badRadius_bound m stride hgainLog hstride)
    hpres lower width hwidth hlower hcontained hPdim hX hvars hτ hξ hN hnoise
    (half_pos hκ) hinv (fun t => (hdet t).le)
end Path
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j ex, coefficients (poly j) ex ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost : ℝ}
  (Dmod : ℕ)
  {Lrank : ℕ}
  (spatial : Fin Lrank ↪ G)
  (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
  (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
  (e : Fin 2 × X ↪ G)
  (Pdim gainLog Qstride : ℝ)
  (primes : Finset ℕ)
  (hprime : ∀ p ∈ primes, p.Prime)
  (depth : ℕ → ℕ)
  (hPdim : 0 ≤ Pdim)
  (hX : (Fintype.card X : ℝ) ≤ Pdim)
  (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
  (hnX : 0 < Fintype.card X)
  (hgainLog : 0 ≤ gainLog)
  (hgainDim : gainLog ≤ Pdim)
  (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)

variable {Selected : Type}
    {selected : Selected → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := E)
      B U b S Dmod selected τ δslice)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ setup.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ setup.Pbad)

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedForecastSourceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type}
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)} {τ δslice : ℝ}

namespace ActualFixedSpatialForecastSetup

noncomputable def enlargeP
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)
    {P' : ℝ} (hP : s.P ≤ P') :
    ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice :=
  { s with
    P := P'
    hP := s.hP.trans hP
    hDP := s.hDP.trans hP
    hX := s.hX.trans hP
    hblocks := s.hblocks.trans hP
    hδsliceInv := s.hδsliceInv.trans (Real.exp_le_exp.mpr hP) }

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)
variable {P' : ℝ} (hP : s.P ≤ P')

@[simp] theorem enlargeP_P : (s.enlargeP hP).P = P' := rfl
@[simp] theorem enlargeP_D : (s.enlargeP hP).D = s.D := rfl
@[simp] theorem enlargeP_κ : (s.enlargeP hP).κ = s.κ := rfl
@[simp] theorem enlargeP_Pbad : (s.enlargeP hP).Pbad = s.Pbad := rfl
@[simp] theorem enlargeP_Ppres : (s.enlargeP hP).Ppres = s.Ppres := rfl

noncomputable def withSliceWidth
    (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δslice)
    {δ' : ℝ} (hδ' : 0 < δ') (hδinv : δ'⁻¹ ≤ Real.exp s.P) :
    ActualFixedSpatialForecastSetup (X := X) (Eout := Eout) B U b S Dmod selected τ δ' :=
  { s with
    hδslice := hδ'
    hδsliceInv := hδinv }

variable {δ' : ℝ} (hδ' : 0 < δ') (hδinv : δ'⁻¹ ≤ Real.exp s.P)

@[simp] theorem withSliceWidth_P : (s.withSliceWidth hδ' hδinv).P = s.P := rfl
@[simp] theorem withSliceWidth_κ : (s.withSliceWidth hδ' hδinv).κ = s.κ := rfl
@[simp] theorem withSliceWidth_Pbad : (s.withSliceWidth hδ' hδinv).Pbad = s.Pbad := rfl
@[simp] theorem withSliceWidth_Ppres : (s.withSliceWidth hδ' hδinv).Ppres = s.Ppres := rfl

end ActualFixedSpatialForecastSetup

variable [DecidableEq X]
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type}
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

noncomputable def enlargeP
    (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
    {P' : ℝ} (hP : P ≤ P') :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P' Pbad Ppres :=
  { path with
    hjac := path.hjac.trans (Real.exp_le_exp.mpr hP)
    hinverse := path.hinverse.trans (Real.exp_le_exp.mpr hP) }

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable {P' : ℝ} (hP : P ≤ P')

@[simp] theorem enlargeP_base : (path.enlargeP hP).base = path.base := rfl
@[simp] theorem enlargeP_noise : (path.enlargeP hP).noise = path.noise := rfl
@[simp] theorem enlargeP_sample : (path.enlargeP hP).sample = path.sample := rfl
@[simp] theorem enlargeP_read : (path.enlargeP hP).read = path.read := rfl
@[simp] theorem enlargeP_center : (path.enlargeP hP).center = path.center := rfl
@[simp] theorem enlargeP_commonTuple : (path.enlargeP hP).commonTuple = path.commonTuple := rfl
@[simp] theorem enlargeP_primes : (path.enlargeP hP).primes = path.primes := rfl
@[simp] theorem enlargeP_exponent : (path.enlargeP hP).exponent = path.exponent := rfl
@[simp] theorem enlargeP_prescribed : (path.enlargeP hP).prescribed = path.prescribed := rfl
@[simp] theorem enlargeP_origin : (path.enlargeP hP).origin = path.origin := rfl
@[simp] theorem enlargeP_lower : (path.enlargeP hP).lower = path.lower := rfl
@[simp] theorem enlargeP_width : (path.enlargeP hP).width = path.width := rfl

@[simp] theorem target_enlargeP [Fintype A] [Fintype Tsp]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ) :
    (path.enlargeP hP).target selected hBactive o bW hb originalpoly hmem κ =
      path.target selected hBactive o bW hb originalpoly hmem κ := rfl

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

structure ActualFixedSpatialSlicedForecastPath where
  path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
    Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres
  step : ℕ
  step_pos : 0 < step
  kernelLength : G → ℕ
  kernelStart : G → ℤ
  kernelLength_two : ∀ g, 2 ≤ kernelLength g
  kernelInside : ∀ g (t : Fin (kernelLength g)),
    0 ≤ kernelStart g + (step : ℤ) * t.val ∧
      kernelStart g + (step : ℤ) * t.val < S.value
  principalLength : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ
  principalStep : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ
  principalStart : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ
  principalLength_pos : ∀ j, 0 < principalLength j
  principalInside : ∀ j (t : Fin (principalLength j)),
    0 ≤ principalStart j + (principalStep j : ℤ) * t.val ∧
      principalStart j + (principalStep j : ℤ) * t.val < allocatedPrincipalSides B U b S j
  principalStep_active : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), principalStep ⟨a.val,p⟩ = step
  prescribed_eq : ∀ p, path.prescribed p = padicValNat p step
  origin_eq : ∀ (p : path.primes) (v : LayerSamplerLongVariables
      (allocatedShortAxis (I := I) U b S.value) G B),
    path.origin p v = ((Sum.elim kernelStart
      (fun a => principalStart ⟨a.1.val,a.2⟩) v : ℤ) : ZMod (p.val ^ path.exponent p.val))
  lower_eq : ∀ a p, path.lower a p =
    (principalStart ⟨a.val,p⟩ : ℝ) / allocatedPrincipalSides B U b S ⟨a.val,p⟩
  width_eq : ∀ a p, path.width a p =
    (principalStep ⟨a.val,p⟩ : ℝ) * (principalLength ⟨a.val,p⟩ - 1 : ℕ) /
      allocatedPrincipalSides B U b S ⟨a.val,p⟩

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def kernelLower (g : G) : ℝ := (slice.kernelStart g : ℝ) / S.value
noncomputable def kernelWidth (g : G) : ℝ :=
  (slice.step : ℝ) * (slice.kernelLength g - 1 : ℕ) / S.value

omit [Fintype Tsp] in
theorem kernelWidth_pos (g : G) : 0 < slice.kernelWidth g := by
  have hstep : (0 : ℝ) < slice.step := Nat.cast_pos.mpr slice.step_pos
  have hlength : (0 : ℝ) < (slice.kernelLength g - 1 : ℕ) :=
    Nat.cast_pos.mpr (by have := slice.kernelLength_two g; omega)
  exact div_pos (mul_pos hstep hlength) (Nat.cast_pos.mpr S.positive)

omit [Fintype Tsp] in
theorem kernelWidth_ne_zero (g : G) : slice.kernelWidth g ≠ 0 :=
  (slice.kernelWidth_pos g).ne'

noncomputable def principalLaw : FiniteProbabilityWeights
    (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)) :=
  principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S)
    slice.principalLength slice.principalStep slice.principalStart slice.principalInside
    slice.principalLength_pos

theorem det_ne_zero_change_decidable {Y : Type} [Fintype Y]
    (d₀ d₁ : DecidableEq Y) (A : Matrix Y Y ℝ) :
    (letI := d₀; A.det ≠ 0) → (letI := d₁; A.det ≠ 0) := by
  cases Subsingleton.elim d₀ d₁
  exact id

noncomputable def density
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) :
    (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ)) → ℝ := by
  have h0 := det_ne_zero_change_decidable (inferInstance : DecidableEq X) (Classical.decEq X)
    (fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise false) slice.path.detFalse
  have h1 := det_ne_zero_change_decidable (inferInstance : DecidableEq X) (Classical.decEq X)
    (fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise true) slice.path.detTrue
  exact fixedSpatialKernelSliceOriginalForecastDensity
    (m := m) (G := G) (X := X) (T := Tsp) (I := I) (n := n) (J := J)
    B U b S spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth
    h0 h1 slice.kernelWidth_ne_zero hBactive slice.path.lower slice.path.width slice.path.sample

variable {A : Type} [Fintype A]

noncomputable def target
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ)
    (u : integerBox physicalN) : ℂ := by
  let : ∀ p : slice.path.primes, NeZero p.val := slice.path.primeNeZero
  let N := ∏ p : slice.path.primes, p.val ^ slice.path.exponent p.val
  let : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr
    (fun p _ => pow_ne_zero _ (NeZero.ne p.val))⟩
  let poly := allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
    slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
    (fun j a => allocatedReadProjection slice.path.read ⟨j,a.val⟩)
  let pRat := crtPolynomialInputLaw (fun p : slice.path.primes => p.val)
    (fun p : slice.path.primes => slice.path.exponent p.val)
    (fun p : slice.path.primes => slice.path.prescribed p.val)
    (primePower_crt_coprime (fun p : slice.path.primes => p.val)
      (fun p : slice.path.primes => slice.path.exponent p.val)
      (fun p => slice.path.prime p.val p.property) Subtype.val_injective) slice.path.origin
  exact (κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density hBactive) selected slice.path.sample slice.path.commonTuple (fun _ => pRat)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW (slice.path.physicalPolynomial originalpoly)
    (slice.path.physicalPolynomial_mem originalpoly hmem) u.val

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type}
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)} {τ δslice : ℝ}

variable [DecidableEq X]
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type}
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

noncomputable def weakenSliceWidth
    (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
    {δ' : ℝ} (hδ : δ' ≤ δslice) :
    ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δ' P Pbad Ppres :=
  { path with hwidth := fun a p => hδ.trans (path.hwidth a p) }

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable {δ' : ℝ} (hδ : δ' ≤ δslice)

@[simp] theorem weakenSliceWidth_lower : (path.weakenSliceWidth hδ).lower = path.lower := rfl
@[simp] theorem weakenSliceWidth_width : (path.weakenSliceWidth hδ).width = path.width := rfl

@[simp] theorem target_weakenSliceWidth [Fintype A] [Fintype Tsp]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ) :
    (path.weakenSliceWidth hδ).target selected hBactive o bW hb originalpoly hmem κ =
      path.target selected hBactive o bW hb originalpoly hmem κ := rfl

end ActualFixedSpatialForecastPath

namespace ActualFixedSpatialSlicedForecastPath

noncomputable def enlargeP
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
    {P' : ℝ} (hP : P ≤ P') :
    ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P' Pbad Ppres :=
  { slice with path := slice.path.enlargeP hP }

noncomputable def weakenSliceWidth
    (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
    {δ' : ℝ} (hδ : δ' ≤ δslice) :
    ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
      Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δ' P Pbad Ppres :=
  { slice with path := slice.path.weakenSliceWidth hδ }

variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)
variable {P' δ' : ℝ} (hP : P ≤ P') (hδ : δ' ≤ δslice)

@[simp] theorem enlargeP_path : (slice.enlargeP hP).path = slice.path.enlargeP hP := rfl
@[simp] theorem weakenSliceWidth_path :
    (slice.weakenSliceWidth hδ).path = slice.path.weakenSliceWidth hδ := rfl
@[simp] theorem enlargeP_kernelLower : (slice.enlargeP hP).kernelLower = slice.kernelLower := rfl
@[simp] theorem enlargeP_kernelWidth : (slice.enlargeP hP).kernelWidth = slice.kernelWidth := rfl
@[simp] theorem weakenSliceWidth_kernelLower :
    (slice.weakenSliceWidth hδ).kernelLower = slice.kernelLower := rfl
@[simp] theorem weakenSliceWidth_kernelWidth :
    (slice.weakenSliceWidth hδ).kernelWidth = slice.kernelWidth := rfl
@[simp] theorem enlargeP_principalLaw : (slice.enlargeP hP).principalLaw = slice.principalLaw := rfl
@[simp] theorem weakenSliceWidth_principalLaw :
    (slice.weakenSliceWidth hδ).principalLaw = slice.principalLaw := rfl

@[simp] theorem density_enlargeP [Fintype Tsp]
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) :
    (slice.enlargeP hP).density hBactive = slice.density hBactive := rfl

@[simp] theorem density_weakenSliceWidth [Fintype Tsp]
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) :
    (slice.weakenSliceWidth hδ).density hBactive = slice.density hBactive := rfl

@[simp] theorem target_enlargeP [Fintype A] [Fintype Tsp]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ) :
    (slice.enlargeP hP).target selected hBactive o bW hb originalpoly hmem κ =
      slice.target selected hBactive o bW hb originalpoly hmem κ := rfl

@[simp] theorem target_weakenSliceWidth [Fintype A] [Fintype Tsp]
    (selected : A → Σ j : Fin m, Fin (n j))
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j) (κ : ℝ) :
    (slice.weakenSliceWidth hδ).target selected hBactive o bW hb originalpoly hmem κ =
      slice.target selected hBactive o bW hb originalpoly hmem κ := rfl

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem principalSupport (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    integerProgressionSupport (slice.principalStart j) (slice.principalStep j : ℤ)
      (slice.principalLength j) ⊆ Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ) :=
  integerProgressionSupport_subset_of_fin _ _ _ _ (slice.principalInside j)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

end


