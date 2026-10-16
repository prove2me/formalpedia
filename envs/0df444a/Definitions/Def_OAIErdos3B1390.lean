-- Prove2me | Definitions.Def_OAIErdos3B1390
-- name    : OAIErdos3B1390
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T07:53:12.582828+00:00
-- url     : https://prove2.me/theorems/184f7213-4cda-4629-b0ec-92840d553c7e
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1391 of 1413
-- statement:
--   Definitions bundle 1391 of 1413 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1389`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1391 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.allocatedCoveredDeck_density_test`, `OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_raw_integral`, `OAI.Erdos3.VectorPolynomial.allocatedFrozenProfile_mixed_integral`, `OAI.Erdos3.VectorPolynomial.allocatedProductChartIdealApproximation_norm_le`, `OAI.Erdos3.VectorPolynomial.allocatedWholeMaskedCoveredProfile_join`, `OAI.Erdos3.uniform_complex_approximation_test`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1397

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedChartIdealModelBound
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem allocatedProductChartIdealApproximation_norm_le {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (hf : ∀ k s v, ‖f k s v‖ ≤ 1) (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
      ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
        ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k‖ := by
  unfold allocatedProductChartIdealApproximation
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro label _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul, norm_prod]
  apply (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)).trans_eq (mul_one _)
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro s _
  exact allocatedMaskedSiteChartFactor_norm B U b S o hb bW d r hr period (label s) (f k s) (hf k s) _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSlicedRowIdealSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "gridRef" => allocatedFrozenJetReference B U b S O
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "rawRef" => Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v rows

theorem allocatedFrozenProfile_mixed_integral
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f)
    (hf : Integrable f longRef)
    (φ : (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) → ℂ)
    (hφ : Measurable φ) {C : ℝ} (hbound : ∀ z, ‖φ z‖ ≤ C) :
    (∫ a, ∫ z, (f z : ℂ) * φ (allocatedMixedJetReconstruct B U b S x u v rows a z)
      ∂longRef ∂allocatedFrozenCoefficientSource B U b hR hσ S) =
    ∫ z, ((fg ((split z).1) * f ((split z).2) : ℝ) : ℂ) * φ z ∂rawRef := by
  let ψ := fun p : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O =>
    (f p.2 : ℂ) * φ ((split).symm p)
  have hψ : Measurable ψ :=
    (Complex.measurable_ofReal.comp (hfm.comp measurable_snd)).mul
      (hφ.comp (split).symm.measurable)
  have hint : Measurable (fun g => ∫ z, ψ (g, z) ∂longRef) :=
    hψ.stronglyMeasurable.integral_prod_right'.measurable
  have hfg := (allocatedGridJetDensity_probability_data B U b S O hR hσ x u v rows).1
  have hprod : Integrable (fun p : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O =>
      ((fg p.1 * f p.2 : ℝ) : ℂ) * φ ((split).symm p)) ((gridRef).prod longRef) :=
    (hfg.mul_prod hf).ofReal.mul_bdd (hφ.comp (split).symm.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound _))
  calc
    _ = ∫ g, (fg g : ℂ) * (∫ z, ψ (g, z) ∂longRef) ∂gridRef := by
      change (∫ a, (fun g => ∫ z, ψ (g, z) ∂longRef)
        (allocatedFrozenJetMap B U b S x u v rows a)
        ∂allocatedFrozenCoefficientSource B U b hR hσ S) = _
      rw [← integral_map (allocatedFrozenJetMap_measurable B U b S x u v rows).aemeasurable
        hint.aestronglyMeasurable, allocatedGridJetDensity_law B U b S O hR hσ x u v rows,
        realDensityMeasure_integral_complex gridRef fg
          (allocatedGridJetDensity_measurable B U b hR hσ S x u v rows)
          (fun z => (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows z).1)]
    _ = ∫ g, ∫ z, ((fg g * f z : ℝ) : ℂ) * φ ((split).symm (g, z)) ∂longRef ∂gridRef := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun g => by
        calc
          _ = ∫ z, (fg g : ℂ) * ψ (g, z) ∂longRef :=
            (integral_const_mul (fg g : ℂ) (fun z => ψ (g, z))).symm
          _ = _ := integral_congr_ae (Filter.Eventually.of_forall
            (fun z => by simp only [ψ, Complex.ofReal_mul, mul_assoc])))
    _ = ∫ p, ((fg p.1 * f p.2 : ℝ) : ℂ) * φ ((split).symm p) ∂(gridRef).prod longRef :=
      (integral_prod _ hprod).symm
    _ = _ := by
      have he := coefficientJetAxisSplit_measurePreserving O I n grid
      have hh := he.integral_comp (split).measurableEmbedding
        (fun p => ((fg p.1 * f p.2 : ℝ) : ℂ) * φ ((split).symm p))
      simpa only [allocatedFrozenJetReference, allocatedLongJetReference,
        MeasurableEquiv.symm_apply_apply] using hh.symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "mixedRef" => Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := Q) (n := n) d
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v₀ rows
local notation "fd" => coefficientDeckJetDensity (B := Q) root dirs rows d
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

omit [Fintype α] in
theorem allocatedCoveredDeck_density_test
    (F : EuclideanJetLayers U O → ℂ)
    (t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    (∫ r, F (chart (t, coefficientDeckJetMap root dirs rows d r)) ∂(deck).toMeasure) =
      ∫ r, (fd r : ℂ) * F (chart (t, r))
        ∂(PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure := by
  have he := coefficientDeckJetDensity_integral
    (K := LayerSamplerVariables G I n B) (O := O) (B := Q)
    root dirs rows d (fun r => F (chart (t, r)))
  convert he using 1
  apply congrArg (fun p : PMF (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d) =>
    ∫ r, F (chart (t, coefficientDeckJetMap root dirs rows d r)) ∂p.toMeasure)
  exact congrArg (fun i : Fintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d) =>
    @PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d) i _)
      (Subsingleton.elim _ _)

omit [Fintype α] in
theorem allocatedCoveredProfile_raw_integral
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f)
    (hf : Integrable f longRef)
    (F : EuclideanJetLayers U O → ℂ) (hF : Measurable F)
    {C : ℝ} (hbound : ∀ z, ‖F z‖ ≤ C) :
    (∫ a, ∫ z, (f z : ℂ) *
      allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d (fun p => F p.2) a z
      ∂longRef ∂allocatedFrozenCoefficientSource B U b hR hσ S) =
    ∫ z, (allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z : ℂ) *
      F (chart z) ∂raw := by
  let φ := fun t : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ) =>
    ∫ r, F (chart (t, coefficientDeckJetMap root dirs rows d r)) ∂(deck).toMeasure
  have hchart : Measurable chart :=
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := Q) (n := n) U o d)
  have hφ : Measurable φ := finitePMF_integral_measurable deck _
    (fun r => hF.comp (hchart.comp (measurable_id.prodMk measurable_const)))
  have hφb : ∀ t, ‖φ t‖ ≤ C := fun t => finitePMF_integral_norm_le deck _ (fun r => hbound _)
  have hφeq (t) : φ t = ∫ r, (fd r : ℂ) * F (chart (t, r)) ∂(PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure := by
    exact allocatedCoveredDeck_density_test B U b S x u v₀ rows Q hb o bW d F t
  have hi := (allocatedGridlessWeightedKernel_mass_data B U b S x u v₀ rows (Q := Q) d fg f
    (allocatedGridJetDensity_probability_data B U b S O hR hσ x u v₀ rows).1 hf).1
  have hprod : Integrable (fun z : MixedCoveredJetSource I O Q n d =>
      (allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z : ℂ) *
        F (chart z)) raw :=
    hi.ofReal.mul_bdd (hF.comp hchart).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => hbound _))
  calc
    _ = ∫ t, ((fg ((split t).1) * f ((split t).2) : ℝ) : ℂ) * φ t ∂mixedRef :=
      allocatedFrozenProfile_mixed_integral B U b S O hR hσ x u v₀ rows f hfm hf φ hφ hφb
    _ = ∫ t, ∫ r,
        (allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f (t, r) : ℂ) *
          F (chart (t, r)) ∂(PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure ∂mixedRef := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      change ((fg ((split t).1) * f ((split t).2) : ℝ) : ℂ) * φ t = _
      rw [hφeq t]
      rw [← integral_const_mul (((fg ((split t).1) * f ((split t).2) : ℝ) : ℂ))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by
        simp only [allocatedGridlessWeightedKernel, Complex.ofReal_mul, mul_assoc])
    _ = _ := (integral_prod _ hprod).symm

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (v₀ : PrincipalAxisTuples (α := Fin 1) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n

variable (hR : ∀ j, 0 < R j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (v₀ : PrincipalAxisTuples (α := Fin 1) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)] [∀ j, DecidableEq (I j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin 1)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin 1)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable (hR : ∀ j, 0 < R j) (hrows : ∀ j t, t ∈ rowSets j)
variable (hB : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, 4 ≤ Fintype.card (B a.val))
variable (lower width : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedFiniteModelComparison
namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem uniform_complex_approximation_test {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : X → ℂ) (hf : Integrable f μ) (hg : Measurable g)
    {ε : ℝ} (he : ∀ x, ‖f x - g x‖ ≤ ε)
    (φ : X → ℂ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1) :
    Integrable g μ ∧
      ‖(∫ x, f x * φ x ∂μ) - ∫ x, g x * φ x ∂μ‖ ≤ ε := by
  have hd : Integrable (fun x => f x - g x) μ :=
    Integrable.of_bound (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable) ε
      (Filter.Eventually.of_forall he)
  have hgi : Integrable g μ :=
    (hf.sub hd).congr (Filter.Eventually.of_forall (fun x => sub_sub_cancel (f x) (g x)))
  refine ⟨hgi, ?_⟩
  have hfiφ := hf.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hgiφ := hgi.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  rw [← integral_sub hfiφ hgiφ]
  have hp (x) : ‖f x * φ x - g x * φ x‖ ≤ ε := by
    rw [← sub_mul, norm_mul]
    exact ((mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)).trans_eq (mul_one _)).trans (he x)
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (ae_of_all μ hp)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

omit [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] [Fintype α] in
theorem allocatedWholeMaskedCoveredProfile_join
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ) :
    allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
      (principalAxisJoin grid u v) q f =
    allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter
      (allocatedLongProfileDensity B U b S x rows q
        (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) q) f) := by
  simp only [allocatedWholeMaskedCoveredProfile, principalAxisRestrict_join_left,
    principalAxisRestrict_join_right]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)

local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))


variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U (fun _ : Fin m => Finset (Fin 1)) → ℂ)

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)

local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))


variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U (fun _ : Fin m => Finset (Fin 1)) → ℂ)

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)

local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))


variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : EuclideanJetLayers U (fun _ : Fin m => Finset (Fin 1)) → ℂ)

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)

local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))


variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (rowSets : Fin m → Finset (Finset (Fin 1))) (hrows : ∀ j t, t ∈ rowSets j)
variable (F : EuclideanJetLayers U (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j}) → ℂ)

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1))
  S.positive x (j.val + 1) id (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B (Fin 1) (fun _ => Finset (Fin 1)) P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)

local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))


variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (rowSets : Fin m → Finset (Finset (Fin 1))) (hrows : ∀ j t, t ∈ rowSets j)
variable (F : EuclideanJetLayers U (fun j : Fin m => {t : Finset (Fin 1) // t ∈ rowSets j}) → ℂ)

variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin 1) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := Fin 1) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

end OAI

end


