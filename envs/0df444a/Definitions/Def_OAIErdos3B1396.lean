-- Prove2me | Definitions.Def_OAIErdos3B1396
-- name    : OAIErdos3B1396
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-16T05:52:17.241473+00:00
-- url     : https://prove2.me/theorems/2a3dcced-6633-47ee-aca3-aad77f1ecb5e
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1397 of 1403
-- statement:
--   Definitions bundle 1397 of 1403 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1395`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1397 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.affineAmbientMassLog_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedClippedPrefactorSiteMask_bound`, `OAI.Erdos3.VectorPolynomial.allocatedClippedPrefactorSiteMask_coefficient_sum`, `OAI.Erdos3.VectorPolynomial.allocatedFullGridChartModel_measurable`, `OAI.Erdos3.VectorPolynomial.allocatedProductFullGridProfile_eq_model`, `OAI.Erdos3.VectorPolynomial.allocatedProductFullGridProfile_mixed`, `OAI.Erdos3.VectorPolynomial.allocatedProductFullGridProfile_prefactor_error`, `OAI.Erdos3.VectorPolynomial.allocatedProductFullGridProfile_zero`, `OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_norm`, `OAI.Erdos3.VectorPolynomial.generalDetectorCoefficientCost_single`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetectorResources_primitive_domination`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetector_ideal_site_bound`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1377
import Definitions.Def_OAIErdos3B1386
import Definitions.Def_OAIErdos3B1387
import Definitions.Def_OAIErdos3B1398

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductIdealCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical Matrix

variable {α : Type*} [DecidableEq α]

namespace VectorPolynomial

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable (rowSets : Fin m → Finset (Finset α))
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (d : ℕ)


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedProductSiteCutoff_norm (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y‖ ≤ 1 := by
  rw [allocatedProductSiteCutoff, norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro s _
  exact allocatedBufferedSiteChartFactor_norm_le B U b S o hb bW d r hr (fun _ => 1)
    (fun _ => by simp) _

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
variable (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
variable (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ))
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α]
variable (rowSets : Fin m → Finset (Finset α))

variable [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFullGridChartModelMeasurable
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

theorem allocatedProductFullGridProfile_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e (chart z) =
      allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) *
        allocatedFullGridSiteApproximation B U b S rowSets e
          (allocatedFullGridRowsOfMixed B U b S rowSets z.1) := by
  rw [allocatedProductFullGridProfile,
    allocatedFullGridSiteProfile_mixed B U b S rowSets d hR hσ x hb o bW q y₀ hcell f e z hz]
  unfold allocatedProductFullGridPrefactor allocatedFullGridSiteChartPrefactor
  exact (mul_assoc _ _ _).symm

theorem allocatedProductFullGridProfile_zero
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (y : EuclideanJetLayers U rowTypes) (hy : y ∉ chart '' region) :
    allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y = 0 := by
  rw [allocatedProductFullGridProfile, allocatedFullGridSiteProfile,
    allocatedComplexGridMultiplier_zero B U b S rowTypes hb o bW d _ y hy, zero_mul, mul_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

theorem allocatedProductFullGridProfile_eq_model
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) (y : EuclideanJetLayers U rowTypes) :
    allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y =
      allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f y *
        allocatedFullGridChartModel B U b S rowSets d hb o bW e y := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedProductFullGridProfile_mixed B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e z hz,
      allocatedFullGridChartModel_mixed B U b S rowSets d hb o bW e z hz]
  · rw [allocatedProductFullGridProfile_zero B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y hy,
      allocatedProductFullGridPrefactor_zero B U b S rowSets d r hr x hb o bW q y₀ f y hy, zero_mul]

theorem allocatedProductFullGridProfile_prefactor_error
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (F : EuclideanJetLayers U rowTypes → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (herr : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f y - F y‖ ≤ η)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductFullGridProfile B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y -
      F y * allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤ η * ∏ a, Cc a := by
  rw [allocatedProductFullGridProfile_eq_model B U b S rowSets d r hr x hb o bW q y₀ f hR hσ hcell e y,
    ← sub_mul, norm_mul]
  exact mul_le_mul (herr y) (allocatedFullGridChartModel_norm_le B U b S rowSets d hb o bW e he y)
    (norm_nonneg _) hη

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} →
  ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

theorem allocatedFullGridChartModel_measurable
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) :
    Measurable (allocatedFullGridChartModel B U b S rowSets d hb o bW e) := by
  let : ∀ a : gridAxes, Countable (CoefficientJetAxisRow rowTypes a.val) := by
    intro a
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · change Countable (rowTypes j → ℤ)
      infer_instance
  let : ∀ a : gridAxes, MeasurableSingletonClass (CoefficientJetAxisRow rowTypes a.val) := by
    intro a
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · change MeasurableSingletonClass (rowTypes j → ℤ)
      infer_instance
  exact allocatedComplexGridMultiplier_measurable B U b S rowTypes hb o bW d _
    (measurable_of_countable _)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductPrefactorMasks
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y₀
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

theorem allocatedClippedPrefactorSiteMask_bound
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue j) z ≤ C)
    (r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) :
    |allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period r| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period := by
  have hd := coefficientDeckSiteMask_bounds root dirs rows d period
    (fun j => (hperiod j).trans (allocatedWholeJetMatrix_kernel_range_le B U b S x y₀ rows j))
    (fun s => (r s).2)
  rw [allocatedClippedPrefactorSiteMask, abs_mul, abs_of_nonneg hd.1]
  exact mul_le_mul (allocatedKernelSiteMask_bound B U b S rowSets x q residue period hC hm _)
    hd.2 hd.1 (pow_nonneg (zero_le_one.trans hC) _)

theorem allocatedClippedPrefactorSiteMask_coefficient_sum
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {C A : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue j) z ≤ C)
    {K : Type*} [Fintype K] (c : K → ℂ) (hc : (∑ k, ‖c k‖) ≤ A) :
    (∑ r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period), ∑ k,
      ‖(allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period r : ℂ) * c k‖) ≤
      (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
        Fintype.card (Finset α) *
      (C ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * A := by
  apply maskedSiteExpansion_coefficient_sum _ c
    (mul_nonneg (pow_nonneg (zero_le_one.trans hC) _) (coefficientDeckPeriodCap_nonneg rowTypes E period)) _ hc
  intro r
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact allocatedClippedPrefactorSiteMask_bound B U b S rowSets x y₀ q d period hperiod hC hm r

variable (T : Fin m → ℝ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineAmbientPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

theorem affineAmbientMassLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineAmbientMassLog P := by unfold affineAmbientMassLog; positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorNativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem generalDetectorCoefficientCost_single (m dim : ℕ) (j : Fin m) :
    Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) ≤
      generalDetectorCoefficientCost m dim := by
  exact Finset.single_le_sum (f := fun j : Fin m =>
    Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem preparedModularGeneralDetectorResources_primitive_domination
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ)
    {P L : ℝ} (hP : 0 ≤ P) (hPL : P ≤ L) :
    let r := preparedModularGeneralDetectorResources K dim P L
    P ≤ r.v ∧ P ≤ r.Dg ∧ P ≤ r.Pnative ∧
    (generalDetectorCoefficientCost K.m dim : ℝ) ≤ r.Psample ∧
    r.Pmass ≤ r.Psample ∧ r.ambient ≤ r.Psample ∧ r.Pproj ≤ r.Psample ∧
    r.Psample ≤ r.Pside ∧ L ≤ r.Pside ∧
    ∀ j : Fin K.m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ) ≤
      Real.exp r.Psample := by
  intro r
  have hL := hP.trans hPL
  have h := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget K dim)).2 hP hPL).1
  have hv : P ≤ r.v := by change P ≤ P + 8; linarith
  have hD : P ≤ r.Dg := by
    have hrest : 0 ≤ (K.m : ℝ) * P + (layerTailDegree K.m + 1 : ℕ) +
        K.m + comparisonProfileBound + 8 := by positivity
    change P ≤ 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) + K.m + comparisonProfileBound + 8
    linarith only [hP, hrest]
  have hN : P ≤ r.Pnative := by
    change P ≤ r.Dg + r.gridlog + r.v + r.Fpref + 6 * P + r.Banalytic
    linarith only [hv, h.Dg.1, h.gridlog.1, h.Fpref.1, h.Banalytic.1, hP]
  have hpow : 0 ≤ (P + (K.m + dim + 2 : ℕ)) ^ (K.m + dim + 2) := by positivity
  have hcost0 : (0 : ℝ) ≤ generalDetectorCoefficientCost K.m dim := Nat.cast_nonneg _
  have hsample : r.Psample = r.Pmass + r.ambient + r.Pproj + 2 * P +
      generalDetectorCoefficientCost K.m dim + (P + (K.m + dim + 2 : ℕ)) ^ (K.m + dim + 2) + 8 := rfl
  have hcost : (generalDetectorCoefficientCost K.m dim : ℝ) ≤ r.Psample := by
    linarith only [hsample, h.Pmass.1, h.ambient.1, h.Pproj.1, hP, hpow]
  have hside : r.Pside = r.Psample + r.Pproj + r.Pmass + 2 * L := rfl
  refine ⟨hv, hD, hN, hcost, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hsample, h.ambient.1, h.Pproj.1, hP, hcost0, hpow]
  · linarith only [hsample, h.Pmass.1, h.Pproj.1, hP, hcost0, hpow]
  · linarith only [hsample, h.Pmass.1, h.ambient.1, hP, hcost0, hpow]
  · linarith only [hside, h.Pproj.1, h.Pmass.1, hL]
  · linarith only [hside, h.Psample.1, h.Pproj.1, h.Pmass.1, hL]
  · intro j
    exact (Nat.cast_le.mpr (generalDetectorCoefficientCost_single K.m dim j)).trans
      (hcost.trans (by linarith only [Real.add_one_le_exp r.Psample]))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem preparedModularGeneralDetector_ideal_site_bound
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) {P L : ℝ} (hP : 0 ≤ P)
    {outputs : ℕ} (hout : (outputs : ℝ) ≤ P) {sumlog : ℝ}
    (hsum : sumlog ∈ Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).sumlog) :
    idealSiteLogBudget outputs dim sumlog ∈
      Set.Icc 0 (preparedModularGeneralDetectorResources K dim P L).idealQ := by
  let r := preparedModularGeneralDetectorResources K dim P L
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ comparisonProfileBound :=
    (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)
  refine ⟨(idealSiteLogBudget_bounds outputs dim hsum.1).1, ?_⟩
  change idealSiteLogBudget outputs dim sumlog ≤
    (dim : ℝ) + P * r.sumlog + (P + comparisonProfileBound + (P + 1) * r.sumlog) + r.sumlog + 1
  unfold idealSiteLogBudget affineProfileLogBound
  have hs0 := hsum.1
  have hs1 := hsum.2
  gcongr

end Erdos3.VectorPolynomial

end

end OAI

end


