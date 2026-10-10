-- Prove2me | Definitions.Def_OAIErdos3B150
-- name    : OAIErdos3B150
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T23:57:29.89259+00:00
-- url     : https://prove2.me/theorems/f5643ba6-f5cb-42fc-ab4a-aef1c6090c21
-- title:
--   OpenAI Erdős-3 split, definitions bundle 151 of 177
-- statement:
--   Definitions bundle 151 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B149`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 151 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedActiveIntegerAxis`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.conjugate`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.conjugate_eval`, `OAI.Erdos3.VectorPolynomial.allocatedActiveIntegerGridScale`, `OAI.Erdos3.VectorPolynomial.allocatedActiveIntegerGridScale_pos`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedAmbientCutoff`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedTorusCutoff`, `OAI.Erdos3.VectorPolynomial.allocatedForecastAllAxisLiftCap`, `OAI.Erdos3.VectorPolynomial.allocatedForecastAllAxisLiftLip`, `OAI.Erdos3.VectorPolynomial.allocatedForecastAllAxisRowCap`, `OAI.Erdos3.VectorPolynomial.allocatedMaskedSiteChartFactor`, `OAI.Erdos3.VectorPolynomial.allocatedProductMaskedIdealSiteFactor`, `OAI.Erdos3.VectorPolynomial.exists_canonicalSlicedModelPrefactor_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedModularCanonicalDetector_grid_parameters`, `OAI.Erdos3.VectorPolynomial.exists_preparedModularCanonicalDetector_period_budget`, `OAI.Erdos3.VectorPolynomial.forecastIntegerAxisMerge`, `OAI.Erdos3.VectorPolynomial.forecastIntegerAxisMerge_active`, `OAI.Erdos3.VectorPolynomial.forecastIntegerAxisMerge_short`, `OAI.Erdos3.VectorPolynomial.forecastIntegerAxisSplit`, `OAI.Erdos3.VectorPolynomial.instFintypeAllocatedActiveIntegerAxis`, `OAI.Erdos3.VectorPolynomial.mixedCoveredSiteResidue`, `OAI.Erdos3.VectorPolynomial.normalizedTwist_eval_mem_twistedNativeSampleFunctions`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B170
import Definitions.Def_OAIErdos3B172

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCutoffMaskedIdeal
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

local notation "chart" => mixedCoveredJetChart U o b hb bW d

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

noncomputable def allocatedProductMaskedIdealSiteFactor {K : Type*}
    (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) (k : K) (s : Finset α)
    (w : MixedCoveredJetSource I (fun _ => Unit) E n d) : ℂ :=
  maskedSiteFactor
    (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
      fun j i => ((v.2 j () i).val : ZMod period))) label
    (fun k s v => allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (f k s) (chart v)) k s w

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

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
local notation "split" => coefficientJetAxisSplit rowTypes I n grid

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedMaskedChartProduct
namespace OAI

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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d quarter

noncomputable def mixedCoveredSiteResidue (w : MixedCoveredJetSource I single E n d) :
    (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period) :=
  (fun j i => ((w.1 j).2 i () : ZMod period), fun j i => ((w.2 j () i).val : ZMod period))

noncomputable def allocatedMaskedSiteChartFactor
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) : EuclideanJetLayers U single → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun w =>
    if mixedCoveredSiteResidue d period w = label then
      allocatedBufferedMixedSiteFactor B U b S r hr f (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())
    else 0)

end Erdos3.VectorPolynomial

end

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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedBufferedAmbientCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

variable (r : ℝ≥0) (hr : 0 < r)

noncomputable def allocatedBufferedAmbientCutoff (z : ambient → ℝ) : ℝ :=
  normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
    (allocatedFullAmbientSiteCoordinates (R := R) U b o z)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedNormalizedTorusCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ} (r : ℝ≥0) (hr : 0 < r)
local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J

noncomputable def allocatedBufferedTorusCutoff : (ambient → UnitAddCircle) → ℝ :=
  smallBoxTorusKernel (allocatedBufferedAmbientCutoff (R := R) U b o r hr)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

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
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)

variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

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
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)

variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTwistNativeMembership
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

namespace NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def conjugate (W : NormalizedPolynomialTwist X Y periodCap coverCap L) :
    NormalizedPolynomialTwist X Y periodCap coverCap L :=
  { W with
    mask := fun z => star (W.mask z)
    mask_bound := fun z => by simpa only [norm_star] using W.mask_bound z
    smooth := fun z => star (W.smooth z)
    smooth_bound := fun z => by simpa only [norm_star] using W.smooth_bound z
    smooth_lipschitz := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm, ← star_sub, norm_star] using W.smooth_lipschitz.dist_le_mul x y }

@[simp] theorem conjugate_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    W.conjugate.eval N poly u = star (W.eval N poly u) := by
  simp only [eval, conjugate, star_mul, mul_comm]
  rfl

end NormalizedPolynomialTwist

theorem normalizedTwist_eval_mem_twistedNativeSampleFunctions
    {X Ω : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) {budget : ℝ} (hbudget : 2 ≤ budget) :
    (fun t => W.eval N poly (sample t)) ∈ twistedNativeSampleFunctions w degree budget sample
      (fun (V : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) t =>
        V.eval N poly (sample t)) := by
  refine Or.inr ⟨W.conjugate, fun _ => 1, ⟨NativeSampleModel.constOne hbudget⟩, ?_⟩
  funext t
  simp only [NormalizedPolynomialTwist.conjugate_eval, star_star, mul_one]

end Erdos3.VectorPolynomial

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

noncomputable def allocatedForecastAllAxisRowCap {δ : ℝ} (hδ : 0 < δ)
    (a : LayerSamplerAxis I n) : ℝ≥0 :=
  allocatedFixedPathLiftRowCap (fun _ : LayerSamplerAxis I n => False)
    (unitProfilePrincipalLowerBound_pos B) hδ ⟨a, not_false⟩

noncomputable def allocatedForecastAllAxisLiftCap {δ : ℝ} (hδ : 0 < δ) : ℝ≥0 :=
  ∏ a, (allocatedForecastAllAxisRowCap B hδ a + 1)

noncomputable def allocatedForecastAllAxisLiftLip {δ : ℝ} (hδ : 0 < δ) : ℝ≥0 :=
  allocatedForecastAllAxisLiftCap B hδ *
    ∑ a, allocatedForecastAllAxisRowCap B hδ a * (2 * allocatedForecastAllAxisRowCap B hδ a)

variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable {δ : ℝ} (hδ : 0 < δ)

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

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastIntegerAxisSplit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

def AllocatedActiveIntegerAxis (L : ℕ) :=
  {a : Σ j : Fin m, Fin (n j) // L ^ (a.1.val + 1) < basisAxisScale (basis a.1) a.2}

noncomputable instance (L : ℕ) : Fintype (AllocatedActiveIntegerAxis U basis L) :=
  inferInstanceAs (Fintype {a : Σ j : Fin m, Fin (n j) //
    L ^ (a.1.val + 1) < basisAxisScale (basis a.1) a.2})

noncomputable def allocatedActiveIntegerGridScale (R : Fin m → ℝ) (L : ℕ)
    (a : AllocatedActiveIntegerAxis U basis L) : ℝ :=
  R a.val.1 * (basisAxisScale (basis a.val.1) a.val.2 : ℝ)

theorem allocatedActiveIntegerGridScale_pos {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) (a : AllocatedActiveIntegerAxis U basis L) :
    0 < allocatedActiveIntegerGridScale U basis R L a :=
  mul_pos (hR a.val.1) (Nat.cast_pos.mpr (basisAxisScale_pos _ _))

variable {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

noncomputable def forecastIntegerAxisMerge
    (short : AllocatedShortIntegerAxis U basis L → ℤ)
    (active : AllocatedActiveIntegerAxis U basis L → ℤ)
    (a : Σ j : Fin m, Fin (n j)) : ℤ :=
  if h : basisAxisScale (basis a.1) a.2 ≤ L ^ (a.1.val + 1)
    then short ⟨a, h⟩ else active ⟨a, Nat.lt_of_not_ge h⟩

theorem forecastIntegerAxisMerge_short
    (short : AllocatedShortIntegerAxis U basis L → ℤ)
    (active : AllocatedActiveIntegerAxis U basis L → ℤ)
    (a : AllocatedShortIntegerAxis U basis L) :
    forecastIntegerAxisMerge U basis L short active a.val = short a := by
  rw [forecastIntegerAxisMerge, dif_pos a.property]
  rfl

theorem forecastIntegerAxisMerge_active
    (short : AllocatedShortIntegerAxis U basis L → ℤ)
    (active : AllocatedActiveIntegerAxis U basis L → ℤ)
    (a : AllocatedActiveIntegerAxis U basis L) :
    forecastIntegerAxisMerge U basis L short active a.val = active a := by
  rw [forecastIntegerAxisMerge, dif_neg (Nat.not_le.mpr a.property)]
  rfl

noncomputable def forecastIntegerAxisSplit :
    ((Σ j : Fin m, Fin (n j)) → ℤ) ≃ᵐ
      ((AllocatedShortIntegerAxis U basis L → ℤ) ×
        (AllocatedActiveIntegerAxis U basis L → ℤ)) where
  toFun z := (fun a => z a.val, fun a => z a.val)
  invFun z := forecastIntegerAxisMerge U basis L z.1 z.2
  left_inv z := by
    funext a
    dsimp only [forecastIntegerAxisMerge]
    split <;> rfl
  right_inv z := by
    apply Prod.ext
    · funext a
      exact forecastIntegerAxisMerge_short U basis L z.1 z.2 a
    · funext a
      exact forecastIntegerAxisMerge_active U basis L z.1 z.2 a
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorPeriodBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_canonicalSlicedModelPrefactor_budget (m dim : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Fin m → Type*} [∀ j, Fintype (I j)]
      {n : Fin m → ℕ} {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
      {P Pnum Pk : ℝ}, 0 ≤ P → Pnum ∈ Set.Icc 0 P → Pk ∈ Set.Icc 0 P →
      (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P →
      (∀ j, (Fintype.card (Q j) : ℝ) ≤ P) →
      let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin dim)) * (Pnum + 8) * (1 + 4 * Pnum) +
        Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
        ∑ j : Fin m, (Fintype.card (Q j) : ℝ) *
          (Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) * ((m + 1 : ℕ) * Pk))
      Fmodel ∈ Set.Icc 0 ((P + C) ^ C) := by
  let rows : ℕ := ∑ j : Fin m,
    Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
  let X : Polynomial ℕ := Polynomial.X
  let poly := Polynomial.C (m * 2 ^ dim) * (X + 8) * (1 + 4 * X) +
    X * (Polynomial.C (m * 2 ^ (m + 1)) * X) +
    X * (Polynomial.C rows * (Polynomial.C (m + 1) * X))
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro I _ n Q _ P Pnum Pk hP hPnum hPk haxes hQ Fmodel
  have hnum : 0 ≤ Pnum := hPnum.1
  have hk : 0 ≤ Pk := hPk.1
  have hsum : (∑ j : Fin m, (Fintype.card (Q j) : ℝ) *
      (Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) * ((m + 1 : ℕ) * Pk))) ≤
      P * (rows * ((m + 1 : ℕ) * P)) := by
    calc
      _ ≤ ∑ j : Fin m, P *
          (Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) * ((m + 1 : ℕ) * P)) := by
        apply Finset.sum_le_sum
        intro j _
        gcongr
        exact hQ j
        exact hPk.2
      _ = _ := by
        simp only [rows, Nat.cast_sum]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hF : Fmodel ≤ (m * (2 : ℝ) ^ dim) * (P + 8) * (1 + 4 * P) +
      P * ((m * 2 ^ (m + 1) : ℕ) * P) + P * (rows * ((m + 1 : ℕ) * P)) := by
    dsimp only [Fmodel]
    simp only [Fintype.card_fin]
    apply add_le_add _ hsum
    gcongr
    exact hPnum.2
    exact hPnum.2
    exact hPk.2
  refine ⟨by dsimp only [Fmodel]; positivity, hF.trans ?_⟩
  simpa [poly, X, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_preparedModularCanonicalDetector_period_budget (m dim Cgrid : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {nX : ℕ} {A : Type*} [Fintype A]
      (n : Fin m → ℕ) (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
      {P Pk Qstride p : ℝ}, 0 ≤ P → (nX : ℝ) ≤ P → Pk ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P →
      (Fintype.card A : ℝ) ≤ P → (∀ j, (n j : ℝ) ≤ P) →
      (∀ j, (Fintype.card (Q j) : ℝ) ≤ P) →
      let O := fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
      let budget := (P + C) ^ C
      let L := ((m + 1 : ℕ) : ℝ) * Pk
      let qlog := L + nX * Qstride
      let maskLog := (Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
        ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
      let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
      P ≤ budget ∧ L ∈ Set.Icc 0 budget ∧ qlog ∈ Set.Icc 0 budget ∧
      (p + 1) ∈ Set.Icc 0 budget ∧ maskLog ∈ Set.Icc 0 budget ∧
      labelLog ∈ Set.Icc 0 budget ∧
      ((dim : ℝ) + qlog + (p + 1) + 1) ∈ Set.Icc 0 budget ∧
      ((Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (p + 1) + 4) ∈ Set.Icc 0 budget ∧
      ∀ {M period : ℕ} [NeZero period],
        (M : ℝ) ≤ Real.exp Pk → period ≤ M ^ (m + 1) →
        (period : ℝ) ≤ Real.exp budget ∧
        (layerKernelIndexBound m M : ℝ) ^ Fintype.card A * coefficientDeckPeriodCap O Q period ≤
          Real.exp budget ∧
        (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤
          Real.exp budget := by
  let rows : ℕ := ∑ j : Fin m, Fintype.card
    (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)
  let X : Polynomial ℕ := Polynomial.X
  let Lp := Polynomial.C (m + 1) * X
  let Qp := Lp + X * X
  let Mp := X * (Polynomial.C (m * 2 ^ (m + 1)) * X) + X * (Polynomial.C rows * Lp)
  let labelp := Polynomial.C (2 * m) * X * Lp
  let tp := Polynomial.C dim + Qp + (X + 1) + 1
  let gp := Polynomial.C Cgrid + Polynomial.C (dim + 1) * Qp + (X + 1) + 4
  let poly := X + Lp + Mp + labelp + tp + gp
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro nX A _ n Q _ P Pk Qstride p hP hnX hPk hQstride hp hA hn hQ O budget L qlog maskLog labelLog
  have hPk0 : 0 ≤ Pk := hPk.1
  have hp0 : 0 ≤ p := hp.1
  let Lb := ((m + 1 : ℕ) : ℝ) * P
  let Qb := Lb + P * P
  let Mb := P * ((m * 2 ^ (m + 1) : ℕ) * P) + P * (rows * Lb)
  let labelb := (2 * m : ℕ) * P * Lb
  let tb := (dim : ℝ) + Qb + (P + 1) + 1
  let gb := (Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * Qb + (P + 1) + 4
  have hLb : 0 ≤ Lb := by dsimp only [Lb]; positivity
  have hQb : 0 ≤ Qb := by dsimp only [Qb]; positivity
  have hMb : 0 ≤ Mb := by dsimp only [Mb]; positivity
  have hlb : 0 ≤ labelb := by dsimp only [labelb]; positivity
  have htb : 0 ≤ tb := by dsimp only [tb]; positivity
  have hgb : 0 ≤ gb := by dsimp only [gb]; positivity
  have htotal : P + Lb + Mb + labelb + tb + gb ≤ budget := by
    simpa [poly, X, Lp, Qp, Mp, labelp, tp, gp, Lb, Qb, Mb, labelb, tb, gb,
      Polynomial.eval₂_pow] using hbound P hP
  have hL : L ≤ Lb := mul_le_mul_of_nonneg_left hPk.2 (Nat.cast_nonneg _)
  have hL0 : 0 ≤ L := mul_nonneg (Nat.cast_nonneg _) hPk.1
  have hqlog : qlog ≤ Qb := add_le_add hL
    (mul_le_mul hnX hQstride.2 hQstride.1 hP)
  have hqlog0 : 0 ≤ qlog := add_nonneg hL0 (mul_nonneg (Nat.cast_nonneg _) hQstride.1)
  have hsum : (∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)) ≤ P * (rows * Lb) := by
    calc
      _ ≤ ∑ j : Fin m, P * (Fintype.card (O j) * Lb) := by
        apply Finset.sum_le_sum
        intro j _
        gcongr
        exact hQ j
      _ = _ := by
        simp only [O, rows, Nat.cast_sum]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hmask : maskLog ≤ Mb := by
    apply add_le_add _ hsum
    gcongr
    exact hPk.2
  have hlabel : labelLog ≤ labelb := by
    calc
      _ ≤ (∑ _j : Fin m, P * Lb) + ∑ _j : Fin m, P * Lb := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro j _
          gcongr
          exact hn j
        · apply Finset.sum_le_sum
          intro j _
          gcongr
          exact hQ j
      _ = _ := by simp only [labelb, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring
  have ht : (dim : ℝ) + qlog + (p + 1) + 1 ≤ tb := by
    dsimp only [tb]
    gcongr
    exact hp.2
  have hg : (Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (p + 1) + 4 ≤ gb := by
    dsimp only [gb]
    gcongr
    exact hp.2
  have hLbudget : L ≤ budget := by linarith
  have hmaskbudget : maskLog ≤ budget := by linarith
  have hlabelbudget : labelLog ≤ budget := by linarith
  refine ⟨by linarith, ⟨hL0, hLbudget⟩,
    ⟨hqlog0, ?_⟩, ⟨by positivity, ?_⟩,
    ⟨by dsimp only [maskLog]; positivity, hmaskbudget⟩,
    ⟨by dsimp only [labelLog]; positivity, hlabelbudget⟩,
    ⟨by positivity, by linarith⟩, ⟨by positivity, by linarith⟩, ?_⟩
  · dsimp only [tb] at htotal htb
    linarith [Nat.cast_nonneg (α := ℝ) dim]
  · dsimp only [tb] at htotal htb
    linarith [Nat.cast_nonneg (α := ℝ) dim, hp.2]
  · intro M period _ hM hperiod
    obtain ⟨hperiodBound, hmaskBound, hlabelBound⟩ :=
      canonicalPeriod_primitive_bounds A n O Q hM hperiod
    exact ⟨hperiodBound.trans (Real.exp_le_exp.mpr hLbudget),
      hmaskBound.trans (Real.exp_le_exp.mpr hmaskbudget),
      hlabelBound.trans (Real.exp_le_exp.mpr hlabelbudget)⟩

theorem exists_preparedModularCanonicalDetector_grid_parameters (m dim : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {nX : ℕ} {Pk Qstride p : ℝ},
      0 ≤ Pk → 0 ≤ Qstride → 0 ≤ p →
      let Q := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let tg := (dim : ℝ) + Q + (p + 1) + 1
      let pg := (C : ℝ) + ((dim + 1 : ℕ) : ℝ) * Q + (p + 1) + 4
      let δ := Real.exp (-(p + 1))
      0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp (p + 1) ∧ 0 ≤ tg ∧ 0 ≤ pg ∧
      ∃ T : ℕ, (T : ℝ) ≤ Real.exp tg ∧
      ∀ {M period : ℕ} (stride : Fin nX → ℕ),
        (M : ℝ) ≤ Real.exp Pk → 0 < period → period ≤ M ^ (m + 1) →
        (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp Qstride) →
        let q := residueRefinedPeriod period stride
        (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
        1 ≤ Real.exp pg ∧
        scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Real.exp pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Real.exp pg ∧
        ∀ {Y : Type*} (step : Y → ℕ),
          (∀ y, (step y : ℝ) ≤ 4 * Real.exp (p + 1)) →
          ∀ y, ((step y * q : ℕ) : ℝ) ≤ Real.exp pg := by
  obtain ⟨C, hC, hparameters⟩ := exists_uniform_slicedGridParameters dim A
  refine ⟨C, hC, ?_⟩
  intro nX Pk Qstride p hPk hQstride hp Q tg pg δ
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hF : 0 ≤ p + 1 := by positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hδF : δ⁻¹ ≤ Real.exp (p + 1) := by
    simp only [δ, Real.exp_neg, inv_inv, le_refl]
  obtain ⟨T, hT, hgrid⟩ := hparameters hF hQ
  refine ⟨hδ, Real.exp_le_one_iff.mpr (by linarith), hδF,
    by dsimp only [tg]; positivity, by dsimp only [pg]; positivity, T, hT, ?_⟩
  intro M period stride hM hperiod hperiodBound hstride hstrideBound q
  have hperiodLog : (period : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * Pk) := by
    calc
      _ ≤ ((M ^ (m + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hperiodBound
      _ = (M : ℝ) ^ (m + 1) := Nat.cast_pow _ _
      _ ≤ (Real.exp Pk) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hq : 0 < q := residueRefinedPeriod_pos hperiod stride hstride
  have hqQ : (q : ℝ) ≤ Real.exp Q := by
    simpa only [Fintype.card_fin] using residueRefinedPeriod_exp_bound period stride hperiodLog hstrideBound
  have hstepZero : ((0 : ℕ) : ℝ) ≤ 4 * Real.exp (p + 1) := by
    simpa only [Nat.cast_zero] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_nonneg (p + 1))
  obtain ⟨hQT, hPg, hcP, hsP, _⟩ := hgrid (step := 0) hδ hδF hq hqQ hstepZero
  refine ⟨hQT, hPg, hcP, hsP, ?_⟩
  intro Y step hstep y
  exact (hgrid hδ hδF hq hqQ (hstep y)).2.2.2.2

end Erdos3.VectorPolynomial

end

end OAI

end


