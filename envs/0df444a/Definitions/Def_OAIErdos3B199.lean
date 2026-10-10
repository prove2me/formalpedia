-- Prove2me | Definitions.Def_OAIErdos3B199
-- name    : OAIErdos3B199
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T09:25:01.246528+00:00
-- url     : https://prove2.me/theorems/af870e8c-84f8-48ff-b7e4-d1a58a8f178d
-- title:
--   OpenAI Erdős-3 split, definitions bundle 200 of 206
-- statement:
--   Definitions bundle 200 of 206 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B198`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 200 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.exists_translated_physical_jet_density_window_mass`, `OAI.Erdos3.BooleanCubeKernel.exists_translated_physical_jet_probability_mass`, `OAI.Erdos3.BooleanCubeKernel.exists_translated_physical_jet_probability_window_mass`, `OAI.Erdos3.VectorPolynomial.PreparedModularGeneralEarlyAnalyticBounds.casesOn`, `OAI.Erdos3.VectorPolynomial.PreparedModularGeneralLateAmbientBounds.rec`, `OAI.Erdos3.VectorPolynomial.allocatedRecenteredFiniteModelSource`, `OAI.Erdos3.VectorPolynomial.exists_allocatedRecenteredFactor_normalization`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B162
import Definitions.Def_OAIErdos3B164
import Definitions.Def_OAIErdos3B200

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedNormalizedNativeModel
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
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

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
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

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
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable {X : Type*} [Fintype X] (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : X → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X spatialModulus stride wholeReference x base label

noncomputable def allocatedRecenteredFiniteModelSource
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) : ℂ :=
  ∑ z : cells × window, (selectedResidueCellWeight stride cells widths z.1 : ℂ) *
    allocatedRecenteredResidueWeight (τ := τ) B U b S X spatialModulus stride wholeReference x hM selection hx
      N hW mesh base cells (physicalCubeSiteTest test) label z.1 z.2.val *
    (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)) *
    allocatedFullGridChartModel B U b S rowSets d hb o bW e
      (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocatedRecenteredFactor_normalization (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
      {J : Fin m → Type*} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
      {X Y : Type*} [Fintype X] [PseudoMetricSpace Y]
      (selection : Fin dim ↪ G) {M modulus : ℕ} [NeZero modulus]
      {p E analytic : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ analytic →
      (Fintype.card G : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p → ((dim + 1 : ℕ) : ℝ) ≤ p →
      0 < M → (M : ℝ) ≤ Real.exp p → modulus ≤ M ^ (m + 1) →
      ∀ (r : ℝ≥0), (r : ℝ) = allocatedEarlyRecenteredMesh X selection M modulus p E →
      ∀ (stride N : X → ℕ) {τ : ℝ},
      (∀ i, 0 < N i) → (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp p) →
      0 < τ → 1 / τ ≤ Real.exp p →
      ∀ (wholeReference :
        (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
          PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
        (x : G → IntegerScalarCubeBox (Fin dim) S.value) (base : X → ℤ)
        (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride))
        (cell : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)
        (t : X → SpatialSiteLabel (Fin dim) modulus 4 r) (site : Finset (Fin dim))
        (F : Y → ℂ) {L : ℝ≥0}, LipschitzWith L F → (∀ y, ‖F y‖ ≤ 1) → (L : ℝ) ≤ Real.exp analytic →
      0 < residueRefinedPeriod modulus stride ∧
      (residueRefinedPeriod modulus stride : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * p + Fintype.card X * p) ∧
      ∃ (mask : (X → ZMod (residueRefinedPeriod modulus stride)) → ℂ)
        (H : (X → ℝ) × Y → ℂ),
        (∀ z, ‖mask z‖ ≤ 1) ∧ (∀ v, ‖H v‖ ≤ 1) ∧
        LipschitzWith ⟨Real.exp ((p + E + analytic + A) ^ A), Real.exp_nonneg _⟩ H ∧
        ∀ (u : X → ℤ) (y : Y),
          allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus stride wholeReference x N r base label cell t site u * F y =
            mask (fun i => (u i : ZMod (residueRefinedPeriod modulus stride))) * H (fun i => (u i : ℝ) / N i, y) := by
  obtain ⟨A, hA, hfactor⟩ := exists_allocatedSlicedFactor_budget m dim
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ S X Y _ _ selection M modulus _ p E analytic hp hE ha hG hX hdim
    hM hMP hmodulus r hr stride N τ hN hs hsP hτ hτP wholeReference x base label cell t site F L hF hFb hL
  let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
  let dirs := allocatedPhysicalCubeDirections B U b S x (wholeReference label)
  let residue := boundedColumnResidueRepresentative stride cell
  let hdiv := stride_mul_dvd_residueRefinedPeriod modulus stride
  let mask := physicalResidueSpatialMaskMod root dirs base residue stride 4 r hdiv t site
  let H := physicalSpatialAnalyticContinuous (τ := τ) root dirs base residue stride N r t site F
  have hmod : (modulus : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * p) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hmodulus
      _ ≤ (Real.exp p) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hMP _
      _ = _ := (Real.exp_nat_mul _ _).symm
  obtain ⟨hHb, hHL⟩ := hfactor selection hp hE ha hG hX hdim hM hMP hmodulus r hr root dirs base residue stride N
    hN hs hτ hτP t site F hF hFb hL
  refine ⟨residueRefinedPeriod_pos (Nat.pos_of_ne_zero (NeZero.ne modulus)) stride hs,
    residueRefinedPeriod_exp_bound modulus stride hmod hsP, mask, H,
    physicalResidueSpatialMaskMod_norm root dirs base residue stride 4 r hdiv t site, hHb, hHL, ?_⟩
  intro u y
  exact physicalSpatialAnalytic_normalized root dirs base residue stride N r t site F hN hdiv u y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))


attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
local notation "refined" => residueRefinedPeriod spatialModulus stride
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalRowsProbabilityMassSampling
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_translated_physical_jet_probability_mass (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → EuclideanJetLayers U O → ℝ)
    (_hg0 : ∀ a z, 0 ≤ g a z)
    (_hgi : ∀ a, Integrable (g a) (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    (_hgmass : ∀ a, (∫ z, g a z ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) = 1)
    (f : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Cf : ℝ≥0) (_hf : LipschitzWith Lf f) (_hfb : ∀ z, ‖f z‖ ≤ Cf)
    (_hactual : ∀ z, law.complexMean (fun a => (g a z : ℂ)) = f (coveredJetAmbientTorus U 1 z))
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hCf : (Cf : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        law.mean (fun a => g a (physicalCubeRowSample U q rows p _hm
          (translatePhysicalCube base (standardPhysicalCubeOutput z))))) ≤ 1 + (2 * η + ε) := by
  obtain ⟨A, hA, hsample⟩ := exists_translated_physical_jet_l1_perturbation m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    Y _ law g hg0 hgi hgmass f Lf Cf hf hfb hactual η hη hdim hLf hCf hjet hηT
  have hnorm (z) : ‖f (coveredJetAmbientTorus U 1 z)‖ = law.mean (fun a => g a z) := by
    rw [← hactual, FiniteProbabilityWeights.complexMean_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (law.mean_nonneg (fun a => hg0 a z))]
  have hmass : (∫ z, ‖f (coveredJetAmbientTorus U 1 z) - 0‖
      ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ 1 := by
    simp only [sub_zero, hnorm]
    rw [law.integral_mean _ _ hgi]
    simp only [hgmass, law.mean_const, le_refl]
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hT hn hd U μ ν base p hp hm q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    f (fun _ => 0) Lf 0 Cf 0 hf (LipschitzWith.const 0) hfb (fun _ => by simp)
    hη hdim hLf (by positivity) hCf (by positivity) hjet hηT (fun _ => 0) measurable_const
    (δ := 0) (fun _ => by simp) hmass
  refine ⟨hZ, ?_⟩
  simpa only [sub_zero, hnorm, mul_zero, add_zero] using he

theorem exists_translated_physical_jet_probability_window_mass (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    {K : Type*} [Fintype K] (root : K → ℤ) (D : Matrix (Fin dim) K ℤ)
    (residue : ColumnResiduePattern (Option K) I stride)
    (Hwindow : I → ℝ) (_hHwindow : ∀ i, 0 < Hwindow i)
    (_hcoef : ∀ i t, (∑ k, |(physicalCubeCoefficient root D t k : ℝ)|) ≤ Hwindow i)
    (_hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hwindow i)
    (_hwidth : ∀ z : Option (Fin dim) × I, ρ * H z.2 ≤ referenceJetEnvelopeWidths stride Hwindow z)
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → EuclideanJetLayers U O → ℝ)
    (_hg0 : ∀ a z, 0 ≤ g a z)
    (_hgi : ∀ a, Integrable (g a) (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    (_hgmass : ∀ a, (∫ z, g a z ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) = 1)
    (f : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Cf : ℝ≥0) (_hf : LipschitzWith Lf f) (_hfb : ∀ z, ‖f z‖ ≤ Cf)
    (_hactual : ∀ z, law.complexMean (fun a => (g a z : ℂ)) = f (coveredJetAmbientTorus U 1 z))
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hCf : (Cf : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T) (_hsmall : 2 * η + ε ≤ 3),
    (∑ v ∈ spatialWindow Hwindow 4, law.mean (fun a => g a (physicalCubeRowSample U q rows p _hm
      (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative stride residue) stride v)))) ≤
      (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × I)) *
        (∏ i, ∏ _t : Unit ⊕ Fin dim, Hwindow i) := by
  obtain ⟨A, hA, hsample⟩ := exists_translated_physical_jet_probability_mass m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR K _ root D residue Hwindow hHwindow hcoef hscale hwidth
    Y _ law g hg0 hgi hgmass f Lf Cf hf hfb hactual η hη hdim hLf hCf hjet hηT hsmall
  let target := columnResiduePattern stride (standardPhysicalCubeFrame
    (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride residue)))
  let V := referenceJetEnvelopeWidths (q := dim) stride Hwindow
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hT hn hd U μ ν base p hp hm q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank hR {target} (Finset.singleton_nonempty _)
    V (referenceJetEnvelopeWidths_pos stride hs Hwindow hHwindow) hwidth law g hg0 hgi hgmass
    f Lf Cf hf hfb hactual hη hdim hLf hCf hjet hηT
  have hraw := physicalReconstruction_sum_le_sampled_mass stride hs root D residue Hwindow hHwindow hcoef hscale
    (fun v => law.mean (fun a => g a (physicalCubeRowSample U q rows p hm (translatePhysicalCube base v))))
    (fun v => law.mean_nonneg (fun a => hg0 a _)) hZ
  rw [referenceJetEnvelope_volume stride hs Hwindow] at hraw
  have hvol : 0 ≤ (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × I) *
      (∏ i, ∏ _t : Unit ⊕ Fin dim, Hwindow i) := by
    apply mul_nonneg (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
    exact Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun _ _ => (hHwindow i).le))
  have hfour := he.trans (show 1 + (2 * η + ε) ≤ 4 by linarith)
  have hout := hraw.trans (mul_le_mul_of_nonneg_left hfour hvol)
  simp_rw [← physicalResidueReconstruction_translate] at hout
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hout

theorem exists_translated_physical_jet_density_window_mass (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    {K : Type*} [Fintype K] (root : K → ℤ) (D : Matrix (Fin dim) K ℤ)
    (residue : ColumnResiduePattern (Option K) I stride)
    (Hwindow : I → ℝ) (_hHwindow : ∀ i, 0 < Hwindow i)
    (_hcoef : ∀ i t, (∑ k, |(physicalCubeCoefficient root D t k : ℝ)|) ≤ Hwindow i)
    (_hscale : ∀ i, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * Hwindow i)
    (_hwidth : ∀ z : Option (Fin dim) × I, ρ * H z.2 ≤ referenceJetEnvelopeWidths stride Hwindow z)
    (g : EuclideanJetLayers U O → ℝ)
    (_hg0 : ∀ z, 0 ≤ g z)
    (_hgi : Integrable g (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))))
    (_hgmass : (∫ z, g z ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) = 1)
    (f : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Cf : ℝ≥0) (_hf : LipschitzWith Lf f) (_hfb : ∀ z, ‖f z‖ ≤ Cf)
    (_hactual : ∀ z, (g z : ℂ) = f (coveredJetAmbientTorus U 1 z))
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hCf : (Cf : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T) (_hsmall : 2 * η + ε ≤ 3),
    (∑ v ∈ spatialWindow Hwindow 4, g (physicalCubeRowSample U q rows p _hm
      (physicalResidueReconstruction root D base (boundedColumnResidueRepresentative stride residue) stride v))) ≤
      (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × I)) *
        (∏ i, ∏ _t : Unit ⊕ Fin dim, Hwindow i) := by
  obtain ⟨A, hA, hsample⟩ := exists_translated_physical_jet_probability_window_mass m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR K _ root D residue Hwindow hHwindow hcoef hscale hwidth
    g hg0 hgi hgmass f Lf Cf hf hfb hactual η hη hdim hLf hCf hjet hηT hsmall
  let law : FiniteProbabilityWeights Unit := {
    weight := fun _ => 1
    nonneg := fun _ => zero_le_one
    total := by simp }
  have he := hsample rows hinj hrows hT hn hd U μ ν base p hp hm q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank hR root D residue Hwindow hHwindow hcoef hscale hwidth
    law (fun _ => g) (fun _ => hg0) (fun _ => hgi) (fun _ => hgmass) f Lf Cf hf hfb
    (fun z => by simpa only [law.complexMean_const] using hactual z)
    hη hdim hLf hCf hjet hηT hsmall
  simpa only [law.mean_const] using he

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularCanonicalDetectorAmbientConsumer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin 1)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)


variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

structure PreparedModularGeneralEarlyAnalyticBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) (P D pDetect : ℝ) : Prop where
  hQgrid : ∀ a : {a // grid a},
    8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤
        (Real.toNNReal (8 * (D + 1)) : ℝ)
  hDg : 0 ≤ r.Dg
  hvg : 0 ≤ r.v
  hwg : 0 ≤ r.w
  hcube : (Fintype.card (Fin dim) : ℝ) ≤ r.Dg
  hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ r.Dg
  hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ r.Dg
  htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ r.Dg
  hblocks : ∀ a, (Fintype.card (B a) : ℝ) ≤ r.Dg
  hRv : ∀ j, R j ≤ Real.exp r.v
  hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp r.v
  hδw : pDetect + 1 ≤ r.w
  hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp r.v
  haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ r.Dg
  hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ r.Dg
  hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ r.Dg
  hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ r.Dg
  hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ r.Dg
  hBanalytic : 0 ≤ r.Banalytic
  hDanalytic : r.Dg ≤ r.Banalytic
  hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp r.Banalytic
  hcoordAnalytic : ((Ksource * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤
    Real.exp r.Banalytic
  hgridAnalytic : (Real.toNNReal (8 * (D + 1)) : ℝ) ≤ Real.exp r.Banalytic
  hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P
  hn : ∀ j, (n j : ℝ) ≤ P
  hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
    (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P
  hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp P
  hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V Cforward : Fin m → ℝ≥0) (Ksource : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

structure PreparedModularGeneralLateAmbientBounds
    (r : PreparedModularCanonicalDetectorResources ℝ) : Prop where
  hPbox : 0 ≤ r.Pbox
  hVlog : 0 ≤ r.Vlog
  hNlog : 0 ≤ r.Nlog
  hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp r.Pbox
  hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp r.Vlog
  hnormalizer : ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp r.Nlog
  hbaseAmbient : 0 ≤ r.baseAmbient
  hvbase : r.Vlog ≤ r.baseAmbient
  hnbase : r.Nlog ≤ r.baseAmbient
  hsites : (Fintype.card (Finset (Fin dim)) : ℝ) ≤ r.baseAmbient
  haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ r.baseAmbient
  hKbase : (Ksource : ℝ) ≤ Real.exp r.baseAmbient
  hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp r.baseAmbient
  hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp r.baseAmbient
  hrowsAmbient : ((∑ j, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp r.baseAmbient
  houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ r.baseAmbient
  hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp r.baseAmbient

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (0 + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
variable (selection : Fin (0 + 1) ↪ G) (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

end Erdos3.VectorPolynomial

end

end OAI

end


