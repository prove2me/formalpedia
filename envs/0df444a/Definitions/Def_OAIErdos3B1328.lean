-- Prove2me | Definitions.Def_OAIErdos3B1328
-- name    : OAIErdos3B1328
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T18:21:43.211156+00:00
-- url     : https://prove2.me/theorems/3d648f7f-a7ca-4476-b4c3-77516df708c9
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1329 of 1335
-- statement:
--   Definitions bundle 1329 of 1335 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1327`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1329 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.path_base_abs_le`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.path_spatial_center_mass_le`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.path_spatial_center_mass_le_trim`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSamplerFamily.preparedConditionalExcessFinDecidableEq`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.zeroLayerScale`, `OAI.Erdos3.VectorPolynomial.CanonicalEmptyLayerGeometry.zeroLayerScale_value`, `OAI.Erdos3.VectorPolynomial.PreparedShortCertifiedSameScaleBadProductInterface`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredJointDensity_empty_layers`, `OAI.Erdos3.VectorPolynomial.exists_allocated_centered_narrow_amplitude_normalization`, `OAI.Erdos3.VectorPolynomial.exists_allocated_narrow_amplitude_normalization`, `OAI.Erdos3.VectorPolynomial.preparedCenteredShortJoint_badProduct_of_read`, `OAI.Erdos3.exp_unconditionedCommonSideExtra`, `OAI.Erdos3.unconditionedCommonSide`, `OAI.Erdos3.unconditionedCommonSideExtra`, `OAI.Erdos3.unconditionedCommonSideScalarRatio`, `OAI.Erdos3.unconditionedCommonSide_cast`, `_private.Estimates.AllocatedCanonicalUniformCoarseSource.0.OAI.Erdos3.VectorPolynomial.canonicalCoverExponent`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1327

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalUniformCoarseSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal
attribute [local instance 2000] fullBooleanRowSetFintype

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (Cproj Vproj : Fin m → ℝ≥0)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) →
  ZMod (residueRefinedPeriod modulus q))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod modulus q) y = label₀)))
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset (residueRefinedPeriod modulus q) label₀ hcell).weight y₀)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hcanonical : modulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
local notation "O" => (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type))
local notation "rows" => (fun j => (Subtype.val : O j → Finset (Fin dim)))
variable (cover : ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
variable (signal : (X → ℤ) → ℂ) (hsignal : ∀ u, ‖signal u‖ ≤ 1)


variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)


variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal
attribute [local instance 2000] fullBooleanRowSetFintype

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (Cproj Vproj : Fin m → ℝ≥0)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) →
  ZMod (residueRefinedPeriod modulus q))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod modulus q) y = label₀)))
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset (residueRefinedPeriod modulus q) label₀ hcell).weight y₀)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hcanonical : modulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
local notation "O" => (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type))
local notation "rows" => (fun j => (Subtype.val : O j → Finset (Fin dim)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
variable (signal : (X → ℤ) → ℂ) (hsignal : ∀ u, ‖signal u‖ ≤ 1)


variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)


variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)]
variable [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
variable (μcoeff : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μcoeff.IsAddLeftInvariant] [IsProbabilityMeasure μcoeff]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal
attribute [local instance 2000] fullBooleanRowSetFintype

noncomputable abbrev canonicalCoverExponent_p0
    (m dim : ℕ) (_X : Type uX) (_G : Type uG) (I : Fin m → Type uI)
    (n : Fin m → ℕ) (_B : LayerSamplerAxis I n → Type uB) (_J : Fin m → Type uJ) : ℕ :=
  Classical.choose (exists_allocated_canonical_constructed_projection.{uX,uG,uI,uB,uJ} m dim)

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (Cproj Vproj : Fin m → ℝ≥0)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) →
  ZMod (residueRefinedPeriod modulus q))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod modulus q) y = label₀)))
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset (residueRefinedPeriod modulus q) label₀ hcell).weight y₀)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hcanonical : modulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
local notation "O" => (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type))
local notation "rows" => (fun j => (Subtype.val : O j → Finset (Fin dim)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
variable (signal : (X → ℤ) → ℂ) (hsignal : ∀ u, ‖signal u‖ ≤ 1)


variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)


variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)]
variable [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
variable (μcoeff : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μcoeff.IsAddLeftInvariant] [IsProbabilityMeasure μcoeff]

variable {Pproj Pk : ℝ}
local notation "coverExponent" => canonicalCoverExponent_p0 m dim X G I n B J
local notation "samplingExponent" => Classical.choose
  (exists_allocatedCanonicalProjection_composed_budget m dim coverExponent)
local notation "Pmass" => (Pproj + samplingExponent) ^ samplingExponent

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredShortJointBadProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

variable (Elog Vlog : ℝ) (Q : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

def PreparedShortCertifiedSameScaleBadProductInterface (B Elog Vlog : ℝ) (Q : ℕ) : Prop :=
  let Ps := (B + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m
  ∀ {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp B) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp B)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (_hρ : 0 < ρ) (_hρPs : 1 / ρ ≤ Real.exp B)
    (stride : Fin nX → ℕ) (_hstride : ∀ x, 0 < stride x)
    (_hSmax : 0 ≤ Smax) (_hSmaxPs : Smax ≤ Real.exp B) (_hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (_hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (_hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (_hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (_hwide : ∀ z, ρ * H z.2 ≤ width z)
    , let Dphysical := fun z : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ =>
      allocatedCoefficientDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
        AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hne : ∀ p : primes, NeZero p.val),
          letI := hne
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q),
            letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness
                  (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)
                  (modularInitialRankStrength m (nX + m * M) : ℝ) primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad
                (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)
                (preparedInitialRankSpatialEmbedding (m := m) nX M)
                (preparedInitialRankKernelEmbedding (m := m) nX M)
                (preparedInitialRankPrincipalEmbedding prep nX M
                  (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value))
                (modularInitialRankStrength m (nX + m * M) : ℝ)
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 3 * (physicalBadProductAccuracy Elog Vlog) ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      0 < (quantitativeBadPrimeRadius Elog) ∧ ((quantitativeBadPrimeRadius Elog) : ℝ) ≤ Real.exp (Elog + 3) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if (∏ x, stride x) ^ 2 *
              (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * (quantitativeBadPrimeRadius Elog)) <
                ∏ p ∈ primes, p ^ largestTestedBadDepth depth
                  (fun p a z => allocatedActualPrimeBad (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M)
                    (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) primes ((modularInitialRankStrength m ((nX + m * M : ℕ)) : ℝ)) p a (read z)) p z
              then (1 : ℝ) else 0)) ≤ Real.exp (-Elog)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

omit [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))] in

theorem preparedCenteredShortJoint_badProduct_of_read
    (B0 Elog Vlog : ℝ) (Q : ℕ)
    (hsource : PreparedShortCertifiedSameScaleBadProductInterface prep U b S B0 Elog Vlog Q)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp B0)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp B0) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp B0)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {ρ Rs Smax : ℝ}
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp B0)
    (stride : Fin nX → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp B0) (hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (hsize : ∀ x, Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((((B0 + preparedBadProductSpatialExponent m) ^ preparedBadProductSpatialExponent m) + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)

    (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (read : (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ)
    (hread : ∀ a z, allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center a z ≠ 0 → AllocatedPhysicalRankReadCertificate (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o (allocatedCenteredConditionalPolynomial U poly c a) (allocatedCenteredConditionalPolynomial_mem U poly hm c a) (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) z (read a z)) :
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ _hlocal : ∀ a, 0 < selectedResidueDensityMass stride cells width (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center a),
    ∀ (bases : Finset (Fin nX → ℤ)) (hbases : bases.Nonempty),
      ∃ htotal : 0 < selectedJointDensityMass bases stride cells width (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center),
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (selectedJointFiniteLaw bases hbases stride cells width hwidth hZ (allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center)
            (allocatedCenteredJointDensity_nonneg (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center) htotal).mean
            (fun az => let a := az.1.val; let z := az.2.val
              if (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog) <
        ∏ p ∈ primes, p ^ largestTestedBadDepth depth
          (fun p d z => allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M)
            (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ) p d (read a z)) p z then (1 : ℝ) else 0) ≤ Real.exp (-Elog) := by
  let density := allocatedCenteredJointDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm center
  have hconditional (a : Fin nX → ℤ) :=
    hsource bW hb o C V hC hV hR hσ hσ1 Cinv hCinv hchart hsmall hAP hCP hVP μ ν
      (allocatedCenteredConditionalPolynomial U poly c a) (allocatedCenteredConditionalPolynomial_degree U poly c a hp)
      (allocatedCenteredConditionalPolynomial_mem U poly hm c a) hρ hρPs stride hstride hSmax hSmaxPs hstrideMax H hsize
      (fun j => (allocatedCenteredConditionalPolynomial_rank U poly c a hp H Rs j).mpr (hrank j))
      hRs cells hcells width hwidth hwide
  dsimp only at hconditional
  simp_rw [allocatedCenteredConditionalPolynomial_density U poly hm c _ (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) b hb o hR hσ S center hc] at hconditional
  choose hD0 hZ hDpos chosen hnoise hcert hmass hlower hupper hRbad hRbound htail using hconditional
  refine ⟨hZ 0, hDpos, ?_⟩
  intro bases hbases
  have htotal : 0 < selectedJointDensityMass bases stride cells width density := by
    have hbound := selectedJointDensityMass_bounds bases hbases stride cells width density
      (fun a => ⟨hlower a, hupper a⟩)
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hbound.1
  refine ⟨htotal, ?_⟩
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  have hmix := selectedJointFiniteLaw_conditional_event_le bases hbases stride cells width hwidth (hZ 0)
    density hD0 htotal hDpos (fun a z =>
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius Elog) <
      ∏ p ∈ primes, p ^ largestTestedBadDepth depth
        (fun p d z => allocatedActualPrimeBad
          (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)
          (preparedInitialRankSpatialEmbedding (m := m) nX M)
          (preparedInitialRankKernelEmbedding (m := m) nX M)
          (preparedInitialRankPrincipalEmbedding prep nX M
            (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes
          (modularInitialRankStrength m (nX + m * M) : ℝ) p d (read a z)) p z) (ε := Real.exp (-Elog))
  apply (show _ = _ from ?_).trans_le (hmix ?_)
  · congr 1
    funext az
    dsimp only
    split_ifs <;> rfl
  intro a
  have ht := htail a primes hprime depth hdepth
  have heq := selectedResidueDensityPMF_certifiedRead_badProduct_congr
    (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o (allocatedCenteredConditionalPolynomial U poly c a) (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
    (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ)
    stride cells width hwidth (hZ 0) (density a) (hD0 a) (hDpos a)
    (chosen a) (read a) (hcert a) (hread a) primes depth
    ((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius Elog))
  rw [heq] at ht
  apply le_of_eq_of_le ?_ ht
  apply tsum_congr
  intro z
  congr 1
  split_ifs <;> rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredNarrowAmplitudeNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_amplitude_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
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
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
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
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let pa := fun (base : X → ℤ) j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun (base : X → ℤ) j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let density := fun base z => allocatedCoefficientDensity B U basis hb o hR hσ S
      (affineSampleCoefficientTorus U (pa base) (hma base) (fun k d => (z (k, d) : ℝ)))
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ (base : X → ℤ) (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
        (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
          (Lip : ℝ) ≤ Real.exp P →
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P) ∧
      ∀ base, |selectedResidueDensityMass stride T widths (density base) - 1| ≤
          3 * positiveProjectionAccuracy P ∧
        ∃ (hD0 : ∀ z, 0 ≤ density base z)
          (hD : 0 < selectedResidueDensityMass stride T widths (density base)),
          ∀ (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
            (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
              (Lip : ℝ) ≤ Real.exp P →
            ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
              ((selectedResidueDensityPMF stride T widths hwidths hZ
                (density base) hD0 hD z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)) -
              ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
                ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
              6 * positiveProjectionAccuracy P := by
  obtain ⟨A₀, _, hmass⟩ := exists_affine_coefficient_amplitude_density_test m
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m 0
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + 8 * Polynomial.X + 128 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths pa hma density
  have h2P : 0 ≤ 2 * P := mul_nonneg (by norm_num) hP
  have hP2P : P ≤ 2 * P := by linarith
  have hτξ : 0 < ξ * τ := mul_pos hξ hτ
  have hτξP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      τ⁻¹ * ξ⁻¹ ≤ Real.exp P * Real.exp P := by gcongr
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
  let Q := positiveComparisonDataBudget m 0 P + spatialSamplingBudget (2 * P)
  have hdata := positiveComparisonDataBudget_bounds m 0 hP
  have hdataQ : positiveComparisonDataBudget m 0 P ≤ Q :=
    le_add_of_nonneg_right (h2P.trans (le_spatialSamplingBudget h2P))
  have hspatialQ : spatialSamplingBudget (2 * P) ≤ Q := le_add_of_nonneg_left hdata.1
  have hPQ : P ≤ Q := hdata.2.1.trans hdataQ
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    have hbase : Q + (A₀ : ℝ) ≤ (P + b) ^ b + 8 * P + 128 + A₀ := by
      have h := hbnd P hP
      dsimp [Q, spatialSamplingBudget]
      linarith
    calc
      _ ≤ ((P + b) ^ b + 8 * P + 128 + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀)) hbase A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV 0
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  let _ := inst
  have hspec := allocatedCoefficientDensity_spec B U basis hb o hR hσ S
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hwidths := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  have hwidthLower (z : Option (LayerSamplerVariables G I n B) × X) :
      spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ widths z :=
    (spatialWidthFraction_le_allocated_width h2P hW
      (hWP.trans (Real.exp_le_exp.mpr hP2P)) hτξ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : 1 / positiveProjectionAccuracy P ≤ Real.exp Q := by
    simp only [one_div, positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (hdata.2.2.1.trans hdataQ)
  have hlocal (base : X → ℤ)
      (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ)
      (hamp : ∀ x, ‖amplitude x‖ ≤ 1) {Lip : ℝ≥0}
      (hLip : LipschitzWith Lip amplitude) (hLipP : (Lip : ℝ) ≤ Real.exp P) :
      ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P := by
    have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa base j) :=
      degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
    have hranka (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa base j) :=
      (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
    obtain ⟨hZ, hclose⟩ := hmass hQ (hX.trans hPQ) (hdim.trans hPQ) U μ
      (Real.exp_nonneg Q) le_rfl frequency
      (fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr hdataQ))
      coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans (Real.exp_le_exp.mpr hdataQ))
      (pa base) hpa (hma base) stride hs (Real.exp_nonneg Q) le_rfl
      (spatialWidthFraction_pos (2 * P) hτξ) hη
      ((spatialWidthFraction_inv_le h2P hτξ hτξP).trans (Real.exp_le_exp.mpr hspatialQ)) hηQ
      (fun d => (hsP d).trans hExp) (fun d => (N d : ℝ))
      (fun d => (Real.exp_le_exp.mpr hcut).trans (hsize d)) hranka
      ((Real.exp_le_exp.mpr hcut).trans hRank) T hT widths hwidths
      hwidthLower amplitude hamp hLip (hLipP.trans hExp)
      (allocatedCoefficientDensity B U basis hb o hR hσ S) hspec.2.2.1 hspec.2.2.2.1 hη.le happ
    refine ⟨hZ, ?_⟩
    exact hclose.trans_eq (by ring)
  obtain ⟨hZ, _⟩ := hlocal 0 (fun _ => 0) (by simp) (LipschitzWith.const 0)
    (by simpa using (Real.exp_nonneg P))
  refine ⟨hwidths, hZ, ?_, ?_⟩
  · intro base amplitude hamp Lip hLip hLipP
    exact (hlocal base amplitude hamp hLip hLipP).choose_spec
  · intro base
    have hmass := selectedResidueDensityMass_bound_of_constant_test stride T widths hwidths hZ
      (density base) ((hlocal base (fun _ => 1) (by simp) (LipschitzWith.const 1)
        (by simpa using (Real.exp_nonneg P))).choose_spec)
    have hD0 : ∀ z, 0 ≤ density base z := fun _ => hspec.2.1 _
    have hD := (positiveProjectionAccuracy_normalizer hP hmass).2.2.1
    refine ⟨hmass, hD0, hD, ?_⟩
    intro amplitude hamp Lip hLip hLipP
    have htest := (hlocal base amplitude hamp hLip hLipP).choose_spec
    have hn := selectedResidueDensityPMF_error_of_bounded_test stride T widths hwidths hZ
      (density base) hD0 hD (fun z => amplitude (fun t => (z t : ℝ) / widths t))
      (fun z => hamp _) htest hmass
    exact hn.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_centered_narrow_amplitude_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
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
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
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
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) (base : X → ℤ) (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
        (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
          (Lip : ℝ) ≤ Real.exp P →
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density center base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P) ∧
      ∀ center base, |selectedResidueDensityMass stride T widths (density center base) - 1| ≤
          3 * positiveProjectionAccuracy P ∧
        ∃ (hD0 : ∀ z, 0 ≤ density center base z)
          (hD : 0 < selectedResidueDensityMass stride T widths (density center base)),
          ∀ (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
            (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
              (Lip : ℝ) ≤ Real.exp P →
            ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
              ((selectedResidueDensityPMF stride T widths hwidths hZ
                (density center base) hD0 hD z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)) -
              ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
                ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
              6 * positiveProjectionAccuracy P := by
  obtain ⟨A, hA, hnormalization⟩ := exists_allocated_narrow_amplitude_normalization m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths density
  have hcenter (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ (base : X → ℤ) (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
        (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
          (Lip : ℝ) ≤ Real.exp P →
        ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
          ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (amplitude (fun t => (z t : ℝ) / widths t) * (density center base z : ℂ))) -
          ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
            ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
              amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
          3 * positiveProjectionAccuracy P) ∧
      ∀ base, |selectedResidueDensityMass stride T widths (density center base) - 1| ≤
          3 * positiveProjectionAccuracy P ∧
        ∃ (hD0 : ∀ z, 0 ≤ density center base z)
          (hD : 0 < selectedResidueDensityMass stride T widths (density center base)),
          ∀ (amplitude : (Option (LayerSamplerVariables G I n B) × X → ℝ) → ℂ),
            (∀ x, ‖amplitude x‖ ≤ 1) → ∀ {Lip : ℝ≥0}, LipschitzWith Lip amplitude →
              (Lip : ℝ) ≤ Real.exp P →
            ‖(∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
              ((selectedResidueDensityPMF stride T widths hwidths hZ
                (density center base) hD0 hD z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)) -
              ∑' z : Option (LayerSamplerVariables G I n B) × X → ℤ,
                ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
                  amplitude (fun t => (z t : ℝ) / widths t)‖ ≤
              6 * positiveProjectionAccuracy P := by
    obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
    have hp' (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (subtractConstant (c j).val (p j)) :=
      (hp j).subtractConstant _
    have hm' := fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)
    have hrank' (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j)
        (subtractConstant (c j).val (p j)) :=
      (hasLayerSamplingRank_subtractConstant_iff (by omega) _ _ _ _ _).mpr (hrank j)
    have h := hnormalization B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv
      hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP
      (fun j => subtractConstant (c j).val (p j)) hp' hm' stride hs hsP hW hWP hτ hτP hξ hξ1 hξP
      N hsize hrank' hRank T hT
    have heq := allocatedJointBaseDensity_subtractConstant_centered B U basis hb o hR hσ S p hm
      center c hc
    obtain ⟨hw, hZ, hraw, hnorm⟩ := h
    refine ⟨hw, hZ, ?_, ?_⟩
    · intro base amplitude hamp Lip hLip hLipP
      have hh := hraw base amplitude hamp hLip hLipP
      simpa only [density, ← heq, allocatedJointBaseDensity] using hh
    · intro base
      obtain ⟨hmass, _, _, _⟩ := hnorm base
      have hmass' : |selectedResidueDensityMass stride T widths (density center base) - 1| ≤
          3 * positiveProjectionAccuracy P := by
        dsimp only [density]
        rw [← heq]
        unfold allocatedJointBaseDensity
        exact hmass
      have hD0' : ∀ z, 0 ≤ density center base z := fun z =>
        allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center base z
      have hD' := (positiveProjectionAccuracy_normalizer hP hmass').2.2.1
      refine ⟨hmass', hD0', hD', ?_⟩
      intro amplitude hamp Lip hLip hLipP
      have hh := selectedResidueDensityPMF_error_of_bounded_test stride T widths hw hZ
        (density center base) hD0' hD'
        (fun z => amplitude (fun t => (z t : ℝ) / widths t)) (fun _ => hamp _)
        (ε := 3 * positiveProjectionAccuracy P)
        (by simpa only [density, ← heq, allocatedJointBaseDensity] using
          hraw base amplitude hamp hLip hLipP) hmass'
      exact hh.trans_eq (by ring)
  obtain ⟨hwidths, hZ, _, _⟩ := hcenter 0
  refine ⟨hwidths, hZ, ?_, ?_⟩
  · intro center base amplitude hamp Lip hLip hLipP
    obtain ⟨_, _, hraw, _⟩ := hcenter center
    exact hraw base amplitude hamp hLip hLipP
  · intro center base
    obtain ⟨_, _, _, hnorm⟩ := hcenter center
    exact hnorm base

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalZeroLayerBudgetedInitialization
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def unconditionedCommonSide {n : ℕ} (P : Fin n → ℕ) : ℕ := 1 + ∑ i, P i

@[simp] theorem unconditionedCommonSide_cast {n : ℕ} (P : Fin n → ℕ) :
    (unconditionedCommonSide P : ℝ) = 1 + unconditionedResidueSiteBound P := by
  simp [unconditionedCommonSide, unconditionedResidueSiteBound]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def unconditionedCommonSideScalarRatio (n : ℕ) : ℕ :=
  1 + n * unconditionedScalarPrimeRatio n

noncomputable def unconditionedCommonSideExtra (n : ℕ) : ℝ :=
  Real.log ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ)

@[simp] theorem exp_unconditionedCommonSideExtra (n : ℕ) :
    Real.exp (unconditionedCommonSideExtra n) = ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) := by
  exact Real.exp_log (by positivity)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

namespace CanonicalEmptyLayerGeometry

noncomputable def zeroLayerScale (G : Type) [Fintype G] (side : ℕ) (hside : 0 < side) :
    LayerSamplerScale (G := G) (B 0) (U 0) (b 0) (fun _ => 1) (fun _ => 1) :=
  emptyLayerSamplerScale (B 0) (U 0) (b 0) side hside (fun j => Fin.elim0 j)

@[simp] theorem zeroLayerScale_value (G : Type) [Fintype G] (side : ℕ) (hside : 0 < side) :
    (zeroLayerScale G side hside).value = side := rfl

end CanonicalEmptyLayerGeometry


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualCandidateSpatialCenter
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ stride cells center)

theorem path_base_abs_le (z : A.Path) (x : X) : |(z.1.val x : ℝ)| ≤ N x := by
  have hz := z.1.property
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hz
  have hax := (mem_integerBox _ _).mp ha x
  have hx := congrFun he x
  simp only [Pi.add_apply] at hx
  have hi : |z.1.val x| ≤ (N x : ℤ) := by
    rw [abs_of_nonneg (by omega : 0 ≤ z.1.val x)]
    omega
  exact_mod_cast hi

theorem path_spatial_center_mass_le_trim (z : A.Path) (x : X) :
    |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| / (N x : ℝ) + τ / 8 ≤
      1 + τ / 4 := by
  have hN : (0 : ℝ) < N x := by exact_mod_cast A.size_pos x
  have hnoise := rectangularWeightIndices_zero_bound
    (allocatedExternalCandidateWidths B U b S N τ ξ) z.2.property (none, x)
  have hnoise' : |(z.2.val (none, x) : ℝ)| ≤ τ * (N x : ℝ) / 8 := by
    simpa only [allocatedExternalCandidateWidths, narrowTrimmedSpatialWidths,
      trimmedSpatialWidths, centeredSpatialWidths, one_mul, mul_div_assoc] using hnoise
  have hcenter : |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| ≤
      (N x : ℝ) + τ * (N x : ℝ) / 8 := by
    simp only [jointIntegerFrame, Int.cast_add]
    exact (abs_add_le _ _).trans (add_le_add (A.path_base_abs_le z x) hnoise')
  have hnorm : |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| / (N x : ℝ) ≤
      1 + τ / 8 := by
    apply (div_le_iff₀ hN).mpr
    nlinarith
  linarith

theorem path_spatial_center_mass_le (hτ1 : τ ≤ 1) (z : A.Path) (x : X) :
    |(jointIntegerFrame (z.1.val, z.2.val) none x : ℝ)| / (N x : ℝ) + τ / 8 ≤ 2 := by
  have h := A.path_spatial_center_mass_le_trim z x
  linarith

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedEmptyLayerLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [Fintype X] in

@[simp] theorem allocatedCenteredJointDensity_empty_layers
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z = 1 := by
  exact canonicalCoefficientDensity_empty U b hb o _ _ _ _

variable (N : X → ℕ) (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedGeometryConditionalExcess
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m nX s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
    {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : Fin nX → ℕ} {poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : Fin nX → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride)}

namespace AllocatedExternalCandidateSamplerFamily

noncomputable local instance preparedConditionalExcessFinDecidableEq : DecidableEq (Fin nX) := Classical.decEq _

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

end AllocatedExternalCandidateSamplerFamily
end Erdos3.VectorPolynomial

end

end OAI

end


