-- Prove2me | Definitions.Def_OAIErdos3B206
-- name    : OAIErdos3B206
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T11:34:52.798295+00:00
-- url     : https://prove2.me/theorems/7bd4c75f-5c32-4f67-be5f-6834f5224824
-- title:
--   OpenAI Erdős-3 split, definitions bundle 207 of 207
-- statement:
--   Definitions bundle 207 of 207 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B205`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 207 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.allocatedSlicedPhysicalAmbientGridError`, `OAI.Erdos3.allocatedFixedPathSlicedAmbientFloorLog`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B167

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Active" => {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Output" => (Σ _a : Active, Unit)

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
variable {Cidx : Type*}
variable (selected : Cidx → Σ j : Fin m, Fin (n j))
variable (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U basis S.value) j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ}
variable (hV : gridVolume ≠ 0)
variable (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℂ)
variable {Kφ : ℝ≥0}
variable (htest : ∀ grid residue, LipschitzWith Kφ (test grid residue))
variable (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Output" => (Σ _a : Active, Unit)

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)

local notation "sides" => allocatedPrincipalSides B U basis S

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
  (allocatedLayerWidths B U basis S j)
  (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (hbox : ∀ a, 0 < box a) {τ : ℝ} (hτ : τ ≠ 0)
variable (q : ℕ) [NeZero q] (hm : 0 < m)
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)






variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)
variable (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ) (stepG : ℕ)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
  Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (S.value : ℤ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

noncomputable def allocatedFixedPathSlicedAmbientFloorLog
    (d : ℕ) (D P V cost E Pg PR : ℝ) : ℝ :=
  max (D + 2 * P + V + cost + E + 32)
    (forecastJointGridSamplerLog d Pg (E + 4) V PR + 1)

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Output" => (Σ _a : Active, Unit)

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)


variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)






end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Output" => (Σ _a : Active, Unit)

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample

variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)






local notation "actualLaw" => principalAffineIntervalLaw B degree
  (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP
local notation "actualActive" => (fun _ : Original => crtPolynomialInputLaw primes exponent
  (fun l => padicValNat (primes l) stepG) hcoprime
  (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l))))
local notation "actualOutput" => (fun v : Original => integerLongPolynomialOutput
  (allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) projection)
  (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) Ncrt)

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
variable (radius : ℝ≥0) (hradius0 : 0 < radius) (hradius3 : (3 : ℝ) ≤ radius)
variable (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
variable (chartCap : Fin m → ℝ) (hchartCap : ∀ j, 0 ≤ chartCap j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
  chartCap j * ‖v‖)
variable (hchartBudget : ∀ j, chartCap j * (((Fintype.card (I j) : ℝ) + 1) *
  (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ box i ≤ box i)
variable (htrimbase : base ∈ trimmedIntegerBox box (spatialTrimMargin τ box))
variable (hVpos : 0 < gridVolume)
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hX : (Fintype.card X : ℝ) ≤ Pambient)
variable (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (box i : ℝ))
  Rrank (U j) (nativePoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
variable (hPdecay : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) + 2 : ℕ) : ℝ) ≤ Pdecay)


variable (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U basis R S.value box τ j ≤ δgrid)

noncomputable def allocatedSlicedPhysicalAmbientGridError : ℝ :=
  let lowerG := fun g => (cG g : ℝ) / S.value
  let widthG := fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value
  let frame := allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame
  let hwGne := fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive
    (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))
  let slicedFrame := fixedSpatialKernelSliceFrame budget (S.value : ℝ) frame lowerG widthG
  let h0slice := fixedSpatialKernelBlock_slice_det_ne_zero e budget (S.value : ℝ) frame
    lowerG widthG false h0 hwGne
  let h1slice := fixedSpatialKernelBlock_slice_det_ne_zero e budget (S.value : ℝ) frame
    lowerG widthG true h1 hwGne
  let hδP : 0 < δ / 2 := div_pos hδ (by norm_num)
  let Cgrid := fixedSpatialOriginalForecastCap B
    (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ) slicedFrame true h1slice) hδP
  let Lgrid := fixedSpatialOriginalForecastLip B
    (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ) slicedFrame false h0slice)
    (fixedSpatialKernelBlockEquiv e budget (S.value : ℝ) slicedFrame true h1slice) hδP
  forecastJointGridError (Fintype.card Out)
    (Fintype.card (X ⊕ AllocatedActiveIntegerAxis U basis S.value))
    (Fintype.card (Σ j, I j)) cutoff D Lgrid Cgrid Knative δgrid

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Output" => (Σ _a : Active, Unit)

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample

variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)






local notation "actualLaw" => principalAffineIntervalLaw B degree
  (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP
local notation "actualActive" => (fun _ : Original => crtPolynomialInputLaw primes exponent
  (fun l => padicValNat (primes l) stepG) hcoprime
  (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l))))
local notation "actualOutput" => (fun v : Original => integerLongPolynomialOutput
  (allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) projection)
  (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) Ncrt)

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
variable (radius : ℝ≥0) (hradius0 : 0 < radius) (hradius3 : (3 : ℝ) ≤ radius)
variable (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
variable (chartCap : Fin m → ℝ) (hchartCap : ∀ j, 0 ≤ chartCap j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
  chartCap j * ‖v‖)
variable (hchartBudget : ∀ j, chartCap j * (((Fintype.card (I j) : ℝ) + 1) *
  (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ box i ≤ box i)
variable (htrimbase : base ∈ trimmedIntegerBox box (spatialTrimMargin τ box))
variable (hVpos : 0 < gridVolume)
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hX : (Fintype.card X : ℝ) ≤ Pambient)
variable (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (box i : ℝ))
  Rrank (U j) (nativePoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
variable (hPdecay : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) + 2 : ℕ) : ℝ) ≤ Pdecay)


variable (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U basis R S.value box τ j ≤ δgrid)

end Erdos3.VectorPolynomial

end

end OAI

end


