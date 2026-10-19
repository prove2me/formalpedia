-- Prove2me | Definitions.Def_OAIE3v2B232
-- name    : OAIE3v2B232
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:26:48.668531+00:00
-- url     : https://prove2.me/theorems/752c50b7-cad8-422b-805b-645f045847e5
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 237 of 311
-- statement:
--   Definitions bundle 237 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B206`, `OAIE3v2B210`, `OAIE3v2B211`, `OAIE3v2B212`, `OAIE3v2B213` of this split.
--
--   Modules: `Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`, `Lattices/AllocatedAffineFixedPathRationalReference.lean`, `Lattices/ForecastNativeResidueTest.lean`, `Lattices/NativePairAffineCellStepDrop.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Probability/AllocatedFixedPathSlicedPhysicalDensityComparison.lean`, `Sampling/ForecastNativeJointTestBudget.lean`, `Sampling/ForecastPreparedScaleBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B206
import Definitions.Def_OAIE3v2B210
import Definitions.Def_OAIE3v2B211
import Definitions.Def_OAIE3v2B212
import Definitions.Def_OAIE3v2B213

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

abbrev EnlargedPreparedCommonSamplerBlock (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :=
  Fin (preparedCommonBlockCount m a.1 + Jalloc)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastNativeResidueTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical Matrix

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

noncomputable def forecastNativeCoordinateResidue (q : ℕ)
    (frozen : ∀ j, {i : Fin (n j) // inactive ⟨j, .inr i⟩} → ℤ)
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod q)
    (j : Fin m) : Fin (n j) ⊕ E j → ZMod q :=
  Sum.elim (forecastNativeSheetResidue inactive q frozen out j)
    (forecastNativeFreeDeckResidue inactive out j)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

noncomputable def forecastNativeAmbientDeckResidue (q : ℕ) [NeZero q]
    (frozen : ∀ j, {i : Fin (n j) // inactive ⟨j, .inr i⟩} → ℤ)
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod q) :
    (Σ j, J j) → ZMod q := fun a =>
  (integerResidueMatrix (forecastNativeDeckResidueMatrix U b hb bW q a.1) q *ᵥ
    forecastNativeCoordinateResidue inactive q frozen out a.1) a.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ) (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E P)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {L : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)

noncomputable def forecastResidueTest (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (sheet : ∀ j, {i : Fin (n j) // P ⟨j, .inr i⟩} → ℤ)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (center : X → ℝ) (τ : ℝ) (out : Out → ZMod q) : Domain → ℂ :=
  W.forecastPullback U b o R P
    (zmodPiReduction hperiod (forecastNativeSpatialResidue P hm out))
    (zmodPiReduction hcover (forecastNativeAmbientDeckResidue P U b hb bW q sheet out))
    center τ frozen

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativeJointTestBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)
local notation "short" => allocatedShortAxis (I := I) U b Lsize
local notation "Grid" => AllocatedShortIntegerAxis U b Lsize →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

noncomputable def forecastShortGridTest (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (center : X → ℝ) (τ : ℝ) (grid : Grid) (out : Out → ZMod q) : Domain → ℂ :=
  W.forecastResidueTest U b hb o bW R short q hm hperiod hcover
    (forecastShortGridSheet U b Lsize grid)
    (forecastShortGridNormalized U b Lsize R grid) center τ out

end NormalizedPolynomialTwist

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < (allocatedPrincipalSides B U basis S) j)
variable (hH : ∀ j, 0 < H j)

noncomputable def allocatedInactiveAffineIntervalLaw
    (H step : (PrincipalTupleIndex B (layerSamplerDegree I n)) → ℕ) (start : (PrincipalTupleIndex B (layerSamplerDegree I n)) → ℤ)
    (hinside : ∀ j (t : Fin (H j)),
      0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < (allocatedPrincipalSides B U basis S) j)
    (hH : ∀ j, 0 < H j) : FiniteProbabilityWeights (PrincipalAxisTuples (α := Empty) (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)) :=
  principalAffineIntervalAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step start hinside hH (allocatedShortAxis (I := I) U basis S.value)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "AI" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

variable (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (deck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis short j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)

noncomputable def allocatedJointResidueOutput
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ) (rG : G → ZMod q)
    (r : FullInput → Option Empty → ZMod q) : Out → ZMod q :=
  fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
    (Sum.elim (Sum.elim rG (fun j : AI => r ⟨j.1.val, j.2⟩ none))
      (fun k => r k.1 k.2)) (allocatedForecastPolynomial short base noise deck projection o)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFixedPathSlicedPhysicalDensityComparison
namespace OAI

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

local notation "degree" => layerSamplerDegree I n
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "FullInput" => PrincipalTupleIndex B degree

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]

noncomputable def allocatedFixedPathKernelFrame (τ ξ : ℝ) (box : X → ℕ)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    Option G × X → ℝ :=
  (fun k => (integerFrame k : ℝ) /
    narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box k) ∘
      canonicalZeroSpatialKernelEmbedding G FullInput X

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

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
local notation "Domain" => Spatial × (Output → ℝ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
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

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedPhysicalDensityCRTNeZero
noncomputable def allocatedSlicedPhysicalForecastDensity : Domain → ℝ :=
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (stepG : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    fixedSpatialKernelSliceOriginalForecastDensity B U basis S e budget
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) (fun g => (cG g : ℝ) / S.value)
      (fun g => (stepG : ℝ) * ((HG g - 1 : ℕ) : ℝ) / S.value) h0 h1
      (fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive
        (show (0 : ℤ) < stepG by exact_mod_cast hstepG) (hHG g))) hB lower width sample

noncomputable def allocatedSlicedPhysicalRationalMean (g : Domain → ℝ) : ℂ :=
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let poly := allocatedForecastPolynomial short base integerFrame deck projection
    (∑' grid, 𝔼 residue : Out → ZMod Ncrt,
        ((rationalInactiveForecast
          (principalAffineIntervalLaw B degree (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP)
          (fun _ => crtPolynomialInputLaw primes exponent
            (fun l => padicValNat (primes l) stepG) hcoprime
            (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l))))
          (forecastInactiveFixedOutput B U basis S selected coeff xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) Ncrt)
          Ncrt gridVolume grid residue / gridVolume : ℝ) : ℂ) *
        ∫ y, test grid (fun j => ZMod.castHom hqN (ZMod q) (residue j)) y
          ∂realDensityMeasure volume g)

noncomputable def allocatedSlicedPhysicalComparisonError : ℝ :=
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ((∑ j, (q : ℝ) / H j) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ j, (q : ℝ) / H j + K * ε) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) * ∑ g, (q : ℝ) / HG g + (Kφ : ℝ) * ξ

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop
namespace OAI

universe u

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ τ ι : Type*}

theorem pairOrbitSymbol_scalarAffine_substitute
    (p : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (q : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (r : ℚ) (shift : σ → ℚ) :
    pairOrbitSymbol D E
      (D.filtration.realification.polynomialOrbitSubstitute
        (scalarAffinePolynomial r shift) (scalarAffinePolynomial_support r shift) p)
      (E.filtration.realification.polynomialOrbitSubstitute
        (scalarAffinePolynomial r shift) (scalarAffinePolynomial_support r shift) q) b ω hF =
      (pi (pairModels D E)).filtration.realPolynomialSymbolDilationHom (fun _ => 1) r
        (pairOrbitSymbol D E p q b ω hF) := by
  apply NilpotentLieBCHGroup.ext
  change (pi (pairModels D E)).filtration.realSymbolOfPolynomial b ω hF (fun _ => 1)
      (pairOrbit D E _ _).log =
    (pi (pairModels D E)).filtration.realPolynomialSymbolDilation (fun _ => 1) r
      ((pi (pairModels D E)).filtration.realSymbolOfPolynomial b ω hF (fun _ => 1)
        (pairOrbit D E p q).log)
  rw [pairOrbit_substitute_log, VectorPolynomial.substitute_scalarAffinePolynomial]
  apply NilpotentLieFiltration.realSymbolOfPolynomial_affine
  · exact fun _ => Nat.zero_lt_one
  · exact (pairOrbit D E p q).adapted

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

theorem pairOrbitSymbol_scalarAffinePullback
    (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (r : ℚ) (shift : σ → ℚ) :
    pairOrbitSymbol D E (V.scalarAffinePullback r shift).orbit
      (W.scalarAffinePullback r shift).orbit b ω hF =
      (pi (pairModels D E)).filtration.realPolynomialSymbolDilationHom (fun _ => 1) r
        (pairOrbitSymbol D E V.orbit W.orbit b ω hF) :=
  pairOrbitSymbol_scalarAffine_substitute D E V.orbit W.orbit b ω hF r shift

theorem pairOrbitSymbol_scalarAffinePullback_inverse_stride
    (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (Q : ℕ) (hQ : 0 < Q) (shift : σ → ℚ) :
    (pi (pairModels D E)).filtration.realPolynomialSymbolDilationHom (fun _ => 1) ((Q : ℚ)⁻¹)
      (pairOrbitSymbol D E (V.scalarAffinePullback Q shift).orbit
        (W.scalarAffinePullback Q shift).orbit b ω hF) =
      pairOrbitSymbol D E V.orbit W.orbit b ω hF := by
  rw [pairOrbitSymbol_scalarAffinePullback]
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieFiltration.realPolynomialSymbolDilationHom_coord,
    ← NilpotentLieFiltration.realPolynomialSymbolDilation_mul,
    inv_mul_cancel₀ (show (Q : ℚ) ≠ 0 by exact_mod_cast hQ.ne'),
    NilpotentLieFiltration.realPolynomialSymbolDilation_one]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

universe v

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]

variable [Fintype ι] {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (j : ι)

theorem optionPairProjection_layer_surjective (k : ℕ) (x : PairAlgebra L₀ (L j))
    (hx : x ∈ (pi (pairModels D₀ (D j))).filtration.layer k) :
    ∃ y ∈ (optionProduct D₀ D).filtration.layer k, optionPairProjection j y = x := by
  classical
  let y : ∀ i : Option ι, optionLieSpace L₀ L i
    | none => x true
    | some i => Pi.single (M := L) j (x false) i
  refine ⟨y, ?_, ?_⟩
  · apply (mem_pi_layer (fun i => (optionFactors D₀ D i).filtration) k y).mpr
    intro i
    cases i with
    | none =>
      exact (mem_pi_layer (fun b => (pairModels D₀ (D j) b).filtration) k x).mp hx true
    | some i =>
      by_cases hij : i = j
      · subst i
        change Pi.single (M := L) j (x false) j ∈ (D j).filtration.layer k
        erw [Pi.single_eq_same]
        exact (mem_pi_layer (fun b => (pairModels D₀ (D j) b).filtration) k x).mp hx false
      · change Pi.single (M := L) j (x false) i ∈ (D i).filtration.layer k
        erw [Pi.single_eq_of_ne hij]
        exact Submodule.zero_mem _
  · funext b
    cases b
    · exact Pi.single_eq_same (M := L) j (x false)
    · rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {J : Type*} [Fintype J] {L : Type u} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))

theorem optionPairProjection_native_logHeight (j : J)
    (x : ∀ i : Option J, optionLieSpace L M i) {p : ℝ}
    (hx : ∀ k, rationalLogHeight ((optionProduct D E).basis.repr x k) ≤ p) :
    ∀ k, rationalLogHeight ((pi (pairModels D (E j))).basis.repr
      (optionPairProjection j x) k) ≤ p := by
  intro k
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ b : Bool, Fin (Bool.rec (d j) d₀ b))).symm k = z
  rcases z with ⟨b, i⟩
  cases b
  · change rationalLogHeight ((E j).basis.repr (x (some j)) i) ≤ p
    exact (congrArg rationalLogHeight
      (productFinBasis_repr_component (optionFactors D E) x (some j) i)).le.trans (hx _)
  · change rationalLogHeight (D.basis.repr (x none) i) ≤ p
    exact (congrArg rationalLogHeight
      (productFinBasis_repr_component (optionFactors D E) x none i)).le.trans (hx _)

theorem optionPairProjection_adapted_logHeight {α β : Type*}
    (j : J) (e : Basis α ℚ (∀ i : Option J, optionLieSpace L M i))
    (b : Basis β ℚ (PairAlgebra L (M j))) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ i : Bool, Fin (Bool.rec (d j) d₀ i)) : ℝ) ≤ p)
    (he : ∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ p)
    (hb : ∀ i k, rationalLogHeight (b.repr ((pi (pairModels D (E j))).basis i) k) ≤ p) :
    ∀ i k, rationalLogHeight (b.repr (optionPairProjection j (e i)) k) ≤ (p + 3) ^ 4 := by
  intro i k
  have hp' : 0 ≤ p + 1 := by linarith
  have hcoord := rational_basis_coordinates_logHeight (pi (pairModels D (E j))).basis b
    hp' (by simpa only [Fintype.card_fin] using hdim.trans (show p ≤ p + 1 by linarith))
    (ceil_exp_le_exp_add_one hp)
    (fun i k => rationalHeightLE_ceil_exp (hb i k)) (optionPairProjection j (e i))
    (fun k => (optionPairProjection_native_logHeight D E j (e i) (he i) k).trans
      (by linarith)) k
  convert hcoord using 1
  ring

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end


