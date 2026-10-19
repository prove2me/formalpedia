-- Prove2me | Definitions.Def_OAIE3v2B254
-- name    : OAIE3v2B254
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:23:41.763382+00:00
-- url     : https://prove2.me/theorems/66d4baf9-9a0f-41f5-9ae7-d597ad08ab1e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 260 of 311
-- statement:
--   Definitions bundle 260 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B244`, `OAIE3v2B245`, `OAIE3v2B246` of this split.
--
--   Modules: `Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`, `Estimates/AllocatedCanonicalUniformCoarseSource.lean`, `Estimates/AllocatedCenteredMeasurableBadTail.lean`, `Linear/AllocatedCenteredMeasurableFramedBadTail.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Sampling/AllocatedExternalLocalGoodForecastPath.lean`, `Sampling/AllocatedRetainedActualForecastFactory.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B244
import Definitions.Def_OAIE3v2B245
import Definitions.Def_OAIE3v2B246

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem allocatedRankComponentCoefficientSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) :
    Function.Injective
      (allocatedRankComponentCoefficientSlot (G := G) (X := X) (E := E) (B := B) inactive) := by
  rintro ⟨⟨j, o⟩, q⟩ ⟨⟨k, p⟩, r⟩ he
  cases o with
  | inl x =>
    cases p with
    | inl y =>
      have hjk : j = k := Fin.ext (x.property.trans y.property.symm)
      subst k
      have hp : (q, x.val) = (r, y.val) := Sum.inl.inj he
      have hxy : x = y := Subtype.ext (congrArg Prod.snd hp)
      subst y
      have hqr : q = r := congrArg Prod.fst hp
      subst r
      rfl
    | inr p => cases p <;> cases he
  | inr o =>
    cases p with
    | inl y => cases o <;> cases he
    | inr p =>
      cases o with
      | inl i =>
        cases p with
        | inl t =>
          have hh := Sum.inl.inj (Sum.inr.inj he)
          have hjk : j = k := congrArg Sigma.fst hh
          subst k
          have hp : (q, i) = (r, t) := by
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and,
              AllocatedRankComponentCoefficient] using hh
          have hit : i = t := congrArg Prod.snd hp
          subst t
          have hqr : q = r := congrArg Prod.fst hp
          subst r
          rfl
        | inr a => cases he
      | inr a =>
        cases p with
        | inl t => cases he
        | inr b =>
          have hh := Sum.inr.inj (Sum.inr.inj he)
          have haxis : (⟨j, .inr a.val⟩ : LayerSamplerAxis I n) = ⟨k, .inr b.val⟩ :=
            congrArg Sigma.fst hh
          have hjk : j = k := congrArg Sigma.fst haxis
          subst k
          have hab : a = b := Subtype.ext (by
            apply Sum.inr.inj
            exact eq_of_heq (Sigma.mk.inj haxis).2)
          subst b
          have hqr : q = r := eq_of_heq (Sigma.mk.inj hh).2
          subst r
          rfl

def allocatedRankComponentCoefficientEmbedding
    (inactive : LayerSamplerAxis I n → Prop) :
    AllocatedRankComponentCoefficientIndex G X I E n B inactive ↪
      AllocatedActualCoefficientIndex G X I E n B :=
  ⟨allocatedRankComponentCoefficientSlot inactive,
    allocatedRankComponentCoefficientSlot_injective inactive⟩

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

local instance slicedNativeRecoveredCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

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

local instance slicedCompleteRecoveredCoverNeZero : NeZero W.cover := ⟨W.cover_pos.ne'⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalUniformCoarseSource
namespace OAI

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

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredMeasurableBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (center : C → ∀ j, U j) (hcenter : Measurable center)
variable (base : Ω → X → ℤ)
variable (noise : Ω → Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (law : C → FiniteProbabilityWeights Ω)
variable (read : C → Ω → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hcertificate : ∀ c x, 0 < (law c).weight x →
  AllocatedPhysicalRankReadCertificate B U bW b hb o
    (fun j => translate (fun v => (base x v : ℝ)) (subtractConstant (center c j).val (poly j)))
    (fun j => coefficients_translate_mem (U j) (fun v => (base x v : ℝ)) _
      (coefficients_subtractConstant_mem (U j) (center c j) (poly j) (hm j)))
    inactive spatial kernel block rankC (noise x) (read c x))
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

include hcenter hcertificate in

theorem exists_allocatedCentered_badProduct_surrogate :
    ∃ test : Set (C × Ω), MeasurableSet test ∧ ∀ c x, 0 < (law c).weight x →
      (cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p (read c x) ↔
      (c,x) ∈ test) := by
  let surrogate : Ω → ℕ → ℕ → C → Prop := fun x p a c =>
    if hp : p ∈ P then
      let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
      allocatedPhysicalPrimePowerEvent B U bW b hb o
        (fun j => translate (fun v => (base x v : ℝ)) (subtractConstant (center c j).val (poly j)))
        (fun j => coefficients_translate_mem (U j) (fun v => (base x v : ℝ)) _
          (coefficients_subtractConstant_mem (U j) (center c j) (poly j) (hm j)))
        inactive rankC (noise x) p a
    else False
  have hsurrogate (x : Ω) (p : ℕ) (hp : p ∈ P) (a : ℕ) :
      MeasurableSet {c | surrogate x p a c} := by
    let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
    simp only [surrogate, dif_pos hp]
    exact allocatedPhysicalPrimePowerEvent_center_measurableSet B U bW b hb o poly hm
      inactive rankC center hcenter (base x) (noise x) p a
  let test : Set (C × Ω) := {z | cutoff <
    ∏ p ∈ P, p ^ largestTestedBadDepth A (surrogate z.2) p z.1}
  refine ⟨test, ?_, ?_⟩
  · apply centeredFinite_event_measurableSet
    intro x
    exact largestBadPrimeProduct_tail_measurableSet P A (surrogate x)
      (fun p hp a _ => hsurrogate x p hp a) cutoff
  · intro c x hx
    have heq : (∏ p ∈ P, p ^ largestTestedBadDepth A
        (fun p a c => allocatedActualPrimeBad inactive spatial kernel block P rankC p a (read c x)) p c) =
        ∏ p ∈ P, p ^ largestTestedBadDepth A (surrogate x) p c := by
      apply largestBadPrimeProduct_congr_on_tested
      intro p hp a _ _
      let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
      simp only [surrogate, dif_pos hp]
      have hactual := allocatedActualPrimeBad_iff_modulusBad inactive spatial kernel block P rankC
        ⟨p,hp⟩ a (read c x)
      exact hactual.trans ((hcertificate c x hx).primePowerEvent_iff B U bW b hb o _ _
        inactive rankC spatial kernel block p a).symm
    change (cutoff < _) ↔ (cutoff < _)
    exact congrArg (fun v : ℕ => cutoff < v) heq |>.to_iff

include hcenter hcertificate in

theorem allocatedCentered_badProduct_probability_le
    (μ : Measure C) [IsProbabilityMeasure μ]
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    {ε : ℝ} (hbound : ∀ c, (law c).mean (fun x =>
      if cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p (read c x)
      then (1 : ℝ) else 0) ≤ ε) :
    (centeredFiniteProbabilityMeasure μ law).real {z | cutoff < ∏ p ∈ P,
      p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
        p (read z.1 z.2)} ≤ ε := by
  obtain ⟨test, htest, heq⟩ := exists_allocatedCentered_badProduct_surrogate B U bW b hb o
    poly hm inactive spatial kernel block rankC center hcenter base noise law read hcertificate P A cutoff
  apply centeredFiniteProbabilityMeasure_real_event_le_of_support μ law hweight _ test htest heq
  intro c
  convert hbound c using 1
  apply congrArg (law c).mean
  funext x
  simp only [Set.mem_ofPred_eq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (center : C → ∀ j, U j) (hcenter : Measurable center)
variable (base : Ω → X → ℤ)
variable (noise : Ω → Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (law : C → FiniteProbabilityWeights Ω)
variable (read : C → Ω → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hcertificate : ∀ c x, 0 < (law c).weight x →
  AllocatedPhysicalRankReadCertificate B U bW b hb o
    (fun j => translate (fun v => (base x v : ℝ)) (subtractConstant (center c j).val (poly j)))
    (fun j => coefficients_translate_mem (U j) (fun v => (base x v : ℝ)) _
      (coefficients_subtractConstant_mem (U j) (center c j) (poly j) (hm j)))
    inactive spatial kernel block rankC (noise x) (read c x))
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

include hcenter hcertificate in

theorem exists_allocatedCentered_badProduct_measurable_tail
    (μ : Measure C) [IsProbabilityMeasure μ]
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    {ε : ℝ} (hbound :
      (centeredFiniteProbabilityMeasure μ law).real {z | cutoff < ∏ p ∈ P,
        p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
          p (read z.1 z.2)} ≤ ε) :
    ∃ bad : Set (C × Ω), MeasurableSet bad ∧
      (centeredFiniteProbabilityMeasure μ law).real bad ≤ ε ∧
      (∀ c x, 0 < (law c).weight x →
        (cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p (read c x) ↔
        (c,x) ∈ bad)) ∧
      {z | cutoff < ∏ p ∈ P,
        p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
          p (read z.1 z.2)} =ᵐ[centeredFiniteProbabilityMeasure μ law] bad := by
  obtain ⟨bad, hbad, heq⟩ := exists_allocatedCentered_badProduct_surrogate B U bW b hb o
    poly hm inactive spatial kernel block rankC center hcenter base noise law read hcertificate P A cutoff
  have hae : {z | cutoff < ∏ p ∈ P,
      p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
        p (read z.1 z.2)} =ᵐ[centeredFiniteProbabilityMeasure μ law] bad :=
    (centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight).mono
      (fun z hz => propext (heq z.1 z.2 hz))
  refine ⟨bad, hbad, ?_, heq, hae⟩
  simpa only [measureReal_def, measure_congr hae] using hbound

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable [Fintype X]

theorem allocatedReplaceReadNoise_primeBad
    (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = integerBaseTranslation base + z)
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p d : ℕ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p d (allocatedReplaceReadNoise B z f) =
      allocatedActualPrimeBad inactive spatial kernel block P C p d f := by
  rw [allocatedReplaceReadNoise_eq_jointFrame B base z f hf]
  exact allocatedJointFrameRead_rankBad inactive spatial kernel block P C p d (-base) f

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
variable (hc : Measurable c)
variable (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
  (Option (LayerSamplerVariables G I n B) × X → ℤ) → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
  (Option (LayerSamplerVariables G I n B) × X → ℤ) → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
  inactive spatial kernel block rankC center (c center) a (sample center a) (read center a))
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
variable (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells width
  (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center))
local notation "jointLaw" => (fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hZ
  (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
  (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center))
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U)) [IsProbabilityMeasure μ]
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

include hc hread in

theorem exists_allocatedCentered_measurable_unframed_bad_tail
    {ε : ℝ} (hbound : (centeredFiniteProbabilityMeasure μ jointLaw).real
      {z | cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
        (read z.1 z.2.1.val z.2.2.val)} ≤ ε) :
    ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 width 1)),
      MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ jointLaw).real bad ≤ ε ∧
      ∀ center x, 0 < (jointLaw center).weight x →
        (cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
          (read center x.1.val x.2.val) ↔ (center,x) ∈ bad) := by
  have hweight := allocatedCentered_joint_weight_measurable B U b hb o S hR hσ poly hm
    stride cells width hwidth hZ bases hbases hD
  have hcertificate := allocatedCentered_joint_positive_rankCertificate B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block rankC c sample read hread stride cells width hwidth hZ bases hbases hD
  obtain ⟨bad, hbad, hmassbad, heq, _⟩ := exists_allocatedCentered_badProduct_measurable_tail
    (C := CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (Ω := bases × rectangularWeightIndices 0 width 1) B U bW b hb o poly hm inactive spatial kernel block rankC c hc
    (fun x => x.1.val) (fun x => x.2.val) jointLaw
    (fun center x => read center x.1.val x.2.val) hcertificate P A cutoff μ hweight hbound
  exact ⟨bad, hbad, hmassbad, heq⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalLocalGoodForecastPath
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedRetainedActualForecastFactory
namespace OAI

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

variable (z : A.Path) (centerLift : ∀ j, U j)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      centerLift z.1.val z.2.val sample f)
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (Pdim gainLog Qstride : ℝ)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime) (depth : ℕ → ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth depth
        (allocatedActualPrimeBad (allocatedShortAxis (I := I) U b S.value)
          spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p f) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card X) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hdet : ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : X => spatialMatrixNormalizedEntries e A.widths z.2.val (t,j,i))|)

noncomputable def allocatedRecoveredGoodForecastPath :
    ActualFixedSpatialForecastPath (Eout := E) B U b S hR hσ Dmod spatial kernel block
      (spatialTwoBlockEquiv e) (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      S.value N τ 1 (preparedCenteredForecastSpatialLog Pdim)
      (2 * Fintype.card X * Qstride +
        (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11) 0 := by
  let commonTuple : G → IntegerScalarCubeBox Empty S.value :=
    fun _ _ => ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  have hnoise : z.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 := by
    simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
      using z.2.property
  exact preparedCenteredGoodActualForecastPath B U b S hR hσ hb o poly hm
    Dmod spatial kernel block e N τ ξ 1 Pdim
    ((Pdim + preparedCenteredForecastThresholdExponent) ^ preparedCenteredForecastThresholdExponent)
    0 gainLog Qstride z.1.val z.2.val centerLift sample f hrecovered
    commonTuple primes hprime depth (fun _ => 0) (fun _ _ => 0) stride hgood (by simp)
    (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => by norm_num) hPdim hX hvars A.trim_pos A.narrow_pos A.size_pos
    hnoise hnX hgainLog hstride
    (preparedCenteredForecast_threshold_inverse hPdim hnX hX hgainLog hgainDim)
    (by simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq] using hdet)

variable {Selected : Type}
    {selected : Selected → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := E)
      B U b S Dmod selected τ δslice)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ setup.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ setup.Pbad)

noncomputable def allocatedRecoveredGoodForecastPathForSetup :
    ActualFixedSpatialForecastPath (Eout := E) B U b S hR hσ Dmod spatial kernel block
      (spatialTwoBlockEquiv e) (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      S.value N τ 1 setup.P setup.Pbad 0 :=
  (allocatedRecoveredGoodForecastPath z centerLift sample f hrecovered Dmod spatial kernel block e Pdim gainLog Qstride
    primes hprime depth hgood hPdim hX hvars hnX hgainLog hgainDim hstride hdet).enlargeBudgets
    hPmodel hPbad le_rfl

end Erdos3.VectorPolynomial

end

end OAI
end


