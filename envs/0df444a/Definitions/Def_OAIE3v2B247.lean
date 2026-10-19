-- Prove2me | Definitions.Def_OAIE3v2B247
-- name    : OAIE3v2B247
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:05:27.885474+00:00
-- url     : https://prove2.me/theorems/144aacb5-e3d0-47c3-b76f-a10e28243ad0
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 252 of 311
-- statement:
--   Definitions bundle 252 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B301`, `OAIE3v2B230`, `OAIE3v2B232`, `OAIE3v2B233`, `OAIE3v2B235`, `OAIE3v2B236` of this split.
--
--   Modules: `Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`, `Estimates/AllocatedNarrowJointCollision.lean`, `Estimates/PreparedModularGeneralDetectorProductive.lean`, `Estimates/PreparedRelativeInitializerScalarInputs.lean`, `Lattices/AllocatedModularRankAffineProbability.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Sampling/ActualSlicedForecastLateData.lean`, `Sampling/AllocatedFixedScaleProductiveNarrowSampler.lean`, `Sampling/ForecastLawCenteredRecoveredKernel.lean`, `Sampling/ForecastPreparedScaleBudget.lean`, `Sampling/PreparedActualForecastSetup.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B301
import Definitions.Def_OAIE3v2B230
import Definitions.Def_OAIE3v2B232
import Definitions.Def_OAIE3v2B233
import Definitions.Def_OAIE3v2B235
import Definitions.Def_OAIE3v2B236

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem enlargedPreparedCommonSamplerBlock_positive (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    0 < Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlock, Fintype.card_fin] using
    (preparedCommonBlockCount_positive m a.1).trans_le (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlock_spectrum (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    max (positiveModerateSpectrumBlockCount a.1.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount a.1.val rows.card ((a.1.val + 1) * rows.card)) ≤
        Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlock, Fintype.card_fin] using
    (preparedCommonBlockCount_spectrum m a.1 ⟨s, Nat.lt_succ_of_le hs⟩).trans
      (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlock_uniform (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    uniformSpectrumBlockCount a.1.val rows.card ((a.1.val + 1) * rows.card) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) :=
  (le_max_right _ _).trans (enlargedPreparedCommonSamplerBlock_spectrum L Jalloc s hs a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

noncomputable def allocatedRankComponentSelectedEmbedding
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) :
    Fin L ↪ AllocatedRankComponentCoefficient (G := G) (B := B) inactive j o :=
  ⟨allocatedRankComponentSelectedSlot inactive spatial kernel block j o,
    allocatedRankComponentSelectedSlot_injective inactive spatial kernel block j o⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineProbability
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ} {R : Type*}

def allocatedSelectedNoiseOffset [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (residue : Option (LayerSamplerVariables G I n B) × X → R) :
    AllocatedCongruenceCoefficientIndex X E inactive L → R
  | ⟨_j,.inl x,l⟩ => residue (some (.inl (spatial l)),x.val)
  | ⟨_j,.inr _,_l⟩ => 0

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
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => Spatial × (Output → ℝ)

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

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedPhysicalDensityCRTNeZero
noncomputable def allocatedSlicedPhysicalResidueMean (g : Domain → ℝ) : ℂ :=
    let shortLaw := allocatedInactiveAffineIntervalLaw B U basis S HP stepP cP hinsideP hHP
    let coeff := allocatedOriginalSampleInactiveCoefficients B selected sample
    let φ := fun u rG rA => test (forecastInactiveShortGrid B U basis S selected coeff u)
      (allocatedJointResidueOutput B U basis S base integerFrame deck projection q rG
        (allocatedPrincipalResidueJoin B U basis S q u rA))
    shortLaw.complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ y, φ u (fun g => (cG g : ZMod q) + (stepG : ZMod q) * rG g)
            (fun j => (c j : ZMod q) + (stepG : ZMod q) * rA j) y
            ∂realDensityMeasure volume g)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNarrowJointCollision
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_joint_collision (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G Sites : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype G] [Fintype Sites] [DecidableEq Sites]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {P δ : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hSP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    (site : Sites → LayerSamplerVariables G I n B → ℤ) (_hsite : Function.Injective site)
    (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hroot : ∀ q, (∑ k, |(site q k : ℝ)|) ≤ W)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N stride : X → ℕ) (_hs : ∀ i, 0 < stride i) (_hsP : ∀ i, (stride i : ℝ) ≤ Real.exp P)
    (_hsize : ∀ i, Real.exp ((P + A)^A) ≤ (N i : ℝ))
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (hbases : bases.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
      (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U),
    let density := allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center
    ∀ (hD : 0 < selectedJointDensityMass bases stride cells widths density),
    1/2 ≤ selectedJointDensityMass bases stride cells widths density →
    (selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass density
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hD).mean
      (fun z => noninjectivityIndicator
        (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val))) ≤ δ := by
  obtain ⟨A₁, _, hcollisionBudget⟩ := exists_allocatedFixedScaleCollisionLog_bound m
  obtain ⟨A, hA, hbudget⟩ := exists_narrow_sampler_threshold 0 A₁
  refine ⟨A, hA, ?_⟩
  intro X G Sites _ _ _ _ _ _ I _ n B _ J _ U b hb o R σ hR hσ S _
    C V hC hV hσ1 Cinv hCinv hchart hsmall P δ hP hm hK hRP hσP hcount hI hn hJ
    hAP hSP hCP hVP poly hmem site hsite hδ hδP W τ ξ hW hWP hroot
    hτ hτP hξ hξ1 hξP N stride hs hsP hsize cells hcells bases hbases
    widths hwidths hmass center density hD hlower
  let P' := spatialSamplingBudget (2*P)
  have hPP' : P ≤ P' := by dsimp [P', spatialSamplingBudget]; linarith
  have hP' : 0 ≤ P' := hP.trans hPP'
  have hexp := Real.exp_le_exp.mpr hPP'
  obtain ⟨_, hcut, hlargeLog⟩ := hbudget P hP
  have hlarge i : Real.exp (10*P+128) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hlargeLog).trans (hsize i)
  have hN i : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hlarge i)
  obtain ⟨hρ, hρP, hwidth⟩ := narrow_sampler_width_bounds (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    hP hW hWP hτ hτP hξ hξ1 hξP N hN
  have hscale := narrow_sampler_residue_scale (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    hP hW hWP hτ hτP hξ hξ1 hξP N stride hs hsP hAP hlarge
  let i : X := Classical.choice inferInstance
  apply allocatedFixedScaleJoint_collision_small B U b hb o hR hσ S C V hC hV hσ1
    Cinv hCinv hchart hsmall
    (fun a z => coefficientConstantCenter U center + affineSampleCoefficientTorus U poly hmem
      (fun k v => (jointIntegerFrame (a,z) k v : ℝ)))
    hP' (hm.trans hPP') (hK.trans hPP')
    (fun j => (hRP j).trans hexp) (fun j => (hσP j).trans hexp)
    (fun j => (hcount j).trans hPP') (fun j => (hI j).trans hPP')
    (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
    (hAP.trans hexp) (hSP.trans hexp) (fun j => (hCP j).trans hexp) (fun j => (hVP j).trans hexp)
    bases hbases site hsite i hδ (hδP.trans hexp)
    (fun q k => ((Finset.single_le_sum (fun j _ => abs_nonneg (site q j : ℝ))
      (Finset.mem_univ k)).trans (hroot q)).trans (hWP.trans hexp))
    stride hs ((hsP i).trans hexp) cells hcells widths hwidths hmass hscale hρ
    (hρP.trans (Real.exp_le_exp.mpr (le_spatialSamplingBudget hP')))
    ((Real.exp_le_exp.mpr (hcollisionBudget P' hP')).trans
      ((Real.exp_le_exp.mpr hcut).trans (hsize i)))
    (fun k => hwidth (some k,i))
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hD hlower

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem enlargedPreparedCommonSamplerBlock_single_uniform (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    uniformSpectrumBlockCount a.1.val 1 (a.1.val + 1) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  have hrows : 1 ≤ (boundedBooleanJetRows (Fin 1) (a.1.val + 1)).card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    refine ⟨∅, ?_⟩
    simp only [mem_boundedBooleanJetRows, Finset.card_empty, Nat.zero_le]
  apply le_trans _ (enlargedPreparedCommonSamplerBlock_uniform L Jalloc 0
    (Nat.zero_le m) a)
  unfold uniformSpectrumBlockCount majorArcSpectrumExponent majorArcCoverExponent
  gcongr
  simpa only [mul_one] using Nat.mul_le_mul_left (a.1.val + 1) hrows

theorem enlargedPreparedCommonSamplerBlock_four (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    4 ≤ Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  apply le_trans _ (enlargedPreparedCommonSamplerBlock_single_uniform L Jalloc a)
  unfold uniformSpectrumBlockCount majorArcSpectrumExponent majorArcCoverExponent
    majorArcErrorExponent
  simp only [mul_one]
  omega

theorem enlargedPreparedCommonSamplerBlock_transverse_uniform (Jalloc : ℕ)
    (j : Fin m) (i : Fin (preparedSamplerTransverse L j)) :
    uniformSpectrumBlockCount j.val 1 (j.val + 1) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc ⟨j, Sum.inr i⟩) :=
  enlargedPreparedCommonSamplerBlock_single_uniform L Jalloc ⟨j, Sum.inr i⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

theorem layerSampler_block_sum_le_principal_card {m : ℕ}
    (I : Fin m → Type*) [∀ j, Fintype (I j)] (n : Fin m → ℕ)
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] :
    (∑ a, Fintype.card (B a)) ≤
      Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) :=
  principalTupleIndex_block_sum_le_card B (layerSamplerDegree I n)
    (fun _ => Nat.succ_le_succ (Nat.zero_le _))

theorem enlargedPreparedCommonSampler_block_sum_le_principal_card
    {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m) (Jalloc : ℕ) :
    (∑ a, Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a)) ≤
      Fintype.card (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock L Jalloc)
        (layerSamplerDegree (PreparedSamplerContinuous L) (preparedSamplerTransverse L))) :=
  layerSampler_block_sum_le_principal_card (PreparedSamplerContinuous L)
    (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualSlicedForecastLateData
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact : Type*} [Fintype Vact] [DecidableEq Vact]
variable {X : Type*} [Fintype X]
variable {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)

local instance slicedSeparateTailCharOrderNeZero (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFixedScaleProductiveNarrowSampler
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_fixedScale_productive_joint_measure (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedFixedScaleProductiveStatement m A := by
  obtain ⟨A₁, _, hmarginal⟩ := exists_allocated_fixedScale_joint_marginal m
  obtain ⟨A₂, _, hcollision⟩ := exists_allocated_narrow_joint_collision m
  let A := max (max A₁ A₂) 256
  have hA : 256 ≤ A := le_max_right _ _
  have hA₁ : A₁ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hA₂ : A₂ ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨A, by omega, ?_⟩
  intro X G _ _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density
  have hthreshold (a : ℕ) (ha : a ≤ A) :
      Real.exp ((P + a) ^ a) ≤ Real.exp ((P + A) ^ A) := by
    have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
    have har : (a : ℝ) ≤ A := by exact_mod_cast ha
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by positivity)
      (by linarith only [har] : P + (a : ℝ) ≤ P + A) a).trans
      (pow_le_pow_right₀ (by linarith only [hP, hAr] : (1 : ℝ) ≤ P + A) ha)
  obtain ⟨hN, hwidths, hmargin, hmass, hD, hnormal, hmarginal⟩ :=
    hmarginal B U basis S hb o μ ν hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall
      hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm
      stride hs hsP hW hWP hτ hτP hτhalf hξ hξ1 hξP N
      (fun i => (hthreshold A₁ hA₁).trans (hsize i)) hrank
      ((hthreshold A₁ hA₁).trans hRank) T hT
  refine ⟨hN, hwidths, hmargin, hmass, hD, ?_⟩
  intro law
  refine ⟨hnormal, ?_⟩
  intro Sites _ _ _ site hsite hrootSum test htest gain hgain hbad herror hscore productive joint
  have hroot q k : |(site q k : ℝ)| ≤ Real.exp P :=
    ((Finset.single_le_sum (fun j _ => abs_nonneg (site q j : ℝ))
      (Finset.mem_univ k)).trans (hrootSum q)).trans hWP
  have hmarg q := hmarginal (site q) (hroot q) (hrootSum q)
    (fun x => (test x : ℂ))
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using htest x)
  have hmeanCast : (𝔼 x ∈ integerBox N, (test (fun i => (x i : ℝ)) : ℂ)) =
      ((𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)) : ℝ) : ℂ) := by
    simp only [Finset.expect_eq_sum_div_card, Complex.ofReal_div,
      Complex.ofReal_sum, Complex.ofReal_natCast]
  have hprod := allocatedCenteredJoint_productivity B U basis hb o hR hσ S p hm μ
    bases (trimmedIntegerBox_nonempty N _ hmargin) stride T widths hwidths hmass hD
    site (fun x => test (fun i => (x i : ℝ))) hgain herror hscore
    (fun x => (le_abs_self _).trans (htest _))
    (fun q => by
      simpa only [jointIntegerPhysicalSite_cast, hmeanCast] using hmarg q)
    (fun center => (hcollision B U basis hb o hR hσ S C V hC hV hσ1 Cinv hCinv hchart hsmall
      hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hm site hsite
      (Real.exp_pos (-P)) (by simpa only [← Real.exp_neg, neg_neg] using
        (le_rfl : Real.exp P ≤ Real.exp P))
      hW hWP hrootSum hτ hτP hξ hξ1 hξP N stride hs hsP
      (fun i => (hthreshold A₂ hA₂).trans (hsize i)) T hT bases
      (trimmedIntegerBox_nonempty N _ hmargin) hwidths hmass center (hD center)
      (hnormal center).2.1.1).trans hbad)
  refine ⟨hprod.1, hprod.2.1, hprod.2.2.1, hprod.2.2.2, ?_⟩
  have hmarginSize i : 4 ≤ τ * (N i : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((spatial_threshold_large hP hA).trans (hsize i))
  intro z q
  exact narrow_jointIntegerPhysicalSite_mem_box hW hτ hτhalf hξ1 (site q)
    (hrootSum q) N hN hmarginSize z

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorProductive
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def preparedModularGeneralProductivityExponent (m : ℕ) : ℕ :=
  Classical.choose (exists_allocated_fixedScale_productive_joint_measure.{0,0,0,0,0,0} m)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeInitializerScalarInputs
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {m s D nX : ℕ}

noncomputable abbrev preparedRelativeInitializerVariableCount
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (s M : ℕ) : ℕ :=
  Fintype.card (LayerSamplerVariables
    (EnlargedPreparedCommonKernel (max m s)
      (modularInitialBlockCount (max m s) (nX + max m s * M)))
    (PreparedSamplerContinuous (prep.pad (max m s)))
    (preparedSamplerTransverse (prep.pad (max m s)))
    (EnlargedPreparedCommonSamplerBlock (prep.pad (max m s))
      (modularInitialBlockCount (max m s) (nX + max m s * M))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawCenteredRecoveredKernel
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "kernel" => forecastLawRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

variable {d : ℕ} (e : Fin d ≃ Σ j, J j) (c : (Σ j, J j) → ℝ)

def centeredTagPullback (f : ((Σ j, J j) → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun y => f (fun a => y (e.symm a) + c a)

noncomputable def forecastLawCenteredRecoveredKernel
    (v : X → ℝ) (r : X → ZMod N) (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ :=
  centeredTagPullback e c (kernel v r (fun a => β (e.symm a))) y

end Erdos3.VectorPolynomial

end

end OAI
end


