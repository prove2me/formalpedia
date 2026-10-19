-- Prove2me | Definitions.Def_OAIE3v2B291
-- name    : OAIE3v2B291
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:52:14.574954+00:00
-- url     : https://prove2.me/theorems/2f4bbec6-5b2e-4b13-bda2-75c58eb01b0b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 304 of 311
-- statement:
--   Definitions bundle 304 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B283`, `OAIE3v2B284`, `OAIE3v2B286`, `OAIE3v2B287` of this split.
--
--   Modules: `Estimates/PreparedCanonicalInitializedRelativeSource.lean`, `Estimates/PreparedCanonicalRelativeEndpointBounds.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeLongCommonFactors.lean`, `Sampling/PreparedCenteredShortForecastGoodInterface.lean`, `Sampling/SharedWidthPreparedShortForecastSourceModelAttachment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B283
import Definitions.Def_OAIE3v2B284
import Definitions.Def_OAIE3v2B286
import Definitions.Def_OAIE3v2B287

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredShortForecastGoodInterface
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedShortForecastProductiveRequired (m : ℕ)
    (Pmaster Plate E B0 Pgood Pprod : ℝ) : ℝ :=
  let r := preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m 0) 1 Pmaster Plate
  max (max r.required ((max r.Pproj E + preparedCenteredMarginalExponent m) ^
    preparedCenteredMarginalExponent m))
    (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
      ((Pprod + preparedModularGeneralProductivityExponent m) ^
        preparedModularGeneralProductivityExponent m))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SharedWidthPreparedShortForecastSourceModelAttachment
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m)
local notation "kernel" => EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))
local notation "blocks" => EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))
local notation "axes" => PreparedSamplerContinuous prep
local notation "transverse" => preparedSamplerTransverse prep
local notation "coords" => (fun j : Fin m => RankPreparationLayer.Coord (prep j))
variable (U : ∀ j, Submodule ℝ (coords j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (transverse j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := kernel) (I := axes) (n := transverse) (J := coords) blocks U b R σ)
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (0 + 1) ↪ kernel) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ u p forecastCap : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (axes j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

def SharedWidthPreparedCenteredShortForecastGoodModelInterface
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 gainLog gain Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) : Prop := by
  exact SharedWidthPreparedCenteredForecastModelExtensionInterface
    (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (μ := μ)
    (Good := PreparedCenteredShortForecastGoodProperty (m := m) (nX := nX) (M := M) prep U b S bW hb o hR hσ μ
      stride gainLog gain Qgood spatialEmbedding)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    (preparedCenteredShortForecastGoodRequired m B0 Pgood)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m)
local notation "kernel" => EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))
local notation "blocks" => EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))
local notation "axes" => PreparedSamplerContinuous prep
local notation "transverse" => preparedSamplerTransverse prep
local notation "coords" => (fun j : Fin m => RankPreparationLayer.Coord (prep j))
variable (U : ∀ j, Submodule ℝ (coords j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (transverse j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := kernel) (I := axes) (n := transverse) (J := coords) blocks U b R σ)
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (0 + 1) ↪ kernel) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ u p forecastCap : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (axes j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

structure SharedWidthPreparedCenteredShortForecastGoodBounds
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (u p forecastCap : ℝ)
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget : ℝ)
    (B0 Vlog gainLog gain Pwidth P₀ Pgood : ℝ) (Qgood : ℕ) (D : ℝ) : Prop where
  hcert : PreparedShortCertifiedSameScaleBadProductInterface (nX := nX) (M := M) prep U b S B0 (gainLog + 8) Vlog Qgood
  hnX : 0 < nX
  hσ1 : ∀ j, σ j ≤ 1
  hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4
  hMaster : 0 ≤ Pmaster
  hLate : Pmaster ≤ Plate
  hd : AllocatedComparisonDimensions (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (Fin (0 + 1)) (fun j : Fin m => (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1) : Type)) D
  hD : D ≤ Pmaster
  hnMaster : (nX : ℝ) ≤ Pmaster
  hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster
  hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate
  hS : (S.value : ℝ) ≤ Real.exp Plate
  hchartB : Pchart ≤ B0
  hprojection : (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).Pproj ≤ Pwidth
  hphysical : jointPhysicalBaseLog Pwidth (gainLog + 8) Vlog ≤ B0
  hVlog : 0 ≤ Vlog
  hQexp : (Qgood : ℝ) ≤ Real.exp Vlog
  hP₀ : 0 ≤ P₀
  hnP₀ : (nX : ℝ) ≤ P₀
  hgP₀ : gainLog ≤ P₀
  hcutoffP : (P₀ + preparedCenteredShortForecastSpatialExponent m) ^
      preparedCenteredShortForecastSpatialExponent m ≤ Pgood
  hBP : B0 ≤ Pgood
  hwidthP : Pwidth ≤ Pgood
  hg : 0 ≤ gainLog
  hgP : gainLog + 8 ≤ Pgood
  hgain : Real.exp (-gainLog) ≤ gain
  hstrideWidth : Qstride ≤ Pwidth
  hτWidth : Pphysical ≤ Pwidth
  hξWidth : Plate ≤ Pwidth

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalRelativeEndpointBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def preparedFiniteNestedSourceRequiredLog
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (M count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ) : ℝ :=
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
  let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
  let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision A Cdirect constants
    (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k) gainLog stageLog
  let modelLog := fun k : K => preparedFiniteForwardWork A constants
    (preparedFiniteNestedForwardAllDegreeStage k).val
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k)
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
  let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
  let detectionGain := fun k : K => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k : K => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (detectionGain k + pDetect k + 4)
  let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
  let Eprofile := fun k : K => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let Prho := fun k : K => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (Eprofile k) (pDetect k + 2) + 2
  let Ptail := fun k : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (Eprofile k) (pDetect k + 2)
  let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
  let Tmod := fun k : K => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengthLogs := fun k : K => allocatedAffineLengthLog m D Pscale (Prho k) (Pk k)
    (target k) (pDetect k + 2) (Tmod k)
  let Pseed := allocatedScaleLog (Pscale + ∑ k, lengthLogs k + Pmin + 1)
  let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
  let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
  let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
  let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
    (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
  let Econditional := preparedFiniteNestedSourceProjectionPrecision
    (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := cutoff)
    m G count nX A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate endpoint
  let baseB0 := preparedUniformDegreeProductiveCertificateBudget
    M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
  let Pwidth := 4 * (Plate + 8) ^ 2
  let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
  let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent m)
    baseB0 Bstruct Pwidth gainLog Vlog
  let anchorRequired := preparedFiniteScheduleAnchorGoodRequired
    m (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
  let conditionalRequired := preparedConditionalExcessRequired m Plate Econditional
  let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m (degree k)) (degree k + 1) (Pmaster k) Plate).required
  let Rreq := preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff Bstruct
    anchorRequired conditionalRequired detectorRequired
  Rreq

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalInitializedRelativeSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def preparedFiniteNestedSourceLiteralRequired
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (M count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ) : ℝ :=
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
  let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
  let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision A Cdirect constants
    (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k) gainLog stageLog
  let modelLog := fun k : K => preparedFiniteForwardWork A constants
    (preparedFiniteNestedForwardAllDegreeStage k).val
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k)
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
  let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
  let detectionGain := fun k : K => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k : K => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (detectionGain k + pDetect k + 4)
  let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
  let Eprofile := fun k : K => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let Prho := fun k : K => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (Eprofile k) (pDetect k + 2) + 2
  let Ptail := fun k : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (Eprofile k) (pDetect k + 2)
  let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
  let Tmod := fun k : K => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengthLogs := fun k : K => allocatedAffineLengthLog m D Pscale (Prho k) (Pk k)
    (target k) (pDetect k + 2) (Tmod k)
  let Pseed := allocatedScaleLog (Pscale + ∑ k, lengthLogs k + Pmin + 1)
  let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
  let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
  let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
  let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
    (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
  let native : K → ℝ := fun k =>
    (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m (degree k))
      (degree k + 1) (Pmaster k) Plate).nativeBudget
  let Econditional := preparedNestedFrontProjectionEnvelope A constants innerDepth
    (fun k : K => k.1.val) (fun k : K => k.2.1.val) native
    Bstruct gainLog stageLog endpoint
  let baseB0 := preparedUniformDegreeProductiveCertificateBudget
    M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
  let Pwidth := 4 * (Plate + 8) ^ 2
  let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
  let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent m)
    baseB0 Bstruct Pwidth gainLog Vlog
  let anchorRequired := preparedFiniteScheduleAnchorGoodRequired
    m (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
  let conditionalRequired := preparedConditionalExcessRequired m Plate Econditional
  let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m (degree k)) (degree k + 1) (Pmaster k) Plate).required
  let Rreq := preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff Bstruct
    anchorRequired conditionalRequired detectorRequired
  Rreq

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeLongCommonFactors
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

theorem exists_allocatedExternalCandidateSpatialNativeFamily_long_common_factors
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C Cbasis K T : ℕ, 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

    {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip),
    ∀ {qVertical : ℝ}, pNative ≤ qVertical → pLocal + r + 1 ≤ qVertical →
      verticalDecompositionBudget qVertical ≤ p →
      r + verticalDecompositionBudget qVertical + 2 ≤ p →
    ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
      (∀ a ∈ H, ∀ j, Real.exp (-r) ≤ ‖F.correlation a j‖) →
    ∀ {α : Type*} [Fintype α] {pGeo bnd : ℝ},
      0 ≤ pGeo → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (F.native j).model)).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
      (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight
        ((optionProduct D (fun j => (F.native j).model)).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := jointCost + (jointCost + K) ^ K
    ∀ (keepLong : LayerSamplerVariables G I n B → Prop),
      (∀ i, keepLong i → keep i) →
    ∀ [Nonempty {i // keepLong i}], (Fintype.card {i // keepLong i} : ℝ) ≤ bnd →
      (∀ i : {i // keepLong i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keepLong i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let qCommon := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      F.LongCommonFactors keepLong outer H e ω hF qVertical qCommon := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedExternalCandidateTaggedPairFamily_long_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Ω Pivot _ _ LG LM _ _ _ _ _ _ _ _ d₀ t D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget outer H hH hcorr
    α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he
    localCost jointCost P keepLong hLongSub _ hkeep hlong hcommonLong
  obtain ⟨retained, hretSub, hretPos, hretMass, selected,
    _hchart, _hcandidate, _hreference, _htwist, heta, _hambient, hjoint⟩ :=
    F.exists_taggedPairFamily outer H hH hpq hprecision hfrequency hbudget hcorr
  have hselectedCommon := hcommon (A := A) (D := D)
    (E := fun j => (F.native j).model) (H := retained) hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF
    hstructure he outer hretPos selected keepLong hLongSub hkeep hlong hcommonLong
  obtain ⟨W, v, den, H', hsub, hpos, hmass, hspan, hgraded, hheight, hzero,
    hden, hdenBound, hfactor⟩ := hselectedCommon
  refine ⟨selected.θ, W, v, den, H', fun a ha => hretSub (hsub ha), hpos,
    ?_, hspan, hgraded, hheight, ?_, hden, hdenBound, ?_⟩
  · apply compose_exponential_mass_losses_p1 (hsecond := hmass)
    simpa only [neg_mul] using hretMass
  · simpa only [heta] using hzero
  · intro a ha
    have hj : selected.extendedLongJointOrbit keepLong a = F.longJointOrbit keepLong a := by
      rw [selected.extendedLongJointOrbit_mem keepLong a (hsub ha)]
      unfold AllocatedExternalCandidateTaggedPairFamily.longJointOrbit
        AllocatedExternalCandidateSpatialNativeFamily.longJointOrbit
      rw [hjoint ⟨a, hsub ha⟩]
      rfl
    simpa only [hj] using hfactor a ha

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

noncomputable section

theorem exists_allocatedExternalCandidateSpatialNativeFamily_actual_adapted_long_quotient_factors
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C Cbasis K T : ℕ, 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

    {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip),
    ∀ {qVertical : ℝ}, pNative ≤ qVertical → pLocal + r + 1 ≤ qVertical →
      verticalDecompositionBudget qVertical ≤ p →
      r + verticalDecompositionBudget qVertical + 2 ≤ p →
    ∀ (H : Finset A.Path), 0 < A.law.mass H →
      (∀ a ∈ H, ∀ j, Real.exp (-r) ≤ ‖F.correlation a j‖) →
    ∀ {α : Type*} [Fintype α] {pGeo bnd : ℝ},
      0 ≤ pGeo → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (F.native j).model)).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
      (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight
        ((optionProduct D (fun j => (F.native j).model)).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := jointCost + (jointCost + K) ^ K
    ∀ (keepLong : LayerSamplerVariables G I n B → Prop),
      (∀ i, keepLong i → keep i) →
    ∀ [Nonempty {i // keepLong i}], (Fintype.card {i // keepLong i} : ℝ) ≤ bnd →
      (∀ i : {i // keepLong i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keepLong i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let qCommon := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
    ∀ (sourceCenter : ∀ j, U j)
      (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
      (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
      (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      (scoreThreshold : ℝ)
      (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)
      (js : List Pivot) {dQ : ℕ}
      (Q : RationalFilteredNilmanifold
        (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
      (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
      (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0)
      (descended : (X → ℤ) → Q.Space → ℂ)
      (hrecovery : ∀ x (g : D.RealGroup),
        descended x (QuotientGroup.mk
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
          observable x (QuotientGroup.mk g))
      (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)
      {height : ℕ} {pProj : ℝ},
      (∀ i j, RationalHeightLE
        (adapted.basis.repr
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) (e j)) i) height) →
      0 ≤ pProj → qCommon ≤ pProj →
      (Fintype.card α : ℝ) ≤ pProj →
      (finrank ℚ (∀ i : Option Pivot,
        optionLieSpace (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js)
          (fun j => (F.native j).L) i) : ℝ) ≤ pProj →
      (height : ℝ) ≤ Real.exp pProj →
      F.ActualAdaptedPivotQuotientLongFactors keepLong H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
        qVertical qCommon pProj := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedExternalCandidateSpatialNativeFamily_long_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Pivot _ LG LM _ _ _ _ _ _ _ _ d₀ D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget H hH hcorr
    α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he
    localCost jointCost P keepLong hLongSub _ hkeep hlong hcommonLong qCommon
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore
    js dQ Q hQ hker descended hrecovery adapted height pProj hentries hpProj hqProj
    hsource htarget hheight
  have hc : F.LongCommonFactors keepLong A.law H e ω hF qVertical qCommon :=
    hcommon F hpq hprecision hfrequency hbudget A.law H hH hcorr
      hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he keepLong hLongSub hkeep hlong hcommonLong
  exact hc.toActualAdaptedPivotQuotientLongFactors F keepLong H sourceCenter hpath hcenter hfrozen
    observable weight scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
    hentries hpProj hqProj hsource htarget hheight

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

noncomputable section

theorem exists_allocatedExternalCandidateSpatialNativeFamily_native_long_geometry_factors
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ Cgeometry C Cbasis K T : ℕ, 2 ≤ Cgeometry ∧ 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

    {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip),
    ∀ {qVertical : ℝ}, pNative ≤ qVertical → pLocal + r + 1 ≤ qVertical →
      verticalDecompositionBudget qVertical ≤ p →
      r + verticalDecompositionBudget qVertical + 2 ≤ p →
    ∀ (H : Finset A.Path), 0 < A.law.mass H →
      (∀ a ∈ H, ∀ j, Real.exp (-r) ≤ ‖F.correlation a j‖) →
    ∀ (pGeometry : ℝ), 2 ≤ pGeometry → D.GeometryComplexityLE pGeometry →
      pNative ≤ pGeometry → (Fintype.card Pivot : ℝ) ≤ pGeometry →
    ∀ (js : List Pivot) {dQ : ℕ}
      (Q : RationalFilteredNilmanifold
        (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
      (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
      (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0),
      Q.GeometryComplexityLE pGeometry →
      (∀ i j, rationalLogHeight
        (Q.basis.repr (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)
          (D.basis j)) i) ≤ pGeometry) →
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + p + 2
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := jointCost + (jointCost + K) ^ K
    ∀ (keepLong : LayerSamplerVariables G I n B → Prop)
      (_hLongSub : ∀ i, keepLong i → keep i) [Nonempty {i // keepLong i}],
      (∀ i : {i // keepLong i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keepLong i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let qCommon := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
    ∀ (sourceCenter : ∀ j, U j)
      (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
      (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
      (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      (scoreThreshold : ℝ)
      (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)
      (descended : (X → ℤ) → Q.Space → ℂ)
      (hrecovery : ∀ x (g : D.RealGroup),
        descended x (QuotientGroup.mk
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
          observable x (QuotientGroup.mk g)),
      ∃ geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
          (optionProduct Q (fun j => (F.native j).model))
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)))
          jointGeo adaptedBudget,
        F.ActualAdaptedPivotQuotientLongFactors keepLong H sourceCenter hpath hcenter hfrozen observable weight
          scoreThreshold hscore geometry.source.basis geometry.source.weight geometry.source.layers
          js Q hQ hker descended hrecovery geometry.target qVertical qCommon pProj := by
  obtain ⟨Cgeometry, hCgeometry, hgeometry⟩ := exists_native_adapted_map_geometry
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hfactor⟩ :=
    exists_allocatedExternalCandidateSpatialNativeFamily_actual_adapted_long_quotient_factors s hs
  refine ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Pivot _ LG LM _ _ _ _ _ _ _ _ d₀ D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget H hH hcorr
    pGeometry hpGeometry hD hpNative hPivot js dQ Q hQ hker hQGeometry hmap
    pGeo jointGeo adaptedBudget bnd localCost jointCost P keepLong hLongSub _ hlong hcommonLong qCommon pProj
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore descended hrecovery
  have hpGeometry0 : 0 ≤ pGeometry := (by norm_num : (0 : ℝ) ≤ 2).trans hpGeometry
  have hnative (j : Pivot) : (F.native j).model.GeometryComplexityLE pGeometry :=
    (F.native j).complexity.1.mono (F.native j).model hpNative
  have hpGeo : 0 ≤ pGeo := by dsimp [pGeo]; positivity
  have hjointGeo : 0 ≤ jointGeo := by dsimp [jointGeo]; positivity
  have hGeometryJoint : pGeometry ≤ jointGeo := by dsimp [jointGeo]; nlinarith
  have hsourceGeo := optionProduct_geometry D (fun j => (F.native j).model)
    hpGeometry0 hPivot hD hnative
  have htargetGeo := optionProduct_geometry Q (fun j => (F.native j).model)
    hpGeometry0 hPivot hQGeometry hnative
  have hmapJoint := optionMarkedLieMap_native_logHeight D Q
    (fun j => (F.native j).model)
    (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) hpGeometry0 hmap
  obtain ⟨geometry⟩ := hgeometry
    (optionProduct D (fun j => (F.native j).model))
    (optionProduct Q (fun j => (F.native j).model))
    (optionMarkedLieMap (L := fun j => (F.native j).L)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)))
    hjointGeo hsourceGeo htargetGeo (fun i j => (hmapJoint j i).trans hGeometryJoint)
  refine ⟨geometry, ?_⟩
  have hpair (j : Pivot) : (pi (pairModels D (F.native j).model)).GeometryComplexityLE pGeo := by
    apply pi_geometry _ hpGeometry0
    · simpa only [Fintype.card_bool, Nat.cast_ofNat] using hpGeometry
    · intro k
      cases k
      · exact hnative j
      · exact hD
  have hadapted : 0 ≤ adaptedBudget := geometry.budget_nonneg
  have hpow : 0 ≤ (pGeo + 3) ^ 5 := by positivity
  have hbnd : 0 ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]
  have habnd : adaptedBudget ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]
  have hpbnd : p ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0]
  have hgbnd : jointGeo + 1 ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]
  have hLongCard : (Fintype.card {i // keepLong i} : ℝ) ≤ p := by
    have hcard : Fintype.card {i // keepLong i} ≤ Fintype.card {i // keep i} :=
      Fintype.card_le_of_injective
        (fun i : {i // keepLong i} => (⟨i.val, hLongSub i.val i.property⟩ : {i // keep i}))
        (fun _ _ h => Subtype.ext (congrArg (fun i : {i // keep i} => i.val) h))
    exact (Nat.cast_le.mpr hcard).trans F.hK
  have hsourceDim : (Fintype.card (Fin (finrank ℚ
      (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))) : ℝ) ≤ bnd := by
    simpa only [Fintype.card_fin] using geometry.source_dimension.trans (by linarith only [hgbnd] : jointGeo ≤ bnd)
  have hProj : 0 ≤ pProj :=
    add_nonneg (add_nonneg (le_max_right qCommon 0) hadapted) zero_le_one
  have hqProj : qCommon ≤ pProj :=
    (le_max_left qCommon 0).trans
      ((le_add_of_nonneg_right hadapted).trans (le_add_of_nonneg_right zero_le_one))
  have haProj : adaptedBudget ≤ pProj :=
    (le_add_of_nonneg_left (le_max_right qCommon 0)).trans
      (le_add_of_nonneg_right zero_le_one)
  have hJointProj : jointGeo ≤ pProj :=
    (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)).trans
      (geometry.forward_budget.trans haProj)
  exact hfactor F hpq hprecision hfrequency hbudget H hH hcorr
    (α := Fin (finrank ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i)))
    (pGeo := pGeo) (bnd := bnd) hpGeo hbnd hpair
    (by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp])
    (by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]) hsourceDim
    (hPivot.trans (by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]))
    geometry.source.basis geometry.source.weight geometry.source.layers
    (fun i j k => (geometry.source_structure i j k).trans habnd)
    (fun i k => (geometry.source_forward i k).trans hgbnd)
    keepLong hLongSub (hLongCard.trans hpbnd) hlong hcommonLong
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore
    js Q hQ hker descended hrecovery geometry.target
    (height := geometry.entries_height) (pProj := pProj) geometry.entries hProj hqProj
    (by simpa only [Fintype.card_fin] using geometry.source_dimension.trans hJointProj)
    (geometry.target_dimension.trans hJointProj)
    (geometry.entries_bound.trans (Real.exp_le_exp.mpr haProj))

end

end Erdos3.VectorPolynomial

end

end OAI
end


