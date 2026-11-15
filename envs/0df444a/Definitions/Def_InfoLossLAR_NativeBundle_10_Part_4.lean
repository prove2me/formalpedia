-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_10_Part_4
-- name    : InfoLossLAR_NativeBundle_10_Part_4
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:17:20.833251+00:00
-- url     : https://prove2.me/theorems/18ef7912-7fd6-4100-9e67-ae090b846091
-- title:
--   Flag charts, public shifts, and sparse cycle evaluation
-- statement:
--   This package defines binary flag metadata and masks, marked arrays and finite-response coordinates, public flag weights and draws, safe chart and branch data, public shift programs, sparse cycle evaluation, Gaussian window and edge draws, root signed-mass and scalar-average programs.
--
--   These are stored finite data and their constructor and interpretation APIs. They keep the actual binary or rational computation distinct from its ideal real semantics; later theorems establish approximation and platform running-time guarantees. The smaller compilation unit preserves entire original source modules and introduces no assumed transport or lattice-reduction result.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0. Original source units Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagBinary, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagBinaryCost, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagBinaryMasks, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagBinaryMetadata, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagCompletion, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagMarkedArray, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagFiniteResponse, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagFiniteCoordinates, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagTargetNorm, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagPublicProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagIdealArrays, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagWeightArray, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagReferenceSupport, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagWeightCost, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagBranchDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagJointDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagChartDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentPublicShiftProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinarySparseCycleEvaluation, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryCycleTest, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinarySparseCycleSemantic, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinarySparseCycleAverage, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentWindowDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentEdgeDrawProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootSignedMass, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryScalarAverage. Exact syntax-oracle source spans, body hashes and closed scope wrappers recorded in compact_heavy_split/manifest.json. Source SHA256 96e0e7f1676203a7bdcbd11392c2f9b2d140928953365f66afa251a6342db4e5.

import Definitions.Def_InfoLossLAR_NativeBundle_10_Part_3

section




















/-!
# Binary-rational simultaneous flag repair

The line mask excludes all protected zero-first-coordinate inputs.  The
deletion matrix and every iterate are stored arrays; the program uses the
existing Boolean-list arithmetic and sequential mask/vector scans.
-/

namespace CurrentAFT.CurrentFlagBinary

open AFT AFT.RationalNumerics AFT.BoundaryCalibration AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators

def defectTerm {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts)
    (point : Fin charts) (index : Fin features) : RationalResult :=
  let onLine := readVector false line index
  if onLine.value then ⟨zero, onLine.work + 2⟩ else
    let term := chartProjectionTerm feature allowed spike point index
    ⟨term.data, onLine.work + term.work + 2⟩



def defect {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
  sumFin features (defectTerm feature allowed line spike point)





def targetEntry {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (atom : RationalBits) (spike : Vector RationalBits charts)
    (point : Fin charts) : RationalResult :=
  let remaining := difference one atom
  let odds := quotient atom remaining.data
  let offLine := defect feature allowed line spike point
  let correction := multiply odds.data offLine.data
  let result := difference one correction.data
  ⟨result.data, remaining.work + odds.work + offLine.work + correction.work + result.work + 5⟩



def maskedEntry {charts : ℕ} (safe : Vector Bool charts) (profile : Vector RationalBits charts)
    (point : Fin charts) : RationalResult :=
  let active := readVector false safe point
  if active.value then
    let value := readVector zero profile point
    ⟨value.value, active.work + value.work + 2⟩
  else ⟨zero, active.work + 2⟩



def regular {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (safe fiber : Vector Bool charts) (atom : RationalBits) (steps : ℕ) :
    ArrayResult charts :=
  let spike := buildArray charts (chartSpike fiber)
  let matrix := chartDeletionMatrix feature allowed safe
  let rhs := buildArray charts (targetEntry feature allowed line atom spike.data)
  let raw := iteration matrix.data rhs.data steps
  let result := buildArray charts (maskedEntry safe raw.data)
  ⟨result.data, spike.work + matrix.work + rhs.work + raw.work + result.work + 5⟩



end CurrentAFT.CurrentFlagBinary

end

section


















/-! Literal bit-operation and rational-height bounds for all-line flag repair. -/

namespace CurrentAFT.CurrentFlagBinary

open AFT AFT.RationalNumerics AFT.BoundaryCalibration AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1200000

def defectHeight (charts colors features spikeBits : ℕ) : ℕ :=
  features * (chartFeatureHeight charts colors spikeBits + 1)

def targetHeight (charts colors features atomBits spikeBits : ℕ) : ℕ :=
  2 * atomBits + defectHeight charts colors features spikeBits + 2

def defectTermWork (charts colors features spikeBits : ℕ) : ℕ :=
  featureWork charts colors spikeBits + 12 * features + charts + colors + 13

def offLineWork (charts colors features spikeBits : ℕ) : ℕ :=
  finiteSumWork features (chartFeatureHeight charts colors spikeBits)
    (defectTermWork charts colors features spikeBits)

def targetWork (charts colors features atomBits spikeBits : ℕ) : ℕ :=
  offLineWork charts colors features spikeBits +
    7 * primitiveWorkBound (targetHeight charts colors features atomBits spikeBits) + 11















def storedHeight (charts colors features atomBits : ℕ) : ℕ :=
  chartProjectionHeight charts colors features 0 + targetHeight charts colors features atomBits (2 * charts)

def iterateHeight (charts colors features atomBits steps : ℕ) : ℕ :=
  steps * ((3 * (charts ^ 2 + charts) + 1) * storedHeight charts colors features atomBits + charts + 1)

def regularWork (charts colors features atomBits steps : ℕ) : ℕ :=
  (charts * (spikeWork charts + 2) + 2) + deletionMatrixWork charts colors features +
    (charts * (targetWork charts colors features atomBits (2 * charts) + 2) + 2) +
    (steps * iterationWorkStep charts (storedHeight charts colors features atomBits) steps + 2 * charts + 2) +
    (charts * (6 * charts + 10) + 2) + 5





end CurrentAFT.CurrentFlagBinary

end

section

























/-!
# Explicit masks for the current marked chart fiber

The public marked chart fixes its base and sets its shear to zero.  Only
nonzero-first-coordinate protected inputs constrain its scale.  These are
actual sequential Boolean tests, with no support-membership oracle.
-/

namespace CurrentAFT.CurrentFlagBinaryMasks

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 400000

def onLine (cutoff : ℕ) (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) : CountedValue Bool :=
  let doubled := doubleCounter cutoff
  let source := divideCounter index.val doubled.count.succ
  let result := equalCounter source.quotient cutoff
  ⟨result.value, doubled.work + source.work + result.work + 3⟩



def onLineWork (cutoff : ℕ) : ℕ :=
  let count := (2 * cutoff + 1) * (2 * cutoff + 1)
  3 * cutoff + 1 + 500 * (count + (2 * cutoff + 1) + 2) ^ 2 + 3 * (count + cutoff) + 5



def offLineAllowed {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (point : Fin charts) (index : Fin features) : CountedValue Bool :=
  let active := readVector false line index
  let permitted := chartAllowedAt feature allowed point index
  ⟨active.value || permitted.value, active.work + permitted.work + 2⟩



def fiberAt {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (base scale shear : Vector (Fin colors) charts)
    (mark : Fin colors) (point : Fin charts) : CountedValue Bool :=
  let permitted := countedFinAll features (offLineAllowed feature allowed line point)
  let b := readVector 0 base point
  let s := readVector 0 scale point
  let h := readVector 0 shear point
  let isMark := equalCounter b.value.val mark.val
  let isZeroScale := equalCounter s.value.val 0
  let isZeroShear := equalCounter h.value.val 0
  ⟨isMark.value && !isZeroScale.value && isZeroShear.value && permitted.value,
    permitted.work + b.work + s.work + h.work + isMark.work + isZeroScale.work + isZeroShear.work + 7⟩



def fiberWork (charts colors features : ℕ) : ℕ :=
  features * (9 * features + 4 * charts + 4 * colors + 23) +
    9 * charts + 12 * colors + 25



end CurrentAFT.CurrentFlagBinaryMasks

end

section




















namespace AFT
end AFT
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic




/-!
# Generating the current flag arrays from public integer data

The inherited feature, palette, and safe tables are reused.  Their old
single-point fiber is discarded.  A fresh fiber fixes base and shear and
uses the complete zero-first-coordinate line mask.
-/

namespace CurrentAFT.CurrentFlagBinaryMetadata

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits CurrentFlagBinaryMasks
open scoped BigOperators
set_option maxHeartbeats 400000

structure Data (charts colors features : ℕ) where
  feature : Vector (Vector (Fin colors) charts) features
  allowed : Vector (Vector Bool colors) features
  safe : Vector Bool charts
  line : Vector Bool features
  fiber : Vector Bool charts

def coordinates (modulus : ℕ) [NeZero modulus]
    (point : Fin (modulus * (modulus * modulus))) : CountedValue (Fin modulus × Fin modulus × Fin modulus) :=
  let result := binaryChartCoordinates modulus point.val
  let bounds := binaryChartCoordinates_bounds modulus point.val (NeZero.pos _) point.isLt
  ⟨(⟨result.offset, bounds.1⟩, ⟨result.scale, bounds.2.1⟩, ⟨result.shear, bounds.2.2⟩), result.work + 3⟩





def build (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
    CountedValue (Data (modulus * (modulus * modulus)) modulus ((2 * cutoff + 1) * (2 * cutoff + 1))) :=
  let inherited := protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark
  let line := storeData ((2 * cutoff + 1) * (2 * cutoff + 1)) (onLine cutoff)
  let base := storeData (modulus * (modulus * modulus)) (fun point =>
    let result := coordinates modulus point
    ⟨result.value.1, result.work + 1⟩)
  let shear := storeData (modulus * (modulus * modulus)) (fun point =>
    let result := coordinates modulus point
    ⟨result.value.2.2, result.work + 1⟩)
  let fiber := storeData (modulus * (modulus * modulus))
    (fiberAt inherited.value.feature inherited.value.allowed line.value base.value inherited.value.scale shear.value mark)
  ⟨⟨inherited.value.feature, inherited.value.allowed, inherited.value.safe, line.value, fiber.value⟩,
    inherited.work + line.work + base.work + shear.work + fiber.work + 5⟩











def workBound (cutoff modulus boundaryBits baselineBits : ℕ) : ℕ :=
  let charts := modulus * (modulus * modulus)
  let features := (2 * cutoff + 1) * (2 * cutoff + 1)
  protectedMetadataWork cutoff modulus boundaryBits baselineBits +
    (features * (onLineWork cutoff + 2) + 2) +
    2 * (charts * (protectedScaleWork modulus charts + 6) + 2) +
    (charts * (fiberWork charts modulus features + 2) + 2) + 5



end CurrentAFT.CurrentFlagBinaryMetadata

end

section











/-! # The actual public completion law is the canonical rational ideal -/

namespace CurrentAFT.CurrentFlagCompletion

open AFT AffineFlagCalibration ActualPublicLegCharge
open scoped BigOperators Classical
noncomputable section

local instance completionTablePrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

def model (security : ℕ) (primary : AffineFlagCalibration.Palette security) (seed : PublicSeed security) :=
  CurrentFlagProgram.current security (publicShift security primary seed)
    (by simpa only [legOffsetBound, add_sub_assoc] using publicShift_bound security primary seed)
    ((ZMod.finEquiv (Parameters.modulus security)) primary) (1 / 2 : ℚ) (by norm_num) (by norm_num)











end
end CurrentAFT.CurrentFlagCompletion

end

section


















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CurrentFlagIteration
end CurrentAFT.CurrentFlagIteration
namespace CurrentAFT.CurrentFlagIteration.regularIterate
end CurrentAFT.CurrentFlagIteration.regularIterate
namespace CurrentAFT.CurrentFlagReindex
end CurrentAFT.CurrentFlagReindex



/-! The correct marked array has fixed base and zero shear, with all line inputs exempted. -/

namespace CurrentAFT.CurrentFlagMarkedArray

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

def markedEmbedding (mark : F) : F ↪ Chart F where
  toFun scale := (mark, scale, 0)
  inj' _ _ h := congrArg (fun chart => chart.2.1) h

def fiber {charts : ℕ} (chartEquiv : Fin charts ≃ Chart F) (inputs : I → F × F)
    (allowed : I → Finset F) (mark : F) : Finset (Fin charts) :=
  ((markedScaleSet inputs allowed mark).map (markedEmbedding mark)).map chartEquiv.symm.toEmbedding







local instance markedArrayPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩



end
end CurrentAFT.CurrentFlagMarkedArray

end

section























/-!
# Actual finite-coordinate flag response

These arrays use the current protected inputs, the full affine chart,
the two prescribed trimmed palettes, and the exact marked scale fiber.
Coordinate changes preserve the canonical rational inverse exactly.
-/

namespace CurrentAFT.CurrentFlagFiniteResponse

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagIteration CurrentFlagReindex CurrentFlagMarkedArray
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]

def finiteRegular {charts colors inputsCount : ℕ}
    (chartEquiv : Fin charts ≃ Chart F) (colorEquiv : Fin colors ≃ F) (inputEquiv : Fin inputsCount ≃ I)
    (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℚ) (steps : ℕ) : Fin charts → ℚ :=
  regularIterate
    (fun index point => colorEquiv.symm (feature (inputs (inputEquiv index)).1
      (inputs (inputEquiv index)).2 (chartEquiv point)))
    (fun index => (allowed (inputEquiv index)).map colorEquiv.symm.toEmbedding)
    (fun index => (inputs (inputEquiv index)).1 = 0)
    (fun point => affineSafe inputs allowed (chartEquiv point)) atom
    (chartSpikeProgram charts (fiber chartEquiv inputs allowed mark)) steps



local instance finiteResponseZModDecidableEq (security : ℕ) : DecidableEq (ZMod (Parameters.modulus security)) :=
  Classical.decEq _
local instance finiteResponsePrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance finiteResponseNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

def currentRegular (security : ℕ) (baseline : ℤ) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (steps : ℕ) : Fin (Parameters.modulus security *
      (Parameters.modulus security * Parameters.modulus security)) → ℚ :=
  finiteRegular (finiteChartEquiv (Parameters.modulus security))
    (ZMod.finEquiv (Parameters.modulus security)).toEquiv
    (finiteInputEquiv (Parameters.sourceCutoff security - 1))
    (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
    (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
    mark atom steps



end
end CurrentAFT.CurrentFlagFiniteResponse

end

section




















namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.ProtectedChartSupport
end AFT.BoundaryCalibration.ProtectedChartSupport
namespace AFT.BoundaryCalibration.chartPaletteFeature
end AFT.BoundaryCalibration.chartPaletteFeature
namespace AFT.BoundaryCalibration.finiteAffineFeature
end AFT.BoundaryCalibration.finiteAffineFeature
namespace AFT.BoundaryCalibration.finiteAffineScale
end AFT.BoundaryCalibration.finiteAffineScale
namespace AFT.BoundaryCalibration.finiteProtectedFeatures
end AFT.BoundaryCalibration.finiteProtectedFeatures
namespace AFT.BoundaryCalibration.finiteProtectedMark
end AFT.BoundaryCalibration.finiteProtectedMark
namespace AFT.BoundaryCalibration.protectedInputs
end AFT.BoundaryCalibration.protectedInputs
namespace AFT.BoundaryCalibration.v7ProtectedPalettes
end AFT.BoundaryCalibration.v7ProtectedPalettes



/-! The finite-coordinate repair uses the actual executable feature and palette arrays. -/

namespace CurrentAFT.CurrentFlagFiniteCoordinates

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagIteration CurrentFlagFiniteResponse CurrentFlagMarkedArray
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000

variable (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]







def nativeRegular (baseline : ℤ) (mark : ZMod modulus) (atom : ℚ) (steps : ℕ) :
    Fin (modulus * (modulus * modulus)) → ℚ :=
  regularIterate (finiteProtectedFeatures cutoff modulus) (finiteProtectedPalettes cutoff modulus 1 baseline)
    (fun index => (((finiteInputEquiv cutoff index).1 : ℤ) : ZMod modulus) = 0)
    (fun point => point ∈ finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
      (finiteProtectedPalettes cutoff modulus 1 baseline)) atom
    (chartSpikeProgram (modulus * (modulus * modulus))
      (fiber (finiteChartEquiv modulus) (protectedInputs cutoff modulus)
        (protectedPalettes cutoff modulus 1 baseline) mark)) steps



end
end CurrentAFT.CurrentFlagFiniteCoordinates

end

section



















/-! A polynomial bound for the actual all-line right-hand side. -/

namespace CurrentAFT.CurrentFlagTargetNorm

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000

variable {F I : Type*} [Field F] [Fintype F] [Fintype I]



local instance targetNormPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩





def precisionSteps (cutoff bits : ℕ) : ℕ := bits + (4 * (2 * cutoff + 1) ^ 2 + 4)



end
end CurrentAFT.CurrentFlagTargetNorm

end

section






















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CurrentFlagBinary
end CurrentAFT.CurrentFlagBinary
namespace CurrentAFT.CurrentFlagBinaryMetadata
end CurrentAFT.CurrentFlagBinaryMetadata
namespace CurrentAFT.CurrentFlagBinaryMetadata.build
end CurrentAFT.CurrentFlagBinaryMetadata.build
namespace CurrentAFT.CurrentFlagIteration
end CurrentAFT.CurrentFlagIteration
namespace CurrentAFT.CurrentFlagIteration.iterationMatrix
end CurrentAFT.CurrentFlagIteration.iterationMatrix
namespace CurrentAFT.CurrentFlagMetadataSemantics
end CurrentAFT.CurrentFlagMetadataSemantics




/-!
# Public binary program for the current regular flag branch

Only the public offset, prescribed color, dimensions, and iteration count
are inputs.  No protected first or second source value is observed.  The
generated table has exactly the canonical current response semantics.
-/

namespace CurrentAFT.CurrentFlagPublicProgram

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentFlagFiniteCoordinates CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000

def half : RationalResult := quotient one (ofCounter 2).data



def evaluate (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) (steps : ℕ) :
    ArrayResult (modulus * (modulus * modulus)) :=
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let result := CurrentFlagBinary.regular metadata.value.feature metadata.value.allowed metadata.value.line
    metadata.value.safe metadata.value.fiber half.data steps
  ⟨result.data, metadata.work + half.work + result.work + 3⟩

def workBound (cutoff modulus baselineBits steps : ℕ) : ℕ :=
  CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baselineBits + half.work +
    CurrentFlagBinary.regularWork (modulus * (modulus * modulus)) modulus
      ((2 * cutoff + 1) * (2 * cutoff + 1)) 1 steps + 3





noncomputable section
open scoped Classical



local instance publicProgramPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance publicProgramNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩



end
end CurrentAFT.CurrentFlagPublicProgram

end

section




















/-! Actual canonical branch laws on the generated finite chart array. -/

namespace CurrentAFT.CurrentFlagIdealArrays

open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentFlagMarkedArray
open CurrentRationalFlagLaw AFT.BinaryArithmetic
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000

local instance idealArrayPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance idealArrayNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

def model (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) :=
  CurrentFlagProgram.current security baseline hbaseline ((ZMod.finEquiv (Parameters.modulus security)) mark)
    (1 / 2 : ℚ) (by norm_num) (by norm_num)

def regularLaw (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) :
    FiniteDist (Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :=
  (model security baseline hbaseline mark).model.regular.map (finiteChartEquiv (Parameters.modulus security)).symm

def markedLaw (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) :
    FiniteDist (Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :=
  (model security baseline hbaseline mark).model.marked.map (finiteChartEquiv (Parameters.modulus security)).symm





end
end CurrentAFT.CurrentFlagIdealArrays

end

section




















/-! Binary division by the chart count, producing probability-weight arrays. -/

namespace CurrentAFT.CurrentFlagWeightArray

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentFlagPublicProgram CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000

def entry {charts : ℕ} (raw : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
  let value := readVector zero raw point
  let count := ofCounter charts
  let result := quotient value.value count.data
  ⟨result.data, value.work + count.work + result.work + 3⟩



def scale {charts : ℕ} (raw : Vector RationalBits charts) : ArrayResult charts := buildArray charts (entry raw)



def entryWork (charts height : ℕ) : ℕ :=
  3 * charts + 3 + 60 * (charts + 1) ^ 2 + 2 * primitiveWorkBound (height + charts) + 5

def scaleWork (charts height : ℕ) : ℕ := charts * (entryWork charts height + 2) + 2







def regularWeights (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) (steps : ℕ) :
    ArrayResult (modulus * (modulus * modulus)) :=
  let raw := CurrentFlagPublicProgram.evaluate cutoff modulus baselineSign baseline mark steps
  let weights := scale raw.data
  ⟨weights.data, raw.work + weights.work + 2⟩

def markedWeights (cutoff modulus : ℕ) [NeZero modulus]
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) :
    ArrayResult (modulus * (modulus * modulus)) :=
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let density := buildArray (modulus * (modulus * modulus)) (chartSpike metadata.value.fiber)
  let weights := scale density.data
  ⟨weights.data, metadata.work + density.work + weights.work + 3⟩

noncomputable section
open scoped Classical
local instance flagWeightPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance flagWeightNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩





end
end CurrentAFT.CurrentFlagWeightArray

end

section
























/-! Positive finite-bit array sampling with an actual safe-mask fallback scan. -/

namespace CurrentAFT.CurrentFlagDraw

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 400000

def draw {charts : ℕ} [NeZero charts] (raw : Vector RationalBits charts) (mask : Vector Bool charts)
    (bits : ℕ) (word : Fin (bits + charts + 1) → Fin 2) : CountedValue (Fin charts) :=
  let selected := binaryPositiveFinDraw raw bits word
  let point : Fin charts := ⟨selected.value, binaryPositiveFinDraw_lt raw bits word⟩
  let legal := binaryLegalChartIndex mask point
  ⟨legal.value, selected.work + legal.work + 2⟩



def workBound (charts height bits : ℕ) : ℕ :=
  binaryPositiveDrawWork charts height bits + 7 * charts + 13



noncomputable section
open scoped Classical





end
end CurrentAFT.CurrentFlagDraw

end

section




















/-! The exact branch laws are supported on their generated public masks. -/

namespace CurrentAFT.CurrentFlagReferenceSupport

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagIdealArrays CurrentFlagBinaryMetadata CurrentFlagFiniteCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000

local instance referenceSupportPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance referenceSupportNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩





end
end CurrentAFT.CurrentFlagReferenceSupport

end

section




















/-! Costs and heights of the materialized branch probability arrays. -/

namespace CurrentAFT.CurrentFlagWeightArray

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentFlagPublicProgram CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 400000

def regularWeightHeight (cutoff modulus steps : ℕ) : ℕ :=
  CurrentFlagBinary.iterateHeight (modulus * (modulus * modulus)) modulus
    ((2 * cutoff + 1) * (2 * cutoff + 1)) 1 steps + modulus * (modulus * modulus)

def regularWeightWork (cutoff modulus baselineBits steps : ℕ) : ℕ :=
  CurrentFlagPublicProgram.workBound cutoff modulus baselineBits steps +
    scaleWork (modulus * (modulus * modulus))
      (CurrentFlagBinary.iterateHeight (modulus * (modulus * modulus)) modulus
        ((2 * cutoff + 1) * (2 * cutoff + 1)) 1 steps) + 2





def markedWeightWork (cutoff modulus baselineBits : ℕ) : ℕ :=
  let charts := modulus * (modulus * modulus)
  CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baselineBits +
    (charts * (spikeWork charts + 2) + 2) + scaleWork charts (2 * charts) + 3





end CurrentAFT.CurrentFlagWeightArray

end

section
























/-! The two actual public flag branches, sampled with finite fair bits. -/

namespace CurrentAFT.CurrentFlagBranchDraw

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentFlagBinaryMetadata CurrentFlagWeightArray
open scoped BigOperators
set_option maxHeartbeats 500000

def regular (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ)
    (word : Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2) :
    CountedValue (Fin (modulus * (modulus * modulus))) :=
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let weights := regularWeights cutoff modulus baselineSign baseline mark (CurrentFlagTargetNorm.precisionSteps cutoff precisionBits)
  let result := CurrentFlagDraw.draw weights.data metadata.value.safe drawBits word
  ⟨result.value, metadata.work + weights.work + result.work + 3⟩

def marked (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (drawBits : ℕ)
    (word : Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2) :
    CountedValue (Fin (modulus * (modulus * modulus))) :=
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  let weights := markedWeights cutoff modulus baselineSign baseline mark
  let result := CurrentFlagDraw.draw weights.data metadata.value.fiber drawBits word
  ⟨result.value, metadata.work + weights.work + result.work + 3⟩

def regularWork (cutoff modulus baselineBits precisionBits drawBits : ℕ) : ℕ :=
  let steps := CurrentFlagTargetNorm.precisionSteps cutoff precisionBits
  CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baselineBits +
    regularWeightWork cutoff modulus baselineBits steps +
    CurrentFlagDraw.workBound (modulus * (modulus * modulus)) (regularWeightHeight cutoff modulus steps) drawBits + 3

def markedWork (cutoff modulus baselineBits drawBits : ℕ) : ℕ :=
  CurrentFlagBinaryMetadata.workBound cutoff modulus 1 baselineBits + markedWeightWork cutoff modulus baselineBits +
    CurrentFlagDraw.workBound (modulus * (modulus * modulus)) (3 * (modulus * (modulus * modulus))) drawBits + 3





noncomputable section
open scoped Classical
local instance branchDrawPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance branchDrawNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩







end
end CurrentAFT.CurrentFlagBranchDraw

end

section





















namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.joint
end AFT.FiniteDist.joint



/-! The same public fair flag and finite-bit chart law for all protected inputs. -/

namespace CurrentAFT.CurrentFlagJointDraw

open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentFlagBranchDraw
open scoped BigOperators
set_option maxHeartbeats 500000

abbrev Tape (modulus drawBits : ℕ) := Bool × (Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2)

def draw (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : Tape modulus drawBits) :
    CountedValue (Bool × Fin (modulus * (modulus * modulus))) :=
  if word.1 then
    let result := marked cutoff modulus baselineSign baseline mark drawBits word.2
    ⟨(true, result.value), result.work + 2⟩
  else
    let result := regular cutoff modulus baselineSign baseline mark precisionBits drawBits word.2
    ⟨(false, result.value), result.work + 2⟩



def workBound (cutoff modulus baselineBits precisionBits drawBits : ℕ) : ℕ :=
  regularWork cutoff modulus baselineBits precisionBits drawBits + markedWork cutoff modulus baselineBits drawBits + 2



noncomputable section
open scoped Classical

def tapeLaw (modulus drawBits : ℕ) : FiniteDist (Tape modulus drawBits) :=
  (FiniteDist.uniform Bool).prod (FiniteDist.uniform (Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2))

def branchLaw (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (flag : Bool) :=
  (FiniteDist.uniform (Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2)).map
    (fun word => if flag then (marked cutoff modulus baselineSign baseline mark drawBits word).value
      else (regular cutoff modulus baselineSign baseline mark precisionBits drawBits word).value)



local instance jointDrawPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance jointDrawNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩

def referenceBranches (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (flag : Bool) :=
  if flag then CurrentFlagIdealArrays.markedLaw security baseline hbaseline mark
    else CurrentFlagIdealArrays.regularLaw security baseline hbaseline mark

def indexedReference (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) :=
  FiniteDist.joint (FiniteDist.uniform Bool) (referenceBranches security baseline hbaseline mark)





end
end CurrentAFT.CurrentFlagJointDraw

end

section




















/-! Sampling complete flag and affine charts with binary coordinate decoding. -/

namespace CurrentAFT.CurrentFlagChartDraw

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentFlagJointDraw CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000

def draw (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : Tape modulus drawBits) :
    CountedValue (Bool × Chart (ZMod modulus)) :=
  let selected := CurrentFlagJointDraw.draw cutoff modulus baselineSign baseline mark precisionBits drawBits word
  let chart := coordinates modulus selected.value.2
  ⟨(selected.value.1, (ZMod.finEquiv modulus) chart.value.1,
      (ZMod.finEquiv modulus) chart.value.2.1, (ZMod.finEquiv modulus) chart.value.2.2),
    selected.work + chart.work + 3⟩



def workBound (cutoff modulus baselineBits precisionBits drawBits : ℕ) : ℕ :=
  CurrentFlagJointDraw.workBound cutoff modulus baselineBits precisionBits drawBits +
    protectedScaleWork modulus (modulus * (modulus * modulus)) + 6



noncomputable section
open scoped Classical
local instance chartDrawPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance chartDrawNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩





end
end CurrentAFT.CurrentFlagChartDraw

end

section
























/-! Actual public-shift encoding by counter comparisons and signed binary arithmetic. -/

namespace CurrentAFT.CurrentPublicShiftProgram

open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 500000

def encode : ℤ → CountedValue IntegerBits
  | .ofNat value =>
    let bits := canonicalCounter value
    ⟨⟨false, bits.digits⟩, bits.work + 1⟩
  | .negSucc value =>
    let bits := canonicalCounter (value + 1)
    ⟨⟨true, bits.digits⟩, bits.work + 1⟩







def direction (modulus primary : ℕ) (coin : Bool) : CountedValue Bool :=
  let doubled := doubleCounter primary
  let boundary := differenceCounter modulus 1
  let below := lessCounter doubled.count boundary.count
  let above := lessCounter boundary.count doubled.count
  ⟨if below.value then false else if above.value then true else coin,
    doubled.work + boundary.work + below.work + above.work + 3⟩





def program (modulus width primary index : ℕ) (coin : Bool) (blurFirst blurSecond : ℤ) : CountedValue IntegerBits :=
  let sign := direction modulus primary coin
  let offset := addCounter width index
  let bits := canonicalCounter offset.count
  let signedOffset : IntegerBits := ⟨!sign.value, bits.digits⟩
  let first := encode blurFirst
  let second := encode blurSecond
  let blur := IntegerBits.subtract first.value second.value
  let result := IntegerBits.add signedOffset blur.value
  ⟨result.value, sign.work + offset.work + bits.work + first.work + second.work + blur.work + result.work + 7⟩



def programWork (modulus width primary index firstSize secondSize : ℕ) : ℕ :=
  (15 * primary + 8 * modulus + 9) + (2 * width + 1) + 50 * (width + index + 1) ^ 2 +
    (50 * (firstSize + 1) ^ 2 + 1) + (50 * (secondSize + 1) ^ 2 + 1) +
    (20 * (firstSize + secondSize) + 13) + (20 * (width + index + firstSize + secondSize + 1) + 9) + 7



def current (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) : CountedValue IntegerBits :=
  let modulus := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let width := powerCounter base.count 48
  let result := program modulus.count width.count primary.val seed.anchorIndex.val seed.coin seed.blur.1.val seed.blur.2.val
  ⟨result.value, modulus.work + base.work + width.work + result.work + 3⟩



end CurrentAFT.CurrentPublicShiftProgram

end

section





























/-! Literal binary Gaussian evaluation on the materialized touched edges.
All selected roots read the cached rank pair, so adjacent roots share exactly
the same latent edge coordinate. The closing predecessor is retained. -/
namespace CurrentAFT.BinarySparseCycleEvaluation
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryTouchedCycle BinaryTouchedCycleBuffer BinaryTouchedCycleRanks
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def rootEntry {edges count cutoff : ℕ} (ranks : Vector (Fin edges × Fin edges) count)
    (word : Vector (Fin (2*cutoff+1)) edges) (slot : Fin count) : CountedValue IntegerBits :=
  let selected := readList ranks.toList slot.val
  match selected.data with
  | none => ⟨IntegerBits.zero,selected.work+count+4⟩
  | some pair =>
    let first := readVector (⟨0,by omega⟩ : Fin (2*cutoff+1)) word pair.1
    let second := readVector (⟨0,by omega⟩ : Fin (2*cutoff+1)) word pair.2
    let firstBits := CurrentPublicShiftProgram.encode (first.value.val : ℤ)
    let secondBits := CurrentPublicShiftProgram.encode (second.value.val : ℤ)
    let difference := IntegerBits.subtract firstBits.value secondBits.value
    ⟨difference.value,selected.work+count+first.work+second.work+firstBits.work+secondBits.work+difference.work+7⟩

 


def roots {edges count cutoff : ℕ} (ranks : Vector (Fin edges × Fin edges) count)
    (word : Vector (Fin (2*cutoff+1)) edges) : CountedValue (Vector IntegerBits count) :=
  storeData count (rootEntry ranks word)

 


def weightEntry {edges cutoff : ℕ} (weights : Vector RationalBits (2*cutoff+1))
    (word : Vector (Fin (2*cutoff+1)) edges) (edge : Fin edges) : RationalResult :=
  let index := readVector (⟨0,by omega⟩ : Fin (2*cutoff+1)) word edge
  let weight := readVector RationalBits.zero weights index.value
  ⟨weight.value,index.work+weight.work+2⟩

 


def term {edges count cutoff : ℕ} (weights : Vector RationalBits (2*cutoff+1))
    (ranks : Vector (Fin edges × Fin edges) count) (test : Vector IntegerBits count → RationalResult)
    (word : Vector (Fin (2*cutoff+1)) edges) : RationalResult :=
  let rootWord := roots ranks word
  let response := test rootWord.value
  let mass := BinaryFiniteProduct.current edges (weightEntry weights word)
  let product := RationalBits.multiply mass.data response.data
  ⟨product.data,rootWord.work+response.work+mass.work+product.work+4⟩

 


def current {body count : ℕ} (security cutoff bits : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count)
    (test : Vector IntegerBits count → RationalResult) : RationalResult :=
  let touched := prepare hb sites
  let rankPairs := positions hb sites
  let weights := CurrentGaussianBits.table security cutoff bits
  let summed := BinaryTupleSum.current (2*cutoff+1) touched.value.length (term weights.data rankPairs.value test)
  ⟨summed.data,touched.work+touched.value.length+rankPairs.work+weights.work+summed.work+5⟩

 

end CurrentAFT.BinarySparseCycleEvaluation

end

section





























/-! Modular point indicators and centered products for sparse cycle tests.
The equality test uses Euclidean binary residue and two signed comparisons. -/
namespace CurrentAFT.BinaryCycleTest
open AFT BinaryArithmetic RationalRejectionProgram RationalNumerics
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def equalResidue (modulus : List Bool) (root : IntegerBits) (output : ℕ) : CountedValue Bool :=
  let residue := IntegerBits.residue root modulus
  let expected := canonicalCounter output
  let first := signedLe false false residue.digits expected.digits
  let second := signedLe false false expected.digits residue.digits
  ⟨first.value && second.value,residue.work+expected.work+first.work+second.work+4⟩

 

 


def point {count : ℕ} (modulus : List Bool) (output : Vector ℕ count) (roots : Vector IntegerBits count) : RationalResult :=
  let test := BinaryProposalGuard.allFin count (fun slot =>
    let root := readVector IntegerBits.zero roots slot
    let expected := readVector 0 output slot
    let checked := equalResidue modulus root.value expected.value
    ⟨checked.value,root.work+expected.work+checked.work+3⟩)
  ⟨if test.value then RationalBits.one else RationalBits.zero,test.work+2⟩

 


def centeredFactor {count : ℕ} (modulus : List Bool) (output : Vector ℕ count)
    (reference : Vector RationalBits count) (roots : Vector IntegerBits count) (slot : Fin count) : RationalResult :=
  let root := readVector IntegerBits.zero roots slot
  let expected := readVector 0 output slot
  let mass := readVector RationalBits.zero reference slot
  let checked := equalResidue modulus root.value expected.value
  let negative := RationalBits.negate mass.value
  let result := RationalBits.add (if checked.value then RationalBits.one else RationalBits.zero) negative.data
  ⟨result.data,root.work+expected.work+mass.work+checked.work+negative.work+result.work+6⟩

 


def signed {count : ℕ} (modulus : List Bool) (output : Vector ℕ count)
    (reference : Vector RationalBits count) (roots : Vector IntegerBits count) : RationalResult :=
  BinaryFiniteProduct.current count (centeredFactor modulus output reference roots)

 

end CurrentAFT.BinaryCycleTest

end

section





















/-! The executed touched-edge Gaussian sum is exactly the manuscript's sparse
cycle evaluator, for arbitrary joint tests and every root-placement pattern. -/
namespace CurrentAFT.BinarySparseCycleSemantic
open AFT GaussianSource RationalNumerics BinaryArithmetic
open BinaryTouchedCycle BinaryTouchedCycleBuffer BinaryTouchedCycleRanks
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def coordinates {body count : ℕ} (cutoff : ℕ) (hb : 0 < body) (sites : Vector (Fin body) count) :
    (Fin (prepare hb sites).value.length → Fin (2*cutoff+1)) ≃
      (CyclePatternProgram.touched sites.get → Window cutoff) :=
  Equiv.arrowCongr (edgeEquiv hb sites) (FiniteConvolutionProgram.windowIndexEquiv cutoff)

 

 

 

 

end
end CurrentAFT.BinarySparseCycleSemantic

end

section























/-! Uniform distinct cycle-root placements are averaged by executed tuple
loops and their computed distinct-selection normalizer. -/
namespace CurrentAFT.BinarySparseCycleAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def current (security cutoff bits body count : ℕ) (hb : 0 < body)
    (test : Vector IntegerBits count → RationalResult) : RationalResult :=
  let numerator := BinaryDistinctTuples.sum body count hb (fun sites =>
    BinarySparseCycleEvaluation.current security cutoff bits hb sites test)
  let denominator := BinaryDistinctTuples.normalizer body count hb
  let result := RationalBits.quotient numerator.data denominator.data
  ⟨result.data,numerator.work+denominator.work+result.work+3⟩

noncomputable section
open scoped Classical

 

end
end CurrentAFT.BinarySparseCycleAverage

end

section




















/-! Current finite Gaussian-window sampling by literal binary table and ticket programs. -/

namespace CurrentAFT.CurrentWindowDraw

open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open AFT.RationalRejectionProgram AFT.FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 500000

 theorem table_nonneg (security cutoff bits : ℕ) (index : Fin (2 * cutoff + 1)) :
    0 ≤ ((CurrentGaussianBits.table security cutoff bits).data.get index).decode := by
  rw [CurrentGaussianBits.table_value]
  exact windowGaussianWeights_nonneg _ _ _ _

 theorem table_sum (security cutoff bits : ℕ) :
    ∑ index, ((CurrentGaussianBits.table security cutoff bits).data.get index).decode = 1 := by
  simp only [CurrentGaussianBits.table_value]
  exact windowGaussianWeights_sum _ _ _



def draw (security cutoff bits : ℕ) (word : Fin (windowTicketBits cutoff bits) → Fin 2) : CountedValue (Window cutoff) :=
  let weights := CurrentGaussianBits.table security cutoff (bits + 1)
  let selected := binaryRationalDraw weights.data (windowTicketBits cutoff bits) word
  have hi : selected.value < 2 * cutoff + 1 := by
    rw [binaryRationalDraw_value weights.data (table_nonneg security cutoff (bits + 1))
      (table_sum security cutoff (bits + 1))]
    exact Fin.isLt _
  let point := integerDifference selected.value cutoff
  have hp : point.value ∈ Finset.Icc (-(cutoff : ℤ)) cutoff := by
    have hw := (windowIndexEquiv cutoff (⟨selected.value, hi⟩ : Fin (2 * cutoff + 1))).property
    change ((selected.value : ℤ) - cutoff) ∈ Finset.Icc (-(cutoff : ℤ)) cutoff at hw
    simpa only [point, integerDifference_value] using hw
  ⟨⟨point.value, hp⟩, weights.work + selected.work + point.work + 3⟩



def workBound (security cutoff bits : ℕ) : ℕ :=
  CurrentGaussianBits.tableWork security (bits + 1) +
    binaryRationalDrawWork (2 * cutoff + 1) (500000000 * (CurrentGaussianBits.budget security (bits + 1)) ^ 6)
      (windowTicketBits cutoff bits) + 6 * cutoff + 7



noncomputable section
open scoped Classical



end
end CurrentAFT.CurrentWindowDraw

end

section




















/-! The closing-edge sampler includes its actual public cutoff generation. -/

namespace CurrentAFT.CurrentEdgeDrawProgram

open AFT GaussianSource RationalNumerics BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 400000

def cutoffProgram (security : ℕ) : CounterDivisionResult :=
  let base := addCounter security 2
  let square := powerCounter base.count 2
  let trimmed := differenceCounter square.count 1
  let result := divideCounter trimmed.count 2
  ⟨result.quotient, result.remainder, base.work + square.work + trimmed.work + result.work + 4⟩

theorem cutoff_value (security : ℕ) : (cutoffProgram security).quotient = DiffuseProfiles.edgeCutoff security := by
  simp only [cutoffProgram, (divideCounter_value _ 2 (by decide)).1, differenceCounter_value,
    powerCounter_value, addCounter_value, DiffuseProfiles.edgeCutoff, Parameters.sourceCutoff, Parameters.base]

def cutoffWork (security : ℕ) : ℕ :=
  2 * security + 1 + powerCounterWork (security + 2) 2 + (2 * (security + 2) ^ 2 + 1) +
    500 * ((security + 2) ^ 2 + 4) ^ 2 + 4

theorem cutoff_work (security : ℕ) : (cutoffProgram security).work ≤ cutoffWork security := by
  have hp := powerCounter_work (security + 2) 2
  have ht := differenceCounter_work ((security + 2) ^ 2) 1
  have hd := divideCounter_work ((security + 2) ^ 2 - 1) 2 (by decide)
  have hd' : (divideCounter ((security + 2) ^ 2 - 1) 2).work ≤
      500 * ((security + 2) ^ 2 + 4) ^ 2 := hd.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega) 2))
  simp only [cutoffProgram, powerCounter_value, addCounter_value, differenceCounter_value, addCounter_work, cutoffWork]
  omega

def castWindow {first second : ℕ} (h : first = second) (result : CountedValue (Window first)) : CountedValue (Window second) :=
  ⟨h ▸ result.value, result.work⟩



def draw (security bits : ℕ) (word : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) bits) → Fin 2) :
    CountedValue (Window (DiffuseProfiles.edgeCutoff security)) :=
  let cutoff := cutoffProgram security
  have hc : cutoff.quotient = DiffuseProfiles.edgeCutoff security := cutoff_value security
  let result := CurrentWindowDraw.draw security cutoff.quotient bits
    (cast (congrArg (fun cutoff => Fin (windowTicketBits cutoff bits) → Fin 2) hc.symm) word)
  let converted := castWindow hc result
  ⟨converted.value, cutoff.work + converted.work + 2⟩



def workBound (security bits : ℕ) : ℕ :=
  cutoffWork security + CurrentWindowDraw.workBound security (DiffuseProfiles.edgeCutoff security) bits + 2



noncomputable section
open scoped Classical



end
end CurrentAFT.CurrentEdgeDrawProgram

end

section



























/-! Actual binary reference and centered root masses. Only selected sites and
their touched-edge Gaussian words are enumerated; no root atom is inverted. -/
namespace CurrentAFT.BinaryRootSignedMass
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus


def bodyProgram (security : ℕ) : UnaryCounterResult :=
  let q := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let scale := powerCounter base.count 96
  let result := multiplyCounter q.count scale.count
  ⟨result.count,q.work+base.work+scale.work+result.work+4⟩

 theorem bodyProgram_value (security : ℕ) : (bodyProgram security).count = CurrentCycleEntryProgram.bodyCount security := by
  simp only [bodyProgram,multiplyCounter_value,powerCounter_value,addCounter_value,CurrentCycleEntryProgram.bodyCount]

 theorem bodyProgram_positive (security : ℕ) : 0 < (bodyProgram security).count := by
  rw [bodyProgram_value,CurrentCycleEntryProgram.bodyCount,PublicParameterProgram.modulus_value]
  exact Nat.mul_pos (Parameters.modulus_spec security).2.pos (pow_pos (by omega) _)


def referenceEntry (security bits output : ℕ) : RationalResult :=
  let body := bodyProgram security
  let cutoff := CurrentEdgeDrawProgram.cutoffProgram security
  let q := PublicParameterProgram.modulus security
  let code := canonicalCounter q.count
  let expected := storeData 1 (fun _ => (⟨output,1⟩ : CountedValue ℕ))
  let result := BinarySparseCycleAverage.current security cutoff.quotient bits body.count 1 (bodyProgram_positive security)
    (BinaryCycleTest.point code.digits expected.value)
  ⟨result.data,body.work+cutoff.work+q.work+code.work+expected.work+result.work+6⟩

 


def references {count : ℕ} (security bits : ℕ) (output : Vector ℕ count) :
    CountedValue (Vector RationalBits count) :=
  storeData count (fun slot =>
    let expected := readVector 0 output slot
    let mass := referenceEntry security bits expected.value
    ⟨mass.data,expected.work+mass.work+2⟩)

 


def weightedEntry {count : ℕ} (security bits : ℕ) (output : Vector ℕ count) : RationalResult :=
  let body := bodyProgram security
  let cutoff := CurrentEdgeDrawProgram.cutoffProgram security
  let q := PublicParameterProgram.modulus security
  let code := canonicalCounter q.count
  let masses := references security bits output
  let result := BinarySparseCycleAverage.current security cutoff.quotient bits body.count count (bodyProgram_positive security)
    (BinaryCycleTest.signed code.digits output masses.value)
  ⟨result.data,body.work+cutoff.work+q.work+code.work+masses.work+result.work+6⟩

 

end CurrentAFT.BinaryRootSignedMass

end

section
























/-! # The same executed scalar average for a scalar-valued finite mass -/
namespace CurrentAFT.BinaryScalarAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct GradedControlAlgebra
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def table (kernel : IntegerBits → RationalResult) (scalar : IntegerBits) : CoefficientProgram 0 :=
  fun _ _ _ => ⟨(kernel scalar).data,(kernel scalar).work⟩

def current (security bits : ℕ) (kernel : IntegerBits → RationalResult) : RationalResult :=
  let result := BinaryCoefficientScalarAverage.current security bits 0 (table kernel)
    (zeroArity 0) #v[] #v[]
  ⟨result.value,result.work⟩



noncomputable section
open scoped BigOperators



end
end CurrentAFT.BinaryScalarAverage

end


