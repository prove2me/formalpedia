-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_11_Part_1
-- name    : InfoLossLAR_NativeBundle_11_Part_1
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:19:16.511196+00:00
-- url     : https://prove2.me/theorems/21c729b2-e113-4439-ab25-8770e3a41f53
-- title:
--   Normalized root kernels and public completion interfaces
-- statement:
--   This package defines rational and binary leg masses, proposal dimensions and resources, rectangle and source padding indices, local positive and ordinary normalized family programs, packed root data and sparse cycle bounds, public permutation caches, chart drawing, and public completion.
--
--   These are stored finite data and their constructor and interpretation APIs. They keep the actual binary or rational computation distinct from its ideal real semantics; later theorems establish approximation and platform running-time guarantees. The smaller compilation unit preserves entire original source modules and introduces no assumed transport or lattice-reduction result.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0. Original source units Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalLegMassProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryLegMass, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryCycleTestResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentProposalDimensions, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentPublicShiftCost, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentProposalResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CalibrationRectanglePadding, Definitions.Def_InfoLossLAR_Native_CurrentAFT_WeightCoordinateDecode, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RectanglePointIndex, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentRectangleIndex, Definitions.Def_InfoLossLAR_Native_CurrentAFT_GroupSourcePadding, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RootWeightedSynthesis, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentGroupSourcePadding, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalFamilyWordProduct, Definitions.Def_InfoLossLAR_Native_CurrentAFT_LegCoefficientPointBounds, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalLocalFamilyProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_LocalCoefficientPointBounds, Definitions.Def_InfoLossLAR_Native_CurrentAFT_PositiveFamilyPointBound, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalPositiveFamilyProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalNormalizedPrimaryProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalSingletonProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalUnselectedLegProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalUnselectedLegNormalized, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalOrdinaryProfileProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalOrdinaryFamilyProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalOrdinaryNormalized, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalRootGroupProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalPackedRootProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPackedRootSum, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinarySparseCycleTermResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinarySparseCycleBounds, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinarySparseCyclePolynomial, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinarySparseCycleAveragePolynomial, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentPermutationDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentPermutationCache, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentFlagCompletionProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentChartsDraw, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentPublicCompletion. Exact syntax-oracle source spans, body hashes and closed scope wrappers recorded in compact_heavy_split/manifest.json. Source SHA256 9c16ff05a6398d9c8713f8852cfbae9ddf2c02fe333e5881b0318117d89a18e4. Header-only omission of a zero-declaration import facade; direct last-part import retains every mathematical declaration, instance, attribute andoption. Lean parser/kernel evidence andfull9429native+2099runtime type/std3 audits pass in native_empty_facades_bypass; all non-import source bytes exact. Current sourceSHA256 51ea4aae16819313bc475d5fc6491a5b07b2e6397bcd326e653bce02ce756589. Compiler-only optimization: one local scope marks Polynomial addition and multiplication instances irreducible while generating native equation lemmas. Every original definition and proof source body is unchanged; all11528 public types and recursive standard-axiom audits pass. New sourceSHA256 20721f956d0001f8bd5ed53b665a22a4ee3e1f8517fcae539c998a4b03b24460.

import Definitions.Def_InfoLossLAR_NativeBundle_10_Part_4

section
attribute [local irreducible] Polynomial.instAdd Polynomial.instMul

section


























/-! # The actual same-scalar three-endpoint mass before its higher coefficients -/
namespace CurrentAFT.RationalLegMassProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
open PositiveFirstCoefficient (positiveTripleLaw positiveFourLaw consEquiv)
open PairedReferenceEnergy (compensatorAt)
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def fixed (security bits : ℕ) (root scalar : ℤ) (word : Fin 3 → ℕ) : ℚ :=
  ∑ compensator : Fin (PublicParameterProgram.modulus security).count,
    RationalPositiveReferenceProgram.fixedMass security bits 0 root scalar (Fin.cons compensator.val word)

def atRoot (security bits : ℕ) (root : ℤ) (word : Fin 3 → ℕ) : ℚ :=
  ∑ index : Fin (2*((security + 2)^2 - 1)+1),
    let scalar := FiniteConvolutionProgram.windowIndexEquiv ((security + 2)^2 - 1) index
    RationalProposalProgram.gaussianWeight security ((security + 2)^2 - 1) bits scalar *
      fixed security bits root scalar.val word

def mean (security bits : ℕ) (word : Fin 3 → ℕ) : ℚ :=
  ∑ root : Fin (PublicParameterProgram.modulus security).count,
    RootSignedMassProgram.referenceEntry security bits root.val * atRoot security bits root.val word

def difference (security bits : ℕ) (root : ℤ) (word : Fin 3 → ℕ) : ℚ :=
  atRoot security bits root word - mean security bits word

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus
attribute [local irreducible] rootReference ActualBlockFock.primaryLawAt







def atRootErrorConstant (security : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ) * RationalPositiveReferenceProgram.fixedErrorConstant security + 1











def meanErrorConstant (security : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ) * (atRootErrorConstant security + 2)



def differenceErrorConstant (security : ℕ) : ℝ := atRootErrorConstant security + meanErrorConstant security





end
end CurrentAFT.RationalLegMassProgram

end

section

































/-! # The executed same-scalar joint mass of the three actual leg endpoints -/
namespace CurrentAFT.BinaryLegMass
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryPositiveReference.fixedMass
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def fixedTerm (security bits : ℕ) (root scalar : IntegerBits) (word : Vector (Fin (colors security)) 3)
    (compensator : Fin (colors security)) : RationalResult :=
  let four := BinaryTupleSum.prepend compensator word
  let result := BinaryPositiveReference.fixedMass security bits BinaryProfileLookup.zeroRoot root scalar four.value
  ⟨result.data,four.work+result.work+2⟩



def fixed (security bits : ℕ) (root scalar : IntegerBits) (word : Vector (Fin (colors security)) 3) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := sumFin modulus.count (fixedTerm security bits root scalar word)
  ⟨result.data,modulus.work+result.work+2⟩



def atRoot (security bits : ℕ) (root : IntegerBits) (word : Vector (Fin (colors security)) 3) : RationalResult :=
  BinaryScalarAverage.current security bits (fun scalar => fixed security bits root scalar word)



def meanTerm (security bits : ℕ) (word : Vector (Fin (colors security)) 3) (root : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter root.val
  let probability := BinaryRootSignedMass.referenceEntry security bits root.val
  let column := atRoot security bits ⟨false,code.digits⟩ word
  let result := RationalBits.multiply probability.data column.data
  ⟨result.data,code.work+probability.work+column.work+result.work+4⟩



def mean (security bits : ℕ) (word : Vector (Fin (colors security)) 3) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := sumFin modulus.count (meanTerm security bits word)
  ⟨result.data,modulus.work+result.work+2⟩



def difference (security bits : ℕ) (root : IntegerBits) (word : Vector (Fin (colors security)) 3) : RationalResult :=
  let first := atRoot security bits root word
  let second := mean security bits word
  let result := RationalBits.difference first.data second.data
  ⟨result.data,first.work+second.work+result.work+3⟩



noncomputable section
def fixedHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(BinaryPositiveReference.heightPolynomial precision inputBits+1)
def fixedWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryFirstInverseProgram.colorsPolynomial*
    (BinaryPositiveReference.workPolynomial precision inputBits+60+
      primitiveWorkPolynomial ((BinaryFirstInverseProgram.colorsPolynomial+1)*
        (BinaryPositiveReference.heightPolynomial precision inputBits+1))+2)+4



def atRootHeightPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.heightPolynomial precision
    (fixedHeightPolynomial precision (rootBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial))
def atRootWorkPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.workPolynomial precision
    (fixedHeightPolynomial precision (rootBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial))
    (fixedWorkPolynomial precision (rootBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial))



end
end CurrentAFT.BinaryLegMass

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegMass.fixedHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryLegMass.fixedWorkPolynomial
  pure ()

end

section





















/-! Explicit binary costs and heights for modular cycle point and centered tests. -/
namespace CurrentAFT.BinaryCycleTestResources
open AFT BinaryArithmetic RationalRejectionProgram RationalNumerics BinaryCycleTest
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def matchWork (rootBits modulusBits outputBound : ℕ) : ℕ :=
  60*(rootBits+modulusBits+1)^2+50*(outputBound+1)^2+48*(rootBits+modulusBits+outputBound)+50


def pointWork (count rootBits modulusBits outputBound : ℕ) : ℕ :=
  count*(6*count+matchWork rootBits modulusBits outputBound+11)+3

 


def factorWork (count rootBits modulusBits outputBound height : ℕ) : ℕ :=
  9*count+matchWork rootBits modulusBits outputBound+2*RationalBits.primitiveWorkBound (height+1)+20

 

 

end CurrentAFT.BinaryCycleTestResources

end

section
























/-! Executed current dimensions of every finite public proposal buffer. -/
namespace CurrentAFT.CurrentProposalDimensions
open AFT AFT.BinaryArithmetic
set_option maxHeartbeats 500000

structure Result where
  colors : ℕ
  legs : ℕ
  body : ℕ
  dimension : ℕ
  ordinary : ℕ
  controls : ℕ
  work : ℕ

def current (security : ℕ) : Result :=
  let sizes := BinaryProposalMetadata.counts security
  let doubled := doubleCounter sizes.legs
  let dimension := addCounter sizes.population doubled.count
  let nonqueue := subtractCounter sizes.population sizes.colors
  let ordinary := subtractCounter nonqueue.count doubled.count
  let controls := addCounter sizes.legs ordinary.count
  ⟨sizes.colors, sizes.legs, sizes.population, dimension.count, ordinary.count, controls.count,
    sizes.work + doubled.work + dimension.work + nonqueue.work + ordinary.work + controls.work + 6⟩

theorem current_values (security : ℕ) :
    (current security).colors = Parameters.modulus security ∧
    (current security).legs = Parameters.legCount security ∧
    (current security).body = Parameters.bodySize security ∧
    (current security).dimension = Parameters.dimension security ∧
    (current security).ordinary = BackgroundRates.ordinaryPool security ∧
    (current security).controls = Parameters.legCount security + BackgroundRates.ordinaryPool security := by
  rcases BinaryProposalMetadata.counts_value security with ⟨hq, hl, hb⟩
  have hlegs : (BinaryProposalMetadata.counts security).legs = Parameters.legCount security := by
    rw [hl, Parameters.legCount, Parameters.scale, Parameters.base, ← pow_mul]
  have hbody : (BinaryProposalMetadata.counts security).population = Parameters.bodySize security := by
    rw [hb, Parameters.bodySize, Parameters.scale, Parameters.base, ← pow_mul]
  simp only [current, addCounter_value, subtractCounter_value, doubleCounter_value, hq, hlegs, hbody,
    Parameters.dimension, BackgroundRates.ordinaryPool, and_self]

def controlsEquiv (security : ℕ) : Fin (current security).controls ≃ PublicOutputExperiment.PublicIndex security :=
  (finCongr (current_values security).2.2.2.2.2).trans finSumFinEquiv.symm

def legEquiv (security : ℕ) : Fin (current security).legs ≃ Fin (Parameters.legCount security) :=
  finCongr (current_values security).2.1

def queueEquiv (security : ℕ) : Fin (current security).colors ≃ Fin (Parameters.modulus security) :=
  finCongr (current_values security).1

def bodyEquiv (security : ℕ) : Fin (current security).body ≃ ActualCycleMeanMGF.BodyIndex security :=
  finCongr (current_values security).2.2.1

def endpointEquiv (security : ℕ) : Fin (current security).dimension ≃ Fin (Parameters.dimension security) :=
  finCongr (current_values security).2.2.2.1

end CurrentAFT.CurrentProposalDimensions

end

section




















/-! Uniform current-parameter work and length bounds for public shifts. -/

namespace CurrentAFT.CurrentPublicShiftProgram

open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
set_option maxHeartbeats 500000







def workBound (security : ℕ) : ℕ :=
  let base := security + 2
  let q := 131072 * base ^ 64
  let width := base ^ 48
  let cutoff := base ^ 2
  PublicParameterProgram.workBound security + (2 * security + 1) + powerCounterWork base 48 +
    programWork q width q width cutoff cutoff + 3





end CurrentAFT.CurrentPublicShiftProgram

end

section























/-! Explicit polynomial resources for current proposal metadata and public shifts. -/
namespace CurrentAFT.CurrentProposalResources
open AFT AFT.BinaryArithmetic CurrentProposalDimensions
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
attribute [local irreducible] BinaryProposalMetadata.counts CurrentProposalDimensions.current

noncomputable def countPolynomial : Polynomial ℕ := 3 * BinaryProposalMetadata.sizePolynomial
noncomputable def metadataWorkPolynomial : Polynomial ℕ :=
  BinaryProposalMetadata.countsWorkPolynomial + 11 * BinaryProposalMetadata.sizePolynomial + 13

 theorem count_bounds (security : ℕ) :
    (current security).controls ≤ countPolynomial.eval security ∧
    (current security).legs ≤ countPolynomial.eval security ∧
    (current security).colors ≤ countPolynomial.eval security ∧
    (current security).body ≤ countPolynomial.eval security ∧
    (current security).dimension ≤ countPolynomial.eval security := by
  rcases BinaryProposalMetadata.counts_bounds security with ⟨hq, hl, hb⟩
  simp only [countPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat, BinaryProposalMetadata.sizePolynomial_eval]
  simp only [CurrentProposalDimensions.current, addCounter_value, subtractCounter_value, doubleCounter_value]
  omega

 theorem metadata_work (security : ℕ) :
    (current security).work ≤ metadataWorkPolynomial.eval security := by
  let sizes := BinaryProposalMetadata.counts security
  have hs := BinaryProposalMetadata.counts_work security
  have hl : sizes.legs ≤ BinaryProposalMetadata.sizeBound security := (BinaryProposalMetadata.counts_bounds security).2.1
  have hb : sizes.population ≤ BinaryProposalMetadata.sizeBound security := (BinaryProposalMetadata.counts_bounds security).2.2
  have hn := subtractCounter_work_left sizes.population sizes.colors
  have ho := subtractCounter_work_left (subtractCounter sizes.population sizes.colors).count (doubleCounter sizes.legs).count
  have hnc : (subtractCounter sizes.population sizes.colors).count ≤ sizes.population := by
    rw [subtractCounter_value]; exact Nat.sub_le _ _
  change sizes.work ≤ _ at hs
  unfold CurrentProposalDimensions.current
  change sizes.work + (doubleCounter sizes.legs).work +
    (addCounter sizes.population (doubleCounter sizes.legs).count).work +
    (subtractCounter sizes.population sizes.colors).work +
    (subtractCounter (subtractCounter sizes.population sizes.colors).count (doubleCounter sizes.legs).count).work +
    (addCounter sizes.legs _).work + 6 ≤ _
  simp only [doubleCounter_work, addCounter_work, metadataWorkPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    BinaryProposalMetadata.countsWorkPolynomial_eval, BinaryProposalMetadata.sizePolynomial_eval]
  omega

noncomputable def primeSizePolynomial : Polynomial ℕ := 131072 * (Polynomial.X + 2)^64
noncomputable def anchorSizePolynomial : Polynomial ℕ := (Polynomial.X + 2)^48
noncomputable def cutoffSizePolynomial : Polynomial ℕ := (Polynomial.X + 2)^2

noncomputable def shiftWorkPolynomial : Polynomial ℕ :=
  let q := primeSizePolynomial
  let width := anchorSizePolynomial
  let cutoff := cutoffSizePolynomial
  PublicParameterProgram.workPolynomial + 2 * Polynomial.X + 1 +
    49 * (6 * (Polynomial.X + 3)^50 + 4) +
    ((15*q + 8*q + 9) + (2*width + 1) + 50*(width+width+1)^2 +
      (50*(cutoff+1)^2+1) + (50*(cutoff+1)^2+1) +
      (20*(cutoff+cutoff)+13) + (20*(width+width+cutoff+cutoff+1)+9)+7) + 3

 theorem shiftWorkPolynomial_eval (security : ℕ) :
    shiftWorkPolynomial.eval security = CurrentPublicShiftProgram.workBound security := by
  simp only [shiftWorkPolynomial, primeSizePolynomial, anchorSizePolynomial, cutoffSizePolynomial,
    CurrentPublicShiftProgram.workBound, CurrentPublicShiftProgram.programWork, powerCounterWork,
    PublicParameterProgram.workPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  norm_num only
  simp only [show security + 2 + 1 = security + 3 by omega, Nat.add_assoc]

 

end
end CurrentAFT.CurrentProposalResources

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentProposalResources.countPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentProposalResources.metadataWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.CurrentProposalResources.primeSizePolynomial
  pure ()

end

section




/-! # Zero padding of the calibration defect in rectangular storage

The full response is the identity on unused rectangular coordinates.
Equivalently its defect, right-hand side, and every iterate vanish there.
This exact data statement allows rectangular array reads without changing
any joint safe-palette coordinate of the calibration algorithm.
-/
namespace CurrentAFT.CalibrationRectanglePadding
open AFT RationalNumerics
open scoped BigOperators

variable {Small Large : Type*}

def extend {Scalar : Type*} [Zero Scalar] (decode : Large → Option Small)
    (table : Small → Scalar) (point : Large) : Scalar :=
  (decode point).elim 0 table

def defect {Scalar : Type*} [Zero Scalar] (decode : Large → Option Small)
    (matrix : Small → Small → Scalar) (output input : Large) : Scalar :=
  (decode output).elim 0 (fun out => (decode input).elim 0 (matrix out))

section
variable [Fintype Small] [Fintype Large]
variable (encode : Small ↪ Large) (decode : Large → Option Small)
variable (hdecode : ∀ point small, decode point = some small ↔ point = encode small)
include encode hdecode













end
end CurrentAFT.CalibrationRectanglePadding

end

section




/-! # Executable inverse coordinates for complete joint tables -/
namespace CurrentAFT.WeightCoordinates
set_option maxHeartbeats 600000

def tupleDecode (base : ℕ) (hb : 0 < base) : (count : ℕ) → ℕ → (Fin count → Fin base)
  | 0, _ => Fin.elim0
  | count+1, code => Fin.lastCases ⟨code % base, Nat.mod_lt _ hb⟩
      (tupleDecode base hb count (code / base))

theorem tupleDecode_code (base count : ℕ) (hb : 0 < base) (word : Fin count → Fin base) :
    tupleDecode base hb count (tupleCode base count (fun index => (word index).val)) = word := by
  induction count with
  | zero => exact Subsingleton.elim _ _
  | succ count ih =>
    funext index
    refine Fin.lastCases ?_ (fun index => ?_) index
    · apply Fin.ext
      simp only [tupleDecode, Fin.lastCases_last, tupleCode, Nat.mul_add_mod_self_left,
        Nat.mod_eq_of_lt (word (Fin.last count)).isLt]
    · simp only [tupleDecode, Fin.lastCases_castSucc, tupleCode]
      have hd : (base * tupleCode base count (fun index => (word index.castSucc).val) +
          (word (Fin.last count)).val) / base =
          tupleCode base count (fun index => (word index.castSucc).val) := by
        rw [Nat.mul_add_div hb, Nat.div_eq_of_lt (word (Fin.last count)).isLt, Nat.add_zero]
      rw [hd, ih]

theorem tupleCode_decode (base count : ℕ) (hb : 0 < base) (code : ℕ) (hc : code < base^count) :
    tupleCode base count (fun index => (tupleDecode base hb count code index).val) = code := by
  induction count generalizing code with
  | zero => simp only [pow_zero] at hc; simp only [tupleCode]; omega
  | succ count ih =>
    have hdiv : code / base < base^count := by
      apply (Nat.div_lt_iff_lt_mul hb).mpr
      simpa only [pow_succ] using hc
    simp only [tupleCode, tupleDecode, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [ih (code / base) hdiv]
    exact Nat.div_add_mod code base

theorem tupleCode_injective (base count : ℕ) (hb : 0 < base) : Function.Injective
    (fun word : Fin count → Fin base => tupleCode base count (fun index => (word index).val)) := by
  intro first second he
  have h := congrArg (tupleDecode base hb count) he
  simpa only [tupleDecode_code] using h

theorem jointCode_div (base r s : ℕ) (hb : 0 < base)
    (primary : Fin r → Fin base) (body : Fin s → Fin base) :
    jointCode base r s (fun i => (primary i).val) (fun i => (body i).val) / base^s =
      tupleCode base r (fun i => (primary i).val) := by
  unfold jointCode
  rw [Nat.mul_add_div (pow_pos hb s), Nat.div_eq_of_lt
    (tupleCode_lt base s hb _ (fun i => (body i).isLt)), Nat.add_zero]

theorem jointCode_mod (base r s : ℕ) (hb : 0 < base)
    (primary : Fin r → Fin base) (body : Fin s → Fin base) :
    jointCode base r s (fun i => (primary i).val) (fun i => (body i).val) % base^s =
      tupleCode base s (fun i => (body i).val) := by
  unfold jointCode
  rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (tupleCode_lt base s hb _ (fun i => (body i).isLt))]

theorem jointCode_injective (base r s : ℕ) (hb : 0 < base) : Function.Injective
    (fun pair : (Fin r → Fin base) × (Fin s → Fin base) =>
      jointCode base r s (fun i => (pair.1 i).val) (fun i => (pair.2 i).val)) := by
  rintro ⟨firstPrimary, firstBody⟩ ⟨secondPrimary, secondBody⟩ he
  have hp := congrArg (fun value => value / base^s) he
  have hb' := congrArg (fun value => value % base^s) he
  simp only [jointCode_div base r s hb] at hp
  simp only [jointCode_mod base r s hb] at hb'
  exact Prod.ext (tupleCode_injective base r hb hp) (tupleCode_injective base s hb hb')

end CurrentAFT.WeightCoordinates

end

section

















/-! # Explicit finite coordinates of safe joint points in rectangular arrays

Enumeration is by integer counters, and the inverse searches this bounded
list. The list has at most `(D+1)^2 q^D` entries; no finite-choice enumeration
or subset of an exponentially larger latent space is used.
-/
namespace CurrentAFT.RectanglePointIndex
open AFT GradedControlAlgebra WeightCoordinates
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev Point (base order : ℕ) (safe : Fin base → Prop) :=
  CalibrationPointCoordinates.PointIndex (Fin base) {color : Fin base // safe color} order
abbrev Rectangle (base order : ℕ) := Fin ((order+1)^2) × Fin (base^order)

def encode (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop)
    (point : Point base order safe) : Rectangle base order :=
  (arityIndex order point.1.val.1 point.1.val.2,
    wordIndex base order point.1.val.1.val point.1.val.2.val hb point.1.property
      point.2.1 (fun index => (point.2.2 index).val))

def words (base count : ℕ) (hb : 0 < base) : List (Fin count → Fin base) :=
  List.ofFn (fun index : Fin (base^count) => tupleDecode base hb count index.val)

def arities (order : ℕ) : List (TruncatedArity order) :=
  (List.finRange (order+1)).flatMap (fun first =>
    (List.finRange (order+1)).filterMap (fun second =>
      if h : first.val + second.val ≤ order then some ⟨(first, second), h⟩ else none))

def atArity (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe]
    (arity : TruncatedArity order) : List (Point base order safe) :=
  (words base arity.val.1.val hb).flatMap (fun primary =>
    (words base arity.val.2.val hb).filterMap (fun body =>
      if h : ∀ index, safe (body index) then
        some ⟨arity, primary, fun index => ⟨body index, h index⟩⟩ else none))

def points (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe] :
    List (Point base order safe) :=
  (arities order).flatMap (atArity base order hb safe)

def decode (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) [DecidablePred safe]
    (index : Rectangle base order) : Option (Point base order safe) :=
  (points base order hb safe).find? (fun point => decide (encode base order hb safe point = index))

theorem encode_injective (base order : ℕ) (hb : 0 < base) (safe : Fin base → Prop) :
    Function.Injective (encode base order hb safe) := by
  rintro ⟨arity, primary, body⟩ ⟨arity', primary', body'⟩ he
  have ha := arityCode_injective order (congrArg Prod.fst he)
  have haa : arity = arity' := Subtype.ext ha
  subst arity'
  have hw := congrArg (fun index : Rectangle base order => index.2.val) he
  have hh : (primary, fun i => (body i).val) = (primary', fun i => (body' i).val) :=
    jointCode_injective base arity.val.1.val arity.val.2.val hb hw
  have hp := congrArg Prod.fst hh
  have hb' := congrArg Prod.snd hh
  have hb'' : body = body' := by
    funext index
    exact Subtype.ext (congrFun hb' index)
  cases hp
  cases hb''
  rfl





















end CurrentAFT.RectanglePointIndex

end

section























/-! # Actual checked modulus and safe palette in rectangular calibration storage -/
namespace CurrentAFT.CurrentRectangleIndex
open AFT GradedControlAlgebra
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def colors (security : ℕ) : ℕ := (PublicParameterProgram.modulus security).count

def safe (security : ℕ) (color : Fin (colors security)) : Prop :=
  ((3 * (security+2)^2 : ℕ) : ℤ) ≤ color.val ∧
    (color.val : ℤ) < (colors security : ℤ) - ((3 * (security+2)^2 : ℕ) : ℤ)

instance safeDecidable (security : ℕ) : DecidablePred (safe security) := fun color => by
  unfold safe
  infer_instance

theorem colors_eq (security : ℕ) : colors security = Parameters.modulus security :=
  PublicParameterProgram.modulus_value security

theorem colors_pos (security : ℕ) : 0 < colors security := by
  rw [colors_eq]
  exact (Parameters.modulus_spec security).2.pos

def paletteEquiv (security : ℕ) : Fin (colors security) ≃ ActualControls.Palette security :=
  finCongr (colors_eq security)

theorem safe_iff (security : ℕ) (color : Fin (colors security)) :
    safe security color ↔ InwardAnchor.SafeColor security (paletteEquiv security color) := by
  simp only [safe, InwardAnchor.SafeColor, paletteEquiv, finCongr_apply, Fin.val_cast,
    colors_eq, Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]

def safeEquiv (security : ℕ) : {color : Fin (colors security) // safe security color} ≃ ActualControls.SafePalette security where
  toFun color := ⟨paletteEquiv security color.val, (safe_iff security color.val).mp color.property⟩
  invFun color := ⟨(paletteEquiv security).symm color.val, (safe_iff security _).mpr (by
    simpa only [Equiv.apply_symm_apply] using color.property)⟩
  left_inv color := by apply Subtype.ext; exact (paletteEquiv security).symm_apply_apply color.val
  right_inv color := by apply Subtype.ext; exact (paletteEquiv security).apply_symm_apply color.val

def pointEquiv (security order : ℕ) :
    RectanglePointIndex.Point (colors security) order (safe security) ≃
      CalibrationPointCoordinates.PointIndex (ActualControls.Palette security) (ActualControls.SafePalette security) order :=
  Equiv.sigmaCongrRight (fun arity : TruncatedArity order =>
    Equiv.prodCongr (Equiv.piCongrRight (fun _ : Fin arity.val.1.val => paletteEquiv security))
      (Equiv.piCongrRight (fun _ : Fin arity.val.2.val => safeEquiv security)))

abbrev Rectangle (security order : ℕ) := RectanglePointIndex.Rectangle (colors security) order
abbrev Point (security order : ℕ) :=
  CalibrationPointCoordinates.PointIndex (ActualControls.Palette security) (ActualControls.SafePalette security) order

def encode (security order : ℕ) : Point security order ↪ Rectangle security order where
  toFun point := RectanglePointIndex.encode (colors security) order (colors_pos security) (safe security)
    ((pointEquiv security order).symm point)
  inj' := (RectanglePointIndex.encode_injective _ _ _ _).comp (pointEquiv security order).symm.injective

def decode (security order : ℕ) (index : Rectangle security order) : Option (Point security order) :=
  (RectanglePointIndex.decode (colors security) order (colors_pos security) (safe security) index).map
    (pointEquiv security order)



def defect (security order : ℕ) (matrix : Point security order → Point security order → ℚ) :
    Rectangle security order → Rectangle security order → ℚ :=
  CalibrationRectanglePadding.defect (decode security order) matrix

def rhs (security order : ℕ) : Rectangle security order → ℚ :=
  CalibrationRectanglePadding.extend (decode security order)
    (fun point => if point.1.val.1.val + point.1.val.2.val = 0 then 1 else 0)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _









end
end CurrentAFT.CurrentRectangleIndex

end

section






/-! Native base-q padding of bounded grouped sources. A primary has two
roots and one control; an ordinary group has one root and a safe control;
a retained group has one root. Padding is checked explicitly. -/
namespace CurrentAFT.GroupSourcePadding
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

inductive Kind where
  | primary
  | ordinary
  | kept
  deriving DecidableEq

def Input (q : ℕ) (safe : Fin q → Prop) : Kind → Type
  | .primary => (Fin 2 → Fin q) × Fin q
  | .ordinary => (Fin 1 → Fin q) × {color : Fin q // safe color}
  | .kept => (Fin 1 → Fin q) × Unit

instance inputFintype (q : ℕ) (safe : Fin q → Prop) [DecidablePred safe] (kind : Kind) : Fintype (Input q safe kind) := by
  cases kind <;> unfold Input <;> infer_instance

def encode (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) : (kind : Kind) → Input q safe kind → (Fin 3 → Fin q)
  | .primary, input => ![input.1 0, input.1 1, input.2]
  | .ordinary, input => ![input.1 0, input.2.val, ⟨0, hq⟩]
  | .kept, input => ![input.1 0, ⟨0, hq⟩, ⟨0, hq⟩]

def Valid (q : ℕ) (safe : Fin q → Prop) : Kind → (Fin 3 → Fin q) → Prop
  | .primary, _ => True
  | .ordinary, word => safe (word 1) ∧ (word 2).val = 0
  | .kept, word => (word 1).val = 0 ∧ (word 2).val = 0

instance validDecidable (q : ℕ) (safe : Fin q → Prop) [DecidablePred safe] (kind : Kind) (word : Fin 3 → Fin q) :
    Decidable (Valid q safe kind word) := by
  cases kind <;> unfold Valid <;> infer_instance

def recover (q : ℕ) (safe : Fin q → Prop) : (kind : Kind) → (word : Fin 3 → Fin q) → Valid q safe kind word → Input q safe kind
  | .primary, word, _ => (![word 0, word 1], word 2)
  | .ordinary, word, h => (fun _ => word 0, ⟨word 1, h.1⟩)
  | .kept, word, _ => (fun _ => word 0, ())

theorem encode_valid (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) (kind : Kind) (input : Input q safe kind) :
    Valid q safe kind (encode q hq safe kind input) := by
  cases kind with
  | primary => trivial
  | ordinary => exact ⟨input.2.property, rfl⟩
  | kept => exact ⟨rfl, rfl⟩

theorem recover_encode (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) (kind : Kind) (input : Input q safe kind) :
    recover q safe kind (encode q hq safe kind input) (encode_valid q hq safe kind input) = input := by
  cases kind with
  | primary =>
    apply Prod.ext
    · funext slot
      fin_cases slot <;> rfl
    · rfl
  | ordinary =>
    apply Prod.ext
    · funext slot
      fin_cases slot
      rfl
    · rfl
  | kept =>
    apply Prod.ext
    · funext slot
      fin_cases slot
      rfl
    · exact Subsingleton.elim _ _



theorem encode_injective (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) (kind : Kind) :
    Function.Injective (encode q hq safe kind) := by
  intro first second h
  have hh := congrArg (fun word : {word // Valid q safe kind word} => recover q safe kind word.val word.property)
    (show (⟨encode q hq safe kind first, encode_valid q hq safe kind first⟩ : {word // Valid q safe kind word}) =
      ⟨encode q hq safe kind second, encode_valid q hq safe kind second⟩ from Subtype.ext h)
  simpa only [recover_encode] using hh

section Grouped
variable {Group : Type*} [Fintype Group] (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) [DecidablePred safe]
  (kind : Group → Kind)

abbrev Source := (group : Group) → Input q safe (kind group)
abbrev Word := Group → Fin 3 → Fin q

instance sourceFintype [DecidableEq Group] : Fintype (Source q safe kind) :=
  Pi.instFintype

def sourceEncode (source : Source q safe kind) : Word (Group := Group) q :=
  fun group => encode q hq safe (kind group) (source group)

def sourceDecode (word : Word (Group := Group) q) : Option (Source q safe kind) :=
  if h : ∀ group, Valid q safe (kind group) (word group) then
    some (fun group => recover q safe (kind group) (word group) (h group)) else none



omit [Fintype Group] [DecidablePred safe] in
theorem sourceEncode_injective : Function.Injective (sourceEncode q hq safe kind) := by
  intro first second h
  funext group
  exact encode_injective q hq safe (kind group) (congrFun h group)



end Grouped

def flatten {Group : Type*} (count q : ℕ) (ordering : Fin count ≃ Group) :
    (Group → Fin 3 → Fin q) ≃ (Fin (count*3) → Fin q) where
  toFun word index := word (ordering (finProdFinEquiv.symm index).1) (finProdFinEquiv.symm index).2
  invFun word group slot := word (finProdFinEquiv (ordering.symm group, slot))
  left_inv word := by funext group slot; simp
  right_inv word := by
    funext index
    dsimp only
    rw [Equiv.symm_apply_apply]
    exact congrArg word (finProdFinEquiv.apply_symm_apply index)

def tupleEquiv (q count : ℕ) (hq : 0 < q) : (Fin count → Fin q) ≃ Fin (q^count) where
  toFun word := ⟨WeightCoordinates.tupleCode q count (fun index => (word index).val),
    WeightCoordinates.tupleCode_lt q count hq _ (fun index => (word index).isLt)⟩
  invFun index := WeightCoordinates.tupleDecode q hq count index.val
  left_inv word := WeightCoordinates.tupleDecode_code q count hq word
  right_inv index := by apply Fin.ext; exact WeightCoordinates.tupleCode_decode q count hq index.val index.isLt

section Indexed
variable {Group : Type*} [Fintype Group] [DecidableEq Group] (q : ℕ) (hq : 0 < q) (safe : Fin q → Prop) [DecidablePred safe]
  (kind : Group → Kind) (count : ℕ) (ordering : Fin count ≃ Group)

def indexEquiv : Word (Group := Group) q ≃ Fin (q^(count*3)) :=
  (flatten count q ordering).trans (tupleEquiv q (count*3) hq)

def indexEncode : Source q safe kind ↪ Fin (q^(count*3)) where
  toFun source := indexEquiv q hq count ordering (sourceEncode q hq safe kind source)
  inj' := (indexEquiv q hq count ordering).injective.comp (sourceEncode_injective q hq safe kind)

def indexDecode (index : Fin (q^(count*3))) : Option (Source q safe kind) :=
  sourceDecode q safe kind ((indexEquiv q hq count ordering).symm index)





end Indexed
end CurrentAFT.GroupSourcePadding

end

section





















/-! # The actual root response with signed masses instead of root densities

Every tagged root reference factor is absorbed into its centered cycle
coefficient. The remaining factors are ordinary reference probabilities.
This is a data identity in the current canonical family algebra, including
zero root atoms, and exposes the bounded sparse-cycle program interface.
-/
namespace CurrentAFT.RootWeightedSynthesis
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance nativeVertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) := instDecidableEqFin _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

abbrev RootSlot {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) := Sigma (groupRootSlots selection tagged)

def taggedOutput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : GroupInput selection tagged) : Fin tagged.card → Root security :=
  fun index => (source (sourceEmbedding selection tagged index).fst).1 (sourceEmbedding selection tagged index).snd

def untaggedWeight {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : GroupInput selection tagged) : ℝ :=
  ∏ slot ∈ (Finset.univ.map (sourceEmbedding selection tagged))ᶜ,
    (rootReference security).weight ((source slot.fst).1 slot.snd)

def weightedCoefficient {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (source : GroupInput selection tagged) : ℝ :=
  (rootLaw security).expectation
    (fun input => ∏ index, ((if input (labels tagged layout index) = taggedOutput selection tagged source index then (1 : ℝ) else 0) -
      (rootReference security).weight (taggedOutput selection tagged source index)))









end
end CurrentAFT.RootWeightedSynthesis

end

section























/-! The native three-slot source enumeration equals the actual grouped
root source sum. This transports the whole joint summand, without
factoring either a paired control or the common queue. -/
namespace CurrentAFT.CurrentGroupSourcePadding
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GroupSourcePadding CurrentRectangleIndex
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def groupKind {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → Kind
  | .inl (.inl _) => .primary
  | .inl (.inr _) => .ordinary
  | .inr _ => .kept

def rootEquiv (security : ℕ) : Fin (colors security) ≃ CycleRootExpansion.Root security :=
  (paletteEquiv security).trans (ZMod.finEquiv (Parameters.modulus security)).toEquiv

def groupEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    Input (colors security) (safe security) (groupKind selection tagged group) ≃
      ((groupRootSlots selection tagged group → CycleRootExpansion.Root security) ×
        ControlInput selection tagged group) := by
  rcases group with (primary | ordinary) | kept
  · exact Equiv.prodCongr (Equiv.piCongrRight (fun _ => rootEquiv security)) (paletteEquiv security)
  · exact Equiv.prodCongr (Equiv.piCongrRight (fun _ => rootEquiv security)) (safeEquiv security)
  · exact Equiv.prodCongr (Equiv.piCongrRight (fun _ => rootEquiv security)) (Equiv.refl Unit)

def sourceEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    Source (colors security) (safe security) (groupKind selection tagged) ≃ GroupInput selection tagged :=
  Equiv.piCongrRight (groupEquiv selection tagged)

def groupOrdering {security r s k : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (keptOrdering : Fin k ≃ HitKept selection tagged) :
    Fin ((r+s)+k) ≃ ActiveGroup selection tagged :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm keptOrdering)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def decode {security r s k : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (keptOrdering : Fin k ≃ HitKept selection tagged)
    (index : Fin ((colors security)^(((r+s)+k)*3))) : Option (GroupInput selection tagged) :=
  (indexDecode (colors security) (colors_pos security) (safe security) (groupKind selection tagged)
    ((r+s)+k) (groupOrdering selection tagged keptOrdering) index).map (sourceEquiv selection tagged)







end
end CurrentAFT.CurrentGroupSourcePadding

end

section















/-! # Products of distinct local coefficient tables in an explicitly ordered word -/
namespace CurrentAFT.RationalFamilyWordProduct
open AFT ActualControls ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def current {Scalar Primary Body : Type*} [Field Scalar] (order : ℕ) :
    (count : ℕ) → (Fin count → Table Scalar Primary Body order) → Table Scalar Primary Body order
  | 0, _ => unit order
  | count+1, tables => product order (current order count (fun index => tables index.succ)) (tables 0)

noncomputable section
open scoped Classical
local instance wordProductFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _











end
end CurrentAFT.RationalFamilyWordProduct

end

section






















/-! # Actual point bounds for fixed-root local numerator coefficients

The estimates use the actual positive primary atoms, finite coefficient
extraction and the actual tensor inverse. No root probability is divided
out, and the resulting bounds are polynomials in current public parameters.
-/
namespace CurrentAFT.LegCoefficientPointBounds
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw







def selectedBound (security : ℕ) (massBound : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^3 * (1 + RationalTensorInverseProgram.actualBound security)^3 *
    ((Parameters.modulus security : ℝ)^3 * massBound * (4 * (Parameters.modulus security : ℝ))^3)













end
end CurrentAFT.LegCoefficientPointBounds

end

section






















/-! # Explicit point tables of the centered primary numerator family

Each of the fifteen nonempty physical slot subsets is inserted in its
actual arity. The constant and all body fibers are set to zero, as proved
for the centered primary experiment.
-/
namespace CurrentAFT.RationalLocalFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def insertSelected {Scalar Primary Body : Type*} [Zero Scalar] (order : ℕ)
    (selected : Finset (Fin 4)) (value : (Fin selected.card → Primary) → Scalar) :
    RationalFamilyProductProgram.Table Scalar Primary Body order :=
  fun arity colors _ => if hmatch : selected.card = arity.val.1.val ∧ 0 = arity.val.2.val then
    value (colors ∘ finCongr hmatch.1) else 0

def numerator (security bits order : ℕ) (compensatorRoot attachmentRoot : ℤ) (primaryColor : ℕ) :
    RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  fun arity colors centers => ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
    insertSelected order selected
      (RationalPrimaryColumnProgram.current security bits compensatorRoot attachmentRoot primaryColor selected)
        arity colors centers

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw











def numeratorErrorConstant (security : ℕ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
    RationalPrimaryColumnProgram.errorConstant security selected.card



end
end CurrentAFT.RationalLocalFamilyProgram

end

section




















/-! # Actual point bounds for fixed-root local numerator coefficients

The estimates use the actual positive primary atoms, finite coefficient
extraction and the actual tensor inverse. No root probability is divided
out, and the resulting bounds are polynomials in current public parameters.
-/
namespace CurrentAFT.LocalCoefficientPointBounds
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw







def selectedBound (security : ℕ) (massBound : ℝ) : ℝ :=
  (Parameters.modulus security : ℝ)^4 * (1 + RationalTensorInverseProgram.actualBound security)^4 *
    ((Parameters.modulus security : ℝ)^4 * massBound * (4 * (Parameters.modulus security : ℝ))^4)





def numeratorBound (security : ℕ) : ℝ := 16 * selectedBound security (2 * (Parameters.modulus security : ℝ)^2)





end
end CurrentAFT.LocalCoefficientPointBounds

end

section













/-! # Polynomial point bounds for the actual independent positive family -/
namespace CurrentAFT.PositiveFamilyPointBound
open AFT ProposalPrimary ActualControls LocalCoefficientFamily NormalizedLocalPolynomial
  LocalRaisingBounds GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def bound (security order : ℕ) : ℝ :=
  (2 * (Parameters.modulus security : ℝ) * Parameters.dimension security)^order * (1 + positiveConstant)









end
end CurrentAFT.PositiveFamilyPointBound

end

section





















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.RationalFamilyProductProgram
end CurrentAFT.RationalFamilyProductProgram




/-! # The actual positive local reference as a rational coefficient table -/
namespace CurrentAFT.RationalPositiveFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def coefficient (security bits : ℕ) (selected : Finset (Fin 4)) (output : Fin selected.card → ℕ) : ℚ :=
  RationalCoefficientExtraction.selectedKernel security bits (RationalPositiveReferenceProgram.current security bits) selected output

def positive (security bits order : ℕ) : Table ℚ ℕ ℕ order :=
  fun arity colors centers => unit order arity colors centers +
    ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅,
      RationalLocalFamilyProgram.insertSelected order selected (coefficient security bits selected) arity colors centers

def inverse (security bits order : ℕ) : Table ℚ ℕ ℕ order := reciprocal order (positive security bits order)

def primaryChannel (security bits order : ℕ) (compensatorRoot attachmentRoot : ℤ) (primaryColor : ℕ) : Table ℚ ℕ ℕ order :=
  product order (RationalLocalFamilyProgram.numerator security bits order compensatorRoot attachmentRoot primaryColor)
    (inverse security bits order)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def coefficientError (security degree : ℕ) : ℝ :=
  RationalCoefficientExtraction.normalizedError security degree 1 (RationalPositiveReferenceProgram.errorConstant security)











def errorConstant (security : ℕ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).erase ∅, coefficientError security selected.card



end
end CurrentAFT.RationalPositiveFamilyProgram

end

section


























/-! # Actual normalized primary columns from rational finite reciprocals -/
namespace CurrentAFT.RationalNormalizedPrimaryProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def lifted (security order : ℕ) (table : Table ℚ ℕ ℕ order) : Table ℝ (Palette security) (SafePalette security) order :=
  pullback order (fun color : Palette security => color.val) (fun color : SafePalette security => color.val.val)
    (realTable order table)







def inverseBound (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ) * (growth order (1 + PositiveFamilyPointBound.bound security order) 0)^order





def inverseErrorConstant (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ)^2 * RationalPositiveFamilyProgram.errorConstant security *
    (growth order (1 + PositiveFamilyPointBound.bound security order)
      (RationalPositiveFamilyProgram.errorConstant security))^(order + 1)







def primaryErrorConstant (security order : ℕ) : ℝ :=
  (Nat.card (TruncatedArity order) : ℝ)^2 *
    (RationalLocalFamilyProgram.numeratorErrorConstant security * inverseBound security order +
      (LocalCoefficientPointBounds.numeratorBound security + RationalLocalFamilyProgram.numeratorErrorConstant security) *
        inverseErrorConstant security order)



end
end CurrentAFT.RationalNormalizedPrimaryProgram

end

section
























/-! # Rational pure-primary singleton columns and their actual finite reciprocals -/
namespace CurrentAFT.RationalSingletonProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls RootTaggedLocal
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram
open UniformBodyProfiles (BodyRole)
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def first (security bits order : ℕ) (role : BodyRole) (queue root : ℤ) : Table ℚ ℕ ℕ order :=
  RationalBackgroundTable.firstTable order (RationalRootProfileProgram.firstDensity security bits role queue root) (fun _ => 0)

def positive (security bits order : ℕ) (role : BodyRole) (queue : ℤ) : Table ℚ ℕ ℕ order :=
  unit order + RationalBackgroundTable.firstTable order (RationalRootProfileProgram.meanDensity security bits role queue) (fun _ => 0)

def inverse (security bits order : ℕ) (role : BodyRole) (queue : ℤ) : Table ℚ ℕ ℕ order :=
  reciprocal order (positive security bits order role queue)

def current (security bits order : ℕ) (role : BodyRole) (queue root : ℤ) : Table ℚ ℕ ℕ order :=
  product order (first security bits order role queue root) (inverse security bits order role queue)

noncomputable section
open scoped Classical
local instance programFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

















def firstBound (security : ℕ) : ℝ := 2 * RationalTensorInverseProgram.actualBound security

def positiveBound (security : ℕ) : ℝ := 1 + firstBound security











def inverseBound (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ) * (growth order (1 + positiveBound security) 0)^order



def inverseErrorConstant (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ)^2 * RationalRootProfileProgram.meanErrorConstant security *
    (growth order (1 + positiveBound security) (RationalRootProfileProgram.meanErrorConstant security))^(order + 1)





def errorConstant (security order : ℕ) : ℝ :=
  (Nat.card (TruncatedArity order) : ℝ)^2 *
    (RationalRootProfileProgram.firstErrorConstant security * inverseBound security order +
      (firstBound security + RationalRootProfileProgram.firstErrorConstant security) * inverseErrorConstant security order)



end
end CurrentAFT.RationalSingletonProgram

end

section


























/-! # The complete actual unselected leg with its pure-primary denominator -/
namespace CurrentAFT.RationalUnselectedLegProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def higher (security bits order : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  RationalLegFamilyTable.higher security bits order (RationalLegMassProgram.difference security bits root)

def positive (security bits order : ℕ) : Table ℚ ℕ ℕ order :=
  RationalLegFamilyTable.positive security bits order (RationalLegMassProgram.mean security bits)

def inverse (security bits order : ℕ) : Table ℚ ℕ ℕ order := reciprocal order (positive security bits order)

def numerator (security bits order : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  RationalSingletonProgram.first security bits order .attachment 0 root + higher security bits order root

def current (security bits order : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  product order (numerator security bits order root) (inverse security bits order)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw

def higherError (security : ℕ) : ℝ :=
  RationalLegFamilyTable.higherError security 2 (RationalLegMassProgram.differenceErrorConstant security)

def positiveError (security : ℕ) : ℝ :=
  RationalLegFamilyTable.positiveError security (RationalLegMassProgram.meanErrorConstant security)









end
end CurrentAFT.RationalUnselectedLegProgram

end

section




















/-! # Accuracy of the original complete pure-primary unselected leg column -/
namespace CurrentAFT.RationalUnselectedLegProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates GradedControlAlgebra
  RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance normalizedFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

def positiveBound (security : ℕ) : ℝ := 1 + 8 * LegCoefficientPointBounds.selectedBound security 1









def inverseBound (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ) * (growth order (1 + positiveBound security) 0)^order

def inverseError (security order : ℕ) : ℝ :=
  ((order + 1 : ℕ) : ℝ)^2 * positiveError security *
    (growth order (1 + positiveBound security) (positiveError security))^(order + 1)







def numeratorActual (security order : ℕ) (horder : 1 ≤ order) (root : CycleRootExpansion.Root security) :
    BackgroundFamilies.ActualFamily security order :=
  RootReferenceColumns.singletonFirstAt security order horder .attachment 0 root + RootReferenceColumns.legHigherAt security order root

def numeratorBound (security : ℕ) : ℝ :=
  RationalSingletonProgram.firstBound security + 8 * LegCoefficientPointBounds.selectedBound security 2

def numeratorError (security : ℕ) : ℝ := RationalRootProfileProgram.firstErrorConstant security + higherError security







def errorConstant (security order : ℕ) : ℝ :=
  productError order (numeratorBound security) (inverseBound security order) (numeratorError security) (inverseError security order)



end
end CurrentAFT.RationalUnselectedLegProgram

end

section






















/-! # The actual root-shifted centered ordinary control column -/
namespace CurrentAFT.RationalOrdinaryProfileProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def preRoot (security bits source output : ℕ) : ℚ :=
  RationalProposalProgram.center security bits source *
    ((if output = source then 1 else 0) - RationalProposalProgram.center security bits output)

def shifted (security bits source : ℕ) (root : ℤ) (output : ℕ) : ℚ :=
  preRoot security bits source (RationalBackgroundProfiles.inverseShift security root output)

def density (security bits source : ℕ) (root : ℤ) (output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (shifted security bits source root) output

noncomputable section
open scoped Classical
local instance ordinaryFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance ordinarySafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus

def actualPreRoot (security : ℕ) (source : SafePalette security) (output : Palette security) : ℝ :=
  (bodyReference security).weight source * ((if output = source.val then 1 else 0) - (centerLaw security).weight output)









def profileErrorConstant (security : ℕ) : ℝ := 2 * RationalBackgroundDensities.centerErrorConstant security



def errorConstant (security : ℕ) : ℝ := RationalMassLiftProgram.errorConstant security +
  RationalTensorInverseProgram.actualBound security * profileErrorConstant security



end
end CurrentAFT.RationalOrdinaryProfileProgram

end

section






















/-! # Literal ordinary hybrid coefficient tables before the outer root sums -/
namespace CurrentAFT.RationalOrdinaryFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def first (security bits order source : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  RationalBackgroundTable.firstTable order (RationalOrdinaryProfileProgram.density security bits source root) (fun _ => 0)

def bodyFirst (security bits order source : ℕ) : Table ℚ ℕ ℕ order :=
  RationalBackgroundTable.firstTable order (fun _ => 0) (WeightedPointKernelProgram.bodyDelta security bits source)

def atRoot (security bits order source : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  product order (first security bits order source root) (RationalSingletonProgram.inverse security bits order .free 0)

def independent (security bits order source : ℕ) : Table ℚ ℕ ℕ order :=
  product order (bodyFirst security bits order source) (RationalSingletonProgram.inverse security bits order .free 0)

def mean (security bits order source : ℕ) : Table ℚ ℕ ℕ order := fun arity colors centers =>
  ∑ root : Fin (PublicParameterProgram.modulus security).count,
    RootSignedMassProgram.referenceEntry security bits root.val * atRoot security bits order source root.val arity colors centers

def current (security bits order source : ℕ) (root : ℤ) : Table ℚ ℕ ℕ order :=
  independent security bits order source + atRoot security bits order source root - mean security bits order source

noncomputable section
open scoped Classical
local instance ordinaryFamilyFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance ordinaryFamilySafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw PublicParameterProgram.modulus

def firstActual (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security) :
    BackgroundFamilies.ActualFamily security order :=
  LocalRaisingLinear.primaryEmbeddingLinear security order horder
    ⟨RootReferenceColumns.ordinaryDensityAt security root (Pi.single source 1),
      RootReferenceColumns.ordinaryDensityAt_mean security root (Pi.single source 1)⟩





















end
end CurrentAFT.RationalOrdinaryFamilyProgram

end

section






















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.RootOrdinaryDataIdentity
end CurrentAFT.RootOrdinaryDataIdentity



/-! # Accuracy of the literal retained-body ordinary hybrid column -/
namespace CurrentAFT.RationalOrdinaryFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance ordinaryNormalizedFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance ordinaryNormalizedSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference PublicParameterProgram.modulus







def atRootError (security order : ℕ) : ℝ := productError order (RationalTensorInverseProgram.actualBound security)
  (RationalSingletonProgram.inverseBound security order) (RationalOrdinaryProfileProgram.errorConstant security)
    (RationalSingletonProgram.inverseErrorConstant security order)

def independentError (security order : ℕ) : ℝ := productError order 1
  (RationalSingletonProgram.inverseBound security order) (RationalBackgroundDensities.centerErrorConstant security)
    (RationalSingletonProgram.inverseErrorConstant security order)





def atRootBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order) : ℝ)^2 *
  (RationalTensorInverseProgram.actualBound security * RationalSingletonProgram.inverseBound security order)





def meanError (security order : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ) * (atRootError security order + 2 * atRootBound security order)





def errorConstant (security order : ℕ) : ℝ := independentError security order + atRootError security order + meanError security order



end
end CurrentAFT.RationalOrdinaryFamilyProgram

end

section






















/-! # All five actual local group columns in one rational dispatch program -/
namespace CurrentAFT.RationalRootGroupProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

inductive LocalRole where
  | primary | ordinary | leg | center | queue
  deriving DecidableEq

def localTable (security bits order : ℕ) (queue : ℤ) (role : LocalRole) (source : Fin 3 → ℕ) : Table ℚ ℕ ℕ order :=
  match role with
  | .primary => RationalPositiveFamilyProgram.primaryChannel security bits order (source 0) (source 1) (source 2)
  | .ordinary => RationalOrdinaryFamilyProgram.current security bits order (source 1) (source 0)
  | .leg => RationalUnselectedLegProgram.current security bits order (source 0)
  | .center => RationalSingletonProgram.current security bits order .free queue (source 0)
  | .queue => RationalSingletonProgram.current security bits order .queue queue (source 0)

noncomputable section
open scoped Classical
local instance groupProgramFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference PublicParameterProgram.modulus

def role {security r s : ℕ} (selection : TaggedSelection.Selection security r s)
    (tagged : Finset (ActualBlockFock.BlockIndex security)) : PairedRootPlacement.ActiveGroup selection tagged → LocalRole
  | .inl (.inl _) => .primary
  | .inl (.inr _) => .ordinary
  | .inr index => match index.val.val with
    | .inl _ => .leg
    | .inr (.inl _) => .center
    | .inr (.inr _) => .queue

def sourceNatural {security r s : ℕ} (selection : TaggedSelection.Selection security r s)
    (tagged : Finset (ActualBlockFock.BlockIndex security)) :
    (group : PairedRootPlacement.ActiveGroup selection tagged) → ActualRootGroupedChannel.Input selection tagged group → (Fin 3 → ℕ)
  | .inl (.inl _), source => ![(source.1 (0 : Fin 2)).val, (source.1 (1 : Fin 2)).val, source.2.val]
  | .inl (.inr _), source => ![(source.1 (0 : Fin 1)).val, source.2.val.val, 0]
  | .inr _, source => ![(source.1 (0 : Fin 1)).val, 0, 0]

def table {security r s : ℕ} (bits order : ℕ) (queue : ℤ) (selection : TaggedSelection.Selection security r s)
    (tagged : Finset (ActualBlockFock.BlockIndex security)) (group : PairedRootPlacement.ActiveGroup selection tagged)
    (source : ActualRootGroupedChannel.Input selection tagged group) : Table ℚ ℕ ℕ order :=
  localTable security bits order queue (role selection tagged group) (sourceNatural selection tagged group source)

def errorConstant (security order : ℕ) : ℝ :=
  |RationalNormalizedPrimaryProgram.primaryErrorConstant security order| +
    |RationalOrdinaryFamilyProgram.errorConstant security order| +
    |RationalUnselectedLegProgram.errorConstant security order| + |RationalSingletonProgram.errorConstant security order|





end
end CurrentAFT.RationalRootGroupProgram

end

section
























/-! # A native base-q program for the whole joint root/control summand

The metadata contain only small role and root-slot arrays. Gaussian,
proposal, inverse and cycle entries are all computed by the existing
rational programs; the source array is enumerated as one joint word.
-/
namespace CurrentAFT.RationalPackedRootProgram
open AFT RationalRootGroupProgram RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure Metadata (primaryDegree bodyDegree keptCount tagCount : ℕ) where
  roles : Fin ((primaryDegree + bodyDegree) + keptCount) → LocalRole
  taggedSlots : Fin tagCount → Fin ((primaryDegree + bodyDegree) + keptCount) × Fin 2

def sourceWord (security groups : ℕ) (index : Fin ((CurrentRectangleIndex.colors security)^(groups*3))) :
    Fin groups → Fin 3 → ℕ :=
  fun group slot => (WeightCoordinates.tupleDecode (CurrentRectangleIndex.colors security)
    (CurrentRectangleIndex.colors_pos security) (groups*3) index.val (finProdFinEquiv (group, slot))).val

def validGroup (security : ℕ) (role : LocalRole) (word : Fin 3 → ℕ) : Prop :=
  match role with
  | .primary => True
  | .ordinary => RationalBackgroundProfiles.Safe security (word 1) ∧ word 2 = 0
  | .leg | .center | .queue => word 1 = 0 ∧ word 2 = 0

instance validGroupDecidable (security : ℕ) (role : LocalRole) (word : Fin 3 → ℕ) : Decidable (validGroup security role word) := by
  cases role <;> unfold validGroup <;> infer_instance

def Valid {r s kept tags : ℕ} (security : ℕ) (metadata : Metadata r s kept tags)
    (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : Prop := ∀ group, validGroup security (metadata.roles group) (word group)

instance validDecidable {r s kept tags : ℕ} (security : ℕ) (metadata : Metadata r s kept tags)
    (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : Decidable (Valid security metadata word) := by
  unfold Valid
  infer_instance

def primaryGroup (r s kept : ℕ) (index : Fin r) : Fin ((r+s)+kept) := ⟨index.val, by omega⟩

def ordinaryGroup (r s kept : ℕ) (index : Fin s) : Fin ((r+s)+kept) := ⟨r + index.val, by omega⟩

def rootActive (role : LocalRole) (slot : Fin 2) : Prop := role = .primary ∨ slot.val = 0

instance rootActiveDecidable (role : LocalRole) (slot : Fin 2) : Decidable (rootActive role slot) := by
  unfold rootActive
  infer_instance

def untagged {r s kept tags : ℕ} (security bits : ℕ) (metadata : Metadata r s kept tags)
    (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : ℚ :=
  ∏ group, ∏ slot : Fin 2,
    if rootActive (metadata.roles group) slot ∧ ¬∃ tag, metadata.taggedSlots tag = (group, slot) then
      RootSignedMassProgram.referenceEntry security bits (word group slot.castSucc) else 1

def control {r s kept tags : ℕ} (security bits : ℕ) (_metadata : Metadata r s kept tags)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : ℚ :=
  WeightedPointKernelProgram.current security bits r s sourcePrimary sourceBody
    (fun index => word (primaryGroup r s kept index) 2) (fun index => word (ordinaryGroup r s kept index) 1)

def signed {r s kept tags : ℕ} (security bits : ℕ) (metadata : Metadata r s kept tags)
    (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : ℚ :=
  RootSignedMassProgram.weightedEntry security bits tags
    (fun tag => word (metadata.taggedSlots tag).1 (metadata.taggedSlots tag).2.castSucc)

def localProduct {r s kept tags : ℕ} (security bits order : ℕ) (queue : ℤ) (metadata : Metadata r s kept tags)
    (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : Table ℚ ℕ ℕ order :=
  RationalFamilyWordProduct.current order ((r+s)+kept)
    (fun group => localTable security bits order queue (metadata.roles group) (word group))

def summand {r s kept tags : ℕ} (security bits order : ℕ) (queue : ℤ) (metadata : Metadata r s kept tags)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) (word : Fin ((r+s)+kept) → Fin 3 → ℕ) : Table ℚ ℕ ℕ order :=
  fun arity colors centers => if Valid security metadata word then
    control security bits metadata sourcePrimary sourceBody word * untagged security bits metadata word * signed security bits metadata word *
      localProduct security bits order queue metadata word arity colors centers else 0

def current {r s kept tags : ℕ} (security bits order : ℕ) (queue : ℤ) (metadata : Metadata r s kept tags)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) : Table ℚ ℕ ℕ order :=
  fun arity colors centers => ∑ index : Fin ((CurrentRectangleIndex.colors security)^(((r+s)+kept)*3)),
    summand security bits order queue metadata sourcePrimary sourceBody
      (sourceWord security ((r+s)+kept) index) arity colors centers



end CurrentAFT.RationalPackedRootProgram

end

section


























/-! The joint root/control source is enumerated by actual nested finite loops.
Every source word is materialized by charged prepend operations. The bijection
to the paper's flat base-q source index is used only in the semantic proof. -/
namespace CurrentAFT.BinaryPackedRootSum
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus

abbrev Source (security groups : ℕ) := Vector (Fin (CurrentRectangleIndex.colors security)) (groups*3)


def current (security groups : ℕ) (kernel : Source security groups → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryTupleSum.current modulus.count (groups*3) kernel
  ⟨result.data, modulus.work+result.work+2⟩

 

noncomputable section

 

 


def heightPolynomial (limit : ℕ) (leafHeight : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count ∈ Finset.range (limit*3+1),
    BinaryTupleSum.heightPolynomial CurrentProposalResources.primeSizePolynomial count leafHeight


def workPolynomial (limit : ℕ) (leafHeight leafWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial +
    (∑ count ∈ Finset.range (limit*3+1),
      BinaryTupleSum.workPolynomial CurrentProposalResources.primeSizePolynomial count leafHeight leafWork) + 2

 

end
end CurrentAFT.BinaryPackedRootSum

end

section





















/-! Bit lengths and costs of each actual sparse-cycle Gaussian summand. -/
namespace CurrentAFT.BinarySparseCycleTermResources
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinarySparseCycleEvaluation
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def rootEntryWork (edges count cutoff : ℕ) : ℕ :=
  3*count+6*edges+100*(2*cutoff+2)^2+20*(2*cutoff+1)+30

 


def rootsWork (edges count cutoff : ℕ) : ℕ := count*(rootEntryWork edges count cutoff+2)+2

 


def weightEntryWork (edges cutoff : ℕ) : ℕ := 3*edges+3*(2*cutoff+1)+8

 


def termHeight (edges gaussianHeight testHeight : ℕ) : ℕ := edges*gaussianHeight+testHeight

def termWork (edges count cutoff gaussianHeight testHeight testWork : ℕ) : ℕ :=
  rootsWork edges count cutoff+testWork+BinaryFiniteProduct.work edges gaussianHeight (weightEntryWork edges cutoff)+
    RationalBits.primitiveWorkBound (termHeight edges gaussianHeight testHeight)+4

 

end CurrentAFT.BinarySparseCycleTermResources

end

section
























/-! Uniform summand and loop budgets for bounded-order sparse cycle evaluation.
The dynamic touched-edge count is at most twice the selected-root order. -/
namespace CurrentAFT.BinarySparseCycleBounds
open AFT GaussianSource RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryTouchedCycle BinaryTouchedCycleBuffer BinaryTouchedCycleRanks
open BinarySparseCycleEvaluation
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

 

 

 

 


def heightLimit (security bits limit cutoff testHeight : ℕ) : ℕ :=
  ∑ edges ∈ Finset.range (2*limit+1), BinaryTupleSum.height (2*cutoff+1) edges
    (BinarySparseCycleTermResources.termHeight (2*limit) (BinaryGaussianAverage.gaussianHeight security bits) testHeight)


def workLimit (security bits body limit cutoff testHeight testWork : ℕ) : ℕ :=
  prepareWork body limit+2*limit+positionsWork body limit+CurrentGaussianBits.tableWork security bits+
    (∑ edges ∈ Finset.range (2*limit+1), BinaryTupleSum.work (2*cutoff+1) edges
      (BinarySparseCycleTermResources.termHeight (2*limit) (BinaryGaussianAverage.gaussianHeight security bits) testHeight)
      (BinarySparseCycleTermResources.termWork (2*limit) limit cutoff (BinaryGaussianAverage.gaussianHeight security bits) testHeight testWork))+5

 

 

end CurrentAFT.BinarySparseCycleBounds

end

section






















/-! Fixed-order polynomial witnesses for the actual sparse Gaussian evaluator.
Body size, numerical precision and the concrete test program have explicit
polynomial budgets; every touched-word and rank operation is included. -/
namespace CurrentAFT.BinarySparseCyclePolynomial
open AFT GaussianSource RationalNumerics BinaryArithmetic
open BinarySparseCycleBounds BinaryTouchedCycleRanks
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def preparePolynomial (body count : Polynomial ℕ) : Polynomial ℕ :=
  count*(3*count+7*body+19)+3+(2*count)*(2*count*(6*body+4)+3)+3

def bufferPolynomial (body count : Polynomial ℕ) : Polynomial ℕ :=
  preparePolynomial body count+(2*count)*(4*count+5)+4

def positionsPolynomial (body count : Polynomial ℕ) : Polynomial ℕ :=
  bufferPolynomial body count+count*(3*count+7*body+2*((2*count)*(6*count+6*body+8)+3)+20)+4

def gaussianHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  500000000*((Polynomial.X+2)^2+precision+2)^6

def termHeightPolynomial (edges gh th : Polynomial ℕ) : Polynomial ℕ := edges*gh+th

def rootEntryPolynomial (edges count cutoff : Polynomial ℕ) : Polynomial ℕ :=
  3*count+6*edges+100*(2*cutoff+2)^2+20*(2*cutoff+1)+30

def rootsPolynomial (edges count cutoff : Polynomial ℕ) : Polynomial ℕ := count*(rootEntryPolynomial edges count cutoff+2)+2

def weightPolynomial (edges cutoff : Polynomial ℕ) : Polynomial ℕ := 3*edges+3*(2*cutoff+1)+8

def termPolynomial (edges count cutoff gh th tw : Polynomial ℕ) : Polynomial ℕ :=
  rootsPolynomial edges count cutoff+tw+
    edges*(weightPolynomial edges cutoff+RationalBits.primitiveWorkPolynomial (edges*gh)+2)+2+
    RationalBits.primitiveWorkPolynomial (termHeightPolynomial edges gh th)+4

 

 

 

 

 


def heightPolynomial (limit : ℕ) (cutoff precision testHeight : Polynomial ℕ) : Polynomial ℕ :=
  ∑ edges ∈ Finset.range (2*limit+1), BinaryTupleSum.heightPolynomial (2*cutoff+1) edges
    (termHeightPolynomial (Polynomial.C (2*limit)) (gaussianHeightPolynomial precision) testHeight)


def workPolynomial (limit : ℕ) (body cutoff precision testHeight testWork : Polynomial ℕ) : Polynomial ℕ :=
  preparePolynomial body (Polynomial.C limit)+Polynomial.C (2*limit)+positionsPolynomial body (Polynomial.C limit)+
    CurrentGaussianBits.workPolynomial precision+
    (∑ edges ∈ Finset.range (2*limit+1), BinaryTupleSum.workPolynomial (2*cutoff+1) edges
      (termHeightPolynomial (Polynomial.C (2*limit)) (gaussianHeightPolynomial precision) testHeight)
      (termPolynomial (Polynomial.C (2*limit)) (Polynomial.C limit) cutoff (gaussianHeightPolynomial precision) testHeight testWork))+5

 

 

 

end
end CurrentAFT.BinarySparseCyclePolynomial

end

section
























/-! The complete distinct-placement sparse cycle average has a polynomial
budget for every fixed order bound, including its computed normalizer. -/
namespace CurrentAFT.BinarySparseCycleAveragePolynomial
open AFT GaussianSource RationalNumerics BinaryArithmetic
open BinarySparseCyclePolynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def distinctWorkPolynomial (pool count : Polynomial ℕ) : Polynomial ℕ :=
  count*(count*(12*count+12*pool+22)+3)+1

 

 


def numeratorHeight (limit : ℕ) (body leafHeight : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count ∈ Finset.range (limit+1), BinaryTupleSum.heightPolynomial body count leafHeight

def numeratorWork (limit : ℕ) (body leafHeight leafWork : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count ∈ Finset.range (limit+1), BinaryTupleSum.workPolynomial body count leafHeight
    (distinctWorkPolynomial body (Polynomial.C count)+leafWork+2)


def heightPolynomial (limit : ℕ) (body cutoff precision th : Polynomial ℕ) : Polynomial ℕ :=
  numeratorHeight limit body (BinarySparseCyclePolynomial.heightPolynomial limit cutoff precision th)+numeratorHeight limit body 0


def workPolynomial (limit : ℕ) (body cutoff precision th tw : Polynomial ℕ) : Polynomial ℕ :=
  numeratorWork limit body (BinarySparseCyclePolynomial.heightPolynomial limit cutoff precision th)
      (BinarySparseCyclePolynomial.workPolynomial limit body cutoff precision th tw)+
    numeratorWork limit body 0 1+
    2*RationalBits.primitiveWorkPolynomial (heightPolynomial limit body cutoff precision th)+5

 

end
end CurrentAFT.BinarySparseCycleAveragePolynomial

end

section






















/-! Executed insertion permutations with both directions stored as finite arrays.
The inverse is found by an explicit scan of the generated forward rows.  All
array reads and integer comparisons are charged. No inverse oracle is used. -/
namespace CurrentAFT.CurrentPermutationDraw

open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 700000

/-- An initial-segment scan, with an arbitrary valid fallback before a hit. -/
def inverseScan {count : ℕ} (rows : Vector (Fin count) count) (target : Fin count) :
    (length : ℕ) → length ≤ count → CountedValue (Fin count)
  | 0, _ => ⟨target, 1⟩
  | length + 1, h =>
    let previous := inverseScan rows target length (by omega)
    let index : Fin count := ⟨length, by omega⟩
    let entry := readVector target rows index
    let equal := equalCounter entry.value.val target.val
    ⟨if equal.value then index else previous.value,
      previous.work + entry.work + equal.work + 3⟩

theorem inverseScan_value {count : ℕ} (rows : Vector (Fin count) count)
    (permutation : Equiv.Perm (Fin count)) (hrows : ∀ index, rows.get index = permutation index)
    (target : Fin count) (length : ℕ) (h : length ≤ count)
    (hhit : (permutation.symm target).val < length) :
    (inverseScan rows target length h).value = permutation.symm target := by
  induction length with
  | zero => omega
  | succ length ih =>
    let index : Fin count := ⟨length, by omega⟩
    have he : (equalCounter (readVector target rows index).value.val target.val).value = true ↔
        permutation index = target := by
      rw [equalCounter_value, readVector_value, hrows]
      exact ⟨fun hh => Fin.ext hh, fun hh => congrArg Fin.val hh⟩
    change (if (equalCounter (readVector target rows index).value.val target.val).value then index
      else (inverseScan rows target length _).value) = _
    by_cases hit : permutation index = target
    · rw [if_pos (he.mpr hit)]
      exact (permutation.apply_eq_iff_eq_symm_apply).mp hit
    · rw [if_neg (by simpa only [he] using hit)]
      apply ih (by omega)
      have hne : permutation.symm target ≠ index := by
        intro hi
        apply hit
        rw [← hi, permutation.apply_symm_apply]
      have hv : (permutation.symm target).val ≠ length := by
        intro hi
        exact hne (Fin.ext hi)
      omega

def inverseScanWork (count length : ℕ) : ℕ := length * (9 * count + 8) + 1



structure CachedPermutation (count : ℕ) where
  forward : Vector (Fin count) count
  inverse : Vector (Fin count) count
  left_inv : ∀ index, inverse.get (forward.get index) = index
  right_inv : ∀ index, forward.get (inverse.get index) = index

def CachedPermutation.toEquiv {count : ℕ} (cached : CachedPermutation count) : Equiv.Perm (Fin count) where
  toFun := cached.forward.get
  invFun := cached.inverse.get
  left_inv := cached.left_inv
  right_inv := cached.right_inv

def draw (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) : CountedValue (CachedPermutation count) :=
  let forward := binaryPermutationFromTape count bits tape
  let inverse := storeData count (fun target => inverseScan forward.value target count le_rfl)
  have he (target : Fin count) : inverse.value.get target = (PermutationProgram.draw count bits tape.get).symm target := by
    rw [storeData_get]
    exact inverseScan_value forward.value (PermutationProgram.draw count bits tape.get)
      (binaryPermutationFromTape_value count bits tape) target count le_rfl (Fin.isLt _)
  ⟨⟨forward.value, inverse.value,
      fun index => by rw [he, binaryPermutationFromTape_value, Equiv.symm_apply_apply],
      fun index => by rw [he, binaryPermutationFromTape_value, Equiv.apply_symm_apply]⟩,
    forward.work + inverse.work + 3⟩







def workBound (count bits : ℕ) : ℕ := binaryPermutationFromTapeWork count bits +
  count * (inverseScanWork count count + 2) + 5



noncomputable section
open scoped Classical

def law (count bits : ℕ) : FiniteDist (Equiv.Perm (Fin count)) :=
  (FiniteDist.uniform (Fin (count * bits) → Fin 2)).map
    (fun word => (draw count bits (Vector.ofFn word)).value.toEquiv)







end
end CurrentAFT.CurrentPermutationDraw

end

section




















/-! The two stored directions represent precisely one finite permutation. -/
namespace CurrentAFT.CurrentPermutationDraw

 theorem vector_ofFn_get {count : ℕ} (data : Vector (Fin count) count) :
    Vector.ofFn data.get = data := by
  apply Vector.ext
  intro index hindex
  change (Vector.ofFn data.get).get ⟨index, hindex⟩ = data.get ⟨index, hindex⟩
  exact Vector.get_ofFn _ _

def cachedEquiv (count : ℕ) : CachedPermutation count ≃ Equiv.Perm (Fin count) where
  toFun := CachedPermutation.toEquiv
  invFun permutation := ⟨Vector.ofFn permutation, Vector.ofFn permutation.symm,
    fun index => by simp only [Vector.get_ofFn, Equiv.symm_apply_apply],
    fun index => by simp only [Vector.get_ofFn, Equiv.apply_symm_apply]⟩
  left_inv cached := by
    cases cached with
    | mk forward inverse left right =>
      change CachedPermutation.mk (Vector.ofFn forward.get) (Vector.ofFn inverse.get) _ _ = _
      congr 1 <;> exact vector_ofFn_get _
  right_inv permutation := by
    apply Equiv.ext
    intro index
    exact Vector.get_ofFn _ _

noncomputable instance cachedPermutationFintype (count : ℕ) : Fintype (CachedPermutation count) :=
  Fintype.ofEquiv (Equiv.Perm (Fin count)) (cachedEquiv count).symm

end CurrentAFT.CurrentPermutationDraw

end

section




















/-!
# The executable current completion sampler

The least prime, protected cutoff, and public signed shift are calculated
by checked programs.  Casts identify their verified addresses with the
manuscript types and have no runtime content.
-/

namespace CurrentAFT.CurrentFlagCompletionProgram

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentFlagJointDraw
open scoped BigOperators
set_option maxHeartbeats 500000

def castChart {first second : ℕ} (h : first = second)
    (result : CountedValue (Bool × Chart (ZMod first))) : CountedValue (Bool × Chart (ZMod second)) :=
  ⟨h ▸ result.value, result.work⟩



 instance generatedPrimeNeZero (security : ℕ) : NeZero (PublicParameterProgram.modulus security).count :=
  ⟨by rw [PublicParameterProgram.modulus_value]; exact (Parameters.modulus_spec security).2.ne_zero⟩

def draw (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) (precisionBits drawBits : ℕ)
    (word : Tape (Parameters.modulus security) drawBits) :
    CountedValue (Bool × Chart (ZMod (Parameters.modulus security))) :=
  let modulus := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let width := powerCounter base.count 2
  let cutoff := differenceCounter width.count 1
  let shift := CurrentPublicShiftProgram.current security primary seed
  have hmodulus : modulus.count = Parameters.modulus security := PublicParameterProgram.modulus_value security
  let result := CurrentFlagChartDraw.draw cutoff.count modulus.count shift.value.negative shift.value.digits
    (primary.cast hmodulus.symm) precisionBits drawBits
    (cast (congrArg (fun modulus => Tape modulus drawBits) hmodulus.symm) word)
  let converted := castChart hmodulus result
  ⟨converted.value, modulus.work + base.work + width.work + cutoff.work + shift.work + converted.work + 6⟩

noncomputable section
open scoped Classical
local instance completionProgramPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩
local instance completionProgramNeZero (security : ℕ) : NeZero (Parameters.modulus security) :=
  ⟨(Parameters.modulus_spec security).2.ne_zero⟩





end
end CurrentAFT.CurrentFlagCompletionProgram

end

section

























/-!
# Independent complete charts from a stored public input vector

Every core input is read by the sequential vector reader.  The leg count
is generated by a checked counter program.  `inputsOfCore` is the exact
mathematical decoder interface for the separately generated public core.
-/

namespace CurrentAFT.CurrentChartsDraw

open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentAffineData ActualPublicCharge CurrentFlagJointDraw
open scoped BigOperators
set_option maxHeartbeats 500000
attribute [local irreducible] Parameters.legCount CurrentFlagCompletionProgram.draw

abbrev Input (security : ℕ) := AffineFlagCalibration.Palette security × ActualPublicLegCharge.PublicSeed security
abbrev InputVector (security : ℕ) := Vector (Input security) (Parameters.legCount security)
abbrev Tapes (security drawBits : ℕ) := Fin (Parameters.legCount security) → Tape (Parameters.modulus security) drawBits

def defaultInput (security : ℕ) : Input security :=
  (⟨0, (Parameters.modulus_spec security).2.pos⟩,
    ⟨false, false, ⟨0, InwardAnchor.anchorWidth_pos security⟩,
      (GaussianSource.windowZero (DiffuseProfiles.edgeCutoff security), GaussianSource.windowZero (DiffuseProfiles.edgeCutoff security))⟩)

def drawStored (security : ℕ) (inputs : InputVector security) (precisionBits drawBits : ℕ)
    (word : Tapes security drawBits) : CountedValue (Vector (Bool × Chart (ZMod (Parameters.modulus security))) (Parameters.legCount security)) :=
  let base := addCounter security 2
  let count := powerCounter base.count 128
  have hcount : count.count = Parameters.legCount security := by
    rw [powerCounter_value, addCounter_value, Parameters.legCount_eq, Parameters.base]
  let charts := storeData count.count (fun index =>
    let leg := index.cast hcount
    let input := readVector (defaultInput security) inputs leg
    let result := CurrentFlagCompletionProgram.draw security input.value.1 input.value.2 precisionBits drawBits (word leg)
    (⟨result.value, input.work + result.work + 2⟩ : CountedValue (Bool × Chart (ZMod (Parameters.modulus security)))))
  ⟨charts.value.cast hcount, base.work + count.work + charts.work + 3⟩


/-- The public semantic function is the decoder of the retained chart array. -/
def draw (security : ℕ) (inputs : InputVector security) (precisionBits drawBits : ℕ)
    (word : Tapes security drawBits) : CountedValue (Charts security) :=
  let stored := drawStored security inputs precisionBits drawBits word
  ⟨stored.value.get, stored.work⟩







attribute [local irreducible] draw

noncomputable section
open scoped Classical

def inputsOfCore (security : ℕ) (core : Core security) : InputVector security :=
  Vector.ofFn (fun leg => ((core.controls (.inl leg)).1, (core.legs leg).1))

def tapeLaw (security drawBits : ℕ) : FiniteDist (Tapes security drawBits) :=
  FiniteDist.independent (fun _ : Fin (Parameters.legCount security) =>
    CurrentFlagJointDraw.tapeLaw (Parameters.modulus security) drawBits)





end
end CurrentAFT.CurrentChartsDraw

end

section























/-!
# Completing a finite public-core result into a full affine sample

The cached leg inputs are read by the chart program.  They are uniquely
determined by the public core, and their equality is a proof field.  The
completion observes no hidden source.  Failed core attempts remain `none`.
-/

namespace CurrentAFT.CurrentPublicCompletion

open AFT GaussianSource RationalNumerics BinaryArithmetic AFT.RationalRejectionProgram
open CurrentAffineData ActualPublicCharge
open scoped BigOperators
set_option maxHeartbeats 600000
attribute [local irreducible] Parameters.legCount CurrentChartsDraw.draw CurrentEdgeDrawProgram.draw

structure CachedCore (security : ℕ) where
  core : Core security
  inputs : CurrentChartsDraw.InputVector security
  correct : inputs = CurrentChartsDraw.inputsOfCore security core

abbrev Tapes (security drawBits edgeBits : ℕ) :=
  CurrentChartsDraw.Tapes security drawBits × (Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) edgeBits) → Fin 2)

def complete (security : ℕ) (input : Option (CachedCore security)) (precisionBits drawBits edgeBits : ℕ)
    (word : Tapes security drawBits edgeBits) : CountedValue (Option (CurrentPublicAffineSample.Sample security)) :=
  match input with
  | none => ⟨none, 1⟩
  | some cached =>
    let charts := CurrentChartsDraw.draw security cached.inputs precisionBits drawBits word.1
    let edge := CurrentEdgeDrawProgram.draw security edgeBits word.2
    ⟨some ((cached.core, charts.value), edge.value), charts.work + edge.work + 3⟩





noncomputable section
open scoped Classical

def coreEquiv (security : ℕ) : CachedCore security ≃ Core security where
  toFun cached := cached.core
  invFun core := ⟨core, CurrentChartsDraw.inputsOfCore security core, rfl⟩
  left_inv cached := by
    cases cached with
    | mk core inputs correct => cases correct; rfl
  right_inv _ := rfl

instance cachedCoreFintype (security : ℕ) : Fintype (CachedCore security) :=
  Fintype.ofEquiv (Core security) (coreEquiv security).symm

def tapeLaw (security drawBits edgeBits : ℕ) : FiniteDist (Tapes security drawBits edgeBits) :=
  (CurrentChartsDraw.tapeLaw security drawBits).prod
    (FiniteDist.independent (fun _ : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) edgeBits) => FiniteDist.uniform (Fin 2)))

def kernel (security precisionBits drawBits edgeBits : ℕ) (input : Option (CachedCore security)) :
    FiniteDist (Option (CurrentPublicAffineSample.Sample security)) :=
  (tapeLaw security drawBits edgeBits).map (fun word => (complete security input precisionBits drawBits edgeBits word).value)

def targetKernel (security : ℕ) : Option (CachedCore security) → FiniteDist (Option (CurrentPublicAffineSample.Sample security))
  | none => CanonicalMoments.pointLaw none
  | some cached => ((CurrentPublicAffineSample.chartsLaw security cached.core).prod (DiffuseProfiles.edgeLaw security)).map
    (fun pair => some ((cached.core, pair.1), pair.2))

def errorBound (security precisionBits drawBits edgeBits : ℕ) : ℝ :=
  (Parameters.legCount security : ℝ) * (1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits)) +
    1 / (2 : ℝ) ^ edgeBits







end
end CurrentAFT.CurrentPublicCompletion

end

end


