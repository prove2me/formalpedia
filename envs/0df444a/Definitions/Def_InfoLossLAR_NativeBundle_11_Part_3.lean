-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_11_Part_3
-- name    : InfoLossLAR_NativeBundle_11_Part_3
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:29:00.832192+00:00
-- url     : https://prove2.me/theorems/6636569a-135c-4fa9-81ea-d1d99e601628
-- title:
--   Normalized physical root groups and full-response metadata
-- statement:
--   This package defines normalized primary and ordinary profiles, finite profile coefficients and means, singleton and root-group programs, full-response enumeration and point formulas, root ordering and slot indices, rational full-response data, and binary packed-root metadata, factors, guards, scalar values and resource expressions.
--
--   These are stored finite data and their constructor and interpretation APIs. They keep the actual binary or rational computation distinct from its ideal real semantics; later theorems establish approximation and platform running-time guarantees. The smaller compilation unit preserves entire original source modules and introduces no assumed transport or lattice-reduction result.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0. Original source units Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPrimaryMass, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryNormalizedPrimary, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryShiftedProfile, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryOrdinaryProfile, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryProfileCoefficient, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryOrdinaryCoefficient, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryOrdinaryCoefficientResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryOrdinaryMean, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryOrdinaryMeanResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryOrdinaryGroup, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinarySingletonGroup, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootGroupProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_FullResponseEnumeration, Definitions.Def_InfoLossLAR_Native_CurrentAFT_FullResponsePointFormula, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentRootOrdering, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CurrentRootSlotIndex, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalPackedRootSource, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RationalFullResponseProgram, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryFullResponseData, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryFamilyWordProduct, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryRootSignedMassResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPackedRootMetadata, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPackedRootFactors, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPackedRootFactorResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPackedRootGuard, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPackedRootScalar, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPackedRootCurrent, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPackedRootResources, Definitions.Def_InfoLossLAR_Native_CurrentAFT_BinaryPackedRootUniform. Exact syntax-oracle source spans, body hashes and closed scope wrappers recorded in compact_heavy_split/manifest.json. Source SHA256 eb7cab1aeecdd864947285404b0e6f233d846026838aa775dbe65011c19074c3. Compiler-only optimization: one local scope marks Polynomial addition and multiplication instances irreducible while generating native equation lemmas. Every original definition and proof source body is unchanged; all11528 public types and recursive standard-axiom audits pass. New sourceSHA256 58a85937f4ea557e8273bf29a3553718935ed3d461930dc3cb2de1a428f125fd.

import Definitions.Def_InfoLossLAR_NativeBundle_11_Part_2

section
attribute [local irreducible] Polynomial.instAdd Polynomial.instMul

section





























/-! Actual centered primary four-endpoint mass with its single shared scalar. -/
namespace CurrentAFT.BinaryPrimaryMass
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (compensator attachment : IntegerBits) (source : Fin (colors security))
    (word : Vector (Fin (colors security)) 4) : RationalResult :=
  let score := BinaryPrimaryCenteredScore.current security bits source
  let result := BinaryScalarAverage.current security bits (fun scalar =>
    BinaryPrimaryFixedMass.fixedMass security bits compensator attachment scalar score.data word)
  ⟨result.data,score.work+result.work+2⟩



noncomputable section
noncomputable def jointBits (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  inputBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial
noncomputable def fixedHeight (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFixedMass.heightPolynomial precision (jointBits inputBits) (BinaryPrimaryCenteredScore.heightPolynomial precision)
noncomputable def fixedWork (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFixedMass.workPolynomial precision (jointBits inputBits) (BinaryPrimaryCenteredScore.heightPolynomial precision)
noncomputable def heightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.heightPolynomial precision (fixedHeight precision inputBits)
noncomputable def workPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryCenteredScore.workPolynomial precision+
    BinaryCoefficientScalarAverage.workPolynomial precision (fixedHeight precision inputBits) (fixedWork precision inputBits)+2



end
end CurrentAFT.BinaryPrimaryMass

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryMass.jointBits
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryMass.workPolynomial
  pure ()

end

section



























/-! The actual normalized primary channel, including its centered point score. -/
namespace CurrentAFT.BinaryNormalizedPrimary
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
  GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security
abbrev Descriptor := BinaryPrimarySelectedCoefficient.Entry

def numerator (security bits order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 16)
    (compensator attachment : IntegerBits) (source : Fin (colors security)) : CoefficientProgram order :=
  BinaryPrimaryFamily.sum security bits order 1 fallback entries (BinaryPrimaryMass.current security bits compensator attachment source)

def atRoots (security bits order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 16)
    (compensator attachment : IntegerBits) (source : Fin (colors security)) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (numerator security bits order fallback entries compensator attachment source)
    (BinaryPositivePrimary.inverse security bits order programs fallback entries)

def current (security bits order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 16)
    (compensator attachment source : Fin (colors security)) : CoefficientProgram order := fun arity inputs centers =>
  let left := canonicalCounter compensator.val
  let right := canonicalCounter attachment.val
  let value := atRoots security bits order programs fallback entries ⟨false,left.digits⟩ ⟨false,right.digits⟩ source arity inputs centers
  ⟨value.value,left.work+right.work+value.work+4⟩

noncomputable section
open scoped BigOperators Classical







noncomputable def numeratorHeight (entries : Vector Descriptor 16) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFamily.heightPolynomial entries precision (BinaryPrimaryMass.heightPolynomial precision inputBits)
noncomputable def numeratorWork (order : ℕ) (entries : Vector Descriptor 16) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFamily.workPolynomial order 1 entries precision (BinaryPrimaryMass.heightPolynomial precision inputBits)
    (BinaryPrimaryMass.workPolynomial precision inputBits)



noncomputable def jointHeight (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  numeratorHeight entries precision inputBits+BinaryPositivePrimary.heightPolynomial order programs entries precision
noncomputable def jointWork (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  numeratorWork order entries precision inputBits+BinaryPositivePrimary.workPolynomial order programs entries precision
noncomputable def atRootsHeight (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs (jointHeight order programs entries precision inputBits)
noncomputable def atRootsWork (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs (jointHeight order programs entries precision inputBits)
    (jointWork order programs entries precision inputBits)



noncomputable def rootBits : Polynomial ℕ := BinaryFirstInverseProgram.colorsPolynomial+1
noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision : Polynomial ℕ) : Polynomial ℕ := atRootsHeight order programs entries precision rootBits
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 16)
    (precision : Polynomial ℕ) : Polynomial ℕ :=
  100*(BinaryFirstInverseProgram.colorsPolynomial+2)^2+atRootsWork order programs entries precision rootBits+4



end
end CurrentAFT.BinaryNormalizedPrimary

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryNormalizedPrimary.jointHeight
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryNormalizedPrimary.jointWork
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryNormalizedPrimary.rootBits
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryNormalizedPrimary.workPolynomial
  pure ()

end

section
























/-! # A general generated profile shifted by the actual cyclic root -/
namespace CurrentAFT.BinaryShiftedProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryRootProfile.key BinaryPaletteLookup.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security : ℕ) (profile : Fin (colors security) → RationalResult) (root : IntegerBits) (output : ℕ) : RationalResult :=
  let code := canonicalCounter output
  let modulus := PublicParameterProgram.modulus security
  let table := buildArray modulus.count profile
  let key := BinaryRootProfile.key security root code.digits
  let result := BinaryPaletteLookup.current table.data key.digits
  ⟨result.data,code.work+modulus.work+table.work+key.work+result.work+5⟩



noncomputable section
def heightPolynomial (profileBits : Polynomial ℕ) : Polynomial ℕ := BinaryProfileLookup.heightPolynomial profileBits
def lookupWorkPolynomial (rootBits profileBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  let K := BinaryRootProfile.keyBitsPolynomial rootBits Q
  Q*(50*(Q+1)^2+48*(Q+K)+42+3*Q+3+primitiveWorkPolynomial ((Q+1)*(profileBits+1))+2)+2
def workPolynomial (rootBits profileBits profileWork : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+PublicParameterProgram.workPolynomial+
    BinaryFirstInverseProgram.colorsPolynomial*(profileWork+2)+2+
    BinaryRootProfile.keyWorkPolynomial rootBits BinaryFirstInverseProgram.colorsPolynomial+
    lookupWorkPolynomial rootBits profileBits+5



end
end CurrentAFT.BinaryShiftedProfile

end

section




























/-! # Actual ordinary centered columns retain their shifted joint mass -/
namespace CurrentAFT.BinaryOrdinaryProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
  BinaryShiftedProfile.current BinaryMassLiftInput.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def preRoot (security bits : ℕ) (source output : Fin (colors security)) : RationalResult :=
  let reference := BinaryReferenceTables.current security bits
  let sourceValue := readVector zero reference.center source
  let outputValue := readVector zero reference.center output
  let point := BinaryMassLiftColumn.point source output
  let centered := difference point.data outputValue.value
  let result := RationalBits.multiply sourceValue.value centered.data
  ⟨result.data,reference.work+sourceValue.work+outputValue.work+point.work+centered.work+result.work+6⟩



def shifted (security bits : ℕ) (source : Fin (colors security)) (root : IntegerBits) (output : ℕ) : RationalResult :=
  BinaryShiftedProfile.current security (preRoot security bits source) root output



def density (security bits : ℕ) (source : Fin (colors security)) (root : IntegerBits)
    (output : Fin (colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (fun color => shifted security bits source root color.val) output



noncomputable section
def preRootHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryReferenceTables.heightPolynomial precision+2
def preRootWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+18*BinaryFirstInverseProgram.colorsPolynomial+21+
    2*primitiveWorkPolynomial (BinaryReferenceTables.heightPolynomial precision+1)+
    primitiveWorkPolynomial (preRootHeightPolynomial precision)



def shiftedHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryShiftedProfile.heightPolynomial (preRootHeightPolynomial precision)
def shiftedWorkPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryShiftedProfile.workPolynomial rootBits (preRootHeightPolynomial precision) (preRootWorkPolynomial precision)



def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (shiftedHeightPolynomial precision)
def workPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (shiftedHeightPolynomial precision) (shiftedWorkPolynomial precision rootBits)



end
end CurrentAFT.BinaryOrdinaryProfile

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryOrdinaryProfile.preRootHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryOrdinaryProfile.preRootWorkPolynomial
  pure ()

end

section




























/-! # A generated palette profile inserted in the actual degree-one fiber -/
namespace CurrentAFT.BinaryProfileCoefficient
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (security order : ℕ) (primary : Bool)
    (profile : Fin (BinaryProfileLookup.colors security) → RationalResult) : CoefficientProgram order :=
  BinaryFirstCoefficient.current order
    (if primary then BinaryProfileLookup.current security profile else BinaryRootSingleton.zeroProfile)
    (if primary then BinaryRootSingleton.zeroProfile else BinaryProfileLookup.current security profile)



noncomputable section
def heightPolynomial (profileBits : Polynomial ℕ) : Polynomial ℕ := BinaryProfileLookup.heightPolynomial profileBits
def workPolynomial (order : ℕ) (profileBits profileWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (30*order+51)+BinaryProfileLookup.workPolynomial profileBits profileWork



end
end CurrentAFT.BinaryProfileCoefficient

end

section






























/-! # Executed ordinary hybrid numerator and its actual shared denominator -/
namespace CurrentAFT.BinaryOrdinaryCoefficient
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def first (security bits order : ℕ) (source : Fin (colors security)) (root : IntegerBits) : CoefficientProgram order :=
  BinaryProfileCoefficient.current security order true (BinaryOrdinaryProfile.density security bits source root)

def bodyDelta (security bits : ℕ) (source output : Fin (colors security)) : RationalResult :=
  let reference := BinaryReferenceTables.current security bits
  let sourceValue := readVector zero reference.center source
  let point := BinaryMassLiftColumn.point source output
  let result := difference point.data sourceValue.value
  ⟨result.data,reference.work+sourceValue.work+point.work+result.work+4⟩



def bodyFirst (security bits order : ℕ) (source : Fin (colors security)) : CoefficientProgram order :=
  BinaryProfileCoefficient.current security order false (bodyDelta security bits source)

def atRoot (security bits order : ℕ) (programs : List (Entry order))
    (source : Fin (colors security)) (root : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (first security bits order source root)
    (BinaryRootSingleton.inverse security bits order programs .free BinaryProfileLookup.zeroRoot)

def independent (security bits order : ℕ) (programs : List (Entry order))
    (source : Fin (colors security)) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (bodyFirst security bits order source)
    (BinaryRootSingleton.inverse security bits order programs .free BinaryProfileLookup.zeroRoot)





noncomputable section
open scoped Classical





end
end CurrentAFT.BinaryOrdinaryCoefficient

end

section


























/-! # Polynomial resources for the actual ordinary numerator and denominator -/
namespace CurrentAFT.BinaryOrdinaryCoefficient
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current
noncomputable section

def bodyDeltaHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryReferenceTables.heightPolynomial precision+2
def bodyDeltaWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+15*BinaryFirstInverseProgram.colorsPolynomial+
    2*primitiveWorkPolynomial (BinaryReferenceTables.heightPolynomial precision+1)+16



def firstHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileCoefficient.heightPolynomial (BinaryOrdinaryProfile.heightPolynomial precision)
def firstWorkPolynomial (order : ℕ) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileCoefficient.workPolynomial order (BinaryOrdinaryProfile.heightPolynomial precision)
    (BinaryOrdinaryProfile.workPolynomial precision rootBits)
def bodyFirstHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileCoefficient.heightPolynomial (bodyDeltaHeightPolynomial precision)
def bodyFirstWorkPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileCoefficient.workPolynomial order (bodyDeltaHeightPolynomial precision) (bodyDeltaWorkPolynomial precision)





def atRootHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.heightPolynomial order programs (firstHeightPolynomial precision)
    (BinaryRootSingleton.inverseHeightPolynomial order programs precision 0)
def atRootWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.workPolynomial order programs (firstHeightPolynomial precision)
    (BinaryRootSingleton.inverseHeightPolynomial order programs precision 0) (firstWorkPolynomial order precision rootBits)
    (BinaryRootSingleton.inverseWorkPolynomial order programs precision 0)
def independentHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.heightPolynomial order programs (bodyFirstHeightPolynomial precision)
    (BinaryRootSingleton.inverseHeightPolynomial order programs precision 0)
def independentWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.workPolynomial order programs (bodyFirstHeightPolynomial precision)
    (BinaryRootSingleton.inverseHeightPolynomial order programs precision 0) (bodyFirstWorkPolynomial order precision)
    (BinaryRootSingleton.inverseWorkPolynomial order programs precision 0)





end
end CurrentAFT.BinaryOrdinaryCoefficient

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryOrdinaryCoefficient.bodyDeltaHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryOrdinaryCoefficient.bodyDeltaWorkPolynomial
  pure ()

end

section



























/-! # The actual ordinary hybrid keeps the same root in its full numerator -/
namespace CurrentAFT.BinaryOrdinaryMean
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def term (security bits order : ℕ) (programs : List (Entry order)) (source : Fin (colors security))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (root : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let code := canonicalCounter root.val
  let probability := BinaryRootSignedMass.referenceEntry security bits root.val
  let column := BinaryOrdinaryCoefficient.atRoot security bits order programs source ⟨false,code.digits⟩ arity colors centers
  let result := RationalBits.multiply probability.data column.value
  ⟨result.data,code.work+probability.work+column.work+result.work+4⟩

def mean (security bits order : ℕ) (programs : List (Entry order)) (source : Fin (colors security)) : CoefficientProgram order :=
  fun arity colors centers =>
    let modulus := PublicParameterProgram.modulus security
    let result := sumFin modulus.count (term security bits order programs source arity colors centers)
    ⟨result.data,modulus.work+result.work+2⟩

def current (security bits order : ℕ) (programs : List (Entry order)) (source : Fin (colors security))
    (root : IntegerBits) : CoefficientProgram order :=
  fun arity colors centers =>
    let independent := BinaryOrdinaryCoefficient.independent security bits order programs source arity colors centers
    let atRoot := BinaryOrdinaryCoefficient.atRoot security bits order programs source root arity colors centers
    let average := mean security bits order programs source arity colors centers
    let combined := RationalBits.add independent.value atRoot.value
    let result := difference combined.data average.value
    ⟨result.data,independent.work+atRoot.work+average.work+combined.work+result.work+5⟩

noncomputable section
open scoped Classical







end
end CurrentAFT.BinaryOrdinaryMean

end

section





























/-! # All ordinary hybrid costs use the actual computed reference-root law -/
namespace CurrentAFT.BinaryOrdinaryMean
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

def meanHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootAverage.heightPolynomial precision (BinaryOrdinaryCoefficient.atRootHeightPolynomial order programs precision)
def meanWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootAverage.workPolynomial precision (BinaryOrdinaryCoefficient.atRootHeightPolynomial order programs precision)
    (BinaryOrdinaryCoefficient.atRootWorkPolynomial order programs precision BinaryFirstInverseProgram.colorsPolynomial)



def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryOrdinaryCoefficient.independentHeightPolynomial order programs precision+
    BinaryOrdinaryCoefficient.atRootHeightPolynomial order programs precision+meanHeightPolynomial order programs precision+2
def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryOrdinaryCoefficient.independentWorkPolynomial order programs precision+
    BinaryOrdinaryCoefficient.atRootWorkPolynomial order programs precision rootBits+meanWorkPolynomial order programs precision+
    3*primitiveWorkPolynomial (heightPolynomial order programs precision)+7



end
end CurrentAFT.BinaryOrdinaryMean

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryOrdinaryMean.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryOrdinaryMean.workPolynomial
  pure ()

end

section



























namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BinaryRootSingleton
end CurrentAFT.BinaryRootSingleton



/-! # The ordinary group reads its one actual control and root exactly once -/
namespace CurrentAFT.BinaryOrdinaryGroup
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits order : ℕ) (programs : List (Entry order))
    (source : Vector (Fin (colors security)) 3) : CoefficientProgram order := fun arity colors centers =>
  let root := readVector (BinaryFirstFamily.first security) source 0
  let center := readVector (BinaryFirstFamily.first security) source 1
  let code := canonicalCounter root.value.val
  let result := BinaryOrdinaryMean.current security bits order programs center.value ⟨false,code.digits⟩ arity colors centers
  ⟨result.value,root.work+center.work+code.work+result.work+4⟩

noncomputable section
open scoped Classical



def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryOrdinaryMean.heightPolynomial order programs precision
def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryOrdinaryMean.workPolynomial order programs precision BinaryFirstInverseProgram.colorsPolynomial+28



end
end CurrentAFT.BinaryOrdinaryGroup

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryOrdinaryGroup.workPolynomial
  pure ()

end

section


























/-! # Stored root-source reads for the two singleton group roles -/
namespace CurrentAFT.BinarySingletonGroup
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open UniformBodyProfiles (BodyRole)
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits order : ℕ) (programs : List (Entry order)) (role : BodyRole)
    (queue : IntegerBits) (source : Vector (Fin (colors security)) 3) : CoefficientProgram order :=
  fun arity colors centers =>
    let root := readVector (BinaryFirstFamily.first security) source 0
    let code := canonicalCounter root.value.val
    let result := BinaryRootSingleton.current security bits order programs role queue ⟨false,code.digits⟩ arity colors centers
    ⟨result.value,root.work+code.work+result.work+3⟩

noncomputable section
open scoped Classical



def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootSingleton.heightPolynomial order programs precision queueBits BinaryFirstInverseProgram.colorsPolynomial
def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryRootSingleton.workPolynomial order programs precision queueBits BinaryFirstInverseProgram.colorsPolynomial+15



end
end CurrentAFT.BinarySingletonGroup

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinarySingletonGroup.workPolynomial
  pure ()

end

section



































/-! # Every actual grouped response column has an executed binary producer

The stored multiplication and subset programs are fixed before security.
Their correctness assertions verify finite metadata, not response bounds.
-/
namespace CurrentAFT.BinaryRootGroupProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
open RationalRootGroupProgram (LocalRole)
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

structure Data (order : ℕ) where
  programs : List (Entry order)
  primaryFallback : BinaryNormalizedPrimary.Descriptor
  primaryEntries : Vector BinaryNormalizedPrimary.Descriptor 16
  legFallback : BinaryLegGroup.Descriptor
  legEntries : Vector BinaryLegGroup.Descriptor 8

def Correct {order : ℕ} (data : Data order) : Prop :=
  FixedFamilyPrograms.Correct order data.programs ∧ FixedFamilyPrograms.Complete order data.programs ∧
    (∃ ordering : Fin 16 ≃ Finset (Fin 4), (∀ index, (data.primaryEntries.get index).selected=ordering index) ∧
      ∀ index, BinaryPrimarySelectedCoefficient.Valid (data.primaryEntries.get index)) ∧
    (∃ ordering : Fin 8 ≃ Finset (Fin 3), (∀ index, (data.legEntries.get index).selected=ordering index) ∧
      ∀ index, BinaryLegSelectedCoefficient.Valid (data.legEntries.get index))

def primary (security bits order : ℕ) (data : Data order) (source : Vector (Fin (colors security)) 3) : CoefficientProgram order :=
  fun arity inputs centers =>
    let comp := readVector (BinaryFirstFamily.first security) source 0
    let attach := readVector (BinaryFirstFamily.first security) source 1
    let control := readVector (BinaryFirstFamily.first security) source 2
    let result := BinaryNormalizedPrimary.current security bits order data.programs data.primaryFallback data.primaryEntries
      comp.value attach.value control.value arity inputs centers
    ⟨result.value,comp.work+attach.work+control.work+result.work+4⟩

def localTable (security bits order : ℕ) (data : Data order) (queue : IntegerBits) (role : LocalRole)
    (source : Vector (Fin (colors security)) 3) : CoefficientProgram order :=
  let table := match role with
    | .primary => primary security bits order data source
    | .ordinary => BinaryOrdinaryGroup.current security bits order data.programs source
    | .leg => BinaryLegGroup.current security bits order data.programs data.legFallback data.legEntries source
    | .center => BinarySingletonGroup.current security bits order data.programs .free queue source
    | .queue => BinarySingletonGroup.current security bits order data.programs .queue queue source
  fun arity inputs centers =>
    let result := table arity inputs centers
    ⟨result.value,result.work+1⟩

noncomputable section
open scoped Classical





def heightPolynomial (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryNormalizedPrimary.heightPolynomial order data.programs data.primaryEntries precision+
    BinaryOrdinaryGroup.heightPolynomial order data.programs precision+
    BinaryLegGroup.heightPolynomial order data.programs data.legEntries precision+
    BinarySingletonGroup.heightPolynomial order data.programs precision queueBits
def workPolynomial (order : ℕ) (data : Data order) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryNormalizedPrimary.workPolynomial order data.programs data.primaryEntries precision+
    BinaryOrdinaryGroup.workPolynomial order data.programs precision+
    BinaryLegGroup.workPolynomial order data.programs data.legEntries precision+
    BinarySingletonGroup.workPolynomial order data.programs precision queueBits+41



end
end CurrentAFT.BinaryRootGroupProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootGroupProgram.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootGroupProgram.workPolynomial
  pure ()

end

section













/-! # Polynomial-size root-tag enumeration in the actual full response

All subsets with at most the fixed truncation order are generated as the
images of bounded-length words. The algorithm never forms the powerset
of the body population before filtering it by cardinality.
-/
namespace CurrentAFT.FullResponseEnumeration

open AFT ActualBlockFock ControlCoordinates GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev SubsetWords (Pool : Type*) (order : ℕ) := (size : Fin (order + 1)) × (Fin size.val → Pool)

def boundedSubsets (Pool : Type*) [Fintype Pool] [DecidableEq Pool] (order : ℕ) : Finset (Finset Pool) :=
  (Finset.univ : Finset (SubsetWords Pool order)).image (fun word => Finset.univ.image word.2)

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount













end
end CurrentAFT.FullResponseEnumeration

end

section















/-! # The exact bounded-enumeration formula for each full response column

A column has one source arity and one joint centered point kernel. Its root
part averages the actual distinct control choices and only root tags of size
at most the fixed order. The common queue stays outside each full product.
-/
namespace CurrentAFT.FullResponsePointFormula
open AFT ActualControls ProposalPrimary ControlCoordinates ControlProduct CanonicalReconstruction
  GradedControlAlgebra LocalCoefficientFamily ActualCompleteStability
  CalibrationPointCoordinates ActualRootFamily ActualBlockFock
  TaggedSelection UniformTaggedOutput BackgroundRates ActualBackground FullResponseEnumeration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance pointFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  primaryLaw bodyReference ordinaryPool

abbrev Index (security order : ℕ) := PointIndex (ActualControls.Palette security) (SafePalette security) order

def referenceWeight (security order : ℕ) (source : Index security order) : ℝ :=
  (∏ index, (primaryLaw security).weight (source.2.1 index)) *
    ∏ index, (bodyReference security).weight (source.2.2 index)

def basisFamily (security order : ℕ) (source : Index security order) : Family security order :=
  Pi.single source.1 (pointKernel (primaryLaw security) (bodyReference security)
    (primaryReference_positive security) (bodyReference_positive security) source.2.1 source.2.2)





def rootPointResponse (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (source : Index security order) : Family security order :=
  ∑ choice : Choice security source.1.val.1.val source.1.val.2.val,
    (choiceLaw security _ _ (primary_room security order hroom source.1)
      (body_room security order hroom source.1)).weight choice •
      ∑ tagged ∈ (boundedSubsets (BlockIndex security) order).filter (fun tagged => 2 ≤ tagged.card),
        ActualRootResponse.response order horder queue (selection security _ _ choice) tagged layout
          (pointKernel (primaryLaw security) (bodyReference security) (primaryReference_positive security)
            (bodyReference_positive security) source.2.1 source.2.2)



def pointResponse (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (source : Index security order) : Family security order :=
  background security order horder *
    (basisFamily security order source + CompleteRaising.raisingLinear security order (by omega)
      (basisFamily security order source)) +
    ∑ scalar : FirstHistogram.Scalar security, (DiffuseProfiles.scalarLaw security).weight scalar •
      (fixedQueueBackground security order horder scalar.val *
        rootPointResponse security order (by omega) hroom scalar.val layout source)





end
end CurrentAFT.FullResponsePointFormula

end

section



















/-! Sorted block ordinals for tagged and retained roots. The runtime
ordering filters the supplied bounded tag list and compares the selected
indices; it does not enumerate the complement of the body population. -/
namespace CurrentAFT.CurrentRootOrdering
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def blockNumbering (security : ℕ) : BlockIndex security ≃
    Fin (Parameters.legCount security + (centerCount security + Parameters.modulus security)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def isKept {security r s : ℕ} (selection : Selection security r s) (index : BlockIndex security) : Prop :=
  (∀ primary, index ≠ .inl (selection.primary primary)) ∧
    (∀ compensator, index ≠ .inr (.inl (selection.compensator compensator))) ∧
    (∀ body, index ≠ .inr (.inl (selection.body body)))

instance isKeptDecidable {security r s : ℕ} (selection : Selection security r s) : DecidablePred (isKept selection) :=
  fun index => by unfold isKept; infer_instance

def keptTags {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Finset (BlockIndex security) := tagged.filter (isKept selection)

def tagIndices {security : ℕ} (tagged : Finset (BlockIndex security)) :=
  tagged.map (blockNumbering security).toEmbedding

def keptIndices {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :=
  tagIndices (keptTags selection tagged)

def numberedTags {security : ℕ} (tagged : Finset (BlockIndex security)) : tagIndices tagged ≃ tagged where
  toFun index := ⟨(blockNumbering security).symm index.val, by
    obtain ⟨original, ho, he⟩ := Finset.mem_map.mp index.property
    simpa only [← he, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using ho⟩
  invFun index := ⟨blockNumbering security index.val, Finset.mem_map.mpr ⟨index.val, index.property, rfl⟩⟩
  left_inv index := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _
  right_inv index := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _

def tagOrdering {security : ℕ} (tagged : Finset (BlockIndex security)) : Fin tagged.card ≃ tagged :=
  (Finset.orderIsoOfFin (tagIndices tagged) (Finset.card_map _)).toEquiv.trans (numberedTags tagged)

theorem isKept_iff {security r s : ℕ} (selection : Selection security r s) (index : BlockIndex security) :
    isKept selection index ↔ index ∈ selection.kept := by
  classical
  simp only [Selection.kept, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Selection.removed, Finset.mem_map, Finset.mem_univ, true_and, not_exists]
  constructor
  · rintro ⟨hp, hc, hb⟩ (primary | (compensator | body))
    · exact (hp primary).symm
    · exact (hc compensator).symm
    · exact (hb body).symm
  · intro h
    exact ⟨fun p hp => h (.inl p) hp.symm, fun c hc => h (.inr (.inl c)) hc.symm,
      fun b hb => h (.inr (.inr b)) hb.symm⟩

def keptTagsEquiv {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    keptTags selection tagged ≃ HitKept selection tagged where
  toFun index := ⟨⟨index.val, (isKept_iff selection index.val).mp (Finset.mem_filter.mp index.property).2⟩,
    (Finset.mem_filter.mp index.property).1⟩
  invFun index := ⟨index.val.val, Finset.mem_filter.mpr
    ⟨index.property, (isKept_iff selection index.val.val).mpr index.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def keptOrdering {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Fin (keptIndices selection tagged).card ≃ HitKept selection tagged :=
  ((Finset.orderIsoOfFin (keptIndices selection tagged) rfl).toEquiv.trans
    (numberedTags (keptTags selection tagged))).trans (keptTagsEquiv selection tagged)



theorem tagOrdering_number {security : ℕ} (tagged : Finset (BlockIndex security)) (index : Fin tagged.card) :
    blockNumbering security (tagOrdering tagged index).val =
      (Finset.orderIsoOfFin (tagIndices tagged) (Finset.card_map _) index).val := by
  exact (blockNumbering security).apply_symm_apply _

end CurrentAFT.CurrentRootOrdering

end

section



















/-! Bounded native lookup of each tagged root in the active groups.
There are two candidate root slots per group; the second slot of an
ordinary or retained group is explicitly rejected. -/
namespace CurrentAFT.CurrentRootSlotIndex
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

abbrev Slot {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :=
  Sigma (groupRootSlots selection tagged)

def within {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    (group : ActiveGroup selection tagged) → Fin 2 → Option (Slot selection tagged)
  | .inl (.inl primary), slot => some ⟨.inl (.inl primary), slot⟩
  | .inl (.inr ordinary), slot => if slot.val=0 then some ⟨.inl (.inr ordinary), (0 : Fin 1)⟩ else none
  | .inr kept, slot => if slot.val=0 then some ⟨.inr kept, (0 : Fin 1)⟩ else none

def slotNumber {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Slot selection tagged → Fin 2
  | ⟨.inl (.inl _), slot⟩ => slot
  | ⟨.inl (.inr _), _⟩ => 0
  | ⟨.inr _, _⟩ => 0

def encode {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (root : Slot selection tagged) : Fin (count*2) :=
  finProdFinEquiv (ordering.symm root.fst, slotNumber selection tagged root)

def decode {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (index : Fin (count*2)) : Option (Slot selection tagged) :=
  within selection tagged (ordering (finProdFinEquiv.symm index).1) (finProdFinEquiv.symm index).2

theorem decode_encode {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (root : Slot selection tagged) :
    decode selection tagged ordering (encode selection tagged ordering root) = some root := by
  rcases root with ⟨(primary | ordinary) | kept, slot⟩
  · simp only [decode, encode, Equiv.symm_apply_apply, Equiv.apply_symm_apply, slotNumber, within]
  · change Fin 1 at slot
    have hs : slot=0 := Subsingleton.elim _ _
    subst slot
    simp only [decode, encode, Equiv.symm_apply_apply, Equiv.apply_symm_apply, slotNumber, within,
      Fin.val_zero, ite_true]
  · change Fin 1 at slot
    have hs : slot=0 := Subsingleton.elim _ _
    subst slot
    simp only [decode, encode, Equiv.symm_apply_apply, Equiv.apply_symm_apply, slotNumber, within,
      Fin.val_zero, ite_true]

theorem decode_eq_some {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (index : Fin (count*2)) (root : Slot selection tagged) :
    decode selection tagged ordering index = some root ↔ index=encode selection tagged ordering root := by
  constructor
  · intro h
    obtain ⟨⟨group, slot⟩, rfl⟩ := finProdFinEquiv.surjective index
    obtain ⟨group, rfl⟩ := ordering.symm.surjective group
    simp only [decode, Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
    rcases group with (primary | ordinary) | kept
    · simp only [within, Option.some.injEq] at h
      subst root
      rfl
    · fin_cases slot <;> simp [within] at h
      subst root
      rfl
    · fin_cases slot <;> simp [within] at h
      subst root
      rfl
  · rintro rfl
    exact decode_encode selection tagged ordering root

def rootBlock {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Slot selection tagged → BlockIndex security
  | ⟨.inl (.inl primary), slot⟩ => if slot.val=0 then .inr (.inl (selection.compensator primary)) else .inl (selection.primary primary)
  | ⟨.inl (.inr ordinary), _⟩ => .inr (.inl (selection.body ordinary))
  | ⟨.inr kept, _⟩ => kept.val.val

theorem rootBlock_eq {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (root : Slot selection tagged) : rootBlock selection tagged root = rootEmbedding selection tagged root := by
  rcases root with ⟨(primary | ordinary) | kept, slot⟩
  · change Fin 2 at slot
    fin_cases slot <;> rfl
  · change Fin 1 at slot
    have hs : slot=0 := Subsingleton.elim _ _
    subst slot
    rfl
  · change Fin 1 at slot
    have hs : slot=0 := Subsingleton.elim _ _
    subst slot
    rfl

def test {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (block : BlockIndex security) (index : Fin (count*2)) : Bool :=
  (decode selection tagged ordering index).any (fun root => decide (rootBlock selection tagged root=block))

def position {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (block : BlockIndex security) : Option (Fin (count*2)) :=
  (List.ofFn (id : Fin (count*2) → Fin (count*2))).find? (test selection tagged ordering block)

theorem matches_root {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (root : Slot selection tagged) (index : Fin (count*2)) :
    test selection tagged ordering (rootBlock selection tagged root) index=true ↔
      index=encode selection tagged ordering root := by
  unfold test
  cases hd : decode selection tagged ordering index with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, false_iff]
    intro h
    have hh := (decode_eq_some selection tagged ordering index root).mpr h
    rw [hd] at hh
    cases hh
  | some other =>
    simp only [Option.any_some, decide_eq_true_eq]
    constructor
    · intro h
      have he : other=root := (rootEmbedding selection tagged).injective (by simpa only [rootBlock_eq] using h)
      subst other
      exact (decode_eq_some selection tagged ordering index root).mp hd
    · intro h
      have hh := (decode_eq_some selection tagged ordering index root).mpr h
      rw [hd] at hh
      exact congrArg (rootBlock selection tagged) (Option.some.inj hh)

theorem position_root {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (root : Slot selection tagged) :
    position selection tagged ordering (rootBlock selection tagged root) = some (encode selection tagged ordering root) := by
  unfold position
  apply (List.find?_ofFn_eq_some_of_injective (f := id) Function.injective_id).mpr
  constructor
  · exact (matches_root selection tagged ordering root _).mpr rfl
  · intro earlier hlt hmatch
    have he := (matches_root selection tagged ordering root earlier).mp hmatch
    subst earlier
    exact lt_irrefl _ hlt

theorem position_tag {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (tag : tagged) :
    position selection tagged ordering tag.val =
      some (encode selection tagged ordering (tagEmbedding selection tagged tag)) := by
  have he : rootBlock selection tagged (tagEmbedding selection tagged tag)=tag.val := by
    rw [rootBlock_eq, tag_image]
  rw [← he]
  exact position_root selection tagged ordering _

def tagPosition {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) (tag : tagged) : Fin count × Fin 2 :=
  finProdFinEquiv.symm ((position selection tagged ordering tag.val).get (by rw [position_tag]; rfl))



def taggedSlots {security r s count : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (ordering : Fin count ≃ ActiveGroup selection tagged) : Fin tagged.card → Fin count × Fin 2 :=
  fun index => tagPosition selection tagged ordering (CurrentRootOrdering.tagOrdering tagged index)

end CurrentAFT.CurrentRootSlotIndex

end

section






















namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CurrentRootSourceNatural
end CurrentAFT.CurrentRootSourceNatural




/-! # The actual native metadata and source numbering for the packed program -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT ActualBlockFock TaggedSelection PairedRootPlacement CurrentGroupSourcePadding
  CurrentRootOrdering CurrentRootSlotIndex CurrentRectangleIndex GroupSourcePadding RationalRootGroupProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def nativeRole {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    ActiveGroup selection tagged → LocalRole
  | .inl (.inl _) => .primary
  | .inl (.inr _) => .ordinary
  | .inr index => match index.val.val with
    | .inl _ => .leg
    | .inr (.inl _) => .center
    | .inr (.inr _) => .queue

def groupCount {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) : ℕ :=
  (r+s)+(keptIndices selection tagged).card

def ordering {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Fin (groupCount selection tagged) ≃ ActiveGroup selection tagged :=
  groupOrdering selection tagged (keptOrdering selection tagged)

def actualMetadata {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Metadata r s (keptIndices selection tagged).card tagged.card where
  roles index := nativeRole selection tagged (ordering selection tagged index)
  taggedSlots := CurrentRootSlotIndex.taggedSlots selection tagged (ordering selection tagged)

def nativeKind : LocalRole → Kind
  | .primary => .primary
  | .ordinary => .ordinary
  | .leg | .center | .queue => .kept









section NativeEncoding
variable {Group : Type*} [Fintype Group] [DecidableEq Group]



end NativeEncoding

noncomputable section
open scoped Classical
local instance packedSourceFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedSourceSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize

def sourceIndex {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged) : Fin ((colors security)^((groupCount selection tagged)*3)) :=
  indexEncode (colors security) (colors_pos security) (safe security) (groupKind selection tagged)
    (groupCount selection tagged) (ordering selection tagged) ((sourceEquiv selection tagged).symm source)













end
end CurrentAFT.RationalPackedRootProgram

end

section


























/-! The complete rational response column: actual distinct control choices,
bounded root tags, and the three population products under one shared queue.
The final subtraction produces the defect matrix used by iteration. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra RationalFamilyProductProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension

def centerSplit (security : ℕ) :
    (Fin (Parameters.legCount security) ⊕ Fin (BackgroundRates.ordinaryPool security)) ≃ Fin (centerCount security) :=
  finSumFinEquiv.trans (finCongr (UniformTaggedOutput.centerCount_split security))

def selection (security r s : ℕ) (choice : UniformTaggedOutput.Choice security r s) : Selection security r s where
  primary := choice.1
  compensator := choice.1.trans ⟨fun index => centerSplit security (.inl index),
    fun _ _ he => Sum.inl.inj ((centerSplit security).injective he)⟩
  body := choice.2.trans ⟨fun index => centerSplit security (.inr index),
    fun _ _ he => Sum.inr.inj ((centerSplit security).injective he)⟩
  separated _ _ he := by
    have h := (centerSplit security).injective he
    cases h



def tags (security order : ℕ) : Finset (Finset (BlockIndex security)) :=
  (FullResponseEnumeration.boundedSubsets (BlockIndex security) order).filter (fun tagged => 2 ≤ tagged.card)

def selected {security r s : ℕ} (bits order : ℕ) (queue : ℤ) (chosen : Selection security r s)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) : Table ℚ ℕ ℕ order :=
  fun arity colors centers =>
    RationalPackedRootProgram.current security bits order queue (RationalPackedRootProgram.actualMetadata chosen ∅)
      sourcePrimary sourceBody arity colors centers +
    ∑ tagged ∈ tags security order,
      RationalPackedRootProgram.current security bits order queue (RationalPackedRootProgram.actualMetadata chosen tagged)
        sourcePrimary sourceBody arity colors centers

def choiceAverage (security bits order r s : ℕ) (queue : ℤ)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) : Table ℚ ℕ ℕ order :=
  letI := CyclePatternProgram.selectionFintype (Parameters.legCount security) r
  letI := CyclePatternProgram.selectionFintype (BackgroundRates.ordinaryPool security) s
  fun arity colors centers =>
    (∑ choice : UniformTaggedOutput.Choice security r s,
      selected bits order queue (selection security r s choice) sourcePrimary sourceBody arity colors centers) /
      (((Parameters.legCount security).descFactorial r : ℚ)*((BackgroundRates.ordinaryPool security).descFactorial s : ℚ))

def fixedQueue (security bits order r s : ℕ) (queue : ℤ)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) : Table ℚ ℕ ℕ order :=
  product order (RationalBackgroundPopulationProgram.current security bits order queue)
    (choiceAverage security bits order r s queue sourcePrimary sourceBody)

def response (security bits order r s : ℕ)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) : Table ℚ ℕ ℕ order :=
  RationalScalarFamilyAverage.current security bits order
    (fun queue => fixedQueue security bits order r s queue sourcePrimary sourceBody)

def basis (security bits order : ℕ) (source : TruncatedArity order)
    (sourcePrimary : Fin source.val.1.val → ℕ) (sourceBody : Fin source.val.2.val → ℕ) : Table ℚ ℕ ℕ order :=
  fun output colors centers => if h : output = source then
    WeightedPointKernelProgram.current security bits source.val.1.val source.val.2.val sourcePrimary sourceBody
      (fun index => colors (index.cast (congrArg (fun arity : TruncatedArity order => arity.val.1.val) h).symm))
      (fun index => centers (index.cast (congrArg (fun arity : TruncatedArity order => arity.val.2.val) h).symm))
    else 0

def defect (security bits order : ℕ) (source : TruncatedArity order)
    (sourcePrimary : Fin source.val.1.val → ℕ) (sourceBody : Fin source.val.2.val → ℕ) : Table ℚ ℕ ℕ order :=
  response security bits order source.val.1.val source.val.2.val sourcePrimary sourceBody-
    basis security bits order source sourcePrimary sourceBody

end CurrentAFT.RationalFullResponseProgram

end

section

































/-! # Finite stored full-response metadata and its genuine weighted point basis -/
namespace CurrentAFT.BinaryFullResponseData
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Data (order : ℕ) where
  groups : BinaryRootGroupProgram.Data order
  points : List (BinaryFixedPointPrograms.Entry order)

def Correct {order : ℕ} (data : Data order) : Prop :=
  BinaryRootGroupProgram.Correct data.groups ∧ BinaryFixedPointPrograms.Correct order data.points ∧ BinaryFixedPointPrograms.Complete order data.points

def finiteBasis (security bits order : ℕ) (data : Data order) (source : TruncatedArity order)
    (sourcePrimary : Vector (BinaryWeightedPointKernel.Color security) source.val.1.val)
    (sourceBody : Vector (BinaryWeightedPointKernel.Color security) source.val.2.val) : BinaryFiniteCoefficient.FiniteProgram security order :=
  fun output inputs centers =>
    let checked := FixedFamilyPrograms.matchArity order output source
    if h : checked.value=true then
      let same := (FixedFamilyPrograms.matchArity_value order output source).mp h
      let result := BinaryFixedPointPrograms.current security bits order data.points source sourcePrimary
        (Vector.cast (congrArg (fun arity : TruncatedArity order => arity.val.1.val) same) inputs)
        sourceBody (Vector.cast (congrArg (fun arity : TruncatedArity order => arity.val.2.val) same) centers)
      ⟨result.data,checked.work+result.work+3⟩
    else ⟨zero,checked.work+2⟩

def basis (security bits order : ℕ) (data : Data order) (source : TruncatedArity order)
    (sourcePrimary : Vector (BinaryWeightedPointKernel.Color security) source.val.1.val)
    (sourceBody : Vector (BinaryWeightedPointKernel.Color security) source.val.2.val) : CoefficientProgram order :=
  BinaryFiniteCoefficient.lift security order (finiteBasis security bits order data source sourcePrimary sourceBody)

noncomputable section






noncomputable def basisHeightPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFixedPointPrograms.heightPolynomial order data.points precision
noncomputable def finiteBasisWorkPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFixedPointPrograms.workPolynomial order data.points precision+Polynomial.C (12*order+8)
noncomputable def basisWorkPolynomial (order : ℕ) (data : Data order) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteCoefficient.workPolynomial order (finiteBasisWorkPolynomial order data precision)





end
end CurrentAFT.BinaryFullResponseData

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFullResponseData.basisHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFullResponseData.finiteBasisWorkPolynomial
  pure ()

end

section





















/-! Executed heterogeneous products of fixed-order local coefficient tables.
The public metadata for each leaf is read from its stored vector whenever a
product program requests it. No coefficient evaluation oracle is introduced. -/
namespace CurrentAFT.BinaryFamilyWordProduct
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false


def product (order : ℕ) (programs : List (Entry order)) :
    (count : ℕ) → (Fin count → CoefficientProgram order) → CoefficientProgram order
  | 0, _ => BinaryFamilyPower.unit order
  | count+1, tables => BinaryFamilyArithmetic.multiply order programs
      (product order programs count (fun index => tables index.succ)) (tables 0)







noncomputable section
open scoped BigOperators Classical

 

 

 

 







 

end
end CurrentAFT.BinaryFamilyWordProduct

end

section



























/-! Closed fixed-order resources for centered joint cycle masses. The reference
atoms are computed and cached; no atom reciprocal or joint factorization occurs. -/
namespace CurrentAFT.BinaryRootSignedMassResources
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open CurrentProposalResources BinaryRootSignedMass
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus


def referenceCacheWorkPolynomial (limit : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C limit*(Polynomial.C (3*limit)+BinaryRootReferenceResources.workPolynomial precision+7)+2

 


def factorPolynomial (count : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  let R := BinaryRootReferenceResources.rootBitsPolynomial
  let Q := primeSizePolynomial
  Polynomial.C (9*count)+(60*(R+Q+1)^2+50*(Q+1)^2+48*(R+Q+Q)+50)+
    2*RationalBits.primitiveWorkPolynomial (BinaryRootReferenceResources.heightPolynomial precision+1)+20

 


def testHeightPolynomial (limit : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C limit*(BinaryRootReferenceResources.heightPolynomial precision+1)

def testWorkPolynomial (limit : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count ∈ Finset.range (limit+1), BinaryFiniteProduct.workPolynomial count
    (BinaryRootReferenceResources.heightPolynomial precision+1) (factorPolynomial count precision)

 


def heightPolynomial (limit : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinarySparseCycleAveragePolynomial.heightPolynomial limit BinaryRootReferenceResources.bodyPolynomial
    BinaryRootReferenceResources.cutoffPolynomial precision (testHeightPolynomial limit precision)

def workPolynomial (limit : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootReferenceResources.bodyWorkPolynomial+CurrentProposalSamplerPolynomial.edgeCutoffWorkPolynomial+
    PublicParameterProgram.workPolynomial+50*(primeSizePolynomial+1)^2+
    referenceCacheWorkPolynomial limit precision+
    BinarySparseCycleAveragePolynomial.workPolynomial limit BinaryRootReferenceResources.bodyPolynomial
      BinaryRootReferenceResources.cutoffPolynomial precision (testHeightPolynomial limit precision) (testWorkPolynomial limit precision)+6

 

end
end CurrentAFT.BinaryRootSignedMassResources

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSignedMassResources.factorPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSignedMassResources.referenceCacheWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSignedMassResources.testHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSignedMassResources.testWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryRootSignedMassResources.workPolynomial
  pure ()

end

section





























/-! Stored role/root-slot metadata and executed accesses to one whole joint
base-q source word. No joint root/control input is factored. -/
namespace CurrentAFT.BinaryPackedRootMetadata
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open RationalRootGroupProgram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus

abbrev Color (security : ℕ) := Fin (PublicParameterProgram.modulus security).count

structure Data (r s kept tags : ℕ) where
  roles : Vector LocalRole ((r+s)+kept)
  tagged : Vector (Fin ((r+s)+kept) × Fin 2) tags


def Data.metadata {r s kept tags : ℕ} (data : Data r s kept tags) : RationalPackedRootProgram.Metadata r s kept tags :=
  ⟨data.roles.get,data.tagged.get⟩


def firstColor (security : ℕ) : Color security :=
  ⟨0, by rw [PublicParameterProgram.modulus_value]; exact (Parameters.modulus_spec security).2.pos⟩

def word {groups : ℕ} (security : ℕ) (source : Vector (Color security) (groups*3)) : Fin groups → Fin 3 → ℕ :=
  fun group slot => (source.get (finProdFinEquiv (group,slot))).val


def sourceEntry {groups : ℕ} (security : ℕ) (source : Vector (Color security) (groups*3))
    (group : Fin groups) (slot : Fin 3) : CountedValue (Color security) :=
  let base := multiplyCounter group.val 3
  let position := addCounter base.count slot.val
  let result := readVector (firstColor security) source ⟨position.count, by
    rw [addCounter_value,multiplyCounter_value];have := group.isLt;have := slot.isLt;omega⟩
  ⟨result.value,base.work+position.work+result.work+3⟩

 

 


def taggedDefault {groups tags : ℕ} (positions : Vector (Fin groups × Fin 2) tags) (index : Fin tags) : Fin groups × Fin 2 :=
  (⟨0, by have := (positions.get index).1.isLt;omega⟩,0)


def absent {groups tags : ℕ} (positions : Vector (Fin groups × Fin 2) tags) (group : Fin groups) (slot : Fin 2) : CountedValue Bool :=
  BinaryProposalGuard.allFin tags (fun index =>
    let position := readVector (taggedDefault positions index) positions index
    let sameGroup := equalCounter position.value.1.val group.val
    let sameSlot := equalCounter position.value.2.val slot.val
    ⟨!(sameGroup.value && sameSlot.value),position.work+sameGroup.work+sameSlot.work+3⟩)

 

 


def active {r s kept tags : ℕ} (data : Data r s kept tags) (group : Fin ((r+s)+kept)) (slot : Fin 2) : CountedValue Bool :=
  let role := readVector LocalRole.primary data.roles group
  let first := equalCounter slot.val 0
  let missing := absent data.tagged group slot
  let isActive := match role.value with | .primary => true | _ => first.value
  ⟨isActive && missing.value,role.work+first.work+missing.work+3⟩

 

 

end CurrentAFT.BinaryPackedRootMetadata

end

section





























/-! The three actual scalar multipliers of a packed joint source column:
reference-weighted canonical point input, untagged root marginals, and centered
joint tagged cycle mass. All dynamic coordinates are read from stored arrays. -/
namespace CurrentAFT.BinaryPackedRootFactors
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryPackedRootMetadata
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def untaggedFactor {r s kept tags : ℕ} (security bits : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin (((r+s)+kept)*2)) : RationalResult :=
  let pair := finProdFinEquiv.symm index
  let used := active data pair.1 pair.2
  let output := sourceEntry security source pair.1 pair.2.castSucc
  let reference := BinaryRootSignedMass.referenceEntry security bits output.value.val
  ⟨if used.value then reference.data else RationalBits.one,used.work+output.work+reference.work+3⟩


def untagged {r s kept tags : ℕ} (security bits : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) : RationalResult :=
  BinaryFiniteProduct.current (((r+s)+kept)*2) (untaggedFactor security bits data source)

 

 


def taggedOutputs {r s kept tags : ℕ} (security : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) : CountedValue (Vector ℕ tags) :=
  storeData tags (fun index =>
    let position := readVector (taggedDefault data.tagged index) data.tagged index
    let output := sourceEntry security source position.value.1 position.value.2.castSucc
    ⟨output.value.val,position.work+output.work+2⟩)

 

 


def signed {r s kept tags : ℕ} (security bits : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) : RationalResult :=
  let outputs := taggedOutputs security data source
  let result := BinaryRootSignedMass.weightedEntry security bits outputs.value
  ⟨result.data,outputs.work+result.work+2⟩

 


def primaryOutputs {r s kept : ℕ} (security : ℕ) (source : Vector (Color security) (((r+s)+kept)*3)) :
    CountedValue (Vector (Color security) r) :=
  storeData r (fun index => sourceEntry security source (RationalPackedRootProgram.primaryGroup r s kept index) 2)


def bodyOutputs {r s kept : ℕ} (security : ℕ) (source : Vector (Color security) (((r+s)+kept)*3)) :
    CountedValue (Vector (Color security) s) :=
  storeData s (fun index =>
    let position := addCounter r index.val
    let output := sourceEntry security source ⟨position.count,by rw [addCounter_value];have := index.isLt;omega⟩ 1
    ⟨output.value,position.work+output.work+2⟩)

 

 

 

 


def control {r s kept tags : ℕ} (security bits : ℕ) (program : BinaryWeightedPointKernel.Program r s)
    (_data : Data r s kept tags) (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) : RationalResult :=
  let colors := primaryOutputs security source
  let centers := bodyOutputs security source
  let result := BinaryWeightedPointKernel.current security bits program sourcePrimary colors.value sourceBody centers.value
  ⟨result.data,colors.work+centers.work+result.work+3⟩

 

end CurrentAFT.BinaryPackedRootFactors

end

section



























/-! Fixed-order closed resource polynomials for all packed root scalar factors. -/
namespace CurrentAFT.BinaryPackedRootFactorResources
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryPackedRootMetadata BinaryPackedRootFactors
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def untaggedHeightPolynomial (groups : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (groups*2)*BinaryRootReferenceResources.heightPolynomial precision

def untaggedLeafWorkPolynomial (groups tags : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (3*groups+tags*(3*tags+6*groups+34)+20+30*groups+20+3)+
    BinaryRootReferenceResources.workPolynomial precision

def untaggedWorkPolynomial (groups tags : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteProduct.workPolynomial (groups*2) (BinaryRootReferenceResources.heightPolynomial precision)
    (untaggedLeafWorkPolynomial groups tags precision)

 


def signedWorkPolynomial (groups tags : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootSignedMassResources.workPolynomial tags precision+Polynomial.C (tags*(3*tags+30*groups+27)+4)

 


def controlWorkPolynomial {r s : ℕ} (kept : ℕ) (program : BinaryWeightedPointKernel.Program r s) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryWeightedPointKernel.workPolynomial program precision+
    Polynomial.C (r*(30*((r+s)+kept)+22)+s*(2*r+30*((r+s)+kept)+25)+7)

 

end
end CurrentAFT.BinaryPackedRootFactorResources

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootFactorResources.controlWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootFactorResources.signedWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootFactorResources.untaggedHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootFactorResources.untaggedLeafWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootFactorResources.untaggedWorkPolynomial
  pure ()

end

section



























/-! Actual binary safety and dummy-slot guards for packed group sources. -/
namespace CurrentAFT.BinaryPackedRootGuard
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryPackedRootMetadata RationalRootGroupProgram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus


def safe (colors margin output : ℕ) : CountedValue Bool :=
  let below := lessCounter output margin
  let translated := addCounter output margin
  let upper := lessCounter translated.count colors
  ⟨!below.value && upper.value,below.work+translated.work+upper.work+3⟩

 

 



def group {r s kept tags : ℕ} (security colors margin : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) (index : Fin ((r+s)+kept)) : CountedValue Bool :=
  let role := readVector LocalRole.primary data.roles index
  let first := sourceEntry security source index 1
  let last := sourceEntry security source index 2
  let firstZero := equalCounter first.value.val 0
  let lastZero := equalCounter last.value.val 0
  let interior := safe colors margin first.value.val
  let answer := match role.value with
    | .primary => true
    | .ordinary => interior.value && lastZero.value
    | .leg | .center | .queue => firstZero.value && lastZero.value
  ⟨answer,role.work+first.work+last.work+firstZero.work+lastZero.work+interior.work+6⟩

 


def marginProgram (security : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let square := powerCounter base.count 2
  let result := multiplyCounter 3 square.count
  ⟨result.count,base.work+square.work+result.work+3⟩

 


def current {r s kept tags : ℕ} (security : ℕ) (data : Data r s kept tags)
    (source : Vector (Color security) (((r+s)+kept)*3)) : CountedValue Bool :=
  let colors := PublicParameterProgram.modulus security
  let margin := marginProgram security
  let result := BinaryProposalGuard.allFin ((r+s)+kept) (group security colors.count margin.count data source)
  ⟨result.value,colors.work+margin.work+result.work+3⟩

 

 

noncomputable section

def marginPolynomial : Polynomial ℕ := 3*(Polynomial.X+2)^2

def marginWorkPolynomial : Polynomial ℕ :=
  2*Polynomial.X+1+3*(6*(Polynomial.X+3)^4+4)+3*(2*(Polynomial.X+2)^2+3)+4

 


def workPolynomial (groups : ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+marginWorkPolynomial+
    Polynomial.C groups*(Polynomial.C (100*groups)+30*CurrentProposalResources.primeSizePolynomial+10*marginPolynomial+102)+4

 

end

end CurrentAFT.BinaryPackedRootGuard

end

section





























/-! The complete executed scalar multiplying each whole packed source family.
Safety is tested by binary counters and every probability factor is computed. -/
namespace CurrentAFT.BinaryPackedRootScalar
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open BinaryPackedRootMetadata
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def current {r s kept tags : ℕ} (security bits : ℕ) (program : BinaryWeightedPointKernel.Program r s)
    (data : Data r s kept tags) (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) : RationalResult :=
  let guard := BinaryPackedRootGuard.current security data source
  let control := BinaryPackedRootFactors.control security bits program data sourcePrimary sourceBody source
  let untagged := BinaryPackedRootFactors.untagged security bits data source
  let signed := BinaryPackedRootFactors.signed security bits data source
  let pair := RationalBits.multiply control.data untagged.data
  let result := RationalBits.multiply pair.data signed.data
  ⟨if guard.value then result.data else RationalBits.zero,
    guard.work+control.work+untagged.work+signed.work+pair.work+result.work+7⟩

 

noncomputable section


def heightPolynomial {r s : ℕ} (kept tags : ℕ) (program : BinaryWeightedPointKernel.Program r s)
    (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryWeightedPointKernel.heightPolynomial program precision+
    BinaryPackedRootFactorResources.untaggedHeightPolynomial ((r+s)+kept) precision+
    BinaryRootSignedMassResources.heightPolynomial tags precision


def workPolynomial {r s : ℕ} (kept tags : ℕ) (program : BinaryWeightedPointKernel.Program r s)
    (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPackedRootGuard.workPolynomial ((r+s)+kept)+BinaryPackedRootFactorResources.controlWorkPolynomial kept program precision+
    BinaryPackedRootFactorResources.untaggedWorkPolynomial ((r+s)+kept) tags precision+
    BinaryPackedRootFactorResources.signedWorkPolynomial ((r+s)+kept) tags precision+
    2*RationalBits.primitiveWorkPolynomial (heightPolynomial kept tags program precision)+7

 

end
end CurrentAFT.BinaryPackedRootScalar

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootScalar.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootScalar.workPolynomial
  pure ()

end

section































namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BinaryFamilyArithmetic
end CurrentAFT.BinaryFamilyArithmetic
namespace CurrentAFT.BinaryFamilyArithmetic.multiply
end CurrentAFT.BinaryFamilyArithmetic.multiply
namespace CurrentAFT.BinaryFamilyProduct
end CurrentAFT.BinaryFamilyProduct
namespace CurrentAFT.BinaryFamilyProduct.run
end CurrentAFT.BinaryFamilyProduct.run
namespace CurrentAFT.BinaryFamilyValidSemantics
end CurrentAFT.BinaryFamilyValidSemantics
namespace CurrentAFT.BinaryFamilyWordProduct
end CurrentAFT.BinaryFamilyWordProduct





/-! The complete packed coefficient entry: true binary role dispatch, actual
heterogeneous family products, scalar root/control factors and joint source
loops. The ideal value is the literal rational packed program. -/
namespace CurrentAFT.BinaryPackedRootCurrent
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms BinaryPackedRootMetadata
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def sourceGroup {groups : ℕ} (security : ℕ) (source : Vector (Color security) (groups*3)) (group : Fin groups) :
    CountedValue (Vector (Color security) 3) := storeData 3 (sourceEntry security source group)

 

 


def localFamily {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (queue : IntegerBits) (data : Data r s kept tags) (source : Vector (Color security) (((r+s)+kept)*3))
    (index : Fin ((r+s)+kept)) : CoefficientProgram order := fun arity colors centers =>
  let role := readVector RationalRootGroupProgram.LocalRole.primary data.roles index
  let input := sourceGroup security source index
  let result := BinaryRootGroupProgram.localTable security bits order programs queue role.value input.value arity colors centers
  ⟨result.value,role.work+input.work+result.work+3⟩


def localProduct {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (queue : IntegerBits) (data : Data r s kept tags) (source : Vector (Color security) (((r+s)+kept)*3)) :
    CoefficientProgram order :=
  BinaryFamilyWordProduct.product order programs.programs ((r+s)+kept) (localFamily security bits order programs queue data source)

 


def summand {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (queue : IntegerBits) (data : Data r s kept tags)
    (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s)
    (source : Vector (Color security) (((r+s)+kept)*3)) : CoefficientProgram order := fun arity colors centers =>
  let scalar := BinaryPackedRootScalar.current security bits pointProgram data sourcePrimary sourceBody source
  let family := localProduct security bits order programs queue data source arity colors centers
  let result := RationalBits.multiply scalar.data family.value
  ⟨result.data,scalar.work+family.work+result.work+3⟩

 


def current {r s kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (queue : IntegerBits) (data : Data r s kept tags)
    (sourcePrimary : Vector (Color security) r) (sourceBody : Vector (Color security) s) : CoefficientProgram order :=
  fun arity colors centers =>
    let result := BinaryPackedRootSum.current security ((r+s)+kept)
      (fun source =>
        let value := summand security bits order programs pointProgram queue data sourcePrimary sourceBody source arity colors centers
        (⟨value.value,value.work⟩ : RationalResult))
    ⟨result.data,result.work+1⟩

 

end CurrentAFT.BinaryPackedRootCurrent

end

section



























/-! Polynomial work for the entire actual packed coefficient producer,
including all local family production and all joint source buffers. -/
namespace CurrentAFT.BinaryPackedRootResources
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms BinaryPackedRootMetadata BinaryPackedRootCurrent
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def localLeafWorkPolynomial (order groups : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootGroupProgram.workPolynomial order programs precision queueBits+Polynomial.C (93*groups+74)

 


def localHeightPolynomial (order groups : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyPower.heightPolynomial order programs.programs (BinaryRootGroupProgram.heightPolynomial order programs precision queueBits) groups

def localWorkPolynomial (order groups : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyPower.workPolynomial order programs.programs (BinaryRootGroupProgram.heightPolynomial order programs precision queueBits)
    (localLeafWorkPolynomial order groups programs precision queueBits) groups

 


def summandHeightPolynomial {r s : ℕ} (order kept tags : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPackedRootScalar.heightPolynomial kept tags pointProgram precision+
    localHeightPolynomial order ((r+s)+kept) programs precision queueBits

def summandWorkPolynomial {r s : ℕ} (order kept tags : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPackedRootScalar.workPolynomial kept tags pointProgram precision+
    localWorkPolynomial order ((r+s)+kept) programs precision queueBits+
    RationalBits.primitiveWorkPolynomial (summandHeightPolynomial order kept tags programs pointProgram precision queueBits)+3

 


def heightPolynomial {r s : ℕ} (order kept tags : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPackedRootSum.heightPolynomial ((r+s)+kept)
    (summandHeightPolynomial order kept tags programs pointProgram precision queueBits)

def workPolynomial {r s : ℕ} (order kept tags : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (pointProgram : BinaryWeightedPointKernel.Program r s) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPackedRootSum.workPolynomial ((r+s)+kept)
    (summandHeightPolynomial order kept tags programs pointProgram precision queueBits)
    (summandWorkPolynomial order kept tags programs pointProgram precision queueBits)+1

 

end
end CurrentAFT.BinaryPackedRootResources

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootResources.localLeafWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootResources.summandHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootResources.summandWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootResources.workPolynomial
  pure ()

end

section





























/-! One actual packed entry program and one resource polynomial for the fixed
order. Source arities are dispatched from stored point programs; all bounded
kept/tag counts share a finite polynomial envelope. -/
namespace CurrentAFT.BinaryPackedRootUniform
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct BinaryPackedRootMetadata
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current


def current {kept tags : ℕ} (security bits order : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (points : List (BinaryFixedPointPrograms.Entry order)) (queue : IntegerBits) (source : TruncatedArity order)
    (metadata : Data source.val.1.val source.val.2.val kept tags)
    (sourcePrimary : Vector (Color security) source.val.1.val) (sourceBody : Vector (Color security) source.val.2.val) :
    CoefficientProgram order := fun arity colors centers =>
  let selected := BinaryFixedPointPrograms.lookup order source points
  let result := BinaryPackedRootCurrent.current security bits order programs selected.value queue metadata sourcePrimary sourceBody arity colors centers
  ⟨result.value,selected.work+result.work+1⟩

 

noncomputable section
open scoped Classical


def envelope (order limit : ℕ) (value : TruncatedArity order → ℕ → ℕ → Polynomial ℕ) : Polynomial ℕ :=
  ∑ source : TruncatedArity order, ∑ kept ∈ Finset.range (limit+1), ∑ tags ∈ Finset.range (limit+1), value source kept tags

 


def heightPolynomial (order limit : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (points : List (BinaryFixedPointPrograms.Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  envelope order limit (fun source kept tags => BinaryPackedRootResources.heightPolynomial order kept tags programs
    (BinaryFixedPointPrograms.lookup order source points).value precision queueBits)


def workPolynomial (order limit : ℕ) (programs : BinaryRootGroupProgram.Data order)
    (points : List (BinaryFixedPointPrograms.Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (points.length*(12*order+7)+2)+
    envelope order limit (fun source kept tags => BinaryPackedRootResources.workPolynomial order kept tags programs
      (BinaryFixedPointPrograms.lookup order source points).value precision queueBits)

 

end
end CurrentAFT.BinaryPackedRootUniform

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootUniform.envelope
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPackedRootUniform.workPolynomial
  pure ()

end

end


