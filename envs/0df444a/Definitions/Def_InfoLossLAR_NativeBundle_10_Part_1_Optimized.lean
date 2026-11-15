-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_10_Part_1_Optimized
-- name    : InfoLossLAR_NativeBundle_10_Part_1_Optimized
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T18:56:42.50544+00:00
-- url     : https://prove2.me/theorems/47d4243d-9245-4b21-9b97-78abd6630a73
-- title:
--   Binary background and diffuse coefficient kernels (compiler-optimized version)
-- statement:
--   This package defines binary background and primary coefficient data, unsafe-array and seed-density interfaces, canonical diffuse pairs and residuals, finite coefficient and density-inverse programs, marked-anchor and marked-seed data, and primary deviation interfaces.
--
--   These are stored finite data and their constructor and interpretation APIs. They keep the actual binary or rational computation distinct from its ideal real semantics; later theorems establish approximation and platform running-time guarantees. The smaller compilation unit preserves entire original source modules and introduces no assumed transport or lattice-reduction result.
-- source:
--   Compiler-optimized version of InfoLossLAR_NativeBundle_10_Part_1. Original mathematical body byte-for-byte unchanged after removing one local scope with irreducible Polynomial addition and multiplication instances. All11528 public native/runtime types agree; recursive standard-axiom and single-version import audits pass. SourceSHA256 d92805c00d8dabe542870101839f2b82568cc554cea7d14cfcfe8f00159b786e.

import Definitions.Def_InfoLossLAR_NativeBundle_09

section
attribute [local irreducible] Polynomial.instAdd Polynomial.instMul

section





















/-! # Binary evaluation of the fixed finite reciprocal -/
namespace CurrentAFT.BinaryFamilyReciprocal
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def complement (order : ℕ) (table : CoefficientProgram order) : CoefficientProgram order :=
  fun arity colors centers =>
    let first := BinaryFamilyPower.unit order arity colors centers
    let second := table arity colors centers
    let result := difference first.value second.value
    ⟨result.data, first.work + second.work + result.work + 2⟩

def current (order : ℕ) (programs : List (Entry order)) (table : CoefficientProgram order) : CoefficientProgram order :=
  fun arity colors centers =>
    let result := sumFin (order+1) (fun count =>
      let term := BinaryFamilyPower.power order programs (complement order table) count.val arity colors centers
      ⟨term.value, term.work+1⟩)
    ⟨result.data, result.work+1⟩



noncomputable section
open scoped Classical



noncomputable def complementWork (order : ℕ) (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (12*order+10) + budget + 2 * BinaryCalibrationIteration.primitivePolynomial bits



noncomputable def heightSum (order : ℕ) (programs : List (Entry order)) (bits : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count : Fin (order+1), BinaryFamilyPower.heightPolynomial order programs (bits+1) count.val

noncomputable def workSum (order : ℕ) (programs : List (Entry order)) (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count : Fin (order+1), BinaryFamilyPower.workPolynomial order programs (bits+1)
    (complementWork order bits budget) count.val

noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (order+1) * (heightSum order programs bits + 1)

noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (order+1) * (workSum order programs bits budget +
    BinaryCalibrationIteration.primitivePolynomial (Polynomial.C (order+2) * (heightSum order programs bits + 1)) + 3) + 3



end
end CurrentAFT.BinaryFamilyReciprocal

end

section





















/-! # Binary truncated population powers

The population enters only the computed binomial coefficients. The number of
family multiplications depends on the fixed calibration order.
-/
namespace CurrentAFT.BinaryFamilyBinomial
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def term (order population : ℕ) (programs : List (Entry order))
    (table : CoefficientProgram order) (count : ℕ) : CoefficientProgram order :=
  fun arity colors centers =>
    let coefficient := BinaryBinomialCoefficient.current population count
    let value := BinaryFamilyPower.power order programs table count arity colors centers
    let result := multiply coefficient.data value.value
    ⟨result.data, coefficient.work+value.work+result.work+3⟩

def current (order population : ℕ) (programs : List (Entry order))
    (table : CoefficientProgram order) : CoefficientProgram order :=
  fun arity colors centers =>
    let result := sumFin (order+1) (fun count =>
      let value := term order population programs table count.val arity colors centers
      ⟨value.value, value.work+1⟩)
    ⟨result.data, result.work+1⟩

noncomputable section
open scoped Classical



def powerHeightSum (order : ℕ) (programs : List (Entry order)) (bits : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count : Fin (order+1), BinaryFamilyPower.heightPolynomial order programs bits count.val

def powerWorkSum (order : ℕ) (programs : List (Entry order)) (bits budget : Polynomial ℕ) : Polynomial ℕ :=
  ∑ count : Fin (order+1), BinaryFamilyPower.workPolynomial order programs bits budget count.val

def termHeight (order : ℕ) (programs : List (Entry order)) (population bits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBinomialCoefficient.heightPolynomial order population + powerHeightSum order programs bits

def termWork (order : ℕ) (programs : List (Entry order)) (population bits budget : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBinomialCoefficient.workPolynomial order population + powerWorkSum order programs bits budget +
    BinaryCalibrationIteration.primitivePolynomial (termHeight order programs population bits)+3

def heightPolynomial (order : ℕ) (programs : List (Entry order)) (population bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (order+1)*(termHeight order programs population bits+1)

def workPolynomial (order : ℕ) (programs : List (Entry order)) (population bits budget : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (order+1)*(termWork order programs population bits budget +
    BinaryCalibrationIteration.primitivePolynomial (Polynomial.C (order+2)*(termHeight order programs population bits+1))+3)+3





end
end CurrentAFT.BinaryFamilyBinomial

end

section


























/-! # The actual body-minus-uniform profile produced on binary data -/
namespace CurrentAFT.BinaryBackgroundDeviation
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryBodyProgram.current

def current (security bits : ℕ) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let encoded := ofCounter modulus.count
  let reference := BinaryBodyProgram.current security bits false output
  let reciprocal := RationalBits.inverse encoded.data
  let negative := RationalBits.negate reciprocal.data
  let result := RationalBits.add reference.data negative.data
  ⟨result.data, modulus.work+encoded.work+reference.work+reciprocal.work+negative.work+result.work+6⟩



noncomputable section
noncomputable def operandHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+BinaryBodyProgram.currentHeightPolynomial precision inputBits
noncomputable def heightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*operandHeightPolynomial precision inputBits+1
noncomputable def workPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+60*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryBodyProgram.currentWorkPolynomial precision inputBits+
    3*primitiveWorkPolynomial (operandHeightPolynomial precision inputBits)+6



end
end CurrentAFT.BinaryBackgroundDeviation

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundDeviation.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundDeviation.operandHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundDeviation.workPolynomial
  pure ()

end

section


























/-! # Full binary production of the original free primary-certificate density -/
namespace CurrentAFT.BinaryBackgroundPrimary
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryBackgroundDeviation.current BinaryMassLiftInput.current

def point (security bits : ℕ) (color : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let code := canonicalCounter color.val
  let result := BinaryBackgroundDeviation.current security bits code.digits
  ⟨result.data, code.work+result.work+2⟩



def current (security bits : ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (point security bits) output



noncomputable section
noncomputable def pointHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundDeviation.heightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial
noncomputable def pointWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryBackgroundDeviation.workPolynomial precision BinaryFirstInverseProgram.colorsPolynomial+2
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (pointHeightPolynomial precision)
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (pointHeightPolynomial precision) (pointWorkPolynomial precision)





end
end CurrentAFT.BinaryBackgroundPrimary

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundPrimary.pointWorkPolynomial
  pure ()

end

section
























/-! # A generated unsafe profile cache and its exact total mass -/
namespace CurrentAFT.BinaryUnsafeArray
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryUnsafeProfile.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def point (security : ℕ) (shift : IntegerBits) (output : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := BinaryUnsafeProfile.current security shift code.digits
  ⟨result.data, code.work+result.work+2⟩



def read {count : ℕ} (profile : Vector RationalBits count) (index : Fin count) : RationalResult :=
  let result := readVector zero profile index
  ⟨result.value, result.work+1⟩

structure Result (security : ℕ) where
  profile : Vector RationalBits (colors security)
  total : RationalBits
  work : ℕ

def current (security : ℕ) (shift : IntegerBits) : Result security :=
  let modulus := PublicParameterProgram.modulus security
  let profile := buildArray modulus.count (point security shift)
  let total := sumFin modulus.count (read profile.data)
  ⟨profile.data, total.data, modulus.work+profile.work+total.work+4⟩





noncomputable section
noncomputable def pointHeightPolynomial (shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnsafeProfile.heightPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial
noncomputable def pointWorkPolynomial (shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryUnsafeProfile.workPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial+2
noncomputable def heightPolynomial (shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  pointHeightPolynomial shiftBits+BinaryFirstInverseProgram.colorsPolynomial*(pointHeightPolynomial shiftBits+1)
noncomputable def workPolynomial (shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  PublicParameterProgram.workPolynomial+Q*(pointWorkPolynomial shiftBits+2)+2+
    Q*(3*Q+6+primitiveWorkPolynomial ((Q+1)*(pointHeightPolynomial shiftBits+1)))+2+4





end
end CurrentAFT.BinaryUnsafeArray

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryUnsafeArray.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryUnsafeArray.workPolynomial
  pure ()

end

section


























namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BinaryRootConvolution
end CurrentAFT.BinaryRootConvolution
namespace CurrentAFT.RationalBackgroundProfiles
end CurrentAFT.RationalBackgroundProfiles





/-! # Actual unsafe-root residual and its original primary mass lift -/
namespace CurrentAFT.BinaryBackgroundResidual
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryUnsafeArray.current BinaryRootConvolution.current BinaryBodyProgram.current
  BinaryMassLiftInput.current PublicParameterProgram.modulus

def profile (security bits : ℕ) (shift : IntegerBits) (output : List Bool) : RationalResult :=
  let cache := BinaryUnsafeArray.current security shift
  let convolution := BinaryRootConvolution.current security bits cache.profile output
  let body := BinaryBodyProgram.current security bits false output
  let product := RationalBits.multiply cache.total body.data
  let negative := RationalBits.negate product.data
  let result := RationalBits.add convolution.data negative.data
  ⟨result.data, cache.work+convolution.work+body.work+product.work+negative.work+result.work+6⟩



def point (security bits : ℕ) (shift : IntegerBits)
    (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := profile security bits shift code.digits
  ⟨result.data, code.work+result.work+2⟩



def current (security bits : ℕ) (shift : IntegerBits)
    (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (point security bits shift) output



noncomputable section
noncomputable def operandHeightPolynomial (precision shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnsafeArray.heightPolynomial shiftBits+
    BinaryRootConvolution.heightPolynomial precision outputBits (BinaryUnsafeArray.heightPolynomial shiftBits)+
    BinaryBodyProgram.currentHeightPolynomial precision outputBits
noncomputable def profileHeightPolynomial (precision shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  3*operandHeightPolynomial precision shiftBits outputBits+1
noncomputable def profileWorkPolynomial (precision shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnsafeArray.workPolynomial shiftBits+
    BinaryRootConvolution.workPolynomial precision outputBits (BinaryUnsafeArray.heightPolynomial shiftBits)+
    BinaryBodyProgram.currentWorkPolynomial precision outputBits+
    3*primitiveWorkPolynomial (2*operandHeightPolynomial precision shiftBits outputBits)+6
noncomputable def pointHeightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  profileHeightPolynomial precision shiftBits BinaryFirstInverseProgram.colorsPolynomial
noncomputable def pointWorkPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    profileWorkPolynomial precision shiftBits BinaryFirstInverseProgram.colorsPolynomial+2
noncomputable def heightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (pointHeightPolynomial precision shiftBits)
noncomputable def workPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (pointHeightPolynomial precision shiftBits) (pointWorkPolynomial precision shiftBits)







end
end CurrentAFT.BinaryBackgroundResidual

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundResidual.operandHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundResidual.pointWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundResidual.profileHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundResidual.profileWorkPolynomial
  pure ()

end

section





















/-! # Literal compiled arithmetic of the original projected seed density -/
namespace CurrentAFT.BinarySeedDensityFormula
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | shifted | fringe | total | safe | center
  deriving DecidableEq

def expression : ScalarProgram Leaf :=
  .multiply
    (.add (.add (.add (.atom .shifted) (.negate (.atom .fringe)))
      (.multiply (.atom .total) (.atom .safe))) (.negate (.atom .safe)))
    (.inverse (.atom .center))



def leaf (shifted fringe total safe center : RationalBits) : Leaf→RationalBits
  | .shifted => shifted
  | .fringe => fringe
  | .total => total
  | .safe => safe
  | .center => center

def read (values : Leaf→RationalBits) (code : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (values code)
  ⟨result.data,result.work+1⟩

def current (shifted fringe total safe center : RationalBits) : RationalResult :=
  let result := expression.compileBinaryRun (read (leaf shifted fringe total safe center))
  ⟨result.value,result.work+1⟩



def height (bound : ℕ) := expression.nodes*(bound+3)
def work (bound : ℕ) := expression.nodes*(smallRationalEncodingWork 1+(4*bound+9)+primitiveWorkBound (height bound)+2)+2



noncomputable def heightPolynomial (bound : Polynomial ℕ) : Polynomial ℕ := Polynomial.C expression.nodes*(bound+3)
noncomputable def workPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(smallRationalEncodingPolynomial 1+(4*bound+9)+primitiveWorkPolynomial (heightPolynomial bound)+2)+2





end CurrentAFT.BinarySeedDensityFormula

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinarySeedDensityFormula.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinarySeedDensityFormula.workPolynomial
  pure ()

end

section






























/-! # The original mixed translation body density from generated binary inputs -/
namespace CurrentAFT.BinaryBackgroundSeed
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryUnsafeArray.current BinaryShiftedSafeProfile.current
  BinarySafeProfile.current BinaryReferenceTables.current BinarySeedDensityFormula.current

def current (security bits : ℕ) (shift : IntegerBits) (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let cache := BinaryUnsafeArray.current security shift
  let shifted := BinaryShiftedSafeProfile.current security shift code.digits
  let safe := BinarySafeProfile.current security code.digits
  let reference := BinaryReferenceTables.current security bits
  let fringe := readVector zero cache.profile output
  let center := readVector zero reference.center output
  let result := BinarySeedDensityFormula.current shifted.data fringe.value cache.total safe.data center.value
  ⟨result.data,code.work+cache.work+shifted.work+safe.work+reference.work+fringe.work+center.work+result.work+8⟩



noncomputable section
noncomputable def operandHeightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnsafeArray.heightPolynomial shiftBits+
    BinaryShiftedSafeProfile.heightPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial+
    BinarySafeProfile.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial+
    BinaryReferenceTables.heightPolynomial precision
noncomputable def heightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinarySeedDensityFormula.heightPolynomial (operandHeightPolynomial precision shiftBits)
noncomputable def workPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryUnsafeArray.workPolynomial shiftBits+
    BinaryShiftedSafeProfile.workPolynomial shiftBits BinaryFirstInverseProgram.colorsPolynomial+
    BinarySafeProfile.workPolynomial BinaryFirstInverseProgram.colorsPolynomial+
    BinaryReferenceTables.currentWorkPolynomial precision+6*BinaryFirstInverseProgram.colorsPolynomial+
    BinarySeedDensityFormula.workPolynomial (operandHeightPolynomial precision shiftBits)+14



end
end CurrentAFT.BinaryBackgroundSeed

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundSeed.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundSeed.operandHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundSeed.workPolynomial
  pure ()

end

section


























/-! # Original free-body certificate density from generated safe and center tables -/
namespace CurrentAFT.BinaryBackgroundBody
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinarySafeProfile.current BinaryReferenceTables.current

def current (security bits : ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let safe := BinarySafeProfile.current security code.digits
  let reference := BinaryReferenceTables.current security bits
  let center := readVector zero reference.center output
  let density := RationalBits.quotient safe.data center.value
  let negative := RationalBits.negate density.data
  let result := RationalBits.add one negative.data
  ⟨result.data, code.work+safe.work+reference.work+center.work+density.work+negative.work+result.work+7⟩



noncomputable section
noncomputable def operandHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinarySafeProfile.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial+
    BinaryReferenceTables.heightPolynomial precision+1
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := operandHeightPolynomial precision+1
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinarySafeProfile.workPolynomial BinaryFirstInverseProgram.colorsPolynomial+
    BinaryReferenceTables.currentWorkPolynomial precision+3*BinaryFirstInverseProgram.colorsPolynomial+
    4*primitiveWorkPolynomial (operandHeightPolynomial precision)+12



end
end CurrentAFT.BinaryBackgroundBody

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundBody.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundBody.operandHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundBody.workPolynomial
  pure ()

end

section


























/-! # Executed first-primary/first-body coefficient-table dispatch -/
namespace CurrentAFT.BinaryFirstFamily
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lessCounter PublicParameterProgram.modulus

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def first (security : ℕ) : Fin (colors security) :=
  ⟨0,by rw [colors,BinaryFirstInverseProgram.colors,PublicParameterProgram.modulus_value]
        exact (Parameters.modulus_spec security).2.pos⟩

def primaryGuard (r s : ℕ) : CountedValue Bool :=
  let positive := lessCounter 0 r
  let belowTwo := lessCounter r 2
  let bodyZero := lessCounter s 1
  ⟨positive.value && belowTwo.value && bodyZero.value,positive.work+belowTwo.work+bodyZero.work+4⟩

theorem primaryGuard_value (r s : ℕ) : (primaryGuard r s).value=true ↔ r=1 ∧ s=0 := by
  simp only [primaryGuard,Bool.and_eq_true,lessCounter_value]
  omega



def current (security r s : ℕ) (primary body : Fin (colors security)→RationalResult)
    (inputs : Vector (Fin (colors security)) r) (centers : Vector (Fin (colors security)) s) : RationalResult :=
  let primaryShape := primaryGuard r s
  let bodyShape := primaryGuard s r
  if hp : primaryShape.value=true then
    let input := readVector (first security) inputs ⟨0,by have := (primaryGuard_value r s).mp hp; omega⟩
    let result := primary input.value
    ⟨result.data,primaryShape.work+bodyShape.work+input.work+result.work+5⟩
  else if hb : bodyShape.value=true then
    let center := readVector (first security) centers ⟨0,by have := (primaryGuard_value s r).mp hb; omega⟩
    let result := body center.value
    ⟨result.data,primaryShape.work+bodyShape.work+center.work+result.work+5⟩
  else ⟨zero,primaryShape.work+bodyShape.work+3⟩



def work (r s primaryWork bodyWork : ℕ) := 15*(r+s)+primaryWork+bodyWork+50



end CurrentAFT.BinaryFirstFamily

end

section
































/-! # Actual binary producers of the original mixed free and translation tables -/
namespace CurrentAFT.BinaryBackgroundFamilies
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryBackgroundPrimary.current BinaryBackgroundResidual.current
  BinaryBackgroundBody.current BinaryBackgroundSeed.current BinaryFirstFamily.current PublicParameterProgram.modulus

def translationPrimary (security bits : ℕ) (shift : IntegerBits)
    (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let first := BinaryBackgroundPrimary.current security bits output
  let residual := BinaryBackgroundResidual.current security bits shift output
  let result := RationalBits.add first.data residual.data
  ⟨result.data,first.work+residual.work+result.work+3⟩



def free (security bits order : ℕ) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) : RationalResult :=
  BinaryFirstFamily.current security arity.val.1.val arity.val.2.val
    (BinaryBackgroundPrimary.current security bits) (BinaryBackgroundBody.current security bits) inputs centers

def translation (security bits order : ℕ) (shift : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) : RationalResult :=
  BinaryFirstFamily.current security arity.val.1.val arity.val.2.val
    (translationPrimary security bits shift) (BinaryBackgroundSeed.current security bits shift) inputs centers





noncomputable section
noncomputable def primaryOperandHeightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundPrimary.heightPolynomial precision+BinaryBackgroundResidual.heightPolynomial precision shiftBits
noncomputable def primaryHeightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  primaryOperandHeightPolynomial precision shiftBits+1
noncomputable def primaryWorkPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundPrimary.workPolynomial precision+BinaryBackgroundResidual.workPolynomial precision shiftBits+
    primitiveWorkPolynomial (primaryOperandHeightPolynomial precision shiftBits)+3
noncomputable def freeHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundPrimary.heightPolynomial precision+BinaryBackgroundBody.heightPolynomial precision
noncomputable def freeWorkPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundPrimary.workPolynomial precision+BinaryBackgroundBody.workPolynomial precision+Polynomial.C (15*order+50)
noncomputable def translationHeightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  primaryHeightPolynomial precision shiftBits+BinaryBackgroundSeed.heightPolynomial precision shiftBits
noncomputable def translationWorkPolynomial (order : ℕ) (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  primaryWorkPolynomial precision shiftBits+BinaryBackgroundSeed.workPolynomial precision shiftBits+Polynomial.C (15*order+50)







end
end CurrentAFT.BinaryBackgroundFamilies

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundFamilies.freeHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundFamilies.freeWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundFamilies.primaryHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundFamilies.primaryOperandHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundFamilies.primaryWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundFamilies.translationHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundFamilies.translationWorkPolynomial
  pure ()

end

section
























/-! # A counted exact-arity guard for concrete local coefficient kernels -/
namespace CurrentAFT.BinaryCoefficientFiber
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lessCounter addCounter PublicParameterProgram.modulus

def equal (count target : ℕ) : CountedValue Bool :=
  let next := addCounter target 1
  let below := lessCounter count next.count
  let lower := lessCounter count target
  ⟨below.value && !lower.value,next.work+below.work+lower.work+4⟩

theorem equal_value (count target : ℕ) : (equal count target).value=true ↔ count=target := by
  let below := lessCounter count (addCounter target 1).count
  let lower := lessCounter count target
  have hu : below.value=true ↔ count<target+1 :=
    (lessCounter_value count (addCounter target 1).count).trans (by rw [addCounter_value])
  have hl : lower.value=true ↔ count<target := lessCounter_value count target
  change (below.value && !lower.value)=true ↔ _
  constructor
  · intro h
    have hp : below.value=true ∧ (!lower.value)=true := by simpa only [Bool.and_eq_true] using h
    have hb := hu.mp hp.1
    have hn : ¬count<target := by
      intro hlt
      have hv := hl.mpr hlt
      have hx := hp.2
      simp only [hv,Bool.not_true] at hx
      contradiction
    omega
  · intro h
    have hb := hu.mpr (show count<target+1 by omega)
    have hn : lower.value=false := by
      cases hv : lower.value
      · rfl
      · have hx := hl.mp hv
        omega
    simp only [hb,hn,Bool.not_false,Bool.and_self]



def shape (r s primaryDegree bodyDegree : ℕ) : CountedValue Bool :=
  let primary := equal r primaryDegree
  let body := equal s bodyDegree
  ⟨primary.value && body.value,primary.work+body.work+3⟩

theorem shape_value (r s primaryDegree bodyDegree : ℕ) :
    (shape r s primaryDegree bodyDegree).value=true ↔ r=primaryDegree ∧ s=bodyDegree := by
  simp only [shape,Bool.and_eq_true,equal_value]



def current (security r s primaryDegree bodyDegree : ℕ)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) r)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) s)
    (kernel : Vector (Fin (BinaryFirstInverseProgram.colors security)) primaryDegree→
      Vector (Fin (BinaryFirstInverseProgram.colors security)) bodyDegree→RationalResult) : RationalResult :=
  let test := shape r s primaryDegree bodyDegree
  if h : test.value=true then
    let sizes := (shape_value r s primaryDegree bodyDegree).mp h
    let result := kernel (Vector.cast sizes.1 inputs) (Vector.cast sizes.2 centers)
    ⟨result.data,test.work+result.work+3⟩
  else ⟨zero,test.work+2⟩





end CurrentAFT.BinaryCoefficientFiber

end

section






















/-! # Explicit fixed-length tuple enumeration with binary sums

Tuple construction scans the stored tail.  The callback is charged on each
visit; the weight evaluator supplies a concrete joint-array reader.
-/
namespace CurrentAFT.BinaryTupleSum
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

/-- Materialize the new tuple using charged sequential reads. -/
def prepend {Value : Type*} {count : ℕ} (head : Value) (tail : Vector Value count) : CountedValue (Vector Value (count+1)) :=
  let computed := Vector.ofFn (fun index : Fin (count+1) =>
    Fin.cases (motive := fun _ => CountedValue Value) (⟨head, 1⟩ : CountedValue Value) (fun rest => readVector head tail rest) index)
  ⟨computed.map (fun result => result.value), (∑ index, (computed.get index).work)+2*(count+1)+2⟩





def prependWork (count : ℕ) : ℕ := (count+1)*(3*count+5)+2





def current (pool : ℕ) : (count : ℕ) → (Vector (Fin pool) count → RationalResult) → RationalResult
  | 0, kernel => kernel (Vector.ofFn Fin.elim0)
  | count+1, kernel =>
      sumFin pool (fun head => current pool count (fun tail =>
        let word := prepend head tail
        let result := kernel word.value
        ⟨result.data, word.work+result.work+1⟩))



def height (pool : ℕ) : (count leafHeight : ℕ) → ℕ
  | 0, leafHeight => leafHeight
  | count+1, leafHeight => pool*(height pool count leafHeight+1)

def work (pool : ℕ) : (count leafHeight leafWork : ℕ) → ℕ
  | 0, _, leafWork => leafWork
  | count+1, leafHeight, leafWork =>
      pool*(work pool count leafHeight (prependWork count+leafWork+1)+
        primitiveWorkBound ((pool+1)*(height pool count leafHeight+1))+2)+2



noncomputable def heightPolynomial (pool : Polynomial ℕ) : (count : ℕ) → Polynomial ℕ → Polynomial ℕ
  | 0, leafHeight => leafHeight
  | count+1, leafHeight => pool*(heightPolynomial pool count leafHeight+1)

noncomputable def workPolynomial (pool : Polynomial ℕ) : (count : ℕ) → Polynomial ℕ → Polynomial ℕ → Polynomial ℕ
  | 0, _, leafWork => leafWork
  | count+1, leafHeight, leafWork =>
      pool*(workPolynomial pool count leafHeight (Polynomial.C (prependWork count)+leafWork+1)+
        primitiveWorkPolynomial ((pool+1)*(heightPolynomial pool count leafHeight+1))+2)+2





end CurrentAFT.BinaryTupleSum

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryTupleSum.heightPolynomial
  let _ ← Lean.Meta.getUnfoldEqnFor? `CurrentAFT.BinaryTupleSum.heightPolynomial true
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryTupleSum.workPolynomial
  let _ ← Lean.Meta.getUnfoldEqnFor? `CurrentAFT.BinaryTupleSum.workPolynomial true
  pure ()

end

section


























/-! # Executed finite pair canonicalization, including all marginal sums -/
namespace CurrentAFT.BinaryCanonicalPair
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | point | first | second | row | column | total
  deriving DecidableEq

def expression : ScalarProgram Leaf :=
  .add (.add (.add (.atom .point) (.negate (.multiply (.atom .first) (.atom .column))))
    (.negate (.multiply (.atom .row) (.atom .second))))
    (.multiply (.multiply (.atom .total) (.atom .first)) (.atom .second))



def read (values : Leaf → RationalBits) (code : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (values code)
  ⟨result.data,result.work+1⟩

def formula (values : Leaf → RationalBits) : RationalResult :=
  let result := expression.compileBinaryRun (read values)
  ⟨result.value,result.work+1⟩



def current (count : ℕ) (reference : Fin count → RationalResult) (mass : Fin count → Fin count → RationalResult)
    (first second : Fin count) : RationalResult :=
  let point := mass first second
  let refFirst := reference first
  let refSecond := reference second
  let row := sumFin count (mass first)
  let column := sumFin count (fun index => mass index second)
  let total := sumFin count (fun index => sumFin count (mass index))
  let result := formula (fun
    | .point => point.data | .first => refFirst.data | .second => refSecond.data
    | .row => row.data | .column => column.data | .total => total.data)
  ⟨result.data,point.work+refFirst.work+refSecond.work+row.work+column.work+total.work+result.work+7⟩



def marginalHeight (count bits : ℕ) := count*(bits+1)
def totalHeight (count bits : ℕ) := count*(marginalHeight count bits+1)
def operandHeight (count refBits massBits : ℕ) := refBits+massBits+marginalHeight count massBits+totalHeight count massBits
def height (count refBits massBits : ℕ) := expression.nodes*(operandHeight count refBits massBits+3)
def sumWork (count bits budget : ℕ) := count*(budget+primitiveWorkBound ((count+1)*(bits+1))+2)+2
def formulaWork (bits : ℕ) := expression.nodes*(smallRationalEncodingWork 1+(4*bits+9)+primitiveWorkBound (expression.nodes*(bits+3))+2)+2
def work (count refBits massBits refWork massWork : ℕ) :=
  massWork+2*refWork+2*sumWork count massBits massWork+
    sumWork count (marginalHeight count massBits) (sumWork count massBits massWork)+
    formulaWork (operandHeight count refBits massBits)+7





noncomputable def operandPolynomial (count refBits massBits : Polynomial ℕ) : Polynomial ℕ :=
  refBits+massBits+count*(massBits+1)+count*(count*(massBits+1)+1)
noncomputable def heightPolynomial (count refBits massBits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(operandPolynomial count refBits massBits+3)
noncomputable def sumWorkPolynomial (count bits budget : Polynomial ℕ) : Polynomial ℕ :=
  count*(budget+primitiveWorkPolynomial ((count+1)*(bits+1))+2)+2
noncomputable def formulaWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C expression.nodes*(smallRationalEncodingPolynomial 1+(4*bits+9)+primitiveWorkPolynomial (Polynomial.C expression.nodes*(bits+3))+2)+2
noncomputable def workPolynomial (count refBits massBits refWork massWork : Polynomial ℕ) : Polynomial ℕ :=
  massWork+2*refWork+2*sumWorkPolynomial count massBits massWork+
    sumWorkPolynomial count (count*(massBits+1)) (sumWorkPolynomial count massBits massWork)+
    formulaWorkPolynomial (operandPolynomial count refBits massBits)+7









end CurrentAFT.BinaryCanonicalPair

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCanonicalPair.formulaWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCanonicalPair.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCanonicalPair.operandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCanonicalPair.sumWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCanonicalPair.workPolynomial
  pure ()

end

section
































/-! # The genuine fair-sign diffuse pair, executed with binary data -/
namespace CurrentAFT.BinaryFairDiffuse
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryDiffuseCurrent.current

def midpoint (security : ℕ) : UnaryCounterResult :=
  let modulus := PublicParameterProgram.modulus security
  let last := differenceCounter modulus.count 1
  let result := divideCounter last.count 2
  ⟨result.quotient,modulus.work+last.work+result.work+3⟩

theorem midpoint_value (security : ℕ) :
    (midpoint security).count=(Parameters.modulus security-1)/2 := by
  simp only [midpoint,(divideCounter_value _ _ (by omega : 0<2)).1,differenceCounter_value,
    PublicParameterProgram.modulus_value]

theorem modulus_gt_two (security : ℕ) : 2<Parameters.modulus security := by
  have hb : 1 ≤ Parameters.base security^64 := one_le_pow₀ (by have := Parameters.base_ge_two security; omega)
  have h := (Parameters.modulus_bounds security).1
  omega

theorem midpoint_twice (security : ℕ) : 2*(midpoint security).count=Parameters.modulus security-1 := by
  rw [midpoint_value]
  obtain ⟨number,hn⟩ := (Parameters.modulus_spec security).2.even_sub_one (by have := modulus_gt_two security; omega)
  omega

def primary (security : ℕ) : FirstHistogram.Palette security :=
  ⟨(midpoint security).count,by have := midpoint_twice security; have := modulus_gt_two security; omega⟩



def current (security bits : ℕ) (scalar : IntegerBits) (first second : List Bool) : RationalResult :=
  let middle := midpoint security
  let result := BinaryDiffuseCurrent.current security bits middle.count scalar.negative scalar.digits first second
  ⟨result.data,middle.work+result.work+2⟩



noncomputable section
noncomputable def midpointWorkPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+2*BinaryFirstInverseProgram.colorsPolynomial+1+
    500*(BinaryFirstInverseProgram.colorsPolynomial+4)^2+3
noncomputable def heightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPairProgram.diffuseHeightPolynomial precision inputBits
noncomputable def workPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  midpointWorkPolynomial+BinaryDiffuseCurrent.currentWorkPolynomial precision inputBits+2





end
end CurrentAFT.BinaryFairDiffuse

end

section
























/-! # Executed current safe-interval membership test -/
namespace CurrentAFT.BinarySafeMembership
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinarySafeProfile.margin

def current (security : ℕ) (output : List Bool) : CountedValue Bool :=
  let modulus := PublicParameterProgram.modulus security
  let margin := BinarySafeProfile.margin security
  let qc := canonicalCounter modulus.count
  let mc := canonicalCounter margin.count
  let result := BinaryUnsafeProfile.membership qc.digits mc.digits output
  ⟨result.value,modulus.work+margin.work+qc.work+mc.work+result.work+5⟩



noncomputable section
noncomputable def parameterPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+3*(Polynomial.X+2)^2+inputBits
noncomputable def workPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinarySafeProfile.marginWorkPolynomial+
    100*(parameterPolynomial inputBits+1)^2+100*parameterPolynomial inputBits+100+5



end
end CurrentAFT.BinarySafeMembership

end

section


























/-! # True fair diffuse pair and its safe-core mask on stored binary colors -/
namespace CurrentAFT.BinaryDiffusePairLeaf
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryFairDiffuse.current BinarySafeProfile.current BinarySafeMembership.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def pair (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let fc := canonicalCounter first.val
  let sc := canonicalCounter second.val
  let result := BinaryFairDiffuse.current security bits scalar fc.digits sc.digits
  ⟨result.data,fc.work+sc.work+result.work+3⟩



def safePair (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let fc := canonicalCounter first.val
  let sc := canonicalCounter second.val
  let fs := BinarySafeMembership.current security fc.digits
  let ss := BinarySafeMembership.current security sc.digits
  let result := pair security bits scalar first second
  ⟨if fs.value && ss.value then result.data else zero,fc.work+sc.work+fs.work+ss.work+result.work+5⟩



def safeReference (security : ℕ) (output : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := BinarySafeProfile.current security code.digits
  ⟨result.data,code.work+result.work+2⟩



def uniformReference (security : ℕ) (_output : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let count := ofCounter modulus.count
  let result := RationalBits.inverse count.data
  ⟨result.data,modulus.work+count.work+result.work+3⟩



noncomputable section
noncomputable def codeWorkPolynomial : Polynomial ℕ := 50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2
noncomputable def inputPolynomial (scalarBits : Polynomial ℕ) : Polynomial ℕ := BinaryFirstInverseProgram.colorsPolynomial+scalarBits
noncomputable def pairHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFairDiffuse.heightPolynomial precision (inputPolynomial scalarBits)
noncomputable def pairWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  2*codeWorkPolynomial+BinaryFairDiffuse.workPolynomial precision (inputPolynomial scalarBits)+3
noncomputable def safePairWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  2*codeWorkPolynomial+2*BinarySafeMembership.workPolynomial BinaryFirstInverseProgram.colorsPolynomial+
    pairWorkPolynomial precision scalarBits+5
noncomputable def safeHeightPolynomial : Polynomial ℕ := BinarySafeProfile.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial
noncomputable def safeWorkPolynomial : Polynomial ℕ :=
  codeWorkPolynomial+BinarySafeProfile.workPolynomial BinaryFirstInverseProgram.colorsPolynomial+2
noncomputable def uniformWorkPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+60*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    primitiveWorkPolynomial BinaryFirstInverseProgram.colorsPolynomial+3











end
end CurrentAFT.BinaryDiffusePairLeaf

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffusePairLeaf.codeWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffusePairLeaf.safePairWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffusePairLeaf.safeWorkPolynomial
  pure ()

end

section



























/-! # Both literal canonicalizations of the actual fair diffuse pair -/
namespace CurrentAFT.BinaryDiffuseCanonical
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryCanonicalPair.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def seed (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryCanonicalPair.current modulus.count (BinaryDiffusePairLeaf.safeReference security)
    (BinaryDiffusePairLeaf.safePair security bits scalar) first second
  ⟨result.data,modulus.work+result.work+2⟩



def uniform (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryCanonicalPair.current modulus.count (BinaryDiffusePairLeaf.uniformReference security)
    (BinaryDiffusePairLeaf.pair security bits scalar) first second
  ⟨result.data,modulus.work+result.work+2⟩



noncomputable section
noncomputable def seedHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCanonicalPair.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial BinaryDiffusePairLeaf.safeHeightPolynomial
    (BinaryDiffusePairLeaf.pairHeightPolynomial precision scalarBits)
noncomputable def seedWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    BinaryCanonicalPair.workPolynomial BinaryFirstInverseProgram.colorsPolynomial BinaryDiffusePairLeaf.safeHeightPolynomial
      (BinaryDiffusePairLeaf.pairHeightPolynomial precision scalarBits) BinaryDiffusePairLeaf.safeWorkPolynomial
      (BinaryDiffusePairLeaf.safePairWorkPolynomial precision scalarBits)+2
noncomputable def uniformHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCanonicalPair.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial BinaryFirstInverseProgram.colorsPolynomial
    (BinaryDiffusePairLeaf.pairHeightPolynomial precision scalarBits)
noncomputable def uniformWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    BinaryCanonicalPair.workPolynomial BinaryFirstInverseProgram.colorsPolynomial BinaryFirstInverseProgram.colorsPolynomial
      (BinaryDiffusePairLeaf.pairHeightPolynomial precision scalarBits) BinaryDiffusePairLeaf.uniformWorkPolynomial
      (BinaryDiffusePairLeaf.pairWorkPolynomial precision scalarBits)+2





end
end CurrentAFT.BinaryDiffuseCanonical

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseCanonical.seedHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseCanonical.seedWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseCanonical.uniformHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseCanonical.uniformWorkPolynomial
  pure ()

end

section



























/-! # The actual diffuse body-pair density on binary reference atoms -/
namespace CurrentAFT.BinaryDiffuseBodyDensity
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current BinaryDiffuseCanonical.seed
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let seed := BinaryDiffuseCanonical.seed security bits scalar first second
  let refs := BinaryReferenceTables.current security bits
  let f := readVector zero refs.center first
  let s := readVector zero refs.center second
  let denominator := RationalBits.multiply f.value s.value
  let inverse := RationalBits.inverse denominator.data
  let result := RationalBits.multiply seed.data inverse.data
  ⟨result.data,seed.work+refs.work+f.work+s.work+denominator.work+inverse.work+result.work+7⟩



noncomputable section
noncomputable def operandPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCanonical.seedHeightPolynomial precision scalarBits+2*BinaryReferenceTables.heightPolynomial precision
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := operandPolynomial precision scalarBits
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCanonical.seedWorkPolynomial precision scalarBits+BinaryReferenceTables.currentWorkPolynomial precision+
    6*BinaryFirstInverseProgram.colorsPolynomial+6+3*primitiveWorkPolynomial (operandPolynomial precision scalarBits)+7



end
end CurrentAFT.BinaryDiffuseBodyDensity

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseBodyDensity.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseBodyDensity.operandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseBodyDensity.workPolynomial
  pure ()

end

section























namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.BinaryRootConvolution
end CurrentAFT.BinaryRootConvolution
namespace CurrentAFT.RationalBackgroundProfiles
end CurrentAFT.RationalBackgroundProfiles



/-! # Materialized local profiles for the true binary root convolution -/
namespace CurrentAFT.BinaryRootConvolutionInput
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryRootConvolution.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (profile : Fin (colors security) → RationalResult) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let input := buildArray modulus.count profile
  let result := BinaryRootConvolution.current security bits input.data output
  ⟨result.data,modulus.work+input.work+result.work+4⟩



noncomputable section
noncomputable def heightPolynomial (precision inputBits profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootConvolution.heightPolynomial precision inputBits profileBits
noncomputable def workPolynomial (precision inputBits profileBits profileWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryFirstInverseProgram.colorsPolynomial*(profileWork+2)+2+
    BinaryRootConvolution.workPolynomial precision inputBits profileBits+4



end
end CurrentAFT.BinaryRootConvolutionInput

end

section



























/-! # Actual double-root smoothing of the joint safe diffuse seed -/
namespace CurrentAFT.BinaryDiffuseResidual
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryRootConvolutionInput.current BinaryDiffuseCanonical.seed BinaryDiffuseCanonical.uniform
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def inner (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter second.val
  let result := BinaryRootConvolutionInput.current security bits (BinaryDiffuseCanonical.seed security bits scalar first) code.digits
  ⟨result.data,code.work+result.work+2⟩



def smoothed (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter first.val
  let result := BinaryRootConvolutionInput.current security bits (fun left => inner security bits scalar left second) code.digits
  ⟨result.data,code.work+result.work+2⟩



def current (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let uniform := BinaryDiffuseCanonical.uniform security bits scalar first second
  let smooth := smoothed security bits scalar first second
  let negative := RationalBits.negate smooth.data
  let result := RationalBits.add uniform.data negative.data
  ⟨result.data,uniform.work+smooth.work+negative.work+result.work+4⟩



noncomputable section
noncomputable def innerHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootConvolutionInput.heightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial
    (BinaryDiffuseCanonical.seedHeightPolynomial precision scalarBits)
noncomputable def innerWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffusePairLeaf.codeWorkPolynomial+
    BinaryRootConvolutionInput.workPolynomial precision BinaryFirstInverseProgram.colorsPolynomial
      (BinaryDiffuseCanonical.seedHeightPolynomial precision scalarBits) (BinaryDiffuseCanonical.seedWorkPolynomial precision scalarBits)+2
noncomputable def smoothedHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootConvolutionInput.heightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial (innerHeightPolynomial precision scalarBits)
noncomputable def smoothedWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffusePairLeaf.codeWorkPolynomial+
    BinaryRootConvolutionInput.workPolynomial precision BinaryFirstInverseProgram.colorsPolynomial
      (innerHeightPolynomial precision scalarBits) (innerWorkPolynomial precision scalarBits)+2
noncomputable def operandPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCanonical.uniformHeightPolynomial precision scalarBits+smoothedHeightPolynomial precision scalarBits
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := operandPolynomial precision scalarBits+1
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCanonical.uniformWorkPolynomial precision scalarBits+smoothedWorkPolynomial precision scalarBits+
    2*primitiveWorkPolynomial (operandPolynomial precision scalarBits)+4







end
end CurrentAFT.BinaryDiffuseResidual

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseResidual.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseResidual.innerWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseResidual.operandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseResidual.smoothedWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseResidual.workPolynomial
  pure ()

end

section




















/-! # Counted fixed-length products of computed binary rationals -/
namespace CurrentAFT.BinaryFiniteProduct
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1400000

def current : (count : ℕ) → (Fin count → RationalResult) → RationalResult
  | 0, _ => ⟨one,2⟩
  | count+1, term =>
      let previous := current count (fun index => term index.castSucc)
      let next := term (Fin.last count)
      let result := RationalBits.multiply previous.data next.data
      ⟨result.data, previous.work+next.work+result.work+2⟩





def work (count bits termWork : ℕ) := count*(termWork+primitiveWorkBound (count*bits)+2)+2



noncomputable def workPolynomial (count : ℕ) (bits termWork : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C count*(termWork+primitiveWorkPolynomial (Polynomial.C count*bits)+2)+2



end CurrentAFT.BinaryFiniteProduct

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFiniteProduct.workPolynomial
  pure ()

end

section
























/-! # Actual binary columns of the current first mass lift -/
namespace CurrentAFT.BinaryMassLiftColumn
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lessCounter BinaryFirstInverseProgram.current PublicParameterProgram.modulus

def point {count : ℕ} (source output : Fin count) : RationalResult :=
  let forward := lessCounter source.val output.val
  let backward := lessCounter output.val source.val
  ⟨if forward.value || backward.value then zero else one, forward.work+backward.work+3⟩







def delta {count : ℕ} (source : Fin count) : ArrayResult count := buildArray count (point source)





def current (security bits : ℕ) (source output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let input := delta source
  let result := BinaryFirstInverseProgram.current security bits input.data output
  ⟨result.data, input.work+result.work+3⟩



noncomputable section
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.currentHeightPolynomial precision 1
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  Q*(12*Q+9)+2+BinaryFirstInverseProgram.currentWorkPolynomial precision 1+3



end
end CurrentAFT.BinaryMassLiftColumn

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftColumn.workPolynomial
  pure ()

end

section































/-! # The full joint mass-lift tensor on explicitly enumerated binary tuples -/
namespace CurrentAFT.BinaryMassLiftTensor
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryMassLiftColumn.current BinaryFiniteProduct.current
  BinaryTupleSum.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def first (security : ℕ) : Fin (colors security) :=
  ⟨0, by rw [colors, BinaryFirstInverseProgram.colors, PublicParameterProgram.modulus_value]
         exact (Parameters.modulus_spec security).2.pos⟩

def column {degree : ℕ} (security bits : ℕ) (source output : Vector (Fin (colors security)) degree)
    (slot : Fin degree) : RationalResult :=
  let input := readVector (first security) source slot
  let result := readVector (first security) output slot
  let entry := BinaryMassLiftColumn.current security bits input.value result.value
  ⟨entry.data, input.work+result.work+entry.work+3⟩



def term {degree : ℕ} (security bits : ℕ) (output : Vector (Fin (colors security)) degree)
    (profile : Vector (Fin (colors security)) degree → RationalResult)
    (source : Vector (Fin (colors security)) degree) : RationalResult :=
  let input := profile source
  let kernel := BinaryFiniteProduct.current degree (column security bits source output)
  let result := RationalBits.multiply input.data kernel.data
  ⟨result.data, input.work+kernel.work+result.work+3⟩



def current (security bits degree : ℕ) (output : Vector (Fin (colors security)) degree)
    (profile : Vector (Fin (colors security)) degree → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := BinaryTupleSum.current modulus.count degree (term security bits output profile)
  ⟨result.data, modulus.work+result.work+2⟩



noncomputable section





noncomputable def columnWorkPolynomial (degree : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (6*degree+9)+BinaryMassLiftColumn.workPolynomial precision
noncomputable def termHeightPolynomial (degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  inputBits+Polynomial.C degree*BinaryMassLiftColumn.heightPolynomial precision
noncomputable def termWorkPolynomial (degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  inputWork+BinaryFiniteProduct.workPolynomial degree (BinaryMassLiftColumn.heightPolynomial precision)
    (columnWorkPolynomial degree precision)+primitiveWorkPolynomial (termHeightPolynomial degree precision inputBits)+3
noncomputable def heightPolynomial (degree : ℕ) (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryTupleSum.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial degree (termHeightPolynomial degree precision inputBits)
noncomputable def workPolynomial (degree : ℕ) (precision inputBits inputWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    BinaryTupleSum.workPolynomial BinaryFirstInverseProgram.colorsPolynomial degree
      (termHeightPolynomial degree precision inputBits) (termWorkPolynomial degree precision inputBits inputWork)+2







end
end CurrentAFT.BinaryMassLiftTensor

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftTensor.columnWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftTensor.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftTensor.termHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftTensor.termWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMassLiftTensor.workPolynomial
  pure ()

end

section

































/-! # The complete original diffuse certificate, with both mixed coefficient fibers -/
namespace CurrentAFT.BinaryDiffuseFamily
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDiffuseResidual.current BinaryDiffuseBodyDensity.current
  BinaryMassLiftTensor.current BinaryCoefficientFiber.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def residual (security bits : ℕ) (scalar : IntegerBits) (word : Vector (Fin (colors security)) 2) : RationalResult :=
  let first := readVector (BinaryFirstFamily.first security) word 0
  let second := readVector (BinaryFirstFamily.first security) word 1
  let result := BinaryDiffuseResidual.current security bits scalar first.value second.value
  ⟨result.data,first.work+second.work+result.work+3⟩



def primaryKernel (security bits : ℕ) (scalar : IntegerBits)
    (inputs : Vector (Fin (colors security)) 2) (_centers : Vector (Fin (colors security)) 0) : RationalResult :=
  BinaryMassLiftTensor.current security bits 2 inputs (residual security bits scalar)



def bodyKernel (security bits : ℕ) (scalar : IntegerBits)
    (_inputs : Vector (Fin (colors security)) 0) (centers : Vector (Fin (colors security)) 2) : RationalResult :=
  let first := readVector (BinaryFirstFamily.first security) centers 0
  let second := readVector (BinaryFirstFamily.first security) centers 1
  let result := BinaryDiffuseBodyDensity.current security bits scalar first.value second.value
  ⟨result.data,first.work+second.work+result.work+3⟩



def body (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) : RationalResult :=
  BinaryCoefficientFiber.current security arity.val.1.val arity.val.2.val 0 2 inputs centers (bodyKernel security bits scalar)

def primary (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) : RationalResult :=
  BinaryCoefficientFiber.current security arity.val.1.val arity.val.2.val 2 0 inputs centers (primaryKernel security bits scalar)





def current (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) : RationalResult :=
  let body := body security bits order scalar arity inputs centers
  let primary := primary security bits order scalar arity inputs centers
  let result := RationalBits.add body.data primary.data
  ⟨result.data,body.work+primary.work+result.work+3⟩



noncomputable section
noncomputable def residualWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := BinaryDiffuseResidual.workPolynomial precision scalarBits+21
noncomputable def primaryHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftTensor.heightPolynomial 2 precision (BinaryDiffuseResidual.heightPolynomial precision scalarBits)
noncomputable def primaryWorkPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftTensor.workPolynomial 2 precision (BinaryDiffuseResidual.heightPolynomial precision scalarBits)
    (residualWorkPolynomial precision scalarBits)+Polynomial.C (6*order+46)
noncomputable def bodyWorkPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseBodyDensity.workPolynomial precision scalarBits+Polynomial.C (6*order+67)
noncomputable def operandPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseBodyDensity.heightPolynomial precision scalarBits+primaryHeightPolynomial precision scalarBits
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := operandPolynomial precision scalarBits+1
noncomputable def workPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  bodyWorkPolynomial order precision scalarBits+primaryWorkPolynomial order precision scalarBits+
    primitiveWorkPolynomial (operandPolynomial precision scalarBits)+3











end
end CurrentAFT.BinaryDiffuseFamily

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseFamily.bodyWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseFamily.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseFamily.operandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseFamily.primaryWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseFamily.residualWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDiffuseFamily.workPolynomial
  pure ()

end

section


























/-! # Charged conversion of natural coefficient coordinates to the palette -/
namespace CurrentAFT.BinaryCoefficientInput
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus lessCounter
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def first (security : ℕ) : Fin (colors security) := BinaryFirstFamily.first security

def entry {count : ℕ} (security : ℕ) (modulus : ℕ) (hmodulus : modulus=colors security)
    (input : Vector ℕ count) (index : Fin count) : CountedValue (Fin (colors security)) :=
  let value := readVector 0 input index
  let checked := lessCounter value.value modulus
  if h : checked.value=true then
    ⟨⟨value.value,by rw [← hmodulus]; exact (lessCounter_value value.value modulus).mp h⟩,value.work+checked.work+2⟩
  else ⟨first security,value.work+checked.work+2⟩



def convert {count : ℕ} (security : ℕ) (modulus : ℕ) (hmodulus : modulus=colors security)
    (input : Vector ℕ count) : CountedValue (Vector (Fin (colors security)) count) :=
  storeData count (entry security modulus hmodulus input)



def current (security r s : ℕ) (inputs : Vector ℕ r) (centers : Vector ℕ s)
    (kernel : Vector (Fin (colors security)) r → Vector (Fin (colors security)) s → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let primary := convert security modulus.count rfl inputs
  let body := convert security modulus.count rfl centers
  let result := kernel primary.value body.value
  ⟨result.data,modulus.work+primary.work+body.work+result.work+4⟩





noncomputable section
noncomputable def workPolynomial (order : ℕ) (kernelWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+
    2*Polynomial.C order*(Polynomial.C (3*order)+6*BinaryFirstInverseProgram.colorsPolynomial+9)+kernelWork+8



end
end CurrentAFT.BinaryCoefficientInput

end

section


























/-! # Concrete palette programs as guarded natural coefficient programs -/
namespace CurrentAFT.BinaryFiniteCoefficient
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

abbrev FiniteProgram (security order : ℕ) := (arity : TruncatedArity order) →
  Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val →
    Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val → RationalResult

def lift (security order : ℕ) (kernel : FiniteProgram security order) : CoefficientProgram order :=
  fun arity inputs centers =>
    let result := BinaryCoefficientInput.current security arity.val.1.val arity.val.2.val inputs centers (kernel arity)
    ⟨result.data,result.work+1⟩



noncomputable section
noncomputable def workPolynomial (order : ℕ) (kernelWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientInput.workPolynomial order kernelWork+1



end
end CurrentAFT.BinaryFiniteCoefficient

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFiniteCoefficient.workPolynomial
  pure ()

end

section
























/-! # Binary primary conjugation before the actual mass lift -/
namespace CurrentAFT.BinaryDensityInverseProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
  BinaryFirstInverseProgram.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def term {count : ℕ} (primary score : Vector RationalBits count) (color : Fin count) : RationalResult :=
  let atom := readVector zero primary color
  let point := readVector zero score color
  let result := RationalBits.multiply atom.value point.value
  ⟨result.data, atom.work+point.work+result.work+3⟩



def conjugate (security bits : ℕ) (score : Vector RationalBits (colors security)) : ArrayResult (colors security) :=
  let reference := BinaryReferenceTables.current security bits
  let result := buildArray (colors security) (term reference.primary score)
  ⟨result.data, reference.work+result.work+2⟩





def current (security bits : ℕ) (score : Vector RationalBits (colors security)) (output : Fin (colors security)) : RationalResult :=
  let input := conjugate security bits score
  let result := BinaryFirstInverseProgram.current security bits input.data output
  ⟨result.data, input.work+result.work+3⟩



noncomputable section
open scoped Classical

noncomputable def operandHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.heightPolynomial precision+inputBits
noncomputable def conjugateHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*operandHeightPolynomial precision inputBits
noncomputable def conjugateWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  BinaryReferenceTables.currentWorkPolynomial precision+Q*(6*Q+11+
    primitiveWorkPolynomial (operandHeightPolynomial precision inputBits))+4



noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.currentHeightPolynomial precision (conjugateHeightPolynomial precision inputBits)
noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  conjugateWorkPolynomial precision inputBits+
    BinaryFirstInverseProgram.currentWorkPolynomial precision (conjugateHeightPolynomial precision inputBits)+3



end
end CurrentAFT.BinaryDensityInverseProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseProgram.conjugateHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseProgram.conjugateWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseProgram.currentWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseProgram.operandHeightPolynomial
  pure ()

end

section
























/-! # Executed materialization of arbitrary current density-inverse inputs -/
namespace CurrentAFT.BinaryDensityInverseInput
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryDensityInverseProgram.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security



def current (security bits : ℕ) (profile : Fin (colors security)→RationalResult) (output : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let input := buildArray modulus.count profile
  let result := BinaryDensityInverseProgram.current security bits input.data output
  ⟨result.data,modulus.work+input.work+result.work+4⟩



noncomputable section
noncomputable def heightPolynomial (precision profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDensityInverseProgram.currentHeightPolynomial precision profileBits
noncomputable def workPolynomial (precision profileBits profileWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryFirstInverseProgram.colorsPolynomial*(profileWork+2)+2+
    BinaryDensityInverseProgram.currentWorkPolynomial precision profileBits+4



end
end CurrentAFT.BinaryDensityInverseInput

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryDensityInverseInput.workPolynomial
  pure ()

end

section


























/-! # The original fixed-scalar marked anchor with an actual binary index average -/
namespace CurrentAFT.BinaryMarkedFixedAnchor
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDiffuseCurrent.metadata BinaryMarkedKernel.average PublicParameterProgram.modulus

def current (security : ℕ) (scalar : IntegerBits) (primary : Fin (BinaryFirstInverseProgram.colors security))
    (output : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let code := canonicalCounter primary.val
  let result := BinaryMarkedKernel.average parameters.colors parameters.width primary.val 0 0
    scalar.negative scalar.digits code.digits output
  ⟨result.data,parameters.work+code.work+result.work+3⟩



noncomputable section
noncomputable def widthPolynomial : Polynomial ℕ := (Polynomial.X+2)^48
noncomputable def parameterPolynomial (scalarBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+widthPolynomial+scalarBits+outputBits
noncomputable def heightPolynomial : Polynomial ℕ := BinaryMarkedCurrent.averageHeightPolynomial widthPolynomial
noncomputable def workPolynomial (scalarBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial+50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryMarkedCurrent.averageWorkPolynomial widthPolynomial (parameterPolynomial scalarBits outputBits)+3



end
end CurrentAFT.BinaryMarkedFixedAnchor

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedFixedAnchor.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedFixedAnchor.workPolynomial
  pure ()

end

section
























/-! # Same-scalar marked centered profiles and their actual primary mean -/
namespace CurrentAFT.BinaryMarkedCenteredCache
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current BinaryMarkedFixedAnchor.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def point (security : ℕ) (scalar : IntegerBits) (primary output : Fin (colors security)) (center : RationalBits) : RationalResult :=
  let code := canonicalCounter output.val
  let anchor := BinaryMarkedFixedAnchor.current security scalar primary code.digits
  let ratio := RationalBits.quotient anchor.data center
  let result := RationalBits.add ratio.data minusOne
  ⟨result.data,code.work+anchor.work+ratio.work+result.work+4⟩



def read {count : ℕ} (profile : Vector RationalBits count) (index : Fin count) : RationalResult :=
  let result := readVector zero profile index
  ⟨result.value,result.work+1⟩

structure Result (security : ℕ) where
  primary : Vector RationalBits (colors security)
  centered : Vector RationalBits (colors security)
  mean : RationalBits
  count : RationalBits
  work : ℕ

def current (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) : Result security :=
  let modulus := PublicParameterProgram.modulus security
  let count := ofCounter modulus.count
  let reference := BinaryReferenceTables.current security bits
  let center := readVector zero reference.center output
  let profile := buildArray modulus.count (fun primary => point security scalar primary output center.value)
  let mean := BinaryWindowAverage.sum reference.primary (read profile.data)
  ⟨reference.primary,profile.data,mean.data,count.data,
    modulus.work+count.work+reference.work+center.work+profile.work+mean.work+6⟩









noncomputable section
noncomputable def pointOperandHeightPolynomial (centerBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMarkedFixedAnchor.heightPolynomial+centerBits
noncomputable def pointHeightPolynomial (centerBits : Polynomial ℕ) : Polynomial ℕ := pointOperandHeightPolynomial centerBits+1
noncomputable def pointWorkPolynomial (scalarBits centerBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryMarkedFixedAnchor.workPolynomial scalarBits BinaryFirstInverseProgram.colorsPolynomial+
    3*primitiveWorkPolynomial (pointOperandHeightPolynomial centerBits)+6
noncomputable def profileHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := pointHeightPolynomial (BinaryReferenceTables.heightPolynomial precision)
noncomputable def profileWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := pointWorkPolynomial scalarBits (BinaryReferenceTables.heightPolynomial precision)
noncomputable def meanHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(BinaryReferenceTables.heightPolynomial precision+profileHeightPolynomial precision+1)
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.heightPolynomial precision+profileHeightPolynomial precision+meanHeightPolynomial precision+
    BinaryFirstInverseProgram.colorsPolynomial
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  PublicParameterProgram.workPolynomial+60*(Q+1)^2+BinaryReferenceTables.currentWorkPolynomial precision+3*Q+3+
    Q*(profileWorkPolynomial precision scalarBits+2)+2+
    BinaryWindowAverage.sumWorkPolynomial Q (BinaryReferenceTables.heightPolynomial precision) (profileHeightPolynomial precision) (3*Q+4)+6





end
end CurrentAFT.BinaryMarkedCenteredCache

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedCenteredCache.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedCenteredCache.meanHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedCenteredCache.pointHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedCenteredCache.pointOperandHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedCenteredCache.pointWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedCenteredCache.workPolynomial
  pure ()

end

section


























/-! # Original centered marked mixed density and its actual binary inverse -/
namespace CurrentAFT.BinaryMarkedSeed
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryMarkedCenteredCache.current BinaryDensityInverseInput.current PublicParameterProgram.modulus

def point {security : ℕ} (cache : BinaryMarkedCenteredCache.Result security)
    (primary : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let value := readVector zero cache.centered primary
  let atom := readVector zero cache.primary primary
  let countInverse := RationalBits.inverse cache.count
  let atomInverse := RationalBits.inverse atom.value
  let reciprocal := RationalBits.multiply countInverse.data atomInverse.data
  let correction := RationalBits.multiply reciprocal.data cache.mean
  let negative := RationalBits.negate correction.data
  let result := RationalBits.add value.value negative.data
  ⟨result.data,value.work+atom.work+countInverse.work+atomInverse.work+reciprocal.work+correction.work+negative.work+result.work+9⟩



def current (security bits : ℕ) (scalar : IntegerBits)
    (primary center : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let cache := BinaryMarkedCenteredCache.current security bits scalar center
  let result := BinaryDensityInverseInput.current security bits (point cache) primary
  ⟨result.data,cache.work+result.work+3⟩



def pointWork (count bits : ℕ) := 6*count+6*primitiveWorkBound (3*bits)+15



noncomputable section
noncomputable def pointHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  4*BinaryMarkedCenteredCache.heightPolynomial precision+1
noncomputable def pointWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  6*BinaryFirstInverseProgram.colorsPolynomial+6*primitiveWorkPolynomial (3*BinaryMarkedCenteredCache.heightPolynomial precision)+15
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDensityInverseInput.heightPolynomial precision (pointHeightPolynomial precision)
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMarkedCenteredCache.workPolynomial precision scalarBits+
    BinaryDensityInverseInput.workPolynomial precision (pointHeightPolynomial precision) (pointWorkPolynomial precision)+3



end
end CurrentAFT.BinaryMarkedSeed

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedSeed.pointHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedSeed.pointWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedSeed.workPolynomial
  pure ()

end

section




























/-! # The original marked mixed coefficient fiber as a complete binary program -/
namespace CurrentAFT.BinaryMarkedMixedFamily
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryMarkedSeed.current BinaryCoefficientFiber.current PublicParameterProgram.modulus

def kernel (security bits : ℕ) (scalar : IntegerBits)
    (inputs centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) 1) : RationalResult :=
  let primary := readVector (BinaryFirstFamily.first security) inputs 0
  let center := readVector (BinaryFirstFamily.first security) centers 0
  let result := BinaryMarkedSeed.current security bits scalar primary.value center.value
  ⟨result.data,primary.work+center.work+result.work+3⟩



def current (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) : RationalResult :=
  BinaryCoefficientFiber.current security arity.val.1.val arity.val.2.val 1 1 inputs centers (kernel security bits scalar)



noncomputable section
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryMarkedSeed.heightPolynomial precision
noncomputable def workPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMarkedSeed.workPolynomial precision scalarBits+Polynomial.C (6*order+61)





end
end CurrentAFT.BinaryMarkedMixedFamily

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedMixedFamily.workPolynomial
  pure ()

end

section




























/-! # The actual primary-minus-uniform mass certificate on binary data -/
namespace CurrentAFT.BinaryPrimaryDeviation
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current BinaryMassLiftInput.current BinaryFirstFamily.current

def point {count : ℕ} (primary : Vector RationalBits count) (colors : RationalBits) (output : Fin count) : RationalResult :=
  let atom := readVector zero primary output
  let uniform := RationalBits.inverse colors
  let negative := RationalBits.negate uniform.data
  let result := RationalBits.add atom.value negative.data
  ⟨result.data,atom.work+uniform.work+negative.work+result.work+4⟩



def density (security bits : ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let count := ofCounter modulus.count
  let reference := BinaryReferenceTables.current security bits
  let result := BinaryMassLiftInput.current security bits (point reference.primary count.data) output
  ⟨result.data,modulus.work+count.work+reference.work+result.work+4⟩



def current (security bits order : ℕ) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) : RationalResult :=
  BinaryFirstFamily.current security arity.val.1.val arity.val.2.val (density security bits) (fun _ => ⟨zero,2⟩) inputs centers



def pointWork (count bits : ℕ) := 3*count+3*primitiveWorkBound bits+7



noncomputable section
noncomputable def operandHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.heightPolynomial precision+BinaryFirstInverseProgram.colorsPolynomial
noncomputable def pointHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := 2*operandHeightPolynomial precision+1
noncomputable def pointWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  3*BinaryFirstInverseProgram.colorsPolynomial+3*primitiveWorkPolynomial (operandHeightPolynomial precision)+7
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (pointHeightPolynomial precision)
noncomputable def densityWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+60*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryReferenceTables.currentWorkPolynomial precision+
    BinaryMassLiftInput.workPolynomial precision (pointHeightPolynomial precision) (pointWorkPolynomial precision)+4
noncomputable def workPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ := densityWorkPolynomial precision+Polynomial.C (15*order+52)





end
end CurrentAFT.BinaryPrimaryDeviation

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryDeviation.densityWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryDeviation.operandHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryDeviation.pointHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryDeviation.pointWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPrimaryDeviation.workPolynomial
  pure ()

end

end


