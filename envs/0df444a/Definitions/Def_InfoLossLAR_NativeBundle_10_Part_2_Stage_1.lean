-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_10_Part_2_Stage_1
-- name    : InfoLossLAR_NativeBundle_10_Part_2_Stage_1
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T17:50:19.5437+00:00
-- url     : https://prove2.me/theorems/380f9db4-8680-4cf0-8528-9a3efe81666d
-- title:
--   Binary background leaves and conditional pair profiles
-- statement:
--   This package defines the finite binary background leaves, scalar and linear coefficient operations, conditional pair profiles and means, and marked pair programs. It preserves the concrete rational and binary interfaces and their immediate constructor semantics; approximation guarantees are proved by separate theorems.
-- source:
--   Unchanged scope-closed source modules from local proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, regrouped into a smaller semantic compilation unit after two terminal platform timeouts. All original source-body hashes are preserved; all 11528 public native/runtime types and recursive standard-axiom audits pass. Source SHA256 a98e7ecfdf6d253070d44bbca8c078d072318e28924d0eb0755d8c7621e10309.

import Definitions.Def_InfoLossLAR_NativeBundle_10_Part_1

section

































/-! # The actual background coefficient leaves in the common finite program format -/
namespace CurrentAFT.BinaryBackgroundLeaves
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Role where
  | free | translation | primaryDeviation | markedMixed | diffuse
  deriving DecidableEq

def finite (role : Role) (security bits order : ℕ) (scalar : IntegerBits) : BinaryFiniteCoefficient.FiniteProgram security order :=
  match role with
  | .free => BinaryBackgroundFamilies.free security bits order
  | .translation => BinaryBackgroundFamilies.translation security bits order scalar
  | .primaryDeviation => BinaryPrimaryDeviation.current security bits order
  | .markedMixed => BinaryMarkedMixedFamily.current security bits order scalar
  | .diffuse => BinaryDiffuseFamily.current security bits order scalar

def ideal (role : Role) (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  match role with
  | .free => RationalBackgroundProgram.free security bits order
  | .translation => RationalBackgroundProgram.translation security bits order scalar
  | .primaryDeviation => RationalPrimaryDeviationProgram.current security bits order
  | .markedMixed => RationalMarkedCertificateProgram.current security bits order scalar
  | .diffuse => RationalDiffuseFamilyProgram.current security bits order scalar

def current (role : Role) (security bits order : ℕ) (scalar : IntegerBits) : CoefficientProgram order :=
  BinaryFiniteCoefficient.lift security order (finite role security bits order scalar)





noncomputable section
noncomputable def heightPolynomial (role : Role) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .free => BinaryBackgroundFamilies.freeHeightPolynomial precision
  | .translation => BinaryBackgroundFamilies.translationHeightPolynomial precision scalarBits
  | .primaryDeviation => BinaryPrimaryDeviation.heightPolynomial precision
  | .markedMixed => BinaryMarkedMixedFamily.heightPolynomial precision
  | .diffuse => BinaryDiffuseFamily.heightPolynomial precision scalarBits
noncomputable def finiteWorkPolynomial (role : Role) (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .free => BinaryBackgroundFamilies.freeWorkPolynomial order precision
  | .translation => BinaryBackgroundFamilies.translationWorkPolynomial order precision scalarBits
  | .primaryDeviation => BinaryPrimaryDeviation.workPolynomial order precision
  | .markedMixed => BinaryMarkedMixedFamily.workPolynomial order precision scalarBits
  | .diffuse => BinaryDiffuseFamily.workPolynomial order precision scalarBits
noncomputable def workPolynomial (role : Role) (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteCoefficient.workPolynomial order (finiteWorkPolynomial role order precision scalarBits)





end
end CurrentAFT.BinaryBackgroundLeaves

end

section





















/-! # Executed fixed scalar syntax with every stored operand copied -/
namespace CurrentAFT.BinaryScalarFormula
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
variable {Leaf : Type*}

def read (values : Leaf → RationalBits) (leaf : Leaf) : CountedValue RationalBits :=
  let result := RationalBits.copy (values leaf)
  ⟨result.data,result.work+1⟩

def current (program : ScalarProgram Leaf) (values : Leaf → RationalBits) : RationalResult :=
  let result := program.compileBinaryRun (read values)
  ⟨result.value,result.work+1⟩



def height (program : ScalarProgram Leaf) (bits : ℕ) := program.nodes*(bits+3)
def work (program : ScalarProgram Leaf) (bits : ℕ) :=
  program.nodes*(smallRationalEncodingWork 1+(4*bits+9)+primitiveWorkBound (height program bits)+2)+2



noncomputable def heightPolynomial (program : ScalarProgram Leaf) (bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C program.nodes*(bits+3)
noncomputable def workPolynomial (program : ScalarProgram Leaf) (bits : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C program.nodes*(smallRationalEncodingPolynomial 1+(4*bits+9)+primitiveWorkPolynomial (heightPolynomial program bits)+2)+2




end CurrentAFT.BinaryScalarFormula

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryScalarFormula.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryScalarFormula.workPolynomial
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






/-! # The actual balanced leg-linear certificate, with scalar averaging last -/
namespace CurrentAFT.BinaryBackgroundLinear
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Leaf where
  | colors | legs | population | free | mean
  deriving DecidableEq

def expression : ScalarProgram Leaf :=
  .multiply (.negate (.add
    (.multiply (.add (.add (.atom .population) (.negate (.atom .legs))) (.negate (.atom .colors))) (.atom .free))
    (.multiply (.atom .colors) (.atom .mean)))) (.inverse (.atom .legs))



def values (metadata : BinaryProposalMetadata.Encoded) (free mean : RationalBits) : Leaf → RationalBits
  | .colors => metadata.colors | .legs => metadata.legs | .population => metadata.population | .free => free | .mean => mean

def meanTranslation (security bits order : ℕ) : CoefficientProgram order :=
  BinaryCoefficientScalarAverage.current security bits order (fun scalar => BinaryBackgroundLeaves.current .translation security bits order scalar)

def current (security bits order : ℕ) : CoefficientProgram order :=
  fun arity inputs centers =>
    let metadata := BinaryProposalMetadata.current security
    let free := BinaryBackgroundLeaves.current .free security bits order IntegerBits.zero arity inputs centers
    let mean := meanTranslation security bits order arity inputs centers
    let result := BinaryScalarFormula.current expression (values metadata free.value mean.value)
    ⟨result.data,metadata.work+free.work+mean.work+result.work+4⟩

noncomputable section




noncomputable def scalarBitsPolynomial : Polynomial ℕ := BinaryCoefficientScalarAverage.scalarBitsPolynomial
noncomputable def translationHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryBackgroundLeaves.heightPolynomial .translation precision scalarBitsPolynomial
noncomputable def translationWorkPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ := BinaryBackgroundLeaves.workPolynomial .translation order precision scalarBitsPolynomial
noncomputable def meanHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryCoefficientScalarAverage.heightPolynomial precision (translationHeightPolynomial precision)
noncomputable def meanWorkPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.workPolynomial precision (translationHeightPolynomial precision) (translationWorkPolynomial order precision)
noncomputable def operandPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.sizePolynomial+BinaryBackgroundLeaves.heightPolynomial .free precision scalarBitsPolynomial+meanHeightPolynomial precision
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryScalarFormula.heightPolynomial expression (operandPolynomial precision)
noncomputable def workPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProposalMetadata.currentWorkPolynomial+BinaryBackgroundLeaves.workPolynomial .free order precision scalarBitsPolynomial+
    meanWorkPolynomial order precision+BinaryScalarFormula.workPolynomial expression (operandPolynomial precision)+4





end
end CurrentAFT.BinaryBackgroundLinear

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundLinear.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundLinear.operandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundLinear.workPolynomial
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



/-! # Executed coefficient sums and compositional polynomial resource bounds -/
namespace CurrentAFT.BinaryCoefficientOperations
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def add (order : ℕ) (first second : CoefficientProgram order) : CoefficientProgram order :=
  fun arity inputs centers =>
    let a := first arity inputs centers
    let b := second arity inputs centers
    let result := RationalBits.add a.value b.value
    ⟨result.data,a.work+b.work+result.work+3⟩



noncomputable section
noncomputable def addHeight (firstBits secondBits : Polynomial ℕ) : Polynomial ℕ := firstBits+secondBits+1
noncomputable def addWork (firstBits secondBits firstWork secondWork : Polynomial ℕ) : Polynomial ℕ :=
  firstWork+secondWork+primitiveWorkPolynomial (firstBits+secondBits)+3





end
end CurrentAFT.BinaryCoefficientOperations

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientOperations.addHeight
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryCoefficientOperations.addWork
  pure ()

end

section




























/-! # Both actual pair marginals, with a common retained scalar -/
namespace CurrentAFT.BinaryConditionalPairProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryPairProgram.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def pair (security bits : ℕ) (scalar : IntegerBits) (primary first second : Fin (colors security)) : RationalResult :=
  let fc := canonicalCounter first.val
  let sc := canonicalCounter second.val
  let result := BinaryPairProgram.current security bits primary.val scalar.negative scalar.digits fc.digits sc.digits
  ⟨result.data,fc.work+sc.work+result.work+3⟩



def current (security bits : ℕ) (scalar : IntegerBits) (primary output : Fin (colors security)) : RationalResult :=
  let first := sumFin (colors security) (fun other => pair security bits scalar primary output other)
  let second := sumFin (colors security) (fun other => pair security bits scalar primary other output)
  let result := RationalBits.add first.data second.data
  ⟨result.data,first.work+second.work+result.work+3⟩



noncomputable section
noncomputable def inputPolynomial (scalarBits : Polynomial ℕ) : Polynomial ℕ := BinaryFirstInverseProgram.colorsPolynomial+scalarBits
noncomputable def pairHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPairProgram.currentHeightPolynomial precision (inputPolynomial scalarBits)
noncomputable def pairWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryDiffusePairLeaf.codeWorkPolynomial+BinaryPairProgram.currentWorkPolynomial precision (inputPolynomial scalarBits)+3
noncomputable def marginalHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(pairHeightPolynomial precision scalarBits+1)
noncomputable def marginalWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(pairWorkPolynomial precision scalarBits+
    primitiveWorkPolynomial ((BinaryFirstInverseProgram.colorsPolynomial+1)*(pairHeightPolynomial precision scalarBits+1))+2)+2
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := 2*marginalHeightPolynomial precision scalarBits+1
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  2*marginalWorkPolynomial precision scalarBits+primitiveWorkPolynomial (marginalHeightPolynomial precision scalarBits)+3





end
end CurrentAFT.BinaryConditionalPairProfile

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairProfile.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairProfile.inputPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairProfile.marginalHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairProfile.marginalWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairProfile.pairWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairProfile.workPolynomial
  pure ()

end

section




























/-! # The actual primary-averaged pair profile and its centered mass -/
namespace CurrentAFT.BinaryConditionalPairMean
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryReferenceTables.current
  BinaryConditionalPairProfile.current BinaryWindowAverage.sum
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def mean (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let refs := BinaryReferenceTables.current security bits
  let result := BinaryWindowAverage.sum refs.primary (fun primary => BinaryConditionalPairProfile.current security bits scalar primary output)
  ⟨result.data,modulus.work+refs.work+result.work+3⟩



def current (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) : RationalResult :=
  let averaged := mean security bits scalar output
  let modulus := PublicParameterProgram.modulus security
  let count := ofCounter modulus.count
  let two := ofCounter 2
  let reciprocal := RationalBits.inverse count.data
  let uniform := RationalBits.multiply two.data reciprocal.data
  let negative := RationalBits.negate uniform.data
  let result := RationalBits.add averaged.data negative.data
  ⟨result.data,averaged.work+modulus.work+count.work+two.work+reciprocal.work+uniform.work+negative.work+result.work+8⟩



noncomputable section
noncomputable def meanHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(BinaryReferenceTables.heightPolynomial precision+
    BinaryConditionalPairProfile.heightPolynomial precision scalarBits+1)
noncomputable def meanWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryReferenceTables.currentWorkPolynomial precision+
    BinaryWindowAverage.sumWorkPolynomial BinaryFirstInverseProgram.colorsPolynomial (BinaryReferenceTables.heightPolynomial precision)
      (BinaryConditionalPairProfile.heightPolynomial precision scalarBits) (BinaryConditionalPairProfile.workPolynomial precision scalarBits)+3
noncomputable def operandPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  meanHeightPolynomial precision scalarBits+BinaryFirstInverseProgram.colorsPolynomial+2
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := operandPolynomial precision scalarBits+1
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  meanWorkPolynomial precision scalarBits+PublicParameterProgram.workPolynomial+60*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    540+4*primitiveWorkPolynomial (operandPolynomial precision scalarBits)+8





end
end CurrentAFT.BinaryConditionalPairMean

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairMean.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairMean.meanHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairMean.meanWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairMean.operandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairMean.workPolynomial
  pure ()

end

section






























/-! # The literal current conditional pair mass certificate in binary form -/
namespace CurrentAFT.BinaryConditionalPairProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryMassLiftInput.current BinaryFirstFamily.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def density (security bits : ℕ) (scalar : IntegerBits) (output : Fin (colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (BinaryConditionalPairMean.current security bits scalar) output



def finite (security bits order : ℕ) (scalar : IntegerBits) : BinaryFiniteCoefficient.FiniteProgram security order :=
  fun arity inputs centers => BinaryFirstFamily.current security arity.val.1.val arity.val.2.val
    (density security bits scalar) (fun _ => ⟨zero,2⟩) inputs centers



def current (security bits order : ℕ) (scalar : IntegerBits) : BinaryFamilyProduct.CoefficientProgram order :=
  BinaryFiniteCoefficient.lift security order (finite security bits order scalar)



noncomputable section
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (BinaryConditionalPairMean.heightPolynomial precision scalarBits)
noncomputable def densityWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (BinaryConditionalPairMean.heightPolynomial precision scalarBits)
    (BinaryConditionalPairMean.workPolynomial precision scalarBits)
noncomputable def finiteWorkPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  densityWorkPolynomial precision scalarBits+Polynomial.C (15*order+52)
noncomputable def workPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteCoefficient.workPolynomial order (finiteWorkPolynomial order precision scalarBits)







end
end CurrentAFT.BinaryConditionalPairProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryConditionalPairProgram.finiteWorkPolynomial
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




/-! # The actual marked quadratic certificate, including its mixed product -/
namespace CurrentAFT.BinaryMarkedPairProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def product (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs
    (BinaryBackgroundLeaves.current .primaryDeviation security bits order scalar)
    (BinaryBackgroundLeaves.current .free security bits order scalar)

def current (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  fun arity inputs centers =>
    let mixed := BinaryBackgroundLeaves.current .markedMixed security bits order scalar arity inputs centers
    let product := product security bits order programs scalar arity inputs centers
    let result := RationalBits.add mixed.value product.value
    ⟨result.data,mixed.work+product.work+result.work+3⟩

noncomputable section




noncomputable def productOperandHeight (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundLeaves.heightPolynomial .primaryDeviation precision scalarBits+BinaryBackgroundLeaves.heightPolynomial .free precision scalarBits
noncomputable def productOperandWork (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundLeaves.workPolynomial .primaryDeviation order precision scalarBits+BinaryBackgroundLeaves.workPolynomial .free order precision scalarBits
noncomputable def productHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs (productOperandHeight precision scalarBits)
noncomputable def productWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs (productOperandHeight precision scalarBits) (productOperandWork order precision scalarBits)
noncomputable def operandPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundLeaves.heightPolynomial .markedMixed precision scalarBits+productHeightPolynomial order programs precision scalarBits
noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := operandPolynomial order programs precision scalarBits+1
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundLeaves.workPolynomial .markedMixed order precision scalarBits+productWorkPolynomial order programs precision scalarBits+
    primitiveWorkPolynomial (operandPolynomial order programs precision scalarBits)+3





end
end CurrentAFT.BinaryMarkedPairProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedPairProgram.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedPairProgram.operandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedPairProgram.productHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedPairProgram.productOperandHeight
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedPairProgram.productOperandWork
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedPairProgram.productWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMarkedPairProgram.workPolynomial
  pure ()

end


