-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_10_Part_2_Stage_2
-- name    : InfoLossLAR_NativeBundle_10_Part_2_Stage_2
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:05:57.917621+00:00
-- url     : https://prove2.me/theorems/6375e930-e2eb-40d0-95ed-e15d69d87dd2
-- title:
--   Binary mixtures, leg backgrounds, and response counts
-- statement:
--   This package defines mixtures of finite pair responses, quadratic pair programs, conditional leg and leg-background programs, background population data, full-response counting interfaces, and distinct-tuple enumerations. The finite algorithms are explicit and do not assume any transport or lattice-reduction conclusion.
-- source:
--   Unchanged scope-closed source modules from local proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, regrouped into a smaller semantic compilation unit after two terminal platform timeouts. All original source-body hashes are preserved; all 11528 public native/runtime types and recursive standard-axiom audits pass. Source SHA256 e89dbc82bd47f9a9f81acce9f4aa60fc48b2c18b4b79137dfc1ed3d25db2048f. Compiler-only optimization: one local scope marks Polynomial addition and multiplication instances irreducible while generating native equation lemmas. Every original definition and proof source body is unchanged; all11528 public types and recursive standard-axiom audits pass. New sourceSHA256 ba0e07be3a225647af83776b6482d02b3c6bdf748b4a79638bf96dd2b1396b43. Only dependency version changed to the measured compiler-optimized Stage1; all mathematical body bytes and public types are preserved. SourceSHA256 1e4b8a60718ddef7b433f7cadbd04528c8d99b077ebe318c72cba2c97be567e4.

import Definitions.Def_InfoLossLAR_NativeBundle_10_Part_2_Stage_1_Optimized

section
attribute [local irreducible] Polynomial.instAdd Polynomial.instMul

section





















/-! # Executed binary affine mixture with derived operand heights -/
namespace CurrentAFT.BinaryMixture
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (rate first second : RationalBits) : RationalResult :=
  let negative := RationalBits.negate rate
  let remaining := RationalBits.add one negative.data
  let left := RationalBits.multiply remaining.data first
  let right := RationalBits.multiply rate second
  let result := RationalBits.add left.data right.data
  ⟨result.data,negative.work+remaining.work+left.work+right.work+result.work+5⟩



def height (bits : ℕ) := 4*bits+2
def work (bits : ℕ) := 5*primitiveWorkBound (height bits)+5



noncomputable def heightPolynomial (bits : Polynomial ℕ) : Polynomial ℕ := 4*bits+2
noncomputable def workPolynomial (bits : Polynomial ℕ) : Polynomial ℕ := 5*primitiveWorkPolynomial (heightPolynomial bits)+5




end CurrentAFT.BinaryMixture

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMixture.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryMixture.workPolynomial
  pure ()

end

section





























/-! # The literal activation mixture of complete actual quadratic data -/
namespace CurrentAFT.BinaryPairQuadraticProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  fun arity inputs centers =>
    let rate := BinaryActivationProgram.current security bits
    let diffuse := BinaryBackgroundLeaves.current .diffuse security bits order scalar arity inputs centers
    let marked := BinaryMarkedPairProgram.current security bits order programs scalar arity inputs centers
    let result := BinaryMixture.current rate.data diffuse.value marked.value
    ⟨result.data,rate.work+diffuse.work+marked.work+result.work+4⟩

noncomputable section


noncomputable def operandPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.currentHeightPolynomial precision+BinaryBackgroundLeaves.heightPolynomial .diffuse precision scalarBits+
    BinaryMarkedPairProgram.heightPolynomial order programs precision scalarBits
noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMixture.heightPolynomial (operandPolynomial order programs precision scalarBits)
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.currentWorkPolynomial precision+BinaryBackgroundLeaves.workPolynomial .diffuse order precision scalarBits+
    BinaryMarkedPairProgram.workPolynomial order programs precision scalarBits+
    BinaryMixture.workPolynomial (operandPolynomial order programs precision scalarBits)+4



end
end CurrentAFT.BinaryPairQuadraticProgram

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPairQuadraticProgram.heightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPairQuadraticProgram.operandPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryPairQuadraticProgram.workPolynomial
  pure ()

end

section































/-! # Same-scalar quadratic and cubic leg data before the Gaussian average -/
namespace CurrentAFT.BinaryLegConditional
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Role where | quadratic | cubic deriving DecidableEq

def left (role : Role) (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  match role with
  | .quadratic => BinaryConditionalPairProgram.current security bits order scalar
  | .cubic => BinaryPairQuadraticProgram.current security bits order programs scalar

def leftIdeal (role : Role) (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  match role with
  | .quadratic => RationalConditionalPairProgram.current security bits order scalar
  | .cubic => RationalPairQuadraticProgram.current security bits order scalar

def product (role : Role) (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (left role security bits order programs scalar)
    (BinaryBackgroundLeaves.current .translation security bits order scalar)

def current (role : Role) (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  match role with
  | .quadratic => BinaryCoefficientOperations.add order (BinaryPairQuadraticProgram.current security bits order programs scalar)
      (product .quadratic security bits order programs scalar)
  | .cubic => product .cubic security bits order programs scalar

def ideal (role : Role) (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  match role with
  | .quadratic => RationalLegBackgroundProgram.conditionalQuadratic security bits order scalar
  | .cubic => RationalLegBackgroundProgram.conditionalCubic security bits order scalar

noncomputable section






noncomputable def leftHeightPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .quadratic => BinaryConditionalPairProgram.heightPolynomial precision scalarBits
  | .cubic => BinaryPairQuadraticProgram.heightPolynomial order programs precision scalarBits
noncomputable def leftWorkPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .quadratic => BinaryConditionalPairProgram.workPolynomial order precision scalarBits
  | .cubic => BinaryPairQuadraticProgram.workPolynomial order programs precision scalarBits
noncomputable def productHeightPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs
    (leftHeightPolynomial role order programs precision scalarBits+BinaryBackgroundLeaves.heightPolynomial .translation precision scalarBits)
noncomputable def productWorkPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs
    (leftHeightPolynomial role order programs precision scalarBits+BinaryBackgroundLeaves.heightPolynomial .translation precision scalarBits)
    (leftWorkPolynomial role order programs precision scalarBits+BinaryBackgroundLeaves.workPolynomial .translation order precision scalarBits)
noncomputable def heightPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .quadratic => BinaryCoefficientOperations.addHeight (BinaryPairQuadraticProgram.heightPolynomial order programs precision scalarBits)
      (productHeightPolynomial .quadratic order programs precision scalarBits)
  | .cubic => productHeightPolynomial .cubic order programs precision scalarBits
noncomputable def workPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .quadratic => BinaryCoefficientOperations.addWork (BinaryPairQuadraticProgram.heightPolynomial order programs precision scalarBits)
      (productHeightPolynomial .quadratic order programs precision scalarBits) (BinaryPairQuadraticProgram.workPolynomial order programs precision scalarBits)
      (productWorkPolynomial .quadratic order programs precision scalarBits)
  | .cubic => productWorkPolynomial .cubic order programs precision scalarBits







end
end CurrentAFT.BinaryLegConditional

end

section



























/-! # The complete original leg-background atom as a binary coefficient program -/
namespace CurrentAFT.BinaryLegBackground
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def average (role : BinaryLegConditional.Role) (security bits order : ℕ) (programs : List (Entry order)) : CoefficientProgram order :=
  BinaryCoefficientScalarAverage.current security bits order (fun scalar => BinaryLegConditional.current role security bits order programs scalar)

def lowerPart (security bits order : ℕ) (programs : List (Entry order)) : CoefficientProgram order :=
  BinaryCoefficientOperations.add order (BinaryBackgroundLinear.current security bits order) (average .quadratic security bits order programs)

def current (security bits order : ℕ) (programs : List (Entry order)) : CoefficientProgram order :=
  BinaryCoefficientOperations.add order (lowerPart security bits order programs) (average .cubic security bits order programs)

noncomputable section




noncomputable def scalarBitsPolynomial : Polynomial ℕ := BinaryCoefficientScalarAverage.scalarBitsPolynomial
noncomputable def averageHeightPolynomial (role : BinaryLegConditional.Role) (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.heightPolynomial precision (BinaryLegConditional.heightPolynomial role order programs precision scalarBitsPolynomial)
noncomputable def averageWorkPolynomial (role : BinaryLegConditional.Role) (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.workPolynomial precision (BinaryLegConditional.heightPolynomial role order programs precision scalarBitsPolynomial)
    (BinaryLegConditional.workPolynomial role order programs precision scalarBitsPolynomial)
noncomputable def lowerPartHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientOperations.addHeight (BinaryBackgroundLinear.heightPolynomial precision) (averageHeightPolynomial .quadratic order programs precision)
noncomputable def lowerPartWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientOperations.addWork (BinaryBackgroundLinear.heightPolynomial precision) (averageHeightPolynomial .quadratic order programs precision)
    (BinaryBackgroundLinear.workPolynomial order precision) (averageWorkPolynomial .quadratic order programs precision)
noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientOperations.addHeight (lowerPartHeightPolynomial order programs precision) (averageHeightPolynomial .cubic order programs precision)
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientOperations.addWork (lowerPartHeightPolynomial order programs precision) (averageHeightPolynomial .cubic order programs precision)
    (lowerPartWorkPolynomial order programs precision) (averageWorkPolynomial .cubic order programs precision)







end
end CurrentAFT.BinaryLegBackground

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
namespace CurrentAFT.BinaryPopulationSemantics
end CurrentAFT.BinaryPopulationSemantics




/-! # The complete original fixed-queue background, executed on binary data -/
namespace CurrentAFT.BinaryBackgroundPopulation
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Role where | free | queue | leg deriving DecidableEq

def population (role : Role) (counts : BinaryBackgroundPopulationCounts.Counts) : ℕ :=
  match role with | .free => counts.free | .queue => counts.queue | .leg => counts.leg
def idealPopulation (role : Role) (security : ℕ) : ℕ :=
  match role with
  | .free => RationalBackgroundPopulationProgram.freeCount security
  | .queue => (PublicParameterProgram.modulus security).count
  | .leg => (security+2)^128

def atom (role : Role) (security bits order : ℕ) (programs : List (Entry order)) (queue : IntegerBits) : CoefficientProgram order :=
  match role with
  | .free => BinaryBackgroundLeaves.current .free security bits order IntegerBits.zero
  | .queue => BinaryBackgroundLeaves.current .translation security bits order queue
  | .leg => BinaryLegBackground.current security bits order programs
def atomIdeal (role : Role) (security bits order : ℕ) (queue : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  match role with
  | .free => RationalBackgroundProgram.free security bits order
  | .queue => RationalBackgroundProgram.translation security bits order queue
  | .leg => RationalLegBackgroundProgram.current security bits order

def factor (role : Role) (security bits order : ℕ) (programs : List (Entry order)) (queue : IntegerBits) : CoefficientProgram order :=
  fun arity inputs centers =>
    let counts := BinaryBackgroundPopulationCounts.current security
    let result := BinaryFamilyBinomial.current order (population role counts) programs
      (atom role security bits order programs queue) arity inputs centers
    ⟨result.value,counts.work+result.work+2⟩
def factorIdeal (role : Role) (security bits order : ℕ) (queue : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  RationalFamilyProductProgram.binomial order (idealPopulation role security) (atomIdeal role security bits order queue)

def freeQueue (security bits order : ℕ) (programs : List (Entry order)) (queue : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (factor .free security bits order programs queue) (factor .queue security bits order programs queue)
def current (security bits order : ℕ) (programs : List (Entry order)) (queue : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (freeQueue security bits order programs queue) (factor .leg security bits order programs queue)

noncomputable section










noncomputable def atomHeightPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .free => BinaryBackgroundLeaves.heightPolynomial .free precision queueBits
  | .queue => BinaryBackgroundLeaves.heightPolynomial .translation precision queueBits
  | .leg => BinaryLegBackground.heightPolynomial order programs precision
noncomputable def atomWorkPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .free => BinaryBackgroundLeaves.workPolynomial .free order precision queueBits
  | .queue => BinaryBackgroundLeaves.workPolynomial .translation order precision queueBits
  | .leg => BinaryLegBackground.workPolynomial order programs precision
noncomputable def factorHeightPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyBinomial.heightPolynomial order programs BinaryProposalMetadata.sizePolynomial (atomHeightPolynomial role order programs precision queueBits)
noncomputable def factorWorkPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundPopulationCounts.workPolynomial+
    BinaryFamilyBinomial.workPolynomial order programs BinaryProposalMetadata.sizePolynomial
      (atomHeightPolynomial role order programs precision queueBits) (atomWorkPolynomial role order programs precision queueBits)+2
noncomputable def freeQueueHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs
    (factorHeightPolynomial .free order programs precision queueBits+factorHeightPolynomial .queue order programs precision queueBits)
noncomputable def freeQueueWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs
    (factorHeightPolynomial .free order programs precision queueBits+factorHeightPolynomial .queue order programs precision queueBits)
    (factorWorkPolynomial .free order programs precision queueBits+factorWorkPolynomial .queue order programs precision queueBits)
noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs
    (freeQueueHeightPolynomial order programs precision queueBits+factorHeightPolynomial .leg order programs precision queueBits)
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision queueBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs
    (freeQueueHeightPolynomial order programs precision queueBits+factorHeightPolynomial .leg order programs precision queueBits)
    (freeQueueWorkPolynomial order programs precision queueBits+factorWorkPolynomial .leg order programs precision queueBits)









end
end CurrentAFT.BinaryBackgroundPopulation

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryBackgroundPopulation.factorWorkPolynomial
  pure ()

end

section






















/-! # Actual counts for full-response choices and root ordinals -/
namespace CurrentAFT.BinaryFullResponseCounts
open AFT RationalNumerics BinaryArithmetic
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryProposalMetadata.counts differenceCounter doubleCounter

structure Counts where
  leg : ℕ
  ordinary : ℕ
  queue : ℕ
  body : ℕ
  work : ℕ

def current (security : ℕ) : Counts :=
  let sizes := BinaryProposalMetadata.counts security
  let noQueue := differenceCounter sizes.population sizes.colors
  let doubled := doubleCounter sizes.legs
  let ordinary := differenceCounter noQueue.count doubled.count
  ⟨sizes.legs,ordinary.count,sizes.colors,sizes.population,
    sizes.work+noQueue.work+doubled.work+ordinary.work+4⟩

theorem current_value (security : ℕ) :
    (current security).leg=Parameters.legCount security ∧
    (current security).ordinary=BackgroundRates.ordinaryPool security ∧
    (current security).queue=Parameters.modulus security ∧
    (current security).body=Parameters.bodySize security := by
  rcases BinaryProposalMetadata.counts_value security with ⟨hq,hl,hp⟩
  simp only [current,differenceCounter_value,doubleCounter_value,hq,hl,hp,BackgroundRates.ordinaryPool,
    Parameters.legCount_eq,Parameters.bodySize_eq,Parameters.base,and_self]



theorem body_decomposition (security : ℕ) :
    (current security).leg+((current security).leg+(current security).ordinary)+(current security).queue=(current security).body := by
  rcases current_value security with ⟨hl,ho,hq,hb⟩
  rw [hl,ho,hq,hb]
  have hroom := ProposalPrimary.population_room security
  unfold BackgroundRates.ordinaryPool
  omega

theorem positive (security : ℕ) :
    0<(current security).leg ∧ 0<(current security).ordinary ∧ 0<(current security).queue ∧ 0<(current security).body := by
  rcases current_value security with ⟨hl,ho,hq,hb⟩
  rw [hl,ho,hq,hb]
  have hp : 0<Parameters.legCount security := by rw [Parameters.legCount_eq]; exact pow_pos (Parameters.base_pos security) _
  have ho := BackgroundRates.ordinaryPool_pos security
  have hq := (Parameters.modulus_spec security).2.pos
  have hroom := ProposalPrimary.population_room security
  exact ⟨hp,ho,hq,by omega⟩

noncomputable def workPolynomial : Polynomial ℕ := BinaryProposalMetadata.countsWorkPolynomial+7*BinaryProposalMetadata.sizePolynomial+7



end CurrentAFT.BinaryFullResponseCounts

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryFullResponseCounts.workPolynomial
  pure ()

end

section


























/-! # Executed distinct ordered selections and their exact normalizer -/
namespace CurrentAFT.BinaryDistinctTuples
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lessCounter

def pairCheck (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) (first second : Fin count) : CountedValue Bool :=
  let ordered := lessCounter first.val second.val
  let left := readVector ⟨0, hp⟩ word first
  let right := readVector ⟨0, hp⟩ word second
  let forward := lessCounter left.value.val right.value.val
  let backward := lessCounter right.value.val left.value.val
  ⟨if ordered.value then forward.value || backward.value else true,
    ordered.work+left.work+right.work+forward.work+backward.work+4⟩



def current (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) : CountedValue Bool :=
  BinaryProposalGuard.allFin count (fun first =>
    BinaryProposalGuard.allFin count (fun second => pairCheck pool count hp word first second))



def pairWork (pool count : ℕ) : ℕ := 12*count+12*pool+20
def work (pool count : ℕ) : ℕ := count*(count*(pairWork pool count+2)+3)+1





def guarded (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → RationalResult)
    (word : Vector (Fin pool) count) : RationalResult :=
  let check := current pool count hp word
  let result := kernel word
  ⟨if check.value then result.data else zero, check.work+result.work+2⟩



def sum (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → RationalResult) : RationalResult :=
  BinaryTupleSum.current pool count (guarded pool count hp kernel)

def normalizer (pool count : ℕ) (hp : 0 < pool) : RationalResult :=
  sum pool count hp (fun _ => ⟨one, 1⟩)


noncomputable section
open scoped Classical








end
end CurrentAFT.BinaryDistinctTuples

end

end


