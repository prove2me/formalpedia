-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_10_Part_2
-- name    : InfoLossLAR_NativeBundle_10_Part_2
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T19:08:45.144646+00:00
-- url     : https://prove2.me/theorems/6d012dc5-4f94-4cc7-aa32-23fc1ff515fc
-- title:
--   Rational and binary physical-weight programs
-- statement:
--   This package defines the rational physical-weight program, its local and blockwise binary implementations, the complete binary weight evaluator, and the resource polynomials used in subsequent running-time proofs. It imports the earlier paired-response and weight-coordinate interfaces and adds no assumed approximation or lattice-reduction theorem.
-- source:
--   Unchanged scope-closed source modules from local proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, regrouped into a smaller semantic compilation unit after two terminal platform timeouts. All original source-body hashes are preserved; all 11528 public native/runtime types and recursive standard-axiom audits pass. Source SHA256 3f20f40c56cd30ab5f12c8c9909bc9fa19b64963af4b3b1bbee3f8f8cd74aff9. Compiler-only optimization: one local scope marks Polynomial addition and multiplication instances irreducible while generating native equation lemmas. Every original definition and proof source body is unchanged; all11528 public types and recursive standard-axiom audits pass. New sourceSHA256 fa3fa94739476404e6d286be0d379ef6d0d727e4fe8baa0681aa6ff655de5108.

import Definitions.Def_InfoLossLAR_NativeBundle_10_Part_2_Stage_3

section
attribute [local irreducible] Polynomial.instAdd Polynomial.instMul

section






















/-! # Finite rational evaluation of the current public weight

The array contains every joint kernel entry. The recursion applies the
computed paired operator to each primary slot, then averages distinct
choices in the two pools. All arithmetic in the program is rational.
-/
namespace CurrentAFT.RationalWeightProgram
open AFT ActualControls ControlCoordinates GradedControlAlgebra CalibrationPointCoordinates
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

abbrev RawTable (order : ℕ) := (arity : TruncatedArity order) →
  (Fin arity.val.1.val → ℕ) → (Fin arity.val.2.val → ℕ) → ℚ

def pairedTensor (security bits : ℕ) : (count : ℕ) → ((Fin count → ℕ) → ℚ) →
    (Fin count → ℕ × ℕ) → ℚ
  | 0, kernel, _ => kernel Fin.elim0
  | count + 1, kernel, groups =>
      RationalPairedLiftProgram.current security bits
        (fun color => pairedTensor security bits count (fun rest => kernel (Fin.cons color rest))
          (fun index => groups index.succ)) (groups 0).1 (groups 0).2

def average (r s primaryPool bodyPool : ℕ)
    (kernel : (Fin r → ℕ × ℕ) → (Fin s → ℕ) → ℚ)
    (groups : Fin primaryPool → ℕ × ℕ) (centers : Fin bodyPool → ℕ) : ℚ :=
  letI := CyclePatternProgram.selectionFintype primaryPool r
  letI := CyclePatternProgram.selectionFintype bodyPool s
  (∑ selection : (Fin r ↪ Fin primaryPool) × (Fin s ↪ Fin bodyPool),
    kernel (groups ∘ selection.1) (centers ∘ selection.2)) /
      ((primaryPool.descFactorial r : ℚ) * (bodyPool.descFactorial s : ℚ))

def current (security bits order primaryPool bodyPool : ℕ) (table : RawTable order)
    (groups : Fin primaryPool → ℕ × ℕ) (centers : Fin bodyPool → ℕ) : ℚ :=
  table (zeroArity order) Fin.elim0 Fin.elim0 +
    ∑ arity : PositiveArity order,
      average arity.val.1.val arity.val.2.val primaryPool bodyPool
        (fun selected selectedCenters => pairedTensor security bits arity.val.1.val
          (fun colors => table (positiveArity order arity) colors selectedCenters) selected) groups centers

noncomputable section
open scoped Classical
local instance weightFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def realTable (security order : ℕ) (table : RawTable order) :
    PointTable (ActualControls.Palette security) (SafePalette security) order :=
  fun point => table point.1 (fun index => (point.2.1 index).val) (fun index => (point.2.2 index).val.val)

def groupValues (security : ℕ) (group : SafeControlGroups.SafeGroup security) : ℕ × ℕ :=
  (group.1.val, group.2.val.val)









end
end CurrentAFT.RationalWeightProgram

end

section





























/-! # Joint-table readers and the actual cached primary tensor -/
namespace CurrentAFT.BinaryWeightLocal
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

abbrev colors (security : ℕ) := (PublicParameterProgram.modulus security).count

theorem colors_pos (security : ℕ) : 0 < colors security := by
  change 0 < (PublicParameterProgram.modulus security).count
  rw [PublicParameterProgram.modulus_value]
  exact (Parameters.modulus_spec security).2.pos

def gather {Value : Type*} {pool count : ℕ} (fallback : Value) (hp : 0 < pool)
    (values : Vector Value pool) (sites : Vector (Fin pool) count) : CountedValue (Vector Value count) :=
  let computed := Vector.ofFn (fun slot : Fin count =>
    let index := readVector ⟨0, hp⟩ sites slot
    let value := readVector fallback values index.value
    (⟨value.value, index.work+value.work+2⟩ : CountedValue Value))
  ⟨computed.map (fun result => result.value), (∑ slot, (computed.get slot).work)+2*count+2⟩



def gatherWork (pool count : ℕ) : ℕ := count*(3*count+3*pool+10)+2



def rawTable (security order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order) : RationalWeightProgram.RawTable order :=
  fun arity primary body =>
    if h : (∀ index, primary index < colors security) ∧ (∀ index, body index < colors security) then
      ((table.get (WeightCoordinates.arityIndex order arity.val.1 arity.val.2)).get
        ⟨WeightCoordinates.jointCode (colors security) arity.val.1.val arity.val.2.val primary body,
          WeightCoordinates.jointCode_lt_capacity _ _ _ _
            (colors_pos security)
            arity.property primary body h.1 h.2⟩).decode
    else 0







def current (security _bits order : ℕ) (references : BinaryReferenceTables.Result security)
    (table : BinaryWeightCoordinates.Table (colors security) order) (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) arity.val.1.val)
    (centers : Vector (Fin (colors security)) arity.val.2.val) : RationalResult :=
  BinaryPairedTensor.current references.primary references.center references.anchor references.activation
    (⟨0, colors_pos security⟩,
     ⟨0, colors_pos security⟩)
    arity.val.1.val (fun primary => BinaryWeightCoordinates.read (colors security) order arity.val.1.val arity.val.2.val
      (colors_pos security)
      arity.property table primary centers) groups





end CurrentAFT.BinaryWeightLocal

end

section



























/-! # The full two-pool physical weight contribution of one joint block -/
namespace CurrentAFT.BinaryWeightBlock
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra
open BinaryWeightLocal
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryWeightLocal.current BinaryTwoPoolAverage.current BinaryReferenceTables.current

def selected (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (references : BinaryReferenceTables.Result security) (table : BinaryWeightCoordinates.Table (colors security) order)
    (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool)
    (first : Vector (Fin primaryPool) arity.val.1.val) (second : Vector (Fin bodyPool) arity.val.2.val) : RationalResult :=
  let gs := gather (⟨0, colors_pos security⟩, ⟨0, colors_pos security⟩) hp groups first
  let bs := gather ⟨0, colors_pos security⟩ hb centers second
  let result := BinaryWeightLocal.current security bits order references table arity gs.value bs.value
  ⟨result.data, gs.work+bs.work+result.work+3⟩

def current (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (references : BinaryReferenceTables.Result security) (table : BinaryWeightCoordinates.Table (colors security) order)
    (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) : RationalResult :=
  BinaryTwoPoolAverage.current primaryPool bodyPool arity.val.1.val arity.val.2.val hp hb
    (selected security bits order primaryPool bodyPool hp hb references table arity groups centers)

def localHeight (security referenceHeight tableHeight r : ℕ) : ℕ := BinaryPairedTensor.height (colors security) referenceHeight r tableHeight

def localWork (security order primaryPool bodyPool referenceHeight tableHeight r s : ℕ) : ℕ :=
  gatherWork primaryPool r+gatherWork bodyPool s+
    BinaryPairedTensor.work (colors security) referenceHeight r tableHeight
      (BinaryWeightCoordinates.readWork (colors security) order r s)+3

def height (security primaryPool bodyPool referenceHeight tableHeight r s : ℕ) : ℕ :=
  BinaryTwoPoolAverage.height primaryPool bodyPool r s (localHeight security referenceHeight tableHeight r)

def work (security order primaryPool bodyPool referenceHeight tableHeight r s : ℕ) : ℕ :=
  BinaryTwoPoolAverage.work primaryPool bodyPool r s (localHeight security referenceHeight tableHeight r)
    (localWork security order primaryPool bodyPool referenceHeight tableHeight r s)

noncomputable section
open scoped Classical







end
end CurrentAFT.BinaryWeightBlock

end

section



























/-! # The complete current binary physical-weight evaluator

The full joint table is supplied by the matrix iteration.  References,
primary tensor contraction, both distinct-pool averages and all arities are
executed, with no unit-cost joint-kernel oracle.
-/
namespace CurrentAFT.BinaryWeightProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra ControlCoordinates
open BinaryWeightLocal
open scoped BigOperators
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter lessCounter PublicParameterProgram.modulus BinaryWeightBlock.current BinaryReferenceTables.current BinaryWeightBlock.height BinaryWeightBlock.work

def term (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (references : BinaryReferenceTables.Result security) (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) (r s : Fin (order+1)) : RationalResult :=
  let degree := addCounter r.val s.val
  let allowed := lessCounter degree.count (order+1)
  let result := if h : allowed.value = true then
    BinaryWeightBlock.current security bits order primaryPool bodyPool hp hb references table
      ⟨(r, s), by change r.val+s.val ≤ order; have hd := (lessCounter_value _ _).mp h; rw [addCounter_value] at hd; omega⟩ groups centers
    else ⟨zero, 1⟩
  ⟨result.data, degree.work+allowed.work+result.work+3⟩

def current (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) : RationalResult :=
  let references := BinaryReferenceTables.current security bits
  let result := sumFin (order+1) (fun r => sumFin (order+1) (term security bits order primaryPool bodyPool hp hb references table groups centers r))
  ⟨result.data, references.work+result.work+2⟩

noncomputable section
open scoped Classical

def idealBlock (security bits order primaryPool bodyPool : ℕ)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) (arity : TruncatedArity order) : ℚ :=
  RationalWeightProgram.average arity.val.1.val arity.val.2.val primaryPool bodyPool
    (fun selected selectedCenters => RationalWeightProgram.pairedTensor security bits arity.val.1.val
      (fun primary => rawTable security order table arity primary selectedCenters) selected)
    (fun index => ((groups.get index).1.val, (groups.get index).2.val)) (fun index => (centers.get index).val)









def blockHeightSum (security order primaryPool bodyPool referenceHeight tableHeight : ℕ) : ℕ :=
  ∑ arity : TruncatedArity order,
    BinaryWeightBlock.height security primaryPool bodyPool referenceHeight tableHeight arity.val.1.val arity.val.2.val

def blockWorkSum (security order primaryPool bodyPool referenceHeight tableHeight : ℕ) : ℕ :=
  ∑ arity : TruncatedArity order,
    BinaryWeightBlock.work security order primaryPool bodyPool referenceHeight tableHeight arity.val.1.val arity.val.2.val

def termWork (security order primaryPool bodyPool referenceHeight tableHeight : ℕ) : ℕ :=
  blockWorkSum security order primaryPool bodyPool referenceHeight tableHeight+5*order+11

def outputHeight (security order primaryPool bodyPool referenceHeight tableHeight : ℕ) : ℕ :=
  let inner := (order+1)*(blockHeightSum security order primaryPool bodyPool referenceHeight tableHeight+1)
  (order+1)*(inner+1)

def evaluationWork (security order primaryPool bodyPool referenceHeight tableHeight : ℕ) : ℕ :=
  let H := blockHeightSum security order primaryPool bodyPool referenceHeight tableHeight
  let K := termWork security order primaryPool bodyPool referenceHeight tableHeight
  let innerH := (order+1)*(H+1)
  let innerW := (order+1)*(K+primitiveWorkBound ((order+2)*(H+1))+2)+2
  (order+1)*(innerW+primitiveWorkBound ((order+2)*(innerH+1))+2)+2





end
end CurrentAFT.BinaryWeightProgram

end

section

























/-! # Fixed-order polynomial bit work of the complete binary weight -/
namespace CurrentAFT.BinaryWeightResources
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits GradedControlAlgebra
open BinaryWeightLocal
open scoped BigOperators
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryWeightProgram.current



















noncomputable def distinctWorkPolynomial (pool : Polynomial ℕ) (count : ℕ) : Polynomial ℕ :=
  Polynomial.C count*(Polynomial.C count*(12*Polynomial.C count+12*pool+20+2)+3)+1
noncomputable def normalizerHeightPolynomial (pool : Polynomial ℕ) (count : ℕ) : Polynomial ℕ :=
  BinaryTupleSum.heightPolynomial pool count 0
noncomputable def normalizerWorkPolynomial (pool : Polynomial ℕ) (count : ℕ) : Polynomial ℕ :=
  BinaryTupleSum.workPolynomial pool count 0 (distinctWorkPolynomial pool count+3)
noncomputable def averageHeightPolynomial (primary body : Polynomial ℕ) (r s : ℕ) (leafHeight : Polynomial ℕ) : Polynomial ℕ :=
  BinaryTupleSum.heightPolynomial primary r (BinaryTupleSum.heightPolynomial body s leafHeight)+
    normalizerHeightPolynomial primary r+normalizerHeightPolynomial body s
noncomputable def averageWorkPolynomial (primary body : Polynomial ℕ) (r s : ℕ) (leafHeight leafWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryTupleSum.workPolynomial primary r (BinaryTupleSum.heightPolynomial body s leafHeight)
    (distinctWorkPolynomial primary r+BinaryTupleSum.workPolynomial body s leafHeight (distinctWorkPolynomial body s+leafWork+2)+2)+
    normalizerWorkPolynomial primary r+normalizerWorkPolynomial body s+
    primitiveWorkPolynomial (normalizerHeightPolynomial primary r+normalizerHeightPolynomial body s)+
    2*primitiveWorkPolynomial (averageHeightPolynomial primary body r s leafHeight)+7







noncomputable def gatherWorkPolynomial (pool : Polynomial ℕ) (count : ℕ) : Polynomial ℕ :=
  Polynomial.C count*(3*Polynomial.C count+3*pool+10)+2
noncomputable def blockHeightPolynomial (colors primary body referenceHeight tableHeight : Polynomial ℕ) (r s : ℕ) : Polynomial ℕ :=
  averageHeightPolynomial primary body r s (BinaryPairedTensor.heightPolynomial colors referenceHeight r tableHeight)
noncomputable def blockWorkPolynomial (colors primary body referenceHeight tableHeight : Polynomial ℕ) (order r s : ℕ) : Polynomial ℕ :=
  averageWorkPolynomial primary body r s (BinaryPairedTensor.heightPolynomial colors referenceHeight r tableHeight)
    (gatherWorkPolynomial primary r+gatherWorkPolynomial body s+
      BinaryPairedTensor.workPolynomial colors referenceHeight r tableHeight
        (BinaryWeightCoordinates.readWorkPolynomial colors order r s)+3)

noncomputable def blockHeightSumPolynomial (colors primary body referenceHeight tableHeight : Polynomial ℕ) (order : ℕ) : Polynomial ℕ :=
  ∑ arity : TruncatedArity order, blockHeightPolynomial colors primary body referenceHeight tableHeight arity.val.1.val arity.val.2.val
noncomputable def blockWorkSumPolynomial (colors primary body referenceHeight tableHeight : Polynomial ℕ) (order : ℕ) : Polynomial ℕ :=
  ∑ arity : TruncatedArity order, blockWorkPolynomial colors primary body referenceHeight tableHeight order arity.val.1.val arity.val.2.val





noncomputable def outputHeightPolynomial (colors primary body precision tableHeight : Polynomial ℕ) (order : ℕ) : Polynomial ℕ :=
  let H := blockHeightSumPolynomial colors primary body (BinaryReferenceTables.heightPolynomial precision) tableHeight order
  Polynomial.C (order+1)*(Polynomial.C (order+1)*(H+1)+1)

noncomputable def evaluationWorkPolynomial (colors primary body precision tableHeight : Polynomial ℕ) (order : ℕ) : Polynomial ℕ :=
  let H := blockHeightSumPolynomial colors primary body (BinaryReferenceTables.heightPolynomial precision) tableHeight order
  let K := blockWorkSumPolynomial colors primary body (BinaryReferenceTables.heightPolynomial precision) tableHeight order+Polynomial.C (5*order+11)
  let innerH := Polynomial.C (order+1)*(H+1)
  let innerW := Polynomial.C (order+1)*(K+primitiveWorkPolynomial (Polynomial.C (order+2)*(H+1))+2)+2
  Polynomial.C (order+1)*(innerW+primitiveWorkPolynomial (Polynomial.C (order+2)*(innerH+1))+2)+2

noncomputable def currentWorkPolynomial (colors primary body precision tableHeight : Polynomial ℕ) (order : ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+evaluationWorkPolynomial colors primary body precision tableHeight order+2





theorem primaryPool_pos (security : ℕ) : 0 < Parameters.legCount security := by
  rw [Parameters.legCount_eq]
  exact pow_pos (Parameters.base_pos security) 128



end CurrentAFT.BinaryWeightResources

-- Realize native equation theorems before export, using declaration-time options.
run_meta do
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.averageHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.averageWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.blockHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.blockHeightSumPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.blockWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.blockWorkSumPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.currentWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.distinctWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.evaluationWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.gatherWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.normalizerHeightPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.normalizerWorkPolynomial
  let _ ← Lean.Meta.getEqnsFor? `CurrentAFT.BinaryWeightResources.outputHeightPolynomial
  pure ()

end

end


