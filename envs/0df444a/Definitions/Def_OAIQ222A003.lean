-- Prove2me | Definitions.Def_OAIQ222A003
-- name    : OAIQ222A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:05:57.484065+00:00
-- url     : https://prove2.me/theorems/3f7801f2-990c-41dc-932b-a449bf7b969b
-- title:
--   Definitions bundle OAIQ222A003 of the split of OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 253 declarations of OpenAI's Lean: 185 definitions, 1 inductive type or structure, 1 instance and 66 theorems. The definitions and types are `OAI.ExactQuantumFactoring.BitArithmetic.bequiv`, `OAI.ExactQuantumFactoring.BitArithmetic.cfHead`, `OAI.ExactQuantumFactoring.BitArithmetic.cfP`, `OAI.ExactQuantumFactoring.BitArithmetic.cfQ`, `OAI.ExactQuantumFactoring.BitArithmetic.cfTail`, `OAI.ExactQuantumFactoring.BitArithmetic.liftInput`, `OAI.ExactQuantumFactoring.BitArithmetic.resizeWord`, `OAI.ExactQuantumFactoring.BitArithmetic.rootGuess`, `OAI.ExactQuantumFactoring.BitArithmetic.rootModulus`, `OAI.ExactQuantumFactoring.BitStackProgram.Emits`, `OAI.ExactQuantumFactoring.BitStackProgram.Emits.recursionCode`, `OAI.ExactQuantumFactoring.BitStackProgram.Node`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.append`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryDiv`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryDivMod`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryGcd`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryMod`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryMul`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryPow`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.boolListAll`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.boolXor`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.boundedUnary`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.chooseBitD`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.clippedUnary`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.divStepP`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.divideRawP`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.dropWord`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.gcdStepP`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.intAbs`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.intAdd`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.intMul`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.intNeg`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.intPow`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.intSign`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.intToRat`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.listFlatten`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.listJoinWords`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.listMapIdxWith`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.makeRat`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.mulFoldP` and 146 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `QuantumFactoring_AdaptivePrepared`, `QuantumFactoring_BitStackBooleans`, `QuantumFactoring_BitStackBoundedPrime`, `QuantumFactoring_BitStackBoundedUnary`, `QuantumFactoring_BitStackDependentChoice`, `QuantumFactoring_BitStackDivision`, `QuantumFactoring_BitStackGCD`, `QuantumFactoring_BitStackIntegers`, `QuantumFactoring_BitStackListFlatten`, `QuantumFactoring_BitStackListMapIdx`, `QuantumFactoring_BitStackListWords`, `QuantumFactoring_BitStackMultiplier`, `QuantumFactoring_BitStackPowers`, `QuantumFactoring_BitStackProcedures`, `QuantumFactoring_BitStackPrograms`, `QuantumFactoring_BitStackRationalDivision`, `QuantumFactoring_BitStackRationalFloor`, `QuantumFactoring_BitStackRationalPower`, `QuantumFactoring_BitStackRationals`, `QuantumFactoring_BitStackSumInjection`, `QuantumFactoring_BitStackTestBit`, `QuantumFactoring_BitStackWords`, `QuantumFactoring_BooleanAlgebra`, `QuantumFactoring_BooleanCircuit`, `QuantumFactoring_BooleanNetwork`, `QuantumFactoring_BooleanOracle`, `QuantumFactoring_BooleanProgram`, `QuantumFactoring_CircuitBooleanEmission`, `QuantumFactoring_CircuitEmissionEncoding`, `QuantumFactoring_CircuitEmissionModel`, `QuantumFactoring_CircuitFinalEmission`, `QuantumFactoring_CircuitPreparationEmission`, `QuantumFactoring_CircuitProgramEmission`, `QuantumFactoring_CircuitSemantics`, `QuantumFactoring_CleanPermutation`, `QuantumFactoring_CleanPermutationEmission`, `QuantumFactoring_CoherentSampling`, `QuantumFactoring_ContinuedFractionCircuit`, `QuantumFactoring_ControlledTranslation`, `QuantumFactoring_CoveringPowerEmission`, `QuantumFactoring_DescendingFilter`, `QuantumFactoring_DescendingFilterEmission`, `QuantumFactoring_EmissionBoundedRecursion`, `QuantumFactoring_EmissionCombinators`, `QuantumFactoring_EmissionLists`, `QuantumFactoring_ExpressionPostfix`, `QuantumFactoring_ExpressionPowerEmission`, `QuantumFactoring_ExpressionSyntaxEmission`, `QuantumFactoring_ExpressionTemplateEmission`, `QuantumFactoring_ExpressionTokenProcedure`, `QuantumFactoring_ListSamplerEmission`, `QuantumFactoring_NativeAIGModel`, `QuantumFactoring_NativeAIGVector`, `QuantumFactoring_NetworkCanonicalEmission`, `QuantumFactoring_NetworkEmissionBasic`, `QuantumFactoring_NetworkEmissionBounds`, `QuantumFactoring_NetworkEmissionCombinators`, `QuantumFactoring_NetworkEmissionModel`, `QuantumFactoring_NetworkEmissionPack`, `QuantumFactoring_NetworkLoopEmission`, `QuantumFactoring_NetworkPolyResources`, `QuantumFactoring_NetworkPredicateEmission`, `QuantumFactoring_NetworkStackCompiler`, `QuantumFactoring_OracleLayout`, `QuantumFactoring_OracleReadOnly`, `QuantumFactoring_OrderSampleCircuit`, `QuantumFactoring_PhaseOracle`, `QuantumFactoring_PhysicalAmplification`, `QuantumFactoring_PolynomialTemplateEmission`, `QuantumFactoring_PreparedOracle`, `QuantumFactoring_ProcedureFurther`, `QuantumFactoring_RegisterBasis`, `QuantumFactoring_RegisterCircuit`, `QuantumFactoring_RetrospectiveCircuit`, `QuantumFactoring_RootCircuit`, `QuantumFactoring_RowNetwork`, `QuantumFactoring_SignedSyntaxEmission`, `QuantumFactoring_TreeTableEmission`, `QuantumFactoring_TwoAdicCircuit`, `QuantumFactoring_WordResize`.
--
--   **Imports.** It imports the published bundle `Def_ExactQuantumFactoring`; the bundles `OAIQ222A000` and `OAIQ222A001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ222A004`.
-- source:
--   OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 279; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_ExactQuantumFactoring
import Definitions.Def_OAIQ222A000
import Definitions.Def_OAIQ222A001

section
-- module Solutions.OAIQ222_QF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitSemantics
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

/-- Reindex a full computational basis by the gate wires and all other wires.
This is only a proof equivalence; it introduces no new gate in the model. -/
noncomputable def Instruction.splitBasis {q : ℕ} (o : Instruction q) :
    Basis q ≃ Basis o.gate.arity × (o.Unused → Bool) := by
  classical
  refine {
    toFun := fun x => (x ∘ o.wire, fun i => x i.val)
    invFun := fun x i => if h : ∃ j, o.wire j = i then x.1 h.choose
      else x.2 ⟨i, by simpa only [not_exists] using h⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    funext i
    dsimp
    split_ifs with h
    · simp only [h.choose_spec]
    · rfl
  · intro x
    apply Prod.ext
    · funext j
      dsimp
      have h : ∃ j', o.wire j' = o.wire j := ⟨j, rfl⟩
      rw [dite_eq_left h]
      exact congrArg x.1 (o.distinct h.choose_spec)
    · funext i
      dsimp
      rw [dite_eq_right (by simpa only [not_exists] using i.property)]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.Instruction.target_place _root_.OAI.ExactQuantumFactoring.Instruction.target_reverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

/-- Lift a local classical reversible gate to the actual wires; this is not an
additional circuit instruction, just its classical semantics. -/
noncomputable def Instruction.liftPerm {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity)) : Equiv.Perm (Basis q) :=
  (o.splitBasis.trans (Equiv.prodCongr e (Equiv.refl _))).trans o.splitBasis.symm

abbrev toffoliAt {q : ℕ} (a b t : Fin q) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    Instruction q :=
  ⟨plainGate .toffoli, ![a,b,t], by
    change Function.Injective (![a,b,t] : Fin 3 → Fin q)
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all⟩

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators

namespace BooleanOp

def compile {q : ℕ} {t : Fin q} : BooleanOp q t → List (Instruction q)
  | .constant false => []
  | .constant true => [notAt t]
  | .copy a ha => [cnotAt a t ha]
  | .neg a ha => [cnotAt a t ha, notAt t]
  | .conj a b ha hb => if h : a = b then [cnotAt a t ha]
      else [toffoliAt a b t h ha hb]

end BooleanOp

def BooleanProgram.compile {q : ℕ} (p : BooleanProgram q) : List (Instruction q) :=
  p.flatMap (fun o => o.2.compile)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RegisterCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.Instruction.target_place
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

namespace Register

noncomputable def split {p q : ℕ} (w : Register p q) :
    Basis q ≃ Basis p × (w.Unused → Bool) := by
  classical
  exact {
    toFun := fun x => (x ∘ w, fun i => x i.val)
    invFun := fun x i => if h : ∃ j, w j = i then x.1 h.choose
      else x.2 ⟨i, by simpa only [not_exists] using h⟩
    left_inv := by
      intro x; funext i; dsimp
      split_ifs with h
      · simp only [h.choose_spec]
      · rfl
    right_inv := by
      intro x; apply Prod.ext
      · funext j; dsimp
        have h : ∃ j', w j' = w j := ⟨j,rfl⟩
        rw [dite_eq_left h]
        exact congrArg x.1 (w.injective h.choose_spec)
      · funext i; dsimp
        rw [dite_eq_right (by simpa only [not_exists] using i.property)] }

noncomputable def liftMatrix {p q : ℕ} (w : Register p q)
    (A : Matrix (Basis p) (Basis p) ℂ) : Matrix (Basis q) (Basis q) ℂ :=
  Matrix.reindex w.split.symm w.split.symm
    (A ⊗ₖ (1 : Matrix (w.Unused → Bool) (w.Unused → Bool) ℂ))

end Register

/-- Tensor states in the actual physical wire order. -/
noncomputable def Register.pairState {p q : ℕ} (w : Register p q)
    (v : State p) (z : (w.Unused → Bool) → ℂ) : State q :=
  fun x => v (w.split x).1 * z (w.split x).2

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RegisterBasis
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Replace just one placed register, keeping every other physical wire. -/
noncomputable def Register.replace {p q : ℕ} (w : Register p q) (x : Basis q) (y : Basis p) : Basis q :=
  w.split.symm (y, (w.split x).2)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanNetwork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring

namespace BoolNode

/-- The new wire is distinct from every preexisting wire. -/
def compileOp {n q : ℕ} (h : n + 1 ≤ q) (o : BoolNode n) :
    BooleanOp q ⟨n, by omega⟩ :=
  match o with
  | .constant b => .constant b
  | .copy i => .copy (i.castLE (by omega)) (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)
  | .neg i => .neg (i.castLE (by omega)) (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)
  | .conj i j => .conj (i.castLE (by omega)) (j.castLE (by omega))
      (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)
      (by intro he; have hh := congrArg Fin.val he; simp only [Fin.val_castLE] at hh; omega)

end BoolNode

namespace BoolNet

def program {n k : ℕ} (p : BoolNet n k) {q : ℕ} (h : k ≤ q) : BooleanProgram q :=
  match p with
  | .input => []
  | .add p o => p.program (by omega) ++ [⟨⟨_, by omega⟩, o.compileOp h⟩]

end BoolNet


end ExactQuantumFactoring
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanOracle
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

namespace BooleanNetwork

/-- Actual fixed-gate compute/copy/uncompute, with all trace wires restored. -/
def oracle {n m : ℕ} (c : BooleanNetwork n m) : List (Instruction (c.width+m)) :=
  let p := c.net.program (Nat.le_add_right c.width m)
  p.compile ++ (copyPrefix c.output m le_rfl).compile ++
    p.compile.reverse.map Instruction.reverse

/-- The basis-state whose trace is zero and whose target is toggled by c(x). -/
def oracleOutput {n m : ℕ} (c : BooleanNetwork n m) (x : Basis (c.width+m)) : Basis (c.width+m) :=
  fun i => if h : c.width ≤ i.val then
    Bool.xor (x i) (c.eval (fun j => x (j.castLE (c.net.input_le.trans (Nat.le_add_right _ _))))
      ⟨i.val-c.width, by omega⟩) else x i

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OracleLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

/-- Place the oracle's retained trace after its output rather than between the
input and output. A larger reservoir of work wires is permitted. -/
def oraclePlacement {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r) :
    Register (c.width+m) (n+m+r) where
  toFun i := ⟨oracleIndex n m c.width i.val, by
    have := c.net.width_eq
    have := i.isLt
    unfold oracleIndex
    split_ifs <;> omega⟩
  inj' := by
    intro i j he
    apply Fin.ext
    have hh : oracleIndex n m c.width i.val = oracleIndex n m c.width j.val :=
      congrArg Fin.val he
    unfold oracleIndex at hh
    split_ifs at hh <;> have hi := i.isLt <;> have hj := j.isLt <;>
      have hn := c.net.input_le <;> omega

def oracleOn {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r) :
    List (Instruction (n+m+r)) := c.oracle.map (Instruction.place (oraclePlacement c hr))

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CoherentSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

/-- Retain the modular value register while interfering the exponent register;
no copy of the exponent or hidden measurement is inserted. -/
def sampleProgram {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction n)) : List (Instruction (n+m+r)) :=
  oracleOn c hr ++ firstProgram m r ops

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.BooleanNetwork

/-- Sequentially composed bounded logical updates compile by retained history. -/
def sequence {n : ℕ} : List (BooleanNetwork n n) → BooleanNetwork n n
  | [] => select id
  | c :: cs => c.comp (sequence cs)

def iterate {n : ℕ} (c : BooleanNetwork n n) (k : ℕ) : BooleanNetwork n n :=
  sequence (List.replicate k c)

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CleanPermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

/-- The standard clean implementation of a bijection uses a verified forward
and inverse Boolean network, two work registers, and only the named gates. -/
def cleanPermutation {n r : ℕ} (f g : BooleanNetwork n n)
    (hf : f.net.count ≤ r) (hg : g.net.count ≤ r) : List (Instruction (n+n+r)) :=
  oracleOn f hf ++ swapPrefix n r n le_rfl ++ oracleOn g hg

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ControlledTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

namespace ControlledTranslation

def addInput {p b : ℕ} (δ : BooleanNetwork p b) : BooleanNetwork (p+b) (b+b) :=
  (select (Fin.natAdd p)).pair ((select (fun i => i.castAdd b)).comp δ)

end ControlledTranslation
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RowNetwork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

/-- Combining one triangular row is just a bit permutation and masked ANDs;
no arbitrary phase or exponentially large truth table is present. -/
def rowNetwork {b : ℕ} (j : Fin b) : BooleanNetwork b b :=
  vector (fun e => if j.val ≤ e.val ∧ e.val < b-1 then
    (bit (rowIndex j e)).band (bit j)
    else constant false)

lemma rowNetwork_count {b : ℕ} (j : Fin b) : (rowNetwork j).net.count = b := by
  rw [rowNetwork, count_vector]
  have h : ∀ e : Fin b, (if j.val ≤ e.val ∧ e.val < b-1 then
      (bit (rowIndex j e)).band (bit j)
      else constant false).net.count = 1 := by
    intro e
    by_cases he : j.val ≤ e.val ∧ e.val < b-1
    · rw [ite_eq_left he]; simp
    · rw [ite_eq_right he]; rfl
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSampleCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Actual modular-power/triangular-transform order sampler. All arithmetic
inputs are read-only wires; the modular output remains coherent. -/
namespace ExactQuantumFactoring.OrderSample
open scoped BigOperators
open BooleanNetwork Triangular

def powerInputs (w b : ℕ) : BooleanNetwork (inputWidth w b) ((w+w)+b) :=
  select (Fin.addCases (Fin.castAdd (Triangular.width b))
    (fun i => Fin.natAdd (w+w) (Triangular.dataWire i)))

end ExactQuantumFactoring.OrderSample


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PreparedOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

/-- Prepare a runtime-dependent input with a genuine clean Boolean oracle,
then run the same fixed quantum program on that fresh input. All old bits x
survive, and c is a network, not a large table of counterfactual outputs. -/
def preparedOracle {n m r : ℕ} (c : BooleanNetwork n m) (hr : c.net.count ≤ r)
    (ops : List (Instruction m)) : List (Instruction (n+m+r)) :=
  oracleOn c hr++targetProgram n r ops

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AdaptivePrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

def appendPrepared {p q r : ℕ} (A : List (Instruction p)) (c : BooleanNetwork p q)
    (hc : c.net.count ≤ r) (ops : List (Instruction q)) : List (Instruction (p+q+r)) :=
  firstProgram q r A++preparedOracle c hc ops

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

/-! A literal finite Boolean-stack compiler for circuit descriptions.
Branches inspect and consume one symbol, not an entire encoded word.
Operational derivations below count actual finite-state TM2 transitions.
-/
namespace ExactQuantumFactoring.BitStackProgram
open Turing.TM2 StateTransition

def Node {K : Type} : Program K → Type
  | .skip | .push _ _ => Unit
  | .seq p q => Node p ⊕ Node q
  | .cases _ a b c => Unit ⊕ (Node a ⊕ (Node b ⊕ Node c))
  | .loop _ b c => Unit ⊕ (Node b ⊕ Node c)

noncomputable instance nodeFintype {K : Type} (p : Program K) : Fintype (Node p) := by
  induction p with
  | skip => exact inferInstanceAs (Fintype Unit)
  | push => exact inferInstanceAs (Fintype Unit)
  | seq p q hp hq => letI := hp; letI := hq; exact inferInstanceAs (Fintype (Node p ⊕ Node q))
  | cases k a b c ha hb hc =>
    letI := ha; letI := hb; letI := hc
    exact inferInstanceAs (Fintype (Unit ⊕ (Node a ⊕ (Node b ⊕ Node c))))
  | loop k b c hb hc =>
    letI := hb; letI := hc
    exact inferInstanceAs (Fintype (Unit ⊕ (Node b ⊕ Node c)))

def entry {K : Type} : (p : Program K) → Node p
  | .skip | .push _ _ => ()
  | .seq p _ => .inl (entry p)
  | .cases _ _ _ _ | .loop _ _ _ => .inl ()

def configured {K Λ : Type} (l : Λ) (s : Store K) : Config K Λ := ⟨some l,none,s⟩

def statement {K Λ : Type} : (p : Program K) → Λ → (Node p → Λ) → Node p →
    Stmt (fun _ : K => Bool) Λ (Option Bool)
  | .skip,e,_,_ => jump e
  | .push k b,e,_,_ => .push k (fun _ => b) (jump e)
  | .seq p q,_e,w,.inl i => statement p (w (.inr (entry q))) (w ∘ Sum.inl) i
  | .seq _ q,e,w,.inr i => statement q e (w ∘ Sum.inr) i
  | .cases k a b c,_,w,.inl _ => dispatch k
      (w (.inr (.inl (entry a)))) (w (.inr (.inr (.inl (entry b)))))
      (w (.inr (.inr (.inr (entry c)))))
  | .cases _ a _ _,e,w,.inr (.inl i) => statement a e (w ∘ Sum.inr ∘ Sum.inl) i
  | .cases _ _ b _,e,w,.inr (.inr (.inl i)) =>
      statement b e (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inl) i
  | .cases _ _ _ c,e,w,.inr (.inr (.inr i)) =>
      statement c e (w ∘ Sum.inr ∘ Sum.inr ∘ Sum.inr) i
  | .loop k b c,e,w,.inl _ => dispatch k e
      (w (.inr (.inl (entry b)))) (w (.inr (.inr (entry c))))
  | .loop _ b _,_,w,.inr (.inl i) =>
      statement b (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inl) i
  | .loop _ _ c,_,w,.inr (.inr i) =>
      statement c (w (.inl ())) (w ∘ Sum.inr ∘ Sum.inr) i

lemma dispatch_nil {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (hs : s k=[]) : stepAux (dispatch k a b c) none s = configured a s := by
  simp only [dispatch,stepAux,hs,List.head?_nil,List.tail_nil,Option.isSome_none,
    Bool.cond_false,jump]
  rw [← hs,Function.update_eq_self]
  rfl
lemma dispatch_false {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (xs : List Bool) (hs : s k=false::xs) :
    stepAux (dispatch k a b c) none s = configured b (Function.update s k xs) := by
  simp only [dispatch,stepAux,hs,List.head?_cons,List.tail_cons,Option.isSome_some,
    Bool.cond_true,Option.getD_some,Bool.cond_false,jump]
  rfl
lemma dispatch_true {K Λ : Type} [DecidableEq K] (s : Store K) (k : K) (a b c : Λ)
    (xs : List Bool) (hs : s k=true::xs) :
    stepAux (dispatch k a b c) none s = configured c (Function.update s k xs) := by
  simp only [dispatch,stepAux,hs,List.head?_cons,List.tail_cons,Option.isSome_some,
    Bool.cond_true,Option.getD_some,jump]
  rfl

theorem compile_runs {K : Type} [DecidableEq K] {p : Program K}
    {s t : Store K} {c : ℕ} (h : Runs p s t c) :
    ∀ {Λ : Type} (e : Λ) (w : Node p → Λ)
      (M : Λ → Stmt (fun _ : K => Bool) Λ (Option Bool)),
      (∀ i, M (w i) = statement p e w i) →
      (flip bind (step M))^[c] (some (configured (w (entry p)) s)) = some (configured e t) := by
  induction h with
  | skip s =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w ())) none s) = _
    rw [hM ()]
    rfl
  | push s k b =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w ())) none s) = _
    rw [hM ()]
    rfl
  | @seq p q s t u a b hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (entry q))) t) _ a b
    · exact ihp _ _ M (fun i => hM (.inl i))
    · exact ihq _ _ M (fun i => hM (.inr i))
  | @cases_nil k p q r s t a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inl (entry p)))) s) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_nil _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inl i)))
  | @cases_false k p q r s t xs a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (.inl (entry q)))))
      (Function.update s k xs)) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_false _ _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inr (.inl i))))
  | @cases_true k p q r s t xs a hs hp ih =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (.inr (entry r)))))
      (Function.update s k xs)) _ 1 a
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_true _ _ _ _ _ _ hs]
    · exact ih _ _ M (fun i => hM (.inr (.inr (.inr i))))
  | @loop_nil k p q s hs =>
    intro Λ e w M hM
    apply iterate_step
    change some (stepAux (M (w (.inl ()))) none s) = _
    rw [hM (.inl ()),statement,dispatch_nil _ _ _ _ _ hs]
  | @loop_false k p q s t u xs a b hs hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inl (entry p))))
      (Function.update s k xs)) _ 1 (b+a)
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_false _ _ _ _ _ _ hs]
    · apply iterate_comp (step M) _ (configured (w (.inl ())) t) _ a b
      · exact ihp _ _ M (fun i => hM (.inr (.inl i)))
      · exact ihq _ _ M hM
  | @loop_true k p q s t u xs a b hs hp hq ihp ihq =>
    intro Λ e w M hM
    apply iterate_comp (step M) _ (configured (w (.inr (.inr (entry q))))
      (Function.update s k xs)) _ 1 (b+a)
    · apply iterate_step
      change some (stepAux (M (w (.inl ()))) none s) = _
      rw [hM (.inl ()),statement,dispatch_true _ _ _ _ _ _ hs]
    · apply iterate_comp (step M) _ (configured (w (.inl ())) t) _ a b
      · exact ihp _ _ M (fun i => hM (.inr (.inr i)))
      · exact ihq _ _ M hM

noncomputable def machine {K : Type} [Fintype K] [DecidableEq K] (input output : K) (p : Program K) :
    Turing.FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := Option (Node p)
  main := some (entry p)
  σ := Option Bool
  initialState := none
  m
    | none => .halt
    | some i => statement p none some i

noncomputable def machine_outputs {K : Type} [Fintype K] [DecidableEq K]
    (input output : K) (p : Program K) (s t : List Bool) (c : ℕ)
    (h : Runs p (singletonStore input s) (singletonStore output t) c) :
    Turing.TM2OutputsInTime (machine input output p) s (some t) (c+1) := by
  let tm := machine input output p
  have hi : Turing.initList tm s = configured (some (entry p)) (singletonStore input s) := by
    change Turing.initList (machine input output p) s = _
    unfold machine Turing.initList configured singletonStore
    congr 1
    funext k
    by_cases hk : k=input
    · subst k; simp
    · simp [hk,Function.update]
  have hf : Turing.haltList tm t =
      (⟨none,none,singletonStore output t⟩ : Config K (Option (Node p))) := by
    change Turing.haltList (machine input output p) t = _
    unfold machine Turing.haltList singletonStore
    congr 1
    funext k
    by_cases hk : k=output
    · subst k; simp
    · simp [hk,Function.update]
  have hr := compile_runs h (none : Option (Node p)) some tm.m (fun _ => rfl)
  refine ⟨⟨c+1,?_⟩,le_rfl⟩
  change (flip bind (step tm.m))^[c+1] (some (Turing.initList tm s)) =
    some (Turing.haltList tm t)
  rw [hi,hf]
  have hend : step tm.m (configured (none : Option (Node p)) (singletonStore output t)) =
      some (⟨none,none,singletonStore output t⟩ : Config K (Option (Node p))) := rfl
  rw [Nat.add_comm c 1]
  exact iterate_comp (step tm.m) _ _ _ c 1 hr (iterate_step _ _ _ hend)
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackProcedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]

namespace Procedure
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

noncomputable def toTM2 (p : Procedure ea eb f) : Turing.TM2ComputableInPolyTime ea eb f where
  tm := machine p.input p.output p.program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := p.bound+1
  outputsFun a := by
    classical
    let c := Classical.choose (p.runs a)
    have hc := (Classical.choose_spec (p.runs a)).1
    have hr := (Classical.choose_spec (p.runs a)).2
    have h := machine_outputs p.input p.output p.program (ea a) (eb (f a)) c hr
    have ht : Turing.TM2OutputsInTime (machine p.input p.output p.program)
        (ea a) (some (eb (f a))) (p.bound.eval (ea a).length+1) :=
      ⟨h.1, h.2.trans (Nat.add_le_add_right hc 1)⟩
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Polynomial.eval_add,Polynomial.eval_one]
    congr 1
    · exact List.map_id _
    · congr 1
      exact List.map_id _

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α : Type}

noncomputable def append : Procedure (prodCode (id : List Bool→List Bool) id) id
    (fun x=>x.1++x.2) where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=.seq (unquoteMove 0 1 2 3) (.seq (reverseMove 1 2) (reverseMove 2 0))
  bound:=Polynomial.C 11*Polynomial.X+Polynomial.C 8
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode id id x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 x.2) 1 x.1
    let v : Store (Fin 4):=Function.update (singletonStore 0 x.2) 2 x.1.reverse
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*x.1.length+6):=by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) x.1 x.2 s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext k;fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (reverseMove 1 2) u v (2*x.1.length+1):=by
      have hh:=reverseMove_runs (1 : Fin 4) 2 (by decide) u
      convert hh using 1
      · funext k;fin_cases k <;> simp [u,v,singletonStore,Function.update]
      · simp [u]
    have h3 : Runs (reverseMove 2 0) v (singletonStore 0 (x.1++x.2)) (2*x.1.length+1):=by
      have hh:=reverseMove_runs (2 : Fin 4) 0 (by decide) v
      convert hh using 1
      · funext k;fin_cases k <;> simp [v,singletonStore,Function.update]
      · simp [v]
    refine ⟨(2*x.1.length+1)+(2*x.1.length+1)+(7*x.1.length+6),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length,id_eq]
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackBooleans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {β : Type}

noncomputable def boolXor : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>xor x.1 x.2) := ofBool₂ boolCode xor

end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma bits_length_value (xs : List Bool) : (binaryValue xs).bits.length≤xs.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact binaryValue_lt xs

lemma mul_fold (xs : List Bool) (x : ℕ×ℕ) :
    xs.foldl (bitAction mulZeroStep mulOneStep) x=
      (x.1,x.1*binaryValue xs.reverse+2^xs.length*x.2) := by
  induction xs generalizing x with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    rw [List.foldl_cons,ih]
    simp only [List.reverse_cons,binaryValue_append,List.length_reverse,List.length_cons,
      binaryValue,pow_succ]
    cases b <;> simp [bitAction,mulZeroStep,mulOneStep] <;> ring

namespace Procedure
noncomputable def mulZeroStepP : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) mulZeroStep :=
  ((first Nat.bits Nat.bits).pair (double.comp (second Nat.bits Nat.bits))).congrFun (by intro x;rfl)
noncomputable def mulOneStepP : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) mulOneStep := by
  let first:=first Nat.bits Nat.bits
  let second:=second Nat.bits Nat.bits
  exact (first.pair (binaryAdd.comp ((double.comp second).pair first))).congrFun (by intro x;rfl)

noncomputable def mulFoldP : Procedure (prodCode id (prodCode Nat.bits Nat.bits))
    (prodCode Nat.bits Nat.bits) (fun x=>x.1.foldl (bitAction mulZeroStep mulOneStep) x.2) :=
  foldBits mulZeroStepP mulOneStepP (Polynomial.C 3*Polynomial.X+Polynomial.C 3) (by
    intro xs x i
    rw [mul_fold]
    simp only [prodCode,pairBits_length]
    have hs:=bits_length_add (x.1*binaryValue (xs.take i).reverse) (2^(xs.take i).length*x.2)
    have hm:=bits_length_mul x.1 (binaryValue (xs.take i).reverse)
    have hn:=bits_length_mul (2^(xs.take i).length) x.2
    have hv:=bits_length_value (xs.take i).reverse
    rw [List.length_reverse] at hv
    rw [bits_length_pow2] at hn
    have hl : (xs.take i).length≤xs.length:=by simp only [List.length_take];omega
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega)

noncomputable def binaryMul : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1*x.2) := by
  let first:=first Nat.bits Nat.bits
  let second:=second Nat.bits Nat.bits
  let bits : Procedure Nat.bits (id : List Bool→List Bool) Nat.bits:=
    (identity (id : List Bool→List Bool)).precompose Nat.bits
  let start:=(reverse.comp (bits.comp second)).pair
    (first.pair (constant (prodCode Nat.bits Nat.bits) Nat.bits 0))
  exact ((Procedure.second Nat.bits Nat.bits).comp (mulFoldP.comp start)).congrFun (by
    intro x
    simp [mul_fold,binaryValue_bits])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
abbrev divStateCode := prodCode Nat.bits (prodCode Nat.bits Nat.bits)

lemma divStep_size (b : Bool) (x : DivState) :
    (divStateCode (divStep b x)).length≤(divStateCode x).length+3 := by
  have hq : (2*x.2.1+1).bits.length≤x.2.1.bits.length+1:=doubleOne_bits_length _
  have hq0:=double_bits_length x.2.1
  have hr : (2*x.2.2+b.toNat).bits.length≤x.2.2.bits.length+1:=by
    cases b
    · simpa using double_bits_length x.2.2
    · exact doubleOne_bits_length x.2.2
  have hs : (2*x.2.2+b.toNat-x.1).bits.length≤(2*x.2.2+b.toNat).bits.length:=
    bits_length_mono (Nat.sub_le _ _)
  simp only [divStateCode,divStep,prodCode,pairBits_length]
  split <;> dsimp only <;> omega

lemma div_fold_spec (xs : List Bool) (x : DivState) (hr : x.2.2<x.1) :
    let y:=xs.foldl (bitAction (divStep false) (divStep true)) x
    y.1=x.1 ∧ y.2.2<x.1 ∧
      y.2.1*x.1+y.2.2=binaryValue xs.reverse+2^xs.length*(x.2.1*x.1+x.2.2) := by
  induction xs generalizing x with
  | nil=>simp [binaryValue,hr]
  | cons b bs ih=>
    have he : bitAction (divStep false) (divStep true) x b=divStep b x:=by cases b <;> rfl
    rw [List.foldl_cons,he]
    have H:=divStep_spec b x hr
    have hi:=ih (divStep b x) (by rw [divStep_fst];exact H.1)
    simp only [divStep_fst] at hi
    refine ⟨hi.1,hi.2.1,?_⟩
    rw [hi.2.2,H.2]
    simp only [List.reverse_cons,binaryValue_append,List.length_reverse,List.length_cons,
      binaryValue,pow_succ]
    ring

def divideRaw (x : List Bool×ℕ) : ℕ×ℕ :=
  (x.1.reverse.foldl (bitAction (divStep false) (divStep true)) (x.2,0,0)).2

lemma divideRaw_spec (x : List Bool×ℕ) (hp : 0<x.2) :
    divideRaw x=(binaryValue x.1/x.2,binaryValue x.1%x.2) := by
  have hh:=div_fold_spec x.1.reverse (x.2,0,0) hp
  simp only [List.reverse_reverse,zero_mul,mul_zero,Nat.add_zero] at hh
  have hq : binaryValue x.1/x.2=(divideRaw x).1:=by
    apply Nat.div_eq_of_lt_le <;> dsimp [divideRaw] <;> nlinarith [hh.2.1,hh.2.2]
  have hm:=Nat.mod_add_div (binaryValue x.1) x.2
  rw [hq] at hm
  apply Prod.ext
  · exact hq.symm
  · dsimp [divideRaw] at hm ⊢ <;> nlinarith [hh.2.2]

namespace Procedure
noncomputable def divStepP (b : Bool) : Procedure divStateCode divStateCode (divStep b) := by
  let d:=first Nat.bits (prodCode Nat.bits Nat.bits)
  let qr:=second Nat.bits (prodCode Nat.bits Nat.bits)
  let q:=(first Nat.bits Nat.bits).comp qr
  let r:=(second Nat.bits Nat.bits).comp qr
  let db : Procedure Nat.bits Nat.bits (fun n=>2*n+b.toNat):=by
    cases b
    · exact double.congrFun (by intro n;simp)
    · exact doubleOne
  let t:=db.comp r
  let test:=binaryLe.comp (d.pair t)
  let yes:=d.pair ((doubleOne.comp q).pair (binarySub.comp (t.pair d)))
  let no:=d.pair ((double.comp q).pair t)
  exact (conditional test yes no).congrFun (by intro x;simp only [Function.comp_apply,divStep,decide_eq_true_eq])

noncomputable def divideRawP : Procedure (prodCode (id : List Bool→List Bool) Nat.bits)
    (prodCode Nat.bits Nat.bits) divideRaw := by
  let x:=first (id : List Bool→List Bool) Nat.bits
  let d:=second (id : List Bool→List Bool) Nat.bits
  let zero:=constant (prodCode (id : List Bool→List Bool) Nat.bits) Nat.bits 0
  let start:=(reverse.comp x).pair (d.pair (zero.pair zero))
  let fold:=foldBitsLinear (divStepP false) (divStepP true) 3 (divStep_size false) (divStep_size true)
  exact ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp (fold.comp start)).congrFun (by intro x;rfl)

noncomputable def binaryDivMod : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) (fun x=>(x.1/x.2,x.1%x.2)) := by
  let raw:=(divideRawP.precompose (fun x : ℕ×ℕ=>(x.1.bits,x.2)))
  let test:=binaryZero.comp (second Nat.bits Nat.bits)
  let zerocase:=(constant (prodCode Nat.bits Nat.bits) Nat.bits 0).pair (first Nat.bits Nat.bits)
  exact (conditional test zerocase raw).congrFun (by
    intro x
    change (if decide (x.2=0) then (0,x.1) else divideRaw (x.1.bits,x.2))=(x.1/x.2,x.1%x.2)
    by_cases hz : x.2=0
    · simp [hz]
    · simp only [hz,decide_false,Bool.false_eq_true,ite_false, if_false]
      simpa only [binaryValue_bits] using divideRaw_spec (x.1.bits,x.2) (by omega))

noncomputable def binaryDiv : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1/x.2) := (first Nat.bits Nat.bits).comp binaryDivMod
noncomputable def binaryMod : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1%x.2) := (second Nat.bits Nat.bits).comp binaryDivMod
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackBoundedPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def boolListAll : Procedure (listCode boolCode) boolCode (fun xs=>xs.all id):=by
  let fold:=foldList false boolAnd (Polynomial.C 1) (by intro xs b i;simp only [boolCode,List.length_singleton,Polynomial.eval_C];rfl)
  exact (fold.comp ((identity _).pair (constant _ boolCode true))).congrFun (by intro xs;change xs.foldl (fun b a=>a&&b) true=xs.all id;rw [boolFold_eq];simp)
end Procedure

end ExactQuantumFactoring.BitStackProgram
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackBoundedUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def unaryDecodeStepP : Procedure (prodCode Nat.bits unaryCode) (prodCode Nat.bits unaryCode)
    unaryDecodeStep := by
  let x:=first Nat.bits unaryCode
  let y:=second Nat.bits unaryCode
  let next:=(binarySub.comp (x.pair (Procedure.constant _ Nat.bits 1))).pair (unarySuccessor.comp y)
  exact (conditional (binaryZero.comp x) (identity _) next).congrFun (by
    intro s;unfold unaryDecodeStep;split <;> simp_all)
noncomputable def clippedUnary : Procedure (prodCode unaryCode Nat.bits) unaryCode (fun x=>min x.1 x.2) := by
  let rep:=unaryDecodeStepP.iterate Polynomial.X (by
    intro n s i hi
    rw [unaryDecodeStep_iterate]
    have hbits:=bits_length_mono (Nat.sub_le s.1 i)
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)
  let inp:=(first unaryCode Nat.bits).pair
    ((second unaryCode Nat.bits).pair (Procedure.constant _ unaryCode 0))
  exact ((second Nat.bits unaryCode).comp (rep.comp inp)).congrFun (by
    intro x;dsimp only [Function.comp_def];rw [unaryDecodeStep_iterate];simp)
noncomputable def boundedUnary {α : Type} {ea : α→List Bool} {f B : α→ℕ}
    (p : Procedure ea Nat.bits f) (b : Procedure ea unaryCode B) (h : ∀a,f a ≤ B a) :
    Procedure ea unaryCode f :=
  (clippedUnary.comp (b.pair p)).congrFun (by intro a;exact min_eq_right (h a))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackSumInjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Procedure
noncomputable def sumLeft {α β : Type} (ea : α→List Bool) (eb : β→List Bool) :
    Procedure ea (sumCode ea eb) Sum.inl:=
  (prepend ea [false]).result (by intro a;rfl)
noncomputable def sumRight {α β : Type} (ea : α→List Bool) (eb : β→List Bool) :
    Procedure eb (sumCode ea eb) Sum.inr:=
  (prepend eb [true]).result (by intro a;rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std Sat

def eraseDecl {n : ℕ} : AIG.Decl (Fin n) → Decl
  | .false => .zero
  | .atom i => .atom i.val
  | .gate a b => .gate (a.gate,a.invert) (b.gate,b.invert)

def nativeKey {n : ℕ} (k : Key) : AIG.Decl (Fin n) :=
  .gate (.mk k.1.1 k.1.2) (.mk k.2.1 k.2.2)

def empty : Graph := ⟨[.zero],[]⟩
def atom (r : Graph) (i : ℕ) : Graph × Ref :=
  (⟨r.decls++[.atom i],r.cache⟩,(r.decls.length,false))
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

@[simp] lemma refVec_get_gate {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w)
    (idx : ℕ) (h : idx<w) : (v.get idx h).gate=v.refs[idx].gate := by
  cases v;rfl
@[simp] lemma refVec_get_invert {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w)
    (idx : ℕ) (h : idx<w) : (v.get idx h).invert=v.refs[idx].invert := by
  cases v;rfl

end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
def eraseNode {n : ℕ} : BoolNode n→Node
  | .constant b=>.constant b
  | .copy i=>.copy i.val
  | .neg i=>.neg i.val
  | .conj i j=>.conj i.val j.val
def eraseNet {n k : ℕ} : BoolNet n k→List Node
  | .input=>[]
  | .add p o=>eraseNet p++[eraseNode o]
lemma eraseNet_length {n k : ℕ} (p : BoolNet n k) : (eraseNet p).length=p.count := by
  induction p with
  | input=>rfl
  | add p o ih=>simp only [eraseNet,List.length_append,List.length_singleton,BoolNet.count,ih]

def erase {n m : ℕ} (a : BooleanNetwork n m) : Data:=
  ⟨n,eraseNet a.net,List.ofFn (fun i=>(a.output i).val)⟩
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def bnot (a : Data) : Data:=comp a (node 1 (.neg 0))
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

lemma eraseNode_bound {n : ℕ} (o : BoolNode n) : (eraseNode o).Bound n:=by
  cases o <;> simp only [eraseNode,Node.Bound] <;> omega
lemma eraseNet_nodes_bound {n k : ℕ} (p : BoolNet n k) : ∀o∈eraseNet p,o.Bound k:=by
  induction p with
  | input=>intro o ho;cases ho
  | @add k p op ih=>
    intro o ho
    simp only [eraseNet,List.mem_append,List.mem_singleton] at ho
    rcases ho with ho|rfl
    · exact (ih _ ho).mono (by omega)
    · exact (eraseNode_bound op).mono (by omega)
lemma erase_valid {n m : ℕ} (a : BooleanNetwork n m) : (erase a).Valid:=by
  have hw : (erase a).width=a.width:=by
    change n+(eraseNet a.net).length=a.width
    rw [eraseNet_length];exact a.net.width_eq.symm
  constructor
  · rw [hw];exact eraseNet_nodes_bound a.net
  · intro i hi
    change i∈List.ofFn (fun j=>(a.output j).val) at hi
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi
    rw [hw];exact Nat.le_of_lt (a.output j).isLt
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionPack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
def erasePack {n m : ℕ} (a : BooleanNetwork n m) : Pack:=
  ⟨⟨n+a.net.count+m,erase a⟩,erase_valid a,by simp only [Data.mass,Data.width,erase,eraseNet_length,List.length_ofFn];rfl⟩
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RootCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

def rootModulus (w : ℕ) : BooleanNetwork (w+w) w := select (Fin.castAdd w)
def rootGuess (w : ℕ) : BooleanNetwork (w+w) w := select (Fin.natAdd w)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackTestBit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def dropWord : Procedure (prodCode unaryCode (id : List Bool→List Bool)) id
    (fun x=>x.2.drop x.1):=by
  refine (tail.iterate Polynomial.X ?_).congrFun ?_
  · intro n xs i hi
    have h : (List.tail^[i] xs).length≤xs.length:=by
      induction i with
      | zero=>rfl
      | succ i ih=>
        rw [Function.iterate_succ_apply']
        simp only [List.length_tail]
        omega
    simp only [Polynomial.eval_X,id_eq]
    exact h.trans (Nat.le_add_left _ _)
  · rintro ⟨n,xs⟩
    change List.tail^[n] xs=xs.drop n
    induction n with
    | zero=>rfl
    | succ n ih=> rw [Function.iterate_succ_apply',ih,List.tail_drop]
noncomputable def testBit : Procedure (prodCode Nat.bits unaryCode) boolCode
    (fun x=>x.1.testBit x.2):=by
  let p:=head.comp (dropWord.comp
    ((second Nat.bits unaryCode).pair ((identity (id : List Bool→List Bool)).precompose Nat.bits |>.comp
      (first Nat.bits unaryCode))))
  refine p.congrFun ?_
  intro x
  change (x.1.bits.drop x.2).headD false=x.1.testBit x.2
  rw [Nat.testBit_eq_inth,List.headD_eq_head?_getD,List.head?_drop]
  rfl
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkStackCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
abbrev StackOp := Pack ⊕ Bool
def stackOpCode : StackOp→List Bool:=sumCode packCode boolCode
def stackBudget (s : List Pack) : ℕ:=(s.map (fun a=>a.val.budget)).sum

end ExactQuantumFactoring.NetworkEmission
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionPostfix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
open AIGNetworkEmission

def exprTokenCode {v : Type} (ev : v→List Bool) : ExprToken v→List Bool:=sumCode ev (sumCode Nat.bits Nat.bits)
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordResize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Ordinary zero extension/truncation, without copying a word circuit once per bit. -/
def resizeWord (u w : ℕ) : BooleanNetwork u w :=
  vector (fun i => if h : i.val<u then bit ⟨i.val,h⟩ else constant false)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionSyntaxEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
variable {v : Type}
def exprPayload (ev : v→List Bool):=prodCode unaryCode (prodCode Nat.bits (listCode (exprTokenCode ev)))
def exprCode (ev : v→List Bool) (e : NatExpr v):=exprPayload ev (exprView e)
namespace Emission
variable (ev : v→List Bool)
noncomputable def exprViewP : Procedure (exprCode ev) (exprPayload ev) exprView:=
  (identity (exprPayload ev)).precompose exprView
noncomputable def exprSizeP : Procedure (exprCode ev) unaryCode NatExpr.size:=
  (first unaryCode _).comp (exprViewP ev)
noncomputable def exprMaxP : Procedure (exprCode ev) Nat.bits NatExpr.maxConst:=
  (first Nat.bits _).comp ((second unaryCode _).comp (exprViewP ev))
noncomputable def exprTokensP : Procedure (exprCode ev) (listCode (exprTokenCode ev)) exprTokens:=
  (second Nat.bits _).comp ((second unaryCode _).comp (exprViewP ev))
noncomputable def binaryMax : Procedure (prodCode Nat.bits Nat.bits) Nat.bits (fun x=>max x.1 x.2):=
  (conditional binaryLe (second Nat.bits Nat.bits) (first Nat.bits Nat.bits)).congrFun (by
    intro x;simp only [decide_eq_true_eq];split_ifs with h
    · exact (max_eq_right h).symm
    · exact (max_eq_left (by omega)).symm)
noncomputable def exprVarP : Procedure ev (exprCode ev) NatExpr.var:=by
  let token:=(sumLeft ev (sumCode Nat.bits Nat.bits))
  let ts:=(listCons (exprTokenCode ev)).comp (token.pair (Procedure.constant ev (listCode (exprTokenCode ev)) []))
  exact ((Procedure.constant ev unaryCode 1).pair ((Procedure.constant ev Nat.bits 0).pair ts)).result (by intro i;rfl)
noncomputable def constTokenP : Procedure Nat.bits (exprTokenCode ev) (fun c=>Sum.inr (Sum.inl c)):=
  (sumRight ev (sumCode Nat.bits Nat.bits)).comp (sumLeft Nat.bits Nat.bits)
noncomputable def exprConstP : Procedure Nat.bits (exprCode ev) NatExpr.const:=by
  let ts:=(listCons (exprTokenCode ev)).comp ((constTokenP ev).pair (Procedure.constant Nat.bits (listCode (exprTokenCode ev)) []))
  exact ((Procedure.constant Nat.bits unaryCode 1).pair ((identity Nat.bits).pair ts)).result (by intro i;rfl)
noncomputable def tokensAppendP : Procedure (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
    (listCode (exprTokenCode ev)) (fun x=>x.1++x.2):=listAppend _ (opToken 0)
noncomputable def tokensPairP : Procedure (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
    (listCode (exprTokenCode ev)) (fun x=>x.1++x.2++[pairToken]):=
  (tokensAppendP ev).comp ((tokensAppendP ev).pair (Procedure.constant _ _ [pairToken]))
noncomputable def tokensOpP (j : ℕ) : Procedure (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))
    (fun ts=>ts++[opToken j,compToken]):=
  (tokensAppendP ev).comp ((identity _).pair (Procedure.constant _ _ [opToken j,compToken]))
noncomputable def tokensLeP : Procedure (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
    (listCode (exprTokenCode ev)) (fun x=>leTokens x.1 x.2):=
  (tokensOpP ev 6).comp ((tokensOpP ev 5).comp ((tokensPairP ev).comp
    ((second _ _).pair (first _ _))))
noncomputable def tokensMuxP : Procedure (prodCode (listCode (exprTokenCode ev))
    (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))))
    (listCode (exprTokenCode ev)) (fun x=>muxTokens x.1 x.2.1 x.2.2):=by
  let a:=first (listCode (exprTokenCode ev)) (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
  let rs:=second (listCode (exprTokenCode ev)) (prodCode (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev)))
  let b:=(first (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))).comp rs
  let c:=(second (listCode (exprTokenCode ev)) (listCode (exprTokenCode ev))).comp rs
  exact (tokensOpP ev 7).comp ((tokensPairP ev).comp (((tokensPairP ev).comp (a.pair b)).pair c))
noncomputable def exprBinaryP (j : ℕ) (f : NatExpr v→NatExpr v→NatExpr v)
    (hs : ∀a b,(f a b).size=a.size+b.size+1)
    (hm : ∀a b,(f a b).maxConst=max a.maxConst b.maxConst)
    (ht : ∀a b,exprTokens (f a b)=exprTokens a++exprTokens b++[pairToken]++[opToken j,compToken]) :
    Procedure (prodCode (exprCode ev) (exprCode ev)) (exprCode ev) (fun x=>f x.1 x.2):=by
  let a:=first (exprCode ev) (exprCode ev)
  let b:=second (exprCode ev) (exprCode ev)
  let sz:=unarySuccessor.comp (unaryAdd.comp (((exprSizeP ev).comp a).pair ((exprSizeP ev).comp b)))
  let mx:=binaryMax.comp (((exprMaxP ev).comp a).pair ((exprMaxP ev).comp b))
  let ts:=(tokensOpP ev j).comp ((tokensPairP ev).comp (((exprTokensP ev).comp a).pair ((exprTokensP ev).comp b)))
  exact (sz.pair (mx.pair ts)).result (by intro x;simp only [exprCode,exprView,hs,hm,ht];rfl)
noncomputable def exprAddP:=exprBinaryP ev 0 NatExpr.add (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprMulP:=exprBinaryP ev 1 NatExpr.mul (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprDivP:=exprBinaryP ev 3 NatExpr.div (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprModP:=exprBinaryP ev 4 NatExpr.mod (by intros;rfl) (by intros;rfl) (by intros;rfl)
noncomputable def exprSubP : Procedure (prodCode (exprCode ev) (exprCode ev)) (exprCode ev) (fun x=>NatExpr.sub x.1 x.2):=by
  let a:=first (exprCode ev) (exprCode ev)
  let b:=second (exprCode ev) (exprCode ev)
  let sz:=unarySuccessor.comp (unaryAdd.comp (((exprSizeP ev).comp a).pair ((exprSizeP ev).comp b)))
  let mx:=binaryMax.comp (((exprMaxP ev).comp a).pair ((exprMaxP ev).comp b))
  let as':=(exprTokensP ev).comp a
  let bs:=(exprTokensP ev).comp b
  let test:=(tokensLeP ev).comp (bs.pair as')
  let sub:=(tokensOpP ev 2).comp ((tokensPairP ev).comp (as'.pair bs))
  let z:=Procedure.constant (prodCode (exprCode ev) (exprCode ev)) (listCode (exprTokenCode ev)) [.inr (.inl 0)]
  exact (sz.pair (mx.pair ((tokensMuxP ev).comp (test.pair (sub.pair z))))).result (by intro x;rfl)
noncomputable def exprIteP : Procedure (prodCode (exprCode ev) (prodCode (exprCode ev) (prodCode (exprCode ev) (exprCode ev))))
    (exprCode ev) (fun x=>NatExpr.iteLe x.1 x.2.1 x.2.2.1 x.2.2.2):=by
  let a:=first (exprCode ev) (prodCode (exprCode ev) (prodCode (exprCode ev) (exprCode ev)))
  let rs:=second (exprCode ev) (prodCode (exprCode ev) (prodCode (exprCode ev) (exprCode ev)))
  let b:=(first (exprCode ev) (prodCode (exprCode ev) (exprCode ev))).comp rs
  let rt:=(second (exprCode ev) (prodCode (exprCode ev) (exprCode ev))).comp rs
  let c:=(first (exprCode ev) (exprCode ev)).comp rt
  let d:=(second (exprCode ev) (exprCode ev)).comp rt
  let sz:=unarySuccessor.comp (unaryAdd.comp ((unaryAdd.comp ((unaryAdd.comp (((exprSizeP ev).comp a).pair
    ((exprSizeP ev).comp b))).pair ((exprSizeP ev).comp c))).pair ((exprSizeP ev).comp d)))
  let mx:=binaryMax.comp ((binaryMax.comp (((exprMaxP ev).comp a).pair ((exprMaxP ev).comp b))).pair
    (binaryMax.comp (((exprMaxP ev).comp c).pair ((exprMaxP ev).comp d))))
  let test:=(tokensLeP ev).comp (((exprTokensP ev).comp a).pair ((exprTokensP ev).comp b))
  let ts:=(tokensMuxP ev).comp (test.pair (((exprTokensP ev).comp c).pair ((exprTokensP ev).comp d)))
  exact (sz.pair (mx.pair ts)).result (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionCombinators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
/-- Existence of a charged, clean, finite-alphabet stack procedure. -/
def Emits {α β : Type} (ea : α→List Bool) (eb : β→List Bool) (f : α→β) : Prop :=
  Nonempty (Procedure ea eb f)
namespace Emits
variable {α β γ δ : Type} {ea : α→List Bool} {eb : β→List Bool}
  {ec : γ→List Bool} {ed : δ→List Bool}
lemma ofProcedure {f : α→β} (p : Procedure ea eb f) : Emits ea eb f:=⟨p⟩
lemma id (e : α→List Bool) : Emits e e (fun x=>x):=⟨Procedure.identity e⟩
lemma const (ea : α→List Bool) (eb : β→List Bool) (b : β) : Emits ea eb (fun _=>b):=⟨Procedure.constant ea eb b⟩
lemma comp {f : α→β} {g : β→γ} (g' : Emits eb ec g) (f' : Emits ea eb f) :
    Emits ea ec (fun x=>g (f x)):=by
  obtain ⟨p⟩:=f';obtain ⟨q⟩:=g';exact ⟨q.comp p⟩
lemma pair {f : α→β} {g : α→γ} (h : Emits ea eb f) (j : Emits ea ec g) :
    Emits ea (prodCode eb ec) (fun x=>(f x,g x)):=by
  obtain ⟨p⟩:=h;obtain ⟨q⟩:=j;exact ⟨p.pair q⟩
lemma fst {f : α→β×γ} (h : Emits ea (prodCode eb ec) f) : Emits ea eb (fun x=>(f x).1):=
  (ofProcedure (Procedure.first eb ec)).comp h
lemma snd {f : α→β×γ} (h : Emits ea (prodCode eb ec) f) : Emits ea ec (fun x=>(f x).2):=
  (ofProcedure (Procedure.second eb ec)).comp h
lemma natAdd {f g : α→ℕ} (h : Emits ea Nat.bits f) (j : Emits ea Nat.bits g) :
    Emits ea Nat.bits (fun x=>f x+g x):=(ofProcedure Procedure.binaryAdd).comp (h.pair j)
end Emits
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackDependentChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f : α→β}
noncomputable def chooseBitD (c : α→Prop) [DecidablePred c]
    (p : Procedure (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val))
    (q : Procedure (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val)) :
    Procedure (fun a=>decide (c a)::ea a) eb f where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs a:=by
    have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
    have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (ea a).length)
    by_cases h:c a
    · obtain ⟨t,ht,hd⟩:=q.shared.runs ⟨a,h⟩
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨t+1,?_,?_⟩
      · simpa only [List.length_cons,Polynomial.eval_add,Polynomial.eval_one] using
          Nat.add_le_add_right ((ht.trans hqmono).trans (Nat.le_add_left
            (q.shared.bound.eval ((ea a).length+1)) (p.shared.bound.eval ((ea a).length+1)))) 1
      · simp only [h,decide_true]
        have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (true::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    · obtain ⟨t,ht,hd⟩:=p.shared.runs ⟨a,h⟩
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨t+1,?_,?_⟩
      · simpa only [List.length_cons,Polynomial.eval_add,Polynomial.eval_one] using
          Nat.add_le_add_right ((ht.trans hpmono).trans (Nat.le_add_right
            (p.shared.bound.eval ((ea a).length+1)) (q.shared.bound.eval ((ea a).length+1)))) 1
      · simp only [h,decide_false]
        have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
noncomputable def splitOn (c : α→Prop) [DecidablePred c]
    (test : Procedure ea boolCode (fun a=>decide (c a)))
    (yes : Procedure (fun x:{a // c a}=>ea x.val) eb (fun x=>f x.val))
    (no : Procedure (fun x:{a // ¬c a}=>ea x.val) eb (fun x=>f x.val)) : Procedure ea eb f:=by
  let p:=no.comp (unprefix (fun x:{a // ¬c a}=>ea x.val) false)
  let q:=yes.comp (unprefix (fun x:{a // c a}=>ea x.val) false)
  let choice:=(chooseBitD c p q).comp (unprefix (fun a=>decide (c a)::false::ea a) true)
  let input:= (test.pair (identity ea)).result (ec:=fun a=>true::decide (c a)::false::ea a)
    (h:=id) (by intro a;rfl)
  exact choice.comp input
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackGCD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma gcdStep_sizeSum (x : ℕ×ℕ) :
    (gcdStep x).1.bits.length+(gcdStep x).2.bits.length≤x.1.bits.length+x.2.bits.length := by
  have hm:=bits_length_mono (Nat.mod_le x.1 x.2)
  unfold gcdStep
  split
  · exact le_rfl
  · change x.2.bits.length+(x.1%x.2).bits.length≤x.1.bits.length+x.2.bits.length
    omega

lemma gcdRound_iterate_sizeSum (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).1.bits.length+(gcdRound^[i] x).2.bits.length≤
      x.1.bits.length+x.2.bits.length := by
  induction i with
  | zero=>rfl
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    exact ((gcdStep_sizeSum _).trans (gcdStep_sizeSum _)).trans ih


end ExactQuantumFactoring.BitStackProgram
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackIntegers
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def intCode (z : ℤ) : List Bool := prodCode Procedure.boolCode Nat.bits (intData z)

namespace Procedure
noncomputable def intSign : Procedure intCode boolCode (fun z=>decide (z<0)) :=
  (first boolCode Nat.bits).precompose intData
noncomputable def intAbs : Procedure intCode Nat.bits Int.natAbs :=
  (second boolCode Nat.bits).precompose intData

noncomputable def signedInt : Procedure (prodCode boolCode Nat.bits) intCode intOfSign := by
  let s:=first boolCode Nat.bits
  let a:=second boolCode Nat.bits
  let nz:=boolNot.comp (binaryZero.comp a)
  exact ((boolAnd.comp (s.pair nz)).pair a).result (by
    intro x
    change prodCode boolCode Nat.bits (x.1 && !decide (x.2=0),x.2)=intCode (intOfSign x)
    rw [intCode,intData_ofSign]
    simp only [decide_not])

noncomputable def natToInt : Procedure Nat.bits intCode (fun n=>(n : ℤ)) :=
  (signedInt.comp ((constant Nat.bits boolCode false).pair (identity Nat.bits))).congrFun (by intro n;rfl)

noncomputable def intNeg : Procedure intCode intCode Neg.neg :=
  (signedInt.comp ((boolNot.comp intSign).pair intAbs)).congrFun (by
    intro z
    change intOfSign (!(intData z).1,(intData z).2) = -z
    rw [intOfSign_not,intOfSign_data])

noncomputable def signedAddP : Procedure
    (prodCode (prodCode boolCode Nat.bits) (prodCode boolCode Nat.bits))
    (prodCode boolCode Nat.bits) signedAdd := by
  let a:=first (prodCode boolCode Nat.bits) (prodCode boolCode Nat.bits)
  let b:=second (prodCode boolCode Nat.bits) (prodCode boolCode Nat.bits)
  let s:=(first boolCode Nat.bits).comp a
  let t:=(first boolCode Nat.bits).comp b
  let m:=(second boolCode Nat.bits).comp a
  let n:=(second boolCode Nat.bits).comp b
  let eqs:=boolNot.comp (boolXor.comp (s.pair t))
  let same:=s.pair (binaryAdd.comp (m.pair n))
  let le:=binaryLe.comp (m.pair n)
  let small:=t.pair (binarySub.comp (n.pair m))
  let large:=s.pair (binarySub.comp (m.pair n))
  exact (conditional eqs same (conditional le small large)).congrFun (by
    rintro ⟨⟨s,m⟩,⟨t,n⟩⟩
    cases s <;> cases t <;> simp [signedAdd,Function.comp_apply])

noncomputable def intAdd : Procedure (prodCode intCode intCode) intCode (fun x=>x.1+x.2) :=
  ((signedInt.comp signedAddP).precompose (fun x : ℤ×ℤ=>(intData x.1,intData x.2))).congrFun
    (by intro x;change intOfSign (signedAdd (intData x.1,intData x.2))=x.1+x.2
        rw [signedAdd_value,intOfSign_data,intOfSign_data])

noncomputable def intMul : Procedure (prodCode intCode intCode) intCode (fun x=>x.1*x.2) := by
  let a:=first intCode intCode
  let b:=second intCode intCode
  let sign:=boolXor.comp ((intSign.comp a).pair (intSign.comp b))
  let mag:=binaryMul.comp ((intAbs.comp a).pair (intAbs.comp b))
  exact (signedInt.comp (sign.pair mag)).congrFun (by
    intro x
    change intOfSign (xor (intData x.1).1 (intData x.2).1,
      (intData x.1).2*(intData x.2).2)=x.1*x.2
    rw [signedMul_value (intData x.1,intData x.2),intOfSign_data,intOfSign_data])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListFlatten
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
lemma listCode_length_flatten_le (ea : α→List Bool) (xss : List (List α)) :
    (listCode ea xss.flatten).length≤(listCode (listCode ea) xss).length:=by
  induction xss with
  | nil=>simp [listCode]
  | cons xs xss ih=>
    simp only [List.flatten_cons,listCode_length_cons]
    have hh:=listCode_length_append ea xs xss.flatten
    omega
namespace Procedure
noncomputable def listFlatten (ea : α→List Bool) (d : α) :
    Procedure (listCode (listCode ea)) (listCode ea) List.flatten:=by
  let step:=(listAppend ea d).comp ((second (listCode ea) (listCode ea)).pair
    (first (listCode ea) (listCode ea)))
  let p:=foldList [] step Polynomial.X (by
    intro xss xs i
    change (listCode ea ((xss.take i).foldl (fun xs ys=>xs++ys) xs)).length≤_
    rw [fold_append_flatten]
    have hh:=listCode_length_append ea xs (xss.take i).flatten
    have hl:=listCode_length_flatten_le ea (xss.take i)
    have ht:=listCode_length_take_le (listCode ea) i xss
    simp only [Polynomial.eval_X];omega)
  exact (p.comp ((identity (listCode (listCode ea))).pair (constant _ (listCode ea) []))).congrFun (by
    intro xss;exact fold_append_flatten xss [])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListMapIdx
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β γ : Type}
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool} {f : α→ℕ→β→γ}
noncomputable def listMapIdxWith (d : β) (e : γ)
    (p : Procedure (prodCode ea (prodCode Nat.bits eb)) ec (fun x=>f x.1 x.2.1 x.2.2)) :
    Procedure (prodCode ea (listCode eb)) (listCode ec) (fun x=>x.2.mapIdx (f x.1)):=by
  let i:=unaryToBits.comp (first unaryCode (prodCode ea (listCode eb)))
  let env:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp env
  let xs:=(second ea (listCode eb)).comp env
  let get:=(listGet eb d).comp (i.pair xs)
  let step:=p.comp (a.pair (i.pair get))
  let len:=(NativeAIG.Emission.listUnaryLength eb d).comp (second ea (listCode eb))
  exact ((tabulate (f:=fun (env : α×List β) i=>f env.1 i ((env.2.drop i).headD d)) e step).comp
    (len.pair (identity (prodCode ea (listCode eb))))).congrFun (by
      intro x;exact map_range_getD_index x.2 d (f x.1))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListWords
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma flatten_length_le_code (xs : List (List Bool)) :
    xs.flatten.length ≤ (listCode (id : List Bool→List Bool) xs).length := by
  induction xs with
  | nil=>simp [listCode]
  | cons x xs ih=>
    simp only [List.flatten_cons,List.length_append,listCode_length_cons,id_eq]
    omega
namespace Procedure
noncomputable def listJoinWords : Procedure (listCode (id : List Bool→List Bool)) id List.flatten := by
  let step:=(append.comp (swap (id : List Bool→List Bool) id))
  let rep:=foldList [] step Polynomial.X (by
    intro xs ys i
    change ((xs.take i).foldl (fun ys x=>ys++x) ys).length ≤ _
    rw [fold_append_words,List.length_append]
    have hh:=flatten_length_le_code (xs.take i)
    have ht:=listCode_length_take_le (id : List Bool→List Bool) i xs
    simp only [Polynomial.eval_X,id_eq]
    omega)
  exact (rep.comp ((identity (listCode (id : List Bool→List Bool))).pair
    (constant (listCode (id : List Bool→List Bool)) id []))).congrFun (by
      intro xs;change xs.foldl (fun ys x=>ys++x) []=xs.flatten
      simpa only [List.nil_append] using fold_append_words xs [])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def binaryPow : Procedure (prodCode unaryCode Nat.bits) Nat.bits (fun x=>x.2^x.1):=by
  let a:=first Nat.bits Nat.bits
  let b:=second Nat.bits Nat.bits
  let step : Procedure (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) powerStep:=
    a.pair (binaryMul.comp (b.pair a))
  let rep:=step.iterate (Polynomial.X^2+Polynomial.C 3*Polynomial.X+1) (by
    intro n s i hi
    rw [powerStep_iterate]
    have hm:=bits_length_mul s.2 (s.1^i)
    have hp:=bits_length_pow s.1 i
    simp only [prodCode,pairBits_length,Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one]
    nlinarith)
  let e:=first unaryCode Nat.bits
  let x:=second unaryCode Nat.bits
  exact ((second Nat.bits Nat.bits).comp (rep.comp (e.pair (x.pair (constant _ Nat.bits 1))))).congrFun (by
    intro x;change ((powerStep^[x.1]) (x.2,1)).2=x.2^x.1
    rw [powerStep_iterate];simp)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ProcedureFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def gcdStepP : Procedure (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) gcdStep :=
  (conditional (binaryZero.comp (second Nat.bits Nat.bits))
    (identity (prodCode Nat.bits Nat.bits)) ((second Nat.bits Nat.bits).pair binaryMod)).congrFun
      (by intro x;simp only [gcdStep,Function.comp_apply,id_eq,decide_eq_true_eq])

noncomputable def binaryGcd : Procedure (prodCode Nat.bits Nat.bits) Nat.bits (fun x=>x.1.gcd x.2) := by
  let p:=(gcdStepP.comp gcdStepP).congrFun (g:=gcdRound) (by intro x;rfl)
  let rep:=p.iterate (Polynomial.C 2*Polynomial.X+1) (by
    intro n x i _
    have hh:=gcdRound_iterate_sizeSum i x
    simp only [prodCode,pairBits_length,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let len:=(length.precompose Nat.bits).comp (second Nat.bits Nat.bits)
  exact ((first Nat.bits Nat.bits).comp (rep.comp (len.pair (identity (prodCode Nat.bits Nat.bits))))).congrFun
    (by intro x;exact gcdRound_result x)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackRationals
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def ratCode (q : ℚ) : List Bool := prodCode intCode Nat.bits (q.num,q.den)

namespace Procedure
noncomputable def ratNum : Procedure ratCode intCode Rat.num :=
  (first intCode Nat.bits).precompose (fun q : ℚ=>(q.num,q.den))
noncomputable def ratDen : Procedure ratCode Nat.bits Rat.den :=
  (second intCode Nat.bits).precompose (fun q : ℚ=>(q.num,q.den))

noncomputable def makeRat : Procedure (prodCode intCode Nat.bits) ratCode
    (fun x=>mkRat x.1 x.2) := by
  let n:=first intCode Nat.bits
  let d:=second intCode Nat.bits
  let a:=intAbs.comp n
  let g:=binaryGcd.comp (d.pair a)
  let num:=signedInt.comp ((intSign.comp n).pair (binaryDiv.comp (a.pair g)))
  let den:=binaryDiv.comp (d.pair g)
  let zero:=constant (prodCode intCode Nat.bits) (prodCode intCode Nat.bits) (0,1)
  let p:=conditional (binaryZero.comp d) zero (num.pair den)
  exact p.result (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq]
    change prodCode intCode Nat.bits (ratData x)=ratCode (mkRat x.1 x.2)
    rw [ratData_spec];rfl)

noncomputable def intToRat : Procedure intCode ratCode (fun z=>(z : ℚ)) :=
  (makeRat.comp ((identity intCode).pair (constant intCode Nat.bits 1))).congrFun (by
    intro z; simp [Rat.mkRat_eq_div])

noncomputable def ratNeg : Procedure ratCode ratCode Neg.neg :=
  (makeRat.comp ((intNeg.comp ratNum).pair ratDen)).congrFun (by
    intro q
    change mkRat (-q.num) q.den = -q
    rw [Rat.mkRat_eq_div,Int.cast_neg,neg_div,Rat.num_div_den])

noncomputable def ratAdd : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1+x.2) := by
  let a:=first ratCode ratCode
  let b:=second ratCode ratCode
  let an:=ratNum.comp a
  let bn:=ratNum.comp b
  let ad:=ratDen.comp a
  let bd:=ratDen.comp b
  let num:=intAdd.comp ((intMul.comp (an.pair (natToInt.comp bd))).pair
    (intMul.comp (bn.pair (natToInt.comp ad))))
  let den:=binaryMul.comp (ad.pair bd)
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.1.num * (x.2.den : ℤ) + x.2.num * (x.1.den : ℤ))
      (x.1.den*x.2.den) = x.1+x.2
    rw [←Rat.mkRat_add_mkRat _ _ x.1.den_nz x.2.den_nz]
    simp)

noncomputable def ratMul : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1*x.2) := by
  let a:=first ratCode ratCode
  let b:=second ratCode ratCode
  let num:=intMul.comp ((ratNum.comp a).pair (ratNum.comp b))
  let den:=binaryMul.comp ((ratDen.comp a).pair (ratDen.comp b))
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.1.num*x.2.num) (x.1.den*x.2.den)=x.1*x.2
    rw [←Rat.mkRat_mul_mkRat];simp)

noncomputable def ratSub : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1-x.2) :=
  (ratAdd.comp ((first ratCode ratCode).pair (ratNeg.comp (second ratCode ratCode)))).congrFun
    (by intro x;exact (sub_eq_add_neg _ _).symm)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackRationalDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def ratInv : Procedure ratCode ratCode (fun q=>q⁻¹):=by
  let num:=signedInt.comp ((intSign.comp ratNum).pair ratDen)
  let den:=intAbs.comp ratNum
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro q
    change mkRat (intOfSign (decide (q.num<0),q.den)) q.num.natAbs=q⁻¹
    rw [Rat.mkRat_eq_div]
    by_cases h:q.num<0
    · have hz:=Int.eq_neg_natAbs_of_nonpos h.le
      simp only [h,decide_true,intOfSign,ite_true, if_true,Int.cast_neg,Int.cast_natCast]
      conv_rhs=>rw [←Rat.num_div_den q,hz]
      simp only [Int.cast_neg,Int.cast_natCast,neg_div,inv_neg,inv_div]
    · have hz:=Int.natAbs_of_nonneg (le_of_not_gt h)
      simp only [h,decide_false,intOfSign,Bool.false_eq_true,ite_false, if_false,Int.cast_natCast]
      conv_rhs=>rw [←Rat.num_div_den q,←hz]
      simp only [inv_div,Int.cast_natCast])
noncomputable def ratDiv : Procedure (prodCode ratCode ratCode) ratCode (fun x=>x.1/x.2):=
  (ratMul.comp ((first ratCode ratCode).pair (ratInv.comp (second ratCode ratCode)))).congrFun
    (by intro x;exact (div_eq_mul_inv _ _).symm)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackRationalFloor
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
noncomputable def ratFloor : Procedure ratCode intCode (fun q=>⌊q⌋):=by
  let num:=ratNum
  let den:=ratDen
  let mag:=intAbs.comp num
  let negmag:=binaryAdd.comp ((binaryDiv.comp
    ((binarySub.comp (mag.pair (constant ratCode Nat.bits 1))).pair den)).pair
    (constant ratCode Nat.bits 1))
  let pos:=natToInt.comp (binaryDiv.comp (mag.pair den))
  let neg:=intNeg.comp (natToInt.comp negmag)
  exact (conditional (intSign.comp num) neg pos).congrFun (by
    intro q
    change (if decide (q.num<0) then -((((q.num.natAbs-1)/q.den+1):ℕ):ℤ)
      else ((q.num.natAbs/q.den):ℤ))=⌊q⌋
    rw [Rat.floor_def']
    obtain ⟨d,hd⟩:=Nat.exists_eq_succ_of_ne_zero q.den_nz
    rw [hd]
    cases q.num with
    | ofNat a=>simp
    | negSucc a=>
      simp only [Int.negSucc_lt_zero, decide_true, ite_true, if_true, Int.natAbs_negSucc,
        Int.negSucc_ediv_ofNat_succ]
      change -((((a+1-1)/(d+1)+1):ℕ):ℤ)=Int.negSucc (a/(d+1))
      simp only [Nat.add_sub_cancel]
      rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackRationalPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def intPow : Procedure (prodCode unaryCode intCode) intCode (fun x=>x.2^x.1):=by
  let k:=first unaryCode intCode
  let z:=second unaryCode intCode
  let odd:=binaryEq.comp ((binaryMod.comp ((unaryToBits.comp k).pair
    (constant _ Nat.bits 2))).pair (constant _ Nat.bits 1))
  let s:=boolAnd.comp ((intSign.comp z).pair odd)
  let a:=binaryPow.comp (k.pair (intAbs.comp z))
  exact (signedInt.comp (s.pair a)).congrFun (by intro x;exact intOfSign_pow x.2 x.1)
noncomputable def ratPow : Procedure (prodCode unaryCode ratCode) ratCode (fun x=>x.2^x.1):=by
  let k:=first unaryCode ratCode
  let q:=second unaryCode ratCode
  let num:=intPow.comp (k.pair (ratNum.comp q))
  let den:=binaryPow.comp (k.pair (ratDen.comp q))
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.2.num^x.1) (x.2.den^x.1)=x.2^x.1
    rw [Rat.mkRat_eq_div,Int.cast_pow,Nat.cast_pow,←div_pow,Rat.num_div_den])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitEmissionModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission

def eraseOp {q : ℕ} (o : Instruction q) : Op:=⟨o.gate,List.ofFn (fun i=>(o.wire i).val)⟩

def Op.map (f : ℕ→ℕ) (o : Op) : Op:=⟨o.gate,o.wires.map f⟩
def Op.reverse (o : Op) : Op:=⟨o.gate.reverse,o.wires⟩

def erase (c : Circuit) : Data:=⟨c.qubits,c.instructions.map eraseOp⟩
def opView (o : Op):=(o.gate,o.wires)
def dataView (c : Data):=(c.qubits,c.ops)

def Op.encodeClipped (cap : ℕ) (o : Op) : List Bool:=
  natWord o.gate.primitive.code++[o.gate.inverse,o.gate.controlled]++
    o.wires.flatMap (fun i=>natWord (min cap i))
def Data.encodeClipped (c : Data) : List Bool:=natWord c.qubits++natWord c.ops.length++
  c.ops.flatMap (Op.encodeClipped c.qubits)
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitBooleanEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open NetworkEmission

def notOp (t : ℕ) : Op:=⟨plainGate .not,[t]⟩
def cnotOp (a t : ℕ) : Op:=⟨plainGate .cnot,[a,t]⟩
def toffoliOp (a b t : ℕ) : Op:=⟨plainGate .toffoli,[a,b,t]⟩

def nodeOps (t : ℕ) : Node→List Op
  | .constant false=>[]
  | .constant true=>[notOp t]
  | .copy a=>[cnotOp a t]
  | .neg a=>[cnotOp a t,notOp t]
  | .conj a b=>if a=b then [cnotOp a t] else [toffoliOp a b t]

def netOps (n : ℕ) (xs : List Node) : List Op:=
  (xs.mapIdx (fun i o=>nodeOps (n+i) o)).flatten

def copyOps (k : ℕ) (xs : List ℕ) : List Op:=xs.mapIdx (fun i a=>cnotOp a (k+i))

def oracleOps (a : NetworkEmission.Data) : List Op:=
  let p:=netOps a.inputs a.nodes
  p++copyOps (a.inputs+a.nodes.length) a.outputs++p.reverse.map Op.reverse
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitEmissionEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def natWordP : Procedure unaryCode id natWord :=
  ((append.comp ((identity (id : List Bool→List Bool)).pair
    (Procedure.constant (id : List Bool→List Bool) id [false]))).precompose unaryCode).congrFun (by intro n;rfl)
noncomputable def wireWordsP : Procedure (prodCode unaryCode (listCode Nat.bits)) id
    (fun x=>x.2.flatMap (fun i=>natWord (min x.1 i))) :=
  (listJoinWords.comp (listMapWith (f:=fun cap i=>natWord (min cap i)) 0 []
    (natWordP.comp clippedUnary))).congrFun (by intro x;rfl)
end Emission

end ExactQuantumFactoring.CircuitEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma listCons {f : α→β} {g : α→List β} (hf : Emits ea eb f) (hg : Emits ea (listCode eb) g) :
    Emits ea (listCode eb) (fun x=>f x::g x):=(ofProcedure (Procedure.listCons eb)).comp (hf.pair hg)
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionTokenProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure AIGNetworkEmission
namespace Emission
noncomputable def tokenTagP : Procedure (exprTokenCode Nat.bits) Nat.bits tokenTag:=
  (casesSum (Procedure.constant Nat.bits Nat.bits 0)
    (casesSum (Procedure.constant Nat.bits Nat.bits 1) (Procedure.constant Nat.bits Nat.bits 2))).congrFun (by
      intro t;rcases t with i|c|j <;> rfl)
noncomputable def tokenPayloadP : Procedure (exprTokenCode Nat.bits) Nat.bits tokenPayload:=
  (casesSum (identity Nat.bits) (casesSum (identity Nat.bits) (identity Nat.bits))).congrFun (by
    intro t;rcases t with i|c|j <;> rfl)
abbrev exprEnvCode:=prodCode unaryCode (prodCode unaryCode (listCode packCode))
abbrev ExprEnv:=ℕ×ℕ×List Pack
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionTemplateEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
variable {v : Type}
lemma tokenMap_code (f : v→ℕ) (t : ExprToken v) :
    exprTokenCode Nat.bits (tokenMap f t)=exprTokenCode (fun i=>(f i).bits) t:=by
  rcases t with i|c|j <;> rfl
lemma tokenMap_listCode (f : v→ℕ) (ts : List (ExprToken v)) :
    listCode (exprTokenCode Nat.bits) (ts.map (tokenMap f))=
    listCode (exprTokenCode (fun i=>(f i).bits)) ts:=by
  induction ts with
  | nil=>rfl
  | cons t ts ih=>simp only [List.map_cons,listCode,tokenMap_code,ih]
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionCombinators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
/-- Exact, syntactic network emission. Pack budgets are internal certificates,
not additional generator advice. -/
def NetEmits {α : Type} (ea : α→List Bool) {n m : α→ℕ}
    (f : ∀x,BooleanNetwork (n x) (m x)) : Prop:=
  ∃p : α→Pack,BitStackProgram.Emits ea packCode p ∧ ∀x,(p x).val.value=erase (f x)
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ContinuedFractionCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open OrderTrial

def cfHead (w : ℕ) : BooleanNetwork (w+(w+w)) w := select (Fin.castAdd (w+w))
def cfTail (w : ℕ) : BooleanNetwork (w+(w+w)) (w+w) := select (Fin.natAdd w)
def cfP (w : ℕ) : BooleanNetwork (w+(w+w)) w := (cfTail w).comp (rootModulus w)
def cfQ (w : ℕ) : BooleanNetwork (w+(w+w)) w := (cfTail w).comp (rootGuess w)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhaseOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

namespace BooleanNetwork

/-- Predicate phase kickback is a clean oracle, two S gates, and the same
clean XOR oracle again, all over the fixed gate alphabet. -/
def phaseOracle {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r) :
    List (Instruction (n+1+r)) :=
  oracleOn c hr ++ [phaseAt phaseTarget,phaseAt phaseTarget] ++ oracleOn c hr

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

/-- Five actual programs: prepare, mark good, unprepare, mark zero work,
prepare. The two phase predicates share a clean flag and scratch area. -/
def amplificationProgram {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r) :
    List (Instruction (n+1+r)) :=
  firstProgram 1 r ops ++ phaseOracle good hg ++
    firstProgram 1 r (ops.reverse.map Instruction.reverse) ++ phaseOracle zero hz ++
      firstProgram 1 r ops

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

namespace BitArithmetic

def liftInput {k l w : ℕ} (a : BooleanNetwork k w) (f : Fin k → Fin l) : BooleanNetwork l w :=
  (select f).comp a

@[simp] lemma liftInput_count {k l w : ℕ} (a : BooleanNetwork k w) (f : Fin k → Fin l) :
    (liftInput a f).net.count=a.net.count := by simp [liftInput,count_comp]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TwoAdicCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

namespace BitArithmetic

def bequiv {k : ℕ} (a b : BooleanNetwork k 1) : BooleanNetwork k 1 := (a.bxor b).bnot
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OracleReadOnly
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

@[simp] lemma toffoliAt_target {q : ℕ} (a b t : Fin q) (hab : a≠b) (hat : a≠t) (hbt : b≠t) :
    (toffoliAt a b t hab hat hbt).target=t := rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitProgramEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

namespace CircuitEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits

def oracleOnOps (a : NetworkEmission.Data) : List Op:=
  (oracleOps a).map (Op.map (BooleanNetwork.oracleIndex a.inputs a.outputs.length a.width))

def phaseOp (n : ℕ) : Op:=⟨plainGate .phase,[n]⟩

def phaseOps (a : NetworkEmission.Data) : List Op:=
  oracleOnOps a++[phaseOp a.inputs,phaseOp a.inputs]++oracleOnOps a

namespace Emission
noncomputable def oracleIndexP : Procedure
    (prodCode (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits) Nat.bits
    (fun x=>BooleanNetwork.oracleIndex x.1.1 x.1.2.1 x.1.2.2 x.2):=by
  let e:=first (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let i:=second (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let n:=(first Nat.bits (prodCode Nat.bits Nat.bits)).comp e
  let m:=(first Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let w:=(second Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let input:=binaryLt.comp (i.pair n)
  let work:=binaryLt.comp (i.pair w)
  let wi:=binaryAdd.comp ((binaryAdd.comp (n.pair m)).pair (binarySub.comp (i.pair n)))
  let oi:=binaryAdd.comp (n.pair (binarySub.comp (i.pair w)))
  exact (conditional input i (conditional work wi oi)).congrFun (by intro x;simp [BooleanNetwork.oracleIndex])
end Emission

end CircuitEmission
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitFinalEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
namespace Emission
noncomputable def relocateValP : Procedure
    (prodCode (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits) Nat.bits
    (fun x=>relocateVal x.1.1 x.1.2.1 x.1.2.2 x.2):=by
  let e:=first (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let i:=second (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Nat.bits
  let a:=(first Nat.bits (prodCode Nat.bits Nat.bits)).comp e
  let m:=(first Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let l:=(second Nat.bits Nat.bits).comp ((second Nat.bits (prodCode Nat.bits Nat.bits)).comp e)
  let z:=binaryEq.comp (i.pair (constant _ Nat.bits 0))
  let il:=boolNot.comp (binaryLt.comp (l.pair i))
  let ia:=binaryLt.comp (i.pair a)
  let iam:=binaryLt.comp (i.pair (binaryAdd.comp (a.pair m)))
  let case0:=binaryAdd.comp (l.pair m)
  let case1:=binarySub.comp (i.pair (constant _ Nat.bits 1))
  let case2:=binaryAdd.comp (i.pair m)
  let case3:=binaryAdd.comp (l.pair (binarySub.comp (i.pair a)))
  exact (conditional z case0 (conditional il case1 (conditional ia case2 (conditional iam case3 i)))).congrFun (by
    intro x;simp only [Function.comp_apply,decide_eq_true_eq,relocateVal,Bool.not_eq_true',decide_eq_false_iff_not,not_lt])
end Emission
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitPreparationEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

def hadamardOp (i : ℕ) : Op:=⟨plainGate .hadamard,[i]⟩
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkLoopEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma fold_budget_extra (f : Pack→Pack→Pack) (c : ℕ)
    (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget+c)
    (xs : List Pack) (a : Pack) :
    (xs.foldl (fun b a=>f a b) a).val.budget=a.val.budget+(xs.map (fun s=>s.val.budget)).sum+c*xs.length:=by
  induction xs generalizing a with
  | nil=>simp
  | cons s xs ih=>rw [List.foldl_cons,ih,h,List.map_cons,List.sum_cons,List.length_cons];ring
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CleanPermutationEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

def swapOps (n i : ℕ) : List Op:=[cnotOp i (n+i),cnotOp (n+i) i,cnotOp i (n+i)]
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SignedSyntaxEmission
attribute [-instance] _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
variable {v : Type}
def intExprCode (ev : v→List Bool) (a : IntExpr v):=prodCode (exprCode ev) (exprCode ev) (intExprView a)
def ratExprCode (ev : v→List Bool) (a : RatExpr v):=prodCode (intExprCode ev) (exprCode ev) (ratExprView a)
namespace Emission
noncomputable def intToNatP : Procedure intCode Nat.bits Int.toNat:=
  (conditional intSign (Procedure.constant intCode Nat.bits 0) intAbs).congrFun (by
    intro z;cases z <;> simp)
noncomputable def intExprViewP (ev : v→List Bool) : Procedure (intExprCode ev)
    (prodCode (exprCode ev) (exprCode ev)) intExprView :=(identity _).precompose _
noncomputable def intExprPosP (ev : v→List Bool) : Procedure (intExprCode ev) (exprCode ev) IntExpr.pos:=
  (first _ _).comp (intExprViewP ev)
noncomputable def intExprNegP (ev : v→List Bool) : Procedure (intExprCode ev) (exprCode ev) IntExpr.neg:=
  (second _ _).comp (intExprViewP ev)
noncomputable def intExprMkP (ev : v→List Bool) : Procedure
    (prodCode (exprCode ev) (exprCode ev)) (intExprCode ev) (fun x=>IntExpr.mk x.1 x.2):=
  (identity _).result (by intro x;rfl)
noncomputable def ratExprViewP (ev : v→List Bool) : Procedure (ratExprCode ev)
    (prodCode (intExprCode ev) (exprCode ev)) ratExprView :=(identity _).precompose _
noncomputable def ratExprNumP (ev : v→List Bool) : Procedure (ratExprCode ev) (intExprCode ev) RatExpr.num:=
  (first _ _).comp (ratExprViewP ev)
noncomputable def ratExprDenP (ev : v→List Bool) : Procedure (ratExprCode ev) (exprCode ev) RatExpr.den:=
  (second _ _).comp (ratExprViewP ev)
noncomputable def ratExprMkP (ev : v→List Bool) : Procedure
    (prodCode (intExprCode ev) (exprCode ev)) (ratExprCode ev) (fun x=>RatExpr.mk x.1 x.2):=
  (identity _).result (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionPowerEmission
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
variable {v : Type} (ev : v→List Bool)
lemma exprCode_length (a : NatExpr v) :
    (exprCode ev a).length=2*a.size+2*a.maxConst.bits.length+(listCode (exprTokenCode ev) (exprTokens a)).length+2:=by
  simp only [exprCode,exprPayload,exprView,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
lemma exprCode_const (a : ℕ) : (exprCode ev (NatExpr.const a)).length=4*a.bits.length+11:=by
  rw [exprCode_length]
  simp only [NatExpr.size,NatExpr.maxConst,exprTokens,listCode_length_cons,exprTokenCode,sumCode,List.length_cons]
  have hz : (listCode (sumCode ev (sumCode Nat.bits Nat.bits)) []).length=1:=rfl
  rw [hz];omega
lemma exprCode_mul_le (a b : NatExpr v) :
    (exprCode ev (.mul a b)).length≤(exprCode ev a).length+(exprCode ev b).length+24:=by
  have hm : (max a.maxConst b.maxConst).bits.length≤a.maxConst.bits.length+b.maxConst.bits.length:=by
    rcases le_total a.maxConst b.maxConst with h|h
    · rw [max_eq_right h];omega
    · rw [max_eq_left h];omega
  have h1:=listCode_length_append (exprTokenCode ev) (exprTokens a) (exprTokens b)
  have h2:=listCode_length_append (exprTokenCode ev) (exprTokens a++exprTokens b) [pairToken]
  have h3:=listCode_length_append (exprTokenCode ev) (exprTokens a++exprTokens b++[pairToken]) [opToken 1,compToken]
  rw [exprCode_length,exprCode_length,exprCode_length]
  simp only [NatExpr.size,NatExpr.maxConst,exprTokens]
  have hx : (listCode (exprTokenCode ev) [pairToken]).length=7:=rfl
  have hy : (listCode (exprTokenCode ev) [opToken 1,compToken]).length=19:=rfl
  rw [hx] at h2;rw [hy] at h3
  omega

lemma exprPowerStep_bound (s : NatExpr v×NatExpr v) (i : ℕ) :
    (exprCode ev ((exprPowerStep^[i]) s).2).length≤(exprCode ev s.2).length+i*((exprCode ev s.1).length+24):=by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    have hh:=exprCode_mul_le ev ((exprPowerStep^[i]) s).2 ((exprPowerStep^[i]) s).1
    rw [exprPowerStep_fst] at hh
    change (exprCode ev (.mul _ _)).length≤_
    rw [exprPowerStep_fst]
    nlinarith
namespace Emission
noncomputable def exprPowerP : Procedure (prodCode unaryCode (exprCode ev)) (exprCode ev)
    (fun x=>x.2.pow x.1):=by
  let a:=first (exprCode ev) (exprCode ev)
  let b:=second (exprCode ev) (exprCode ev)
  let step : Procedure (prodCode (exprCode ev) (exprCode ev)) (prodCode (exprCode ev) (exprCode ev)) exprPowerStep:=
    a.pair ((exprMulP ev).comp (b.pair a))
  let rep:=step.iterate (Polynomial.X^2+Polynomial.C 25*Polynomial.X) (by
    intro n s i hi
    have hh:=exprPowerStep_bound ev s i
    simp only [prodCode,pairBits_length,exprPowerStep_fst,Polynomial.eval_add,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    nlinarith)
  let e:=first unaryCode (exprCode ev)
  let a:=second unaryCode (exprCode ev)
  exact ((second (exprCode ev) (exprCode ev)).comp
    (rep.comp (e.pair (a.pair (Procedure.constant _ (exprCode ev) (.const 1)))))).congrFun (by
      intro x;change ((exprPowerStep^[x.1]) (x.2,.const 1)).2=_
      rw [exprPowerStep_start])
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CoveringPowerEmission
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
variable {v : Type} (ev : v→List Bool)
lemma tokenCode_length_append (a b : List (ExprToken v)) :
    (listCode (exprTokenCode ev) (a++b)).length=(listCode (exprTokenCode ev) a).length+(listCode (exprTokenCode ev) b).length-1:=by
  have h:=listCode_length_append (exprTokenCode ev) a b;omega
lemma exprCode_ite_le (a b c d : NatExpr v) :
    (exprCode ev (.iteLe a b c d)).length≤(exprCode ev a).length+(exprCode ev b).length+
      (exprCode ev c).length+(exprCode ev d).length+100:=by
  have h1:=bits_length_max_le a.maxConst b.maxConst
  have h2:=bits_length_max_le c.maxConst d.maxConst
  have h3:=bits_length_max_le (max a.maxConst b.maxConst) (max c.maxConst d.maxConst)
  simp only [exprCode_length,NatExpr.size,NatExpr.maxConst,exprTokens,muxTokens,leTokens]
  have hpair : (listCode (exprTokenCode ev) [pairToken]).length=7:=rfl
  have ho5 : (listCode (exprTokenCode ev) [opToken 5,compToken]).length=21:=rfl
  have ho6 : (listCode (exprTokenCode ev) [opToken 6,compToken]).length=23:=rfl
  have ho7 : (listCode (exprTokenCode ev) [opToken 7,compToken]).length=23:=rfl
  simp only [tokenCode_length_append,hpair,ho5,ho6,ho7]
  omega

lemma coveringStep_expr_bound (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    (exprCode ev ((coveringStep^[i]) s).2.2).length≤(exprCode ev s.2.2).length+
      i*((exprCode ev s.2.1).length+8*(s.1).bits.length+16*i+200):=by
  induction i with
  | zero=>simp
  | succ i ih=>
    have hh:=exprCode_ite_le ev ((coveringStep^[i]) s).2.1 (.const ((coveringStep^[i]) s).1)
      ((coveringStep^[i]) s).2.2 (.const (((coveringStep^[i]) s).1*2))
    rw [exprCode_const,exprCode_const,coveringStep_base] at hh
    have hp:=coveringStep_pow_size s i
    have h2:=bits_length_mul ((coveringStep^[i]) s).1 2
    have ht : (2:ℕ).bits.length=2:=rfl
    rw [ht] at h2
    rw [Function.iterate_succ_apply']
    change (exprCode ev (.iteLe _ _ _ _)).length≤_
    rw [coveringStep_base]
    nlinarith
namespace Emission
noncomputable def coveringPowP : Procedure (prodCode unaryCode (exprCode ev)) (exprCode ev)
    (fun x=>OrderTrial.Expressions.coveringPow x.2 x.1):=by
  let ecode:=prodCode (exprCode ev) (exprCode ev)
  let scode:=prodCode Nat.bits ecode
  let p:=first Nat.bits ecode
  let r:=second Nat.bits ecode
  let d:=(first (exprCode ev) (exprCode ev)).comp r
  let a:=(second (exprCode ev) (exprCode ev)).comp r
  let p2:=binaryMul.comp (p.pair (Procedure.constant scode Nat.bits 2))
  let expr:=(exprIteP ev).comp (d.pair (((exprConstP ev).comp p).pair
    (a.pair ((exprConstP ev).comp p2))))
  let step : Procedure scode scode coveringStep:=p2.pair (d.pair expr)
  let rep:=step.iterate (Polynomial.C 100*Polynomial.X^2+Polynomial.C 205*Polynomial.X+2) (by
    intro n s i hi
    have hp:=coveringStep_pow_size s i
    have he:=coveringStep_expr_bound ev s i
    simp only [scode,ecode,prodCode,pairBits_length,coveringStep_base,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,
      Polynomial.eval_ofNat]
    nlinarith)
  let k:=first unaryCode (exprCode ev)
  let d:=second unaryCode (exprCode ev)
  let start:=(Procedure.constant _ Nat.bits 1).pair (d.pair (Procedure.constant _ (exprCode ev) (.const 1)))
  let out:=(second (exprCode ev) (exprCode ev)).comp (second Nat.bits ecode)
  exact (out.comp (rep.comp (k.pair start))).congrFun (by
    intro x;change ((coveringStep^[x.1]) (1,x.2,.const 1)).2.2=_
    rw [coveringStep_start])
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DescendingFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BooleanNetwork BitStackProgram BitStackProgram.Emits
structure FilterState (k : ℕ) (w : ℕ→ℕ) where
  depth : ℕ
  raw : BooleanNetwork k (w depth)
  pending : List (BooleanNetwork k 1)
def filterStep {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) : FilterState k w→FilterState k w
  | ⟨0,v,ps⟩ => ⟨0,v,ps⟩
  | ⟨s+1,v,ps⟩ => ⟨s,v.comp (prev s),keep s v::ps⟩
def FilterState.code {k : ℕ} {w : ℕ→ℕ} (s : FilterState k w) : ℕ×Pack×List Pack:=
  (s.depth,erasePack s.raw,s.pending.map erasePack)
def filterPrefix {k : ℕ} {w : ℕ→ℕ} (prev : ∀s,BooleanNetwork (w (s+1)) (w s))
    (keep : ∀s,BooleanNetwork k (w (s+1))→BooleanNetwork k 1) : ∀s,BooleanNetwork k (w s)→BooleanNetwork k 1
  | 0,_=>BooleanNetwork.constant true
  | s+1,v=>(filterPrefix prev keep s (v.comp (prev s))).band (keep s v)
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkPredicateEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
namespace Emission
noncomputable def swapIndicesP : Procedure unaryCode (listCode Nat.bits)
    (fun w=>List.ofFn (fun i:Fin (w+w)=>(Fin.addCases (Fin.natAdd w) (Fin.castAdd w) i : Fin (w+w)).val)):=by
  let step:=binaryAdd.comp ((unaryToBits.comp (second unaryCode unaryCode)).pair
    (unaryToBits.comp (first unaryCode unaryCode)))
  let a:=(tabulate (f:=fun w i=>w+i) 0 step).comp ((identity unaryCode).pair (identity unaryCode))
  let b:=(tabulate (f:=fun (_:ℕ) i=>i) 0 (unaryToBits.comp (first unaryCode unaryCode))).comp
    ((identity unaryCode).pair (identity unaryCode))
  exact ((Procedure.listAppend Nat.bits 0).comp (a.pair b)).congrFun (by
    intro w
    change (List.range w).map (fun i=>w+i)++(List.range w).map id=_
    rw [←ofFn_val_range,List.map_ofFn,List.map_id,List.ofFn_add]
    congr 1 <;> apply congrArg List.ofFn <;> funext i
    · change w+i.val=(Fin.addCases (Fin.natAdd w) (Fin.castAdd w) (i.castAdd w) : Fin (w+w)).val
      rw [Fin.addCases_left];rfl
    · rw [Fin.addCases_right];rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionBoundedRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}

def recursionCode (K : α→ℕ) (f : α→ℕ→β) (x : Σa,Fin (K a+1)) : List Bool:=
  prodCode ea (prodCode unaryCode eb) (x.1,(x.2.val,f x.1 x.2.val))
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ListSamplerEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.ListSamplerEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}

def maskOp (n i : ℕ) : Op:=⟨⟨.hadamard,false,true⟩,[i,n+i]⟩
end ExactQuantumFactoring.ListSamplerEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkPolyResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork

def NetworkPoly {a b : ℕ→ℕ} (f : ∀ n,BooleanNetwork (a n) (b n)) : Prop :=
  PolyBound (fun n=>(f n).net.count)


end ExactQuantumFactoring
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkCanonicalEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emission
open Procedure
noncomputable def massP : Procedure dataCode Nat.bits Data.mass:=
  binaryAdd.comp (dataWidthP.pair ((listLength Nat.bits 0).comp dataOutputsP))
def canonicalPack (p : Pack) : Pack:=⟨⟨p.val.value.mass,p.val.value⟩,p.property.1,le_rfl⟩
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolynomialTemplateEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits Emits
variable {α v : Type} {ea : α→List Bool} {ev : v→List Bool}
/-- A fixed polynomial syntax skeleton transports literal coefficient emitters
through substitution. The outer polynomial's depth is fixed; input coefficients
are generated by the supplied charged Boolean-stack procedures. -/
def PolyEmits (ea : α→List Bool) (ev : v→List Bool) (f : α→PolyExpr v) : Prop:=
  ∀(g : α→PolyExpr v), (∀k,BitStackProgram.Emits ea (ratExprCode ev) (fun x=>(g x).coeff k))→
    ∀k,BitStackProgram.Emits ea (ratExprCode ev) (fun x=>((f x).comp (g x)).coeff k)
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DescendingFilterEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BooleanNetwork BitStackProgram BitStackProgram.Emits
abbrev filterCode := prodCode unaryCode (prodCode packCode (listCode packCode))
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeTableEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emission
open BitStackProgram BitStackProgram.Procedure
abbrev rowCode := prodCode packCode packCode
def compRow (a : Pack) (r : Pack×Pack) : Pack×Pack:=(canonicalPack (compPack a r.1),canonicalPack (compPack a r.2))
end ExactQuantumFactoring.NetworkEmission.Emission

end



end OAI
end


