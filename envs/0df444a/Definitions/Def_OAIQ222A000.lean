-- Prove2me | Definitions.Def_OAIQ222A000
-- name    : OAIQ222A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:02:24.443115+00:00
-- url     : https://prove2.me/theorems/df4eea52-ccf8-4ce7-abf0-428bce4b8404
-- title:
--   Definitions bundle OAIQ222A000 of the split of OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 429 declarations of OpenAI's Lean: 210 definitions, 13 inductive types or structures and 206 theorems. The definitions and types are `OAI.ExactQuantumFactoring.AIGCompiler.compile`, `OAI.ExactQuantumFactoring.AIGCompiler.compileVec`, `OAI.ExactQuantumFactoring.AIGCompiler.faninNet`, `OAI.ExactQuantumFactoring.AIGCompiler.graphWire`, `OAI.ExactQuantumFactoring.AIGCompiler.inputs`, `OAI.ExactQuantumFactoring.AIGCompiler.inputsPrefix`, `OAI.ExactQuantumFactoring.AIGCompiler.nodeDenote`, `OAI.ExactQuantumFactoring.AIGCompiler.nodeNet`, `OAI.ExactQuantumFactoring.AIGCompiler.nodeStep`, `OAI.ExactQuantumFactoring.AIGCompiler.partialGraph`, `OAI.ExactQuantumFactoring.AIGCompiler.refVector`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.dimsCode`, `OAI.ExactQuantumFactoring.AIGNetworkEmission.faninPack`, `OAI.ExactQuantumFactoring.BitStackProgram.AddState`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.addStepP`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryAdd`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryEq`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryLe`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryLt`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binarySub`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.binaryZero`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.boolAnd`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.boolCode`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.boolNot`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.casesSum`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.choose`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.chooseBit`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.comp`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.conditional`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.congrEncoding`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.congrFun`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.cons`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.constant`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.double`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.doubleOne`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.duplicate`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.first`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.foldBits`, `OAI.ExactQuantumFactoring.BitStackProgram.Procedure.foldBitsLinear` and 183 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `QuantumFactoring_AIGBounds`, `QuantumFactoring_AIGCompiler`, `QuantumFactoring_AIGDivisionBounds`, `QuantumFactoring_AIGInputs`, `QuantumFactoring_AIGNetworkEmission`, `QuantumFactoring_AIGNetworkProcedure`, `QuantumFactoring_BitStackAdder`, `QuantumFactoring_BitStackBasicProcedures`, `QuantumFactoring_BitStackBinaryBasics`, `QuantumFactoring_BitStackBooleans`, `QuantumFactoring_BitStackChoice`, `QuantumFactoring_BitStackComposition`, `QuantumFactoring_BitStackConstants`, `QuantumFactoring_BitStackDivision`, `QuantumFactoring_BitStackFold`, `QuantumFactoring_BitStackFrames`, `QuantumFactoring_BitStackIncrement`, `QuantumFactoring_BitStackIteration`, `QuantumFactoring_BitStackListCode`, `QuantumFactoring_BitStackListFold`, `QuantumFactoring_BitStackListIndex`, `QuantumFactoring_BitStackListLength`, `QuantumFactoring_BitStackListMapWith`, `QuantumFactoring_BitStackListOps`, `QuantumFactoring_BitStackLists`, `QuantumFactoring_BitStackMultiplier`, `QuantumFactoring_BitStackNaturals`, `QuantumFactoring_BitStackOptions`, `QuantumFactoring_BitStackProcedures`, `QuantumFactoring_BitStackProducts`, `QuantumFactoring_BitStackPrograms`, `QuantumFactoring_BitStackQuotation`, `QuantumFactoring_BitStackRelabel`, `QuantumFactoring_BitStackSubtractor`, `QuantumFactoring_BitStackSums`, `QuantumFactoring_BitStackTabulate`, `QuantumFactoring_BitStackUnary`, `QuantumFactoring_BitStackWords`, `QuantumFactoring_BooleanAlgebra`, `QuantumFactoring_BooleanNetwork`, `QuantumFactoring_BooleanNetworkFurther`, `QuantumFactoring_BooleanVector`, `QuantumFactoring_CircuitEmissionModel`, `QuantumFactoring_NativeAIGAdd`, `QuantumFactoring_NativeAIGAddWrapper`, `QuantumFactoring_NativeAIGBoolean`, `QuantumFactoring_NativeAIGModel`, `QuantumFactoring_NativeAIGProcedures`, `QuantumFactoring_NativeAIGVector`, `QuantumFactoring_NetworkEmissionBasic`, `QuantumFactoring_NetworkEmissionBounds`, `QuantumFactoring_NetworkEmissionModel`, `QuantumFactoring_NetworkEmissionPack`, `QuantumFactoring_NetworkEmissionProcedures`, `QuantumFactoring_NetworkEmissionVector`, `QuantumFactoring_Procedure`.
--
--   **Imports.** It imports the published bundle `Def_ExactQuantumFactoring`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ222A002` and `OAIQ222A003`.
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

section
-- module Solutions.OAIQ222_QF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGBounds
open Std.Sat
open Std.Tactic.BVDecide.BVExpr.bitblast

variable {α : Type} [Hashable α] [DecidableEq α]

lemma cached_go_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (AIG.mkGateCached.go aig input).aig.decls.size ≤ aig.decls.size + 1 := by
  dsimp only [AIG.mkGateCached.go]
  split
  · simp
  · split <;> try simp
    split
    · split <;> simp
    · simp

lemma cached_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkGateCached input).aig.decls.size ≤ aig.decls.size + 1 := by
  dsimp only [AIG.mkGateCached]
  split <;> apply cached_go_size

lemma and_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkAndCached input).aig.decls.size ≤ aig.decls.size + 1 := cached_size _ _

lemma or_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkOrCached input).aig.decls.size ≤ aig.decls.size + 1 := cached_size _ _

lemma xor_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkXorCached input).aig.decls.size ≤ aig.decls.size + 3 := by
  unfold AIG.mkXorCached
  dsimp only
  exact (cached_size _ _).trans (by
    have := cached_size aig input
    have := cached_size (aig.mkGateCached input).aig
      ((input.cast (AIG.LawfulOperator.le_size ..)).invert true true)
    omega)

lemma fullAdderOut_size (aig : AIG α) (input : FullAdderInput aig) :
    (mkFullAdderOut aig input).aig.decls.size ≤ aig.decls.size + 6 := by
  unfold mkFullAdderOut
  dsimp only
  exact (xor_size _ _).trans (by
    have := xor_size aig ⟨input.lhs,input.rhs⟩
    omega)

lemma fullAdderCarry_size (aig : AIG α) (input : FullAdderInput aig) :
    (mkFullAdderCarry aig input).aig.decls.size ≤ aig.decls.size + 6 := by
  unfold mkFullAdderCarry
  dsimp only
  apply (or_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  apply (and_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  apply (and_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  exact xor_size _ _

lemma fullAdder_size (aig : AIG α) (input : FullAdderInput aig) :
    (mkFullAdder aig input).aig.decls.size ≤ aig.decls.size + 12 := by
  unfold mkFullAdder
  dsimp only
  apply (fullAdderCarry_size _ _).trans
  have := fullAdderOut_size aig input
  omega

lemma add_go_size {w : ℕ} (aig : AIG α) (lhs rhs : AIG.RefVec aig w)
    (curr : ℕ) (hcurr : curr ≤ w) (cin : AIG.Ref aig) (s : AIG.RefVec aig curr) :
    (blastAdd.go aig lhs rhs curr hcurr cin s).aig.decls.size ≤
      aig.decls.size + 12*(w-curr) := by
  rw [blastAdd.go]
  split
  next h =>
    dsimp only
    apply (add_go_size _ _ _ _ _ _ _).trans
    have hh := fullAdder_size aig ⟨lhs.get curr h, rhs.get curr h, cin⟩
    omega
  next h => simp
termination_by w-curr

/-- A verified native ripple circuit has linear declaration count. The cache
can only decrease this upper bound. -/
theorem add_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastAdd aig input).aig.decls.size ≤ aig.decls.size + 12*w := by
  unfold blastAdd
  split <;> unfold blastAdd.blast <;> apply add_go_size

lemma if_size (aig : AIG α) (input : AIG.TernaryInput aig) :
    (aig.mkIfCached input).aig.decls.size ≤ aig.decls.size + 3 := by
  unfold AIG.mkIfCached
  dsimp only
  apply (or_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  apply (and_size _ _).trans
  apply Nat.add_le_add_right ?_ 1
  exact and_size _ _

lemma ite_go_size {w : ℕ} (aig : AIG α) (curr : ℕ) (hcurr : curr ≤ w)
    (discr : AIG.Ref aig) (lhs rhs : AIG.RefVec aig w) (s : AIG.RefVec aig curr) :
    (AIG.RefVec.ite.go aig curr hcurr discr lhs rhs s).aig.decls.size ≤
      aig.decls.size + 3*(w-curr) := by
  rw [AIG.RefVec.ite.go]
  split
  next h =>
    dsimp only
    apply (ite_go_size _ _ _ _ _ _ _).trans
    have hh := if_size aig ⟨discr, lhs.get curr h, rhs.get curr h⟩
    omega
  next h => simp
termination_by w-curr

lemma ite_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec.IfInput aig w) :
    (AIG.RefVec.ite aig input).aig.decls.size ≤ aig.decls.size + 3*w :=
  ite_go_size _ 0 _ _ _ _ _

lemma shift_go_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w)
    (distance curr : ℕ) (hcurr : curr ≤ w) (s : AIG.RefVec aig curr) :
    (blastShiftLeftConst.go aig input distance curr hcurr s).aig.decls.size = aig.decls.size := by
  rw [blastShiftLeftConst.go]
  split
  · split <;> apply shift_go_size
  · simp
termination_by w-curr

lemma shift_size {w : ℕ} (aig : AIG α) (input : AIG.ShiftTarget aig w) :
    (blastShiftLeftConst aig input).aig.decls.size = aig.decls.size := shift_go_size ..

lemma mul_go_size {w : ℕ} (aig : AIG α) (lhs rhs : AIG.RefVec aig w)
    (curr : ℕ) (acc : AIG.RefVec aig w) :
    (blastMul.go aig lhs rhs curr acc).aig.decls.size ≤ aig.decls.size + 15*w*(w-curr) := by
  rw [blastMul.go]
  split
  next h =>
    split
    · apply (mul_go_size _ _ _ _ _).trans
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    · dsimp only
      apply (mul_go_size _ _ _ _ _).trans
      have hshift := shift_size aig ⟨lhs,curr⟩
      refine (Nat.add_le_add_right (ite_size _ _) _).trans ?_
      have hadd : (blastAdd (blastShiftLeftConst aig ⟨lhs,curr⟩).aig
            ⟨acc.cast (AIG.LawfulVecOperator.le_size ..),
              (blastShiftLeftConst aig ⟨lhs,curr⟩).vec⟩).aig.decls.size ≤ aig.decls.size + 12*w := by
          rw [← hshift]
          apply add_size
      have he : w-curr = (w-(curr+1))+1 := by omega
      rw [he, Nat.mul_add, Nat.mul_one]
      omega
  next h => simp
termination_by w-curr

lemma mul_blast_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastMul.blast aig input).aig.decls.size ≤ aig.decls.size + 15*w*w := by
  unfold blastMul.blast
  split
  · simp_all
  next h =>
    dsimp only
    apply (mul_go_size _ _ _ _ _).trans
    have hh := ite_size aig ⟨input.rhs.get 0 (by omega), input.lhs, blastConst aig 0⟩
    have he : w-1+1=w := by omega
    nlinarith

/-- The native shift-and-add multiplier has quadratic declaration count. -/
theorem mul_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastMul aig input).aig.decls.size ≤ aig.decls.size + 15*w*w := by
  unfold blastMul
  split <;> apply mul_blast_size

end ExactQuantumFactoring.AIGBounds


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

/-- A bounded-fan-in Boolean node, with no hidden arithmetic operation. -/
inductive BoolNode (n : ℕ) where
  | constant (b : Bool)
  | copy (i : Fin n)
  | neg (i : Fin n)
  | conj (i j : Fin n)

namespace BoolNode

def eval {n : ℕ} : BoolNode n → (Fin n → Bool) → Bool
  | .constant b, _ => b
  | .copy i, x => x i
  | .neg i, x => !x i
  | .conj i j, x => x i && x j

def map {n m : ℕ} (f : Fin n → Fin m) : BoolNode n → BoolNode m
  | .constant b => .constant b
  | .copy i => .copy (f i)
  | .neg i => .neg (f i)
  | .conj i j => .conj (f i) (f j)

end BoolNode

/-- Straight-line Boolean computation retaining its whole trace. Width increases
by exactly one per node, so there is no truth-table synthesis overhead. -/
inductive BoolNet (n : ℕ) : ℕ → Type
  | input : BoolNet n n
  | add {k : ℕ} (p : BoolNet n k) (o : BoolNode k) : BoolNet n (k+1)

namespace BoolNet

def count {n k : ℕ} : BoolNet n k → ℕ
  | .input => 0
  | .add p _ => p.count + 1

lemma width_eq {n k : ℕ} (p : BoolNet n k) : k = n + p.count := by
  induction p with
  | input => simp [count]
  | add p o ih => simp only [count]; omega

lemma input_le {n k : ℕ} (p : BoolNet n k) : n ≤ k := by rw [p.width_eq]; omega

def eval {n k : ℕ} : BoolNet n k → (Fin n → Bool) → (Fin k → Bool)
  | .input, x => x
  | .add p o, x => Fin.snoc (p.eval x) (o.eval (p.eval x))

@[simp] lemma eval_add_castSucc {n k : ℕ} (p : BoolNet n k) (o : BoolNode k)
    (x : Fin n → Bool) (i : Fin k) : (p.add o).eval x i.castSucc = p.eval x i := by
  simp [eval]

@[simp] lemma eval_add_last {n k : ℕ} (p : BoolNet n k) (o : BoolNode k)
    (x : Fin n → Bool) : (p.add o).eval x (Fin.last k) = o.eval (p.eval x) := by
  simp [eval]

/-- Append a network whose inputs are arbitrary already-computed wires.
Repeated input sources are permitted and do not cause duplicated computation. -/
def attach {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    (j : ℕ) × BoolNet n j × (Fin l → Fin j) :=
  match b with
  | .input => ⟨k, a, ρ⟩
  | .add b o =>
    let c := a.attach ρ b
    ⟨c.1 + 1, c.2.1.add (o.map c.2.2), Fin.snoc (fun i => (c.2.2 i).castSucc) (Fin.last c.1)⟩

lemma attach_count {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    (a.attach ρ b).2.1.count = a.count + b.count := by
  induction b with
  | input => simp [attach, count]
  | add b o ih => simp only [attach, count, ih, Nat.add_assoc]

lemma attach_width {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    (a.attach ρ b).1 = k + b.count := by
  have hw := (a.attach ρ b).2.1.width_eq
  rw [attach_count, ← Nat.add_assoc, ← a.width_eq] at hw
  exact hw

lemma attach_le {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m → Fin k) (b : BoolNet m l) :
    k ≤ (a.attach ρ b).1 := by rw [attach_width]; omega

end BoolNet

/-- Typed interfaces for network composition, with explicitly retained workspace. -/
structure BooleanNetwork (n m : ℕ) where
  width : ℕ
  net : BoolNet n width
  output : Fin m → Fin width


end ExactQuantumFactoring
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanNetworkFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring

namespace BooleanNetwork

def eval {n m : ℕ} (c : BooleanNetwork n m) (x : Fin n → Bool) : Fin m → Bool :=
  c.net.eval x ∘ c.output

def select {n m : ℕ} (f : Fin m → Fin n) : BooleanNetwork n m := ⟨n, .input, f⟩

def node {n : ℕ} (o : BoolNode n) : BooleanNetwork n 1 :=
  ⟨n+1, .add .input o, fun _ => Fin.last n⟩

def comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l) : BooleanNetwork n l :=
  let c := a.net.attach a.output b.net
  ⟨c.1, c.2.1, c.2.2 ∘ b.output⟩

lemma count_comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l) :
    (a.comp b).net.count = a.net.count + b.net.count := BoolNet.attach_count _ _ _

/-- Parallel computations share the input but retain disjoint new traces. -/
def pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l) : BooleanNetwork n (m+l) :=
  let ρ : Fin n → Fin a.width := fun i => i.castLE a.net.input_le
  let c := a.net.attach ρ b.net
  ⟨c.1, c.2.1, Fin.append (fun i => (a.output i).castLE (a.net.attach_le ρ b.net))
    (c.2.2 ∘ b.output)⟩

lemma count_pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l) :
    (a.pair b).net.count = a.net.count + b.net.count := BoolNet.attach_count _ _ _

@[simp] lemma eval_select {n m : ℕ} (f : Fin m → Fin n) (x : Fin n → Bool) :
    (select f).eval x = x ∘ f := rfl

@[simp] lemma count_select {n m : ℕ} (f : Fin m → Fin n) :
    (select f).net.count = 0 := rfl

@[simp] lemma eval_node {n : ℕ} (o : BoolNode n) (x : Fin n → Bool) (i : Fin 1) :
    (node o).eval x i = o.eval x := by
  exact BoolNet.eval_add_last _ _ _

@[simp] lemma count_node {n : ℕ} (o : BoolNode n) : (node o).net.count = 1 := rfl

end BooleanNetwork
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

/-- Wire routing is free: it refers to values already physically present. -/
def rewire {n m l : ℕ} (c : BooleanNetwork n m) (f : Fin l → Fin m) : BooleanNetwork n l :=
  ⟨c.width, c.net, c.output ∘ f⟩

@[simp] lemma eval_rewire {n m l : ℕ} (c : BooleanNetwork n m) (f : Fin l → Fin m)
    (x : Fin n → Bool) : (c.rewire f).eval x = c.eval x ∘ f := rfl

@[simp] lemma count_rewire {n m l : ℕ} (c : BooleanNetwork n m) (f : Fin l → Fin m) :
    (c.rewire f).net.count = c.net.count := rfl

def bit {n : ℕ} (i : Fin n) : BooleanNetwork n 1 := select (fun _ => i)
def constant {n : ℕ} (b : Bool) : BooleanNetwork n 1 := node (.constant b)
def bnot {n : ℕ} (a : BooleanNetwork n 1) : BooleanNetwork n 1 := a.comp (node (.neg 0))
def band {n : ℕ} (a b : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (a.pair b).comp (node (.conj 0 1))
def bor {n : ℕ} (a b : BooleanNetwork n 1) : BooleanNetwork n 1 := (a.bnot.band b.bnot).bnot
def bxor {n : ℕ} (a b : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (a.band b.bnot).bor (a.bnot.band b)
def mux {n : ℕ} (c a b : BooleanNetwork n 1) : BooleanNetwork n 1 :=
  (c.band a).bor (c.bnot.band b)

@[simp] lemma eval_bit {n : ℕ} (i : Fin n) (x : Fin n → Bool) (j : Fin 1) :
    (bit i).eval x j = x i := rfl

@[simp] lemma eval_constant {n : ℕ} (b : Bool) (x : Fin n → Bool) (j : Fin 1) :
    (constant b).eval x j = b := eval_node _ _ _

@[simp] lemma count_bit {n : ℕ} (i : Fin n) : (bit i).net.count = 0 := rfl
@[simp] lemma count_constant {n : ℕ} (b : Bool) : (constant (n := n) b).net.count = 1 := rfl
@[simp] lemma count_bnot {n : ℕ} (a : BooleanNetwork n 1) : a.bnot.net.count = a.net.count + 1 := by
  simp [bnot, count_comp]
@[simp] lemma count_band {n : ℕ} (a b : BooleanNetwork n 1) :
    (a.band b).net.count = a.net.count + b.net.count + 1 := by simp [band, count_comp, count_pair]
@[simp] lemma count_bor {n : ℕ} (a b : BooleanNetwork n 1) :
    (a.bor b).net.count = a.net.count + b.net.count + 4 := by simp [bor]; omega
@[simp] lemma count_bxor {n : ℕ} (a b : BooleanNetwork n 1) :
    (a.bxor b).net.count = 2 * a.net.count + 2 * b.net.count + 8 := by simp [bxor]; omega
@[simp] lemma count_mux {n : ℕ} (c a b : BooleanNetwork n 1) :
    (mux c a b).net.count = 2 * c.net.count + a.net.count + b.net.count + 7 := by simp [mux]; omega

/-- Logical assignment preserves the input values in the physical trace, but
provides the standard overwritten-state interface to the next computation. -/
def assign {n : ℕ} (i : Fin n) (v : BooleanNetwork n 1) : BooleanNetwork n n :=
  ((select id).pair v).rewire (fun j => if j = i then Fin.natAdd n 0 else j.castAdd 1)

@[simp] lemma count_assign {n : ℕ} (i : Fin n) (v : BooleanNetwork n 1) :
    (assign i v).net.count = v.net.count := by simp [assign, count_pair]

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


open scoped BigOperators
namespace ExactQuantumFactoring.BooleanNetwork

/-- Assemble an arbitrary vector of single-bit combinational outputs, retaining
separate traces. This is a finite circuit construction, not a truth table. -/
def vector {n : ℕ} : {m : ℕ} → (Fin m → BooleanNetwork n 1) → BooleanNetwork n m
  | 0, _ => select Fin.elim0
  | m+1, f => (vector (fun i => f i.castSucc)).pair (f (Fin.last m))

@[simp] lemma count_vector {n m : ℕ} (f : Fin m → BooleanNetwork n 1) :
    (vector f).net.count = ∑ i, (f i).net.count := by
  induction m with
  | zero => simp [vector]
  | succ m ih => simp [vector, count_pair, ih, Fin.sum_univ_castSucc]

lemma count_vector_le {n m c : ℕ} (f : Fin m → BooleanNetwork n 1)
    (h : ∀ i, (f i).net.count ≤ c) : (vector f).net.count ≤ m*c := by
  rw [count_vector]
  calc
    _ ≤ ∑ _ : Fin m, c := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

/-- Add explicit zero slots, with <=m nodes. Duplicate outputs may share zero,
but the simple linear upper bound is sufficient for the compiler. -/
def padRight (n m : ℕ) : BooleanNetwork n (n+m) :=
  vector (fun i => if h : i.val < n then bit ⟨i.val,h⟩ else constant false)

lemma count_padRight (n m : ℕ) : (padRight n m).net.count = m := by
  rw [padRight, count_vector, Fin.sum_univ_add]
  have h₁ : (∑ x : Fin n, (if h : x.val < n then bit (n := n) ⟨x.val,h⟩
      else constant false).net.count) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [dite_eq_left x.isLt]
    rfl
  have h₂ : (∑ x : Fin m, (if h : n+x.val < n then bit (n := n) ⟨n+x.val,h⟩
      else constant false).net.count) = m := by
    trans ∑ _ : Fin m, 1
    · apply Finset.sum_congr rfl
      intro x _
      rw [dite_eq_right (by omega : ¬ n+x.val < n)]
      rfl
    · simp
  exact (congrArg₂ (· + ·) h₁ h₂).trans (Nat.zero_add _)

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

open BooleanNetwork Std.Sat

namespace AIGCompiler

variable {n : ℕ} (g : AIG (Fin n))

def graphWire (i : Fin g.decls.size) : Fin (n + g.decls.size) := Fin.natAdd n i

def faninNet (f : AIG.Fanin) : BooleanNetwork (n + g.decls.size) 1 :=
  let v := if h : f.gate < g.decls.size then bit (graphWire g ⟨f.gate,h⟩) else constant false
  if f.invert then v.bnot else v

lemma fanin_count (f : AIG.Fanin) : (faninNet g f).net.count ≤ 2 := by
  have hv : (if h : f.gate < g.decls.size then bit (graphWire g ⟨f.gate,h⟩)
      else constant false : BooleanNetwork (n+g.decls.size) 1).net.count ≤ 1 := by
    by_cases h : f.gate < g.decls.size
    · rw [dite_eq_left h]; simp
    · rw [dite_eq_right h]; simp
  unfold faninNet
  generalize (if h : f.gate < g.decls.size then bit (graphWire g ⟨f.gate,h⟩)
      else constant false : BooleanNetwork (n+g.decls.size) 1) = v at *
  cases hf : f.invert
  · change v.net.count ≤ 2
    omega
  · change v.bnot.net.count ≤ 2
    rw [count_bnot]
    omega

def nodeNet (i : Fin g.decls.size) : BooleanNetwork (n+g.decls.size) 1 :=
  match g.decls[i.val] with
  | .false => constant false
  | .atom v => bit (Fin.castAdd g.decls.size v)
  | .gate a b => (faninNet g a).band (faninNet g b)

lemma node_count (i : Fin g.decls.size) : (nodeNet g i).net.count ≤ 5 := by
  unfold nodeNet
  cases g.decls[i.val] with
  | false => simp
  | atom v => simp
  | gate a b =>
    rw [count_band]
    have := fanin_count g a
    have := fanin_count g b
    omega

def nodeDenote (x : Fin n → Bool) (i : Fin g.decls.size) : Bool :=
  AIG.denote x ⟨g, ⟨i.val, false, i.isLt⟩⟩

def nodeStep (i : Fin g.decls.size) : BooleanNetwork (n+g.decls.size) (n+g.decls.size) :=
  assign (graphWire g i) (nodeNet g i)

def partialGraph (g : AIG (Fin n)) : (k : ℕ) → k ≤ g.decls.size →
    BooleanNetwork (n+g.decls.size) (n+g.decls.size)
  | 0, _ => select id
  | k+1, h => (partialGraph g k (by omega)).comp (nodeStep g ⟨k, by omega⟩)

lemma graph_count (k : ℕ) (h : k ≤ g.decls.size) : (partialGraph g k h).net.count ≤ 5*k := by
  induction k with
  | zero => simp [partialGraph]
  | succ k ih =>
    rw [partialGraph, count_comp, nodeStep, count_assign]
    have := node_count g ⟨k, by omega⟩
    have := ih (by omega)
    omega

/-- Compile designated references of an AIG, starting only with its input bits.
All graph slots and their retained evaluation traces are genuine ancillas. -/
def compile {m : ℕ} (refs : Fin m → AIG.Ref g) : BooleanNetwork n m :=
  ((padRight n g.decls.size).comp (partialGraph g g.decls.size le_rfl)).comp
    (vector (fun i => faninNet g (AIG.Fanin.mk (refs i).gate (refs i).invert)))

lemma compile_count {m : ℕ} (refs : Fin m → AIG.Ref g) :
    (compile g refs).net.count ≤ 6*g.decls.size + 2*m := by
  rw [compile, count_comp, count_comp, count_padRight]
  have hg := graph_count g g.decls.size le_rfl
  have hv := count_vector_le (fun i => faninNet g (AIG.Fanin.mk (refs i).gate (refs i).invert))
    (fun i => fanin_count g (AIG.Fanin.mk (refs i).gate (refs i).invert))
  omega

/-- The whole output BitVec of a native, already verified, arithmetic bitblaster
is now a Boolean network with a linear overhead in its AIG graph size. -/
def compileVec {w : ℕ} (refs : AIG.RefVec g w) : BooleanNetwork n w :=
  compile g (fun i => refs.get i.val i.isLt)

lemma compileVec_count {w : ℕ} (refs : AIG.RefVec g w) :
    (compileVec g refs).net.count ≤ 6*g.decls.size + 2*w := compile_count ..

end AIGCompiler
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGDivisionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGBounds
open Std.Sat Std.Tactic.BVDecide
open BVExpr.bitblast
variable {α : Type} [Hashable α] [DecidableEq α]

lemma not_go_size {w : ℕ} (aig : AIG α) (i : ℕ) (hi : i ≤ w)
    (s : AIG.RefVec aig i) (input : AIG.RefVec aig w) :
    (AIG.RefVec.map.go aig i hi s input AIG.mkNotCached).aig.decls.size = aig.decls.size := by
  rw [AIG.RefVec.map.go]
  split
  · dsimp only
    rw [not_go_size]
    rfl
  · rfl
termination_by w-i

lemma not_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w) :
    (blastNot aig input).aig.decls.size = aig.decls.size :=
  not_go_size ..

lemma neg_size {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w) :
    (blastNeg aig input).aig.decls.size ≤ aig.decls.size+12*w := by
  unfold blastNeg
  have h := add_size (blastNot aig input).aig
    ⟨(blastNot aig input).vec, blastConst (blastNot aig input).aig (1#w)⟩
  simpa only [not_size] using h

lemma sub_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastSub aig input).aig.decls.size ≤ aig.decls.size+24*w := by
  unfold blastSub
  dsimp only
  apply (add_size _ _).trans
  have h := neg_size aig input.rhs
  omega

lemma overflow_go_size {w : ℕ} (aig : AIG α) (lhs rhs : AIG.RefVec aig w)
    (curr : ℕ) (cin : AIG.Ref aig) :
    (mkOverflowBit.go aig lhs rhs curr cin).aig.decls.size ≤
      aig.decls.size+6*(w-curr) := by
  rw [mkOverflowBit.go]
  split
  next h =>
    dsimp only
    apply (overflow_go_size _ _ _ _ _).trans
    have hh := fullAdderCarry_size aig ⟨lhs.get curr h, rhs.get curr h, cin⟩
    omega
  · simp
termination_by w-curr

lemma overflow_size (aig : AIG α) (input : OverflowInput aig) :
    (mkOverflowBit aig input).aig.decls.size ≤ aig.decls.size+6*input.w :=
  overflow_go_size ..

lemma ult_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (BVPred.mkUlt aig input).aig.decls.size ≤ aig.decls.size+6*w := by
  unfold BVPred.mkUlt
  dsimp only
  change (mkOverflowBit _ _).aig.decls.size ≤ _
  apply (overflow_size _ _).trans
  simp only [not_size, le_refl]

lemma extend_go_size (aig : AIG α) (w : ℕ) (input : AIG.RefVec aig w)
    (newWidth curr : ℕ) (hcurr : curr ≤ newWidth) (s : AIG.RefVec aig curr) :
    (blastZeroExtend.go aig w input newWidth curr hcurr s).aig.decls.size = aig.decls.size := by
  rw [blastZeroExtend.go]
  split
  · dsimp only
    split <;> apply extend_go_size
  · rfl
termination_by newWidth-curr

lemma extend_size {w : ℕ} (aig : AIG α) (input : AIG.ExtendTarget aig w) :
    (blastZeroExtend aig input).aig.decls.size = aig.decls.size := extend_go_size ..

lemma shiftConcat_size {w : ℕ} (aig : AIG α) (input : blastUdiv.ShiftConcatInput aig w) :
    (blastUdiv.blastShiftConcat aig input).aig.decls.size = aig.decls.size := extend_size ..

lemma div_step_size {w : ℕ} (aig : AIG α) (n d : AIG.RefVec aig w)
    (wn wr : ℕ) (q r : AIG.RefVec aig w) :
    (blastUdiv.blastDivSubtractShift aig n d wn wr q r).aig.decls.size ≤
      aig.decls.size+36*w := by
  unfold blastUdiv.blastDivSubtractShift
  dsimp only
  apply (ite_size _ _).trans
  apply (Nat.add_le_add_right (ite_size _ _) (3*w)).trans
  apply (Nat.add_le_add_right (Nat.add_le_add_right (ult_size _ _) (3*w)) (3*w)).trans
  apply (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (sub_size _ _) (6*w)) (3*w)) (3*w)).trans
  simp only [shiftConcat_size]
  omega

lemma div_go_size {w : ℕ} (aig : AIG α) (curr : ℕ) (n d : AIG.RefVec aig w)
    (wn wr : ℕ) (q r : AIG.RefVec aig w) :
    (blastUdiv.go aig curr n d wn wr q r).aig.decls.size ≤ aig.decls.size+36*w*curr := by
  induction curr generalizing aig wn wr with
  | zero => simp [blastUdiv.go]
  | succ curr ih =>
    rw [blastUdiv.go]
    dsimp only
    apply (ih _ _ _ _ _ _ _).trans
    have h := div_step_size aig n d wn wr q r
    nlinarith

lemma beq_size (aig : AIG α) (input : AIG.BinaryInput aig) :
    (aig.mkBEqCached input).aig.decls.size ≤ aig.decls.size+3 := by
  unfold AIG.mkBEqCached
  dsimp only
  apply (cached_size _ _).trans
  apply (Nat.add_le_add_right (cached_size _ _) 1).trans
  apply (Nat.add_le_add_right (Nat.add_le_add_right (cached_size _ _) 1) 1).trans
  omega

lemma zip_go_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f] [AIG.RefVec.LawfulZipOperator α f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (idx : ℕ) (s : AIG.RefVec aig idx) (hi : idx ≤ w)
    (lhs rhs : AIG.RefVec aig w) :
    (AIG.RefVec.zip.go aig idx s hi lhs rhs f).aig.decls.size ≤ aig.decls.size+c*(w-idx) := by
  rw [AIG.RefVec.zip.go]
  split
  next h =>
    dsimp only
    apply (zip_go_size f c hf _ _ _ _ _ _).trans
    have hh := hf aig ⟨lhs.get idx h, rhs.get idx h⟩
    have he : w-idx = w-(idx+1)+1 := by omega
    rw [he]
    nlinarith
  · simp
termination_by w-idx

lemma zip_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f] [AIG.RefVec.LawfulZipOperator α f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (AIG.RefVec.zip aig input f).aig.decls.size ≤ aig.decls.size+c*w := zip_go_size f c hf aig 0 _ (by omega) input.lhs input.rhs

lemma fold_go_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (acc : AIG.Ref aig) (idx : ℕ) (input : AIG.RefVec aig w) :
    (AIG.RefVec.fold.go aig acc idx w input f).aig.decls.size ≤ aig.decls.size+c*(w-idx) := by
  rw [AIG.RefVec.fold.go]
  split
  next h =>
    dsimp only
    apply (fold_go_size f c hf _ _ _ _).trans
    have hh := hf aig ⟨acc, input.get idx h⟩
    have he : w-idx = w-(idx+1)+1 := by omega
    rw [he]
    nlinarith
  · simp
termination_by w-idx

lemma fold_size (f : (aig : AIG α) → AIG.BinaryInput aig → AIG.Entrypoint α)
    [AIG.LawfulOperator α AIG.BinaryInput f]
    (c : ℕ) (hf : ∀ aig input, (f aig input).aig.decls.size ≤ aig.decls.size+c)
    {w : ℕ} (aig : AIG α) (input : AIG.RefVec aig w) :
    (AIG.RefVec.fold aig input f).aig.decls.size ≤ aig.decls.size+c*w := fold_go_size f c hf aig (aig.mkConstCached true) 0 input

lemma eq_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (BVPred.mkEq aig input).aig.decls.size ≤ aig.decls.size+4*w := by
  unfold BVPred.mkEq
  dsimp only
  apply (fold_size _ 1 and_size _ _).trans
  have hh := zip_size _ 3 beq_size aig input
  omega

lemma mod_size {w : ℕ} (aig : AIG α) (input : AIG.BinaryRefVec aig w) :
    (blastUmod aig input).aig.decls.size ≤ aig.decls.size+36*w*w+7*w := by
  unfold blastUmod
  dsimp only
  apply (ite_size _ _).trans
  apply (Nat.add_le_add_right (div_go_size _ _ _ _ _ _ _ _) (3*w)).trans
  have hh := eq_size aig ⟨input.rhs, blastConst aig 0#w⟩
  omega

end ExactQuantumFactoring.AIGBounds


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.AIGCompiler
open Std.Sat

/-- One real AIG atom per input bit. The initial graph has one false node. -/
def inputsPrefix (n : ℕ) : (k : ℕ) → k ≤ n →
    (g : AIG (Fin n)) × (Fin k → AIG.Ref g)
  | 0, _ => ⟨AIG.empty, Fin.elim0⟩
  | k+1, h =>
    let old := inputsPrefix n k (by omega)
    let res := old.1.mkAtom ⟨k, by omega⟩
    ⟨res.aig, Fin.snoc (fun i => (old.2 i).cast (AIG.LawfulOperator.le_size (f := AIG.mkAtom) old.1 (⟨k, by omega⟩ : Fin n))) res.ref⟩

lemma inputsPrefix_size (n k : ℕ) (h : k ≤ n) : (inputsPrefix n k h).1.decls.size = k+1 := by
  induction k with
  | zero => simp [inputsPrefix, AIG.empty]
  | succ k ih => simp [inputsPrefix, AIG.mkAtom, ih]

def inputs (n : ℕ) := inputsPrefix n n le_rfl

lemma inputs_size (n : ℕ) : (inputs n).1.decls.size = n+1 := inputsPrefix_size ..

/-- A vector of ordinary references; this constructor emits no graph nodes. -/
def refVector {α : Type} [Hashable α] [DecidableEq α] {g : AIG α} {w : ℕ}
    (f : Fin w → AIG.Ref g) : AIG.RefVec g w where
  refs := Vector.ofFn (fun i => AIG.Fanin.mk (f i).gate (f i).invert)
  hrefs := by intro i hi; simpa using (f ⟨i,hi⟩).hgate

end ExactQuantumFactoring.AIGCompiler


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

inductive Program (K : Type) where
  | skip
  | push (k : K) (b : Bool)
  | seq (p q : Program K)
  | cases (k : K) (nil ff tt : Program K)
  | loop (k : K) (ff tt : Program K)

abbrev Store (K : Type) := K → List Bool

inductive Runs {K : Type} [DecidableEq K] : Program K → Store K → Store K → ℕ → Prop
  | skip (s) : Runs .skip s s 1
  | push (s) (k) (b) : Runs (.push k b) s (Function.update s k (b :: s k)) 1
  | seq {p q s t u a b} : Runs p s t a → Runs q t u b → Runs (.seq p q) s u (b+a)
  | cases_nil {k p q r s t a} : s k=[] → Runs p s t a → Runs (.cases k p q r) s t (a+1)
  | cases_false {k p q r s t xs a} : s k=false::xs →
      Runs q (Function.update s k xs) t a → Runs (.cases k p q r) s t (a+1)
  | cases_true {k p q r s t xs a} : s k=true::xs →
      Runs r (Function.update s k xs) t a → Runs (.cases k p q r) s t (a+1)
  | loop_nil {k p q s} : s k=[] → Runs (.loop k p q) s s 1
  | loop_false {k p q s t u xs a b} : s k=false::xs →
      Runs p (Function.update s k xs) t a → Runs (.loop k p q) t u b →
      Runs (.loop k p q) s u (b+a+1)
  | loop_true {k p q s t u xs a b} : s k=true::xs →
      Runs q (Function.update s k xs) t a → Runs (.loop k p q) t u b →
      Runs (.loop k p q) s u (b+a+1)

def singletonStore {K : Type} [DecidableEq K] (k : K) (v : List Bool) : Store K :=
  Function.update (fun _ => []) k v

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]

/-- Reverse one stack onto another, preserving all symbols. -/
def reverseMove (a b : K) : Program K := .loop a (.push b false) (.push b true)
def clear (a : K) : Program K := .loop a .skip .skip

def duplicateReverse (a b t : K) : Program K :=
  .seq (.loop a (.seq (.push b false) (.push t false))
    (.seq (.push b true) (.push t true))) (reverseMove t a)

lemma clear_runs (a : K) (s : Store K) :
    Runs (clear a) s (Function.update s a []) (2*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update s a []=s := by rw [←hs,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    have ht : Function.update s a xs a=xs := by simp
    have hh := ih (Function.update s a xs) ht
    cases x
    · have hr := Runs.loop_false hs (Runs.skip (Function.update s a xs)) hh
      convert hr using 1 <;> first | rfl | simp only [Function.update_idem]
    · have hr := Runs.loop_true hs (Runs.skip (Function.update s a xs)) hh
      convert hr using 1 <;> first | rfl | simp only [Function.update_idem]

lemma reverseMove_runs (a b : K) (hab : a≠b) (s : Store K) :
    Runs (reverseMove a b) s
      (Function.update (Function.update s a []) b ((s a).reverse++s b))
      (2*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update s a []) b ([].reverse++s b)=s := by
      rw [List.reverse_nil,List.nil_append,←hs,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let t := Function.update s a xs
    let u := Function.update t b (x::t b)
    have hua : u a=xs := by simp [u,t,hab]
    have htail := ih u hua
    have body : Runs (.push b x) t u 1 := Runs.push _ _ _
    have hr : Runs (reverseMove a b) s
        (Function.update (Function.update u a []) b (xs.reverse++u b)) (2*xs.length+1+1+1) := by
      cases x
      · exact Runs.loop_false (a:=1) (b:=2*xs.length+1) hs body htail
      · exact Runs.loop_true (a:=1) (b:=2*xs.length+1) hs body htail
    convert hr using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;>
      simp_all [u,t,Function.update,List.reverse_cons,List.append_assoc]

lemma duplicateReverse_loop_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) :
    Runs (.loop a (.seq (.push b false) (.push t false))
      (.seq (.push b true) (.push t true))) s
      (Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
        t ((s a).reverse++s t)) (3*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update (Function.update s a []) b ([].reverse++s b))
        t ([].reverse++s t)=s := by
      rw [List.reverse_nil,List.nil_append,List.nil_append,←hs,Function.update_eq_self,
        Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let u := Function.update s a xs
    let w := Function.update u b (x::u b)
    let v := Function.update w t (x::w t)
    have hva : v a=xs := by simp [v,w,u,hab,hat]
    have htail := ih v hva
    have body : Runs (.seq (.push b x) (.push t x)) u v 2 :=
      Runs.seq (Runs.push _ _ _) (Runs.push _ _ _)
    have hr : Runs (.loop a (.seq (.push b false) (.push t false))
      (.seq (.push b true) (.push t true))) s
      (Function.update (Function.update (Function.update v a []) b (xs.reverse++v b))
        t (xs.reverse++v t)) (3*xs.length+1+2+1) := by
      cases x
      · exact Runs.loop_false (a:=2) (b:=3*xs.length+1) hs body htail
      · exact Runs.loop_true (a:=2) (b:=3*xs.length+1) hs body htail
    convert hr using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht : k=t <;>
      simp_all [v,w,u,Function.update,List.reverse_cons,List.append_assoc]

lemma duplicateReverse_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) (ht : s t=[]) :
    Runs (duplicateReverse a b t) s (Function.update s b ((s a).reverse++s b))
      (5*(s a).length+2) := by
  let v := Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
    t ((s a).reverse++s t)
  have hr := reverseMove_runs t a hat.symm v
  have hh := Runs.seq (duplicateReverse_loop_runs a b t hab hat hbt s) hr
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht' : k=t <;>
      simp_all [v,Function.update]
  · simp only [v,Function.update_self,ht,List.append_nil,List.length_reverse]; omega

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

lemma Runs.length_le {p : Program K} {s t : Store K} {c : ℕ} (h : Runs p s t c) (k : K) :
    (t k).length ≤ (s k).length+c := by
  induction h with
  | skip s => omega
  | push s a b =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self,List.length_cons]; omega
    · simp only [Function.update_of_ne hk]; omega
  | seq hp hq ip iq => omega
  | cases_nil hs hr ih => omega
  | @cases_false a p q r s t xs c hs hr ih =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ih; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ih; omega
  | @cases_true a p q r s t xs c hs hr ih =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ih; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ih; omega
  | loop_nil hs => omega
  | @loop_false a p q s t u xs c d hs hp hq ip iq =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ip; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ip; omega
  | @loop_true a p q s t u xs c d hs hp hq ip iq =>
    by_cases hk : k=a
    · subst k; simp only [Function.update_self] at ip; rw [hs,List.length_cons]; omega
    · simp only [Function.update_of_ne hk] at ip; omega

/-- A completely explicit finite-state Boolean-stack subroutine, with the
same clean input/output convention as the frozen TM2 uniformity target. -/
structure Procedure {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  K : Type
  finiteK : Fintype K
  decideK : DecidableEq K
  input : K
  output : K
  program : Program K
  bound : Polynomial ℕ
  runs : ∀ a, ∃ c, c ≤ bound.eval (ea a).length ∧
    @Runs K decideK program (@singletonStore K decideK input (ea a)) (@singletonStore K decideK output (eb (f a))) c

attribute [instance] Procedure.finiteK Procedure.decideK
namespace Procedure
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

lemma output_length_le (p : Procedure ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length+p.bound.eval (ea a).length := by
  obtain ⟨c,hc,hr⟩ := p.runs a
  have h := hr.length_le p.output
  simp only [singletonStore,Function.update_self] at h
  by_cases he : p.output=p.input
  · simp only [he,Function.update_self] at h; omega
  · simp only [Function.update_of_ne he,List.length_nil,Nat.zero_add] at h; omega

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

variable {K L : Type}
def Program.relabel (f : K → L) : Program K → Program L
  | .skip => .skip
  | .push k b => .push (f k) b
  | .seq p q => .seq (p.relabel f) (q.relabel f)
  | .cases k p q r => .cases (f k) (p.relabel f) (q.relabel f) (r.relabel f)
  | .loop k p q => .loop (f k) (p.relabel f) (q.relabel f)

/-- An extension of a small register store with arbitrary untouched registers. -/
noncomputable def overlay (f : K ↪ L) (base : Store L) (s : Store K) : Store L := by
  classical
  exact fun j => if h : ∃ i, f i=j then s (Classical.choose h) else base j

lemma overlay_at (f : K ↪ L) (base : Store L) (s : Store K) (i : K) :
    overlay f base s (f i)=s i := by
  classical
  unfold overlay
  rw [dite_eq_left ⟨i,rfl⟩]
  congr 1
  apply f.injective
  exact Classical.choose_spec (show ∃ k, f k=f i from ⟨i,rfl⟩)

lemma overlay_outside (f : K ↪ L) (base : Store L) (s : Store K) (j : L)
    (h : ∀ i, f i≠j) : overlay f base s j=base j := by
  classical
  unfold overlay
  exact dite_eq_right (by simpa only [not_exists] using h)

variable [DecidableEq K] [DecidableEq L]

lemma overlay_update (f : K ↪ L) (base : Store L) (s : Store K) (k : K) (xs : List Bool) :
    overlay f base (Function.update s k xs)=Function.update (overlay f base s) (f k) xs := by
  funext j
  by_cases hj : ∃ i,f i=j
  · rcases hj with ⟨i,rfl⟩
    rw [overlay_at]
    by_cases h : i=k
    · subst i; simp
    · have hf : f i≠f k := fun h' => h (f.injective h')
      simp only [Function.update_of_ne h,Function.update_of_ne hf,overlay_at]
  · have h : ∀ i,f i≠j := by simpa only [not_exists] using hj
    rw [overlay_outside f base _ j h,Function.update_of_ne (Ne.symm (h k)),
      overlay_outside f base s j h]

/-- Exact-cost subroutine embedding. Scratch separation is proved, not assumed
as an extra TM operation. -/
lemma Runs.relabel {p : Program K} {s t : Store K} {c : ℕ}
    (h : Runs p s t c) (f : K ↪ L) (base : Store L) :
    Runs (p.relabel f) (overlay f base s) (overlay f base t) c := by
  induction h with
  | skip s => exact Runs.skip _
  | push s k b =>
    rw [overlay_update]
    simpa only [overlay_at, Program.relabel] using Runs.push (overlay f base s) (f k) b
  | seq hp hq ip iq => exact Runs.seq ip iq
  | @cases_nil k p q r s t a hs hr ih =>
    exact Runs.cases_nil (by rw [overlay_at,hs]) ih
  | @cases_false k p q r s t xs a hs hr ih =>
    rw [overlay_update] at ih
    exact Runs.cases_false (by rw [overlay_at,hs]) ih
  | @cases_true k p q r s t xs a hs hr ih =>
    rw [overlay_update] at ih
    exact Runs.cases_true (by rw [overlay_at,hs]) ih
  | @loop_nil k p q s hs => exact Runs.loop_nil (by rw [overlay_at,hs])
  | @loop_false k p q s t u xs a b hs hp hq ip iq =>
    rw [overlay_update] at ip
    exact Runs.loop_false (by rw [overlay_at,hs]) ip iq
  | @loop_true k p q s t u xs a b hs hp hq ip iq =>
    rw [overlay_update] at ip
    exact Runs.loop_true (by rw [overlay_at,hs]) ip iq
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K L : Type} [DecidableEq K] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
lemma overlay_empty (f : K ↪ L) : overlay f (fun _=>[]) (fun _=>[])=fun _=>[] := by
  funext j
  by_cases h : ∃ i,f i=j
  · rcases h with ⟨i,rfl⟩; exact overlay_at f _ _ i
  · exact overlay_outside f _ _ j (by simpa only [not_exists] using h)
lemma overlay_singleton (f : K ↪ L) (k : K) (xs : List Bool) :
    overlay f (fun _=>[]) (singletonStore k xs)=singletonStore (f k) xs := by
  rw [singletonStore,overlay_update,overlay_empty]
  rfl

/-- Move an entire word without reversing its order. Each symbol is pushed
and popped twice; this is not an atomic bulk-copy instruction. -/
def moveWord (a b t : K) : Program K := .seq (reverseMove a t) (reverseMove t b)
lemma moveWord_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t) (xs : List Bool) :
    Runs (moveWord a b t) (singletonStore a xs) (singletonStore b xs) (4*xs.length+2) := by
  let s := singletonStore a xs
  let u := Function.update (Function.update s a []) t ((s a).reverse++s t)
  have hh := Runs.seq (reverseMove_runs a t hat s) (reverseMove_runs t b hbt.symm u)
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht : k=t <;>
      simp_all [u,s,singletonStore,Function.update,Ne.symm hat,Ne.symm hab,Ne.symm hbt]
  · simp only [u,Function.update_self,s,singletonStore,Function.update_self]
    simp only [Function.update_of_ne hat.symm,List.append_nil,List.length_reverse]
    omega

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
  {f : α→β} {g : β→γ}

def joinLeft (A B : Type) : A ↪ A ⊕ (B ⊕ Unit) := ⟨Sum.inl,Sum.inl_injective⟩
def joinRight (A B : Type) : B ↪ A ⊕ (B ⊕ Unit) :=
  ⟨Sum.inr ∘ Sum.inl,Sum.inr_injective.comp Sum.inl_injective⟩

lemma eval_nat_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

/-- Checked composition for actual finite Boolean-stack procedures. This
constructs the combined program and accounts for the intermediate-word copy;
it does NOT invoke Mathlib's unproved TM2 polytime-composition declaration. -/
noncomputable def comp (q : Procedure eb ec g) (p : Procedure ea eb f) :
    Procedure ea ec (g ∘ f) where
  K := p.K ⊕ (q.K ⊕ Unit)
  finiteK := inferInstance
  decideK := inferInstance
  input := Sum.inl p.input
  output := Sum.inr (Sum.inl q.output)
  program := .seq (p.program.relabel (joinLeft p.K q.K))
    (.seq (moveWord (Sum.inl p.output) (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ())))
      (q.program.relabel (joinRight p.K q.K)))
  bound := p.bound+(Polynomial.C 4*(Polynomial.X+p.bound)+Polynomial.C 2)+
    q.bound.comp (Polynomial.X+p.bound)
  runs a := by
    obtain ⟨cp,hcp,hp⟩ := p.runs a
    obtain ⟨cq,hcq,hq⟩ := q.runs (f a)
    have hleft := hp.relabel (joinLeft p.K q.K) (fun _=>[])
    have hright := hq.relabel (joinRight p.K q.K) (fun _=>[])
    simp only [overlay_singleton] at hleft hright
    have hmove := moveWord_runs (K:=p.K ⊕ (q.K ⊕ Unit)) (Sum.inl p.output)
      (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ()))
      (by simp) (by simp) (by simp) (eb (f a))
    refine ⟨cq+(4*(eb (f a)).length+2)+cp,?_,Runs.seq hleft (Runs.seq hmove hright)⟩
    have hlen := p.output_length_le a
    have hmono := eval_nat_mono q.bound hlen
    dsimp only at hmono
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp]
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K L : Type}
def sumStore (s : Store K) (t : Store L) : Store (K ⊕ L) := Sum.elim s t
@[simp] lemma sumStore_left (s : Store K) (t : Store L) (k : K) :
    sumStore s t (Sum.inl k)=s k := rfl
@[simp] lemma sumStore_right (s : Store K) (t : Store L) (l : L) :
    sumStore s t (Sum.inr l)=t l := rfl
lemma sumStore_empty : sumStore (fun _ : K=>[]) (fun _ : L=>[])=fun _=>[] := by
  funext j; cases j <;> rfl

def leftEmbed (K L : Type) : K ↪ K ⊕ L := ⟨Sum.inl,Sum.inl_injective⟩
lemma overlay_left (s : Store K) (t : Store L) :
    overlay (leftEmbed K L) (sumStore (fun _=>[]) t) s=sumStore s t := by
  funext j
  cases j with
  | inl j => exact overlay_at _ _ _ j
  | inr j => exact overlay_outside _ _ _ _ (by intro i; simp [leftEmbed])

variable [DecidableEq K] [DecidableEq L]
@[simp] lemma sumStore_update_left (s : Store K) (t : Store L) (k : K) (xs : List Bool) :
    Function.update (sumStore s t) (Sum.inl k) xs=sumStore (Function.update s k xs) t := by
  funext j; cases j <;> simp [Function.update,sumStore]
@[simp] lemma sumStore_update_right (s : Store K) (t : Store L) (k : L) (xs : List Bool) :
    Function.update (sumStore s t) (Sum.inr k) xs=sumStore s (Function.update t k xs) := by
  funext j; cases j <;> simp [Function.update,sumStore]
lemma sumStore_singleton_left (k : K) (xs : List Bool) :
    singletonStore (Sum.inl k) xs=sumStore (singletonStore k xs) (fun _ : L=>[]) := by
  rw [singletonStore,←sumStore_empty,sumStore_update_left]; rfl
lemma Runs.left {p : Program K} {s u : Store K} {c : ℕ} (h : Runs p s u c) (t : Store L) :
    Runs (p.relabel Sum.inl) (sumStore s t) (sumStore u t) c := by
  have hh := h.relabel (leftEmbed K L) (sumStore (fun _=>[]) t)
  rw [overlay_left,overlay_left] at hh
  exact hh

namespace Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f g : α→β}
def congrFun (p : Procedure ea eb f) (h : ∀ a,f a=g a) : Procedure ea eb g where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [h a] using p.runs a

noncomputable def identity (ea : α→List Bool) : Procedure ea ea id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.skip
  bound:=1
  runs a:=⟨1,by simp,Runs.skip _⟩
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackQuotation
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_right _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

/-- Prefix-free quoting for one Boolean word. Both constructor tags and payload
bits are literal stack symbols. It is used only by the classical generator. -/
def quoteBits (xs : List Bool) : List Bool :=
  xs.flatMap (fun b=>[true,b]) ++ [false]
@[simp] lemma quoteBits_nil : quoteBits []=[false] := rfl
@[simp] lemma quoteBits_cons (b : Bool) (xs : List Bool) :
    quoteBits (b::xs)=true::b::quoteBits xs := rfl
lemma quoteBits_length (xs : List Bool) : (quoteBits xs).length=2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [quoteBits_cons,List.length_cons,ih]; omega

def pairBits (xs ys : List Bool) : List Bool := quoteBits xs++ys
lemma pairBits_length (xs ys : List Bool) :
    (pairBits xs ys).length=2*xs.length+ys.length+1 := by
  simp only [pairBits,List.length_append,quoteBits_length]; omega

variable {K : Type} [DecidableEq K]
def quoteLoop (a t : K) : Program K :=
  .loop a (.seq (.push t true) (.push t false)) (.seq (.push t true) (.push t true))
def quoteMove (a b t : K) : Program K :=
  .seq (quoteLoop a t) (.seq (.push t false) (reverseMove t b))

lemma quoteLoop_runs (a t : K) (hat : a≠t) (s : Store K) :
    Runs (quoteLoop a t) s
      (Function.update (Function.update s a []) t
        (((s a).flatMap (fun b=>[true,b])).reverse++s t)) (3*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have h : Function.update (Function.update s a []) t
        (([].flatMap (fun b=>[true,b])).reverse++s t)=s := by
      simp only [List.flatMap_nil,List.reverse_nil,List.nil_append]
      rw [←hs,Function.update_eq_self,Function.update_eq_self]
    rw [h]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let u := Function.update s a xs
    let v := Function.update u t (x::true::u t)
    have hva : v a=xs := by simp [v,u,hat]
    have hb : Runs (.seq (.push t true) (.push t x)) u v 2 := by
      have hh := Runs.seq (Runs.push u t true)
        (Runs.push (Function.update u t (true::u t)) t x)
      simpa only [Function.update_self,Function.update_idem] using hh
    have hh : Runs (quoteLoop a t) s
        (Function.update (Function.update v a []) t
          ((xs.flatMap (fun b=>[true,b])).reverse++v t)) (3*xs.length+1+2+1) := by
      cases x
      · exact Runs.loop_false (a:=2) (b:=3*xs.length+1) hs hb (ih v hva)
      · exact Runs.loop_true (a:=2) (b:=3*xs.length+1) hs hb (ih v hva)
    convert hh using 1
    · funext k
      by_cases ha : k=a <;> by_cases ht : k=t <;>
        simp_all [v,u,Function.update,List.reverse_cons,List.append_assoc]
    · first | omega | (simp only [List.length_cons, List.length_nil]; try omega)

lemma quoteMove_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) (ht : s t=[]) :
    Runs (quoteMove a b t) s
      (Function.update (Function.update s a []) b (quoteBits (s a)++s b))
      (7*(s a).length+5) := by
  let u := Function.update (Function.update s a []) t
    (((s a).flatMap (fun b=>[true,b])).reverse++s t)
  let v := Function.update u t (false::u t)
  have hh := Runs.seq (quoteLoop_runs a t hat s)
    (Runs.seq (Runs.push u t false) (reverseMove_runs t b hbt.symm v))
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht' : k=t <;>
      simp_all [u,v,Function.update,quoteBits,Ne.symm hat,Ne.symm hab,Ne.symm hbt]
  · simp only [v,Function.update_self,u,Function.update_self,ht,List.append_nil,
      List.length_cons,List.length_reverse]
    have hl : ((s a).flatMap (fun b=>[true,b])).length=2*(s a).length := by
      have h:=quoteBits_length (s a)
      simp only [quoteBits,List.length_append,List.length_cons,List.length_nil] at h
      omega
    rw [hl]; omega

def unquoteBody (a t c : K) : Program K :=
  .cases a .skip .skip
    (.cases a .skip (.seq (.push t false) (.push c true))
      (.seq (.push t true) (.push c true)))
def unquoteLoop (a t c : K) : Program K :=
  .loop c (unquoteBody a t c) (unquoteBody a t c)
def unquoteMove (a b t c : K) : Program K :=
  .seq (.push c true) (.seq (unquoteLoop a t c) (reverseMove t b))

lemma unquoteLoop_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (xs ys : List Bool) (s : Store K) (ha : s a=quoteBits xs++ys) (hc : s c=[true]) :
    Runs (unquoteLoop a t c) s
      (Function.update (Function.update (Function.update s a ys) c []) t (xs.reverse++s t))
      (5*xs.length+4) := by
  induction xs generalizing s with
  | nil =>
    let u := Function.update s c []
    let v := Function.update u a ys
    have hua : u a=false::ys := by simp [u,hac,ha]
    have hvc : v c=[] := by simp [v,u,hac.symm]
    have hb : Runs (unquoteBody a t c) u v 2 := Runs.cases_false hua (Runs.skip v)
    have hh := Runs.loop_true (p:=unquoteBody a t c) hc hb (Runs.loop_nil hvc)
    change Runs (.loop _ _ _) _ _ _
    convert hh using 1
    · funext k
      by_cases ha' : k=a <;> by_cases hc' : k=c <;> by_cases ht' : k=t <;>
        simp_all [v,u,Function.update,Ne.symm hat,Ne.symm hac,Ne.symm htc]
    · first | omega | (simp only [List.length_cons, List.length_nil]; try omega)
  | cons x xs ih =>
    let u := Function.update s c []
    let v := Function.update u a (x::quoteBits xs++ys)
    let w := Function.update v a (quoteBits xs++ys)
    let z := Function.update (Function.update w t (x::w t)) c [true]
    have hua : u a=true::x::quoteBits xs++ys := by simp [u,hac,ha]
    have hva : v a=x::quoteBits xs++ys := by simp [v]
    have hzc : z c=[true] := by simp [z]
    have hza : z a=quoteBits xs++ys := by simp [z,w,v,hat,hac]
    have hb : Runs (unquoteBody a t c) u z 4 := by
      apply Runs.cases_true hua
      have hh := Runs.seq (Runs.push w t x)
        (Runs.push (Function.update w t (x::w t)) c true)
      have hc0 : Function.update w t (x::w t) c=[] := by simp [w,v,u,htc.symm,hac.symm]
      rw [hc0] at hh
      cases x
      · exact Runs.cases_false hva hh
      · exact Runs.cases_true hva hh
    have hh := Runs.loop_true hc hb (ih z hza hzc)
    change Runs (.loop _ _ _) _ _ _
    convert hh using 1
    · funext k
      by_cases ha' : k=a <;> by_cases hc' : k=c <;> by_cases ht' : k=t <;>
        simp_all [z,w,v,u,Function.update,Ne.symm hat,Ne.symm hac,Ne.symm htc,
          List.reverse_cons,List.append_assoc]
    · first | omega | (simp only [List.length_cons, List.length_nil]; try omega)

lemma unquoteMove_runs (a b t c : K) (hab : a≠b) (hat : a≠t) (hac : a≠c)
    (hbt : b≠t) (hbc : b≠c) (htc : t≠c)
    (xs ys : List Bool) (s : Store K) (ha : s a=quoteBits xs++ys)
    (ht : s t=[]) (hc : s c=[]) :
    Runs (unquoteMove a b t c) s
      (Function.update (Function.update s a ys) b (xs++s b)) (7*xs.length+6) := by
  let u := Function.update s c [true]
  let v := Function.update (Function.update (Function.update u a ys) c []) t (xs.reverse++u t)
  have hua : u a=quoteBits xs++ys := by simp [u,hac,ha]
  have huc : u c=[true] := by simp [u]
  have hp : Runs (.push c true) s u 1 := by simpa only [hc] using Runs.push s c true
  have hh := Runs.seq hp (Runs.seq (unquoteLoop_runs a t c hat hac htc xs ys u hua huc)
    (reverseMove_runs t b hbt.symm v))
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha' : k=a <;> by_cases hb' : k=b <;> by_cases ht' : k=t <;> by_cases hc' : k=c <;>
      simp_all [v,u,Function.update,Ne.symm hab,Ne.symm hat,Ne.symm hac,Ne.symm hbt,
        Ne.symm hbc,Ne.symm htc]
  · simp only [v,Function.update_self,u,Function.update_of_ne htc,ht,List.append_nil,
      List.length_reverse]; omega
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def prodCode {α β : Type} (ea : α→List Bool) (eb : β→List Bool) (x : α×β) : List Bool :=
  pairBits (ea x.1) (eb x.2)

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool} {f : α→β}

/-- Run a procedure on the first component, keeping the second component
literally on a disjoint stack. Parsing and re-quoting are explicitly charged. -/
noncomputable def left (p : Procedure ea eb f) (ec : γ→List Bool) :
    Procedure (prodCode ea ec) (prodCode eb ec) (fun x=>(f x.1,x.2)) where
  K:=p.K ⊕ Fin 3
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (unquoteMove (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1) (Sum.inr 2))
    (.seq (p.program.relabel Sum.inl)
      (quoteMove (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 14*Polynomial.X+Polynomial.C 8*p.bound+Polynomial.C 11
  runs x:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs x.1
    let s : Store (p.K ⊕ Fin 3):=singletonStore (Sum.inr 0) (prodCode ea ec x)
    let u : Store (p.K ⊕ Fin 3):=sumStore (singletonStore p.input (ea x.1))
      (singletonStore 0 (ec x.2))
    let v : Store (p.K ⊕ Fin 3):=sumStore (singletonStore p.output (eb (f x.1)))
      (singletonStore 0 (ec x.2))
    have hparse : Runs (unquoteMove (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1) (Sum.inr 2))
        s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (Sum.inr 0 : p.K ⊕ Fin 3) (Sum.inl p.input)
        (Sum.inr 1) (Sum.inr 2) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (ea x.1) (ec x.2) s (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext k
      cases k with
      | inl k => by_cases hk : k=p.input <;> simp_all [s,u,singletonStore,sumStore,Function.update]
      | inr k => fin_cases k <;> simp [s,u,singletonStore,sumStore,Function.update]
    have hcall : Runs (p.program.relabel Sum.inl) u v cp := hp.left (singletonStore (0 : Fin 3) (ec x.2))
    have hquote : Runs (quoteMove (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)) v
        (singletonStore (Sum.inr 0) (pairBits (eb (f x.1)) (ec x.2)))
        (7*(eb (f x.1)).length+5) := by
      have hh:=quoteMove_runs (Sum.inl p.output : p.K ⊕ Fin 3)
        (Sum.inr 0) (Sum.inr 1) (by simp) (by simp) (by simp) v (by simp [v,singletonStore])
      convert hh using 1
      · funext k
        cases k with
        | inl k => by_cases hk : k=p.output <;>
            simp_all [v,singletonStore,sumStore,Function.update]
        | inr k => fin_cases k <;> simp [v,singletonStore,sumStore,Function.update,pairBits]
      · simp [v,singletonStore]
    refine ⟨(7*(eb (f x.1)).length+5)+cp+(7*(ea x.1).length+6),?_,
      Runs.seq hparse (Runs.seq hcall hquote)⟩
    have hlen:=p.output_length_le x.1
    have hx : (ea x.1).length≤(prodCode ea ec x).length := by
      simp only [prodCode,pairBits_length]; omega
    have hm:=eval_nat_mono p.bound hx
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

/-- Exchange two quoted word fields, without a unit-cost tuple operation. -/
noncomputable def swap (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) (prodCode eb ea) Prod.swap where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.seq (unquoteMove 0 1 2 3) (quoteMove 0 1 2)
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 11
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode ea eb x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 (eb x.2)) 1 (ea x.1)
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (ea x.1) (eb x.2) s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext k; fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (quoteMove 0 1 2) u (singletonStore 1 (prodCode eb ea x.swap))
        (7*(eb x.2).length+5) := by
      have hh:=quoteMove_runs (0 : Fin 4) 1 2 (by decide) (by decide) (by decide) u
        (by simp [u,singletonStore])
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,singletonStore,Function.update,prodCode,pairBits]
      · simp [u,singletonStore]
    refine ⟨(7*(eb x.2).length+5)+(7*(ea x.1).length+6),?_,Runs.seq h1 h2⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length]
    omega

/-- Two arbitrary already verified subroutines acting independently on a pair. -/
noncomputable def parallel {δ : Type} {ed : δ→List Bool} {g : γ→δ}
    (p : Procedure ea eb f) (q : Procedure ec ed g) :
    Procedure (prodCode ea ec) (prodCode eb ed) (fun x=>(f x.1,g x.2)) :=
  (((swap ed eb).comp ((q.left eb).comp ((swap eb ec).comp (p.left ec)))).congrFun
    (by intro x; rfl))
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α : Type} {ea : α→List Bool} {f : α→α}

/-- Return the result to one fixed public register. Both word movements are
implemented by two reversals; no output-to-input renaming is a TM operation. -/
noncomputable def inplace (p : Procedure ea ea f) : Procedure ea ea f where
  K:=p.K ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (moveWord (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1))
    (.seq (p.program.relabel Sum.inl)
      (moveWord (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 8*Polynomial.X+Polynomial.C 5*p.bound+Polynomial.C 4
  runs a:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs a
    have h1:=moveWord_runs (Sum.inr 0 : p.K ⊕ Fin 2) (Sum.inl p.input) (Sum.inr 1)
      (by simp) (by simp) (by simp) (ea a)
    have h2:=hp.relabel (leftEmbed p.K (Fin 2)) (fun _=>[])
    simp only [overlay_singleton] at h2
    have h3:=moveWord_runs (Sum.inl p.output : p.K ⊕ Fin 2) (Sum.inr 0) (Sum.inr 1)
      (by simp) (by simp) (by simp) (ea (f a))
    refine ⟨(4*(ea (f a)).length+2)+cp+(4*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    have hl:=p.output_length_le a
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

/-- Literal repetition of an in-place subroutine by a unary counter. Each
iteration consumes one control token; the bound charges every subroutine step. -/
lemma iterate_loop_runs {L : Type} [DecidableEq L] (p : Procedure ea ea f)
    (he : p.output=p.input) (k : L) (n : ℕ) (a : α) (B : ℕ)
    (hm : ∀ i≤n,(ea ((f^[i]) a)).length≤B) (s : Store L)
    (hs : s k=List.replicate n true) :
    ∃ c,c≤n*(p.bound.eval B+1)+1 ∧
      Runs (.loop (Sum.inr k) (p.program.relabel Sum.inl) (p.program.relabel Sum.inl))
        (sumStore (singletonStore p.input (ea a)) s)
        (sumStore (singletonStore p.input (ea ((f^[n]) a))) (Function.update s k [])) c := by
  induction n generalizing a s with
  | zero =>
    have hk : Function.update s k []=s := by
      simp only [List.replicate_zero] at hs
      rw [←hs,Function.update_eq_self]
    refine ⟨1,by simp,?_⟩
    rw [Function.iterate_zero_apply,hk]
    apply Runs.loop_nil
    exact hs
  | succ n ih =>
    let t:=Function.update s k (List.replicate n true)
    have ht : t k=List.replicate n true:=by simp [t]
    have hm' : ∀ i≤n,(ea ((f^[i]) (f a))).length≤B := by
      intro i hi
      simpa only [Function.iterate_succ_apply] using hm (i+1) (by omega)
    obtain ⟨ct,hct,hrt⟩:=ih (f a) hm' t ht
    obtain ⟨cp,hcp,hrp⟩:=p.runs a
    rw [he] at hrp
    have hcall:=hrp.left t
    have hcpB : cp≤p.bound.eval B:=
      hcp.trans (eval_nat_mono p.bound (by simpa using hm 0 (by omega)))
    have hhead : sumStore (singletonStore p.input (ea a)) s (Sum.inr k)=
        true::List.replicate n true := by simpa only [sumStore_right,List.replicate_succ] using hs
    have hbody : Runs (p.program.relabel Sum.inl)
        (Function.update (sumStore (singletonStore p.input (ea a)) s)
          (Sum.inr k) (List.replicate n true))
        (sumStore (singletonStore p.input (ea (f a))) t) cp := by
      simpa only [sumStore_update_right] using hcall
    have hh:=Runs.loop_true hhead hbody hrt
    refine ⟨ct+cp+1,?_,?_⟩
    · nlinarith
    · simpa only [t,Function.update_idem,Function.iterate_succ_apply] using hh

/-- Input-length-bounded iteration. The extra hypothesis is solely a size
invariant along the already implemented iteration, not a computability oracle. -/
noncomputable def iterate (p : Procedure ea ea f) (q : Polynomial ℕ)
    (hgrowth : ∀ n a i,i≤n→(ea ((f^[i]) a)).length≤q.eval (n+(ea a).length)) :
    Procedure (prodCode (fun n=>List.replicate n true) ea) ea (fun x=>(f^[x.1]) x.2) where
  K:=p.inplace.K ⊕ Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inl p.inplace.input
  program:=.seq (unquoteMove (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))
    (.seq (moveWord (Sum.inr 0) (Sum.inl p.inplace.input) (Sum.inr 2))
      (.loop (Sum.inr 1) (p.inplace.program.relabel Sum.inl) (p.inplace.program.relabel Sum.inl)))
  bound:=Polynomial.C 11*Polynomial.X+
    Polynomial.X*(p.inplace.bound.comp q+1)+Polynomial.C 9
  runs x:=by
    let r:=p.inplace
    let s : Store (r.K ⊕ Fin 4):=singletonStore (Sum.inr 0)
      (prodCode (fun n=>List.replicate n true) ea x)
    let u : Store (r.K ⊕ Fin 4):=Function.update (singletonStore (Sum.inr 0) (ea x.2))
      (Sum.inr 1) (List.replicate x.1 true)
    let v : Store (r.K ⊕ Fin 4):=sumStore (singletonStore r.input (ea x.2))
      (singletonStore 1 (List.replicate x.1 true))
    have hparse : Runs (unquoteMove (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)) s u
        (7*x.1+6) := by
      have hh:=unquoteMove_runs (Sum.inr 0 : r.K ⊕ Fin 4) (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (List.replicate x.1 true) (ea x.2) s (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      · funext k; cases k with
        | inl k => simp [s,u,singletonStore,Function.update]
        | inr k => fin_cases k <;> simp [s,u,singletonStore,Function.update]
      · simp
    have hmove : Runs (moveWord (Sum.inr 0) (Sum.inl r.input) (Sum.inr 2)) u v
        (4*(ea x.2).length+2) := by
      let emb : Fin 3 ↪ r.K ⊕ Fin 4 :=
        ⟨fun k=>if k=0 then Sum.inr 0 else if k=1 then Sum.inl r.input else Sum.inr 2,
          by intro a b; fin_cases a <;> fin_cases b <;> simp⟩
      have emb0 : emb 0=Sum.inr 0 := rfl
      have emb1 : emb 1=Sum.inl r.input := rfl
      have emb2 : emb 2=Sum.inr 2 := rfl
      have hh:=(moveWord_runs (0 : Fin 3) 1 2 (by decide) (by decide) (by decide) (ea x.2)).relabel
        emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
      -- A framed move has the counter outside its three touched registers.
      have hs' : overlay emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
          (singletonStore 0 (ea x.2))=u := by
        funext k
        cases k with
        | inl k =>
          by_cases hk : k=r.input
          · subst k
            have h:=overlay_at emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
              (singletonStore 0 (ea x.2)) 1
            simpa [emb0,emb1,emb2,u,singletonStore] using h
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2,Ne.symm hk])]
            simp [u,singletonStore]
        | inr k =>
          fin_cases k
          · simpa [emb0,emb1,emb2,u,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 0 (ea x.2)) 0
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [u,singletonStore]
          · simpa [emb0,emb1,emb2,u,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 0 (ea x.2)) 2
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [u,singletonStore]
      have ht' : overlay emb (singletonStore (Sum.inr 1) (List.replicate x.1 true))
          (singletonStore 1 (ea x.2))=v := by
        funext k
        cases k with
        | inl k =>
          by_cases hk : k=r.input
          · subst k
            simpa [emb0,emb1,emb2,v,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 1 (ea x.2)) 1
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2,Ne.symm hk])]
            simp [v,singletonStore,hk]
        | inr k =>
          fin_cases k
          · simpa [emb0,emb1,emb2,v,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 1 (ea x.2)) 0
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [v,singletonStore]
          · simpa [emb0,emb1,emb2,v,singletonStore] using overlay_at emb
              (singletonStore (Sum.inr 1) (List.replicate x.1 true)) (singletonStore 1 (ea x.2)) 2
          · rw [overlay_outside _ _ _ _ (by intro i; fin_cases i <;> simp [emb0,emb1,emb2])]
            simp [v,singletonStore]
      rw [hs',ht'] at hh
      simpa [moveWord,reverseMove,Program.relabel,emb0,emb1,emb2] using hh
    obtain ⟨cl,hcl,hl⟩:=iterate_loop_runs r rfl (1 : Fin 4) x.1 x.2
      (q.eval (x.1+(ea x.2).length)) (hgrowth x.1 x.2)
      (singletonStore 1 (List.replicate x.1 true)) (by simp [singletonStore])
    have hfinal : sumStore (singletonStore r.input (ea ((f^[x.1]) x.2)))
        (Function.update (singletonStore (1 : Fin 4) (List.replicate x.1 true)) 1 [])=
        singletonStore (Sum.inl r.input) (ea ((f^[x.1]) x.2)) := by
      rw [sumStore_singleton_left]
      congr 1
      funext k; fin_cases k <;> simp [singletonStore,Function.update]
    rw [hfinal] at hl
    refine ⟨cl+(4*(ea x.2).length+2)+(7*x.1+6),?_,
      Runs.seq hparse (Runs.seq hmove hl)⟩
    let L:=(prodCode (fun n=>List.replicate n true) ea x).length
    have hx : x.1+(ea x.2).length≤L:=by simp only [L,prodCode,pairBits_length,List.length_replicate]; omega
    have hm:=eval_nat_mono r.bound (eval_nat_mono q hx)
    dsimp only at hm
    have hmul:=Nat.mul_le_mul (by omega : x.1≤L) (Nat.add_le_add_right hm 1)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_one,Polynomial.eval_comp]
    change cl+(4*(ea x.2).length+2)+(7*x.1+6)≤11*L+L*(r.bound.eval (q.eval L)+1)+9
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackConstants
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_right _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]
/-- A fixed finite list is part of the program, not a run-time oracle. -/
def pushWord (k : K) : List Bool→Program K
  | []=>.skip
  | b::bs=>.seq (pushWord k bs) (.push k b)
lemma pushWord_runs (k : K) (xs : List Bool) (s : Store K) :
    Runs (pushWord k xs) s (Function.update s k (xs++s k)) (xs.length+1) := by
  induction xs with
  | nil=>simpa [pushWord] using Runs.skip s
  | cons b bs ih=>
    have hh:=Runs.seq ih (Runs.push (Function.update s k (bs++s k)) k b)
    simpa only [pushWord,Function.update_self,Function.update_idem,List.cons_append,
      List.length_cons,Nat.add_comm] using hh
namespace Procedure
variable {α β : Type} (ea : α→List Bool) (eb : β→List Bool)
noncomputable def constant (b : β) : Procedure ea eb (fun _=>b) where
  K:=Fin 1
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=.seq (clear 0) (pushWord 0 (eb b))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C ((eb b).length+2)
  runs a:=by
    let s : Store (Fin 1):=singletonStore 0 (ea a)
    let u : Store (Fin 1):=Function.update s 0 []
    have hc:=clear_runs (0 : Fin 1) s
    have hp:=pushWord_runs (0 : Fin 1) (eb b) u
    have hh:=Runs.seq hc hp
    refine ⟨((eb b).length+1)+(2*(ea a).length+1),by simp;omega,?_⟩
    convert hh using 1
    · funext k;fin_cases k;simp [u,s,singletonStore]
    · simp [s,singletonStore]

/-- Count each actual symbol, returning a unary length. -/
noncomputable def length : Procedure (id : List Bool→List Bool)
    (fun n=>List.replicate n true) List.length where
  K:=Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.loop 0 (.push 1 true) (.push 1 true)
  bound:=Polynomial.C 2*Polynomial.X+1
  runs xs:=by
    have h : ∀ xs (s : Store (Fin 2)),s 0=xs→
        Runs (.loop 0 (.push 1 true) (.push 1 true)) s
          (Function.update (Function.update s 0 []) 1 (List.replicate xs.length true++s 1))
          (2*xs.length+1) := by
      intro ys; induction ys with
      | nil=>
        intro s hs
        have he : Function.update (Function.update s 0 []) 1
            (List.replicate ([] : List Bool).length true++s 1)=s := by
          simp only [List.length_nil,List.replicate_zero,List.nil_append]
          rw [←hs,Function.update_eq_self,Function.update_eq_self]
        rw [he];exact Runs.loop_nil hs
      | cons y ys ih=>
        intro s hs
        let u:=Function.update s 0 ys
        let v:=Function.update u 1 (true::u 1)
        have hv : v 0=ys:=by simp [v,u]
        have htail:=ih v hv
        have hh : Runs (.loop 0 (.push 1 true) (.push 1 true)) s
            (Function.update (Function.update v 0 []) 1 (List.replicate ys.length true++v 1))
            (2*ys.length+1+1+1) := by
          cases y
          · exact Runs.loop_false (a:=1) (b:=2*ys.length+1) hs (Runs.push u 1 true) htail
          · exact Runs.loop_true (a:=1) (b:=2*ys.length+1) hs (Runs.push u 1 true) htail
        convert hh using 1
        · funext k;fin_cases k <;> simp [u,v,Function.update,List.replicate_succ]
          rw [←List.cons_append,←List.replicate_succ,List.replicate_succ',List.append_assoc]
          rfl
        · first | omega | (simp only [List.length_cons, List.length_nil]; try omega)
    refine ⟨2*xs.length+1,by simp,?_⟩
    convert h xs (singletonStore 0 xs) (by simp [singletonStore]) using 1 <;>
      (funext k;fin_cases k <;> simp [singletonStore,Function.update])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def leftPublic (K L : Type) : (K ⊕ Fin 2) ↪ ((K ⊕ L) ⊕ Fin 2) where
  toFun := fun k=>match k with | .inl i=>.inl (.inl i) | .inr i=>.inr i
  inj' := by intro i j h; cases i <;> cases j <;> simp_all

def rightPublic (K L : Type) : (L ⊕ Fin 2) ↪ ((K ⊕ L) ⊕ Fin 2) where
  toFun := fun k=>match k with | .inl i=>.inl (.inr i) | .inr i=>.inr i
  inj' := by intro i j h; cases i <;> cases j <;> simp_all

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {f g : α→β}
/-- A same-wire interface, even when the input and output word encodings differ. -/
noncomputable abbrev shared (p : Procedure ea eb f) : Procedure ea eb f where
  K:=p.K ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (moveWord (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1))
    (.seq (p.program.relabel Sum.inl)
      (moveWord (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 8*Polynomial.X+Polynomial.C 5*p.bound+Polynomial.C 4
  runs a:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs a
    have h1:=moveWord_runs (Sum.inr 0 : p.K ⊕ Fin 2) (Sum.inl p.input) (Sum.inr 1)
      (by simp) (by simp) (by simp) (ea a)
    have h2:=hp.relabel (leftEmbed p.K (Fin 2)) (fun _=>[])
    simp only [overlay_singleton] at h2
    have h3:=moveWord_runs (Sum.inl p.output : p.K ⊕ Fin 2) (Sum.inr 0) (Sum.inr 1)
      (by simp) (by simp) (by simp) (eb (f a))
    refine ⟨(4*(eb (f a)).length+2)+cp+(4*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    have hl:=p.output_length_le a
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

/-- Reinterpret the domain, with its entire previous encoding still on tape. -/
def precompose (p : Procedure ea eb f) (h : γ→α) :
    Procedure (fun a=>ea (h a)) eb (fun a=>f (h a)) where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=p.runs (h a)

def congrEncoding (p : Procedure ea eb f) {ec : α→List Bool} {ed : β→List Bool}
    (ha : ∀a,ea a=ec a) (hb : ∀b,eb b=ed b) : Procedure ec ed f where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [ha,hb] using p.runs a

/-- Change the mathematical output only when its *actual encoded word* agrees. -/
def result (p : Procedure ea eb f) {ec : γ→List Bool} {h : α→γ}
    (hr : ∀a,eb (f a)=ec (h a)) : Procedure ea ec h where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [hr a] using p.runs a

noncomputable def unprefix (ea : α→List Bool) (b : Bool) :
    Procedure (fun a=>b::ea a) ea id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip .skip .skip
  bound:=Polynomial.C 2
  runs a:=by
    refine ⟨2,by simp,?_⟩
    have hu : Function.update (singletonStore () (b::ea a)) () (ea a)=
        singletonStore () (ea a):=by simp [singletonStore]
    cases b
    · exact hu ▸ Runs.cases_false (by simp [singletonStore]) (Runs.skip _)
    · exact hu ▸ Runs.cases_true (by simp [singletonStore]) (Runs.skip _)

noncomputable def chooseBit (p : Procedure ea eb f) (q : Procedure ea eb g) :
    Procedure (fun x : Bool×α=>x.1::ea x.2) eb (fun x=>if x.1 then g x.2 else f x.2) where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs x:=by
    rcases x with ⟨b,a⟩
    have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
    have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (ea a).length)
    cases b
    · obtain ⟨c,hc,hd⟩:=p.shared.runs a
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hpmono).trans (Nat.le_add_right _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    · obtain ⟨c,hc,hd⟩:=q.shared.runs a
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hqmono).trans (Nat.le_add_left _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (true::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)

abbrev boolCode (b : Bool) : List Bool := [b]
noncomputable def choose (p : Procedure ea eb f) (q : Procedure ea eb g) :
    Procedure (prodCode boolCode ea) eb (fun x=>if x.1 then g x.2 else f x.2) := by
  let pp:=p.comp (unprefix ea false)
  let qq:=q.comp (unprefix ea false)
  exact ((chooseBit pp qq).comp
    (unprefix (fun x : Bool×α=>x.1::false::ea x.2) true)).congrEncoding
      (by intro x;rfl) (by intro b;rfl)
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
noncomputable def prepend (ea : α→List Bool) (xs : List Bool) :
    Procedure ea (fun a=>xs++ea a) id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=pushWord () xs
  bound:=Polynomial.C (xs.length+1)
  runs a:=by
    refine ⟨xs.length+1,by simp,?_⟩
    simpa [singletonStore] using pushWord_runs () xs (singletonStore () (ea a))

noncomputable def reverse : Procedure (id : List Bool→List Bool) id List.reverse where
  K:=Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=reverseMove 0 1
  bound:=Polynomial.C 2*Polynomial.X+1
  runs xs:=by
    have hh:=reverseMove_runs (0 : Fin 2) 1 (by decide) (singletonStore 0 xs)
    refine ⟨2*xs.length+1,by simp,?_⟩
    convert hh using 1
    · funext k;fin_cases k <;> simp [singletonStore,Function.update]
    · simp [singletonStore]
    · simp [singletonStore]

noncomputable def tail : Procedure (id : List Bool→List Bool) id List.tail where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip .skip .skip
  bound:=Polynomial.C 2
  runs xs:=by
    refine ⟨2,by simp,?_⟩
    cases xs with
    | nil=>exact Runs.cases_nil (by simp [singletonStore]) (Runs.skip _)
    | cons b bs=>
      have hu : Function.update (singletonStore () (b::bs)) () bs=singletonStore () bs:=by
        simp [singletonStore]
      cases b
      · exact hu ▸ Runs.cases_false (by simp [singletonStore]) (Runs.skip _)
      · exact hu ▸ Runs.cases_true (by simp [singletonStore]) (Runs.skip _)

noncomputable def isEmpty : Procedure (id : List Bool→List Bool) boolCode List.isEmpty where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () (.push () true)
    (.seq (clear ()) (.push () false)) (.seq (clear ()) (.push () false))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C 3
  runs xs:=by
    cases xs with
    | nil=>
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (by
        simpa [singletonStore,boolCode] using Runs.push (singletonStore () []) () true)
    | cons b bs=>
      let s:=singletonStore () bs
      let u:=Function.update s () []
      have hc:=clear_runs () s
      have hp:=Runs.push u () false
      have hh:=Runs.seq hc hp
      have hu : Function.update (singletonStore () (b::bs)) () bs=s:=by simp [s,singletonStore]
      have hv : Function.update u () (false::u ())=singletonStore () [false]:=by
        funext k;cases k;simp [u,s,singletonStore]
      rw [hv] at hh
      have ht : 1+(2*(s ()).length+1)=2*bs.length+2:=by simp [s,singletonStore];omega
      rw [ht] at hh
      refine ⟨2*bs.length+3,by simp,?_⟩
      cases b
      · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)
      · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)

noncomputable def head : Procedure (id : List Bool→List Bool) boolCode (fun xs=>xs.headD false) where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () (.push () false)
    (.seq (clear ()) (.push () false)) (.seq (clear ()) (.push () true))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C 3
  runs xs:=by
    cases xs with
    | nil=>
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (by
        simpa [singletonStore,boolCode] using Runs.push (singletonStore () []) () false)
    | cons b bs=>
      let s:=singletonStore () bs
      let u:=Function.update s () []
      have hc:=clear_runs () s
      have hp:=Runs.push u () b
      have hh:=Runs.seq hc hp
      have hu : Function.update (singletonStore () (b::bs)) () bs=s:=by simp [s,singletonStore]
      have hv : Function.update u () (b::u ())=singletonStore () [b]:=by
        funext k;cases k;simp [u,s,singletonStore]
      rw [hv] at hh
      have ht : 1+(2*(s ()).length+1)=2*bs.length+2:=by simp [s,singletonStore];omega
      rw [ht] at hh
      refine ⟨2*bs.length+3,by simp,?_⟩
      cases b
      · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)
      · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)

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

/-- A truth table on one Boolean has two literal finite output words. This
performs no run-time computation in its Boolean branch labels. -/
noncomputable def ofBool (eb : β→List Bool) (f : Bool→β) :
    Procedure boolCode eb f := by
  let p:=constant (fun _ : Unit=>[]) eb (f false)
  let q:=constant (fun _ : Unit=>[]) eb (f true)
  exact ((chooseBit p q).precompose (fun b=>(b,()))).congrFun
    (by intro b;cases b <;> rfl)

noncomputable def ofBool₂ (eb : β→List Bool) (f : Bool→Bool→β) :
    Procedure (prodCode boolCode boolCode) eb (fun x=>f x.1 x.2) :=
  (choose (ofBool eb (f false)) (ofBool eb (f true))).congrFun
    (by rintro ⟨b,c⟩;cases b <;> rfl)

noncomputable def ofBool₃ (eb : β→List Bool) (f : Bool→Bool→Bool→β) :
    Procedure (prodCode boolCode (prodCode boolCode boolCode)) eb
      (fun x=>f x.1 x.2.1 x.2.2) :=
  (choose (ofBool₂ eb (f false)) (ofBool₂ eb (f true))).congrFun
    (by rintro ⟨b,c,d⟩;cases b <;> rfl)

noncomputable def boolNot : Procedure boolCode boolCode not := ofBool boolCode not
noncomputable def boolAnd : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>x.1 && x.2) := ofBool₂ boolCode and

noncomputable def cons : Procedure (prodCode boolCode (id : List Bool→List Bool)) id
    (fun x=>x.1::x.2) := by
  let pp : Procedure (id : List Bool→List Bool) id (fun xs=>false::xs):=
    (prepend id [false]).result (by intro xs;rfl)
  let qq : Procedure (id : List Bool→List Bool) id (fun xs=>true::xs):=
    (prepend id [true]).result (by intro xs;rfl)
  exact (choose pp qq).congrFun (by rintro ⟨b,xs⟩;cases b <;> rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackBasicProcedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
  {f : α→β} {g : α→γ}

/-- Duplicate the input word and quote the first copy to represent a pair. -/
noncomputable def duplicate (ea : α→List Bool) :
    Procedure ea (prodCode ea ea) (fun a=>(a,a)) where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=3
  program:=.seq (duplicateReverse 0 1 2) (.seq (reverseMove 1 3) (quoteMove 0 3 1))
  bound:=Polynomial.C 14*Polynomial.X+Polynomial.C 8
  runs a:=by
    let s : Store (Fin 4):=singletonStore 0 (ea a)
    let u : Store (Fin 4):=Function.update s 1 (ea a).reverse
    let v : Store (Fin 4):=Function.update s 3 (ea a)
    have h1 : Runs (duplicateReverse 0 1 2) s u (5*(ea a).length+2) := by
      have hh:=duplicateReverse_runs (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
        s (by simp [s,singletonStore])
      simpa only [u,s,singletonStore,Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 4)≠0),List.append_nil] using hh
    have h2 : Runs (reverseMove 1 3) u v (2*(ea a).length+1) := by
      have hh:=reverseMove_runs (1 : Fin 4) 3 (by decide) u
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,v,s,singletonStore,Function.update]
      · simp [u]
    have h3 : Runs (quoteMove 0 3 1) v
        (singletonStore 3 (prodCode ea ea (a,a))) (7*(ea a).length+5) := by
      have hh:=quoteMove_runs (0 : Fin 4) 3 1 (by decide) (by decide) (by decide) v
        (by simp [v,s,singletonStore])
      convert hh using 1
      · funext k; fin_cases k <;> simp [v,s,singletonStore,Function.update,prodCode,pairBits]
      · simp [v,s,singletonStore]
    refine ⟨(7*(ea a).length+5)+(2*(ea a).length+1)+(5*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

noncomputable def pair (p : Procedure ea eb f) (q : Procedure ea ec g) :
    Procedure ea (prodCode eb ec) (fun a=>(f a,g a)) :=
  (p.parallel q).comp (duplicate ea)

/-- Projection parses the actual prefix code and explicitly clears its tail. -/
noncomputable def first (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) ea Prod.fst where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.seq (unquoteMove 0 1 2 3) (clear 0)
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 7
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode ea eb x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 (eb x.2)) 1 (ea x.1)
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (ea x.1) (eb x.2) s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      funext k; fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (clear 0) u (singletonStore 1 (ea x.1)) (2*(eb x.2).length+1) := by
      have hh:=clear_runs (0 : Fin 4) u
      convert hh using 1
      · funext k; fin_cases k <;> simp [u,singletonStore,Function.update]
      · simp [u,singletonStore]
    refine ⟨(2*(eb x.2).length+1)+(7*(ea x.1).length+6),?_,Runs.seq h1 h2⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length]
    omega

noncomputable def second (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) eb Prod.snd :=
  ((first eb ea).comp (swap ea eb)).congrFun (by intro x; rfl)

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def sumCode {α β : Type} (ea : α→List Bool) (eb : β→List Bool) : α⊕β→List Bool
  | .inl a=>false::ea a
  | .inr b=>true::eb b

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
    {f : α→γ} {g : β→γ}
noncomputable def casesSum (p : Procedure ea ec f) (q : Procedure eb ec g) :
    Procedure (sumCode ea eb) ec (Sum.elim f g) where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs x:=by
    cases x with
    | inl a=>
      have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
      obtain ⟨c,hc,hd⟩:=p.shared.runs a
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hpmono).trans (Nat.le_add_right _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu,sumCode] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    | inr b=>
      have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (eb b).length)
      obtain ⟨c,hc,hd⟩:=q.shared.runs b
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hqmono).trans (Nat.le_add_left _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::eb b)) (Sum.inr 0) (eb b)=singletonStore (Sum.inr 0) (eb b):=by
          simp [singletonStore]
        simpa only [hu,sumCode] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=eb b) (s:=singletonStore (Sum.inr 0) (true::eb b)) (by simp [singletonStore])
          (by rw [hu];exact hh)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def listCode (ea : α→List Bool) : List α→List Bool
  | []=>[false]
  | a::as=>true::pairBits (ea a) (listCode ea as)

def emptyCode (_ : Unit) : List Bool := []

def listView : List α→Unit⊕(α×List α)
  | []=>.inl ()
  | a::as=>.inr (a,as)

lemma listCode_length_cons (ea : α→List Bool) (a : α) (as : List α) :
    (listCode ea (a::as)).length=2*(ea a).length+2+(listCode ea as).length := by
  simp [listCode,pairBits_length];omega

lemma listCode_length_append (ea : α→List Bool) (xs ys : List α) :
    (listCode ea (xs++ys)).length+1=(listCode ea xs).length+(listCode ea ys).length := by
  induction xs with
  | nil=>simp [listCode,Nat.add_comm]
  | cons a as ih=>simp only [List.cons_append,listCode_length_cons];omega

lemma listCode_length_rev (ea : α→List Bool) (xs : List α) :
    (listCode ea xs.reverse).length=(listCode ea xs).length := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>
    rw [List.reverse_cons]
    have hh:=listCode_length_append ea as.reverse [a]
    simp only [listCode_length_cons,ih] at hh ⊢
    have hz : (listCode ea []).length=1:=rfl
    omega

lemma listCode_length_pos (ea : α→List Bool) (xs : List α) : 0<(listCode ea xs).length := by
  cases xs <;> simp [listCode]

lemma list_length_le_code (ea : α→List Bool) (xs : List α) : xs.length≤(listCode ea xs).length := by
  induction xs with
  | nil=>simp
  | cons a as ih=>simp only [List.length_cons,listCode_length_cons];omega

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listUncons : Procedure (listCode ea)
    (sumCode emptyCode (prodCode ea (listCode ea))) listView :=
  (identity (listCode ea)).result (by intro xs;cases xs <;> rfl)

noncomputable def listCons : Procedure (prodCode ea (listCode ea)) (listCode ea)
    (fun x=>x.1::x.2) :=
  (prepend (prodCode ea (listCode ea)) [true]).result (by intro x;rfl)

noncomputable def listHead (d : α) : Procedure (listCode ea) ea (fun xs=>xs.headD d) :=
  ((casesSum (constant emptyCode ea d) (first ea (listCode ea))).comp (listUncons ea)).congrFun
    (by intro xs;cases xs <;> rfl)

noncomputable def listTail : Procedure (listCode ea) (listCode ea) List.tail :=
  ((casesSum (constant emptyCode (listCode ea) []) (second ea (listCode ea))).comp
    (listUncons ea)).congrFun (by intro xs;cases xs <;> rfl)

noncomputable def listEmpty : Procedure (listCode ea) boolCode List.isEmpty :=
  ((casesSum (constant emptyCode boolCode true) (constant (prodCode ea (listCode ea)) boolCode false)).comp
    (listUncons ea)).congrFun (by intro xs;cases xs <;> rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

def listScan (f : α×β→β) : List α×β→List α×β
  | ([],b)=>([],b)
  | (a::as,b)=>(as,f (a,b))

lemma listScan_iterate (f : α×β→β) (i : ℕ) (xs : List α) (b : β) :
    (listScan f)^[i] (xs,b)=(xs.drop i,(xs.take i).foldl (fun b a=>f (a,b)) b) := by
  induction i generalizing xs b with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil=>simpa [listScan] using ih [] b
    | cons a as=>simpa [listScan] using ih as (f (a,b))

lemma listCode_length_drop_le (ea : α→List Bool) (i : ℕ) (xs : List α) :
    (listCode ea (xs.drop i)).length≤(listCode ea xs).length := by
  have hh:=listCode_length_append ea (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at hh
  have hp:=listCode_length_pos ea (xs.take i)
  omega

lemma listCode_length_take_le (ea : α→List Bool) (i : ℕ) (xs : List α) :
    (listCode ea (xs.take i)).length≤(listCode ea xs).length := by
  have hh:=listCode_length_append ea (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at hh
  have hp:=listCode_length_pos ea (xs.drop i)
  omega

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {f : α×β→β}
noncomputable def listScanP (d : α) (p : Procedure (prodCode ea eb) eb f) :
    Procedure (prodCode (listCode ea) eb) (prodCode (listCode ea) eb) (listScan f) := by
  let xs:=first (listCode ea) eb
  let b:=second (listCode ea) eb
  let upd:=((listTail ea).comp xs).pair (p.comp (((listHead ea d).comp xs).pair b))
  exact ((choose upd (identity (prodCode (listCode ea) eb))).comp
    (((listEmpty ea).comp xs).pair (identity (prodCode (listCode ea) eb)))).congrFun
      (by rintro ⟨xs,b⟩;cases xs <;> rfl)

noncomputable def foldList (d : α) (p : Procedure (prodCode ea eb) eb f)
    (bound : Polynomial ℕ)
    (hsize : ∀ (xs : List α) b i,
      (eb ((xs.take i).foldl (fun b a=>f (a,b)) b)).length≤
        bound.eval ((listCode ea xs).length+(eb b).length)) :
    Procedure (prodCode (listCode ea) eb) eb (fun x=>x.1.foldl (fun b a=>f (a,b)) x.2) := by
  let s:=listScanP d p
  let rep:=s.iterate (Polynomial.C 2*Polynomial.X+1+bound) (by
    intro n x i _
    rw [listScan_iterate]
    simp only [prodCode,pairBits_length]
    have hs:=hsize x.1 x.2 i
    have hl:=listCode_length_drop_le ea i x.1
    have hm:=eval_nat_mono bound (by omega :
      (listCode ea x.1).length+(eb x.2).length≤n+(2*(listCode ea x.1).length+(eb x.2).length+1))
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let wc:=(length.precompose (listCode ea)).comp (first (listCode ea) eb)
  exact ((second (listCode ea) eb).comp (rep.comp (wc.pair (identity (prodCode (listCode ea) eb))))).congrFun
    (by
      rintro ⟨xs,b⟩
      change ((listScan f)^[(listCode ea xs).length] (xs,b)).2=xs.foldl (fun b a=>f (a,b)) b
      rw [listScan_iterate,List.take_of_length_le (list_length_le_code ea xs)])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

lemma fold_cons_append (xs ys : List α) : xs.foldl (fun ys a=>a::ys) ys=xs.reverse++ys := by
  induction xs generalizing ys with
  | nil=>rfl
  | cons a as ih=>simp only [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

lemma listCode_length_map_bound (eb : β→List Bool) (f : α→β) (xs : List α) (B : ℕ)
    (h : ∀ a∈xs,(eb (f a)).length≤B) :
    (listCode eb (xs.map f)).length≤xs.length*(2*B+2)+1 := by
  induction xs with
  | nil=>simp [listCode]
  | cons a as ih=>
    have ha:=h a (by simp)
    have hb:=ih (by intro b hb;exact h b (by simp [hb]))
    simp only [List.map_cons,listCode_length_cons,List.length_cons]
    nlinarith

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listRevAppend (d : α) : Procedure (prodCode (listCode ea) (listCode ea))
    (listCode ea) (fun x=>x.1.reverse++x.2) :=
  (foldList d (listCons ea) Polynomial.X (by
    intro xs ys i
    rw [fold_cons_append]
    have hh:=listCode_length_append ea (xs.take i).reverse ys
    rw [listCode_length_rev] at hh
    have ht:=listCode_length_take_le ea i xs
    simp only [Polynomial.eval_X]
    omega)).congrFun (by intro x;exact fold_cons_append x.1 x.2)

noncomputable def listReverse (d : α) : Procedure (listCode ea) (listCode ea) List.reverse :=
  ((listRevAppend ea d).comp ((identity (listCode ea)).pair
    (constant (listCode ea) (listCode ea) []))).congrFun (by intro xs;exact List.append_nil _)

noncomputable def listAppend (d : α) : Procedure (prodCode (listCode ea) (listCode ea))
    (listCode ea) (fun x=>x.1++x.2) :=
  ((listRevAppend ea d).comp (((listReverse ea d).comp (first (listCode ea) (listCode ea))).pair
    (second (listCode ea) (listCode ea)))).congrFun (by intro x;exact congrArg (fun xs=>xs++x.2) (List.reverse_reverse x.1))

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackIncrement
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_right _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_left _root_.OAI.ExactQuantumFactoring.BitStackProgram.sumStore_update_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

/-- Little-endian evaluation; leading zeroes at the high end are allowed. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b::xs => b.toNat+2*binaryValue xs

def incrementWord : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => false::incrementWord xs

def carryTail : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => carryTail xs

def carryCount : List Bool → ℕ
  | [] => 0
  | false::_ => 0
  | true::xs => carryCount xs+1

lemma carryCount_le_length (xs : List Bool) : carryCount xs≤xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [carryCount,List.length_cons]; omega
lemma incrementWord_eq (xs : List Bool) :
    incrementWord xs=List.replicate (carryCount xs) false++carryTail xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [incrementWord,carryCount,carryTail,ih,List.replicate_succ]
lemma incrementWord_length (xs : List Bool) : (incrementWord xs).length≤xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [incrementWord,List.length_cons]; omega

variable {K : Type} [DecidableEq K]
def rippleBody (a t c : K) : Program K :=
  .cases a (.push a true) (.push a true) (.seq (.push t false) (.push c true))
def ripple (a t c : K) : Program K := .loop c (rippleBody a t c) (rippleBody a t c)
def increment (a t c : K) : Program K :=
  .seq (.push c true) (.seq (ripple a t c) (reverseMove t a))

lemma ripple_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (s : Store K) (hc : s c=[true]) :
    Runs (ripple a t c) s
      (Function.update (Function.update (Function.update s c []) a (carryTail (s a)))
        t (List.replicate (carryCount (s a)) false++s t))
      (4*(carryCount (s a)+1)) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    let u := Function.update s c []
    let v := Function.update u a [true]
    have hua : u a=[] := by simp [u,hac,hs]
    have hvc : v c=[] := by simp [v,u,hac.symm]
    have body : Runs (rippleBody a t c) u v 2 :=
      Runs.cases_nil hua (by simpa only [hua] using Runs.push u a true)
    have hh := Runs.loop_true (p:=rippleBody a t c) (a:=2) (b:=1) hc body (Runs.loop_nil hvc)
    change Runs (.loop _ _ _) _ _ _
    convert hh using 1
    · simp only [carryCount,carryTail,List.replicate_zero,List.nil_append]
      change Function.update v t (s t)=v
      rw [← show v t=s t by simp [v,u,hat.symm,htc],Function.update_eq_self]
    · rfl
  | cons x xs ih =>
    cases x
    · let u := Function.update s c []
      let w := Function.update u a xs
      let v := Function.update w a (true::xs)
      have hua : u a=false::xs := by simp [u,hac,hs]
      have hvc : v c=[] := by simp [v,w,u,hac.symm]
      have body : Runs (rippleBody a t c) u v 2 :=
        Runs.cases_false hua (by simpa only [w,Function.update_self] using Runs.push w a true)
      have hh := Runs.loop_true (p:=rippleBody a t c) (a:=2) (b:=1) hc body (Runs.loop_nil hvc)
      change Runs (.loop _ _ _) _ _ _
      convert hh using 1
      · funext k
        by_cases ha : k=a <;> by_cases ht : k=t <;> by_cases hcc : k=c <;>
          simp_all [v,w,u,Function.update,carryCount,carryTail]
      · rfl
    · let u := Function.update s c []
      let w := Function.update u a xs
      let z := Function.update w t (false::w t)
      let v := Function.update z c (true::z c)
      have hua : u a=true::xs := by simp [u,hac,hs]
      have hva : v a=xs := by simp [v,z,w,hac,hat]
      have hvc : v c=[true] := by simp [v,z,w,u,htc.symm,hac.symm]
      have body : Runs (rippleBody a t c) u v 3 :=
        Runs.cases_true (a:=2) hua (Runs.seq (Runs.push w t false) (Runs.push z c true))
      have hh := Runs.loop_true (p:=rippleBody a t c) (a:=3) (b:=4*(carryCount xs+1)) hc body (ih v hvc hva)
      change Runs (.loop _ _ _) _ _ _
      convert hh using 1
      · funext k
        by_cases ha : k=a <;> by_cases ht : k=t <;> by_cases hcc : k=c <;>
          simp_all [v,z,w,u,Function.update,carryCount,carryTail,List.replicate_succ]
        rw [← List.cons_append, ← List.replicate_succ, List.replicate_succ',List.append_assoc]
        rfl
      · simp only [carryCount]; omega

lemma increment_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (s : Store K) (ht : s t=[]) (hc : s c=[]) :
    Runs (increment a t c) s (Function.update s a (incrementWord (s a)))
      (6*carryCount (s a)+6) := by
  let u := Function.update s c [true]
  have hua : u a=s a := by simp [u,hac]
  have hut : u t=[] := by simp [u,ht,htc]
  have huc : u c=[true] := by simp [u]
  let v := Function.update (Function.update (Function.update u c []) a (carryTail (u a)))
    t (List.replicate (carryCount (u a)) false++u t)
  have hp : Runs (.push c true) s u 1 := by simpa only [hc] using Runs.push s c true
  have hh := Runs.seq hp
    (Runs.seq (ripple_runs a t c hat hac htc u huc) (reverseMove_runs t a hat.symm v))
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases htk : k=t <;> by_cases hck : k=c <;>
      simp_all [v,u,Function.update,incrementWord_eq]
  · simp only [v,Function.update_self,hut,List.append_nil,List.length_replicate,hua]
    omega

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackNaturals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma binaryValue_bits (n : ℕ) : binaryValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [binaryValue,ih,Nat.bit,Nat.add_comm]

lemma incrementWord_bits (n : ℕ) : incrementWord n.bits=(n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b
    · simp only [incrementWord,Nat.bit_false,Nat.bit1_bits]
    · simp only [incrementWord,ih,Nat.bit_true]
      rw [show 2*n+1+1=2*(n+1) by omega,Nat.bit0_bits (n+1) (by omega)]

abbrev unaryCode (n : ℕ) := List.replicate n true
namespace Procedure
noncomputable def successor : Procedure Nat.bits Nat.bits Nat.succ where
  K:=Fin 3
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=increment 0 1 2
  bound:=Polynomial.C 6*Polynomial.X+Polynomial.C 6
  runs n:=by
    have hh:=increment_runs (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
      (singletonStore 0 n.bits) (by simp [singletonStore]) (by simp [singletonStore])
    refine ⟨6*carryCount n.bits+6,?_,?_⟩
    · have hl:=carryCount_le_length n.bits
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      omega
    · simpa [singletonStore,incrementWord_bits] using hh

noncomputable def unarySuccessor : Procedure unaryCode unaryCode Nat.succ where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.push () true
  bound:=1
  runs n:=by
    refine ⟨1,by simp,?_⟩
    simpa [singletonStore,unaryCode,List.replicate_succ] using
      Runs.push (singletonStore () (unaryCode n)) () true

/-- Unary-to-binary conversion charges every carry and all word moves. -/
noncomputable def unaryToBits : Procedure unaryCode Nat.bits id := by
  let p:=successor.iterate (Polynomial.X+1) (by
    intro n a i hi
    have hlen : (a+i).bits.length≤a.bits.length+i := by
      clear hi
      induction i with
      | zero => simp
      | succ i ih =>
        have h:=incrementWord_length (a+i).bits
        rw [incrementWord_bits] at h
        simpa only [Nat.add_assoc] using (h.trans (Nat.add_le_add_right ih 1))
    simpa only [Function.iterate_succ_apply',Function.iterate_succ_apply,
      Nat.succ_iterate,Nat.size_eq_bits_len,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one] using (hlen.trans (by omega : a.bits.length+i≤n+a.bits.length+1)))
  exact (p.comp ((identity unaryCode).pair (constant unaryCode Nat.bits 0))).congrFun
    (by intro n; simp [Nat.succ_iterate])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackTabulate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def tabStep (f : α→ℕ→β) (s : ℕ×(α×List β)) : ℕ×(α×List β) :=
  (s.1+1,s.2.1,f s.2.1 s.1::s.2.2)
def tabCode (ea : α→List Bool) (eb : β→List Bool) := prodCode unaryCode (prodCode ea (listCode eb))
lemma tabStep_iterate (f : α→ℕ→β) (j i : ℕ) (a : α) (ys : List β) :
    (tabStep f)^[j] (i,a,ys)=(i+j,a,((List.range' i j).map (f a)).reverse++ys) := by
  induction j with
  | zero=>simp
  | succ j ih=>
    rw [Function.iterate_succ_apply',ih]
    simp only [tabStep,List.range'_1_concat,List.map_append,List.map_cons,List.map_nil,
      List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
    simp only [Nat.add_assoc]
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {f : α→ℕ→β}
noncomputable def tabStepP (p : Procedure (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Procedure (tabCode ea eb) (tabCode ea eb) (tabStep f) := by
  let i:=first unaryCode (prodCode ea (listCode eb))
  let rest:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp rest
  let ys:=(second ea (listCode eb)).comp rest
  exact ((unarySuccessor.comp i).pair
    (a.pair ((listCons eb).comp ((p.comp (i.pair a)).pair ys)))).congrFun (by intro s;rfl)
noncomputable def tabulate (d : β)
    (p : Procedure (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Procedure (prodCode unaryCode ea) (listCode eb)
      (fun x=>(List.range x.1).map (f x.2)) := by
  let q:=(Polynomial.X+p.bound).comp (Polynomial.C 2*Polynomial.X+1)
  have hval (a : α) (i : ℕ) : (eb (f a i)).length≤q.eval (i+(ea a).length) := by
    have ho:=p.output_length_le (i,a)
    have hm:=eval_nat_mono (Polynomial.X+p.bound)
      (show (prodCode unaryCode ea (i,a)).length≤2*(i+(ea a).length)+1 by
        simp only [prodCode,pairBits_length,unaryCode,List.length_replicate];omega)
    simp only [Polynomial.eval_add,Polynomial.eval_X] at hm
    simpa only [q,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one] using ho.trans hm
  let rep:=(tabStepP p).iterate (Polynomial.X*(Polynomial.C 2*q+Polynomial.C 5)) (by
    rintro n ⟨i,a,ys⟩ j hj
    rw [tabStep_iterate]
    have len0 : (tabCode ea eb (i,a,ys)).length=2*i+2*(ea a).length+(listCode eb ys).length+2 := by
      simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
    have hv : ∀ k∈List.range' i j,(eb (f a k)).length≤q.eval (n+(tabCode ea eb (i,a,ys)).length) := by
      intro k hk
      have hk':=List.mem_range'.mp hk
      exact (hval a k).trans (eval_nat_mono q (by rw [len0];omega))
    have hmap:=listCode_length_map_bound eb (f a) (List.range' i j) _ hv
    have happ:=listCode_length_append eb (((List.range' i j).map (f a)).reverse) ys
    rw [listCode_length_rev] at happ
    simp only [List.length_range'] at hmap
    simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X] at *
    nlinarith)
  let inputN:=first unaryCode ea
  let inputA:=second unaryCode ea
  let start:=(constant (prodCode unaryCode ea) unaryCode 0).pair
    (inputA.pair (constant (prodCode unaryCode ea) (listCode eb) []))
  let result:=((second ea (listCode eb)).comp
    (second unaryCode (prodCode ea (listCode eb)))).comp (rep.comp (inputN.pair start))
  exact ((listReverse eb d).comp result).congrFun (by
    rintro ⟨n,a⟩
    change (((tabStep f)^[n] (0,a,[])).2.2).reverse=(List.range n).map (f a)
    rw [tabStep_iterate,List.append_nil,List.reverse_reverse,List.range_eq_range'])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
def scanStep (f g : α→α) : List Bool×α→List Bool×α
  | ([],a)=>([],a)
  | (b::bs,a)=>(bs,if b then g a else f a)

def bitAction (f g : α→α) (a : α) (b : Bool) : α := if b then g a else f a

lemma scanStep_iterate (f g : α→α) (i : ℕ) (xs : List Bool) (a : α) :
    (scanStep f g)^[i] (xs,a)=(xs.drop i,(xs.take i).foldl (bitAction f g) a) := by
  induction i generalizing xs a with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil=>simpa [scanStep] using ih [] a
    | cons b bs=>simpa [scanStep,bitAction] using ih bs (if b then g a else f a)

lemma foldl_measure {m : α→ℕ} {f g : α→α} {c : ℕ}
    (hf : ∀a,m (f a)≤ m a+c) (hg : ∀a,m (g a)≤ m a+c) (xs : List Bool) (a : α) :
    m (xs.foldl (bitAction f g) a)≤ m a+xs.length*c := by
  induction xs generalizing a with
  | nil=>simp
  | cons b bs ih=>
    simp only [List.foldl_cons,List.length_cons]
    have hh : m (bitAction f g a b)≤ m a+c:=by cases b <;> simp [bitAction,hf,hg]
    have hi:=ih (bitAction f g a b)
    nlinarith

namespace Procedure
variable {ea : α→List Bool} {f g : α→α}
noncomputable def scan (p : Procedure ea ea f) (q : Procedure ea ea g) :
    Procedure (prodCode id ea) (prodCode id ea) (scanStep f g) := by
  let fst:=first (id : List Bool→List Bool) ea
  let snd:=second (id : List Bool→List Bool) ea
  let upd:=(choose p q).comp ((head.comp fst).pair snd)
  let body:=(tail.comp fst).pair upd
  let pp:=(choose body (identity (prodCode id ea))).comp
    ((isEmpty.comp fst).pair (identity (prodCode id ea)))
  exact pp.congrFun (by
    rintro ⟨xs,a⟩
    cases xs <;> rfl)

/-- Fold a variable Boolean word. The bound covers every actual intermediate
state; all pairing, data movement and loop iterations are charged. -/
noncomputable def foldBits (p : Procedure ea ea f) (q : Procedure ea ea g)
    (bound : Polynomial ℕ)
    (hsize : ∀ (xs : List Bool) a i,(ea ((xs.take i).foldl (bitAction f g) a)).length≤
      bound.eval (xs.length+(ea a).length)) :
    Procedure (prodCode id ea) ea (fun x=>x.1.foldl (bitAction f g) x.2) := by
  let s:=scan p q
  let rep:=s.iterate (Polynomial.C 2*Polynomial.X+1+bound) (by
    intro n x i _
    rw [scanStep_iterate]
    simp only [prodCode,pairBits_length,id_eq,List.length_drop]
    have hs:=hsize x.1 x.2 i
    have hm:=eval_nat_mono bound (by omega :
      x.1.length+(ea x.2).length≤n+(2*x.1.length+(ea x.2).length+1))
    dsimp only at hm
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let start:=(length.comp (first (id : List Bool→List Bool) ea)).pair (identity (prodCode id ea))
  exact ((second (id : List Bool→List Bool) ea).comp (rep.comp start)).congrFun (by
    rintro ⟨xs,a⟩
    change ((scanStep f g)^[xs.length] (xs,a)).2=xs.foldl (bitAction f g) a
    rw [scanStep_iterate,List.take_length])

noncomputable def foldBitsLinear (p : Procedure ea ea f) (q : Procedure ea ea g) (c : ℕ)
    (hf : ∀a,(ea (f a)).length≤(ea a).length+c)
    (hg : ∀a,(ea (g a)).length≤(ea a).length+c) :
    Procedure (prodCode id ea) ea (fun x=>x.1.foldl (bitAction f g) x.2) :=
  foldBits p q (Polynomial.C (c+1)*Polynomial.X) (by
    intro xs a i
    have hh:=foldl_measure (m:=fun a=>(ea a).length) (f:=f) (g:=g) (c:=c) hf hg (xs.take i) a
    have hl : (xs.take i).length≤xs.length:=by simp only [List.length_take];omega
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    nlinarith)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackBinaryBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma binaryValue_append (xs ys : List Bool) :
    binaryValue (xs++ys)=binaryValue xs+2^xs.length*binaryValue ys := by
  induction xs with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.cons_append,List.length_cons,binaryValue,ih,pow_succ]
    ring

lemma bigEndian_value (xs : List Bool) (a : ℕ) :
    xs.foldl (bitAction (fun n=>2*n) (fun n=>2*n+1)) a=
      binaryValue xs.reverse+2^xs.length*a := by
  induction xs generalizing a with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.foldl_cons,ih,List.reverse_cons,binaryValue_append,
      List.length_reverse,List.length_cons,pow_succ]
    cases b <;> simp [bitAction,binaryValue] <;> ring

lemma double_bits_length (n : ℕ) : (2*n).bits.length≤n.bits.length+1 := by
  by_cases h : n=0
  · subst n;simp
  · rw [Nat.bit0_bits n h,List.length_cons]
lemma doubleOne_bits_length (n : ℕ) : (2*n+1).bits.length≤n.bits.length+1 := by
  rw [Nat.bit1_bits,List.length_cons]

namespace Procedure
noncomputable def double : Procedure Nat.bits Nat.bits (fun n=>2*n) where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip (.seq (.push () false) (.push () false))
    (.seq (.push () true) (.push () false))
  bound:=Polynomial.C 3
  runs n:=by
    by_cases hn : n=0
    · subst n
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (Runs.skip _)
    · have he : n.bits≠[]:=by
        intro h
        have hv:=binaryValue_bits n
        rw [h] at hv
        exact hn hv.symm
      cases hb : n.bits with
      | nil=>exact (he hb).elim
      | cons b bs=>
        have hout : (2*n).bits=false::b::bs:=by rw [Nat.bit0_bits n hn,hb]
        have hbody : Runs (.seq (.push () b) (.push () false))
            (singletonStore () bs) (singletonStore () (false::b::bs)) 2:=by
          have hh:=Runs.seq (Runs.push (singletonStore () bs) () b)
            (Runs.push (singletonStore () (b::bs)) () false)
          simpa only [singletonStore,Function.update_self,Function.update_idem] using hh
        refine ⟨3,by simp,?_⟩
        rw [hout]
        cases b
        · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa [singletonStore] using hbody)
        · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa [singletonStore] using hbody)

noncomputable def doubleOne : Procedure Nat.bits Nat.bits (fun n=>2*n+1) :=
  (prepend Nat.bits [true]).result (by intro n;simp only [List.singleton_append,Nat.bit1_bits,id_eq])

/-- Canonicalize a binary word, charging a linear-growth bit fold. -/
noncomputable def normalize : Procedure (id : List Bool→List Bool) Nat.bits binaryValue := by
  let p:=foldBitsLinear double doubleOne 1 double_bits_length doubleOne_bits_length
  let start:=reverse.pair (constant (id : List Bool→List Bool) Nat.bits 0)
  exact (p.comp start).congrFun (by intro xs;simp [bigEndian_value])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def unaryAdd : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1+x.2) :=
  (unarySuccessor.iterate Polynomial.X (by
    intro n a i hi
    simp only [Nat.succ_iterate,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)).congrFun (by intro x;simp [Nat.succ_iterate,Nat.add_comm])

end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackAdder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

/-- Literal full-adder truth tables, not an arithmetic oracle. -/
def sumBit (a b c : Bool) : Bool := xor a (xor b c)
def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

lemma sum_carry (a b c : Bool) :
    a.toNat+b.toNat+c.toNat=(sumBit a b c).toNat+2*(carryBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

abbrev AddState := List Bool × List Bool × Bool × List Bool
abbrev addStateCode : AddState→List Bool :=
  prodCode id (prodCode id (prodCode Procedure.boolCode id))

def addStep (s : AddState) : AddState :=
  (s.1.tail,s.2.1.tail,
    carryBit (s.1.headD false) (s.2.1.headD false) s.2.2.1,
    sumBit (s.1.headD false) (s.2.1.headD false) s.2.2.1 :: s.2.2.2)

def addMeasure (s : AddState) : ℕ := s.1.length+s.2.1.length+s.2.2.1.toNat

def residual (s : AddState) : ℕ := binaryValue s.1+binaryValue s.2.1+s.2.2.1.toNat

def addInvariant (s : AddState) : ℕ :=
  binaryValue s.2.2.2.reverse+2^s.2.2.2.length*residual s

lemma binaryValue_head_tail (xs : List Bool) :
    binaryValue xs=(xs.headD false).toNat+2*binaryValue xs.tail := by
  cases xs <;> rfl

lemma addInvariant_step (s : AddState) : addInvariant (addStep s)=addInvariant s := by
  have hx:=binaryValue_head_tail s.1
  have hy:=binaryValue_head_tail s.2.1
  have hh:=sum_carry (s.1.headD false) (s.2.1.headD false) s.2.2.1
  simp only [addInvariant,addStep,List.reverse_cons,binaryValue_append,List.length_reverse,
    binaryValue,List.length_cons,pow_succ,residual]
  rw [hx,hy]
  nlinarith [congrArg (fun n : ℕ=>2^s.2.2.2.length*n) hh]

lemma addMeasure_step (s : AddState) : addMeasure (addStep s)≤addMeasure s-1 := by
  rcases s with ⟨xs,ys,c,zs⟩
  cases xs with
  | nil=>cases ys with
    | nil=>cases c <;> simp [addMeasure,addStep,carryBit]
    | cons b bs=>cases b <;> cases c <;> simp [addMeasure,addStep,carryBit]
  | cons a as=>cases ys with
    | nil=>cases a <;> cases c <;> simp [addMeasure,addStep,carryBit]
    | cons b bs=>cases a <;> cases b <;> cases c <;>
        simp [addMeasure,addStep,carryBit] <;> omega

lemma addMeasure_iterate (i : ℕ) (s : AddState) :
    addMeasure (addStep^[i] s)≤addMeasure s-i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    exact (addMeasure_step _).trans (by omega)

lemma addInvariant_iterate (i : ℕ) (s : AddState) :
    addInvariant (addStep^[i] s)=addInvariant s := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',addInvariant_step,ih]

lemma residual_zero {s : AddState} (h : addMeasure s=0) : residual s=0 := by
  have hx : s.1=[]:=List.length_eq_zero_iff.mp (by unfold addMeasure at h;omega)
  have hy : s.2.1=[]:=List.length_eq_zero_iff.mp (by unfold addMeasure at h;omega)
  have hc : s.2.2.1.toNat=0:=by unfold addMeasure at h;omega
  simp [residual,hx,hy,hc,binaryValue]

def wordAdd (x : List Bool×List Bool) : List Bool :=
  (addStep^[x.1.length+x.2.length+1] (x.1,x.2,false,[])).2.2.2.reverse

lemma wordAdd_value (x : List Bool×List Bool) :
    binaryValue (wordAdd x)=binaryValue x.1+binaryValue x.2 := by
  let s : AddState:=(x.1,x.2,false,[])
  let i:=x.1.length+x.2.length+1
  have hz : addMeasure (addStep^[i] s)=0:=by
    have hh:=addMeasure_iterate i s
    simp only [s,i,addMeasure,Bool.toNat_false,Nat.add_zero] at hh
    dsimp only [s,i,addMeasure]
    omega
  have hh:=addInvariant_iterate i s
  simp only [addInvariant,residual_zero hz,Nat.mul_zero,Nat.add_zero] at hh
  simpa [s,i,wordAdd,residual,binaryValue] using hh

lemma addStep_size (s : AddState) :
    (addStateCode (addStep s)).length≤(addStateCode s).length+1 := by
  simp only [addStateCode,addStep,prodCode,pairBits_length,id_eq,Procedure.boolCode,
    List.length_cons,List.length_tail]
  omega

namespace Procedure
variable {α : Type} {ea : α→List Bool} {f : α→α}

noncomputable def iterateLinear (p : Procedure ea ea f) (c : ℕ)
    (hg : ∀a,(ea (f a)).length≤(ea a).length+c) :
    Procedure (prodCode unaryCode ea) ea (fun x=>f^[x.1] x.2) := by
  have hh : ∀ i a,(ea (f^[i] a)).length≤(ea a).length+i*c:=by
    intro i a
    induction i with
    | zero=>simp
    | succ i ih=>
      rw [Function.iterate_succ_apply']
      have h:=hg (f^[i] a)
      nlinarith
  exact p.iterate (Polynomial.C (c+1)*Polynomial.X) (by
    intro n a i hi
    have h:=hh i a
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    nlinarith)

noncomputable def addStepP : Procedure addStateCode addStateCode addStep := by
  let x:=first (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let rem:=second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let y:=(first (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  let bits:=(head.comp x).pair ((head.comp y).pair c)
  let newc:=(ofBool₃ boolCode carryBit).comp bits
  let newb:=(ofBool₃ boolCode sumBit).comp bits
  exact ((tail.comp x).pair ((tail.comp y).pair
    (newc.pair (cons.comp (newb.pair zs))))).congrFun (by intro s;rfl)

noncomputable def wordAddP : Procedure (prodCode (id : List Bool→List Bool) id) id wordAdd := by
  let x:=first (id : List Bool→List Bool) (id : List Bool→List Bool)
  let y:=second (id : List Bool→List Bool) (id : List Bool→List Bool)
  let len:=unarySuccessor.comp (unaryAdd.comp ((length.comp x).pair (length.comp y)))
  let start:=x.pair (y.pair ((constant (prodCode id id) boolCode false).pair
    (constant (prodCode id id) (id : List Bool→List Bool) [])))
  let rep:=addStepP.iterateLinear 1 addStep_size
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp
    (second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id)))
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  exact (reverse.comp (zs.comp (rep.comp (len.pair start)))).congrFun (by intro x;rfl)

noncomputable def binaryAdd : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1+x.2) :=
  ((normalize.comp wordAddP).precompose (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
    (by
      intro x
      change binaryValue (wordAdd (x.1.bits,x.2.bits))=x.1+x.2
      rw [wordAdd_value,binaryValue_bits,binaryValue_bits])

end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackSubtractor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def borrowBit (a b c : Bool) : Bool := (!a && b) || (!a && c) || (b && c)

lemma difference_borrow (a b c : Bool) :
    (a.toNat : ℤ)-b.toNat-c.toNat=(sumBit a b c).toNat-2*(borrowBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

lemma binaryValue_lt (xs : List Bool) : binaryValue xs<2^xs.length := by
  induction xs with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.length_cons,binaryValue,pow_succ]
    cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

abbrev SubState := AddState
abbrev subStateCode := addStateCode

def subStep (s : SubState) : SubState :=
  (s.1.tail,s.2.1.tail,
    borrowBit (s.1.headD false) (s.2.1.headD false) s.2.2.1,
    sumBit (s.1.headD false) (s.2.1.headD false) s.2.2.1 :: s.2.2.2)

def subInvariant (s : SubState) : ℤ :=
  (binaryValue s.2.2.2.reverse : ℤ)+2^s.2.2.2.length*
    ((binaryValue s.1 : ℤ)-binaryValue s.2.1-s.2.2.1.toNat)

lemma subInvariant_step (s : SubState) : subInvariant (subStep s)=subInvariant s := by
  have hx:=binaryValue_head_tail s.1
  have hy:=binaryValue_head_tail s.2.1
  have hh:=difference_borrow (s.1.headD false) (s.2.1.headD false) s.2.2.1
  simp only [subInvariant,subStep,List.reverse_cons,binaryValue_append,List.length_reverse,
    binaryValue,List.length_cons,pow_succ]
  push_cast
  have hx' : (binaryValue s.1 : ℤ)=(s.1.headD false).toNat+2*binaryValue s.1.tail:=by
    exact_mod_cast hx
  have hy' : (binaryValue s.2.1 : ℤ)=(s.2.1.headD false).toNat+2*binaryValue s.2.1.tail:=by
    exact_mod_cast hy
  rw [hx',hy']
  nlinarith [congrArg (fun n : ℤ=>2^s.2.2.2.length*n) hh]

lemma subInvariant_iterate (i : ℕ) (s : SubState) :
    subInvariant (subStep^[i] s)=subInvariant s := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',subInvariant_step,ih]

lemma subStep_tapes (i : ℕ) (s : SubState) :
    (subStep^[i] s).1=s.1.drop i ∧ (subStep^[i] s).2.1=s.2.1.drop i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    simp only [subStep,ih.1,ih.2,List.tail_drop]
    trivial

def wordSubtract (x : List Bool×List Bool) : Bool×List Bool :=
  let s:=subStep^[x.1.length+x.2.length+1] (x.1,x.2,false,[])
  (s.2.2.1,s.2.2.2.reverse)

lemma wordSubtract_spec (x : List Bool×List Bool) :
    (binaryValue (wordSubtract x).2 : ℤ) -
      2^(wordSubtract x).2.length*((wordSubtract x).1.toNat : ℤ)=
      (binaryValue x.1 : ℤ)-binaryValue x.2 := by
  let s : SubState:=(x.1,x.2,false,[])
  let i:=x.1.length+x.2.length+1
  have hx : (subStep^[i] s).1=[]:=by
    rw [(subStep_tapes i s).1]
    exact List.drop_eq_nil_iff.mpr (by dsimp [s,i];omega)
  have hy : (subStep^[i] s).2.1=[]:=by
    rw [(subStep_tapes i s).2]
    exact List.drop_eq_nil_iff.mpr (by dsimp [s,i];omega)
  have hh:=subInvariant_iterate i s
  simp only [subInvariant,hx,hy,binaryValue,Int.natCast_zero,zero_sub] at hh
  simpa [wordSubtract,s,i,List.length_reverse,subInvariant,binaryValue,sub_eq_add_neg] using hh

lemma wordSubtract_borrow (x : List Bool×List Bool) :
    (wordSubtract x).1=decide (binaryValue x.1<binaryValue x.2) := by
  have hh:=wordSubtract_spec x
  have hl:=binaryValue_lt (wordSubtract x).2
  have hl' : (binaryValue (wordSubtract x).2 : ℤ)<2^(wordSubtract x).2.length:=by
    exact_mod_cast hl
  cases hb : (wordSubtract x).1 <;> simp only [hb,Bool.toNat_false,Bool.toNat_true,
    Int.natCast_zero,Int.natCast_one,mul_zero,mul_one,sub_zero] at hh
  · symm;apply decide_eq_false;omega
  · symm;apply decide_eq_true;omega

lemma wordSubtract_value (x : List Bool×List Bool) :
    (if (wordSubtract x).1 then 0 else binaryValue (wordSubtract x).2)=
      binaryValue x.1-binaryValue x.2 := by
  have hh:=wordSubtract_spec x
  have hb:=wordSubtract_borrow x
  cases hc : (wordSubtract x).1
  · simp only [hc,Bool.false_eq_true,ite_false, if_false,Bool.toNat_false,Int.natCast_zero,mul_zero,sub_zero] at *
    omega
  · simp only [hc,ite_true, if_true,true_eq_decide_iff] at *
    omega

lemma subStep_size (s : SubState) :
    (subStateCode (subStep s)).length≤(subStateCode s).length+1 := by
  simp only [subStateCode,addStateCode,subStep,prodCode,pairBits_length,id_eq,Procedure.boolCode,
    List.length_cons,List.length_tail]
  omega


end ExactQuantumFactoring.BitStackProgram
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

lemma bits_length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_Procedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def subStepP : Procedure subStateCode subStateCode subStep := by
  let x:=first (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let rem:=second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let y:=(first (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  let bits:=(head.comp x).pair ((head.comp y).pair c)
  let newc:=(ofBool₃ boolCode borrowBit).comp bits
  let newb:=(ofBool₃ boolCode sumBit).comp bits
  exact ((tail.comp x).pair ((tail.comp y).pair
    (newc.pair (cons.comp (newb.pair zs))))).congrFun (by intro s;rfl)

noncomputable def wordSubtractP :
    Procedure (prodCode (id : List Bool→List Bool) id) (prodCode boolCode id) wordSubtract := by
  let x:=first (id : List Bool→List Bool) (id : List Bool→List Bool)
  let y:=second (id : List Bool→List Bool) (id : List Bool→List Bool)
  let len:=unarySuccessor.comp (unaryAdd.comp ((length.comp x).pair (length.comp y)))
  let start:=x.pair (y.pair ((constant (prodCode id id) boolCode false).pair
    (constant (prodCode id id) (id : List Bool→List Bool) [])))
  let rep:=subStepP.iterateLinear 1 subStep_size
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp
    (second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id)))
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  exact ((c.pair (reverse.comp zs)).comp (rep.comp (len.pair start))).congrFun (by intro x;rfl)

noncomputable def binaryLt : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1<x.2)) :=
  (((first boolCode (id : List Bool→List Bool)).comp wordSubtractP).precompose
    (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
      (by
        intro x
        change (wordSubtract (x.1.bits,x.2.bits)).1=decide (x.1<x.2)
        rw [wordSubtract_borrow,binaryValue_bits,binaryValue_bits])

noncomputable def binaryLe : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1≤x.2)) :=
  (boolNot.comp (binaryLt.comp (swap Nat.bits Nat.bits))).congrFun (by
    intro x
    change (!(decide (x.2<x.1)))=decide (x.1≤x.2)
    simp only [← decide_not,Nat.not_lt])

noncomputable def binarySub : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1-x.2) :=
  (((choose normalize (constant (id : List Bool→List Bool) Nat.bits 0)).comp
    wordSubtractP).precompose (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
      (by
        intro x
        change (if (wordSubtract (x.1.bits,x.2.bits)).1 then 0 else
          binaryValue (wordSubtract (x.1.bits,x.2.bits)).2)=x.1-x.2
        rw [wordSubtract_value,binaryValue_bits,binaryValue_bits])
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
namespace Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
    {c : α→Bool} {f g : α→β}
noncomputable def conditional (test : Procedure ea boolCode c)
    (yes : Procedure ea eb f) (no : Procedure ea eb g) :
    Procedure ea eb (fun x=>if c x then f x else g x) :=
  (choose no yes).comp (test.pair (identity ea))

noncomputable def binaryZero : Procedure Nat.bits boolCode (fun n=>decide (n=0)) :=
  (isEmpty.precompose Nat.bits).congrFun (by
    intro n
    by_cases hn : n=0
    · subst n;rfl
    · have hh : n.bits≠[]:=by
        intro h
        have hy:=binaryValue_bits n
        rw [h] at hy
        exact hn hy.symm
      simp [hh,hn])
end Procedure

end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackOptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool}
noncomputable def binaryEq : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1=x.2)) := by
  let swap:=(second Nat.bits Nat.bits).pair (first Nat.bits Nat.bits)
  exact (boolAnd.comp (binaryLe.pair (binaryLe.comp swap))).congrFun
    (by intro x;apply Bool.eq_iff_iff.mpr;simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq];omega)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
def dropStep : ℕ×List α→ℕ×List α
  | (n,xs)=>if n=0 then (n,xs) else (n-1,xs.tail)
lemma dropStep_iterate (i n : ℕ) (xs : List α) :
    dropStep^[i] (n,xs)=(n-i,xs.drop (min i n)) := by
  induction i generalizing n xs with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    by_cases hn : n=0
    · subst n;simp [dropStep,ih]
    · obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hn
      simp only [dropStep,Nat.succ_ne_zero,ite_false, if_false,Nat.succ_sub_one,ih]
      rw [←List.drop_one,List.drop_drop]
      congr 1
      · omega
      · congr 1; omega

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listDrop : Procedure (prodCode Nat.bits (listCode ea)) (listCode ea)
    (fun x=>x.2.drop x.1) := by
  let en:=prodCode Nat.bits (listCode ea)
  let n:=first Nat.bits (listCode ea)
  let xs:=second Nat.bits (listCode ea)
  let pred:=binarySub.comp (n.pair (constant en Nat.bits 1))
  let step:=(conditional (binaryZero.comp n) (identity en)
    (pred.pair ((listTail ea).comp xs))).congrFun (by intro x;rfl)
  have stepType : Procedure en en (dropStep (α:=α)):=
    step.congrFun (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,id_eq,dropStep])
  let rep:=stepType.iterate Polynomial.X (by
    intro k x i _
    rw [dropStep_iterate]
    simp only [en,prodCode,pairBits_length,Polynomial.eval_X]
    have hn:=bits_length_mono (Nat.sub_le x.1 i)
    have hl:=listCode_length_drop_le ea (min i x.1) x.2
    omega)
  let times:=(length.precompose (listCode ea)).comp xs
  exact (xs.comp (rep.comp (times.pair (identity en)))).congrFun (by
    intro x
    change (dropStep^[(listCode ea x.2).length] x).2=x.2.drop x.1
    rw [dropStep_iterate]
    by_cases h:x.1≤(listCode ea x.2).length
    · rw [Nat.min_eq_right h]
    · have hlen:=list_length_le_code ea x.2
      rw [Nat.min_eq_left (by omega),List.drop_eq_nil_of_le (by omega),List.drop_eq_nil_of_le (by omega)])
noncomputable def listGet (d : α) : Procedure (prodCode Nat.bits (listCode ea)) ea
    (fun x=>(x.2.drop x.1).headD d) := (listHead ea d).comp (listDrop ea)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
lemma fold_count (xs : List α) (n : ℕ) : xs.foldl (fun n _=>n+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil=>simp
  | cons a as ih=>simp only [List.foldl_cons,ih,List.length_cons];omega
namespace Procedure
noncomputable def listLength (ea : α→List Bool) (d : α) :
    Procedure (listCode ea) Nat.bits List.length := by
  let step:=unarySuccessor.comp (second ea unaryCode)
  let rep:=foldList d step Polynomial.X (by
    intro xs n i
    change (unaryCode ((xs.take i).foldl (fun n _=>n+1) n)).length≤_
    rw [fold_count]
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X,List.length_take]
    have hh:=list_length_le_code ea xs
    omega)
  let start:=(identity (listCode ea)).pair (constant (listCode ea) unaryCode 0)
  exact (unaryToBits.comp (rep.comp start)).congrFun (by intro xs;simpa only [Function.comp_apply,id_eq,Nat.zero_add] using fold_count xs 0)
end Procedure
end ExactQuantumFactoring.BitStackProgram

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
abbrev Ref := ℕ × Bool
abbrev Key := Ref × Ref
/-- A literal list representation of the nodes and the (possibly incomplete)
cache. The cache is not replaced by a search through all nodes. -/
inductive Decl where
  | zero
  | atom (i : ℕ)
  | gate (a b : Ref)
  deriving DecidableEq, Inhabited
structure Graph where
  decls : List Decl
  cache : List (Key × ℕ)
  deriving Inhabited

end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGProcedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure
abbrev refCode := prodCode Nat.bits boolCode
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGBoolean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat
def notRef (a : Ref) : Ref := (a.1,!a.2)
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

def eraseVec {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) : List Ref :=
  List.ofFn (fun i : Fin w=>((v.get i.val i.isLt).gate,(v.get i.val i.isLt).invert))
@[simp] lemma eraseVec_length {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) :
    (eraseVec v).length=w := List.length_ofFn
@[simp] lemma eraseVec_get {n w k : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) (h : k<w) :
    ((eraseVec v).drop k).headD (0,false)=((v.get k h).gate,(v.get k h).invert) := by
  rw [List.headD_eq_head?_getD,List.head?_drop]
  simp [eraseVec,h]
@[simp] lemma eraseVec_cast {n w : ℕ} {g g' : AIG (Fin n)} (v : AIG.RefVec g w)
    (h : g.decls.size≤g'.decls.size) : eraseVec (v.cast h)=eraseVec v := rfl
@[simp] lemma eraseVec_empty {n : ℕ} (g : AIG (Fin n)) : eraseVec (AIG.RefVec.empty (aig:=g))=[] := rfl
@[simp] lemma eraseVec_push {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) (a : AIG.Ref g) :
    eraseVec (v.push a)=eraseVec v++[(a.gate,a.invert)] := by
  rw [eraseVec,List.ofFn_succ_last]
  congr 1
  · congr 1;funext i
    dsimp only [Fin.val_castSucc]
    rw [AIG.RefVec.get_push_ref_lt _ _ _ i.isLt]
  · simp

def declIsZero : Decl→Bool
  | .zero=>true
  | _=>false
def known (r : Graph) (a : Ref) : Bool:=declIsZero (r.decls[a.1]?.getD .zero)
def countKnown (r : Graph) (as : List Ref) : ℕ := (as.filter (known r)).length
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
@[simp] lemma countKnown_nil (r : Graph) : countKnown r []=0 := rfl
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGAddWrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

namespace Emission
noncomputable def listUnaryLength {α : Type} (ea : α→List Bool) (d : α) :
    Procedure (listCode ea) unaryCode List.length := by
  let step:=unarySuccessor.comp (second ea unaryCode)
  let rep:=foldList d step Polynomial.X (by
    intro xs n i
    change (unaryCode ((xs.take i).foldl (fun n _=>n+1) n)).length≤_
    rw [fold_count]
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X,List.length_take]
    have hh:=list_length_le_code ea xs
    omega)
  let start:=(identity (listCode ea)).pair (Procedure.constant (listCode ea) unaryCode 0)
  exact (rep.comp start).congrFun (by
    intro xs;simpa only [Function.comp_apply,id_eq,Nat.zero_add] using fold_count xs 0)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListMapWith
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β γ : Type}
lemma map_range_getD (xs : List β) (d : β) (f : β→γ) :
    (List.range xs.length).map (fun i=>f ((xs.drop i).headD d))=xs.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map,List.getElem_range]
    have hi : i<xs.length:=by simpa using h1
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi,Option.getD_some]
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool} {f : α→β→γ}
noncomputable def listMapWith (d : β) (e : γ)
    (p : Procedure (prodCode ea eb) ec (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea (listCode eb)) (listCode ec) (fun x=>x.2.map (f x.1)) := by
  let i:=unaryToBits.comp (first unaryCode (prodCode ea (listCode eb)))
  let env:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp env
  let xs:=(second ea (listCode eb)).comp env
  let get:=(listGet eb d).comp (i.pair xs)
  let step:=p.comp (a.pair get)
  let len:=(NativeAIG.Emission.listUnaryLength eb d).comp (second ea (listCode eb))
  exact ((tabulate (f:=fun (env : α×List β) i=>f env.1 ((env.2.drop i).headD d)) e step).comp (len.pair (identity (prodCode ea (listCode eb))))).congrFun (by
    intro x;exact map_range_getD x.2 d (f x.1))
end Procedure
end ExactQuantumFactoring.BitStackProgram

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
inductive Node where
  | constant (b : Bool)
  | copy (i : ℕ)
  | neg (i : ℕ)
  | conj (i j : ℕ)
  deriving DecidableEq, Inhabited

def Node.map (f : ℕ→ℕ) : Node→Node
  | .constant b=>.constant b
  | .copy i=>.copy (f i)
  | .neg i=>.neg (f i)
  | .conj i j=>.conj (f i) (f j)

structure Data where
  inputs : ℕ
  nodes : List Node
  outputs : List ℕ
  deriving Inhabited

def attachRawIndex (width : ℕ) (ρ : List ℕ) (i : ℕ) : ℕ:=
  if i<ρ.length then (ρ.drop i).headD 0 else width+(i-ρ.length)

def comp (a b : Data) : Data:=
  let f:=attachRawIndex (a.inputs+a.nodes.length) a.outputs
  ⟨a.inputs,a.nodes++b.nodes.map (Node.map f),b.outputs.map f⟩

def select (n : ℕ) (xs : List ℕ) : Data:=⟨n,[],xs⟩

def node (n : ℕ) (o : Node) : Data:=⟨n,[o],[n]⟩
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionProcedures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def nodeView : Node→ℕ×Bool×ℕ×ℕ
  | .constant b=>(0,b,0,0)
  | .copy i=>(1,false,i,0)
  | .neg i=>(2,false,i,0)
  | .conj i j=>(3,false,i,j)
def nodePayload:=prodCode Nat.bits (prodCode boolCode (prodCode Nat.bits Nat.bits))
def nodeCode (o : Node) : List Bool:=nodePayload (nodeView o)
def dataView (a : Data) := (a.inputs,a.nodes,a.outputs)
def dataPayload:=prodCode Nat.bits (prodCode (listCode nodeCode) (listCode Nat.bits))
def dataCode (a : Data) : List Bool:=dataPayload (dataView a)

namespace Emission
noncomputable def nodeViewP : Procedure nodeCode nodePayload nodeView:=
  (identity nodePayload).precompose nodeView
noncomputable def nodeBoolP : Procedure nodeCode boolCode (fun o=>(nodeView o).2.1):=
  (first boolCode _).comp ((second Nat.bits _).comp nodeViewP)
noncomputable def nodeLhsP : Procedure nodeCode Nat.bits (fun o=>(nodeView o).2.2.1):=
  (first Nat.bits Nat.bits).comp ((second boolCode _).comp ((second Nat.bits _).comp nodeViewP))
noncomputable def dataViewP : Procedure dataCode dataPayload dataView:=
  (identity dataPayload).precompose dataView
noncomputable def dataInputP : Procedure dataCode Nat.bits Data.inputs:=
  (first Nat.bits _).comp dataViewP
noncomputable def dataNodesP : Procedure dataCode (listCode nodeCode) Data.nodes:=
  (first (listCode nodeCode) _).comp ((second Nat.bits _).comp dataViewP)
noncomputable def dataOutputsP : Procedure dataCode (listCode Nat.bits) Data.outputs:=
  (second (listCode nodeCode) _).comp ((second Nat.bits _).comp dataViewP)
noncomputable def dataPackP : Procedure dataPayload dataCode (fun x=>Data.mk x.1 x.2.1 x.2.2):=
  (identity dataPayload).result (by intro x;rfl)
noncomputable def dataWidthP : Procedure dataCode Nat.bits (fun a=>a.inputs+a.nodes.length):=
  binaryAdd.comp (dataInputP.pair ((listLength nodeCode (.constant false)).comp dataNodesP))

abbrev indexCode:=prodCode Nat.bits (listCode Nat.bits)
noncomputable def attachIndexP : Procedure (prodCode indexCode Nat.bits) Nat.bits
    (fun x=>attachRawIndex x.1.1 x.1.2 x.2) := by
  let env:=first indexCode Nat.bits
  let width:=(first Nat.bits (listCode Nat.bits)).comp env
  let rho:=(second Nat.bits (listCode Nat.bits)).comp env
  let i:=second indexCode Nat.bits
  let len:=(listLength Nat.bits 0).comp rho
  let off:=binarySub.comp (i.pair len)
  let test:=binaryLt.comp (i.pair len)
  let get:=(listGet Nat.bits 0).comp (i.pair rho)
  exact (conditional test get (binaryAdd.comp (width.pair off))).congrFun (by
    intro x;unfold attachRawIndex;split <;> simp_all)
end Emission
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

def bit (n i : ℕ) : Data:=select n [i]
def constant (n : ℕ) (b : Bool) : Data:=node n (.constant b)

namespace Emission
noncomputable def selectP : Procedure (prodCode Nat.bits (listCode Nat.bits)) dataCode
    (fun x=>select x.1 x.2):=
  (dataPackP.comp ((first Nat.bits (listCode Nat.bits)).pair
    ((Procedure.constant _ (listCode nodeCode) []).pair (second Nat.bits (listCode Nat.bits))))).congrFun (by intro x;rfl)
noncomputable def bitP : Procedure (prodCode Nat.bits Nat.bits) dataCode (fun x=>bit x.1 x.2):=
  (selectP.comp ((first Nat.bits Nat.bits).pair
    ((listCons Nat.bits).comp ((second Nat.bits Nat.bits).pair (Procedure.constant _ (listCode Nat.bits) []))))).congrFun (by intro x;rfl)
end Emission
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

def Node.Bound (B : ℕ) : Node→Prop
  | .constant _=>True
  | .copy i=>i≤B
  | .neg i=>i≤B
  | .conj i j=>i≤B ∧ j≤B
lemma Node.Bound.mono {A B : ℕ} {o : Node} (h : o.Bound A) (hab : A≤B) : o.Bound B:=by
  cases o <;> simp only [Node.Bound] at * <;> omega
lemma Node.Bound.map {A B : ℕ} {o : Node} (h : o.Bound A) (f : ℕ→ℕ)
    (hf : ∀i,i≤A→f i≤B) : (o.map f).Bound B:=by
  cases o with
  | constant=>trivial
  | copy i=>exact hf i h
  | neg i=>exact hf i h
  | conj i j=>exact ⟨hf i h.1,hf j h.2⟩
def Data.width (a : Data) : ℕ:=a.inputs+a.nodes.length
def Data.mass (a : Data) : ℕ:=a.width+a.outputs.length
def Data.Valid (a : Data) : Prop := (∀o∈a.nodes,o.Bound a.width) ∧ (∀i∈a.outputs,i≤a.width)
lemma valid_select (n : ℕ) (xs : List ℕ) (h : ∀i∈xs,i≤n) : (select n xs).Valid:=
by
  constructor
  · intro o ho;cases ho
  · exact h
lemma valid_node (n : ℕ) (o : Node) (h : o.Bound n) : (node n o).Valid:=by
  constructor
  · intro p hp
    have he : p=o:=by simpa only [node,List.mem_singleton] using hp
    subst p
    exact h.mono (by simp [Data.width,node])
  · intro i hi
    have he : i=n:=by simpa only [node,List.mem_singleton] using hi
    subst i;simp [Data.width,node]
lemma headD_drop_bound {xs : List ℕ} {B : ℕ} (h : ∀j∈xs,j≤B) (i : ℕ) :
    (xs.drop i).headD 0≤B:=by
  cases hh : (xs.drop i).head? with
  | none=>simp [List.headD_eq_head?_getD,hh]
  | some j=>
    rw [List.headD_eq_head?_getD,hh,Option.getD_some]
    exact h _ (List.mem_of_mem_drop (List.mem_of_head? hh))
lemma attachRawIndex_bound {xs : List ℕ} {wa wb : ℕ} (h : ∀j∈xs,j≤wa)
    (i : ℕ) (hi : i≤xs.length+wb) : attachRawIndex wa xs i≤wa+wb:=by
  unfold attachRawIndex
  split
  · exact (headD_drop_bound h i).trans (by omega)
  · omega
lemma comp_valid {a b : Data} (ha : a.Valid) (hb : b.Valid) (he : a.outputs.length=b.inputs) :
    (comp a b).Valid:=by
  have hw : (comp a b).width=a.width+b.nodes.length:=by simp [Data.width,comp,Nat.add_assoc]
  have hf : ∀i,i≤b.width→attachRawIndex a.width a.outputs i≤(comp a b).width:=by
    intro i hi
    rw [hw]
    apply attachRawIndex_bound ha.2
    simpa only [Data.width,←he] using hi
  constructor
  · intro o ho
    simp only [comp,List.mem_append,List.mem_map] at ho
    rcases ho with ho|⟨p,hp,rfl⟩
    · exact (ha.1 _ ho).mono (by rw [hw];omega)
    · exact (hb.1 _ hp).map _ hf
  · intro i hi
    simp only [comp,List.mem_map] at hi
    obtain ⟨j,hj,rfl⟩:=hi
    exact hf _ (hb.2 _ hj)
lemma comp_mass (a b : Data) : (comp a b).mass≤a.mass+b.mass:=by
  simp only [Data.mass,Data.width,comp,List.length_append,List.length_map];omega
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
structure PackData where
  budget : ℕ
  value : Data
abbrev Pack:={s : PackData // s.value.Valid ∧ s.value.mass ≤ s.budget}
def packCode (s : Pack) : List Bool:=prodCode unaryCode dataCode (s.val.budget,s.val.value)
def compPack (a b : Pack) : Pack:=
  ⟨⟨a.val.budget+b.val.budget,if a.val.value.outputs.length=b.val.value.inputs then comp a.val.value b.val.value else a.val.value⟩,by
    split
    · rename_i h
      exact ⟨comp_valid a.property.1 b.property.1 h,(comp_mass _ _).trans (Nat.add_le_add a.property.2 b.property.2)⟩
    · exact ⟨a.property.1,a.property.2.trans (Nat.le_add_right _ _)⟩⟩

def selectPack (n : ℕ) (xs : List ℕ) (h : ∀i∈xs,i≤n) : Pack:=
  ⟨⟨n+xs.length,select n xs⟩,valid_select n xs h,by simp [Data.mass,Data.width,select]⟩
def nodePack (n : ℕ) (o : Node) (h : o.Bound n) : Pack:=
  ⟨⟨n+2,node n o⟩,valid_node n o h,by simp [Data.mass,Data.width,node]⟩
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def bitPack (n i : ℕ) : Pack:=selectPack n [min n i] (by simp)
def constantPack (n : ℕ) (b : Bool) : Pack:=nodePack n (.constant b) trivial
def bnotPack (a : Pack) : Pack:=compPack a (nodePack 1 (.neg 0) (by simp [Node.Bound]))
namespace Emission
noncomputable def bitPackP : Procedure (prodCode unaryCode Nat.bits) packCode (fun x=>bitPack x.1 x.2):=by
  let n:=first unaryCode Nat.bits
  let i:=second unaryCode Nat.bits
  let nb:=unaryToBits.comp n
  let idx:=conditional (binaryLt.comp (nb.pair i)) nb i
  let v:=bitP.comp (nb.pair idx)
  exact ((unarySuccessor.comp n).pair v).result (by
    intro x
    simp only [Function.comp_apply,id_eq,decide_eq_true_eq]
    by_cases h : x.1<x.2
    · simp only [h,↓reduceIte,bitPack,selectPack,packCode,bit,prodCode,
        min_eq_left (Nat.le_of_lt h),List.length_singleton,Nat.succ_eq_add_one]
    · simp only [h,↓reduceIte,bitPack,selectPack,packCode,bit,prodCode,
        min_eq_right (by omega : x.2≤x.1),List.length_singleton,Nat.succ_eq_add_one])
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGNetworkEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open Std.Sat BooleanNetwork
open NetworkEmission

def faninPack (n gs : ℕ) (f : NativeAIG.Ref) : Pack:=
  let v:=if f.1<gs then bitPack (n+gs) (n+f.1) else constantPack (n+gs) false
  if f.2 then bnotPack v else v
end ExactQuantumFactoring.AIGNetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGNetworkProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open BitStackProgram BitStackProgram.Procedure NetworkEmission
open NetworkEmission.Emission
namespace Emission
abbrev dimsCode:=prodCode unaryCode unaryCode
end Emission
end ExactQuantumFactoring.AIGNetworkEmission

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
structure Op where
  gate : Gate
  wires : List ℕ

structure Data where
  qubits : ℕ
  ops : List Op

end ExactQuantumFactoring.CircuitEmission

end



end OAI
end


