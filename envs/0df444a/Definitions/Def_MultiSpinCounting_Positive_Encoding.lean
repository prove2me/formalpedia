-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_Encoding
-- name    : MultiSpinCounting_Positive_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:20:38.709908+00:00
-- url     : https://prove2.me/theorems/dcb83738-9cf5-4978-81d0-5d0ce3bd3848
-- title:
--   Binary serialization and finite deterministic bit-machine semantics
-- statement:
--   The alphabet consists of bits and two separators. Natural numbers are binary; rational numbers are reduced numerator–denominator pairs. Vectors and matrices list their entries. An instance encoding lists the ambient size, spin count, active vertex labels, each active edge with its interaction matrix, and each active external field. It contains no partition function, marginal or computed answer. Define
--   $$|\Phi|=|\operatorname{encInstance}(\Phi)|,\qquad \operatorname{bit}(r)=|\operatorname{encRat}(r)|.$$
--   Vector and matrix bit lengths are sums of entry lengths. The goal input appends the binary rational tolerance after a separator.
--
--   A bit machine has finitely many stacks, a finite alphabet on every stack, finitely many labels and finite control. A run asserts actual execution of this fixed machine on the encoded input, halting with the encoded output within a witnessed number of steps. It does not assert an arbitrary output–time relation. This interface charges input parsing, arithmetic and output through machine execution.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 3, computation model; p. 18, bit-length convention

import Mathlib
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_MultiSpinCounting_Positive_Instance
import Definitions.Def_RobustToDynamics_encMat

noncomputable section

namespace MultiSpinCounting.Positive
open OnlineCRS.Combine

/-- A fixed finite bit machine: FinTM2 alone only guarantees a finite input alphabet. -/
structure BitMachine where
  code : Turing.TM2ComputableAux Sym Sym
  finiteStacks : ∀ k : code.tm.K, Finite (code.tm.Γ k)

def Runs (M : BitMachine) (input output : List Sym) (steps : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime M.code.tm
    (input.map M.code.inputAlphabet.symm) (some (output.map M.code.outputAlphabet.symm)) steps)

def encMatrix {q : ℕ} (A : Fin q → Fin q → ℚ) : List Sym :=
  RobustToDynamics.encMat A

def vectorBits {q : ℕ} (x : Fin q → ℚ) : ℕ := ∑ a, (encRat (x a)).length

def matrixBits {q : ℕ} (A : Fin q → Fin q → ℚ) : ℕ := ∑ a, vectorBits (A a)

/-- Serialization only: ambient size, q, active labels, edge list with matrices, then fields.
Every individual natural ends at a separator. No partition function or marginal is encoded. -/
def encInstance {n q : ℕ} (Φ : Instance n q ℚ) : List Sym :=
  encNat n ++ [3] ++ encNat q ++ [3] ++ encNat Φ.active.card ++ [3] ++
  ((Φ.active.sort (· ≤ ·)).flatMap (fun v => encNat v.val ++ [3])) ++
  encNat (edges Φ).card ++ [3] ++
  (((edges Φ).toList.mergeSort (fun e f => decide (e.1.val*n+e.2.val ≤ f.1.val*n+f.2.val))).flatMap (fun e =>
    encNat e.1.val ++ [3] ++ encNat e.2.val ++ [3] ++ encMatrix (Φ.interaction e.1 e.2))) ++
  ((Φ.active.sort (· ≤ ·)).flatMap (fun v => encVec (Φ.field v)))

def inputEncoding {n q : ℕ} (Φ : Instance n q ℚ) (ε : ℚ) : List Sym :=
  encInstance Φ ++ [3] ++ encRat ε

end MultiSpinCounting.Positive


