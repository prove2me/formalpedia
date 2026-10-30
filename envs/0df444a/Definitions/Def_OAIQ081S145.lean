-- Prove2me | Definitions.Def_OAIQ081S145
-- name    : OAIQ081S145
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:52:19.397155+00:00
-- url     : https://prove2.me/theorems/f7be4bf8-c1dc-461a-a562-2ea81c7a3620
-- title:
--   Definitions bundle OAIQ081S145 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 19 definitions, 2 inductive types or structures and 31 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.modelTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeNative.originEntries`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.PackingSpare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.staged`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.stagedStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.ScalarOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.TableInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.constantBatchStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.constantResultStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.copyPlanCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.searchAndPad`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.searchCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssembly.EntryInvariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssembly.ValidEntries`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.maskHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.maskPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.outerHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.outerPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.context`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.readyLocal`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.context`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics`, `SubexponentialSAT_SqrtLog_LeafProgramNodeNativeConstants`, `SubexponentialSAT_SqrtLog_LeafProgramQueryPackingEmpty`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramConstantBridge`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrame`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramTableBridge`, `SubexponentialSAT_SqrtLog_MomentsAssemblyProgramUniformBounds`, `SubexponentialSAT_SqrtLog_MomentsAssemblySemanticsValidity`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramCore`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFinish`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramReady`, `SubexponentialSAT_SqrtLog_RingProgramTableBridge`, `SubexponentialSAT_SqrtLog_RingProgramTableCanonical`, `SubexponentialSAT_SqrtLog_RingProgramTableInitial`, `SubexponentialSAT_SqrtLog_RingProgramTableSemantics`, `SubexponentialSAT_Subexp_AssignmentInputProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S121`, `OAIQ081S122`, `OAIQ081S123`, `OAIQ081S125`, `OAIQ081S127`, `OAIQ081S128` and `OAIQ081S129` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S158`, `OAIQ081S159`, `OAIQ081S160`, `OAIQ081S161`, `OAIQ081S163`, `OAIQ081S164` and `OAIQ081S165`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.resume_candidate_ready`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S121
import Definitions.Def_OAIQ081S122
import Definitions.Def_OAIQ081S123
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S127
import Definitions.Def_OAIQ081S128
import Definitions.Def_OAIQ081S129

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and storage bounds for the actual raw dictionaries produced by
native hash-row execution. No canonical-output premise is used. -/


/-! Denotation of the concrete raw row recurrence used by the native program. -/


/-! Instantiation at the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

 def modelTable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t) :=
  (RingProgram.structureTableRun (RingProgram.scalarProgram 3 t M cache)
    (RingProgram.liftCoefficientsRun t a.coefficients).1).1

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

@[simp] theorem innerCounter_state (regs : Fin 8 → Bool) (a : D) (h : High)
    (u : ℕ) (rem : List Bool) :
    (wideState regs a (innerHigh h u rem)).stacks innerPorts.counter = rem := rfl

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def outerPorts : UnaryForPrograms.Ports 8 40 := ⟨33,0,1⟩

def outerHigh (h : High) (z : ℕ) (rem out : List Bool) : High :=
  {h with u:=[],remU:=[],z:=unary z,remZ:=rem,output:=out}

@[simp] theorem outerCounter_state (regs : Fin 8 → Bool) (a : D) (h : High)
    (z : ℕ) (rem out : List Bool) :
    (wideState regs a (outerHigh h z rem out)).stacks outerPorts.counter = rem := rfl

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def maskPorts : UnaryForPrograms.Ports 8 40 := ⟨38,0,1⟩
def maskHigh (h : High) (rem acc : List Bool) : High := {h with tmp2:=rem,mask:=acc}

@[simp] theorem maskCounter_state (regs : Fin 8 → Bool) (a : D) (h : High)
    (rem acc : List Bool) :
    (wideState regs a (maskHigh h rem acc)).stacks maskPorts.counter = rem := rfl

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsAssemblySemanticsValidity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (vars : Finset (Fin n)) (u J : ℕ)

abbrev ValidEntries {B d : ℕ} (entries : List (Product.Entry n B d)) : Prop :=
  ∀ a ∈ entries, Product.ValidKey vars u J a.1

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsAssemblyProgramUniformBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform physical costs on valid, normalized sparse dictionaries.  The
invariant bounds actual serialized intermediate states, not arbitrary tapes.
Assignment production remains a charged native callback. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

abbrev EntryInvariant {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) : Prop :=
  ValidEntries vars u J entries ∧ (Sparse.keys entries).Nodup

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeNativeConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical sparse-one cache is exactly the encoded origin entry. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

def originEntries {n B d : ℕ} (one : RingProgram.Code (Word B) d) : List (Product.Entry n B d) :=
  [(Squarefree.Index.origin,one)]

theorem originEntries_valid {n B d : ℕ} (one : RingProgram.Code (Word B) d)
    (vars : Finset (Fin n)) (u J : ℕ) (hu : 0 < u) (hJ : 0 < J) :
    EntryInvariant vars u J (originEntries one) := by
  constructor
  · intro e he
    simp only [originEntries,List.mem_singleton] at he
    subst e
    simp [Product.ValidKey,Squarefree.Index.origin,Squarefree.Index.Kept,Squarefree.Index.Valid,hu,hJ]
  · simp [originEntries,Squarefree.Sparse.keys]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical input construction for sequential type assignment

All parameters are unary stack data. The fixed program constructs the one-hot
word alphabet, reads its actual first word, derives its packed view, and builds
the exact seed range and dimensions expected by `AssignmentInitProgram`.
-/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls SubexpSetupStorage AssignmentInputCall

def context (r Q delta D E : ℕ) (pairs : List Bool) : AssignmentInitProgram.Context where
  defaultWord := (AssignmentAlphabetSemantics.wordBytes r Q).headD []
  packedAlphabet := (AssignmentAlphabetSemantics.wordBytes r Q).flatten
  alphabetRecords := ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q)
  width := unary (Q * r)
  depth := unary (2 * (delta + 1))
  rawPairs := pairs
  seedRecords := AssignmentSeedRange.seedRecords (seedCount delta D E)
  seedCount := seedCount delta D E

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native alphabet/seed construction followed by actual assignment copying.
The old producer is used at delta=0 so the seed count is exactly ambient+factors;
the new scorer's four-word depth is installed separately. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def context (r Q n f : ℕ) (pairs : List Bool) :=
  AssignmentInputProgram.context r Q 0 n f pairs

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Install the packing scorer's depth and binary parameter bank after the
native alphabet/assignment producer has finished using its low workspace. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage SubexponentialSAT.Subexp
attribute [local simp] Fin.coe_ofNat_eq_mod

def readyLocal (regs : Fin 16 → Bool) (r Q n f : ℕ) (pairs nb sb mb rb : List Bool) : State 16 48 :=
  ⟨regs,fun i => if i=20 then nb else if i=21 then sb else if i=22 then mb
    else if i=23 then rb else if i=34 then List.replicate 4 true
    else (AssignmentInitProgram.outputState (context r Q n f pairs)).stacks i⟩

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact selector memory and environment from the physically generated
alphabet, retaining all ambient head addresses before factor addresses. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

@[simp] theorem ready_remaining (regs : Fin 16 → Bool) (r Q n f : ℕ)
    (pairs nb sb mb rb : List Bool) :
    ((readyLocal regs r Q n f pairs nb sb mb rb).stacks 11).length=n+f := by
  simp [readyLocal,AssignmentInitProgram.outputState,AssignmentInitProgram.state,
    context,AssignmentInputProgram.context,AssignmentInputProgram.seedCount,
    AssignmentInitProgram.unary,Nat.add_comm]

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryPackingEmpty
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The only untouched destinations needed by packing after the frontend. -/
def PackingSpare (a : Data) : Prop :=
  a.stacks 684=[] ∧ a.stacks 133=[] ∧ a.stacks 135=[] ∧ a.stacks 136=[] ∧
    ∀ i,a.stacks (LayoutMasters.high i)=[]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableInitial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem literalLast_independent {B : ℕ} (n : ℕ) (hn : 0 < n) (seed zeroWord : Word B)
    (x y : List Bool) : literalLast n seed zeroWord x = literalLast n seed zeroWord y := by
  cases n with
  | zero => omega
  | succ n => rfl

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem tailCorrect_get {B d : ℕ} (hd : 0 < d) (v : VectorData B d)
    (hv : TailCorrect v) :
    v.last = v.coefficients.get ⟨d-1, by omega⟩ := by
  have hne : v.coefficients.val ≠ [] := by
    intro he
    have h := v.coefficients.property
    rw [he] at h
    simp at h
    omega
  have hv' : (List.ofFn v.coefficients.get).getLast? = some v.last := by
    rw [listOfFn_get]
    exact hv
  have hne' : List.ofFn v.coefficients.get ≠ [] := by
    simpa only [listOfFn_get] using hne
  rw [List.getLast?_eq_getLast_of_ne_nil hne', List.getLast_ofFn] at hv'
  exact (Option.some.inj hv').symm

theorem initialData_get {B d : ℕ} (oneWord zeroWord : Word B) (i : Fin d) :
    (initialData d oneWord zeroWord).coefficients.get i =
      if i.val = 0 then oneWord else zeroWord := by
  have hv : (initialData d oneWord zeroWord).coefficients =
      List.Vector.ofFn (fun i : Fin d => if i.val = 0 then oneWord else zeroWord) := by
    apply Subtype.ext
    change literalWords d oneWord zeroWord =
      (List.Vector.ofFn (fun i : Fin d => if i.val = 0 then oneWord else zeroWord)).toList
    rw [List.Vector.toList_ofFn]
    exact literalWords_ofFn d oneWord zeroWord
  rw [hv]
  exact List.Vector.get_ofFn _ _

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableCanonical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t)

theorem powerData_canonical {d : ℕ} (c : List.Vector (Word (baseWidth p t)) d)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (ho : BinaryArithmetic.toNat cache.one.val < p^t)
    (n : ℕ) (i : Fin d) :
    BinaryArithmetic.toNat ((iterData p t M cache.zero cache.minusOne c n
      (initialData d cache.one cache.zero)).coefficients.get i).val < p^t := by
  cases n with
  | zero =>
    change BinaryArithmetic.toNat ((initialData d cache.one cache.zero).coefficients.get i).val < p^t
    rw [initialData_get]
    split <;> assumption
  | succ n =>
    rw [iterData_succ]
    exact advance_canonical p t M cache.zero cache.minusOne c _ i

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- The native power accumulator is exactly the forward record layout consumed
by the indexed table-layout machine. -/
theorem generatedBits_eq_powerRecords (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ}
    (zeroWord minusOne : Word (baseWidth p t)) (c : List.Vector (Word (baseWidth p t)) d)
    (n : ℕ) (v : VectorData (baseWidth p t) d) :
    wordBits v.coefficients.val ++ generatedBits p t M zeroWord minusOne c n v =
      (RingTableLayout.powerRecords
        (fun j => (iterData p t M zeroWord minusOne c j v).coefficients.get) (n+1)).flatten := by
  induction n generalizing v with
  | zero =>
    simp only [generatedBits, RingTableLayout.powerRecords, List.ofFn_succ,
      List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil,
 iterData, vectorRecords_flat]
  | succ n ih =>
    rw [powerRecords_succ, List.flatten_append]
    change wordBits v.coefficients.val ++ (wordBits (advance p t M zeroWord minusOne c v).coefficients.val ++
      generatedBits p t M zeroWord minusOne c n (advance p t M zeroWord minusOne c v)) =
      (List.ofFn (fun i => (v.coefficients.get i).val)).flatten ++
        (RingTableLayout.powerRecords
          (fun j => (iterData p t M zeroWord minusOne c j (advance p t M zeroWord minusOne c v)).coefficients.get) (n+1)).flatten
    rw [vectorRecords_flat, ← ih]

theorem allPowerBits_eq_powerRecords (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (c : List.Vector (Word (baseWidth p t)) d) (oneWord zeroWord minusOne : Word (baseWidth p t)) :
    allPowerBits p t M c oneWord zeroWord minusOne =
      (RingTableLayout.powerRecords (fun j =>
        (iterData p t M zeroWord minusOne c j (initialData d oneWord zeroWord)).coefficients.get)
        (2*d-1)).flatten := by
  have hn : (2*d-2)+1 = 2*d-1 := by omega
  simpa only [allPowerBits, hn] using
    generatedBits_eq_powerRecords p t M zeroWord minusOne c (2*d-2) (initialData d oneWord zeroWord)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/- Component: LeafRingSetupProgramScalar.lean -/

/-! The first concrete stage of ring setup.  Only the runtime binary
precision is supplied.  The generated scalar cache remains exposed while
the extension-ring table and constants are built.  The idempotent producer
later uses a separately framed preparation, with its own charged cost. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls SubexpQuarticRing
open IdempotentPreparationProgram

structure ScalarOutput (t : ℕ) (bits : List Bool)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u : RingProgram.ScalarCode 3 t) (logword : List Bool)
    (out : IdempotentPreparationProgram.Data) : Prop where
  prepared : Scalar.Prepared t M cache u out
  logValue : CounterPrograms.value logword = Nat.clog 2 t
  logLength : logword.length ≤ bits.length + 1
  unchanged : ∀ j, (∀ i, Scalar.port i ≠ j) →
    out.stacks j = bootStacks t bits M.bits logword j

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram


/- Component: LeafRingSetupProgramSearch.lean -/

/-! Actual irreducible search followed by coefficient padding.  The model
below is the one selected by the finite search, not a supplied polynomial. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing


abbrev searchCall : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram IrreducibleSearchBootstrap.searchProgram
    (registers 22 (by decide)) search)

/-- Padding is executed on the actual caller workspace.  Every stack other
than source13 and output21 is preserved, including the original degree14. -/
theorem paddingCall_eval (a : Data) (t : ℕ) (ht : 0 < t)
    (d : ℕ) (hd : 0 < d)
    (hr : RingCoefficientLiftProgram.SearchReady
      (projectState (registers 22 (by decide)) search a))
    (hi : a.stacks 195 = IrreducibleSearchProgram.coefficientArray
      (List.ofFn (IrreducibleSearch.data hd).coefficients))
    (hw : (a.stacks 432).length = baseWidth 3 t) :
    ∃ out : Data, Eval paddingCall (d*(28*t+14)+7) a out ∧
      out.stacks = Function.update (Function.update a.stacks 195 []) 441
        (RingProgram.flat (RingProgram.liftCoefficientsRun t
          (IrreducibleSearch.data hd).coefficients).1) := by
  let localState := projectState (registers 22 (by decide)) search a
  obtain ⟨e,he,hs,hregs⟩ := RingCoefficientLiftProgram.searchCommand_eval t ht
    (IrreducibleSearch.data hd).coefficients localState hr
    (by simpa [localState,projectState,search] using hi)
    (by simpa [localState,projectState,search] using hw)
  refine ⟨embedState (registers 22 (by decide)) search a e,?_,?_⟩
  · simpa [paddingCall,Nat.add_assoc] using
      eval_liftCommand_from_state RingCoefficientLiftProgram.searchCommand 13 21
        (registers 22 (by decide)) search a (registers_injective 22 (by decide))
        search_injective he
  · change Function.extend search e.stacks a.stacks = _
    rw [hs,ProgramLinking.extend_update search_injective,
      ProgramLinking.extend_update search_injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project (registers 22 (by decide)) search a
        (registers_injective 22 (by decide)) search_injective)
    change Function.extend search localState.stacks a.stacks = a.stacks at hb
    rw [hb]
    rfl

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramTable.lean -/

/-! Table generation for the cache produced by the native scalar stage.
The cache is not replaced by a separately chosen mathematical cache. -/

/-! Physical node generation and record framing at the ring-setup ports. -/

/-! Actual constant-vector and idempotent calls in the setup workspace. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

theorem constantCall_eval (a : Data) (out : Fin 640)
    (hinj : Function.Injective (constant out))
    {B : ℕ} (d : ℕ) (seed zeroWord : Word B) (s : RingProgramTable.Store)
    (r : Fin 8 → Bool) (hd : s.degree.length=d)
    (ha : projectState (registers 8 (by decide)) (constant out) a =
      RingProgramTable.state r (LeafProgram.Constants.input s seed zeroWord)) :
    ∃ n ≤ LeafProgram.Constants.budget B d+1, ∃ rf,
      Eval (constantCall out) n a
        (embedState (registers 8 (by decide)) (constant out) a
          (RingProgramTable.state rf (LeafProgram.Constants.output s d seed zeroWord))) := by
  obtain ⟨rf,n,hn,he⟩ := LeafProgram.Constants.program_run d seed zeroWord s r hd
  exact ⟨n,hn,rf,eval_call_from_state LeafProgram.Constants.program
    (registers 8 (by decide)) (constant out) a (registers_injective 8 (by decide))
    hinj (ha.symm ▸ he)⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramConstantBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing

/-- This form of the constant service exposes its complete physical write
set: the consumed seed and one output.  All other local and global tapes
are retained, so the three calls can safely reuse the same workspace. -/
theorem constantCall_produces (a : Data) (out : Fin 640)
    (hi : Function.Injective (constant out)) {B : ℕ}
    (seed zeroWord : Word B)
    (hseed : a.stacks 538=seed.val) (hzero : a.stacks 203=zeroWord.val)
    (hc : ∀ i∈constantScratch, a.stacks (constant out i)=[]) :
    ∃ n ≤ LeafProgram.Constants.budget B (a.stacks 204).length+1,
      ∃ e : Data, Eval (constantCall out) n a e ∧
      e.stacks=Function.update (Function.update a.stacks 538 []) out
        (RingProgramTable.literalBits (a.stacks 204).length seed zeroWord) := by
  let s := constantStore out a
  let r := (projectState (registers 8 (by decide)) (constant out) a).regs
  have hin : projectState (registers 8 (by decide)) (constant out) a =
      RingProgramTable.state r (LeafProgram.Constants.input s seed zeroWord) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [ RingProgramTable.tapes,
          LeafProgram.Constants.input, s, constantStore, constant,
          hseed, hzero]
      all_goals first
        | exact hc 1 (by decide)
        | exact hc 2 (by decide)
        | exact hc 3 (by decide)
        | exact hc 4 (by decide)
        | exact hc 6 (by decide)
        | exact hc 7 (by decide)
        | exact hc 8 (by decide)
        | exact hc 11 (by decide)
        | exact hc 13 (by decide)
        | exact hc 14 (by decide)
        | exact hc 15 (by decide)
        | exact hc 19 (by decide)
        | exact hc 20 (by decide)
        | exact hc 23 (by decide)
  obtain ⟨n,hn,rf,he⟩ := constantCall_eval a out hi (a.stacks 204).length
    seed zeroWord s r rfl hin
  refine ⟨n,hn,_,he,?_⟩
  have hlocal :
      (RingProgramTable.state rf
        (LeafProgram.Constants.output s (a.stacks 204).length seed zeroWord)).stacks =
      Function.update (Function.update
        (projectState (registers 8 (by decide)) (constant out) a).stacks 0 []) 15
        (RingProgramTable.literalBits (a.stacks 204).length seed zeroWord) := by
    rw [hin]
    funext i
    fin_cases i <;> simp [RingProgramTable.tapes,
      LeafProgram.Constants.output,LeafProgram.Constants.input]
  change Function.extend (constant out) _ a.stacks = _
  rw [hlocal,ProgramLinking.extend_update hi,ProgramLinking.extend_update hi]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project (registers 8 (by decide)) (constant out) a
      (registers_injective 8 (by decide)) hi)
  change Function.extend (constant out)
    (projectState (registers 8 (by decide)) (constant out) a).stacks a.stacks=a.stacks at hb
  rw [hb]
  rfl

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramTableBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical table-input projection and the exact native table-call bridge. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing RingProgramTable

/-- Physical inputs to the table producer. The polynomial bytes are supplied
by `searchAndPad_eval`, and the scalar bytes by `scalarCall_eval`. -/
structure TableInput (t d : ℕ) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (a : LeafRingSetupProgram.Data) : Prop where
  modulus : a.stacks 194=M.bits
  width : (a.stacks 202).length=baseWidth 3 t
  degree : (a.stacks 204).length=d
  seed : a.stacks 538=cache.one.val
  zero : a.stacks 203=cache.zero.val
  minusOne : a.stacks 508=cache.minusOne.val
  coefficients : a.stacks 441=wordBits (modelCoefficients t model).val
  clean : ∀ i : Fin 42, i ∉ ([0,5,12,17,21,22,24] : List (Fin 42)) →
    a.stacks (LeafRingSetupProgram.table i)=[]

theorem TableInput.project {t d : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {a : LeafRingSetupProgram.Data} (h : TableInput t d model M cache a) :
    projectState (registers 8 (by decide)) LeafRingSetupProgram.table a =
      Machine.state (a.regs ∘ registers 8 (by decide))
        (initialStore (tableInputStore a) (modelCoefficients t model)
          cache.one cache.zero cache.minusOne) [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  have hc := h.clean i
  fin_cases i <;>
    simp [LeafRingSetupProgram.table,tapes,initialStore,
      tableInputStore,h.seed,h.zero,h.minusOne,h.coefficients] at hc ⊢
  all_goals exact hc


end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing StackRoutines

abbrev searchAndPad : Cmd 32 640 :=
  .seq searchCall (.seq (overwrite 202 432) paddingCall)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram



namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing StackRoutines

theorem buildConstant_eval (a : Data) (src out : Fin 640)
    (hi : Function.Injective (constant out))
    (hs538 : src≠538) (hs639 : src≠639)
    {B : ℕ} (seed zeroWord : Word B)
    (hseed : a.stacks src=seed.val) (hzero : a.stacks 203=zeroWord.val)
    (h538 : a.stacks 538=[]) (h639 : a.stacks 639=[])
    (hc : ∀ i∈constantScratch, a.stacks (constant out i)=[]) :
    ∃ n ≤ 7*B+8+(LeafProgram.Constants.budget B (a.stacks 204).length+1),
      ∃ e : Data, Eval (buildConstant src out) n a e ∧
      e.stacks=Function.update (Function.update a.stacks 538 []) out
        (RingProgramTable.literalBits (a.stacks 204).length seed zeroWord) := by
  let b : Data := ⟨readRegs a.regs 30 31 none,Function.update a.stacks 538 (a.stacks src)⟩
  have hp : Eval (overwrite src 538) (7*B+8) a b := by
    simpa [b,h538,hseed,seed.property] using overwrite_eval src 538 a hs538 hs639 (by decide) h639
  have hclean : ∀ i∈constantScratch, b.stacks (constant out i)=[] := by
    intro i himem
    have hn : constant out i≠538 := by
      intro he
      have he' : constant out i=constant out 0 := he
      have hz := hi he'
      subst i
      simp [constantScratch] at himem
    simpa [b,hn] using hc i himem
  obtain ⟨nc,hnc,e,he,hout⟩ := constantCall_produces b out hi seed zeroWord
    (by simpa [b] using hseed) (by simpa [b] using hzero) hclean
  refine ⟨7*B+8+nc,?_,e,hp.seq he,?_⟩
  · simpa [b] using Nat.add_le_add_left hnc (7*B+8)
  · simpa [b,Function.update_idem] using hout

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing

def constantBatchStacks {B : ℕ} (a : Data) (one minusOne zero : Word B) :
    Fin 640 → List Bool :=
  Function.update (Function.update (Function.update (Function.update a.stacks 538 [])
    207 (RingProgramTable.literalBits (a.stacks 204).length one zero))
    211 (RingProgramTable.literalBits (a.stacks 204).length minusOne zero))
    280 (RingProgramTable.literalBits (a.stacks 204).length zero zero)

theorem constantBatch_eval (a : Data) {B : ℕ} (one minusOne zero : Word B)
    (h1 : a.stacks 498=one.val) (hm : a.stacks 508=minusOne.val)
    (hz : a.stacks 203=zero.val) (h538 : a.stacks 538=[]) (h639 : a.stacks 639=[])
    (hc : ∀ out∈([207,211,280] : List (Fin 640)),
      ∀ i∈constantScratch,a.stacks (constant out i)=[]) :
    ∃ n ≤ 3*(7*B+8+(LeafProgram.Constants.budget B (a.stacks 204).length+1)),
      ∃ e : Data, Eval constantBatch n a e ∧ e.stacks=constantBatchStacks a one minusOne zero := by
  obtain ⟨n1,hn1,a1,he1,hs1⟩ := buildConstant_eval a 498 207 constant_one_injective
    (by decide) (by decide) one zero h1 hz h538 h639 (hc _ (by simp))
  have hc2 : ∀ i∈constantScratch, a1.stacks (constant 211 i)=[] := by
    intro i hi
    rw [hs1]
    have hbase := hc 211 (by simp) i hi
    have h538' : constant 211 i≠538 := by
      intro hh
      have hh' : i=0 := constant_minusOne_injective hh
      subst i
      simp [constantScratch] at hi
    have h207 : constant 211 i≠207 := by fin_cases i <;> decide
    rw [Function.update_of_ne h207,Function.update_of_ne h538']
    exact hbase
  obtain ⟨n2,hn2,a2,he2,hs2⟩ := buildConstant_eval a1 508 211 constant_minusOne_injective
    (by decide) (by decide) minusOne zero (by simpa [hs1] using hm)
    (by simpa [hs1] using hz) (by simp [hs1]) (by simpa [hs1] using h639) hc2
  have hc3 : ∀ i∈constantScratch, a2.stacks (constant 280 i)=[] := by
    intro i hi
    rw [hs2,hs1]
    have hbase := hc 280 (by simp) i hi
    have h538' : constant 280 i≠538 := by
      intro hh
      have hh' : i=0 := constant_zero_injective hh
      subst i
      simp [constantScratch] at hi
    have h207 : constant 280 i≠207 := by fin_cases i <;> decide
    have h211 : constant 280 i≠211 := by fin_cases i <;> decide
    simp only [Function.update_of_ne h207,Function.update_of_ne h211,Function.update_of_ne h538']
    exact hbase
  obtain ⟨n3,hn3,e,he3,hs3⟩ := buildConstant_eval a2 203 280 constant_zero_injective
    (by decide) (by decide) zero zero (by simpa [hs2,hs1] using hz)
    (by simpa [hs2,hs1] using hz) (by simp [hs2]) (by simpa [hs2,hs1] using h639) hc3
  refine ⟨n1+(n2+n3),?_,e,he1.seq (he2.seq he3),?_⟩
  · simp only [hs1,hs2,Function.update_of_ne (by decide : (204 : Fin 640)≠211),
      Function.update_of_ne (by decide : (204 : Fin 640)≠207),
      Function.update_of_ne (by decide : (204 : Fin 640)≠538)] at hn2 hn3
    omega
  · funext i
    simp only [hs3,hs2,hs1,constantBatchStacks]
    by_cases h538' : i=538 <;> by_cases h207 : i=207 <;>
      by_cases h211 : i=211 <;> by_cases h280 : i=280 <;>
      simp_all only [Function.update_apply,Fin.reduceEq,ite_true, if_true,ite_false,not_false_eq_true]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls StackRoutines

def copyPlanCost : List (Fin 640 × Fin 640) → Data → ℕ
  | [],_ => 0
  | p::ps,a => 2*(a.stacks p.2).length+7*(a.stacks p.1).length+8+
      copyPlanCost ps (copied p a)

theorem copyPlanCost_bound (ps : List (Fin 640 × Fin 640)) (a : Data) (W : ℕ)
    (hw : ∀ i,(a.stacks i).length ≤ W) :
    copyPlanCost ps a ≤ ps.length*(9*W+8) := by
  induction ps generalizing a with
  | nil => simp [copyPlanCost]
  | cons p ps ih =>
    have hb : ∀ i,((copied p a).stacks i).length ≤ W := by
      intro i
      by_cases hi : i=p.2
      · simpa [copied,hi] using hw p.1
      · simpa [copied,hi] using hw i
    have ht := ih (copied p a) hb
    have hs := hw p.1
    have hd := hw p.2
    simp only [copyPlanCost,List.length_cons]
    nlinarith

theorem copiedPlan_frame (ps : List (Fin 640 × Fin 640)) (a : Data) (i : Fin 640)
    (hi : ∀ p∈ps,i≠p.2) : (copiedPlan ps a).stacks i=a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [copiedPlan,ih (copied p a) (fun q hq => hi q (by simp [hq]))]
    simp [copied,hi p (by simp)]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing

def constantResultStacks {B : ℕ} (a : Data) (one minusOne zero : Word B) :
    Fin 640 → List Bool :=
  let a0 := clearedPorts constantStartPorts a
  (copiedPlan constantAliases
    ⟨a0.regs,constantBatchStacks a0 one minusOne zero⟩).stacks

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Paid staging of the native interpolation-cache producer in the wide
leaf machine. The private 320-tape bank is disjoint from all ring and
collector masters. Native table computation is followed by paid extraction
of all five outputs; the entire staging bank is then cleared. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation
open BitProgram StructuredCalls StackRoutines SubexpLiftRing SubexpQuarticRing

theorem copy_eval (src dst : Fin 768) (a : Data)
    (hsd : src ≠ dst) (hs : src ≠ 699) (hd : (699 : Fin 768) ≠ dst)
    (hw : a.stacks 699 = []) :
    Eval (copy src dst) (7*(a.stacks src).length+5) a
      ⟨readRegs a.regs 38 39 none,
        Function.update a.stacks dst (a.stacks src ++ a.stacks dst)⟩ :=
  Subexp.TupleProgram.copy_eval src dst 699 38 39 hsd hs hd (by decide) a hw

/-- Clear the destination before copying.  This supports reuse of physical
scratch without requiring its previous value to vanish for free. -/
theorem overwrite_eval (src dst : Fin 768) (a : Data)
    (hsd : src ≠ dst) (hs : src ≠ 699) (hd : (699 : Fin 768) ≠ dst)
    (hw : a.stacks 699 = []) :
    Eval (overwrite src dst) (2*(a.stacks dst).length+7*(a.stacks src).length+8) a
      ⟨readRegs a.regs 38 39 none, Function.update a.stacks dst (a.stacks src)⟩ := by
  let b : Data := ⟨readRegs a.regs 38 39 none, Function.update a.stacks dst []⟩
  have hc := clear_eval dst a
  have hp := copy_eval src dst b hsd hs hd (by simpa [b, hd] using hw)
  convert hc.seq hp using 1 <;>
    simp [ b, hsd, readRegs_reset] ; omega


theorem copyPlan_eval (ps : List (Fin 768 × Fin 768)) (a : Data)
    (hports : ∀ p∈ps,p.1≠p.2 ∧ p.1≠699 ∧ p.2≠699)
    (hwork : a.stacks 699=[]) :
    Eval (copyPlan ps) (copyPlanCost ps a) a (copiedPlan ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip _)
  | cons p ps ih =>
    have hp := hports p (by simp)
    have he := overwrite_eval p.1 p.2 a hp.1 hp.2.1 (Ne.symm hp.2.2) hwork
    have ht := ih (copied p a) (fun q hq => hports q (by simp [hq]))
      (by simpa [copied,hp.2.2,Ne.symm hp.2.2] using hwork)
    exact he.seq ht

theorem copyPlanCost_bound (ps : List (Fin 768 × Fin 768)) (a : Data) (W : ℕ)
    (hw : ∀ i,(a.stacks i).length ≤ W) :
    copyPlanCost ps a ≤ ps.length*(9*W+8) := by
  induction ps generalizing a with
  | nil => simp [copyPlanCost]
  | cons p ps ih =>
    have hb : ∀ i,((copied p a).stacks i).length ≤ W := by
      intro i
      by_cases hi : i=p.2
      · simpa [copied,hi] using hw p.1
      · simpa [copied,hi] using hw i
    have ht := ih (copied p a) hb
    have hs := hw p.1
    have hd := hw p.2
    simp only [copyPlanCost,List.length_cons]
    nlinarith

theorem copiedPlan_frame (ps : List (Fin 768 × Fin 768)) (a : Data) (i : Fin 768)
    (hi : ∀ p∈ps,i≠p.2) : (copiedPlan ps a).stacks i=a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [copiedPlan,ih (copied p a) (fun q hq => hi q (by simp [hq]))]
    simp [copied,hi p (by simp)]



/-- Caller preparation is a concrete clear/copy program. Its logical store
is named only to state the interface to the native cache producer. -/
def staged (base : Data) : Data :=
  copiedPlan inputPlan (clearedPorts (699::privatePorts) base)

def stagedStore (base : Data) : InterpolationCacheProgram.Store :=
  fun i => (staged base).stacks (localPorts i)

/-- Exact input-byte certificate for the paid staging operation. -/
theorem stagedStore_eq (base : Data) (i : Fin 320) :
    stagedStore base i=((inputIndex i).map base.stacks).getD [] := by
  have hz : (clearedPorts (699::privatePorts) base).stacks (localPorts i)=[] := by
    simp only [clearedPorts_stacks]
    simp [privatePorts_mem i]
  have hl (j : Fin 768) (hj : j.val < 340) :
      (clearedPorts (699::privatePorts) base).stacks j=base.stacks j := by
    have hn := privatePorts_not_low j hj
    have h699 : j≠699 := by
      intro he
      subst j
      change (699 : ℕ) < 340 at hj
      omega
    simp [clearedPorts_stacks,hn,h699]
  have h280 := hl 280 (by decide)
  have h194 := hl 194 (by decide)
  have h201 := hl 201 (by decide)
  have h202 := hl 202 (by decide)
  have h203 := hl 203 (by decide)
  have h204 := hl 204 (by decide)
  have h207 := hl 207 (by decide)
  have h209 := hl 209 (by decide)
  have h211 := hl 211 (by decide)
  have h212 := hl 212 (by decide)
  have h256 := hl 256 (by decide)
  by_cases h104 : i = 104
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h194i : i = 194
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h201i : i = 201
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h202i : i = 202
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h203i : i = 203
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h204i : i = 204
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h207i : i = 207
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h209i : i = 209
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h211i : i = 211
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h212i : i = 212
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  by_cases h256i : i = 256
  · subst i
    simp [stagedStore,staged,inputIndex,inputPlan,copiedPlan,copied,
      localPorts,h280,h194,h201,h202,h203,h204,h207,h209,h211,h212,h256]
  have hv104 : i.val ≠ 104 := fun h => h104 (Fin.ext h)
  have hv194 : i.val ≠ 194 := fun h => h194i (Fin.ext h)
  have hv201 : i.val ≠ 201 := fun h => h201i (Fin.ext h)
  have hv202 : i.val ≠ 202 := fun h => h202i (Fin.ext h)
  have hv203 : i.val ≠ 203 := fun h => h203i (Fin.ext h)
  have hv204 : i.val ≠ 204 := fun h => h204i (Fin.ext h)
  have hv207 : i.val ≠ 207 := fun h => h207i (Fin.ext h)
  have hv209 : i.val ≠ 209 := fun h => h209i (Fin.ext h)
  have hv211 : i.val ≠ 211 := fun h => h211i (Fin.ext h)
  have hv212 : i.val ≠ 212 := fun h => h212i (Fin.ext h)
  have hv256 : i.val ≠ 256 := fun h => h256i (Fin.ext h)
  change (copiedPlan inputPlan (clearedPorts (699::privatePorts) base)).stacks
      (localPorts i) = ((inputIndex i).map base.stacks).getD []
  rw [copiedPlan_frame inputPlan]
  · simpa [stagedStore,staged,inputIndex,h104,h194i,h201i,h202i,h203i,h204i,
      h207i,h209i,h211i,h212i,h256i] using hz
  · intro p hp
    simp only [inputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      intro he <;> have hh := congrArg Fin.val he <;> dsimp [localPorts] at hh <;> omega

/-- All native workspace assumptions follow from literal empty staged
bytes. This fact makes no assumption about the caller's previous scratch. -/
theorem staged_inputEmpty (base : Data) :
    ∀i∈InterpolationCacheProgram.inputEmpty,stagedStore base i=[] := by
  intro i hi
  rw [stagedStore_eq]
  simp only [InterpolationCacheProgram.inputEmpty,List.mem_cons,
    List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem copied_width (ps : List (Fin 768 × Fin 768)) (a : Data) (W : ℕ)
    (hw : ∀i,(a.stacks i).length ≤ W) :
    ∀i,((copiedPlan ps a).stacks i).length ≤ W := by
  induction ps generalizing a with
  | nil => exact hw
  | cons p ps ih =>
    apply ih
    intro i
    by_cases hi : i=p.2
    · simpa [copied,hi] using hw p.1
    · simpa [copied,hi] using hw i

theorem eval_width {c : Cmd 40 768} {n W : ℕ} {a e : Data}
    (he : Eval c n a e) (hw : ∀i,(a.stacks i).length ≤ W) :
    ∀i,(e.stacks i).length ≤ W+n+1 := by
  intro i
  have h := Subexp.SequentialProgram.trace_stack_length_le (compiled_halt_trace he 0 0) i
  simp only [] at h
  have := hw i
  omega

theorem copied_register_frame (ps : List (Fin 768 × Fin 768)) (a : Data)
    (i : Fin 40) (h38 : i≠38) (h39 : i≠39) :
    (copiedPlan ps a).regs i=a.regs i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [copiedPlan,ih]
    simp [copied,readRegs,h38,h39]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The ring producer can clear low arithmetic workspace, but never inserts
data there.  Thus initially blank low node-work tapes stay blank.  This is a
property of the existing program, not an additional cleanup operation. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame
open BitProgram StructuredCalls

theorem unaryPlan (ps : List (Fin 640 × Fin 640)) (i : Fin 640) (hi : i.val < 190)
    (hp : ∀ p∈ps,190 ≤ p.1.val ∧ 190 ≤ p.2.val) :
    EmptyPreserved (LeafRingSetupProgram.unaryPlan ps) i := by
  induction ps with
  | nil => exact skip i
  | cons p ps ih =>
    exact seq (unary p.1 p.2 i hi (hp p (by simp)).1 (hp p (by simp)).2)
      (ih (fun q hq => hp q (by simp [hq])))

theorem buildConstant (src out i : Fin 640) (hi : i.val < 190)
    (hs : 190 ≤ src.val) (ho : 190 ≤ out.val) :
    EmptyPreserved (LeafRingSetupProgram.buildConstant src out) i := by
  apply seq (overwrite src 538 i hi hs (by decide))
  apply highLift _ _ _ i hi
  intro j
  unfold constant
  split_ifs <;> (try dsimp only) <;> omega

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame

end OAI.Algorithms
end


