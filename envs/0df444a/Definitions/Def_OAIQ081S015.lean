-- Prove2me | Definitions.Def_OAIQ081S015
-- name    : OAIQ081S015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:24:07.369487+00:00
-- url     : https://prove2.me/theorems/3e033002-dba1-4e0f-91c2-9f8c7c6151a4
-- title:
--   Definitions bundle OAIQ081S015 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 178 declarations of OpenAI's Lean: 135 definitions, 3 inductive types or structures and 40 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.addressRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.cacheInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.cacheOutputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.cacheRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.countInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.countOutputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.countRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.factorInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.factorOutputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.headInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.headOutputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.inputCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.outputCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.retainedCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.retainedPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.rowCountInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.rowCountOutputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.rowCountRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.scatterInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.scatterOutputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.scatterRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.workPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.workPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.zeros`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.flatOutRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.flatRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.flatStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.maskRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.maskStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.mergeStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.tapes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.cachePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.constantRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.constantStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.constantTapes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.copies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.directCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.pocket`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Store` and 98 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_SparseCodeProgram`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRetain`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSupport`, `SubexponentialSAT_SqrtLog_LeafHighContextProgramBase`, `SubexponentialSAT_SqrtLog_LeafHighContextProgramFlatProject`, `SubexponentialSAT_SqrtLog_LeafNodeCacheProgram`, `SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram`, `SubexponentialSAT_SqrtLog_LeafOuterNativeReferences`, `SubexponentialSAT_SqrtLog_LeafOuterProgramBase`, `SubexponentialSAT_SqrtLog_LeafOuterProgramParameters`, `SubexponentialSAT_SqrtLog_LeafOuterProgramPrepare`, `SubexponentialSAT_SqrtLog_LeafOuterProgramStorage`, `SubexponentialSAT_SqrtLog_LeafParameterArithmeticSearch`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnaryCopy`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramCache`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExports`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExportsOps`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExportsTable`, `SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendPoly`, `SubexponentialSAT_SqrtLog_LeafParametersProgramInterval`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafProgramClause`, `SubexponentialSAT_SqrtLog_LeafProgramClauseCount`, `SubexponentialSAT_SqrtLog_LeafProgramCount`, `SubexponentialSAT_SqrtLog_LeafProgramCountPrepare`, `SubexponentialSAT_SqrtLog_LeafProgramExpansion`, `SubexponentialSAT_SqrtLog_LeafProgramFactor`, `SubexponentialSAT_SqrtLog_LeafProgramFactorBase`, `SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch`, `SubexponentialSAT_SqrtLog_LeafProgramFactorJet`, `SubexponentialSAT_SqrtLog_LeafProgramFactorServicesBase`, `SubexponentialSAT_SqrtLog_LeafProgramHashParameters`, `SubexponentialSAT_SqrtLog_LeafProgramIncidence`, `SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters`, `SubexponentialSAT_SqrtLog_MomentsOutput`, `SubexponentialSAT_SqrtLog_MomentsPerturbation`, `SubexponentialSAT_SqrtLog_MomentsSquarefree`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyOuter`, `SubexponentialSAT_SqrtLog_PerturbationEmitProgram`, `SubexponentialSAT_SqrtLog_PerturbationProgramKey`, `SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorOuter`, `SubexponentialSAT_SqrtLog_ReconstructionProgramHorner`, `SubexponentialSAT_SqrtLog_ReconstructionProgramMiddle`, `SubexponentialSAT_SqrtLog_ReconstructionProgramScalar`, `SubexponentialSAT_SqrtLog_RingProgramTableBasic`, `SubexponentialSAT_SubexpCRTOuterControl`, `SubexponentialSAT_SubexpCRTOuterFinish`, `SubexponentialSAT_SubexpClauseMastersProgram`, `SubexponentialSAT_SubexpGuardProgram`, `SubexponentialSAT_SubexpIntervalCoreProgram`, `SubexponentialSAT_SubexpIntervalFinishProgram`, `SubexponentialSAT_SubexpIntervalStartProgram`, `SubexponentialSAT_SubexpTaylorFrames`, `SubexponentialSAT_Subexp_AssignmentRecordViews`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S037`, `OAIQ081S038`, `OAIQ081S040`, `OAIQ081S041`, `OAIQ081S042` and `OAIQ081S043`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_sparse_parameter_bounds`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpGuardProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete binary guard control for the subexponential schedule

The comparator below has a fixed instruction table, reads arbitrary-width
little-endian binary words, and uses only Boolean operations and stack pops.
Schedule arithmetic is not an instruction of this program.
-/

namespace SubexponentialSAT.SubexpGuardProgram

namespace Compare

def operandStacks (xs ys : List Bool) (i : Fin 2) : List Bool :=
  if i = 0 then xs else ys

@[simp] theorem operandStacks_left (xs ys : List Bool) : operandStacks xs ys 0 = xs := rfl
@[simp] theorem operandStacks_right (xs ys : List Bool) : operandStacks xs ys 1 = ys := rfl

theorem update_left (xs ys zs : List Bool) :
    Function.update (operandStacks xs ys) 0 zs = operandStacks zs ys := by
  funext i
  fin_cases i <;> simp [operandStacks]

theorem update_right (xs ys zs : List Bool) :
    Function.update (operandStacks xs ys) 1 zs = operandStacks xs zs := by
  funext i
  fin_cases i <;> simp [operandStacks]

end Compare

theorem extend_restrict {α β γ : Type} (f : α → β) (hf : Function.Injective f)
    (g : β → γ) : Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    exact hf.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hb

theorem pair_eta (f : Fin 2 → List Bool) : Compare.operandStacks (f 0) (f 1) = f := by
  first | done | (funext i; fin_cases i <;> rfl)


end SubexponentialSAT.SubexpGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

def checkerPorts : Fin 40 → Fin 48 := Fin.castAdd 8

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

def workPort {s : ℕ} (hs : s ≤ 288) (i : Fin s) : Fin 768 :=
  ⟨340+i.val,by omega⟩
def workPorts {s : ℕ} (hs : s ≤ 288) : List (Fin 768) := List.ofFn (workPort hs)

def inputCopies {s : ℕ} (hs : s ≤ 288) (xs : List (Fin 768 × Fin s)) :=
  xs.map (fun p => (p.1,workPort hs p.2))
def outputCopies {s : ℕ} (hs : s ≤ 288) (xs : List (Fin s × Fin 768)) :=
  xs.map (fun p => (workPort hs p.1,p.2))

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

def addressRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def rowCountRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def rowCountInputs : List (Fin 768 × Fin 15) := [(136,1)]
def rowCountOutputs : List (Fin 15 × Fin 768) := [(2,647)]

def cacheRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def cacheInputs : List (Fin 768 × Fin 24) := [(139,20),(138,21),(140,22)]
def cacheOutputs : List (Fin 24 × Fin 768) := [(0,640),(1,641),(2,642),(19,643)]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRetain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the paid interpolation cache for the later source-polynomial
worker. These three copies are charged before the private head bank is cleared. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

def retainedPorts : List (Fin 768) := [659]
def retainedCopies : List (Fin 768 × Fin 768) := [(640,710),(641,711),(642,712)]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
abbrev zeros (n : ℕ) := List.replicate n false

def headInputs : List (Fin 768 × Fin 64) :=
  [(128,30),(134,31),(649,32),(133,33),(132,38)]
def headOutputs : List (Fin 64 × Fin 768) := [(0,650),(1,651)]

def factorInputs : List (Fin 768 × Fin 64) :=
  [(129,30),(128,31),(649,32),(133,33),(132,38)]
def factorOutputs : List (Fin 64 × Fin 768) := [(0,671)]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct the full ambient head-support mask from the IDs actually
selected. A low-variable mask alone is not a head-support mask. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

def countRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def countInputs : List (Fin 768 × Fin 2) := [(651,0)]
def countOutputs : List (Fin 2 × Fin 768) := [(1,652)]

def scatterRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def scatterInputs : List (Fin 768 × Fin 13) := [(650,10),(652,11),(128,12)]
def scatterOutputs : List (Fin 13 × Fin 768) := [(0,670)]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentRecordViews
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed parser-based views of an actual framed word alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentRecordViews

def firstTwo : Fin 2 → Fin 3 := Fin.castAdd 1

end SubexponentialSAT.Subexp.AssignmentRecordViews

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid parser pipeline stages the current physical high assignment. -/
namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

def tapes (counter mask forward output copy acc high work tmp low : List Bool) : Fin 10 → List Bool :=
  fun i => match i.val with
  | 0 => counter
  | 1 => mask
  | 2 => forward
  | 3 => output
  | 4 => copy
  | 5 => acc
  | 6 => high
  | 7 => work
  | 8 => tmp
  | _ => low

def maskRegs : Fin 2 → Fin 4 := Fin.castAdd 2
def maskStacks : Fin 4 → Fin 10 := ![1,7,2,8]
def flatRegs : Fin 3 → Fin 4 := Fin.castAdd 1
def flatStacks : Fin 3 → Fin 10 := ![4,5,6]
def mergeStacks : Fin 4 → Fin 10 := ![7,6,9,3]


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramFlatProject
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
def flatOutRegs (regs : Fin 4 → Bool) : Fin 4 → Bool := ![false,false,false,regs 3]


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeCacheProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical staging of node-local cached ring words. The ambient source tapes
and ring masters are copied, never consumed. The two raw-one caches are built
by the checked sparse-constant program, rather than supplied semantically. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

def directCopies : List (Fin 768 × Fin 768) :=
  [(194,5),(202,12),(203,17),(201,22),(204,39),(212,45),(243,46),
   (211,76),(281,143),(128,88),(280,190),(128,191)]
def copies : List (Fin 768 × Fin 768) := directCopies ++ [(128,340),(207,343)]
def cachePorts : List (Fin 768) := [5,12,17,22,39,45,46,76,143,88,190,191,69,167]
def pocket : List (Fin 768) := [340,341,342,343,344,345,346]
def Ready (f : Fin 768 → List Bool) : Prop := ∀ i ∈ cachePorts ++ pocket, f i = []

def constantRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def constantStacks (i : Fin 6) : Fin 768 := ⟨340+i.val,by omega⟩

def constantTapes (f : Fin 768 → List Bool) (word : List Bool) : Fin 768 → List Bool :=
  fun i => if i=345 then word else if 340 ≤ i.val ∧ i.val < 345 then [] else f i


end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed indexed traversal of the actual framed node table. The installed
worker is a real command; its measured, frame-preserving execution remains an
explicit producer obligation. Neither the index nor a jet is semantic advice. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

structure Store where
  frame : Fin 768 → List Bool
  source : List Bool := []
  payload : List Bool := []
  nodesRev : List Bool := []
  jetsRev : List Bool := []
  temporary : List Bool := []
  index : List Bool := []
  node : List Bool := []
  jet : List Bool := []
  shape : List Bool := []
  nodesOut : List Bool := []
  jetsOut : List Bool := []

def tapes (s : Store) (i : Fin 768) : List Bool :=
  if i = 301 then s.source else
  if i = 302 then s.payload else
  if i = 303 then s.nodesRev else
  if i = 304 then s.jetsRev else
  if i = 305 then s.temporary else
  if i = 307 then s.index else
  if i = 78 then s.node else
  if i = 102 then s.jet else
  if i = 104 then s.shape else
  if i = 256 then s.nodesOut else
  if i = 265 then s.jetsOut else
  s.frame i

@[simp] theorem tapes_source (s : Store) : tapes s 301 = s.source := by simp [tapes]
@[simp] theorem update_source (s : Store) (bits : List Bool) :
    Function.update (tapes s) 301 bits = tapes {s with source := bits} := by
  funext i
  by_cases hi : i = 301
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_payload (s : Store) : tapes s 302 = s.payload := by simp [tapes]
@[simp] theorem update_payload (s : Store) (bits : List Bool) :
    Function.update (tapes s) 302 bits = tapes {s with payload := bits} := by
  funext i
  by_cases hi : i = 302
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_nodesRev (s : Store) : tapes s 303 = s.nodesRev := by simp [tapes]
@[simp] theorem update_nodesRev (s : Store) (bits : List Bool) :
    Function.update (tapes s) 303 bits = tapes {s with nodesRev := bits} := by
  funext i
  by_cases hi : i = 303
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_jetsRev (s : Store) : tapes s 304 = s.jetsRev := by simp [tapes]
@[simp] theorem update_jetsRev (s : Store) (bits : List Bool) :
    Function.update (tapes s) 304 bits = tapes {s with jetsRev := bits} := by
  funext i
  by_cases hi : i = 304
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_temporary (s : Store) : tapes s 305 = s.temporary := by simp [tapes]
@[simp] theorem update_temporary (s : Store) (bits : List Bool) :
    Function.update (tapes s) 305 bits = tapes {s with temporary := bits} := by
  funext i
  by_cases hi : i = 305
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_index (s : Store) : tapes s 307 = s.index := by simp [tapes]
@[simp] theorem update_index (s : Store) (bits : List Bool) :
    Function.update (tapes s) 307 bits = tapes {s with index := bits} := by
  funext i
  by_cases hi : i = 307
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_node (s : Store) : tapes s 78 = s.node := by simp [tapes]
@[simp] theorem update_node (s : Store) (bits : List Bool) :
    Function.update (tapes s) 78 bits = tapes {s with node := bits} := by
  funext i
  by_cases hi : i = 78
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_jet (s : Store) : tapes s 102 = s.jet := by simp [tapes]
@[simp] theorem update_jet (s : Store) (bits : List Bool) :
    Function.update (tapes s) 102 bits = tapes {s with jet := bits} := by
  funext i
  by_cases hi : i = 102
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_shape (s : Store) : tapes s 104 = s.shape := by simp [tapes]
@[simp] theorem update_shape (s : Store) (bits : List Bool) :
    Function.update (tapes s) 104 bits = tapes {s with shape := bits} := by
  funext i
  by_cases hi : i = 104
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_nodesOut (s : Store) : tapes s 256 = s.nodesOut := by simp [tapes]
@[simp] theorem update_nodesOut (s : Store) (bits : List Bool) :
    Function.update (tapes s) 256 bits = tapes {s with nodesOut := bits} := by
  funext i
  by_cases hi : i = 256
  · subst i; simp [tapes]
  · simp [tapes,hi]

@[simp] theorem tapes_jetsOut (s : Store) : tapes s 265 = s.jetsOut := by simp [tapes]
@[simp] theorem update_jetsOut (s : Store) (bits : List Bool) :
    Function.update (tapes s) 265 bits = tapes {s with jetsOut := bits} := by
  funext i
  by_cases hi : i = 265
  · subst i; simp [tapes]
  · simp [tapes,hi]

def parserRegs (regs : Fin 40 → Bool) (v pr f : Bool) : Fin 40 → Bool :=
  Function.update (Function.update (Function.update regs 37 v) 38 pr) 39 f

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterNativeReferences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked-reference stream is generated by a fixed program from the binary
clause count. Both binary-to-unary expansion and the quadratic framed stream
emission are part of the measured run. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative.References
open SubexponentialSAT

def registers : Fin 3 → Fin 10 := Fin.castAdd 7
def stackMap : Fin 3 → Fin 10 := ![0,6,1]

end SubexponentialSAT.SqrtLog.LeafOuterNative.References

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

theorem size_eq_log2_add_one {n : ℕ} (hn : n ≠ 0) : Nat.size n = Nat.log2 n + 1 := by
  have hu : Nat.size n ≤ Nat.log2 n + 1 :=
    Nat.size_le.mpr ((Nat.log2_lt hn).mp (by omega))
  have hl : Nat.log2 n < Nat.size n :=
    Nat.lt_size.mpr ((Nat.le_log2 hn).mp le_rfl)
  omega

theorem two_pow_size_le (n : ℕ) : 2 ^ Nat.size n ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n; norm_num
  · rw [size_eq_log2_add_one hn, pow_succ]
    have h : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn).mp le_rfl
    omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generic correctness for the actual tested square-times-coefficient search.
The command is exactly `Setup.Search.command`; there is no arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic.Search

def root (coefficient bound : ℕ) : ℕ := Nat.sqrt (bound / coefficient)

theorem le_root_iff (coefficient bound a : ℕ) (hc : 0 < coefficient) :
    a ≤ root coefficient bound ↔ a^2 * coefficient ≤ bound := by
  rw [root, Nat.le_sqrt', Nat.le_div_iff_mul_le hc]

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic.Search

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpClauseMastersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical preparation of the shared clause-factor masters

Four preserved binary input words supply the declared variable count, chunk
width, field modulus, and chunk count. Copies of the three counts are converted
by the checked binary-to-unary program. The checked full-shape capture then
builds the padded-array shape. No desired shape is an input assumption.

The modulus-width shape is a physical copy of the modulus word: its consumers
use its length, not its bits. The other two copies supply the binary chunk
width and field modulus at the clause-family's own persistent ports.
-/

namespace SubexponentialSAT.SubexpClauseMastersProgram

def zeroRegs : Fin 3 → Bool := fun _ => false

end SubexponentialSAT.SubexpClauseMastersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

def pair (j : Fin 10) (h : Fin 2) : Fin 20 := ⟨2*j.val+h.val,by omega⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuit -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.GuardSetup

def pair (j : Fin 10) (h : Fin 2) : Fin 64 := ⟨44+2*j.val+h.val,by omega⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.GuardSetup


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPrepared -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

def coefficient : ℕ → ℕ
  | 0 => 1
  | n+1 => coefficient n * 10000000^(6^n)

def polynomialCoefficient : ℕ → ℕ
  | 0 => 1
  | n+1 => polynomialCoefficient n * (10000000*3^6)^(6^n)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutCost -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open Circuit

def publicSlot : Fin 12 → Fin 64 := ![13,14,17,18,21,25,29,31,33,34,35,42]

theorem publicSlot_lt (i : Fin 12) : (publicSlot i).val < 44 := by
  fin_cases i <;> decide

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramSerialization -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT

abbrev Route := Fin 896 × Fin 896

def routeValid (p : Route) : Prop :=
  p.1 ≠ p.2 ∧ p.1 ≠ 767 ∧ p.2 ≠ 767

def workerStack (i : Fin 768) : Fin 896 := i.castAdd 128

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared fixed port maps and the paid native code-parameter stage. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT

def regs8 : Fin 8 → Fin 40 := Fin.castAdd 32
def regs16 : Fin 16 → Fin 40 := Fin.castAdd 24
def stacks77 : Fin 77 → Fin 896 := Fin.castAdd 819
def stacks64 : Fin 64 → Fin 896 := Fin.castAdd 832

def parameterInputs : List Route := [(782,0),(786,1)]
def parameterOutputs : List Route :=
  [(5,800),(9,801),(11,802),(12,803),(15,804),(18,805),(19,806),(21,807),
   (24,808),(25,809),(26,810),(27,811),(28,812),(29,813),(30,814)]

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer-leaf parameter stage: input copies, native arithmetic,
output copies, and complete worker cleanup, with every command charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT

def binaryMetadataPort (j : Fin 7) : Fin 896 := ⟨801+j.val, by omega⟩
def unaryMetadataPort (j : Fin 7) : Fin 896 := ⟨808+j.val, by omega⟩

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHashParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete placement of the selector's numerical preparation in the full
leaf bank. Formula784 and answer787 are outside this routine;782 contains the
actual binary clause count produced by ClauseCount.caller. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.HashParameters

open SubexponentialSAT

def registers (i : Fin 16) : Fin 40 := i.castAdd 24

def stackMap : Fin 44 → Fin 896 :=
  ![768,769,770,771,772,773,774,775,776,777,778,779,780,781,
    785,782,786,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]

end SubexponentialSAT.SqrtLog.LeafProgram.HashParameters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact arithmetic preparation, cleanup, and preservation of the decoder's
physical width. The only incoming numerical data are n, m and B. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT

def prepareHashBudget (L : ℕ) : ℕ :=
  let c := 10000000000*(L+1)^2+1
  c+1536*(L+c)+2348

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnaryCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

attribute [local simp] Fin.coe_ofNat_eq_mod

def unaryRegs : Fin 3 → Fin 8 := Fin.castAdd 5

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalCoreProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The multiplication and predecessor prefix of the actual interval-start
initializer. All widths refer to physical input words, including padding. -/

namespace SubexponentialSAT.SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Regs := Fin 8 → Bool
abbrev Words := Fin 10 → List Bool

abbrev port (i : Fin 10) : Fin 32 := ⟨i.val, by omega⟩

end SubexponentialSAT.SubexpIntervalCoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalFinishProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual long division and scratch cleanup for the interval initializer. -/

namespace SubexponentialSAT.SubexpIntervalFinishProgram

open SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def quotientPorts : Fin 8 → Fin 32 := ![10, 11, 12, 13, 14, 8, 15, 3]

end SubexponentialSAT.SubexpIntervalFinishProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalStartProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical binary initialization of the centered interval start

Three preserved input words encode r, Q, and R on ports 0, 1, and 2.
The fixed program computes ((Q-1)*(r-1)-R*r)/(2*r) using saturated
predecessors, products, saturated subtraction, and binary long division.
Only output port 3 differs on return; ports 4 through 31 are empty again.
-/

namespace SubexponentialSAT.SubexpIntervalStartProgram

open SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def subtractionPorts : Fin 8 → Fin 32 := ![6, 7, 9, 10, 11, 12, 13, 14]

end SubexponentialSAT.SubexpIntervalStartProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval


open Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The preserving interval routine can read the parameter words directly.
Its private work bank is cleared by the preceding finite instruction table. -/
def ports : Fin 32 → Fin 77 :=
  ![18,21,29,46,47,48,49,50,51,52,53,54,55,56,57,58,
    59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCache
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache


open Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

def unaryBound (v l : ℕ) : ℕ := 7*l+6+32*(v+1)*(l+1)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExportsOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid metadata exports. These commands touch only their destination and
three working registers; binary sources and all scratch words are restored. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

structure Field where
  src : Fin 768
  dst : Fin 768
  unary : Bool
  deriving DecidableEq

def Field.Good (f : Field) : Prop :=
  340  ≤  f.src.val ∧ f.src.val < 417 ∧
    ((128  ≤  f.dst.val ∧ f.dst.val  ≤  140) ∨ (720  ≤  f.dst.val ∧ f.dst.val  ≤  727))

def regs : Fin 3 → Fin 40 := Fin.castAdd 37

def ports (f : Field) (i : Fin 14) : Fin 768 :=
  if i.val=0 then f.src else if i.val=1 then f.dst else ⟨648+i.val,by omega⟩

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExportsTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The first five fields require numeric binary-to-unary conversion. Fields
5--7 are already true-unary results of the paid cache preparation. -/
def localSource : Fin 16 → Fin 64 := ![0,5,18,21,47,51,52,53,21,18,25,7,1,3,5,29]
def destination : Fin 16 → Fin 768 :=
  ![128,129,130,131,132,138,139,140,720,721,722,723,724,725,726,727]
def field (i : Fin 16) : Field :=
  ⟨⟨340+(localSource i).val,by have := (localSource i).isLt; omega⟩,
    destination i,decide (i.val < 5)⟩
def fields : List Field := (List.finRange 16).map field

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def bankRegs : Fin 8 → Fin 40 := Fin.castAdd 32
def bank (i : Fin 77) : Fin 768 := ⟨340+i.val,by omega⟩

def clearPorts : List (Fin 768) := (List.finRange 18).map (fun i => bank ⟨46+i.val,by omega⟩)

def binarySources : Fin 8 → Fin 64 := ![21,18,25,7,1,3,5,29]

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open Circuit
noncomputable section

/-- A fixed ordinary polynomial in a declared input measure. -/
def Poly {α : Type*} (measure f : α → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ a, f a ≤ C*(measure a)^d

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial bounds for the actual parameter/export prefix. Only
input counts and input word lengths enter the final bound. In particular the
large grid value never becomes a unary counter in this prefix. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod



def smallPorts : List (Fin 64) := [0,5,18,21,29]
def resultPorts : List (Fin 64) := [0,5,18,21,29,46,47,50]

def valueHeight (B : ℕ) := 4*(B+1)^2

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramClause
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Evaluate the optional marked clause without applying a hash idempotent.
The constant seed is copied by the machine, and every original literal is
processed by the same concrete decoder and sparse arithmetic as hash rows. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Clause

open SubexponentialSAT

def callerRegisters (i : Fin 8) : Fin 40 := i.castAdd 32
def callerStacks (i : Fin 96) : Fin 768 := i.castAdd 672

end SubexponentialSAT.SqrtLog.LeafProgram.Clause

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramClauseCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the clauses in the actual emitted leaf. Both the preserving record
scan and unary-to-binary conversion are fixed native programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

open SubexponentialSAT

def binaryRegisters (i : Fin 3) : Fin 8 := i.castAdd 5
def binaryStacks : Fin 3 → Fin 16 := ![2,15,14]

def callerRegisters (i : Fin 8) : Fin 40 := i.castAdd 32
def callerStacks : Fin 16 → Fin 896 := ![0,784,1,2,3,4,5,6,7,8,9,10,11,12,13,782]

end SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

def registers : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective 8 8⟩
def threeRegisters : Fin 3 ↪ Fin 16 := ⟨Fin.castAdd 13, Fin.castAdd_injective 3 13⟩
def localPorts : Fin 256 ↪ Fin 320 := ⟨Fin.castAdd 64, Fin.castAdd_injective 256 64⟩

def countPorts : Fin 13 ↪ Fin 320 :=
  ⟨![267,243,268,269,316,317,270,271,272,273,274,275,276], by decide⟩

def blockCopyPorts : Fin 4 ↪ Fin 320 := ⟨![104,277,278,279], by decide⟩

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Final cleanup and complete tape-loop costs for scalar reconstruction.
The arithmetic-middle premise below is an actual execution of a fixed command;
its concrete implementation is assembled separately from the CRT services. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open scoped BigOperators

def initialCleanPorts : List (Fin 320) :=
  [104,261,268,277,278,279,316,317,318,214,257,266] ++ [213,216,225,258,259,260]

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

open SubexponentialSAT SubexpCRTOuterProgram

def cleanPorts : List (Fin 320) :=
  [120,121,122,215,217,218,219,223,229,240,241,244,245,246,262,318,319]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramHorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical staging of local CRT correction evaluation. The dense correction
is consumed from 244; its value at the retained point 263 is returned on 264. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

open SubexponentialSAT SubexpCRTOuterProgram

def cleanPorts : List (Fin 320) := [120,240,241,245,246,247,248,250,251,252,264,318,319]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed outer calls to the native scalar ring arithmetic. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

open SubexponentialSAT SubexpCRTOuterProgram

def cleanPorts : List (Fin 320) := [120,240,241,244,245,318,319]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramMiddle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition of the physical arithmetic stages for one Hermite node. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT SubexpCRTOuterProgram

def cleanPorts : List (Fin 320) :=
  CofactorOuter.cleanPorts ++ Scalar.cleanPorts ++ Horner.cleanPorts ++ [192,193,262,263,264]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One closed native count-recovery table: Hermite reconstruction over the
computed ring, integer readback, and reclamation of the two CRT entry caches.
Node-jet production and its semantic theorem are composed at the caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count

def crtRegisters (i : Fin 16) : Fin 40 := i.castAdd 24
def crtStacks (i : Fin 320) : Fin 768 := i.castAdd 448

end SubexponentialSAT.SqrtLog.LeafProgram.Count

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCountPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual reclamation of node-work scratch before Hermite reconstruction.
The static port set includes both the native CRT work ports and the scalar/
polynomial arithmetic readiness ports, together with the reader temporaries. Runtime data are cleared by real
stack loops; persistent node and jet inputs remain outside this set. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

open SubexponentialSAT

/-- In particular the actual ring metadata and the newly produced node/jet
streams survive the cleanup that establishes the CRT scratch condition. -/
def protectedInputs : List (Fin 768) :=
  [194,201,202,203,204,207,209,211,212,243,256,265,280,281,300]

end SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native expansion of one selected raw hash row.  The row is read from the
dispatcher result; every original clause lookup and coefficient lift is paid
by the fixed assembler.  The original formula and dynamic width words are
read in place, so they remain available for the next factor. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion

open SubexponentialSAT

def register (i : Fin 8) : Fin 40 := i.castAdd 32

def stackMap : Fin 24 → Fin 768 :=
  ![154,708,340,341,342,343,344,707,345,346,347,348,
    349,350,700,280,64,351,352,353,354,355,356,357]

def scratch : List (Fin 768) :=
  [340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357]

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Wide native factor arithmetic and paid tape movement. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT

def nativeRegisters (i : Fin 8) : Fin 40 := i.castAdd 32
def nativeStacks (i : Fin 96) : Fin 768 := i.castAdd 672


end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor dispatcher in the native leaf's actual bank.  The parsed ID
is retained for incidence preparation.  The mark flag is read from a tape,
not inserted as a program parameter. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

open SubexponentialSAT

def register (i : Fin 8) : Fin 40 := i.castAdd 32
def stackMap : Fin 16 → Fin 768 :=
  ![701,700,152,704,705,340,341,342,343,344,345,346,347,348,349,154]

def scratch : List (Fin 768) := [152,154,340,341,342,343,344,345,346,347,348,349,359]

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsSquarefree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact coefficient extraction in the Boolean squarefree algebra, including
both formal scalar variables. No total-degree truncation is substituted for
support union. The final U coefficient sum is only an additive operation. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators

noncomputable section

section SquarefreeEvaluation

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

abbrev ScalarJet (R : Type*) [Semiring R] := Polynomial (Polynomial R)

end SquarefreeEvaluation

end
end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual row perturbations, rather than an assumed support invariant.
Every formal Boolean coordinate is multiplied by a polynomial with zero
constant term in Z. The construction is valid over any commutative ring. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommRing R]

noncomputable def rowDelta (p : Polynomial R) (theta : R) : Polynomial R :=
  p.comp (Polynomial.X + Polynomial.C theta) - Polynomial.C (p.eval theta)

@[simp] theorem rowDelta_coeff_zero (p : Polynomial R) (theta : R) :
    (rowDelta p theta).coeff 0 = 0 := by
  simp [rowDelta, Polynomial.coeff_zero_eq_eval_zero]

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramKey
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native construction of a positive-Z singleton key from its runtime unary
exponent and support mask. The reversed result feeds the sparse record emitter. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Key
open SubexponentialSAT

def bits (unary mask : List Bool) : List Bool := false::(unary++(false::mask))

end SubexponentialSAT.SqrtLog.PerturbationProgram.Key

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationEmitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native emission of the positive part of a shifted coefficient array.
The dimensions and the singleton support mask are runtime data. The constant
cell is consumed without emission; all later cells are framed, including zero
coefficients. No normalization or arithmetic oracle is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT

def keyBits (mask : List Bool) (j : ℕ) : List Bool :=
  PerturbationProgram.Key.bits (List.replicate j true) mask

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation and the finite total-variable table traversal. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev OuterStore := Fin 768 → List Bool

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT

def pairs : List (Fin 768 × Fin 768) :=
  [(194,345),(202,350),(280,444),
   (194,534),(201,541),(202,542),(203,543),(204,544),
   (145,546),(280,547),(207,548),(78,549),(280,551),(128,552),
   (243,553),(702,574),(703,575),(243,583)]

def workerPorts : List (Fin 768) :=
  (List.finRange 340).map (fun i => (⟨340+i.val,by omega⟩ : Fin 768))

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed per-assignment factor evaluation. Factors are dispatched by runtime
ID; hash rows are expanded and tested by the computed idempotent, the marked
clause is multiplied directly, and added neutral factors contribute one.
Every operation below is an actual finite instruction table or native loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT

/-- The indicator's coefficient port78 is relocated; runtime theta78 stays
available to every subsequent source-row computation. -/
def indicatorStacks (i : Fin 96) : Fin 768 :=
  Equiv.swap 78 143 (nativeStacks i)

@[simp] theorem coefficient_port : indicatorStacks 78 = 143 := by decide
@[simp] theorem factor_result_port : indicatorStacks 67 = 67 := by decide

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The incidence meaning depends only on the merged assignment and the
fixed-high context. Parser and accumulator contents do not enter it. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT
open PerturbationAssembly

/-- Project the three physical assignment masters into the incidence ABI. -/
def choiceStore (s : Fin 768 → List Bool) : OuterStore :=
  fun i => if i=546 then s 145 else if i=574 then s 702 else if i=575 then s 703 else []

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorServicesBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact framing tools for the fixed wide indicator and marked-clause calls.
The functions below only describe states; executable code remains Factor's
already defined finite service tables. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorServices
open SubexponentialSAT

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

def indicatorScratch : List (Fin 96) :=
  [56,57,58,59,60,61,63,65,66,67,68,70,79,80,81,82,83,84,85,86,87,89,90,91,92,93,94,95]
def clauseScratch : List (Fin 96) := [56,57,58,59,60,61,67,70]

end SubexponentialSAT.SqrtLog.LeafProgram.FactorServices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Layout/source metadata are parked outside the native arithmetic bank.
CRT and scalar arithmetic use several ports128..141 as scratch; these values
are therefore physically reloaded for each node and cleared before CRT. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters
open SubexponentialSAT

def low (i : Fin 14) : Fin 768 := ⟨128+i.val,by omega⟩
def high (i : Fin 14) : Fin 768 := ⟨730+i.val,by omega⟩
def loadPairs : List (Fin 768 × Fin 768) := (List.finRange 14).map fun i => (high i,low i)

theorem low_injective : Function.Injective low := by
  intro i j h; apply Fin.ext
  have hv := congrArg Fin.val h
  change 128+i.val=128+j.val at hv
  omega
theorem high_injective : Function.Injective high := by
  intro i j h; apply Fin.ext
  have hv := congrArg Fin.val h
  change 730+i.val=730+j.val at hv
  omega

theorem load_nodup : (loadPairs.map Prod.snd).Nodup := by
  simpa only [loadPairs,List.map_map,Function.comp_def] using
    (List.nodup_finRange 14).map low_injective
theorem load_sep : ∀ p ∈ loadPairs, ∀ q ∈ loadPairs, p.1 ≠ q.2 := by
  intro p hp q hq
  simp only [loadPairs,List.mem_map,List.mem_finRange,true_and] at hp hq
  obtain ⟨i,rfl⟩ := hp
  obtain ⟨j,rfl⟩ := hq
  intro h
  have hv := congrArg Fin.val h
  change 730+i.val=128+j.val at hv
  omega

def registers : Fin 16 → Fin 40 := Fin.castAdd 24

end SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete dense Z-output list for CRT reconstruction. Its entries are
obtained only by sparse coefficient scans and a finite sum over retained U. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators

variable {R V : Type*} [CommSemiring R] [DecidableEq V]

def tabulate : ℕ → (ℕ → R) → List R
  | 0, _ => []
  | n+1, f => f 0 :: tabulate n (fun j => f (j+1))

omit [CommSemiring R] in
@[simp] theorem tabulate_length (n : ℕ) (f : ℕ → R) : (tabulate n f).length = n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp [tabulate, ih]

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native primitives used by the companion-table preparation machine. -/
namespace SubexponentialSAT.SqrtLog.RingProgramTable

/-- The first fifteen ports are the audited scalar/triple scanner ABI. -/
structure Store where
  modulus : List Bool
  left : List Bool := []
  source : List Bool := []
  saved : List Bool := []
  count : List Bool := []
  width : List Bool
  vector : List Bool := []
  coefficients : List Bool := []
  minusOne : List Bool
  tail : List Bool
  newTail : List Bool := []
  output : List Bool := []
  polynomial : List Bool
  degree : List Bool
  zero : List Bool
  powers : List Bool := []
  rounds : List Bool := []

abbrev tapes (s : Store) : Fin 27 → List Bool :=
  ![s.left, [], [], [], [], s.modulus, [], [], [], s.source, s.saved,
    s.count, s.width, [], [], s.vector, s.coefficients, s.minusOne, s.tail,
    s.newTail, s.output, s.polynomial, s.degree, [], s.zero, s.powers, s.rounds]

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTaylorFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control conversion of a flat coefficient stream into an ordered
list of framed coefficients. Runtime counters determine the coefficient
width and requested count. Missing high coefficients are actually read as
zero by the existing padded-reader program. -/

namespace SubexponentialSAT.SubexpTaylorFrames

def padRegs : Fin 2 → Fin 5 := ![0, 1]

end SubexponentialSAT.SubexpTaylorFrames

end OAI.Algorithms
end


