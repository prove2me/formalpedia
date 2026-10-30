-- Prove2me | Definitions.Def_OAIQ081S077
-- name    : OAIQ081S077
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:59:17.862155+00:00
-- url     : https://prove2.me/theorems/7961a68a-79ca-4309-bce9-a63e960d2abe
-- title:
--   Definitions bundle OAIQ081S077 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 34 definitions and 22 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.flagged`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.markedInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.unmarkedInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide.completed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide.install`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide.project`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.cleaned`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.deltaState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.prepareCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.restored`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.saved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.clauseFoldValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.rowFoldValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.loadBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.listCandidate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds.rawDecode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.bootBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.uniformStepBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.supportBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.jetConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.jetScalar`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.sumUCoeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.hitBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.header`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.miss`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.rewriteKey`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.commit`, `OAI.Algorithms.SubexponentialSAT.SubexpBasePUnranking.remainingRank`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafProgramFolded`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackFrames`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackStore`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackWide`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReference`, `SubexponentialSAT_SqrtLog_LeafProgramSourceControls`, `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyCore`, `SubexponentialSAT_SqrtLog_LeafProgramSourceStaging`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand`, `SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsDecode`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramBoot`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramBounds`, `SubexponentialSAT_SqrtLog_LeafWeightProgramModel`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryFinish`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryHit`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramAccumulate`, `SubexponentialSAT_SqrtLog_MomentsSquarefree`, `SubexponentialSAT_SqrtLog_RingProgramTableRound`, `SubexponentialSAT_SqrtLog_RingProgramTableSetup`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBasic`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramStep`, `SubexponentialSAT_SubexpBasePUnranking`, `SubexponentialSAT_SubexpFieldRowPreparation`, `SubexponentialSAT_SubexpPrimeProgram`, `SubexponentialSAT_Subexp_PackingBucketBounds`, `SubexponentialSAT_Subexp_PackingTupleBounds`, `SubexponentialSAT_Subexp_SelectorMapProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S049`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S054`, `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S059` and `OAIQ081S060` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S094`, `OAIQ081S095` and `OAIQ081S099`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S049
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S052
import Definitions.Def_OAIQ081S054
import Definitions.Def_OAIQ081S056
import Definitions.Def_OAIQ081S057
import Definitions.Def_OAIQ081S058
import Definitions.Def_OAIQ081S059
import Definitions.Def_OAIQ081S060

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsSquarefree
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

noncomputable section

section SquarefreeEvaluation

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

def jetScalar : ScalarJet R →+* SquarefreeJet V R :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (scalar (V := V) (R := R)))

def jetConstant (r : R) : ScalarJet R := Polynomial.C (Polynomial.C r)

/-- Sum the retained U coefficients, after the complete head moment product. -/
def sumUCoeff (t : ℕ) : ScalarJet R →+ Polynomial R where
  toFun f := ∑ u ∈ Finset.range t, f.coeff u
  map_zero' := by simp
  map_add' f g := by simp [Finset.sum_add_distrib]

@[simp] theorem sumUCoeff_coeff (t : ℕ) (f : ScalarJet R) (z : ℕ) :
    (sumUCoeff t f).coeff z = ∑ u ∈ Finset.range t, (f.coeff u).coeff z := by
  simp [sumUCoeff, Polynomial.finsetSum_coeff]

end SquarefreeEvaluation

end
end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFolded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Left-fold semantics for the physical record interpreter. Canonical sparse
lists need not be equal under reassociation; their denotations are the same
canonical projection of the common source polynomial. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

variable {V C R : Type*} [CommRing R]

def clauseFoldValue (alg : Algebra R) (value : V → R)
    (ls : List (SAT.Literal V)) (init : R) : R :=
  ls.foldl (fun acc l => alg.mul acc (literalValue alg value l)) init

def rowFoldValue (alg : Algebra R) (decode : C → R) (value : V → R)
    (terms : SparseRow V C) (init : R) : R :=
  terms.foldl (fun acc term =>
    alg.add acc (alg.mul (decode term.1) (clauseValue alg value term.2))) init

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and cleanup facts for the physical CRT count reader. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

noncomputable def finish (a : Data) (regs : Fin 8 → Bool)
    (word modulus width : List Bool) : Data :=
  afterMove (install a ⟨regs, store word modulus [] width⟩)

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the concrete reader into the shared marked/branch caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

noncomputable def install (frame : Data) (a : QueryReadback.Data) : Data :=
  embedState regMap stackMap frame a

def project (a : Data) : QueryReadback.Data :=
  ⟨a.regs ∘ regMap, a.stacks ∘ stackMap⟩

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackStore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact wide-store restoration for count readback.  Parser and odometer
registers are preserved even though the reusable narrow ABI includes them. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

open SubexponentialSAT BitProgram StructuredCalls

noncomputable def completed (a : Data) (regs : Fin 8 → Bool) (word : List Bool) : Data :=
  install a (QueryReadback.finish (project a) regs word (a.stacks 194) (a.stacks 202))

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked collector supplies a reversed reference payload on321. The
query itself pays to copy and reverse that reference into the frontend's
forward index slot705. The original payload survives until the branch exit. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def flagged (a : Data) : Data :=
  SubexpParameterProgram.runAtoms [.set 0 true,.push 706 0] a

def markedInput (a : Data) : Data :=
  flagged (afterTransfer (afterCopy a 321 699 0 1) 699 705 0 1)

def unmarkedInput (a : Data) : Data :=
  SubexpParameterProgram.runAtoms [.set 0 false,.push 705 0,.push 706 0] a

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPrimeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable pieces of prime trial division

The numeric trial-division functions in the first section are specifications.
They are never instructions of a program. The executable zero test and Boolean
accumulator below contain only existing finite Boolean-stack instructions.
Candidate numbers, divisors, and remainders are runtime data.
-/

namespace SubexponentialSAT.SubexpPrimeProgram

open BitProgram StructuredProgram StructuredCalls

/-- Actual structured executions have a unique final data state.  The proof
uses the verified compiler and deterministic terminal configurations. -/
theorem eval_result_unique {R S : ℕ} {cmd : StructuredCalls.Cmd R S}
    {n m : ℕ} {a b c : StructuredProgram.State R S}
    (h₁ : StructuredCalls.Eval cmd n a b)
    (h₂ : StructuredCalls.Eval cmd m a c) (input output : Fin S) : b = c := by
  have t₁ := StructuredCalls.compiled_halt_trace h₁ input output
  have t₂ := StructuredCalls.compiled_halt_trace h₂ input output
  have hb : BitProgram.step (StructuredCalls.compiled cmd input output)
      (b.withPC none) = none := rfl
  have hc : BitProgram.step (StructuredCalls.compiled cmd input output)
      (c.withPC none) = none := rfl
  have heq := Computation.RunsIn.terminal_unique
    (show Computation.RunsIn _ (n + 1) _ _ from ⟨n + 1, le_rfl, t₁⟩)
    (show Computation.RunsIn _ (m + 1) _ _ from ⟨m + 1, le_rfl, t₂⟩) hb hc
  exact congrArg StructuredProgram.State.ofCfg heq

end SubexponentialSAT.SubexpPrimeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Protect the target-jet caches while the source-polynomial initializer
uses the same private local ports. Source length and target jet order are
independent runtime values. These are actual copy and clear programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

def saved (a : Data) : Data := clearManyState cachePorts (copyManyState savePairs a)

def restored (a : Data) : Data :=
  clearManyState backupPorts (copyManyState restorePairs (clearManyState cachePorts a))
def finished (a : Data) : Data := clearManyState lowClearPorts (restored a)

end SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
def deltaState (a : Data) : Data :=
  (StructuredProgram.Atom.push (365 : Fin 768) (0 : Fin 16)).eval
    ((StructuredProgram.Atom.set (0 : Fin 16) true).eval a)

def prepared (a : Data) : Data := deltaState (copyManyState pairs a)
def prepareCost (a : Data) : ℕ := copyManyCost pairs a + 2

def cleaned (a : Data) : Data := clearManyState extraPorts a

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte-level value and frame rules for source preparation. These rules
concern the actual paid copy/clear state transformer, not assumed source
execution or a supplied readiness certificate. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

def prepared (a : Data) : Data := SourceControls.prepared (SourceStaging.saved a)

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The variable scan is started from actual serialized scopes and a mask.
The factor count is obtained by a physical record scan, never supplied as data. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def bootBudget (scopes : List (List ℕ)) (mask : List Bool) :=
  7*(scopeBits scopes).length+5+
    SubexpSunflowerProgram.CountRecords.loopSteps (scopes.map SubexpIncidenceSlotProgram.scopeBytes)+
    (7*mask.length+5)

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial physical cost and basic exact output identities. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def uniformStepBudget (scopes : List (List ℕ)) (n : ℕ) :=
  1000*((scopeBits scopes).length+scopes.length+n+1)^2+50*(scopes.length+1)+50

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native syntax from physical formula/row masters through the guarded
parameter bank. The only static input is the fixed formula-width bound k. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def loadBits (dst : Fin 768) (bits : List Bool) : Code :=
  liftCommand (ArithmeticExpressionSupport.pushWord dst bits) dst dst r8 id

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single raw-slot decoder for the actual logical records returned by the
selector's parser. It retains zero-coefficient and repeated entries. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashSelectProgram

def listCandidate {m : ℕ} (row : List (Fin m × ZMod 3)) : HashFamily.Candidate m row.length :=
  (fun j => (row.get j).1, fun j => (row.get j).2)

abbrev rawDecode (m width : ℕ) (hm : 0 < m) (payload : List Bool) :=
  HashInputProgram.candidateTerms (HashFamilyPayload.decode m (payload.length / width) width hm payload)

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafWeightProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native three-mask branch computes the exact squarefree head weight. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram

open SubexponentialSAT
open scoped BigOperators

def supportBits {n : ℕ} (s : Squarefree.Support (Fin n)) : List Bool :=
  List.ofFn fun i => decide (i ∈ s.vars)

end SubexponentialSAT.SqrtLog.LeafWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev finish : Cmd 8 27 := .seq (clear 18)
  (.seq (transfer 0 26) (.seq replace (.seq (copy 25 15 23) (clear 25))))

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryHit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def hitBudget (p t : ℕ) (pairs : List (Word (baseWidth p t) × Word (baseWidth p t))) : ℕ :=
  9 * (RingScan.rightBits pairs).length + 7 * (RingScan.leftBits pairs).length +
  7 * pairs.length + pairs.length * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 23

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingTupleBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Bounds for the actual tuple tables used by packing

These estimates use the concrete framed record encoding and the executable
Cartesian-power recurrence.  The cost bound includes an empty alphabet.
-/

namespace SubexponentialSAT.Subexp.PackingTupleBounds

theorem member_length_le (rows : List (List Bool)) (x : List Bool) (hx : x ∈ rows) :
    x.length ≤ (ProgramEncoding.encodeRecords rows).length := by
  induction rows generalizing x with
  | nil => simp at hx
  | cons y ys ih =>
      have hlen : (ProgramEncoding.encodeRecords (y :: ys)).length =
          2 * y.length + 2 + (ProgramEncoding.encodeRecords ys).length :=
        Encoding.length_encodeList_cons id y ys
      rcases List.mem_cons.mp hx with rfl | ht
      · omega
      · have h := ih x ht
        omega

end SubexponentialSAT.Subexp.PackingTupleBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev clear (src : Fin 10) : Cmd 5 10 := Squarefree.Program.clearAt src

abbrev header : Cmd 5 10 :=
  .seq (Squarefree.Program.readNat 4 5) (.base (.atom (.push 5 0)))
abbrev rewriteKey : Cmd 5 10 := .seq (transfer 2 4) (.seq header (.seq header scanMask))
abbrev miss : Cmd 5 10 := .seq (clear 3) (clear 5)

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramAccumulate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Commit the native sum as the next accumulator, reclaiming all temporary
strings. The dictionary and query are preserved for the runtime loop. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram.Dictionary

abbrev commit : Cmd 8 27 := .seq (clear 17) (.seq (transfer 0 26) (transfer 26 17))

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableRound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem prepareRound_eval (s : Store) (regs : Fin 8 → Bool)
    (hl : s.left = []) (hc : s.coefficients = []) (hn : s.count = []) :
    Eval prepareRound (7*s.polynomial.length+7*s.degree.length+7*s.zero.length+15)
      (state regs s)
      (state (readRegs regs 1 3 none) {s with left := s.zero, coefficients := s.polynomial, count := s.degree}) := by
  let s1 := {s with coefficients := s.polynomial}
  let s2 := {s1 with count := s.degree}
  let s3 := {s2 with left := s.zero}
  let rr := readRegs regs 1 3 none
  have h1 := copy_store_eval s s1 regs 21 16 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s1, hc])
  have h2 := copy_store_eval s1 s2 rr 22 11 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s2, s1, hn])
  have h3 := copy_store_eval s2 s3 rr 24 0 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s3, s2, s1, hl])
  simp only [rr, readRegs_reset] at h2 h3
  convert h1.seq (h2.seq h3) using 1
  all_goals try with_reducible_and_instances rfl
  simp [s1, s2, tapes]
  omega

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem prepareRounds_eval (s : Store) (regs : Fin 8 → Bool) (hempty : s.rounds = []) :
    Eval prepareRounds (14*s.degree.length+12) (state regs s)
      (state (readRegs (readRegs (readRegs regs 1 3 none) 1 3 (s.degree ++ s.degree).head?) 1 3 (s.degree ++ s.degree).tail.head?)
        {s with rounds := roundCounter s.degree}) := by
  let s1 := {s with rounds := s.degree}
  let s2 := {s with rounds := s.degree ++ s.degree}
  let rr := readRegs regs 1 3 none
  have h1 := copy_store_eval s s1 regs 22 26 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s1, hempty])
  have h2 := copy_store_eval s1 s2 rr 22 26 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s2, s1])
  have h3 := popRound_eval s2 rr
  have h4 := popRound_eval {s2 with rounds := s2.rounds.tail} (readRegs rr 1 3 s2.rounds.head?)
  simp only [rr, readRegs_reset] at h2
  convert h1.seq (h2.seq (h3.seq h4)) using 1 <;>
    simp [s1, s2, tapes, roundCounter] <;>
    first | ring

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control primitives for laying out a stored power table.  All indices,
dimensions, and scalar widths are data on unary tapes. -/
namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem read_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 0 = earlier.flatten ++ (word ++ rest))
    (hi : (d.stacks 5).length = earlier.length)
    (hr : ∀ row ∈ earlier, row.length = (d.stacks 2).length)
    (hw : word.length = (d.stacks 2).length)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    Eval read
      (earlier.length * (14 * (d.stacks 2).length + 10) + 15 * (d.stacks 2).length + 16)
      d (afterRead d word) := by
  let a : State 2 8 := ⟨d.regs, d.stacks ∘ readPorts⟩
  let b : State 2 8 :=
    ⟨readRegs d.regs 0 1 none, ArrayUpdatePrograms.readStacks word a.stacks⟩
  have ha : embedState id readPorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id readPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; rfl
    · intro i hi; rfl
  have hb : embedState id readPorts d b = afterRead d word := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id readPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      fin_cases i <;> simp [b, a, afterRead, ArrayUpdatePrograms.readStacks, readPorts]
    · intro i hi
      have h4 : i ≠ 4 := fun h => hi ⟨1, h.symm⟩
      have h5 : i ≠ 5 := fun h => hi ⟨2, h.symm⟩
      simp [afterRead, h4, h5]
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 2) 1 (by decide)
    earlier word rest (d.stacks 2) (d.stacks 5) d.regs a.stacks
    hs rfl rfl hi hr hw h6 h7 h8 h9
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 2) 1)
    id readPorts d Function.injective_id readPorts_injective (a := a) (b := b) ht
  simpa only [ha, hb, read] using he

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem readAt_eval (d : Data) (rows : List (List Bool)) (i : ℕ)
    (hp : d.stacks 0 = rows.flatten) (hi : (d.stacks 5).length = i)
    (hb : i < rows.length) (hw : ∀ row ∈ rows, row.length = (d.stacks 2).length)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    Eval read (i * (14 * (d.stacks 2).length + 10) + 15 * (d.stacks 2).length + 16)
      d (afterRead d (wordAt rows i)) := by
  have hsplit : rows = rows.take i ++ rows[i] :: rows.drop (i+1) := by
    rw [← List.drop_eq_getElem_cons hb]
    exact (List.take_append_drop i rows).symm
  have hflat : rows.flatten = (rows.take i).flatten ++
      (wordAt rows i ++ (rows.drop (i+1)).flatten) := by
    simpa only [wordAt, getElem!_pos, hb, List.flatten_append, List.flatten_cons]
      using congrArg List.flatten hsplit
  have hlen : (rows.take i).length = i := by simp [Nat.min_eq_left (Nat.le_of_lt hb)]
  have ht := read_eval d (rows.take i) (wordAt rows i) (rows.drop (i+1)).flatten
    (hp.trans hflat) (hi.trans hlen.symm)
    (by intro row hr; exact hw row (List.mem_of_mem_take hr))
    (wordAt_length rows i _ hb hw) h6 h7 h8 h9
  simpa only [hlen] using ht

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBasePUnranking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual base-p digit extraction

A digit is obtained by the checked binary long-division program. Its remainder
is copied to the fixed width of the modulus, while the padded high bits are
removed. Repeated extraction uses the quotient as the next rank. The modulus,
arity, and all widths are data; the instruction table is fixed.
-/

namespace SubexponentialSAT.SubexpBasePUnranking

open BitProgram StructuredCalls StackRoutines
open BinaryArithmetic ModularQuotientArithmetic

/-- The discarded high bits are zero when the modulus is positive. Their
removal is therefore justified rather than a truncation approximation. -/
theorem high_bits_zero (modulus rank : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus) :
    BinaryArithmetic.toNat ((divide modulus rank).2.drop modulus.length) = 0 := by
  let low := digit modulus rank
  let high := (divide modulus rank).2.drop modulus.length
  have hsplit : low ++ high = (divide modulus rank).2 :=
    List.take_append_drop _ _
  have hl : low.length = modulus.length := digit_length _ _
  have hlt : BinaryArithmetic.toNat (low ++ high) < 2 ^ low.length := by
    rw [hsplit, hl]
    exact (divide_remainder_lt modulus rank hm).trans (SubexpFactorProgram.toNat_lt_pow_length modulus)
  exact (SubexpFactorProgram.allZero_iff_toNat_zero high).mp
    ((SubexpFactorProgram.unary_validity_iff low high).mpr hlt)

theorem digit_value (modulus rank : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus) :
    BinaryArithmetic.toNat (digit modulus rank) = BinaryArithmetic.toNat rank % BinaryArithmetic.toNat modulus := by
  have hsplit := congrArg BinaryArithmetic.toNat
    (List.take_append_drop modulus.length (divide modulus rank).2)
  rw [SubexpFactorProgram.toNat_append, high_bits_zero modulus rank hm] at hsplit
  calc
    BinaryArithmetic.toNat (digit modulus rank) = BinaryArithmetic.toNat (divide modulus rank).2 := by
      simpa only [digit, Nat.mul_zero, Nat.add_zero] using hsplit
    _ = BinaryArithmetic.toNat rank % BinaryArithmetic.toNat modulus := divide_remainder_correct modulus rank hm

def remainingRank (modulus : List Bool) : ℕ → List Bool → List Bool
  | 0, rank => rank
  | k + 1, rank => remainingRank modulus k (nextRank modulus rank)

@[simp] theorem remainingRank_length (modulus rank : List Bool) (k : ℕ) :
    (remainingRank modulus k rank).length = rank.length := by
  induction k generalizing rank with
  | zero => rfl
  | succ k ih => simpa [remainingRank] using ih (nextRank modulus rank)

theorem copy_eval (src dst tmp : Fin 13)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (regs : Fin 8 → Bool) (stk : Fin 13 → List Bool) (ht : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp (1 : Fin 8) 3)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, copyStacks src dst stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace src dst tmp (1 : Fin 8) 3 hsd hst htd (by decide) regs stk ht)
    7 rfl rfl
  simpa [StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using h

theorem clear_eval (src : Fin 13) (regs : Fin 8 → Bool) (stk : Fin 13 → List Bool) :
    Eval (.call (clearProgram src (1 : Fin 8) 3)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, clearStacks src stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace src (1 : Fin 8) 3 regs stk) 2 rfl rfl
  simpa [StructuredProgram.State.withPC, clearResult, clearProgram, Nat.add_assoc] using h

theorem transfer_eval (src dst : Fin 13) (hsd : src ≠ dst)
    (regs : Fin 8 → Bool) (stk : Fin 13 → List Bool) :
    Eval (.call (transferProgram src dst (1 : Fin 8) 3)) (3 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, transferStacks src dst stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _
    (transferProgram_trace src dst (1 : Fin 8) 3 hsd (by decide) regs stk) 3 rfl rfl
  simpa [StructuredProgram.State.withPC, transferResult, transferProgram, Nat.add_assoc] using h

theorem counted_transfer_eval (regs : Fin 8 → Bool) (stk : Fin 13 → List Bool)
    (low high width : List Bool) (hrem : stk 0 = low ++ high) (hwidth : stk 9 = width)
    (hlen : width.length = low.length) :
    Eval (.call (ArrayPrograms.countedTransferProgram 9 0 11 (1 : Fin 8) 3))
      (4 * low.length + 3) ⟨regs, stk⟩
      ⟨readRegs regs 1 3 none, ArrayPrograms.countedTransferStacks 9 0 11 low high stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _
    (ArrayPrograms.countedTransferProgram_trace (9 : Fin 13) 0 11 (1 : Fin 8) 3
      (by decide) (by decide) (by decide) (by decide)
      low high width regs stk hrem hwidth hlen) 4 rfl rfl
  simpa [StructuredProgram.State.withPC, ArrayPrograms.countedTransferResult,
    ArrayPrograms.countedTransferProgram, Nat.add_assoc] using h

theorem collectDigit_eval (regs : Fin 8 → Bool)
    (low high modulus quotient arity rev output : List Bool) (hlen : low.length = modulus.length) :
    Eval collectDigit (11 * modulus.length + 2 * high.length + 6 * quotient.length + 17)
      ⟨regs, tapes (low ++ high) modulus [] quotient arity [] [] rev output⟩
      (state (readRegs regs 1 3 none) modulus quotient arity (low.reverse ++ rev) output) := by
  have h₁ := copy_eval 5 9 10 (by decide) (by decide) (by decide) regs
    (tapes (low ++ high) modulus [] quotient arity [] [] rev output) rfl
  simp only [copyStacks, tapes_5, tapes_9, List.append_nil, tapes_update_9] at h₁
  have h₂ := counted_transfer_eval (readRegs regs 1 3 none)
    (tapes (low ++ high) modulus [] quotient arity modulus [] rev output)
    low high modulus rfl rfl hlen.symm
  simp only [ArrayPrograms.countedTransferStacks, tapes_update_9, tapes_update_0,
    tapes_11, tapes_update_11, readRegs_reset] at h₂
  have h₃ := clear_eval 0 (readRegs regs 1 3 none)
    (tapes high modulus [] quotient arity [] [] (low.reverse ++ rev) output)
  simp only [clearStacks, tapes_0, tapes_update_0, readRegs_reset] at h₃
  have h₄ := transfer_eval 7 10 (by decide) (readRegs regs 1 3 none)
    (tapes [] modulus [] quotient arity [] [] (low.reverse ++ rev) output)
  simp only [transferStacks, tapes_7, tapes_10, tapes_update_7, tapes_update_10,
    List.append_nil, readRegs_reset] at h₄
  have h₅ := transfer_eval 10 6 (by decide) (readRegs regs 1 3 none)
    (tapes [] modulus [] [] arity [] quotient.reverse (low.reverse ++ rev) output)
  simp only [transferStacks, tapes_10, tapes_6, tapes_update_10, tapes_update_6,
    List.append_nil, List.reverse_reverse, List.length_reverse, readRegs_reset] at h₅
  have ht := h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | omega


end SubexponentialSAT.SubexpBasePUnranking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFieldRowPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving preparation of a local field-label row

Copy the enumerator's rank and the factor's unary arity into the checked
unranking routine, produce the fixed-width digit stream, and clear the padded
final quotient. The modulus, rank master, and arity master are preserved.
-/

namespace SubexponentialSAT.SubexpFieldRowPreparation

open BitProgram StructuredCalls StackRoutines

theorem embed_unrank (regs oldRegs : Fin 8 → Bool)
    (m rm am x ar out oldX oldAr oldOut : List Bool) :
    embedState id stackPort (data oldRegs m rm am oldX oldAr oldOut)
      (SubexpBasePUnranking.state regs m x ar [] out) = data regs m rm am x ar out := by
  apply state_ext
  · exact ProgramLinking.extend_id _ _
  · funext j
    by_cases hj : j.val < 13
    · let k : Fin 13 := ⟨j.val, hj⟩
      have hk : stackPort k = j := Fin.ext rfl
      rw [← hk, embedState_stack id stackPort _ _ stackPort_injective]
      have hports : ∀ i : Fin 13,
          (SubexpBasePUnranking.state regs m x ar [] out).stacks i =
            (data regs m rm am x ar out).stacks (stackPort i) := by
        intro i
        fin_cases i <;> rfl
      exact hports k
    · have hout : ¬ ∃ k, stackPort k = j := by
        rintro ⟨k, hk⟩
        have hval := congrArg (fun i : Fin 15 => i.val) hk
        have hklt := k.isLt
        change k.val = j.val at hval
        omega
      rw [embedState_stack_frame id stackPort _ _ j hout]
      have hc : j = 13 ∨ j = 14 := by
        have hjlt := j.isLt
        have hv : j.val = 13 ∨ j.val = 14 := by omega
        rcases hv with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hc with rfl | rfl <;> rfl

theorem copy_eval (src dst : Fin 15) (hsd : src ≠ dst)
    (hst : src ≠ 10) (htd : (10 : Fin 15) ≠ dst)
    (regs : Fin 8 → Bool) (stk : Fin 15 → List Bool) (ht : stk 10 = []) :
    Eval (.call (copyProgram src dst 10 (1 : Fin 8) 3)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, copyStacks src dst stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace src dst 10 (1 : Fin 8) 3 hsd hst htd (by decide) regs stk ht)
    7 rfl rfl
  simpa [StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using h

theorem clear_eval (regs : Fin 8 → Bool) (stk : Fin 15 → List Bool) :
    Eval (.call (clearProgram 6 (1 : Fin 8) 3)) (2 * (stk 6).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, clearStacks 6 stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace (6 : Fin 15) (1 : Fin 8) 3 regs stk) 2 rfl rfl
  simpa [StructuredProgram.State.withPC, clearResult, clearProgram, Nat.add_assoc] using h

end SubexponentialSAT.SubexpFieldRowPreparation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed loop applying the selected-index map to query records

The selector uses ports 0--5.  Port 6 is the framed query cursor, port 7
preserves the raw key/payload table, and port 8 accumulates framed answers.
Answers are prepended, so the returned record list reverses query order.
-/

namespace SubexponentialSAT.Subexp.SelectorMapProgram

open BitProgram StructuredCalls

theorem callbackCost_bound (records : List (List Bool × List Bool)) (query : List Bool) :
    callbackCost records query ≤
      220 * ((SelectorProgram.rawRecords records).length + 1) * (query.length + 1) := by
  have hs := selectorBudget_bound records query
  have hl := selected_length_le records query
  dsimp [callbackCost]
  nlinarith [Nat.zero_le (query.length * (SelectorProgram.rawRecords records).length)]

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial serialized-input bounds for the actual all-type bucket program. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open MatrixProgramSupport

theorem table_payload_bound (records : List BucketProgram.Record) (keys : List (List Bool))
    (T : ℕ) (hkeys : ∀ key ∈ keys, key.length ≤ T) :
    ∀ payload ∈ table records keys,
      payload.length ≤ 2 * T + 1 + (BucketProgram.encodeRecords records).length := by
  intro payload hp
  obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hp
  have hq := hkeys key hk
  have hb := selected_words_length_le records key
  simp only [bucketPayload, List.length_append, Encoding.length_frame]
  omega

theorem table_encoded_bound (records : List BucketProgram.Record) (keys : List (List Bool))
    (T : ℕ) (hkeys : ∀ key ∈ keys, key.length ≤ T) :
    (ProgramEncoding.encodeRecords (table records keys)).length ≤
      1 + (2 * (2 * T + 1 + (BucketProgram.encodeRecords records).length) + 2) * keys.length := by
  simpa only [table, List.length_map] using
    ProgramEncoding.encodeRecords_length_le (table records keys)
      (2 * T + 1 + (BucketProgram.encodeRecords records).length)
      (table_payload_bound records keys T hkeys)

/-- Every factor here is a data length or a constant. In particular the
degree does not depend on the number of types or on the vertex count. -/
theorem budget_bound (records : List BucketProgram.Record) (keys : List (List Bool))
    (T : ℕ) (hkeys : ∀ key ∈ keys, key.length ≤ T) :
    budget records keys ≤
      9 + keys.length *
        (6 * T + 100 * ((BucketProgram.encodeRecords records).length + 1) * (T + 1) + 7) +
        3 * (1 + (2 * (2 * T + 1 + (BucketProgram.encodeRecords records).length) + 2) * keys.length) := by
  have hi := iteration_bound records keys T hkeys
  have ht := table_encoded_bound records keys T hkeys
  unfold budget
  omega

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end


