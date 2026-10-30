-- Prove2me | Definitions.Def_OAIQ081S188
-- name    : OAIQ081S188
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:40:37.560988+00:00
-- url     : https://prove2.me/theorems/09dca2d2-e719-4649-aeed-527deba3294d
-- title:
--   Definitions bundle OAIQ081S188 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 13 definitions and 7 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.prepareLow`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.inverseLaw`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds.querySpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.Native.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.Native.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.lowProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction.sourceSpec`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.effect`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.output`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.prepend`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.factorUpdate`, `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.serviceState`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_HighQuerySetup`, `SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation`, `SubexponentialSAT_SqrtLogSpace_NativeQuerySpaceBounds`, `SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction`, `SubexponentialSAT_SqrtLogSpace_QueryHeadSourceFacts`, `SubexponentialSAT_SqrtLogSpace_QueryIncidenceCommand`, `SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation`, `SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction`, `SubexponentialSAT_SqrtLogSpace_QueryTargetMetadata`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleSourceAlignment`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyPreparation`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_Subexp_UniversalRowLoop`, `SubexponentialSAT_Subexp_UniversalRowProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S180`, `OAIQ081S181`, `OAIQ081S182`, `OAIQ081S183`, `OAIQ081S184` and `OAIQ081S185` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S189` and `OAIQ081S190`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds.envelope_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.hash_literals`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.marked_literals`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots.inventory_slots`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_polynomial`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds.envelope_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.hash_literals`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.marked_literals`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots.inventory_slots`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.low_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata.actual_target_degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_polynomial` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.active_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S180
import Definitions.Def_OAIQ081S181
import Definitions.Def_OAIQ081S182
import Definitions.Def_OAIQ081S183
import Definitions.Def_OAIQ081S184
import Definitions.Def_OAIQ081S185

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable incidence preparation. The inner worker has no arithmetic,
mask, beta, shifted-polynomial or dictionary oracle. Source generation is
composed as a fixed command in the outer768-stack frame. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

/-- Source205 and full choice206 are preserved through beta and row traversal.
Target caches are paid, temporary, and restored before returning. -/
def prepareLow : Code := .seq PerturbationBetaProgram.betaCommand (.seq origin
  (.seq initializeTarget (.seq (scanRows coordinate) (.seq finishTarget (clear 220)))))

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryIncidenceCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed native incidence command and its physical port ABI. The definitions
are extracted unchanged from the same emitter-specializer composition. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProgram
open SubexpScanPrimitives SubexpSetupStorage

def lowProgram := compiled PerturbationAssembly.prepareLow 205 217

namespace Native

/-- One fixed native incidence producer over all supplied ambient rows, including immediate specialization,
normalization, result export and complete local high-bank reclamation. -/
def command : Cmd 16 294 :=
  .seq (.call (ProgramLinking.liftProgram lowProgram id lowPorts))
    (.seq loadCommand
      (.seq (.call (ProgramLinking.liftProgram preparedProgram producerRegisters producerPorts))
        finishCommand))

def program := compiled command 205 217

end Native
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

/-- Data boundary with cleared Boolean registers and explicit constant ports. -/
def serviceState (source zero one : Word) : State 3 8 :=
  ⟨fun _ => false, (state false false source zero one emptyAccumulator).stacks⟩

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical source construction for universal interpolation rows

The input holds raw coefficient payloads, node inverses, and negative nodes.
It does not contain polynomial instructions. Fixed nested scans emit the
Lagrange products and correction sum as postfix source in canonical list order.
The surrounding row-data producer supplies the selected mismatch positions;
its matrix, cache, and type-mask construction is tracked separately.
-/

namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan scanCost)

def factorUpdate (x : Word) (f : Factor Word) (a : Accumulator) : Accumulator :=
  bump 1 (emit (factorCode x f) a)

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer loop assembling correction terms in selected-index order. -/

namespace SubexponentialSAT.Subexp.UniversalRowLoop

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)
open UniversalRowFactorLoop (indexWord)

def prepend (t : Tables) (positions : List ℕ) (i : ℕ) (acc : Word) : Word :=
  true :: (Encoding.frame (UniversalRowProgram.encodeTerm (term t positions i)) ++ acc)

def effect (t : Tables) (positions : List ℕ) (bits : Word) (a b : Data) : Prop :=
  b.stacks 31 = prepend t positions bits.length (a.stacks 31)

def output (t : Tables) (positions : List ℕ) (records : List Word) (acc : Word) : Word :=
  records.foldl (fun out bits => prepend t positions bits.length out) acc

end SubexponentialSAT.Subexp.UniversalRowLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def specializeCall : OuterCode :=
  .seq (SubexpSetupStorage.copyCmd 857 625 881)
    (liftCommand QueryProducerSpace.Native.command 205 217 id joinedPort)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query packing and arithmetic preparation. Numeric and physical
input caps are kept separate from the subsequent exponential node traversal.
Every arithmetic object is returned by its actual native producer. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- The concrete guarded frontend fixes all packing scalars and ring-array
sizes. These facts use its actual serialized bank, not a supplied layout. -/
theorem front_numeric_inputs (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base front : Data) (l : Fin 8 → ℕ) (w : Bank.Words)
    (hfront : FrontState q k base front l w) (S : ℕ)
    (hv : ∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).val i ≤ S)
    (hl : ∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).len i ≤ S) :
    let p := packingProblem q k hg
    let m := Execute.guardedModel (q.input k) l
    PackingCallerProgram.Sources front p ∧ PackingCallerProgram.Empty front ∧
    Circuit.Shape m w ∧
    projectState Exports.bankRegs Exports.bank front = Bank.state (front.regs ∘ Exports.bankRegs) w ∧
    p.n ≤ S ∧ p.factors ≤ S ∧ p.incidences ≤ S ∧ p.r ≤ S ∧ p.Q ≤ S ∧ p.s ≤ S ∧
    p.r ^ (2 * p.Q) ≤ S ∧ (∀ i, m.val i ≤ S) ∧ (∀ i, m.len i ≤ S) ∧
    0 < m.val 33 ∧ 0 < m.val 34 ∧
    (Circuit.result Serialization.code m).val 44 = 3 ^ (m.val 34) - 2 ∧
    3 ^ (m.val 34) ≤ 16 * (m.val 21 + 1) ^ 2 := by
  have hmv := QueryModelBudgets.serialized_model_values_le (q.input k) l S hv
  have hml := QueryModelBudgets.serialized_model_lengths_le (q.input k) l S hl
  obtain ⟨hn,hf,hD,hr,hQ,hs,_,hN,_⟩ :=
    QueryModelBudgets.produced_layout_scalars_le (q.input k) l S hmv
  refine ⟨packing_sources q k front hg l hfront.exported hfront.scopes hfront.forward hfront.ambient,
    packing_empty front hfront.privateEmpty hfront.spare, hfront.shape, hfront.bank,
    hn, ?_, ?_, hr, hQ, hs, hN, hmv, hml, ring_precision_pos _ _ hg,
    ring_degree_pos _ _ hg, ring_exponent _ _ hg, ?_⟩
  · simpa only [packing_factors_eq] using hf
  · simpa only [packingProblem_incidences] using hD
  · have hq : (produce (q.input k)).Q ≠ 0 := by
      have h := hg.2.2.2.2.2.2.1
      omega
    rw [Execute.guardedModel_degree (q.input k) l hq]
    have he : (Execute.guardedModel (q.input k) l).val 21 = (produce (q.input k)).Q :=
      (Execute.guardedModel_public (q.input k) l 4).trans
        (Layout.model_core_values (q.input k) l).2.2.2.2.1
    rw [he]
    exact fieldCard_le (q.input k)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

def inverseLaw (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (padding : Fin 8 → ℕ) (packed : Lower)
    (modulus : SubexpPreparedQuartic.Modulus 3 ((preparedModel q k padding).val 33))
    (cache : RingProgram.ScalarCache 3 ((preparedModel q k padding).val 33))
    (half : RingProgram.ScalarCode 3 ((preparedModel q k padding).val 33)) : Prop :=
  (RingProgram.modelRing ((preparedModel q k padding).val 33)
      (ring_precision_pos (q.input k) padding hg) (ring_degree_pos (q.input k) padding hg)
      (IrreducibleSearch.data (ring_degree_pos (q.input k) padding hg)) modulus cache).decode
      (LayoutDenominatorProgramQuery.value ((preparedModel q k padding).val 33)
        (IrreducibleSearch.data (ring_degree_pos (q.input k) padding hg)) modulus cache half
        (packed.stacks 740).length) *
      (2 : (IrreducibleSearch.data (ring_degree_pos (q.input k) padding hg)).O
        ((preparedModel q k padding).val 33)) ^ ((packed.stacks 740).length - 1) = 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query-entry facts from the actual arithmetic and native cache
producers. Pair masks are installed by the paid pair-start command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource
open LeafHeadSetupProgram QueryTupleState
open ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

section SharedSource

variable (src : SignatureTupleSource.ProducedSource)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : src.input.Q < 3 ^ (m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (hJ : 0 < m.val 42) (source : List (List (SAT.Literal (Fin src.input.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)

/-- One source snapshot supplies the native input and generated cache of the
factor specification. There is no second, independently chosen input record. -/
noncomputable def sourceSpec : Factor.Spec src.input.r src.input.Q src.input.n (m.val 34) :=
  nativeSpecOfInputs src.input m ht hd src.cacheWords src.cache M cache half e hp
    hfield q hv (m.val 42) hJ source hsource

end SharedSource

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSourceAlignment
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The frontend's actual mask, the produced head rows and the authentic
source factory use the same ambient variables and the same full integer keys.
No selected-coordinate or factory-alignment witness is supplied by the caller. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment

open scoped BigOperators
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram
open BucketTupleProgram.Concrete

section Query
attribute [local instance] Classical.propDecidable
variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
local notation "p" => LeafProgram.Query.packingProblem q k hg
variable (first : Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem q k hg).Q)
local notation "s" => Native.queryInputsAddressed q k hg first tail node
local notation "owner" => ProducedQueryRank.owner p
include q k hg first tail node


section Produced
open SubexpLiftRing SubexpQuarticRing
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : CacheCorrect (Native.queryInputsAddressed q k hg first tail node).height (unary (Native.queryInputsAddressed q k hg first tail node).R) (Native.queryInputsAddressed q k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed q k hg first tail node).Q < 3^(m.val 34)) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => LeafProgram.PreparedSource.nativeSpecOfInputs s m ht hd words hc
  M cache half e hp hfield q hv J hJ source hsource
local notation "sourceOwner" => owner ∘ Fin.cast (Native.Inputs.plans_length s)
include m ht hd words hc M cache half e hp hfield hv J hJ source hsource

/-- The source factory uses the same original integer matrix; only the
proof-level row index is transported to the actual saved plan-list length. -/
theorem produced_literal (j v : ℕ) :
    LayoutProducedMatrix.literalNat (spec).packing sourceOwner
      (spec).p.aWord.length (spec).p.R node j v =
      LayoutProducedMatrix.literalNat (s).packing owner (s).height.length (s).R node j v := by
  change LayoutProducedMatrix.literalNat
    (PackingIncidenceInput.reindexPacking (s).plans_length.symm (s).packing)
    (owner ∘ Fin.cast (s).plans_length) (s).height.length (s).R node j v = _
  exact SignatureKeySource.literalNat_reindex (s).plans_length.symm (s).packing owner
    (s).height.length (s).R node j v

end Produced
end Query
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadSourceFacts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual addressed query source fixes the native layout and factor
specification together. Its semantic facts require no independent source,
selected-head, integer-matrix or successful-layout alignment premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram LeafProgram
open SignatureTupleSourceAlignment

variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
local notation "p" => LeafProgram.Query.packingProblem q k hg
variable (first : Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem q k hg).Q)
local notation "s" => Native.queryInputsAddressed q k hg first tail node
variable (physical : Data)
  (ready : Native.Ready (Native.queryInputsAddressed q k hg first tail node) physical)
  (bound : ℕ) (bounded : OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound bound physical)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed q k hg first tail node).height
    (unary (Native.queryInputsAddressed q k hg first tail node).R)
    (Native.queryInputsAddressed q k hg first tail node).width words)

local notation "src" => addressedSource q k hg first tail node physical ready bound bounded ra rd rc words hc

section Factor
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed q k hg first tail node).Q < 3^(m.val 34))
    (hv : q.Valid) (hJ : 0 < m.val 42)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e hp
  hfield q hv hJ source hsource
local notation "owner" => ProducedQueryRank.owner p
local notation "sourceOwner" => owner ∘ Fin.cast (Native.Inputs.plans_length s)
local notation "head" => (fun t v => ProducedQueryRank.words p first tail (Sum.inl v) t)
local notation "H" => HighMarkedFrontend.highSet q

/-- All fixed-high coordinates vanish in the actual addressed source rows.
The physical plan list contains only low owners, including repeated incidences. -/
theorem source_high_zero (id j : ℕ) (v : Fin (s).n) (hvH : v ∈ H) :
    PerturbationAssembly.fixedSourceRow (spec).p (spec).ps (spec).packing (s).n id j v = 0 := by
  apply LeafProgram.NodeConcrete.fixedSourceRow_zero
  intro a ha he
  obtain ⟨i,hi,hia⟩ := List.mem_iff_getElem.mp ha
  have ho := plans_owner q k hg first tail node ⟨i,hi⟩
  change ((spec).ps.get ⟨i,hi⟩).1 = (sourceOwner ⟨i,hi⟩).val at ho
  simp only [List.get_eq_getElem,hia] at ho
  have hev : sourceOwner ⟨i,hi⟩ = v := Fin.ext (ho.symm.trans he)
  have hvowner : sourceOwner ⟨i,hi⟩ ∈ H := hev.symm ▸ hvH
  exact owner_low q k hg (Fin.cast (s).plans_length ⟨i,hi⟩) hvowner

/-- Concrete semantic certificate for the actual one-head visitor, generated
from one addressed ProducedSource and its authentic sourceSpec factory. -/
theorem sourceFacts : QueryVisitorHead.SourceFacts (src).input spec H
    sourceOwner (src).owner head where
  dimension := (s).plans_length
  plans_owner := plans_owner q k hg first tail node
  literal := produced_literal q k hg first tail node m ht hd words hc M cache half e hp
    hfield hv (m.val 42) hJ source hsource
  selected := selected_spec q k hg first tail node
  source_zero := source_high_zero q k hg first tail node physical ready bound bounded
    ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource
  rows_length := query_rows_length q k hg first tail node

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators

section AddressedSource
variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
  (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
variable (a : Data) (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
  (hbank : NativeLayoutLoad.SourceBank (Native.queryInputsAddressed query k hg first tail node) a)
  (hparked : ∀ j : Fin 14,
    (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed query k hg first tail node).height
    (unary (Native.queryInputsAddressed query k hg first tail node).R)
    (Native.queryInputsAddressed query k hg first tail node).width words)

local notation "src" => nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc

/-- The authentic source semantic facts are derived for this same bounded
snapshot; no independently supplied source, owner or selected head is used. -/
theorem nodeSource_facts
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (native).Q < 3^(m.val 34)) (hv : query.Valid) (hJ : 0 < m.val 42)
    (source : List (List (SAT.Literal (Fin (native).n))))
    (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source) :
    QueryVisitorHead.SourceFacts (src).input
      (QueryReadyConstruction.sourceSpec src m ht hd M cache half e hp
        hfield query hv hJ source hsource)
      (HighMarkedFrontend.highSet query)
      ((ProducedQueryRank.owner (LeafProgram.Query.packingProblem query k hg)) ∘
        Fin.cast (Native.Inputs.plans_length native)) (src).owner
      (fun t v => ProducedQueryRank.words (LeafProgram.Query.packingProblem query k hg)
        first tail (Sum.inl v) t) :=
  QueryHeadSourceFacts.sourceFacts query k hg first tail node
    (QuerySourceSnapshot.snapshot (sourceSnapshot a bits remaining))
    (QuerySourceSnapshot.snapshot_ready (sourceSnapshot_ready native a bits remaining hbank))
    A (QuerySourceSnapshot.snapshot_bound _ A
      (sourceSnapshot_bank_bound native a bits remaining A hbank hparked))
    ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource

end AddressedSource


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTargetMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The polynomial reconstructed by the native query is the target of its
actual generated ternary ring and idempotent code. Its constant term is the
exact marked or unmarked count; the executed parameter bank supplies both
the interpolation budget and sufficient precision. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata

open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram
open LeafProgram.PreparedSource LeafProgram.NodeConcrete

attribute [local irreducible] Execute.guardedModel

theorem numeric_order_pos (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) :
    0 < (numeric q k lengths).val 42 := by
  rw [numeric_J q k lengths hg]
  exact produce_J_pos _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTargetMetadata
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The coefficients emitted by the actual ordered node loop determine the
same fixed-length Hermite inputs consumed by the native reconstruction tail.
No canonical choice of coefficient bytes across node states is required. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryCountReconstruction

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open Polynomial DensePolynomialProgram LeafProgram LeafParametersProgram

theorem order_of_model (q : LeafQueryFrontend.Query) (k : ℕ)
    (lengths : Fin 8 → ℕ) (hg : Guard (q.input k)) (m : Circuit.Model)
    (hm : m = PreparedSource.numeric q k lengths) : 0 < m.val 42 := by
  rw [hm]
  exact QueryTargetMetadata.numeric_order_pos q k lengths hg

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryCountReconstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQuerySpaceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Polynomial space for the actual complete marked and accepted queries.
The input cap is the same immutable leaf bound used by preparation. The
conditioned stream, high loop and whole-word return use their own proved
prefix bounds; no query runtime or number of attained tuples enters space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds

open SqrtLog LeafParametersProgram NativeQueryInputBounds
open CostAssembly.Polynomial

/-- Exactly the prefix expression of the completed native query, with the
source and field allowances chosen by the actual literal-query caller. -/
def querySpace (q : LeafQueryFrontend.Query)
    (Cp dp Cn dn Cl dl Cf df N L k n h t d J f B : ℕ) : ℕ :=
  let S := sourceCap Cn dn Cl dl N L k
  let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
  let A := 12*P+4*N+6
  let T := A+S+2
  HighQueryCorrect.space q S (frontendCap Cf df L k) (S+f) B (Cp*(S+f+1)^dp)
    (HighQueryCorrect.loopSpace n h t d J A T) (QueryHeadBudgets.compact A)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds
end


