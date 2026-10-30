-- Prove2me | Definitions.Def_OAIQ081S170
-- name    : OAIQ081S170
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:13:36.979368+00:00
-- url     : https://prove2.me/theorems/276b1f2e-0973-4771-ab88-aeb1c44709d7
-- title:
--   Definitions bundle OAIQ081S170 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 10 definitions, 1 inductive type or structure and 14 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.nativeResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.bank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offsetModelBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.bankOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.buildProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.computeBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.produce`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install.build`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.staged`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLog_LeafProgramSourceNative`, `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyInput`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendPostBound`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay`, `SubexponentialSAT_SqrtLog_NativePackingBounds`, `SubexponentialSAT_SqrtLog_NativePackingBoundsAddress`, `SubexponentialSAT_SqrtLog_NativePackingBoundsOutput`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsCore`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsOutput`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsPolynomial`, `SubexponentialSAT_SqrtLog_PackingCallerProgramIncidence`, `SubexponentialSAT_SqrtLog_PackingCallerProgramJoin`, `SubexponentialSAT_SqrtLog_PackingCallerProgramState`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S153`, `OAIQ081S156`, `OAIQ081S157`, `OAIQ081S158`, `OAIQ081S159`, `OAIQ081S160`, `OAIQ081S162` and `OAIQ081S163` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ081S176`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.Ready.staged_common`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.staged_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.bank_ready` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.base_bound`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.Ready.staged_common`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.staged_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.bank_ready` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.base_bound`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S156
import Definitions.Def_OAIQ081S157
import Definitions.Def_OAIQ081S158
import Definitions.Def_OAIQ081S159
import Definitions.Def_OAIQ081S160
import Definitions.Def_OAIQ081S162
import Definitions.Def_OAIQ081S163

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native beta evaluation.  The caller supplies actual coefficient arrays,
not evaluated row values.  Masters205..212 are preserved;220 is the result.
Work230/231/232 holds the framed row scan, choice scan and reverse buffer. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives

def body : Code := .seq step peekRow

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

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

noncomputable def staged (a : OuterData) : OuterData :=
  embedState id basePort (initialized a)
    (LeafProgram.Incidence.staged (projectState id basePort (initialized a)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed source generation in the incidence worker. The result arrays are
witnesses of the actual run; no equality of separately generated byte arrays
is inferred from equality of their polynomial meanings. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

def nativeResult {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (s : LayoutSourceRowsProgram.Store)
    (rows : List (List (DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)))
    (regs : Fin 16 → Bool) : State 16 340 :=
  ⟨regs,Function.update (initializeFinish s (p.R+1) (d*baseWidth 3 p.t)) 205
    (Encoding.encodeList DensePolynomialProgram.encode rows)⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical caller contract. All hypotheses are bytes in retained masters,
blank work tapes, or explicit length bounds. In particular no native source
readiness or execution is assumed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

structure Input {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : Data) (v N f S : ℕ) : Prop where
  arithmetic : PerturbationAssembly.ArithmeticInput p.t p.model p.modulus p.cache (rawLow a)
  clean : ∀ i : Fin 340,i ∉ physicalLive → a.stacks (localPort i)=[]
  tmp : a.stacks 684=[]
  backups : ∀ i ∈ SourceStaging.backupPorts,a.stacks i=[]
  dimension : a.stacks (localPort 210)=List.replicate (p.R+1) true
  ambient : a.stacks (localPort 212)=LayoutSourcePlanLookup.unary N
  factor : a.stacks (localPort 216)=LayoutSourcePlanLookup.unary f
  literal : a.stacks (localPort 233)=LayoutSourcePlanLookup.unary v
  colors : a.stacks 130=List.replicate r true
  nodes : a.stacks 131=List.replicate Q true
  typeWidth : a.stacks 132=List.replicate (Q*r) true
  positive : a.stacks 710=p.saved.hp
  negative : a.stacks 711=p.saved.hn
  scalarWidth : a.stacks 140=p.width
  power : a.stacks 712=p.power.1
  powerNegative : p.power.2=[]
  radius : a.stacks 138=List.replicate p.R true
  offset : a.stacks 139=p.aWord
  metadata : a.stacks 135=SelectorProgram.rawRecords (PackingMetadata.records P (fun v => List.replicate v.val true) CollisionProgram.encodeType)
  plans : a.stacks 136=LayoutOwnerFiberProgram.stream ps
  inverses : a.stacks 713=(List.ofFn (fun i => RingProgram.flat (p.inverse i))).flatten
  negatives : a.stacks 714=(List.ofFn (fun i => RingProgram.flat (p.negative i))).flatten
  differences : a.stacks 715=(List.ofFn (fun i =>
    (List.ofFn (fun j => RingProgram.flat (p.difference i j))).flatten)).flatten
  ringWidth : a.stacks 717=p.ringWidth
  rowWidth : a.stacks 716=p.rowWidth
  zero : a.stacks 280=RingProgram.flat p.ops.zeroRun.1
  one : a.stacks 207=RingProgram.flat p.ops.oneRun.1
  minusOne : a.stacks 211=RingProgram.flat p.minusOne
  inverseDenominator : a.stacks 728=RingProgram.flat p.invDenom
  size : ∀ i : Fin 768,(a.stacks i).length ≤ S
  arraySize : (p.R+1)*(d*baseWidth 3 p.t) ≤ S
  countSize : p.R+1 ≤ S
  metadataSize : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S
  incidenceBound : ps.length ≤ S

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

def bank (a : Data) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ) : SourceBank.Data :=
  ⟨fun _ => false,clearedSourceStore (sourceBase a D W ps v N f) ∘ sourcePorts⟩

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPostBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def offsetModelBudget (m : Circuit.Model) : ℕ :=
  5000*(2*m.val 29+1)^2*(m.len 3+m.len 21+m.len 29+11)^2

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Syntactic no-read/no-write certificate for the existing native ring
producer.  Hidden collector tapes do not affect its exact execution time. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem constants : AvoidsCmd hidden constantsPhase := by
  have hc : ∀i∈constantStartPorts,¬hidden i := by
    intro i hi hh
    have h := hidden_bounds hh
    exact (collector_not_touched i h.1 h.2).2.2.2.1 hi
  exact ⟨clearPorts _ hc,
    ⟨buildConstant 498 207 (by decide) (by decide),
      buildConstant 508 211 (by decide) (by decide),
      buildConstant 203 280 (by decide) (by decide)⟩,
    copyPlan _ (by
      intro p hp
      simp only [constantAliases,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl <;> decide)⟩

theorem nodes : AvoidsCmd hidden nodesPhase := by
  have hn : AvoidsCmd hidden nodesCall :=
    avoids_call_lift_of_range _ _ _ _ (fun i => visible _ (nodes_avoids_collector i))
  have hf : AvoidsCmd hidden nodeFramesCall :=
    avoids_call_lift_of_range _ _ _ _ (by
      intro i
      apply visible
      left
      fin_cases i <;> norm_num [nodeFramePorts])
  exact ⟨clearPorts _ (by
      intro i hi
      apply visible
      simp [nodesStartPorts] at hi
      omega),copyPlan _ (by
      intro p hp
      simp only [nodeInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> decide),hn,
    overwrite 256 628 (by decide) (by decide),hf,overwrite 628 256 (by decide) (by decide)⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial cost of the actual native address-plan suffix. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram LayoutProgram
variable {U : Type*} [DecidableEq U]

/-- One coefficient and one degree apply to all represented input types,
dimensions, block counts, row widths and initial alphabets. -/
theorem budget_le (s : NativePacking.Spec U) : NativePacking.budget s ≤ 81000000 * sourceSize s ^ 12 := by
  have h := PackingBudgetArithmetic.final_le _ _ _ _ _ _ (sourceSize_pos s)
    (frontend_bound_le s) (buckets_budget_le s) (extraction_budget_le s)
    (vertices_budget_le s) (tail_budget_scaled_le s)
  unfold NativePacking.budget PackLabels.budget
  have hD : s.suffix.params.D=s.params.D := rfl
  simp only [hD]
  omega

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsAddress
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit scalar envelope for the actual two-address packing call. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes LayoutProgram

variable {D r Q : ℕ}

/-- Metadata emitted on native packing port32. -/
theorem metadata_output_bytes_le {U : Type*} [DecidableEq U]
    (s : NativePacking.Spec U) : s.suffix.metadata.length ≤ 34*sourceSize s^4 :=
  (metadata_length_le s).trans (PackingBudgetArithmetic.metadata_le _ _ _
    (sourceSize_pos s) (dimension_le s) (type_stream_le s))

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes LayoutProgram

theorem output_word_le {U : Type*} [DecidableEq U] (s : NativePacking.Spec U)
    (regs : Fin 16 → Bool) (i : Fin 48) :
    ((s.suffix.outputState regs).stacks i).length ≤ 34*sourceSize s^4 := by
  let S := sourceSize s
  have hS : 1 ≤ S := sourceSize_pos s
  have h4 : S ≤ S^4 := PackingBudgetArithmetic.le_power hS (by decide)
  have h24 : S^2 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have hD : s.params.D ≤ S := dimension_le s
  have hW : s.params.width.length ≤ S := width_le s
  have hA : (ProgramEncoding.encodeRecords s.params.alphabet).length ≤ S := alphabet_bytes_le s
  have hR : s.params.rows.flatten.length ≤ S := by dsimp [S,sourceSize]; omega
  have hd : s.params.Δ ≤ S := by have := depth_le s; dsimp [S]; omega
  have h34 : S ≤ 34*S^4 := by nlinarith
  have hblocks : s.suffix.packing.blockCount ≤ 34*S^4 :=
    (block_count_le s).trans (hD.trans h34)
  have hleft : s.suffix.packing.leftovers.length ≤ 34*S^4 :=
    (leftovers_length_le s).trans (hD.trans h34)
  have hm : s.suffix.metadata.length ≤ 34*S^4 := metadata_output_bytes_le s
  have ha : s.suffix.addresses.length ≤ 34*S^4 := by
    calc
      _ ≤ addressBound s.params.D := addresses_length_le s
      _ ≤ addressBound S := by unfold addressBound; gcongr
      _ ≤ 34*S^4 := by unfold addressBound; nlinarith
  have hv : wordBound s.params.D ≤ 34*S^4 := by
    calc
      _ ≤ wordBound S := by unfold wordBound; gcongr
      _ ≤ 34*S^4 := by unfold wordBound; nlinarith
  have hs : s.suffix.storage.length ≤ 34*S^4 := (storage_length_le s).trans hv
  have hi : s.suffix.inverse.length ≤ 34*S^4 := (inverse_length_le s).trans hv
  by_cases h30 : i=30
  · subst i
    change (List.replicate s.suffix.packing.blockCount true).length ≤ 34*S^4
    simpa only [List.length_replicate] using hblocks
  by_cases h31 : i=31
  · subst i
    change (List.replicate s.suffix.packing.leftovers.length true).length ≤ 34*S^4
    simpa only [List.length_replicate] using hleft
  by_cases h32 : i=32
  · subst i
    exact hm
  by_cases h33 : i=33
  · subst i
    exact ha
  by_cases h34 : i=34
  · subst i
    exact hs
  by_cases h35 : i=35
  · subst i
    exact hi
  by_cases h40 : i=40
  · subst i
    change s.params.rows.flatten.length ≤ 34*S^4
    omega
  by_cases h41 : i=41
  · subst i
    change s.params.width.length ≤ 34*S^4
    omega
  by_cases h42 : i=42
  · subst i
    change (List.replicate s.params.D true).length ≤ 34*S^4
    simp only [List.length_replicate]
    omega
  by_cases h43 : i=43
  · subst i
    change (List.replicate s.params.Δ true).length ≤ 34*S^4
    simp only [List.length_replicate]
    omega
  by_cases h44 : i=44
  · subst i
    change 1 ≤ 34*S^4
    omega
  by_cases h45 : i=45
  · subst i
    change (ProgramEncoding.encodeRecords s.params.alphabet).length ≤ 34*S^4
    omega
  simp only [PackLabels.Spec.outputState,PackingProgram.outputState,PackingProgram.inputState,
    h30,h31,h32,h33,h34,h35,h40,h41,h42,h43,h44,h45,ite_false,List.length_nil]
  omega

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/


/-! Native per-variable incident-factor scan from the original scope stream. -/


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem scan_eq_work (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    Scan.result r scopes n v z mask out = work r scopes n v z mask out
      (Encoding.encodeList Rows.unary (Scan.indices scopes v).reverse) [] := by
  apply congrArg (StructuredProgram.State.mk r)
  funext i; fin_cases i <;> simp [Scan.data]

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw scope bytes and a mask produce the actual installed incidence-pair table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev build : Cmd 16 48 := .call (ProgramLinking.liftProgram Boot.fullProgram id ports)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the physically generated owner/factor plans before the incidence
pair installer consumes them. The extra master is local port61. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open PackingLoaderProgram PackingIncidenceInput

def buildProgram := compiled Install.build 32 20

def produce : Code := .seq (.call (ProgramLinking.liftProgram buildProgram id lowPorts))
  (.seq (saveHigh 20 61) (.call (ProgramLinking.liftProgram incidenceTailProgram id lowPorts)))

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

theorem source_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    NativePackingBounds.sourceSize (p.spec a tail) ≤ sourceEnvelope S := by
  have hs := NativePackingBounds.address_sourceSize_le p.hr p.hQ (p.words a tail)
    (Address.address p.scopes p.n p.mask p.mask_le (p.words a tail) (p.words_length a tail))
  rw [p.words_length] at hs
  change NativePackingBounds.sourceSize (p.spec a tail) ≤ _ at hs
  apply hs.trans
  unfold NativePackingBounds.addressSize sourceEnvelope alphabetEnvelope planEnvelope
  have hw := width_le h
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  gcongr <;> first | exact h.incidences | exact h.types | exact hw | exact hn | exact h.alphabet

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem suffix_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (hp : Parameters outside p) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    suffixBudget (selectedStore outside p a tail) (p.spec a tail) ≤ suffixEnvelope S := by
  have hs := source_le h a tail
  have hb := (NativePackingBounds.budget_le (p.spec a tail)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 12))
  have hm := (NativePackingBounds.metadata_output_bytes_le (p.spec a tail)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 4))
  have hc := clearLowBudget_le ((p.spec a tail).suffix.outputState (fun _=>false))
    (34*sourceEnvelope S^4) (fun i => (NativePackingBounds.output_word_le (p.spec a tail)
      (fun _=>false) i).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 4)))
  have hp := prepare_le h hp a tail
  unfold suffixBudget suffixEnvelope
  omega

theorem coreBudget_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (hp : Parameters outside p) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q) :
    coreBudget outside p a tail ≤ coreEnvelope S := by
  have h0 := produce_le h a tail
  have h1 := loader_le h hp
  have h2 := selection_le h a tail hrows
  have h3 := suffix_le h hp a tail
  unfold coreBudget coreEnvelope
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def bankOutput (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) : Local :=
  framed (outputStore (Wide.parameterStore (Wide.project a)) p w tail)
    (⟨fun _=>false,fun _=>[]⟩ : Small)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem outputStore_word_le {outside : Store} {p : Problem} {S B : ℕ}
    (h : Cap outside p S) (ho : ∀ i,(outside i).length ≤ B)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 64) :
    ((outputStore outside p a tail) i).length ≤ B+outputEnvelope S := by
  have hs := source_le h a tail
  have hm := (NativePackingBounds.metadata_output_bytes_le (p.spec a tail)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 4))
  have hp := plans_le h a tail
  have ha := alphabet_bytes_le h
  have hw := width_le h
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  have hwords : ((p.words a tail).map ReadPlan.encodeWord).flatten.length ≤ (2*S)*S^2 := by
    rw [words_bits]; exact Nat.mul_le_mul hn hw
  have hsc := h.scopes
  have hoi := ho i
  by_cases h63 : i=63
  · subst i; simp only [outputStore,Function.update_same]; unfold outputEnvelope; omega
  by_cases h62 : i=62
  · subst i
    simp only [outputStore,selectedStore,Function.update_of_ne (by decide : (62 : Fin 64)≠63),Function.update_same]
    unfold outputEnvelope; omega
  by_cases h54 : i=54
  · subst i
    simp [outputStore,selectedStore,cached,loadedStore,planStore]
    unfold outputEnvelope; omega
  by_cases h53 : i=53
  · subst i
    simp [outputStore,selectedStore,cached,loadedStore,planStore]
    unfold outputEnvelope; omega
  by_cases h60 : i=60
  · subst i
    simp [outputStore,selectedStore,cached,loadedStore,planStore]
    unfold outputEnvelope; omega
  by_cases h61 : i=61
  · subst i
    simp [outputStore,selectedStore,cached,loadedStore,planStore]
    unfold outputEnvelope; omega
  simp only [outputStore,selectedStore,cached,loadedStore,planStore,
    Function.update_of_ne h63,Function.update_of_ne h62,Function.update_of_ne h54,
    Function.update_of_ne h53,Function.update_of_ne h60,Function.update_of_ne h61]
  omega

theorem parameterStore_word_le (a : Wide.Data) (p : Problem) (i : Fin 64) :
    ((Wide.parameterStore (Wide.project a)) i).length ≤ scalarSize (Wide.parameterStore (Wide.project a)) p := by
  have h := scalarSize_cap (Wide.parameterStore (Wide.project a)) p
  have h55 := h.l55
  have h56 := h.l56
  have h57 := h.l57
  have h58 := h.l58
  have h59 := h.l59
  unfold Wide.parameterStore
  split_ifs <;> subst_vars <;> first | exact h55 | exact h56 | exact h57 | exact h58 | exact h59 | simp

theorem bankOutput_word_le (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 64) :
    ((bankOutput a p w tail).stacks i).length ≤
      scalarSize (Wide.parameterStore (Wide.project a)) p+
        outputEnvelope (scalarSize (Wide.parameterStore (Wide.project a)) p) := by
  have h := outputStore_word_le (scalarSize_cap (Wide.parameterStore (Wide.project a)) p)
    (parameterStore_word_le a p) w tail i
  by_cases hi : i.val < 48
  · simp [bankOutput,framed_stack,hi]
  · simpa [bankOutput,framed_stack,hi] using h

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsPolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open CostAssembly.Polynomial
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem coreBudget_polynomial : ∃ C d : ℕ, ∀ (outside : Store) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)), Parameters outside p →
    (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q →
    coreBudget outside p w tail ≤ C*(scalarSize outside p+1)^d := by
  obtain ⟨C,d,h⟩ := coreEnvelope_ordinary
  exact ⟨C,d,fun outside p w tail hp hw =>
    (coreBudget_le (scalarSize_cap outside p) hp w tail hw).trans (h _)⟩

theorem bankOutput_word_polynomial : ∃ C d : ℕ, ∀ (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 64),
    ((bankOutput a p w tail).stacks i).length ≤
      C*(scalarSize (Wide.parameterStore (Wide.project a)) p+1)^d := by
  obtain ⟨C,d,h⟩ := ordinary_add ordinary_id outputEnvelope_ordinary
  exact ⟨C,d,fun a p w tail i => (bankOutput_word_le a p w tail i).trans (h _)⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramJoin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

noncomputable def computeBudget (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  SubexponentialSAT.SubexpSetupStorage.copyManyCost Wide.stagePairs (Wide.project a)+1+
    coreBudget (Wide.parameterStore (Wide.project a)) p w tail

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end


