-- Prove2me | Definitions.Def_OAIQ081S175
-- name    : OAIQ081S175
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:22:30.425803+00:00
-- url     : https://prove2.me/theorems/92161f6e-92c8-4fc0-8a35-d9690efcbf38
-- title:
--   Definitions bundle OAIQ081S175 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 14 definitions, 3 inductive types or structures and 13 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.queryInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.queryInputsAddressed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.queryWeightedHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.factorSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.generatedCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.heads`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.markIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.numeric`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.ArithmeticOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.FrontState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.Inputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.idempotentCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.idempotentPhase`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.producerCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.producerProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.producerWideCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.Data`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeAddressedQuery`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeQuery`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteQueryLiterals`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedFactorBase`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedSource`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedSpec`, `SubexponentialSAT_SqrtLog_LeafProgramQueryArithmetic`, `SubexponentialSAT_SqrtLog_LeafProgramQueryFrontState`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrame`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S166`, `OAIQ081S168` and `OAIQ081S169` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S181`, `OAIQ081S182`, `OAIQ081S183` and `OAIQ081S185`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.loader_caps` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S166
import Definitions.Def_OAIQ081S168
import Definitions.Def_OAIQ081S169

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

/-- This is an actual instruction trace from the one-word input, not an
assumption that a scalar cache or a modulus was supplied. -/
theorem scalarCommand_eval (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits = t) (ht : 0 < t) :
    ∃ n out, ∃ (M : SubexpPreparedQuartic.Modulus 3 t)
      (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t), ∃ logword,
      Eval scalarCommand n (inputData bits) out ∧
      ScalarOutput t bits M cache u logword out ∧ n ≤ scalarBudget t bits.length := by
  obtain ⟨M, logword, nb, rb, hlog, hlen, hnb, heb⟩ := boot_eval bits t hv ht
  let a : IdempotentPreparationProgram.Data := ⟨rb, bootStacks t bits M.bits logword⟩
  let W := 2*t + bits.length
  have hs : (List.replicate (2*t) true).length = SubexpLiftRing.baseWidth 3 t := by
    simp [RingProgram.ternary_baseWidth]
  have hr : Scalar.Rest a M.bits := by
    constructor
    · intro i; fin_cases i <;> simp [a, Scalar.low, bootStacks]
    · simp [a, bootStacks]
  have hp : ∀ i, (a.stacks (Scalar.port i)).length ≤ W := by
    intro i
    fin_cases i <;> simp [a, Scalar.port, bootStacks, W]
  obtain ⟨ns, out, cache, u, he, ho, hf, hn⟩ := Scalar.command_prepares t ht M
    (List.replicate (2*t) true) hs a W hr (by simp [a, bootStacks])
    (by simp [W]) hp (by simp [a, bootStacks]) (by simp [a, bootStacks])
  refine ⟨nb + ns, out, M, cache, u, logword, heb.seq he,
    ⟨ho, hlog, hlen, hf⟩, ?_⟩
  have hscalar := hn.trans (Scalar.budget_polynomial t W)
  rw [show t+W+1=3*t+bits.length+1 by dsimp [W]; omega] at hscalar
  unfold scalarBudget
  omega

/-- The local preparation executes on the declared physical ports. The
single input word is checked against the caller projection, and all other
caller tapes are framed by the actual lifted call. -/
theorem scalarCall_eval (a : LeafRingSetupProgram.Data) (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits = t) (ht : 0 < t)
    (ha : projectState (registers 8 (by decide)) scalar a = inputData bits) :
    ∃ n out, ∃ (M : SubexpPreparedQuartic.Modulus 3 t)
      (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t), ∃ logword,
      Eval scalarCall n a (embedState (registers 8 (by decide)) scalar a out) ∧
      ScalarOutput t bits M cache u logword out ∧ n ≤ scalarBudget t bits.length + 1 := by
  obtain ⟨n,out,M,cache,u,logword,he,ho,hn⟩ := scalarCommand_eval bits t hv ht
  have he' : Eval scalarCommand n (projectState (registers 8 (by decide)) scalar a) out :=
    ha.symm ▸ he
  exact ⟨n+1,out,M,cache,u,logword,
    eval_liftCommand_from_state scalarCommand 31 17 (registers 8 (by decide)) scalar a
      (registers_injective 8 (by decide)) scalar_injective he',
    ho,Nat.add_le_add_right hn 1⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram


/- Component: LeafRingSetupProgramSearch.lean -/

/-! Actual irreducible search followed by coefficient padding.  The model
below is the one selected by the finite search, not a supplied polynomial. -/

/-! Table generation for the cache produced by the native scalar stage.
The cache is not replaced by a separately chosen mathematical cache. -/

/-! Physical node generation and record framing at the ring-setup ports. -/

/-! Actual constant-vector and idempotent calls in the setup workspace. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

/-- The idempotent producer is called with a fresh private workspace.  It
computes its own scalar preparation from binary t; no coefficient array or
arithmetic oracle is passed to it. -/
abbrev idempotentCall : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram IdempotentProgram.completeProgram
    (registers 8 (by decide)) idempotent)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramCode.lean -/

/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing StackRoutines

abbrev idempotentPhase : Cmd 32 640 :=
  .seq (clearPorts idempotentStartPorts) (.seq (overwrite 373 511)
    (.seq RegisterResetProgram.all (.seq idempotentCall (overwrite 512 281))))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls LeafParametersProgram SubexpQuarticRing SubexpLiftRing

/-- The assembled producer uses the proved clearing boundaries between
services, rather than depending on unused values in prior work tapes. -/
abbrev producerCommand : Cmd 32 640 := .seq numberPhase (.seq coreCommand
  (.seq constantsPhase (.seq nodesPhase (.seq idempotentPhase finalCleanup))))

def producerProgram := compiled producerCommand (parameters 0) 300

abbrev producerWideCall : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram producerProgram wideRegisters wideStacks)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Instantiate the closed head setup from the actual frontend query and
native packing output. Structural bounds are derived, not new promises. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open PackingCallerProgram LeafParametersProgram

def queryInputs (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) : Inputs where
  n := (LeafProgram.Query.packingProblem q k hg).n
  N := (LeafProgram.Query.packingProblem q k hg).factors
  r := (LeafProgram.Query.packingProblem q k hg).r
  Q := (LeafProgram.Query.packingProblem q k hg).Q
  D := (LeafProgram.Query.packingProblem q k hg).incidences
  R := (produce (q.input k)).R
  occurrence := (q.input k).occurrence
  packing := ProducedQueryRank.packing (LeafProgram.Query.packingProblem q k hg) a tail
  node := t
  plans := PackingIncidenceInput.Semantics.nativeEntries q.scopeRows q.forward
  rows := ProducedQueryRank.rows (LeafProgram.Query.packingProblem q k hg) a tail
  low := q.forward.map Bool.not
  height := unary (TailInterval.intervalStart (produce (q.input k)).r (produce (q.input k)).Q
    (produce (q.input k)).R)
  width := unary (1+2*(TailInterval.intervalStart (produce (q.input k)).r (produce (q.input k)).Q
    (produce (q.input k)).R)*(produce (q.input k)).R+(produce (q.input k)).Q)
  plans_length := rfl
  rows_length := by simp [ProducedQueryRank.rows,Problem.words_length]
  rows_width := by
    intro row hrow
    obtain ⟨word,_,rfl⟩ := List.mem_map.mp hrow
    simp [ReadPlan.wordWidth]
  height_le := by
    simp only [unary,List.length_replicate]
    exact Interval.intervalStart_le_Q _ _ _ (LeafProgram.Query.packingProblem q k hg).hr
  width_boot := by simp [unary]
  width_node := by simp [unary,LeafProgram.Query.packingProblem]
  fiber_degree := by
    intro v hv
    exact ProducedQueryRank.query_fiber_length_le q k hg ⟨v,hv⟩

@[simp] theorem queryInputs_offset (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) :
    (queryInputs q k hg a tail t).offset=ProducedQueryRank.queryHeight q k := rfl

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeAddressedQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The saved runtime plan stream uses absolute word addresses: the factor
component is ambient+factor. This constructor matches those bytes while
preserving the incidence order, owner fibers, packing, and head relation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open PackingCallerProgram LeafParametersProgram

variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
variable (a : Word (LeafProgram.Query.packingProblem q k hg).r
  (LeafProgram.Query.packingProblem q k hg).Q)
variable (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
  (LeafProgram.Query.packingProblem q k hg).Q))
variable (t : Fin (LeafProgram.Query.packingProblem q k hg).Q)

def queryInputsAddressed : Inputs :=
  { queryInputs q k hg a tail t with
    plans := PackingIncidenceInput.addressedEntries q.scopeRows
      (LeafProgram.Query.packingProblem q k hg).n q.forward
    plans_length := by
      rw [PackingIncidenceInput.addressedEntries_length]
      rfl
    fiber_degree := by
      intro v hv
      rw [PackingIncidenceInput.addressedEntries_fibers]
      exact ProducedQueryRank.query_fiber_length_le q k hg ⟨v,hv⟩ }

@[simp] theorem queryInputsAddressed_plans :
    (queryInputsAddressed q k hg a tail t).plans=
      PackingIncidenceInput.addressedEntries q.scopeRows
        (LeafProgram.Query.packingProblem q k hg).n q.forward := rfl

@[simp] theorem queryInputsAddressed_offset :
    (queryInputsAddressed q k hg a tail t).offset=ProducedQueryRank.queryHeight q k := rfl

@[simp] theorem queryInputsAddressed_packing :
    (queryInputsAddressed q k hg a tail t).packing=(queryInputs q k hg a tail t).packing := rfl

@[simp] theorem queryInputsAddressed_rows :
    (queryInputsAddressed q k hg a tail t).rows=(queryInputs q k hg a tail t).rows := rfl

@[simp] theorem queryInputsAddressed_columnLength :
    (queryInputsAddressed q k hg a tail t).columnLength=
      (queryInputs q k hg a tail t).columnLength := rfl

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source parameter object is derived from the executed query's numeric
bank, ring setup, and native head cache. Source order and jet order remain distinct. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

def numeric (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ) :=
  Execute.guardedModel (q.input k) l

variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (first : Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q)
    (tail : List (Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q))
    (node : Fin (Query.packingProblem q k hg).Q)
    (l : Fin 8 → ℕ)

abbrev heads := LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A typed factor specification using the original query's row stream and
marked-clause selector. Finite-index transports do not alter stored bytes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics MomentsProgram
noncomputable section

def markIndex (q : LeafQueryFrontend.Query) : ℕ := (q.mark.map Fin.val).getD 0

theorem markIndex_valid (q : LeafQueryFrontend.Query) :
    q.mark.isSome=true → markIndex q < q.clauses.length := by
  cases h : q.mark with
  | none => simp
  | some v => simp [markIndex,h,v.isLt]

def factorSpec {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : ConstructivePacking.PackingData (Fin ps.length) (UniversalType r Q 1))
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin n)))) (hc : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t)
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)) : Factor.Spec r Q n d where
  p := p
  ps := ps
  packing := P
  u := p.t
  J := J
  hu := p.ht
  hJ := hJ
  theta := theta
  width := width
  widthLength := hw
  minus := p.minusOne
  minusValue := p.hminus
  one := NodeNative.originEntries p.ops.oneRun.1
  oneGood := origin_good p p.t J p.ht hJ
  oneValue := origin_value p p.t J p.ht hJ
  source := source
  rows := castRows (congrArg List.length hc) q.rows
  bitWidth := q.width.length
  bitWidthPositive := hv.1
  sourceBound := by simpa only [hc] using hv.2.2.2.1
  code := code
  marked := q.mark.isSome
  mark := markIndex q
  markValid := by
    have h := markIndex_valid q
    simpa only [hc,HashInputProgram.Expansion.encodedClauses,List.length_map] using h

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedFactorBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor specification uses the actual generated idempotent code and
native node word. The existential scalar preparation of the code is retained
as a witness; no canonical-byte assumption is needed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

def generatedCode {m : LeafParametersProgram.Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)}
    {half : RingProgram.ScalarCode 3 (m.val 33)} {e : LeafRingSetupProgram.Data}
    (hp : LeafRingSetupProgram.Produced m hd M cache half e) :
    GeneratedCode (m.val 33) (e.stacks 281) :=
  let h := hp.idempotent
  ⟨h.choose,h.choose_spec.choose,h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.1,h.choose_spec.choose_spec.choose_spec.2⟩

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

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

/-- These are the retained physical bytes of ring setup, not an additional
arithmetic-service oracle. Every private workspace byte is supplied by the
paid clearing operation above. -/
structure Inputs (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : InterpolationCacheProgram.Coeff t d) (base : Data) : Prop where
  modulus : base.stacks 194=M.bits
  table : base.stacks 201=RingTriple.tableEncoding (HornerProgram.modelTable t model M cache)
  width : (base.stacks 202).length=baseWidth 3 t
  scalarZero : base.stacks 203=cache.zero.val
  degree : (base.stacks 204).length=d
  zero : base.stacks 280=RingProgram.flat (RingProgram.modelProgram t model M cache).zeroRun.1
  one : base.stacks 207=RingProgram.flat (RingProgram.modelProgram t model M cache).oneRun.1
  minus : base.stacks 211=RingProgram.flat minusOne
  exponent : (base.stacks 209).length=3^d-2
  precision : (base.stacks 212).length=t

local instance instFactPrimeOfNatNat_solutions_r716ae9_1 : Fact (Nat.Prime 3) := ⟨by decide⟩
theorem staged_ready (base : Data) (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : InterpolationCacheProgram.Coeff t d)
    (h : Inputs t model M cache minusOne base) :
    InterpolationCacheProgram.Ready t model M cache minusOne (stagedStore base) := by
  constructor
  · constructor
    · constructor
      · simp [InterpolationCacheProgram.low,stagedStore_eq,inputIndex]
      · intro i
        fin_cases i <;>
          simp [ReconstructionProgram.RingAdapter.ports,ReconstructionProgram.RingAdapter.finalNative,ReconstructionProgram.RingAdapter.nativeStacks,
            InterpolationCacheProgram.low,stagedStore_eq,inputIndex,h.modulus,h.table,
            h.scalarZero]
    · simpa [InterpolationCacheProgram.low,stagedStore_eq,inputIndex] using h.modulus
    · simpa [InterpolationCacheProgram.low,stagedStore_eq,inputIndex] using h.width
    · simpa [InterpolationCacheProgram.low,stagedStore_eq,inputIndex] using h.scalarZero
    · simpa [InterpolationCacheProgram.low,stagedStore_eq,inputIndex] using h.table
    · simpa [InterpolationCacheProgram.low,stagedStore_eq,inputIndex] using h.degree
  · simpa [stagedStore_eq,inputIndex] using h.zero
  · simpa [stagedStore_eq,inputIndex] using h.one
  · simpa [stagedStore_eq,inputIndex] using h.minus
  · simpa [stagedStore_eq,inputIndex] using h.exponent
  · simpa [stagedStore_eq,inputIndex] using h.precision
  · intro i hi
    rw [stagedStore_eq]
    simp only [InterpolationCacheProgram.scratchPorts,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- The actual ring producer discharges the staged byte interface. The
remaining equality is the numerical bank's field-cardinality identity. -/
theorem inputs_of_produced (base : Data) (a : LeafRingSetupProgram.Data)
    (m : LeafParametersProgram.Circuit.Model) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33))
    (hp : Produced m hd M cache u a)
    (hb : ∀i,base.stacks (wideStacks i)=a.stacks i)
    (hexp : (LeafParametersProgram.Circuit.result LeafParametersProgram.Serialization.code m).val 44=
      3^(m.val 34)-2) :
    Inputs (m.val 33) (IrreducibleSearch.data hd) M cache
      (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero) base := by
  constructor
  · exact (hb 194).trans hp.caches.modulus
  · exact (hb 201).trans hp.native.table
  · rw [show base.stacks 202=a.stacks 202 from hb 202]; exact hp.caches.width
  · exact (hb 203).trans hp.caches.scalarZero
  · rw [show base.stacks 204=a.stacks 204 from hb 204]; exact hp.caches.degree
  · exact (hb 280).trans hp.caches.fullZero_model
  · exact (hb 207).trans hp.caches.fullOne_model
  · exact (hb 211).trans (hp.caches.fullMinusOne.trans
      (LeafProgram.Constants.constantCode_flat _ _ _).symm)
  · rw [show base.stacks 209=a.stacks 209 from hb 209,hp.exponent,List.length_replicate]
    exact hexp
  · rw [show base.stacks 212=a.stacks 212 from hb 212,hp.caches.precision,List.length_replicate]

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

theorem idempotents (i : Fin 640) (hi : i.val < 190) : EmptyPreserved idempotentPhase i := by
  unfold idempotentPhase
  have h : EmptyPreserved idempotentCall i := by
    apply highLift _ _ _ i hi
    intro j
    change 190 ≤ 480+j.val
    omega
  exact seq (clearPorts _ i) (seq (overwrite 373 511 i hi (by decide) (by decide))
    (seq (resetAll i) (seq h (overwrite 512 281 i hi (by decide) (by decide)))))

theorem producerCommand_preservesEmpty (i : Fin 640) (hi : i.val < 190) :
    EmptyPreserved producerCommand i :=
  seq (number i hi) (seq (core i hi) (seq (constants i hi) (seq (nodes i hi)
    (seq (idempotents i hi) (seq (clearPorts _ i) (resetAll i))))))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual arithmetic preparation per query: ring caches, interpolation
caches, then the inverse layout denominator. All three run before branching. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

/-- The final arithmetic state remembers the exact generated cache state;
only port728 is added after the ring/interpolation program. -/
structure ArithmeticOutput (base out : Data) (m : Circuit.Model) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data) : Prop where
  produced : LeafRingSetupProgram.Produced m hd M cache u e
  low : ∀i : Fin 640,i.val < 340 → out.stacks (LeafRingSetupProgram.wideStacks i)=e.stacks i
  inverse : out.stacks 713=InterpolationCacheProgram.inverseBytes (m.val 33) (IrreducibleSearch.data hd)
    M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
    (LeafRingSetupProgram.nodeWords (m.val 33) (m.val 34) (m.val 21))
  negative : out.stacks 714=InterpolationCacheProgram.negativeBytes (m.val 33) (IrreducibleSearch.data hd)
    M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
    (LeafRingSetupProgram.nodeWords (m.val 33) (m.val 34) (m.val 21))
  difference : out.stacks 715=InterpolationCacheProgram.differenceBytes (m.val 33) (IrreducibleSearch.data hd)
    M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
    (LeafRingSetupProgram.nodeWords (m.val 33) (m.val 34) (m.val 21))
  nodesLength : out.stacks 716=List.replicate (m.val 21*(m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33))) true
  width : out.stacks 717=List.replicate (m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33)) true
  denominator : out.stacks 728=RingProgram.flat (LayoutDenominatorProgramQuery.value
    (m.val 33) (IrreducibleSearch.data hd) M cache u (base.stacks 740).length)
  privateEmpty : ∀i : Fin 768,340 ≤ i.val → i.val < 660 → out.stacks i=[]
  highFrame : ∀i : Fin 768,660 ≤ i.val → i≠699 →
    i∉([713,714,715,716,717,728] : List (Fin 768)) → out.stacks i=base.stacks i
  collectorFrame : ∀i : Fin 768,320 ≤ i.val → i.val < 340 → out.stacks i=base.stacks i
  registerFrame : ∀i : Fin 40,16 ≤ i.val → i.val < 24 → out.regs i=base.regs i
  lowBlank : ∀i : Fin 768,i.val < 190 → base.stacks i=[] → out.stacks i=[]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteQueryLiterals
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact weighted clauses supplied to the native factor interpreter
inherit their low-literal incidence entries from the original query. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT HashInputProgram
open HashCircuitProgram HashCircuitProgram.Native

variable (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))))
    (hs : q.clauses=Expansion.encodedClauses source)

def queryWeightedHashes (t d : ℕ) :=
  (PreparedSource.castRows (congrArg List.length hs) q.rows).map
    (Expansion.weightedRow t d source)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
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

abbrev Data := State 40 896

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryFrontState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The physical output required by the following native packing/ring stages. -/
structure FrontState (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data)
    (l : Fin 8 → ℕ) (w : Bank.Words) : Prop where
  hashCount : b.stacks 704=List.replicate q.rows.length true
  scopes : b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows
  descending : b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)
  forward : b.stacks 719=q.forward
  low : b.stacks 134=q.forward.map Bool.not
  exported : LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) b
  bank : projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w
  shape : Circuit.Shape (Execute.guardedModel (q.input k) l) w
  guard : b.regs 8=true ↔ Guard (q.input k)
  privateEmpty : LeafQueryFrontend.emptyRange b 417 680
  spare : PackingSpare b
  ambient : b.stacks 709=q.ambient
  frame : ∀i : Fin 768,(i.val < 340 ∨ 680 ≤ i.val) →
    i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 →
    (∀j,Exports.destination j≠i) → b.stacks i=a.stacks i
  registerFrame : ∀i : Fin 40,11 ≤ i.val → b.regs i=a.regs i
  offset : BinaryArithmetic.toNat (b.stacks 141)=
    2*(Execute.guardedModel (q.input k) l).val 3*
      (8*(Execute.guardedModel (q.input k) l).val 21)^
        (2*(Execute.guardedModel (q.input k) l).val 29)
  canonicalLengths : l=q.inputLengths k

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end


