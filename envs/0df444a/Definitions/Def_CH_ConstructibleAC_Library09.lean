-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library09
-- name    : CH_ConstructibleAC_Library09
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:19:27.01511+00:00
-- url     : https://prove2.me/theorems/5b10b3cf-e0a1-4380-9ae4-185e7b5626d0
-- title:
--   Internal semantics and ordering of programs
-- statement:
--   The coded execution formulas describe the intended finite program computations, and finite descriptions carry a lexicographic order. This library supplies their realization and ordering interfaces, together with the absoluteness interfaces needed to interpret a computation in sufficiently large transitive stages. The resulting data lets later constructions compare descriptions internally.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackProgramEvalSemantics.lean#L1-L221; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryTokenOrderFormula.lean#L1-L191; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackTokenOrderFormula.lean#L1-L180; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackProgramOrderFormula.lean#L1-L157; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackProgramOrderAbsolute.lean#L1-L732; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackStepAbsolute.lean#L1-L367

import Definitions.Def_CH_ConstructibleAC_Library08
import Definitions.Def_CH_Constructible
import Mathlib.Data.List.Shortlex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sigma.Lex
import Mathlib.Data.Sum.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Tactic.FinCases

/-!
# Adaptation of Zike Liu's constructible-universe Choice proof

Original formalization: Copyright (c) 2026 Zike Liu, Apache-2.0.
Source: https://github.com/05-02-07/lean-constructible-universe
Commit: 7f5a7d03d63d9769172f17350bbe8303996e5b53.
All original per-file copyright notices are retained below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

This credit concerns the Prove2Me adaptation and semantic bridge. The original
well-ordering formalization is by Zike Liu, credited above and in each source section.
-/

set_option autoImplicit false


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalSemantics -/
section CUAdapterModule56
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Semantic correctness of the fixed postfix-program evaluator

The evaluator accepts arbitrary indexed-sequence representations, not only
the canonical graph produced by `sequenceCode`. This ensures correctness when
program codes are quantified over by a first-order formula.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open FiniteSequenceZF
open IndexedSequenceZF

 theorem valueAt_zero_iff_head?_eq
    {sequence : ZFSet.{u}} {xs : List ZFSet.{u}}
    (hrep : Represents sequence xs) (hne : xs ≠ []) (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequence, (∅ : ZFSet.{u}), value] <->
      xs.head? = some value := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      simpa [natCode, Ordinal.toZFSet_zero, eq_comm] using
        (satisfies_valueAt_represents_iff hrep 0 value)

 theorem valueAt_last_iff_getLast?_eq
    {sequence : ZFSet.{u}} {xs : List ZFSet.{u}}
    (hrep : Represents sequence xs) (n : Nat)
    (hlength : xs.length = n + 1) (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequence, natCode n, value] <->
      xs.getLast? = some value := by
  have hn : n < xs.length := by omega
  have hlast : xs.getLast? = some (xs.get ⟨n, hn⟩) := by
    rw [List.getLast?_eq_getElem?]
    have hindex : xs.length - 1 = n := by omega
    rw [hindex, List.getElem?_eq_getElem hn]
    rfl
  rw [satisfies_valueAt_represents_iff hrep, hlast,
    Option.some.injEq]
  constructor
  · rintro ⟨hn', hvalue⟩
    simpa only using hvalue.symm
  · intro hvalue
    refine ⟨hn, ?_⟩
    simpa only using hvalue.symm

/-- A valid indexed code represents at most one finite list. -/
 theorem represents_list_unique
    {sequence : ZFSet.{u}} {xs ys : List ZFSet.{u}}
    (hxs : Represents sequence xs) (hys : Represents sequence ys) :
    xs = ys := by
  rcases hxs with ⟨xsGraph, hxsCode, hxsGraph⟩
  rcases hys with ⟨ysGraph, hysCode, hysGraph⟩
  have hparts := ZFSet.pair_inj.mp (hxsCode.symm.trans hysCode)
  have hlength : xs.length = ys.length := natCode_injective hparts.1
  apply List.ext_get hlength
  intro k hkx hky
  let ix : Fin xs.length := ⟨k, hkx⟩
  let iy : Fin ys.length := ⟨k, hky⟩
  have hmem :
      ZFSet.pair (xs.get ix) (natCode k) ∈ ysGraph := by
    rw [← hparts.2]
    simpa only [ix] using (hxsGraph ix).1
  simpa only [ix, iy] using (hysGraph iy).2 (xs.get ix) hmem

/-- Raw codes accepted by the evaluator decode to genuine typed programs. -/
theorem satisfies_stackProgramEvalFormula_iff_exists_run
    (U programCode result : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
        (stackProgramEvalAssignment U programCode result) <->
      ∃ program : List
          (StackToken (Option (Constructible.ZFCarrier U))),
        Represents programCode (encodedStackProgram U program) ∧
          runStackProgram (rudimentaryGenerator U) program [] =
            some [result] := by
  rw [satisfies_stackProgramEvalFormula]
  constructor
  · rintro ⟨hprogramValid, traceCode, htraceValid,
      programLength, traceLength, finalStack,
      hprogramLength, htraceLength, hsuccessor,
      hinitial, hfinal, hfinalStack, hsteps⟩
    rcases
        (satisfies_sequenceValidityFormula_iff_exists_represents
          programCode).mp hprogramValid with
      ⟨rawTokens, hprogramRep⟩
    rcases
        (satisfies_sequenceValidityFormula_iff_exists_represents
          traceCode).mp htraceValid with
      ⟨rawStates, htraceRep⟩
    have hprogramLengthEq :
        programLength = natCode rawTokens.length :=
      (satisfies_hasLength_represents_iff hprogramRep
        programLength).mp hprogramLength
    have htraceLengthEq :
        traceLength = natCode rawStates.length :=
      (satisfies_hasLength_represents_iff htraceRep
        traceLength).mp htraceLength
    have hrawLength : rawStates.length = rawTokens.length + 1 := by
      apply natCode_injective
      rw [← htraceLengthEq, hsuccessor, hprogramLengthEq]
      exact (natCode_succ_eq_insert rawTokens.length).symm
    have hhead : rawStates.head? = some (listCode []) := by
      apply (valueAt_zero_iff_head?_eq htraceRep (by
        intro hnil
        simp only [hnil, List.length_nil] at hrawLength
        omega) (listCode [])).mp
      simpa only [listCode] using hinitial
    have hlast : rawStates.getLast? = some (listCode [result]) := by
      apply (valueAt_last_iff_getLast?_eq htraceRep
        rawTokens.length hrawLength (listCode [result])).mp
      rw [← hprogramLengthEq]
      simpa only [listCode, hfinalStack] using hfinal
    have hchain : RawStackFormulaChain U rawTokens rawStates := by
      refine ⟨hrawLength, ?_⟩
      intro k
      have hkMem : natCode k.1 ∈ programLength := by
        rw [hprogramLengthEq]
        exact (mem_natCode_iff _ _).mpr ⟨k.1, k.2, rfl⟩
      have hkFormula := hsteps (natCode k.1) hkMem
      rcases
          (satisfies_traceStepFormula_represents_iff
            U hprogramRep htraceRep k.1).mp hkFormula with
        ⟨hp, hi, ho, hstep⟩
      simpa only using hstep
    rcases exists_executionTrace_decoding_of_rawStackFormulaChain
        U rawTokens rawStates hhead hchain with
      ⟨program, states, hprogramCodes, hstateCodes, htrace⟩
    have hrun :
        runStackProgram (rudimentaryGenerator U) program [] =
          some [result] := by
      apply (exists_rawStackFormulaTrace_iff_run U program result).mp
      refine ⟨rawStates, ?_, hhead, hlast⟩
      simpa only [encodedStackProgram, hprogramCodes] using hchain
    refine ⟨program, ?_, hrun⟩
    simpa only [encodedStackProgram, hprogramCodes] using hprogramRep
  · rintro ⟨program, hprogramRep, hrun⟩
    rcases (exists_rawStackFormulaTrace_iff_run U program result).mpr
        hrun with
      ⟨rawStates, hchain, hhead, hlast⟩
    let traceCode : ZFSet.{u} := IndexedSequenceZF.sequenceCode rawStates
    have htraceRep : Represents traceCode rawStates := by
      exact represents_sequenceCode rawStates
    refine ⟨
      (satisfies_sequenceValidityFormula_iff_exists_represents
        programCode).mpr ⟨_, hprogramRep⟩,
      traceCode,
      (satisfies_sequenceValidityFormula_iff_exists_represents
        traceCode).mpr ⟨_, htraceRep⟩,
      natCode (encodedStackProgram U program).length,
      natCode rawStates.length,
      listCode [result], ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · exact (satisfies_hasLength_represents_iff hprogramRep _).mpr rfl
    · exact (satisfies_hasLength_represents_iff htraceRep _).mpr rfl
    · rcases hchain with ⟨hlength, _hsteps⟩
      rw [hlength]
      exact natCode_succ_eq_insert _
    · apply (valueAt_zero_iff_head?_eq htraceRep (by
        rcases hchain with ⟨hlength, _hsteps⟩
        intro hnil
        simp only [hnil, List.length_nil] at hlength
        omega) (listCode [])).mpr
      exact hhead
    · rcases hchain with ⟨hlength, _hsteps⟩
      apply (valueAt_last_iff_getLast?_eq htraceRep
        (encodedStackProgram U program).length hlength
        (listCode [result])).mpr
      exact hlast
    · intro index hindex
      rcases (mem_natCode_iff index
          (encodedStackProgram U program).length).mp hindex with
        ⟨k, hk, rfl⟩
      rcases hchain with ⟨hlength, hrawSteps⟩
      apply (satisfies_traceStepFormula_represents_iff
        U hprogramRep htraceRep k).mpr
      refine ⟨hk, by omega, by omega, ?_⟩
      simpa only using hrawSteps ⟨k, hk⟩

/-- Canonical program codes have exactly the intended execution semantics. -/
theorem satisfies_stackProgramEvalFormula_iff_run
    (U : ZFSet.{u})
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
        (stackProgramEvalAssignment U
          (stackProgramZFCode U program) result) <->
      runStackProgram (rudimentaryGenerator U) program [] =
        some [result] := by
  rw [satisfies_stackProgramEvalFormula_iff_exists_run]
  constructor
  · rintro ⟨decoded, hrep, hrun⟩
    have hencoded :
        encodedStackProgram U program = encodedStackProgram U decoded :=
      represents_list_unique
        (represents_sequenceCode (encodedStackProgram U program)) hrep
    have hprogram : program = decoded := by
      apply (stackTokenZFCode_injective U).list_map
      simpa only [encodedStackProgram] using hencoded
    simpa only [hprogram] using hrun
  · intro hrun
    exact ⟨program, represents_sequenceCode _, hrun⟩

end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule56



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryTokenOrderFormula -/
section CUAdapterModule57
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A formula for the generator-token order

This file internalizes the variable-token branch of
`RudimentaryTerm.codeTokenRel`, where the distinguished generator `U` comes
first and ordinary generators are compared by membership of their Kuratowski
pair in an internal relation graph `r`.

The free-variable layout of `generatorTokenLtFormula` is

`[U, r, zeroTag, leftCode, rightCode]`.

The formula uses two unrestricted witnesses for the decoded generator
payloads.  All structural checks on those witnesses are bounded formulas.
For actual variable tokens, `zeroTag` is instantiated by the empty set, which
is both `varTag` and the third component of the token code.

`RudimentaryStackTokenOrderFormula` combines this branch with operation-token
and mixed-token comparisons to obtain the full token order.
-/


universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section

/-- The raw relation represented by a Kuratowski-pair graph. -/
def generatorPairRel {U : ZFSet.{u}} (r : ZFSet.{u})
    (x y : Constructible.ZFCarrier U) : Prop :=
  ZFSet.pair x.1 y.1 ∈ r

/--
The generator order used by prefix tokens: `none`, representing `U`, is
strictly before every `some x`; ordinary generators use the graph `r`.
-/
def generatorTokenRel (U r : ZFSet.{u}) :
    Option (Constructible.ZFCarrier U) ->
      Option (Constructible.ZFCarrier U) -> Prop
  | none, none => False
  | none, some _ => True
  | some _, none => False
  | some x, some y => generatorPairRel r x y

/-- With assignment `[r,x,y]`, assert that `pair x y` belongs to `r`. -/
def pairMemAt {n : Nat} (relation x y : Fin n) : Delta0Formula n :=
  .boundedEx relation
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) x.castSucc y.castSucc)

@[simp]
theorem satisfies_pairMemAt {n : Nat} (relation x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (pairMemAt relation x y) s <->
      ZFSet.pair (s x) (s y) ∈ s relation := by
  simp only [pairMemAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, hpair⟩
    simpa only [hpair] using hq
  · intro hpair
    exact ⟨ZFSet.pair (s x) (s y), hpair, rfl⟩

/--
The bounded body after decoding payloads `x` and `y`.  Its context is
`[U, r, zeroTag, leftCode, rightCode, x, y]`.
-/
def generatorTokenLtBody : Delta0Formula 7 :=
  .conj
    (Delta0Formula.tripleEqAt 3 2 5 2)
    (.conj
      (Delta0Formula.tripleEqAt 4 2 6 2)
      (.disj
        (.conj (.eq 5 0) (.mem 6 0))
        (.conj (.mem 5 0)
          (.conj (.mem 6 0) (pairMemAt 1 5 6)))))

/--
The variable-token strict-order formula in context
`[U, r, zeroTag, leftCode, rightCode]`.
-/
def generatorTokenLtFormula : FOFormula 5 :=
  .ex (.ex generatorTokenLtBody.toFO)

/-- The two decoded witnesses occupy coordinates five and six. -/
@[simp]
theorem generatorTokenWitnessAssignment {A : Type u}
    (s : Tuple A 5) (x y : A) :
    snoc (snoc s x) y = ![s 0, s 1, s 2, s 3, s 4, x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_generatorTokenLtFormula (s : Tuple ZFSet.{u} 5) :
    FOFormula.Satisfies Delta0Formula.ZFMem generatorTokenLtFormula s <->
      exists x y : ZFSet.{u},
        s 3 = triple (s 2) x (s 2) /\
        s 4 = triple (s 2) y (s 2) /\
          ((x = s 0 /\ y ∈ s 0) \/
            (x ∈ s 0 /\ y ∈ s 0 /\ ZFSet.pair x y ∈ s 1)) := by
  simp only [generatorTokenLtFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO, generatorTokenLtBody,
    Delta0Formula.Satisfies, Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_disj, satisfies_pairMemAt]
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  rw [generatorTokenWitnessAssignment]
  rfl

@[simp]
theorem varTag_eq_empty : (varTag : ZFSet.{u}) = ∅ := by
  simp [varTag]

/-- No member of `U` is equal to `U`. -/
theorem carrier_value_ne_universe {U : ZFSet.{u}}
    (x : Constructible.ZFCarrier U) : x.1 ≠ U := by
  intro h
  have hself : U ∈ U := by
    simpa only [h] using x.2
  exact ZFSet.mem_irrefl U hself





end


end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule57



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackTokenOrderFormula -/
section CUAdapterModule58
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A first-order formula for the postfix stack-token order

The free-variable layout of `stackTokenLtFormula` is

`[U, r, varTag, appTag, empty, leftCode, rightCode]`.

Two unrestricted witnesses decode the payloads of the two token codes.  The
bounded body is the disjunction of the three possible strict-order branches:

* two variable tokens, ordered by `generatorTokenRel U r`;
* a variable token followed by an operation token;
* two operation tokens, ordered by membership of their finite ordinal codes.

There is deliberately no operation-variable branch.  On genuine
`stackTokenZFCode`s, the formula is exactly `stackTokenRel
(generatorTokenRel U r)`.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

/-! ## Formula -/

/--
The bounded body after decoding payloads `x` and `y`.  Its context is
`[U, r, varTag, appTag, empty, leftCode, rightCode, x, y]`.
-/
def stackTokenLtBody : Delta0Formula 9 :=
  .disj
    (.conj
      (Delta0Formula.tripleEqAt 5 2 7 4)
      (.conj
        (Delta0Formula.tripleEqAt 6 2 8 4)
        (.disj
          (.conj (.eq 7 0) (.mem 8 0))
          (.conj (.mem 7 0)
            (.conj (.mem 8 0) (pairMemAt 1 7 8))))))
    (.disj
      (.conj
        (Delta0Formula.tripleEqAt 5 2 7 4)
        (Delta0Formula.tripleEqAt 6 3 8 4))
      (.conj
        (Delta0Formula.tripleEqAt 5 3 7 4)
        (.conj
          (Delta0Formula.tripleEqAt 6 3 8 4)
          (.mem 7 8))))

/-- The complete strict-order formula for postfix stack-token codes. -/
def stackTokenLtFormula : FOFormula 7 :=
  .ex (.ex stackTokenLtBody.toFO)

/-- The intended assignment for comparing two internal stack-token codes. -/
def stackTokenLtAssignment (U r leftCode rightCode : ZFSet.{u}) :
    Tuple ZFSet.{u} 7 :=
  ![U, r, varTag, appTag, ∅, leftCode, rightCode]

@[simp]
theorem stackTokenLtWitnessAssignment {A : Type u}
    (s : Tuple A 7) (x y : A) :
    snoc (snoc s x) y =
      ![s 0, s 1, s 2, s 3, s 4, s 5, s 6, x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_stackTokenLtFormula (s : Tuple ZFSet.{u} 7) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackTokenLtFormula s <->
      exists x y : ZFSet.{u},
        ((s 5 = triple (s 2) x (s 4) /\
            s 6 = triple (s 2) y (s 4) /\
            ((x = s 0 /\ y ∈ s 0) \/
              (x ∈ s 0 /\ y ∈ s 0 /\ ZFSet.pair x y ∈ s 1))) \/
          (s 5 = triple (s 2) x (s 4) /\
            s 6 = triple (s 3) y (s 4)) \/
          (s 5 = triple (s 3) x (s 4) /\
            s 6 = triple (s 3) y (s 4) /\ x ∈ y)) := by
  simp only [stackTokenLtFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO, stackTokenLtBody,
    Delta0Formula.Satisfies, Delta0Formula.satisfies_disj,
    Delta0Formula.satisfies_tripleEqAt, satisfies_pairMemAt]
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  rw [stackTokenLtWitnessAssignment]
  rfl

/-! ## Exact semantics on genuine token codes -/

/-- The payload condition used by the variable-variable branch. -/
@[simp]
theorem generatorPayloadLt_iff
    (U r : ZFSet.{u})
    (left right : Option (Constructible.ZFCarrier U)) :
    ((rudimentaryGenerator U left = U /\
        rudimentaryGenerator U right ∈ U) \/
      (rudimentaryGenerator U left ∈ U /\
        rudimentaryGenerator U right ∈ U /\
        ZFSet.pair (rudimentaryGenerator U left)
          (rudimentaryGenerator U right) ∈ r)) <->
      generatorTokenRel U r left right := by
  cases left with
  | none =>
      cases right with
      | none =>
          simp [rudimentaryGenerator, generatorTokenRel,
            ZFSet.mem_irrefl]
      | some y =>
          simp [rudimentaryGenerator, generatorTokenRel,
            y.2, ZFSet.mem_irrefl]
  | some x =>
      have hxne : x.1 ≠ U := carrier_value_ne_universe x
      cases right with
      | none =>
          simp [rudimentaryGenerator, generatorTokenRel,
            x.2, hxne, ZFSet.mem_irrefl]
      | some y =>
          simp [rudimentaryGenerator, generatorTokenRel,
            generatorPairRel, x.2, y.2, hxne]

/--
The internal formula agrees exactly with the external structural order on
all genuine postfix stack-token codes.
-/
theorem satisfies_stackTokenLtFormula_tokenCodes
    (U r : ZFSet.{u})
    (left right : StackToken (Option (Constructible.ZFCarrier U))) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackTokenLtFormula
        (stackTokenLtAssignment U r
          (stackTokenZFCode U left) (stackTokenZFCode U right)) <->
      stackTokenRel (generatorTokenRel U r) left right := by
  rw [satisfies_stackTokenLtFormula]
  have hempty_ne_appTag : (∅ : ZFSet.{u}) ≠ appTag := by
    intro h
    apply (varTag_ne_appTag : (varTag : ZFSet.{u}) ≠ appTag)
    rw [varTag_eq_empty]
    exact h
  have happTag_ne_empty : (appTag : ZFSet.{u}) ≠ ∅ :=
    Ne.symm hempty_ne_appTag
  cases left with
  | inl leftGenerator =>
      cases right with
      | inl rightGenerator =>
          simp [stackTokenLtAssignment, stackTokenZFCode,
            stackTokenRel, triple, ZFSet.pair_inj,
            hempty_ne_appTag]
      | inr rightOperation =>
          simp [stackTokenLtAssignment, stackTokenZFCode,
            stackTokenRel, triple, ZFSet.pair_inj,
            hempty_ne_appTag, happTag_ne_empty]
  | inr leftOperation =>
      cases right with
      | inl rightGenerator =>
          simp [stackTokenLtAssignment, stackTokenZFCode,
            stackTokenRel, triple, ZFSet.pair_inj,
            hempty_ne_appTag, happTag_ne_empty]
      | inr rightOperation =>
          simp [stackTokenLtAssignment, stackTokenZFCode,
            stackTokenRel, triple, ZFSet.pair_inj,
            happTag_ne_empty]

end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule58



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderFormula -/
section CUAdapterModule59
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A first-order Shortlex order on postfix stack-program codes

The generic indexed-sequence comparison formula is specialized to the fixed
stack-token formula.  The resulting object-language relation has exactly the
external `stackProgramRel` semantics on genuine program codes.
-/


universe u v

namespace Constructible

/-! ## Mapping lemmas for structural list orders -/

theorem listLex_map_iff_of_length_eq {A : Type u} {B : Type v}
    {r : A → A → Prop} {R : B → B → Prop} (f : A → B)
    (hinjective : Function.Injective f)
    (hrel : ∀ x y, R (f x) (f y) ↔ r x y)
    (xs ys : List A) (hlength : xs.length = ys.length) :
    List.Lex R (xs.map f) (ys.map f) ↔ List.Lex r xs ys := by
  rw [listLex_iff_exists_index (by simpa using hlength),
    listLex_iff_exists_index hlength]
  constructor
  · rintro ⟨k, hx, hy, htake, hk⟩
    have hx' : k < xs.length := by simpa using hx
    have hy' : k < ys.length := by simpa using hy
    refine ⟨k, hx', hy', ?_, ?_⟩
    · apply hinjective.list_map
      simpa only [List.map_take] using htake
    · have hk' : R (f (xs.get ⟨k, hx'⟩))
          (f (ys.get ⟨k, hy'⟩)) := by
        simpa only [List.get_eq_getElem, List.getElem_map] using hk
      exact (hrel _ _).mp hk'
  · rintro ⟨k, hx, hy, htake, hk⟩
    refine ⟨k, by simpa using hx, by simpa using hy, ?_, ?_⟩
    · simp only [← List.map_take, htake]
    · have hk' := (hrel _ _).mpr hk
      simpa only [List.get_eq_getElem, List.getElem_map] using hk'

theorem listShortlex_map_iff {A : Type u} {B : Type v}
    {r : A → A → Prop} {R : B → B → Prop} (f : A → B)
    (hinjective : Function.Injective f)
    (hrel : ∀ x y, R (f x) (f y) ↔ r x y)
    (xs ys : List A) :
    List.Shortlex R (xs.map f) (ys.map f) ↔
      List.Shortlex r xs ys := by
  rw [List.shortlex_def, List.shortlex_def]
  simp only [List.length_map]
  constructor
  · rintro (hlength | ⟨hlength, hlex⟩)
    · exact Or.inl hlength
    · exact Or.inr ⟨hlength,
        (listLex_map_iff_of_length_eq f hinjective hrel xs ys hlength).mp hlex⟩
  · rintro (hlength | ⟨hlength, hlex⟩)
    · exact Or.inl hlength
    · exact Or.inr ⟨hlength,
        (listLex_map_iff_of_length_eq f hinjective hrel xs ys hlength).mpr hlex⟩

namespace Godel.RudimentaryTerm

noncomputable section

open IndexedSequenceZF

/-! ## The specialized formula -/

/--
Program comparison layout:

`[U, relation, varTag, appTag, empty, omega, leftProgram, rightProgram]`.
-/
def stackProgramLtFormula : FOFormula 8 :=
  IndexedSequenceZF.shortlexFormula stackTokenLtFormula

/-- The intended raw assignment for two genuine postfix programs. -/
def stackProgramLtAssignment (U relation : ZFSet.{u})
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    Tuple ZFSet.{u} 8 :=
  ![U, relation, varTag, appTag, ∅, Ordinal.omega0.toZFSet,
    stackProgramZFCode U left, stackProgramZFCode U right]

/-- The structural program-order formula has exact Shortlex semantics. -/
@[simp]
theorem satisfies_stackProgramLtFormula
    (U relation : ZFSet.{u})
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramLtFormula
        (stackProgramLtAssignment U relation left right) ↔
      stackProgramRel (generatorTokenRel U relation) left right := by
  let params : Tuple ZFSet.{u} 5 :=
    ![U, relation, varTag, appTag, ∅]
  let rawTokenRel : ZFSet.{u} → ZFSet.{u} → Prop :=
    fun x y =>
      FOFormula.Satisfies Delta0Formula.ZFMem stackTokenLtFormula
        (snoc (snoc params x) y)
  have hshort :=
    IndexedSequenceZF.satisfies_shortlexFormula_sequenceCode_iff
      stackTokenLtFormula params rawTokenRel
      (fun _ _ => Iff.rfl)
      (left.map (stackTokenZFCode U))
      (right.map (stackTokenZFCode U))
  have htoken : ∀ x y : StackToken
      (Option (Constructible.ZFCarrier U)),
      rawTokenRel (stackTokenZFCode U x) (stackTokenZFCode U y) ↔
        stackTokenRel (generatorTokenRel U relation) x y := by
    intro x y
    change FOFormula.Satisfies Delta0Formula.ZFMem stackTokenLtFormula
      (snoc (snoc params (stackTokenZFCode U x))
        (stackTokenZFCode U y)) ↔
      stackTokenRel (generatorTokenRel U relation) x y
    have hassign :
        snoc (snoc params (stackTokenZFCode U x))
            (stackTokenZFCode U y) =
          ![U, relation, varTag, appTag, ∅,
            stackTokenZFCode U x, stackTokenZFCode U y] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    exact satisfies_stackTokenLtFormula_tokenCodes U relation x y
  have hmap := listShortlex_map_iff (stackTokenZFCode U)
    (stackTokenZFCode_injective U) htoken left right
  have hformula :
      FOFormula.Satisfies Delta0Formula.ZFMem stackProgramLtFormula
          (stackProgramLtAssignment U relation left right) ↔
        List.Shortlex rawTokenRel
          (left.map (stackTokenZFCode U))
          (right.map (stackTokenZFCode U)) := by
    have hassign :
        stackProgramLtAssignment U relation left right =
          snoc
            (snoc (snoc params Ordinal.omega0.toZFSet)
              (sequenceCode (left.map (stackTokenZFCode U))))
            (sequenceCode (right.map (stackTokenZFCode U))) := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    simpa only [stackProgramLtFormula] using hshort
  exact hformula.trans hmap

end

end Godel.RudimentaryTerm

end Constructible
end CUAdapterModule59



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderAbsolute -/
section CUAdapterModule60
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Absoluteness of the postfix-program order on genuine codes

`stackProgramLtFormula` contains unrestricted witnesses for decoded lengths,
graphs, entries, and token payloads.  Consequently it is not a bounded formula
and no blanket absoluteness theorem applies.  This file supplies constructible
witnesses for genuine program codes and proves the restricted semantics
directly.
-/


open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open IndexedSequenceZF
open FiniteSequenceZF

/-- Every entry in the encoded-token list of a genuine program is in `L`. -/
theorem stackTokenCodes_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (program : List (StackToken (Option (Constructible.ZFCarrier U)))) :
    ∀ code ∈ program.map (stackTokenZFCode U), code ∈ L := by
  intro code hcode
  rcases List.mem_map.mp hcode with ⟨token, _htoken, rfl⟩
  exact stackTokenZFCode_mem_L hU token



/-- All eight free coordinates of the program comparison, packaged in `L`. -/
def stackProgramLtLAssignment (U relation : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    Tuple Model.LCarrier.{u} 8 :=
  ![⟨U, hU⟩,
    ⟨relation, hrelation⟩,
    ⟨varTag, varTag_mem_L⟩,
    ⟨appTag, appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩,
    ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩,
    ⟨stackProgramZFCode U left, stackProgramZFCode_mem_L hU left⟩,
    ⟨stackProgramZFCode U right, stackProgramZFCode_mem_L hU right⟩]

theorem stackProgramLtLAssignment_val (U relation : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    (fun i =>
      (stackProgramLtLAssignment U relation hU hrelation left right i).1) =
      stackProgramLtAssignment U relation left right := by
  funext i
  fin_cases i <;> rfl

/-! ## Component formulas over `LCarrier` -/

local notation "LMem" => Model.lCarrierMem

theorem satisfies_kuratowskiPairEqAt_lCarrier {n : Nat}
    (pair left right : Fin n) (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.kuratowskiPairEqAt pair left right).toFO s ↔
      (s pair).1 = ZFSet.pair (s left).1 (s right).1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]

@[simp]
theorem satisfies_functionGraphValueAt_lCarrier {n : Nat}
    (graph value index : Fin n) (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (IndexedSequenceZF.functionGraphValueAt graph value index) s ↔
      ZFSet.pair (s value).1 (s index).1 ∈ (s graph).1 := by
  rw [IndexedSequenceZF.functionGraphValueAt,
    Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO]
  simp only [Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hq
    exact ⟨ZFSet.pair (s value).1 (s index).1, hq, rfl⟩

@[simp]
theorem satisfies_valueAtFormula_lCarrier_iff
    (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ L)
    (k : Nat) (value : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            IndexedSequenceZF.sequenceCode_mem_L hxs⟩,
          ⟨natCode k, natCode_mem_L k⟩, value] ↔
      ∃ hk : k < xs.length, value.1 = xs.get ⟨k, hk⟩ := by
  rw [IndexedSequenceZF.valueAtFormula,
    Delta0Formula.satisfies_toFO_lCarrier_absolute]
  have hval :
      (fun i =>
        (![⟨IndexedSequenceZF.sequenceCode xs,
              IndexedSequenceZF.sequenceCode_mem_L hxs⟩,
            ⟨natCode k, natCode_mem_L k⟩, value] i).1) =
        ![IndexedSequenceZF.sequenceCode xs, natCode k, value.1] := by
    funext i
    fin_cases i <;> rfl
  rw [hval]
  exact IndexedSequenceZF.satisfies_valueAt_sequenceCode_iff xs k value.1

@[simp]
theorem satisfies_samePrefixFormula_lCarrier
    (leftSequence rightSequence bound : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.samePrefixFormula
        ![leftSequence, rightSequence, bound] ↔
      ∀ index : Model.LCarrier.{u}, index.1 ∈ bound.1 →
        ∃ value : Model.LCarrier.{u},
          FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
              ![leftSequence, index, value] ∧
            FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
              ![rightSequence, index, value] := by
  simp only [IndexedSequenceZF.samePrefixFormula,
    FOFormula.satisfies_boundedAll, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  constructor
  · intro h index hindex
    rcases h index hindex with ⟨value, hleft, hright⟩
    refine ⟨value, ?_, ?_⟩
    · change FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
        ![leftSequence, index, value] at hleft
      exact hleft
    · change FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
        ![rightSequence, index, value] at hright
      exact hright
  · intro h index hindex
    rcases h index hindex with ⟨value, hleft, hright⟩
    refine ⟨value, ?_, ?_⟩
    · change FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
        (fun i => snoc (snoc ![leftSequence, rightSequence, bound] index) value
          (![0, 3, 4] i))
      exact hleft
    · change FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
        (fun i => snoc (snoc ![leftSequence, rightSequence, bound] index) value
          (![1, 3, 4] i))
      exact hright

theorem satisfies_samePrefix_sequenceCode_lCarrier_iff
    (xs ys : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ L) (hys : ∀ y ∈ ys, y ∈ L)
    (k : Nat) :
    FOFormula.Satisfies LMem IndexedSequenceZF.samePrefixFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            IndexedSequenceZF.sequenceCode_mem_L hxs⟩,
          ⟨IndexedSequenceZF.sequenceCode ys,
            IndexedSequenceZF.sequenceCode_mem_L hys⟩,
          ⟨natCode k, natCode_mem_L k⟩] ↔
      ∀ j : Nat, j < k →
        ∃ hx : j < xs.length, ∃ hy : j < ys.length,
          xs.get ⟨j, hx⟩ = ys.get ⟨j, hy⟩ := by
  rw [satisfies_samePrefixFormula_lCarrier]
  constructor
  · intro h j hj
    let index : Model.LCarrier.{u} := ⟨natCode j, natCode_mem_L j⟩
    rcases h index ((mem_natCode_iff _ _).mpr ⟨j, hj, rfl⟩) with
      ⟨value, hleft, hright⟩
    rcases (satisfies_valueAtFormula_lCarrier_iff xs hxs j value).mp
        (by simpa only [index] using hleft) with ⟨hx, hvalueX⟩
    rcases (satisfies_valueAtFormula_lCarrier_iff ys hys j value).mp
        (by simpa only [index] using hright) with ⟨hy, hvalueY⟩
    exact ⟨hx, hy, hvalueX.symm.trans hvalueY⟩
  · intro h index hindex
    rcases (mem_natCode_iff index.1 k).mp hindex with ⟨j, hj, hindexEq⟩
    rcases h j hj with ⟨hx, hy, hxy⟩
    let indexJ : Model.LCarrier.{u} := ⟨natCode j, natCode_mem_L j⟩
    have hindexCarrier : index = indexJ := Subtype.ext hindexEq
    have hvalueL : xs.get ⟨j, hx⟩ ∈ L :=
      hxs _ (List.get_mem xs ⟨j, hx⟩)
    let value : Model.LCarrier.{u} := ⟨xs.get ⟨j, hx⟩, hvalueL⟩
    refine ⟨value, ?_, ?_⟩
    · have hleft :=
        (satisfies_valueAtFormula_lCarrier_iff xs hxs j value).mpr
          ⟨hx, rfl⟩
      simpa only [hindexCarrier, indexJ] using hleft
    · have hright :=
        (satisfies_valueAtFormula_lCarrier_iff ys hys j value).mpr
          ⟨hy, hxy⟩
      simpa only [hindexCarrier, indexJ, value] using hright

@[simp]
theorem satisfies_hasLengthFormula_lCarrier_iff
    (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ L)
    (length : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.hasLengthFormula
        ![⟨IndexedSequenceZF.sequenceCode xs,
            IndexedSequenceZF.sequenceCode_mem_L hxs⟩, length] ↔
      length.1 = natCode xs.length := by
  simp only [IndexedSequenceZF.hasLengthFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨graph, hpair⟩
    have hpairRaw :=
      (satisfies_kuratowskiPairEqAt_lCarrier
        (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
        (snoc ![⟨IndexedSequenceZF.sequenceCode xs,
          IndexedSequenceZF.sequenceCode_mem_L hxs⟩, length] graph)).mp hpair
    exact (ZFSet.pair_inj.mp hpairRaw).1.symm
  · intro hlength
    let graph : Model.LCarrier.{u} :=
      ⟨IndexedSequenceZF.graph xs,
        IndexedSequenceZF.graphFrom_mem_L hxs 0⟩
    refine ⟨graph, ?_⟩
    apply (satisfies_kuratowskiPairEqAt_lCarrier
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
      (snoc ![⟨IndexedSequenceZF.sequenceCode xs,
        IndexedSequenceZF.sequenceCode_mem_L hxs⟩, length] graph)).mpr
    change IndexedSequenceZF.sequenceCode xs =
      ZFSet.pair length.1 (IndexedSequenceZF.graph xs)
    rw [hlength]
    rfl

@[simp]
theorem satisfies_uniqueValueAtBody_lCarrier
    (omega sequence length graph index value : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.uniqueValueAtBody
        ![omega, sequence, length, graph, index, value] ↔
      ZFSet.pair value.1 index.1 ∈ graph.1 ∧
        ∀ other : Model.LCarrier.{u},
          ZFSet.pair other.1 index.1 ∈ graph.1 → other.1 = value.1 := by
  simp [IndexedSequenceZF.uniqueValueAtBody,
    IndexedSequenceZF.satisfies_formulaImp,
    satisfies_functionGraphValueAt_lCarrier, Subtype.ext_iff,
    Model.snoc_eq_finSnoc]

@[simp]
theorem satisfies_totalFunctionalBody_lCarrier
    (omega sequence length graph index : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.totalFunctionalBody
        ![omega, sequence, length, graph, index] ↔
      (index.1 ∈ length.1 →
        ∃ value : Model.LCarrier.{u},
          ZFSet.pair value.1 index.1 ∈ graph.1 ∧
            ∀ other : Model.LCarrier.{u},
              ZFSet.pair other.1 index.1 ∈ graph.1 →
                other.1 = value.1) := by
  simp [IndexedSequenceZF.totalFunctionalBody,
    IndexedSequenceZF.satisfies_formulaImp,
    satisfies_uniqueValueAtBody_lCarrier, Model.snoc_eq_finSnoc]

@[simp]
theorem satisfies_sequenceValidityFormula_lCarrier
    (omega sequence : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
        ![omega, sequence] ↔
      ∃ length graph : Model.LCarrier.{u},
        sequence.1 = ZFSet.pair length.1 graph.1 ∧
          length.1 ∈ omega.1 ∧
          ∀ index : Model.LCarrier.{u}, index.1 ∈ length.1 →
            ∃ value : Model.LCarrier.{u},
              ZFSet.pair value.1 index.1 ∈ graph.1 ∧
                ∀ other : Model.LCarrier.{u},
                  ZFSet.pair other.1 index.1 ∈ graph.1 →
                    other.1 = value.1 := by
  simp only [IndexedSequenceZF.sequenceValidityFormula,
    FOFormula.Satisfies, FOFormula.satisfies_all]
  constructor
  · rintro ⟨length, graph, hpair, hlength, htotal⟩
    refine ⟨length, graph, ?_, hlength, ?_⟩
    · have hpairRaw :=
        (satisfies_kuratowskiPairEqAt_lCarrier
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (snoc (snoc ![omega, sequence] length) graph)).mp hpair
      change sequence.1 = ZFSet.pair length.1 graph.1 at hpairRaw
      exact hpairRaw
    · intro index hindex
      have hbody := htotal index
      exact
        ((satisfies_totalFunctionalBody_lCarrier
          omega sequence length graph index).mp
            (by
              change FOFormula.Satisfies LMem
                IndexedSequenceZF.totalFunctionalBody
                ![omega, sequence, length, graph, index] at hbody
              exact hbody)) hindex
  · rintro ⟨length, graph, hpair, hlength, htotal⟩
    refine ⟨length, graph, ?_, hlength, ?_⟩
    · apply (satisfies_kuratowskiPairEqAt_lCarrier
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
        (snoc (snoc ![omega, sequence] length) graph)).mpr
      change sequence.1 = ZFSet.pair length.1 graph.1
      exact hpair
    · intro index
      have hbody :=
        (satisfies_totalFunctionalBody_lCarrier
          omega sequence length graph index).mpr (htotal index)
      change FOFormula.Satisfies LMem
        IndexedSequenceZF.totalFunctionalBody
        ![omega, sequence, length, graph, index]
      exact hbody

/-- Every genuine indexed code is valid even with all quantifiers restricted to `L`. -/
theorem satisfies_sequenceValidity_sequenceCode_lCarrier
    (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ L) :
    FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
      ![⟨Ordinal.omega0.toZFSet, omega_mem_L⟩,
        ⟨IndexedSequenceZF.sequenceCode xs,
          IndexedSequenceZF.sequenceCode_mem_L hxs⟩] := by
  rw [satisfies_sequenceValidityFormula_lCarrier]
  let length : Model.LCarrier.{u} :=
    ⟨natCode xs.length, natCode_mem_L xs.length⟩
  let graph : Model.LCarrier.{u} :=
    ⟨IndexedSequenceZF.graph xs,
      IndexedSequenceZF.graphFrom_mem_L hxs 0⟩
  refine ⟨length, graph, rfl, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 xs.length)
  · intro index hindex
    rcases (mem_natCode_iff index.1 xs.length).mp hindex with
      ⟨k, hk, hindexEq⟩
    have hvalueL : xs.get ⟨k, hk⟩ ∈ L :=
      hxs _ (List.get_mem xs ⟨k, hk⟩)
    let value : Model.LCarrier.{u} := ⟨xs.get ⟨k, hk⟩, hvalueL⟩
    refine ⟨value, ?_, ?_⟩
    · apply (IndexedSequenceZF.mem_graph_iff xs _).mpr
      exact ⟨⟨k, hk⟩, by simp only [hindexEq, value]⟩
    · intro other hother
      rcases (IndexedSequenceZF.mem_graph_iff xs _).mp hother with
        ⟨j, hpair⟩
      have hparts := ZFSet.pair_inj.mp hpair
      have hkj : k = j.1 := by
        apply natCode_injective
        exact hindexEq.symm.trans hparts.2
      simpa only [value, hkj] using hparts.1

/-! ## Token comparison over `LCarrier` -/

/-- The seven-coordinate token comparison assignment, with all entries in `L`. -/
def stackTokenLtLAssignment (U relation : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : StackToken (Option (Constructible.ZFCarrier U))) :
    Tuple Model.LCarrier.{u} 7 :=
  ![⟨U, hU⟩, ⟨relation, hrelation⟩,
    ⟨varTag, varTag_mem_L⟩, ⟨appTag, appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩,
    ⟨stackTokenZFCode U left, stackTokenZFCode_mem_L hU left⟩,
    ⟨stackTokenZFCode U right, stackTokenZFCode_mem_L hU right⟩]



@[simp]
theorem satisfies_stackTokenLtFormula_lCarrier_normal
    (s : Tuple Model.LCarrier.{u} 7) :
    FOFormula.Satisfies LMem stackTokenLtFormula s ↔
      ∃ x y : Model.LCarrier.{u},
        ((s 5).1 = triple (s 2).1 x.1 (s 4).1 ∧
          (s 6).1 = triple (s 2).1 y.1 (s 4).1 ∧
          ((x.1 = (s 0).1 ∧ y.1 ∈ (s 0).1) ∨
            (x.1 ∈ (s 0).1 ∧ y.1 ∈ (s 0).1 ∧
              ZFSet.pair x.1 y.1 ∈ (s 1).1))) ∨
        ((s 5).1 = triple (s 2).1 x.1 (s 4).1 ∧
          (s 6).1 = triple (s 3).1 y.1 (s 4).1) ∨
        ((s 5).1 = triple (s 3).1 x.1 (s 4).1 ∧
          (s 6).1 = triple (s 3).1 y.1 (s 4).1 ∧ x.1 ∈ y.1) := by
  simp only [stackTokenLtFormula, FOFormula.Satisfies]
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute]
  simp only [Delta0Formula.satisfies_toFO,
    stackTokenLtBody, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_disj,
    Delta0Formula.satisfies_tripleEqAt, satisfies_pairMemAt,
    Model.subtypeVal_snoc]
  rw [stackTokenLtWitnessAssignment]
  rfl

/-- Exact token-order semantics with the two payload witnesses restricted to `L`. -/
theorem satisfies_stackTokenLtFormula_lCarrier_tokenCodes
    (U relation : ZFSet.{u}) (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : StackToken (Option (Constructible.ZFCarrier U))) :
    FOFormula.Satisfies LMem stackTokenLtFormula
        (stackTokenLtLAssignment U relation hU hrelation left right) ↔
      stackTokenRel (generatorTokenRel U relation) left right := by
  constructor
  · intro h
    rw [satisfies_stackTokenLtFormula_lCarrier_normal] at h
    rcases h with ⟨x, y, hbody⟩
    apply (satisfies_stackTokenLtFormula_tokenCodes U relation left right).mp
    apply (satisfies_stackTokenLtFormula
      (stackTokenLtAssignment U relation
        (stackTokenZFCode U left) (stackTokenZFCode U right))).mpr
    simpa [stackTokenLtLAssignment] using ⟨x.1, y.1, hbody⟩
  · intro h
    rw [satisfies_stackTokenLtFormula_lCarrier_normal]
    cases left with
    | inl leftGenerator =>
        let leftPayload : Model.LCarrier.{u} :=
          ⟨rudimentaryGenerator U leftGenerator,
            rudimentaryGenerator_mem_L hU leftGenerator⟩
        cases right with
        | inl rightGenerator =>
            let rightPayload : Model.LCarrier.{u} :=
              ⟨rudimentaryGenerator U rightGenerator,
                rudimentaryGenerator_mem_L hU rightGenerator⟩
            refine ⟨leftPayload, rightPayload, Or.inl ⟨rfl, rfl, ?_⟩⟩
            exact (generatorPayloadLt_iff U relation
              leftGenerator rightGenerator).mpr (by
                cases h with
                | inl hgenerator => exact hgenerator)
        | inr rightOperation =>
            let rightPayload : Model.LCarrier.{u} :=
              ⟨operationCode rightOperation,
                operationCode_mem_L rightOperation⟩
            exact ⟨leftPayload, rightPayload,
              Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    | inr leftOperation =>
        let leftPayload : Model.LCarrier.{u} :=
          ⟨operationCode leftOperation,
            operationCode_mem_L leftOperation⟩
        cases right with
        | inl rightGenerator =>
            cases h
        | inr rightOperation =>
            let rightPayload : Model.LCarrier.{u} :=
              ⟨operationCode rightOperation,
                operationCode_mem_L rightOperation⟩
            refine ⟨leftPayload, rightPayload,
              Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩
            cases h with
            | inr hoperation =>
                exact (operationCode_mem_operationCode_iff
                  leftOperation rightOperation).mpr hoperation

/-! ## Program comparison over `LCarrier` -/

/--
The structural normal form of indexed-sequence shortlex when every unbounded
quantifier ranges over `LCarrier`.  No absoluteness claim is made about the
supplied token formula.
-/
theorem satisfies_shortlexFormula_lCarrier {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple Model.LCarrier.{u} parameterCount)
    (omega leftSequence rightSequence : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem (IndexedSequenceZF.shortlexFormula tokenLt)
        (snoc (snoc (snoc params omega) leftSequence) rightSequence) ↔
      FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
          ![omega, leftSequence] ∧
        FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
          ![omega, rightSequence] ∧
        ∃ leftLength rightLength : Model.LCarrier.{u},
          FOFormula.Satisfies LMem IndexedSequenceZF.hasLengthFormula
              ![leftSequence, leftLength] ∧
            FOFormula.Satisfies LMem IndexedSequenceZF.hasLengthFormula
              ![rightSequence, rightLength] ∧
            (leftLength.1 ∈ rightLength.1 ∨
              leftLength = rightLength ∧
                ∃ index : Model.LCarrier.{u}, index.1 ∈ leftLength.1 ∧
                  FOFormula.Satisfies LMem IndexedSequenceZF.samePrefixFormula
                      ![leftSequence, rightSequence, index] ∧
                    ∃ leftValue rightValue : Model.LCarrier.{u},
                      FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
                          ![leftSequence, index, leftValue] ∧
                        FOFormula.Satisfies LMem IndexedSequenceZF.valueAtFormula
                          ![rightSequence, index, rightValue] ∧
                        FOFormula.Satisfies LMem tokenLt
                          (snoc (snoc params leftValue) rightValue)) := by
  simp only [IndexedSequenceZF.shortlexFormula,
    IndexedSequenceZF.shortlexCore, FOFormula.Satisfies,
    FOFormula.satisfies_rename, FOFormula.satisfies_disj,
    FOFormula.satisfies_boundedEx,
    IndexedSequenceZF.comp_validityLeftRename,
    IndexedSequenceZF.comp_validityRightRename,
    IndexedSequenceZF.comp_leftLengthRename,
    IndexedSequenceZF.comp_rightLengthRename,
    IndexedSequenceZF.comp_prefixRename,
    IndexedSequenceZF.comp_leftValueRename,
    IndexedSequenceZF.comp_rightValueRename,
    IndexedSequenceZF.comp_tokenLtRename, snoc_last, snoc_castSucc]

/--
The relation on raw constructible codes induced by a formula whose witnesses
and quantifiers are interpreted in `LCarrier`.
-/
def lCarrierFormulaRel {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple Model.LCarrier.{u} parameterCount)
    (leftCode rightCode : ZFSet.{u}) : Prop :=
  ∃ leftValue rightValue : Model.LCarrier.{u},
    leftValue.1 = leftCode ∧ rightValue.1 = rightCode ∧
      FOFormula.Satisfies LMem tokenLt
        (snoc (snoc params leftValue) rightValue)

/--
On canonical indexed codes whose entries lie in `L`, restricted shortlex
satisfaction is exactly shortlex for the relation induced on their entries.
-/
theorem satisfies_shortlexFormula_sequenceCode_lCarrier_iff
    {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple Model.LCarrier.{u} parameterCount)
    (xs ys : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ L) (hys : ∀ y ∈ ys, y ∈ L) :
    FOFormula.Satisfies LMem (IndexedSequenceZF.shortlexFormula tokenLt)
        (snoc (snoc
          (snoc params ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
          ⟨IndexedSequenceZF.sequenceCode xs,
            IndexedSequenceZF.sequenceCode_mem_L hxs⟩)
          ⟨IndexedSequenceZF.sequenceCode ys,
            IndexedSequenceZF.sequenceCode_mem_L hys⟩) ↔
      List.Shortlex (lCarrierFormulaRel tokenLt params) xs ys := by
  rw [satisfies_shortlexFormula_lCarrier]
  have hvalidLeft :
      FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
        ![⟨Ordinal.omega0.toZFSet, omega_mem_L⟩,
          ⟨IndexedSequenceZF.sequenceCode xs,
            IndexedSequenceZF.sequenceCode_mem_L hxs⟩] :=
    satisfies_sequenceValidity_sequenceCode_lCarrier xs hxs
  have hvalidRight :
      FOFormula.Satisfies LMem IndexedSequenceZF.sequenceValidityFormula
        ![⟨Ordinal.omega0.toZFSet, omega_mem_L⟩,
          ⟨IndexedSequenceZF.sequenceCode ys,
            IndexedSequenceZF.sequenceCode_mem_L hys⟩] :=
    satisfies_sequenceValidity_sequenceCode_lCarrier ys hys
  constructor
  · rintro ⟨_hvalidLeft, _hvalidRight, leftLength, rightLength,
      hleftLength, hrightLength, hshort⟩
    have hleftLengthEq :=
      (satisfies_hasLengthFormula_lCarrier_iff xs hxs leftLength).mp
        hleftLength
    have hrightLengthEq :=
      (satisfies_hasLengthFormula_lCarrier_iff ys hys rightLength).mp
        hrightLength
    rcases hshort with hlength | ⟨hlengthCarrier, index, hindex,
        hprefix, leftValue, rightValue, hleftValue, hrightValue, hlt⟩
    · apply List.Shortlex.of_length_lt
      apply (natCode_mem_natCode_iff xs.length ys.length).mp
      simpa only [hleftLengthEq, hrightLengthEq] using hlength
    · have hlengthCode : natCode xs.length = natCode ys.length :=
        hleftLengthEq.symm.trans
          ((congrArg Subtype.val hlengthCarrier).trans hrightLengthEq)
      have hlength : xs.length = ys.length := natCode_injective hlengthCode
      have hindexNat : index.1 ∈ natCode xs.length := by
        simpa only [hleftLengthEq] using hindex
      rcases (mem_natCode_iff index.1 xs.length).mp hindexNat with
        ⟨k, hk, hindexEq⟩
      let indexK : Model.LCarrier.{u} :=
        ⟨natCode k, natCode_mem_L k⟩
      have hindexCarrier : index = indexK := Subtype.ext hindexEq
      have hpoint :=
        (satisfies_samePrefix_sequenceCode_lCarrier_iff
          xs ys hxs hys k).mp
          (by simpa only [hindexCarrier, indexK] using hprefix)
      have hkRightLe : k ≤ ys.length := by
        rw [← hlength]
        exact hk.le
      have htake : xs.take k = ys.take k :=
        (IndexedSequenceZF.take_eq_take_iff_pointwise
          xs ys k hk.le hkRightLe).mpr hpoint
      rcases (satisfies_valueAtFormula_lCarrier_iff
          xs hxs k leftValue).mp
          (by simpa only [hindexCarrier, indexK] using hleftValue) with
        ⟨hkx, hleftValueEq⟩
      rcases (satisfies_valueAtFormula_lCarrier_iff
          ys hys k rightValue).mp
          (by simpa only [hindexCarrier, indexK] using hrightValue) with
        ⟨hky, hrightValueEq⟩
      have hrelation :
          lCarrierFormulaRel tokenLt params
            (xs.get ⟨k, hkx⟩) (ys.get ⟨k, hky⟩) :=
        ⟨leftValue, rightValue, hleftValueEq, hrightValueEq, hlt⟩
      apply List.Shortlex.of_lex hlength
      apply (listLex_iff_exists_index hlength).mpr
      exact ⟨k, hkx, hky, htake, hrelation⟩
  · intro hshortlex
    let leftLength : Model.LCarrier.{u} :=
      ⟨natCode xs.length, natCode_mem_L xs.length⟩
    let rightLength : Model.LCarrier.{u} :=
      ⟨natCode ys.length, natCode_mem_L ys.length⟩
    refine ⟨hvalidLeft, hvalidRight, leftLength, rightLength, ?_, ?_, ?_⟩
    · exact (satisfies_hasLengthFormula_lCarrier_iff
        xs hxs leftLength).mpr (by rfl)
    · exact (satisfies_hasLengthFormula_lCarrier_iff
        ys hys rightLength).mpr (by rfl)
    · rcases List.shortlex_def.mp hshortlex with
        hlength | ⟨hlength, hlex⟩
      · apply Or.inl
        simpa only [leftLength, rightLength] using
          ((natCode_mem_natCode_iff xs.length ys.length).mpr hlength)
      · apply Or.inr
        refine ⟨Subtype.ext (congrArg natCode hlength), ?_⟩
        rcases (listLex_iff_exists_index hlength).mp hlex with
          ⟨k, hkx, hky, htake, hrelation⟩
        rcases hrelation with
          ⟨leftValue, rightValue, hleftValueEq, hrightValueEq, hlt⟩
        let index : Model.LCarrier.{u} :=
          ⟨natCode k, natCode_mem_L k⟩
        refine ⟨index, ?_, ?_, leftValue, rightValue, ?_, ?_, hlt⟩
        · simpa only [index, leftLength] using
            ((natCode_mem_natCode_iff k xs.length).mpr hkx)
        · apply (satisfies_samePrefix_sequenceCode_lCarrier_iff
            xs ys hxs hys k).mpr
          exact (IndexedSequenceZF.take_eq_take_iff_pointwise
            xs ys k hkx.le hky.le).mp htake
        · exact (satisfies_valueAtFormula_lCarrier_iff
            xs hxs k leftValue).mpr ⟨hkx, hleftValueEq⟩
        · exact (satisfies_valueAtFormula_lCarrier_iff
            ys hys k rightValue).mpr ⟨hky, hrightValueEq⟩

/--
The program-order formula has its intended structural semantics when all
quantifiers are restricted to `L` and both programs are genuine codes.
-/
@[simp]
theorem satisfies_stackProgramLtFormula_lCarrier
    (U relation : ZFSet.{u}) (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    FOFormula.Satisfies LMem stackProgramLtFormula
        (stackProgramLtLAssignment U relation hU hrelation left right) ↔
      stackProgramRel (generatorTokenRel U relation) left right := by
  let params : Tuple Model.LCarrier.{u} 5 :=
    ![⟨U, hU⟩, ⟨relation, hrelation⟩,
      ⟨varTag, varTag_mem_L⟩, ⟨appTag, appTag_mem_L⟩,
      ⟨∅, empty_mem_L⟩]
  let xs : List ZFSet.{u} := left.map (stackTokenZFCode U)
  let ys : List ZFSet.{u} := right.map (stackTokenZFCode U)
  have hxs : ∀ code ∈ xs, code ∈ L := by
    simpa only [xs] using stackTokenCodes_mem_L hU left
  have hys : ∀ code ∈ ys, code ∈ L := by
    simpa only [ys] using stackTokenCodes_mem_L hU right
  have hshort :=
    satisfies_shortlexFormula_sequenceCode_lCarrier_iff
      stackTokenLtFormula params xs ys hxs hys
  have htoken : ∀ leftToken rightToken : StackToken
      (Option (Constructible.ZFCarrier U)),
      lCarrierFormulaRel stackTokenLtFormula params
          (stackTokenZFCode U leftToken)
          (stackTokenZFCode U rightToken) ↔
        stackTokenRel (generatorTokenRel U relation)
          leftToken rightToken := by
    intro leftToken rightToken
    constructor
    · rintro ⟨leftValue, rightValue,
        hleftValue, hrightValue, hlt⟩
      let leftCode : Model.LCarrier.{u} :=
        ⟨stackTokenZFCode U leftToken,
          stackTokenZFCode_mem_L hU leftToken⟩
      let rightCode : Model.LCarrier.{u} :=
        ⟨stackTokenZFCode U rightToken,
          stackTokenZFCode_mem_L hU rightToken⟩
      have hleftCarrier : leftValue = leftCode := Subtype.ext hleftValue
      have hrightCarrier : rightValue = rightCode := Subtype.ext hrightValue
      apply (satisfies_stackTokenLtFormula_lCarrier_tokenCodes
        U relation hU hrelation leftToken rightToken).mp
      rw [hleftCarrier, hrightCarrier] at hlt
      change FOFormula.Satisfies LMem stackTokenLtFormula
        (stackTokenLtLAssignment U relation hU hrelation leftToken rightToken) at hlt
      exact hlt
    · intro hlt
      let leftValue : Model.LCarrier.{u} :=
        ⟨stackTokenZFCode U leftToken,
          stackTokenZFCode_mem_L hU leftToken⟩
      let rightValue : Model.LCarrier.{u} :=
        ⟨stackTokenZFCode U rightToken,
          stackTokenZFCode_mem_L hU rightToken⟩
      refine ⟨leftValue, rightValue, rfl, rfl, ?_⟩
      have hrestricted :=
        (satisfies_stackTokenLtFormula_lCarrier_tokenCodes
          U relation hU hrelation leftToken rightToken).mpr hlt
      change FOFormula.Satisfies LMem stackTokenLtFormula
        (snoc (snoc params leftValue) rightValue) at hrestricted
      exact hrestricted
  have hmap :
      List.Shortlex (lCarrierFormulaRel stackTokenLtFormula params) xs ys ↔
        stackProgramRel (generatorTokenRel U relation) left right := by
    simpa only [xs, ys, stackProgramRel] using
      (listShortlex_map_iff (stackTokenZFCode U)
        (stackTokenZFCode_injective U) htoken left right)
  have hformula :
      FOFormula.Satisfies LMem stackProgramLtFormula
          (stackProgramLtLAssignment U relation hU hrelation left right) ↔
        List.Shortlex (lCarrierFormulaRel stackTokenLtFormula params)
          xs ys := by
    change FOFormula.Satisfies LMem stackProgramLtFormula
        (stackProgramLtLAssignment U relation hU hrelation left right) ↔
      List.Shortlex (lCarrierFormulaRel stackTokenLtFormula params) xs ys at hshort
    exact hshort
  exact hformula.trans hmap

/-- Raw-assignment presentation of restricted satisfaction in `L`. -/
@[simp]
theorem satisfiesIn_L_stackProgramLtFormula
    (U relation : ZFSet.{u}) (hU : U ∈ L) (hrelation : relation ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U)))) :
    Model.SatisfiesIn L stackProgramLtFormula
        (stackProgramLtAssignment U relation left right) ↔
      stackProgramRel (generatorTokenRel U relation) left right := by
  rw [← stackProgramLtLAssignment_val U relation hU hrelation left right]
  rw [← Model.satisfies_lCarrier_iff_satisfiesIn_L
    stackProgramLtFormula
    (stackProgramLtLAssignment U relation hU hrelation left right)]
  exact satisfies_stackProgramLtFormula_lCarrier
    U relation hU hrelation left right

end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule60



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackStepAbsolute -/
section CUAdapterModule61
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Absoluteness of one rudimentary stack-machine step

The ambient correctness theorem for `stackStepFormula` quantifies over all
`ZFSet`s.  This file packages its fixed assignment in `LCarrier` and proves
the corresponding correctness theorem when all stack entries are
constructible. The results are stated using both subtype semantics and the
raw-domain semantics `Model.SatisfiesIn L`.
-/


open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

/-- The intended stack-step assignment, with every coordinate in `L`. -/
def stackStepLAssignment (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    Tuple Model.LCarrier.{u} 16 :=
  ![⟨U, hU⟩,
    ⟨varTag, varTag_mem_L⟩,
    ⟨appTag, appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩,
    ⟨operationCode 0, operationCode_mem_L 0⟩,
    ⟨operationCode 1, operationCode_mem_L 1⟩,
    ⟨operationCode 2, operationCode_mem_L 2⟩,
    ⟨operationCode 3, operationCode_mem_L 3⟩,
    ⟨operationCode 4, operationCode_mem_L 4⟩,
    ⟨operationCode 5, operationCode_mem_L 5⟩,
    ⟨operationCode 6, operationCode_mem_L 6⟩,
    ⟨operationCode 7, operationCode_mem_L 7⟩,
    ⟨operationCode 8, operationCode_mem_L 8⟩,
    ⟨stackTokenZFCode U token, stackTokenZFCode_mem_L hU token⟩,
    ⟨FiniteSequenceZF.listCode input,
      FiniteSequenceZF.listCode_mem_L hinput⟩,
    ⟨FiniteSequenceZF.listCode output,
      FiniteSequenceZF.listCode_mem_L houtput⟩]

theorem stackStepLAssignment_val (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    (fun i =>
      (stackStepLAssignment U hU token input output hinput houtput i).1) =
      stackStepAssignment U (stackTokenZFCode U token)
        (FiniteSequenceZF.listCode input)
        (FiniteSequenceZF.listCode output) := by
  funext i
  fin_cases i <;> rfl

/-- Semantic normal form of the variable branch over `LCarrier`. -/
@[simp]
theorem satisfies_variableStackStepFormula_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        variableStackStepFormula
        (stackStepLAssignment U hU token input output hinput houtput) ↔
      ∃ generator : Model.LCarrier.{u},
        stackTokenZFCode U token = triple varTag generator.1 ∅ ∧
          (generator.1 = U ∨ generator.1 ∈ U) ∧
          FiniteSequenceZF.listCode output =
            ZFSet.pair generator.1 (FiniteSequenceZF.listCode input) := by
  simp only [variableStackStepFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_lCarrier_absolute,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_disj, snoc_last, snoc_castSucc,
    Model.subtypeVal_snoc, stackStepLAssignment_val,
    stackStepAssignment, stackStepLiftOne,
    stackStepTokenIndex, stackStepVarTagIndex,
    stackStepEmptyIndex, stackStepUniverseIndex,
    stackStepOutputIndex, stackStepInputIndex,
    Subtype.ext_iff]
  rfl

theorem comp_stackStepOpGraphRename_lCarrier
    (s : Tuple Model.LCarrier.{u} 16)
    (right left rest result inner : Model.LCarrier.{u}) :
    (fun i =>
      (snoc (snoc (snoc (snoc (snoc s right) left) rest)
        result) inner (stackStepOpGraphRename i)).1) =
      ![result.1, left.1, right.1] := by
  funext i
  fin_cases i <;> rfl

/-- Semantic normal form of one operation branch over `LCarrier`. -/
@[simp]
theorem satisfies_operationStackStepFormula_lCarrier (i : Fin 9)
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        (operationStackStepFormula i)
        (stackStepLAssignment U hU token input output hinput houtput) ↔
      ∃ right left rest result : Model.LCarrier.{u},
        stackTokenZFCode U token =
            triple appTag (operationCode i) ∅ ∧
          FiniteSequenceZF.listCode input =
            ZFSet.pair right.1 (ZFSet.pair left.1 rest.1) ∧
          FiniteSequenceZF.listCode output =
            ZFSet.pair result.1 rest.1 ∧
          result.1 = op i left.1 right.1 := by
  simp only [operationStackStepFormula, operationStackStepBody,
    FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_lCarrier_absolute,
    Delta0Formula.satisfies_tripleEqAt,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    FOFormula.satisfies_rename,
    snoc_castSucc, Model.subtypeVal_snoc,
    stackStepLAssignment_val,
    stackStepLiftFive,
    stackStepAssignment_operation,
    stackStepAssignment_appTag, stackStepAssignment_empty,
    stackStepAssignment_token, stackStepAssignment_input,
    stackStepAssignment_output,
    stackStepWitness_right, stackStepWitness_left,
    stackStepWitness_rest, stackStepWitness_result,
    stackStepWitness_inner]
  constructor
  · rintro ⟨right, left, rest, result, inner,
      htoken, hinputCode, hinner, houtputCode, hop⟩
    have hop' : result.1 = op i left.1 right.1 := by
      have hopRaw :
          Delta0Formula.Satisfies Delta0Formula.ZFMem (opGraphFormula i)
            ![result.1, left.1, right.1] := by
        simpa only [comp_stackStepOpGraphRename_lCarrier] using hop
      exact
        (satisfies_opGraphFormula i result.1 left.1 right.1).mp hopRaw
    exact ⟨right, left, rest, result, htoken,
      hinputCode.trans (congrArg (ZFSet.pair right.1) hinner),
      houtputCode, hop'⟩
  · rintro ⟨right, left, rest, result,
      htoken, hinputCode, houtputCode, hop⟩
    have hop' :
        Delta0Formula.Satisfies Delta0Formula.ZFMem (opGraphFormula i)
          ![result.1, left.1, right.1] :=
      (satisfies_opGraphFormula i result.1 left.1 right.1).mpr hop
    let inner : Model.LCarrier.{u} :=
      ⟨ZFSet.pair left.1 rest.1, orderedPair_mem_L left.2 rest.2⟩
    refine ⟨right, left, rest, result, inner,
      htoken, hinputCode, rfl, houtputCode, ?_⟩
    simpa only [comp_stackStepOpGraphRename_lCarrier] using hop'

/-- Semantic normal form of the finite operation disjunction over `LCarrier`. -/
@[simp]
theorem satisfies_anyOperationStackStepFormula_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        anyOperationStackStepFormula
        (stackStepLAssignment U hU token input output hinput houtput) ↔
      ∃ i : Fin 9, ∃ right left rest result : Model.LCarrier.{u},
        stackTokenZFCode U token =
            triple appTag (operationCode i) ∅ ∧
          FiniteSequenceZF.listCode input =
            ZFSet.pair right.1 (ZFSet.pair left.1 rest.1) ∧
          FiniteSequenceZF.listCode output =
            ZFSet.pair result.1 rest.1 ∧
          result.1 = op i left.1 right.1 := by
  simp only [anyOperationStackStepFormula, FOFormula.satisfies_disj,
    satisfies_operationStackStepFormula_lCarrier]
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
    · exact ⟨6, h⟩
    · exact ⟨7, h⟩
    · exact ⟨8, h⟩
  · rintro ⟨i, h⟩
    fin_cases i
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr h)))))))

/-- Raw semantic normal form of the complete transition formula over `L`. -/
@[simp]
theorem satisfies_stackStepFormula_lCarrier
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        stackStepFormula
        (stackStepLAssignment U hU token input output hinput houtput) ↔
      (∃ generator : Model.LCarrier.{u},
        stackTokenZFCode U token = triple varTag generator.1 ∅ ∧
          (generator.1 = U ∨ generator.1 ∈ U) ∧
          FiniteSequenceZF.listCode output =
            ZFSet.pair generator.1 (FiniteSequenceZF.listCode input)) ∨
      (∃ i : Fin 9, ∃ right left rest result : Model.LCarrier.{u},
        stackTokenZFCode U token =
            triple appTag (operationCode i) ∅ ∧
          FiniteSequenceZF.listCode input =
            ZFSet.pair right.1 (ZFSet.pair left.1 rest.1) ∧
          FiniteSequenceZF.listCode output =
            ZFSet.pair result.1 rest.1 ∧
          result.1 = op i left.1 right.1) := by
  simp only [stackStepFormula, FOFormula.satisfies_disj,
    satisfies_variableStackStepFormula_lCarrier,
    satisfies_anyOperationStackStepFormula_lCarrier]

/-- On constructible stack codes, satisfaction in `LCarrier` is one step. -/
theorem satisfies_stackStepFormula_lCarrier_iff_run
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        stackStepFormula
        (stackStepLAssignment U hU token input output hinput houtput) ↔
      runStackToken (rudimentaryGenerator U) token input = some output := by
  constructor
  · intro hstep
    apply (satisfies_stackStepFormula_iff_run U token input output).mp
    apply (satisfies_stackStepFormula U
      (stackTokenZFCode U token)
      (FiniteSequenceZF.listCode input)
      (FiniteSequenceZF.listCode output)).mpr
    rw [satisfies_stackStepFormula_lCarrier] at hstep
    rcases hstep with hvar | hop
    · rcases hvar with ⟨generator, htoken, hgenerator, houtputCode⟩
      exact Or.inl
        ⟨generator.1, htoken, hgenerator, houtputCode⟩
    · rcases hop with
        ⟨i, right, left, rest, result, htoken,
          hinputCode, houtputCode, hop⟩
      exact Or.inr
        ⟨i, right.1, left.1, rest.1, result.1,
          htoken, hinputCode, houtputCode, hop⟩
  · intro hrun
    rw [satisfies_stackStepFormula_lCarrier]
    cases token with
    | inl generator =>
        cases generator with
        | none =>
            have houtputEq : output = U :: input := by
              exact (Option.some.inj hrun).symm
            refine Or.inl ⟨⟨U, hU⟩, rfl, Or.inl rfl, ?_⟩
            simp only [houtputEq, FiniteSequenceZF.listCode_cons]
        | some generator =>
            have hgeneratorL : generator.1 ∈ L :=
              mem_L_of_mem generator.2 hU
            have houtputEq : output = generator.1 :: input := by
              exact (Option.some.inj hrun).symm
            refine Or.inl
              ⟨⟨generator.1, hgeneratorL⟩, rfl,
                Or.inr generator.2, ?_⟩
            simp only [houtputEq, FiniteSequenceZF.listCode_cons]
    | inr operation =>
        cases input with
        | nil =>
            cases hrun
        | cons right tail =>
            cases tail with
            | nil =>
                cases hrun
            | cons left rest =>
                have hrightL : right ∈ L :=
                  hinput right (by simp)
                have hleftL : left ∈ L :=
                  hinput left (by simp)
                have hrestEntries : ∀ x ∈ rest, x ∈ L := by
                  intro x hx
                  exact hinput x (by simp [hx])
                have hrestL : FiniteSequenceZF.listCode rest ∈ L :=
                  FiniteSequenceZF.listCode_mem_L hrestEntries
                have hresultL : op operation left right ∈ L :=
                  op_mem_L hleftL hrightL
                have houtputEq :
                    output = op operation left right :: rest := by
                  exact (Option.some.inj hrun).symm
                refine Or.inr
                  ⟨operation,
                    ⟨right, hrightL⟩,
                    ⟨left, hleftL⟩,
                    ⟨FiniteSequenceZF.listCode rest, hrestL⟩,
                    ⟨op operation left right, hresultL⟩,
                    rfl, rfl, ?_, rfl⟩
                simp only [houtputEq,
                  FiniteSequenceZF.listCode_cons]

/--
On genuine token and list codes, satisfaction with every quantifier restricted
to `L` is exactly one stack-machine transition.
-/
@[simp]
theorem satisfiesIn_L_stackStepFormula_iff_run
    (U : ZFSet.{u}) (hU : U ∈ L)
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (input output : List ZFSet.{u})
    (hinput : ∀ x ∈ input, x ∈ L)
    (houtput : ∀ x ∈ output, x ∈ L) :
    Model.SatisfiesIn L stackStepFormula
        (stackStepAssignment U (stackTokenZFCode U token)
          (FiniteSequenceZF.listCode input)
          (FiniteSequenceZF.listCode output)) ↔
      runStackToken (rudimentaryGenerator U) token input = some output := by
  have hbridge :=
    Model.satisfies_lCarrier_iff_satisfiesIn_L stackStepFormula
      (stackStepLAssignment U hU token input output hinput houtput)
  have hbridgeRaw :
      FOFormula.Satisfies
          (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
          stackStepFormula
          (stackStepLAssignment U hU token input output hinput houtput) ↔
        Model.SatisfiesIn L stackStepFormula
          (stackStepAssignment U (stackTokenZFCode U token)
            (FiniteSequenceZF.listCode input)
            (FiniteSequenceZF.listCode output)) := by
    simpa only [stackStepLAssignment_val] using hbridge
  exact hbridgeRaw.symm.trans
    (satisfies_stackStepFormula_lCarrier_iff_run
      U hU token input output hinput houtput)

end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule61


