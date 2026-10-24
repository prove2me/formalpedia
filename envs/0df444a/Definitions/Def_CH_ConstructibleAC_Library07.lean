-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library07
-- name    : CH_ConstructibleAC_Library07
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:14:07.899351+00:00
-- url     : https://prove2.me/theorems/46ad41f6-ef3d-4d13-b940-b2d2b968b216
-- title:
--   Constructible-model structure and internal orders
-- statement:
--   The external constructible carrier is equipped with its membership-model structure. This library supplies the model and axiom interfaces needed by subsequent internal constructions, including the constructor proofs required for that structure. It also defines internal well-order relation graphs: the relation itself is a set in the constructible universe, so Separation can later form a choice set from its least elements.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackTraceDecode.lean#L1-L295; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/ModelTheory/SetTheory/ZF.lean#L1-L331; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/ModelTheory/SetTheory/ZFC.lean#L1-L100; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/BasicAxioms.lean#L1-L95; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Infinity.lean#L1-L65; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/PowerSet.lean#L1-L118; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Reflection.lean#L1-L383; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Separation.lean#L1-L181; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Collection.lean#L1-L128; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Replacement.lean#L1-L293; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/ZFModel.lean#L1-L91; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Choice.lean#L1-L146; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalWellOrder.lean#L1-L299

import Definitions.Def_CH_ConstructibleAC_Library06
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


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackTraceDecode -/
section CUAdapterModule37
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Decoding raw formula-certified stack traces

Starting from a genuine input stack code, the one-step decoding theorem can
be iterated along raw token and state-code lists.  This reconstructs an actual
typed stack program and an `ExecutionTrace`.  Conversely, encoding any real
execution trace makes every adjacent triple satisfy `stackStepFormula`.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

open FiniteSequenceZF

noncomputable section

/-- Raw token codes of a typed stack program. -/
def encodedStackProgram (U : ZFSet.{u})
    (program : List (StackToken (Option (Constructible.ZFCarrier U)))) :
    List ZFSet.{u} :=
  program.map (stackTokenZFCode U)

/-- Raw structural list codes of a list of stack states. -/
def encodedStackStates (states : List (List ZFSet.{u})) : List ZFSet.{u} :=
  states.map listCode

/--
The local formula-chain condition on raw token and state-code lists.  The
state list has one more entry, and token `k` relates states `k` and `k + 1`.
-/
def RawStackFormulaChain (U : ZFSet.{u})
    (rawTokens rawStates : List ZFSet.{u}) : Prop :=
  ∃ hlength : rawStates.length = rawTokens.length + 1,
    ∀ k : Fin rawTokens.length,
      FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U
          (rawTokens.get k)
          (rawStates.get ⟨k.1, by omega⟩)
          (rawStates.get ⟨k.1 + 1, by omega⟩))

/--
Strong decoding theorem with an arbitrary already-decoded initial stack.
The returned state tail is chosen so that the decoded trace starts exactly at
`input`.
-/
theorem exists_executionTrace_decoding_of_formula_chain
    (U : ZFSet.{u}) (input : List ZFSet.{u})
    (rawTokens rawStates : List ZFSet.{u})
    (hlength : rawStates.length = rawTokens.length + 1)
    (hhead : rawStates.head? = some (listCode input))
    (hsteps : ∀ k : Fin rawTokens.length,
      FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U
          (rawTokens.get k)
          (rawStates.get ⟨k.1, by omega⟩)
          (rawStates.get ⟨k.1 + 1, by omega⟩))) :
    ∃ program : List
        (StackToken (Option (Constructible.ZFCarrier U))),
      ∃ stateTail : List (List ZFSet.{u}),
        rawTokens = encodedStackProgram U program ∧
          rawStates = encodedStackStates (input :: stateTail) ∧
          ExecutionTrace (rudimentaryGenerator U)
            program (input :: stateTail) := by
  induction rawTokens generalizing input rawStates with
  | nil =>
      cases rawStates with
      | nil =>
          simp only [List.length_nil] at hlength
          omega
      | cons first tail =>
          cases tail with
          | nil =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              subst first
              exact ⟨[], [], rfl, rfl, .nil input⟩
          | cons second rest =>
              simp only [List.length_cons, List.length_nil] at hlength
              omega
  | cons tokenCode rawTokens ih =>
      cases rawStates with
      | nil =>
          simp only [List.length_nil, List.length_cons] at hlength
          omega
      | cons inputCode tail =>
          cases tail with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlength
              omega
          | cons nextCode rest =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              subst inputCode
              have hfirst :=
                hsteps (0 : Fin (tokenCode :: rawTokens).length)
              have hfirstDecoded :
                  FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
                    (stackStepAssignment U tokenCode
                      (listCode input) nextCode) := by
                simpa using hfirst
              rcases exists_decoding_of_satisfies_stackStepFormula
                  U tokenCode nextCode input hfirstDecoded with
                ⟨token, next, htokenCode, hnextCode, hrun⟩
              have htailLength :
                  (nextCode :: rest).length = rawTokens.length + 1 := by
                simp only [List.length_cons] at hlength ⊢
                omega
              have htailHead :
                  (nextCode :: rest).head? = some (listCode next) := by
                simp only [List.head?_cons, Option.some.injEq]
                exact hnextCode
              have htailSteps : ∀ k : Fin rawTokens.length,
                  FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
                    (stackStepAssignment U
                      (rawTokens.get k)
                      ((nextCode :: rest).get ⟨k.1, by omega⟩)
                      ((nextCode :: rest).get
                        ⟨k.1 + 1, by omega⟩)) := by
                intro k
                have hk := hsteps k.succ
                simpa using hk
              rcases ih next (nextCode :: rest) htailLength
                  htailHead htailSteps with
                ⟨program, stateTail, hprogram, hstates, htrace⟩
              refine ⟨token :: program, next :: stateTail, ?_, ?_, ?_⟩
              · simp only [encodedStackProgram, List.map_cons] at hprogram ⊢
                rw [htokenCode, hprogram]
              · calc
                  listCode input :: nextCode :: rest =
                      listCode input :: encodedStackStates
                        (next :: stateTail) := by rw [hstates]
                  _ = encodedStackStates (input :: next :: stateTail) := rfl
              · exact .cons hrun htrace

/--
Decode a raw formula-certified chain whose first state is the empty stack.
-/
theorem exists_executionTrace_decoding_of_empty_formula_chain
    (U : ZFSet.{u}) (rawTokens rawStates : List ZFSet.{u})
    (hlength : rawStates.length = rawTokens.length + 1)
    (hhead : rawStates.head? = some (listCode []))
    (hsteps : ∀ k : Fin rawTokens.length,
      FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
        (stackStepAssignment U
          (rawTokens.get k)
          (rawStates.get ⟨k.1, by omega⟩)
          (rawStates.get ⟨k.1 + 1, by omega⟩))) :
    ∃ program : List
        (StackToken (Option (Constructible.ZFCarrier U))),
      ∃ states : List (List ZFSet.{u}),
        rawTokens = program.map (stackTokenZFCode U) ∧
          rawStates = states.map listCode ∧
          ExecutionTrace (rudimentaryGenerator U) program states := by
  rcases exists_executionTrace_decoding_of_formula_chain
      U [] rawTokens rawStates hlength hhead hsteps with
    ⟨program, stateTail, hprogram, hstates, htrace⟩
  exact ⟨program, [] :: stateTail,
    by simpa only [encodedStackProgram] using hprogram,
    by simpa only [encodedStackStates] using hstates,
    htrace⟩

/-- Predicate-packaged form of empty-stack raw trace decoding. -/
theorem exists_executionTrace_decoding_of_rawStackFormulaChain
    (U : ZFSet.{u}) (rawTokens rawStates : List ZFSet.{u})
    (hhead : rawStates.head? = some (listCode []))
    (hchain : RawStackFormulaChain U rawTokens rawStates) :
    ∃ program : List
        (StackToken (Option (Constructible.ZFCarrier U))),
      ∃ states : List (List ZFSet.{u}),
        rawTokens = program.map (stackTokenZFCode U) ∧
          rawStates = states.map listCode ∧
          ExecutionTrace (rudimentaryGenerator U) program states := by
  rcases hchain with ⟨hlength, hsteps⟩
  exact exists_executionTrace_decoding_of_empty_formula_chain
    U rawTokens rawStates hlength hhead hsteps

/-- Every indexed step of a genuine trace satisfies `stackStepFormula`. -/
theorem ExecutionTrace.satisfies_stackStepFormula_at
    {U : ZFSet.{u}}
    {program : List
      (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states)
    (k : Fin program.length) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
      (stackStepAssignment U
        (stackTokenZFCode U (program.get k))
        (listCode (states.get ⟨k.1, by
          have hlength := htrace.length
          omega⟩))
        (listCode (states.get ⟨k.1 + 1, by
          have hlength := htrace.length
          omega⟩))) := by
  rcases htrace.indexed with ⟨_hlength, hsteps⟩
  apply (satisfies_stackStepFormula_iff_run U
    (program.get k)
    (states.get ⟨k.1, by
      have hlength := htrace.length
      omega⟩)
    (states.get ⟨k.1 + 1, by
      have hlength := htrace.length
      omega⟩)).mpr
  simpa using hsteps k

/-- Encoding a genuine execution trace produces a raw formula chain. -/
theorem ExecutionTrace.encoded_rawStackFormulaChain
    {U : ZFSet.{u}}
    {program : List
      (StackToken (Option (Constructible.ZFCarrier U)))}
    {states : List (List ZFSet.{u})}
    (htrace : ExecutionTrace (rudimentaryGenerator U) program states) :
    RawStackFormulaChain U
      (encodedStackProgram U program) (encodedStackStates states) := by
  refine ⟨?_, ?_⟩
  · simp only [encodedStackProgram, encodedStackStates,
      List.length_map, htrace.length]
  · intro rawIndex
    let k : Fin program.length :=
      ⟨rawIndex.1, by
        simpa only [encodedStackProgram, List.length_map]
          using rawIndex.2⟩
    have hstep := htrace.satisfies_stackStepFormula_at k
    have hinputBound : k.1 < states.length := by
      have hlength := htrace.length
      omega
    have houtputBound : k.1 + 1 < states.length := by
      have hlength := htrace.length
      omega
    have htoken :
        (encodedStackProgram U program).get rawIndex =
          stackTokenZFCode U (program.get k) := by
      change (program.map (stackTokenZFCode U))[rawIndex.1] =
        stackTokenZFCode U program[k.1]
      rw [List.getElem_map]
    have hinput :
        (encodedStackStates states).get ⟨rawIndex.1, by
          simp only [encodedStackStates, List.length_map]
          have hlength := htrace.length
          have hindex := rawIndex.2
          simp only [encodedStackProgram, List.length_map] at hindex
          omega⟩ =
          listCode (states.get ⟨k.1, by
            have hlength := htrace.length
            omega⟩) := by
      change (states.map listCode)[rawIndex.1]'(by
          simpa only [List.length_map, k] using hinputBound) =
        listCode (states[k.1]'hinputBound)
      rw [List.getElem_map]
    have houtput :
        (encodedStackStates states).get ⟨rawIndex.1 + 1, by
          simp only [encodedStackStates, List.length_map]
          have hlength := htrace.length
          have hindex := rawIndex.2
          simp only [encodedStackProgram, List.length_map] at hindex
          omega⟩ =
          listCode (states.get ⟨k.1 + 1, by
            have hlength := htrace.length
            omega⟩) := by
      change (states.map listCode)[rawIndex.1 + 1]'(by
          simpa only [List.length_map, k] using houtputBound) =
        listCode (states[k.1 + 1]'houtputBound)
      rw [List.getElem_map]
    rw [htoken, hinput, houtput]
    exact hstep



end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule37



/- Original module: ConstructibleUniverse.ModelTheory.SetTheory.ZF -/
section CUAdapterModule38
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/


/-!
# The First-Order Theory ZF

This file defines the Zermelo--Fraenkel axioms in the first-order language of set theory.
The Separation and Replacement schemes range over all formulas in that language, with finitely
many free variables.

## Main definitions

- `FirstOrder.SetTheory.ZFAxiom` indexes the finite axioms and the two axiom schemes.
- `FirstOrder.SetTheory.ZFAxiom.toSentence` is the sentence associated with a ZF axiom.
- `FirstOrder.SetTheory.ZFAxiom.toProp` gives the usual semantics of each axiom.
- `FirstOrder.Language.Theory.ZF` is the first-order theory of ZF.
-/


universe u

namespace FirstOrder.SetTheory

open Language Language.BoundedFormula Language.Structure
open scoped FirstOrder



/-! The following relabellings make the de Bruijn variable order in the two schemes explicit. -/













































end FirstOrder.SetTheory
end CUAdapterModule38



/- Original module: ConstructibleUniverse.ModelTheory.SetTheory.ZFC -/
section CUAdapterModule39
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/


/-!
# The First-Order Theory ZFC

This file extends the first-order theory `Language.Theory.ZF` by the Axiom of Choice. We use the
standard disjoint-family formulation: every pairwise disjoint family of nonempty sets has a set
meeting each member of the family in exactly one element.

## Main definitions

- `FirstOrder.SetTheory.choiceSentence` is the Axiom of Choice in the language of set theory.
- `FirstOrder.SetTheory.ModelsChoice` is its usual disjoint-family semantics.
- `FirstOrder.Language.Theory.ZFC` is ZF together with `choiceSentence`.
- `FirstOrder.Language.Theory.model_ZFC_iff` characterizes models of ZFC.
-/


universe u

namespace FirstOrder.SetTheory

open Language Language.BoundedFormula Language.Structure
open scoped FirstOrder

/-- Every member of `a` is nonempty in the membership structure on `M`. -/
def IsNonemptyFamily (M : Type u) [Language.setTheory.Structure M] (a : M) : Prop :=
  ∀ x : M, RelMap memRel ![x, a] → ∃ y : M, RelMap memRel ![y, x]

/-- Distinct members of `a` are disjoint in the membership structure on `M`. -/
def IsPairwiseDisjointFamily (M : Type u) [Language.setTheory.Structure M] (a : M) : Prop :=
  ∀ x : M, RelMap memRel ![x, a] →
    ∀ y : M, RelMap memRel ![y, a] → x ≠ y →
      ∀ z : M, RelMap memRel ![z, x] → ¬RelMap memRel ![z, y]

/-- `c` meets every member of `a` in exactly one element. -/
def IsChoiceSet (M : Type u) [Language.setTheory.Structure M] (a c : M) : Prop :=
  ∀ x : M, RelMap memRel ![x, a] →
    ∃ y : M, RelMap memRel ![y, x] ∧ RelMap memRel ![y, c] ∧
      ∀ z : M, RelMap memRel ![z, x] → RelMap memRel ![z, c] → z = y

/-- The disjoint-family semantic form of the Axiom of Choice. -/
def ModelsChoice (M : Type u) [Language.setTheory.Structure M] : Prop :=
  ∀ a : M, IsNonemptyFamily M a → IsPairwiseDisjointFamily M a →
    ∃ c : M, IsChoiceSet M a c











end FirstOrder.SetTheory
end CUAdapterModule39



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.BasicAxioms -/
section CUAdapterModule40
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The elementary set axioms in the constructible universe

This file records the axioms which follow immediately from transitivity and
the basic closure properties of `L`.  They are stated on `Model.LCarrier`, so
they connect directly to the sentences in the membership language.
-/


open Set

universe u

namespace Constructible.Model

/-- Extensionality for the membership structure induced on `L`. -/
theorem lCarrier_extensionality {x y : LCarrier.{u}}
    (h : ∀ z : LCarrier.{u}, z.1 ∈ x.1 ↔ z.1 ∈ y.1) :
    x = y := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hzx
    exact (h ⟨z, mem_L_of_mem hzx x.2⟩).mp hzx
  · intro hzy
    exact (h ⟨z, mem_L_of_mem hzy y.2⟩).mpr hzy

/-- The empty-set witness in `L`. -/
def emptyLCarrier : LCarrier.{u} :=
  ⟨∅, empty_mem_L⟩

@[simp]
theorem not_mem_emptyLCarrier (x : LCarrier.{u}) :
    x.1 ∉ emptyLCarrier.1 :=
  ZFSet.notMem_empty x.1

/-- The unordered-pair witness in `L`. -/
def pairLCarrier (x y : LCarrier.{u}) : LCarrier.{u} :=
  ⟨({x.1, y.1} : ZFSet.{u}), pair_mem_L x.2 y.2⟩

@[simp]
theorem mem_pairLCarrier_iff (x y z : LCarrier.{u}) :
    z.1 ∈ (pairLCarrier x y).1 ↔ z = x ∨ z = y := by
  rw [pairLCarrier, ZFSet.mem_pair]
  simp only [Subtype.ext_iff]

/-- The union-set witness in `L`. -/
def sUnionLCarrier (x : LCarrier.{u}) : LCarrier.{u} :=
  ⟨ZFSet.sUnion x.1, sUnion_mem_L x.2⟩

@[simp]
theorem mem_sUnionLCarrier_iff (x z : LCarrier.{u}) :
    z.1 ∈ (sUnionLCarrier x).1 ↔
      ∃ y : LCarrier.{u}, y.1 ∈ x.1 ∧ z.1 ∈ y.1 := by
  rw [sUnionLCarrier, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hyx, hzy⟩
    exact ⟨⟨y, mem_L_of_mem hyx x.2⟩, hyx, hzy⟩
  · rintro ⟨y, hyx, hzy⟩
    exact ⟨y.1, hyx, hzy⟩



end Constructible.Model
end CUAdapterModule40



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Infinity -/
section CUAdapterModule41
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Infinity in the constructible universe

The standard von Neumann code `omega0.toZFSet` is constructible.  Its ordinal
membership characterization immediately gives the empty element and closure
under von Neumann successor.
-/


universe u

namespace Constructible.Model









end Constructible.Model
end CUAdapterModule41



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.PowerSet -/
section CUAdapterModule42
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The internal powerset axiom for the constructible universe

The ambient powerset of a constructible set need not itself be constructible.
The powerset computed by `L` contains exactly those ambient subsets which are
constructible.  We first bound all such subsets in one level and then define
the required collection over that level.

This is the standard inner-model proof using the ambient set
`P(a) intersect L`.  Here that ambient set is constructed by Mathlib's
predicate-valued `ZFSet.sep`.  The resulting membership theorem is exact, but
this operation should not be confused with an already formalized invocation
of an object-language formula defining `L` in an arbitrary ZFC model.
-/


open Set

universe u

namespace Constructible

section ZFC

/-- The ambient set collecting the constructible subsets of `a`. -/
def constructibleSubsetsZF (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => x ∈ L) a.powerset

@[simp]
theorem mem_constructibleSubsetsZF_iff {a x : ZFSet.{u}} :
    x ∈ constructibleSubsetsZF a ↔ x ∈ L ∧ x ⊆ a := by
  simp [constructibleSubsetsZF, and_comm]







end ZFC

end Constructible
end CUAdapterModule42



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Reflection -/
section CUAdapterModule43
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Formula reflection for the constructible hierarchy

For a fixed first-order formula and a starting level, this file constructs an
omega-chain of levels.  At every successor step, witnesses for all existential
subformulas with parameters in the current level are added.  The union level
is then closed under the relevant witnesses, so the Tarski--Vaught induction
shows that the formula has the same truth value there as in the full class
`L`.

The witness selector below lives in Lean's ambient classical metatheory.  It
is used only to obtain ordinal bounds in this semantic proof and is not an
internally represented choice function of `L`.  Consequently this file
implements the standard reflection argument for the concrete `ZFSet`
universe; it is not by itself a syntactic reflection proof over an arbitrary
model of ZF.
-/


open Set

universe u

namespace Constructible

section ZFC

open Model

/-- Forget the membership proofs in a tuple over an internal stage. -/
def stageTupleVal {alpha : Ordinal.{u}} {n : Nat}
    (s : Tuple (ZFCarrier (LStageZF alpha)) n) : Tuple ZFSet.{u} n :=
  fun i => (s i).1

@[simp]
theorem stageTupleVal_apply {alpha : Ordinal.{u}} {n : Nat}
    (s : Tuple (ZFCarrier (LStageZF alpha)) n) (i : Fin n) :
    stageTupleVal s i = (s i).1 :=
  rfl

/--
`ClosesFrom phi alpha beta` says that `beta` contains witnesses for every
existential subformula of `phi` whose free assignment lies in level `alpha`.
The recursive clauses ensure that the same holds for every subformula.
-/
def ClosesFrom : {n : Nat} -> FOFormula n ->
    Ordinal.{u} -> Ordinal.{u} -> Prop
  | _, .mem _ _, _, _ => True
  | _, .eq _ _, _, _ => True
  | _, .neg phi, alpha, beta => ClosesFrom phi alpha beta
  | _, .conj phi psi, alpha, beta =>
      ClosesFrom phi alpha beta /\ ClosesFrom psi alpha beta
  | n, .ex phi, alpha, beta =>
      ClosesFrom phi alpha beta /\
        forall s : Tuple ZFSet.{u} n,
          (forall i, s i ∈ LStageZF alpha) ->
          Model.SatisfiesIn L (.ex phi) s ->
          exists x : ZFSet.{u},
            x ∈ LStageZF beta /\ Model.SatisfiesIn L phi (snoc s x)

/-- Enlarging the target level preserves witness closure. -/
theorem ClosesFrom.mono_right {n : Nat} {phi : FOFormula n}
    {alpha beta gamma : Ordinal.{u}} (hbeta : beta <= gamma)
    (h : ClosesFrom phi alpha beta) : ClosesFrom phi alpha gamma := by
  induction phi with
  | mem i j => trivial
  | eq i j => trivial
  | neg phi ih => exact ih h
  | conj phi psi ihPhi ihPsi =>
      exact ⟨ihPhi h.1, ihPsi h.2⟩
  | ex phi ih =>
      refine ⟨ih h.1, ?_⟩
      intro s hs hsat
      rcases h.2 s hs hsat with ⟨x, hx, hphi⟩
      exact ⟨x, LStageZF_mono hbeta hx, hphi⟩

/-- A total metatheoretically chosen witness, using the empty set when the
existential is false.  This definition is not an internal choice function. -/
noncomputable def chosenWitness {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) : ZFSet.{u} := by
  classical
  exact if h : Model.SatisfiesIn L (.ex phi) s then Classical.choose h else ∅

theorem chosenWitness_mem_L {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) (h : Model.SatisfiesIn L (.ex phi) s) :
    chosenWitness phi s ∈ L := by
  rw [chosenWitness, dif_pos h]
  exact (Classical.choose_spec h).1

theorem chosenWitness_satisfies {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) (h : Model.SatisfiesIn L (.ex phi) s) :
    Model.SatisfiesIn L phi (snoc s (chosenWitness phi s)) := by
  rw [chosenWitness, dif_pos h]
  exact (Classical.choose_spec h).2

/-- A proof-independent chosen occurrence level, defaulting to zero off `L`. -/
noncomputable def stageOfConstructible (x : ZFSet.{u}) : Ordinal.{u} := by
  classical
  exact if hx : x ∈ L then stageOf x hx else 0

theorem mem_stageOfConstructible {x : ZFSet.{u}} (hx : x ∈ L) :
    x ∈ LStageZF (stageOfConstructible x) := by
  simp only [stageOfConstructible, dif_pos hx]
  exact mem_LStageZF_stageOf x hx

/-- A common ordinal bound for the chosen witnesses over one stage. -/
noncomputable def existentialWitnessBound {n : Nat}
    (phi : FOFormula (n + 1)) (alpha : Ordinal.{u}) : Ordinal.{u} :=
  iSup fun s : Tuple (ZFCarrier (LStageZF alpha)) n =>
    Order.succ (stageOfConstructible (chosenWitness phi (stageTupleVal s)))

theorem chosenWitness_mem_existentialWitnessBound {n : Nat}
    (phi : FOFormula (n + 1)) (alpha : Ordinal.{u})
    (s : Tuple (ZFCarrier (LStageZF alpha)) n)
    (h : Model.SatisfiesIn L (.ex phi) (stageTupleVal s)) :
    chosenWitness phi (stageTupleVal s) ∈
      LStageZF (existentialWitnessBound phi alpha) := by
  have hwL := chosenWitness_mem_L phi (stageTupleVal s) h
  have hwStage := mem_stageOfConstructible hwL
  apply LStageZF_mono _ hwStage
  exact (Order.le_succ _).trans (Ordinal.le_iSup
    (fun t : Tuple (ZFCarrier (LStageZF alpha)) n =>
      Order.succ (stageOfConstructible (chosenWitness phi (stageTupleVal t)))) s)

/-- Recursively combine all witness bounds required by a formula. -/
noncomputable def closingBound : {n : Nat} -> FOFormula n ->
    Ordinal.{u} -> Ordinal.{u}
  | _, .mem _ _, alpha => alpha
  | _, .eq _ _, alpha => alpha
  | _, .neg phi, alpha => closingBound phi alpha
  | _, .conj phi psi, alpha =>
      max (closingBound phi alpha) (closingBound psi alpha)
  | _, .ex phi, alpha =>
      max (closingBound phi alpha) (existentialWitnessBound phi alpha)

theorem le_closingBound {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : alpha <= closingBound phi alpha := by
  induction phi with
  | mem i j => exact le_rfl
  | eq i j => exact le_rfl
  | neg phi ih => exact ih
  | conj phi psi ihPhi ihPsi => exact ihPhi.trans (le_max_left _ _)
  | ex phi ih => exact ih.trans (le_max_left _ _)

/-- The recursively computed bound really closes all relevant subformulas. -/
theorem closesFrom_closingBound {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) :
    ClosesFrom phi alpha (closingBound phi alpha) := by
  induction phi with
  | mem i j => trivial
  | eq i j => trivial
  | neg phi ih => exact ih
  | conj phi psi ihPhi ihPsi =>
      exact ⟨ihPhi.mono_right (le_max_left _ _),
        ihPsi.mono_right (le_max_right _ _)⟩
  | ex phi ih =>
      refine ⟨ih.mono_right (le_max_left _ _), ?_⟩
      intro s hs hsat
      let sa : Tuple (ZFCarrier (LStageZF alpha)) _ :=
        fun i => ⟨s i, hs i⟩
      have hval : stageTupleVal sa = s := by
        funext i
        rfl
      have hwBound := chosenWitness_mem_existentialWitnessBound phi alpha sa
        (by simpa only [hval] using hsat)
      refine ⟨chosenWitness phi s, ?_, chosenWitness_satisfies phi s hsat⟩
      apply LStageZF_mono (le_max_right _ _)
      simpa only [hval] using hwBound

/-- One closure step is chosen strictly above every bound just constructed. -/
noncomputable def reflectionStep {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : Ordinal.{u} :=
  Order.succ (closingBound phi alpha)

theorem lt_reflectionStep {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : alpha < reflectionStep phi alpha :=
  (le_closingBound phi alpha).trans_lt (Order.lt_succ _)

theorem closesFrom_reflectionStep {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) :
    ClosesFrom phi alpha (reflectionStep phi alpha) :=
  (closesFrom_closingBound phi alpha).mono_right (Order.le_succ _)

/-- The omega-sequence obtained by repeatedly adjoining all required witnesses. -/
noncomputable def reflectionSequence {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : Nat -> Ordinal.{u}
  | 0 => alpha
  | k + 1 => reflectionStep phi (reflectionSequence phi alpha k)

@[simp]
theorem reflectionSequence_zero {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : reflectionSequence phi alpha 0 = alpha :=
  rfl

@[simp]
theorem reflectionSequence_succ {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) (k : Nat) :
    reflectionSequence phi alpha (k + 1) =
      reflectionStep phi (reflectionSequence phi alpha k) :=
  rfl

theorem reflectionSequence_lt_succ {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) (k : Nat) :
    reflectionSequence phi alpha k < reflectionSequence phi alpha (k + 1) := by
  rw [reflectionSequence_succ]
  exact lt_reflectionStep phi _

theorem reflectionSequence_strictMono {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : StrictMono (reflectionSequence phi alpha) :=
  strictMono_nat_of_lt_succ (reflectionSequence_lt_succ phi alpha)

/-- The limit of the witness-closure sequence. -/
noncomputable def reflectionOrdinal {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : Ordinal.{u} :=
  iSup (reflectionSequence phi alpha)

theorem reflectionSequence_le_ordinal {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) (k : Nat) :
    reflectionSequence phi alpha k <= reflectionOrdinal phi alpha :=
  Ordinal.le_iSup (reflectionSequence phi alpha) k

theorem reflectionSequence_lt_ordinal {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) (k : Nat) :
    reflectionSequence phi alpha k < reflectionOrdinal phi alpha :=
  (reflectionSequence_lt_succ phi alpha k).trans_le
    (reflectionSequence_le_ordinal phi alpha (k + 1))

theorem reflectionOrdinal_isSuccLimit {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : Order.IsSuccLimit (reflectionOrdinal phi alpha) := by
  rw [Order.isSuccLimit_iff]
  constructor
  · exact not_isMin_iff.mpr ⟨reflectionSequence phi alpha 0,
      reflectionSequence_lt_ordinal phi alpha 0⟩
  · apply Order.isSuccPrelimit_of_succ_lt
    intro gamma hgamma
    apply Ordinal.succ_lt_iSup_of_ne_iSup
      (f := reflectionSequence phi alpha)
    · intro k hk
      exact (reflectionSequence_lt_ordinal phi alpha k).ne hk
    · exact hgamma

theorem le_reflectionOrdinal {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : alpha <= reflectionOrdinal phi alpha := by
  simpa only [reflectionSequence_zero] using
    reflectionSequence_le_ordinal phi alpha 0

/-- Every finite tuple in the limit already occurs together at one sequence stage. -/
theorem exists_reflectionSequence_for_tuple {m n : Nat}
    (phi : FOFormula n) (alpha : Ordinal.{u})
    (s : Tuple ZFSet.{u} m)
    (hs : forall i, s i ∈ LStageZF (reflectionOrdinal phi alpha)) :
    exists k : Nat, forall i, s i ∈ LStageZF (reflectionSequence phi alpha k) := by
  induction m with
  | zero =>
      exact ⟨0, fun i => Fin.elim0 i⟩
  | succ m ih =>
      let init : Tuple ZFSet.{u} m := fun i => s i.castSucc
      have hinit : forall i, init i ∈ LStageZF (reflectionOrdinal phi alpha) :=
        fun i => hs i.castSucc
      rcases ih init hinit with ⟨k, hk⟩
      have hlast := hs (Fin.last m)
      rcases (mem_LStageZF_limit_iff
        (reflectionOrdinal_isSuccLimit phi alpha)).mp hlast with
        ⟨gamma, hgamma, hlastGamma⟩
      rcases (Ordinal.lt_iSup_iff.mp hgamma) with ⟨l, hgammaL⟩
      refine ⟨max k l, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact LStageZF_mono
          ((reflectionSequence_strictMono phi alpha).monotone
            (le_max_right k l))
          (LStageZF_mono hgammaL.le hlastGamma)
      · exact LStageZF_mono
          ((reflectionSequence_strictMono phi alpha).monotone
            (le_max_left k l))
          (hk j)

/--
If every step of one cofinal chain closes a formula from that step to the
next, then its limit is closed for that formula.  Crucially, the same chain is
kept while recursing through subformulas.
-/
theorem closesFrom_of_cofinal_sequence {n : Nat} (phi : FOFormula n)
    (sequence : Nat -> Ordinal.{u}) (beta : Ordinal.{u})
    (hcofinal : forall {m : Nat} (s : Tuple ZFSet.{u} m),
      (forall i, s i ∈ LStageZF beta) ->
      exists k : Nat, forall i, s i ∈ LStageZF (sequence k))
    (hstep : forall k, ClosesFrom phi (sequence k) (sequence (k + 1)))
    (hle : forall k, sequence (k + 1) <= beta) :
    ClosesFrom phi beta beta := by
  induction phi with
  | mem i j => trivial
  | eq i j => trivial
  | neg phi ih =>
      exact ih (fun k => hstep k)
  | conj phi psi ihPhi ihPsi =>
      exact ⟨ihPhi (fun k => (hstep k).1),
        ihPsi (fun k => (hstep k).2)⟩
  | ex phi ih =>
      refine ⟨ih (fun k => (hstep k).1), ?_⟩
      intro s hs hsat
      rcases hcofinal s hs with ⟨k, hk⟩
      rcases (hstep k).2 s hk hsat with ⟨x, hx, hphi⟩
      exact ⟨x, LStageZF_mono (hle k) hx, hphi⟩

/-- The limit level is closed under witnesses for the formula and all subformulas. -/
theorem closesFrom_reflectionOrdinal {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) :
    ClosesFrom phi (reflectionOrdinal phi alpha)
      (reflectionOrdinal phi alpha) := by
  apply closesFrom_of_cofinal_sequence phi (reflectionSequence phi alpha)
    (reflectionOrdinal phi alpha)
  · intro m s hs
    exact exists_reflectionSequence_for_tuple phi alpha s hs
  · intro k
    rw [reflectionSequence_succ]
    exact closesFrom_reflectionStep phi _
  · intro k
    exact reflectionSequence_le_ordinal phi alpha (k + 1)

/-- Tarski--Vaught induction from witness closure to formula absoluteness. -/
theorem satisfiesIn_stage_iff_L_of_closes {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u})
    (hclose : ClosesFrom phi alpha alpha)
    (s : Tuple ZFSet.{u} n) (hs : forall i, s i ∈ LStageZF alpha) :
    Model.SatisfiesIn (LStageZF alpha : Set ZFSet.{u}) phi s <->
      Model.SatisfiesIn L phi s := by
  induction phi with
  | mem i j => rfl
  | eq i j => rfl
  | neg phi ih =>
      exact not_congr (ih hclose s hs)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi hclose.1 s hs) (ihPsi hclose.2 s hs)
  | ex phi ih =>
      constructor
      · rintro ⟨x, hxStage, hphi⟩
        have hxL : x ∈ L :=
          LStageZF_subset_constructibleUniverse alpha hxStage
        refine ⟨x, hxL, ?_⟩
        apply (ih hclose.1 (snoc s x) ?_).mp hphi
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hxStage
        · simpa using hs j
      · intro hex
        rcases hclose.2 s hs hex with ⟨x, hxStage, hphi⟩
        refine ⟨x, hxStage, ?_⟩
        apply (ih hclose.1 (snoc s x) ?_).mpr hphi
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hxStage
        · simpa using hs j

/--
Every formula reflects between `L` and an arbitrarily high constructible
level.  This is the form used by full Separation and Replacement.
-/
theorem exists_reflecting_LStage {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) :
    exists beta : Ordinal.{u}, alpha <= beta /\
      forall s : Tuple ZFSet.{u} n,
        (forall i, s i ∈ LStageZF beta) ->
        (Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u}) phi s <->
          Model.SatisfiesIn L phi s) := by
  refine ⟨reflectionOrdinal phi alpha, le_reflectionOrdinal phi alpha, ?_⟩
  intro s hs
  exact satisfiesIn_stage_iff_L_of_closes phi _
    (closesFrom_reflectionOrdinal phi alpha) s hs

end ZFC

end Constructible
end CUAdapterModule43



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Separation -/
section CUAdapterModule44
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Full Separation in the constructible universe

For a formula with constructible parameters and a constructible set `a`, a
reflecting level turns truth in the proper class `L` into ordinary
first-order truth over one internal stage.  The corresponding definable
subset of that stage lies in its `DefZF`; intersecting it with `a` gives the
required Separation set.
-/


open Set

universe u

namespace Constructible

section ZFC

/--
Full first-order Separation for the raw-domain semantics of `L`.

The last variable of `phi` is the element being separated; the preceding
`n` variables are parameters.
-/
theorem exists_separation {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple ZFSet.{u} n) (hparams : forall i, params i ∈ L)
    {a : ZFSet.{u}} (ha : a ∈ L) :
    exists b : ZFSet.{u}, b ∈ L /\
      forall x : ZFSet.{u},
        x ∈ b <-> x ∈ a /\
          Model.SatisfiesIn L phi (snoc params x) := by
  have hall : forall i, snoc params a i ∈ L := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using hparams j
  rcases exists_LStage_for_tuple (snoc params a) hall with ⟨alpha, halpha⟩
  have hparamsAlpha : forall i, params i ∈ LStageZF alpha := by
    intro i
    simpa using halpha i.castSucc
  have haAlpha : a ∈ LStageZF alpha := by
    simpa using halpha (Fin.last n)
  rcases exists_reflecting_LStage phi alpha with
    ⟨beta, halphaBeta, hreflect⟩
  have hparamsBeta : forall i, params i ∈ LStageZF beta :=
    fun i => LStageZF_mono halphaBeta (hparamsAlpha i)
  have haBeta : a ∈ LStageZF beta :=
    LStageZF_mono halphaBeta haAlpha
  let paramsBeta : Tuple (ZFCarrier (LStageZF beta)) n :=
    fun i => ⟨params i, hparamsBeta i⟩
  let c : ZFSet.{u} :=
    ZFSet.sep
      (fun x => Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u})
        phi (snoc params x))
      (LStageZF beta)
  have hcDef : c ∈ DefZF (LStageZF beta) := by
    rw [mem_DefZF_iff_exists_satisfies]
    refine ⟨ZFSet.sep_subset, n, paramsBeta, phi, ?_⟩
    intro x
    simp only [c, ZFSet.mem_sep, and_iff_right x.2]
    have hbridge :=
      Model.satisfies_stageCarrier_iff_satisfiesIn
        (alpha := beta) phi (snoc paramsBeta x)
    have hassign :
        (fun i => (snoc paramsBeta x i).1) = snoc params x.1 := by
      simp only [Model.subtypeVal_snoc, paramsBeta]
    change
      Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u}) phi
          (snoc params x.1) ↔
        FOFormula.Satisfies
          (fun y z : ZFCarrier (LStageZF beta) => y.1 ∈ z.1) phi
          (snoc paramsBeta x)
    rw [← hassign]
    exact hbridge.symm
  have hcL : c ∈ L := by
    refine ⟨Order.succ beta, ?_⟩
    rw [LStageZF_succ]
    exact hcDef
  refine ⟨a ∩ c, inter_mem_L ha hcL, ?_⟩
  intro x
  rw [ZFSet.mem_inter]
  constructor
  · rintro ⟨hxa, hxc⟩
    have hxBeta : x ∈ LStageZF beta :=
      (LStageZF_isTransitive beta).mem_trans hxa haBeta
    have hstage :
        Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u})
          phi (snoc params x) :=
      (ZFSet.mem_sep.mp hxc).2
    have hassign : forall i, snoc params x i ∈ LStageZF beta := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hxBeta
      · simpa using hparamsBeta j
    exact ⟨hxa, (hreflect (snoc params x) hassign).mp hstage⟩
  · rintro ⟨hxa, hL⟩
    have hxBeta : x ∈ LStageZF beta :=
      (LStageZF_isTransitive beta).mem_trans hxa haBeta
    have hassign : forall i, snoc params x i ∈ LStageZF beta := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hxBeta
      · simpa using hparamsBeta j
    have hstage := (hreflect (snoc params x) hassign).mpr hL
    refine ⟨hxa, ?_⟩
    exact ZFSet.mem_sep.mpr ⟨hxBeta, hstage⟩

/-- Full Separation packaged on the subtype model `LCarrier`. -/
theorem Model.exists_separationLCarrier {n : Nat}
    (phi : FOFormula (n + 1)) (params : Tuple Model.LCarrier.{u} n)
    (a : Model.LCarrier.{u}) :
    exists b : Model.LCarrier.{u}, forall x : Model.LCarrier.{u},
      x.1 ∈ b.1 <-> x.1 ∈ a.1 /\
        FOFormula.Satisfies
          (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc params x) := by
  let rawParams : Tuple ZFSet.{u} n := fun i => (params i).1
  have hraw : forall i, rawParams i ∈ L := fun i => (params i).2
  rcases exists_separation phi rawParams hraw a.2 with ⟨b, hbL, hb⟩
  refine ⟨⟨b, hbL⟩, ?_⟩
  intro x
  rw [hb x.1]
  have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
    phi (snoc params x)
  simpa only [Model.subtypeVal_snoc] using
    and_congr_right (fun _ => hbridge.symm)





end ZFC

end Constructible
end CUAdapterModule44



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Collection -/
section CUAdapterModule45
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Collection in the constructible universe

Ambient choice selects one constructible witness for each member of the
given internal set.  Since that index type is small, the occurrence levels of
all selected witnesses have a supremum.  The corresponding constructible
stage is itself an element of `L` and collects every selected witness.

The selected family is a function in Lean's classical metatheory, not a
function graph assumed to belong to `L`.  Thus there is no circular use of
the target Axiom of Choice.  A proof parameterized over arbitrary ZF models
would instead have to internalize the corresponding rank-bounding or
Collection argument.
-/


universe u

namespace Constructible

section ZFC

/-- Full first-order Collection for the raw-domain semantics of `L`. -/
theorem exists_collection {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) {a : ZFSet.{u}} (_ha : a ∈ L)
    (h : forall x : ZFSet.{u}, x ∈ a ->
      exists y : ZFSet.{u}, y ∈ L /\
        Model.SatisfiesIn L phi (snoc (snoc params x) y)) :
    exists b : ZFSet.{u}, b ∈ L /\
      forall x : ZFSet.{u}, x ∈ a ->
        exists y : ZFSet.{u}, y ∈ b /\
          Model.SatisfiesIn L phi (snoc (snoc params x) y) := by
  classical
  let witness : a -> ZFSet.{u} := fun x => Classical.choose (h x.1 x.2)
  have hwitnessL (x : a) : witness x ∈ L :=
    (Classical.choose_spec (h x.1 x.2)).1
  have hwitnessSat (x : a) :
      Model.SatisfiesIn L phi (snoc (snoc params x.1) (witness x)) :=
    (Classical.choose_spec (h x.1 x.2)).2
  let level : a -> Ordinal.{u} := fun x => stageOf (witness x) (hwitnessL x)
  let beta : Ordinal.{u} := iSup level
  refine ⟨LStageZF beta, LStageZF_mem_L beta, ?_⟩
  intro x hx
  let xa : a := ⟨x, hx⟩
  refine ⟨witness xa, ?_, hwitnessSat xa⟩
  exact LStageZF_mono (Ordinal.le_iSup level xa)
    (mem_LStageZF_stageOf (witness xa) (hwitnessL xa))





end ZFC

end Constructible
end CUAdapterModule45



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Replacement -/
section CUAdapterModule46
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Replacement in the constructible universe

Collection first gives a constructible set containing a value for every
input.  Full Separation then cuts out the exact range.  The formula
`replacementRangeFormula phi` expresses that its last variable is related by
`phi` to some member of the set parameter immediately preceding it.
-/


universe u

namespace Constructible

section ZFC

namespace Model

/-- Renaming raw-domain formulas composes their assignments. -/
@[simp]
theorem satisfiesIn_rename (M : Set ZFSet.{u}) {n m : Nat}
    (phi : FOFormula n) (rho : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.rename rho phi) s <->
      SatisfiesIn M phi (fun i => s (rho i)) := by
  induction phi generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg phi ih => exact not_congr (ih rho s)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi rho s) (ihPsi rho s)
  | ex phi ih =>
      simp only [FOFormula.rename, SatisfiesIn, ih]
      constructor
      · rintro ⟨x, hxM, hphi⟩
        refine ⟨x, hxM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hphi
      · rintro ⟨x, hxM, hphi⟩
        refine ⟨x, hxM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hphi

end Model

/--
Variable permutation used under the existential in
`replacementRangeFormula`.  The old layout is `(params, x, y)` and the new
body layout is `(params, a, y, x)`.
-/
def replacementRangeRename {n : Nat} : Fin (n + 2) -> Fin (n + 3) :=
  Fin.lastCases
    (Fin.castSucc (Fin.last (n + 1)))
    (fun j => Fin.lastCases
      (Fin.last (n + 2))
      (fun i => i.castSucc.castSucc.castSucc)
      j)

/-- The variable permutation has the intended effect on appended tuples. -/
theorem comp_replacementRangeRename {A : Type u} {n : Nat}
    (params : Tuple A n) (a y x : A) :
    (fun i => snoc (snoc (snoc params a) y) x
      (replacementRangeRename i)) =
      snoc (snoc params x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [replacementRangeRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [replacementRangeRename]
    · simp [replacementRangeRename]

/--
`replacementRangeFormula phi(params,a,y)` says that some `x ∈ a` satisfies
`phi(params,x,y)`.
-/
def replacementRangeFormula {n : Nat}
    (phi : FOFormula (n + 2)) : FOFormula (n + 2) :=
  .ex (.conj
    (.mem (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc)
    (FOFormula.rename replacementRangeRename phi))

@[simp]
theorem satisfiesIn_replacementRangeFormula (M : Set ZFSet.{u})
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (a y : ZFSet.{u}) :
    Model.SatisfiesIn M (replacementRangeFormula phi)
        (snoc (snoc params a) y) <->
      exists x : ZFSet.{u}, x ∈ M /\ x ∈ a /\
        Model.SatisfiesIn M phi (snoc (snoc params x) y) := by
  simp only [replacementRangeFormula, Model.SatisfiesIn,
    Model.satisfiesIn_rename]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _hxM
  change
    (snoc (snoc (snoc params a) y) x (Fin.last (n + 2)) ∈
        snoc (snoc (snoc params a) y) x
          (Fin.last n).castSucc.castSucc /\
      Model.SatisfiesIn M phi
        (fun i => snoc (snoc (snoc params a) y) x
          (replacementRangeRename i))) <-> _
  simp only [snoc_last, snoc_castSucc, comp_replacementRangeRename]

/--
Function-form Replacement for the raw-domain semantics of `L`.

The predicate is required to have a unique constructible output for every
member of `a`.  The resulting set consists of exactly those outputs.
-/
theorem exists_replacement {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (hparams : forall i, params i ∈ L)
    {a : ZFSet.{u}} (ha : a ∈ L)
    (hfun : forall x : ZFSet.{u}, x ∈ a ->
      ∃! y : ZFSet.{u}, y ∈ L /\
        Model.SatisfiesIn L phi (snoc (snoc params x) y)) :
    exists b : ZFSet.{u}, b ∈ L /\
      forall y : ZFSet.{u}, y ∈ b <->
        y ∈ L /\ exists x : ZFSet.{u}, x ∈ a /\
          Model.SatisfiesIn L phi (snoc (snoc params x) y) := by
  have hexists : forall x : ZFSet.{u}, x ∈ a ->
      exists y : ZFSet.{u}, y ∈ L /\
        Model.SatisfiesIn L phi (snoc (snoc params x) y) :=
    fun x hx => (hfun x hx).exists
  rcases exists_collection phi params ha hexists with ⟨c, hcL, hcollect⟩
  let extendedParams : Tuple ZFSet.{u} (n + 1) := snoc params a
  have hextended : forall i, extendedParams i ∈ L := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [extendedParams] using ha
    · simpa [extendedParams] using hparams j
  rcases exists_separation (replacementRangeFormula phi)
      extendedParams hextended hcL with ⟨b, hbL, hb⟩
  refine ⟨b, hbL, ?_⟩
  intro y
  constructor
  · intro hyb
    rcases (hb y).mp hyb with ⟨hyc, hyrange⟩
    have hyL : y ∈ L := mem_L_of_mem hyc hcL
    rcases (satisfiesIn_replacementRangeFormula L phi params a y).mp
        (by simpa only [extendedParams] using hyrange) with
      ⟨x, _hxL, hxa, hphi⟩
    exact ⟨hyL, x, hxa, hphi⟩
  · rintro ⟨hyL, x, hxa, hphi⟩
    rcases hcollect x hxa with ⟨z, hzc, hzphi⟩
    have hzL : z ∈ L := mem_L_of_mem hzc hcL
    rcases hfun x hxa with ⟨w, hw, hunique⟩
    have hzw : z = w := hunique z ⟨hzL, hzphi⟩
    have hyw : y = w := hunique y ⟨hyL, hphi⟩
    have hyz : y = z := hyw.trans hzw.symm
    have hyc : y ∈ c := by simpa only [hyz] using hzc
    apply (hb y).mpr
    refine ⟨hyc, ?_⟩
    have hxL : x ∈ L := mem_L_of_mem hxa ha
    have hrange :=
      (satisfiesIn_replacementRangeFormula L phi params a y).mpr
        ⟨x, hxL, hxa, hphi⟩
    simpa only [extendedParams] using hrange

/-- Function-form Replacement packaged on `LCarrier`. -/
theorem Model.exists_replacementLCarrier {n : Nat}
    (phi : FOFormula (n + 2)) (params : Tuple Model.LCarrier.{u} n)
    (a : Model.LCarrier.{u})
    (hfun : forall x : Model.LCarrier.{u}, x.1 ∈ a.1 ->
      ∃! y : Model.LCarrier.{u},
        FOFormula.Satisfies
          (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc (snoc params x) y)) :
    exists b : Model.LCarrier.{u}, forall y : Model.LCarrier.{u},
      y.1 ∈ b.1 <-> exists x : Model.LCarrier.{u}, x.1 ∈ a.1 /\
        FOFormula.Satisfies
          (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc (snoc params x) y) := by
  let rawParams : Tuple ZFSet.{u} n := fun i => (params i).1
  have hrawParams : forall i, rawParams i ∈ L := fun i => (params i).2
  have hrawFun : forall x : ZFSet.{u}, x ∈ a.1 ->
      ∃! y : ZFSet.{u}, y ∈ L /\
        Model.SatisfiesIn L phi (snoc (snoc rawParams x) y) := by
    intro x hx
    let xL : Model.LCarrier.{u} := ⟨x, mem_L_of_mem hx a.2⟩
    rcases hfun xL hx with ⟨y, hy, hunique⟩
    refine ⟨y.1, ?_, ?_⟩
    · refine ⟨y.2, ?_⟩
      have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
        phi (snoc (snoc params xL) y)
      simpa only [Model.subtypeVal_snoc, rawParams] using hbridge.mp hy
    · intro z hz
      let zL : Model.LCarrier.{u} := ⟨z, hz.1⟩
      have hzSat :
          FOFormula.Satisfies
            (fun p q : Model.LCarrier.{u} => p.1 ∈ q.1)
            phi (snoc (snoc params xL) zL) := by
        have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
          phi (snoc (snoc params xL) zL)
        apply hbridge.mpr
        simpa only [Model.subtypeVal_snoc, rawParams] using hz.2
      exact congrArg Subtype.val (hunique zL hzSat)
  rcases exists_replacement phi rawParams hrawParams a.2 hrawFun with
    ⟨b, hbL, hb⟩
  refine ⟨⟨b, hbL⟩, ?_⟩
  intro y
  constructor
  · intro hyb
    rcases (hb y.1).mp hyb with ⟨_hyL, x, hxa, hphi⟩
    let xL : Model.LCarrier.{u} := ⟨x, mem_L_of_mem hxa a.2⟩
    refine ⟨xL, hxa, ?_⟩
    have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
      phi (snoc (snoc params xL) y)
    apply hbridge.mpr
    simpa only [Model.subtypeVal_snoc, rawParams] using hphi
  · rintro ⟨x, hxa, hphi⟩
    apply (hb y.1).mpr
    refine ⟨y.2, x.1, hxa, ?_⟩
    have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
      phi (snoc (snoc params x) y)
    simpa only [Model.subtypeVal_snoc, rawParams] using hbridge.mp hphi





end ZFC

end Constructible
end CUAdapterModule46



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.ZFModel -/
section CUAdapterModule47
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The constructible universe is a model of ZF

This file packages the closure, reflection, bounding, and ordinal results for
the constructible universe into Mathlib's canonical first-order theory of ZF.
The Separation and Replacement schemes range over every formula in
`FirstOrder.Language.setTheory`.
-/


universe u

namespace Constructible.Model



end Constructible.Model
end CUAdapterModule47



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Choice -/
section CUAdapterModule48
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The Axiom of Choice for the constructible universe

The canonical model-theoretic ZFC API supplies the disjoint-family formulation
of Choice. This file proves that a definable relation giving unique minima to
all nonempty constructible sets produces the required choice sets in `L`.
-/


universe u

namespace Constructible

namespace Model



end Model

namespace ChoiceSyntax

/-! ## Selecting minima -/

/-- Place the order formula on the newest variable and coordinate `1`. -/
def leastLtRename : Fin 2 -> Fin 4 :=
  ![Fin.last 3, (1 : Fin 2).castSucc.castSucc]

theorem comp_leastLtRename {A : Type u} (s : Tuple A 2) (x z : A) :
    (fun i => snoc (snoc s x) z (leastLtRename i)) = ![z, s 1] := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change snoc (snoc s x) z (Fin.last 3) = z
    exact snoc_last _ _
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change snoc (snoc s x) z ((1 : Fin 2).castSucc.castSucc) = s 1
    simp only [snoc_castSucc]

/--
With assignment `![a,y]`, this says that `y` is minimal in some member of
the family `a` according to `ltFormula`.
-/
def leastMemberPredicate (ltFormula : FOFormula 2) : FOFormula 2 :=
  .ex
    (.conj
      (.mem (Fin.last 2) (0 : Fin 2).castSucc)
      (.conj
        (.mem (1 : Fin 2).castSucc (Fin.last 2))
        (.all
          (FOFormula.imp
            (.mem (Fin.last 3) (Fin.last 2).castSucc)
            (.neg (FOFormula.rename leastLtRename ltFormula))))))

@[simp]
theorem satisfies_leastMemberPredicate {A : Type u} (E : A -> A -> Prop)
    (ltFormula : FOFormula 2) (s : Tuple A 2) :
    FOFormula.Satisfies E (leastMemberPredicate ltFormula) s <->
      exists x : A, E x (s 0) /\ E (s 1) x /\
        forall z : A, E z x ->
          Not (FOFormula.Satisfies E ltFormula ![z, s 1]) := by
  simp only [leastMemberPredicate, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_rename, snoc_last, snoc_castSucc,
    comp_leastLtRename]

end ChoiceSyntax

namespace Model





end Model

end Constructible
end CUAdapterModule48



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.InternalWellOrder -/
section CUAdapterModule49
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internal well-orders and Choice in the constructible universe

An external Lean relation is not enough to prove Choice inside `L`: its graph
must itself be represented by a constructible set.  This file isolates that
requirement.  A constructible set `r` represents the relation
`x <_r y` when the Kuratowski pair `⟨x,y⟩` belongs to `r`.

We prove that if every constructible set is well-orderable by such a
constructible graph, then `L` satisfies the disjoint-family form of Choice and
hence Mathlib's canonical first-order theory ZFC. The proposition
`ModelsInternalWellOrdering` is the interface used to derive these results.
-/


open Set

universe u

namespace Constructible

namespace Delta0Formula

/-! ## Bounded absoluteness for the proper class `L` -/

/--
Bounded formulas are absolute between the transitive class `L` and the
ambient `ZFSet` universe.  The left side uses subtype-valued assignments; the
right side forgets the constructibility proofs.
-/
theorem satisfies_lCarrier_absolute {n : Nat} (phi : Delta0Formula n)
    (s : Tuple Model.LCarrier.{u} n) :
    Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1) phi s ↔
      Satisfies ZFMem phi (fun i => (s i).1) := by
  induction phi with
  | mem i j => rfl
  | eq i j =>
      change s i = s j ↔ (s i).1 = (s j).1
      exact Subtype.coe_injective.eq_iff.symm
  | neg phi ih => simp only [Satisfies, ih]
  | conj phi psi ihPhi ihPsi =>
      simp only [Satisfies, ihPhi, ihPsi]
  | boundedEx i phi ih =>
      constructor
      · rintro ⟨x, hx, hphi⟩
        refine ⟨x.1, hx, ?_⟩
        have habs := (ih (snoc s x)).mp hphi
        simpa only [Model.subtypeVal_snoc] using habs
      · rintro ⟨x, hx, hphi⟩
        let xL : Model.LCarrier.{u} :=
          ⟨x, mem_L_of_mem hx (s i).2⟩
        refine ⟨xL, hx, ?_⟩
        apply (ih (snoc s xL)).mpr
        simpa only [Model.subtypeVal_snoc, xL] using hphi

/-- The same absoluteness statement after translation to `FOFormula`. -/
theorem satisfies_toFO_lCarrier_absolute {n : Nat}
    (phi : Delta0Formula n) (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1) phi.toFO s ↔
      FOFormula.Satisfies ZFMem phi.toFO (fun i => (s i).1) := by
  rw [satisfies_toFO, satisfies_toFO, satisfies_lCarrier_absolute]

end Delta0Formula

namespace Model

/-! ## Relations represented by constructible graphs -/

/-- The relation represented by a constructible set of Kuratowski pairs. -/
def GraphRel (r x y : LCarrier.{u}) : Prop :=
  ZFSet.pair x.1 y.1 ∈ r.1

/-- The carrier of an internal set, still retaining constructibility proofs. -/
abbrev InternalCarrier (a : LCarrier.{u}) :=
  {x : LCarrier.{u} // x.1 ∈ a.1}

/-- The graph relation restricted to the elements of `a`. -/
def graphRelOn (r a : LCarrier.{u}) :
    InternalCarrier a -> InternalCarrier a -> Prop :=
  fun x y => GraphRel r x.1 y.1

/-- `r ∈ L` represents a genuine well-order of the elements of `a`. -/
def InternallyWellOrders (r a : LCarrier.{u}) : Prop :=
  IsWellOrder (InternalCarrier a) (graphRelOn r a)

/-- Every internal set has a well-order whose relation graph also belongs to `L`. -/
def ModelsInternalWellOrdering : Prop :=
  forall a : LCarrier.{u}, exists r : LCarrier.{u},
    InternallyWellOrders r a

/-! ## The object-language graph predicate -/

/--
With assignment `![r,x,y]`, this bounded formula says that the Kuratowski pair
`⟨x,y⟩` belongs to `r`.
-/
def graphRelDelta0 : Delta0Formula 3 :=
  .boundedEx (0 : Fin 3)
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last 3) (1 : Fin 3).castSucc (2 : Fin 3).castSucc)

/-- The graph predicate in the unrestricted syntax used by Separation. -/
def graphRelFormula : FOFormula 3 :=
  graphRelDelta0.toFO

@[simp]
theorem satisfies_graphRelFormula (s : Tuple LCarrier.{u} 3) :
    FOFormula.Satisfies
        (fun x y : LCarrier.{u} => x.1 ∈ y.1)
        graphRelFormula s ↔
      GraphRel (s 0) (s 1) (s 2) := by
  rw [graphRelFormula,
    Delta0Formula.satisfies_toFO_lCarrier_absolute]
  simp only [Delta0Formula.satisfies_toFO, graphRelDelta0,
    Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc, GraphRel]
  constructor
  · rintro ⟨q, hqr, hq⟩
    simpa [hq] using hqr
  · intro hpair
    exact ⟨ZFSet.pair (s 1).1 (s 2).1, hpair, rfl⟩

/-- Select `[r,z,y]` from the context `[a,r,y,x,z]`. -/
def graphMinimumRename : Fin 3 -> Fin 5 :=
  ![(1 : Fin 3).castSucc.castSucc,
    Fin.last 4,
    (2 : Fin 3).castSucc.castSucc]

theorem comp_graphMinimumRename {A : Type u}
    (s : Tuple A 3) (x z : A) :
    (fun i => snoc (snoc s x) z (graphMinimumRename i)) =
      ![s 1, z, s 2] := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change snoc (snoc s x) z ((1 : Fin 3).castSucc.castSucc) = s 1
    simp only [snoc_castSucc]
  · refine Fin.cases ?_ (fun k => ?_) j
    · change snoc (snoc s x) z (Fin.last 4) = z
      exact snoc_last _ _
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      change snoc (snoc s x) z ((2 : Fin 3).castSucc.castSucc) = s 2
      simp only [snoc_castSucc]

/--
With assignment `![a,r,y]`, this says that `y` is an `r`-least member of
some member of the family `a`.
-/
def graphLeastMemberPredicate : FOFormula 3 :=
  .ex
    (.conj
      (.mem (Fin.last 3) (0 : Fin 3).castSucc)
      (.conj
        (.mem (2 : Fin 3).castSucc (Fin.last 3))
        (.all
          (FOFormula.imp
            (.mem (Fin.last 4) (Fin.last 3).castSucc)
            (.neg
              (FOFormula.rename graphMinimumRename graphRelFormula))))))

@[simp]
theorem satisfies_graphLeastMemberPredicate (s : Tuple LCarrier.{u} 3) :
    FOFormula.Satisfies
        (fun x y : LCarrier.{u} => x.1 ∈ y.1)
        graphLeastMemberPredicate s ↔
      exists x : LCarrier.{u},
        x.1 ∈ (s 0).1 /\ (s 2).1 ∈ x.1 /\
          forall z : LCarrier.{u}, z.1 ∈ x.1 ->
            Not (GraphRel (s 1) z (s 2)) := by
  simp only [graphLeastMemberPredicate, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_rename, snoc_last, snoc_castSucc,
    comp_graphMinimumRename, satisfies_graphRelFormula]
  simp

/-! ## Unique minima from an internal well-order -/



/-! ## Choice and ZFC -/





end Model

end Constructible
end CUAdapterModule49


