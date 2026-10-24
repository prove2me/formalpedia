-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library12
-- name    : CH_ConstructibleAC_Library12
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:33:29.528752+00:00
-- url     : https://prove2.me/theorems/3ae79733-9ba2-45ad-9c5b-295ac0fc557f
-- title:
--   Least programs and successor-stage order data
-- statement:
--   Descriptions that successfully produce a set can be ordered and compared through their least representatives. This library provides those successful-program and least-program interfaces and the internal order constructions used when passing to a successor stage. The successor-state and definable-output formulas describe the resulting data inside the membership language.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentarySuccessfulProgramOrder.lean#L1-L155; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryLeastProgramAbsolute.lean#L1-L295; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageInternalOrder.lean#L1-L164; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentarySuccessorInternalOrder.lean#L1-L199; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentarySuccessorExtensionOrder.lean#L1-L467; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalSuccessorOrder.lean#L1-L192; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryDefOutputFormula.lean#L1-L301; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/SuccessorStageStateFormula.lean#L1-L201

import Definitions.Def_CH_ConstructibleAC_Library11
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


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentarySuccessfulProgramOrder -/
section CUAdapterModule77
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Ordering definable values by successful stack programs

This module gives a formula-independent presentation of the canonical order
on one Gödel-definability step. A value `x` precedes `y` when some program
evaluating to `x` precedes every program evaluating to `y`.  Once the
generator relation is a well-order, this is exactly the existing order by
least successful programs, `defCarrierStackRel`.
-/


universe u

namespace Constructible.Godel

namespace RudimentaryTerm

noncomputable section

/--
`x` precedes `y` if a successful program for `x` is earlier than every
successful program for `y` in the structural program order.
-/
def successfulProgramValueRel (U relation : ZFSet.{u}) :
    DefCarrier U -> DefCarrier U -> Prop :=
  fun x y =>
    exists program : List (StackToken (Option (ZFCarrier U))),
      runStackProgram (rudimentaryGenerator U) program [] = some [x.1] /\
        forall other : List (StackToken (Option (ZFCarrier U))),
          runStackProgram (rudimentaryGenerator U) other [] = some [y.1] ->
            stackProgramRel (generatorTokenRel U relation) program other

/-- No successful program for `z` lies below its canonical least program. -/
theorem leastStackProgram_minimal
    (U z : ZFSet.{u}) (hz : z ∈ godelDef U)
    (r : Option (ZFCarrier U) -> Option (ZFCarrier U) -> Prop)
    [IsWellOrder (Option (ZFCarrier U)) r]
    {program : List (StackToken (Option (ZFCarrier U)))}
    (hprogram :
      runStackProgram (rudimentaryGenerator U) program [] = some [z]) :
    Not (stackProgramRel r program (leastStackProgram U z hz r)) := by
  letI : IsWellOrder
      (List (StackToken (Option (ZFCarrier U))))
      (stackProgramRel r) := stackProgramRel_isWellOrder r
  exact
    (IsWellFounded.wf : WellFounded (stackProgramRel r)).not_lt_min
      (representingStackPrograms U z) hprogram

/--
The successful-program presentation is exactly comparison of the two least
successful programs.
-/
theorem successfulProgramValueRel_eq_defCarrierStackRel
    (U relation : ZFSet.{u})
    [IsWellOrder (Option (ZFCarrier U))
      (generatorTokenRel U relation)] :
    successfulProgramValueRel U relation =
      defCarrierStackRel U (generatorTokenRel U relation) := by
  let programRel :=
    stackProgramRel (generatorTokenRel U relation)
  letI : IsWellOrder
      (List (StackToken (Option (ZFCarrier U)))) programRel :=
    stackProgramRel_isWellOrder (generatorTokenRel U relation)
  funext x y
  apply propext
  change
    (exists program : List (StackToken (Option (ZFCarrier U))),
      runStackProgram (rudimentaryGenerator U) program [] = some [x.1] /\
        forall other : List (StackToken (Option (ZFCarrier U))),
          runStackProgram (rudimentaryGenerator U) other [] = some [y.1] ->
            programRel program other) <->
      programRel
        (leastStackProgram U x.1 x.2 (generatorTokenRel U relation))
        (leastStackProgram U y.1 y.2 (generatorTokenRel U relation))
  constructor
  · rintro ⟨program, hprogram, hbelow⟩
    have hprogramBelowY :
        programRel program
          (leastStackProgram U y.1 y.2
            (generatorTokenRel U relation)) :=
      hbelow _
        (run_leastStackProgram U y.1 y.2
          (generatorTokenRel U relation))
    rcases trichotomous_of programRel
        (leastStackProgram U x.1 x.2
          (generatorTokenRel U relation)) program with
      hleast | heq | hprogramBelowX
    · exact IsTrans.trans _ _ _ hleast hprogramBelowY
    · simpa only [heq] using hprogramBelowY
    · exact False.elim
        (leastStackProgram_minimal U x.1 x.2
          (generatorTokenRel U relation) hprogram hprogramBelowX)
  · intro hleast
    refine
      ⟨leastStackProgram U x.1 x.2 (generatorTokenRel U relation),
        run_leastStackProgram U x.1 x.2
          (generatorTokenRel U relation), ?_⟩
    intro other hother
    rcases trichotomous_of programRel other
        (leastStackProgram U y.1 y.2
          (generatorTokenRel U relation)) with
      hotherBelow | heq | hleastYBelow
    · exact False.elim
        (leastStackProgram_minimal U y.1 y.2
          (generatorTokenRel U relation) hother hotherBelow)
    · simpa only [heq] using hleast
    · exact IsTrans.trans _ _ _ hleast hleastYBelow



/--
An internally represented well-order of `U` therefore makes the
successful-program relation a well-order of `DefCarrier U.1`.
-/
theorem successfulProgramValueRel_isWellOrder_of_internal
    (U relation : Model.LCarrier.{u})
    (hwell : Model.InternallyWellOrders relation U) :
    IsWellOrder (DefCarrier U.1)
      (successfulProgramValueRel U.1 relation.1) := by
  let generatorWellOrder :=
    generatorTokenRel_isWellOrder_of_internal U relation hwell
  letI : IsWellOrder (Option (ZFCarrier U.1))
      (generatorTokenRel U.1 relation.1) := generatorWellOrder
  rw [successfulProgramValueRel_eq_defCarrierStackRel]
  exact defCarrierStackRel_isWellOrder U.1
    (generatorTokenRel U.1 relation.1)

end

end RudimentaryTerm

end Constructible.Godel
end CUAdapterModule77



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryLeastProgramAbsolute -/
section CUAdapterModule78
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Absoluteness of the least-successful-program value order

The combined least-program formula has unbounded program-code quantifiers.
This file proves its exact semantics in `Model.LCarrier`.  Arbitrary internal
codes are projected to the ambient evaluator and decoded; canonical codes
supply the converse witnesses.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

local notation "LMem" => Model.lCarrierMem

/-! ## Constructible assignments -/

/-- The fifteen constructible parameters of the value-order formula. -/
def leastProgramValueLtParametersLAssignment
    (U relation : Model.LCarrier.{u}) :
    Tuple Model.LCarrier.{u} 15 :=
  snoc
    (snoc (stackStepPrefixLAssignment U.1 U.2)
      ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
    relation

/-- The full constructible assignment, with the compared values last. -/
def leastProgramValueLtLAssignment
    (U relation left right : Model.LCarrier.{u}) :
    Tuple Model.LCarrier.{u} 17 :=
  snoc (snoc (leastProgramValueLtParametersLAssignment U relation) left)
    right

theorem leastProgramValueLtLAssignment_val
    (U relation left right : Model.LCarrier.{u}) :
    (fun i => (leastProgramValueLtLAssignment U relation left right i).1) =
      leastProgramValueLtAssignment U.1 relation.1 left.1 right.1 := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rfl
      · refine Fin.lastCases ?_ (fun i12 => ?_) i13
        · rfl
        · simpa only [leastProgramValueLtLAssignment,
            leastProgramValueLtParametersLAssignment,
            leastProgramValueLtAssignment,
            leastProgramValueLtParametersAssignment, snoc_castSucc] using
            congrFun (stackStepPrefixLAssignment_val U.1 U.2) i12

theorem comp_leastProgramLeftEvalRename_lCarrier
    (U relation left right p : Model.LCarrier.{u}) :
    (fun i =>
      snoc (leastProgramValueLtLAssignment U relation left right) p
        (leastProgramLeftEvalRename i)) =
      stackProgramEvalCodeLAssignment U.1 p.1 left.1
        U.2 p.2 left.2 := by
  funext i
  apply Subtype.ext
  have hraw := congrFun
    (comp_leastProgramLeftEvalRename
      U.1 relation.1 left.1 right.1 p.1) i
  calc
    (snoc (leastProgramValueLtLAssignment U relation left right) p
        (leastProgramLeftEvalRename i)).1 =
        snoc
          (fun j =>
            (leastProgramValueLtLAssignment U relation left right j).1)
          p.1 (leastProgramLeftEvalRename i) :=
      congrFun
        (Model.subtypeVal_snoc
          (leastProgramValueLtLAssignment U relation left right) p)
        (leastProgramLeftEvalRename i)
    _ = snoc
          (leastProgramValueLtAssignment U.1 relation.1 left.1 right.1)
          p.1 (leastProgramLeftEvalRename i) := by
      rw [leastProgramValueLtLAssignment_val]
    _ = stackProgramEvalAssignment U.1 p.1 left.1 i := hraw
    _ = (stackProgramEvalCodeLAssignment U.1 p.1 left.1
          U.2 p.2 left.2 i).1 := by
      symm
      exact congrFun
        (stackProgramEvalCodeLAssignment_val
          U.1 p.1 left.1 U.2 p.2 left.2) i

theorem comp_leastProgramRightEvalRename_lCarrier
    (U relation left right p q : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (leastProgramValueLtLAssignment U relation left right) p) q
        (leastProgramRightEvalRename i)) =
      stackProgramEvalCodeLAssignment U.1 q.1 right.1
        U.2 q.2 right.2 := by
  funext i
  apply Subtype.ext
  have hraw := congrFun
    (comp_leastProgramRightEvalRename
      U.1 relation.1 left.1 right.1 p.1 q.1) i
  calc
    (snoc (snoc (leastProgramValueLtLAssignment U relation left right) p) q
        (leastProgramRightEvalRename i)).1 =
        snoc
          (fun j =>
            (snoc (leastProgramValueLtLAssignment U relation left right) p j).1)
          q.1 (leastProgramRightEvalRename i) :=
      congrFun
        (Model.subtypeVal_snoc
          (snoc (leastProgramValueLtLAssignment U relation left right) p) q)
        (leastProgramRightEvalRename i)
    _ = snoc
          (snoc
            (fun j =>
              (leastProgramValueLtLAssignment U relation left right j).1)
            p.1) q.1 (leastProgramRightEvalRename i) := by
      rw [Model.subtypeVal_snoc]
    _ = snoc
          (snoc
            (leastProgramValueLtAssignment U.1 relation.1 left.1 right.1)
            p.1) q.1 (leastProgramRightEvalRename i) := by
      rw [leastProgramValueLtLAssignment_val]
    _ = stackProgramEvalAssignment U.1 q.1 right.1 i := hraw
    _ = (stackProgramEvalCodeLAssignment U.1 q.1 right.1
          U.2 q.2 right.2 i).1 := by
      symm
      exact congrFun
        (stackProgramEvalCodeLAssignment_val
          U.1 q.1 right.1 U.2 q.2 right.2) i

theorem comp_leastProgramOrderRename_lCarrier
    (U relation left right p q : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (leastProgramValueLtLAssignment U relation left right) p) q
        (leastProgramOrderRename i)) =
      stackProgramLtCodeLAssignment U.1 relation.1 p.1 q.1
        U.2 relation.2 p.2 q.2 := by
  funext i
  apply Subtype.ext
  have hraw := congrFun
    (comp_leastProgramOrderRename
      U.1 relation.1 left.1 right.1 p.1 q.1) i
  calc
    (snoc (snoc (leastProgramValueLtLAssignment U relation left right) p) q
        (leastProgramOrderRename i)).1 =
        snoc
          (fun j =>
            (snoc (leastProgramValueLtLAssignment U relation left right) p j).1)
          q.1 (leastProgramOrderRename i) :=
      congrFun
        (Model.subtypeVal_snoc
          (snoc (leastProgramValueLtLAssignment U relation left right) p) q)
        (leastProgramOrderRename i)
    _ = snoc
          (snoc
            (fun j =>
              (leastProgramValueLtLAssignment U relation left right j).1)
            p.1) q.1 (leastProgramOrderRename i) := by
      rw [Model.subtypeVal_snoc]
    _ = snoc
          (snoc
            (leastProgramValueLtAssignment U.1 relation.1 left.1 right.1)
            p.1) q.1 (leastProgramOrderRename i) := by
      rw [leastProgramValueLtLAssignment_val]
    _ = rawStackProgramLtAssignment U.1 relation.1 p.1 q.1 i := hraw
    _ = stackProgramLtCodeAssignment U.1 relation.1 p.1 q.1 i := by
      rw [rawStackProgramLtAssignment_eq_codeAssignment]
    _ = (stackProgramLtCodeLAssignment U.1 relation.1 p.1 q.1
          U.2 relation.2 p.2 q.2 i).1 := by
      symm
      exact congrFun
        (stackProgramLtCodeLAssignment_val U.1 relation.1 p.1 q.1
          U.2 relation.2 p.2 q.2) i

/-! ## Constructible values of the definability step -/

/-- Every member of `godelDef U` is constructible when `U` is. -/
theorem defCarrier_val_mem_L (U : Model.LCarrier.{u})
    (x : DefCarrier U.1) : x.1 ∈ L := by
  rcases (mem_godelDef_iff_exists_rudimentaryTerm.mp x.2).2 with
    ⟨term, hterm⟩
  rw [← hterm]
  exact term.eval_mem_L U.2

/-- Regard a definability-step value as an element of `LCarrier`. -/
def defCarrierToLCarrier (U : Model.LCarrier.{u})
    (x : DefCarrier U.1) : Model.LCarrier.{u} :=
  ⟨x.1, defCarrier_val_mem_L U x⟩

@[simp]
theorem defCarrierToLCarrier_val (U : Model.LCarrier.{u})
    (x : DefCarrier U.1) :
    (defCarrierToLCarrier U x).1 = x.1 := rfl

/-! ## Exact restricted semantics -/

/-- In `LCarrier`, the formula is exactly the successful-program relation. -/
@[simp]
theorem satisfies_leastProgramValueLtFormula_lCarrier_iff_successful
    (U relation : Model.LCarrier.{u}) (x y : DefCarrier U.1) :
    FOFormula.Satisfies LMem leastProgramValueLtFormula
        (leastProgramValueLtLAssignment U relation
          (defCarrierToLCarrier U x) (defCarrierToLCarrier U y)) ↔
      successfulProgramValueRel U.1 relation.1 x y := by
  simp only [leastProgramValueLtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_rename,
    satisfies_formulaImp, comp_leastProgramLeftEvalRename_lCarrier,
    comp_leastProgramRightEvalRename_lCarrier,
    comp_leastProgramOrderRename_lCarrier,
    successfulProgramValueRel]
  constructor
  · rintro ⟨pCode, hpEval, hpBelow⟩
    rcases satisfies_stackProgramEvalFormula_code_lCarrier_to_exists_run
        U.1 pCode.1 x.1 U.2 pCode.2 (defCarrier_val_mem_L U x)
        hpEval with
      ⟨program, hpRepresents, hpRun⟩
    refine ⟨program, hpRun, ?_⟩
    intro other hotherRun
    let otherCode : Model.LCarrier.{u} :=
      ⟨stackProgramZFCode U.1 other,
        stackProgramZFCode_mem_L U.2 other⟩
    have hotherEval :
        FOFormula.Satisfies LMem stackProgramEvalFormula
          (stackProgramEvalCodeLAssignment U.1 otherCode.1 y.1
            U.2 otherCode.2 (defCarrier_val_mem_L U y)) := by
      simpa only [otherCode, stackProgramEvalCodeLAssignment,
        stackProgramEvalLAssignment] using
        (satisfies_stackProgramEvalFormula_lCarrier_of_run
          U.1 U.2 other y.1 (defCarrier_val_mem_L U y) hotherRun)
    have hlt := hpBelow otherCode hotherEval
    exact (satisfies_stackProgramLtFormula_represents_lCarrier_iff
      U.1 relation.1 pCode.1 otherCode.1 U.2 relation.2
      pCode.2 otherCode.2 program other hpRepresents
      (represents_sequenceCode _)).mp hlt
  · rintro ⟨program, hprogramRun, hbelow⟩
    let programCode : Model.LCarrier.{u} :=
      ⟨stackProgramZFCode U.1 program,
        stackProgramZFCode_mem_L U.2 program⟩
    refine ⟨programCode, ?_, ?_⟩
    · have heval :=
        satisfies_stackProgramEvalFormula_lCarrier_of_run
          U.1 U.2 program x.1 (defCarrier_val_mem_L U x) hprogramRun
      change FOFormula.Satisfies LMem stackProgramEvalFormula
        (stackProgramEvalCodeLAssignment U.1 programCode.1
          (defCarrierToLCarrier U x).1 U.2 programCode.2
          (defCarrierToLCarrier U x).2) at heval
      exact heval
    · intro qCode hqEval
      rcases satisfies_stackProgramEvalFormula_code_lCarrier_to_exists_run
          U.1 qCode.1 y.1 U.2 qCode.2 (defCarrier_val_mem_L U y)
          hqEval with
        ⟨other, hqRepresents, hotherRun⟩
      exact (satisfies_stackProgramLtFormula_represents_lCarrier_iff
        U.1 relation.1 programCode.1 qCode.1 U.2 relation.2
        programCode.2 qCode.2 program other
        (represents_sequenceCode _) hqRepresents).mpr
          (hbelow other hotherRun)



end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule78



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageInternalOrder -/
section CUAdapterModule79
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# From internally represented stage orders to Choice

Every constructible set is contained in some level `L_alpha`.  Consequently,
it is enough to construct, for every level, a well-order whose Kuratowski-pair
graph is itself a member of `L`.  This file proves that reduction and states
the exact internalization obligation for the external birth-layer order from
`StageOrder`.
-/


open Set

universe u

namespace Constructible

namespace Model

/-- Include an element of one level into the full constructible carrier. -/
def stageToLCarrier (alpha : Ordinal.{u})
    (x : LStageCarrier alpha) : LCarrier.{u} :=
  ⟨x.1, LStageZF_subset_constructibleUniverse alpha x.2⟩

@[simp]
theorem stageToLCarrier_val (alpha : Ordinal.{u})
    (x : LStageCarrier alpha) :
    (stageToLCarrier alpha x).1 = x.1 :=
  rfl

/-- The relation induced on `L_alpha` by a constructible pair graph. -/
def stageGraphRel (r : LCarrier.{u}) (alpha : Ordinal.{u}) :
    LStageCarrier alpha -> LStageCarrier alpha -> Prop :=
  fun x y => GraphRel r (stageToLCarrier alpha x)
    (stageToLCarrier alpha y)

/-- A level has a well-order represented by an actual constructible graph. -/
def StageInternallyWellOrdered (alpha : Ordinal.{u}) : Prop :=
  exists r : LCarrier.{u},
    IsWellOrder (LStageCarrier alpha) (stageGraphRel r alpha)

/-- Every level has a constructibly represented well-order. -/
def AllStagesInternallyWellOrdered : Prop :=
  forall alpha : Ordinal.{u}, StageInternallyWellOrdered alpha









/-! ## Alternative conditional birth-layer route

This section gives a conditional reduction through an externally specified
birth-layer order. The model theorem in `StageHistoryGraphSystem.lean` is
independent of this interface and constructs coherent internal graphs through
stage histories.
-/











end Model

end Constructible
end CUAdapterModule79



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentarySuccessorInternalOrder -/
section CUAdapterModule80
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Internally represented well-orders of successor stages

Assume an actual constructible graph internally well-orders `L_alpha`.
The fixed least-successful-program formula then well-orders
`L_(alpha+1) = Def(L_alpha)`.  Full Separation turns that formula-defined
relation into an actual Kuratowski graph belonging to `L`.
-/


universe u

namespace Constructible

namespace Model

noncomputable section

/-- A constructible stage packaged as an element of `LCarrier`. -/
def stageLCarrier (alpha : Ordinal.{u}) : LCarrier.{u} :=
  ⟨LStageZF alpha, LStageZF_mem_L alpha⟩

@[simp]
theorem stageLCarrier_val (alpha : Ordinal.{u}) :
    (stageLCarrier alpha).1 = LStageZF alpha := rfl

/-- The internal carrier of the successor stage is the corresponding
Gödel-definability carrier. -/
def successorDefCarrierEquiv (alpha : Ordinal.{u}) :
    InternalCarrier (stageLCarrier (Order.succ alpha)) ≃
      Godel.DefCarrier (LStageZF alpha) where
  toFun x :=
    ⟨x.1.1, by
      simpa only [stageLCarrier, LStageZF_succ,
        Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)] using x.2⟩
  invFun x :=
    let hx : x.1 ∈ LStageZF (Order.succ alpha) := by
      simpa only [LStageZF_succ,
        Godel.DefZF_eq_godelDef (LStageZF_isTransitive alpha)] using x.2
    ⟨⟨x.1, LStageZF_subset_constructibleUniverse
        (Order.succ alpha) hx⟩, hx⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

@[simp]
theorem successorDefCarrierEquiv_val (alpha : Ordinal.{u})
    (x : InternalCarrier (stageLCarrier (Order.succ alpha))) :
    (successorDefCarrierEquiv alpha x).1 = x.1.1 := rfl

/-- The formula parameters induced by a represented order on `L_alpha`. -/
def successorProgramOrderParameters (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) : Tuple LCarrier.{u} 15 :=
  Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
    (stageLCarrier alpha) relation









end

end Model

end Constructible
end CUAdapterModule80



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentarySuccessorExtensionOrder -/
section CUAdapterModule81
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Coherent internally represented successor-stage orders

The raw least-program order need not extend the order on the previous stage.
For limit unions we instead put the old stage first, preserving its given
relation, and order only the genuinely new values by least successful
programs.  The old stage is therefore an initial segment by construction.
-/


universe u

namespace Constructible

namespace Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## The fixed extension formula -/

/-- The universe parameter in the seventeen-coordinate layout. -/
def successorUniverseIndex : Fin 17 :=
  (0 : Fin 13).castSucc.castSucc.castSucc.castSucc

/-- The inherited relation parameter in the seventeen-coordinate layout. -/
def successorRelationIndex : Fin 17 :=
  (Fin.last 14).castSucc.castSucc

/-- The left compared value in the seventeen-coordinate layout. -/
def successorLeftIndex : Fin 17 :=
  (Fin.last 15).castSucc

/-- The right compared value in the seventeen-coordinate layout. -/
def successorRightIndex : Fin 17 :=
  Fin.last 16

/-- Select `[relation, left, right]` from the seventeen-coordinate layout. -/
def successorRelationGraphRename : Fin 3 -> Fin 17 :=
  ![successorRelationIndex, successorLeftIndex, successorRightIndex]

theorem comp_successorRelationGraphRename
    (U relation left right : LCarrier.{u}) :
    (fun i =>
      Godel.RudimentaryTerm.leastProgramValueLtLAssignment
        U relation left right (successorRelationGraphRename i)) =
      ![relation, left, right] := by
  funext i
  fin_cases i <;> rfl

/--
On `Def(U)`, preserve `relation` on old values, put every old value before
every new value, and compare two new values by least successful programs.
-/
def successorExtensionLtFormula : FOFormula 17 :=
  let leftInU : FOFormula 17 :=
    .mem successorLeftIndex successorUniverseIndex
  let rightInU : FOFormula 17 :=
    .mem successorRightIndex successorUniverseIndex
  let oldGraph : FOFormula 17 :=
    FOFormula.rename successorRelationGraphRename graphRelFormula
  FOFormula.disj
    (.conj leftInU (.conj rightInU oldGraph))
    (FOFormula.disj
      (.conj leftInU (.neg rightInU))
      (.conj (.neg leftInU)
        (.conj (.neg rightInU)
          Godel.RudimentaryTerm.leastProgramValueLtFormula)))

@[simp]
theorem satisfies_successorExtensionLtFormula
    (U relation left right : LCarrier.{u}) :
    FOFormula.Satisfies LMem successorExtensionLtFormula
        (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
          U relation left right) ↔
      (left.1 ∈ U.1 ∧ right.1 ∈ U.1 ∧
          GraphRel relation left right) ∨
      (left.1 ∈ U.1 ∧ right.1 ∉ U.1) ∨
      (left.1 ∉ U.1 ∧ right.1 ∉ U.1 ∧
        FOFormula.Satisfies LMem
          Godel.RudimentaryTerm.leastProgramValueLtFormula
          (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
            U relation left right)) := by
  have hUCoord :
      Godel.RudimentaryTerm.leastProgramValueLtLAssignment
        U relation left right successorUniverseIndex = U := by
    simp [successorUniverseIndex,
      Godel.RudimentaryTerm.leastProgramValueLtLAssignment,
      Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment,
      Godel.RudimentaryTerm.stackStepPrefixLAssignment,
      Model.snoc_eq_finSnoc]
  have hleftCoord :
      Godel.RudimentaryTerm.leastProgramValueLtLAssignment
        U relation left right successorLeftIndex = left := by
    change snoc
      (snoc
        (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
          U relation) left) right (Fin.last 15).castSucc = left
    rw [snoc_castSucc, snoc_last]
  have hrightCoord :
      Godel.RudimentaryTerm.leastProgramValueLtLAssignment
        U relation left right successorRightIndex = right := by
    change snoc
      (snoc
        (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
          U relation) left) right (Fin.last 16) = right
    rw [snoc_last]
  simp only [successorExtensionLtFormula, FOFormula.satisfies_disj,
    FOFormula.Satisfies, FOFormula.satisfies_rename,
    comp_successorRelationGraphRename, satisfies_graphRelFormula,
    hUCoord, hleftCoord, hrightCoord]
  rfl

/-! ## The corresponding external block order -/

/-- The predicate identifying the old part of the successor carrier. -/
def successorIsOld (alpha : Ordinal.{u})
    (x : InternalCarrier (stageLCarrier (Order.succ alpha))) : Prop :=
  x.1.1 ∈ LStageZF alpha

/-- The old block is canonically the internal carrier of `L_alpha`. -/
def successorOldPartEquiv (alpha : Ordinal.{u}) :
    {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
      successorIsOld alpha x} ≃
      InternalCarrier (stageLCarrier alpha) where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x :=
    ⟨⟨x.1, LStageZF_subset_succ alpha x.2⟩, x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- The old block uses exactly the supplied internal graph relation. -/
def successorOldBlockRel (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) :
    {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
      successorIsOld alpha x} ->
    {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
      successorIsOld alpha x} -> Prop :=
  InvImage (graphRelOn relation (stageLCarrier alpha))
    (successorOldPartEquiv alpha)

/-- The new block is the restriction of the successful-program order. -/
def successorNewBlockRel (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) :
    {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
      Not (successorIsOld alpha x)} ->
    {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
      Not (successorIsOld alpha x)} -> Prop :=
  InvImage
    (Godel.RudimentaryTerm.successfulProgramValueRel
      (LStageZF alpha) relation.1)
    (fun x => successorDefCarrierEquiv alpha x.1)

/-- The coherent old-before-new relation on the successor carrier. -/
def successorExtensionRel (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) :
    InternalCarrier (stageLCarrier (Order.succ alpha)) ->
      InternalCarrier (stageLCarrier (Order.succ alpha)) -> Prop :=
  partitionLexRel (successorIsOld alpha)
    (successorOldBlockRel alpha relation)
    (successorNewBlockRel alpha relation)

theorem successorOldBlockRel_isWellOrder
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    IsWellOrder
      {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
        successorIsOld alpha x}
      (successorOldBlockRel alpha relation) := by
  letI : IsWellOrder (InternalCarrier (stageLCarrier alpha))
      (graphRelOn relation (stageLCarrier alpha)) := hwell
  exact
    { wf := InvImage.wf (successorOldPartEquiv alpha)
        (IsWellFounded.wf : WellFounded
          (graphRelOn relation (stageLCarrier alpha)))
      trichotomous :=
        (InvImage.trichotomous
          (r := graphRelOn relation (stageLCarrier alpha))
          (successorOldPartEquiv alpha).injective).trichotomous }

theorem successorNewBlockRel_isWellOrder
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    IsWellOrder
      {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
        Not (successorIsOld alpha x)}
      (successorNewBlockRel alpha relation) := by
  letI : IsWellOrder (Godel.DefCarrier (LStageZF alpha))
      (Godel.RudimentaryTerm.successfulProgramValueRel
        (LStageZF alpha) relation.1) :=
    Godel.RudimentaryTerm.successfulProgramValueRel_isWellOrder_of_internal
      (stageLCarrier alpha) relation hwell
  let embedding :
      {x : InternalCarrier (stageLCarrier (Order.succ alpha)) //
        Not (successorIsOld alpha x)} ->
        Godel.DefCarrier (LStageZF alpha) :=
    fun x => successorDefCarrierEquiv alpha x.1
  have hinjective : Function.Injective
      embedding := by
    intro x y hxy
    apply Subtype.ext
    exact (successorDefCarrierEquiv alpha).injective hxy
  change IsWellOrder _ (InvImage
    (Godel.RudimentaryTerm.successfulProgramValueRel
      (LStageZF alpha) relation.1) embedding)
  exact
    { wf := InvImage.wf
        embedding
        (IsWellFounded.wf : WellFounded
          (Godel.RudimentaryTerm.successfulProgramValueRel
            (LStageZF alpha) relation.1))
      trichotomous :=
        (InvImage.trichotomous
          (r := Godel.RudimentaryTerm.successfulProgramValueRel
            (LStageZF alpha) relation.1)
          hinjective).trichotomous }

theorem successorExtensionRel_isWellOrder
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    IsWellOrder
      (InternalCarrier (stageLCarrier (Order.succ alpha)))
      (successorExtensionRel alpha relation) := by
  letI := successorOldBlockRel_isWellOrder alpha relation hwell
  letI := successorNewBlockRel_isWellOrder alpha relation hwell
  exact partitionLexRel_isWellOrder
    (successorIsOld alpha)
    (successorOldBlockRel alpha relation)
    (successorNewBlockRel alpha relation)

/-! ## Formula semantics and internalization -/

 theorem successorLeastFormula_iff_successful
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (x y : InternalCarrier (stageLCarrier (Order.succ alpha))) :
    FOFormula.Satisfies LMem
        Godel.RudimentaryTerm.leastProgramValueLtFormula
        (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
          (stageLCarrier alpha) relation x.1 y.1) ↔
      Godel.RudimentaryTerm.successfulProgramValueRel
        (LStageZF alpha) relation.1
        (successorDefCarrierEquiv alpha x)
        (successorDefCarrierEquiv alpha y) := by
  let U := stageLCarrier alpha
  let xL := Godel.RudimentaryTerm.defCarrierToLCarrier U
    (successorDefCarrierEquiv alpha x)
  let yL := Godel.RudimentaryTerm.defCarrierToLCarrier U
    (successorDefCarrierEquiv alpha y)
  have hxL : x.1 = xL := by
    apply Subtype.ext
    rfl
  have hyL : y.1 = yL := by
    apply Subtype.ext
    rfl
  rw [hxL, hyL]
  exact
    Godel.RudimentaryTerm.satisfies_leastProgramValueLtFormula_lCarrier_iff_successful
      U relation (successorDefCarrierEquiv alpha x)
        (successorDefCarrierEquiv alpha y)

theorem successorExtensionFormulaRel_eq
    (alpha : Ordinal.{u}) (relation : LCarrier.{u}) :
    formulaRelOn successorExtensionLtFormula
        (successorProgramOrderParameters alpha relation)
        (stageLCarrier (Order.succ alpha)) =
      successorExtensionRel alpha relation := by
  funext x y
  apply propext
  change
    FOFormula.Satisfies LMem successorExtensionLtFormula
        (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
          (stageLCarrier alpha) relation x.1 y.1) ↔
      successorExtensionRel alpha relation x y
  rw [satisfies_successorExtensionLtFormula]
  by_cases hx : successorIsOld alpha x
  · by_cases hy : successorIsOld alpha y
    · have hxRaw : x.1.1 ∈ LStageZF alpha := hx
      have hyRaw : y.1.1 ∈ LStageZF alpha := hy
      rw [successorExtensionRel,
        partitionLexRel_old_old (successorIsOld alpha)
          (successorOldBlockRel alpha relation)
          (successorNewBlockRel alpha relation) hx hy]
      change
        ((x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∈ LStageZF alpha ∧
            GraphRel relation x.1 y.1) ∨
          (x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha) ∨
          (x.1.1 ∉ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha ∧ _)) ↔
        GraphRel relation x.1 y.1
      simp [hxRaw, hyRaw]
    · have hxRaw : x.1.1 ∈ LStageZF alpha := hx
      have hyRaw : y.1.1 ∉ LStageZF alpha := hy
      have hrel := partitionLexRel_old_new
        (successorIsOld alpha)
        (successorOldBlockRel alpha relation)
        (successorNewBlockRel alpha relation) hx hy
      change
        ((x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∈ LStageZF alpha ∧ _) ∨
          (x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha) ∨
          (x.1.1 ∉ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha ∧ _)) ↔
        successorExtensionRel alpha relation x y
      simp [hxRaw, hyRaw]
      simpa only [successorExtensionRel] using hrel
  · by_cases hy : successorIsOld alpha y
    · have hxRaw : x.1.1 ∉ LStageZF alpha := hx
      have hyRaw : y.1.1 ∈ LStageZF alpha := hy
      have hrel := partitionLexRel_new_old
        (successorIsOld alpha)
        (successorOldBlockRel alpha relation)
        (successorNewBlockRel alpha relation) hx hy
      change
        ((x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∈ LStageZF alpha ∧ _) ∨
          (x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha) ∨
          (x.1.1 ∉ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha ∧ _)) ↔
        successorExtensionRel alpha relation x y
      simp [hxRaw, hyRaw]
      simpa only [successorExtensionRel] using hrel
    · have hxRaw : x.1.1 ∉ LStageZF alpha := hx
      have hyRaw : y.1.1 ∉ LStageZF alpha := hy
      rw [successorLeastFormula_iff_successful]
      rw [successorExtensionRel,
        partitionLexRel_new_new (successorIsOld alpha)
          (successorOldBlockRel alpha relation)
          (successorNewBlockRel alpha relation) hx hy]
      change
        ((x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∈ LStageZF alpha ∧ _) ∨
          (x.1.1 ∈ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha) ∨
          (x.1.1 ∉ LStageZF alpha ∧ y.1.1 ∉ LStageZF alpha ∧
            Godel.RudimentaryTerm.successfulProgramValueRel
              (LStageZF alpha) relation.1
              (successorDefCarrierEquiv alpha x)
              (successorDefCarrierEquiv alpha y))) ↔
        Godel.RudimentaryTerm.successfulProgramValueRel
          (LStageZF alpha) relation.1
          (successorDefCarrierEquiv alpha x)
          (successorDefCarrierEquiv alpha y)
      simp [hxRaw, hyRaw]

theorem successorExtensionFormulaRel_isWellOrder
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    IsWellOrder
      (InternalCarrier (stageLCarrier (Order.succ alpha)))
      (formulaRelOn successorExtensionLtFormula
        (successorProgramOrderParameters alpha relation)
        (stageLCarrier (Order.succ alpha))) := by
  rw [successorExtensionFormulaRel_eq]
  exact successorExtensionRel_isWellOrder alpha relation hwell

/-- The data retained from a coherent successor-stage graph. -/
structure SuccessorOrderExtension (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) where
  /-- The relation extending the well-order to the successor stage. -/
  nextRelation : LCarrier.{u}
  wellOrders : InternallyWellOrders nextRelation
    (stageLCarrier (Order.succ alpha))
  supported : ∀ x y : LCarrier.{u}, GraphRel nextRelation x y ->
    x.1 ∈ LStageZF (Order.succ alpha) ∧
      y.1 ∈ LStageZF (Order.succ alpha)
  agreesOnOld : ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF alpha -> y.1 ∈ LStageZF alpha ->
      (GraphRel nextRelation x y ↔ GraphRel relation x y)
  oldIsInitial : ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF alpha ->
      y.1 ∈ LStageZF (Order.succ alpha) ->
        GraphRel nextRelation y x -> y.1 ∈ LStageZF alpha





end

end Model

end Constructible
end CUAdapterModule81



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalSuccessorOrder -/
section CUAdapterModule82
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The canonical coherent successor-stage order

The successor extension formula determines an exact graph by Separation in
the constructible Cartesian square.  Unlike an existential graph witness,
this graph is a genuine function of the preceding stage and relation, which
is the form used by the transfinite recursion.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-- The canonical constructible graph extending the order on `L_alpha`. -/
def canonicalSuccessorRelation (alpha : Ordinal.{u})
    (relation : LCarrier.{u}) : LCarrier.{u} :=
  canonicalDefinableRelationGraph successorExtensionLtFormula
    (successorProgramOrderParameters alpha relation)
    (stageLCarrier (Order.succ alpha))

/-- Object-language specification of the exact coherent successor graph.
Its layout is `(fifteen program parameters, successor domain, output)`. -/
def canonicalSuccessorOutputFormula : FOFormula 17 :=
  canonicalGraphOutputFormula successorExtensionLtFormula





@[simp]
theorem graphRel_canonicalSuccessorRelation_iff
    (alpha : Ordinal.{u}) (relation x y : LCarrier.{u}) :
    GraphRel (canonicalSuccessorRelation alpha relation) x y ↔
      x.1 ∈ LStageZF (Order.succ alpha) ∧
        y.1 ∈ LStageZF (Order.succ alpha) ∧
          FOFormula.Satisfies LMem successorExtensionLtFormula
            (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
              (stageLCarrier alpha) relation x y) := by
  have h := graphRel_canonicalDefinableRelationGraph_iff
    successorExtensionLtFormula
    (successorProgramOrderParameters alpha relation)
    (stageLCarrier (Order.succ alpha)) x y
  change
    GraphRel (canonicalSuccessorRelation alpha relation) x y ↔
      x.1 ∈ LStageZF (Order.succ alpha) ∧
        y.1 ∈ LStageZF (Order.succ alpha) ∧
          FOFormula.Satisfies LMem successorExtensionLtFormula
            (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
              (stageLCarrier alpha) relation x y) at h
  exact h

/-- The canonical graph has no members other than the intended ordered
pairs, a stronger specification than merely agreeing through `GraphRel`. -/
@[simp]
theorem mem_canonicalSuccessorRelation_iff
    (alpha : Ordinal.{u}) (relation q : LCarrier.{u}) :
    q.1 ∈ (canonicalSuccessorRelation alpha relation).1 ↔
      ∃ x y : LCarrier.{u},
        x.1 ∈ LStageZF (Order.succ alpha) ∧
          y.1 ∈ LStageZF (Order.succ alpha) ∧
            q.1 = ZFSet.pair x.1 y.1 ∧
              FOFormula.Satisfies LMem successorExtensionLtFormula
                (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
                  (stageLCarrier alpha) relation x y) := by
  have h := mem_canonicalDefinableRelationGraph_iff
    successorExtensionLtFormula
    (successorProgramOrderParameters alpha relation)
    (stageLCarrier (Order.succ alpha)) q
  change
    q.1 ∈ (canonicalSuccessorRelation alpha relation).1 ↔
      ∃ x y : LCarrier.{u},
        x.1 ∈ LStageZF (Order.succ alpha) ∧
          y.1 ∈ LStageZF (Order.succ alpha) ∧
            q.1 = ZFSet.pair x.1 y.1 ∧
              FOFormula.Satisfies LMem successorExtensionLtFormula
                (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
                  (stageLCarrier alpha) relation x y) at h
  exact h

/-- If the old graph well-orders `L_alpha`, the canonical successor graph is
the coherent extension constructed by the successor formula. -/
def canonicalSuccessorOrderExtension
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    SuccessorOrderExtension alpha relation where
  nextRelation := canonicalSuccessorRelation alpha relation
  wellOrders := by
    have heq :
        graphRelOn (canonicalSuccessorRelation alpha relation)
            (stageLCarrier (Order.succ alpha)) =
          formulaRelOn successorExtensionLtFormula
            (successorProgramOrderParameters alpha relation)
            (stageLCarrier (Order.succ alpha)) := by
      funext x y
      apply propext
      change
        GraphRel (canonicalSuccessorRelation alpha relation) x.1 y.1 ↔
          FOFormula.Satisfies LMem successorExtensionLtFormula
            (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
              (stageLCarrier alpha) relation x.1 y.1)
      have hx : x.1.1 ∈ LStageZF (Order.succ alpha) := x.2
      have hy : y.1.1 ∈ LStageZF (Order.succ alpha) := y.2
      simpa only [hx, hy, true_and] using
        (graphRel_canonicalSuccessorRelation_iff
          alpha relation x.1 y.1)
    rw [InternallyWellOrders, heq]
    exact successorExtensionFormulaRel_isWellOrder alpha relation hwell
  supported := by
    intro x y hxy
    have hsupported := (graphRel_canonicalSuccessorRelation_iff
      alpha relation x y).mp hxy
    exact ⟨hsupported.1, hsupported.2.1⟩
  agreesOnOld := by
    intro x y hx hy
    have hxSucc : x.1 ∈ LStageZF (Order.succ alpha) :=
      LStageZF_subset_succ alpha hx
    have hySucc : y.1 ∈ LStageZF (Order.succ alpha) :=
      LStageZF_subset_succ alpha hy
    rw [graphRel_canonicalSuccessorRelation_iff]
    simp only [hxSucc, hySucc, true_and]
    change
      FOFormula.Satisfies LMem successorExtensionLtFormula
          (Godel.RudimentaryTerm.leastProgramValueLtLAssignment
            (stageLCarrier alpha) relation x y) ↔
        GraphRel relation x y
    rw [satisfies_successorExtensionLtFormula]
    simp only [stageLCarrier_val, hx, hy, true_and, not_true,
      and_false, false_and, or_false]
  oldIsInitial := by
    intro x y hx hySucc hyx
    have hformula :=
      (graphRel_canonicalSuccessorRelation_iff
        alpha relation y x).mp hyx |>.2.2
    rcases (satisfies_successorExtensionLtFormula
        (stageLCarrier alpha) relation y x).mp hformula with
      hold | hold | hnew
    · exact hold.1
    · exact hold.1
    · exact (hnew.2.1 hx).elim

@[simp]
theorem canonicalSuccessorOrderExtension_nextRelation
    (alpha : Ordinal.{u}) (relation : LCarrier.{u})
    (hwell : InternallyWellOrders relation (stageLCarrier alpha)) :
    (canonicalSuccessorOrderExtension alpha relation hwell).nextRelation =
      canonicalSuccessorRelation alpha relation :=
  rfl

end

end Constructible.Model
end CUAdapterModule82



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryDefOutputFormula -/
section CUAdapterModule83
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A first-order output formula for one Gödel definability step

The fixed stack evaluator recognizes the rudimentary closure of `U`.  Adding
the bounded requirement that the output be a subset of `U` therefore gives a
single first-order definition of `godelDef U`.  This file packages that
definition with an exact `LCarrier` semantics and the unique-output interface
needed by function-form Replacement.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## Successful programs land in the rudimentary closure -/

/-- One stack-machine step preserves membership of every stack entry in the
rudimentary closure generated by `U`. -/
theorem runStackToken_preserves_rudimentaryClosure
    (U : ZFSet.{u})
    (token : StackToken (Option (Constructible.ZFCarrier U)))
    (stack next : List ZFSet.{u})
    (hstack : ∀ z ∈ stack, z ∈ rudimentaryClosure U)
    (hstep : runStackToken (rudimentaryGenerator U) token stack = some next) :
    ∀ z ∈ next, z ∈ rudimentaryClosure U := by
  cases token with
  | inl generator =>
      simp only [runStackToken, Option.some.injEq] at hstep
      subst next
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · cases generator with
        | none => exact self_mem_rudimentaryClosure U
        | some x => exact subset_rudimentaryClosure U x.2
      · exact hstack z hz
  | inr operation =>
      cases stack with
      | nil => simp [runStackToken] at hstep
      | cons right rest =>
          cases rest with
          | nil => simp [runStackToken] at hstep
          | cons left tail =>
              simp only [runStackToken, Option.some.injEq] at hstep
              subst next
              intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact op_mem_rudimentaryClosure
                  (hstack left (by simp)) (hstack right (by simp))
              · exact hstack z (by simp [hz])

/-- Executing a postfix program preserves the same closure invariant. -/
theorem runStackProgram_preserves_rudimentaryClosure
    (U : ZFSet.{u})
    (program : List (StackToken (Option (Constructible.ZFCarrier U))))
    (stack result : List ZFSet.{u})
    (hstack : ∀ z ∈ stack, z ∈ rudimentaryClosure U)
    (hrun : runStackProgram (rudimentaryGenerator U) program stack =
      some result) :
    ∀ z ∈ result, z ∈ rudimentaryClosure U := by
  induction program generalizing stack with
  | nil =>
      simp only [runStackProgram_nil, Option.some.injEq] at hrun
      subst result
      exact hstack
  | cons token program ih =>
      simp only [runStackProgram] at hrun
      cases hstep : runStackToken (rudimentaryGenerator U) token stack with
      | none => simp [hstep] at hrun
      | some next =>
          apply ih next
          · exact runStackToken_preserves_rudimentaryClosure
              U token stack next hstack hstep
          · simpa only [hstep, Option.bind_some] using hrun

/-- In particular, the singleton result of a successful program belongs to
the rudimentary closure. -/
theorem mem_rudimentaryClosure_of_runStackProgram
    (U : ZFSet.{u})
    (program : List (StackToken (Option (Constructible.ZFCarrier U))))
    (result : ZFSet.{u})
    (hrun : runStackProgram (rudimentaryGenerator U) program [] =
      some [result]) :
    result ∈ rudimentaryClosure U := by
  have hclosed := runStackProgram_preserves_rudimentaryClosure
    U program [] [result] (by simp) hrun
  exact hclosed result (by simp)

/-! ## The fixed output formula -/

/-
The outer free-variable layout is

`[U,varTag,appTag,empty,op0,...,op8,omega,nextU]`.

After universally binding `result` and existentially binding `program`, the
evaluator expects `program` before `result`.  The following renaming swaps
those two final coordinates and skips `nextU`.
-/

/-- Embed the evaluator layout under the output-extensionality quantifiers. -/
def godelDefEvalRename : Fin 16 → Fin 17 :=
  Fin.lastCases (15 : Fin 17)
    (fun i14 => Fin.lastCases (16 : Fin 17)
      (fun i13 => i13.castSucc.castSucc.castSucc) i14)

/--
`godelDefOutputFormula(U,...,nextU)` says that the members of `nextU` are
exactly the subsets of `U` computed by a successful rudimentary program.
-/
def godelDefOutputFormula : FOFormula 15 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (15 : Fin 16) (14 : Fin 16))
      (.conj
        (Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO
        (.ex (FOFormula.rename godelDefEvalRename
          stackProgramEvalFormula))))

/-- The constructible assignment for the output formula. -/
def godelDefOutputLAssignment
    (U nextU : Model.LCarrier.{u}) : Tuple Model.LCarrier.{u} 15 :=
  snoc
    (snoc (stackStepPrefixLAssignment U.1 U.2)
      ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
    nextU

theorem comp_godelDefEvalRename
    (U nextU result code : Model.LCarrier.{u}) :
    (fun i =>
      snoc (snoc (godelDefOutputLAssignment U nextU) result) code
        (godelDefEvalRename i)) =
      stackProgramEvalCodeLAssignment
        U.1 code.1 result.1 U.2 code.2 result.2 := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · simp only [godelDefEvalRename, Fin.lastCases_castSucc,
        godelDefOutputLAssignment, stackProgramEvalCodeLAssignment,
        snoc_castSucc]

 theorem satisfies_godelDefSubset
    (U nextU result : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO
        (snoc (godelDefOutputLAssignment U nextU) result) ↔
      result.1 ⊆ U.1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_subsetAt]
  change result.1 ⊆ U.1 ↔ result.1 ⊆ U.1
  rfl

/-- Direct semantic normal form of the output formula on `LCarrier`. -/
@[simp]
theorem satisfies_godelDefOutputFormula_components
    (U nextU : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem godelDefOutputFormula
        (godelDefOutputLAssignment U nextU) ↔
      ∀ result : Model.LCarrier.{u},
        result.1 ∈ nextU.1 ↔
          result.1 ⊆ U.1 ∧
            ∃ code : Model.LCarrier.{u},
              FOFormula.Satisfies LMem stackProgramEvalFormula
                (stackProgramEvalCodeLAssignment
                  U.1 code.1 result.1 U.2 code.2 result.2) := by
  simp only [godelDefOutputFormula, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp]
  apply forall_congr'
  intro result
  change
    (result.1 ∈ nextU.1 ↔
      FOFormula.Satisfies LMem
          (Delta0Formula.subsetAt (15 : Fin 16) (0 : Fin 16)).toFO
          (snoc (godelDefOutputLAssignment U nextU) result) ∧
        ∃ code : Model.LCarrier.{u},
          FOFormula.Satisfies LMem
            (FOFormula.rename godelDefEvalRename stackProgramEvalFormula)
            (snoc (snoc (godelDefOutputLAssignment U nextU) result) code)) ↔
      (result.1 ∈ nextU.1 ↔
        result.1 ⊆ U.1 ∧
          ∃ code : Model.LCarrier.{u},
            FOFormula.Satisfies LMem stackProgramEvalFormula
              (stackProgramEvalCodeLAssignment
                U.1 code.1 result.1 U.2 code.2 result.2))
  rw [satisfies_godelDefSubset]
  simp only [FOFormula.satisfies_rename, comp_godelDefEvalRename]

/-! ## Exactness and uniqueness -/

/-- Internal evaluator witnesses are exactly membership in the rudimentary
closure, for constructible `U` and result. -/
theorem exists_internalProgram_iff_mem_rudimentaryClosure
    (U result : Model.LCarrier.{u}) :
    (∃ code : Model.LCarrier.{u},
      FOFormula.Satisfies LMem stackProgramEvalFormula
        (stackProgramEvalCodeLAssignment
          U.1 code.1 result.1 U.2 code.2 result.2)) ↔
      result.1 ∈ rudimentaryClosure U.1 := by
  constructor
  · rintro ⟨code, heval⟩
    rcases satisfies_stackProgramEvalFormula_code_lCarrier_to_exists_run
        U.1 code.1 result.1 U.2 code.2 result.2 heval with
      ⟨program, _hrep, hrun⟩
    exact mem_rudimentaryClosure_of_runStackProgram U.1 program result.1 hrun
  · intro hresult
    rcases (mem_rudimentaryClosure_iff_exists_term.mp hresult) with
      ⟨term, hterm⟩
    let program := stackProgram term
    let code : Model.LCarrier.{u} :=
      ⟨stackProgramZFCode U.1 program,
        stackProgramZFCode_mem_L U.2 program⟩
    refine ⟨code, ?_⟩
    apply satisfies_stackProgramEvalFormula_lCarrier_of_run
    simp only [program, run_stackProgram, hterm]

/-- Satisfaction defines precisely the internally represented Gödel
definability layer. -/
theorem satisfies_godelDefOutputFormula_iff
    (U nextU : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem godelDefOutputFormula
        (godelDefOutputLAssignment U nextU) ↔
      nextU.1 = godelDef U.1 := by
  rw [satisfies_godelDefOutputFormula_components]
  constructor
  · intro h
    apply ZFSet.ext
    intro result
    constructor
    · intro hnext
      let resultL : Model.LCarrier.{u} :=
        ⟨result, mem_L_of_mem hnext nextU.2⟩
      have hdescription := (h resultL).mp hnext
      exact mem_godelDef_iff.mpr
        ⟨hdescription.1,
          (exists_internalProgram_iff_mem_rudimentaryClosure
            U resultL).mp hdescription.2⟩
    · intro hgodel
      have hclosure : result ∈ rudimentaryClosure U.1 :=
        (mem_godelDef_iff.mp hgodel).2
      have hresultL : result ∈ L := by
        rcases mem_rudimentaryClosure_iff_exists_term.mp hclosure with
          ⟨term, rfl⟩
        exact RudimentaryClosureTerm.eval_mem_L U.2 term
      let resultL : Model.LCarrier.{u} := ⟨result, hresultL⟩
      apply (h resultL).mpr
      exact
        ⟨(mem_godelDef_iff.mp hgodel).1,
          (exists_internalProgram_iff_mem_rudimentaryClosure
            U resultL).mpr hclosure⟩
  · intro hnext result
    rw [hnext, mem_godelDef_iff,
      exists_internalProgram_iff_mem_rudimentaryClosure]





end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule83



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.SuccessorStageStateFormula -/
section CUAdapterModule84
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A deterministic first-order successor step for stage/order states

A recursion state consists of a constructible domain `U` and a constructible
relation graph `oldRelation`.  Its successor consists of `nextU = godelDef U`
and the canonical graph selected by the coherent successor-order formula on
`nextU`.  Both outputs are specified by one fixed first-order formula.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-! ## Formula and assignments -/

/-
The combined layout is

`[U,varTag,appTag,empty,op0,...,op8,omega,oldRelation,nextU,nextRelation]`.

The `godelDef` output formula omits coordinates `oldRelation` and
`nextRelation`; its final output coordinate is therefore sent to `nextU`.
-/

/-- Embed the fifteen-coordinate definability-step output formula into the
seventeen-coordinate successor-state layout. -/
def successorStageGodelDefRename : Fin 15 → Fin 17 :=
  Fin.lastCases (15 : Fin 17)
    (fun i14 => i14.castSucc.castSucc.castSucc)

/-- The fixed first-order graph of one complete successor-state transition. -/
def successorStageStateFormula : FOFormula 17 :=
  .conj
    (FOFormula.rename successorStageGodelDefRename
      Godel.RudimentaryTerm.godelDefOutputFormula)
    canonicalSuccessorOutputFormula

/-- The intended constructible assignment to the combined formula. -/
def successorStageStateLAssignment
    (U oldRelation nextU nextRelation : LCarrier.{u}) :
    Tuple LCarrier.{u} 17 :=
  snoc
    (snoc
      (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
        U oldRelation)
      nextU)
    nextRelation

theorem comp_successorStageGodelDefRename
    (U oldRelation nextU nextRelation : LCarrier.{u}) :
    (fun i => successorStageStateLAssignment
      U oldRelation nextU nextRelation (successorStageGodelDefRename i)) =
      Godel.RudimentaryTerm.godelDefOutputLAssignment U nextU := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · simp only [successorStageGodelDefRename,
      Fin.lastCases_castSucc, successorStageStateLAssignment,
      Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment,
      Godel.RudimentaryTerm.godelDefOutputLAssignment,
      snoc_castSucc]

/-- The canonical graph determined by arbitrary predecessor and successor
domains in the state-transition layout. -/
def canonicalSuccessorStateRelation
    (U oldRelation nextU : LCarrier.{u}) : LCarrier.{u} :=
  canonicalDefinableRelationGraph successorExtensionLtFormula
    (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
      U oldRelation)
    nextU

/-! ## Exact semantics -/

/-- Satisfaction of the combined formula is exactly the intended pair of
output equations. -/
@[simp]
theorem satisfies_successorStageStateFormula_iff
    (U oldRelation nextU nextRelation : LCarrier.{u}) :
    FOFormula.Satisfies LMem successorStageStateFormula
        (successorStageStateLAssignment
          U oldRelation nextU nextRelation) ↔
      nextU.1 = Godel.godelDef U.1 ∧
        nextRelation =
          canonicalSuccessorStateRelation U oldRelation nextU := by
  rw [successorStageStateFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename,
    comp_successorStageGodelDefRename,
    Godel.RudimentaryTerm.satisfies_godelDefOutputFormula_iff]
  change
    nextU.1 = Godel.godelDef U.1 ∧
      FOFormula.Satisfies LMem
        (canonicalGraphOutputFormula successorExtensionLtFormula)
        (snoc
          (snoc
            (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
              U oldRelation)
            nextU)
          nextRelation) ↔
      nextU.1 = Godel.godelDef U.1 ∧
        nextRelation =
          canonicalDefinableRelationGraph successorExtensionLtFormula
            (Godel.RudimentaryTerm.leastProgramValueLtParametersLAssignment
              U oldRelation)
            nextU
  rw [satisfies_canonicalGraphOutputFormula_iff_eq]



/-! ## Functionality and existence -/







end

end Constructible.Model
end CUAdapterModule84


