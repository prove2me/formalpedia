-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library22
-- name    : CH_ConstructibleGCH_Library22
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T08:14:25.153696+00:00
-- url     : https://prove2.me/theorems/b067b884-8e4d-4d34-8faf-e2ac4806b1ca
-- title:
--   Textbook E operations and finite tuple injections
-- statement:
--   This library supplies the constructible interpretation of elementary E operations and finite tuple spaces, together with the injection data used to enumerate definable subsets of a constructible stage.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/DefZFTextbookESection.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEStepLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEStepOperationsLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalFiniteTupleSpaces.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalFiniteTupleInjection.lean#L1

import Definitions.Def_CH_ConstructibleAC_Library15
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
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Cardinal.Basic

import Definitions.Def_CH_ConstructibleGCH_Library21
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_DefZFTextbookESection -/
section GCHSource_Work_CUGCH_DefZFTextbookESection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Definable subsets as textbook E sections

Every member of the genuine internal definable powerset `DefZF a` is a
section of one relation in the textbook enumeration `E`.  The parameters are
represented by an actual finite function graph in `a^n`.

Only the direction needed for the cardinality bound is asserted here.  An
arbitrary value of `E` need not be treated as a section unless its arity and
parameter graph satisfy the displayed side conditions.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-- Every internally represented definable subset of `a` has a textbook
`E`-section presentation with one finite tuple graph of parameters. -/
theorem exists_textbookE_section_of_mem_DefZF
    {a z : ZFSet.{u}} (hz : z ∈ DefZF a) :
    ∃ n m : Nat, ∃ p : ZFSet.{u},
      p ∈ textbookTupleSpace a n ∧
        ∀ x, x ∈ a →
          (x ∈ z ↔
            textbookTupleSnocGraph p n x ∈
              textbookEZF a (natCode (n + 1)) (natCode m)) := by
  rcases mem_DefZF_iff_exists_satisfies.mp hz with
    ⟨_hza, n, params, formula, hformula⟩
  rcases exists_textbookECode_for_positiveFormula a formula with
    ⟨code, hcode⟩
  refine ⟨n, code, textbookTupleGraph params,
    textbookTupleGraph_mem_tupleSpace params, ?_⟩
  intro x hx
  let xCarrier : ZFCarrier a := ⟨x, hx⟩
  calc
    x ∈ z ↔
        FOFormula.Satisfies (zfCarrierMem a) formula
          (snoc params xCarrier) := by
            simpa only [xCarrier] using hformula xCarrier
    _ ↔ textbookTupleGraph (snoc params xCarrier) ∈
          textbookEZF a (natCode (n + 1)) (natCode code) :=
      (hcode (snoc params xCarrier)).symm
    _ ↔ textbookTupleSnocGraph (textbookTupleGraph params) n x ∈
          textbookEZF a (natCode (n + 1)) (natCode code) := by
      rw [textbookTupleGraph_snoc]

end

end Constructible

end
end GCHSource_Work_CUGCH_DefZFTextbookESection


/- Source module: Solutions.Work_CUGCH_TextbookEStepLCarrier -/
section GCHSource_Work_CUGCH_TextbookEStepLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The textbook E step over the constructible universe

This file begins the class-model version of the textbook `E` recursion by
proving that its one-step functional preserves constructibility.  The proof
follows the five clauses of the definition.  In particular, the history
lookup is treated as the actual total operation `uniqueGraphLookupZF`; it is
not replaced by an external choice function.

The exact `LCarrier` semantics of `textbookEStepFormula` is developed below
this closure layer.  The full recursion-value formula additionally requires
the set-like relation and local-solution construction over `LCarrier`; those
are separate obligations.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## Closure of the total history lookup -/

/-- The total unique-value lookup of two constructible sets is constructible.
If the graph has a unique value at the key, that value is a component of a
Kuratowski pair belonging to the graph.  Otherwise the lookup is empty. -/
theorem uniqueGraphLookupZF_mem_L
    {graph key : ZFSet.{u}} (hgraph : graph ∈ L) (_hkey : key ∈ L) :
    uniqueGraphLookupZF graph key ∈ L := by
  by_cases hunique : ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph
  · rcases hunique with ⟨value, hvalue, hvalueUnique⟩
    rw [uniqueGraphLookupZF_eq_of_unique hvalue hvalueUnique]
    have hpairL : ZFSet.pair key value ∈ L :=
      mem_L_of_mem hvalue hgraph
    have hunorderedPair : ({key, value} : ZFSet.{u}) ∈
        ZFSet.pair key value := by
      simp [ZFSet.pair]
    have hunorderedPairL : ({key, value} : ZFSet.{u}) ∈ L :=
      mem_L_of_mem hunorderedPair hpairL
    exact mem_L_of_mem (by simp) hunorderedPairL
  · rw [uniqueGraphLookupZF_eq_empty_of_not_unique hunique]
    exact empty_mem_L

/-! ## Closure of the complete E step -/

/-- The textbook recursion functional maps a constructible parameter and a
constructible history to a constructible value at every genuine key. -/
theorem textbookEStep_mem_L
    {a key history : ZFSet.{u}} (ha : a ∈ L)
    (hhistory : history ∈ L)
    (hkeyDomain : key ∈ TextbookEDomain) :
    textbookEStep a key history ∈ L := by
  rcases exists_textbookEKeyDecode_of_mem_textbookEDomain hkeyDomain with
    ⟨m, n, hdecode, _hkeyEq⟩
  unfold textbookEStep
  rw [hdecode]
  simp only
  cases hcode : textbookEDecode m with
  | none =>
      exact empty_mem_L
  | some fields =>
      rcases fields with ⟨i, j, tag⟩
      cases tag with
      | zero =>
          simp only
          split_ifs
          · rw [textbookDInCodeZF_natCode]
            exact textbookDInZF_mem_L ha n i j
          · exact empty_mem_L
      | succ tag =>
          cases tag with
          | zero =>
              simp only
              split_ifs
              · rw [textbookDEqCodeZF_natCode]
                exact textbookDEqZF_mem_L ha n i j
              · exact empty_mem_L
          | succ tag =>
              cases tag with
              | zero =>
                  simp only
                  have hlookup :
                      uniqueGraphLookupZF history
                          (ZFSet.pair (natCode i) (natCode n)) ∈ L :=
                    uniqueGraphLookupZF_mem_L hhistory
                      (orderedPair_mem_L (natCode_mem_L i) (natCode_mem_L n))
                  exact relativeDifferenceZF_mem_L
                    (textbookTupleSpace_mem_L ha n) hlookup
              | succ tag =>
                  cases tag with
                  | zero =>
                      simp only
                      have hleft :
                          uniqueGraphLookupZF history
                              (ZFSet.pair (natCode i) (natCode n)) ∈ L :=
                        uniqueGraphLookupZF_mem_L hhistory
                          (orderedPair_mem_L
                            (natCode_mem_L i) (natCode_mem_L n))
                      have hright :
                          uniqueGraphLookupZF history
                              (ZFSet.pair (natCode j) (natCode n)) ∈ L :=
                        uniqueGraphLookupZF_mem_L hhistory
                          (orderedPair_mem_L
                            (natCode_mem_L j) (natCode_mem_L n))
                      exact intersectionZF_mem_L hleft hright
                  | succ tag =>
                      cases tag with
                      | zero =>
                          simp only
                          have hrelation :
                              uniqueGraphLookupZF history
                                  (ZFSet.pair (natCode i)
                                    (natCode (n + 1))) ∈ L :=
                            uniqueGraphLookupZF_mem_L hhistory
                              (orderedPair_mem_L
                                (natCode_mem_L i) (natCode_mem_L (n + 1)))
                          rw [textbookExistsProjCodeZF_natCode]
                          exact textbookExistsProjZF_mem_L ha hrelation n
                      | succ tag =>
                          exact empty_mem_L

namespace Model

/-- The one-step value packaged as an element of `LCarrier`. -/
def textbookEStepLCarrier
    (a key history : LCarrier.{u}) (hkeyDomain : key.1 ∈ TextbookEDomain) :
    LCarrier.{u} :=
  ⟨textbookEStep a.1 key.1 history.1,
    textbookEStep_mem_L a.2 history.2 hkeyDomain⟩

@[simp]
theorem textbookEStepLCarrier_val
    (a key history : LCarrier.{u}) (hkeyDomain : key.1 ∈ TextbookEDomain) :
    (textbookEStepLCarrier a key history hkeyDomain).1 =
      textbookEStep a.1 key.1 history.1 :=
  rfl

end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEStepLCarrier


/- Source module: Solutions.Work_CUGCH_TextbookEStepOperationsLCarrier -/
section GCHSource_Work_CUGCH_TextbookEStepOperationsLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Operation semantics for the textbook E step over L

This file proves exact `LCarrier` semantics for the set operations occurring
in the five clauses of the textbook recursion for `E`.  Unbounded quantifiers
are handled over the proper-class carrier itself.  The reverse directions use
explicit constructibility closure theorems for the operation values and for
the finite witnesses selected by the formulas.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem

@[simp]
theorem satisfies_kuratowskiPairEqAt_lCarrier {n : Nat}
    (output left right : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.kuratowskiPairEqAt output left right).toFO s <->
      (s output).1 = ZFSet.pair (s left).1 (s right).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.kuratowskiPairEqAt output left right) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_kuratowskiPairEqAt])

@[simp]
theorem satisfies_successorAt_lCarrier {n : Nat}
    (output input : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.successorAt output input).toFO s <->
      (s output).1 = insert (s input).1 (s input).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.successorAt output input) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt])

/-! ## Coordinate embeddings -/

@[simp]
theorem satisfies_formula3At_lCarrier
    (formula : FOFormula 3) {n : Nat} (x y z : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookEFormula.formula3At formula x y z) s <->
      FOFormula.Satisfies LMem formula ![s x, s y, s z] := by
  rw [TextbookEFormula.formula3At, FOFormula.satisfies_rename]
  have hassign : (fun i => s (![x, y, z] i)) =
      ![s x, s y, s z] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

@[simp]
theorem satisfies_formula4At_lCarrier
    (formula : FOFormula 4) {n : Nat} (v w x y : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookEFormula.formula4At formula v w x y) s <->
      FOFormula.Satisfies LMem formula ![s v, s w, s x, s y] := by
  rw [TextbookEFormula.formula4At, FOFormula.satisfies_rename]
  have hassign : (fun i => s (![v, w, x, y] i)) =
      ![s v, s w, s x, s y] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

@[simp]
theorem satisfies_formula5At_lCarrier
    (formula : FOFormula 5) {n : Nat} (v w x y z : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookEFormula.formula5At formula v w x y z) s <->
      FOFormula.Satisfies LMem formula ![s v, s w, s x, s y, s z] := by
  rw [TextbookEFormula.formula5At, FOFormula.satisfies_rename]
  have hassign : (fun i => s (![v, w, x, y, z] i)) =
      ![s v, s w, s x, s y, s z] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

/-! ## Boolean set operations -/

@[simp]
theorem satisfies_relativeDifferenceOutputFormula_lCarrier
    (space removed output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.relativeDifferenceOutputFormula
        ![space, removed, output] <->
      output.1 = relativeDifferenceZF space.1 removed.1 := by
  rw [TextbookDefFormula.relativeDifferenceOutputFormula,
    FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    TextbookDefFormula.satisfies_relativeDifferenceMemberAt]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [mem_relativeDifferenceZF_iff]
    constructor
    · intro hx
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx output.2⟩
      exact (h xL).mp hx
    · intro hx
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx.1 space.2⟩
      exact (h xL).mpr hx
  · intro houtput x
    change x.1 ∈ output.1 <-> x.1 ∈ space.1 ∧ x.1 ∉ removed.1
    rw [houtput, mem_relativeDifferenceZF_iff]

@[simp]
theorem satisfies_intersectionOutputFormula_lCarrier
    (left right output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.intersectionOutputFormula
        ![left, right, output] <->
      output.1 = intersectionZF left.1 right.1 := by
  rw [TextbookDefFormula.intersectionOutputFormula,
    FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    TextbookDefFormula.satisfies_intersectionMemberAt]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    rw [mem_intersectionZF_iff]
    constructor
    · intro hx
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx output.2⟩
      exact (h xL).mp hx
    · intro hx
      let xL : LCarrier.{u} := ⟨x, mem_L_of_mem hx.1 left.2⟩
      exact (h xL).mpr hx
  · intro houtput x
    change x.1 ∈ output.1 <-> x.1 ∈ left.1 ∧ x.1 ∈ right.1
    rw [houtput, mem_intersectionZF_iff]

/-! ## Total graph lookup -/

/-- Every displayed value of a constructible graph is constructible. -/
theorem graphValue_mem_L
    {graph key value : ZFSet.{u}} (hgraph : graph ∈ L)
    (hvalue : ZFSet.pair key value ∈ graph) : value ∈ L := by
  have hpairL : ZFSet.pair key value ∈ L :=
    mem_L_of_mem hvalue hgraph
  have hunorderedPair : ({key, value} : ZFSet.{u}) ∈
      ZFSet.pair key value := by
    simp [ZFSet.pair]
  have hunorderedPairL : ({key, value} : ZFSet.{u}) ∈ L :=
    mem_L_of_mem hunorderedPair hpairL
  exact mem_L_of_mem (by simp) hunorderedPairL

@[simp]
theorem satisfies_graphValueAt_lCarrier {n : Nat}
    (graph key value : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.graphValueAt graph key value) s <->
      ZFSet.pair (s key).1 (s value).1 ∈ (s graph).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.graphValueDeltaAt graph key value) s).trans
    (TextbookDefFormula.satisfies_graphValueAt graph key value
      (fun i => (s i).1))

@[simp]
theorem satisfies_emptyDeltaAt_lCarrier {n : Nat}
    (index : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.emptyDeltaAt index).toFO s <->
      (s index).1 = (∅ : ZFSet.{u}) := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.emptyDeltaAt index) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_emptyDeltaAt])

@[simp]
theorem satisfies_uniqueGraphValueAt_lCarrier {n : Nat}
    (graph key output : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.uniqueGraphValueAt graph key output) s <->
      IsUniqueGraphValue (s graph).1 (s key).1 (s output).1 := by
  rw [TextbookDefFormula.uniqueGraphValueAt]
  simp only [FOFormula.Satisfies, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, satisfies_graphValueAt_lCarrier,
    snoc_last, snoc_castSucc, IsUniqueGraphValue]
  constructor
  · rintro ⟨hvalue, hunique⟩
    refine ⟨hvalue, ?_⟩
    intro other hother
    let otherL : LCarrier.{u} :=
      ⟨other, graphValue_mem_L (s graph).2 hother⟩
    exact congrArg Subtype.val (hunique otherL hother)
  · rintro ⟨hvalue, hunique⟩
    refine ⟨hvalue, ?_⟩
    intro other hother
    apply Subtype.ext
    exact hunique other.1 hother

@[simp]
theorem satisfies_hasUniqueGraphValueAt_lCarrier {n : Nat}
    (graph key : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.hasUniqueGraphValueAt graph key) s <->
      ∃ value : ZFSet.{u},
        IsUniqueGraphValue (s graph).1 (s key).1 value := by
  rw [TextbookDefFormula.hasUniqueGraphValueAt]
  simp only [FOFormula.Satisfies,
    satisfies_uniqueGraphValueAt_lCarrier, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨value, hvalue⟩
    exact ⟨value.1, hvalue⟩
  · rintro ⟨value, hvalue⟩
    let valueL : LCarrier.{u} :=
      ⟨value, graphValue_mem_L (s graph).2 hvalue.1⟩
    exact ⟨valueL, hvalue⟩

@[simp]
theorem satisfies_uniqueGraphLookupFormula_lCarrier_iff
    (graph key output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.uniqueGraphLookupFormula
        ![graph, key, output] <->
      output.1 = uniqueGraphLookupZF graph.1 key.1 := by
  rw [TextbookDefFormula.uniqueGraphLookupFormula]
  simp only [FOFormula.satisfies_disj, FOFormula.Satisfies,
    satisfies_uniqueGraphValueAt_lCarrier,
    satisfies_hasUniqueGraphValueAt_lCarrier,
    satisfies_emptyDeltaAt_lCarrier]
  change
    (IsUniqueGraphValue graph.1 key.1 output.1 ∨
      ((¬ ∃ value : ZFSet.{u},
          IsUniqueGraphValue graph.1 key.1 value) ∧
        output.1 = (∅ : ZFSet.{u}))) <->
      output.1 = uniqueGraphLookupZF graph.1 key.1
  constructor
  · rintro (houtput | ⟨hnot, hempty⟩)
    · exact (uniqueGraphLookupZF_eq_of_unique
        houtput.1 houtput.2).symm
    · have hnotUnique :
          ¬ ∃! value : ZFSet.{u},
            ZFSet.pair key.1 value ∈ graph.1 := by
        simpa only [existsUnique_graphValue_iff] using hnot
      rw [hempty,
        uniqueGraphLookupZF_eq_empty_of_not_unique hnotUnique]
  · intro houtput
    by_cases hunique :
        ∃! value : ZFSet.{u}, ZFSet.pair key.1 value ∈ graph.1
    · rcases hunique with ⟨value, hvalue, hunique⟩
      left
      have hlookup := uniqueGraphLookupZF_eq_of_unique hvalue hunique
      rw [houtput, hlookup]
      exact ⟨hvalue, hunique⟩
    · right
      constructor
      · simpa only [← existsUnique_graphValue_iff] using hunique
      · rw [houtput,
          uniqueGraphLookupZF_eq_empty_of_not_unique hunique]

/-! ## Finite function spaces -/

@[simp]
theorem satisfies_standardFiniteDomainAt_lCarrier {n : Nat}
    (domain : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (standardFiniteDomainAt domain) s <->
      ∃ k : Nat, (s domain).1 = natCode k := by
  rw [standardFiniteDomainAt, FOFormula.Satisfies]
  constructor
  · rintro ⟨omega, homegaFormula, hdomainOmega⟩
    have homega : omega = omegaLCarrier := by
      simpa only [snoc_last] using
        (satisfies_standardOmegaAt_lCarrier
          (Fin.last n) (snoc s omega)).mp homegaFormula
    subst omega
    have hdomainOmega' : (s domain).1 ∈ omegaLCarrier.1 := by
      change (snoc s omegaLCarrier domain.castSucc).1 ∈
        (snoc s omegaLCarrier (Fin.last n)).1 at hdomainOmega
      simpa only [snoc_castSucc, snoc_last] using hdomainOmega
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (s domain).1).mp hdomainOmega'
  · rintro ⟨k, hdomain⟩
    refine ⟨omegaLCarrier, ?_, ?_⟩
    · apply (satisfies_standardOmegaAt_lCarrier
        (Fin.last n) (snoc s omegaLCarrier)).mpr
      simp only [snoc_last]
    · change (snoc s omegaLCarrier domain.castSucc).1 ∈
        (snoc s omegaLCarrier (Fin.last n)).1
      simp only [snoc_castSucc, snoc_last]
      rw [hdomain]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode k)).mpr ⟨k, rfl⟩

@[simp]
theorem satisfies_isFunctionAt_lCarrier {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.isFunctionAt graph domain codomain) s <->
      ZFSet.IsFunc (s domain).1 (s codomain).1 (s graph).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.isFunctionDeltaAt graph domain codomain) s).trans
    (TextbookDefFormula.satisfies_isFunctionAt graph domain codomain
      (fun i => (s i).1))

@[simp]
theorem satisfies_functionSpaceGraph_lCarrier_natCode_iff
    (n : Nat) (codomain space : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookDefFormula.functionSpaceGraph
        ![TextbookNatFormula.textbookNatCodeLCarrier n,
          codomain, space] <->
      space.1 = ZFSet.funs (natCode n) codomain.1 := by
  rw [TextbookDefFormula.functionSpaceGraph,
    TextbookDefFormula.functionSpaceAt, FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_isFunctionAt_lCarrier, snoc_last, snoc_castSucc]
  change
    (∀ graph : LCarrier.{u},
      graph.1 ∈ space.1 <->
        ZFSet.IsFunc (natCode n) codomain.1 graph.1) <-> _
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_funs]
    constructor
    · intro hgraphSpace
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphSpace space.2⟩
      exact (h graphL).mp hgraphSpace
    · intro hfunc
      have hgraphTupleSpace : graph ∈ textbookTupleSpace codomain.1 n :=
        mem_textbookTupleSpace_iff.mpr hfunc
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphTupleSpace
          (textbookTupleSpace_mem_L codomain.2 n)⟩
      exact (h graphL).mpr hfunc
  · intro hspace graph
    rw [hspace, ZFSet.mem_funs]

@[simp]
theorem satisfies_finiteFunctionSpaceGraph_lCarrier_natCode_iff
    (n : Nat) (codomain space : LCarrier.{u}) :
    FOFormula.Satisfies LMem finiteFunctionSpaceGraph
        ![TextbookNatFormula.textbookNatCodeLCarrier n,
          codomain, space] <->
      space.1 = ZFSet.funs (natCode n) codomain.1 := by
  rw [finiteFunctionSpaceGraph, FOFormula.Satisfies]
  constructor
  · rintro ⟨_hfinite, hspace⟩
    exact (satisfies_functionSpaceGraph_lCarrier_natCode_iff
      n codomain space).mp hspace
  · intro hspace
    refine ⟨?_,
      (satisfies_functionSpaceGraph_lCarrier_natCode_iff
        n codomain space).mpr hspace⟩
    exact (satisfies_standardFiniteDomainAt_lCarrier
      (0 : Fin 3)
      ![TextbookNatFormula.textbookNatCodeLCarrier n,
        codomain, space]).mpr ⟨n, rfl⟩

/-! ## Existential projection -/

@[simp]
theorem satisfies_existsProjMemberDeltaAt_lCarrier {n : Nat}
    (a arity relation graph : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.existsProjMemberDeltaAt
          a arity relation graph).toFO s <->
      (∃ index : ZFSet.{u}, index ∈ (s arity).1) ∧
        ZFSet.IsFunc (s arity).1 (s a).1 (s graph).1 ∧
          ∃ value : ZFSet.{u}, value ∈ (s a).1 ∧
            insert (ZFSet.pair (s arity).1 value) (s graph).1 ∈
              (s relation).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.existsProjMemberDeltaAt
        a arity relation graph) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_existsProjMemberDeltaAt])

@[simp]
theorem satisfies_existsProjOutputMemberCondition_lCarrier_natCode_iff
    (n : Nat) (a relation output graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.existsProjOutputMemberCondition
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          relation, output, graph] <->
      graph.1 ∈ textbookExistsProjCodeZF a.1 (natCode n) relation.1 := by
  rw [TextbookDefFormula.existsProjOutputMemberCondition,
    FOFormula.Satisfies]
  constructor
  · rintro ⟨_hfinite, hmember⟩
    apply mem_textbookExistsProjCodeZF_iff.mpr
    refine ⟨⟨n, rfl⟩, ?_⟩
    exact (satisfies_existsProjMemberDeltaAt_lCarrier
      (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (Fin.last 4)
      ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
        relation, output, graph]).mp hmember
  · intro hgraph
    have hcomponents := mem_textbookExistsProjCodeZF_iff.mp hgraph
    refine ⟨?_, ?_⟩
    · exact (satisfies_standardFiniteDomainAt_lCarrier
        (1 : Fin 5)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          relation, output, graph]).mpr ⟨n, rfl⟩
    · apply (satisfies_existsProjMemberDeltaAt_lCarrier
        (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (Fin.last 4)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          relation, output, graph]).mpr
      exact hcomponents.2

@[simp]
theorem satisfies_existsProjOutputFormula_lCarrier_natCode_iff
    (n : Nat) (a relation output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.existsProjOutputFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          relation, output] <->
      output.1 =
        textbookExistsProjCodeZF a.1 (natCode n) relation.1 := by
  rw [TextbookDefFormula.existsProjOutputFormula,
    FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies]
  change
    (∀ graph : LCarrier.{u}, graph.1 ∈ output.1 <->
      FOFormula.Satisfies LMem
        TextbookDefFormula.existsProjOutputMemberCondition
        (snoc
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            relation, output] graph)) <-> _
  have hcondition (graph : LCarrier.{u}) :
      FOFormula.Satisfies LMem
          TextbookDefFormula.existsProjOutputMemberCondition
          (snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              relation, output] graph) <->
        graph.1 ∈
          textbookExistsProjCodeZF a.1 (natCode n) relation.1 := by
    have hassign :
        snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              relation, output] graph =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            relation, output, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign,
      satisfies_existsProjOutputMemberCondition_lCarrier_natCode_iff]
  simp_rw [hcondition]
  have hresultL :
      textbookExistsProjCodeZF a.1 (natCode n) relation.1 ∈ L := by
    rw [textbookExistsProjCodeZF_natCode]
    exact textbookExistsProjZF_mem_L a.2 relation.2 n
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraphOutput
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphOutput output.2⟩
      exact (h graphL).mp hgraphOutput
    · intro hgraphResult
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphResult hresultL⟩
      exact (h graphL).mpr hgraphResult
  · intro houtput graph
    rw [houtput]

/-! ## Atomic membership and equality relations -/

@[simp]
theorem satisfies_dInMemberDeltaAt_lCarrier {n : Nat}
    (a arity left right graph : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.dInMemberDeltaAt
          a arity left right graph).toFO s <->
      (s left).1 ∈ (s arity).1 ∧ (s right).1 ∈ (s arity).1 ∧
        ZFSet.IsFunc (s arity).1 (s a).1 (s graph).1 ∧
          ∃ x : ZFSet.{u}, x ∈ (s a).1 ∧
            ∃ y : ZFSet.{u}, y ∈ (s a).1 ∧
              ZFSet.pair (s left).1 x ∈ (s graph).1 ∧
              ZFSet.pair (s right).1 y ∈ (s graph).1 ∧ x ∈ y := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.dInMemberDeltaAt
        a arity left right graph) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_dInMemberDeltaAt])

@[simp]
theorem satisfies_dEqMemberDeltaAt_lCarrier {n : Nat}
    (a arity left right graph : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (TextbookDefFormula.dEqMemberDeltaAt
          a arity left right graph).toFO s <->
      (s left).1 ∈ (s arity).1 ∧ (s right).1 ∈ (s arity).1 ∧
        ZFSet.IsFunc (s arity).1 (s a).1 (s graph).1 ∧
          ∃ x : ZFSet.{u}, x ∈ (s a).1 ∧
            ZFSet.pair (s left).1 x ∈ (s graph).1 ∧
              ZFSet.pair (s right).1 x ∈ (s graph).1 := by
  exact
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.dEqMemberDeltaAt
        a arity left right graph) s).trans
    (by
      rw [Delta0Formula.satisfies_toFO,
        TextbookDefFormula.satisfies_dEqMemberDeltaAt])

@[simp]
theorem satisfies_dInOutputMemberCondition_lCarrier_natCode_iff
    (n i j : Nat) (a output graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.dInOutputMemberCondition
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph] <->
      graph.1 ∈ textbookDInZF a.1 n i j := by
  rw [TextbookDefFormula.dInOutputMemberCondition,
    FOFormula.Satisfies]
  constructor
  · rintro ⟨_hfinite, hmember⟩
    have hcode : graph.1 ∈ textbookDInCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      apply mem_textbookDInCodeZF_iff.mpr
      refine ⟨⟨n, rfl⟩, ?_⟩
      exact (satisfies_dInMemberDeltaAt_lCarrier
        (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
        (3 : Fin 6) (Fin.last 5)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mp hmember
    simpa only [textbookDInCodeZF_natCode] using hcode
  · intro hgraph
    have hcode : graph.1 ∈ textbookDInCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      simpa only [textbookDInCodeZF_natCode] using hgraph
    have hcomponents := mem_textbookDInCodeZF_iff.mp hcode
    refine ⟨?_, ?_⟩
    · exact (satisfies_standardFiniteDomainAt_lCarrier
        (1 : Fin 6)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mpr ⟨n, rfl⟩
    · apply (satisfies_dInMemberDeltaAt_lCarrier
        (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
        (3 : Fin 6) (Fin.last 5)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mpr
      exact hcomponents.2

@[simp]
theorem satisfies_dEqOutputMemberCondition_lCarrier_natCode_iff
    (n i j : Nat) (a output graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookDefFormula.dEqOutputMemberCondition
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph] <->
      graph.1 ∈ textbookDEqZF a.1 n i j := by
  rw [TextbookDefFormula.dEqOutputMemberCondition,
    FOFormula.Satisfies]
  constructor
  · rintro ⟨_hfinite, hmember⟩
    have hcode : graph.1 ∈ textbookDEqCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      apply mem_textbookDEqCodeZF_iff.mpr
      refine ⟨⟨n, rfl⟩, ?_⟩
      exact (satisfies_dEqMemberDeltaAt_lCarrier
        (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
        (3 : Fin 6) (Fin.last 5)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mp hmember
    simpa only [textbookDEqCodeZF_natCode] using hcode
  · intro hgraph
    have hcode : graph.1 ∈ textbookDEqCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      simpa only [textbookDEqCodeZF_natCode] using hgraph
    have hcomponents := mem_textbookDEqCodeZF_iff.mp hcode
    refine ⟨?_, ?_⟩
    · exact (satisfies_standardFiniteDomainAt_lCarrier
        (1 : Fin 6)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mpr ⟨n, rfl⟩
    · apply (satisfies_dEqMemberDeltaAt_lCarrier
        (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
        (3 : Fin 6) (Fin.last 5)
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          output, graph]).mpr
      exact hcomponents.2

@[simp]
theorem satisfies_dInOutputFormula_lCarrier_natCode_iff
    (n i j : Nat) (a output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookDefFormula.dInOutputFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, output] <->
      output.1 = textbookDInZF a.1 n i j := by
  rw [TextbookDefFormula.dInOutputFormula, FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies]
  change
    (∀ graph : LCarrier.{u}, graph.1 ∈ output.1 <->
      FOFormula.Satisfies LMem
        TextbookDefFormula.dInOutputMemberCondition
        (snoc
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier i,
            TextbookNatFormula.textbookNatCodeLCarrier j, output]
          graph)) <-> _
  have hcondition (graph : LCarrier.{u}) :
      FOFormula.Satisfies LMem
          TextbookDefFormula.dInOutputMemberCondition
          (snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier i,
              TextbookNatFormula.textbookNatCodeLCarrier j, output]
            graph) <->
        graph.1 ∈ textbookDInZF a.1 n i j := by
    have hassign :
        snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier i,
              TextbookNatFormula.textbookNatCodeLCarrier j, output]
            graph =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier i,
            TextbookNatFormula.textbookNatCodeLCarrier j, output, graph] := by
      funext k
      fin_cases k <;> rfl
    rw [hassign,
      satisfies_dInOutputMemberCondition_lCarrier_natCode_iff]
  simp_rw [hcondition]
  have hresultL : textbookDInZF a.1 n i j ∈ L :=
    textbookDInZF_mem_L a.2 n i j
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraphOutput
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphOutput output.2⟩
      exact (h graphL).mp hgraphOutput
    · intro hgraphResult
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphResult hresultL⟩
      exact (h graphL).mpr hgraphResult
  · intro houtput graph
    rw [houtput]

@[simp]
theorem satisfies_dEqOutputFormula_lCarrier_natCode_iff
    (n i j : Nat) (a output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookDefFormula.dEqOutputFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, output] <->
      output.1 = textbookDEqZF a.1 n i j := by
  rw [TextbookDefFormula.dEqOutputFormula, FOFormula.satisfies_all]
  simp only [FOFormula.satisfies_biimp, FOFormula.Satisfies]
  change
    (∀ graph : LCarrier.{u}, graph.1 ∈ output.1 <->
      FOFormula.Satisfies LMem
        TextbookDefFormula.dEqOutputMemberCondition
        (snoc
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier i,
            TextbookNatFormula.textbookNatCodeLCarrier j, output]
          graph)) <-> _
  have hcondition (graph : LCarrier.{u}) :
      FOFormula.Satisfies LMem
          TextbookDefFormula.dEqOutputMemberCondition
          (snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier i,
              TextbookNatFormula.textbookNatCodeLCarrier j, output]
            graph) <->
        graph.1 ∈ textbookDEqZF a.1 n i j := by
    have hassign :
        snoc
            ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
              TextbookNatFormula.textbookNatCodeLCarrier i,
              TextbookNatFormula.textbookNatCodeLCarrier j, output]
            graph =
          ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
            TextbookNatFormula.textbookNatCodeLCarrier i,
            TextbookNatFormula.textbookNatCodeLCarrier j, output, graph] := by
      funext k
      fin_cases k <;> rfl
    rw [hassign,
      satisfies_dEqOutputMemberCondition_lCarrier_natCode_iff]
  simp_rw [hcondition]
  have hresultL : textbookDEqZF a.1 n i j ∈ L :=
    textbookDEqZF_mem_L a.2 n i j
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    constructor
    · intro hgraphOutput
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphOutput output.2⟩
      exact (h graphL).mp hgraphOutput
    · intro hgraphResult
      let graphL : LCarrier.{u} :=
        ⟨graph, mem_L_of_mem hgraphResult hresultL⟩
      exact (h graphL).mpr hgraphResult
  · intro houtput graph
    rw [houtput]

/-! ## Constructor-code guards -/

@[simp]
theorem satisfies_natLiteralDeltaAt_lCarrier
    (k : Nat) {n : Nat} (index : Fin n)
    (s : Tuple LCarrier.{u} n) :
    Delta0Formula.Satisfies LMem
        (Delta0Formula.natLiteralDeltaAt k index) s <->
      (s index).1 = (natCode k : ZFSet.{u}) := by
  exact
    (Delta0Formula.satisfies_lCarrier_absolute
      (Delta0Formula.natLiteralDeltaAt k index) s).trans
    (Delta0Formula.satisfies_natLiteralDeltaAt
      k index (fun i => (s i).1))

@[simp]
theorem lmem_textbookNatCode_omegaLCarrier (k : Nat) :
    LMem (TextbookNatFormula.textbookNatCodeLCarrier k)
      omegaLCarrier := by
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
    (natCode k)).mpr ⟨k, rfl⟩

@[simp]
theorem lmem_textbookNatCode_iff_lt (i n : Nat) :
    LMem (TextbookNatFormula.textbookNatCodeLCarrier i)
        (TextbookNatFormula.textbookNatCodeLCarrier n) <->
      i < n := by
  exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
    (natCode i) n).trans (by
      constructor
      · rintro ⟨j, hj, hji⟩
        exact (natCode_injective hji).symm ▸ hj
      · intro hi
        exact ⟨i, hi, rfl⟩)

theorem satisfies_codeGuardBody_lCarrier_natCode
    (literal : Nat) (bounded : Bool)
    (a key history output : LCarrier.{u}) (m n i j : Nat) :
    FOFormula.Satisfies LMem
        (TextbookEFormula.codeGuardBody literal bounded)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          TextbookNatFormula.textbookNatCodeLCarrier literal] <->
      m = textbookECode i j literal ∧
        (if bounded then i < n ∧ j < n else True) := by
  cases bounded <;>
    simp [TextbookEFormula.codeGuardBody,
      TextbookNatFormula.satisfies_textbookECodeFormulaAt,
      TextbookNatFormula.satisfies_textbookECodeFormula_lCarrier_natCode_iff,
      satisfies_natLiteralDeltaAt_lCarrier,
      lmem_textbookNatCode_omegaLCarrier,
      lmem_textbookNatCode_iff_lt,
      natCode_injective.eq_iff]

theorem satisfies_codeGuard_lCarrier_standard
    (literal : Nat) (bounded : Bool)
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem
        (TextbookEFormula.codeGuard literal bounded)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j literal ∧
        (if bounded then i < n ∧ j < n else True) := by
  rw [TextbookEFormula.codeGuard]
  simp only [FOFormula.Satisfies]
  let base : Tuple LCarrier.{u} 7 :=
    ![a, key, history, output, omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n]
  have hassign (iSet jSet tagSet : LCarrier.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hbody⟩
    rw [hassign] at hbody
    have hiOmega : iSet.1 ∈ omegaLCarrier.1 := hbody.1
    have hjOmega : jSet.1 ∈ omegaLCarrier.1 := hbody.2.1
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hiOmega with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hjOmega with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode literal : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        literal (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j,
          tagSet]).mp hbody.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier literal :=
      Subtype.ext htagVal
    subst tagSet
    exact ⟨i, j,
      (satisfies_codeGuardBody_lCarrier_natCode
        literal bounded a key history output m n i j).mp hbody⟩
  · rintro ⟨i, j, hcode⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier literal, ?_⟩
    rw [hassign]
    exact (satisfies_codeGuardBody_lCarrier_natCode
      literal bounded a key history output m n i j).mpr hcode

end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEStepOperationsLCarrier


/- Source module: Solutions.Work_CUGCH_InternalFiniteTupleSpaces -/
section GCHSource_Work_CUGCH_InternalFiniteTupleSpaces
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# The internal set of finite tuples

For a constructible set `a`, Replacement applied to the finite-function-space
formula produces the actual family

`{a^n | n in omega}`.

Its union is therefore an actual member of `L` containing exactly the
set-coded finite tuples from `a`.  The index-to-space map is represented by a
Kuratowski graph in `L`; an external `Nat -> ZFSet` is not used as that graph.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## The uniform finite-power formula -/

/-- Reorder `[a,index,space]` as the input layout
`[index,a,space]` of `finiteFunctionSpaceGraph`. -/
def finiteTupleSpaceFormulaRename : Fin 3 -> Fin 3 :=
  ![1, 0, 2]

/-- Layout `[a,index,space]`: `index` is a standard natural-number code and
`space` is the set of all functions from `index` to `a`. -/
def finiteTupleSpaceFormula : FOFormula 3 :=
  FOFormula.rename finiteTupleSpaceFormulaRename
    Constructible.Model.finiteFunctionSpaceGraph

 theorem comp_finiteTupleSpaceFormulaRename
    (a index space : LCarrier.{u}) :
    (fun i => ![a, index, space] (finiteTupleSpaceFormulaRename i)) =
      ![index, a, space] := by
  funext i
  fin_cases i <;> rfl

/-- Exact `LCarrier` semantics at a standard natural-number index. -/
@[simp]
theorem satisfies_finiteTupleSpaceFormula_natCode_iff
    (a space : LCarrier.{u}) (n : Nat) :
    FOFormula.Satisfies LMem finiteTupleSpaceFormula
        ![a, Constructible.TextbookNatFormula.textbookNatCodeLCarrier n,
          space] <->
      space.1 = textbookTupleSpace a.1 n := by
  rw [finiteTupleSpaceFormula, FOFormula.satisfies_rename,
    comp_finiteTupleSpaceFormulaRename]
  simpa only [textbookTupleSpace] using
    (Constructible.Model.satisfies_finiteFunctionSpaceGraph_lCarrier_natCode_iff
      n a space)

/-- The finite power `a^n`, packaged as a genuine member of `L`. -/
def finiteTupleSpaceLCarrier (a : LCarrier.{u}) (n : Nat) :
    LCarrier.{u} :=
  ⟨textbookTupleSpace a.1 n,
    textbookTupleSpace_mem_L a.2 n⟩

@[simp]
theorem finiteTupleSpaceLCarrier_val (a : LCarrier.{u}) (n : Nat) :
    (finiteTupleSpaceLCarrier a n).1 = textbookTupleSpace a.1 n :=
  rfl

 theorem finiteTupleSpaceFormula_existsUnique
    (a index : LCarrier.{u})
    (hindex : index.1 ∈ (omegaLCarrier : LCarrier.{u}).1) :
    ExistsUnique fun space : LCarrier.{u} =>
      FOFormula.Satisfies LMem finiteTupleSpaceFormula
        ![a, index, space] := by
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
      hindex with ⟨n, hindexCode⟩
  have hindexEq :
      index =
        Constructible.TextbookNatFormula.textbookNatCodeLCarrier n := by
    apply Subtype.ext
    exact hindexCode
  subst index
  refine ⟨finiteTupleSpaceLCarrier a n, ?_, ?_⟩
  · exact (satisfies_finiteTupleSpaceFormula_natCode_iff
      a (finiteTupleSpaceLCarrier a n) n).mpr rfl
  · intro other hother
    apply Subtype.ext
    exact (satisfies_finiteTupleSpaceFormula_natCode_iff
      a other n).mp hother

 theorem finiteTupleSpaceFormula_assignment
    (a index space : LCarrier.{u}) :
    snoc (snoc ![a] index) space = ![a, index, space] := by
  funext i
  fin_cases i <;> rfl

/-! ## Replacement range and graph -/

/-- The internally represented data for the family `n |-> a^n`. -/
structure InternalFiniteTupleSpaceFamilyData (a : LCarrier.{u}) where
  graph : LCarrier.{u}
  family : LCarrier.{u}
  isFunctionGraph : IsFunctionGraph LMem graph
    (omegaLCarrier : LCarrier.{u}) family
  mem_family_iff : forall space : LCarrier.{u},
    space.1 ∈ family.1 <->
      exists n : Nat, space = finiteTupleSpaceLCarrier a n
  graphValue_iff : forall index space : LCarrier.{u},
    GraphValue LMem graph index space <->
      index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 /\
        FOFormula.Satisfies LMem finiteTupleSpaceFormula
          ![a, index, space]

/-- Replacement produces both the actual range and the actual Kuratowski
graph of the finite-power operation. -/
theorem exists_internalFiniteTupleSpaceFamilyData
    (a : LCarrier.{u}) :
    Nonempty (InternalFiniteTupleSpaceFamilyData a) := by
  let params : Tuple LCarrier.{u} 1 := ![a]
  have hfun : forall index : LCarrier.{u},
      index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 ->
        ExistsUnique fun space : LCarrier.{u} =>
          FOFormula.Satisfies LMem finiteTupleSpaceFormula
            (snoc (snoc params index) space) := by
    intro index hindex
    simpa only [params, finiteTupleSpaceFormula_assignment] using
      finiteTupleSpaceFormula_existsUnique a index hindex
  rcases Constructible.Model.exists_replacementLCarrier
      finiteTupleSpaceFormula params omegaLCarrier hfun with
    ⟨family, hfamily⟩
  rcases Constructible.Model.exists_replacementFunctionGraphLCarrier
      finiteTupleSpaceFormula params omegaLCarrier hfun with
    ⟨graph, hgraph⟩
  have hvalue : forall index space : LCarrier.{u},
      GraphValue LMem graph index space <->
        index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 /\
          FOFormula.Satisfies LMem finiteTupleSpaceFormula
            ![a, index, space] := by
    intro index space
    constructor
    · rintro ⟨pair, hpairGraph, hpairIS⟩
      rcases (hgraph pair.1).mp hpairGraph with
        ⟨index', hindex', space', hspace', hpairEq⟩
      have hpairISEq :=
        (isKuratowskiPairOf_lCarrier_iff pair index space).mp hpairIS
      have hcoordinates := ZFSet.pair_inj.mp
        (hpairEq.symm.trans hpairISEq)
      have hindexEq : index' = index := Subtype.ext hcoordinates.1
      have hspaceEq : space' = space := Subtype.ext hcoordinates.2
      subst index'
      subst space'
      simpa only [params, finiteTupleSpaceFormula_assignment] using
        And.intro hindex' hspace'
    · rintro ⟨hindex, hspace⟩
      let pair := orderedPairLCarrier index space
      refine ⟨pair, ?_, ?_⟩
      · apply (hgraph pair.1).mpr
        refine ⟨index, hindex, space, ?_, rfl⟩
        simpa only [params, finiteTupleSpaceFormula_assignment] using hspace
      · exact (isKuratowskiPairOf_lCarrier_iff
          pair index space).mpr rfl
  have hbetween : IsGraphBetween LMem graph omegaLCarrier family := by
    intro pair hpairGraph
    rcases (hgraph pair.1).mp hpairGraph with
      ⟨index, hindex, space, hspace, hpairEq⟩
    have hspaceFamily : space.1 ∈ family.1 :=
      (hfamily space).mpr ⟨index, hindex, hspace⟩
    exact ⟨index, hindex, space, hspaceFamily,
      (isKuratowskiPairOf_lCarrier_iff pair index space).mpr hpairEq⟩
  have htotal : forall index : LCarrier.{u},
      index.1 ∈ (omegaLCarrier : LCarrier.{u}).1 ->
        HasUniqueImage LMem graph index family := by
    intro index hindex
    rcases hfun index hindex with ⟨space, hspace, hspaceUnique⟩
    have hspaceFamily : space.1 ∈ family.1 :=
      (hfamily space).mpr ⟨index, hindex, hspace⟩
    refine ⟨space, hspaceFamily,
      (hvalue index space).mpr ⟨hindex, by
        simpa only [params, finiteTupleSpaceFormula_assignment] using
          hspace⟩, ?_⟩
    intro other _hotherFamily hindexOther
    apply hspaceUnique other
    have hother := (hvalue index other).mp hindexOther |>.2
    simpa only [params, finiteTupleSpaceFormula_assignment] using hother
  refine ⟨{
    graph := graph
    family := family
    isFunctionGraph := ⟨hbetween, htotal⟩
    mem_family_iff := ?_
    graphValue_iff := hvalue
  }⟩
  intro space
  rw [hfamily]
  constructor
  · rintro ⟨index, hindex, hspace⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with ⟨n, hindexCode⟩
    have hindexEq :
        index =
          Constructible.TextbookNatFormula.textbookNatCodeLCarrier n := by
      apply Subtype.ext
      exact hindexCode
    subst index
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact (satisfies_finiteTupleSpaceFormula_natCode_iff
      a space n).mp (by
        simpa only [params, finiteTupleSpaceFormula_assignment] using hspace)
  · rintro ⟨n, rfl⟩
    let index :=
      Constructible.TextbookNatFormula.textbookNatCodeLCarrier n
    refine ⟨index, ?_, ?_⟩
    · change (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode n)).mpr ⟨n, rfl⟩
    · simpa only [params, index, finiteTupleSpaceFormula_assignment] using
        (satisfies_finiteTupleSpaceFormula_natCode_iff
          a (finiteTupleSpaceLCarrier a n) n).mpr rfl

/-- A canonical choice of the Replacement data.  Its public API is solely
the extensional specification proved above. -/
noncomputable def internalFiniteTupleSpaceFamilyData
    (a : LCarrier.{u}) : InternalFiniteTupleSpaceFamilyData a :=
  Classical.choice (exists_internalFiniteTupleSpaceFamilyData a)

/-- The genuine internal set of all finite tuple graphs over `a`. -/
noncomputable def internalFiniteTupleSpaces (a : LCarrier.{u}) :
    LCarrier.{u} :=
  sUnionLCarrier (internalFiniteTupleSpaceFamilyData a).family

@[simp]
theorem mem_internalFiniteTupleSpaces_iff
    (a z : LCarrier.{u}) :
    z.1 ∈ (internalFiniteTupleSpaces a).1 <->
      exists n : Nat, z.1 ∈ (finiteTupleSpaceLCarrier a n).1 := by
  rw [internalFiniteTupleSpaces, mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨space, hspaceFamily, hz⟩
    rcases (internalFiniteTupleSpaceFamilyData a).mem_family_iff
        space |>.mp hspaceFamily with ⟨n, rfl⟩
    exact ⟨n, hz⟩
  · rintro ⟨n, hz⟩
    exact ⟨finiteTupleSpaceLCarrier a n,
      (internalFiniteTupleSpaceFamilyData a).mem_family_iff
        (finiteTupleSpaceLCarrier a n) |>.mpr ⟨n, rfl⟩, hz⟩

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalFiniteTupleSpaces


/- Source module: Solutions.Work_CUGCH_InternalFiniteTupleInjection -/
section GCHSource_Work_CUGCH_InternalFiniteTupleInjection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# An internal injection for all finite tuples

Let `a` inject into an infinite internal cardinal `kappa`, and let
`kappa x kappa` inject into `kappa`.  A finite tuple is folded from left to
right with the latter injection.  Its arity is folded into the result once
more, so tuples of different lengths have different codes.

The fold is described by one first-order formula.  Its finite history is an
actual member of `L`, and Separation therefore produces one genuine
Kuratowski graph for the injection.  No externally chosen family of graphs
is used as the represented function.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible
open Constructible.Model
open Constructible.FiniteSequenceZF

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## The uniform finite-fold formula -/

/-- The semantic transition made at each tuple index. -/
def FiniteTupleFoldStep
    (aInjection squareInjection tuple history arity : LCarrier.{u}) : Prop :=
  forall index : LCarrier.{u}, index.1 ∈ arity.1 ->
    exists indexSucc entry entryCode current next pair : LCarrier.{u},
      indexSucc.1 = insert index.1 index.1 /\
        ZFSet.pair index.1 entry.1 ∈ tuple.1 /\
        ZFSet.pair entry.1 entryCode.1 ∈ aInjection.1 /\
        ZFSet.pair index.1 current.1 ∈ history.1 /\
        ZFSet.pair indexSucc.1 next.1 ∈ history.1 /\
        pair.1 = ZFSet.pair current.1 entryCode.1 /\
        ZFSet.pair pair.1 next.1 ∈ squareInjection.1

def finiteTupleFoldStepBodyFormula : FOFormula 12 :=
  .conj
    (Delta0Formula.successorFOAt (6 : Fin 12) (5 : Fin 12))
    (.conj
      (TextbookDefFormula.graphValueAt
        (2 : Fin 12) (5 : Fin 12) (7 : Fin 12))
      (.conj
        (TextbookDefFormula.graphValueAt
          (0 : Fin 12) (7 : Fin 12) (8 : Fin 12))
        (.conj
          (TextbookDefFormula.graphValueAt
            (3 : Fin 12) (5 : Fin 12) (9 : Fin 12))
          (.conj
            (TextbookDefFormula.graphValueAt
              (3 : Fin 12) (6 : Fin 12) (10 : Fin 12))
            (.conj
              (Delta0Formula.kuratowskiPairEqAt
                (11 : Fin 12) (9 : Fin 12) (8 : Fin 12)).toFO
              (TextbookDefFormula.graphValueAt
                (1 : Fin 12) (11 : Fin 12) (10 : Fin 12)))))))

@[simp]
theorem satisfies_finiteTupleFoldStepBodyFormula
    (s : Tuple LCarrier.{u} 12) :
    FOFormula.Satisfies LMem finiteTupleFoldStepBodyFormula s <->
      (s 6).1 = insert (s 5).1 (s 5).1 /\
        ZFSet.pair (s 5).1 (s 7).1 ∈ (s 2).1 /\
        ZFSet.pair (s 7).1 (s 8).1 ∈ (s 0).1 /\
        ZFSet.pair (s 5).1 (s 9).1 ∈ (s 3).1 /\
        ZFSet.pair (s 6).1 (s 10).1 ∈ (s 3).1 /\
        (s 11).1 = ZFSet.pair (s 9).1 (s 8).1 /\
        ZFSet.pair (s 11).1 (s 10).1 ∈ (s 1).1 := by
  simp only [finiteTupleFoldStepBodyFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier,
    Constructible.Model.satisfies_graphValueAt_lCarrier,
    Constructible.Model.satisfies_kuratowskiPairEqAt_lCarrier_generic]

/--
Layout `[aInjection, squareInjection, tuple, history, arity]`.
The six witnesses are the successor index, tuple entry, entry code, current
fold value, next fold value, and their Kuratowski input pair.
-/
def finiteTupleFoldStepFormula : FOFormula 5 :=
  FOFormula.boundedAll (4 : Fin 5)
    (.ex (.ex (.ex (.ex (.ex (.ex
      finiteTupleFoldStepBodyFormula))))))

 theorem satisfies_finiteTupleFoldStepExistentials
    (s : Tuple LCarrier.{u} 6) :
    FOFormula.Satisfies LMem
        (.ex (.ex (.ex (.ex (.ex (.ex
          finiteTupleFoldStepBodyFormula)))))) s ↔
      ∃ indexSucc entry entryCode current next pair : LCarrier.{u},
        FOFormula.Satisfies LMem finiteTupleFoldStepBodyFormula
          (snoc (snoc (snoc (snoc (snoc (snoc
            s indexSucc) entry) entryCode) current) next) pair) := by
  rfl

 theorem snoc_eq_finSnoc
    {A : Type u} {n : Nat} (s : Tuple A n) (x : A) :
    snoc s x = Fin.snoc s x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [snoc_last, Fin.snoc_last]
  · rw [snoc_castSucc, Fin.snoc_castSucc]

 theorem finiteTupleFoldStep_assignment
    (aInjection squareInjection tuple history arity index
      indexSucc entry entryCode current next pair : LCarrier.{u}) :
    snoc (snoc (snoc (snoc (snoc (snoc
      (snoc ![aInjection, squareInjection, tuple, history, arity] index)
      indexSucc) entry) entryCode) current) next) pair =
      ![aInjection, squareInjection, tuple, history, arity, index,
        indexSucc, entry, entryCode, current, next, pair] := by
  simp only [snoc_eq_finSnoc, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty]

@[simp]
theorem satisfies_finiteTupleFoldStepFormula
    (aInjection squareInjection tuple history arity : LCarrier.{u}) :
    FOFormula.Satisfies LMem finiteTupleFoldStepFormula
        ![aInjection, squareInjection, tuple, history, arity] <->
      FiniteTupleFoldStep
        aInjection squareInjection tuple history arity := by
  rw [finiteTupleFoldStepFormula, FOFormula.satisfies_boundedAll]
  simp only [satisfies_finiteTupleFoldStepExistentials]
  change
    (∀ index : LCarrier.{u}, index.1 ∈ arity.1 →
      ∃ indexSucc entry entryCode current next pair : LCarrier.{u},
        FOFormula.Satisfies LMem finiteTupleFoldStepBodyFormula
          (snoc (snoc (snoc (snoc (snoc (snoc
            (snoc ![aInjection, squareInjection, tuple, history, arity]
              index)
            indexSucc) entry) entryCode) current) next) pair)) ↔
      FiniteTupleFoldStep
        aInjection squareInjection tuple history arity
  constructor
  · intro h index hindex
    rcases h index hindex with
      ⟨indexSucc, entry, entryCode, current, next, pair, hbody⟩
    refine ⟨indexSucc, entry, entryCode, current, next, pair, ?_⟩
    rw [finiteTupleFoldStep_assignment,
      satisfies_finiteTupleFoldStepBodyFormula] at hbody
    exact hbody
  · intro h index hindex
    rcases h index hindex with
      ⟨indexSucc, entry, entryCode, current, next, pair, hbody⟩
    refine ⟨indexSucc, entry, entryCode, current, next, pair, ?_⟩
    rw [finiteTupleFoldStep_assignment,
      satisfies_finiteTupleFoldStepBodyFormula]
    exact hbody

/-- Semantic content of one complete finite-fold certificate. -/
def FiniteTupleFoldCertificate
    (zero a kappa aInjection squareInjection tuple output
      arity aritySucc history : LCarrier.{u}) : Prop :=
  ZFSet.IsFunc arity.1 a.1 tuple.1 /\
    ZFSet.IsFunc aritySucc.1 kappa.1 history.1 /\
    ZFSet.pair zero.1 zero.1 ∈ history.1 /\
    FiniteTupleFoldStep
      aInjection squareInjection tuple history arity /\
    exists current pair : LCarrier.{u},
      ZFSet.pair arity.1 current.1 ∈ history.1 /\
        pair.1 = ZFSet.pair arity.1 current.1 /\
        ZFSet.pair pair.1 output.1 ∈ squareInjection.1

/-- Select the five parameters of `finiteTupleFoldStepFormula` from the
certificate layout. -/
def finiteTupleFoldStepRename : Fin 5 -> Fin 11 :=
  ![4, 5, 6, 10, 8]

 theorem comp_finiteTupleFoldStepRename
    (omega zero a kappa aInjection squareInjection tuple output
      arity aritySucc history : LCarrier.{u}) :
    (fun i =>
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple,
        output, arity, aritySucc, history]
        (finiteTupleFoldStepRename i)) =
      ![aInjection, squareInjection, tuple, history, arity] := by
  funext i
  fin_cases i <;> rfl

/--
Layout
`[omega, zero, a, kappa, aInjection, squareInjection, tuple, output,
  arity, aritySucc, history]`.
-/
def finiteTupleFoldCertificateFormula : FOFormula 11 :=
  .conj
    (TextbookDefFormula.isFunctionAt
      (6 : Fin 11) (8 : Fin 11) (2 : Fin 11))
    (.conj
      (TextbookDefFormula.isFunctionAt
        (10 : Fin 11) (9 : Fin 11) (3 : Fin 11))
      (.conj
        (TextbookDefFormula.graphValueAt
          (10 : Fin 11) (1 : Fin 11) (1 : Fin 11))
        (.conj
          (FOFormula.rename finiteTupleFoldStepRename
            finiteTupleFoldStepFormula)
          (.ex (.ex
            (.conj
              (TextbookDefFormula.graphValueAt
                (10 : Fin 13) (8 : Fin 13) (11 : Fin 13))
              (.conj
                (Delta0Formula.kuratowskiPairEqAt
                  (12 : Fin 13) (8 : Fin 13) (11 : Fin 13)).toFO
                (TextbookDefFormula.graphValueAt
                  (5 : Fin 13) (12 : Fin 13) (7 : Fin 13)))))))))

 theorem finiteTupleFoldCertificate_final_assignment
    (omega zero a kappa aInjection squareInjection tuple output
      arity aritySucc history current pair : LCarrier.{u}) :
    snoc (snoc
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple,
        output, arity, aritySucc, history] current) pair =
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple,
        output, arity, aritySucc, history, current, pair] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_finiteTupleFoldCertificateFormula
    (omega zero a kappa aInjection squareInjection tuple output
      arity aritySucc history : LCarrier.{u}) :
    FOFormula.Satisfies LMem finiteTupleFoldCertificateFormula
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple,
        output, arity, aritySucc, history] <->
      FiniteTupleFoldCertificate zero a kappa aInjection squareInjection
        tuple output arity aritySucc history := by
  simp only [finiteTupleFoldCertificateFormula, FOFormula.Satisfies,
    Constructible.Model.satisfies_isFunctionAt_lCarrier,
    Constructible.Model.satisfies_graphValueAt_lCarrier,
    FOFormula.satisfies_rename,
    comp_finiteTupleFoldStepRename,
    satisfies_finiteTupleFoldStepFormula,
    Constructible.Model.satisfies_kuratowskiPairEqAt_lCarrier_generic,
    FiniteTupleFoldCertificate]
  constructor
  · rintro ⟨htuple, hhistory, hzero, hstep,
      current, pair, hfinal⟩
    rw [finiteTupleFoldCertificate_final_assignment] at hfinal
    exact ⟨htuple, hhistory, hzero, hstep, current, pair, hfinal⟩
  · rintro ⟨htuple, hhistory, hzero, hstep,
      current, pair, hfinal⟩
    refine ⟨htuple, hhistory, hzero, hstep,
      current, pair, ?_⟩
    rw [finiteTupleFoldCertificate_final_assignment]
    exact hfinal

/-- A tuple/output pair is related when some standard finite arity and some
finite fold history give the output. -/
def FiniteTupleFoldRel
    (omega zero a kappa aInjection squareInjection
      tuple output : LCarrier.{u}) : Prop :=
  exists arity : LCarrier.{u}, arity.1 ∈ omega.1 /\
    exists aritySucc : LCarrier.{u},
      aritySucc.1 = insert arity.1 arity.1 /\
        exists history : LCarrier.{u},
          FiniteTupleFoldCertificate zero a kappa
            aInjection squareInjection tuple output
            arity aritySucc history

/--
Layout
`[omega, zero, a, kappa, aInjection, squareInjection, tuple, output]`.
-/
def finiteTupleFoldRelationFormula : FOFormula 8 :=
  .ex
    (.conj
      (.mem (8 : Fin 9) (0 : Fin 9))
      (.ex
        (.conj
          (Delta0Formula.successorFOAt
            (9 : Fin 10) (8 : Fin 10))
          (.ex finiteTupleFoldCertificateFormula))))

 theorem finiteTupleFoldRelation_assignment
    (omega zero a kappa aInjection squareInjection tuple output
      arity aritySucc history : LCarrier.{u}) :
    snoc (snoc (snoc
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple, output]
      arity) aritySucc) history =
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple, output,
        arity, aritySucc, history] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_finiteTupleFoldRelationFormula
    (omega zero a kappa aInjection squareInjection tuple output :
      LCarrier.{u}) :
    FOFormula.Satisfies LMem finiteTupleFoldRelationFormula
      ![omega, zero, a, kappa, aInjection, squareInjection, tuple, output] <->
      FiniteTupleFoldRel omega zero a kappa
        aInjection squareInjection tuple output := by
  simp only [finiteTupleFoldRelationFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier,
    FiniteTupleFoldRel]
  constructor
  · rintro ⟨arity, harity, aritySucc, hsucc, history, hcertificate⟩
    rw [finiteTupleFoldRelation_assignment,
      satisfies_finiteTupleFoldCertificateFormula] at hcertificate
    exact ⟨arity, harity, aritySucc, hsucc, history, hcertificate⟩
  · rintro ⟨arity, harity, aritySucc, hsucc, history, hcertificate⟩
    refine ⟨arity, harity, aritySucc, hsucc, history, ?_⟩
    rw [finiteTupleFoldRelation_assignment,
      satisfies_finiteTupleFoldCertificateFormula]
    exact hcertificate

/-! ## Raw functionality and the two finite inductions -/















/-! ## Semantic uniqueness of the fold relation -/





/-! ## A genuine finite history for every tuple -/

/-- Package two members of `kappa` as a member of `kappa × kappa`. -/
 def finiteTupleProductPoint
    (kappa : LCarrier.{u})
    (left right : RelationCarrier LMem kappa) :
    RelationCarrier LMem (prodLCarrier kappa kappa) :=
  ⟨orderedPairLCarrier left.1 right.1, by
    change ZFSet.pair left.1.1 right.1.1 ∈
      ZFSet.prod kappa.1 kappa.1
    rw [ZFSet.pair_mem_prod]
    exact ⟨left.2, right.2⟩⟩

/-- The external recursion used only to exhibit one finite internal history.
Every value lies in `kappa`, because each successor is read from the genuine
internal square-injection graph. -/
 noncomputable def finiteTupleFoldValues
    {a kappa aInjection squareInjection : LCarrier.{u}}
    {n : Nat}
    (haInjection : IsInjection LMem aInjection a kappa)
    (hsquareInjection : IsInjection LMem squareInjection
      (prodLCarrier kappa kappa) kappa)
    (zero : RelationCarrier LMem kappa)
    (entries : Fin n → RelationCarrier LMem a) :
    Nat → RelationCarrier LMem kappa
  | 0 => zero
  | i + 1 =>
      if hi : i < n then
        hsquareInjection.toFun
          (finiteTupleProductPoint kappa
            (finiteTupleFoldValues
              haInjection hsquareInjection zero entries i)
            (haInjection.toFun (entries ⟨i, hi⟩)))
      else
        finiteTupleFoldValues
          haInjection hsquareInjection zero entries i





/-! ## Replacement constructs the complete injection graph -/









end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalFiniteTupleInjection


