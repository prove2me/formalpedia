-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library15
-- name    : CH_ConstructibleGCH_Library15
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:50:26.996583+00:00
-- url     : https://prove2.me/theorems/75005822-92fa-433f-90e5-3c2f827c470e
-- title:
--   Graph lookup and well-founded local recursion
-- statement:
--   Coded relation graphs support lookup and restriction to predecessor domains. This library provides the corresponding absolute formulas and the class-recursion and local-solution interfaces used by the textbook E construction.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookGraphLookupAbsolute.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookClassRecursion.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookLocalRecursion.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookLocalRecursionBridge.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library14
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookGraphLookupAbsolute -/
section GCHSource_Work_CUGCH_TextbookGraphLookupAbsolute
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Absolute lookup in an arbitrary set-coded graph

For a set `graph` and a key `key`, `uniqueGraphLookupZF graph key` returns the
unique `value` whose Kuratowski pair `<key,value>` belongs to `graph`.  If
there is no such unique value, it returns the empty set.  This is a genuinely
total metatheoretic operation: `Classical.choose` is used only after the
existence-and-uniqueness proposition has been established, and is not used to
assert that an arbitrary relation is functional.

The graph formula has free-variable layout `[graph,key,output]`.  Its success
branch says that `output` is a graph value at `key` and is the only such
value.  Its failure branch says that no unique graph value exists and that
`output` is empty.  The formula uses only membership, equality, logical
connectives, and quantifiers.

The main point in the restricted-semantics proof is not assumed: if `graph`
belongs to a transitive model and `<key,value>` belongs to `graph`, then the
Kuratowski pair and hence its right coordinate `value` belong to the model.
Thus model-internal and ambient existence-and-uniqueness agree even when
`graph` is not a function.
-/

section

open Set

universe u

namespace Constructible

noncomputable section

/-- `value` is the unique value occurring at `key` in the arbitrary
Kuratowski-pair relation `graph`. -/
def IsUniqueGraphValue (graph key value : ZFSet.{u}) : Prop :=
  ZFSet.pair key value ∈ graph ∧
    ∀ other : ZFSet.{u}, ZFSet.pair key other ∈ graph → other = value

/-- The unique value at `key`, totalized by the empty set when the relation
does not have exactly one value there.  Choice is only metatheoretic here. -/
noncomputable def uniqueGraphLookupZF
    (graph key : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph then
      Classical.choose h
    else
      ∅

theorem existsUnique_graphValue_iff
    {graph key : ZFSet.{u}} :
    (∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph) ↔
      ∃ value : ZFSet.{u}, IsUniqueGraphValue graph key value := by
  rfl

/-- A displayed value with the required uniqueness is the total lookup. -/
theorem uniqueGraphLookupZF_eq_of_unique
    {graph key value : ZFSet.{u}}
    (hvalue : ZFSet.pair key value ∈ graph)
    (hunique : ∀ other : ZFSet.{u},
      ZFSet.pair key other ∈ graph → other = value) :
    uniqueGraphLookupZF graph key = value := by
  let h : ∃! other : ZFSet.{u}, ZFSet.pair key other ∈ graph :=
    ⟨value, hvalue, hunique⟩
  rw [uniqueGraphLookupZF, dif_pos h]
  exact ((Classical.choose_spec h).2 value hvalue).symm

/-- In the non-unique case the total lookup is exactly the empty set. -/
theorem uniqueGraphLookupZF_eq_empty_of_not_unique
    {graph key : ZFSet.{u}}
    (h : ¬ ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph) :
    uniqueGraphLookupZF graph key = (∅ : ZFSet.{u}) := by
  simp only [uniqueGraphLookupZF, dif_neg h]





namespace TextbookDefFormula

/-- The output coordinate is a graph value at the key and every other graph
value at that key is equal to it. -/
def uniqueGraphValueAt {n : Nat}
    (graph key output : Fin n) : FOFormula n :=
  .conj
    (graphValueAt graph key output)
    (.all <| .imp
      (graphValueAt graph.castSucc key.castSucc (Fin.last n))
      (.eq (Fin.last n) output.castSucc))

/-- There exists a unique graph value at the designated key. -/
def hasUniqueGraphValueAt {n : Nat}
    (graph key : Fin n) : FOFormula n :=
  .ex (uniqueGraphValueAt graph.castSucc key.castSucc (Fin.last n))

/-- Total graph-lookup formula with layout `[graph,key,output]`. -/
def uniqueGraphLookupFormula : FOFormula 3 :=
  .disj
    (uniqueGraphValueAt (0 : Fin 3) (1 : Fin 3) (2 : Fin 3))
    (.conj
      (.neg (hasUniqueGraphValueAt (0 : Fin 3) (1 : Fin 3)))
      (Delta0Formula.emptyDeltaAt (2 : Fin 3)).toFO)

@[simp]
theorem satisfies_uniqueGraphValueAt {n : Nat}
    (graph key output : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (uniqueGraphValueAt graph key output) s ↔
      IsUniqueGraphValue (s graph) (s key) (s output) := by
  simp only [uniqueGraphValueAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphValueAt, snoc_last, snoc_castSucc,
    IsUniqueGraphValue]

@[simp]
theorem satisfies_hasUniqueGraphValueAt {n : Nat}
    (graph key : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (hasUniqueGraphValueAt graph key) s ↔
      ∃ value : ZFSet.{u}, IsUniqueGraphValue (s graph) (s key) value := by
  simp only [hasUniqueGraphValueAt, FOFormula.Satisfies,
    satisfies_uniqueGraphValueAt, snoc_last, snoc_castSucc]

theorem satisfies_uniqueGraphLookupFormula_components
    (graph key output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem uniqueGraphLookupFormula
        ![graph, key, output] ↔
      IsUniqueGraphValue graph key output ∨
        ((¬ ∃ value : ZFSet.{u}, IsUniqueGraphValue graph key value) ∧
          output = (∅ : ZFSet.{u})) := by
  simp only [uniqueGraphLookupFormula, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_uniqueGraphValueAt,
    satisfies_hasUniqueGraphValueAt, Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_emptyDeltaAt]
  rfl

/-- Exact ambient semantics of the total graph-lookup formula. -/
@[simp]
theorem satisfies_uniqueGraphLookupFormula_iff
    (graph key output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem uniqueGraphLookupFormula
        ![graph, key, output] ↔
      output = uniqueGraphLookupZF graph key := by
  rw [satisfies_uniqueGraphLookupFormula_components]
  constructor
  · rintro (houtput | ⟨hnot, hempty⟩)
    · exact (uniqueGraphLookupZF_eq_of_unique
        houtput.1 houtput.2).symm
    · have hnotUnique :
          ¬ ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph := by
        simpa only [existsUnique_graphValue_iff] using hnot
      rw [hempty, uniqueGraphLookupZF_eq_empty_of_not_unique hnotUnique]
  · intro houtput
    by_cases hunique :
        ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph
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

end TextbookDefFormula

namespace Model

/-- A graph value belongs to any transitive set containing the graph.  No
functionality assumption on `graph` is used. -/
theorem graphValue_mem_of_transitive
    {M graph key value : ZFSet.{u}} (hM : M.IsTransitive)
    (hgraph : graph ∈ M)
    (hvalue : ZFSet.pair key value ∈ graph) :
    value ∈ M := by
  have hpairM : ZFSet.pair key value ∈ M :=
    hM.mem_trans hvalue hgraph
  have hcoordinatesM : ({key, value} : ZFSet.{u}) ∈ M :=
    hM.mem_trans (by simp [ZFSet.pair]) hpairM
  exact hM.mem_trans (by simp) hcoordinatesM

 theorem satisfiesIn_lookupAll_iff
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

 theorem satisfiesIn_lookupImp_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp left right) s ↔
      (SatisfiesIn M left s → SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.imp, FOFormula.disj, SatisfiesIn]
  tauto

 theorem satisfiesIn_lookupDisj_iff
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.disj left right) s ↔
      SatisfiesIn M left s ∨ SatisfiesIn M right s := by
  classical
  simp only [FOFormula.disj, SatisfiesIn]
  tauto

theorem satisfiesIn_textbookGraphValueAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (graph key value : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (TextbookDefFormula.graphValueAt graph key value) s ↔
      ZFSet.pair (s key) (s value) ∈ s graph := by
  rw [TextbookDefFormula.graphValueAt,
    satisfiesIn_delta0_iff hM
      (TextbookDefFormula.graphValueDeltaAt graph key value) s hs,
    Delta0Formula.satisfies_toFO,
    TextbookDefFormula.satisfies_graphValueDeltaAt]

/-- Restricted semantics of unique graph values is ambient semantics.  The
unbounded uniqueness quantifier causes no loss, because every competing graph
value is forced into the transitive carrier by pair membership. -/
theorem satisfiesIn_uniqueGraphValueAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (graph key output : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (TextbookDefFormula.uniqueGraphValueAt graph key output) s ↔
      IsUniqueGraphValue (s graph) (s key) (s output) := by
  rw [TextbookDefFormula.uniqueGraphValueAt]
  simp only [SatisfiesIn, satisfiesIn_lookupAll_iff,
    satisfiesIn_lookupImp_iff]
  constructor
  · rintro ⟨hvalueFormula, huniqueFormula⟩
    have hvalue := (satisfiesIn_textbookGraphValueAt_iff hM
      graph key output s hs).mp hvalueFormula
    refine ⟨hvalue, ?_⟩
    intro other hother
    have hotherM : other ∈ M :=
      graphValue_mem_of_transitive hM (hs graph) hother
    have hsOther : ∀ i, snoc s other i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hotherM
      · simpa using hs j
    have hotherFormula :
        SatisfiesIn (M : Set ZFSet.{u})
          (TextbookDefFormula.graphValueAt
            graph.castSucc key.castSucc (Fin.last n))
          (snoc s other) := by
      apply (satisfiesIn_textbookGraphValueAt_iff hM
        graph.castSucc key.castSucc (Fin.last n)
        (snoc s other) hsOther).mpr
      simpa only [snoc_last, snoc_castSucc] using hother
    have heq := huniqueFormula other hotherM hotherFormula
    simpa only [SatisfiesIn, snoc_last, snoc_castSucc] using heq
  · rintro ⟨hvalue, hunique⟩
    constructor
    · exact (satisfiesIn_textbookGraphValueAt_iff hM
        graph key output s hs).mpr hvalue
    · intro other hotherM hotherFormula
      have hsOther : ∀ i, snoc s other i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hotherM
        · simpa using hs j
      have hother := (satisfiesIn_textbookGraphValueAt_iff hM
        graph.castSucc key.castSucc (Fin.last n)
        (snoc s other) hsOther).mp hotherFormula
      have heq : other = s output :=
        hunique other (by simpa only [snoc_last, snoc_castSucc] using hother)
      simpa only [SatisfiesIn, snoc_last, snoc_castSucc] using heq

theorem satisfiesIn_hasUniqueGraphValueAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (graph key : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (TextbookDefFormula.hasUniqueGraphValueAt graph key) s ↔
      ∃ value : ZFSet.{u},
        IsUniqueGraphValue (s graph) (s key) value := by
  rw [TextbookDefFormula.hasUniqueGraphValueAt]
  simp only [SatisfiesIn]
  constructor
  · rintro ⟨value, hvalueM, hvalueFormula⟩
    refine ⟨value, ?_⟩
    simpa only [snoc_last, snoc_castSucc] using
      (satisfiesIn_uniqueGraphValueAt_iff hM
      graph.castSucc key.castSucc (Fin.last n)
      (snoc s value) (by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · simpa using hs j)).mp hvalueFormula
  · rintro ⟨value, hvalue⟩
    have hvalueM : value ∈ M :=
      graphValue_mem_of_transitive hM (hs graph) hvalue.1
    refine ⟨value, hvalueM, ?_⟩
    apply (satisfiesIn_uniqueGraphValueAt_iff hM
      graph.castSucc key.castSucc (Fin.last n)
      (snoc s value) (by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · simpa using hs j)).mpr
    simpa only [snoc_last, snoc_castSucc] using hvalue

/-- Exact restricted semantics of total lookup. -/
theorem satisfiesIn_uniqueGraphLookupFormula_iff
    {M graph key output : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (hgraph : graph ∈ M) (hkey : key ∈ M) (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.uniqueGraphLookupFormula
        ![graph, key, output] ↔
      output = uniqueGraphLookupZF graph key := by
  have hs : ∀ i : Fin 3, ![graph, key, output] i ∈ M := by
    intro i
    fin_cases i
    · exact hgraph
    · exact hkey
    · exact houtput
  rw [TextbookDefFormula.uniqueGraphLookupFormula]
  have hsuccess := satisfiesIn_uniqueGraphValueAt_iff hM.1
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
    ![graph, key, output] hs
  have hexists := satisfiesIn_hasUniqueGraphValueAt_iff hM.1
    (0 : Fin 3) (1 : Fin 3) ![graph, key, output] hs
  have hempty := satisfiesIn_delta0_iff hM.1
    (Delta0Formula.emptyDeltaAt (2 : Fin 3))
    ![graph, key, output] hs
  have hsuccess' :
      SatisfiesIn (M : Set ZFSet.{u})
          (TextbookDefFormula.uniqueGraphValueAt
            (0 : Fin 3) (1 : Fin 3) (2 : Fin 3))
          ![graph, key, output] ↔
        IsUniqueGraphValue graph key output := by
    simpa using hsuccess
  have hexists' :
      SatisfiesIn (M : Set ZFSet.{u})
          (TextbookDefFormula.hasUniqueGraphValueAt
            (0 : Fin 3) (1 : Fin 3))
          ![graph, key, output] ↔
        ∃ value : ZFSet.{u}, IsUniqueGraphValue graph key value := by
    simpa using hexists
  have hempty' :
      SatisfiesIn (M : Set ZFSet.{u})
          (Delta0Formula.emptyDeltaAt (2 : Fin 3)).toFO
          ![graph, key, output] ↔ output = (∅ : ZFSet.{u}) := by
    rw [hempty, Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_emptyDeltaAt]
    rfl
  rw [satisfiesIn_lookupDisj_iff]
  simp only [SatisfiesIn]
  rw [hsuccess', hexists', hempty']
  constructor
  · rintro (hvalue | ⟨hnot, hzero⟩)
    · exact (uniqueGraphLookupZF_eq_of_unique
        hvalue.1 hvalue.2).symm
    · have hnotUnique :
          ¬ ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph := by
        simpa only [existsUnique_graphValue_iff] using hnot
      rw [hzero, uniqueGraphLookupZF_eq_empty_of_not_unique hnotUnique]
  · intro hlookup
    by_cases hunique :
        ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph
    · rcases hunique with ⟨value, hvalue, hunique⟩
      left
      have hlookupValue := uniqueGraphLookupZF_eq_of_unique hvalue hunique
      rw [hlookup, hlookupValue]
      exact ⟨hvalue, hunique⟩
    · right
      constructor
      · simpa only [← existsUnique_graphValue_iff] using hunique
      · rw [hlookup,
          uniqueGraphLookupZF_eq_empty_of_not_unique hunique]

/-- The total lookup is closed in every transitive ZF model on model
arguments. -/
theorem uniqueGraphLookupZF_mem_of_isTransitiveZFModel
    {M graph key : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hgraph : graph ∈ M) (_hkey : key ∈ M) :
    uniqueGraphLookupZF graph key ∈ M := by
  by_cases hunique :
      ∃! value : ZFSet.{u}, ZFSet.pair key value ∈ graph
  · rcases hunique with ⟨value, hvalue, hunique⟩
    rw [uniqueGraphLookupZF_eq_of_unique hvalue hunique]
    exact graphValue_mem_of_transitive hM.1 hgraph hvalue
  · rw [uniqueGraphLookupZF_eq_empty_of_not_unique hunique]
    exact empty_mem_of_isTransitiveZFModel hM



end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookGraphLookupAbsolute


/- Source module: Solutions.Work_CUGCH_TextbookClassRecursion -/
section GCHSource_Work_CUGCH_TextbookClassRecursion
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Textbook recursion on a well-founded set-like class relation

This file formalizes the recursion theorem of Section 6.1 in Wang Fangting,
*Axiomatic Set Theory*.  The hypotheses are the textbook hypotheses:
`R` is a relation on `A`, every nonempty actual set contained in `A` has an
`R`-minimal member, and every predecessor class is represented by an actual
`ZFSet`.

The construction uses `wellFounded_classRel_zfSubtype`, which was derived
from precisely those hypotheses by the preceding textbook closure and
class-minimum arguments.  Lean's `WellFounded.fix` below merely implements
the induction supplied by that derived theorem; global `WellFounded` is not
an additional assumption.

For every `x in A`, the second argument passed to `step` is the actual
Kuratowski graph

`{ <y,F(y)> | y R x } : ZFSet`,

constructed by `predecessorRestrictionGraph` over the displayed predecessor
set.  This is an ambient `ZFSet` statement.  It does not assert that the graph
belongs to a particular inner model.
-/

section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## The recursive construction -/

/-- The temporary total function used when forming the predecessor graph at
`x`.  On an `R`-predecessor it returns the already constructed value; away
from the predecessor relation it is totalized by the empty set.  Only its
values on `displayedPredecessors` enter the graph. -/
noncomputable def textbookClassRecursionPrevious
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hrelation : IsRelationOn A R)
    (x : {z : ZFSet.{u} // z ∈ A})
    (previous : forall y : {z : ZFSet.{u} // z ∈ A},
      ClassRel R y.1 x.1 -> ZFSet.{u})
    (y : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hyx : ClassRel R y x.1 then
    previous ⟨y, hrelation.left_mem hyx⟩ hyx
  else
    ∅

/-- The induction step supplied to the derived well-founded induction on
the subtype `A`.  Its graph argument is an actual `ZFSet`. -/
noncomputable def textbookClassRecursionFunctional
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (x : {z : ZFSet.{u} // z ∈ A})
    (previous : forall y : {z : ZFSet.{u} // z ∈ A},
      ClassRel R y.1 x.1 -> ZFSet.{u}) : ZFSet.{u} :=
  step x.1 <| predecessorRestrictionGraph
    (displayedPredecessors A R hR.2.2 x.1)
    (textbookClassRecursionPrevious hR.1 x previous)

/-- The recursively constructed function on the subtype `A`.

`WellFounded.fix` is used only with the relation obtained from
`wellFounded_classRel_zfSubtype hR`; it therefore implements the induction
already proved from the textbook set-minimum and set-likeness hypotheses. -/
noncomputable def textbookClassRecursionOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) :
    {z : ZFSet.{u} // z ∈ A} -> ZFSet.{u} :=
  (wellFounded_classRel_zfSubtype hR).fix
    (textbookClassRecursionFunctional hR step)

/-- The textbook recursive function, totalized by `empty` away from `A`.
The off-domain value has no mathematical role in the recursion theorem. -/
noncomputable def textbookClassRecursion
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hx : x ∈ A then
    textbookClassRecursionOn hR step ⟨x, hx⟩
  else
    ∅

/-- The exact recursion equation used in the textbook theorem.  In
particular, `displayedPredecessors` is an actual set representing the full
predecessor class. -/
def SatisfiesTextbookClassRecursion
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (F : ZFSet.{u} -> ZFSet.{u}) : Prop :=
  forall x, x ∈ A ->
    F x = step x (predecessorRestrictionGraph
      (displayedPredecessors A R hsetLike x) F)

@[simp]
theorem textbookClassRecursion_eq_empty_of_not_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∉ A) :
    textbookClassRecursion hR step x = ∅ := by
  simp [textbookClassRecursion, hx]

@[simp]
theorem textbookClassRecursion_eq_on
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A) :
    textbookClassRecursion hR step x =
      textbookClassRecursionOn hR step ⟨x, hx⟩ := by
  simp [textbookClassRecursion, hx]





/-! ## Uniqueness -/





end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookClassRecursion


/- Source module: Solutions.Work_CUGCH_TextbookLocalRecursion -/
section GCHSource_Work_CUGCH_TextbookLocalRecursion
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The local-graph proof of textbook class recursion

This file formalizes the existence proof on page 108 of Wang Fangting,
*Axiomatic Set Theory*.  It deliberately constructs the local solutions
`f_x` as actual Kuratowski graphs rather than defining the final class
function first.

For a point `x` the construction is as follows.

* the local domain is `d_x = {x} ∪ cl(A,x,R)`;
* for every immediate predecessor `y R x`, induction supplies a local graph
  `f_y` on `d_y`;
* the local graphs agree on intersections of their domains;
* their set-indexed union `q` is consequently a function graph, with domain
  exactly `cl(A,x,R)`;
* adjoining the pair carrying the value at `x` produces `f_x`.

The only use of Lean's `WellFounded` API is to organize the induction after
`wellFounded_classRel_zfSubtype` has derived it from the textbook set-minimum
and set-likeness hypotheses.  No global recursion solution is assumed or
used.  Every graph occurring below is an ambient `ZFSet`; this file makes no
claim that one of these graphs belongs to an inner model.
-/

section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## Local solutions and overlap uniqueness -/

/-- The recursion equation restricted to the textbook local domain `d_x`. -/
def SatisfiesTextbookLocalRecursion
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) (value : ZFSet.{u} → ZFSet.{u}) : Prop :=
  ∀ t, t ∈ localRecursionDomain A R hsetLike x →
    value t = step t (predecessorRestrictionGraph
      (displayedPredecessors A R hsetLike t) value)

/-- A local solution in the literal set-theoretic form used in the textbook.
`graph` is an actual set of Kuratowski pairs, while `value` records its unique
value semantics in a convenient Lean form. -/
structure TextbookLocalSolution
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) where
  value : ZFSet.{u} → ZFSet.{u}
  graph : ZFSet.{u}
  graph_eq : graph = predecessorRestrictionGraph
    (localRecursionDomain A R hsetLike x) value
  satisfies : SatisfiesTextbookLocalRecursion A R hsetLike step x value

/-- Two local solutions agree wherever their local domains overlap.  This is
the property labelled (3) in the textbook. -/
theorem textbookLocalSolutions_agreeOn_intersection
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    {step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    {x y : ZFSet.{u}} (hx : x ∈ A) (hy : y ∈ A)
    (fx : TextbookLocalSolution A R hR.2.2 step x)
    (fy : TextbookLocalSolution A R hR.2.2 step y) :
    ∀ t, t ∈ localRecursionDomain A R hR.2.2 x ∩
        localRecursionDomain A R hR.2.2 y →
      fx.value t = fy.value t := by
  apply recursionSolutions_agreeOn hR.2.1
  · intro t ht
    exact localRecursionDomain_subset hR.2.2 hx
      (ZFSet.mem_inter.mp ht).1
  · intro t ht z hzt
    have ht' := ZFSet.mem_inter.mp ht
    exact ZFSet.mem_inter.mpr
      ⟨localRecursionDomain_predecessorClosed hR.1 hR.2.2 hx ht'.1 hzt,
        localRecursionDomain_predecessorClosed hR.1 hR.2.2 hy ht'.2 hzt⟩
  · intro t ht
    exact displayedPredecessors_spec hR.2.2
      (localRecursionDomain_subset hR.2.2 hx (ZFSet.mem_inter.mp ht).1)
  · intro t ht
    exact fx.satisfies t (ZFSet.mem_inter.mp ht).1
  · intro t ht
    exact fy.satisfies t (ZFSet.mem_inter.mp ht).2



/-! ## A closure point lies strictly below its top -/

/-- Membership in a finite predecessor layer gives a nonempty finite
`R`-chain to the top point.  The chain is stated on the subtype of `A`, where
the textbook class-minimum theorem provides genuine well-foundedness. -/
theorem transGen_classRel_of_mem_predecessorLayer
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R)
    {x z : ZFSet.{u}} (hx : x ∈ A) {n : Nat}
    (hz : z ∈ predecessorLayer A R hsetLike x n) :
    Relation.TransGen
      (fun y x : {w : ZFSet.{u} // w ∈ A} => ClassRel R y.1 x.1)
      ⟨z, predecessorLayer_subset hsetLike hx n hz⟩
      ⟨x, hx⟩ := by
  induction n generalizing z with
  | zero =>
      have hzSpec := (displayedPredecessors_spec hsetLike hx z).mp
        (by simpa only [predecessorLayer_zero] using hz)
      exact Relation.TransGen.single hzSpec.2
  | succ n ih =>
      rcases (mem_predecessorLayer_succ_iff hsetLike hx n).mp hz with
        ⟨y, hyLayer, hzA, hzy⟩
      have hyA : y ∈ A := predecessorLayer_subset hsetLike hx n hyLayer
      have htail := ih hyLayer
      exact Relation.TransGen.head hzy htail

/-- A point is not in its own finite predecessor closure.  This is the fact
which makes adjoining the top graph pair a genuine one-point extension. -/
theorem not_mem_predecessorClosure_self
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R) {x : ZFSet.{u}} (hx : x ∈ A) :
    x ∉ predecessorClosure A R hR.2.2 x := by
  intro hxx
  rcases mem_predecessorClosure_iff.mp hxx with ⟨n, hxn⟩
  have hcycle := transGen_classRel_of_mem_predecessorLayer
    hR.2.2 hx hxn
  exact (wellFounded_classRel_zfSubtype hR).transGen.irrefl.irrefl
    ⟨x, hx⟩ hcycle

/-! ## Gluing the predecessor-local graphs -/

section Glue

variable {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
variable (hR : IsWellFoundedSetLikeOn A R)
variable (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
variable {x : ZFSet.{u}}

/-- The actual set `d = ⋃ {d_y | y R x}` from the textbook proof. -/
noncomputable def predecessorLocalDomainUnion (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.iUnion fun y : ZFCarrier
      (displayedPredecessors A R hR.2.2 x) =>
    localRecursionDomain A R hR.2.2 y.1

/-- The domain of the union of predecessor-local solutions is exactly
`cl(A,x,R)`. -/
theorem predecessorLocalDomainUnion_eq_predecessorClosure
    (hx : x ∈ A) :
    predecessorLocalDomainUnion hR x =
      predecessorClosure A R hR.2.2 x := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases ZFSet.mem_iUnion.mp hz with ⟨y, hzy⟩
    have hySpec := (displayedPredecessors_spec hR.2.2 hx y.1).mp y.2
    rcases mem_localRecursionDomain_iff.mp hzy with hzx | hzClosure
    · subst z
      apply mem_predecessorClosure_iff.mpr
      refine ⟨0, ?_⟩
      rw [predecessorLayer_zero]
      exact y.2
    · exact predecessorClosure_subset_of_rel hR.1 hR.2.2 hySpec.2
        hzClosure
  · intro hz
    rcases mem_predecessorClosure_iff.mp hz with ⟨n, hzn⟩
    have hlevels : ∀ m, ∀ z,
        z ∈ predecessorLayer A R hR.2.2 x m →
          z ∈ predecessorLocalDomainUnion hR x := by
      intro m
      induction m with
      | zero =>
          intro z hz0
          let zPred : ZFCarrier
              (displayedPredecessors A R hR.2.2 x) :=
            ⟨z, by simpa only [predecessorLayer_zero] using hz0⟩
          apply ZFSet.mem_iUnion.mpr
          refine ⟨zPred, ?_⟩
          exact mem_localRecursionDomain_iff.mpr (Or.inl rfl)
      | succ m ih =>
          intro z hzs
          rcases (mem_predecessorLayer_succ_iff hR.2.2 hx m).mp hzs with
            ⟨y, hym, _hzA, hzy⟩
          have hyUnion := ih y hym
          rcases ZFSet.mem_iUnion.mp hyUnion with ⟨w, hyw⟩
          have hwA := (displayedPredecessors_spec hR.2.2 hx w.1).mp w.2 |>.1
          exact ZFSet.mem_iUnion.mpr
            ⟨w, localRecursionDomain_predecessorClosed
              hR.1 hR.2.2 hwA hyw hzy⟩
    exact hlevels n z hzn

variable (children : ∀ y : ZFCarrier
  (displayedPredecessors A R hR.2.2 x),
    TextbookLocalSolution A R hR.2.2 step y.1)

/-- The actual graph `q = ⋃ {f_y | y R x}`. -/
noncomputable def predecessorLocalGraphUnion : ZFSet.{u} :=
  ZFSet.iUnion fun y : ZFCarrier
      (displayedPredecessors A R hR.2.2 x) =>
    (children y).graph

/-- A totalized value function represented by the glued graph.  At a point
in one of the child domains, it takes the value of one chosen child.  Overlap
agreement below proves that this value is independent of the choice. -/
noncomputable def gluedPredecessorValue (t : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if ht : ∃ y : ZFCarrier
      (displayedPredecessors A R hR.2.2 x),
      t ∈ localRecursionDomain A R hR.2.2 y.1 then
    (children (Classical.choose ht)).value t
  else
    ∅

/-- Every child solution agrees with the glued value throughout its domain. -/
theorem child_value_eq_gluedPredecessorValue
    (hx : x ∈ A)
    (y : ZFCarrier (displayedPredecessors A R hR.2.2 x))
    {t : ZFSet.{u}}
    (ht : t ∈ localRecursionDomain A R hR.2.2 y.1) :
    (children y).value t = gluedPredecessorValue hR step children t := by
  classical
  let hex : ∃ z : ZFCarrier
      (displayedPredecessors A R hR.2.2 x),
      t ∈ localRecursionDomain A R hR.2.2 z.1 := ⟨y, ht⟩
  rw [gluedPredecessorValue, dif_pos hex]
  have hyA := (displayedPredecessors_spec hR.2.2 hx y.1).mp y.2 |>.1
  have hzA := (displayedPredecessors_spec hR.2.2 hx
    (Classical.choose hex).1).mp (Classical.choose hex).2 |>.1
  apply textbookLocalSolutions_agreeOn_intersection hR hyA hzA
    (children y) (children (Classical.choose hex)) t
  exact ZFSet.mem_inter.mpr ⟨ht, Classical.choose_spec hex⟩

/-- The union `q` is precisely the Kuratowski graph of the glued value on
the union of the child domains. -/
theorem predecessorLocalGraphUnion_eq_restrictionGraph (hx : x ∈ A) :
    predecessorLocalGraphUnion hR step children =
      predecessorRestrictionGraph
        (predecessorLocalDomainUnion hR x)
        (gluedPredecessorValue hR step children) := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    rcases ZFSet.mem_iUnion.mp hp with ⟨y, hpy⟩
    rw [(children y).graph_eq] at hpy
    rcases mem_predecessorRestrictionGraph_iff.mp hpy with
      ⟨t, ht, rfl⟩
    apply mem_predecessorRestrictionGraph_iff.mpr
    refine ⟨t, ZFSet.mem_iUnion.mpr ⟨y, ht⟩, ?_⟩
    rw [child_value_eq_gluedPredecessorValue
      (hR := hR) (step := step) (children := children) hx y ht]
  · intro hp
    rcases mem_predecessorRestrictionGraph_iff.mp hp with
      ⟨t, ht, rfl⟩
    rcases ZFSet.mem_iUnion.mp ht with ⟨y, hty⟩
    apply ZFSet.mem_iUnion.mpr
    refine ⟨y, ?_⟩
    rw [(children y).graph_eq]
    apply mem_predecessorRestrictionGraph_iff.mpr
    refine ⟨t, hty, ?_⟩
    rw [child_value_eq_gluedPredecessorValue
      (hR := hR) (step := step) (children := children) hx y hty]

/-- After identifying the domain union with the closure, the graph `q` has
exactly the domain claimed on page 108. -/
theorem predecessorLocalGraphUnion_eq_closureGraph (hx : x ∈ A) :
    predecessorLocalGraphUnion hR step children =
      predecessorRestrictionGraph
        (predecessorClosure A R hR.2.2 x)
        (gluedPredecessorValue hR step children) := by
  rw [predecessorLocalGraphUnion_eq_restrictionGraph
      (hR := hR) (step := step) (children := children) hx,
    predecessorLocalDomainUnion_eq_predecessorClosure hR hx]

/-- The glued value already satisfies the recursion equation throughout
`cl(A,x,R)`. -/
theorem gluedPredecessorValue_satisfies_on_closure
    (hx : x ∈ A)
    {t : ZFSet.{u}}
    (ht : t ∈ predecessorClosure A R hR.2.2 x) :
    gluedPredecessorValue hR step children t =
      step t (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 t)
        (gluedPredecessorValue hR step children)) := by
  have htUnion : t ∈ predecessorLocalDomainUnion hR x := by
    rw [predecessorLocalDomainUnion_eq_predecessorClosure hR hx]
    exact ht
  rcases ZFSet.mem_iUnion.mp htUnion with ⟨y, hty⟩
  have hyA := (displayedPredecessors_spec hR.2.2 hx y.1).mp y.2 |>.1
  calc
    gluedPredecessorValue hR step children t = (children y).value t :=
      (child_value_eq_gluedPredecessorValue
        (hR := hR) (step := step) (children := children) hx y hty).symm
    _ = step t (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 t) (children y).value) :=
      (children y).satisfies t hty
    _ = step t (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 t)
        (gluedPredecessorValue hR step children)) := by
      apply congrArg (step t)
      apply predecessorRestrictionGraph_congr
      intro z hz
      have htA := localRecursionDomain_subset hR.2.2 hyA hty
      have hzt := (displayedPredecessors_spec hR.2.2 htA z).mp hz |>.2
      have hzyDomain := localRecursionDomain_predecessorClosed
        hR.1 hR.2.2 hyA hty hzt
      exact child_value_eq_gluedPredecessorValue
        (hR := hR) (step := step) (children := children)
        hx y hzyDomain

/-! ## Adjoining the top pair -/

/-- The value at the new top point, with the glued predecessor graph as the
second argument of the recursion operator. -/
noncomputable def localTopValue : ZFSet.{u} :=
  step x (predecessorRestrictionGraph
    (displayedPredecessors A R hR.2.2 x)
    (gluedPredecessorValue hR step children))

/-- The value function represented by the graph after adjoining its top
pair. -/
noncomputable def extendedLocalValue (t : ZFSet.{u}) : ZFSet.{u} :=
  by
    classical
    exact if t = x then localTopValue hR step children
    else gluedPredecessorValue hR step children t

/-- The literal graph extension `f_x = q ∪ {⟨x,G(x,q↾x-hat)⟩}`. -/
noncomputable def extendedLocalGraph : ZFSet.{u} :=
  predecessorLocalGraphUnion hR step children ∪
    ({ZFSet.pair x (localTopValue hR step children)} : ZFSet.{u})

@[simp]
theorem extendedLocalValue_at_top :
    extendedLocalValue hR step children x =
      localTopValue hR step children := by
  simp [extendedLocalValue]

theorem extendedLocalValue_eq_glued_of_mem_closure
    (hx : x ∈ A) {t : ZFSet.{u}}
    (ht : t ∈ predecessorClosure A R hR.2.2 x) :
    extendedLocalValue hR step children t =
      gluedPredecessorValue hR step children t := by
  have htx : t ≠ x := by
    intro h
    subst t
    exact not_mem_predecessorClosure_self hR hx ht
  simp [extendedLocalValue, htx]

/-- The adjoined set is exactly the graph of the extended value on `d_x`. -/
theorem extendedLocalGraph_eq_restrictionGraph (hx : x ∈ A) :
    extendedLocalGraph hR step children =
      predecessorRestrictionGraph
        (localRecursionDomain A R hR.2.2 x)
        (extendedLocalValue hR step children) := by
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    rcases ZFSet.mem_union.mp hp with hpq | hpTop
    · rw [predecessorLocalGraphUnion_eq_closureGraph
        (hR := hR) (step := step) (children := children) hx] at hpq
      rcases mem_predecessorRestrictionGraph_iff.mp hpq with
        ⟨t, ht, rfl⟩
      apply mem_predecessorRestrictionGraph_iff.mpr
      refine ⟨t, mem_localRecursionDomain_iff.mpr (Or.inr ht), ?_⟩
      rw [extendedLocalValue_eq_glued_of_mem_closure
        (hR := hR) (step := step) (children := children) hx ht]
    · have hpEq : ZFSet.pair x (localTopValue hR step children) = p := by
        exact (ZFSet.mem_singleton.mp hpTop).symm
      apply mem_predecessorRestrictionGraph_iff.mpr
      refine ⟨x, mem_localRecursionDomain_iff.mpr (Or.inl rfl), ?_⟩
      rw [extendedLocalValue_at_top hR step children]
      exact hpEq
  · intro hp
    rcases mem_predecessorRestrictionGraph_iff.mp hp with
      ⟨t, ht, rfl⟩
    rcases mem_localRecursionDomain_iff.mp ht with rfl | htClosure
    · apply ZFSet.mem_union.mpr
      right
      simp
    · apply ZFSet.mem_union.mpr
      left
      rw [predecessorLocalGraphUnion_eq_closureGraph
        (hR := hR) (step := step) (children := children) hx]
      apply mem_predecessorRestrictionGraph_iff.mpr
      refine ⟨t, htClosure, ?_⟩
      rw [extendedLocalValue_eq_glued_of_mem_closure
        (hR := hR) (step := step) (children := children) hx htClosure]

/-- The extended graph satisfies the recursion equation at every point of
its local domain. -/
theorem extendedLocalValue_satisfies (hx : x ∈ A) :
    SatisfiesTextbookLocalRecursion A R hR.2.2 step x
      (extendedLocalValue hR step children) := by
  intro t ht
  rcases mem_localRecursionDomain_iff.mp ht with htEq | htClosure
  · subst t
    rw [extendedLocalValue_at_top]
    unfold localTopValue
    apply congrArg (step x)
    apply predecessorRestrictionGraph_congr
    intro z hz
    have hzSpec := (displayedPredecessors_spec hR.2.2 hx z).mp hz
    have hzLayer : z ∈ predecessorLayer A R hR.2.2 x 0 := by
      simpa only [predecessorLayer_zero] using hz
    have hzClosure : z ∈ predecessorClosure A R hR.2.2 x :=
      mem_predecessorClosure_iff.mpr ⟨0, hzLayer⟩
    exact extendedLocalValue_eq_glued_of_mem_closure
      (hR := hR) (step := step) (children := children) hx hzClosure |>.symm
  · rw [extendedLocalValue_eq_glued_of_mem_closure
      (hR := hR) (step := step) (children := children) hx htClosure,
      gluedPredecessorValue_satisfies_on_closure
        (hR := hR) (step := step) (children := children) hx htClosure]
    apply congrArg (step t)
    apply predecessorRestrictionGraph_congr
    intro z hz
    have htA := predecessorClosure_subset hR.2.2 hx htClosure
    have hzt := (displayedPredecessors_spec hR.2.2 htA z).mp hz |>.2
    have hzClosure := predecessorClosure_downward_closed
      hR.1 hR.2.2 hx htClosure hzt
    exact (extendedLocalValue_eq_glued_of_mem_closure
      (hR := hR) (step := step) (children := children) hx hzClosure).symm

/-- The local solution assembled from the predecessor-local solutions by
the literal union-and-adjoin construction. -/
noncomputable def assembleTextbookLocalSolution (hx : x ∈ A) :
    TextbookLocalSolution A R hR.2.2 step x where
  value := extendedLocalValue hR step children
  graph := extendedLocalGraph hR step children
  graph_eq := extendedLocalGraph_eq_restrictionGraph
    (hR := hR) (step := step) (children := children) hx
  satisfies := extendedLocalValue_satisfies
    (hR := hR) (step := step) (children := children) hx

end Glue

/-! ## Existence by the textbook local induction -/

/-- For every `x ∈ A`, an actual local solution graph on `d_x` exists.
The induction hypothesis supplies only local solutions at direct
predecessors.  The induction step is exactly the graph union and one-pair
extension developed above; no global recursion function occurs in the
proof. -/
theorem nonempty_textbookLocalSolution
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) :
    ∀ x, x ∈ A → Nonempty (TextbookLocalSolution A R hR.2.2 step x) := by
  intro x hx
  let xA : {z : ZFSet.{u} // z ∈ A} := ⟨x, hx⟩
  change Nonempty (TextbookLocalSolution A R hR.2.2 step xA.1)
  apply (wellFounded_classRel_zfSubtype hR).induction
    (C := fun t => Nonempty
      (TextbookLocalSolution A R hR.2.2 step t.1)) xA
  intro t ih
  let children : ∀ y : ZFCarrier
      (displayedPredecessors A R hR.2.2 t.1),
      TextbookLocalSolution A R hR.2.2 step y.1 := fun y => by
    have hySpec := (displayedPredecessors_spec hR.2.2 t.2 y.1).mp y.2
    exact Classical.choice (ih ⟨y.1, hySpec.1⟩ hySpec.2)
  exact ⟨assembleTextbookLocalSolution
    (hR := hR) (step := step) (children := children) t.2⟩



/-! ## Assembly of the global class function -/

/-- A chosen local solution at each point of `A`.  The existence source is
`nonempty_textbookLocalSolution`, proved above by the textbook local-graph
induction.  This is an ambient Lean choice of witnesses, not an assertion of
an object-theoretic choice function. -/
noncomputable def chosenTextbookLocalSolutionOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : {z : ZFSet.{u} // z ∈ A}) :
    TextbookLocalSolution A R hR.2.2 step x.1 :=
  Classical.choice (nonempty_textbookLocalSolution hR step x.1 x.2)

/-- The global class function assembled on page 108: for `x ∈ A`, set
`F(x) = f_x(x)`.  It is totalized by `∅` away from `A`, where its value has
no mathematical role. -/
noncomputable def textbookGlobalRecursionFromLocalGraphs
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hx : x ∈ A then
    (chosenTextbookLocalSolutionOn hR step ⟨x, hx⟩).value x
  else
    ∅

@[simp]
theorem textbookGlobalRecursionFromLocalGraphs_eq_on
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A) :
    textbookGlobalRecursionFromLocalGraphs hR step x =
      (chosenTextbookLocalSolutionOn hR step ⟨x, hx⟩).value x := by
  simp [textbookGlobalRecursionFromLocalGraphs, hx]

@[simp]
theorem textbookGlobalRecursionFromLocalGraphs_eq_empty_of_not_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∉ A) :
    textbookGlobalRecursionFromLocalGraphs hR step x = ∅ := by
  simp [textbookGlobalRecursionFromLocalGraphs, hx]

/-- The assembled global function agrees on all of `d_x` with any local
solution at `x`.  At `t ∈ d_x`, the definition of the global function uses
the selected local solution `f_t`; textbook property (3) compares `f_t` and
the given `f_x` at the point `t ∈ d_x ∩ d_t`. -/
theorem textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A)
    (fx : TextbookLocalSolution A R hR.2.2 step x)
    {t : ZFSet.{u}}
    (ht : t ∈ localRecursionDomain A R hR.2.2 x) :
    textbookGlobalRecursionFromLocalGraphs hR step t = fx.value t := by
  have htA : t ∈ A := localRecursionDomain_subset hR.2.2 hx ht
  rw [textbookGlobalRecursionFromLocalGraphs_eq_on hR step htA]
  let ft := chosenTextbookLocalSolutionOn hR step ⟨t, htA⟩
  have hagree := textbookLocalSolutions_agreeOn_intersection
    hR hx htA fx ft t
      (ZFSet.mem_inter.mpr
        ⟨ht, mem_localRecursionDomain_iff.mpr (Or.inl rfl)⟩)
  exact hagree.symm



/-- In particular, the global and local functions have equal actual graphs
on the immediate predecessor set of `x`. -/
theorem textbookGlobalRecursionFromLocalGraphs_predecessorGraph_eq_local
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {x : ZFSet.{u}} (hx : x ∈ A)
    (fx : TextbookLocalSolution A R hR.2.2 step x) :
    predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x)
        (textbookGlobalRecursionFromLocalGraphs hR step) =
      predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x) fx.value := by
  apply predecessorRestrictionGraph_congr
  intro t ht
  have htx := (displayedPredecessors_spec hR.2.2 hx t).mp ht |>.2
  have htDomain := localRecursionDomain_predecessorClosed
    hR.1 hR.2.2 hx
      (mem_localRecursionDomain_iff.mpr (Or.inl rfl)) htx
  exact textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
    hR step hx fx htDomain

/-! ## Existence and uniqueness of the global recursive function -/

/-- The global recursion equation, stated independently of any particular
construction.  This is definitionally the same mathematical condition as
the one used by the existing class-recursion module: the second argument of
`step` is the actual Kuratowski graph on the displayed full predecessor set. -/
def SatisfiesTextbookGlobalRecursion
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (F : ZFSet.{u} → ZFSet.{u}) : Prop :=
  ∀ x, x ∈ A →
    F x = step x (predecessorRestrictionGraph
      (displayedPredecessors A R hsetLike x) F)

/-- The function assembled solely from the local graphs satisfies the global
recursion equation. -/
theorem textbookGlobalRecursionFromLocalGraphs_satisfies
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) :
    SatisfiesTextbookGlobalRecursion A R hR.2.2 step
      (textbookGlobalRecursionFromLocalGraphs hR step) := by
  intro x hx
  let fx := chosenTextbookLocalSolutionOn hR step ⟨x, hx⟩
  have hxDomain : x ∈ localRecursionDomain A R hR.2.2 x :=
    mem_localRecursionDomain_iff.mpr (Or.inl rfl)
  calc
    textbookGlobalRecursionFromLocalGraphs hR step x = fx.value x :=
      textbookGlobalRecursionFromLocalGraphs_eq_local_on_domain
        hR step hx fx hxDomain
    _ = step x (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x) fx.value) :=
      fx.satisfies x hxDomain
    _ = step x (predecessorRestrictionGraph
        (displayedPredecessors A R hR.2.2 x)
        (textbookGlobalRecursionFromLocalGraphs hR step)) := by
      apply congrArg (step x)
      exact (textbookGlobalRecursionFromLocalGraphs_predecessorGraph_eq_local
        hR step hx fx).symm





end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookLocalRecursion


/- Source module: Solutions.Work_CUGCH_TextbookLocalRecursionBridge -/
section GCHSource_Work_CUGCH_TextbookLocalRecursionBridge
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Bridge from the textbook local-graph proof to the class-recursion interface

`TextbookLocalRecursion` avoids importing the earlier fixpoint implementation,
so it states the recursion equation under a separate name.  This file proves
that the two predicates are definitionally the same and re-exports the
existence-and-uniqueness theorem through the established class-recursion
interface.  The existence proof below is the page-108 local-graph construction;
it does not invoke the earlier fixpoint existence theorem.
-/

section

open Set

universe u

namespace Constructible

noncomputable section

/-- The local-graph module and the class-recursion module state exactly the
same recursion equation. -/
theorem satisfiesTextbookGlobalRecursion_iff_classRecursion
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u})
    (F : ZFSet.{u} -> ZFSet.{u}) :
    SatisfiesTextbookGlobalRecursion A R hsetLike step F <->
      SatisfiesTextbookClassRecursion A R hsetLike step F := by
  rfl

/-- The function assembled from the textbook local graphs satisfies the
established class-recursion predicate. -/
theorem textbookGlobalRecursionFromLocalGraphs_satisfies_classRecursion
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R)
    (step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}) :
    SatisfiesTextbookClassRecursion A R hR.2.2 step
      (textbookGlobalRecursionFromLocalGraphs hR step) :=
  (satisfiesTextbookGlobalRecursion_iff_classRecursion
    hR.2.2 step (textbookGlobalRecursionFromLocalGraphs hR step)).mp
      (textbookGlobalRecursionFromLocalGraphs_satisfies hR step)



end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookLocalRecursionBridge


