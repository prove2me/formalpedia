-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library23
-- name    : CH_ConstructibleGCH_Library23
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T08:26:07.979788+00:00
-- url     : https://prove2.me/theorems/fa4b0c48-6fe7-470b-8d71-c25887920f83
-- title:
--   Ranges, local E solutions and branch formulas
-- statement:
--   This library provides the internal range interfaces for represented functions, the formulas describing local E solutions, and the branch and domain descriptions needed to interpret those solutions in L.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalFunctionRangeInjection.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookLocalSolutionLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEFormulaLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEStepBranchesLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookLocalDomainLCarrier.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library22
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_InternalFunctionRangeInjection -/
section GCHSource_Work_CUGCH_InternalFunctionRangeInjection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Internal injections from function ranges

For a represented function graph whose displayed codomain is its actual
range, the canonical constructible well-order selects the least preimage of
each range element.  Replacement collects these selections into an actual
right-inverse graph in `L`, yielding an internal injection of the range into
the original domain.
-/

section

universe u

namespace Constructible

noncomputable section

namespace Model

open ContinuumFormula

local notation "LMem" => lCarrierMem

/-! ## Fibers and their canonical minima -/

/-- Layout `[graph,value,input]`: `graph(input) = value`. -/
def inverseFiberFormula : FOFormula 3 :=
  graphRelAt (0 : Fin 3) (2 : Fin 3) (1 : Fin 3)

@[simp]
theorem satisfies_inverseFiberFormula
    (graph value input : LCarrier.{u}) :
    FOFormula.Satisfies LMem inverseFiberFormula
        ![graph, value, input] <->
      GraphRel graph input value := by
  exact satisfies_graphRelAt
    (0 : Fin 3) (2 : Fin 3) (1 : Fin 3)
    ![graph, value, input]

/-- The actual constructible fiber of `value`, bounded by `domain`. -/
def inverseFiberLCarrier
    (graph domain value : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    inverseFiberFormula ![graph, value] domain)

@[simp]
theorem mem_inverseFiberLCarrier_iff
    (graph domain value input : LCarrier.{u}) :
    input.1 ∈ (inverseFiberLCarrier graph domain value).1 <->
      input.1 ∈ domain.1 /\ GraphRel graph input value := by
  rw [inverseFiberLCarrier]
  rw [Classical.choose_spec (exists_separationLCarrier
    inverseFiberFormula ![graph, value] domain) input]
  have hassign : snoc ![graph, value] input =
      ![graph, value, input] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign, satisfies_inverseFiberFormula]

/-- Layout `[graph,domain,order,value,input]`: `input` is the least member of
the inverse fiber of `value`. -/
def inverseMinimumFormula : FOFormula 5 :=
  .conj (.mem (4 : Fin 5) (1 : Fin 5))
    (.conj
      (graphRelAt (0 : Fin 5) (4 : Fin 5) (3 : Fin 5))
      (.all
        (FOFormula.imp
          (.conj
            (.mem (Fin.last 5) (1 : Fin 5).castSucc)
            (graphRelAt
              (0 : Fin 5).castSucc (Fin.last 5)
              (3 : Fin 5).castSucc))
          (.neg
            (graphRelAt
              (2 : Fin 5).castSucc (Fin.last 5)
              (4 : Fin 5).castSucc)))))

@[simp]
theorem satisfies_inverseMinimumFormula
    (graph domain order value input : LCarrier.{u}) :
    FOFormula.Satisfies LMem inverseMinimumFormula
        ![graph, domain, order, value, input] <->
      input.1 ∈ domain.1 /\
        GraphRel graph input value /\
          forall other : LCarrier.{u}, other.1 ∈ domain.1 ->
            GraphRel graph other value ->
              Not (GraphRel order other input) := by
  simp only [inverseMinimumFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphRelAt, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hinput, hvalue, hminimum⟩
    exact ⟨hinput, hvalue,
      fun other hother hotherValue =>
        hminimum other ⟨hother, hotherValue⟩⟩
  · rintro ⟨hinput, hvalue, hminimum⟩
    exact ⟨hinput, hvalue,
      fun other hother => hminimum other hother.1 hother.2⟩



/-! ## The represented inverse injection -/





end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_InternalFunctionRangeInjection


/- Source module: Solutions.Work_CUGCH_TextbookLocalSolutionLCarrier -/
section GCHSource_Work_CUGCH_TextbookLocalSolutionLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Textbook local-solution formulas over L

This file unfolds the local-solution and recursion-value formulas directly
over `LCarrier`.  These are semantic equivalences only: they do not assume
or manufacture an internal local solution graph.
-/

section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Formula insertion -/

@[simp]
theorem satisfies_localDomainFormulaAt_lCarrier_generic
    {n m : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (x domain : Fin m)
    (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (localDomainFormulaAt classFormula relationFormula
          params x domain) s <->
      FOFormula.Satisfies LMem
        (localDomainFormula classFormula relationFormula)
        (snoc (snoc (fun i => s (params i)) (s x)) (s domain)) := by
  rw [localDomainFormulaAt, FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s
        (Fin.lastCases domain (fun j => Fin.lastCases x params j) i)) =
        snoc (snoc (fun i => s (params i)) (s x)) (s domain) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment]

@[simp]
theorem satisfies_stepFormulaAt_lCarrier_generic
    {n m : Nat} (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph value : Fin m)
    (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (stepFormulaAt stepFormula params x graph value) s <->
      FOFormula.Satisfies LMem stepFormula
        (snoc (snoc (snoc (fun i => s (params i)) (s x))
          (s graph)) (s value)) := by
  rw [stepFormulaAt, FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s (Fin.lastCases value (fun k =>
        Fin.lastCases graph (fun j => Fin.lastCases x params j) k) i)) =
        snoc (snoc (snoc (fun i => s (params i)) (s x))
          (s graph)) (s value) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · simp
        · simp
  rw [hassignment]

/-! ## Exact local-solution semantics -/

@[simp]
theorem satisfies_localSolutionFormula_lCarrier_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple LCarrier.{u} n) (x graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) graph) <->
      exists domain : LCarrier.{u},
        FOFormula.Satisfies LMem
          (localDomainFormula classFormula relationFormula)
          (snoc (snoc params x) domain) /\
        (((forall input : LCarrier.{u}, input.1 ∈ domain.1 ->
              exists value : LCarrier.{u},
                ZFSet.pair input.1 value.1 ∈ graph.1 /\
                forall other : LCarrier.{u},
                  ZFSet.pair input.1 other.1 ∈ graph.1 ->
                    other = value) /\
            forall pair : LCarrier.{u}, pair.1 ∈ graph.1 ->
              exists input : LCarrier.{u}, input.1 ∈ domain.1 /\
                exists value : LCarrier.{u},
                  pair.1 = ZFSet.pair input.1 value.1) /\
          forall top : LCarrier.{u}, top.1 ∈ domain.1 ->
            exists restriction value : LCarrier.{u},
              (forall pair : LCarrier.{u},
                pair.1 ∈ restriction.1 <->
                  pair.1 ∈ graph.1 /\
                    exists input output : LCarrier.{u},
                      pair.1 = ZFSet.pair input.1 output.1 /\
                      FOFormula.Satisfies LMem classFormula
                        (snoc params input) /\
                      FOFormula.Satisfies LMem relationFormula
                        (snoc (snoc params input) top)) /\
              ZFSet.pair top.1 value.1 ∈ graph.1 /\
              FOFormula.Satisfies LMem stepFormula
                (snoc (snoc (snoc params top) restriction) value)) := by
  simp only [localSolutionFormula, FOFormula.Satisfies,
    FOFormula.satisfies_boundedAll,
    satisfies_localDomainFormulaAt_lCarrier_generic,
    satisfies_functionGraphOnFormulaAt_lCarrier_iff,
    satisfies_restrictionGraphFormulaAt_lCarrier_iff,
    satisfies_graphValueFormulaAt_lCarrier_iff,
    satisfies_stepFormulaAt_lCarrier_generic,
    snoc_last, snoc_castSucc]

/-! ## Exact recursion-value semantics -/

@[simp]
theorem satisfies_localSolutionFormulaAt_lCarrier_generic
    {n m : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph : Fin m)
    (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (localSolutionFormulaAt classFormula relationFormula stepFormula
          params x graph) s <->
      FOFormula.Satisfies LMem
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc (fun i => s (params i)) (s x)) (s graph)) := by
  rw [localSolutionFormulaAt, FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s
        (Fin.lastCases graph (fun j => Fin.lastCases x params j) i)) =
        snoc (snoc (fun i => s (params i)) (s x)) (s graph) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment]

@[simp]
theorem satisfies_recursionValueFormula_lCarrier_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple LCarrier.{u} n) (x value : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (recursionValueFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) value) <->
      FOFormula.Satisfies LMem classFormula (snoc params x) /\
        exists graph : LCarrier.{u},
          FOFormula.Satisfies LMem
            (localSolutionFormula classFormula relationFormula stepFormula)
            (snoc (snoc params x) graph) /\
          ZFSet.pair x.1 value.1 ∈ graph.1 := by
  simp only [recursionValueFormula, FOFormula.Satisfies,
    satisfies_classFormulaAt_generic,
    satisfies_localSolutionFormulaAt_lCarrier_generic,
    satisfies_graphValueFormulaAt_lCarrier_iff,
    snoc_last, snoc_castSucc]

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookLocalSolutionLCarrier


/- Source module: Solutions.Work_CUGCH_TextbookEFormulaLCarrier -/
section GCHSource_Work_CUGCH_TextbookEFormulaLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# The public textbook E formula over L

This file unfolds the public formula for `E` over `LCarrier`.  It separates
the purely syntactic work from the later existence and uniqueness proof for
the internal local solution graph.
-/

section

universe u

namespace Constructible

noncomputable section

namespace Model

local notation "LMem" => lCarrierMem

@[simp]
theorem satisfies_textbookERecursionValueFormula_rename_lCarrier
    (s : Tuple LCarrier.{u} 5) :
    FOFormula.Satisfies LMem
        (FOFormula.rename
          TextbookEFormula.textbookERecursionValueParameters
          TextbookEFormula.textbookERecursionValueFormula) s <->
      FOFormula.Satisfies LMem
        TextbookEFormula.textbookERecursionValueFormula
        ![s 0, s 4, s 3] := by
  rw [FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s
        (TextbookEFormula.textbookERecursionValueParameters i)) =
        ![s 0, s 4, s 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]

/-- The quantified key in the public formula is exactly the internal
Kuratowski pair `<m,n>`. -/
@[simp]
theorem satisfies_textbookEZFFormula_lCarrier_iff_recursionValue
    (a n m output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
        ![a, n, m, output] <->
      FOFormula.Satisfies LMem
        TextbookEFormula.textbookERecursionValueFormula
        ![a, orderedPairLCarrier m n, output] := by
  rw [TextbookEFormula.textbookEZFFormula]
  simp only [FOFormula.Satisfies]
  constructor
  · rintro ⟨key, hpairFormula, hrecursionFormula⟩
    have hpair :=
      (satisfies_kuratowskiPairEqAt_lCarrier_generic
        (Fin.last 4) (2 : Fin 5) (1 : Fin 5)
        (snoc ![a, n, m, output] key)).mp hpairFormula
    change key.1 = ZFSet.pair m.1 n.1 at hpair
    have hkey : key = orderedPairLCarrier m n := by
      apply Subtype.ext
      simpa only [orderedPairLCarrier_val] using hpair
    subst key
    have hrenamed :=
      (satisfies_textbookERecursionValueFormula_rename_lCarrier
        (snoc ![a, n, m, output] (orderedPairLCarrier m n))).mp
        hrecursionFormula
    have hassignment :
        ![(snoc ![a, n, m, output] (orderedPairLCarrier m n)) 0,
          (snoc ![a, n, m, output] (orderedPairLCarrier m n)) 4,
          (snoc ![a, n, m, output] (orderedPairLCarrier m n)) 3] =
          ![a, orderedPairLCarrier m n, output] := by
      funext i
      fin_cases i <;> rfl
    rw [hassignment] at hrenamed
    exact hrenamed
  · intro hrecursion
    let key : LCarrier.{u} := orderedPairLCarrier m n
    refine ⟨key, ?_, ?_⟩
    · apply (satisfies_kuratowskiPairEqAt_lCarrier_generic
        (Fin.last 4) (2 : Fin 5) (1 : Fin 5)
        (snoc ![a, n, m, output] key)).mpr
      change key.1 = ZFSet.pair m.1 n.1
      rfl
    · apply
        (satisfies_textbookERecursionValueFormula_rename_lCarrier
          (snoc ![a, n, m, output] key)).mpr
      have hassignment :
          ![(snoc ![a, n, m, output] key) 0,
            (snoc ![a, n, m, output] key) 4,
            (snoc ![a, n, m, output] key) 3] =
            ![a, key, output] := by
        funext i
        fin_cases i <;> rfl
      rw [hassignment]
      simpa only [key] using hrecursion

/-- The recursion-value subformula says precisely that the key is in the
textbook domain and that an internal local solution graph has the displayed
value.  Existence of that graph is not asserted here. -/
@[simp]
theorem satisfies_textbookERecursionValueFormula_lCarrier_iff
    (a key output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        TextbookEFormula.textbookERecursionValueFormula
        ![a, key, output] <->
      key.1 ∈ TextbookEDomain /\
        exists graph : LCarrier.{u},
          FOFormula.Satisfies LMem
            (localSolutionFormula
              TextbookEFormula.textbookEDomainWithParamFormula
              TextbookEFormula.textbookERelationWithParamFormula
              TextbookEFormula.textbookEStepFormula)
            ![a, key, graph] /\
          ZFSet.pair key.1 output.1 ∈ graph.1 := by
  have hclassAssignment : snoc ![a] key = ![a, key] := by
    funext i
    fin_cases i <;> rfl
  have hfullAssignment (z : LCarrier.{u}) :
      snoc ![a, key] z = ![a, key, z] := by
    funext i
    fin_cases i <;> rfl
  rw [TextbookEFormula.textbookERecursionValueFormula]
  simpa only [hclassAssignment, hfullAssignment,
    satisfies_textbookEDomainWithParamFormula_lCarrier] using
    (satisfies_recursionValueFormula_lCarrier_iff
      TextbookEFormula.textbookEDomainWithParamFormula
      TextbookEFormula.textbookERelationWithParamFormula
      TextbookEFormula.textbookEStepFormula ![a] key output)

/-- Exact syntactic reduction of the public formula to an internal local
solution at the key `<m,n>`. -/
@[simp]
theorem satisfies_textbookEZFFormula_lCarrier_iff_localSolution
    (a n m output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
        ![a, n, m, output] <->
      (n.1 ∈ textbookEOmegaZF /\ m.1 ∈ textbookEOmegaZF) /\
        exists graph : LCarrier.{u},
          FOFormula.Satisfies LMem
            (localSolutionFormula
              TextbookEFormula.textbookEDomainWithParamFormula
              TextbookEFormula.textbookERelationWithParamFormula
              TextbookEFormula.textbookEStepFormula)
            ![a, orderedPairLCarrier m n, graph] /\
          ZFSet.pair (ZFSet.pair m.1 n.1) output.1 ∈ graph.1 := by
  rw [satisfies_textbookEZFFormula_lCarrier_iff_recursionValue,
    satisfies_textbookERecursionValueFormula_lCarrier_iff]
  simp only [orderedPairLCarrier_val]
  rw [pair_mem_textbookEDomain_iff]
  constructor
  · rintro ⟨⟨hmOmega, hnOmega⟩, hgraph⟩
    exact ⟨⟨hnOmega, hmOmega⟩, hgraph⟩
  · rintro ⟨⟨hnOmega, hmOmega⟩, hgraph⟩
    exact ⟨⟨hmOmega, hnOmega⟩, hgraph⟩

end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEFormulaLCarrier


/- Source module: Solutions.Work_CUGCH_TextbookEStepBranchesLCarrier -/
section GCHSource_Work_CUGCH_TextbookEStepBranchesLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The five textbook E branches over L

This file assembles the exact `LCarrier` operation semantics into the five
constructor clauses of the textbook recursion for `E`, followed by its exact
fallback clause.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Atomic branches -/

@[simp]
theorem satisfies_stepBranchZero_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepBranchZero
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j 0 ∧ i < n ∧ j < n ∧
        output.1 = textbookDInCodeZF a.1
          (natCode n) (natCode i) (natCode j) := by
  rw [TextbookEFormula.stepBranchZero]
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
  · rintro ⟨iSet, jSet, tagSet, hguard, houtput⟩
    rw [hassign] at hguard houtput
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hguard.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hguard.2.1 with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode 0 : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        0 (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, tagSet]).mp
        hguard.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier 0 :=
      Subtype.ext htagVal
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_lCarrier_natCode
        0 true a key history output m n i j).mp hguard
    have hvalue : output.1 = textbookDInCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      rw [satisfies_formula5At_lCarrier] at houtput
      simpa only [textbookDInCodeZF_natCode] using
        (satisfies_dInOutputFormula_lCarrier_natCode_iff
          n i j a output).mp houtput
    exact ⟨i, j, hrecognized.1,
      hrecognized.2.1, hrecognized.2.2, hvalue⟩
  · rintro ⟨i, j, hcode, hi, hj, houtput⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier 0, ?_, ?_⟩
    · rw [hassign]
      exact (satisfies_codeGuardBody_lCarrier_natCode
        0 true a key history output m n i j).mpr
          ⟨hcode, hi, hj⟩
    · rw [hassign, satisfies_formula5At_lCarrier]
      apply (satisfies_dInOutputFormula_lCarrier_natCode_iff
        n i j a output).mpr
      simpa only [textbookDInCodeZF_natCode] using houtput

@[simp]
theorem satisfies_stepBranchOne_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepBranchOne
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j 1 ∧ i < n ∧ j < n ∧
        output.1 = textbookDEqCodeZF a.1
          (natCode n) (natCode i) (natCode j) := by
  rw [TextbookEFormula.stepBranchOne]
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
  · rintro ⟨iSet, jSet, tagSet, hguard, houtput⟩
    rw [hassign] at hguard houtput
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hguard.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hguard.2.1 with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode 1 : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        1 (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, tagSet]).mp
        hguard.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier 1 :=
      Subtype.ext htagVal
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_lCarrier_natCode
        1 true a key history output m n i j).mp hguard
    have hvalue : output.1 = textbookDEqCodeZF a.1
        (natCode n) (natCode i) (natCode j) := by
      rw [satisfies_formula5At_lCarrier] at houtput
      simpa only [textbookDEqCodeZF_natCode] using
        (satisfies_dEqOutputFormula_lCarrier_natCode_iff
          n i j a output).mp houtput
    exact ⟨i, j, hrecognized.1,
      hrecognized.2.1, hrecognized.2.2, hvalue⟩
  · rintro ⟨i, j, hcode, hi, hj, houtput⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier 1, ?_, ?_⟩
    · rw [hassign]
      exact (satisfies_codeGuardBody_lCarrier_natCode
        1 true a key history output m n i j).mpr
          ⟨hcode, hi, hj⟩
    · rw [hassign, satisfies_formula5At_lCarrier]
      apply (satisfies_dEqOutputFormula_lCarrier_natCode_iff
        n i j a output).mpr
      simpa only [textbookDEqCodeZF_natCode] using houtput

/-! ## Relative-complement branch -/

@[simp]
theorem satisfies_stepBranchTwo_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepBranchTwo
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j 2 ∧
        output.1 = relativeDifferenceZF
          (ZFSet.funs (natCode n) a.1)
          (uniqueGraphLookupZF history.1
            (ZFSet.pair (natCode i) (natCode n))) := by
  rw [TextbookEFormula.stepBranchTwo]
  simp only [FOFormula.Satisfies]
  let base : Tuple LCarrier.{u} 7 :=
    ![a, key, history, output, omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n]
  have hfields (iSet jSet tagSet : LCarrier.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hkeyAssignment
      (iSet jSet tagSet lookupKey : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] lookupKey =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, lookupKey] := by
    funext k
    fin_cases k <;> rfl
  have hremovedAssignment
      (iSet jSet tagSet lookupKey removed : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, lookupKey] removed =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, lookupKey, removed] := by
    funext k
    fin_cases k <;> rfl
  have hspaceAssignment
      (iSet jSet tagSet lookupKey removed space : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, lookupKey, removed] space =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, lookupKey, removed, space] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, lookupKey, hpair,
      removed, hlookup, space, hspace, hdifference⟩
    rw [hfields] at hguard hpair hlookup hspace hdifference
    rw [hkeyAssignment] at hpair hlookup hspace hdifference
    rw [hremovedAssignment] at hlookup hspace hdifference
    rw [hspaceAssignment] at hspace hdifference
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hguard.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hguard.2.1 with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode 2 : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        2 (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, tagSet]).mp
        hguard.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier 2 :=
      Subtype.ext htagVal
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_lCarrier_natCode
        2 false a key history output m n i j).mp hguard
    have hlookupKey : lookupKey.1 =
        ZFSet.pair (natCode i) (natCode n) := by
      rw [satisfies_kuratowskiPairEqAt_lCarrier] at hpair
      simpa using hpair
    have hremoved : removed.1 =
        uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode i) (natCode n)) := by
      rw [satisfies_formula3At_lCarrier] at hlookup
      have hvalue :=
        (satisfies_uniqueGraphLookupFormula_lCarrier_iff
          history lookupKey removed).mp hlookup
      simpa only [hlookupKey] using hvalue
    have hspaceValue : space.1 = ZFSet.funs (natCode n) a.1 := by
      rw [satisfies_formula3At_lCarrier] at hspace
      exact (satisfies_finiteFunctionSpaceGraph_lCarrier_natCode_iff
        n a space).mp hspace
    have hvalue : output.1 =
        relativeDifferenceZF (ZFSet.funs (natCode n) a.1)
          (uniqueGraphLookupZF history.1
            (ZFSet.pair (natCode i) (natCode n))) := by
      rw [satisfies_formula3At_lCarrier] at hdifference
      have hraw :=
        (satisfies_relativeDifferenceOutputFormula_lCarrier
          space removed output).mp hdifference
      simpa only [hspaceValue, hremoved] using hraw
    exact ⟨i, j, hrecognized.1, hvalue⟩
  · rintro ⟨i, j, hcode, houtput⟩
    let lookupKey : LCarrier.{u} :=
      ⟨ZFSet.pair (natCode i) (natCode n),
        orderedPair_mem_L (natCode_mem_L i) (natCode_mem_L n)⟩
    let removed : LCarrier.{u} :=
      ⟨uniqueGraphLookupZF history.1 lookupKey.1,
        uniqueGraphLookupZF_mem_L history.2 lookupKey.2⟩
    let space : LCarrier.{u} :=
      ⟨ZFSet.funs (natCode n) a.1, by
        change textbookTupleSpace a.1 n ∈ L
        exact textbookTupleSpace_mem_L a.2 n⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier 2,
      ?_, lookupKey, ?_, removed, ?_, space, ?_, ?_⟩
    · rw [hfields]
      exact (satisfies_codeGuardBody_lCarrier_natCode
        2 false a key history output m n i j).mpr ⟨hcode, trivial⟩
    · rw [hfields, hkeyAssignment,
        satisfies_kuratowskiPairEqAt_lCarrier]
      change lookupKey.1 = ZFSet.pair (natCode i) (natCode n)
      rfl
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        satisfies_formula3At_lCarrier]
      exact (satisfies_uniqueGraphLookupFormula_lCarrier_iff
        history lookupKey removed).mpr rfl
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        hspaceAssignment, satisfies_formula3At_lCarrier]
      exact (satisfies_finiteFunctionSpaceGraph_lCarrier_natCode_iff
        n a space).mpr rfl
    · rw [hfields, hkeyAssignment, hremovedAssignment,
        hspaceAssignment, satisfies_formula3At_lCarrier]
      apply (satisfies_relativeDifferenceOutputFormula_lCarrier
        space removed output).mpr
      simpa only [space, removed, lookupKey] using houtput

/-! ## Intersection branch -/

@[simp]
theorem satisfies_stepBranchThree_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepBranchThree
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j 3 ∧
        output.1 = intersectionZF
          (uniqueGraphLookupZF history.1
            (ZFSet.pair (natCode i) (natCode n)))
          (uniqueGraphLookupZF history.1
            (ZFSet.pair (natCode j) (natCode n))) := by
  rw [TextbookEFormula.stepBranchThree]
  simp only [FOFormula.Satisfies]
  let base : Tuple LCarrier.{u} 7 :=
    ![a, key, history, output, omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n]
  have hfields (iSet jSet tagSet : LCarrier.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hleftKeyAssignment
      (iSet jSet tagSet leftKey : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] leftKey =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey] := by
    funext k
    fin_cases k <;> rfl
  have hleftValueAssignment
      (iSet jSet tagSet leftKey leftValue : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey] leftValue =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey, leftValue] := by
    funext k
    fin_cases k <;> rfl
  have hrightKeyAssignment
      (iSet jSet tagSet leftKey leftValue rightKey : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey, leftValue] rightKey =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey] := by
    funext k
    fin_cases k <;> rfl
  have hrightValueAssignment
      (iSet jSet tagSet leftKey leftValue rightKey rightValue :
        LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey] rightValue =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, leftKey, leftValue, rightKey, rightValue] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, leftKey, hleftPair,
      leftValue, hleftLookup, rightKey, hrightPair,
      rightValue, hrightLookup, hintersection⟩
    rw [hfields] at hguard hleftPair hleftLookup hrightPair hrightLookup
    rw [hfields] at hintersection
    rw [hleftKeyAssignment] at hleftPair hleftLookup hrightPair hrightLookup
    rw [hleftKeyAssignment] at hintersection
    rw [hleftValueAssignment] at hleftLookup hrightPair hrightLookup
    rw [hleftValueAssignment] at hintersection
    rw [hrightKeyAssignment] at hrightPair hrightLookup hintersection
    rw [hrightValueAssignment] at hrightLookup hintersection
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hguard.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hguard.2.1 with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode 3 : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        3 (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, tagSet]).mp
        hguard.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier 3 :=
      Subtype.ext htagVal
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_lCarrier_natCode
        3 false a key history output m n i j).mp hguard
    have hleftKey : leftKey.1 =
        ZFSet.pair (natCode i) (natCode n) := by
      rw [satisfies_kuratowskiPairEqAt_lCarrier] at hleftPair
      simpa using hleftPair
    have hleftValue : leftValue.1 =
        uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode i) (natCode n)) := by
      rw [satisfies_formula3At_lCarrier] at hleftLookup
      have hvalue :=
        (satisfies_uniqueGraphLookupFormula_lCarrier_iff
          history leftKey leftValue).mp hleftLookup
      simpa only [hleftKey] using hvalue
    have hrightKey : rightKey.1 =
        ZFSet.pair (natCode j) (natCode n) := by
      rw [satisfies_kuratowskiPairEqAt_lCarrier] at hrightPair
      simpa using hrightPair
    have hrightValue : rightValue.1 =
        uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode j) (natCode n)) := by
      rw [satisfies_formula3At_lCarrier] at hrightLookup
      have hvalue :=
        (satisfies_uniqueGraphLookupFormula_lCarrier_iff
          history rightKey rightValue).mp hrightLookup
      simpa only [hrightKey] using hvalue
    have hvalue : output.1 = intersectionZF
        (uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode i) (natCode n)))
        (uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode j) (natCode n))) := by
      rw [satisfies_formula3At_lCarrier] at hintersection
      have hraw :=
        (satisfies_intersectionOutputFormula_lCarrier
          leftValue rightValue output).mp hintersection
      simpa only [hleftValue, hrightValue] using hraw
    exact ⟨i, j, hrecognized.1, hvalue⟩
  · rintro ⟨i, j, hcode, houtput⟩
    let leftKey : LCarrier.{u} :=
      ⟨ZFSet.pair (natCode i) (natCode n),
        orderedPair_mem_L (natCode_mem_L i) (natCode_mem_L n)⟩
    let leftValue : LCarrier.{u} :=
      ⟨uniqueGraphLookupZF history.1 leftKey.1,
        uniqueGraphLookupZF_mem_L history.2 leftKey.2⟩
    let rightKey : LCarrier.{u} :=
      ⟨ZFSet.pair (natCode j) (natCode n),
        orderedPair_mem_L (natCode_mem_L j) (natCode_mem_L n)⟩
    let rightValue : LCarrier.{u} :=
      ⟨uniqueGraphLookupZF history.1 rightKey.1,
        uniqueGraphLookupZF_mem_L history.2 rightKey.2⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier 3,
      ?_, leftKey, ?_, leftValue, ?_, rightKey, ?_, rightValue, ?_, ?_⟩
    · rw [hfields]
      exact (satisfies_codeGuardBody_lCarrier_natCode
        3 false a key history output m n i j).mpr ⟨hcode, trivial⟩
    · rw [hfields, hleftKeyAssignment,
        satisfies_kuratowskiPairEqAt_lCarrier]
      change leftKey.1 = ZFSet.pair (natCode i) (natCode n)
      rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        satisfies_formula3At_lCarrier]
      exact (satisfies_uniqueGraphLookupFormula_lCarrier_iff
        history leftKey leftValue).mpr rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, satisfies_kuratowskiPairEqAt_lCarrier]
      change rightKey.1 = ZFSet.pair (natCode j) (natCode n)
      rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, hrightValueAssignment,
        satisfies_formula3At_lCarrier]
      exact (satisfies_uniqueGraphLookupFormula_lCarrier_iff
        history rightKey rightValue).mpr rfl
    · rw [hfields, hleftKeyAssignment, hleftValueAssignment,
        hrightKeyAssignment, hrightValueAssignment,
        satisfies_formula3At_lCarrier]
      apply (satisfies_intersectionOutputFormula_lCarrier
        leftValue rightValue output).mpr
      simpa only [leftValue, leftKey, rightValue, rightKey] using houtput

/-! ## Existential-projection branch -/

@[simp]
theorem satisfies_stepBranchFour_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepBranchFour
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ∃ i j : Nat, m = textbookECode i j 4 ∧
        output.1 = textbookExistsProjCodeZF a.1 (natCode n)
          (uniqueGraphLookupZF history.1
            (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
  rw [TextbookEFormula.stepBranchFour]
  simp only [FOFormula.Satisfies]
  let base : Tuple LCarrier.{u} 7 :=
    ![a, key, history, output, omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n]
  have hfields (iSet jSet tagSet : LCarrier.{u}) :
      snoc (snoc (snoc base iSet) jSet) tagSet =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] := by
    funext k
    fin_cases k <;> rfl
  have hsuccAssignment
      (iSet jSet tagSet succN : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet] succN =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, succN] := by
    funext k
    fin_cases k <;> rfl
  have hkeyAssignment
      (iSet jSet tagSet succN lookupKey : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, succN] lookupKey =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, succN, lookupKey] := by
    funext k
    fin_cases k <;> rfl
  have hrelationAssignment
      (iSet jSet tagSet succN lookupKey relation : LCarrier.{u}) :
      snoc
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, succN, lookupKey] relation =
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          iSet, jSet, tagSet, succN, lookupKey, relation] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨iSet, jSet, tagSet, hguard, succN, hsucc,
      lookupKey, hpair, relation, hlookup, hprojection⟩
    rw [hfields] at hguard hsucc hpair hlookup hprojection
    rw [hsuccAssignment] at hsucc hpair hlookup hprojection
    rw [hkeyAssignment] at hpair hlookup hprojection
    rw [hrelationAssignment] at hlookup hprojection
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode iSet.1).mp
      hguard.1 with ⟨i, hi⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode jSet.1).mp
      hguard.2.1 with ⟨j, hj⟩
    have hiSet : iSet =
        TextbookNatFormula.textbookNatCodeLCarrier i := Subtype.ext hi
    have hjSet : jSet =
        TextbookNatFormula.textbookNatCodeLCarrier j := Subtype.ext hj
    subst iSet
    subst jSet
    have htagVal : tagSet.1 = (natCode 4 : ZFSet.{u}) :=
      (TextbookNatFormula.satisfies_natLiteralDeltaAt_toFO_lCarrier
        4 (9 : Fin 10)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier i,
          TextbookNatFormula.textbookNatCodeLCarrier j, tagSet]).mp
        hguard.2.2.1
    have htag : tagSet =
        TextbookNatFormula.textbookNatCodeLCarrier 4 :=
      Subtype.ext htagVal
    subst tagSet
    have hrecognized :=
      (satisfies_codeGuardBody_lCarrier_natCode
        4 false a key history output m n i j).mp hguard
    have hsuccN : succN.1 = (natCode (n + 1) : ZFSet.{u}) := by
      rw [satisfies_successorAt_lCarrier] at hsucc
      change succN.1 = insert (natCode n) (natCode n) at hsucc
      exact hsucc.trans (natCode_succ_eq_insert n).symm
    have hlookupKey : lookupKey.1 =
        ZFSet.pair (natCode i) (natCode (n + 1)) := by
      rw [satisfies_kuratowskiPairEqAt_lCarrier] at hpair
      change lookupKey.1 = ZFSet.pair (natCode i) succN.1 at hpair
      simpa only [hsuccN] using hpair
    have hrelation : relation.1 = uniqueGraphLookupZF history.1
        (ZFSet.pair (natCode i) (natCode (n + 1))) := by
      rw [satisfies_formula3At_lCarrier] at hlookup
      have hvalue :=
        (satisfies_uniqueGraphLookupFormula_lCarrier_iff
          history lookupKey relation).mp hlookup
      simpa only [hlookupKey] using hvalue
    have hvalue : output.1 = textbookExistsProjCodeZF a.1 (natCode n)
        (uniqueGraphLookupZF history.1
          (ZFSet.pair (natCode i) (natCode (n + 1)))) := by
      rw [satisfies_formula4At_lCarrier] at hprojection
      have hraw :=
        (satisfies_existsProjOutputFormula_lCarrier_natCode_iff
          n a relation output).mp hprojection
      simpa only [hrelation] using hraw
    exact ⟨i, j, hrecognized.1, hvalue⟩
  · rintro ⟨i, j, hcode, houtput⟩
    let succN : LCarrier.{u} :=
      ⟨natCode (n + 1), natCode_mem_L (n + 1)⟩
    let lookupKey : LCarrier.{u} :=
      ⟨ZFSet.pair (natCode i) succN.1,
        orderedPair_mem_L (natCode_mem_L i) succN.2⟩
    let relation : LCarrier.{u} :=
      ⟨uniqueGraphLookupZF history.1 lookupKey.1,
        uniqueGraphLookupZF_mem_L history.2 lookupKey.2⟩
    refine ⟨TextbookNatFormula.textbookNatCodeLCarrier i,
      TextbookNatFormula.textbookNatCodeLCarrier j,
      TextbookNatFormula.textbookNatCodeLCarrier 4,
      ?_, succN, ?_, lookupKey, ?_, relation, ?_, ?_⟩
    · rw [hfields]
      exact (satisfies_codeGuardBody_lCarrier_natCode
        4 false a key history output m n i j).mpr ⟨hcode, trivial⟩
    · rw [hfields, hsuccAssignment, satisfies_successorAt_lCarrier]
      change (natCode (n + 1) : ZFSet.{u}) =
        insert (natCode n) (natCode n)
      exact natCode_succ_eq_insert n
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        satisfies_kuratowskiPairEqAt_lCarrier]
      change lookupKey.1 = ZFSet.pair (natCode i) succN.1
      rfl
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        hrelationAssignment, satisfies_formula3At_lCarrier]
      exact (satisfies_uniqueGraphLookupFormula_lCarrier_iff
        history lookupKey relation).mpr rfl
    · rw [hfields, hsuccAssignment, hkeyAssignment,
        hrelationAssignment, satisfies_formula4At_lCarrier]
      apply (satisfies_existsProjOutputFormula_lCarrier_natCode_iff
        n a relation output).mpr
      simpa only [relation, lookupKey, succN] using houtput

/-! ## Exact combination of the five clauses and fallback -/

@[simp]
theorem satisfies_anyCodeGuard_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.anyCodeGuard
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      TextbookEFormula.TextbookEGuard m n := by
  simp only [TextbookEFormula.anyCodeGuard, FOFormula.satisfies_disj,
    satisfies_codeGuard_lCarrier_standard]
  simp [TextbookEFormula.TextbookEGuard]

@[simp]
theorem satisfies_stepFallback_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.stepFallback
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      ¬ TextbookEFormula.TextbookEGuard m n ∧
        output.1 = (∅ : ZFSet.{u}) := by
  rw [TextbookEFormula.stepFallback]
  change
    (¬ FOFormula.Satisfies LMem TextbookEFormula.anyCodeGuard
          ![a, key, history, output, omegaLCarrier,
            TextbookNatFormula.textbookNatCodeLCarrier m,
            TextbookNatFormula.textbookNatCodeLCarrier n] ∧
      FOFormula.Satisfies LMem
          (Delta0Formula.emptyDeltaAt (3 : Fin 7)).toFO
          ![a, key, history, output, omegaLCarrier,
            TextbookNatFormula.textbookNatCodeLCarrier m,
            TextbookNatFormula.textbookNatCodeLCarrier n]) <-> _
  rw [satisfies_anyCodeGuard_lCarrier_standard,
    satisfies_emptyDeltaAt_lCarrier]
  change
    (¬ TextbookEFormula.TextbookEGuard m n ∧
      output.1 = (∅ : ZFSet.{u})) <-> _
  rfl

@[simp]
theorem satisfies_stepBranches_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem
        (.disj TextbookEFormula.stepBranchZero <|
          .disj TextbookEFormula.stepBranchOne <|
          .disj TextbookEFormula.stepBranchTwo <|
          .disj TextbookEFormula.stepBranchThree <|
          .disj TextbookEFormula.stepBranchFour
            TextbookEFormula.stepFallback)
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      TextbookEFormula.TextbookEBranchResult
        a.1 history.1 output.1 m n := by
  simp only [FOFormula.satisfies_disj,
    satisfies_stepBranchZero_lCarrier_standard,
    satisfies_stepBranchOne_lCarrier_standard,
    satisfies_stepBranchTwo_lCarrier_standard,
    satisfies_stepBranchThree_lCarrier_standard,
    satisfies_stepBranchFour_lCarrier_standard,
    satisfies_stepFallback_lCarrier_standard]
  rfl

/-! ## Exact one-step graph semantics -/

@[simp]
theorem satisfies_textbookEStepBody_lCarrier_standard
    (a key history output : LCarrier.{u}) (m n : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEStepBody
        ![a, key, history, output, omegaLCarrier,
          TextbookNatFormula.textbookNatCodeLCarrier m,
          TextbookNatFormula.textbookNatCodeLCarrier n] <->
      key.1 = ZFSet.pair (natCode m) (natCode n) ∧
        output.1 = textbookEStep a.1
          (ZFSet.pair (natCode m) (natCode n)) history.1 := by
  rw [TextbookEFormula.textbookEStepBody]
  change
    (FOFormula.Satisfies LMem
          (Model.standardOmegaAt (4 : Fin 7))
          ![a, key, history, output, omegaLCarrier,
            TextbookNatFormula.textbookNatCodeLCarrier m,
            TextbookNatFormula.textbookNatCodeLCarrier n] ∧
      LMem (TextbookNatFormula.textbookNatCodeLCarrier m) omegaLCarrier ∧
      LMem (TextbookNatFormula.textbookNatCodeLCarrier n) omegaLCarrier ∧
      FOFormula.Satisfies LMem
          (Delta0Formula.kuratowskiPairEqAt
            (1 : Fin 7) (5 : Fin 7) (6 : Fin 7)).toFO
          ![a, key, history, output, omegaLCarrier,
            TextbookNatFormula.textbookNatCodeLCarrier m,
            TextbookNatFormula.textbookNatCodeLCarrier n] ∧
      FOFormula.Satisfies LMem
          (.disj TextbookEFormula.stepBranchZero <|
            .disj TextbookEFormula.stepBranchOne <|
            .disj TextbookEFormula.stepBranchTwo <|
            .disj TextbookEFormula.stepBranchThree <|
            .disj TextbookEFormula.stepBranchFour
              TextbookEFormula.stepFallback)
          ![a, key, history, output, omegaLCarrier,
            TextbookNatFormula.textbookNatCodeLCarrier m,
            TextbookNatFormula.textbookNatCodeLCarrier n]) <-> _
  rw [satisfies_standardOmegaAt_lCarrier,
    satisfies_kuratowskiPairEqAt_lCarrier,
    satisfies_stepBranches_lCarrier_standard]
  change
    (omegaLCarrier = omegaLCarrier ∧
      LMem (TextbookNatFormula.textbookNatCodeLCarrier m) omegaLCarrier ∧
      LMem (TextbookNatFormula.textbookNatCodeLCarrier n) omegaLCarrier ∧
      key.1 = ZFSet.pair (natCode m) (natCode n) ∧
      TextbookEFormula.TextbookEBranchResult
        a.1 history.1 output.1 m n) <-> _
  rw [TextbookEFormula.textbookEBranchResult_iff_step]
  simp only [lmem_textbookNatCode_omegaLCarrier, true_and]

/-- Exact graph semantics of the textbook one-step operation over `L`.  The
domain conjunct is explicit, so the formula is false off `omega × omega`. -/
@[simp]
theorem satisfies_textbookEStepFormula_lCarrier_iff
    (a key history output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEStepFormula
        ![a, key, history, output] <->
      key.1 ∈ TextbookEDomain ∧
        output.1 = textbookEStep a.1 key.1 history.1 := by
  rw [TextbookEFormula.textbookEStepFormula]
  simp only [FOFormula.Satisfies]
  have hassign (omega mSet nSet : LCarrier.{u}) :
      snoc (snoc (snoc ![a, key, history, output] omega) mSet) nSet =
        ![a, key, history, output, omega, mSet, nSet] := by
    funext k
    fin_cases k <;> rfl
  constructor
  · rintro ⟨omega, mSet, nSet, hbody⟩
    rw [hassign] at hbody
    have homega : omega = omegaLCarrier := by
      have h :=
        (satisfies_standardOmegaAt_lCarrier (4 : Fin 7)
          ![a, key, history, output, omega, mSet, nSet]).mp hbody.1
      change omega = omegaLCarrier at h
      exact h
    subst omega
    have hmOmega : mSet.1 ∈
        (Ordinal.omega0.toZFSet : ZFSet.{u}) := hbody.2.1
    have hnOmega : nSet.1 ∈
        (Ordinal.omega0.toZFSet : ZFSet.{u}) := hbody.2.2.1
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode mSet.1).mp
      hmOmega with ⟨m, hm⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nSet.1).mp
      hnOmega with ⟨n, hn⟩
    have hmSet : mSet =
        TextbookNatFormula.textbookNatCodeLCarrier m := Subtype.ext hm
    have hnSet : nSet =
        TextbookNatFormula.textbookNatCodeLCarrier n := Subtype.ext hn
    subst mSet
    subst nSet
    have hstandard :=
      (satisfies_textbookEStepBody_lCarrier_standard
        a key history output m n).mp hbody
    constructor
    · apply mem_textbookEDomain_iff.mpr
      exact ⟨natCode m,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode m)).mpr ⟨m, rfl⟩,
        natCode n,
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode n)).mpr ⟨n, rfl⟩,
        hstandard.1⟩
    · simpa only [hstandard.1] using hstandard.2
  · rintro ⟨hkeyDomain, houtput⟩
    rcases exists_textbookEKeyDecode_of_mem_textbookEDomain hkeyDomain with
      ⟨m, n, _hdecode, hkey⟩
    refine ⟨omegaLCarrier,
      TextbookNatFormula.textbookNatCodeLCarrier m,
      TextbookNatFormula.textbookNatCodeLCarrier n, ?_⟩
    rw [hassign]
    apply (satisfies_textbookEStepBody_lCarrier_standard
      a key history output m n).mpr
    exact ⟨hkey, by simpa only [hkey] using houtput⟩

end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEStepBranchesLCarrier


/- Source module: Solutions.Work_CUGCH_TextbookLocalDomainLCarrier -/
section GCHSource_Work_CUGCH_TextbookLocalDomainLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Textbook local recursion domains over L

This is the proper-class `LCarrier` counterpart of
`satisfiesIn_localDomainFormula_iff_eq_localRecursionDomain`.  It retains the
same exact class semantics, relation semantics, relation-on-class,
set-likeness, predecessor closure, and represented-local-domain hypotheses.
The only change is that transitivity is supplied by the already proved
transitivity of `L` rather than by an ambient set `M : ZFSet`.
-/

section

open Set

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-- Over `LCarrier`, the least downward-closed-set formula denotes the
concrete textbook local recursion domain whenever that domain is represented
by an actual member of `L`. -/
theorem satisfies_localDomainFormula_lCarrier_iff_eq_localRecursionDomain
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hclass : ∀ z : LCarrier.{u},
      FOFormula.Satisfies LMem classFormula (snoc params z) ↔ z.1 ∈ A)
    (hrelationFormula : ∀ y z : LCarrier.{u},
      FOFormula.Satisfies LMem relationFormula
          (snoc (snoc params y) z) ↔ ClassRel R y.1 z.1)
    (hrelation : IsRelationOn A R)
    (hsetLike : HasSetPredecessorsOn A R)
    (hclosedIn : PredecessorsClosedIn (L : Set ZFSet.{u}) A R)
    {x domain : LCarrier.{u}} (hxA : x.1 ∈ A)
    (hlocalL : localRecursionDomain A R hsetLike x.1 ∈ L) :
    FOFormula.Satisfies LMem
        (localDomainFormula classFormula relationFormula)
        (snoc (snoc params x) domain) ↔
      domain.1 = localRecursionDomain A R hsetLike x.1 := by
  let paramsRaw : Tuple ZFSet.{u} n := fun i => (params i).1
  have hclassRaw (z : ZFSet.{u}) (hzL : z ∈ L) :
      SatisfiesIn (L : Set ZFSet.{u}) classFormula
          (snoc paramsRaw z) ↔ z ∈ A := by
    let zL : LCarrier.{u} := ⟨z, hzL⟩
    have hbridge := satisfies_lCarrier_iff_satisfiesIn_L
      classFormula (snoc params zL)
    have hassign :
        (fun i => (snoc params zL i).1) = snoc paramsRaw z := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [snoc_last, zL]
      · simp only [snoc_castSucc, paramsRaw]
    rw [hassign] at hbridge
    exact hbridge.symm.trans (hclass zL)
  have hrelationRaw (y : ZFSet.{u}) (hyL : y ∈ L)
      (z : ZFSet.{u}) (hzL : z ∈ L) :
      SatisfiesIn (L : Set ZFSet.{u}) relationFormula
          (snoc (snoc paramsRaw y) z) ↔ ClassRel R y z := by
    let yL : LCarrier.{u} := ⟨y, hyL⟩
    let zL : LCarrier.{u} := ⟨z, hzL⟩
    have hbridge := satisfies_lCarrier_iff_satisfiesIn_L
      relationFormula (snoc (snoc params yL) zL)
    have hassign :
        (fun i => (snoc (snoc params yL) zL i).1) =
          snoc (snoc paramsRaw y) z := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [snoc_last, zL]
      · refine Fin.lastCases ?_ (fun k => ?_) j
        · simp only [snoc_castSucc, snoc_last, yL]
        · simp only [snoc_castSucc, paramsRaw]
    rw [hassign] at hbridge
    exact hbridge.symm.trans (hrelationFormula yL zL)
  have hbridge := satisfies_lCarrier_iff_satisfiesIn_L
    (localDomainFormula classFormula relationFormula)
    (snoc (snoc params x) domain)
  have hassignment :
      (fun i => (snoc (snoc params x) domain i).1) =
        snoc (snoc paramsRaw x.1) domain.1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [snoc_last]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [snoc_castSucc, snoc_last]
      · simp only [snoc_castSucc, paramsRaw]
  rw [hassignment] at hbridge
  rw [hbridge]
  let dlocal := localRecursionDomain A R hsetLike x.1
  have hlocalSubsetA : (dlocal : Set ZFSet.{u}) ⊆ A :=
    localRecursionDomain_subset hsetLike hxA
  have hlocalClosed : ∀ t, t ∈ dlocal → ∀ y,
      y ∈ A → ClassRel R y t → y ∈ dlocal := by
    intro t ht y _hyA hyt
    exact localRecursionDomain_predecessorClosed
      hrelation hsetLike hxA ht hyt
  constructor
  · intro hformula
    rcases (satisfiesIn_localDomainFormula_iff
      (L : Set ZFSet.{u}) classFormula relationFormula
      paramsRaw x.1 domain.1).mp hformula with
      ⟨_hxFormula, hxDomain, hdomainSubset, hdomainClosed, hleast⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hzDomain
      have hzL : z ∈ L := mem_L_of_mem hzDomain domain.2
      exact hleast dlocal hlocalL
        (mem_localRecursionDomain_iff.mpr (Or.inl rfl))
        (by
          intro w hwL hwLocal
          exact (hclassRaw w hwL).mpr (hlocalSubsetA hwLocal))
        (by
          intro t htL htLocal y hyL hyFormula hyRelFormula
          have hyA : y ∈ A := (hclassRaw y hyL).mp hyFormula
          have hyt : ClassRel R y t :=
            (hrelationRaw y hyL t htL).mp hyRelFormula
          exact hlocalClosed t htLocal y hyA hyt)
        z hzL hzDomain
    · intro hzLocal
      have hdomainSubsetA : (domain.1 : Set ZFSet.{u}) ⊆ A := by
        intro w hwDomain
        have hwL : w ∈ L := mem_L_of_mem hwDomain domain.2
        exact (hclassRaw w hwL).mp
          (hdomainSubset w hwL hwDomain)
      have hdomainClosedAmbient : ∀ t, t ∈ domain.1 → ∀ y,
          y ∈ A → ClassRel R y t → y ∈ domain.1 := by
        intro t htDomain y hyA hyt
        have htL : t ∈ L := mem_L_of_mem htDomain domain.2
        have hyL : y ∈ L := hclosedIn t htL y hyA hyt
        exact hdomainClosed t htL htDomain y hyL
          ((hclassRaw y hyL).mpr hyA)
          ((hrelationRaw y hyL t htL).mpr hyt)
      exact localRecursionDomain_subset_of_closed hsetLike hxA hxDomain
        hdomainClosedAmbient hzLocal
  · intro hdomain
    apply (satisfiesIn_localDomainFormula_iff
      (L : Set ZFSet.{u}) classFormula relationFormula
      paramsRaw x.1 domain.1).mpr
    rw [hdomain]
    refine ⟨(hclassRaw x.1 x.2).mpr hxA,
      mem_localRecursionDomain_iff.mpr (Or.inl rfl), ?_, ?_, ?_⟩
    · intro z hzL hzLocal
      exact (hclassRaw z hzL).mpr (hlocalSubsetA hzLocal)
    · intro t htL htLocal y hyL hyFormula hyRelFormula
      have hyA : y ∈ A := (hclassRaw y hyL).mp hyFormula
      have hyt : ClassRel R y t :=
        (hrelationRaw y hyL t htL).mp hyRelFormula
      exact hlocalClosed t htLocal y hyA hyt
    · intro candidate hcandidateL hxCandidate hcandidateSubset
        hcandidateClosed z hzL hzLocal
      have hcandidateClosedAmbient : ∀ t, t ∈ candidate → ∀ y,
          y ∈ A → ClassRel R y t → y ∈ candidate := by
        intro t htCandidate y hyA hyt
        have htL : t ∈ L := mem_L_of_mem htCandidate hcandidateL
        have hyL : y ∈ L := hclosedIn t htL y hyA hyt
        exact hcandidateClosed t htL htCandidate y hyL
          ((hclassRaw y hyL).mpr hyA)
          ((hrelationRaw y hyL t htL).mpr hyt)
      exact localRecursionDomain_subset_of_closed hsetLike hxA hxCandidate
        hcandidateClosedAmbient hzLocal

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookLocalDomainLCarrier


