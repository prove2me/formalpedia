-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library10
-- name    : CH_ConstructibleGCH_Library10
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:33:17.160244+00:00
-- url     : https://prove2.me/theorems/f0c19e72-4377-40f3-b59f-a8f230b379ec
-- title:
--   Local recursion and textbook E domain codes
-- statement:
--   The textbook E construction enumerates elementary definability operations using coded requests. This library supplies the local-recursion formula, request domain and key-decoding interfaces needed to represent those operations internally.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookRecursionFormula.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEDomain.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEKeyDecode.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library09
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookRecursionFormula -/
section GCHSource_Work_CUGCH_TextbookRecursionFormula
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# First-order formulas for textbook class recursion

This file begins the syntax layer needed to interpret the recursion theorem of
Section 6.1 of Wang Fangting, *Axiomatic Set Theory*, inside a transitive model.
The formulas are uniformly parameterized.  Their variable layouts are

* `classFormula(params, x)`,
* `relationFormula(params, y, x)`,
* `stepFormula(params, x, q, z)`, and
* the output formulas use `(params, x, output)`.

At this stage the file formalizes the assertion that the relation is set-like,
its displayed predecessor sets, and the canonical local domain

`d_x = {x} union cl(A,x,R)`.

The local domain is described syntactically as the least downward-closed set
containing `x`.  The final theorem proves that this description is exactly the
previously constructed `localRecursionDomain` whenever that actual set and the
candidate interpretation belong to the transitive carrier.  Thus the formula
does not silently replace the textbook definition.

The final formulas describe a candidate local solution graph and its value at
one point.  They do not assert that such a graph belongs to a model; that
existence theorem is a separate mathematical obligation.  In particular,
the formulas below do not refer to a recursively defined function and contain
no syntactic self-reference.
-/

section

open Set

universe u

namespace Constructible.Model

noncomputable section

/-! ## Raw restricted-semantics helpers -/

 theorem satisfiesIn_all_iff_TextbookRecursionFormula_gch
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s <->
      forall x : ZFSet.{u}, x ∈ M ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

 theorem satisfiesIn_imp_iff_TextbookRecursionFormula_gch
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp left right) s <->
      (SatisfiesIn M left s -> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.imp, FOFormula.disj, SatisfiesIn]
  tauto

 theorem satisfiesIn_biimp_iff_TextbookRecursionFormula_gch
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s <->
      (SatisfiesIn M left s <-> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, SatisfiesIn,
    satisfiesIn_imp_iff_TextbookRecursionFormula_gch]
  tauto

 theorem satisfiesIn_boundedAll_iff_TextbookRecursionFormula_gch
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.boundedAll set formula) s <->
      forall x : ZFSet.{u}, x ∈ M -> x ∈ s set ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp only [FOFormula.boundedAll, FOFormula.boundedEx, SatisfiesIn]
  constructor
  · intro h x hxM hxSet
    by_contra hx
    exact h ⟨x, hxM, by simpa using hxSet, hx⟩
  · intro h hex
    rcases hex with ⟨x, hxM, hxSet, hx⟩
    exact hx (h x hxM (by simpa using hxSet))

 theorem satisfiesIn_rename_iff_TextbookRecursionFormula_gch
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.rename rename formula) s <->
      SatisfiesIn M formula (fun i => s (rename i)) := by
  induction formula generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg formula ih => exact not_congr (ih rename s)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft rename s) (ihRight rename s)
  | ex formula ih =>
      simp only [FOFormula.rename, SatisfiesIn, ih]
      constructor
      · rintro ⟨x, hxM, hformula⟩
        refine ⟨x, hxM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula
      · rintro ⟨x, hxM, hformula⟩
        refine ⟨x, hxM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula

/-! ## Formula insertion at named coordinates -/

/-- Insert `classFormula(params,x)` into a larger variable context. -/
def classFormulaAt {n m : Nat} (classFormula : FOFormula (n + 1))
    (params : Fin n -> Fin m) (x : Fin m) : FOFormula m :=
  FOFormula.rename (Fin.lastCases x params) classFormula

/-- Insert `relationFormula(params,y,x)` into a larger variable context. -/
def relationFormulaAt {n m : Nat}
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (y x : Fin m) : FOFormula m :=
  FOFormula.rename
    (Fin.lastCases x (fun j => Fin.lastCases y params j))
    relationFormula

/-- Insert `stepFormula(params,x,graph,value)` into a larger context. -/
def stepFormulaAt {n m : Nat} (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph value : Fin m) : FOFormula m :=
  FOFormula.rename
    (Fin.lastCases value (fun k =>
      Fin.lastCases graph (fun j => Fin.lastCases x params j) k))
    stepFormula

@[simp]
theorem satisfiesIn_classFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (params : Fin n -> Fin m) (x : Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (classFormulaAt classFormula params x) s <->
      SatisfiesIn M classFormula
        (snoc (fun i => s (params i)) (s x)) := by
  rw [classFormulaAt, satisfiesIn_rename_iff_TextbookRecursionFormula_gch]
  have hassignment :
      (fun i => s (Fin.lastCases x params i)) =
        snoc (fun i => s (params i)) (s x) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [hassignment]

@[simp]
theorem satisfiesIn_relationFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (y x : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (relationFormulaAt relationFormula params y x) s <->
      SatisfiesIn M relationFormula
        (snoc (snoc (fun i => s (params i)) (s y)) (s x)) := by
  rw [relationFormulaAt, satisfiesIn_rename_iff_TextbookRecursionFormula_gch]
  have hassignment :
      (fun i =>
        s (Fin.lastCases x (fun j => Fin.lastCases y params j) i)) =
        snoc (snoc (fun i => s (params i)) (s y)) (s x) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment]

@[simp]
theorem satisfiesIn_stepFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph value : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (stepFormulaAt stepFormula params x graph value) s <->
      SatisfiesIn M stepFormula
        (snoc (snoc (snoc (fun i => s (params i)) (s x))
          (s graph)) (s value)) := by
  rw [stepFormulaAt, satisfiesIn_rename_iff_TextbookRecursionFormula_gch]
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

/-! ## Kuratowski graph values -/

/-- In a context containing `graph`, `input`, and `value`, this formula says
that the Kuratowski pair `<input,value>` belongs to `graph`. -/
def graphValueFormulaAt {m : Nat}
    (graph input value : Fin m) : FOFormula m :=
  .ex (.conj
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last m) input.castSucc value.castSucc).toFO
    (.mem (Fin.last m) graph.castSucc))

 theorem satisfiesIn_kuratowskiPairEqAt_iff_TextbookRecursionFormula_gch
    {M : ZFSet.{u}} (hM : M.IsTransitive) {m : Nat}
    (pair input value : Fin m) (s : Tuple ZFSet.{u} m)
    (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt pair input value).toFO s <->
      s pair = ZFSet.pair (s input) (s value) := by
  let sM : Tuple (ZFCarrier M) m := fun i => ⟨s i, hs i⟩
  calc
    SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt pair input value).toFO s <->
        FOFormula.Satisfies (zfCarrierMem M)
          (Delta0Formula.kuratowskiPairEqAt pair input value).toFO sM :=
      (satisfies_subtype_iff_satisfiesIn
        (M : Set ZFSet.{u})
        (Delta0Formula.kuratowskiPairEqAt pair input value).toFO sM).symm
    _ <-> Delta0Formula.Satisfies (zfCarrierMem M)
          (Delta0Formula.kuratowskiPairEqAt pair input value) sM :=
      Delta0Formula.satisfies_toFO (zfCarrierMem M) _ sM
    _ <-> Delta0Formula.Satisfies Delta0Formula.ZFMem
          (Delta0Formula.kuratowskiPairEqAt pair input value) s := by
      exact Delta0Formula.satisfies_absolute hM _ sM
    _ <-> s pair = ZFSet.pair (s input) (s value) :=
      Delta0Formula.satisfies_kuratowskiPairEqAt pair input value s

@[simp]
theorem satisfiesIn_graphValueFormulaAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {m : Nat}
    (graph input value : Fin m) (s : Tuple ZFSet.{u} m)
    (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (graphValueFormulaAt graph input value) s <->
      ZFSet.pair (s input) (s value) ∈ s graph := by
  rw [graphValueFormulaAt]
  simp only [SatisfiesIn]
  constructor
  · rintro ⟨pair, hpairM, hpairEq, hpairGraph⟩
    have hs' : forall i, snoc s pair i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hpairM
      · simpa using hs j
    have hpair := (satisfiesIn_kuratowskiPairEqAt_iff_TextbookRecursionFormula_gch hM
      (Fin.last m) input.castSucc value.castSucc (snoc s pair) hs').mp hpairEq
    have hpairRaw : pair = ZFSet.pair (s input) (s value) := by
      simpa only [snoc_last, snoc_castSucc] using hpair
    rw [hpairRaw] at hpairGraph
    simpa only [snoc_last, snoc_castSucc] using hpairGraph
  · intro hpairGraph
    have hpairM : ZFSet.pair (s input) (s value) ∈ M :=
      hM.mem_trans hpairGraph (hs graph)
    refine ⟨ZFSet.pair (s input) (s value), hpairM, ?_, ?_⟩
    · have hs' : forall i,
          snoc s (ZFSet.pair (s input) (s value)) i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hpairM
        · simpa using hs j
      apply (satisfiesIn_kuratowskiPairEqAt_iff_TextbookRecursionFormula_gch hM
        (Fin.last m) input.castSucc value.castSucc
        (snoc s (ZFSet.pair (s input) (s value))) hs').mpr
      simp
    · simpa using hpairGraph

/-! ## Set-coded function graphs -/

/-- `graph` is a Kuratowski graph with domain exactly `domain`.  Totality and
uniqueness are asserted first; the second conjunct excludes non-pair or
off-domain elements of the graph. -/
def functionGraphOnFormulaAt {m : Nat}
    (graph domain : Fin m) : FOFormula m :=
  .conj
    (FOFormula.boundedAll domain <| .ex <| .conj
      (graphValueFormulaAt graph.castSucc.castSucc
        (Fin.last m).castSucc (Fin.last (m + 1)))
      (FOFormula.all <| FOFormula.imp
        (graphValueFormulaAt graph.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m + 2)))
        (.eq (Fin.last (m + 2)) (Fin.last (m + 1)).castSucc)))
    (FOFormula.boundedAll graph <| .ex <| .conj
      (.mem (Fin.last (m + 1)) domain.castSucc.castSucc)
      (.ex
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last m).castSucc.castSucc
          (Fin.last (m + 1)).castSucc
          (Fin.last (m + 2))).toFO))

@[simp]
theorem satisfiesIn_functionGraphOnFormulaAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {m : Nat}
    (graph domain : Fin m) (s : Tuple ZFSet.{u} m)
    (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (functionGraphOnFormulaAt graph domain) s <->
      ((forall input : ZFSet.{u}, input ∈ M -> input ∈ s domain ->
          exists value : ZFSet.{u}, value ∈ M ∧
            ZFSet.pair input value ∈ s graph ∧
            forall other : ZFSet.{u}, other ∈ M ->
              ZFSet.pair input other ∈ s graph -> other = value) ∧
        forall pair : ZFSet.{u}, pair ∈ M -> pair ∈ s graph ->
          exists input : ZFSet.{u}, input ∈ M ∧ input ∈ s domain ∧
            exists value : ZFSet.{u}, value ∈ M ∧
              pair = ZFSet.pair input value) := by
  rw [functionGraphOnFormulaAt]
  simp only [SatisfiesIn, satisfiesIn_boundedAll_iff_TextbookRecursionFormula_gch,
    satisfiesIn_all_iff_TextbookRecursionFormula_gch, satisfiesIn_imp_iff_TextbookRecursionFormula_gch]
  constructor
  · rintro ⟨htotal, hcovered⟩
    constructor
    · intro input hinputM hinputDomain
      rcases htotal input hinputM hinputDomain with
        ⟨value, hvalueM, hvalue, hunique⟩
      have hsValue : forall i, snoc (snoc s input) value i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hinputM
          · simpa using hs k
      have hvaluePair := (satisfiesIn_graphValueFormulaAt_iff hM
        graph.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m + 1))
        (snoc (snoc s input) value) hsValue).mp hvalue
      refine ⟨value, hvalueM, by simpa using hvaluePair, ?_⟩
      intro other hotherM hotherPair
      have hsOther : forall i,
          snoc (snoc (snoc s input) value) other i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hotherM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hvalueM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa using hinputM
            · simpa using hs l
      have hotherFormula : SatisfiesIn (M : Set ZFSet.{u})
          (graphValueFormulaAt graph.castSucc.castSucc.castSucc
            (Fin.last m).castSucc.castSucc (Fin.last (m + 2)))
          (snoc (snoc (snoc s input) value) other) := by
        apply (satisfiesIn_graphValueFormulaAt_iff hM
          graph.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m + 2))
          (snoc (snoc (snoc s input) value) other) hsOther).mpr
        simpa using hotherPair
      have heq := hunique other hotherM hotherFormula
      simpa only [snoc_last, snoc_castSucc, SatisfiesIn] using heq
    · intro pair hpairM hpairGraph
      rcases hcovered pair hpairM hpairGraph with
        ⟨input, hinputM, hinputDomain, value, hvalueM, hpairFormula⟩
      have hsPair : forall i,
          snoc (snoc (snoc s pair) input) value i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hinputM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa using hpairM
            · simpa using hs l
      have hpairEq := (satisfiesIn_kuratowskiPairEqAt_iff_TextbookRecursionFormula_gch hM
        (Fin.last m).castSucc.castSucc
        (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s pair) input) value) hsPair).mp hpairFormula
      refine ⟨input, hinputM, ?_, value, hvalueM, ?_⟩
      · simpa only [snoc_last, snoc_castSucc] using hinputDomain
      · simpa only [snoc_last, snoc_castSucc] using hpairEq
  · rintro ⟨htotal, hcovered⟩
    constructor
    · intro input hinputM hinputDomain
      rcases htotal input hinputM hinputDomain with
        ⟨value, hvalueM, hvaluePair, hunique⟩
      refine ⟨value, hvalueM, ?_, ?_⟩
      · have hsValue : forall i, snoc (snoc s input) value i ∈ M := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hvalueM
          · refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hinputM
            · simpa using hs k
        apply (satisfiesIn_graphValueFormulaAt_iff hM
          graph.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m + 1))
          (snoc (snoc s input) value) hsValue).mpr
        simpa using hvaluePair
      · intro other hotherM hotherFormula
        have hsOther : forall i,
            snoc (snoc (snoc s input) value) other i ∈ M := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hotherM
          · refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hvalueM
            · refine Fin.lastCases ?_ (fun l => ?_) k
              · simpa using hinputM
              · simpa using hs l
        have hotherPair := (satisfiesIn_graphValueFormulaAt_iff hM
          graph.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m + 2))
          (snoc (snoc (snoc s input) value) other) hsOther).mp
            hotherFormula
        have heq := hunique other hotherM (by simpa using hotherPair)
        simpa only [snoc_last, snoc_castSucc, SatisfiesIn] using heq
    · intro pair hpairM hpairGraph
      rcases hcovered pair hpairM hpairGraph with
        ⟨input, hinputM, hinputDomain, value, hvalueM, hpairEq⟩
      refine ⟨input, hinputM, ?_, value, hvalueM, ?_⟩
      · simpa using hinputDomain
      · have hsPair : forall i,
            snoc (snoc (snoc s pair) input) value i ∈ M := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hvalueM
          · refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hinputM
            · refine Fin.lastCases ?_ (fun l => ?_) k
              · simpa using hpairM
              · simpa using hs l
        apply (satisfiesIn_kuratowskiPairEqAt_iff_TextbookRecursionFormula_gch hM
          (Fin.last m).castSucc.castSucc
          (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
          (snoc (snoc (snoc s pair) input) value) hsPair).mpr
        simpa only [snoc_last, snoc_castSucc] using hpairEq

/-! ## Restricting a graph to the predecessors of one point -/

/-- `restriction` consists exactly of the pairs in `graph` whose first
coordinate belongs to the formula class and is related to `top`. -/
def restrictionGraphFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (graph top restriction : Fin m) :
    FOFormula m :=
  FOFormula.all <| FOFormula.biimp
    (.mem (Fin.last m) restriction.castSucc)
    (.conj
      (.mem (Fin.last m) graph.castSucc)
      (.ex <| .ex <| .conj
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last m).castSucc.castSucc
          (Fin.last (m + 1)).castSucc
          (Fin.last (m + 2))).toFO
        (.conj
          (classFormulaAt classFormula
            (fun i => (params i).castSucc.castSucc.castSucc)
            (Fin.last (m + 1)).castSucc)
          (relationFormulaAt relationFormula
            (fun i => (params i).castSucc.castSucc.castSucc)
            (Fin.last (m + 1)).castSucc top.castSucc.castSucc.castSucc))))

@[simp]
theorem satisfiesIn_restrictionGraphFormulaAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (graph top restriction : Fin m)
    (s : Tuple ZFSet.{u} m) (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (restrictionGraphFormulaAt classFormula relationFormula
          params graph top restriction) s <->
      forall pair : ZFSet.{u}, pair ∈ M ->
        (pair ∈ s restriction <->
          pair ∈ s graph ∧
          exists input : ZFSet.{u}, input ∈ M ∧
            exists value : ZFSet.{u}, value ∈ M ∧
              pair = ZFSet.pair input value ∧
              SatisfiesIn (M : Set ZFSet.{u}) classFormula
                (snoc (fun i => s (params i)) input) ∧
              SatisfiesIn (M : Set ZFSet.{u}) relationFormula
                (snoc (snoc (fun i => s (params i)) input) (s top))) := by
  rw [restrictionGraphFormulaAt, satisfiesIn_all_iff_TextbookRecursionFormula_gch]
  simp only [satisfiesIn_biimp_iff_TextbookRecursionFormula_gch, SatisfiesIn,
    satisfiesIn_classFormulaAt_iff,
    satisfiesIn_relationFormulaAt_iff,
    snoc_last, snoc_castSucc]
  constructor
  · intro h pair hpairM
    have hpairSemantic := h pair hpairM
    constructor
    · intro hpairRestriction
      rcases hpairSemantic.mp hpairRestriction with
        ⟨hpairGraph, input, hinputM, value, hvalueM,
          hpairFormula, hclass, hrelation⟩
      have hsPair : forall i,
          snoc (snoc (snoc s pair) input) value i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hinputM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa using hpairM
            · simpa using hs l
      have hpairEq := (satisfiesIn_kuratowskiPairEqAt_iff_TextbookRecursionFormula_gch hM
        (Fin.last m).castSucc.castSucc
        (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s pair) input) value) hsPair).mp hpairFormula
      refine ⟨by simpa using hpairGraph,
        input, hinputM, value, hvalueM, ?_, ?_, ?_⟩
      · simpa only [snoc_last, snoc_castSucc] using hpairEq
      · simpa only [snoc_last, snoc_castSucc] using hclass
      · simpa only [snoc_last, snoc_castSucc] using hrelation
    · rintro ⟨hpairGraph, input, hinputM, value, hvalueM,
        hpairEq, hclass, hrelation⟩
      apply hpairSemantic.mpr
      refine ⟨by simpa using hpairGraph,
        input, hinputM, value, hvalueM, ?_, ?_, ?_⟩
      · have hsPair : forall i,
            snoc (snoc (snoc s pair) input) value i ∈ M := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hvalueM
          · refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hinputM
            · refine Fin.lastCases ?_ (fun l => ?_) k
              · simpa using hpairM
              · simpa using hs l
        apply (satisfiesIn_kuratowskiPairEqAt_iff_TextbookRecursionFormula_gch hM
          (Fin.last m).castSucc.castSucc
          (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
          (snoc (snoc (snoc s pair) input) value) hsPair).mpr
        simpa only [snoc_last, snoc_castSucc] using hpairEq
      · simpa only [snoc_last, snoc_castSucc] using hclass
      · simpa only [snoc_last, snoc_castSucc] using hrelation
  · intro h pair hpairM
    have hpairRaw := h pair hpairM
    constructor
    · intro hpairRestriction
      rcases hpairRaw.mp hpairRestriction with
        ⟨hpairGraph, input, hinputM, value, hvalueM,
          hpairEq, hclass, hrelation⟩
      refine ⟨by simpa using hpairGraph,
        input, hinputM, value, hvalueM, ?_, ?_, ?_⟩
      · have hsPair : forall i,
            snoc (snoc (snoc s pair) input) value i ∈ M := by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hvalueM
          · refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hinputM
            · refine Fin.lastCases ?_ (fun l => ?_) k
              · simpa using hpairM
              · simpa using hs l
        apply (satisfiesIn_kuratowskiPairEqAt_iff_TextbookRecursionFormula_gch hM
          (Fin.last m).castSucc.castSucc
          (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
          (snoc (snoc (snoc s pair) input) value) hsPair).mpr
        simpa only [snoc_last, snoc_castSucc] using hpairEq
      · simpa only [snoc_last, snoc_castSucc] using hclass
      · simpa only [snoc_last, snoc_castSucc] using hrelation
    · rintro ⟨hpairGraph, input, hinputM, value, hvalueM,
        hpairFormula, hclass, hrelation⟩
      apply hpairRaw.mpr
      have hsPair : forall i,
          snoc (snoc (snoc s pair) input) value i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hinputM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa using hpairM
            · simpa using hs l
      have hpairEq := (satisfiesIn_kuratowskiPairEqAt_iff_TextbookRecursionFormula_gch hM
        (Fin.last m).castSucc.castSucc
        (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s pair) input) value) hsPair).mp hpairFormula
      refine ⟨by simpa using hpairGraph,
        input, hinputM, value, hvalueM, ?_, ?_, ?_⟩
      · simpa only [snoc_last, snoc_castSucc] using hpairEq
      · simpa only [snoc_last, snoc_castSucc] using hclass
      · simpa only [snoc_last, snoc_castSucc] using hrelation

/-- Public parameter layout `(params,graph,top,restriction)`. -/
def restrictionGraphFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula (n + 3) :=
  restrictionGraphFormulaAt classFormula relationFormula
    (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc
    (Fin.last (n + 1)).castSucc
    (Fin.last (n + 2))

@[simp]
theorem satisfiesIn_restrictionGraphFormula_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (graph top restriction : ZFSet.{u})
    (hparams : forall i, params i ∈ M)
    (hgraph : graph ∈ M) (htop : top ∈ M)
    (hrestriction : restriction ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (restrictionGraphFormula classFormula relationFormula)
        (snoc (snoc (snoc params graph) top) restriction) <->
      forall pair : ZFSet.{u}, pair ∈ M ->
        (pair ∈ restriction <->
          pair ∈ graph ∧
          exists input : ZFSet.{u}, input ∈ M ∧
            exists value : ZFSet.{u}, value ∈ M ∧
              pair = ZFSet.pair input value ∧
              SatisfiesIn (M : Set ZFSet.{u}) classFormula
                (snoc params input) ∧
              SatisfiesIn (M : Set ZFSet.{u}) relationFormula
                (snoc (snoc params input) top)) := by
  let s := snoc (snoc (snoc params graph) top) restriction
  have hs : forall i, s i ∈ M := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [s] using hrestriction
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [s] using htop
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · simpa [s] using hgraph
        · simpa [s] using hparams l
  simpa only [restrictionGraphFormula, s, snoc_last, snoc_castSucc] using
    (satisfiesIn_restrictionGraphFormulaAt_iff hM classFormula
      relationFormula (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc (Fin.last (n + 1)).castSucc
      (Fin.last (n + 2)) s hs)

/-! ## Reusable set predicates -/

/-- Every member of `set` satisfies `classFormula`. -/
def subsetClassFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (params : Fin n -> Fin m) (set : Fin m) : FOFormula m :=
  FOFormula.all <| FOFormula.imp
    (.mem (Fin.last m) set.castSucc)
    (classFormulaAt classFormula
      (fun i => (params i).castSucc) (Fin.last m))

/-- The set at `left` is a subset of the set at `right`. -/
def subsetFormulaAt {m : Nat} (left right : Fin m) : FOFormula m :=
  FOFormula.all <| FOFormula.imp
    (.mem (Fin.last m) left.castSucc)
    (.mem (Fin.last m) right.castSucc)

/-- `set` is downward closed under the formula relation, relative to the
formula class. -/
def downwardClosedFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (set : Fin m) : FOFormula m :=
  FOFormula.all <| FOFormula.imp
    (.mem (Fin.last m) set.castSucc)
    (FOFormula.all <| FOFormula.imp
      (.conj
        (classFormulaAt classFormula
          (fun i => (params i).castSucc.castSucc) (Fin.last (m + 1)))
        (relationFormulaAt relationFormula
          (fun i => (params i).castSucc.castSucc)
          (Fin.last (m + 1)) (Fin.last m).castSucc))
      (.mem (Fin.last (m + 1)) set.castSucc.castSucc))

@[simp]
theorem satisfiesIn_subsetClassFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (params : Fin n -> Fin m) (set : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (subsetClassFormulaAt classFormula params set) s <->
      forall z : ZFSet.{u}, z ∈ M -> z ∈ s set ->
        SatisfiesIn M classFormula
          (snoc (fun i => s (params i)) z) := by
  rw [subsetClassFormulaAt, satisfiesIn_all_iff_TextbookRecursionFormula_gch]
  simp only [satisfiesIn_imp_iff_TextbookRecursionFormula_gch, SatisfiesIn,
    satisfiesIn_classFormulaAt_iff, snoc_last, snoc_castSucc]

@[simp]
theorem satisfiesIn_subsetFormulaAt_iff
    (M : Set ZFSet.{u}) {m : Nat} (left right : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (subsetFormulaAt left right) s <->
      forall z : ZFSet.{u}, z ∈ M -> z ∈ s left -> z ∈ s right := by
  rw [subsetFormulaAt, satisfiesIn_all_iff_TextbookRecursionFormula_gch]
  simp only [satisfiesIn_imp_iff_TextbookRecursionFormula_gch, SatisfiesIn,
    snoc_last, snoc_castSucc]

@[simp]
theorem satisfiesIn_downwardClosedFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (set : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M
        (downwardClosedFormulaAt classFormula relationFormula params set) s <->
      forall t : ZFSet.{u}, t ∈ M -> t ∈ s set ->
        forall y : ZFSet.{u}, y ∈ M ->
          SatisfiesIn M classFormula
              (snoc (fun i => s (params i)) y) ->
          SatisfiesIn M relationFormula
              (snoc (snoc (fun i => s (params i)) y) t) ->
          y ∈ s set := by
  rw [downwardClosedFormulaAt, satisfiesIn_all_iff_TextbookRecursionFormula_gch]
  simp only [satisfiesIn_imp_iff_TextbookRecursionFormula_gch, SatisfiesIn, snoc_last,
    snoc_castSucc, satisfiesIn_all_iff_TextbookRecursionFormula_gch,
    satisfiesIn_classFormulaAt_iff,
    satisfiesIn_relationFormulaAt_iff]
  constructor
  · intro h t htM htSet y hyM hyClass hyRelation
    exact h t htM htSet y hyM ⟨hyClass, hyRelation⟩
  · intro h t htM htSet y hyM hy
    exact h t htM htSet y hyM hy.1 hy.2

/-! ## Displayed predecessor sets -/

/-- In the layout `(params,x,predecessors)`, this formula says that
`predecessors` has exactly the members of the formula class which are related
to `x`. -/
def predecessorSetFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula (n + 2) :=
  FOFormula.all <| FOFormula.biimp
    (.mem (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc)
    (.conj
      (classFormulaAt classFormula
        (fun i => i.castSucc.castSucc.castSucc) (Fin.last (n + 2)))
      (relationFormulaAt relationFormula
        (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc))

@[simp]
theorem satisfiesIn_predecessorSetFormula_iff
    (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (x predecessors : ZFSet.{u}) :
    SatisfiesIn M (predecessorSetFormula classFormula relationFormula)
        (snoc (snoc params x) predecessors) <->
      forall y : ZFSet.{u}, y ∈ M ->
        (y ∈ predecessors <->
          SatisfiesIn M classFormula (snoc params y) ∧
          SatisfiesIn M relationFormula (snoc (snoc params y) x)) := by
  rw [predecessorSetFormula, satisfiesIn_all_iff_TextbookRecursionFormula_gch]
  simp only [satisfiesIn_biimp_iff_TextbookRecursionFormula_gch, SatisfiesIn,
    satisfiesIn_classFormulaAt_iff,
    satisfiesIn_relationFormulaAt_iff, snoc_last, snoc_castSucc]

/-! ## The internal assertion that the relation is set-like -/

/-- The formula, in the parameter context, saying that `relationFormula`
defines a relation on `classFormula` and every point of that class has a
displayed predecessor set. -/
def setLikeRelationOnFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula n :=
  .conj
    (FOFormula.all <| FOFormula.all <| FOFormula.imp
      (relationFormulaAt relationFormula
        (fun i => i.castSucc.castSucc)
        (Fin.last n).castSucc (Fin.last (n + 1)))
      (.conj
        (classFormulaAt classFormula
          (fun i => i.castSucc.castSucc) (Fin.last n).castSucc)
        (classFormulaAt classFormula
          (fun i => i.castSucc.castSucc) (Fin.last (n + 1)))))
    (FOFormula.all <| FOFormula.imp
      (classFormulaAt classFormula (fun i => i.castSucc) (Fin.last n))
      (.ex (predecessorSetFormula classFormula relationFormula)))

@[simp]
theorem satisfiesIn_setLikeRelationOnFormula_iff
    (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) :
    SatisfiesIn M (setLikeRelationOnFormula classFormula relationFormula)
        params <->
      (forall y : ZFSet.{u}, y ∈ M ->
        forall x : ZFSet.{u}, x ∈ M ->
          SatisfiesIn M relationFormula (snoc (snoc params y) x) ->
            SatisfiesIn M classFormula (snoc params y) ∧
            SatisfiesIn M classFormula (snoc params x)) ∧
      forall x : ZFSet.{u}, x ∈ M ->
        SatisfiesIn M classFormula (snoc params x) ->
          exists predecessors : ZFSet.{u}, predecessors ∈ M ∧
            forall y : ZFSet.{u}, y ∈ M ->
              (y ∈ predecessors <->
                SatisfiesIn M classFormula (snoc params y) ∧
                SatisfiesIn M relationFormula
                  (snoc (snoc params y) x)) := by
  rw [setLikeRelationOnFormula]
  simp only [SatisfiesIn, satisfiesIn_all_iff_TextbookRecursionFormula_gch,
    satisfiesIn_imp_iff_TextbookRecursionFormula_gch, satisfiesIn_classFormulaAt_iff,
    satisfiesIn_relationFormulaAt_iff, snoc_last, snoc_castSucc,
    satisfiesIn_predecessorSetFormula_iff]

/-! ## The canonical local recursion domain -/

/-- In the layout `(params,x,domain)`, this formula says that `domain` is the
least subset of the formula class which contains `x` and is downward closed
under the formula relation. -/
def localDomainFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula (n + 2) :=
  let params : Fin n -> Fin (n + 2) := fun i => i.castSucc.castSucc
  let x : Fin (n + 2) := (Fin.last n).castSucc
  let domain : Fin (n + 2) := Fin.last (n + 1)
  .conj
    (classFormulaAt classFormula params x)
    (.conj
      (.mem x domain)
      (.conj
        (subsetClassFormulaAt classFormula params domain)
        (.conj
          (downwardClosedFormulaAt classFormula relationFormula params domain)
          (FOFormula.all <| FOFormula.imp
            (.conj
              (.mem x.castSucc (Fin.last (n + 2)))
              (.conj
                (subsetClassFormulaAt classFormula
                  (fun i => (params i).castSucc) (Fin.last (n + 2)))
                (downwardClosedFormulaAt classFormula relationFormula
                  (fun i => (params i).castSucc) (Fin.last (n + 2)))))
            (subsetFormulaAt domain.castSucc (Fin.last (n + 2)))))))

@[simp]
theorem satisfiesIn_localDomainFormula_iff
    (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (x domain : ZFSet.{u}) :
    SatisfiesIn M (localDomainFormula classFormula relationFormula)
        (snoc (snoc params x) domain) <->
      SatisfiesIn M classFormula (snoc params x) ∧
      x ∈ domain ∧
      (forall z : ZFSet.{u}, z ∈ M -> z ∈ domain ->
        SatisfiesIn M classFormula (snoc params z)) ∧
      (forall t : ZFSet.{u}, t ∈ M -> t ∈ domain ->
        forall y : ZFSet.{u}, y ∈ M ->
          SatisfiesIn M classFormula (snoc params y) ->
          SatisfiesIn M relationFormula (snoc (snoc params y) t) ->
          y ∈ domain) ∧
      forall candidate : ZFSet.{u}, candidate ∈ M ->
        x ∈ candidate ->
        (forall z : ZFSet.{u}, z ∈ M -> z ∈ candidate ->
          SatisfiesIn M classFormula (snoc params z)) ->
        (forall t : ZFSet.{u}, t ∈ M -> t ∈ candidate ->
          forall y : ZFSet.{u}, y ∈ M ->
            SatisfiesIn M classFormula (snoc params y) ->
            SatisfiesIn M relationFormula (snoc (snoc params y) t) ->
            y ∈ candidate) ->
        forall z : ZFSet.{u}, z ∈ M -> z ∈ domain -> z ∈ candidate := by
  rw [localDomainFormula]
  simp only [SatisfiesIn, satisfiesIn_classFormulaAt_iff,
    satisfiesIn_subsetClassFormulaAt_iff,
    satisfiesIn_downwardClosedFormulaAt_iff,
    satisfiesIn_all_iff_TextbookRecursionFormula_gch, satisfiesIn_imp_iff_TextbookRecursionFormula_gch,
    satisfiesIn_subsetFormulaAt_iff, snoc_last, snoc_castSucc]
  have hparams : (fun i => params i) = params := rfl
  simp only [hparams]
  constructor
  · rintro ⟨hxFormula, hxDomain, hsubset, hclosed, hleast⟩
    refine ⟨hxFormula, hxDomain, hsubset, hclosed, ?_⟩
    intro candidate hcandidateM hxCandidate hcandidateSubset
      hcandidateClosed
    exact hleast candidate hcandidateM
      ⟨hxCandidate, hcandidateSubset, hcandidateClosed⟩
  · rintro ⟨hxFormula, hxDomain, hsubset, hclosed, hleast⟩
    refine ⟨hxFormula, hxDomain, hsubset, hclosed, ?_⟩
    intro candidate hcandidateM hcandidate
    exact hleast candidate hcandidateM hcandidate.1
      hcandidate.2.1 hcandidate.2.2

/-- Insert the public local-domain formula into a larger variable context. -/
def localDomainFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (x domain : Fin m) : FOFormula m :=
  FOFormula.rename
    (Fin.lastCases domain (fun j => Fin.lastCases x params j))
    (localDomainFormula classFormula relationFormula)

@[simp]
theorem satisfiesIn_localDomainFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (x domain : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M
        (localDomainFormulaAt classFormula relationFormula params x domain) s <->
      SatisfiesIn M (localDomainFormula classFormula relationFormula)
        (snoc (snoc (fun i => s (params i)) (s x)) (s domain)) := by
  rw [localDomainFormulaAt, satisfiesIn_rename_iff_TextbookRecursionFormula_gch]
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

/-! ## Agreement with the textbook `d_x` -/

/-- The actual textbook local domain is the least downward-closed subclass of
`A` containing its top point. -/
theorem localRecursionDomain_subset_of_closed
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hxA : x ∈ A) {D : Set ZFSet.{u}} (hxD : x ∈ D)
    (hclosed : forall t, t ∈ D -> forall y,
      y ∈ A -> ClassRel R y t -> y ∈ D) :
    (localRecursionDomain A R hsetLike x : Set ZFSet.{u}) ⊆ D := by
  have hlayers : forall k,
      (predecessorLayer A R hsetLike x k : Set ZFSet.{u}) ⊆ D := by
    intro k
    induction k with
    | zero =>
        intro y hy
        have hySpec := (displayedPredecessors_spec hsetLike hxA y).mp hy
        exact hclosed x hxD y hySpec.1 hySpec.2
    | succ k ih =>
        intro y hy
        rcases (mem_predecessorLayer_succ_iff hsetLike hxA k).mp hy with
          ⟨t, htLayer, hyA, hyt⟩
        exact hclosed t (ih htLayer) y hyA hyt
  intro z hz
  rcases mem_localRecursionDomain_iff.mp hz with rfl | hzClosure
  · exact hxD
  · rcases mem_predecessorClosure_iff.mp hzClosure with ⟨k, hzk⟩
    exact hlayers k hzk



/-! ## Local solution graphs -/

/-- In the layout `(params,x,graph)`, assert that `graph` is a local solution
on the canonical domain of `x`.  The restriction graph supplied to the step
formula at `t` is quantified independently; the definition contains no
self-reference and makes no claim that a witness exists in a given model. -/
def localSolutionFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3)) : FOFormula (n + 2) :=
  let params : Fin n -> Fin (n + 2) := fun i => i.castSucc.castSucc
  let x : Fin (n + 2) := (Fin.last n).castSucc
  let graph : Fin (n + 2) := Fin.last (n + 1)
  let domain : Fin (n + 3) := Fin.last (n + 2)
  let top : Fin (n + 4) := Fin.last (n + 3)
  let restriction : Fin (n + 5) := Fin.last (n + 4)
  let value : Fin (n + 6) := Fin.last (n + 5)
  .ex <| .conj
    (localDomainFormulaAt classFormula relationFormula
      (fun i => (params i).castSucc) x.castSucc domain)
    (.conj
      (functionGraphOnFormulaAt graph.castSucc domain)
      (FOFormula.boundedAll domain <| .ex <| .ex <| .conj
        (restrictionGraphFormulaAt classFormula relationFormula
          (fun i => (params i).castSucc.castSucc.castSucc.castSucc)
          graph.castSucc.castSucc.castSucc.castSucc
          top.castSucc.castSucc restriction.castSucc)
        (.conj
          (graphValueFormulaAt
            graph.castSucc.castSucc.castSucc.castSucc
            top.castSucc.castSucc value)
          (stepFormulaAt stepFormula
            (fun i => (params i).castSucc.castSucc.castSucc.castSucc)
            top.castSucc.castSucc restriction.castSucc value))))

@[simp]
theorem satisfiesIn_localSolutionFormula_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n) (x graph : ZFSet.{u})
    (hparams : forall i, params i ∈ M) (hx : x ∈ M)
    (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) graph) <->
      exists domain : ZFSet.{u}, domain ∈ M ∧
        SatisfiesIn (M : Set ZFSet.{u})
          (localDomainFormula classFormula relationFormula)
          (snoc (snoc params x) domain) ∧
        (((forall input : ZFSet.{u}, input ∈ M -> input ∈ domain ->
              exists value : ZFSet.{u}, value ∈ M ∧
                ZFSet.pair input value ∈ graph ∧
                forall other : ZFSet.{u}, other ∈ M ->
                  ZFSet.pair input other ∈ graph -> other = value) ∧
            forall pair : ZFSet.{u}, pair ∈ M -> pair ∈ graph ->
              exists input : ZFSet.{u}, input ∈ M ∧ input ∈ domain ∧
                exists value : ZFSet.{u}, value ∈ M ∧
                  pair = ZFSet.pair input value) ∧
          forall top : ZFSet.{u}, top ∈ M -> top ∈ domain ->
            exists restriction : ZFSet.{u}, restriction ∈ M ∧
              exists value : ZFSet.{u}, value ∈ M ∧
                (forall pair : ZFSet.{u}, pair ∈ M ->
                  (pair ∈ restriction <->
                    pair ∈ graph ∧
                    exists input : ZFSet.{u}, input ∈ M ∧
                      exists output : ZFSet.{u}, output ∈ M ∧
                        pair = ZFSet.pair input output ∧
                        SatisfiesIn (M : Set ZFSet.{u}) classFormula
                          (snoc params input) ∧
                        SatisfiesIn (M : Set ZFSet.{u}) relationFormula
                          (snoc (snoc params input) top))) ∧
                ZFSet.pair top value ∈ graph ∧
                SatisfiesIn (M : Set ZFSet.{u}) stepFormula
                  (snoc (snoc (snoc params top) restriction) value)) := by
  let s := snoc (snoc params x) graph
  have hs : forall i, s i ∈ M := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [s] using hgraph
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [s] using hx
      · simpa [s] using hparams k
  change SatisfiesIn (M : Set ZFSet.{u})
      (localSolutionFormula classFormula relationFormula stepFormula) s <-> _
  rw [localSolutionFormula]
  constructor
  · rintro ⟨domain, hdomainM, hlocalRaw, hfunctionRaw, hstepsRaw⟩
    have hsDomain : forall i, snoc s domain i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hdomainM
      · simpa using hs j
    have hlocal := (satisfiesIn_localDomainFormulaAt_iff
      (M : Set ZFSet.{u}) classFormula relationFormula
      (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc (Fin.last (n + 2))
      (snoc s domain)).mp hlocalRaw
    have hfunction := (satisfiesIn_functionGraphOnFormulaAt_iff hM
      (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
      (snoc s domain) hsDomain).mp hfunctionRaw
    refine ⟨domain, hdomainM, ?_, ?_, ?_⟩
    · simpa only [s, snoc_last, snoc_castSucc] using hlocal
    · simpa only [s, snoc_last, snoc_castSucc] using hfunction
    · have hsteps := (satisfiesIn_boundedAll_iff_TextbookRecursionFormula_gch
        (M : Set ZFSet.{u}) (Fin.last (n + 2)) _
        (snoc s domain)).mp hstepsRaw
      intro top htopM htopDomain
      have hstepRaw := hsteps top htopM (by simpa using htopDomain)
      rcases hstepRaw with
        ⟨restriction, hrestrictionM, value, hvalueM,
          hrestrictionRaw, hvalueRaw, hformulaRaw⟩
      let sFinal := snoc (snoc (snoc (snoc s domain) top)
        restriction) value
      have hsFinal : forall i, sFinal i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [sFinal] using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa [sFinal] using hrestrictionM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa [sFinal] using htopM
            · refine Fin.lastCases ?_ (fun a => ?_) l
              · simpa [sFinal] using hdomainM
              · simpa [sFinal] using hs a
      have hrestriction :=
        (satisfiesIn_restrictionGraphFormulaAt_iff hM classFormula
          relationFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc
          (Fin.last (n + 3)).castSucc.castSucc
          (Fin.last (n + 4)).castSucc sFinal hsFinal).mp hrestrictionRaw
      have hvalue := (satisfiesIn_graphValueFormulaAt_iff hM
        (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc
        (Fin.last (n + 3)).castSucc.castSucc (Fin.last (n + 5))
        sFinal hsFinal).mp hvalueRaw
      have hformula := (satisfiesIn_stepFormulaAt_iff
        (M : Set ZFSet.{u}) stepFormula
        (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last (n + 3)).castSucc.castSucc
        (Fin.last (n + 4)).castSucc (Fin.last (n + 5)) sFinal).mp
          hformulaRaw
      refine ⟨restriction, hrestrictionM, value, hvalueM, ?_, ?_, ?_⟩
      · simpa only [sFinal, s, snoc_last, snoc_castSucc] using hrestriction
      · simpa only [sFinal, s, snoc_last, snoc_castSucc] using hvalue
      · simpa only [sFinal, s, snoc_last, snoc_castSucc] using hformula
  · rintro ⟨domain, hdomainM, hlocal, hfunction, hsteps⟩
    have hsDomain : forall i, snoc s domain i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hdomainM
      · simpa using hs j
    refine ⟨domain, hdomainM, ?_, ?_, ?_⟩
    · apply (satisfiesIn_localDomainFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula relationFormula
        (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc (Fin.last (n + 2))
        (snoc s domain)).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hlocal
    · apply (satisfiesIn_functionGraphOnFormulaAt_iff hM
        (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
        (snoc s domain) hsDomain).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hfunction
    · apply (satisfiesIn_boundedAll_iff_TextbookRecursionFormula_gch
        (M : Set ZFSet.{u}) (Fin.last (n + 2)) _
        (snoc s domain)).mpr
      intro top htopM htopDomain
      rcases hsteps top htopM (by simpa using htopDomain) with
        ⟨restriction, hrestrictionM, value, hvalueM,
          hrestriction, hvalue, hformula⟩
      let sFinal := snoc (snoc (snoc (snoc s domain) top)
        restriction) value
      have hsFinal : forall i, sFinal i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [sFinal] using hvalueM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa [sFinal] using hrestrictionM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa [sFinal] using htopM
            · refine Fin.lastCases ?_ (fun a => ?_) l
              · simpa [sFinal] using hdomainM
              · simpa [sFinal] using hs a
      refine ⟨restriction, hrestrictionM, value, hvalueM, ?_, ?_, ?_⟩
      · apply (satisfiesIn_restrictionGraphFormulaAt_iff hM classFormula
          relationFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc
          (Fin.last (n + 3)).castSucc.castSucc
          (Fin.last (n + 4)).castSucc sFinal hsFinal).mpr
        simpa only [sFinal, s, snoc_last, snoc_castSucc] using hrestriction
      · apply (satisfiesIn_graphValueFormulaAt_iff hM
          (Fin.last (n + 1)).castSucc.castSucc.castSucc.castSucc
          (Fin.last (n + 3)).castSucc.castSucc (Fin.last (n + 5))
          sFinal hsFinal).mpr
        simpa only [sFinal, s, snoc_last, snoc_castSucc] using hvalue
      · apply (satisfiesIn_stepFormulaAt_iff
          (M : Set ZFSet.{u}) stepFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 3)).castSucc.castSucc
          (Fin.last (n + 4)).castSucc (Fin.last (n + 5)) sFinal).mpr
        simpa only [sFinal, s, snoc_last, snoc_castSucc] using hformula

/-- Insert the public local-solution formula into a larger context. -/
def localSolutionFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph : Fin m) : FOFormula m :=
  FOFormula.rename
    (Fin.lastCases graph (fun j => Fin.lastCases x params j))
    (localSolutionFormula classFormula relationFormula stepFormula)

@[simp]
theorem satisfiesIn_localSolutionFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Fin n -> Fin m) (x graph : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M
        (localSolutionFormulaAt classFormula relationFormula stepFormula
          params x graph) s <->
      SatisfiesIn M
        (localSolutionFormula classFormula relationFormula stepFormula)
        (snoc (snoc (fun i => s (params i)) (s x)) (s graph)) := by
  rw [localSolutionFormulaAt, satisfiesIn_rename_iff_TextbookRecursionFormula_gch]
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

/-! ## The value relation defined by local recursion -/

/-- In the layout `(params,x,value)`, assert that `x` belongs to the formula
class and some model-internal local solution graph takes `x` to `value`.
This is a non-self-referential first-order formula; existence of such a graph
is not part of the definition. -/
def recursionValueFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3)) : FOFormula (n + 2) :=
  let params : Fin n -> Fin (n + 2) := fun i => i.castSucc.castSucc
  let x : Fin (n + 2) := (Fin.last n).castSucc
  let value : Fin (n + 2) := Fin.last (n + 1)
  .conj
    (classFormulaAt classFormula params x)
    (.ex <| .conj
      (localSolutionFormulaAt classFormula relationFormula stepFormula
        (fun i => (params i).castSucc) x.castSucc (Fin.last (n + 2)))
      (graphValueFormulaAt
        (Fin.last (n + 2)) x.castSucc value.castSucc))

@[simp]
theorem satisfiesIn_recursionValueFormula_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n) (x value : ZFSet.{u})
    (hparams : forall i, params i ∈ M) (hx : x ∈ M)
    (hvalue : value ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (recursionValueFormula classFormula relationFormula stepFormula)
        (snoc (snoc params x) value) <->
      SatisfiesIn (M : Set ZFSet.{u}) classFormula (snoc params x) ∧
      exists graph : ZFSet.{u}, graph ∈ M ∧
        SatisfiesIn (M : Set ZFSet.{u})
          (localSolutionFormula classFormula relationFormula stepFormula)
          (snoc (snoc params x) graph) ∧
        ZFSet.pair x value ∈ graph := by
  let s := snoc (snoc params x) value
  have hs : forall i, s i ∈ M := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [s] using hvalue
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [s] using hx
      · simpa [s] using hparams k
  change SatisfiesIn (M : Set ZFSet.{u})
      (recursionValueFormula classFormula relationFormula stepFormula) s <-> _
  rw [recursionValueFormula]
  constructor
  · rintro ⟨hclassRaw, graph, hgraphM, hsolutionRaw, hpairRaw⟩
    have hclass := (satisfiesIn_classFormulaAt_iff
      (M : Set ZFSet.{u}) classFormula
      (fun i => i.castSucc.castSucc) (Fin.last n).castSucc s).mp hclassRaw
    have hsolution := (satisfiesIn_localSolutionFormulaAt_iff
      (M : Set ZFSet.{u}) classFormula relationFormula stepFormula
      (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc (Fin.last (n + 2))
      (snoc s graph)).mp hsolutionRaw
    have hsGraph : forall i, snoc s graph i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hgraphM
      · simpa using hs j
    have hpair := (satisfiesIn_graphValueFormulaAt_iff hM
      (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc
      (Fin.last (n + 1)).castSucc (snoc s graph) hsGraph).mp hpairRaw
    refine ⟨?_, graph, hgraphM, ?_, ?_⟩
    · simpa only [s, snoc_last, snoc_castSucc] using hclass
    · simpa only [s, snoc_last, snoc_castSucc] using hsolution
    · simpa only [s, snoc_last, snoc_castSucc] using hpair
  · rintro ⟨hclass, graph, hgraphM, hsolution, hpair⟩
    have hsGraph : forall i, snoc s graph i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hgraphM
      · simpa using hs j
    refine ⟨?_, graph, hgraphM, ?_, ?_⟩
    · apply (satisfiesIn_classFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula
        (fun i => i.castSucc.castSucc) (Fin.last n).castSucc s).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hclass
    · apply (satisfiesIn_localSolutionFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula relationFormula stepFormula
        (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc (Fin.last (n + 2))
        (snoc s graph)).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hsolution
    · apply (satisfiesIn_graphValueFormulaAt_iff hM
        (Fin.last (n + 2)) (Fin.last n).castSucc.castSucc
        (Fin.last (n + 1)).castSucc (snoc s graph) hsGraph).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hpair

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookRecursionFormula


/- Source module: Solutions.Work_CUGCH_TextbookEDomain -/
section GCHSource_Work_CUGCH_TextbookEDomain
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The well-founded domain for the textbook enumeration of definable sets

For the simultaneous recursion defining `E(a,n,m)`, the recursion domain is
the actual set `omega x omega` of Kuratowski pairs.  The relation ignores the
second coordinate:

`<i,k> R <m,n>` if and only if `i in m`.

Both the domain and the relation below are expressed by parameter-free
formulas in the pure membership language.  In particular, the external Lean
type `Nat x Nat` is used only as a proof device for well-foundedness; it is
never used as the set-theoretic recursion domain.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## The actual set-coded domain and relation -/

/-- The standard von Neumann omega, used in the set-coded recursion domain. -/
abbrev textbookEOmegaZF : ZFSet.{u} := Ordinal.omega0.toZFSet

/-- The actual set of Kuratowski codes `<m,n>` with `m,n in omega`. -/
def textbookEDomainZF : ZFSet.{u} :=
  ZFSet.prod textbookEOmegaZF textbookEOmegaZF

/-- The recursion domain as the external class represented by
`textbookEDomainZF`. -/
def TextbookEDomain : Set ZFSet.{u} :=
  (textbookEDomainZF : Set ZFSet.{u})

/-- The recursion relation on set-coded pairs.  Both arguments are required
to be genuine pairs of standard finite ordinals. -/
def TextbookERelation : Set (Tuple ZFSet.{u} 2) :=
  {s | exists i k m n : ZFSet.{u},
    i ∈ textbookEOmegaZF ∧ k ∈ textbookEOmegaZF ∧
    m ∈ textbookEOmegaZF ∧ n ∈ textbookEOmegaZF ∧
    s 0 = ZFSet.pair i k ∧ s 1 = ZFSet.pair m n ∧ i ∈ m}

@[simp]
theorem mem_textbookEDomain_iff {x : ZFSet.{u}} :
    x ∈ TextbookEDomain ↔
      exists m : ZFSet.{u}, m ∈ textbookEOmegaZF ∧
        exists n : ZFSet.{u}, n ∈ textbookEOmegaZF ∧
          x = ZFSet.pair m n := by
  exact ZFSet.mem_prod

@[simp]
theorem classRel_textbookERelation_iff
    (left right : ZFSet.{u}) :
    ClassRel TextbookERelation left right ↔
      exists i k m n : ZFSet.{u},
        i ∈ textbookEOmegaZF ∧ k ∈ textbookEOmegaZF ∧
        m ∈ textbookEOmegaZF ∧ n ∈ textbookEOmegaZF ∧
        left = ZFSet.pair i k ∧ right = ZFSet.pair m n ∧ i ∈ m := by
  rfl

/-! ## Pure membership-language formulas -/

namespace TextbookEFormula

/-- With coordinates `(left,right,omega)`, the bounded formula saying that
`left = <i,k>`, `right = <m,n>`, and `i in m`, for four coordinates bounded
by `omega`. -/
def relationDeltaAt {n : Nat}
    (left right omega : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedEx omega
    (Delta0Formula.boundedEx omega.castSucc
      (Delta0Formula.boundedEx omega.castSucc.castSucc
        (Delta0Formula.boundedEx omega.castSucc.castSucc.castSucc
          (.conj
            (Delta0Formula.kuratowskiPairEqAt
              left.castSucc.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc.castSucc
              (Fin.last (n + 1)).castSucc.castSucc)
            (.conj
              (Delta0Formula.kuratowskiPairEqAt
                right.castSucc.castSucc.castSucc.castSucc
                (Fin.last (n + 2)).castSucc
                (Fin.last (n + 3)))
              (.mem
                (Fin.last n).castSucc.castSucc.castSucc
                (Fin.last (n + 2)).castSucc))))))

@[simp]
theorem satisfies_relationDeltaAt {n : Nat}
    (left right omega : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (relationDeltaAt left right omega) s ↔
      exists i : ZFSet.{u}, i ∈ s omega ∧
        exists k : ZFSet.{u}, k ∈ s omega ∧
          exists m : ZFSet.{u}, m ∈ s omega ∧
            exists next : ZFSet.{u}, next ∈ s omega ∧
              s left = ZFSet.pair i k ∧
              s right = ZFSet.pair m next ∧ i ∈ m := by
  simp [relationDeltaAt]

/-- Parameter-free formula for membership in the set-coded domain
`omega x omega`. -/
def domainFormula : FOFormula 1 :=
  .ex (.conj
    (Model.standardOmegaAt (Fin.last 1))
    (TextbookDefFormula.productMemberDeltaAt
      (0 : Fin 2) (Fin.last 1) (Fin.last 1)).toFO)

/-- Parameter-free formula for the relation `<i,k> R <m,n>` iff `i in m`. -/
def relationFormula : FOFormula 2 :=
  .ex (.conj
    (Model.standardOmegaAt (Fin.last 2))
    (relationDeltaAt (0 : Fin 3) (1 : Fin 3) (Fin.last 2)).toFO)

end TextbookEFormula

namespace Model

noncomputable section

/-! ## Exact restricted semantics and absoluteness -/









end

end Model

/-! ## Exact predecessor sets and well-foundedness -/

theorem mem_textbookEOmega_of_mem_of_mem_textbookEOmega
    {i m : ZFSet.{u}} (hi : i ∈ m) (hm : m ∈ textbookEOmegaZF) :
    i ∈ textbookEOmegaZF := by
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m).mp hm with
    ⟨a, rfl⟩
  rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt i a).mp hi with
    ⟨b, _hb, rfl⟩
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
    (natCode b)).mpr ⟨b, rfl⟩

/-- At the key `<m,n>`, the full predecessor class is the actual set
`m x omega`. -/
theorem textbookE_predecessorSet
    {m n : ZFSet.{u}} (hm : m ∈ textbookEOmegaZF)
    (hn : n ∈ textbookEOmegaZF) :
    IsPredecessorSet TextbookEDomain TextbookERelation
      (ZFSet.pair m n) (ZFSet.prod m textbookEOmegaZF) := by
  intro y
  constructor
  · intro hy
    rcases ZFSet.mem_prod.mp hy with ⟨i, hi, k, hk, rfl⟩
    have hiOmega : i ∈ textbookEOmegaZF :=
      mem_textbookEOmega_of_mem_of_mem_textbookEOmega hi hm
    constructor
    · apply mem_textbookEDomain_iff.mpr
      exact ⟨i, hiOmega, k, hk, rfl⟩
    · rw [classRel_textbookERelation_iff]
      exact ⟨i, k, m, n, hiOmega, hk, hm, hn, rfl, rfl, hi⟩
  · rintro ⟨_hyDomain, hyRelation⟩
    rw [classRel_textbookERelation_iff] at hyRelation
    rcases hyRelation with
      ⟨i, k, m', n', hiOmega, hk, _hm', _hn',
        hyPair, hkeyPair, him'⟩
    have hcoordinates := ZFSet.pair_inj.mp hkeyPair
    have him : i ∈ m := by
      simpa only [hcoordinates.1] using him'
    exact ZFSet.mem_prod.mpr ⟨i, him, k, hk, hyPair⟩

/-- Every element of the domain has a unique pair of standard natural-number
coordinates.  This lemma is used only to define an external well-founded
measure. -/
 theorem exists_textbookENatCode
    (x : ZFCarrier textbookEDomainZF.{u}) :
    exists code : Nat × Nat,
      x.1 = ZFSet.pair (natCode code.1) (natCode code.2) := by
  rcases ZFSet.mem_prod.mp x.2 with ⟨m, hm, n, hn, hx⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m).mp hm with
    ⟨a, rfl⟩
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode n).mp hn with
    ⟨b, rfl⟩
  exact ⟨(a, b), hx⟩

/-- External decoding of a genuine set-coded key. -/
 noncomputable def textbookENatCode
    (x : ZFCarrier textbookEDomainZF.{u}) : Nat × Nat :=
  Classical.choose (exists_textbookENatCode x)

 theorem textbookENatCode_spec
    (x : ZFCarrier textbookEDomainZF.{u}) :
    x.1 = ZFSet.pair (natCode (textbookENatCode x).1)
      (natCode (textbookENatCode x).2) :=
  Classical.choose_spec (exists_textbookENatCode x)

 theorem textbookENatCode_first_lt_of_relation
    {left right : ZFCarrier textbookEDomainZF.{u}}
    (h : ClassRel TextbookERelation.{u} left.1 right.1) :
    (textbookENatCode left).1 < (textbookENatCode right).1 := by
  rw [classRel_textbookERelation_iff] at h
  rcases h with
    ⟨i, k, m, n, _hiOmega, _hk, _hm, _hn,
      hleft, hright, him⟩
  have hleftCoordinates := ZFSet.pair_inj.mp
    ((textbookENatCode_spec left).symm.trans hleft)
  have hrightCoordinates := ZFSet.pair_inj.mp
    ((textbookENatCode_spec right).symm.trans hright)
  have hcodes :
      (natCode (textbookENatCode left).1 : ZFSet.{u}) ∈
        natCode (textbookENatCode right).1 := by
    rw [hleftCoordinates.1, hrightCoordinates.1]
    exact him
  exact (natCode_mem_natCode_iff _ _).mp hcodes

theorem textbookERelation_isRelationOn :
    IsRelationOn TextbookEDomain.{u} TextbookERelation.{u} := by
  intro s hs
  rcases hs with
    ⟨i, k, m, n, hi, hk, hm, hn, hleft, hright, _him⟩
  intro j
  fin_cases j
  · apply mem_textbookEDomain_iff.mpr
    exact ⟨i, hi, k, hk, hleft⟩
  · apply mem_textbookEDomain_iff.mpr
    exact ⟨m, hm, n, hn, hright⟩

theorem textbookERelation_hasSetMinimaOn :
    HasSetMinimaOn TextbookEDomain.{u} TextbookERelation.{u} := by
  unfold TextbookEDomain
  apply (hasSetMinimaOn_iff_wellFounded_zfCarrier
    textbookEDomainZF.{u} TextbookERelation.{u}).mpr
  exact (WellFounded.onFun
    (f := fun x : ZFCarrier textbookEDomainZF.{u} =>
      (textbookENatCode x).1)
    (Nat.lt_wfRel).2).mono
    (fun _left _right h =>
      textbookENatCode_first_lt_of_relation h)

theorem textbookERelation_hasSetPredecessorsOn :
    HasSetPredecessorsOn TextbookEDomain.{u} TextbookERelation.{u} := by
  intro x hx
  rcases mem_textbookEDomain_iff.mp hx with ⟨m, hm, n, hn, rfl⟩
  exact ⟨ZFSet.prod m textbookEOmegaZF,
    textbookE_predecessorSet hm hn⟩

/-- The relation used for the textbook enumeration recursion is
well-founded and set-like on the actual set-coded domain. -/
theorem textbookERelation_isWellFoundedSetLikeOn :
    IsWellFoundedSetLikeOn TextbookEDomain.{u} TextbookERelation.{u} :=
  ⟨textbookERelation_isRelationOn,
    textbookERelation_hasSetMinimaOn,
    textbookERelation_hasSetPredecessorsOn⟩

namespace Model

/-! ## Closure and the internal set-likeness assertion -/







end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEDomain


/- Source module: Solutions.Work_CUGCH_TextbookEKeyDecode -/
section GCHSource_Work_CUGCH_TextbookEKeyDecode
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Metatheoretic decoding of keys in the textbook recursion domain

The recursion defining the textbook enumeration `E(a,n,m)` is indexed by
the actual set `omega x omega`. Its keys are Kuratowski pairs

`<natCode m, natCode n>`,

where the first coordinate is the recursive code `m` and the second is the
arity `n`. This file supplies the corresponding partial decoder into Lean's
metatheoretic type `Nat x Nat`.

`Classical.choose` below is used only to read the two unique coordinates in
the external implementation of the recursion step. The decoder is not an
internal function of a ZF model, and no Separation or Replacement argument
may use it as though its graph were internally available. The internal
domain and key formulas, together with their restricted semantics, are
proved independently in `TextbookEDomain`.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## Unique standard coordinates -/

/-- Two representations of a set as a pair of standard natural-number
codes have the same fields. -/
theorem textbookEKey_natCode_fields_unique
    {key : ZFSet.{u}} {m n m' n' : Nat}
    (h : key = ZFSet.pair (natCode m) (natCode n))
    (h' : key = ZFSet.pair (natCode m') (natCode n')) :
    And (m = m') (n = n') := by
  have hcoordinates := ZFSet.pair_inj.mp (h.symm.trans h')
  exact And.intro
    (natCode_injective hcoordinates.1)
    (natCode_injective hcoordinates.2)

/-- The proposition that `key` has standard natural-number coordinates,
packaged with the two coordinates as one metatheoretic product. -/
def IsTextbookEKey (key : ZFSet.{u}) : Prop :=
  Exists fun coordinates : Prod Nat Nat =>
    key = ZFSet.pair (natCode coordinates.1) (natCode coordinates.2)

/-- Decode a genuine textbook recursion key. Keys outside the represented
set `omega x omega` are sent to `none`.

The output order is `(recursiveCode, arity)`, matching the domain key
`<m,n>` and not the opposite order used by some graph encodings. -/
noncomputable def textbookEKeyDecode
    (key : ZFSet.{u}) : Option (Prod Nat Nat) := by
  classical
  exact if h : IsTextbookEKey key then some (Classical.choose h) else none

/-! ## Exact decoder specification -/

/-- The decoder returns `(m,n)` exactly for the Kuratowski key
`<natCode m,natCode n>`. -/
theorem textbookEKeyDecode_eq_some_iff
    (key : ZFSet.{u}) (m n : Nat) :
    Iff (textbookEKeyDecode key = some (m, n))
      (key = ZFSet.pair (natCode m) (natCode n)) := by
  rw [textbookEKeyDecode]
  split_ifs with hkey
  · have hcoordinates :
        key = ZFSet.pair (natCode (Classical.choose hkey).1)
          (natCode (Classical.choose hkey).2) :=
      Classical.choose_spec hkey
    constructor
    · intro hsome
      have hchosen : Classical.choose hkey = (m, n) :=
        Option.some.inj hsome
      rw [hchosen] at hcoordinates
      exact hcoordinates
    · intro hrequested
      have hfields := textbookEKey_natCode_fields_unique
        hcoordinates hrequested
      have hchosen : Classical.choose hkey = (m, n) :=
        Prod.ext hfields.1 hfields.2
      exact congrArg some hchosen
  · constructor
    · intro hnone
      cases hnone
    · intro hrequested
      exfalso
      apply hkey
      exact Exists.intro (m, n) hrequested

@[simp]
theorem textbookEKeyDecode_pair_natCode (m n : Nat) :
    textbookEKeyDecode
      (ZFSet.pair (natCode m : ZFSet.{u}) (natCode n)) = some (m, n) := by
  rw [textbookEKeyDecode_eq_some_iff]



/-! ## Agreement with the actual set-coded domain -/

/-- Existence of decoded fields is exactly membership in the actual
set-coded recursion domain `omega x omega`. -/
theorem textbookEKeyDecode_exists_iff_mem_textbookEDomain
    (key : ZFSet.{u}) :
    Iff
      (Exists fun m : Nat => Exists fun n : Nat =>
        textbookEKeyDecode key = some (m, n))
      (key ∈ TextbookEDomain) := by
  constructor
  · intro hdecoded
    cases hdecoded with
    | intro m hdecodedN =>
      cases hdecodedN with
      | intro n hdecode =>
        have hkey :=
          (textbookEKeyDecode_eq_some_iff key m n).mp hdecode
        have hmOmega :
            (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF :=
          (IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode m)).mpr (Exists.intro m rfl)
        have hnOmega :
            (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF :=
          (IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode n)).mpr (Exists.intro n rfl)
        apply mem_textbookEDomain_iff.mpr
        exact Exists.intro (natCode m)
          (And.intro hmOmega
            (Exists.intro (natCode n) (And.intro hnOmega hkey)))
  · intro hdomain
    have hrepresentation := mem_textbookEDomain_iff.mp hdomain
    cases hrepresentation with
    | intro m hmAnd =>
      have hm := hmAnd.1
      cases hmAnd.2 with
      | intro n hnAnd =>
        have hn := hnAnd.1
        have hkey := hnAnd.2
        have hmCode :=
          (IndexedSequenceZF.mem_omega_iff_exists_natCode m).mp hm
        cases hmCode with
        | intro mCode hmEq =>
          have hnCode :=
            (IndexedSequenceZF.mem_omega_iff_exists_natCode n).mp hn
          cases hnCode with
          | intro nCode hnEq =>
            subst m
            subst n
            exact Exists.intro mCode (Exists.intro nCode
              ((textbookEKeyDecode_eq_some_iff
                key mCode nCode).mpr hkey))

/-- Every element of the recursion domain has decoded coordinates in the
declared order `(recursiveCode, arity)`. -/
theorem exists_textbookEKeyDecode_of_mem_textbookEDomain
    {key : ZFSet.{u}} (hkey : key ∈ TextbookEDomain) :
    Exists fun m : Nat => Exists fun n : Nat =>
      And (textbookEKeyDecode key = some (m, n))
        (key = ZFSet.pair (natCode m) (natCode n)) := by
  have hdecoded :=
    (textbookEKeyDecode_exists_iff_mem_textbookEDomain key).mpr hkey
  cases hdecoded with
  | intro m hdecodedN =>
    cases hdecodedN with
    | intro n hdecode =>
      exact Exists.intro m (Exists.intro n
        (And.intro hdecode
          ((textbookEKeyDecode_eq_some_iff key m n).mp hdecode)))

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEKeyDecode


