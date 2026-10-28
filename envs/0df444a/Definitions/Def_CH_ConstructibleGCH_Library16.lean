-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library16
-- name    : CH_ConstructibleGCH_Library16
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:56:33.503955+00:00
-- url     : https://prove2.me/theorems/4e543b2d-ec18-4d53-baf5-3b8863ef390c
-- title:
--   Internal predecessor sets and recursion data
-- statement:
--   This library supplies the constructible predecessor-closure and local-recursion data needed to carry out the textbook E construction inside the membership model of L. In particular, recursive data are represented by constructible sets and graphs.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalPredecessorClosure.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalTextbookRecursion.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library15
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_InternalPredecessorClosure -/
section GCHSource_Work_CUGCH_InternalPredecessorClosure
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/







/-!
# Internal predecessor closure in transitive ZF models

This file internalizes the finite predecessor layers used in Section 6.1 of
Wang Fangting, *Axiomatic Set Theory*.

There is an essential hypothesis which must not be suppressed.  Ambient
set-likeness together with `PredecessorsClosedIn M A R` says that every
predecessor is an element of `M`; it does **not** say that the set of all
predecessors is itself an element of `M`.  We therefore explicitly assume
that `M` satisfies `setLikeRelationOnFormula`.  Its internal predecessor-set
witness is identified extensionally with `displayedPredecessors` by the two
restricted-absoluteness hypotheses.

At a successor layer, Replacement inside `M` collects the displayed
predecessor sets of the members of the previous layer, and Union inside `M`
then gives the next layer.  No externally indexed union is used to infer
model membership.
-/

section

open Set

universe u

namespace Constructible.Model

noncomputable section

open FiniteSequenceZF

/-! ## Internal displayed predecessor sets -/



/-! ## Replacement followed by Union at a successor layer -/





/-! ## A uniform first-order finite-history formula -/

 theorem internalPC_satisfiesIn_all_iff
    (M : Set ZFSet.{u}) {m : Nat} (formula : FOFormula (m + 1))
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.all formula) s <->
      forall z : ZFSet.{u}, z ∈ M ->
        SatisfiesIn M formula (snoc s z) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

 theorem internalPC_satisfiesIn_biimp_iff
    (M : Set ZFSet.{u}) {m : Nat} (left right : FOFormula m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.biimp left right) s <->
      (SatisfiesIn M left s <-> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, FOFormula.imp, FOFormula.disj, SatisfiesIn]
  tauto

 theorem internalPC_satisfiesIn_boundedAll_iff
    (M : Set ZFSet.{u}) {m : Nat} (set : Fin m)
    (formula : FOFormula (m + 1)) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.boundedAll set formula) s <->
      forall z : ZFSet.{u}, z ∈ M -> z ∈ s set ->
        SatisfiesIn M formula (snoc s z) := by
  classical
  simp only [FOFormula.boundedAll, FOFormula.boundedEx, SatisfiesIn]
  constructor
  · intro h z hzM hzSet
    by_contra hz
    exact h ⟨z, hzM, by simpa using hzSet, hz⟩
  · intro h hex
    rcases hex with ⟨z, hzM, hzSet, hz⟩
    exact hz (h z hzM (by simpa using hzSet))

 theorem internalPC_satisfiesIn_rename_iff
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

/-- Insert the already verified predecessor-set formula at named coordinates
of a larger context. -/
def predecessorSetFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (top predecessors : Fin m) : FOFormula m :=
  FOFormula.rename
    (Fin.lastCases predecessors
      (fun j => Fin.lastCases top params j))
    (predecessorSetFormula classFormula relationFormula)

@[simp]
theorem satisfiesIn_predecessorSetFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (top predecessors : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M
        (predecessorSetFormulaAt classFormula relationFormula
          params top predecessors) s <->
      forall z : ZFSet.{u}, z ∈ M ->
        (z ∈ s predecessors <->
          SatisfiesIn M classFormula
              (snoc (fun i => s (params i)) z) ∧
            SatisfiesIn M relationFormula
              (snoc (snoc (fun i => s (params i)) z) (s top))) := by
  rw [predecessorSetFormulaAt]
  rw [internalPC_satisfiesIn_rename_iff]
  have hassignment :
      (fun i => s
        (Fin.lastCases predecessors
          (fun j => Fin.lastCases top params j) i)) =
        snoc (snoc (fun i => s (params i)) (s top))
          (s predecessors) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment,
    satisfiesIn_predecessorSetFormula_iff]

/-- One layer is obtained from the preceding layer by taking the union of
the displayed predecessor sets. -/
def predecessorLayerStepFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (current next : Fin m) : FOFormula m :=
  FOFormula.all <| FOFormula.biimp
    (.mem (Fin.last m) next.castSucc)
    (.ex <| .conj
      (.mem (Fin.last (m + 1)) current.castSucc.castSucc)
      (.conj
        (classFormulaAt classFormula
          (fun i => (params i).castSucc.castSucc)
          (Fin.last m).castSucc)
        (relationFormulaAt relationFormula
          (fun i => (params i).castSucc.castSucc)
          (Fin.last m).castSucc (Fin.last (m + 1)))))

@[simp]
theorem satisfiesIn_predecessorLayerStepFormulaAt_iff
    (M : Set ZFSet.{u}) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (current next : Fin m)
    (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M
        (predecessorLayerStepFormulaAt classFormula relationFormula
          params current next) s <->
      forall z : ZFSet.{u}, z ∈ M ->
        (z ∈ s next <->
          exists y : ZFSet.{u}, y ∈ M ∧ y ∈ s current ∧
            SatisfiesIn M classFormula
              (snoc (fun i => s (params i)) z) ∧
            SatisfiesIn M relationFormula
              (snoc (snoc (fun i => s (params i)) z) y)) := by
  rw [predecessorLayerStepFormulaAt, internalPC_satisfiesIn_all_iff]
  constructor
  · intro h z hzM
    have hz := h z hzM
    rw [internalPC_satisfiesIn_biimp_iff] at hz
    simpa only [SatisfiesIn, satisfiesIn_classFormulaAt_iff,
      satisfiesIn_relationFormulaAt_iff, snoc_last, snoc_castSucc] using hz
  · intro h z hzM
    rw [internalPC_satisfiesIn_biimp_iff]
    simpa only [SatisfiesIn, satisfiesIn_classFormulaAt_iff,
      satisfiesIn_relationFormulaAt_iff, snoc_last, snoc_castSucc] using
      h z hzM

/-- The single-step clause used by a finite predecessor-layer history.

In a context containing `graph` and `index`, it quantifies the successor
index, the current value, and the next value. -/
def predecessorHistoryStepFormulaAt {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (graph index : Fin m) : FOFormula m :=
  .ex <| .conj
    (transitiveZFSuccessorAt (Fin.last m) index.castSucc)
    (.ex <| .conj
      (graphValueFormulaAt graph.castSucc.castSucc
        index.castSucc.castSucc (Fin.last (m + 1)))
      (.ex <| .conj
        (graphValueFormulaAt graph.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m + 2)))
        (predecessorLayerStepFormulaAt classFormula relationFormula
          (fun i => (params i).castSucc.castSucc.castSucc)
          (Fin.last (m + 1)).castSucc (Fin.last (m + 2)))))

@[simp]
theorem satisfiesIn_predecessorHistoryStepFormulaAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n -> Fin m) (graph index : Fin m)
    (s : Tuple ZFSet.{u} m) (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (predecessorHistoryStepFormulaAt classFormula relationFormula
          params graph index) s <->
      exists successor : ZFSet.{u}, successor ∈ (M : Set ZFSet.{u}) ∧
        successor = insert (s index) (s index) ∧
        exists current : ZFSet.{u}, current ∈ (M : Set ZFSet.{u}) ∧
          ZFSet.pair (s index) current ∈ s graph ∧
          exists next : ZFSet.{u}, next ∈ (M : Set ZFSet.{u}) ∧
            ZFSet.pair successor next ∈ s graph ∧
            forall z : ZFSet.{u}, z ∈ (M : Set ZFSet.{u}) ->
              (z ∈ next <->
                exists y : ZFSet.{u}, y ∈ (M : Set ZFSet.{u}) ∧
                  y ∈ current ∧
                  SatisfiesIn (M : Set ZFSet.{u}) classFormula
                    (snoc (fun i => s (params i)) z) ∧
                  SatisfiesIn (M : Set ZFSet.{u}) relationFormula
                    (snoc (snoc (fun i => s (params i)) z) y)) := by
  rw [predecessorHistoryStepFormulaAt]
  simp only [SatisfiesIn]
  constructor
  · rintro ⟨successor, hsuccessorM, hsuccessorFormula,
      current, hcurrentM, hcurrentFormula,
      next, hnextM, hnextFormula, hstep⟩
    have hsSuccessor : forall i, snoc s successor i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hsuccessorM
      · simpa using hs j
    have hsuccessor :=
      (satisfiesIn_transitiveZFSuccessorAt_iff hM
        (Fin.last m) index.castSucc (snoc s successor) hsSuccessor).mp
          hsuccessorFormula
    have hsCurrent : forall i, snoc (snoc s successor) current i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hcurrentM
      · simpa using hsSuccessor j
    have hcurrent :=
      (satisfiesIn_graphValueFormulaAt_iff hM
        graph.castSucc.castSucc index.castSucc.castSucc
        (Fin.last (m + 1)) (snoc (snoc s successor) current)
        hsCurrent).mp hcurrentFormula
    have hsNext : forall i,
        snoc (snoc (snoc s successor) current) next i ∈ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hnextM
      · simpa using hsCurrent j
    have hnext :=
      (satisfiesIn_graphValueFormulaAt_iff hM
        graph.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s successor) current) next) hsNext).mp
          hnextFormula
    have hstepRaw :=
      (satisfiesIn_predecessorLayerStepFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula relationFormula
        (fun i => (params i).castSucc.castSucc.castSucc)
        (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s successor) current) next)).mp hstep
    refine ⟨successor, hsuccessorM, ?_, current, hcurrentM, ?_,
      next, hnextM, ?_, ?_⟩
    · simpa only [snoc_last, snoc_castSucc] using hsuccessor
    · simpa only [snoc_last, snoc_castSucc] using hcurrent
    · simpa only [snoc_last, snoc_castSucc] using hnext
    · simpa only [snoc_last, snoc_castSucc] using hstepRaw
  · rintro ⟨successor, hsuccessorM, hsuccessor,
      current, hcurrentM, hcurrent,
      next, hnextM, hnext, hstep⟩
    refine ⟨successor, hsuccessorM, ?_, current, hcurrentM, ?_,
      next, hnextM, ?_, ?_⟩
    · have hsSuccessor : forall i, snoc s successor i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hsuccessorM
        · simpa using hs j
      apply (satisfiesIn_transitiveZFSuccessorAt_iff hM
        (Fin.last m) index.castSucc (snoc s successor) hsSuccessor).mpr
      simpa only [snoc_last, snoc_castSucc] using hsuccessor
    · have hsCurrent : forall i,
          snoc (snoc s successor) current i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hcurrentM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hsuccessorM
          · simpa using hs k
      apply (satisfiesIn_graphValueFormulaAt_iff hM
        graph.castSucc.castSucc index.castSucc.castSucc
        (Fin.last (m + 1)) (snoc (snoc s successor) current)
        hsCurrent).mpr
      simpa only [snoc_last, snoc_castSucc] using hcurrent
    · have hsNext : forall i,
          snoc (snoc (snoc s successor) current) next i ∈ M := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hnextM
        · refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hcurrentM
          · refine Fin.lastCases ?_ (fun l => ?_) k
            · simpa using hsuccessorM
            · simpa using hs l
      apply (satisfiesIn_graphValueFormulaAt_iff hM
        graph.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s successor) current) next) hsNext).mpr
      simpa only [snoc_last, snoc_castSucc] using hnext
    · apply (satisfiesIn_predecessorLayerStepFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula relationFormula
        (fun i => (params i).castSucc.castSucc.castSucc)
        (Fin.last (m + 1)).castSucc (Fin.last (m + 2))
        (snoc (snoc (snoc s successor) current) next)).mpr
      simpa only [snoc_last, snoc_castSucc] using hstep

/-! ## The canonical ambient finite history graph -/



/-- The graph containing `<j,p_j(x)>` for all `j ≤ k`.  The ordered-pair
orientation agrees with `functionGraphOnFormulaAt`: input first, value
second. -/
noncomputable def predecessorLayerHistoryGraph
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) :
    Nat -> ZFSet.{u}
  | 0 => {ZFSet.pair (natCode 0) (predecessorLayer A R hsetLike x 0)}
  | k + 1 =>
      insert
        (ZFSet.pair (natCode (k + 1))
          (predecessorLayer A R hsetLike x (k + 1)))
        (predecessorLayerHistoryGraph A R hsetLike x k)

@[simp]
theorem mem_predecessorLayerHistoryGraph_iff
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u})
    (k : Nat) (q : ZFSet.{u}) :
    q ∈ predecessorLayerHistoryGraph A R hsetLike x k <->
      exists j : Nat, j ≤ k ∧
        q = ZFSet.pair (natCode j)
          (predecessorLayer A R hsetLike x j) := by
  induction k with
  | zero =>
      simp [predecessorLayerHistoryGraph]
  | succ k ih =>
      rw [predecessorLayerHistoryGraph, ZFSet.mem_insert_iff, ih]
      constructor
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨k + 1, le_rfl, rfl⟩
        · exact ⟨j, hj.trans (Nat.le_succ k), rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · exact Or.inl rfl
        · exact Or.inr ⟨j, Nat.lt_succ_iff.mp hj, rfl⟩





/-! ## The complete finite-history formula -/

/-- Uniform formula with public layout `(params,top,index,output)`.

It asserts the existence of a function graph on `index ∪ {index}`, whose
zero value is the displayed predecessor set of `top`, whose successive values
satisfy `predecessorLayerStepFormulaAt`, and whose value at `index` is
`output`.  There is no reference to the ambient recursive function in the
formula. -/
def predecessorLayerHistoryFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula (n + 3) :=
  let params : Fin n -> Fin (n + 3) :=
    fun i => i.castSucc.castSucc.castSucc
  let top : Fin (n + 3) := (Fin.last n).castSucc.castSucc
  let index : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let output : Fin (n + 3) := Fin.last (n + 2)
  .ex <| .conj
    (transitiveZFSuccessorAt
      (Fin.last (n + 3)) index.castSucc)
    (.ex <| .conj
      (functionGraphOnFormulaAt
        (Fin.last (n + 4)) (Fin.last (n + 3)).castSucc)
      (.conj
        (graphValueFormulaAt
          (Fin.last (n + 4)) index.castSucc.castSucc
          output.castSucc.castSucc)
        (.conj
          (.ex <| .conj
            (transitiveZFEmptyAt (Fin.last (n + 5)))
            (.ex <| .conj
              (graphValueFormulaAt
                (Fin.last (n + 4)).castSucc.castSucc
                (Fin.last (n + 5)).castSucc (Fin.last (n + 6)))
              (predecessorSetFormulaAt classFormula relationFormula
                (fun i => (params i).castSucc.castSucc.castSucc.castSucc)
                top.castSucc.castSucc.castSucc.castSucc
                (Fin.last (n + 6)))))
          (FOFormula.boundedAll index.castSucc.castSucc
            (predecessorHistoryStepFormulaAt classFormula relationFormula
              (fun i => (params i).castSucc.castSucc.castSucc)
              (Fin.last (n + 4)).castSucc (Fin.last (n + 5)))))))

/-- Raw restricted-model meaning of one predecessor-layer step. -/
def IsPredecessorLayerStepIn (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (current next : ZFSet.{u}) : Prop :=
  forall z : ZFSet.{u}, z ∈ M ->
    (z ∈ next <->
      exists y : ZFSet.{u}, y ∈ M ∧ y ∈ current ∧
        SatisfiesIn M classFormula (snoc params z) ∧
        SatisfiesIn M relationFormula (snoc (snoc params z) y))

/-- Raw restricted-model meaning of a complete finite predecessor history.
This is a semantic abbreviation, not an additional mathematical assumption. -/
def IsPredecessorLayerHistoryIn (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (top index output domain graph : ZFSet.{u}) :
    Prop :=
  domain = insert index index ∧
  ((forall input : ZFSet.{u}, input ∈ M -> input ∈ domain ->
      exists value : ZFSet.{u}, value ∈ M ∧
        ZFSet.pair input value ∈ graph ∧
        forall other : ZFSet.{u}, other ∈ M ->
          ZFSet.pair input other ∈ graph -> other = value) ∧
    forall pair : ZFSet.{u}, pair ∈ M -> pair ∈ graph ->
      exists input : ZFSet.{u}, input ∈ M ∧ input ∈ domain ∧
        exists value : ZFSet.{u}, value ∈ M ∧
          pair = ZFSet.pair input value) ∧
  ZFSet.pair index output ∈ graph ∧
  (exists zero : ZFSet.{u}, zero ∈ M ∧ zero = (∅ : ZFSet.{u}) ∧
    exists base : ZFSet.{u}, base ∈ M ∧
      ZFSet.pair zero base ∈ graph ∧
      forall z : ZFSet.{u}, z ∈ M ->
        (z ∈ base <->
          SatisfiesIn M classFormula (snoc params z) ∧
          SatisfiesIn M relationFormula (snoc (snoc params z) top))) ∧
  forall i : ZFSet.{u}, i ∈ M -> i ∈ index ->
    exists successor : ZFSet.{u}, successor ∈ M ∧
      successor = insert i i ∧
      exists current : ZFSet.{u}, current ∈ M ∧
        ZFSet.pair i current ∈ graph ∧
        exists next : ZFSet.{u}, next ∈ M ∧
          ZFSet.pair successor next ∈ graph ∧
          IsPredecessorLayerStepIn M classFormula relationFormula
            params current next

 theorem internalPC_snoc_mem
    {M : Set ZFSet.{u}} {m : Nat} {s : Tuple ZFSet.{u} m}
    (hs : forall i, s i ∈ M) {x : ZFSet.{u}} (hx : x ∈ M) :
    forall i, snoc s x i ∈ M := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa using hs j

/-- Exact restricted-satisfaction semantics of
`predecessorLayerHistoryFormula`. -/
@[simp]
theorem satisfiesIn_predecessorLayerHistoryFormula_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple ZFSet.{u} n) (top index output : ZFSet.{u})
    (hparams : forall i, params i ∈ M)
    (htop : top ∈ M) (hindex : index ∈ M) (houtput : output ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (predecessorLayerHistoryFormula classFormula relationFormula)
        (snoc (snoc (snoc params top) index) output) <->
      exists domain : ZFSet.{u}, domain ∈ (M : Set ZFSet.{u}) ∧
        exists graph : ZFSet.{u}, graph ∈ (M : Set ZFSet.{u}) ∧
          IsPredecessorLayerHistoryIn (M : Set ZFSet.{u})
            classFormula relationFormula params top index output domain graph := by
  let s : Tuple ZFSet.{u} (n + 3) :=
    snoc (snoc (snoc params top) index) output
  have hs : forall i, s i ∈ (M : Set ZFSet.{u}) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [s] using houtput
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [s] using hindex
      · refine Fin.lastCases ?_ (fun l => ?_) k
        · simpa [s] using htop
        · simpa [s] using hparams l
  change SatisfiesIn (M : Set ZFSet.{u})
      (predecessorLayerHistoryFormula classFormula relationFormula) s <-> _
  rw [predecessorLayerHistoryFormula]
  simp only [SatisfiesIn]
  constructor
  · rintro ⟨domain, hdomainM, hdomainFormula,
      graph, hgraphM, hfunctionFormula, houtputFormula,
      hbaseFormula, hstepsFormula⟩
    have hsDomain := internalPC_snoc_mem hs hdomainM
    have hsGraph := internalPC_snoc_mem hsDomain hgraphM
    have hdomain :=
      (satisfiesIn_transitiveZFSuccessorAt_iff hM
        (Fin.last (n + 3)) (Fin.last (n + 1)).castSucc.castSucc
        (snoc s domain) hsDomain).mp hdomainFormula
    have hfunction :=
      (satisfiesIn_functionGraphOnFormulaAt_iff hM
        (Fin.last (n + 4)) (Fin.last (n + 3)).castSucc
        (snoc (snoc s domain) graph) hsGraph).mp hfunctionFormula
    have houtputGraph :=
      (satisfiesIn_graphValueFormulaAt_iff hM
        (Fin.last (n + 4))
        (Fin.last (n + 1)).castSucc.castSucc.castSucc
        (Fin.last (n + 2)).castSucc.castSucc
        (snoc (snoc s domain) graph) hsGraph).mp houtputFormula
    rcases hbaseFormula with
      ⟨zero, hzeroM, hzeroFormula, base, hbaseM,
        hbaseGraphFormula, hbaseSetFormula⟩
    have hsZero := internalPC_snoc_mem hsGraph hzeroM
    have hsBase := internalPC_snoc_mem hsZero hbaseM
    have hzero :=
      (satisfiesIn_transitiveZFEmptyAt_iff hM
        (Fin.last (n + 5)) (snoc (snoc (snoc s domain) graph) zero)
        hsZero).mp hzeroFormula
    have hbaseGraph :=
      (satisfiesIn_graphValueFormulaAt_iff hM
        (Fin.last (n + 4)).castSucc.castSucc
        (Fin.last (n + 5)).castSucc (Fin.last (n + 6))
        (snoc (snoc (snoc (snoc s domain) graph) zero) base)
        hsBase).mp hbaseGraphFormula
    have hbaseSet :=
      (satisfiesIn_predecessorSetFormulaAt_iff
        (M : Set ZFSet.{u}) classFormula relationFormula
        (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
        (Fin.last (n + 6))
        (snoc (snoc (snoc (snoc s domain) graph) zero) base)).mp
          hbaseSetFormula
    have hsteps :=
      (internalPC_satisfiesIn_boundedAll_iff
        (M : Set ZFSet.{u})
        (Fin.last (n + 1)).castSucc.castSucc.castSucc
        (predecessorHistoryStepFormulaAt classFormula relationFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 4)).castSucc (Fin.last (n + 5)))
        (snoc (snoc s domain) graph)).mp hstepsFormula
    refine ⟨domain, hdomainM, graph, hgraphM, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [s, snoc_last, snoc_castSucc] using hdomain
    · simpa [s] using hfunction
    · simpa only [s, snoc_last, snoc_castSucc] using houtputGraph
    · refine ⟨zero, hzeroM, ?_, base, hbaseM, ?_, ?_⟩
      · simpa only [snoc_last, snoc_castSucc] using hzero
      · simpa only [snoc_last, snoc_castSucc] using hbaseGraph
      · simpa only [s, snoc_last, snoc_castSucc] using hbaseSet
    · intro i hiM hiIndex
      have hstepFormula := hsteps i hiM (by
        simpa only [s, snoc_last, snoc_castSucc] using hiIndex)
      have hsIndex := internalPC_snoc_mem hsGraph hiM
      have hstep :=
        (satisfiesIn_predecessorHistoryStepFormulaAt_iff hM
          classFormula relationFormula
          (fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 4)).castSucc (Fin.last (n + 5))
          (snoc (snoc (snoc s domain) graph) i) hsIndex).mp
            hstepFormula
      simpa only [IsPredecessorLayerStepIn, s,
        snoc_last, snoc_castSucc] using hstep
  · rintro ⟨domain, hdomainM, graph, hgraphM,
      hdomain, hfunction, houtputGraph, hbase, hsteps⟩
    have hsDomain := internalPC_snoc_mem hs hdomainM
    have hsGraph := internalPC_snoc_mem hsDomain hgraphM
    refine ⟨domain, hdomainM, ?_, graph, hgraphM, ?_, ?_, ?_, ?_⟩
    · apply (satisfiesIn_transitiveZFSuccessorAt_iff hM
        (Fin.last (n + 3)) (Fin.last (n + 1)).castSucc.castSucc
        (snoc s domain) hsDomain).mpr
      simpa only [s, snoc_last, snoc_castSucc] using hdomain
    · apply (satisfiesIn_functionGraphOnFormulaAt_iff hM
        (Fin.last (n + 4)) (Fin.last (n + 3)).castSucc
        (snoc (snoc s domain) graph) hsGraph).mpr
      simpa [s] using hfunction
    · apply (satisfiesIn_graphValueFormulaAt_iff hM
        (Fin.last (n + 4))
        (Fin.last (n + 1)).castSucc.castSucc.castSucc
        (Fin.last (n + 2)).castSucc.castSucc
        (snoc (snoc s domain) graph) hsGraph).mpr
      simpa only [s, snoc_last, snoc_castSucc] using houtputGraph
    · rcases hbase with
        ⟨zero, hzeroM, hzero, base, hbaseM, hbaseGraph, hbaseSet⟩
      have hsZero := internalPC_snoc_mem hsGraph hzeroM
      have hsBase := internalPC_snoc_mem hsZero hbaseM
      refine ⟨zero, hzeroM, ?_, base, hbaseM, ?_, ?_⟩
      · apply (satisfiesIn_transitiveZFEmptyAt_iff hM
          (Fin.last (n + 5))
          (snoc (snoc (snoc s domain) graph) zero) hsZero).mpr
        simpa only [snoc_last, snoc_castSucc] using hzero
      · apply (satisfiesIn_graphValueFormulaAt_iff hM
          (Fin.last (n + 4)).castSucc.castSucc
          (Fin.last (n + 5)).castSucc (Fin.last (n + 6))
          (snoc (snoc (snoc (snoc s domain) graph) zero) base)
          hsBase).mpr
        simpa only [snoc_last, snoc_castSucc] using hbaseGraph
      · apply (satisfiesIn_predecessorSetFormulaAt_iff
          (M : Set ZFSet.{u}) classFormula relationFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
          (Fin.last (n + 6))
          (snoc (snoc (snoc (snoc s domain) graph) zero) base)).mpr
        simpa only [s, snoc_last, snoc_castSucc] using hbaseSet
    · apply (internalPC_satisfiesIn_boundedAll_iff
        (M : Set ZFSet.{u})
        (Fin.last (n + 1)).castSucc.castSucc.castSucc
        (predecessorHistoryStepFormulaAt classFormula relationFormula
          (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 4)).castSucc (Fin.last (n + 5)))
        (snoc (snoc s domain) graph)).mpr
      intro i hiM hiIndex
      have hsIndex := internalPC_snoc_mem hsGraph hiM
      apply (satisfiesIn_predecessorHistoryStepFormulaAt_iff hM
        classFormula relationFormula
        (fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last (n + 4)).castSucc (Fin.last (n + 5))
        (snoc (snoc (snoc s domain) graph) i) hsIndex).mpr
      have hstep := hsteps i hiM (by
        simpa only [s, snoc_last, snoc_castSucc] using hiIndex)
      simpa only [IsPredecessorLayerStepIn, s,
        snoc_last, snoc_castSucc] using hstep

/-! ## Uniqueness of finite histories -/









/-! ## Existence and exactness of canonical finite histories -/





/-! ## Replacement over standard omega -/







end

end Constructible.Model

end
end GCHSource_Work_CUGCH_InternalPredecessorClosure


/- Source module: Solutions.Work_CUGCH_InternalTextbookRecursion -/
section GCHSource_Work_CUGCH_InternalTextbookRecursion
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/







/-!
# Internal textbook recursion in a transitive ZF model

This file supplies the model-internal builder required in Section 6.2,
Theorem 2 of Wang Fangting, *Axiomatic Set Theory*.

The first part is the semantic bridge needed before Replacement may be used:
a model-internal graph satisfying `localSolutionFormula` is decoded into an
actual `TextbookLocalSolution`, and two such graphs are proved equal.  Thus
the functionality premise for Replacement is a theorem about the formula's
exact semantics, rather than an assumption hidden behind notation.
-/

section

open Set

universe u

namespace Constructible.Model

noncomputable section

/-! ## Absoluteness of the recursion functional at fixed parameters -/









/-! ## The model-relative well-foundedness consequence -/



/-! ## Internal graph lemmas -/











/-! ## Decoding the formula into an actual local solution -/





/-! ## The model-internal page-108 local construction -/

/-- At `(params,x)`, assert that there is no model-internal graph satisfying
the local-solution formula.  This is the formula used by Separation to form
the internal bad set in the recursion-existence proof. -/
def noLocalSolutionFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3)) : FOFormula (n + 1) :=
  .neg (.ex (localSolutionFormula
    classFormula relationFormula stepFormula))

@[simp]
theorem satisfiesIn_noLocalSolutionFormula_iff
    (M : Set ZFSet.{u}) {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (stepFormula : FOFormula (n + 3))
    (params : Tuple ZFSet.{u} n) (x : ZFSet.{u}) :
    SatisfiesIn M
        (noLocalSolutionFormula classFormula relationFormula stepFormula)
        (snoc params x) <->
      Not (exists graph : ZFSet.{u}, graph ∈ M ∧
        SatisfiesIn M
          (localSolutionFormula classFormula relationFormula stepFormula)
          (snoc (snoc params x) graph)) := by
  rfl





/-! ## The formula-represented global model solution -/





/-! ## The completed fixed-parameter absoluteness theorem -/







/-! ## Standard parameter-free public interface -/



end

end Constructible.Model

end
end GCHSource_Work_CUGCH_InternalTextbookRecursion


