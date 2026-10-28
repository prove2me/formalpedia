-- Prove2me | Definitions.Def_CH_ConstructibleGCH_FiniteIteration
-- name    : CH_ConstructibleGCH_FiniteIteration
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-25T22:31:07.480383+00:00
-- url     : https://prove2.me/theorems/f781d69c-d755-455c-aa27-02c22981a590
-- title:
--   Internal formulas for finite iteration
-- statement:
--   A fixed first-order step formula defines finite recursive iteration. This library supplies the coded histories, iteration graph and formula-realization interfaces needed to collect the iterates by Replacement inside L.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/UniformFiniteIterationFormula.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library26
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_UniformFiniteIterationFormula -/
section GCHSource_Work_CUGCH_UniformFiniteIterationFormula
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# A uniform first-order formula for finite iteration

Given one step formula with layout

`[stepParams, current, next]`,

this file constructs one first-order formula with layout

`[stepParams, initial, index, output]`.

The formula does not mention the external recursive function.  It asserts
the existence of the successor of `index` and of a genuine Kuratowski
function graph on that successor.  The graph has value `initial` at zero,
each consecutive pair of values satisfies the displayed step formula, and
its value at `index` is `output`.

When the step formula defines a single operation exactly, a canonical finite
graph is constructed as an actual member of `L`.  The history formula then
holds exactly when `output` is the corresponding external finite iterate.
This supplies the fixed formula required by
`ParametricUniformOmegaFamilySpec`.
-/

section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF
open Constructible.ContinuumFormula

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The fixed object-language formula -/

/-- Place a step formula at named coordinates of a larger context. -/
def finiteIterationStepFormulaAt {parameterCount contextSize : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Fin parameterCount -> Fin contextSize)
    (current next : Fin contextSize) : FOFormula contextSize :=
  FOFormula.rename
    (Fin.lastCases next (fun i => Fin.lastCases current params i))
    stepFormula

@[simp]
theorem satisfies_finiteIterationStepFormulaAt
    {parameterCount contextSize : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Fin parameterCount -> Fin contextSize)
    (current next : Fin contextSize)
    (s : Tuple LCarrier.{u} contextSize) :
    FOFormula.Satisfies LMem
        (finiteIterationStepFormulaAt stepFormula params current next) s <->
      FOFormula.Satisfies LMem stepFormula
        (snoc (snoc (fun i => s (params i)) (s current)) (s next)) := by
  rw [finiteIterationStepFormulaAt, FOFormula.satisfies_rename]
  have hassignment :
      (fun i =>
        s (Fin.lastCases next
          (fun j => Fin.lastCases current params j) i)) =
        snoc (snoc (fun i => s (params i)) (s current)) (s next) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassignment]

/--
At one history index, look up the current value and its successor value and
apply the displayed step formula.
-/
def finiteIterationHistoryStepFormulaAt
    {parameterCount contextSize : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Fin parameterCount -> Fin contextSize)
    (graph index : Fin contextSize) : FOFormula contextSize :=
  .ex <| .conj
    (Delta0Formula.successorFOAt (Fin.last contextSize) index.castSucc)
    (.ex <| .conj
      (graphValueFormulaAt graph.castSucc.castSucc
        index.castSucc.castSucc (Fin.last (contextSize + 1)))
      (.ex <| .conj
        (graphValueFormulaAt graph.castSucc.castSucc.castSucc
          (Fin.last contextSize).castSucc.castSucc
          (Fin.last (contextSize + 2)))
        (finiteIterationStepFormulaAt stepFormula
          (fun i => (params i).castSucc.castSucc.castSucc)
          (Fin.last (contextSize + 1)).castSucc
          (Fin.last (contextSize + 2)))))

/-- Exact semantic content of one finite-history transition. -/
def IsFiniteIterationHistoryStep
    {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Tuple LCarrier.{u} parameterCount)
    (graph index : LCarrier.{u}) : Prop :=
  exists successor : LCarrier.{u},
    successor.1 = insert index.1 index.1 /\
      exists current : LCarrier.{u},
        ZFSet.pair index.1 current.1 ∈ graph.1 /\
          exists next : LCarrier.{u},
            ZFSet.pair successor.1 next.1 ∈ graph.1 /\
              FOFormula.Satisfies LMem stepFormula
                (snoc (snoc params current) next)

@[simp]
theorem satisfies_finiteIterationHistoryStepFormulaAt
    {parameterCount contextSize : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Fin parameterCount -> Fin contextSize)
    (graph index : Fin contextSize)
    (s : Tuple LCarrier.{u} contextSize) :
    FOFormula.Satisfies LMem
        (finiteIterationHistoryStepFormulaAt
          stepFormula params graph index) s <->
      IsFiniteIterationHistoryStep stepFormula
        (fun i => s (params i)) (s graph) (s index) := by
  simp only [finiteIterationHistoryStepFormulaAt,
    IsFiniteIterationHistoryStep, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier,
    satisfies_graphValueFormulaAt_lCarrier_iff,
    satisfies_finiteIterationStepFormulaAt,
    snoc_last, snoc_castSucc]

/-- Raw function-graph semantics used by the complete history predicate. -/
def IsFiniteIterationFunctionGraph
    (graph domain : LCarrier.{u}) : Prop :=
  ((forall input : LCarrier.{u}, input.1 ∈ domain.1 ->
      exists value : LCarrier.{u},
        ZFSet.pair input.1 value.1 ∈ graph.1 /\
          forall other : LCarrier.{u},
            ZFSet.pair input.1 other.1 ∈ graph.1 ->
              other = value) /\
    forall pair : LCarrier.{u}, pair.1 ∈ graph.1 ->
      exists input : LCarrier.{u}, input.1 ∈ domain.1 /\
        exists value : LCarrier.{u},
          pair.1 = ZFSet.pair input.1 value.1)

/-- Exact semantic content of a complete finite iteration history. -/
def IsFiniteIterationHistory
    {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Tuple LCarrier.{u} parameterCount)
    (initial index output domain graph : LCarrier.{u}) : Prop :=
  domain.1 = insert index.1 index.1 /\
    IsFiniteIterationFunctionGraph graph domain /\
    ZFSet.pair index.1 output.1 ∈ graph.1 /\
    ZFSet.pair emptyLCarrier.1 initial.1 ∈ graph.1 /\
    forall i : LCarrier.{u}, i.1 ∈ index.1 ->
      IsFiniteIterationHistoryStep stepFormula params graph i

/--
The complete finite-history formula.  Its public layout is
`[stepParams, initial, index, output]`.
-/
def uniformFiniteIterationFormula {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2)) :
    FOFormula (parameterCount + 3) :=
  let params : Fin parameterCount -> Fin (parameterCount + 3) :=
    fun i => i.castSucc.castSucc.castSucc
  let initial : Fin (parameterCount + 3) :=
    (Fin.last parameterCount).castSucc.castSucc
  let index : Fin (parameterCount + 3) :=
    (Fin.last (parameterCount + 1)).castSucc
  let output : Fin (parameterCount + 3) :=
    Fin.last (parameterCount + 2)
  .ex <| .conj
    (Delta0Formula.successorFOAt
      (Fin.last (parameterCount + 3)) index.castSucc)
    (.ex <| .conj
      (functionGraphOnFormulaAt
        (Fin.last (parameterCount + 4))
        (Fin.last (parameterCount + 3)).castSucc)
      (.conj
        (graphValueFormulaAt
          (Fin.last (parameterCount + 4))
          index.castSucc.castSucc
          output.castSucc.castSucc)
        (.conj
          (.ex <| .conj
            (Constructible.Model.emptySetAt
              (Fin.last (parameterCount + 5)))
            (graphValueFormulaAt
              (Fin.last (parameterCount + 4)).castSucc
              (Fin.last (parameterCount + 5))
              initial.castSucc.castSucc.castSucc))
          (FOFormula.boundedAll index.castSucc.castSucc
            (finiteIterationHistoryStepFormulaAt stepFormula
              (fun i => (params i).castSucc.castSucc.castSucc)
              (Fin.last (parameterCount + 4)).castSucc
              (Fin.last (parameterCount + 5)))))))

@[simp]
theorem satisfies_uniformFiniteIterationFormula_iff
    {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Tuple LCarrier.{u} parameterCount)
    (initial index output : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (uniformFiniteIterationFormula stepFormula)
        (snoc (snoc (snoc params initial) index) output) <->
      exists domain graph : LCarrier.{u},
        IsFiniteIterationHistory stepFormula params
          initial index output domain graph := by
  simp only [uniformFiniteIterationFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_successorFOAt_lCarrier,
    satisfies_functionGraphOnFormulaAt_lCarrier_iff,
    satisfies_graphValueFormulaAt_lCarrier_iff,
    Constructible.Model.satisfies_emptySetAt,
    FOFormula.satisfies_boundedAll,
    satisfies_finiteIterationHistoryStepFormulaAt,
    IsFiniteIterationHistory, IsFiniteIterationFunctionGraph,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨domain, hdomain, graph, hfunction, houtput,
      ⟨zero, hzero, hbase⟩, hsteps⟩
    subst zero
    exact ⟨domain, graph, hdomain, hfunction, houtput, hbase, hsteps⟩
  · rintro ⟨domain, graph, hdomain, hfunction, houtput, hbase, hsteps⟩
    exact ⟨domain, hdomain, graph, hfunction, houtput,
      ⟨emptyLCarrier, rfl, hbase⟩, hsteps⟩

/-! ## The canonical finite graph -/

/-- External recursion used only in the correctness theorem. -/
def uniformFiniteIterate
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u}) : Nat -> LCarrier.{u}
  | 0 => initial
  | n + 1 => step (uniformFiniteIterate step initial n)

@[simp]
theorem uniformFiniteIterate_zero
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u}) :
    uniformFiniteIterate step initial 0 = initial :=
  rfl

@[simp]
theorem uniformFiniteIterate_succ
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u}) (n : Nat) :
    uniformFiniteIterate step initial (n + 1) =
      step (uniformFiniteIterate step initial n) :=
  rfl

/--
The genuine internal graph containing the values at all indices at most
`n`.  Every recursive value has type `LCarrier`, and `insertGraphValue`
preserves that invariant.
-/
noncomputable def uniformFiniteIterationGraph
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u}) : Nat -> LCarrier.{u}
  | 0 =>
      insertGraphValue emptyLCarrier (natLCarrier 0)
        (uniformFiniteIterate step initial 0)
  | n + 1 =>
      insertGraphValue
        (uniformFiniteIterationGraph step initial n)
        (natLCarrier (n + 1))
        (uniformFiniteIterate step initial (n + 1))

@[simp]
theorem mem_uniformFiniteIterationGraph_iff
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial pair : LCarrier.{u}) (n : Nat) :
    pair.1 ∈ (uniformFiniteIterationGraph step initial n).1 <->
      exists j : Nat, j <= n /\
        pair =
          orderedPairLCarrier (natLCarrier j)
            (uniformFiniteIterate step initial j) := by
  induction n with
  | zero =>
      rw [uniformFiniteIterationGraph,
        mem_insertGraphValue_iff]
      constructor
      · rintro (hnew | hold)
        · exact ⟨0, le_rfl, hnew⟩
        · exact (not_mem_emptyLCarrier pair hold).elim
      · rintro ⟨j, hj, rfl⟩
        have hjzero : j = 0 := Nat.eq_zero_of_le_zero hj
        subst j
        exact Or.inl rfl
  | succ n ih =>
      rw [uniformFiniteIterationGraph,
        mem_insertGraphValue_iff, ih]
      constructor
      · rintro (hnew | ⟨j, hj, hpair⟩)
        · exact ⟨n + 1, le_rfl, hnew⟩
        · exact ⟨j, hj.trans (Nat.le_succ n), hpair⟩
      · rintro ⟨j, hj, hpair⟩
        rcases Nat.eq_or_lt_of_le hj with rfl | hjlt
        · exact Or.inl hpair
        · exact Or.inr ⟨j, Nat.lt_succ_iff.mp hjlt, hpair⟩

theorem pair_mem_uniformFiniteIterationGraph
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u}) {j n : Nat} (hjn : j <= n) :
    ZFSet.pair (natCode j)
        (uniformFiniteIterate step initial j).1 ∈
      (uniformFiniteIterationGraph step initial n).1 := by
  let pair :=
    orderedPairLCarrier (natLCarrier j)
      (uniformFiniteIterate step initial j)
  change pair.1 ∈ (uniformFiniteIterationGraph step initial n).1
  exact (mem_uniformFiniteIterationGraph_iff
    step initial pair n).mpr ⟨j, hjn, rfl⟩

/-- The canonical graph is exactly a function on the successor of `n`. -/
theorem uniformFiniteIterationGraph_isFunctionGraph
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u}) (n : Nat) :
    IsFiniteIterationFunctionGraph
      (uniformFiniteIterationGraph step initial n)
      (natLCarrier (n + 1)) := by
  constructor
  · intro input hinput
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt
      input.1 (n + 1)).mp hinput with ⟨j, hj, hinputCode⟩
    have hjn : j <= n := Nat.lt_succ_iff.mp hj
    let value := uniformFiniteIterate step initial j
    refine ⟨value, ?_, ?_⟩
    · simpa only [hinputCode] using
        pair_mem_uniformFiniteIterationGraph
          step initial hjn
    · intro other hother
      let pair := orderedPairLCarrier input other
      have hpair :
          pair.1 ∈ (uniformFiniteIterationGraph step initial n).1 := by
        simpa only [pair, orderedPairLCarrier_val] using hother
      rcases (mem_uniformFiniteIterationGraph_iff
        step initial pair n).mp hpair with
        ⟨k, _hkn, hpairEq⟩
      have hcoordinates := ZFSet.pair_inj.mp
        (congrArg Subtype.val hpairEq)
      have hjk : j = k := by
        apply natCode_injective
        exact hinputCode.symm.trans hcoordinates.1
      subst k
      apply Subtype.ext
      exact hcoordinates.2
  · intro pair hpair
    rcases (mem_uniformFiniteIterationGraph_iff
      step initial pair n).mp hpair with
      ⟨j, hjn, rfl⟩
    refine ⟨natLCarrier j, ?_,
      uniformFiniteIterate step initial j, rfl⟩
    change natCode j ∈ (natCode (n + 1) : ZFSet.{u})
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
      (natCode j) (n + 1)).mpr
        ⟨j, Nat.lt_succ_iff.mpr hjn, rfl⟩

/-! ## Correctness and uniqueness of finite histories -/

/-- A step formula defines the displayed operation exactly on `LCarrier`. -/
def DefinesFiniteIterationStep
    {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Tuple LCarrier.{u} parameterCount)
    (step : LCarrier.{u} -> LCarrier.{u}) : Prop :=
  forall current next : LCarrier.{u},
    FOFormula.Satisfies LMem stepFormula
        (snoc (snoc params current) next) <->
      next = step current

theorem IsFiniteIterationFunctionGraph.value_unique
    {graph domain input left right : LCarrier.{u}}
    (hfunction : IsFiniteIterationFunctionGraph graph domain)
    (hinput : input.1 ∈ domain.1)
    (hleft : ZFSet.pair input.1 left.1 ∈ graph.1)
    (hright : ZFSet.pair input.1 right.1 ∈ graph.1) :
    left = right := by
  rcases hfunction.1 input hinput with
    ⟨value, _hvalue, hunique⟩
  exact (hunique left hleft).trans (hunique right hright).symm

/-- The canonical graph satisfies every clause of the history predicate. -/
theorem canonical_isFiniteIterationHistory
    {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Tuple LCarrier.{u} parameterCount)
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u})
    (hstep : DefinesFiniteIterationStep stepFormula params step)
    (n : Nat) :
    IsFiniteIterationHistory stepFormula params initial
      (natLCarrier n)
      (uniformFiniteIterate step initial n)
      (natLCarrier (n + 1))
      (uniformFiniteIterationGraph step initial n) := by
  refine ⟨?_, uniformFiniteIterationGraph_isFunctionGraph step initial n,
    ?_, ?_, ?_⟩
  · exact natCode_succ_eq_insert n
  · exact pair_mem_uniformFiniteIterationGraph
      step initial (le_refl n)
  · simpa only [uniformFiniteIterate_zero, natLCarrier_val,
      natCode, Nat.cast_zero, Ordinal.toZFSet_zero,
      emptyLCarrier] using
      (pair_mem_uniformFiniteIterationGraph
        step initial (Nat.zero_le n))
  · intro index hindex
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt
      index.1 n).mp hindex with ⟨j, hjn, hindexCode⟩
    let successor := natLCarrier (j + 1)
    let current := uniformFiniteIterate step initial j
    let next := uniformFiniteIterate step initial (j + 1)
    refine ⟨successor, ?_, current, ?_, next, ?_, ?_⟩
    · change natCode (j + 1) = insert index.1 index.1
      rw [hindexCode, natCode_succ_eq_insert]
    · simpa only [hindexCode] using
        pair_mem_uniformFiniteIterationGraph
          step initial (Nat.le_of_lt hjn)
    · change ZFSet.pair (natCode (j + 1)) next.1 ∈
        (uniformFiniteIterationGraph step initial n).1
      exact pair_mem_uniformFiniteIterationGraph
        step initial (Nat.succ_le_iff.mpr hjn)
    · apply (hstep current next).mpr
      rfl

/-- Every valid exact-step history contains the canonical value at each
index in its displayed finite domain. -/
theorem pair_mem_of_isFiniteIterationHistory
    {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Tuple LCarrier.{u} parameterCount)
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u})
    (hstep : DefinesFiniteIterationStep stepFormula params step)
    {n : Nat} {output domain graph : LCarrier.{u}}
    (history : IsFiniteIterationHistory stepFormula params initial
      (natLCarrier n) output domain graph) :
    forall {j : Nat}, j <= n ->
      ZFSet.pair (natCode j)
          (uniformFiniteIterate step initial j).1 ∈ graph.1 := by
  intro j hjn
  rcases history with
    ⟨hdomain, hfunction, _houtput, hbase, hsteps⟩
  have hindexDomain :
      forall {k : Nat}, k <= n ->
        (natLCarrier k).1 ∈ domain.1 := by
    intro k hkn
    rw [hdomain]
    change natCode k ∈ insert (natCode n) (natCode n)
    rw [← natCode_succ_eq_insert n]
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
      (natCode k) (n + 1)).mpr
        ⟨k, Nat.lt_succ_iff.mpr hkn, rfl⟩
  induction j with
  | zero =>
      simpa only [uniformFiniteIterate_zero, natLCarrier_val,
        natCode, Nat.cast_zero, Ordinal.toZFSet_zero,
        emptyLCarrier] using hbase
  | succ j ih =>
      have hjlt : j < n := by omega
      have hjle : j <= n := Nat.le_of_lt hjlt
      have hcurrentCanonical := ih hjle
      have hjIndex :
          (natLCarrier j).1 ∈ (natLCarrier n).1 := by
        exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
          (natCode j) n).mpr ⟨j, hjlt, rfl⟩
      rcases hsteps (natLCarrier j) hjIndex with
        ⟨successor, hsuccessor, current, hcurrent,
          next, hnext, hnextStep⟩
      have hcurrentEq :
          current = uniformFiniteIterate step initial j :=
        hfunction.value_unique (hindexDomain hjle)
          hcurrent hcurrentCanonical
      subst current
      have hnextEq :
          next =
            uniformFiniteIterate step initial (j + 1) := by
        have := (hstep
          (uniformFiniteIterate step initial j) next).mp hnextStep
        simpa only [uniformFiniteIterate_succ] using this
      subst next
      have hsuccessorEq :
          successor = natLCarrier (j + 1) := by
        apply Subtype.ext
        exact hsuccessor.trans (natCode_succ_eq_insert j).symm
      subst successor
      exact hnext

/-- Exact histories have the canonical final value. -/
theorem output_eq_uniformFiniteIterate_of_history
    {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Tuple LCarrier.{u} parameterCount)
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u})
    (hstep : DefinesFiniteIterationStep stepFormula params step)
    {n : Nat} {output domain graph : LCarrier.{u}}
    (history : IsFiniteIterationHistory stepFormula params initial
      (natLCarrier n) output domain graph) :
    output = uniformFiniteIterate step initial n := by
  have hcanonical :=
    pair_mem_of_isFiniteIterationHistory stepFormula params step initial
      hstep history (j := n) (le_refl n)
  have hdomain : (natLCarrier n).1 ∈ domain.1 := by
    rw [history.1]
    change natCode n ∈ insert (natCode n) (natCode n)
    rw [← natCode_succ_eq_insert n]
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
      (natCode n) (n + 1)).mpr
        ⟨n, Nat.lt_succ_self n, rfl⟩
  exact history.2.1.value_unique hdomain history.2.2.1 hcanonical



/-- The fixed history formula computes exactly the external finite iterate. -/
@[simp]
theorem satisfies_uniformFiniteIterationFormula_natCode_iff
    {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Tuple LCarrier.{u} parameterCount)
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial output : LCarrier.{u})
    (hstep : DefinesFiniteIterationStep stepFormula params step)
    (n : Nat) :
    FOFormula.Satisfies LMem
        (uniformFiniteIterationFormula stepFormula)
        (snoc
          (snoc (snoc params initial) (natLCarrier n))
          output) <->
      output = uniformFiniteIterate step initial n := by
  rw [satisfies_uniformFiniteIterationFormula_iff]
  constructor
  · rintro ⟨domain, graph, history⟩
    exact output_eq_uniformFiniteIterate_of_history
      stepFormula params step initial hstep history
  · intro houtput
    subst output
    exact ⟨natLCarrier (n + 1),
      uniformFiniteIterationGraph step initial n,
      canonical_isFiniteIterationHistory
        stepFormula params step initial hstep n⟩

/-! ## The Replacement-ready omega family -/

/--
Package exact finite iteration as a parameterized uniform omega family.
The parameters of the resulting specification are
`[stepParams, initial]`; its formula is the fixed history formula above.
-/
noncomputable def uniformFiniteIterationOmegaFamilySpec
    {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Tuple LCarrier.{u} parameterCount)
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u})
    (hstep : DefinesFiniteIterationStep stepFormula params step) :
    ParametricUniformOmegaFamilySpec.{u} (parameterCount + 1) where
  params := snoc params initial
  formula := uniformFiniteIterationFormula stepFormula
  value := uniformFiniteIterate step initial
  realizes := by
    intro n output
    exact satisfies_uniformFiniteIterationFormula_natCode_iff
      stepFormula params step initial output hstep n

@[simp]
theorem uniformFiniteIterationOmegaFamilySpec_value
    {parameterCount : Nat}
    (stepFormula : FOFormula (parameterCount + 2))
    (params : Tuple LCarrier.{u} parameterCount)
    (step : LCarrier.{u} -> LCarrier.{u})
    (initial : LCarrier.{u})
    (hstep : DefinesFiniteIterationStep stepFormula params step)
    (n : Nat) :
    (uniformFiniteIterationOmegaFamilySpec
      stepFormula params step initial hstep).value n =
        uniformFiniteIterate step initial n :=
  rfl

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_UniformFiniteIterationFormula


