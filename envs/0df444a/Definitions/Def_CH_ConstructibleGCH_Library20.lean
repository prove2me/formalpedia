-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library20
-- name    : CH_ConstructibleGCH_Library20
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T08:10:29.498061+00:00
-- url     : https://prove2.me/theorems/eb20471e-d480-41b1-a01c-c9266ed6338a
-- title:
--   Internal collapse and canonical witness selection
-- statement:
--   This library provides the data for internalizing a Mostowski collapse, absorption by an infinite internal cardinal, uniform families indexed by omega, and canonical Skolem selection. It also supplies coded finite-syntax and formula-defined-set interfaces used by those constructions.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/GeneralCollapseInternalization.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalInfiniteCardinalAbsorption.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalStageInjectionFamily.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/ParametricUniformOmegaFamily.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/ParametricUniformOmegaSelector.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FormulaDefinedSet.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryClosureConstructible.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalSkolemSelection.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CodedSatisfaction.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library19
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_GeneralCollapseInternalization -/
section GCHSource_Work_CUGCH_GeneralCollapseInternalization
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Internalizing the collapse of a condensation hull

For a constructible elementary hull, Condensation first identifies the
external Mostowski-collapse range with an actual constructible level.  This
file then constructs the collapse graph in `L` without assuming a
`CollapseFormulaSpec`.

The graph is the union of all constructible partial collapse graphs contained
in `domain x range`.  A partial graph is downward closed and satisfies the
usual local recursion equation.  Well-founded induction shows that all of
its values are the external Mostowski-collapse values.  The same induction
then extends the union at every point, proving that it is the full collapse
graph.
-/

section

universe u

namespace Constructible

namespace Model

open Constructible.ContinuumFormula

local notation "LMem" => lCarrierMem

/-! ## Partial collapse graphs -/

/--
A downward-closed partial solution of the Mostowski recursion on `domain`,
with all outputs in `target`.

The recursion clause is exactly
`y = { value(z) | z in x and z in domain }` whenever `(x,y)` is in `graph`.
Functionality is not an extra field: well-founded induction derives it from
this recursion equation.
-/
structure IsPartialCollapseGraph
    (graph domain target : LCarrier.{u}) : Prop where
  graphBetween : IsGraphBetween LMem graph domain target
  predecessor : forall x y : LCarrier.{u},
    GraphValue LMem graph x y ->
      forall z : LCarrier.{u}, z.1 ∈ x.1 -> z.1 ∈ domain.1 ->
        exists value : LCarrier.{u},
          value.1 ∈ target.1 /\ GraphValue LMem graph z value
  recursion : forall x y : LCarrier.{u},
    GraphValue LMem graph x y ->
      forall value : LCarrier.{u},
        value.1 ∈ y.1 <->
          exists z : LCarrier.{u},
            z.1 ∈ x.1 /\ z.1 ∈ domain.1 /\
              GraphValue LMem graph z value

/-- Layout `[domain, target, graph]` for a partial collapse graph. -/
def partialCollapseGraphFormula : FOFormula 3 :=
  .conj (graphBetweenAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    (FOFormula.boundedAll (0 : Fin 3)
      (FOFormula.boundedAll (1 : Fin 4)
        (FOFormula.imp
          (graphValueAt (2 : Fin 5) (3 : Fin 5) (4 : Fin 5))
          (.conj
            (FOFormula.boundedAll (3 : Fin 5)
              (FOFormula.imp
                (.mem (5 : Fin 6) (0 : Fin 6))
                (FOFormula.boundedEx (1 : Fin 6)
                  (graphValueAt
                    (2 : Fin 7) (5 : Fin 7) (6 : Fin 7)))))
            (FOFormula.all
              (FOFormula.biimp
                (.mem (5 : Fin 6) (4 : Fin 6))
                (FOFormula.boundedEx (3 : Fin 6)
                  (.conj
                    (.mem (6 : Fin 7) (0 : Fin 7))
                    (graphValueAt
                      (2 : Fin 7) (6 : Fin 7) (5 : Fin 7))))))))))

 theorem partialCollapseGraph_assignment
    (domain target graph : LCarrier.{u}) :
    ![domain, target, graph] =
      snoc (snoc ![domain] target) graph := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_partialCollapseGraphFormula
    (domain target graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem partialCollapseGraphFormula
        ![domain, target, graph] <->
      IsPartialCollapseGraph graph domain target := by
  simp only [partialCollapseGraphFormula, FOFormula.Satisfies,
    satisfies_graphBetweenAt, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_imp, FOFormula.satisfies_boundedEx,
    FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    satisfies_graphValueAt]
  constructor
  · rintro ⟨hbetween, hlocal⟩
    refine ⟨hbetween, ?_, ?_⟩
    · intro x y hxy z hzx hzDomain
      have hbody := hlocal x
        (hbetween.graphValue_mem_lCarrier hxy).1 y
        (hbetween.graphValue_mem_lCarrier hxy).2 hxy
      rcases hbody.1 z hzx hzDomain with ⟨value, hvalue⟩
      exact ⟨value, hvalue⟩
    · intro x y hxy value
      have hbody := hlocal x
        (hbetween.graphValue_mem_lCarrier hxy).1 y
        (hbetween.graphValue_mem_lCarrier hxy).2 hxy
      exact hbody.2 value
  · intro h
    refine ⟨h.graphBetween, ?_⟩
    intro x hxDomain y hyTarget hxy
    refine ⟨?_, h.recursion x y hxy⟩
    intro z hzx hzDomain
    exact h.predecessor x y hxy z hzx hzDomain



/-! ## The set of all constructible partial collapse graphs -/

theorem IsPartialCollapseGraph.subset_product
    {graph domain target : LCarrier.{u}}
    (h : IsPartialCollapseGraph graph domain target) :
    graph.1 ⊆ (prodLCarrier domain target).1 := by
  intro pair hpair
  let pairL : LCarrier.{u} :=
    ⟨pair, mem_L_of_mem hpair graph.2⟩
  rcases h.graphBetween pairL hpair with
    ⟨x, hxDomain, y, hyTarget, hpairXY⟩
  have hpairEq :=
    (isKuratowskiPairOf_lCarrier_iff pairL x y).mp hpairXY
  change pair = ZFSet.pair x.1 y.1 at hpairEq
  change pair ∈ ZFSet.prod domain.1 target.1
  rw [hpairEq, ZFSet.pair_mem_prod]
  exact ⟨hxDomain, hyTarget⟩

theorem exists_partialCollapsePower
    (domain target : LCarrier.{u}) :
    exists power : LCarrier.{u}, forall graph : LCarrier.{u},
      graph.1 ∈ power.1 <->
        graph.1 ⊆ (prodLCarrier domain target).1 :=
  exists_powerSetLCarrier (prodLCarrier domain target)

/-- The internal powerset of `domain x target`. -/
noncomputable def partialCollapsePower
    (domain target : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_partialCollapsePower domain target)

@[simp]
theorem mem_partialCollapsePower_iff
    (domain target graph : LCarrier.{u}) :
    graph.1 ∈ (partialCollapsePower domain target).1 <->
      graph.1 ⊆ (prodLCarrier domain target).1 :=
  Classical.choose_spec (exists_partialCollapsePower domain target) graph

theorem exists_partialCollapseGraphFamily
    (domain target : LCarrier.{u}) :
    exists family : LCarrier.{u}, forall graph : LCarrier.{u},
      graph.1 ∈ family.1 <-> IsPartialCollapseGraph graph domain target := by
  rcases exists_separationLCarrier partialCollapseGraphFormula
      ![domain, target] (partialCollapsePower domain target) with
    ⟨family, hfamily⟩
  refine ⟨family, ?_⟩
  intro graph
  rw [hfamily graph, mem_partialCollapsePower_iff]
  have hassignment : snoc ![domain, target] graph =
      ![domain, target, graph] :=
    (partialCollapseGraph_assignment domain target graph).symm
  rw [hassignment, satisfies_partialCollapseGraphFormula]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h.subset_product, h⟩

/-- The actual constructible set of all constructible partial collapse graphs. -/
noncomputable def partialCollapseGraphFamily
    (domain target : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_partialCollapseGraphFamily domain target)

@[simp]
theorem mem_partialCollapseGraphFamily_iff
    (domain target graph : LCarrier.{u}) :
    graph.1 ∈ (partialCollapseGraphFamily domain target).1 <->
      IsPartialCollapseGraph graph domain target :=
  Classical.choose_spec
    (exists_partialCollapseGraphFamily domain target) graph

/-- The union of all constructible partial collapse graphs. -/
noncomputable def maximalPartialCollapseGraph
    (domain target : LCarrier.{u}) : LCarrier.{u} :=
  sUnionLCarrier (partialCollapseGraphFamily domain target)

@[simp]
theorem mem_maximalPartialCollapseGraph_iff
    (domain target : LCarrier.{u}) (pair : LCarrier.{u}) :
    pair.1 ∈ (maximalPartialCollapseGraph domain target).1 <->
      exists graph : LCarrier.{u},
        IsPartialCollapseGraph graph domain target /\ pair.1 ∈ graph.1 := by
  rw [maximalPartialCollapseGraph, mem_sUnionLCarrier_iff]
  apply exists_congr
  intro graph
  rw [mem_partialCollapseGraphFamily_iff]







/-! ## Extending a partial graph at one point -/

/-- Insert the Kuratowski pair `(x,y)` into a constructible graph. -/
def insertGraphValue
    (graph x y : LCarrier.{u}) : LCarrier.{u} :=
  unionLCarrier
    (pairLCarrier (orderedPairLCarrier x y) (orderedPairLCarrier x y))
    graph

@[simp]
theorem mem_insertGraphValue_iff
    (graph x y pair : LCarrier.{u}) :
    pair.1 ∈ (insertGraphValue graph x y).1 <->
      pair = orderedPairLCarrier x y \/ pair.1 ∈ graph.1 := by
  rw [insertGraphValue, mem_unionLCarrier_iff,
    mem_pairLCarrier_iff]
  simp only [or_self]

@[simp]
theorem graphValue_insertGraphValue_iff
    (graph x y a b : LCarrier.{u}) :
    GraphValue LMem (insertGraphValue graph x y) a b <->
      GraphValue LMem graph a b \/ (a = x /\ b = y) := by
  constructor
  · rintro ⟨pair, hpair, hpairAB⟩
    rcases (mem_insertGraphValue_iff graph x y pair).mp hpair with
      hnew | hold
    · right
      have hpairNew : pair = orderedPairLCarrier x y := hnew
      have hab := (isKuratowskiPairOf_lCarrier_iff pair a b).mp hpairAB
      rw [hpairNew] at hab
      have habRaw : ZFSet.pair x.1 y.1 = ZFSet.pair a.1 b.1 := by
        simpa only [orderedPairLCarrier_val] using hab
      have hcoordinates := ZFSet.pair_inj.mp habRaw
      exact ⟨Subtype.ext hcoordinates.1.symm,
        Subtype.ext hcoordinates.2.symm⟩
    · exact Or.inl ⟨pair, hold, hpairAB⟩
  · rintro (hold | hnew)
    · rcases hold with ⟨pair, hpair, hpairXY⟩
      exact ⟨pair,
        (mem_insertGraphValue_iff graph x y pair).mpr (Or.inr hpair),
        hpairXY⟩
    · rcases hnew with ⟨ha, hb⟩
      subst a
      subst b
      let pair := orderedPairLCarrier x y
      exact ⟨pair,
        (mem_insertGraphValue_iff graph x y pair).mpr
          (Or.inl rfl),
        (isKuratowskiPairOf_lCarrier_iff pair x y).mpr rfl⟩



/-! ## Totality of the maximal graph -/







end Model

namespace MostowskiCollapse

open Constructible.Model

/-! ## Condensation hulls -/









end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_GeneralCollapseInternalization


/- Source module: Solutions.Work_CUGCH_InternalInfiniteCardinalAbsorption -/
section GCHSource_Work_CUGCH_InternalInfiniteCardinalAbsorption
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Finite absorption by an internally infinite constructible set

This file carries out the standard Hilbert-hotel argument with actual graphs
belonging to `L`.  If `omega` is a subset of a constructible set `kappa`, the
definable map which shifts the natural numbers and fixes every other element
is an internal injection `kappa -> kappa` whose range omits the empty set.
Consequently an internal injection into `kappa` can be extended over one
fresh point.

No ambient function or cardinal comparison is used as an internal witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## The internal omega shift -/

/-- The semantic Hilbert-hotel shift: move members of `omega` to their von
Neumann successors and fix all other sets. -/
def OmegaShift (x y : LCarrier.{u}) : Prop :=
  (x.1 ∈ omegaLCarrier.1 ∧ y = successorLCarrier x) ∨
    (x.1 ∉ omegaLCarrier.1 ∧ y = x)

/-- Layout `(omega,x,y)`. -/
def omegaShiftFormula : FOFormula 3 :=
  .disj
    (.conj
      (.mem (1 : Fin 3) (0 : Fin 3))
      (Constructible.Model.successorSetAt (2 : Fin 3) (1 : Fin 3)))
    (.conj
      (.neg (.mem (1 : Fin 3) (0 : Fin 3)))
      (.eq (2 : Fin 3) (1 : Fin 3)))

@[simp]
theorem satisfies_omegaShiftFormula
    (omega x y : LCarrier.{u}) :
    FOFormula.Satisfies LMem omegaShiftFormula
        (snoc (snoc ![omega] x) y) ↔
      (x.1 ∈ omega.1 ∧ y = successorLCarrier x) ∨
        (x.1 ∉ omega.1 ∧ y = x) := by
  have hassignment : snoc (snoc ![omega] x) y = ![omega, x, y] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]
  simp [omegaShiftFormula]











/-! ## Composition and adjoining a fresh point -/

/-- The constructible set `domain union {point}`. -/
def adjoinLCarrier
    (domain point : LCarrier.{u}) : LCarrier.{u} :=
  unionLCarrier (singletonLCarrier point) domain

@[simp]
theorem mem_adjoinLCarrier_iff
    (domain point z : LCarrier.{u}) :
    z.1 ∈ (adjoinLCarrier domain point).1 ↔
      z = point ∨ z.1 ∈ domain.1 := by
  simp only [adjoinLCarrier, mem_unionLCarrier_iff,
    mem_singletonLCarrier_iff]

@[simp]
theorem adjoin_self_eq_successorLCarrier
    (domain : LCarrier.{u}) :
    adjoinLCarrier domain domain = successorLCarrier domain := by
  apply lCarrier_extensionality
  intro z
  simp only [mem_adjoinLCarrier_iff, successorLCarrier_val,
    ZFSet.mem_insert_iff, Subtype.ext_iff]











end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalInfiniteCardinalAbsorption


/- Source module: Solutions.Work_CUGCH_InternalStageInjectionFamily -/
section GCHSource_Work_CUGCH_InternalStageInjectionFamily
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Collecting internal stage injections by Replacement

`CanonicalLimitStageSelector` reduces the limit-stage cardinal argument to a
single constructible function graph which assigns an injection graph to every
earlier stage.  This file records the exact formula-level input needed to
construct that family by Replacement.

The remaining mathematical obligation is deliberately visible as
`InternalStageInjectionFormulaData`: one fixed first-order formula must have a
unique output at every ordinal below the limit, and that output must really be
an internal injection from the corresponding constructible stage.  An
external cardinal estimate, or an externally chosen family of maps, does not
inhabit this structure.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## A formula-functional Replacement graph and its range -/

/-- Replacement simultaneously supplies the actual function graph and its
actual range set.  The graph-value equivalence exposes precisely the formula
used to construct it. -/
theorem exists_replacementFunctionGraphAndRangeLCarrier
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u})
    (hfun : forall x : LCarrier.{u}, x.1 ∈ domain.1 ->
      ExistsUnique fun y : LCarrier.{u} =>
        FOFormula.Satisfies LMem phi (snoc (snoc params x) y)) :
    exists graph range : LCarrier.{u},
      IsFunctionGraph LMem graph domain range /\
        (forall y : LCarrier.{u}, y.1 ∈ range.1 <->
          exists x : LCarrier.{u}, x.1 ∈ domain.1 /\
            FOFormula.Satisfies LMem phi
              (snoc (snoc params x) y)) /\
        forall x y : LCarrier.{u},
          GraphValue LMem graph x y <->
            x.1 ∈ domain.1 /\
              FOFormula.Satisfies LMem phi
                (snoc (snoc params x) y) := by
  rcases Constructible.Model.exists_replacementLCarrier
      phi params domain hfun with
    ⟨range, hrange⟩
  rcases Constructible.Model.exists_replacementFunctionGraphLCarrier
      phi params domain hfun with
    ⟨graph, hgraph⟩
  have hvalue : forall x y : LCarrier.{u},
      GraphValue LMem graph x y <->
        x.1 ∈ domain.1 /\
          FOFormula.Satisfies LMem phi
            (snoc (snoc params x) y) := by
    intro x y
    constructor
    · rintro ⟨pair, hpairGraph, hpairXY⟩
      rcases (hgraph pair.1).mp hpairGraph with
        ⟨x', hx', y', hy', hpairEq⟩
      have hpairXYEq :=
        (isKuratowskiPairOf_lCarrier_iff pair x y).mp hpairXY
      have hcoordinates := ZFSet.pair_inj.mp
        (hpairEq.symm.trans hpairXYEq)
      have hxEq : x' = x := Subtype.ext hcoordinates.1
      have hyEq : y' = y := Subtype.ext hcoordinates.2
      subst x'
      subst y'
      exact ⟨hx', hy'⟩
    · rintro ⟨hx, hy⟩
      let pair := orderedPairLCarrier x y
      refine ⟨pair, ?_, ?_⟩
      · apply (hgraph pair.1).mpr
        exact ⟨x, hx, y, hy, rfl⟩
      · exact (isKuratowskiPairOf_lCarrier_iff pair x y).mpr rfl
  have hbetween : IsGraphBetween LMem graph domain range := by
    intro pair hpairGraph
    rcases (hgraph pair.1).mp hpairGraph with
      ⟨x, hx, y, hy, hpairEq⟩
    have hyRange : y.1 ∈ range.1 := (hrange y).mpr ⟨x, hx, hy⟩
    exact ⟨x, hx, y, hyRange,
      (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq⟩
  have htotal : forall x : LCarrier.{u}, x.1 ∈ domain.1 ->
      HasUniqueImage LMem graph x range := by
    intro x hx
    rcases hfun x hx with ⟨y, hy, hyUnique⟩
    have hyRange : y.1 ∈ range.1 := (hrange y).mpr ⟨x, hx, hy⟩
    refine ⟨y, hyRange, (hvalue x y).mpr ⟨hx, hy⟩, ?_⟩
    intro z _hzRange hxz
    exact hyUnique z ((hvalue x z).mp hxz).2
  exact ⟨graph, range, ⟨hbetween, htotal⟩, hrange, hvalue⟩

/-! ## The exact uniform-stage interface -/

/-- Formula-level data sufficient to collect a family of stage injections.

The output is required to be unique because Replacement must collect a
function, not merely choose independently from an external family of
existential witnesses. -/
structure InternalStageInjectionFormulaData
    (limit : Ordinal.{u}) (kappa : LCarrier.{u}) where
  arity : Nat
  formula : FOFormula (arity + 2)
  params : Tuple LCarrier.{u} arity
  existsUnique_output : forall index : LCarrier.{u},
    index.1 ∈ (ordinalLCarrier limit).1 ->
      ExistsUnique fun injection : LCarrier.{u} =>
        FOFormula.Satisfies LMem formula
          (snoc (snoc params index) injection)
  output_isInjection : forall ordinal : Ordinal.{u}, ordinal < limit ->
    forall injection : LCarrier.{u},
      FOFormula.Satisfies LMem formula
        (snoc (snoc params (ordinalLCarrier ordinal)) injection) ->
      IsInjection LMem injection (stageLCarrier ordinal) kappa



/-! ## Exact connection to the Hartogs stage bound -/



end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalStageInjectionFamily


/- Source module: Solutions.Work_CUGCH_ParametricUniformOmegaFamily -/
section GCHSource_Work_CUGCH_ParametricUniformOmegaFamily
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Parameterized internal omega families

This is the parameterized form of `UniformOmegaFamilySpec`.  A fixed tuple of
constructible parameters is passed to one object-language formula with layout
`[params,index,value]`.  Replacement over the actual internal omega produces
both the represented function graph and its range, and internal union then
collects all stages.
-/

section

universe u

namespace Constructible.Model

open Constructible.ContinuumFormula
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-- A fixed formula, with constructible parameters, uniformly defines an
omega-indexed family. -/
structure ParametricUniformOmegaFamilySpec (parameterCount : Nat) where
  params : Tuple LCarrier.{u} parameterCount
  formula : FOFormula (parameterCount + 2)
  value : Nat -> LCarrier.{u}
  realizes : forall (n : Nat) (y : LCarrier.{u}),
    FOFormula.Satisfies LMem formula
        (snoc (snoc params (natLCarrier n)) y) <->
      y = value n

/-- The actual Replacement graph and range of a parameterized omega family. -/
structure ParametricUniformOmegaFamilyData {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) where
  graph : LCarrier.{u}
  family : LCarrier.{u}
  isFunctionGraph : IsFunctionGraph LMem graph omegaLCarrier family
  mem_family_iff : forall y : LCarrier.{u},
    y.1 ∈ family.1 <-> exists n : Nat, y = spec.value n
  graphValue_iff : forall index y : LCarrier.{u},
    GraphValue LMem graph index y <->
      index.1 ∈ omegaLCarrier.1 /\
        FOFormula.Satisfies LMem spec.formula
          (snoc (snoc spec.params index) y)

/-- Replacement constructs the represented family data. -/
theorem exists_parametricUniformOmegaFamilyData
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    Nonempty (ParametricUniformOmegaFamilyData spec) := by
  have hfun : forall index : LCarrier.{u},
      index.1 ∈ omegaLCarrier.1 ->
        ExistsUnique fun y : LCarrier.{u} =>
          FOFormula.Satisfies LMem spec.formula
            (snoc (snoc spec.params index) y) := by
    intro index hindex
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with ⟨n, hindexCode⟩
    have hindexEq : index = natLCarrier n := Subtype.ext hindexCode
    subst index
    refine ⟨spec.value n, (spec.realizes n (spec.value n)).mpr rfl, ?_⟩
    intro other hother
    exact (spec.realizes n other).mp hother
  rcases exists_replacementFunctionGraphAndRangeLCarrier
      spec.formula spec.params omegaLCarrier hfun with
    ⟨graph, family, hgraph, hfamily, hvalue⟩
  refine ⟨{
    graph := graph
    family := family
    isFunctionGraph := hgraph
    mem_family_iff := ?_
    graphValue_iff := hvalue
  }⟩
  intro y
  rw [hfamily]
  constructor
  · rintro ⟨index, hindex, hformula⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode index.1).mp
        hindex with ⟨n, hindexCode⟩
    have hindexEq : index = natLCarrier n := Subtype.ext hindexCode
    subst index
    exact ⟨n, (spec.realizes n y).mp hformula⟩
  · rintro ⟨n, rfl⟩
    refine ⟨natLCarrier n, ?_, (spec.realizes n (spec.value n)).mpr rfl⟩
    change (natCode n : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode n)).mpr ⟨n, rfl⟩

/-- A canonical choice of the extensional Replacement data. -/
noncomputable def parametricUniformOmegaFamilyData
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    ParametricUniformOmegaFamilyData spec :=
  Classical.choice (exists_parametricUniformOmegaFamilyData spec)

/-- The actual internal union of the parameterized family. -/
noncomputable def parametricUniformOmegaUnion
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    LCarrier.{u} :=
  sUnionLCarrier (parametricUniformOmegaFamilyData spec).family

@[simp]
theorem mem_parametricUniformOmegaUnion_iff
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (z : LCarrier.{u}) :
    z.1 ∈ (parametricUniformOmegaUnion spec).1 <->
      exists n : Nat, z.1 ∈ (spec.value n).1 := by
  rw [parametricUniformOmegaUnion, mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨stage, hstageFamily, hz⟩
    rcases (parametricUniformOmegaFamilyData spec).mem_family_iff
        stage |>.mp hstageFamily with ⟨n, rfl⟩
    exact ⟨n, hz⟩
  · rintro ⟨n, hz⟩
    exact ⟨spec.value n,
      (parametricUniformOmegaFamilyData spec).mem_family_iff
        (spec.value n) |>.mpr ⟨n, rfl⟩,
      hz⟩



end

end Constructible.Model

end
end GCHSource_Work_CUGCH_ParametricUniformOmegaFamily


/- Source module: Solutions.Work_CUGCH_ParametricUniformOmegaSelector -/
section GCHSource_Work_CUGCH_ParametricUniformOmegaSelector
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The least-stage selector for a uniform omega family

For an internally represented omega-indexed family, this file constructs the
actual Kuratowski graph which sends an element of the union to the least
natural-number index of a family member containing it.  The graph is obtained
by Separation from one fixed first-order formula.  External minimization on
`Nat` is used only to prove totality and uniqueness of that internal graph.
-/

section

universe u

namespace Constructible.Model

open Constructible.ContinuumFormula
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-- In a larger context, some value of `familyGraph` at `index` contains
`element`. -/
def uniformOmegaFamilyContainsAt {n : Nat}
    (familyGraph index element : Fin n) : FOFormula n :=
  .ex <| .conj
    (graphValueAt familyGraph.castSucc index.castSucc (Fin.last n))
    (.mem element.castSucc (Fin.last n))

@[simp]
theorem satisfies_uniformOmegaFamilyContainsAt {n : Nat}
    (familyGraph index element : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (uniformOmegaFamilyContainsAt familyGraph index element) s <->
      exists fiber : LCarrier.{u},
        GraphValue LMem (s familyGraph) (s index) fiber /\
          (s element).1 ∈ fiber.1 := by
  simp only [uniformOmegaFamilyContainsAt, FOFormula.Satisfies,
    satisfies_graphValueAt, snoc_last, snoc_castSucc]

/-- Semantic content of the least-index formula. -/
def IsLeastUniformOmegaFamilyIndex
    (familyGraph omega element index : LCarrier.{u}) : Prop :=
  index.1 ∈ omega.1 /\
    (exists fiber : LCarrier.{u},
      GraphValue LMem familyGraph index fiber /\ element.1 ∈ fiber.1) /\
    forall earlier : LCarrier.{u}, earlier.1 ∈ index.1 ->
      Not (exists fiber : LCarrier.{u},
        GraphValue LMem familyGraph earlier fiber /\
          element.1 ∈ fiber.1)

/-- Layout `[familyGraph,omega,element,index]`. -/
def leastUniformOmegaFamilyIndexFormula : FOFormula 4 :=
  .conj
    (.mem (3 : Fin 4) (1 : Fin 4))
    (.conj
      (uniformOmegaFamilyContainsAt
        (0 : Fin 4) (3 : Fin 4) (2 : Fin 4))
      (FOFormula.boundedAll (3 : Fin 4)
        (.neg (uniformOmegaFamilyContainsAt
          (0 : Fin 5) (Fin.last 4) (2 : Fin 5)))))

@[simp]
theorem satisfies_leastUniformOmegaFamilyIndexFormula
    (familyGraph omega element index : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastUniformOmegaFamilyIndexFormula
        ![familyGraph, omega, element, index] <->
      IsLeastUniformOmegaFamilyIndex
        familyGraph omega element index := by
  simp only [leastUniformOmegaFamilyIndexFormula,
    FOFormula.Satisfies, FOFormula.satisfies_boundedAll,
    satisfies_uniformOmegaFamilyContainsAt,
    IsLeastUniformOmegaFamilyIndex, snoc_last]
  change
    (index.1 ∈ omega.1 /\
      (exists fiber : LCarrier.{u},
        GraphValue LMem familyGraph index fiber /\
          element.1 ∈ fiber.1) /\
      forall earlier : LCarrier.{u}, earlier.1 ∈ index.1 ->
        Not (exists fiber : LCarrier.{u},
          GraphValue LMem familyGraph earlier fiber /\
            element.1 ∈ fiber.1)) <-> _
  rfl

/-- A support containing both the union-domain and the natural-number
codomain of the selector. -/
def parametricUniformOmegaSelectorSupport
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    LCarrier.{u} :=
  unionLCarrier (parametricUniformOmegaUnion spec) omegaLCarrier

/-- The Separation-generated graph selecting the least containing index. -/
noncomputable def parametricUniformOmegaSelectorGraph
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount) :
    LCarrier.{u} :=
  canonicalDefinableRelationGraph
    leastUniformOmegaFamilyIndexFormula
    ![(parametricUniformOmegaFamilyData spec).graph, omegaLCarrier]
    (parametricUniformOmegaSelectorSupport spec)

 theorem least_index_assignment
    (familyGraph omega element index : LCarrier.{u}) :
    snoc (snoc ![familyGraph, omega] element) index =
      ![familyGraph, omega, element, index] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem graphValue_parametricUniformOmegaSelectorGraph_iff
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (element index : LCarrier.{u}) :
    GraphValue LMem (parametricUniformOmegaSelectorGraph spec)
        element index <->
      element.1 ∈ (parametricUniformOmegaUnion spec).1 /\
        IsLeastUniformOmegaFamilyIndex
          (parametricUniformOmegaFamilyData spec).graph
          omegaLCarrier element index := by
  rw [graphValue_lCarrier_iff_graphRel]
  simp only [parametricUniformOmegaSelectorGraph,
    graphRel_canonicalDefinableRelationGraph_iff]
  rw [least_index_assignment,
    satisfies_leastUniformOmegaFamilyIndexFormula]
  constructor
  · rintro ⟨_helementSupport, _hindexSupport, hleast⟩
    rcases hleast.2.1 with ⟨fiber, hfiberValue, helementFiber⟩
    have hfiberFamily :=
      (parametricUniformOmegaFamilyData spec).isFunctionGraph.1
        |>.graphValue_mem_lCarrier hfiberValue |>.2
    exact ⟨(mem_parametricUniformOmegaUnion_iff spec element).mpr <| by
      rcases (parametricUniformOmegaFamilyData spec).mem_family_iff fiber |>.mp
          hfiberFamily with ⟨n, rfl⟩
      exact ⟨n, helementFiber⟩, hleast⟩
  · rintro ⟨helementUnion, hleast⟩
    have helementSupport :
        element.1 ∈ (parametricUniformOmegaSelectorSupport spec).1 :=
      (mem_unionLCarrier_iff
        (parametricUniformOmegaUnion spec) omegaLCarrier element).mpr
          (Or.inl helementUnion)
    have hindexSupport :
        index.1 ∈ (parametricUniformOmegaSelectorSupport spec).1 :=
      (mem_unionLCarrier_iff
        (parametricUniformOmegaUnion spec) omegaLCarrier index).mpr
          (Or.inr hleast.1)
    exact ⟨helementSupport, hindexSupport, hleast⟩













end

end Constructible.Model

end
end GCHSource_Work_CUGCH_ParametricUniformOmegaSelector


/- Source module: Solutions.Work_CUGCH_FormulaDefinedSet -/
section GCHSource_Work_CUGCH_FormulaDefinedSet
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Formula-defined constructible sets

This file provides the generic bridge from external descriptions to internal
constructible sets.  If all members of a `ZFSet` are constructible and, on
the domain `L`, membership in that set is expressed by one fixed first-order
formula with constructible parameters, then the set itself belongs to `L`.

The restriction of the defining equivalence to `x ∈ L` is intentional:
`Model.SatisfiesIn L` restricts quantified variables, but it does not require
the free variables in an externally supplied assignment to belong to `L`.
-/

section

open Set

universe u

namespace Constructible

section ZFC

/--
A `ZFSet` whose members are constructible and whose membership relation is
first-order definable over `L`, with constructible parameters, belongs to `L`.

The defining equivalence is only needed for candidate elements in `L`.
-/
theorem mem_L_of_formula_definition_on_L {n : Nat} {s : ZFSet.{u}}
    (phi : FOFormula (n + 1)) (params : Tuple ZFSet.{u} n)
    (hs : ∀ x ∈ s, x ∈ L) (hparams : ∀ i, params i ∈ L)
    (hdef : ∀ x, x ∈ L →
      (x ∈ s ↔ Model.SatisfiesIn L phi (snoc params x))) :
    s ∈ L := by
  rcases exists_LStage_for_members hs with ⟨alpha, halpha⟩
  rcases exists_separation phi params hparams (LStageZF_mem_L alpha) with
    ⟨t, htL, ht⟩
  have hst : s = t := by
    apply ZFSet.ext
    intro x
    rw [ht x]
    constructor
    · intro hxs
      exact ⟨halpha x hxs, (hdef x (hs x hxs)).mp hxs⟩
    · rintro ⟨hxStage, hxFormula⟩
      have hxL : x ∈ L :=
        LStageZF_subset_constructibleUniverse alpha hxStage
      exact (hdef x hxL).mpr hxFormula
  rw [hst]
  exact htL



namespace Model

/--
Subtype-semantics version of `mem_L_of_formula_definition_on_L`.

The set being constructed is still a raw `ZFSet`; the parameters, candidate
elements, and defining satisfaction statement are presented directly in the
first-order structure `LCarrier`.
-/
theorem mem_L_of_formula_definition_lCarrier {n : Nat} {s : ZFSet.{u}}
    (phi : FOFormula (n + 1)) (params : Tuple LCarrier.{u} n)
    (hs : ∀ x ∈ s, x ∈ L)
    (hdef : ∀ x : LCarrier.{u},
      (x.1 ∈ s ↔
        FOFormula.Satisfies
          (fun z w : LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc params x))) :
    s ∈ L := by
  let rawParams : Tuple ZFSet.{u} n := fun i => (params i).1
  apply mem_L_of_formula_definition_on_L phi rawParams hs
    (fun i => (params i).2)
  intro x hxL
  let xL : LCarrier.{u} := ⟨x, hxL⟩
  have hbridge := satisfies_lCarrier_iff_satisfiesIn_L phi (snoc params xL)
  have hbridgeRaw :
      FOFormula.Satisfies
          (fun z w : LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc params xL) ↔
        SatisfiesIn L phi (snoc rawParams x) := by
    simpa only [subtypeVal_snoc] using hbridge
  exact (hdef xL).trans hbridgeRaw

end Model

end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_FormulaDefinedSet


/- Source module: Solutions.Work_CUGCH_RudimentaryClosureConstructible -/
section GCHSource_Work_CUGCH_RudimentaryClosureConstructible
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Constructibility of the full rudimentary closure

The existing postfix evaluator gives one fixed first-order formula for the
statement that a set is the output of an arbitrary finite rudimentary
program.  Consequently the collection of all such outputs is itself a
constructible set.  This packages `rudimentaryClosure U` as an element of `L`
when `U` belongs to `L`.

This result is needed by the full Skolem-hull construction: all formula
relations over a transitive `U` are members of this one internal index set.
-/

section

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-
The evaluator layout is
`[prefix13, omega, program, result]`.
Under the existential in `rudimentaryClosureMemberFormula` the available
layout is `[prefix13, omega, result, program]`; this renaming swaps the last
two coordinates.
-/
def rudimentaryClosureEvalRename : Fin 16 -> Fin 16 :=
  Fin.lastCases (14 : Fin 16)
    (fun i14 => Fin.lastCases (15 : Fin 16)
      (fun i13 => i13.castSucc.castSucc) i14)

/-- Membership in the full rudimentary closure, with fourteen evaluator
parameters followed by the candidate output. -/
def rudimentaryClosureMemberFormula : FOFormula 15 :=
  .ex (FOFormula.rename rudimentaryClosureEvalRename
    stackProgramEvalFormula)

/-- The evaluator seed and constants used by the membership formula. -/
def rudimentaryClosureParameters
    (U : Constructible.Model.LCarrier.{u}) :
    Tuple Constructible.Model.LCarrier.{u} 14 :=
  snoc (stackStepPrefixLAssignment U.1 U.2)
    ⟨Ordinal.omega0.toZFSet, Constructible.omega_mem_L⟩

 theorem comp_rudimentaryClosureEvalRename
    (U result code : Constructible.Model.LCarrier.{u}) :
    (fun i => snoc (snoc (rudimentaryClosureParameters U) result) code
      (rudimentaryClosureEvalRename i)) =
      stackProgramEvalCodeLAssignment
        U.1 code.1 result.1 U.2 code.2 result.2 := by
  funext i
  fin_cases i <;> rfl

/-- The fixed membership formula recognizes exactly the outputs in the
rudimentary closure. -/
@[simp]
theorem satisfies_rudimentaryClosureMemberFormula
    (U result : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem rudimentaryClosureMemberFormula
        (snoc (rudimentaryClosureParameters U) result) <->
      result.1 ∈ rudimentaryClosure U.1 := by
  simp only [rudimentaryClosureMemberFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  constructor
  · rintro ⟨code, heval⟩
    apply (exists_internalProgram_iff_mem_rudimentaryClosure U result).mp
    refine ⟨code, ?_⟩
    simpa only [comp_rudimentaryClosureEvalRename] using heval
  · intro hresult
    rcases (exists_internalProgram_iff_mem_rudimentaryClosure U result).mpr
        hresult with ⟨code, heval⟩
    refine ⟨code, ?_⟩
    simpa only [comp_rudimentaryClosureEvalRename] using heval

/-- The complete finite rudimentary closure of a constructible seed is a
constructible set, not merely an external collection of constructible
outputs. -/
theorem rudimentaryClosure_mem_L
    (U : Constructible.Model.LCarrier.{u}) :
    rudimentaryClosure U.1 ∈ Constructible.L := by
  apply Constructible.Model.mem_L_of_formula_definition_lCarrier
    rudimentaryClosureMemberFormula (rudimentaryClosureParameters U)
  · intro result hresult
    rcases mem_rudimentaryClosure_iff_exists_term.mp hresult with
      ⟨term, rfl⟩
    exact RudimentaryClosureTerm.eval_mem_L U.2 term
  · intro result
    exact (satisfies_rudimentaryClosureMemberFormula U result).symm

/-- The full closure packaged as an element of the membership structure on
`L`. -/
def rudimentaryClosureLCarrier
    (U : Constructible.Model.LCarrier.{u}) :
    Constructible.Model.LCarrier.{u} :=
  ⟨rudimentaryClosure U.1, rudimentaryClosure_mem_L U⟩

@[simp]
theorem rudimentaryClosureLCarrier_val
    (U : Constructible.Model.LCarrier.{u}) :
    (rudimentaryClosureLCarrier U).1 = rudimentaryClosure U.1 :=
  rfl

end

end Constructible.Godel.RudimentaryTerm

end
end GCHSource_Work_CUGCH_RudimentaryClosureConstructible


/- Source module: Solutions.Work_CUGCH_CanonicalSkolemSelection -/
section GCHSource_Work_CUGCH_CanonicalSkolemSelection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/







/-!
# Canonical internal Skolem selection

This file isolates the set-sized choice operation needed by a Skolem-hull
construction.  A constructible graph internally well-orders a bounding set.
For a constructible family of nonempty subsets of that bound, one fixed
first-order formula selects the least member of each fiber.  Full Separation
then produces the actual Kuratowski-pair graph in `L`, and Replacement produces
its range.

The final section turns a relation in `rudimentaryClosure U` and a finite
parameter tuple into its witness set.  The witness set is explicitly
intersected with `U`: an arbitrary member of `rudimentaryClosure U` need not
contain only well-formed tuple codes.
-/

section

open Set

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The fixed least-witness formula -/

/-- Under a new universally quantified variable, select `[order, z, y]` from
the context `[order, candidate, y, z]`. -/
def leastWitnessOrderRename : Fin 3 -> Fin 4 :=
  ![(0 : Fin 3).castSucc, Fin.last 3, (2 : Fin 3).castSucc]

 theorem comp_leastWitnessOrderRename {A : Type u}
    (order candidate y z : A) :
    (fun i => snoc ![order, candidate, y] z
      (leastWitnessOrderRename i)) =
      ![order, z, y] := by
  funext i
  fin_cases i <;> rfl

/-- With layout `[order, candidate, y]`, assert that `y` is the least member
of `candidate` in the relation represented by `order`. -/
def leastWitnessFormula : FOFormula 3 :=
  .conj
    (.mem (2 : Fin 3) (1 : Fin 3))
    (.all
      (FOFormula.imp
        (.mem (Fin.last 3) (1 : Fin 3).castSucc)
        (.neg (FOFormula.rename leastWitnessOrderRename graphRelFormula))))

@[simp]
theorem satisfies_leastWitnessFormula
    (order candidate y : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastWitnessFormula ![order, candidate, y] <->
      y.1 ∈ candidate.1 /\
        forall z : LCarrier.{u}, z.1 ∈ candidate.1 ->
          Not (GraphRel order z y) := by
  simp only [leastWitnessFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_rename, satisfies_graphRelFormula]
  constructor
  · rintro ⟨hy, hminimal⟩
    refine ⟨hy, ?_⟩
    intro z hz
    have hrename := comp_leastWitnessOrderRename order candidate y z
    have h0 := congrFun hrename 0
    have h1 := congrFun hrename 1
    have h2 := congrFun hrename 2
    simpa [h0, h1, h2] using hminimal z hz
  · rintro ⟨hy, hminimal⟩
    refine ⟨hy, ?_⟩
    intro z hz
    have hrename := comp_leastWitnessOrderRename order candidate y z
    have h0 := congrFun hrename 0
    have h1 := congrFun hrename 1
    have h2 := congrFun hrename 2
    simpa [h0, h1, h2] using hminimal z hz

/-- Select `[order, x, y]` from `[family, order, x, y]`. -/
def leastWitnessFamilyRename : Fin 3 -> Fin 4 :=
  ![1, 2, 3]

 theorem comp_leastWitnessFamilyRename {A : Type u}
    (family order x y : A) :
    (fun i => ![family, order, x, y] (leastWitnessFamilyRename i)) =
      ![order, x, y] := by
  funext i
  fin_cases i <;> rfl

/-- Layout `[family, order, x, y]`: `x` is in the family and `y` is its
`order`-least member. -/
def leastWitnessFamilyFormula : FOFormula 4 :=
  .conj
    (.mem (2 : Fin 4) (0 : Fin 4))
    (FOFormula.rename leastWitnessFamilyRename leastWitnessFormula)

@[simp]
theorem satisfies_leastWitnessFamilyFormula
    (family order x y : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastWitnessFamilyFormula
        ![family, order, x, y] <->
      x.1 ∈ family.1 /\ y.1 ∈ x.1 /\
        forall z : LCarrier.{u}, z.1 ∈ x.1 ->
          Not (GraphRel order z y) := by
  simp only [leastWitnessFamilyFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  rw [comp_leastWitnessFamilyRename,
    satisfies_leastWitnessFormula]
  change
    (x.1 ∈ family.1 /\ y.1 ∈ x.1 /\
      forall z : LCarrier.{u}, z.1 ∈ x.1 ->
        Not (GraphRel order z y)) <-> _
  rfl





/-! ## A constructible choice graph for a set-sized family -/











/-! ## Witness sets attached to rudimentary relation codes -/

/-- A relation indexed by `rudimentaryClosure U`, repackaged as a member of
the membership structure on `L`. -/
def rudimentaryRelationLCarrier
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1)) : LCarrier.{u} :=
  ⟨relation.1, mem_L_of_mem relation.2
    (Godel.RudimentaryTerm.rudimentaryClosure_mem_L U)⟩

/-- The code of a nonempty tuple of members of `U`, packaged in `L`. -/
def positiveTupleCodeLCarrier
    (U : LCarrier.{u}) {n : Nat}
    (params : Tuple (ZFCarrier U.1) (n + 1)) : LCarrier.{u} :=
  ⟨Godel.positiveTupleCode n (Delta0Formula.val params),
    mem_L_of_mem (Godel.positiveTupleCode_mem_rudimentaryClosure params)
      (Godel.RudimentaryTerm.rudimentaryClosure_mem_L U)⟩

/-- Intersection, packaged as an element of `L`. -/
def restrictedLCarrier (x bound : LCarrier.{u}) : LCarrier.{u} :=
  ⟨x.1 ∩ bound.1, inter_mem_L x.2 bound.2⟩

@[simp]
theorem mem_restrictedLCarrier_iff
    (x bound z : LCarrier.{u}) :
    z.1 ∈ (restrictedLCarrier x bound).1 <->
      z.1 ∈ x.1 /\ z.1 ∈ bound.1 := by
  simp [restrictedLCarrier]

/-- Nullary relations use their members directly as witnesses, restricted to
the intended structure `U`. -/
def nullaryRudimentaryWitnessSet
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1)) : LCarrier.{u} :=
  restrictedLCarrier (rudimentaryRelationLCarrier U relation) U

/-- For a nonempty parameter tuple, witnesses form the appropriate fiber of
the represented relation, again restricted to `U`. -/
def positiveRudimentaryWitnessSet
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) (n + 1)) : LCarrier.{u} :=
  restrictedLCarrier
    ⟨Godel.fiber relation.1
        (Godel.positiveTupleCode n (Delta0Formula.val params)),
      Godel.fiber_mem_L (rudimentaryRelationLCarrier U relation).2
        (positiveTupleCodeLCarrier U params).2⟩
    U

@[simp]
theorem mem_nullaryRudimentaryWitnessSet_iff
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    (x : ZFCarrier U.1) :
    x.1 ∈ (nullaryRudimentaryWitnessSet U relation).1 <->
      x.1 ∈ relation.1 := by
  change x.1 ∈ relation.1 ∩ U.1 <-> x.1 ∈ relation.1
  rw [ZFSet.mem_inter]
  simp only [x.2, and_true]

@[simp]
theorem mem_positiveRudimentaryWitnessSet_iff
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) (n + 1))
    (x : ZFCarrier U.1) :
    x.1 ∈ (positiveRudimentaryWitnessSet U relation params).1 <->
      Godel.positiveTupleCode (n + 1)
        (Delta0Formula.val (snoc params x)) ∈ relation.1 := by
  change
    x.1 ∈ Godel.fiber relation.1
      (Godel.positiveTupleCode n (Delta0Formula.val params)) ∩ U.1 <-> _
  rw [ZFSet.mem_inter, Godel.mem_fiber_iff]
  simp only [Godel.positiveTupleCode_snoc, Delta0Formula.val_snoc,
    x.2, and_true]

/-- Witness candidates for an arbitrary finite parameter tuple. -/
def rudimentaryWitnessSet
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) n) : LCarrier.{u} :=
  match n, params with
  | 0, _ => nullaryRudimentaryWitnessSet U relation
  | _n + 1, params => positiveRudimentaryWitnessSet U relation params

@[simp]
theorem mem_rudimentaryWitnessSet_iff
    (U : LCarrier.{u})
    (relation : ZFCarrier (Godel.rudimentaryClosure U.1))
    {n : Nat} (params : Tuple (ZFCarrier U.1) n)
    (x : ZFCarrier U.1) :
    x.1 ∈ (rudimentaryWitnessSet U relation params).1 <->
      Godel.positiveTupleCode n
        (Delta0Formula.val (snoc params x)) ∈ relation.1 := by
  cases n with
  | zero =>
      have hparams : params = (fun i : Fin 0 => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst params
      change
        x.1 ∈ (nullaryRudimentaryWitnessSet U relation).1 <->
          x.1 ∈ relation.1
      exact mem_nullaryRudimentaryWitnessSet_iff U relation x
  | succ n =>
      simp [rudimentaryWitnessSet]



/-! ## Specialization to the canonical stage order -/

/-- A canonical stage containing `U` and hence, by transitivity, every member
of `U`. -/
def canonicalWitnessStageOrdinal (U : LCarrier.{u}) : Ordinal.{u} :=
  Constructible.firstStage U.1 U.2

/-- The actual stage used to bound canonical witnesses. -/
def canonicalWitnessStage (U : LCarrier.{u}) : LCarrier.{u} :=
  stageLCarrier (canonicalWitnessStageOrdinal U)

/-- The internally represented canonical order on the witness stage. -/
def canonicalWitnessOrder (U : LCarrier.{u}) : LCarrier.{u} :=
  (stageHistoryData (canonicalWitnessStageOrdinal U)).relation

theorem seed_subset_canonicalWitnessStage (U : LCarrier.{u}) :
    U.1 ⊆ (canonicalWitnessStage U).1 := by
  intro x hx
  change x ∈ LStageZF (canonicalWitnessStageOrdinal U)
  exact (LStageZF_isTransitive (canonicalWitnessStageOrdinal U)).mem_trans
    hx (Constructible.mem_LStageZF_firstStage U.1 U.2)

/-- The chosen stage order is represented by an actual member of `L`. -/
theorem canonicalWitnessOrder_internallyWellOrders (U : LCarrier.{u}) :
    InternallyWellOrders (canonicalWitnessOrder U)
      (canonicalWitnessStage U) := by
  let ordinal := canonicalWitnessStageOrdinal U
  have hsystem := historyStageGraphs_coherent (Order.succ ordinal)
  simpa only [canonicalWitnessOrder, canonicalWitnessStage, ordinal,
    historyStageGraphs_last, lastStageIndex_val] using
      hsystem.wellOrders (lastStageIndex ordinal)











end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalSkolemSelection


/- Source module: Solutions.Work_CUGCH_CodedSatisfaction -/
section GCHSource_Work_CUGCH_CodedSatisfaction
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Set-sized coded satisfaction relations

For a fixed transitive set `U`, every positive-arity first-order formula has
an extension represented by one genuine `ZFSet` in `rudimentaryClosure U`.
Membership of a tuple code in that set is equivalent to satisfaction in the
set-sized membership structure on `U`.

This is deliberately not a truth predicate for the ambient universe and does
not assign truth to arbitrary formula codes. Instead, each external formula
is compiled to a finite rudimentary program, and the already fixed
`stackProgramEvalFormula` uniformly evaluates such programs. A
cardinal-controlled Skolem hull must enumerate the relations compiled from
the formula syntax and close under those relations formula by formula. It
must not close under every member of `rudimentaryClosure U`: unrestricted
nullary singleton relations would force the alleged hull to contain all of
`U`.
-/

section

universe u

namespace Constructible.Godel

noncomputable section

/-- The internal relation set representing satisfaction of `phi` over `U`. -/
def boundedSatisfactionRelation (U : ZFSet.{u}) (hU : U.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) : ZFSet.{u} :=
  (RelationRep.formulaRep U hU phi).set

/-- Every compiled satisfaction relation is one member of the full
rudimentary closure generated by `U`. -/
theorem boundedSatisfactionRelation_mem_rudimentaryClosure
    (U : ZFSet.{u}) (hU : U.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) :
    boundedSatisfactionRelation U hU phi ∈ rudimentaryClosure U :=
  (RelationRep.formulaRep U hU phi).set_mem



/-- Correctness of the compiled relation on every assignment from `U`. -/
@[simp]
theorem mem_boundedSatisfactionRelation_iff
    (U : ZFSet.{u}) (hU : U.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple (Constructible.ZFCarrier U) (n + 1)) :
    positiveTupleCode n (Constructible.Delta0Formula.val s) ∈
        boundedSatisfactionRelation U hU phi ↔
      FOFormula.Satisfies (Constructible.zfCarrierMem U) phi s :=
  (RelationRep.formulaRep U hU phi).correct s

/-- The compiled relation, packaged as an index in the one set containing all
finite rudimentary outputs. -/
def boundedSatisfactionIndex (U : ZFSet.{u}) (hU : U.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) :
    Constructible.ZFCarrier (rudimentaryClosure U) :=
  ⟨boundedSatisfactionRelation U hU phi,
    boundedSatisfactionRelation_mem_rudimentaryClosure U hU phi⟩

@[simp]
theorem boundedSatisfactionIndex_val
    (U : ZFSet.{u}) (hU : U.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) :
    (boundedSatisfactionIndex U hU phi).1 =
      boundedSatisfactionRelation U hU phi :=
  rfl



/-- If the carrier is constructible, so is every compiled satisfaction
relation. -/
theorem boundedSatisfactionRelation_mem_L
    {U : ZFSet.{u}} (hUL : U ∈ Constructible.L)
    (hU : U.IsTransitive) {n : Nat} (phi : FOFormula (n + 1)) :
    boundedSatisfactionRelation U hU phi ∈ Constructible.L := by
  rcases mem_rudimentaryClosure_iff_exists_term.mp
      (boundedSatisfactionRelation_mem_rudimentaryClosure U hU phi) with
    ⟨term, hterm⟩
  rw [← hterm]
  exact RudimentaryClosureTerm.eval_mem_L hUL term

/-- The compiled relation as an element of the membership structure on `L`. -/
def boundedSatisfactionRelationLCarrier
    (U : Constructible.Model.LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) :
    Constructible.Model.LCarrier.{u} :=
  ⟨boundedSatisfactionRelation U.1 hU phi,
    boundedSatisfactionRelation_mem_L U.2 hU phi⟩

@[simp]
theorem boundedSatisfactionRelationLCarrier_val
    (U : Constructible.Model.LCarrier.{u}) (hU : U.1.IsTransitive)
    {n : Nat} (phi : FOFormula (n + 1)) :
    (boundedSatisfactionRelationLCarrier U hU phi).1 =
      boundedSatisfactionRelation U.1 hU phi :=
  rfl



end

end Constructible.Godel

end
end GCHSource_Work_CUGCH_CodedSatisfaction


