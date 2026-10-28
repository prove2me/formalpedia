-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library06
-- name    : CH_ConstructibleGCH_Library06
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:21:54.456261+00:00
-- url     : https://prove2.me/theorems/4ab8a36f-6d1b-4dc3-8e1d-d024f557d9b7
-- title:
--   Internal cardinal representatives and order types
-- statement:
--   An internal cardinal representative of a constructible set is an internally well-ordered cardinal equipped with an internal bijection to the set. This library supplies canonical order-type, predecessor and recursion interfaces used to construct such representatives.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalCardinalRepresentatives.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalCardinalRepresentativeInterface.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalOrderTypeCanonical.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalOrderTypePredecessor.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalOrderTypeUniqueness.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalOrderTypeReplacement.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalOrderTypeStep.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalOrderTypeInduction.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalOrderTypeWitnessConstruction.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library05
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_InternalCardinalRepresentatives -/
section GCHSource_Work_CUGCH_InternalCardinalRepresentatives
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Internal cardinal representatives

This file constructs the order-type interface needed to turn the internally
represented well-order of a constructible set into an internally represented
bijection with an ordinal.  Every graph appearing in the semantic statements
is an element of `L`; an ambient Lean equivalence is not used as an internal
bijection witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## Semantic order-type predicates -/

/-- `predecessors` consists exactly of the members of `domain` below `point`
in the relation represented by `relation`. -/
def IsPredecessorSetOf {A : Type u} (E : A -> A -> Prop)
    (predecessors relation domain point : A) : Prop :=
  forall z : A, E z predecessors <->
    E z domain /\ GraphValue E relation z point

/-- A set-coded bijection which also preserves and reflects the represented
order. -/
def IsOrderIsomorphism {A : Type u} (E : A -> A -> Prop)
    (graph relation domain ordinal : A) : Prop :=
  IsBijection E graph domain ordinal /\
    forall z w imageZ imageW : A,
      E z domain -> E w domain ->
        GraphValue E graph z imageZ ->
          GraphValue E graph w imageW ->
            (GraphValue E relation z w <-> E imageZ imageW)

/-- `ordinal` is the order type of the strict initial segment below `point`.
Both the predecessor set and the order-isomorphism graph are internal sets. -/
def IsInitialSegmentOrderType {A : Type u} (E : A -> A -> Prop)
    (relation domain point ordinal : A) : Prop :=
  IsVonNeumannOrdinal E ordinal /\
    exists predecessors : A,
      IsPredecessorSetOf E predecessors relation domain point /\
        exists graph : A,
          IsOrderIsomorphism E graph relation predecessors ordinal

/-! ## Object-language formulas -/

/-- `predecessors` is the represented strict initial segment below `point`. -/
def predecessorSetAt {n : Nat}
    (predecessors relation domain point : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last n) predecessors.castSucc)
      (.conj
        (.mem (Fin.last n) domain.castSucc)
        (graphValueAt relation.castSucc (Fin.last n) point.castSucc)))

@[simp]
theorem satisfies_predecessorSetAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (predecessors relation domain point : Fin n)
    (s : Tuple A n) :
    FOFormula.Satisfies E
        (predecessorSetAt predecessors relation domain point) s <->
      IsPredecessorSetOf E (s predecessors) (s relation)
        (s domain) (s point) := by
  simp only [predecessorSetAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_graphValueAt, snoc_last, snoc_castSucc,
    IsPredecessorSetOf]

/-- A represented bijection preserves and reflects the source relation. -/
def orderPreservingAt {n : Nat}
    (graph relation domain : Fin n) : FOFormula n :=
  FOFormula.boundedAll domain
    (FOFormula.boundedAll domain.castSucc
      (FOFormula.all (FOFormula.all
        (FOFormula.imp
          (.conj
            (graphValueAt
              graph.castSucc.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc.castSucc
              (Fin.last (n + 2)).castSucc)
            (graphValueAt
              graph.castSucc.castSucc.castSucc.castSucc
              (Fin.last (n + 1)).castSucc.castSucc
              (Fin.last (n + 3))))
          (FOFormula.biimp
            (graphValueAt
              relation.castSucc.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc.castSucc
              (Fin.last (n + 1)).castSucc.castSucc)
            (.mem (Fin.last (n + 2)).castSucc
              (Fin.last (n + 3))))))))

@[simp]
theorem satisfies_orderPreservingAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (graph relation domain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (orderPreservingAt graph relation domain) s <->
      forall z w imageZ imageW : A,
        E z (s domain) -> E w (s domain) ->
          GraphValue E (s graph) z imageZ ->
            GraphValue E (s graph) w imageW ->
              (GraphValue E (s relation) z w <-> E imageZ imageW) := by
  simp only [orderPreservingAt, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_graphValueAt, snoc_last, snoc_castSucc]
  constructor
  · intro h z w imageZ imageW hz hw hzImage hwImage
    exact h z hz w hw imageZ imageW ⟨hzImage, hwImage⟩
  · intro h z hz w hw imageZ imageW hImages
    exact h z w imageZ imageW hz hw hImages.1 hImages.2

/-- `graph` is an internal order isomorphism from `domain` to `ordinal`. -/
def orderIsomorphismAt {n : Nat}
    (graph relation domain ordinal : Fin n) : FOFormula n :=
  .conj (bijectionAt graph domain ordinal)
    (orderPreservingAt graph relation domain)

@[simp]
theorem satisfies_orderIsomorphismAt {A : Type u}
    (E : A -> A -> Prop) {n : Nat}
    (graph relation domain ordinal : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E
        (orderIsomorphismAt graph relation domain ordinal) s <->
      IsOrderIsomorphism E (s graph) (s relation)
        (s domain) (s ordinal) := by
  simp only [orderIsomorphismAt, FOFormula.Satisfies,
    satisfies_bijectionAt, satisfies_orderPreservingAt,
    IsOrderIsomorphism]

/-- Layout `[relation, domain, point, ordinal]`: the last coordinate is the
order type of the strict initial segment below `point`. -/
def initialSegmentOrderTypeAt : FOFormula 4 :=
  .conj (isOrdinalAt (3 : Fin 4))
    (.ex
      (.conj
        (predecessorSetAt (Fin.last 4)
          (0 : Fin 4).castSucc (1 : Fin 4).castSucc
          (2 : Fin 4).castSucc)
        (.ex
          (orderIsomorphismAt (Fin.last 5)
            (0 : Fin 4).castSucc.castSucc
            (Fin.last 4).castSucc
            (3 : Fin 4).castSucc.castSucc))))

set_option autoImplicit true in
 theorem initialSegmentOrderType_assignment
    (relation domain point ordinal predecessors graph : A) :
    snoc (snoc ![relation, domain, point, ordinal] predecessors) graph =
      ![relation, domain, point, ordinal, predecessors, graph] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_initialSegmentOrderTypeAt {A : Type u}
    (E : A -> A -> Prop) (relation domain point ordinal : A) :
    FOFormula.Satisfies E initialSegmentOrderTypeAt
        ![relation, domain, point, ordinal] <->
      IsInitialSegmentOrderType E relation domain point ordinal := by
  simp only [initialSegmentOrderTypeAt, FOFormula.Satisfies,
    satisfies_isOrdinalAt]
  apply and_congr_right
  intro _hOrdinal
  apply exists_congr
  intro predecessors
  apply and_congr
  · exact satisfies_predecessorSetAt E
      (Fin.last 4) (0 : Fin 4).castSucc
        (1 : Fin 4).castSucc (2 : Fin 4).castSucc
      (snoc ![relation, domain, point, ordinal] predecessors)
  · apply exists_congr
    intro graph
    rw [initialSegmentOrderType_assignment]
    exact satisfies_orderIsomorphismAt E
      (Fin.last 5) (0 : Fin 4).castSucc.castSucc
      (Fin.last 4).castSucc (3 : Fin 4).castSucc.castSucc
      ![relation, domain, point, ordinal, predecessors, graph]

/-- Select `[relation, domain, point, ordinal]` from
`[relation, domain, bound, point, ordinal]`. -/
def beforeOrderTypeRename : Fin 4 -> Fin 5 :=
  ![0, 1, 3, 4]

 theorem comp_beforeOrderTypeRename {A : Type u}
    (relation domain bound point ordinal : A) :
    (fun i => ![relation, domain, bound, point, ordinal]
      (beforeOrderTypeRename i)) =
      ![relation, domain, point, ordinal] := by
  funext i
  fin_cases i <;> rfl

/-- Layout `[relation, domain, bound, point, ordinal]`: `point` is below
`bound` and `ordinal` is the represented order type at `point`. -/
def beforeOrderTypeRelation : FOFormula 5 :=
  .conj (.mem (3 : Fin 5) (1 : Fin 5))
    (.conj (graphValueAt (0 : Fin 5) (3 : Fin 5) (2 : Fin 5))
      (FOFormula.rename beforeOrderTypeRename initialSegmentOrderTypeAt))

@[simp]
theorem satisfies_beforeOrderTypeRelation
    (relation domain bound point ordinal : LCarrier.{u}) :
    FOFormula.Satisfies LMem beforeOrderTypeRelation
        ![relation, domain, bound, point, ordinal] <->
      point.1 ∈ domain.1 /\ GraphRel relation point bound /\
        IsInitialSegmentOrderType LMem relation domain point ordinal := by
  simp only [beforeOrderTypeRelation, FOFormula.Satisfies,
    satisfies_graphValueAt, FOFormula.satisfies_rename,
    comp_beforeOrderTypeRename, satisfies_initialSegmentOrderTypeAt]
  rw [graphValue_lCarrier_iff_graphRel]
  change
    (point.1 ∈ domain.1 /\ GraphRel relation point bound /\
      IsInitialSegmentOrderType LMem relation domain point ordinal) <-> _
  rfl

/-- Layout `[relation, domain, point, ordinal]`: restrict the order-type
relation to members of `domain`. -/
def memberOrderTypeRelation : FOFormula 4 :=
  .conj (.mem (2 : Fin 4) (1 : Fin 4)) initialSegmentOrderTypeAt

@[simp]
theorem satisfies_memberOrderTypeRelation
    (relation domain point ordinal : LCarrier.{u}) :
    FOFormula.Satisfies LMem memberOrderTypeRelation
        ![relation, domain, point, ordinal] <->
      point.1 ∈ domain.1 /\
        IsInitialSegmentOrderType LMem relation domain point ordinal := by
  simp only [memberOrderTypeRelation, FOFormula.Satisfies,
    satisfies_initialSegmentOrderTypeAt]
  change
    (point.1 ∈ domain.1 /\
      IsInitialSegmentOrderType LMem relation domain point ordinal) <-> _
  rfl

/-! ## Small carriers and represented bijections -/

/-- The actual equivalence induced by an internally represented bijection.
This is used only to reason about the represented graph; the internal witness
remains the graph supplied by `h`. -/
noncomputable def IsBijection.toEquiv
    {A : Type u} {E : A -> A -> Prop}
    {graph domain codomain : A}
    (h : IsBijection E graph domain codomain) :
    RelationCarrier E domain ≃ RelationCarrier E codomain := by
  let f := h.toIsInjection.toFun
  apply Equiv.ofBijective f
  constructor
  · exact h.toIsInjection.toFun_injective
  · intro y
    rcases h.2.2 y.1 y.2 with ⟨x, hx, hxy, _huniquePreimage⟩
    let xDomain : RelationCarrier E domain := ⟨x, hx⟩
    rcases h.2.1 x hx with
      ⟨value, hvalueCodomain, hxvalue, huniqueValue⟩
    have hchosenValue : (f xDomain).1 = value :=
      huniqueValue (f xDomain) (f xDomain).2
        (h.toIsInjection.toFun_graphValue xDomain)
    have hyValue : y.1 = value :=
      huniqueValue y.1 y.2 hxy
    refine ⟨xDomain, Subtype.ext ?_⟩
    exact hchosenValue.trans hyValue.symm



/-- The relation on the small carrier represented by an internal graph. -/
def rawGraphRel (relation domain : LCarrier.{u}) :
    ZFCarrier domain.1 -> ZFCarrier domain.1 -> Prop :=
  Constructible.Godel.RudimentaryTerm.generatorPairRel relation.1

/-- Package a member of a constructible set as an element of `LCarrier`. -/
def rawMemberLCarrier (domain : LCarrier.{u})
    (x : ZFCarrier domain.1) : LCarrier.{u} :=
  ⟨x.1, Constructible.mem_L_of_mem x.2 domain.2⟩

@[simp]
theorem rawMemberLCarrier_val (domain : LCarrier.{u})
    (x : ZFCarrier domain.1) :
    (rawMemberLCarrier domain x).1 = x.1 :=
  rfl

@[simp]
theorem rawGraphRel_iff_graphRel
    (relation domain : LCarrier.{u})
    (x y : ZFCarrier domain.1) :
    rawGraphRel relation domain x y <->
      GraphRel relation (rawMemberLCarrier domain x)
        (rawMemberLCarrier domain y) := by
  rfl

/-- An internally represented well-order is a well-order on the genuinely
small carrier of the underlying `ZFSet`. -/
theorem rawGraphRel_isWellOrder
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain) :
    IsWellOrder (ZFCarrier domain.1) (rawGraphRel relation domain) := by
  exact
    Constructible.Godel.RudimentaryTerm.generatorPairRel_isWellOrder_of_internal
      domain relation hwell

/-- A universe-small presentation of the members of a `ZFSet`. -/
abbrev SmallZFCarrier (x : ZFSet.{u}) :=
  Shrink.{u} (ZFCarrier x)

/-- Pull the represented relation back to the small presentation. -/
def smallGraphRel (relation domain : LCarrier.{u}) :
    SmallZFCarrier domain.1 -> SmallZFCarrier domain.1 -> Prop :=
  InvImage (rawGraphRel relation domain)
    (equivShrink (ZFCarrier domain.1)).symm

theorem smallGraphRel_isWellOrder
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain) :
    IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) := by
  letI : IsWellOrder (ZFCarrier domain.1)
      (rawGraphRel relation domain) :=
    rawGraphRel_isWellOrder relation domain hwell
  exact
    { wf := InvImage.wf (equivShrink (ZFCarrier domain.1)).symm
        (IsWellFounded.wf : WellFounded (rawGraphRel relation domain))
      trichotomous :=
        (InvImage.trichotomous
          (r := rawGraphRel relation domain)
          (equivShrink (ZFCarrier domain.1)).symm.injective).trichotomous }

/-! ## The canonical small carrier of a von Neumann ordinal -/

/-- Send an element of the canonical type of `alpha` to its von Neumann set
code in the ordinary (large) element subtype. -/
noncomputable def ordinalToRawZFCarrier (alpha : Ordinal.{u}) :
    alpha.ToType -> ZFCarrier alpha.toZFSet :=
  fun i => ⟨(i : Ordinal.{u}).toZFSet,
    Ordinal.toZFSet_mem_toZFSet_iff.mpr i.toOrd.2⟩

theorem ordinalToRawZFCarrier_injective (alpha : Ordinal.{u}) :
    Function.Injective (ordinalToRawZFCarrier alpha) := by
  intro i j hij
  have hord : (i : Ordinal.{u}) = (j : Ordinal.{u}) := by
    apply Ordinal.toZFSet_injective
    exact congrArg Subtype.val hij
  apply (Ordinal.ToType.mk : Set.Iio alpha ≃o alpha.ToType).symm.injective
  apply Subtype.ext
  exact hord

theorem ordinalToRawZFCarrier_surjective (alpha : Ordinal.{u}) :
    Function.Surjective (ordinalToRawZFCarrier alpha) := by
  intro z
  rcases Ordinal.mem_toZFSet_iff.mp z.2 with ⟨beta, hbeta, hvalue⟩
  let i : alpha.ToType := Ordinal.ToType.mk ⟨beta, hbeta⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  change (i : Ordinal.{u}).toZFSet = z.1
  have hi : (i : Ordinal.{u}) = beta := by
    exact congrArg Subtype.val
      ((Ordinal.ToType.mk : Set.Iio alpha ≃o alpha.ToType).symm_apply_apply
        ⟨beta, hbeta⟩)
  rw [hi]
  exact hvalue

/-- The same canonical map, now landing in the small carrier. -/
noncomputable def ordinalToSmallZFCarrier (alpha : Ordinal.{u}) :
    alpha.ToType -> SmallZFCarrier alpha.toZFSet :=
  fun i => equivShrink (ZFCarrier alpha.toZFSet)
    (ordinalToRawZFCarrier alpha i)

theorem ordinalToSmallZFCarrier_injective (alpha : Ordinal.{u}) :
    Function.Injective (ordinalToSmallZFCarrier alpha) :=
  (equivShrink (ZFCarrier alpha.toZFSet)).injective.comp
    (ordinalToRawZFCarrier_injective alpha)

theorem ordinalToSmallZFCarrier_surjective (alpha : Ordinal.{u}) :
    Function.Surjective (ordinalToSmallZFCarrier alpha) := by
  intro z
  let zRaw := (equivShrink (ZFCarrier alpha.toZFSet)).symm z
  rcases ordinalToRawZFCarrier_surjective alpha zRaw with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  change equivShrink (ZFCarrier alpha.toZFSet)
      (ordinalToRawZFCarrier alpha i) = z
  rw [hi]
  exact (equivShrink (ZFCarrier alpha.toZFSet)).apply_symm_apply z

/-- Membership pulled back to the small presentation of an ordinal. -/
def smallOrdinalMem (alpha : Ordinal.{u}) :
    SmallZFCarrier alpha.toZFSet ->
      SmallZFCarrier alpha.toZFSet -> Prop :=
  InvImage (fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1)
    (equivShrink (ZFCarrier alpha.toZFSet)).symm

instance smallOrdinalMem_isWellOrder (alpha : Ordinal.{u}) :
    IsWellOrder (SmallZFCarrier alpha.toZFSet)
      (smallOrdinalMem alpha) := by
  letI hraw : IsWellOrder (ZFCarrier alpha.toZFSet)
      (fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1) :=
    (ZFSet.isOrdinal_toZFSet alpha).isWellOrder
  change IsWellOrder _
    (InvImage (fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1)
      (equivShrink (ZFCarrier alpha.toZFSet)).symm)
  exact
    { wf := InvImage.wf
        (r := fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1)
        (equivShrink (ZFCarrier alpha.toZFSet)).symm
        (IsWellFounded.wf : WellFounded
          (fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1)),
      trichotomous :=
        (InvImage.trichotomous
          (r := fun x y : ZFCarrier alpha.toZFSet => x.1 ∈ y.1)
          (equivShrink (ZFCarrier alpha.toZFSet)).symm.injective).trichotomous }

noncomputable def ordinalToSmallZFCarrierEquiv (alpha : Ordinal.{u}) :
    alpha.ToType ≃ SmallZFCarrier alpha.toZFSet :=
  Equiv.ofBijective (ordinalToSmallZFCarrier alpha)
    ⟨ordinalToSmallZFCarrier_injective alpha,
      ordinalToSmallZFCarrier_surjective alpha⟩

@[simp]
theorem ordinalToSmallZFCarrierEquiv_apply
    (alpha : Ordinal.{u}) (i : alpha.ToType) :
    ordinalToSmallZFCarrierEquiv alpha i =
      ordinalToSmallZFCarrier alpha i := by
  rfl

/-- The small members of `alpha.toZFSet`, ordered by membership, have order
type exactly `alpha`. -/
noncomputable def ordinalToSmallZFCarrierRelIso (alpha : Ordinal.{u}) :
    ((fun i j : alpha.ToType => i < j) ≃r
      smallOrdinalMem alpha) where
  toEquiv := ordinalToSmallZFCarrierEquiv alpha
  map_rel_iff' {i j} := by
    rw [ordinalToSmallZFCarrierEquiv_apply,
      ordinalToSmallZFCarrierEquiv_apply]
    simp only [smallOrdinalMem, ordinalToSmallZFCarrier, InvImage,
      Equiv.symm_apply_apply, ordinalToRawZFCarrier]
    rw [Ordinal.toZFSet_mem_toZFSet_iff]
    change i.toOrd < j.toOrd <-> i < j
    exact (Ordinal.ToType.mk : Set.Iio alpha ≃o alpha.ToType).symm.lt_iff_lt

theorem type_smallZFCarrier_ordinal (alpha : Ordinal.{u}) :
    Ordinal.type (smallOrdinalMem alpha) =
      alpha := by
  letI : IsWellOrder alpha.ToType (fun i j => i < j) := inferInstance
  calc
    Ordinal.type (smallOrdinalMem alpha) =
        Ordinal.type (fun i j : alpha.ToType => i < j) :=
      (ordinalToSmallZFCarrierRelIso alpha).symm.ordinalType_congr
    _ = alpha := Ordinal.type_toType alpha

/-! ## From internal ordinal representatives to internal cardinals -/



/-- The ordinals internally equinumerous with `a`. -/
def internalOrdinalRepresentatives (a : LCarrier.{u}) : Set Ordinal.{u} :=
  {alpha | Equinumerous LMem a (ordinalLCarrier alpha)}



/-- The least ordinal internally equinumerous with `a`. -/
noncomputable def internalCardinalRepresentativeOrdinal
    (a : LCarrier.{u}) : Ordinal.{u} :=
  sInf (internalOrdinalRepresentatives a)







end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalCardinalRepresentatives


/- Source module: Solutions.Work_CUGCH_InternalCardinalRepresentativeInterface -/
section GCHSource_Work_CUGCH_InternalCardinalRepresentativeInterface
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The explicit order-type interface for internal cardinal representatives

`ModelsInternalWellOrdering` supplies a constructible graph for a well-order,
but it does not by itself supply the graph of the order-type map.  This file
records the exact missing witness.  Once an internal ordinal and a total,
single-valued, onto interpretation of `memberOrderTypeRelation` are supplied,
the existing Separation/graph theorem constructs the actual Kuratowski graph
in `L`.  No ambient equivalence is used as an internal witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## The missing order-type witness -/

/--
An internal witness that `ordinal` is the range of the order-type map for
`relation` on `domain`.  The formula is the already verified
`memberOrderTypeRelation`, with assignment `[relation, domain, point, ordinal]`.

The four semantic fields are deliberately explicit: proving them is the
genuine well-founded-recursion/Replacement step in the usual proof.
-/
structure InternalOrderTypeWitness
    (relation domain : LCarrier.{u}) where
  ordinal : LCarrier.{u}
  ordinal_spec : IsVonNeumannOrdinal LMem ordinal
  total : forall x : LCarrier.{u}, x.1 ∈ domain.1 ->
    exists y : LCarrier.{u},
      y.1 ∈ ordinal.1 /\
        FOFormula.Satisfies LMem memberOrderTypeRelation
          ![relation, domain, x, y]
  bounded : forall x y : LCarrier.{u}, x.1 ∈ domain.1 ->
    FOFormula.Satisfies LMem memberOrderTypeRelation
      ![relation, domain, x, y] ->
      y.1 ∈ ordinal.1
  unique : forall x y z : LCarrier.{u},
    x.1 ∈ domain.1 ->
      y.1 ∈ ordinal.1 ->
        z.1 ∈ ordinal.1 ->
          FOFormula.Satisfies LMem memberOrderTypeRelation
            ![relation, domain, x, y] ->
            FOFormula.Satisfies LMem memberOrderTypeRelation
              ![relation, domain, x, z] ->
              y = z
  injective : forall x z y : LCarrier.{u},
    x.1 ∈ domain.1 ->
      z.1 ∈ domain.1 ->
        y.1 ∈ ordinal.1 ->
          FOFormula.Satisfies LMem memberOrderTypeRelation
            ![relation, domain, x, y] ->
            FOFormula.Satisfies LMem memberOrderTypeRelation
              ![relation, domain, z, y] ->
              x = z
  onto : forall y : LCarrier.{u}, y.1 ∈ ordinal.1 ->
    exists x : LCarrier.{u},
      x.1 ∈ domain.1 /\
        FOFormula.Satisfies LMem memberOrderTypeRelation
          ![relation, domain, x, y]

/-! ## Internal graph and equinumerosity -/



/-! ## Reduction to the cardinal-representative interface -/



end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalCardinalRepresentativeInterface


/- Source module: Solutions.Work_CUGCH_InternalOrderTypeCanonical -/
section GCHSource_Work_CUGCH_InternalOrderTypeCanonical
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Canonical external order types for internally represented well-orders

This file identifies the canonical ordinal attached to each point of an
internally represented well-order.  The construction uses `Ordinal.typein`
only as an external mathematical reference.  It does not claim that the
ordinal or its isomorphism graph is already represented inside `L`; those are
the subsequent Separation and Replacement obligations.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

/-! ## Points in the small presentation -/

/-- A member of an internal set, transported to its universe-small carrier. -/
noncomputable def smallMember (domain x : LCarrier.{u})
    (hx : x.1 ∈ domain.1) :
    SmallZFCarrier domain.1 :=
  equivShrink (ZFCarrier domain.1) ⟨x.1, hx⟩

@[simp]
theorem smallGraphRel_smallMember_iff
    (relation domain x y : LCarrier.{u})
    (hx : x.1 ∈ domain.1) (hy : y.1 ∈ domain.1) :
    smallGraphRel relation domain (smallMember domain x hx)
        (smallMember domain y hy) ↔
      GraphRel relation x y := by
  simpa only [smallGraphRel, smallMember, InvImage,
    Equiv.symm_apply_apply, rawMemberLCarrier, GraphRel] using
      (rawGraphRel_iff_graphRel relation domain
        ⟨x.1, hx⟩ ⟨y.1, hy⟩)

/-! ## Canonical order types -/

/-- The external ordinal type of an internally represented well-order. -/
noncomputable def canonicalOrderType
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain) : Ordinal.{u} := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  exact Ordinal.type (smallGraphRel relation domain)





/-- The external order type of the strict initial segment below `x`. -/
noncomputable def canonicalMemberOrderType
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) : Ordinal.{u} := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  exact Ordinal.typein (smallGraphRel relation domain)
    (smallMember domain x hx)

/-- The von Neumann set code of the canonical initial-segment type.  This is
an element of `L` because every ordinal is constructible.  No function graph
is asserted at this point. -/
noncomputable def canonicalMemberOrderTypeLCarrier
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) : LCarrier.{u} :=
  ordinalLCarrier (canonicalMemberOrderType relation domain hwell x hx)

theorem canonicalMemberOrderTypeLCarrier_isVonNeumannOrdinal
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    IsVonNeumannOrdinal Constructible.Model.lCarrierMem
      (canonicalMemberOrderTypeLCarrier relation domain hwell x hx) := by
  apply (isVonNeumannOrdinal_lCarrier_iff _).mpr
  exact ZFSet.isOrdinal_toZFSet _

/-- Canonical initial-segment types preserve and reflect the represented
strict order. -/
theorem canonicalMemberOrderType_lt_iff
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x y : LCarrier.{u}) (hx : x.1 ∈ domain.1)
    (hy : y.1 ∈ domain.1) :
    canonicalMemberOrderType relation domain hwell x hx <
        canonicalMemberOrderType relation domain hwell y hy ↔
      GraphRel relation x y := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  change Ordinal.typein (smallGraphRel relation domain)
      (smallMember domain x hx) <
        Ordinal.typein (smallGraphRel relation domain)
          (smallMember domain y hy) ↔ _
  rw [Ordinal.typein_lt_typein]
  exact smallGraphRel_smallMember_iff relation domain x y hx hy

/-- Membership between the von Neumann codes of canonical point types is
exactly the represented source order. -/
theorem canonicalMemberOrderTypeLCarrier_mem_iff
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x y : LCarrier.{u}) (hx : x.1 ∈ domain.1)
    (hy : y.1 ∈ domain.1) :
    (canonicalMemberOrderTypeLCarrier relation domain hwell x hx).1 ∈
        (canonicalMemberOrderTypeLCarrier relation domain hwell y hy).1 ↔
      GraphRel relation x y := by
  rw [canonicalMemberOrderTypeLCarrier,
    canonicalMemberOrderTypeLCarrier,
    ordinalLCarrier_mem_ordinalLCarrier_iff,
    canonicalMemberOrderType_lt_iff relation domain hwell x y hx hy]

/-- Distinct points of the represented well-order have distinct canonical
initial-segment types. -/
theorem canonicalMemberOrderType_injective
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x y : LCarrier.{u}) (hx : x.1 ∈ domain.1)
    (hy : y.1 ∈ domain.1)
    (hxy : canonicalMemberOrderType relation domain hwell x hx =
      canonicalMemberOrderType relation domain hwell y hy) :
    x = y := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  have hsmall : smallMember domain x hx = smallMember domain y hy := by
    apply Ordinal.typein_injective (smallGraphRel relation domain)
    exact hxy
  apply Subtype.ext
  have hraw :
      (⟨x.1, hx⟩ : ZFCarrier domain.1) = ⟨y.1, hy⟩ := by
    simpa only [smallMember, Equiv.symm_apply_apply] using congrArg
      (equivShrink (ZFCarrier domain.1)).symm hsmall
  exact congrArg (fun z : ZFCarrier domain.1 => z.1) hraw

/-- Every point type lies below the type of the whole represented order. -/
theorem canonicalMemberOrderType_lt_canonicalOrderType
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    canonicalMemberOrderType relation domain hwell x hx <
      canonicalOrderType relation domain hwell := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  exact Ordinal.typein_lt_type (smallGraphRel relation domain)
    (smallMember domain x hx)



/-- Every ordinal below the type of the whole order is the canonical type of
some member of the internal domain. -/
theorem exists_member_canonicalOrderType_eq_of_lt
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    {alpha : Ordinal.{u}}
    (halpha : alpha < canonicalOrderType relation domain hwell) :
    exists x : LCarrier.{u}, exists hx : x.1 ∈ domain.1,
      canonicalMemberOrderType relation domain hwell x hx = alpha := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  change alpha < Ordinal.type (smallGraphRel relation domain) at halpha
  rcases Ordinal.typein_surj (smallGraphRel relation domain) halpha with
    ⟨small, hsmall⟩
  let raw : ZFCarrier domain.1 :=
    (equivShrink (ZFCarrier domain.1)).symm small
  let x : LCarrier.{u} := rawMemberLCarrier domain raw
  have hx : x.1 ∈ domain.1 := raw.2
  refine ⟨x, hx, ?_⟩
  change Ordinal.typein (smallGraphRel relation domain)
      (smallMember domain x hx) = alpha
  have hpoint : smallMember domain x hx = small := by
    apply (equivShrink (ZFCarrier domain.1)).symm.injective
    simp only [smallMember, Equiv.symm_apply_apply]
    change (⟨x.1, hx⟩ : ZFCarrier domain.1) = raw
    apply Subtype.ext
    rfl
  rw [hpoint]
  exact hsmall

/-- Every ordinal below the canonical type at `bound` is represented by a
unique predecessor of `bound`.  This is the surjectivity fact used in the
standard order-type induction. -/
theorem exists_predecessor_canonicalMemberOrderType_eq_of_lt
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (bound : LCarrier.{u}) (hbound : bound.1 ∈ domain.1)
    {alpha : Ordinal.{u}}
    (halpha : alpha <
      canonicalMemberOrderType relation domain hwell bound hbound) :
    exists x : LCarrier.{u}, exists hx : x.1 ∈ domain.1,
      GraphRel relation x bound /\
        canonicalMemberOrderType relation domain hwell x hx = alpha := by
  have halphaWhole : alpha < canonicalOrderType relation domain hwell :=
    halpha.trans
      (canonicalMemberOrderType_lt_canonicalOrderType
        relation domain hwell bound hbound)
  rcases exists_member_canonicalOrderType_eq_of_lt
      relation domain hwell halphaWhole with ⟨x, hx, htype⟩
  refine ⟨x, hx, ?_, htype⟩
  apply (canonicalMemberOrderType_lt_iff
    relation domain hwell x bound hx hbound).mp
  simpa only [htype] using halpha

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOrderTypeCanonical


/- Source module: Solutions.Work_CUGCH_InternalOrderTypePredecessor -/
section GCHSource_Work_CUGCH_InternalOrderTypePredecessor
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Internal predecessor sets for an represented relation

This is the Separation part of the order-type construction.  It constructs
an actual `LCarrier` predecessor set from an internally represented relation
graph.  The order-type ordinal and its isomorphism graph are separate
well-founded-recursion obligations and are intentionally not assumed here.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-- Formula with layout `[relation, domain, point, z]` selecting a predecessor. -/
def predecessorMembershipAt : FOFormula 4 :=
  .conj
    (.mem (3 : Fin 4) (1 : Fin 4))
    (graphValueAt (0 : Fin 4) (3 : Fin 4) (2 : Fin 4))

 theorem predecessorMembershipAt_assignment
    (relation domain point z : LCarrier.{u}) :
    snoc ![relation, domain, point] z = ![relation, domain, point, z] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_predecessorMembershipAt
    (relation domain point z : LCarrier.{u}) :
    FOFormula.Satisfies LMem predecessorMembershipAt
        ![relation, domain, point, z] <->
      z.1 ∈ domain.1 /\ GraphValue LMem relation z point := by
  simp [predecessorMembershipAt, FOFormula.Satisfies,
    satisfies_graphValueAt]

/-- Separation produces the exact internal predecessor set. -/
theorem exists_internalPredecessorSet
    (relation domain point : LCarrier.{u}) :
    exists predecessors : LCarrier.{u},
      IsPredecessorSetOf LMem predecessors relation domain point := by
  let params : Tuple LCarrier.{u} 3 := ![relation, domain, point]
  rcases Model.exists_separationLCarrier predecessorMembershipAt params domain with
    ⟨predecessors, hpred⟩
  refine ⟨predecessors, ?_⟩
  intro z
  change z.1 ∈ predecessors.1 <->
    z.1 ∈ domain.1 /\ GraphValue LMem relation z point
  rw [hpred z, predecessorMembershipAt_assignment relation domain point z,
    satisfies_predecessorMembershipAt]
  simp

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOrderTypePredecessor


/- Source module: Solutions.Work_CUGCH_InternalOrderTypeUniqueness -/
section GCHSource_Work_CUGCH_InternalOrderTypeUniqueness
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Uniqueness of internally represented order types

An internal order-isomorphism is represented by an actual Kuratowski graph
in `L`.  This file forgets only the representation proofs after that graph
has been supplied, transports the represented isomorphism to the universe-
small carriers, and compares their ordinary ordinal types.

In particular, two internal von Neumann ordinals which are represented as the
order type of the same initial segment are equal.  No ambient equivalence is
used as an internal witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## Transporting an internal graph to the small carriers -/

/-- The canonical equivalence from the small presentation of a set to its
internal carrier. -/
noncomputable def smallToInternalCarrierEquiv (a : LCarrier.{u}) :
    SmallZFCarrier a.1 ≃ Constructible.Model.InternalCarrier a :=
  (equivShrink (ZFCarrier a.1)).symm.trans
    (Constructible.Godel.RudimentaryTerm.zfCarrierInternalEquiv a)

/-- Membership on an internal set, pulled back to its small carrier. -/
noncomputable def smallInternalMem (a : LCarrier.{u}) :
    SmallZFCarrier a.1 -> SmallZFCarrier a.1 -> Prop :=
  InvImage
    (fun x y : Constructible.Model.InternalCarrier a => LMem x.1 y.1)
    (smallToInternalCarrierEquiv a)

theorem smallInternalMem_ordinalLCarrier (alpha : Ordinal.{u}) :
    smallInternalMem (ordinalLCarrier alpha) = smallOrdinalMem alpha := by
  funext x y
  rfl

/-- The equality above, packaged as a relation isomorphism so that it can be
composed without dependent rewriting through `Ordinal.type`. -/
noncomputable def smallInternalMemOrdinalRelIso (alpha : Ordinal.{u}) :
    smallInternalMem (ordinalLCarrier alpha) ≃r smallOrdinalMem alpha where
  toEquiv := Equiv.refl _
  map_rel_iff' {x y} := by
    change smallOrdinalMem alpha x y <->
      smallInternalMem (ordinalLCarrier alpha) x y
    rw [smallInternalMem_ordinalLCarrier]

/-- The semantic equivalence selected from a represented bijection still
follows the represented graph. -/
theorem IsBijection.toEquiv_graphValue
    {graph domain codomain : LCarrier.{u}}
    (h : IsBijection LMem graph domain codomain)
    (x : Constructible.Model.InternalCarrier domain) :
    GraphValue LMem graph x.1 (h.toEquiv x).1 := by
  change GraphValue LMem graph x.1 (h.toIsInjection.toFun x).1
  exact h.toIsInjection.toFun_graphValue x

/-- A represented order-isomorphism induces an ordinary relation isomorphism
between the semantic internal carriers.  The represented graph remains the
source of the map. -/
noncomputable def IsOrderIsomorphism.toInternalRelIso
    {graph relation domain ordinal : LCarrier.{u}}
    (h : IsOrderIsomorphism LMem graph relation domain ordinal) :
    Constructible.Model.graphRelOn relation domain ≃r
      (fun x y : Constructible.Model.InternalCarrier ordinal =>
        LMem x.1 y.1) where
  toEquiv := h.1.toEquiv
  map_rel_iff' {x y} := by
    have hxValue : GraphValue LMem graph x.1 (h.1.toEquiv x).1 :=
      h.1.toEquiv_graphValue x
    have hyValue : GraphValue LMem graph y.1 (h.1.toEquiv y).1 :=
      h.1.toEquiv_graphValue y
    rw [show Constructible.Model.graphRelOn relation domain x y =
        Constructible.Model.GraphRel relation x.1 y.1 from rfl]
    rw [<- graphValue_lCarrier_iff_graphRel]
    exact (h.2 x.1 y.1 (h.1.toEquiv x).1 (h.1.toEquiv y).1
      x.2 y.2 hxValue hyValue).symm

/-- The preceding relation isomorphism on the universe-small presentations. -/
noncomputable def IsOrderIsomorphism.toSmallRelIso
    {graph relation domain ordinal : LCarrier.{u}}
    (h : IsOrderIsomorphism LMem graph relation domain ordinal) :
    smallGraphRel relation domain ≃r smallInternalMem ordinal := by
  let sourceEquiv := smallToInternalCarrierEquiv domain
  let targetEquiv := smallToInternalCarrierEquiv ordinal
  let sourceIso := RelIso.preimage sourceEquiv
    (Constructible.Model.graphRelOn relation domain)
  let targetIso := RelIso.preimage targetEquiv
    (fun x y : Constructible.Model.InternalCarrier ordinal => LMem x.1 y.1)
  have hsource :
      smallGraphRel relation domain =
        InvImage (Constructible.Model.graphRelOn relation domain)
          sourceEquiv := by
    funext x y
    rfl
  have htarget :
      smallInternalMem ordinal =
        InvImage
          (fun x y : Constructible.Model.InternalCarrier ordinal =>
            LMem x.1 y.1)
          targetEquiv := by
    rfl
  rw [hsource, htarget]
  exact sourceIso.trans (h.toInternalRelIso.trans targetIso.symm)

/-! ## Uniqueness of the ordinal target -/



/-- Internal predecessor sets for the same represented relation and point are
extensionally equal. -/
theorem predecessorSet_unique
    {first second relation domain point : LCarrier.{u}}
    (hfirst : IsPredecessorSetOf LMem first relation domain point)
    (hsecond : IsPredecessorSetOf LMem second relation domain point) :
    first = second := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  . intro hz
    let zL : LCarrier.{u} :=
      ⟨z, Constructible.mem_L_of_mem hz first.2⟩
    have hsemantic := (hfirst zL).mp hz
    exact (hsecond zL).mpr hsemantic
  . intro hz
    let zL : LCarrier.{u} :=
      ⟨z, Constructible.mem_L_of_mem hz second.2⟩
    have hsemantic := (hsecond zL).mp hz
    exact (hfirst zL).mpr hsemantic

/-- A well-ordered initial segment has only one internally represented von
Neumann ordinal as its order type. -/
theorem IsInitialSegmentOrderType.ordinal_unique
    {relation domain point first second : LCarrier.{u}}
    (hfirst : IsInitialSegmentOrderType LMem relation domain point first)
    (hsecond : IsInitialSegmentOrderType LMem relation domain point second) :
    first = second := by
  rcases hfirst with ⟨hfirstOrdinal, predecessorsFirst,
    hpredecessorsFirst, graphFirst, hgraphFirst⟩
  rcases hsecond with ⟨hsecondOrdinal, predecessorsSecond,
    hpredecessorsSecond, graphSecond, hgraphSecond⟩
  have hpredecessors : predecessorsSecond = predecessorsFirst :=
    predecessorSet_unique hpredecessorsSecond hpredecessorsFirst
  subst predecessorsSecond
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      first hfirstOrdinal with ⟨alpha, hfirstEq⟩
  rcases exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
      second hsecondOrdinal with ⟨beta, hsecondEq⟩
  subst first
  subst second
  let ordinalIso : smallOrdinalMem alpha ≃r smallOrdinalMem beta :=
    (smallInternalMemOrdinalRelIso alpha).symm.trans
      (hgraphFirst.toSmallRelIso.symm.trans
        (hgraphSecond.toSmallRelIso.trans
          (smallInternalMemOrdinalRelIso beta)))
  have hab : alpha = beta := by
    calc
      alpha = Ordinal.type (smallOrdinalMem alpha) :=
        (type_smallZFCarrier_ordinal alpha).symm
      _ = Ordinal.type (smallOrdinalMem beta) :=
        ordinalIso.ordinalType_congr
      _ = beta := type_smallZFCarrier_ordinal beta
  exact congrArg ordinalLCarrier hab

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOrderTypeUniqueness


/- Source module: Solutions.Work_CUGCH_InternalOrderTypeReplacement -/
section GCHSource_Work_CUGCH_InternalOrderTypeReplacement
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Replacement of the canonical order types below one point

This is the Replacement step in the standard well-order recursion.  Assume
that every strict predecessor of `point` already has its canonical internally
represented order type.  Separation first produces the internal predecessor
set.  Replacement, applied to `beforeOrderTypeRelation`, then produces the
set of predecessor order types.  That range is exactly the canonical ordinal
attached to `point`.

The returned range is an actual `LCarrier`; an external `ZFSet.range` is not
used as its witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

 theorem beforeOrderTypeReplacement_assignment
    (relation domain point input output : LCarrier.{u}) :
    snoc (snoc ![relation, domain, point] input) output =
      ![relation, domain, point, input, output] := by
  funext i
  fin_cases i <;> rfl

/--
Under the induction hypothesis for all predecessors of `point`, Replacement
constructs their order-type range inside `L`, and this range is precisely the
von Neumann ordinal which is the canonical order type at `point`.
-/
theorem exists_internalPredecessorOrderTypeRange
    (relation domain point : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (hpoint : point.1 ∈ domain.1)
    (hsegments : forall z : LCarrier.{u},
      forall hz : z.1 ∈ domain.1,
        GraphRel relation z point ->
          IsInitialSegmentOrderType LMem relation domain z
            (canonicalMemberOrderTypeLCarrier
              relation domain hwell z hz)) :
    exists predecessors range : LCarrier.{u},
      IsPredecessorSetOf LMem predecessors relation domain point /\
        (forall y : LCarrier.{u},
          y.1 ∈ range.1 <->
            (exists x : LCarrier.{u}, x.1 ∈ predecessors.1 /\
              FOFormula.Satisfies LMem beforeOrderTypeRelation
                (snoc (snoc ![relation, domain, point] x) y))) /\
        range = canonicalMemberOrderTypeLCarrier
          relation domain hwell point hpoint := by
  rcases exists_internalPredecessorSet relation domain point with
    ⟨predecessors, hpredecessors⟩
  let params : Tuple LCarrier.{u} 3 := ![relation, domain, point]
  have hfunctional : forall x : LCarrier.{u},
      x.1 ∈ predecessors.1 ->
        ∃! y : LCarrier.{u},
          FOFormula.Satisfies LMem beforeOrderTypeRelation
            (snoc (snoc params x) y) := by
    intro x hx
    have hxSemantic := (hpredecessors x).mp hx
    have hxDomain : x.1 ∈ domain.1 := hxSemantic.1
    have hxRelation : GraphRel relation x point :=
      (graphValue_lCarrier_iff_graphRel relation x point).mp
        hxSemantic.2
    let value := canonicalMemberOrderTypeLCarrier
      relation domain hwell x hxDomain
    have hsegment :
        IsInitialSegmentOrderType LMem relation domain x value :=
      hsegments x hxDomain hxRelation
    have hvalue :
        FOFormula.Satisfies LMem beforeOrderTypeRelation
          (snoc (snoc params x) value) := by
      simp only [params]
      rw [beforeOrderTypeReplacement_assignment]
      exact (satisfies_beforeOrderTypeRelation
        relation domain point x value).mpr
          ⟨hxDomain, hxRelation, hsegment⟩
    refine ⟨value, hvalue, ?_⟩
    intro other hother
    have hotherSemantic :
        IsInitialSegmentOrderType LMem relation domain x other := by
      simp only [params] at hother
      rw [beforeOrderTypeReplacement_assignment] at hother
      exact (satisfies_beforeOrderTypeRelation
        relation domain point x other).mp hother |>.2.2
    exact hotherSemantic.ordinal_unique hsegment
  rcases Model.exists_replacementLCarrier
      beforeOrderTypeRelation params predecessors hfunctional with
    ⟨range, hrange⟩
  refine ⟨predecessors, range, hpredecessors, ?_, ?_⟩
  . intro y
    simpa only [params] using hrange y
  . apply Subtype.ext
    apply ZFSet.ext
    intro y
    constructor
    . intro hyRange
      let yL : LCarrier.{u} :=
        ⟨y, Constructible.mem_L_of_mem hyRange range.2⟩
      rcases (hrange yL).mp hyRange with
        ⟨x, hxPredecessors, hformula⟩
      have hsemantic := (hpredecessors x).mp hxPredecessors
      have hxDomain : x.1 ∈ domain.1 := hsemantic.1
      have hxRelation : GraphRel relation x point :=
        (graphValue_lCarrier_iff_graphRel relation x point).mp
          hsemantic.2
      have hcanonical :
          IsInitialSegmentOrderType LMem relation domain x
            (canonicalMemberOrderTypeLCarrier
              relation domain hwell x hxDomain) :=
        hsegments x hxDomain hxRelation
      have hySegment :
          IsInitialSegmentOrderType LMem relation domain x yL := by
        simp only [params] at hformula
        rw [beforeOrderTypeReplacement_assignment] at hformula
        exact (satisfies_beforeOrderTypeRelation
          relation domain point x yL).mp hformula |>.2.2
      have hyEq : yL = canonicalMemberOrderTypeLCarrier
          relation domain hwell x hxDomain :=
        hySegment.ordinal_unique hcanonical
      have hcanonicalMem :
          (canonicalMemberOrderTypeLCarrier
            relation domain hwell x hxDomain).1 ∈
              (canonicalMemberOrderTypeLCarrier
                relation domain hwell point hpoint).1 :=
        (canonicalMemberOrderTypeLCarrier_mem_iff
          relation domain hwell x point hxDomain hpoint).mpr hxRelation
      change yL.1 ∈
        (canonicalMemberOrderTypeLCarrier
          relation domain hwell point hpoint).1
      rw [hyEq]
      exact hcanonicalMem
    . intro hyTarget
      let yL : LCarrier.{u} :=
        ⟨y, Constructible.mem_L_of_mem hyTarget
          (canonicalMemberOrderTypeLCarrier
            relation domain hwell point hpoint).2⟩
      have hyOrdinal : y ∈
          (canonicalMemberOrderType
            relation domain hwell point hpoint).toZFSet := by
        exact hyTarget
      rcases Ordinal.mem_toZFSet_iff.mp hyOrdinal with
        ⟨beta, hbeta, hbetaValue⟩
      rcases exists_predecessor_canonicalMemberOrderType_eq_of_lt
          relation domain hwell point hpoint hbeta with
        ⟨x, hxDomain, hxRelation, hxType⟩
      have hxPredecessors : x.1 ∈ predecessors.1 :=
        (hpredecessors x).mpr
          ⟨hxDomain,
            (graphValue_lCarrier_iff_graphRel relation x point).mpr
              hxRelation⟩
      have hyEq : yL = canonicalMemberOrderTypeLCarrier
          relation domain hwell x hxDomain := by
        apply Subtype.ext
        change y =
          (canonicalMemberOrderType
            relation domain hwell x hxDomain).toZFSet
        rw [hxType]
        exact hbetaValue.symm
      have hsegment :
          IsInitialSegmentOrderType LMem relation domain x
            (canonicalMemberOrderTypeLCarrier
              relation domain hwell x hxDomain) :=
        hsegments x hxDomain hxRelation
      have hformula :
          FOFormula.Satisfies LMem beforeOrderTypeRelation
            (snoc (snoc params x) yL) := by
        simp only [params]
        rw [beforeOrderTypeReplacement_assignment]
        apply (satisfies_beforeOrderTypeRelation
          relation domain point x yL).mpr
        refine ⟨hxDomain, hxRelation, ?_⟩
        rw [hyEq]
        exact hsegment
      exact (hrange yL).mpr ⟨x, hxPredecessors, hformula⟩

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOrderTypeReplacement


/- Source module: Solutions.Work_CUGCH_InternalOrderTypeStep -/
section GCHSource_Work_CUGCH_InternalOrderTypeStep
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The successor step of the internal order-type recursion

Assume that every strict predecessor of a point already has its canonical
internally represented order type.  The preceding Replacement theorem gives
the exact internal range.  Separation of `beforeOrderTypeRelation` inside the
union of the predecessor set and the target ordinal then gives an actual
Kuratowski graph in `L`.  This file proves that graph is an order isomorphism.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

 theorem beforeOrderTypeStep_assignment
    (relation domain point input output : LCarrier.{u}) :
    snoc (snoc ![relation, domain, point] input) output =
      ![relation, domain, point, input, output] := by
  funext i
  fin_cases i <;> rfl

/-- The canonical order-type code is injective on the points of an internally
represented well-order. -/
theorem canonicalMemberOrderTypeLCarrier_injective
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x y : LCarrier.{u}) (hx : x.1 ∈ domain.1)
    (hy : y.1 ∈ domain.1)
    (hxy : canonicalMemberOrderTypeLCarrier
        relation domain hwell x hx =
      canonicalMemberOrderTypeLCarrier
        relation domain hwell y hy) :
    x = y := by
  apply canonicalMemberOrderType_injective
    relation domain hwell x y hx hy
  apply Ordinal.toZFSet_injective
  exact congrArg Subtype.val hxy

/--
The well-founded induction step: if all strict predecessors of `point` have
their canonical internal order types, then `point` has its canonical internal
order type as well.
-/
theorem canonicalMemberOrderType_isInitial_of_predecessors
    (relation domain point : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (hpoint : point.1 ∈ domain.1)
    (hsegments : forall z : LCarrier.{u},
      forall hz : z.1 ∈ domain.1,
        GraphRel relation z point ->
          IsInitialSegmentOrderType LMem relation domain z
            (canonicalMemberOrderTypeLCarrier
              relation domain hwell z hz)) :
    IsInitialSegmentOrderType LMem relation domain point
      (canonicalMemberOrderTypeLCarrier
        relation domain hwell point hpoint) := by
  let target := canonicalMemberOrderTypeLCarrier
    relation domain hwell point hpoint
  rcases exists_internalPredecessorOrderTypeRange
      relation domain point hwell hpoint hsegments with
    ⟨predecessors, range, hpredecessors, _hrange, hrangeEq⟩
  have hrangeTarget : range = target := by
    exact hrangeEq
  let params : Tuple LCarrier.{u} 3 := ![relation, domain, point]
  let container : LCarrier.{u} := unionLCarrier predecessors target
  rcases Model.exists_definableRelationGraph_with_support
      beforeOrderTypeRelation params container with
    ⟨graph, hsupport, hgraph⟩
  have hformula_iff : forall x y : LCarrier.{u},
      FOFormula.Satisfies LMem beforeOrderTypeRelation
          (snoc (snoc params x) y) <->
        x.1 ∈ domain.1 /\ GraphRel relation x point /\
          IsInitialSegmentOrderType LMem relation domain x y := by
    intro x y
    simp only [params]
    rw [beforeOrderTypeStep_assignment]
    exact satisfies_beforeOrderTypeRelation relation domain point x y
  have hcanonicalMem : forall x : LCarrier.{u},
      forall hx : x.1 ∈ domain.1,
        GraphRel relation x point ->
          (canonicalMemberOrderTypeLCarrier
            relation domain hwell x hx).1 ∈ target.1 := by
    intro x hx hxPoint
    exact (canonicalMemberOrderTypeLCarrier_mem_iff
      relation domain hwell x point hx hpoint).mpr hxPoint
  have hformula_eq : forall x y : LCarrier.{u},
      forall hx : x.1 ∈ predecessors.1,
        FOFormula.Satisfies LMem beforeOrderTypeRelation
          (snoc (snoc params x) y) ->
            y = canonicalMemberOrderTypeLCarrier
              relation domain hwell x
                ((hpredecessors x).mp hx).1 := by
    intro x y hx hformula
    have hxSemantic := (hpredecessors x).mp hx
    have hxDomain : x.1 ∈ domain.1 := hxSemantic.1
    have hxPoint : GraphRel relation x point :=
      (graphValue_lCarrier_iff_graphRel relation x point).mp
        hxSemantic.2
    have hySegment := (hformula_iff x y).mp hformula |>.2.2
    have hcanonical := hsegments x hxDomain hxPoint
    exact hySegment.ordinal_unique hcanonical
  have hbetween : IsGraphBetween LMem graph predecessors target := by
    intro pair hpair
    rcases hsupport pair hpair with
      ⟨x, y, _hxContainer, _hyContainer, hpairEq, hformula⟩
    have hsemantic := (hformula_iff x y).mp hformula
    have hxDomain : x.1 ∈ domain.1 := hsemantic.1
    have hxPoint : GraphRel relation x point := hsemantic.2.1
    have hxPredecessors : x.1 ∈ predecessors.1 :=
      (hpredecessors x).mpr
        ⟨hxDomain,
          (graphValue_lCarrier_iff_graphRel relation x point).mpr
            hxPoint⟩
    have hyEq : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell x hxDomain :=
      hsemantic.2.2.ordinal_unique (hsegments x hxDomain hxPoint)
    have hyTarget : y.1 ∈ target.1 := by
      rw [hyEq]
      exact hcanonicalMem x hxDomain hxPoint
    refine ⟨x, hxPredecessors, y, hyTarget, ?_⟩
    exact (isKuratowskiPairOf_lCarrier_iff pair x y).mpr hpairEq
  have htotal : forall x : LCarrier.{u}, x.1 ∈ predecessors.1 ->
      HasUniqueImage LMem graph x target := by
    intro x hx
    have hxSemantic := (hpredecessors x).mp hx
    have hxDomain : x.1 ∈ domain.1 := hxSemantic.1
    have hxPoint : GraphRel relation x point :=
      (graphValue_lCarrier_iff_graphRel relation x point).mp
        hxSemantic.2
    let value := canonicalMemberOrderTypeLCarrier
      relation domain hwell x hxDomain
    have hvalueTarget : value.1 ∈ target.1 :=
      hcanonicalMem x hxDomain hxPoint
    have hxContainer : x.1 ∈ container.1 :=
      (mem_unionLCarrier_iff predecessors target x).mpr (Or.inl hx)
    have hvalueContainer : value.1 ∈ container.1 :=
      (mem_unionLCarrier_iff predecessors target value).mpr
        (Or.inr hvalueTarget)
    have hvalueFormula :
        FOFormula.Satisfies LMem beforeOrderTypeRelation
          (snoc (snoc params x) value) :=
      (hformula_iff x value).mpr
        ⟨hxDomain, hxPoint, hsegments x hxDomain hxPoint⟩
    have hvalueGraph : GraphValue LMem graph x value :=
      (graphValue_lCarrier_iff_graphRel graph x value).mpr
        ((hgraph x value).mpr
          ⟨hxContainer, hvalueContainer, hvalueFormula⟩)
    refine ⟨value, hvalueTarget, hvalueGraph, ?_⟩
    intro other _hotherTarget hotherGraph
    have hotherFormula := (hgraph x other).mp
      ((graphValue_lCarrier_iff_graphRel graph x other).mp
        hotherGraph) |>.2.2
    exact hformula_eq x other hx hotherFormula
  have honto : forall y : LCarrier.{u}, y.1 ∈ target.1 ->
      HasUniquePreimage LMem graph predecessors y := by
    intro y hyTarget
    have hyOrdinal : y.1 ∈
        (canonicalMemberOrderType
          relation domain hwell point hpoint).toZFSet := by
      exact hyTarget
    rcases Ordinal.mem_toZFSet_iff.mp hyOrdinal with
      ⟨beta, hbeta, hbetaValue⟩
    rcases exists_predecessor_canonicalMemberOrderType_eq_of_lt
        relation domain hwell point hpoint hbeta with
      ⟨x, hxDomain, hxPoint, hxType⟩
    have hxPredecessors : x.1 ∈ predecessors.1 :=
      (hpredecessors x).mpr
        ⟨hxDomain,
          (graphValue_lCarrier_iff_graphRel relation x point).mpr
            hxPoint⟩
    have hyEq : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell x hxDomain := by
      apply Subtype.ext
      change y.1 =
        (canonicalMemberOrderType
          relation domain hwell x hxDomain).toZFSet
      rw [hxType]
      exact hbetaValue.symm
    have hxContainer : x.1 ∈ container.1 :=
      (mem_unionLCarrier_iff predecessors target x).mpr
        (Or.inl hxPredecessors)
    have hyContainer : y.1 ∈ container.1 :=
      (mem_unionLCarrier_iff predecessors target y).mpr
        (Or.inr hyTarget)
    have hformula :
        FOFormula.Satisfies LMem beforeOrderTypeRelation
          (snoc (snoc params x) y) := by
      apply (hformula_iff x y).mpr
      refine ⟨hxDomain, hxPoint, ?_⟩
      rw [hyEq]
      exact hsegments x hxDomain hxPoint
    have hgraphValue : GraphValue LMem graph x y :=
      (graphValue_lCarrier_iff_graphRel graph x y).mpr
        ((hgraph x y).mpr ⟨hxContainer, hyContainer, hformula⟩)
    refine ⟨x, hxPredecessors, hgraphValue, ?_⟩
    intro z hzPredecessors hzGraph
    have hzSemantic := (hpredecessors z).mp hzPredecessors
    have hzDomain : z.1 ∈ domain.1 := hzSemantic.1
    have hzPoint : GraphRel relation z point :=
      (graphValue_lCarrier_iff_graphRel relation z point).mp
        hzSemantic.2
    have hzFormula := (hgraph z y).mp
      ((graphValue_lCarrier_iff_graphRel graph z y).mp hzGraph) |>.2.2
    have hyEqZ : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell z hzDomain :=
      hformula_eq z y hzPredecessors hzFormula
    apply canonicalMemberOrderTypeLCarrier_injective
      relation domain hwell z x hzDomain hxDomain
    exact hyEqZ.symm.trans hyEq
  refine ⟨canonicalMemberOrderTypeLCarrier_isVonNeumannOrdinal
      relation domain hwell point hpoint,
    predecessors, hpredecessors, graph, ?_⟩
  refine ⟨⟨hbetween, htotal, honto⟩, ?_⟩
  intro x y imageX imageY hx hy hxImage hyImage
  have hxSemantic := (hpredecessors x).mp hx
  have hySemantic := (hpredecessors y).mp hy
  have hxDomain : x.1 ∈ domain.1 := hxSemantic.1
  have hyDomain : y.1 ∈ domain.1 := hySemantic.1
  have hxFormula := (hgraph x imageX).mp
    ((graphValue_lCarrier_iff_graphRel graph x imageX).mp
      hxImage) |>.2.2
  have hyFormula := (hgraph y imageY).mp
    ((graphValue_lCarrier_iff_graphRel graph y imageY).mp
      hyImage) |>.2.2
  have hxEq := hformula_eq x imageX hx hxFormula
  have hyEq := hformula_eq y imageY hy hyFormula
  rw [hxEq, hyEq]
  rw [graphValue_lCarrier_iff_graphRel]
  exact (canonicalMemberOrderTypeLCarrier_mem_iff
    relation domain hwell x y hxDomain hyDomain).symm

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOrderTypeStep


/- Source module: Solutions.Work_CUGCH_InternalOrderTypeInduction -/
section GCHSource_Work_CUGCH_InternalOrderTypeInduction
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Well-founded induction for internal order types

The local order-type step is iterated along the universe-small presentation
of an internally represented well-order.  Every point therefore receives its
canonical von Neumann ordinal together with an actual predecessor set and an
actual order-isomorphism graph in `L`.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## Moving between small points and internal points -/

/-- Turn a point of the small carrier back into an internal member. -/
noncomputable def smallPointLCarrier
    (domain : LCarrier.{u}) (point : SmallZFCarrier domain.1) :
    LCarrier.{u} :=
  rawMemberLCarrier domain
    ((equivShrink (ZFCarrier domain.1)).symm point)

theorem smallPointLCarrier_mem
    (domain : LCarrier.{u}) (point : SmallZFCarrier domain.1) :
    (smallPointLCarrier domain point).1 ∈ domain.1 :=
  ((equivShrink (ZFCarrier domain.1)).symm point).2

@[simp]
theorem smallMember_smallPointLCarrier
    (domain : LCarrier.{u}) (point : SmallZFCarrier domain.1) :
    smallMember domain (smallPointLCarrier domain point)
        (smallPointLCarrier_mem domain point) = point := by
  simp [smallMember, smallPointLCarrier]

@[simp]
theorem smallPointLCarrier_smallMember
    (domain x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    smallPointLCarrier domain (smallMember domain x hx) = x := by
  apply Subtype.ext
  simp [smallPointLCarrier, smallMember]

/-! ## The induction theorem -/

/-- Every point of an internally represented well-order has its canonical
internally represented initial-segment order type. -/
theorem canonicalMemberOrderType_isInitial
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (point : LCarrier.{u}) (hpoint : point.1 ∈ domain.1) :
    IsInitialSegmentOrderType LMem relation domain point
      (canonicalMemberOrderTypeLCarrier
        relation domain hwell point hpoint) := by
  letI : IsWellOrder (SmallZFCarrier domain.1)
      (smallGraphRel relation domain) :=
    smallGraphRel_isWellOrder relation domain hwell
  let wellFounded : WellFounded (smallGraphRel relation domain) :=
    IsWellFounded.wf
  have hall : forall small : SmallZFCarrier domain.1,
      forall z : LCarrier.{u}, forall hz : z.1 ∈ domain.1,
        smallMember domain z hz = small ->
          IsInitialSegmentOrderType LMem relation domain z
            (canonicalMemberOrderTypeLCarrier
              relation domain hwell z hz) := by
    intro small
    apply wellFounded.induction small
    intro current ih z hz hzCurrent
    apply canonicalMemberOrderType_isInitial_of_predecessors
      relation domain z hwell hz
    intro predecessor hpredecessor hpredecessorZ
    have hbelowRaw := (smallGraphRel_smallMember_iff
      relation domain predecessor z hpredecessor hz).mpr hpredecessorZ
    have hbelow : smallGraphRel relation domain
        (smallMember domain predecessor hpredecessor) current := by
      simpa only [hzCurrent] using hbelowRaw
    exact ih (smallMember domain predecessor hpredecessor) hbelow
      predecessor hpredecessor rfl
  let pointSmall := smallMember domain point hpoint
  exact hall pointSmall point hpoint rfl

end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOrderTypeInduction


/- Source module: Solutions.Work_CUGCH_InternalOrderTypeWitnessConstruction -/
section GCHSource_Work_CUGCH_InternalOrderTypeWitnessConstruction
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Constructing the internal order-type witness

The pointwise well-founded induction is assembled into the explicit
`InternalOrderTypeWitness` required by the cardinal-representative interface.
The target is the ordinary order type of the universe-small presentation,
represented by its von Neumann code in `L`.  The formula
`memberOrderTypeRelation` is proved total, bounded, single-valued, injective,
and onto that target.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-- The canonical point order type lies in the canonical order type of the
whole represented well-order. -/
theorem canonicalMemberOrderTypeLCarrier_mem_canonicalOrderType
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain)
    (x : LCarrier.{u}) (hx : x.1 ∈ domain.1) :
    (canonicalMemberOrderTypeLCarrier
      relation domain hwell x hx).1 ∈
        (ordinalLCarrier
          (canonicalOrderType relation domain hwell)).1 := by
  exact (ordinalLCarrier_mem_ordinalLCarrier_iff _ _).mpr
    (canonicalMemberOrderType_lt_canonicalOrderType
      relation domain hwell x hx)

/-- An internally represented well-order supplies the complete order-type
witness needed to build its internal bijection with an ordinal. -/
noncomputable def canonicalInternalOrderTypeWitness
    (relation domain : LCarrier.{u})
    (hwell : InternallyWellOrders relation domain) :
    InternalOrderTypeWitness relation domain where
  ordinal := ordinalLCarrier (canonicalOrderType relation domain hwell)
  ordinal_spec := by
    apply (isVonNeumannOrdinal_lCarrier_iff _).mpr
    exact ZFSet.isOrdinal_toZFSet _
  total := by
    intro x hx
    let value := canonicalMemberOrderTypeLCarrier
      relation domain hwell x hx
    refine ⟨value,
      canonicalMemberOrderTypeLCarrier_mem_canonicalOrderType
        relation domain hwell x hx, ?_⟩
    apply (satisfies_memberOrderTypeRelation
      relation domain x value).mpr
    exact ⟨hx,
      canonicalMemberOrderType_isInitial
        relation domain hwell x hx⟩
  bounded := by
    intro x y hx hformula
    have hySegment := (satisfies_memberOrderTypeRelation
      relation domain x y).mp hformula |>.2
    have hcanonical := canonicalMemberOrderType_isInitial
      relation domain hwell x hx
    have hyEq : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell x hx :=
      hySegment.ordinal_unique hcanonical
    rw [hyEq]
    exact canonicalMemberOrderTypeLCarrier_mem_canonicalOrderType
      relation domain hwell x hx
  unique := by
    intro x y z _hx _hy _hz hyFormula hzFormula
    have hySegment := (satisfies_memberOrderTypeRelation
      relation domain x y).mp hyFormula |>.2
    have hzSegment := (satisfies_memberOrderTypeRelation
      relation domain x z).mp hzFormula |>.2
    exact hySegment.ordinal_unique hzSegment
  injective := by
    intro x z y hx hz _hy hxFormula hzFormula
    have hxSegment := (satisfies_memberOrderTypeRelation
      relation domain x y).mp hxFormula |>.2
    have hzSegment := (satisfies_memberOrderTypeRelation
      relation domain z y).mp hzFormula |>.2
    have hxCanonical := canonicalMemberOrderType_isInitial
      relation domain hwell x hx
    have hzCanonical := canonicalMemberOrderType_isInitial
      relation domain hwell z hz
    have hyEqX : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell x hx :=
      hxSegment.ordinal_unique hxCanonical
    have hyEqZ : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell z hz :=
      hzSegment.ordinal_unique hzCanonical
    apply canonicalMemberOrderTypeLCarrier_injective
      relation domain hwell x z hx hz
    exact hyEqX.symm.trans hyEqZ
  onto := by
    intro y hy
    have hyOrdinal : y.1 ∈
        (canonicalOrderType relation domain hwell).toZFSet := by
      exact hy
    rcases Ordinal.mem_toZFSet_iff.mp hyOrdinal with
      ⟨beta, hbeta, hbetaValue⟩
    rcases exists_member_canonicalOrderType_eq_of_lt
        relation domain hwell hbeta with
      ⟨x, hx, hxType⟩
    have hyEq : y = canonicalMemberOrderTypeLCarrier
        relation domain hwell x hx := by
      apply Subtype.ext
      change y.1 =
        (canonicalMemberOrderType relation domain hwell x hx).toZFSet
      rw [hxType]
      exact hbetaValue.symm
    refine ⟨x, hx, ?_⟩
    apply (satisfies_memberOrderTypeRelation
      relation domain x y).mpr
    refine ⟨hx, ?_⟩
    rw [hyEq]
    exact canonicalMemberOrderType_isInitial
      relation domain hwell x hx





end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOrderTypeWitnessConstruction


