-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library11
-- name    : CH_ConstructibleAC_Library11
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:28:39.157507+00:00
-- url     : https://prove2.me/theorems/7bdb5ee8-7ef1-47d0-874d-34fdf41e0624
-- title:
--   Canonical definable graphs and stage orders
-- statement:
--   At a limit stage, a coded history describes the preceding stage data. This library supplies the limit-history and canonical-graph interfaces, orders on initial segments, least-program descriptions, and the first-stage information used to compare constructible elements. These ingredients make the order data compatible with the descriptions used by the rudimentary compiler.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageHistoryLimitFormula.lean#L1-L132; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalDefinableRelationGraph.lean#L1-L222; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InitialSegmentOrder.lean#L1-L114; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryLeastProgramFormula.lean#L1-L198; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackProgramOrderRepresented.lean#L1-L556; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryLeastProgramSemantics.lean#L1-L186; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/MinimalStage.lean#L1-L152; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/StageOrder.lean#L1-L297; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalStageOrder.lean#L1-L123; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryGeneratorInternalOrder.lean#L1-L139

import Definitions.Def_CH_ConstructibleAC_Library10
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


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageHistoryLimitFormula -/
section CUAdapterModule67
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The limit-state clause for constructible-stage histories

At a limit index, both the stage and its coherent order graph are internal
unions of their earlier values.  The formulas here express those two
extensional union clauses using only membership and the verified history-entry
predicate.
-/


universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => Model.lCarrierMem

/-!
All formulas in this file have the outer layout
`(history, index, stage, relation)`.

After binding a candidate member `z`, the union witness layout is
`(history, index, stage, relation, z, earlierIndex, earlierStage,
earlierRelation)`.
-/

/-- The stage coordinate is the union of all earlier stage coordinates. -/
def historyUnionStageFormula : FOFormula 4 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (4 : Fin 5) (2 : Fin 5))
      (FOFormula.boundedEx (1 : Fin 5)
        (.ex (.ex
          (.conj
            (historyEntryAt
              (0 : Fin 8) (5 : Fin 8) (6 : Fin 8) (7 : Fin 8))
            (.mem (4 : Fin 8) (6 : Fin 8)))))))

/-- The relation coordinate is the union of all earlier relation graphs. -/
def historyUnionRelationFormula : FOFormula 4 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (4 : Fin 5) (3 : Fin 5))
      (FOFormula.boundedEx (1 : Fin 5)
        (.ex (.ex
          (.conj
            (historyEntryAt
              (0 : Fin 8) (5 : Fin 8) (6 : Fin 8) (7 : Fin 8))
            (.mem (4 : Fin 8) (7 : Fin 8)))))))

/-- Both coordinates obey their limit-union clauses. -/
def historyLimitStateFormula : FOFormula 4 :=
  .conj historyUnionStageFormula historyUnionRelationFormula

/-- The direct assignment for all history-state formulas. -/
def historyStateAssignment
    (history index stage relation : LCarrier.{u}) :
    Tuple LCarrier.{u} 4 :=
  ![history, index, stage, relation]

@[simp]
theorem satisfies_historyUnionStageFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyUnionStageFormula
        (historyStateAssignment history index stage relation) ↔
      ∀ z : LCarrier.{u}, z.1 ∈ stage.1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ index.1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry history earlierIndex
                earlierStage earlierRelation ∧
                z.1 ∈ earlierStage.1 := by
  simp only [historyUnionStageFormula, historyStateAssignment,
    FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    FOFormula.satisfies_boundedEx, FOFormula.Satisfies,
    satisfies_historyEntryAt_iff, HistoryEntry]
  rfl

@[simp]
theorem satisfies_historyUnionRelationFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyUnionRelationFormula
        (historyStateAssignment history index stage relation) ↔
      ∀ z : LCarrier.{u}, z.1 ∈ relation.1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ index.1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry history earlierIndex
                earlierStage earlierRelation ∧
                z.1 ∈ earlierRelation.1 := by
  simp only [historyUnionRelationFormula, historyStateAssignment,
    FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    FOFormula.satisfies_boundedEx, FOFormula.Satisfies,
    satisfies_historyEntryAt_iff, HistoryEntry]
  rfl

@[simp]
theorem satisfies_historyLimitStateFormula
    (history index stage relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem historyLimitStateFormula
        (historyStateAssignment history index stage relation) ↔
      (∀ z : LCarrier.{u}, z.1 ∈ stage.1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ index.1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry history earlierIndex
                earlierStage earlierRelation ∧
                z.1 ∈ earlierStage.1) ∧
      (∀ z : LCarrier.{u}, z.1 ∈ relation.1 ↔
        ∃ earlierIndex : LCarrier.{u},
          earlierIndex.1 ∈ index.1 ∧
            ∃ earlierStage earlierRelation : LCarrier.{u},
              HistoryEntry history earlierIndex
                earlierStage earlierRelation ∧
                z.1 ∈ earlierRelation.1) := by
  simp only [historyLimitStateFormula, FOFormula.Satisfies,
    satisfies_historyUnionStageFormula,
    satisfies_historyUnionRelationFormula]

end

end Constructible.Model
end CUAdapterModule67



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalDefinableRelationGraph -/
section CUAdapterModule68
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Canonical graphs of formula-defined relations

The existential graph construction is sufficient for Separation, but a
transfinite recursion needs a graph uniquely determined by its inputs.  This
file separates directly inside the constructible Cartesian square and keeps
the resulting exact membership specification.
-/


universe u

namespace Constructible.Model

noncomputable section

/-! ## An object-language formula specifying the exact output graph -/

/--
Embed the layout `(params, domain, pair)` into
`(params, domain, relation, pair)`, skipping the candidate relation.
-/
def canonicalGraphOutputRename {n : Nat} : Fin (n + 2) → Fin (n + 3) :=
  Fin.lastCases
    (Fin.last (n + 2))
    (fun j => Fin.lastCases
      (Fin.castSucc (Fin.castSucc (Fin.last n)))
      (fun i => i.castSucc.castSucc.castSucc)
      j)

theorem comp_canonicalGraphOutputRename {A : Type u} {n : Nat}
    (params : Tuple A n) (domain relation pair : A) :
    (fun i => snoc (snoc (snoc params domain) relation) pair
      (canonicalGraphOutputRename i)) =
      snoc (snoc params domain) pair := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [canonicalGraphOutputRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [canonicalGraphOutputRename]
    · simp [canonicalGraphOutputRename]

/--
`canonicalGraphOutputFormula phi(params, domain, relation)` says that
`relation` consists exactly of the ordered pairs selected by `phi` on
`domain`.  Extensionality therefore makes its output unique.
-/
def canonicalGraphOutputFormula {n : Nat}
    (phi : FOFormula (n + 2)) : FOFormula (n + 2) :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last (n + 2)) (Fin.castSucc (Fin.last (n + 1))))
      (FOFormula.rename canonicalGraphOutputRename
        (DefinableRelationGraph.graphFormula phi)))

@[simp]
theorem satisfies_canonicalGraphOutputFormula {A : Type u}
    (E : A → A → Prop) {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple A n) (domain relation : A) :
    FOFormula.Satisfies E (canonicalGraphOutputFormula phi)
        (snoc (snoc params domain) relation) ↔
      ∀ pair : A, E pair relation ↔
        FOFormula.Satisfies E
          (DefinableRelationGraph.graphFormula phi)
          (snoc (snoc params domain) pair) := by
  simp only [canonicalGraphOutputFormula, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    FOFormula.satisfies_rename, snoc_last, snoc_castSucc,
    comp_canonicalGraphOutputRename]

/-- The Cartesian product of two constructible sets is constructible. -/
def prodLCarrier (x y : LCarrier.{u}) : LCarrier.{u} :=
  ⟨ZFSet.prod x.1 y.1, by
    simpa [Godel.op, Godel.F2] using
      (Godel.op_mem_L (i := (2 : Fin 9)) x.2 y.2)⟩

@[simp]
theorem prodLCarrier_val (x y : LCarrier.{u}) :
    (prodLCarrier x y).1 = ZFSet.prod x.1 y.1 := rfl

/-- The canonical Separation witness for a formula-defined binary relation. -/
def canonicalDefinableRelationGraph {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u}) :
    LCarrier.{u} :=
  Classical.choose
    (exists_separationLCarrier
      (DefinableRelationGraph.graphFormula phi)
      (snoc params domain) (prodLCarrier domain domain))

@[simp]
theorem mem_canonicalDefinableRelationGraph_iff {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain q : LCarrier.{u}) :
    q.1 ∈ (canonicalDefinableRelationGraph phi params domain).1 ↔
      ∃ x y : LCarrier.{u},
        x.1 ∈ domain.1 ∧ y.1 ∈ domain.1 ∧
          q.1 = ZFSet.pair x.1 y.1 ∧
          FOFormula.Satisfies
            (fun z w : LCarrier.{u} => z.1 ∈ w.1)
            phi (snoc (snoc params x) y) := by
  have hsep := Classical.choose_spec
    (exists_separationLCarrier
      (DefinableRelationGraph.graphFormula phi)
      (snoc params domain) (prodLCarrier domain domain)) q
  constructor
  · intro hq
    rcases hsep.mp hq with ⟨_hqProd, hformula⟩
    exact (DefinableRelationGraph.satisfies_graphFormula
      phi params domain q).mp hformula
  · rintro ⟨x, y, hx, hy, hq, hphi⟩
    apply hsep.mpr
    constructor
    · change q.1 ∈ ZFSet.prod domain.1 domain.1
      rw [hq, ZFSet.pair_mem_prod]
      exact ⟨hx, hy⟩
    · apply (DefinableRelationGraph.satisfies_graphFormula
        phi params domain q).mpr
      exact ⟨x, y, hx, hy, hq, hphi⟩

/-- The canonical graph represents exactly the intended relation on the
specified domain. -/
@[simp]
theorem graphRel_canonicalDefinableRelationGraph_iff {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain x y : LCarrier.{u}) :
    GraphRel (canonicalDefinableRelationGraph phi params domain) x y ↔
      x.1 ∈ domain.1 ∧ y.1 ∈ domain.1 ∧
        FOFormula.Satisfies
          (fun z w : LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc (snoc params x) y) := by
  change (orderedPairLCarrier x y).1 ∈
    (canonicalDefinableRelationGraph phi params domain).1 ↔ _
  rw [mem_canonicalDefinableRelationGraph_iff]
  constructor
  · rintro ⟨x', y', hx', hy', hpair, hphi⟩
    have hraw :
        ZFSet.pair x.1 y.1 = ZFSet.pair x'.1 y'.1 := by
      simpa only [orderedPairLCarrier_val] using hpair
    rcases ZFSet.pair_inj.mp hraw with ⟨hxEq, hyEq⟩
    have hxCarrier : x = x' := Subtype.ext hxEq
    have hyCarrier : y = y' := Subtype.ext hyEq
    subst x'
    subst y'
    exact ⟨hx', hy', hphi⟩
  · rintro ⟨hx, hy, hphi⟩
    exact ⟨x, y, hx, hy, rfl, hphi⟩

/-- Exact graph membership determines the canonical graph uniquely. -/
theorem eq_canonicalDefinableRelationGraph_of_mem_iff {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain relation : LCarrier.{u})
    (hexact : ∀ q : LCarrier.{u}, q.1 ∈ relation.1 ↔
      ∃ x y : LCarrier.{u},
        x.1 ∈ domain.1 ∧ y.1 ∈ domain.1 ∧
          q.1 = ZFSet.pair x.1 y.1 ∧
          FOFormula.Satisfies
            (fun z w : LCarrier.{u} => z.1 ∈ w.1)
            phi (snoc (snoc params x) y)) :
    relation = canonicalDefinableRelationGraph phi params domain := by
  apply lCarrier_extensionality
  intro q
  exact (hexact q).trans
    (mem_canonicalDefinableRelationGraph_iff phi params domain q).symm

/-- The object-language output specification identifies exactly the
canonical Separation graph. -/
theorem satisfies_canonicalGraphOutputFormula_iff_eq {n : Nat}
    (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain relation : LCarrier.{u}) :
    FOFormula.Satisfies
        (fun z w : LCarrier.{u} => z.1 ∈ w.1)
        (canonicalGraphOutputFormula phi)
        (snoc (snoc params domain) relation) ↔
      relation = canonicalDefinableRelationGraph phi params domain := by
  rw [satisfies_canonicalGraphOutputFormula]
  constructor
  · intro hexact
    apply eq_canonicalDefinableRelationGraph_of_mem_iff
    intro pair
    exact (hexact pair).trans
      (DefinableRelationGraph.satisfies_graphFormula
        phi params domain pair)
  · intro hrelation
    subst relation
    intro pair
    exact (mem_canonicalDefinableRelationGraph_iff
      phi params domain pair).trans
        (DefinableRelationGraph.satisfies_graphFormula
          phi params domain pair).symm



end

end Constructible.Model
end CUAdapterModule68



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.InitialSegmentOrder -/
section CUAdapterModule69
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Extending a well-order by a final block

This file contains the order-theoretic device used to keep successive
constructible-stage orders coherent.  A carrier is split into an old part
and its complement.  The old part is ordered first, the new part second.
Thus the old part is an initial segment by construction.
-/


universe u

namespace Constructible

noncomputable section

/-- Split a type into the subtype satisfying `p` and its complement. -/
def partitionEquiv {A : Type u} (p : A -> Prop) :
    A ≃ ({x : A // p x} ⊕ {x : A // Not (p x)}) := by
  classical
  refine
    { toFun := fun x =>
        if hx : p x then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, hx⟩
      invFun := fun
        | Sum.inl x => x.1
        | Sum.inr x => x.1
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    by_cases hx : p x <;> simp [hx]
  · intro x
    cases x with
    | inl x => simp [x.2]
    | inr x => simp [x.2]

/--
Lexicographically order the `p`-part before its complement, using the two
given relations inside the respective blocks.
-/
def partitionLexRel {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop) :
    A -> A -> Prop :=
  InvImage (Sum.Lex oldRel newRel) (partitionEquiv p)

theorem partitionLexRel_isWellOrder {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop)
    [IsWellOrder {x : A // p x} oldRel]
    [IsWellOrder {x : A // Not (p x)} newRel] :
    IsWellOrder A (partitionLexRel p oldRel newRel) := by
  letI : IsWellOrder
      ({x : A // p x} ⊕ {x : A // Not (p x)})
      (Sum.Lex oldRel newRel) := by
    infer_instance
  exact
    { wf := InvImage.wf (partitionEquiv p)
        (IsWellFounded.wf : WellFounded (Sum.Lex oldRel newRel))
      trichotomous :=
        (InvImage.trichotomous (r := Sum.Lex oldRel newRel)
          (partitionEquiv p).injective).trichotomous }

@[simp]
theorem partitionLexRel_old_old {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop)
    {x y : A} (hx : p x) (hy : p y) :
    partitionLexRel p oldRel newRel x y <->
      oldRel ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [partitionLexRel, partitionEquiv, hx, hy, InvImage]

@[simp]
theorem partitionLexRel_old_new {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop)
    {x y : A} (hx : p x) (hy : Not (p y)) :
    partitionLexRel p oldRel newRel x y := by
  simp [partitionLexRel, partitionEquiv, hx, hy, InvImage]

@[simp]
theorem partitionLexRel_new_old {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop)
    {x y : A} (hx : Not (p x)) (hy : p y) :
    Not (partitionLexRel p oldRel newRel x y) := by
  simp [partitionLexRel, partitionEquiv, hx, hy, InvImage]

@[simp]
theorem partitionLexRel_new_new {A : Type u} (p : A -> Prop)
    (oldRel : {x : A // p x} -> {x : A // p x} -> Prop)
    (newRel : {x : A // Not (p x)} ->
      {x : A // Not (p x)} -> Prop)
    {x y : A} (hx : Not (p x)) (hy : Not (p y)) :
    partitionLexRel p oldRel newRel x y <->
      newRel ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [partitionLexRel, partitionEquiv, hx, hy, InvImage]

end

end Constructible
end CUAdapterModule69



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryLeastProgramFormula -/
section CUAdapterModule70
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# The least-successful-program order on rudimentary values

This file combines the fixed postfix-program evaluator with the fixed
Shortlex program order.  The free-variable layout is

`[U, varTag, appTag, empty, op0, ..., op8, omega, relation, left, right]`.

The first fifteen coordinates are parameters.  The final two coordinates are
the values being compared, so the formula can be passed directly to the
definable-relation graph construction.  Internally it says

`exists p, Eval(p, left) and forall q, Eval(q, right) -> ProgramLt(p, q)`.

When the program order is a well-order and both values have successful
programs, this is equivalent to comparing their least successful programs.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

/-! ## Fixed layout and assignments -/

/-- The fifteen parameters shared by the least-program value relation. -/
def leastProgramValueLtParametersAssignment
    (U relation : ZFSet.{u}) : Tuple ZFSet.{u} 15 :=
  snoc
    (snoc (stackStepPrefixAssignment U) Ordinal.omega0.toZFSet)
    relation

/-- The intended raw assignment, with the compared values in the last slots. -/
def leastProgramValueLtAssignment
    (U relation left right : ZFSet.{u}) : Tuple ZFSet.{u} 17 :=
  snoc (snoc (leastProgramValueLtParametersAssignment U relation) left) right

/--
Select `[U, relation, varTag, appTag, empty, omega]` from the fifteen
least-program parameters.
-/
def rawStackProgramLtParameterRename : Fin 6 -> Fin 15 :=
  ![(0 : Fin 15), (14 : Fin 15), (1 : Fin 15), (2 : Fin 15),
    (3 : Fin 15), (13 : Fin 15)]

/-- The six fixed coordinates used by a raw program comparison. -/
def rawStackProgramLtPrefixAssignment
    (U relation : ZFSet.{u}) : Tuple ZFSet.{u} 6 :=
  fun i => leastProgramValueLtParametersAssignment U relation
    (rawStackProgramLtParameterRename i)

/-- The raw eight-coordinate assignment used by `stackProgramLtFormula`. -/
def rawStackProgramLtAssignment
    (U relation leftProgram rightProgram : ZFSet.{u}) : Tuple ZFSet.{u} 8 :=
  snoc (snoc (rawStackProgramLtPrefixAssignment U relation) leftProgram)
    rightProgram

/-! ## Renamings -/

/--
Embed `Eval(program, result)` into the context extended by the witness `p`.
The evaluator's fourteen fixed coordinates are unchanged, its program is `p`,
and its result is the left value at coordinate `15`.
-/
def leastProgramLeftEvalRename : Fin 16 -> Fin 18 :=
  Fin.lastCases (15 : Fin 18)
    (fun i14 => Fin.lastCases (17 : Fin 18)
      (fun i13 => i13.castSucc.castSucc.castSucc.castSucc) i14)

/--
Embed `Eval(program, result)` under the subsequent universal witness `q`.
Its program is `q` and its result is the right value at coordinate `16`.
-/
def leastProgramRightEvalRename : Fin 16 -> Fin 19 :=
  Fin.lastCases (16 : Fin 19)
    (fun i14 => Fin.lastCases (18 : Fin 19)
      (fun i13 =>
        i13.castSucc.castSucc.castSucc.castSucc.castSucc) i14)

/-- Embed the six fixed program-order coordinates into the large context. -/
def leastProgramOrderPrefixRename : Fin 6 -> Fin 19 :=
  fun i =>
    (rawStackProgramLtParameterRename i).castSucc.castSucc.castSucc.castSucc

/--
Embed the raw program comparison under both program witnesses.  In the
nineteen-coordinate context, `p` and `q` occupy coordinates `17` and `18`.
-/
def leastProgramOrderRename : Fin 8 -> Fin 19 :=
  Fin.lastCases (18 : Fin 19)
    (fun i7 => Fin.lastCases (17 : Fin 19)
      leastProgramOrderPrefixRename i7)

/-! ## Formula -/

/--
Compare values by their least successful postfix programs, expressed without
choosing a least program in the object language.
-/
def leastProgramValueLtFormula : FOFormula 17 :=
  .ex
    (.conj
      (FOFormula.rename leastProgramLeftEvalRename stackProgramEvalFormula)
      (.all
        (formulaImp
          (FOFormula.rename leastProgramRightEvalRename
            stackProgramEvalFormula)
          (FOFormula.rename leastProgramOrderRename
            stackProgramLtFormula))))

/-! ## Assignment computations -/

theorem comp_leastProgramLeftEvalRename
    (U relation left right p : ZFSet.{u}) :
    (fun i =>
      snoc (leastProgramValueLtAssignment U relation left right) p
        (leastProgramLeftEvalRename i)) =
      stackProgramEvalAssignment U p left := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · simp [leastProgramLeftEvalRename, leastProgramValueLtAssignment,
        leastProgramValueLtParametersAssignment, stackProgramEvalAssignment]

theorem comp_leastProgramRightEvalRename
    (U relation left right p q : ZFSet.{u}) :
    (fun i =>
      snoc
        (snoc (leastProgramValueLtAssignment U relation left right) p) q
        (leastProgramRightEvalRename i)) =
      stackProgramEvalAssignment U q right := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · simp [leastProgramRightEvalRename, leastProgramValueLtAssignment,
        leastProgramValueLtParametersAssignment, stackProgramEvalAssignment]

theorem comp_leastProgramOrderRename
    (U relation left right p q : ZFSet.{u}) :
    (fun i =>
      snoc
        (snoc (leastProgramValueLtAssignment U relation left right) p) q
        (leastProgramOrderRename i)) =
      rawStackProgramLtAssignment U relation p q := by
  funext i
  refine Fin.lastCases ?_ (fun i7 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i6 => ?_) i7
    · rfl
    · simp only [leastProgramOrderRename, Fin.lastCases_castSucc,
        leastProgramOrderPrefixRename, leastProgramValueLtAssignment,
        rawStackProgramLtAssignment, rawStackProgramLtPrefixAssignment,
        snoc_castSucc]

/-! ## Ambient raw semantic normal form -/



end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule70



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramOrderRepresented -/
section CUAdapterModule71
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Program order on arbitrary valid indexed representations

The first-order order formula compares the finite sequence represented by a
code.  It must therefore be insensitive to harmless extra graph entries in a
valid code, rather than being correct only for `sequenceCode` itself.
-/


open Set

universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open IndexedSequenceZF
open FiniteSequenceZF

local notation "LMem" => Model.lCarrierMem

/-- The fixed program-order layout with arbitrary sequence codes. -/
def stackProgramLtCodeAssignment (U relation leftCode rightCode : ZFSet.{u}) :
    Tuple ZFSet.{u} 8 :=
  ![U, relation, varTag, appTag, ∅, Ordinal.omega0.toZFSet,
    leftCode, rightCode]



/-! ## Constructible witnesses for represented sequences -/

 theorem pairRight_mem_L_of_pair_eq
    {sequence length graph : ZFSet.{u}} (hsequence : sequence ∈ L)
    (hcode : sequence = ZFSet.pair length graph) : graph ∈ L := by
  have hpairMem :
      ZFSet.pair length graph ∈ ({sequence} : ZFSet.{u}) := by
    simp only [ZFSet.mem_singleton]
    exact hcode.symm
  exact mem_L_of_mem (pair_right_mem_pairField hpairMem)
    (pairField_mem_L (singleton_mem_L hsequence))

/-- The graph component of a constructible represented code is constructible. -/
theorem representedGraph_mem_L
    {sequence : ZFSet.{u}} (hsequence : sequence ∈ L)
    {xs : List ZFSet.{u}} (hrep : Represents sequence xs) :
    ∃ graph : ZFSet.{u},
      sequence = ZFSet.pair (natCode xs.length) graph ∧
        (∀ k : Fin xs.length,
          ZFSet.pair (xs.get k) (natCode k.1) ∈ graph ∧
            ∀ value : ZFSet.{u},
              ZFSet.pair value (natCode k.1) ∈ graph →
                value = xs.get k) ∧
        graph ∈ L := by
  rcases hrep with ⟨graph, hcode, hgraph⟩
  exact ⟨graph, hcode, hgraph,
    pairRight_mem_L_of_pair_eq hsequence hcode⟩

 theorem representedLength_eq
    {sequence length graph : ZFSet.{u}} {xs : List ZFSet.{u}}
    (hrep : Represents sequence xs)
    (hpair : sequence = ZFSet.pair length graph) :
    length = natCode xs.length := by
  rcases hrep with ⟨representedGraph, hcode, _hgraph⟩
  have hpairs :
      ZFSet.pair (natCode xs.length) representedGraph =
        ZFSet.pair length graph := hcode.symm.trans hpair
  exact (ZFSet.pair_inj.mp hpairs).1.symm

/-- Any constructible representation with constructible entries is valid in `L`. -/
theorem satisfies_sequenceValidity_represents_lCarrier
    (sequence : Model.LCarrier.{u}) {xs : List ZFSet.{u}}
    (hrep : Represents sequence.1 xs) (hxs : ∀ x ∈ xs, x ∈ L) :
    FOFormula.Satisfies LMem sequenceValidityFormula
      ![⟨Ordinal.omega0.toZFSet, omega_mem_L⟩, sequence] := by
  rw [satisfies_sequenceValidityFormula_lCarrier]
  rcases representedGraph_mem_L sequence.2 hrep with
    ⟨graph, hcode, hgraph, hgraphL⟩
  let length : Model.LCarrier.{u} :=
    ⟨natCode xs.length, natCode_mem_L xs.length⟩
  let graphCarrier : Model.LCarrier.{u} := ⟨graph, hgraphL⟩
  refine ⟨length, graphCarrier, hcode, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 xs.length)
  · intro index hindex
    rcases (mem_natCode_iff index.1 xs.length).mp hindex with
      ⟨k, hk, hindexEq⟩
    let i : Fin xs.length := ⟨k, hk⟩
    have hvalueL : xs.get i ∈ L := hxs _ (List.get_mem xs i)
    let value : Model.LCarrier.{u} := ⟨xs.get i, hvalueL⟩
    refine ⟨value, ?_, ?_⟩
    · simpa only [i, hindexEq, value, graphCarrier] using (hgraph i).1
    · intro other hother
      have hunique := (hgraph i).2 other.1
        (by simpa only [i, hindexEq, graphCarrier] using hother)
      simpa only [value] using hunique

set_option maxHeartbeats 250000 in
-- Kernel checking of the three-coordinate subtype assignment needs a small
-- margin above the default budget; the proof itself is finite-case.
theorem satisfies_valueAtFormula_represents_lCarrier_iff
    (sequence : Model.LCarrier.{u}) {xs : List ZFSet.{u}}
    (hrep : Represents sequence.1 xs) (k : Nat)
    (value : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem valueAtFormula
        ![sequence, ⟨natCode k, natCode_mem_L k⟩, value] ↔
      ∃ hk : k < xs.length, value.1 = xs.get ⟨k, hk⟩ := by
  rw [valueAtFormula, Delta0Formula.satisfies_toFO_lCarrier_absolute]
  have hvals :
      (fun i =>
        (![sequence, ⟨natCode k, natCode_mem_L k⟩, value] i).1) =
        ![sequence.1, natCode k, value.1] := by
    funext i
    fin_cases i <;> rfl
  rw [hvals, Delta0Formula.satisfies_toFO]
  exact satisfies_valueAt_represents_iff hrep k value.1

 theorem satisfies_hasLengthFormula_represents_lCarrier_sound
    (sequence : Model.LCarrier.{u}) {xs : List ZFSet.{u}}
    (hrep : Represents sequence.1 xs)
    (length : Model.LCarrier.{u})
    (h : FOFormula.Satisfies LMem hasLengthFormula ![sequence, length]) :
    length.1 = natCode xs.length := by
  simp only [hasLengthFormula, FOFormula.Satisfies] at h
  rcases h with ⟨graphCarrier, hpair⟩
  have hpairRaw :=
    (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.kuratowskiPairEqAt 0 1 2)
      (snoc ![sequence, length] graphCarrier)).mp hpair
  rw [Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt] at hpairRaw
  have hpairRaw' :
      sequence.1 = ZFSet.pair length.1 graphCarrier.1 := by
    change sequence.1 = ZFSet.pair length.1 graphCarrier.1 at hpairRaw
    exact hpairRaw
  exact representedLength_eq hrep hpairRaw'

 theorem representedLengthGraphCarrier
    (sequence : Model.LCarrier.{u}) {xs : List ZFSet.{u}}
    (hrep : Represents sequence.1 xs)
    (length : Model.LCarrier.{u})
    (hlength : length.1 = natCode xs.length) :
    ∃ graphCarrier : Model.LCarrier.{u},
      sequence.1 = ZFSet.pair length.1 graphCarrier.1 := by
  rcases hrep with ⟨graph, hcode, _hgraph⟩
  have hgraphL : graph ∈ L :=
    pairRight_mem_L_of_pair_eq sequence.2 hcode
  let graphCarrier : Model.LCarrier.{u} := ⟨graph, hgraphL⟩
  refine ⟨graphCarrier, ?_⟩
  simpa only [graphCarrier, hlength] using hcode

theorem satisfies_hasLengthFormula_represents_lCarrier_iff
    (sequence : Model.LCarrier.{u}) {xs : List ZFSet.{u}}
    (hrep : Represents sequence.1 xs)
    (length : Model.LCarrier.{u}) :
    FOFormula.Satisfies LMem hasLengthFormula ![sequence, length] ↔
      length.1 = natCode xs.length := by
  constructor
  · exact satisfies_hasLengthFormula_represents_lCarrier_sound
      sequence hrep length
  · intro hlength
    rcases representedLengthGraphCarrier sequence hrep length hlength with
      ⟨graphCarrier, hpair⟩
    simp only [hasLengthFormula, FOFormula.Satisfies]
    refine ⟨graphCarrier, ?_⟩
    apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (Delta0Formula.kuratowskiPairEqAt 0 1 2)
      (snoc ![sequence, length] graphCarrier)).mpr
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_kuratowskiPairEqAt]
    change sequence.1 = ZFSet.pair length.1 graphCarrier.1
    exact hpair

theorem satisfies_samePrefix_represents_lCarrier_iff
    (leftSequence rightSequence : Model.LCarrier.{u})
    {xs ys : List ZFSet.{u}}
    (hleft : Represents leftSequence.1 xs)
    (hright : Represents rightSequence.1 ys)
    (hxs : ∀ x ∈ xs, x ∈ L) (_hys : ∀ y ∈ ys, y ∈ L)
    (k : Nat) :
    FOFormula.Satisfies LMem samePrefixFormula
        ![leftSequence, rightSequence,
          ⟨natCode k, natCode_mem_L k⟩] ↔
      ∀ j : Nat, j < k →
        ∃ hx : j < xs.length, ∃ hy : j < ys.length,
          xs.get ⟨j, hx⟩ = ys.get ⟨j, hy⟩ := by
  constructor
  · intro h
    have hnormal :=
      (satisfies_samePrefixFormula_lCarrier leftSequence rightSequence
        ⟨natCode k, natCode_mem_L k⟩).mp h
    intro j hj
    let index : Model.LCarrier.{u} := ⟨natCode j, natCode_mem_L j⟩
    rcases hnormal index ((mem_natCode_iff _ _).mpr ⟨j, hj, rfl⟩) with
      ⟨value, hleftValue, hrightValue⟩
    rcases (satisfies_valueAtFormula_represents_lCarrier_iff
      leftSequence hleft j value).mp
        (by simpa only [index] using hleftValue) with
      ⟨hx, hvalueX⟩
    rcases (satisfies_valueAtFormula_represents_lCarrier_iff
      rightSequence hright j value).mp
        (by simpa only [index] using hrightValue) with
      ⟨hy, hvalueY⟩
    exact ⟨hx, hy, hvalueX.symm.trans hvalueY⟩
  · intro h
    apply (satisfies_samePrefixFormula_lCarrier leftSequence rightSequence
      ⟨natCode k, natCode_mem_L k⟩).mpr
    intro index hindex
    rcases (mem_natCode_iff index.1 k).mp hindex with
      ⟨j, hj, hindexEq⟩
    rcases h j hj with ⟨hx, hy, hxy⟩
    let indexJ : Model.LCarrier.{u} := ⟨natCode j, natCode_mem_L j⟩
    have hindexCarrier : index = indexJ := Subtype.ext hindexEq
    have hvalueL : xs.get ⟨j, hx⟩ ∈ L :=
      hxs _ (List.get_mem xs ⟨j, hx⟩)
    let value : Model.LCarrier.{u} := ⟨xs.get ⟨j, hx⟩, hvalueL⟩
    refine ⟨value, ?_, ?_⟩
    · have hvalue :=
        (satisfies_valueAtFormula_represents_lCarrier_iff
          leftSequence hleft j value).mpr ⟨hx, rfl⟩
      simpa only [hindexCarrier, indexJ] using hvalue
    · have hvalue :=
        (satisfies_valueAtFormula_represents_lCarrier_iff
          rightSequence hright j value).mpr ⟨hy, hxy⟩
      simpa only [hindexCarrier, indexJ, value] using hvalue

/-! ## Restricted Shortlex on arbitrary representations -/

/-- Arbitrary constructible program-code assignments over `LCarrier`. -/
def stackProgramLtCodeLAssignment
    (U relation leftCode rightCode : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (hleftCode : leftCode ∈ L) (hrightCode : rightCode ∈ L) :
    Tuple Model.LCarrier.{u} 8 :=
  ![⟨U, hU⟩, ⟨relation, hrelation⟩,
    ⟨varTag, varTag_mem_L⟩, ⟨appTag, appTag_mem_L⟩,
    ⟨∅, empty_mem_L⟩, ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩,
    ⟨leftCode, hleftCode⟩, ⟨rightCode, hrightCode⟩]

theorem stackProgramLtCodeLAssignment_val
    (U relation leftCode rightCode : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (hleftCode : leftCode ∈ L) (hrightCode : rightCode ∈ L) :
    (fun i => (stackProgramLtCodeLAssignment U relation leftCode rightCode
      hU hrelation hleftCode hrightCode i).1) =
      stackProgramLtCodeAssignment U relation leftCode rightCode := by
  funext i
  fin_cases i <;> rfl

theorem satisfies_stackProgramLtFormula_represents_lCarrier_iff
    (U relation leftCode rightCode : ZFSet.{u})
    (hU : U ∈ L) (hrelation : relation ∈ L)
    (hleftCode : leftCode ∈ L) (hrightCode : rightCode ∈ L)
    (left right : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (hleft : Represents leftCode (encodedStackProgram U left))
    (hright : Represents rightCode (encodedStackProgram U right)) :
    FOFormula.Satisfies LMem stackProgramLtFormula
        (stackProgramLtCodeLAssignment U relation leftCode rightCode
          hU hrelation hleftCode hrightCode) ↔
      stackProgramRel (generatorTokenRel U relation) left right := by
  let params : Tuple Model.LCarrier.{u} 5 :=
    ![⟨U, hU⟩, ⟨relation, hrelation⟩,
      ⟨varTag, varTag_mem_L⟩, ⟨appTag, appTag_mem_L⟩,
      ⟨∅, empty_mem_L⟩]
  let xs := encodedStackProgram U left
  let ys := encodedStackProgram U right
  have hxs : ∀ x ∈ xs, x ∈ L := by
    simpa only [xs, encodedStackProgram] using stackTokenCodes_mem_L hU left
  have hys : ∀ y ∈ ys, y ∈ L := by
    simpa only [ys, encodedStackProgram] using stackTokenCodes_mem_L hU right
  let leftCarrier : Model.LCarrier.{u} := ⟨leftCode, hleftCode⟩
  let rightCarrier : Model.LCarrier.{u} := ⟨rightCode, hrightCode⟩
  have hassignment :
      stackProgramLtCodeLAssignment U relation leftCode rightCode
          hU hrelation hleftCode hrightCode =
        snoc (snoc
          (snoc params ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩)
          leftCarrier) rightCarrier := by
    funext i
    fin_cases i <;> rfl
  rw [stackProgramLtFormula]
  rw [hassignment]
  rw [satisfies_shortlexFormula_lCarrier]
  have hvalidLeft := satisfies_sequenceValidity_represents_lCarrier
    leftCarrier hleft hxs
  have hvalidRight := satisfies_sequenceValidity_represents_lCarrier
    rightCarrier hright hys
  constructor
  · rintro ⟨_hvl, _hvr, leftLength, rightLength,
      hleftLength, hrightLength, hshort⟩
    have hleftLengthEq :=
      (satisfies_hasLengthFormula_represents_lCarrier_iff
        leftCarrier hleft leftLength).mp
        (by simpa only [params, leftCarrier, rightCarrier,
          stackProgramLtCodeLAssignment] using hleftLength)
    have hrightLengthEq :=
      (satisfies_hasLengthFormula_represents_lCarrier_iff
        rightCarrier hright rightLength).mp
        (by simpa only [params, leftCarrier, rightCarrier,
          stackProgramLtCodeLAssignment] using hrightLength)
    have hshortlex : List.Shortlex
        (lCarrierFormulaRel stackTokenLtFormula params) xs ys := by
      rcases hshort with hlen | ⟨hlengthCarrier, index, hindex,
          hprefix, leftValue, rightValue, hleftValue,
          hrightValue, hlt⟩
      · apply List.Shortlex.of_length_lt
        apply (natCode_mem_natCode_iff xs.length ys.length).mp
        simpa only [hleftLengthEq, hrightLengthEq] using hlen
      · have hlengthCode : natCode xs.length = natCode ys.length :=
          hleftLengthEq.symm.trans
            ((congrArg Subtype.val hlengthCarrier).trans hrightLengthEq)
        have hlength : xs.length = ys.length := natCode_injective hlengthCode
        rcases (mem_natCode_iff index.1 xs.length).mp
            (by simpa only [hleftLengthEq] using hindex) with
          ⟨k, hk, hindexEq⟩
        let indexK : Model.LCarrier.{u} := ⟨natCode k, natCode_mem_L k⟩
        have hindexCarrier : index = indexK := Subtype.ext hindexEq
        have hpoint :=
          (satisfies_samePrefix_represents_lCarrier_iff
            leftCarrier rightCarrier hleft hright hxs hys k).mp
            (by simpa only [params, leftCarrier, rightCarrier,
              hindexCarrier, indexK, stackProgramLtCodeLAssignment]
              using hprefix)
        have htake : xs.take k = ys.take k :=
          (take_eq_take_iff_pointwise xs ys k hk.le
            (by rw [← hlength]; exact hk.le)).mpr hpoint
        rcases (satisfies_valueAtFormula_represents_lCarrier_iff
          leftCarrier hleft k leftValue).mp
            (by simpa only [params, leftCarrier, rightCarrier,
              hindexCarrier, indexK, stackProgramLtCodeLAssignment]
              using hleftValue) with
          ⟨hkx, hleftValueEq⟩
        rcases (satisfies_valueAtFormula_represents_lCarrier_iff
          rightCarrier hright k rightValue).mp
            (by simpa only [params, leftCarrier, rightCarrier,
              hindexCarrier, indexK, stackProgramLtCodeLAssignment]
              using hrightValue) with
          ⟨hky, hrightValueEq⟩
        apply List.Shortlex.of_lex hlength
        apply (listLex_iff_exists_index hlength).mpr
        exact ⟨k, hkx, hky, htake,
          ⟨leftValue, rightValue, hleftValueEq, hrightValueEq,
            by simpa only [params, stackProgramLtCodeLAssignment]
              using hlt⟩⟩
    have htoken : ∀ leftToken rightToken : StackToken
        (Option (Constructible.ZFCarrier U)),
        lCarrierFormulaRel stackTokenLtFormula params
            (stackTokenZFCode U leftToken) (stackTokenZFCode U rightToken) ↔
          stackTokenRel (generatorTokenRel U relation)
            leftToken rightToken := by
      intro leftToken rightToken
      constructor
      · rintro ⟨leftValue, rightValue, hl, hr, hlt⟩
        have hrestricted :=
          (satisfies_stackTokenLtFormula_lCarrier_tokenCodes
            U relation hU hrelation leftToken rightToken).mp
            (by
              have hlc : leftValue =
                  ⟨stackTokenZFCode U leftToken,
                    stackTokenZFCode_mem_L hU leftToken⟩ := Subtype.ext hl
              have hrc : rightValue =
                  ⟨stackTokenZFCode U rightToken,
                    stackTokenZFCode_mem_L hU rightToken⟩ := Subtype.ext hr
              rw [hlc, hrc] at hlt
              change FOFormula.Satisfies LMem stackTokenLtFormula
                (stackTokenLtLAssignment U relation hU hrelation
                  leftToken rightToken) at hlt
              exact hlt)
        exact hrestricted
      · intro hlt
        let leftValue : Model.LCarrier.{u} :=
          ⟨stackTokenZFCode U leftToken,
            stackTokenZFCode_mem_L hU leftToken⟩
        let rightValue : Model.LCarrier.{u} :=
          ⟨stackTokenZFCode U rightToken,
            stackTokenZFCode_mem_L hU rightToken⟩
        refine ⟨leftValue, rightValue, rfl, rfl, ?_⟩
        have hrestricted :=
          (satisfies_stackTokenLtFormula_lCarrier_tokenCodes
            U relation hU hrelation leftToken rightToken).mpr hlt
        change FOFormula.Satisfies LMem stackTokenLtFormula
          (snoc (snoc params leftValue) rightValue) at hrestricted
        exact hrestricted
    simpa only [xs, ys, stackProgramRel] using
      (listShortlex_map_iff (stackTokenZFCode U)
        (stackTokenZFCode_injective U) htoken left right).mp hshortlex
  · intro hprogramLt
    have htoken : ∀ leftToken rightToken : StackToken
        (Option (Constructible.ZFCarrier U)),
        lCarrierFormulaRel stackTokenLtFormula params
            (stackTokenZFCode U leftToken) (stackTokenZFCode U rightToken) ↔
          stackTokenRel (generatorTokenRel U relation)
            leftToken rightToken := by
      intro leftToken rightToken
      constructor
      · rintro ⟨leftValue, rightValue, hl, hr, hlt⟩
        apply (satisfies_stackTokenLtFormula_lCarrier_tokenCodes
          U relation hU hrelation leftToken rightToken).mp
        have hlc : leftValue =
            ⟨stackTokenZFCode U leftToken,
              stackTokenZFCode_mem_L hU leftToken⟩ := Subtype.ext hl
        have hrc : rightValue =
            ⟨stackTokenZFCode U rightToken,
              stackTokenZFCode_mem_L hU rightToken⟩ := Subtype.ext hr
        rw [hlc, hrc] at hlt
        change FOFormula.Satisfies LMem stackTokenLtFormula
          (stackTokenLtLAssignment U relation hU hrelation
            leftToken rightToken) at hlt
        exact hlt
      · intro hlt
        let leftValue : Model.LCarrier.{u} :=
          ⟨stackTokenZFCode U leftToken,
            stackTokenZFCode_mem_L hU leftToken⟩
        let rightValue : Model.LCarrier.{u} :=
          ⟨stackTokenZFCode U rightToken,
            stackTokenZFCode_mem_L hU rightToken⟩
        refine ⟨leftValue, rightValue, rfl, rfl, ?_⟩
        have hrestricted :=
          (satisfies_stackTokenLtFormula_lCarrier_tokenCodes
            U relation hU hrelation leftToken rightToken).mpr hlt
        change FOFormula.Satisfies LMem stackTokenLtFormula
          (snoc (snoc params leftValue) rightValue) at hrestricted
        exact hrestricted
    have hshortlex :
        List.Shortlex (lCarrierFormulaRel stackTokenLtFormula params) xs ys := by
      apply (listShortlex_map_iff (stackTokenZFCode U)
        (stackTokenZFCode_injective U) htoken left right).mpr
      exact hprogramLt
    refine ⟨?_, ?_,
      ⟨natCode xs.length, natCode_mem_L xs.length⟩,
      ⟨natCode ys.length, natCode_mem_L ys.length⟩, ?_, ?_, ?_⟩
    · simpa only [params, leftCarrier, stackProgramLtCodeLAssignment] using
        hvalidLeft
    · simpa only [params, rightCarrier, stackProgramLtCodeLAssignment] using
        hvalidRight
    · have hlen :=
        (satisfies_hasLengthFormula_represents_lCarrier_iff
          leftCarrier hleft
          ⟨natCode xs.length, natCode_mem_L xs.length⟩).mpr rfl
      simpa only [params, leftCarrier, rightCarrier,
        stackProgramLtCodeLAssignment] using hlen
    · have hlen :=
        (satisfies_hasLengthFormula_represents_lCarrier_iff
          rightCarrier hright
          ⟨natCode ys.length, natCode_mem_L ys.length⟩).mpr rfl
      simpa only [params, leftCarrier, rightCarrier,
        stackProgramLtCodeLAssignment] using hlen
    · rcases List.shortlex_def.mp hshortlex with hlen | ⟨hlen, hlex⟩
      · apply Or.inl
        exact (natCode_mem_natCode_iff xs.length ys.length).mpr hlen
      · apply Or.inr
        refine ⟨Subtype.ext (congrArg natCode hlen), ?_⟩
        rcases (listLex_iff_exists_index hlen).mp hlex with
          ⟨k, hkx, hky, htake, hrelationAt⟩
        rcases hrelationAt with
          ⟨leftValue, rightValue, hleftValueEq, hrightValueEq, hlt⟩
        let index : Model.LCarrier.{u} := ⟨natCode k, natCode_mem_L k⟩
        refine ⟨index, (mem_natCode_iff _ _).mpr ⟨k, hkx, rfl⟩,
          ?_, leftValue, rightValue, ?_, ?_, ?_⟩
        · have hprefix :=
            (satisfies_samePrefix_represents_lCarrier_iff
              leftCarrier rightCarrier hleft hright hxs hys k).mpr
              ((take_eq_take_iff_pointwise xs ys k hkx.le hky.le).mp htake)
          simpa only [params, leftCarrier, rightCarrier, index,
            stackProgramLtCodeLAssignment] using hprefix
        · have hvalue :=
            (satisfies_valueAtFormula_represents_lCarrier_iff
              leftCarrier hleft k leftValue).mpr
              ⟨hkx, hleftValueEq⟩
          simpa only [params, leftCarrier, rightCarrier, index,
            stackProgramLtCodeLAssignment] using hvalue
        · have hvalue :=
            (satisfies_valueAtFormula_represents_lCarrier_iff
              rightCarrier hright k rightValue).mpr
              ⟨hky, hrightValueEq⟩
          simpa only [params, leftCarrier, rightCarrier, index,
            stackProgramLtCodeLAssignment] using hvalue
        · simpa only [params, stackProgramLtCodeLAssignment] using hlt



end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule71



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryLeastProgramSemantics -/
section CUAdapterModule72
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Semantics of the least-successful-program value order

The formula from `RudimentaryLeastProgramFormula` quantifies over arbitrary
set codes.  Evaluator satisfaction first decodes such a code to a genuine
postfix program; represented-code invariance of the program-order formula then
compares those decoded programs.  This proves that the formula is exactly the
existing `defCarrierStackRel` defined using `leastStackProgram`.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

/-! ## Assignment compatibility -/

/-- The raw comparison assignment used by the combined formula is the general
represented-code assignment used by the program-order semantics theorem. -/
@[simp]
theorem rawStackProgramLtAssignment_eq_codeAssignment
    (U relation leftCode rightCode : ZFSet.{u}) :
    rawStackProgramLtAssignment U relation leftCode rightCode =
      stackProgramLtCodeAssignment U relation leftCode rightCode := by
  funext i
  fin_cases i <;> rfl

/-! ## Minimality of successful programs -/





/-! ## Exact ambient semantics -/



end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule72



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.MinimalStage -/
section CUAdapterModule73
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Minimal constructible stages

Every constructible set has a least stage at which it occurs.  That stage is
never zero or a limit, hence is a successor.  Its predecessor is the canonical
stage over which the set receives a `DefZF` (equivalently, Gödel-operation)
representation.
-/


open Set

universe u

namespace Constructible

/-- The least constructible stage containing `x`. -/
noncomputable def firstStage (x : ZFSet.{u}) (_hx : x ∈ L) : Ordinal.{u} :=
  sInf {alpha : Ordinal.{u} | x ∈ LStageZF alpha}

/-- The set of stages containing a constructible set is nonempty. -/
theorem firstStage_indexSet_nonempty (x : ZFSet.{u}) (hx : x ∈ L) :
    ({alpha : Ordinal.{u} | x ∈ LStageZF alpha} : Set Ordinal).Nonempty := by
  rcases hx with ⟨alpha, hxa⟩
  exact ⟨alpha, hxa⟩

/-- A constructible set belongs to its least occurrence stage. -/
theorem mem_LStageZF_firstStage (x : ZFSet.{u}) (hx : x ∈ L) :
    x ∈ LStageZF (firstStage x hx) := by
  exact csInf_mem (firstStage_indexSet_nonempty x hx)

/-- The least occurrence stage lies below every other occurrence stage. -/
theorem firstStage_le {x : ZFSet.{u}} (hx : x ∈ L)
    {alpha : Ordinal.{u}} (hxa : x ∈ LStageZF alpha) :
    firstStage x hx ≤ alpha := by
  exact csInf_le' hxa

/-- No strictly earlier stage contains `x`. -/
theorem not_mem_LStageZF_of_lt_firstStage {x : ZFSet.{u}} (hx : x ∈ L)
    {alpha : Ordinal.{u}} (halpha : alpha < firstStage x hx) :
    x ∉ LStageZF alpha := by
  intro hxa
  have hnot : alpha ∉
      ({beta : Ordinal.{u} | x ∈ LStageZF beta} : Set Ordinal.{u}) :=
    notMem_of_lt_csInf' halpha
  exact hnot hxa

/-- The first occurrence stage of a constructible set is nonzero. -/
theorem firstStage_ne_zero (x : ZFSet.{u}) (hx : x ∈ L) :
    firstStage x hx ≠ 0 := by
  intro hzero
  have hmem := mem_LStageZF_firstStage x hx
  rw [hzero, LStageZF_zero] at hmem
  exact ZFSet.notMem_empty x hmem

/-- The first occurrence stage cannot be a nonzero limit. -/
theorem not_isSuccLimit_firstStage (x : ZFSet.{u}) (hx : x ∈ L) :
    Not (Order.IsSuccLimit (firstStage x hx)) := by
  intro hlimit
  rcases (mem_LStageZF_limit_iff hlimit).mp
      (mem_LStageZF_firstStage x hx) with
    ⟨alpha, halpha, hxa⟩
  exact not_mem_LStageZF_of_lt_firstStage hx halpha hxa

/-- The least occurrence stage is a successor ordinal. -/
theorem exists_firstStage_eq_succ (x : ZFSet.{u}) (hx : x ∈ L) :
    exists alpha : Ordinal.{u}, firstStage x hx = Order.succ alpha := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit (firstStage x hx) with
    hzero | hsucc | hlimit
  · exact False.elim (firstStage_ne_zero x hx hzero)
  · rcases hsucc with ⟨alpha, halpha⟩
    exact ⟨alpha, halpha.symm⟩
  · exact False.elim (not_isSuccLimit_firstStage x hx hlimit)

/-- The predecessor of the first stage containing `x`. -/
noncomputable def birthStage (x : ZFSet.{u}) (hx : x ∈ L) : Ordinal.{u} :=
  Classical.choose (exists_firstStage_eq_succ x hx)

@[simp]
theorem firstStage_eq_succ_birthStage (x : ZFSet.{u}) (hx : x ∈ L) :
    firstStage x hx = Order.succ (birthStage x hx) :=
  Classical.choose_spec (exists_firstStage_eq_succ x hx)

/-- Every constructible set is definable over its canonical birth stage. -/
theorem mem_DefZF_birthStage (x : ZFSet.{u}) (hx : x ∈ L) :
    x ∈ DefZF (LStageZF (birthStage x hx)) := by
  rw [← LStageZF_succ, ← firstStage_eq_succ_birthStage]
  exact mem_LStageZF_firstStage x hx



/-- Every member of `L_alpha` was born strictly before `alpha`. -/
theorem birthStage_lt_of_mem_LStageZF {x : ZFSet.{u}} {alpha : Ordinal.{u}}
    (hx : x ∈ LStageZF alpha) :
    birthStage x (LStageZF_subset_constructibleUniverse alpha hx) < alpha := by
  have hfirst := firstStage_le
    (LStageZF_subset_constructibleUniverse alpha hx) hx
  rw [firstStage_eq_succ_birthStage] at hfirst
  exact Order.succ_le_iff.mp hfirst

/-- The stage `L_alpha` first occurs as an element at stage `alpha + 1`. -/
theorem firstStage_LStageZF (alpha : Ordinal.{u}) :
    firstStage (LStageZF alpha) (LStageZF_mem_L alpha) = Order.succ alpha := by
  apply le_antisymm
  · apply firstStage_le (LStageZF_mem_L alpha)
    exact LStageZF_mem_succ alpha
  · apply Order.succ_le_of_lt
    by_contra hnot
    have hle : firstStage (LStageZF alpha) (LStageZF_mem_L alpha) ≤ alpha :=
      le_of_not_gt hnot
    have hself : LStageZF alpha ∈ LStageZF alpha :=
      LStageZF_mono hle
        (mem_LStageZF_firstStage (LStageZF alpha) (LStageZF_mem_L alpha))
    exact ZFSet.mem_irrefl _ hself

@[simp]
theorem birthStage_LStageZF (alpha : Ordinal.{u}) :
    birthStage (LStageZF alpha) (LStageZF_mem_L alpha) = alpha := by
  apply Order.succ_injective
  calc
    Order.succ (birthStage (LStageZF alpha) (LStageZF_mem_L alpha)) =
        firstStage (LStageZF alpha) (LStageZF_mem_L alpha) :=
      (firstStage_eq_succ_birthStage
        (LStageZF alpha) (LStageZF_mem_L alpha)).symm
    _ = Order.succ alpha := firstStage_LStageZF alpha

/-- The birth stage is independent of the proof of constructibility. -/
theorem birthStage_proof_irrel (x : ZFSet.{u}) (hx hy : x ∈ L) :
    birthStage x hx = birthStage x hy := by
  apply Order.succ_injective
  calc
    Order.succ (birthStage x hx) = firstStage x hx :=
      (firstStage_eq_succ_birthStage x hx).symm
    _ = firstStage x hy := by rfl
    _ = Order.succ (birthStage x hy) :=
      firstStage_eq_succ_birthStage x hy

end Constructible
end CUAdapterModule73



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.StageOrder -/
section CUAdapterModule74
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# External birth-layer orders for constructible stages

This file decomposes each constructible stage into the disjoint layers of
sets born at earlier ordinals.  A well-order on each layer can then be combined
lexicographically and transported back to the stage carrier.

All orders in this file are external Lean relations.  No claim is made here
that their graphs are internally represented `ZFSet`s or belong to `L`.
-/


open Set

universe u v

namespace Constructible

/-! ## Birth layers -/

/-- Constructible sets whose canonical birth stage is exactly `alpha`. -/
def BornAt (alpha : Ordinal.{u}) :=
  {x : ZFSet.{u} //
    ∃ hx : x ∈ L, birthStage x hx = alpha}



namespace BornAt

theorem mem_L {alpha : Ordinal.{u}} (x : BornAt alpha) : x.1 ∈ L :=
  Classical.choose x.2

@[simp]
theorem birthStage_eq {alpha : Ordinal.{u}} (x : BornAt alpha) :
    birthStage x.1 x.mem_L = alpha :=
  Classical.choose_spec x.2

theorem mem_LStageZF_succ {alpha : Ordinal.{u}} (x : BornAt alpha) :
    x.1 ∈ LStageZF (Order.succ alpha) := by
  rw [LStageZF_succ]
  have hx := mem_DefZF_birthStage x.1 x.mem_L
  simpa only [x.birthStage_eq] using hx







end BornAt





/-! ## The local least-term order -/





/-! ## Decomposing a stage by birth ordinal -/

/-- The ordinary subtype carrier of the internally represented stage. -/
abbrev LStageCarrier (alpha : Ordinal.{u}) :=
  ZFCarrier (LStageZF alpha)

/-- The dependent sum of all birth layers indexed below `alpha`. -/
abbrev BirthLayers (alpha : Ordinal.{u}) :=
  Σ' beta : Set.Iio alpha, BornAt beta.1

/-- Send a member of `L_alpha` to its canonical birth layer. -/
noncomputable def toBirthLayers (alpha : Ordinal.{u}) :
    LStageCarrier alpha → BirthLayers alpha :=
  fun x =>
    let hxL : x.1 ∈ L :=
      LStageZF_subset_constructibleUniverse alpha x.2
    ⟨⟨birthStage x.1 hxL, birthStage_lt_of_mem_LStageZF x.2⟩,
      ⟨x.1, ⟨hxL, rfl⟩⟩⟩

/-- Forget the birth index and include the layer into `L_alpha`. -/
def fromBirthLayers (alpha : Ordinal.{u}) :
    BirthLayers alpha → LStageCarrier alpha
  | ⟨beta, x⟩ =>
      ⟨x.1, LStageZF_mono (Order.succ_le_of_lt beta.2)
        x.mem_LStageZF_succ⟩

@[simp]
theorem fromBirthLayers_toBirthLayers (alpha : Ordinal.{u})
    (x : LStageCarrier alpha) :
    fromBirthLayers alpha (toBirthLayers alpha x) = x := by
  apply Subtype.ext
  rfl

 theorem bornAt_heq_of_eq {beta gamma : Ordinal.{u}}
    (hbg : beta = gamma) (x : BornAt beta) (y : BornAt gamma)
    (hxy : x.1 = y.1) : HEq x y := by
  subst gamma
  exact heq_of_eq (Subtype.ext hxy)

@[simp]
theorem toBirthLayers_fromBirthLayers (alpha : Ordinal.{u})
    (x : BirthLayers alpha) :
    toBirthLayers alpha (fromBirthLayers alpha x) = x := by
  rcases x with ⟨beta, x⟩
  have hbirth :
      birthStage x.1
          (LStageZF_subset_constructibleUniverse alpha
            (fromBirthLayers alpha ⟨beta, x⟩).2) = beta.1 := by
    calc
      birthStage x.1
          (LStageZF_subset_constructibleUniverse alpha
            (fromBirthLayers alpha ⟨beta, x⟩).2) =
          birthStage x.1 x.mem_L :=
        birthStage_proof_irrel _ _ _
      _ = beta.1 := x.birthStage_eq
  have hindex :
      (toBirthLayers alpha (fromBirthLayers alpha ⟨beta, x⟩)).1 = beta :=
    Subtype.ext hbirth
  apply PSigma.ext hindex
  exact bornAt_heq_of_eq hbirth _ _ rfl



/-! ## Lexicographically combining external layer orders -/











end Constructible
end CUAdapterModule74



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.CanonicalStageOrder -/
section CUAdapterModule75
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Canonical external orders on constructible stages

The order on a birth layer must use the already constructed order on the
preceding stage, rather than an unrelated application of external Choice.
This file performs that well-founded recursion on the birth ordinal.

The resulting relations are still external Lean predicates.  Their
Kuratowski-pair graphs must subsequently be shown constructible; no such
internalization claim is made here.
-/


open Set

universe u

namespace Constructible

/-! ## Adding the distinguished stage generator -/

/-- Identify `Option A` with a singleton placed before `A`. -/
def optionSumEquiv (A : Type u) : Option A ≃ Unit ⊕ A where
  toFun
    | none => Sum.inl ()
    | some x => Sum.inr x
  invFun
    | Sum.inl _ => none
    | Sum.inr x => some x
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- Put the distinguished `none` generator before all ordinary generators. -/
def optionPrependRel {A : Type u} (r : A -> A -> Prop) :
    Option A -> Option A -> Prop :=
  InvImage (Sum.Lex (emptyRelation : Unit -> Unit -> Prop) r)
    (optionSumEquiv A)

theorem optionPrependRel_isWellOrder {A : Type u}
    (r : A -> A -> Prop) [IsWellOrder A r] :
    IsWellOrder (Option A) (optionPrependRel r) := by
  letI : IsWellOrder (Unit ⊕ A)
      (Sum.Lex (emptyRelation : Unit -> Unit -> Prop) r) := by
    infer_instance
  exact
    { wf := InvImage.wf (optionSumEquiv A)
        (IsWellFounded.wf :
          WellFounded
            (Sum.Lex (emptyRelation : Unit -> Unit -> Prop) r))
      trichotomous :=
        (InvImage.trichotomous
          (r := Sum.Lex (emptyRelation : Unit -> Unit -> Prop) r)
          (optionSumEquiv A).injective).trichotomous }

/-! ## Simultaneous stage/layer recursion -/

/-- The mutually dependent canonical orders at one ordinal. -/
structure CanonicalOrderData (alpha : Ordinal.{u}) where
  /-- The canonical well-order relation on the stage. -/
  stageRel : LStageCarrier alpha -> LStageCarrier alpha -> Prop
  stage_isWellOrder : IsWellOrder (LStageCarrier alpha) stageRel
  /-- The canonical well-order relation on the stage's birth layer. -/
  layerRel : BornAt alpha -> BornAt alpha -> Prop
  layer_isWellOrder : IsWellOrder (BornAt alpha) layerRel











end Constructible
end CUAdapterModule75



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryGeneratorInternalOrder -/
section CUAdapterModule76
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Generator orders from internally represented well-orders

An internal relation graph on a constructible set `U` orders
`Model.InternalCarrier U`, while rudimentary programs use
`ZFCarrier U.1` as their ordinary generator type.  These two carriers are
canonically equivalent.  This file transports the represented well-order
across that equivalence, adds the distinguished `none` generator at the
front, and finally lifts the order to postfix stack programs by Shortlex.
-/


universe u

namespace Constructible

namespace Godel

namespace RudimentaryTerm

noncomputable section

/--
The elements of the underlying `ZFSet` of a constructible set are the same
as its internal carrier; the latter additionally records that each element
is constructible.
-/
def zfCarrierInternalEquiv (U : Model.LCarrier.{u}) :
    ZFCarrier U.1 ≃ Model.InternalCarrier U where
  toFun x :=
    ⟨⟨x.1, mem_L_of_mem x.2 U.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp]
theorem zfCarrierInternalEquiv_apply_val
    (U : Model.LCarrier.{u}) (x : ZFCarrier U.1) :
    ((zfCarrierInternalEquiv U x).1).1 = x.1 :=
  rfl

@[simp]
theorem zfCarrierInternalEquiv_symm_apply_val
    (U : Model.LCarrier.{u}) (x : Model.InternalCarrier U) :
    ((zfCarrierInternalEquiv U).symm x).1 = x.1.1 :=
  rfl

/--
The ordinary-generator relation is exactly the pullback of the internally
represented graph relation along `zfCarrierInternalEquiv`.
-/
theorem generatorPairRel_eq_invImage_graphRelOn
    (U relation : Model.LCarrier.{u}) :
    generatorPairRel relation.1 =
      InvImage (Model.graphRelOn relation U) (zfCarrierInternalEquiv U) := by
  funext x y
  rfl

/-- Transport an internally represented well-order to the plain `ZFCarrier`. -/
theorem generatorPairRel_isWellOrder_of_internal
    (U relation : Model.LCarrier.{u})
    (hwell : Model.InternallyWellOrders relation U) :
    IsWellOrder (ZFCarrier U.1) (generatorPairRel relation.1) := by
  rw [generatorPairRel_eq_invImage_graphRelOn]
  letI : IsWellOrder (Model.InternalCarrier U)
      (Model.graphRelOn relation U) := hwell
  exact
    { wf := InvImage.wf (zfCarrierInternalEquiv U)
        (IsWellFounded.wf :
          WellFounded (Model.graphRelOn relation U))
      trichotomous :=
        (InvImage.trichotomous
          (r := Model.graphRelOn relation U)
          (zfCarrierInternalEquiv U).injective).trichotomous }

/--
`generatorTokenRel` is the existing generic construction which puts one
distinguished point before a relation on the ordinary generators.
-/
theorem generatorTokenRel_eq_optionPrependRel
    (U relation : ZFSet.{u}) :
    generatorTokenRel U relation =
      optionPrependRel (generatorPairRel relation) := by
  funext left right
  cases left <;> cases right <;>
    simp [generatorTokenRel, optionPrependRel, optionSumEquiv, InvImage]

/--
An actual constructible graph which internally well-orders `U` induces the
well-order on generator tokens used by rudimentary programs.
-/
theorem generatorTokenRel_isWellOrder_of_internal
    (U relation : Model.LCarrier.{u})
    (hwell : Model.InternallyWellOrders relation U) :
    IsWellOrder (Option (ZFCarrier U.1))
      (generatorTokenRel U.1 relation.1) := by
  letI : IsWellOrder (ZFCarrier U.1) (generatorPairRel relation.1) :=
    generatorPairRel_isWellOrder_of_internal U relation hwell
  rw [generatorTokenRel_eq_optionPrependRel]
  exact optionPrependRel_isWellOrder (generatorPairRel relation.1)



end

end RudimentaryTerm

end Godel

end Constructible
end CUAdapterModule76


