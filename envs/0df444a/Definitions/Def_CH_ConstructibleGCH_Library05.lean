-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library05
-- name    : CH_ConstructibleGCH_Library05
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:17:48.311948+00:00
-- url     : https://prove2.me/theorems/e6ccd036-3302-438e-adeb-11cc1766d891
-- title:
--   Internal cardinal arithmetic and the GCH reduction
-- statement:
--   An internal injection is represented by a function graph that is itself a member of the constructible universe. This library provides injection, equinumerosity, Hartogs successor and power-set interfaces, the internally represented Mostowski-collapse data, and cardinal-controlled hulls. These are the data consumed by the separate GCH proofs.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CondensationOmega.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Hartogs.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalInjections.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalSchroederBernstein.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/HartogsSuccessor.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/GCHReduction.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalCantor.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalMostowskiCollapse.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CondensationGCHBridge.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library04
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_CondensationOmega -/
section GCHSource_Work_CUGCH_CondensationOmega
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Condensation at the first limit level

This file proves the `theta = omega` case of the standard Condensation
Lemma.  The proof does not use the fixed evaluator parameters from the
reflection-level argument: the standard omega level does not contain its own
omega.  Instead it uses the ordinary fact that `L_omega` consists of
hereditarily finite sets and is therefore pointwise generated from the empty
set by finite insertion.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

namespace OmegaCondensation

/-- A `ZFSet` is externally finite when its external set of members is
finite.  This is the direct Lean rendering of ordinary set-theoretic
finiteness used in the metatheoretic proof that `L_omega = HF`. -/
def ExternallyFinite (x : ZFSet.{u}) : Prop :=
  (x : Set ZFSet.{u}).Finite









/-! ## Exact first-order definitions of the finite constructors -/

/-- The unary formula saying that its only coordinate has no members. -/
def emptyBody : FOFormula 1 :=
  FOFormula.all (.neg (.mem (Fin.last 1) (0 : Fin 1).castSucc))

/-- The three-coordinate formula with layout `[element, oldSet, output]`
saying `output = insert element oldSet`. -/
def insertBody : FOFormula 3 :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last 3) (2 : Fin 3).castSucc)
      (FOFormula.disj
        (.eq (Fin.last 3) (0 : Fin 3).castSucc)
        (.mem (Fin.last 3) (1 : Fin 3).castSucc)))

/-- Exact restricted semantics of `emptyBody`.  Quantification is over the
displayed carrier, as required by `SatisfactionAbsolute`. -/
@[simp]
theorem satisfiesIn_emptyBody_iff (M : Set ZFSet.{u}) (x : ZFSet.{u}) :
    Model.SatisfiesIn M emptyBody ![x] ↔
      ∀ z : ZFSet.{u}, z ∈ M → z ∉ x := by
  classical
  simp only [emptyBody, FOFormula.all, Model.SatisfiesIn,
    snoc_last, snoc_castSucc, Matrix.cons_val_zero]
  push Not
  rfl

/-- Exact restricted semantics of `insertBody`. -/
@[simp]
theorem satisfiesIn_insertBody_iff (M : Set ZFSet.{u})
    (a b out : ZFSet.{u}) :
    Model.SatisfiesIn M insertBody ![a, b, out] ↔
      ∀ z : ZFSet.{u}, z ∈ M →
        (z ∈ out ↔ z = a ∨ z ∈ b) := by
  classical
  simp only [insertBody, FOFormula.all, Model.SatisfiesIn,
    Model.satisfiesIn_biimp_iff, Model.satisfiesIn_disj_iff,
    snoc_last, snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push Not
  rfl



/-! ## Closure of `L_omega` and of an elementary substructure -/

















end OmegaCondensation



end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_CondensationOmega


/- Source module: Solutions.Work_CUGCH_Hartogs -/
section GCHSource_Work_CUGCH_Hartogs
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Internal injections and Hartogs numbers

This file formulates Hartogs' construction entirely inside a membership
structure.  Injections are represented by sets of Kuratowski pairs, so an
injection in `LCarrier` is required to have a graph which itself belongs to
`L`.  Ambient cardinal comparison is used only to show that the search for
an obstruction is nonempty; the least obstruction and its specification use
only internally represented injection graphs.
-/

section

universe u

open scoped Cardinal

namespace Constructible.ContinuumFormula

/-! ## Semantic relations -/

/-- The graph has at most one preimage in `domain` at `y`. -/
def HasAtMostOnePreimage {A : Type u} (E : A → A → Prop)
    (graph domain y : A) : Prop :=
  ∀ x : A, E x domain → GraphValue E graph x y →
    ∀ z : A, E z domain → GraphValue E graph z y → z = x

/-- A set-coded injection from `domain` into `codomain`. -/
def IsInjection {A : Type u} (E : A → A → Prop)
    (graph domain codomain : A) : Prop :=
  IsGraphBetween E graph domain codomain ∧
    (∀ x : A, E x domain → HasUniqueImage E graph x codomain) ∧
      ∀ y : A, E y codomain →
        HasAtMostOnePreimage E graph domain y

/-- There is an internally represented injection from `domain` to
`codomain`. -/
def Injects {A : Type u} (E : A → A → Prop)
    (domain codomain : A) : Prop :=
  ∃ graph : A, IsInjection E graph domain codomain

/-- The elements of a set in a relation-parametric membership structure. -/
abbrev RelationCarrier {A : Type u} (E : A → A → Prop) (a : A) :=
  {x : A // E x a}

/-- `hartogs` is the least ordinal which does not internally inject into
`base`. -/
def IsHartogsNumber {A : Type u} (E : A → A → Prop)
    (base hartogs : A) : Prop :=
  IsVonNeumannOrdinal E hartogs ∧
    ¬Injects E hartogs base ∧
      ∀ alpha : A, E alpha hartogs → Injects E alpha base

/-- Every internally represented bijection is, in particular, an internally
represented injection. -/
theorem IsBijection.toIsInjection {A : Type u} {E : A → A → Prop}
    {graph domain codomain : A}
    (h : IsBijection E graph domain codomain) :
    IsInjection E graph domain codomain := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro y hy
  rcases h.2.2 y hy with ⟨x, hx, hxy, hunique⟩
  intro x' hx' hx'y z hz hzy
  exact (hunique z hz hzy).trans (hunique x' hx' hx'y).symm



/-- The function selected from a total internally represented injection. -/
noncomputable def IsInjection.toFun
    {A : Type u} {E : A → A → Prop}
    {graph domain codomain : A}
    (h : IsInjection E graph domain codomain) :
    RelationCarrier E domain → RelationCarrier E codomain :=
  fun x =>
    ⟨Classical.choose (h.2.1 x.1 x.2),
      (Classical.choose_spec (h.2.1 x.1 x.2)).1⟩

theorem IsInjection.toFun_graphValue
    {A : Type u} {E : A → A → Prop}
    {graph domain codomain : A}
    (h : IsInjection E graph domain codomain)
    (x : RelationCarrier E domain) :
    GraphValue E graph x.1 (h.toFun x).1 :=
  (Classical.choose_spec (h.2.1 x.1 x.2)).2.1

theorem IsInjection.toFun_injective
    {A : Type u} {E : A → A → Prop}
    {graph domain codomain : A}
    (h : IsInjection E graph domain codomain) :
    Function.Injective h.toFun := by
  intro x z hxz
  apply Subtype.ext
  have hvalue : (h.toFun x).1 = (h.toFun z).1 :=
    congrArg Subtype.val hxz
  have hzx : z.1 = x.1 :=
    h.2.2 (h.toFun x).1 (h.toFun x).2
      x.1 x.2 (h.toFun_graphValue x)
      z.1 z.2 (by
        rw [hvalue]
        exact h.toFun_graphValue z)
  exact hzx.symm









/-! ## The internal Hartogs number of a constructible set -/

 noncomputable def externalHartogsBound
    (base : Constructible.Model.LCarrier.{u}) : Ordinal.{u} :=
  (Order.succ (ZFSet.card base.1)).ord

/-- The von Neumann ordinal predicate is absolute between the transitive
class `L` and the ambient well-founded `ZFSet` universe. -/
theorem isVonNeumannOrdinal_lCarrier_iff
    (x : Constructible.Model.LCarrier.{u}) :
    IsVonNeumannOrdinal Constructible.Model.lCarrierMem x ↔
      x.1.IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  constructor
  · rintro ⟨hxTransitive, hmembers⟩
    constructor
    · intro y hy z hz
      let yL : Constructible.Model.LCarrier.{u} :=
        ⟨y, Constructible.mem_L_of_mem hy x.2⟩
      let zL : Constructible.Model.LCarrier.{u} :=
        ⟨z, Constructible.mem_L_of_mem hz yL.2⟩
      exact hxTransitive yL hy zL hz
    · intro y hy z hz w hw
      let yL : Constructible.Model.LCarrier.{u} :=
        ⟨y, Constructible.mem_L_of_mem hy x.2⟩
      let zL : Constructible.Model.LCarrier.{u} :=
        ⟨z, Constructible.mem_L_of_mem hz yL.2⟩
      let wL : Constructible.Model.LCarrier.{u} :=
        ⟨w, Constructible.mem_L_of_mem hw zL.2⟩
      exact hmembers yL hy zL hz wL hw
  · rintro ⟨hxTransitive, hmembers⟩
    constructor
    · intro y hy z hz
      exact hxTransitive.mem_trans hz hy
    · intro y hy z hz w hw
      exact (hmembers y.1 hy).mem_trans hw hz

/-- Every internally recognized ordinal is its canonical constructible
ordinal code. -/
theorem exists_eq_ordinalLCarrier_of_isVonNeumannOrdinal
    (x : Constructible.Model.LCarrier.{u})
    (hx : IsVonNeumannOrdinal Constructible.Model.lCarrierMem x) :
    ∃ alpha : Ordinal.{u},
      x = Constructible.Model.ordinalLCarrier alpha := by
  refine ⟨x.1.rank, ?_⟩
  apply Subtype.ext
  exact (isVonNeumannOrdinal_lCarrier_iff x).mp hx |>.toZFSet_rank_eq.symm





/-- The ordinals which do not internally inject into `base`. -/
def internalHartogsObstructions
    (base : Constructible.Model.LCarrier.{u}) : Set Ordinal.{u} :=
  {alpha | ¬Injects Constructible.Model.lCarrierMem
    (Constructible.Model.ordinalLCarrier alpha) base}



/-- The least ordinal which has no injection into `base` represented in
`L`. -/
noncomputable def internalHartogsOrdinal
    (base : Constructible.Model.LCarrier.{u}) : Ordinal.{u} :=
  sInf (internalHartogsObstructions base)

/-- The internal Hartogs ordinal, packaged as a constructible set. -/
noncomputable def internalHartogsLCarrier
    (base : Constructible.Model.LCarrier.{u}) :
    Constructible.Model.LCarrier.{u} :=
  Constructible.Model.ordinalLCarrier (internalHartogsOrdinal base)







/-! ## Object-language formulas -/

/-- The graph has at most one preimage in `domain` at `y`. -/
def atMostOnePreimageAt {n : Nat}
    (graph domain y : Fin n) : FOFormula n :=
  FOFormula.boundedAll domain
    (FOFormula.imp
      (graphValueAt graph.castSucc (Fin.last n) y.castSucc)
      (FOFormula.boundedAll domain.castSucc
        (FOFormula.imp
          (graphValueAt graph.castSucc.castSucc
            (Fin.last (n + 1)) y.castSucc.castSucc)
          (.eq (Fin.last (n + 1)) (Fin.last n).castSucc))))

@[simp]
theorem satisfies_atMostOnePreimageAt
    {A : Type u} (E : A → A → Prop) {n : Nat}
    (graph domain y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (atMostOnePreimageAt graph domain y) s ↔
      HasAtMostOnePreimage E (s graph) (s domain) (s y) := by
  simp only [atMostOnePreimageAt,
    FOFormula.satisfies_boundedAll, FOFormula.satisfies_imp,
    FOFormula.Satisfies, satisfies_graphValueAt,
    snoc_last, snoc_castSucc,
    HasAtMostOnePreimage]

/-- `graph` codes an injection from `domain` into `codomain`. -/
def injectionAt {n : Nat}
    (graph domain codomain : Fin n) : FOFormula n :=
  .conj (graphBetweenAt graph domain codomain)
    (.conj
      (FOFormula.boundedAll domain
        (uniqueImageAt graph.castSucc
          (Fin.last n) codomain.castSucc))
      (FOFormula.boundedAll codomain
        (atMostOnePreimageAt graph.castSucc
          domain.castSucc (Fin.last n))))

@[simp]
theorem satisfies_injectionAt
    {A : Type u} (E : A → A → Prop) {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (injectionAt graph domain codomain) s ↔
      IsInjection E (s graph) (s domain) (s codomain) := by
  simp only [injectionAt, FOFormula.Satisfies,
    satisfies_graphBetweenAt, FOFormula.satisfies_boundedAll,
    satisfies_uniqueImageAt, satisfies_atMostOnePreimageAt,
    snoc_last, snoc_castSucc, IsInjection]

/-- There is a set coding an injection from `domain` to `codomain`. -/
def injectsAt {n : Nat} (domain codomain : Fin n) : FOFormula n :=
  .ex (injectionAt (Fin.last n) domain.castSucc codomain.castSucc)

@[simp]
theorem satisfies_injectsAt
    {A : Type u} (E : A → A → Prop) {n : Nat}
    (domain codomain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (injectsAt domain codomain) s ↔
      Injects E (s domain) (s codomain) := by
  simp only [injectsAt, FOFormula.Satisfies,
    satisfies_injectionAt, snoc_last, snoc_castSucc, Injects]

/-- `hartogs` is the least ordinal not injecting into `base`. -/
def hartogsAt {n : Nat} (base hartogs : Fin n) : FOFormula n :=
  .conj (isOrdinalAt hartogs)
    (.conj
      (.neg (injectsAt hartogs base))
      (FOFormula.boundedAll hartogs
        (injectsAt (Fin.last n) base.castSucc)))

@[simp]
theorem satisfies_hartogsAt
    {A : Type u} (E : A → A → Prop) {n : Nat}
    (base hartogs : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (hartogsAt base hartogs) s ↔
      IsHartogsNumber E (s base) (s hartogs) := by
  simp only [hartogsAt, FOFormula.Satisfies,
    satisfies_isOrdinalAt, satisfies_injectsAt,
    FOFormula.satisfies_boundedAll, snoc_last, snoc_castSucc,
    IsHartogsNumber]

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_Hartogs


/- Source module: Solutions.Work_CUGCH_InternalInjections -/
section GCHSource_Work_CUGCH_InternalInjections
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Internally represented injections in the constructible universe

This file develops the elementary algebra of injection graphs whose graph is
itself an element of `L`.  In particular, inverse and composite graphs are
obtained by Separation from fixed first-order definitions.  No ambient
function is used as a witness for an internal injection.
-/

section

universe u

namespace Constructible.ContinuumFormula

/-! ## Absoluteness of Kuratowski graph semantics -/

theorem isKuratowskiPairOf_lCarrier_iff
    (pair x y : Constructible.Model.LCarrier.{u}) :
    IsKuratowskiPairOf Constructible.Model.lCarrierMem pair x y ↔
      pair.1 = ZFSet.pair x.1 y.1 := by
  have hsemantic := satisfies_kuratowskiPairAt
    Constructible.Model.lCarrierMem
    (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) ![pair, x, y]
  have hraw :=
    Constructible.DefinableRelationGraph.satisfies_pairEq_lCarrier
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) ![pair, x, y]
  rw [show kuratowskiPairAt
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) =
        (Delta0Formula.kuratowskiPairEqAt
          (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)).toFO from rfl]
      at hsemantic
  exact hsemantic.symm.trans hraw

@[simp]
theorem graphValue_lCarrier_iff_graphRel
    (graph x y : Constructible.Model.LCarrier.{u}) :
    GraphValue Constructible.Model.lCarrierMem graph x y ↔
      Constructible.Model.GraphRel graph x y := by
  constructor
  · rintro ⟨pair, hpairGraph, hpair⟩
    rw [Constructible.Model.GraphRel]
    rw [← (isKuratowskiPairOf_lCarrier_iff pair x y).mp hpair]
    exact hpairGraph
  · intro hgraph
    let pair := Constructible.Model.orderedPairLCarrier x y
    refine ⟨pair, hgraph, ?_⟩
    exact (isKuratowskiPairOf_lCarrier_iff pair x y).mpr rfl

theorem IsGraphBetween.graphValue_mem_lCarrier
    {graph domain codomain x y : Constructible.Model.LCarrier.{u}}
    (h : IsGraphBetween Constructible.Model.lCarrierMem
      graph domain codomain)
    (hvalue : GraphValue Constructible.Model.lCarrierMem graph x y) :
    x.1 ∈ domain.1 ∧ y.1 ∈ codomain.1 := by
  rcases hvalue with ⟨pair, hpairGraph, hpairXY⟩
  rcases h pair hpairGraph with
    ⟨x', hx', y', hy', hpairXY'⟩
  have hraw : ZFSet.pair x.1 y.1 = ZFSet.pair x'.1 y'.1 :=
    ((isKuratowskiPairOf_lCarrier_iff pair x y).mp hpairXY).symm.trans
      ((isKuratowskiPairOf_lCarrier_iff pair x' y').mp hpairXY')
  have hcoordinates := ZFSet.pair_inj.mp hraw
  have hx : x = x' := Subtype.ext hcoordinates.1
  have hy : y = y' := Subtype.ext hcoordinates.2
  simpa only [hx, hy] using And.intro hx' hy'

/-! ## Definable identity, converse, and composition graphs -/

/-- The binary union, packaged as an element of `L`. -/
def unionLCarrier
    (x y : Constructible.Model.LCarrier.{u}) :
    Constructible.Model.LCarrier.{u} :=
  ⟨x.1 ∪ y.1, Constructible.union_mem_L x.2 y.2⟩

@[simp]
theorem mem_unionLCarrier_iff
    (x y z : Constructible.Model.LCarrier.{u}) :
    z.1 ∈ (unionLCarrier x y).1 ↔ z.1 ∈ x.1 ∨ z.1 ∈ y.1 := by
  simp [unionLCarrier]

def identityGraphPredicate : FOFormula 2 :=
  .eq (0 : Fin 2) (1 : Fin 2)

 theorem identityGraph_assignment
    (x y : Constructible.Model.LCarrier.{u}) :
    snoc (snoc (fun i : Fin 0 => Fin.elim0 i) x) y = ![x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_identityGraphPredicate
    (x y : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      identityGraphPredicate
      (snoc (snoc (fun i : Fin 0 => Fin.elim0 i) x) y) ↔
        x = y := by
  rw [identityGraph_assignment]
  rfl

def converseGraphPredicate : FOFormula 3 :=
  graphValueAt (0 : Fin 3) (2 : Fin 3) (1 : Fin 3)

 theorem converseGraph_assignment
    (graph x y : Constructible.Model.LCarrier.{u}) :
    snoc (snoc ![graph] x) y = ![graph, x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_converseGraphPredicate
    (graph x y : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      converseGraphPredicate (snoc (snoc ![graph] x) y) ↔
        GraphValue Constructible.Model.lCarrierMem graph y x := by
  rw [converseGraph_assignment]
  exact satisfies_graphValueAt
    Constructible.Model.lCarrierMem
      (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) ![graph, x, y]

def compositionGraphPredicate : FOFormula 4 :=
  .ex (.conj
    (graphValueAt
      (0 : Fin 4).castSucc (2 : Fin 4).castSucc (Fin.last 4))
    (graphValueAt
      (1 : Fin 4).castSucc (Fin.last 4) (3 : Fin 4).castSucc))

 theorem compositionGraph_assignment
    (first second x y : Constructible.Model.LCarrier.{u}) :
    snoc (snoc ![first, second] x) y = ![first, second, x, y] := by
  funext i
  fin_cases i <;> rfl

 theorem compositionGraph_witness_assignment
    (first second x y z : Constructible.Model.LCarrier.{u}) :
    snoc ![first, second, x, y] z = ![first, second, x, y, z] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_compositionGraphPredicate
    (first second x y : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      compositionGraphPredicate
      (snoc (snoc ![first, second] x) y) ↔
        ∃ middle : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem first x middle ∧
            GraphValue Constructible.Model.lCarrierMem second middle y := by
  rw [compositionGraph_assignment]
  simp only [compositionGraphPredicate, FOFormula.Satisfies,
    satisfies_graphValueAt]
  apply exists_congr
  intro z
  rw [compositionGraph_witness_assignment]
  rfl















/-! ## Hartogs numbers are internal cardinals -/



end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalInjections


/- Source module: Solutions.Work_CUGCH_InternalSchroederBernstein -/
section GCHSource_Work_CUGCH_InternalSchroederBernstein
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Cantor--Schroeder--Bernstein inside the constructible universe

The usual least-closed-subset proof is carried out with Full Separation in
`LCarrier`.  The resulting bijection is then built by the definable relation
graph construction, so its graph is an actual member of `L`.
-/

section

universe u

namespace Constructible.ContinuumFormula

/-! ## Formula semantics for the least closed subset -/

def InRange {A : Type u} (E : A -> A -> Prop)
    (graph domain x : A) : Prop :=
  exists y : A, E y domain /\ GraphValue E graph y x

def SBBase {A : Type u} (E : A -> A -> Prop)
    (g a b x : A) : Prop :=
  E x a /\ Not (InRange E g b x)

def SBStep {A : Type u} (E : A -> A -> Prop)
    (f g closed z : A) : Prop :=
  exists x : A, E x closed /\
    exists y : A, GraphValue E f x y /\ GraphValue E g y z

def SBClosed {A : Type u} (E : A -> A -> Prop)
    (f g a b closed : A) : Prop :=
  IsSubsetOf E closed a /\
    (forall x : A, SBBase E g a b x -> E x closed) /\
      forall z : A, SBStep E f g closed z -> E z closed

def SBLeastMember {A : Type u} (E : A -> A -> Prop)
    (f g a b x : A) : Prop :=
  E x a /\ forall closed : A, SBClosed E f g a b closed -> E x closed

def SBGenerated {A : Type u} (E : A -> A -> Prop)
    (f g a b closed x : A) : Prop :=
  SBBase E g a b x \/ SBStep E f g closed x

def SBBijectionRel {A : Type u} (E : A -> A -> Prop)
    (f g a closed x y : A) : Prop :=
  (E x closed /\ GraphValue E f x y) \/
    (E x a /\ Not (E x closed) /\ GraphValue E g y x)

/-- `x` is in the range of `graph` restricted to `domain`. -/
def inRangeAt {n : Nat} (graph domain x : Fin n) : FOFormula n :=
  FOFormula.boundedEx domain
    (graphValueAt graph.castSucc (Fin.last n) x.castSucc)

@[simp]
theorem satisfies_inRangeAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (graph domain x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (inRangeAt graph domain x) s <->
      InRange E (s graph) (s domain) (s x) := by
  simp only [inRangeAt, FOFormula.satisfies_boundedEx,
    satisfies_graphValueAt, snoc_last, snoc_castSucc, InRange]

/-- The points of `a` omitted by the range of `g : b -> a`. -/
def sbBaseAt {n : Nat} (g a b x : Fin n) : FOFormula n :=
  .conj (.mem x a) (.neg (inRangeAt g b x))

@[simp]
theorem satisfies_sbBaseAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (g a b x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbBaseAt g a b x) s <->
      SBBase E (s g) (s a) (s b) (s x) := by
  simp only [sbBaseAt, FOFormula.Satisfies, satisfies_inRangeAt, SBBase]

/-- One application of `g o f` starting in `closed`. -/
def sbStepAt {n : Nat} (f g closed z : Fin n) : FOFormula n :=
  FOFormula.boundedEx closed
    (.ex (.conj
      (graphValueAt f.castSucc.castSucc
        (Fin.last n).castSucc (Fin.last (n + 1)))
      (graphValueAt g.castSucc.castSucc
        (Fin.last (n + 1)) z.castSucc.castSucc)))

@[simp]
theorem satisfies_sbStepAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (f g closed z : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbStepAt f g closed z) s <->
      SBStep E (s f) (s g) (s closed) (s z) := by
  simp only [sbStepAt, FOFormula.satisfies_boundedEx,
    FOFormula.Satisfies, satisfies_graphValueAt,
    snoc_last, snoc_castSucc, SBStep]

/-- A subset of `a` containing the base and closed under `g o f`. -/
def sbClosedAt {n : Nat}
    (f g a b closed : Fin n) : FOFormula n :=
  .conj (subsetAt closed a)
    (.conj
      (.all (.imp
        (sbBaseAt g.castSucc a.castSucc b.castSucc (Fin.last n))
        (.mem (Fin.last n) closed.castSucc)))
      (.all (.imp
        (sbStepAt f.castSucc g.castSucc closed.castSucc (Fin.last n))
        (.mem (Fin.last n) closed.castSucc))))

@[simp]
theorem satisfies_sbClosedAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (f g a b closed : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbClosedAt f g a b closed) s <->
      SBClosed E (s f) (s g) (s a) (s b) (s closed) := by
  simp only [sbClosedAt, FOFormula.Satisfies, satisfies_subsetAt,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_sbBaseAt, satisfies_sbStepAt,
    snoc_last, snoc_castSucc, SBClosed]

/-- Membership in the intersection of all closed subsets of `a`. -/
def sbLeastMemberAt {n : Nat} (f g a b x : Fin n) : FOFormula n :=
  .conj (.mem x a)
    (.all (.imp
      (sbClosedAt f.castSucc g.castSucc a.castSucc b.castSucc (Fin.last n))
      (.mem x.castSucc (Fin.last n))))

@[simp]
theorem satisfies_sbLeastMemberAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (f g a b x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbLeastMemberAt f g a b x) s <->
      SBLeastMember E (s f) (s g) (s a) (s b) (s x) := by
  simp only [sbLeastMemberAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_sbClosedAt, snoc_last, snoc_castSucc, SBLeastMember]

/-- The base together with one step from `closed`. -/
def sbGeneratedAt {n : Nat}
    (f g a b closed x : Fin n) : FOFormula n :=
  .disj (sbBaseAt g a b x) (sbStepAt f g closed x)

@[simp]
theorem satisfies_sbGeneratedAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (f g a b closed x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbGeneratedAt f g a b closed x) s <->
      SBGenerated E (s f) (s g) (s a) (s b) (s closed) (s x) := by
  simp only [sbGeneratedAt, FOFormula.satisfies_disj,
    satisfies_sbBaseAt, satisfies_sbStepAt, SBGenerated]

/-- The piecewise relation used in the CSB construction. -/
def sbBijectionAt {n : Nat}
    (f g a closed x y : Fin n) : FOFormula n :=
  .disj
    (.conj (.mem x closed) (graphValueAt f x y))
    (.conj (.mem x a)
      (.conj (.neg (.mem x closed)) (graphValueAt g y x)))

@[simp]
theorem satisfies_sbBijectionAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (f g a closed x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (sbBijectionAt f g a closed x y) s <->
      SBBijectionRel E (s f) (s g) (s a) (s closed) (s x) (s y) := by
  simp only [sbBijectionAt, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_graphValueAt, SBBijectionRel]

/-! ## The least closed subset of the domain -/

 def sbLeastMemberPredicate : FOFormula 5 :=
  sbLeastMemberAt
    (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (3 : Fin 5) (4 : Fin 5)







 def sbGeneratedPredicate : FOFormula 6 :=
  sbGeneratedAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
    (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)







/-! ## The internally represented CSB bijection -/

 def sbBijectionPredicate : FOFormula 6 :=
  sbBijectionAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
    (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)









end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalSchroederBernstein


/- Source module: Solutions.Work_CUGCH_HartogsSuccessor -/
section GCHSource_Work_CUGCH_HartogsSuccessor
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Hartogs numbers as successor cardinals

This file isolates the one use of the internal Cantor--Schroeder--Bernstein
theorem needed to identify the Hartogs number of an internal cardinal with
its successor cardinal.  Until an unconditional internal CSB construction is
available, the relevant antisymmetry property is kept as an explicit
hypothesis.
-/

section

universe u

namespace Constructible.ContinuumFormula

/-- The internal Cantor--Schroeder--Bernstein principle for a membership
structure.

The conclusion requires a bijection whose graph is itself constructible; an
ambient Lean equivalence is therefore not sufficient.
-/
def InternalInjectionAntisymm {A : Type u} (E : A -> A -> Prop) : Prop :=
  forall {x y : A},
    Injects E x y -> Injects E y x -> Equinumerous E x y









/-! ## Unconditional specialization to `LCarrier` -/







end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_HartogsSuccessor


/- Source module: Solutions.Work_CUGCH_GCHReduction -/
section GCHSource_Work_CUGCH_GCHReduction
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Reduction of GCH in the constructible universe

This file discharges the elementary part of the GCH semantics for
`Model.LCarrier`.  It identifies the standard constructible `omega` with the
least internally inductive set, proves that it is an internal cardinal, and
reduces GCH to the substantive upper-bound theorem for constructible power
sets.

The reduction theorem deliberately keeps that upper bound as an explicit
hypothesis.  In particular, no condensation or small-stage theorem is assumed
implicitly here.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## The internal natural numbers -/





/-! ## Finiteness of the ordinals below `omega` -/

 noncomputable def finiteOrdinalMemberIndex (n : Nat) :
    RelationCarrier LMem
      (ordinalLCarrier (n : Ordinal.{u})) → Fin n :=
  fun x => by
    have hxraw : x.1.1 ∈
        (ordinalLCarrier (n : Ordinal.{u})).1 := x.2
    have hx : x.1.1 ∈
        Constructible.FiniteSequenceZF.natCode n := by
      simpa only [ordinalLCarrier_val,
        Constructible.FiniteSequenceZF.natCode] using hxraw
    let k := Classical.choose
      (Constructible.IndexedSequenceZF.mem_natCode_iff_exists_lt
        x.1.1 n |>.mp hx)
    exact ⟨k, (Classical.choose_spec
      (Constructible.IndexedSequenceZF.mem_natCode_iff_exists_lt
        x.1.1 n |>.mp hx)).1⟩





 noncomputable def omegaNaturalMember (n : Nat) :
    RelationCarrier LMem
      (omegaLCarrier : Constructible.Model.LCarrier.{u}) :=
  ⟨ordinalLCarrier (n : Ordinal.{u}), by
    change (n : Ordinal.{u}).toZFSet ∈ Ordinal.omega0.toZFSet
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)⟩







/-! ## The exact remaining GCH obligation -/





end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_GCHReduction


/- Source module: Solutions.Work_CUGCH_InternalCantor -/
section GCHSource_Work_CUGCH_InternalCantor
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Cantor's theorem inside the constructible universe

The diagonal subset is produced by Full Separation in `L`.  Consequently the
argument rules out an internally represented bijection between a set and its
internal powerset; it does not appeal to ambient cardinal arithmetic.
-/

section

universe u

namespace Constructible.ContinuumFormula

/-- With assignment `[graph, x]`, there is a graph value `y` at `x` and
`x` is not a member of `y`. -/
def cantorDiagonalPredicate : FOFormula 2 :=
  .ex (.conj
    (graphValueAt
      (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2))
    (.neg (.mem (1 : Fin 2).castSucc (Fin.last 2))))

 theorem cantorDiagonal_assignment
    (graph x : Constructible.Model.LCarrier.{u}) :
    snoc ![graph] x = ![graph, x] := by
  funext i
  fin_cases i <;> rfl

 theorem cantorDiagonal_witness_assignment
    (graph x y : Constructible.Model.LCarrier.{u}) :
    snoc ![graph, x] y = ![graph, x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_cantorDiagonalPredicate
    (graph x : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      cantorDiagonalPredicate (snoc ![graph] x) ↔
        ∃ y : Constructible.Model.LCarrier.{u},
          GraphValue Constructible.Model.lCarrierMem graph x y ∧
            x.1 ∉ y.1 := by
  rw [cantorDiagonal_assignment]
  simp only [cantorDiagonalPredicate, FOFormula.Satisfies,
    satisfies_graphValueAt]
  apply exists_congr
  intro y
  rw [cantorDiagonal_witness_assignment]
  rfl

/-! ## The singleton injection into an internal powerset -/

/-- Layout `[base, power, x, y]`: `x ∈ base`, `y ∈ power`, and
`y = {x}` internally. -/
def singletonInjectionPredicate : FOFormula 4 :=
  .conj (.mem (2 : Fin 4) (0 : Fin 4))
    (.conj (.mem (3 : Fin 4) (1 : Fin 4))
      (singletonAt (3 : Fin 4) (2 : Fin 4)))

 theorem singletonInjection_assignment
    (base power x y : Constructible.Model.LCarrier.{u}) :
    snoc (snoc ![base, power] x) y = ![base, power, x, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_singletonInjectionPredicate
    (base power x y : Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      singletonInjectionPredicate
      (snoc (snoc ![base, power] x) y) ↔
        x.1 ∈ base.1 ∧ y.1 ∈ power.1 ∧
          IsSingletonOf Constructible.Model.lCarrierMem y x := by
  rw [singletonInjection_assignment]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (satisfies_singletonAt Constructible.Model.lCarrierMem
      (3 : Fin 4) (2 : Fin 4) ![base, power, x, y]))







end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalCantor


/- Source module: Solutions.Work_CUGCH_InternalMostowskiCollapse -/
section GCHSource_Work_CUGCH_InternalMostowskiCollapse
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Internalizing a set-sized Mostowski collapse

`MostowskiCollapse.collapse` is an external well-founded recursion on actual
`ZFSet`s.  Consequently its range and graph are actual `ZFSet`s, but that fact
alone does not show that either set belongs to `L`.

This file isolates the exact bridge needed for that internalization.  A
`CollapseFormulaSpec` records a fixed first-order formula which is sound for
the external collapse and has an output in `L` for every member of the
domain.  Replacement then constructs the range in `L`, and Separation
constructs the Kuratowski-pair graph in `L`.

The remaining obligation in a full condensation proof is therefore explicit:
one must prove the `complete` field of `CollapseFormulaSpec`, normally from
the well-founded-recursion theorem of ZF.  No form of Condensation is assumed
in this file.
-/

section

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

/-- The Kuratowski-pair graph of the external Mostowski collapse. -/
noncomputable def graph (domain : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun x : {x : ZFSet.{u} // x ∈ domain} =>
    ZFSet.pair x.1 (collapse domain x.1)

@[simp]
theorem mem_graph_iff {domain q : ZFSet.{u}} :
    q ∈ graph domain ↔
      ∃ x : ZFSet.{u}, x ∈ domain ∧
        ZFSet.pair x (collapse domain x) = q := by
  rw [graph, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨x, hx⟩, hvalue⟩
    exact ⟨x, hx, hvalue⟩
  · rintro ⟨x, hx, hvalue⟩
    exact ⟨⟨x, hx⟩, hvalue⟩

@[simp]
theorem pair_mem_graph_iff {domain x y : ZFSet.{u}} :
    ZFSet.pair x y ∈ graph domain ↔
      x ∈ domain ∧ y = collapse domain x := by
  rw [mem_graph_iff]
  constructor
  · rintro ⟨z, hz, hpair⟩
    rcases ZFSet.pair_inj.mp hpair with ⟨hxz, hy⟩
    subst z
    exact ⟨hz, hy.symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl⟩



end

end MostowskiCollapse

namespace Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The first-order internalization interface -/

/--
A first-order definition of the collapse on `domain`.

The formula layout is `[domain, input, output]`.  `sound` rules out both
off-domain inputs and incorrect outputs.  `complete` is the substantive
well-founded-recursion obligation: it says that the formula has a witness in
`L` at every input in `domain`.
-/
structure CollapseFormulaSpec (domain : LCarrier.{u}) where
  formula : FOFormula 3
  sound : ∀ x y : LCarrier.{u},
    FOFormula.Satisfies LMem formula (snoc (snoc ![domain] x) y) →
      x.1 ∈ domain.1 ∧
        y.1 = MostowskiCollapse.collapse domain.1 x.1
  complete : ∀ x : LCarrier.{u}, x.1 ∈ domain.1 →
    ∃ y : LCarrier.{u},
      FOFormula.Satisfies LMem formula (snoc (snoc ![domain] x) y)

/-! A fully explicit sanity-check instance: collapse of a transitive set. -/

/-- On a transitive domain the collapse formula says `x ∈ domain ∧ y = x`. -/
def transitiveCollapseFormula : FOFormula 3 :=
  .conj (.mem (1 : Fin 3) (0 : Fin 3))
    (.eq (2 : Fin 3) (1 : Fin 3))

@[simp]
theorem satisfies_transitiveCollapseFormula
    (domain x y : LCarrier.{u}) :
    FOFormula.Satisfies LMem transitiveCollapseFormula
        (snoc (snoc ![domain] x) y) ↔
      x.1 ∈ domain.1 ∧ y = x := by
  have hassignment : snoc (snoc ![domain] x) y = ![domain, x, y] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]
  rfl









/-! ## Packaged internal range and graph -/

/-- A collapse whose range and Kuratowski graph are both actual members of `L`. -/
structure InternalizedCollapse (domain : LCarrier.{u}) where
  rangeCarrier : LCarrier.{u}
  graphCarrier : LCarrier.{u}
  range_val : rangeCarrier.1 = MostowskiCollapse.range domain.1
  graph_val : graphCarrier.1 = MostowskiCollapse.graph domain.1

/-- Package already established constructibility of the external range and graph. -/
def InternalizedCollapse.of_mem
    (domain : LCarrier.{u})
    (hrange : MostowskiCollapse.range domain.1 ∈ L)
    (hgraph : MostowskiCollapse.graph domain.1 ∈ L) :
    InternalizedCollapse domain where
  rangeCarrier := ⟨MostowskiCollapse.range domain.1, hrange⟩
  graphCarrier := ⟨MostowskiCollapse.graph domain.1, hgraph⟩
  range_val := rfl
  graph_val := rfl









/-! ## Consequences of an internalized collapse -/



@[simp]
theorem InternalizedCollapse.graphRel_iff
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (x y : LCarrier.{u}) :
    GraphRel w.graphCarrier x y ↔
      x.1 ∈ domain.1 ∧
        y.1 = MostowskiCollapse.collapse domain.1 x.1 := by
  rw [GraphRel, w.graph_val, MostowskiCollapse.pair_mem_graph_iff]

@[simp]
theorem InternalizedCollapse.graphValue_iff
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (x y : LCarrier.{u}) :
    Constructible.ContinuumFormula.GraphValue LMem
        w.graphCarrier x y ↔
      x.1 ∈ domain.1 ∧
        y.1 = MostowskiCollapse.collapse domain.1 x.1 := by
  rw [Constructible.ContinuumFormula.graphValue_lCarrier_iff_graphRel,
    w.graphRel_iff]







/-! ## The membership isomorphism -/

def internalCarrierEquivRaw (a : LCarrier.{u}) :
    InternalCarrier a ≃ {x : ZFSet.{u} // x ∈ a.1} where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, mem_L_of_mem x.2 a.2⟩, x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

def InternalizedCollapse.rawRangeEquiv
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain) :
    {z : ZFSet.{u} // z ∈ w.rangeCarrier.1} ≃
      {z : ZFSet.{u} // z ∈ MostowskiCollapse.range domain.1} where
  toFun z := ⟨z.1, by simpa only [w.range_val] using z.2⟩
  invFun z := ⟨z.1, by simpa only [w.range_val] using z.2⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

/-- The internal-carrier version of the Mostowski equivalence. -/
noncomputable def InternalizedCollapse.equivRange
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (hextensional : MostowskiCollapse.IsExtensional domain.1) :
    InternalCarrier domain ≃ InternalCarrier w.rangeCarrier :=
  ((((internalCarrierEquivRaw domain).trans
      (MostowskiCollapse.equivRange hextensional)).trans
      w.rawRangeEquiv.symm).trans
      (internalCarrierEquivRaw w.rangeCarrier).symm)

@[simp]
theorem InternalizedCollapse.equivRange_val
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (hextensional : MostowskiCollapse.IsExtensional domain.1)
    (x : InternalCarrier domain) :
    (w.equivRange hextensional x).1.1 =
      MostowskiCollapse.collapse domain.1 x.1.1 := by
  simp [InternalizedCollapse.equivRange, internalCarrierEquivRaw,
    InternalizedCollapse.rawRangeEquiv,
    MostowskiCollapse.equivRange_apply]

/-- The internalized Mostowski equivalence preserves and reflects membership. -/
@[simp]
theorem InternalizedCollapse.equivRange_mem_iff
    {domain : LCarrier.{u}} (w : InternalizedCollapse domain)
    (hextensional : MostowskiCollapse.IsExtensional domain.1)
    (x y : InternalCarrier domain) :
    (w.equivRange hextensional x).1.1 ∈
        (w.equivRange hextensional y).1.1 ↔
      x.1.1 ∈ y.1.1 := by
  simp only [w.equivRange_val]
  exact MostowskiCollapse.collapse_mem_collapse_iff
    hextensional x.2 y.2

end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_InternalMostowskiCollapse


/- Source module: Solutions.Work_CUGCH_CondensationGCHBridge -/
section GCHSource_Work_CUGCH_CondensationGCHBridge
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# The condensation-to-GCH bridge

This file isolates the exact use of Condensation in the usual proof of GCH
in `L`.  A cardinal-controlled elementary hull containing a subset `x` of an
internal cardinal `kappa` collapses to a level `L_beta`.  If the hull contains
every member of `kappa`, then the collapse fixes `x`; if the hull internally
injects into `kappa`, then `beta` is below the internal Hartogs successor of
`kappa`.  Consequently `x` belongs to that successor-indexed level.

The construction of the full all-formula Skolem hull and the cardinal bound
on the successor-indexed level are deliberately exposed as interfaces.  No
ambient `ZFSet.card` comparison is used as an internal graph witness.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section





end

end MostowskiCollapse

namespace ContinuumFormula

open Constructible.Model
open Constructible.MostowskiCollapse

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## Choosing the ambient reflection level -/

/-- Any two constructible parameters occur together in a condensation
reflection level.  The later Skolem construction starts inside this level. -/
theorem exists_condensationReflectionLevel_containing_pair
    (x y : LCarrier.{u}) :
    ∃ theta : Ordinal.{u},
      IsCondensationReflectionLevel theta ∧
        x.1 ∈ LStageZF theta ∧ y.1 ∈ LStageZF theta := by
  let bound := max
    (stageOf x.1 x.2) (stageOf y.1 y.2)
  rcases exists_condensationReflectionLevel bound with
    ⟨theta, hboundTheta, htheta⟩
  refine ⟨theta, htheta, ?_, ?_⟩
  · exact LStageZF_mono
      ((le_max_left (stageOf x.1 x.2) (stageOf y.1 y.2)).trans
        hboundTheta)
      (mem_LStageZF_stageOf x.1 x.2)
  · exact LStageZF_mono
      ((le_max_right (stageOf x.1 x.2) (stageOf y.1 y.2)).trans
        hboundTheta)
      (mem_LStageZF_stageOf y.1 y.2)

/-! ## Cardinal-controlled hulls -/

/-- The precise hull data consumed by the condensation argument for one
subset `x` of `kappa`.

`bound_subset` makes collapse fix subsets of `kappa`.  `small` is an
internally represented injection, not an ambient cardinal inequality.
`collapseData` records that the collapse range and graph are actual members
of `L`. -/
structure CardinalControlledHull
    (kappa x : LCarrier.{u}) where
  theta : Ordinal.{u}
  domain : LCarrier.{u}
  hull : CondensationHull theta domain.1
  collapseData : InternalizedCollapse domain
  bound_subset : kappa.1 ⊆ domain.1
  element_mem : x.1 ∈ domain.1
  small : Injects LMem domain kappa

namespace CardinalControlledHull

variable {kappa x : LCarrier.{u}}

/-- The ordinal index supplied by Condensation for this hull. -/
noncomputable def collapsedHeight (h : CardinalControlledHull kappa x) :
    Ordinal.{u} :=
  ordinalHeight (range h.domain.1)















end CardinalControlledHull

/-- Every constructible subset of `kappa` admits a fully elementary,
cardinality-controlled, internally collapsible hull.  Constructing this
object is the remaining all-formula Skolem-hull obligation. -/
def HasCardinalControlledHulls (kappa : LCarrier.{u}) : Prop :=
  ∀ x : LCarrier.{u}, IsSubsetOf LMem x kappa →
    Nonempty (CardinalControlledHull kappa x)





/-! ## The two remaining cardinal interfaces -/

/-- The internal version of `|L_(kappa^+)| <= kappa^+`.  Its proof is the
transfinite cardinal-union argument using the canonical stage order. -/
def HartogsStageBound (kappa : LCarrier.{u}) : Prop :=
  Injects LMem (stageLCarrier (internalHartogsOrdinal kappa))
    (internalHartogsLCarrier kappa)

/-- Every set is internally equinumerous with an internal cardinal.  This is
the cardinal-representative consequence of the internal well-ordering
theorem. -/
def HasInternalCardinalRepresentatives : Prop :=
  ∀ a : LCarrier.{u}, ∃ cardinal : LCarrier.{u},
    IsCardinal LMem cardinal ∧ Equinumerous LMem a cardinal









end

end ContinuumFormula

end Constructible

end
end GCHSource_Work_CUGCH_CondensationGCHBridge


