-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library04
-- name    : CH_ConstructibleGCH_Library04
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:13:38.824055+00:00
-- url     : https://prove2.me/theorems/431f0a2e-6709-4364-ae2a-4044c032f907
-- title:
--   Condensation and continuum-formula interfaces
-- statement:
--   The condensation interfaces record a limit stage, a subdomain, elementarity and the stage-covering data used by collapse induction. This library also introduces the membership formulas for injections, cardinals and continuum assertions, and the ordinal-height data of a collapse range.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/DefZFCollapse.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CondensationCore.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/ContinuumHypothesis.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/MostowskiCollapseOrdinals.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Condensation.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CondensationAssembly.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CondensationFixedParameters.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CondensationBareStage.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalBareHistoryOmega.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library03
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_DefZFCollapse -/
section GCHSource_Work_CUGCH_DefZFCollapse
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Definability and the Mostowski collapse

This file proves the successor-step compatibility needed by constructible
condensation.  If a set-sized membership structure is fully elementary in a
transitive ambient set, then its Mostowski collapse commutes with `DefZF` on
every argument for which both the argument and its definable powerset belong
to the small structure.

The finite tuple of parameters occurring in the definition of a subset is
not assumed to lie in the small structure.  Instead it is bound in one
first-order formula.  Full elementarity pulls witnesses into the small
structure, after which invariance of satisfaction under the collapse applies.
-/

section

open Set

universe u

namespace Constructible

noncomputable section

namespace Model

@[simp]
theorem satisfiesIn_disj_iff (M : Set ZFSet.{u}) {n : Nat}
    (phi psi : FOFormula n) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.disj phi psi) s <->
      SatisfiesIn M phi s ∨ SatisfiesIn M psi s := by
  classical
  simp only [FOFormula.disj, SatisfiesIn]
  tauto

@[simp]
theorem satisfiesIn_imp_iff (M : Set ZFSet.{u}) {n : Nat}
    (phi psi : FOFormula n) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp phi psi) s <->
      (SatisfiesIn M phi s -> SatisfiesIn M psi s) := by
  classical
  simp only [FOFormula.imp, satisfiesIn_disj_iff, SatisfiesIn]
  tauto

@[simp]
theorem satisfiesIn_biimp_iff (M : Set ZFSet.{u}) {n : Nat}
    (phi psi : FOFormula n) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp phi psi) s <->
      (SatisfiesIn M phi s <-> SatisfiesIn M psi s) := by
  classical
  simp only [FOFormula.biimp, SatisfiesIn, satisfiesIn_imp_iff]
  tauto

@[simp]
theorem satisfiesIn_boundedEx_iff (M : Set ZFSet.{u}) {n : Nat}
    (i : Fin n) (phi : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.boundedEx i phi) s <->
      ∃ x : ZFSet.{u}, x ∈ M ∧ x ∈ s i ∧
        SatisfiesIn M phi (snoc s x) := by
  simp [FOFormula.boundedEx]

@[simp]
theorem satisfiesIn_boundedAll_iff (M : Set ZFSet.{u}) {n : Nat}
    (i : Fin n) (phi : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.boundedAll i phi) s <->
      ∀ x : ZFSet.{u}, x ∈ M -> x ∈ s i ->
        SatisfiesIn M phi (snoc s x) := by
  classical
  simp only [FOFormula.boundedAll, SatisfiesIn,
    satisfiesIn_boundedEx_iff]
  constructor
  · intro h x hxM hxi
    by_contra hx
    exact h ⟨x, hxM, hxi, hx⟩
  · intro h hex
    rcases hex with ⟨x, hxM, hxi, hx⟩
    exact hx (h x hxM hxi)





end Model

/-! ## One formula saying that a set is a definable section -/

/-- Insert the coordinate for the defined subset between the bound `a` and
the original assignment. -/
def sectionRelativizeRename {n : Nat} :
    Fin (n + 2) -> Fin (n + 3) :=
  Fin.cases 0 (fun i => i.succ.succ)



/-- `subsetDefinitionFormula phi` has free layout `[a, y, params...]` and
asserts that `y` is the section of `phi` over the structure carried by `a`.
-/
def subsetDefinitionFormula {n : Nat} (phi : FOFormula (n + 1)) :
    FOFormula (n + 2) :=
  FOFormula.boundedAll (0 : Fin (n + 2))
    (FOFormula.biimp
      (.mem (Fin.last (n + 2)) (1 : Fin (n + 2)).castSucc)
      (FOFormula.rename sectionRelativizeRename
        (Delta0Formula.relativize phi).toFO))



/-! ## Binding all finite parameters in one object-language formula -/

/-- Bind all coordinates after the first two, requiring every witness to be
a member of coordinate zero. -/
def boundedExistsTail : (n : Nat) -> FOFormula (n + 2) -> FOFormula 2
  | 0, phi => phi
  | n + 1, phi =>
      boundedExistsTail n
        (FOFormula.boundedEx (0 : Fin (n + 2)) phi)





/-- Bind all parameters of a section definition.  The only free variables
are `[a, y]`. -/
def existsParametersDefinitionFormula {n : Nat}
    (phi : FOFormula (n + 1)) : FOFormula 2 :=
  boundedExistsTail n (subsetDefinitionFormula phi)

/-! ## Asking for a defined subset inside `DefZF a` -/

/-- Move the defined-set coordinate to the final position.  The source layout
is `[a, y, params...]`; the target layout is `[a, DefZF a, params..., y]`. -/
def definedSubsetWitnessRename {n : Nat} :
    Fin (n + 2) -> Fin (n + 3) :=
  Fin.cases 0
    (fun i => Fin.cases (Fin.last (n + 2))
      (fun j => (j.succ.succ).castSucc) i)



/-- Free layout `[a, d, params...]`.  This formula says that some `y ∈ d`
is the subset of `a` defined by `phi` and the displayed parameters. -/
def existsDefinedSubsetFormula {n : Nat}
    (phi : FOFormula (n + 1)) : FOFormula (n + 2) :=
  FOFormula.boundedEx (1 : Fin (n + 2))
    (FOFormula.rename definedSubsetWitnessRename
      (subsetDefinitionFormula phi))



namespace MostowskiCollapse









end MostowskiCollapse

end

end Constructible

end
end GCHSource_Work_CUGCH_DefZFCollapse


/- Source module: Solutions.Work_CUGCH_CondensationCore -/
section GCHSource_Work_CUGCH_CondensationCore
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# An abstract core for constructible condensation

This file isolates the final order-theoretic step of a condensation argument.
For a transitive set `M`, `ordinalHeight M` is the supremum of the successors
of the ranks of the ordinal members of `M`.  Consequently, the ordinals in
`M` are exactly the von Neumann codes below this height.

The final theorem identifies `M` with the constructible level at its ordinal
height, under three explicit closure hypotheses:

* ordinal successors of members remain in `M`;
* every member of `M` occurs in a constructible level indexed by an ordinal
  belonging to `M`;
* every constructible level indexed by an ordinal belonging to `M` is itself
  an element of `M`.

These hypotheses are the interface that a later Skolem-hull and Mostowski
collapse development must establish.  No elementarity or collapse theorem is
asserted in this file.
-/

section

open Set

universe u

namespace Constructible

section ZFC

/--
The ordinal height of a set is the supremum of the successor ranks of its
ordinal members.  The zero contribution from non-ordinal members lets us use
the small type `ZFCarrier M` directly as the indexing type.
-/
noncomputable def ordinalHeight (M : ZFSet.{u}) : Ordinal.{u} :=
  by
    classical
    exact iSup fun x : ZFCarrier M =>
      if x.1.IsOrdinal then Order.succ x.1.rank else 0







/-- Closure of the ordinal members of `M` under ordinal successor. -/
def OrdinalSuccessorClosed (M : ZFSet.{u}) : Prop :=
  ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ M →
    (Order.succ alpha).toZFSet ∈ M

/--
Every member of `M` occurs in a constructible level whose ordinal index is
itself represented in `M`.
-/
def InternallyStageCovered (M : ZFSet.{u}) : Prop :=
  ∀ x : ZFSet.{u}, x ∈ M →
    ∃ alpha : Ordinal.{u}, alpha.toZFSet ∈ M ∧ x ∈ LStageZF alpha

/-- `M` contains every constructible level indexed by one of its ordinals. -/
def ContainsInternalLStages (M : ZFSet.{u}) : Prop :=
  ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ M → LStageZF alpha ∈ M









end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_CondensationCore


/- Source module: Solutions.Work_CUGCH_ContinuumHypothesis -/
section GCHSource_Work_CUGCH_ContinuumHypothesis
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# First-order formulations of CH and GCH

This file defines the Continuum Hypothesis and the Generalized Continuum
Hypothesis as parameter-free formulas in the membership language.  Cardinal
comparison is expressed internally through sets of Kuratowski pairs coding
bijections; no ambient Lean cardinal is used in either sentence.

The formula fragments are accompanied by semantics for an arbitrary type and
an arbitrary binary membership relation.  Consequently the final semantic
theorems can later be instantiated both in `LCarrier` and in other
set-theoretic structures.
-/

section

universe u

namespace Constructible.ContinuumFormula

/-! ## Semantic relations -/

def IsEmptySet {A : Type u} (E : A → A → Prop) (x : A) : Prop :=
  ∀ z : A, ¬E z x

def IsSubsetOf {A : Type u} (E : A → A → Prop) (x y : A) : Prop :=
  ∀ z : A, E z x → E z y

def IsSingletonOf {A : Type u} (E : A → A → Prop)
    (singleton x : A) : Prop :=
  E x singleton ∧ ∀ z : A, E z singleton → z = x

def IsUnorderedPairOf {A : Type u} (E : A → A → Prop)
    (pair x y : A) : Prop :=
  E x pair ∧ E y pair ∧
    ∀ z : A, E z pair → z = x ∨ z = y

def IsKuratowskiPairOf {A : Type u} (E : A → A → Prop)
    (pair x y : A) : Prop :=
  (∃ singleton : A,
      E singleton pair ∧ IsSingletonOf E singleton x) ∧
    (∃ unordered : A,
      E unordered pair ∧ IsUnorderedPairOf E unordered x y) ∧
    ∀ z : A, E z pair →
      IsSingletonOf E z x ∨ IsUnorderedPairOf E z x y

def GraphValue {A : Type u} (E : A → A → Prop)
    (graph x y : A) : Prop :=
  ∃ pair : A, E pair graph ∧ IsKuratowskiPairOf E pair x y

def HasUniqueImage {A : Type u} (E : A → A → Prop)
    (graph x codomain : A) : Prop :=
  ∃ y : A, E y codomain ∧ GraphValue E graph x y ∧
    ∀ z : A, E z codomain → GraphValue E graph x z → z = y

def HasUniquePreimage {A : Type u} (E : A → A → Prop)
    (graph domain y : A) : Prop :=
  ∃ x : A, E x domain ∧ GraphValue E graph x y ∧
    ∀ z : A, E z domain → GraphValue E graph z y → z = x

def IsGraphBetween {A : Type u} (E : A → A → Prop)
    (graph domain codomain : A) : Prop :=
  ∀ pair : A, E pair graph →
    ∃ x : A, E x domain ∧
      ∃ y : A, E y codomain ∧ IsKuratowskiPairOf E pair x y

def IsBijection {A : Type u} (E : A → A → Prop)
    (graph domain codomain : A) : Prop :=
  IsGraphBetween E graph domain codomain ∧
    (∀ x : A, E x domain → HasUniqueImage E graph x codomain) ∧
      ∀ y : A, E y codomain → HasUniquePreimage E graph domain y

def Equinumerous {A : Type u} (E : A → A → Prop) (x y : A) : Prop :=
  ∃ graph : A, IsBijection E graph x y

/-! ## Formula fragments for pairs and bijections -/

/-- `s set` behaves as the singleton of `s x`. -/
def singletonAt {n : Nat} (set x : Fin n) : FOFormula n :=
  .conj (.mem x set)
    (FOFormula.boundedAll set
      (.eq (Fin.last n) x.castSucc))

@[simp]
theorem satisfies_singletonAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (set x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (singletonAt set x) s ↔
      IsSingletonOf E (s set) (s x) := by
  simp only [singletonAt, FOFormula.Satisfies,
    FOFormula.satisfies_boundedAll, snoc_last, snoc_castSucc,
    IsSingletonOf]

/-- `s pair` behaves as the unordered pair of `s x` and `s y`. -/
def unorderedPairAt {n : Nat} (pair x y : Fin n) : FOFormula n :=
  .conj (.mem x pair)
    (.conj (.mem y pair)
      (FOFormula.boundedAll pair
        (FOFormula.disj
          (.eq (Fin.last n) x.castSucc)
          (.eq (Fin.last n) y.castSucc))))

@[simp]
theorem satisfies_unorderedPairAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (pair x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (unorderedPairAt pair x y) s ↔
      IsUnorderedPairOf E (s pair) (s x) (s y) := by
  simp only [unorderedPairAt, FOFormula.Satisfies,
    FOFormula.satisfies_boundedAll, FOFormula.satisfies_disj,
    snoc_last, snoc_castSucc, IsUnorderedPairOf]

/-- `s pair` behaves as the Kuratowski ordered pair of `s x` and `s y`. -/
def kuratowskiPairAt {n : Nat} (pair x y : Fin n) : FOFormula n :=
  .conj
    (FOFormula.boundedEx pair
      (singletonAt (Fin.last n) x.castSucc))
    (.conj
      (FOFormula.boundedEx pair
        (unorderedPairAt (Fin.last n) x.castSucc y.castSucc))
      (FOFormula.boundedAll pair
        (FOFormula.disj
          (singletonAt (Fin.last n) x.castSucc)
          (unorderedPairAt (Fin.last n) x.castSucc y.castSucc))))

@[simp]
theorem satisfies_kuratowskiPairAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (pair x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (kuratowskiPairAt pair x y) s ↔
      IsKuratowskiPairOf E (s pair) (s x) (s y) := by
  simp only [kuratowskiPairAt, FOFormula.Satisfies,
    FOFormula.satisfies_boundedEx, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_disj, satisfies_singletonAt,
    satisfies_unorderedPairAt, snoc_last, snoc_castSucc,
    IsKuratowskiPairOf]

/-- The graph `s graph` contains the ordered pair `(s x, s y)`. -/
def graphValueAt {n : Nat} (graph x y : Fin n) : FOFormula n :=
  .ex (.conj
    (.mem (Fin.last n) graph.castSucc)
    (kuratowskiPairAt
      (Fin.last n) x.castSucc y.castSucc))

@[simp]
theorem satisfies_graphValueAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (graph x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (graphValueAt graph x y) s ↔
      GraphValue E (s graph) (s x) (s y) := by
  simp only [graphValueAt, FOFormula.Satisfies,
    satisfies_kuratowskiPairAt, snoc_last, snoc_castSucc,
    GraphValue]

/-- The graph has exactly one value in `codomain` at `x`. -/
def uniqueImageAt {n : Nat}
    (graph x codomain : Fin n) : FOFormula n :=
  FOFormula.boundedEx codomain
    (.conj
      (graphValueAt graph.castSucc x.castSucc (Fin.last n))
      (FOFormula.boundedAll codomain.castSucc
        (FOFormula.imp
          (graphValueAt graph.castSucc.castSucc
            x.castSucc.castSucc (Fin.last (n + 1)))
          (.eq (Fin.last (n + 1)) (Fin.last n).castSucc))))

@[simp]
theorem satisfies_uniqueImageAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (graph x codomain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (uniqueImageAt graph x codomain) s ↔
      HasUniqueImage E (s graph) (s x) (s codomain) := by
  simp only [uniqueImageAt, FOFormula.satisfies_boundedEx,
    FOFormula.Satisfies, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_imp, satisfies_graphValueAt,
    snoc_last, snoc_castSucc, HasUniqueImage]

/-- The graph has exactly one preimage in `domain` at `y`. -/
def uniquePreimageAt {n : Nat}
    (graph domain y : Fin n) : FOFormula n :=
  FOFormula.boundedEx domain
    (.conj
      (graphValueAt graph.castSucc (Fin.last n) y.castSucc)
      (FOFormula.boundedAll domain.castSucc
        (FOFormula.imp
          (graphValueAt graph.castSucc.castSucc
            (Fin.last (n + 1)) y.castSucc.castSucc)
          (.eq (Fin.last (n + 1)) (Fin.last n).castSucc))))

@[simp]
theorem satisfies_uniquePreimageAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (graph domain y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (uniquePreimageAt graph domain y) s ↔
      HasUniquePreimage E (s graph) (s domain) (s y) := by
  simp only [uniquePreimageAt, FOFormula.satisfies_boundedEx,
    FOFormula.Satisfies, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_imp, satisfies_graphValueAt,
    snoc_last, snoc_castSucc, HasUniquePreimage]

/-- Every member of `graph` is a pair from `domain × codomain`. -/
def graphBetweenAt {n : Nat}
    (graph domain codomain : Fin n) : FOFormula n :=
  FOFormula.boundedAll graph
    (FOFormula.boundedEx domain.castSucc
      (FOFormula.boundedEx codomain.castSucc.castSucc
        (kuratowskiPairAt
          (Fin.last n).castSucc.castSucc
          (Fin.last (n + 1)).castSucc
          (Fin.last (n + 2)))))

@[simp]
theorem satisfies_graphBetweenAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (graph domain codomain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (graphBetweenAt graph domain codomain) s ↔
      IsGraphBetween E (s graph) (s domain) (s codomain) := by
  simp only [graphBetweenAt, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_boundedEx, satisfies_kuratowskiPairAt,
    snoc_last, snoc_castSucc, IsGraphBetween]

/-- `graph` codes a bijection from `domain` onto `codomain`. -/
def bijectionAt {n : Nat}
    (graph domain codomain : Fin n) : FOFormula n :=
  .conj (graphBetweenAt graph domain codomain)
    (.conj
      (FOFormula.boundedAll domain
        (uniqueImageAt graph.castSucc
          (Fin.last n) codomain.castSucc))
      (FOFormula.boundedAll codomain
        (uniquePreimageAt graph.castSucc
          domain.castSucc (Fin.last n))))

@[simp]
theorem satisfies_bijectionAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (graph domain codomain : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (bijectionAt graph domain codomain) s ↔
      IsBijection E (s graph) (s domain) (s codomain) := by
  simp only [bijectionAt, FOFormula.Satisfies,
    satisfies_graphBetweenAt, FOFormula.satisfies_boundedAll,
    satisfies_uniqueImageAt, satisfies_uniquePreimageAt,
    snoc_last, snoc_castSucc, IsBijection]

/-- There is a set coding a bijection between `x` and `y`. -/
def equinumerousAt {n : Nat} (x y : Fin n) : FOFormula n :=
  .ex (bijectionAt (Fin.last n) x.castSucc y.castSucc)

@[simp]
theorem satisfies_equinumerousAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (equinumerousAt x y) s ↔
      Equinumerous E (s x) (s y) := by
  simp only [equinumerousAt, FOFormula.Satisfies,
    satisfies_bijectionAt, snoc_last, snoc_castSucc,
    Equinumerous]

/-! ## Subsets, ordinals, and cardinals -/

def IsTransitiveSet {A : Type u} (E : A → A → Prop) (x : A) : Prop :=
  ∀ y : A, E y x → ∀ z : A, E z y → E z x

def IsVonNeumannOrdinal {A : Type u} (E : A → A → Prop) (x : A) : Prop :=
  IsTransitiveSet E x ∧
    ∀ y : A, E y x → IsTransitiveSet E y

def IsPowerSetOf {A : Type u} (E : A → A → Prop)
    (base power : A) : Prop :=
  ∀ x : A, E x power ↔ IsSubsetOf E x base

def IsSuccessorSetOf {A : Type u} (E : A → A → Prop)
    (successor x : A) : Prop :=
  ∀ z : A, E z successor ↔ E z x ∨ z = x

def IsInductiveSet {A : Type u} (E : A → A → Prop) (w : A) : Prop :=
  (∃ empty : A, IsEmptySet E empty ∧ E empty w) ∧
    ∀ x : A, E x w →
      ∃ successor : A,
        IsSuccessorSetOf E successor x ∧ E successor w

def IsOmega {A : Type u} (E : A → A → Prop) (omega : A) : Prop :=
  IsInductiveSet E omega ∧
    ∀ w : A, IsInductiveSet E w → IsSubsetOf E omega w

def IsCardinal {A : Type u} (E : A → A → Prop) (kappa : A) : Prop :=
  IsVonNeumannOrdinal E kappa ∧
    ∀ alpha : A, E alpha kappa →
      ¬Equinumerous E alpha kappa

def IsSuccessorCardinal {A : Type u} (E : A → A → Prop)
    (kappa next : A) : Prop :=
  IsCardinal E kappa ∧ IsCardinal E next ∧ E kappa next ∧
    ¬∃ intermediate : A,
      IsCardinal E intermediate ∧
        E kappa intermediate ∧ E intermediate next

/-- Every member of `x` is a member of `y`. -/
def subsetAt {n : Nat} (x y : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.imp
      (.mem (Fin.last n) x.castSucc)
      (.mem (Fin.last n) y.castSucc))

@[simp]
theorem satisfies_subsetAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (x y : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (subsetAt x y) s ↔
      IsSubsetOf E (s x) (s y) := by
  simp only [subsetAt, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, FOFormula.Satisfies,
    snoc_last, snoc_castSucc, IsSubsetOf]

/-- `power` contains exactly the subsets of `base`. -/
def powerSetAt {n : Nat} (power base : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last n) power.castSucc)
      (subsetAt (Fin.last n) base.castSucc))

@[simp]
theorem satisfies_powerSetAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (power base : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (powerSetAt power base) s ↔
      IsPowerSetOf E (s base) (s power) := by
  simp only [powerSetAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_subsetAt, snoc_last, snoc_castSucc,
    IsPowerSetOf]

 theorem satisfies_isOrdinal_singleton
    {A : Type u} (E : A → A → Prop) (x : A) :
    FOFormula.Satisfies E OrdinalFormula.isOrdinal ![x] ↔
      IsVonNeumannOrdinal E x := by
  simp only [OrdinalFormula.isOrdinal, FOFormula.Satisfies,
    OrdinalFormula.transitive, OrdinalFormula.membersTransitive,
    FOFormula.satisfies_boundedAll, Matrix.cons_val_zero,
    snoc_last, IsVonNeumannOrdinal,
    IsTransitiveSet]
  rw [show (0 : Fin 3) = (0 : Fin 1).castSucc.castSucc by decide]
  rw [show (1 : Fin 4) = (Fin.last 1).castSucc.castSucc by decide]
  simp only [snoc_castSucc, snoc_last, Matrix.cons_val_zero]

/-- Put the von Neumann ordinal predicate at coordinate `i`. -/
def isOrdinalAt {n : Nat} (i : Fin n) : FOFormula n :=
  FOFormula.rename (fun _ : Fin 1 => i) OrdinalFormula.isOrdinal

@[simp]
theorem satisfies_isOrdinalAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (i : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (isOrdinalAt i) s ↔
      IsVonNeumannOrdinal E (s i) := by
  rw [isOrdinalAt, FOFormula.satisfies_rename]
  have hassignment : (fun _ : Fin 1 => s i) = ![s i] := by
    funext j
    exact Fin.eq_zero j ▸ rfl
  rw [hassignment, satisfies_isOrdinal_singleton]

/-- Coordinate `i` has no members. -/
def emptySetAt {n : Nat} (i : Fin n) : FOFormula n :=
  FOFormula.all (.neg (.mem (Fin.last n) i.castSucc))

@[simp]
theorem satisfies_emptySetAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (i : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (emptySetAt i) s ↔
      IsEmptySet E (s i) := by
  simp only [emptySetAt, FOFormula.satisfies_all,
    FOFormula.Satisfies, snoc_last, snoc_castSucc,
    IsEmptySet]

/-- `successor` is the von Neumann successor of `x`. -/
def successorSetAt {n : Nat} (successor x : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last n) successor.castSucc)
      (FOFormula.disj
        (.mem (Fin.last n) x.castSucc)
        (.eq (Fin.last n) x.castSucc)))

@[simp]
theorem satisfies_successorSetAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (successor x : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (successorSetAt successor x) s ↔
      IsSuccessorSetOf E (s successor) (s x) := by
  simp only [successorSetAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.satisfies_disj,
    FOFormula.Satisfies, snoc_last, snoc_castSucc,
    IsSuccessorSetOf]

/-- Coordinate `i` is inductive. -/
def inductiveSetAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (.ex (.conj
      (emptySetAt (Fin.last n))
      (.mem (Fin.last n) i.castSucc)))
    (FOFormula.all
      (FOFormula.imp
        (.mem (Fin.last n) i.castSucc)
        (.ex (.conj
          (successorSetAt
            (Fin.last (n + 1)) (Fin.last n).castSucc)
          (.mem (Fin.last (n + 1)) i.castSucc.castSucc)))))

@[simp]
theorem satisfies_inductiveSetAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (i : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (inductiveSetAt i) s ↔
      IsInductiveSet E (s i) := by
  simp only [inductiveSetAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_emptySetAt, satisfies_successorSetAt,
    snoc_last, snoc_castSucc, IsInductiveSet]

/-- Coordinate `i` is the least inductive set. -/
def omegaAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (inductiveSetAt i)
    (FOFormula.all
      (FOFormula.imp
        (inductiveSetAt (Fin.last n))
        (subsetAt i.castSucc (Fin.last n))))

@[simp]
theorem satisfies_omegaAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (i : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (omegaAt i) s ↔
      IsOmega E (s i) := by
  simp only [omegaAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_inductiveSetAt, satisfies_subsetAt,
    snoc_last, snoc_castSucc, IsOmega]

/-- `kappa` is an initial ordinal, hence an internal cardinal. -/
def cardinalAt {n : Nat} (kappa : Fin n) : FOFormula n :=
  .conj
    (isOrdinalAt kappa)
    (FOFormula.boundedAll kappa
      (.neg (equinumerousAt (Fin.last n) kappa.castSucc)))

@[simp]
theorem satisfies_cardinalAt {A : Type u} (E : A → A → Prop)
    {n : Nat} (kappa : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (cardinalAt kappa) s ↔
      IsCardinal E (s kappa) := by
  simp only [cardinalAt, FOFormula.Satisfies,
    satisfies_isOrdinalAt, FOFormula.satisfies_boundedAll,
    satisfies_equinumerousAt, snoc_last, snoc_castSucc,
    IsCardinal]

/-- `next` is the least internal cardinal strictly above `kappa`. -/
def successorCardinalAt {n : Nat}
    (kappa next : Fin n) : FOFormula n :=
  .conj (cardinalAt kappa)
    (.conj (cardinalAt next)
      (.conj (.mem kappa next)
        (.neg (.ex
          (.conj (cardinalAt (Fin.last n))
            (.conj
              (.mem kappa.castSucc (Fin.last n))
              (.mem (Fin.last n) next.castSucc)))))))

@[simp]
theorem satisfies_successorCardinalAt
    {A : Type u} (E : A → A → Prop) {n : Nat}
    (kappa next : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (successorCardinalAt kappa next) s ↔
      IsSuccessorCardinal E (s kappa) (s next) := by
  simp only [successorCardinalAt, FOFormula.Satisfies,
    satisfies_cardinalAt, snoc_last, snoc_castSucc,
    IsSuccessorCardinal]

/-! ## CH and GCH -/

/-- Semantic form of the Continuum Hypothesis in a membership structure. -/
def ModelsCH {A : Type u} (E : A → A → Prop) : Prop :=
  ∃ omega next power : A,
    IsOmega E omega ∧
      IsSuccessorCardinal E omega next ∧
      IsPowerSetOf E omega power ∧
      Equinumerous E power next

/-- Semantic form of the Generalized Continuum Hypothesis. -/
def ModelsGCH {A : Type u} (E : A → A → Prop) : Prop :=
  ∃ omega : A,
    IsOmega E omega ∧ IsCardinal E omega ∧
      ∀ kappa : A,
        (IsCardinal E kappa ∧ IsSubsetOf E omega kappa) →
          ∃ next power : A,
            IsSuccessorCardinal E kappa next ∧
              IsPowerSetOf E kappa power ∧
              Equinumerous E power next

/-- Layout `(omega, omegaOne, powerOmega)`. -/
def chCoreFormula : FOFormula 3 :=
  .conj (omegaAt (0 : Fin 3))
    (.conj (successorCardinalAt (0 : Fin 3) (1 : Fin 3))
      (.conj (powerSetAt (2 : Fin 3) (0 : Fin 3))
        (equinumerousAt (2 : Fin 3) (1 : Fin 3))))

/-- The parameter-free first-order formula `P(omega) ≈ omegaOne`. -/
def chFormula : FOFormula 0 :=
  .ex (.ex (.ex chCoreFormula))

 theorem ch_assignment
    {A : Type u} (omega next power : A) :
    snoc (snoc (snoc (fun i : Fin 0 => Fin.elim0 i) omega)
      next) power = ![omega, next, power] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_chFormula {A : Type u} (E : A → A → Prop) :
    FOFormula.Satisfies E chFormula
        (fun i : Fin 0 => Fin.elim0 i) ↔
      ModelsCH E := by
  simp only [chFormula, FOFormula.Satisfies]
  apply exists_congr
  intro omega
  apply exists_congr
  intro next
  apply exists_congr
  intro power
  rw [ch_assignment]
  simp only [chCoreFormula, FOFormula.Satisfies,
    satisfies_omegaAt, satisfies_successorCardinalAt,
    satisfies_powerSetAt, satisfies_equinumerousAt,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- With `omega` at coordinate zero, assert GCH at every internal cardinal
containing it. -/
def gchAtOmegaFormula : FOFormula 1 :=
  .conj (omegaAt (0 : Fin 1))
    (.conj (cardinalAt (0 : Fin 1))
      (FOFormula.all
        (FOFormula.imp
          (.conj
            (cardinalAt (Fin.last 1))
            (subsetAt (0 : Fin 1).castSucc (Fin.last 1)))
          (.ex (.ex
            (.conj
              (successorCardinalAt (1 : Fin 4) (2 : Fin 4))
              (.conj
                (powerSetAt (3 : Fin 4) (1 : Fin 4))
                (equinumerousAt (3 : Fin 4) (2 : Fin 4)))))))))

/-- The parameter-free first-order formulation of GCH. -/
def gchFormula : FOFormula 0 :=
  .ex gchAtOmegaFormula

 theorem gch_omega_assignment {A : Type u} (omega : A) :
    snoc (fun i : Fin 0 => Fin.elim0 i) omega = ![omega] := by
  funext i
  fin_cases i
  rfl

 theorem gch_kappa_assignment {A : Type u}
    (omega kappa : A) :
    snoc ![omega] kappa = ![omega, kappa] := by
  funext i
  fin_cases i <;> rfl

 theorem gch_witness_assignment {A : Type u}
    (omega kappa next power : A) :
    snoc (snoc ![omega, kappa] next) power =
      ![omega, kappa, next, power] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_gchFormula {A : Type u} (E : A → A → Prop) :
    FOFormula.Satisfies E gchFormula
        (fun i : Fin 0 => Fin.elim0 i) ↔
      ModelsGCH E := by
  simp only [gchFormula, FOFormula.Satisfies]
  apply exists_congr
  intro omega
  rw [gch_omega_assignment]
  simp only [gchAtOmegaFormula, FOFormula.Satisfies,
    satisfies_omegaAt, satisfies_cardinalAt,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    Matrix.cons_val_zero]
  constructor
  · rintro ⟨homega, homegaCardinal, hgeneral⟩
    refine ⟨homega, homegaCardinal, ?_⟩
    intro kappa hkappa
    have hbody := hgeneral kappa
    rw [gch_kappa_assignment] at hbody
    simp only [satisfies_subsetAt] at hbody
    rcases hbody hkappa with ⟨next, power, hnext⟩
    rw [gch_witness_assignment] at hnext
    refine ⟨next, power, ?_⟩
    simpa only [FOFormula.Satisfies,
      satisfies_successorCardinalAt, satisfies_powerSetAt,
      satisfies_equinumerousAt, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] using hnext
  · rintro ⟨homega, homegaCardinal, hgeneral⟩
    refine ⟨homega, homegaCardinal, ?_⟩
    intro kappa
    rw [gch_kappa_assignment]
    simp only [satisfies_subsetAt]
    intro hkappa
    rcases hgeneral kappa hkappa with ⟨next, power, hnext⟩
    refine ⟨next, power, ?_⟩
    rw [gch_witness_assignment]
    simpa only [FOFormula.Satisfies,
      satisfies_successorCardinalAt, satisfies_powerSetAt,
      satisfies_equinumerousAt, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] using hnext

/-- CH as a Mathlib sentence in the first-order language of membership. -/
def chSentence : FirstOrder.Language.setTheory.Sentence :=
  Model.toSentence chFormula

/-- GCH as a Mathlib sentence in the first-order language of membership. -/
def gchSentence : FirstOrder.Language.setTheory.Sentence :=
  Model.toSentence gchFormula

/-- The translated CH sentence has exactly the relation-parametric semantics
`ModelsCH`. -/
@[simp]
theorem realizes_chSentence_iff {A : Type u} (E : A → A → Prop) :
    Model.realizes E chSentence (fun i : Fin 0 => Fin.elim0 i) ↔
      ModelsCH E := by
  rw [chSentence, Model.realizes_toBoundedFormula,
    satisfies_chFormula]

/-- The translated GCH sentence has exactly the relation-parametric semantics
`ModelsGCH`. -/
@[simp]
theorem realizes_gchSentence_iff {A : Type u} (E : A → A → Prop) :
    Model.realizes E gchSentence (fun i : Fin 0 => Fin.elim0 i) ↔
      ModelsGCH E := by
  rw [gchSentence, Model.realizes_toBoundedFormula,
    satisfies_gchFormula]

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_ContinuumHypothesis


/- Source module: Solutions.Work_CUGCH_MostowskiCollapseOrdinals -/
section GCHSource_Work_CUGCH_MostowskiCollapseOrdinals
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Ordinals through the Mostowski collapse

This file records the order-theoretic part of constructible condensation.
Restricting membership to an arbitrary domain and collapsing an ambient von
Neumann ordinal still produces a von Neumann ordinal.  If the ordinal itself
belongs to the domain, collapse also commutes with ordinal successor.

The final part packages these structural facts for the three hypotheses used
by `CondensationCore`.  Full satisfaction absoluteness is used only to reflect
the assertion that a preimage is an ordinal; no external cardinal or choice
argument occurs here.
-/

section

open Set
open Constructible.ContinuumFormula

universe u

namespace Constructible.MostowskiCollapse

noncomputable section

/-- The restricted collapse of an ambient ordinal is transitive.  No
extensionality or closure assumption on the restricting domain is needed. -/
theorem collapse_isTransitive_of_isOrdinal {domain x : ZFSet.{u}}
    (hx : x.IsOrdinal) :
    (collapse domain x).IsTransitive := by
  intro z hz w hw
  rcases mem_collapse_iff.mp hz with ⟨y, hyx, hydomain, rfl⟩
  rcases mem_collapse_iff.mp hw with ⟨v, hvy, hvdomain, rfl⟩
  exact mem_collapse_iff.mpr
    ⟨v, hx.mem_trans hvy hyx, hvdomain, rfl⟩

/-- Restricting an ordinal to any collection of predecessors and taking its
Mostowski collapse again gives a von Neumann ordinal. -/
theorem collapse_isOrdinal_of_isOrdinal {domain x : ZFSet.{u}}
    (hx : x.IsOrdinal) :
    (collapse domain x).IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  refine ⟨collapse_isTransitive_of_isOrdinal hx, ?_⟩
  intro z hz
  rcases mem_collapse_iff.mp hz with ⟨y, hyx, _hydomain, rfl⟩
  exact collapse_isTransitive_of_isOrdinal (hx.mem hyx)

/-- The ordinal represented by the restricted collapse of `alpha`. -/
noncomputable def collapseOrdinal (domain : ZFSet.{u})
    (alpha : Ordinal.{u}) : Ordinal.{u} :=
  (collapse domain alpha.toZFSet).rank

/-- The collapse of an ordinal code is the code of `collapseOrdinal`. -/
@[simp]
theorem collapseOrdinal_toZFSet (domain : ZFSet.{u})
    (alpha : Ordinal.{u}) :
    (collapseOrdinal domain alpha).toZFSet =
      collapse domain alpha.toZFSet := by
  exact (collapse_isOrdinal_of_isOrdinal
    (ZFSet.isOrdinal_toZFSet alpha)).toZFSet_rank_eq









/-! ## Ordinal reflection through full elementarity -/





/-- A source-domain closure assumption stated directly in terms of ambient
von Neumann successor. -/
def SourceOrdinalSuccessorClosed (domain : ZFSet.{u}) : Prop :=
  ∀ ⦃x : ZFSet.{u}⦄, x ∈ domain → x.IsOrdinal → insert x x ∈ domain

/-- The one-parameter formula asserting that the von Neumann successor of
the parameter exists. -/
def successorExistsFormula : FOFormula 1 :=
  .ex (successorSetAt (Fin.last 1) (0 : Fin 2))







/-- The one-parameter formula asserting that the parameter is a successor
set and returning its predecessor as the existential witness. -/
def predecessorExistsFormula : FOFormula 1 :=
  .ex (successorSetAt (0 : Fin 2) (Fin.last 1))

















/-! ## Constructible stages at limit indices -/

/-- Collapse compatibility at one constructible stage. -/
def CollapseStageCompatibleAt (domain : ZFSet.{u})
    (alpha : Ordinal.{u}) : Prop :=
  collapse domain (LStageZF alpha) =
    LStageZF (collapseOrdinal domain alpha)

/-- The bounded stage-witness property required in the forward direction of
the limit step.  Full elementarity supplies this property by reflecting the
existential assertion `x ∈ L_beta` with `beta ∈ alpha`. -/
def HasSmallerInternalLStageWitnesses (domain : ZFSet.{u})
    (alpha : Ordinal.{u}) : Prop :=
  ∀ ⦃x : ZFSet.{u}⦄, x ∈ domain → x ∈ LStageZF alpha →
    ∃ beta : Ordinal.{u}, beta < alpha ∧
      beta.toZFSet ∈ domain ∧ x ∈ LStageZF beta

/-- The collapse of the empty set is empty. -/
@[simp]
theorem collapse_empty (domain : ZFSet.{u}) :
    collapse domain (∅ : ZFSet.{u}) = ∅ := by
  apply ZFSet.ext
  intro z
  rw [mem_collapse_iff]
  simp

/-- The collapsed ordinal represented by zero is zero. -/
@[simp]
theorem collapseOrdinal_zero (domain : ZFSet.{u}) :
    collapseOrdinal domain 0 = 0 := by
  apply Ordinal.toZFSet_injective
  rw [collapseOrdinal_toZFSet, Ordinal.toZFSet_zero,
    collapse_empty]







end

end Constructible.MostowskiCollapse

end
end GCHSource_Work_CUGCH_MostowskiCollapseOrdinals


/- Source module: Solutions.Work_CUGCH_Condensation -/
section GCHSource_Work_CUGCH_Condensation
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Condensation for constructible levels

This file assembles the order-theoretic condensation core with full
elementarity and the Mostowski collapse.  The only set-recursion input is the
explicit predicate `CollapseDefZFCommutes`: it records that collapse commutes
with one successor step of the constructible hierarchy.  The corresponding
theorem is proved separately from the definability of `DefZF` and is not
silently assumed here.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

/-- The exact successor-step interface needed by the condensation proof. -/
def CollapseDefZFCommutes (domain : ZFSet.{u}) : Prop :=
  forall {a : ZFSet.{u}}, a ∈ domain -> DefZF a ∈ domain ->
    collapse domain (DefZF a) = DefZF (collapse domain a)

/-- Internal proof package for a set-sized elementary hull of a condensation
reflection level. The `fixed_mem` field is derived from full elementarity by
`CondensationHull.of_elementary`; callers need not assume it separately. -/
structure CondensationHull (theta : Ordinal.{u}) (domain : ZFSet.{u}) : Prop where
  reflection : Model.IsCondensationReflectionLevel theta
  subset_stage : domain ⊆ LStageZF theta
  satisfactionAbsolute :
    SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u})
  fixed_mem : forall i : Fin 13,
    (Model.stageHistoryFixedParameters.{u} i).1 ∈ domain

namespace CondensationHull

variable {theta : Ordinal.{u}} {domain : ZFSet.{u}}











/-- Raw tuple consisting of the thirteen fixed parameters followed by an
index and a proposed stage. -/
def stageAssignment (index stage : ZFSet.{u}) : Tuple ZFSet.{u} 15 :=
  snoc
    (snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1) index)
    stage

@[simp]
theorem stageAssignment_fixed (index stage : ZFSet.{u}) (i : Fin 13) :
    stageAssignment index stage i.castSucc.castSucc =
      (Model.stageHistoryFixedParameters.{u} i).1 := by
  simp [stageAssignment]

@[simp]
theorem stageAssignment_index (index stage : ZFSet.{u}) :
    stageAssignment index stage (13 : Fin 15) = index := by
  rfl

@[simp]
theorem stageAssignment_stage (index stage : ZFSet.{u}) :
    stageAssignment index stage (14 : Fin 15) = stage := by
  rfl









/-! ## Bounded stage witnesses for the limit step -/

/-- Select `(fixed13, index, stage)` from the layout
`(fixed13, x, bound, index, stage)`. -/
def boundedStageInternalRename : Fin 15 -> Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i14 => Fin.lastCases
      (15 : Fin 17)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

/-- Layout `(fixed13, x, bound)`. -/
def boundedStageParameters (x bound : ZFSet.{u}) : Tuple ZFSet.{u} 15 :=
  snoc
    (snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1) x)
    bound

/-- Layout `(fixed13, x, bound, index, stage)`. -/
def boundedStageWitnessAssignment
    (x bound index stage : ZFSet.{u}) : Tuple ZFSet.{u} 17 :=
  snoc (snoc (boundedStageParameters x bound) index) stage



/-- There is an ordinal `index ∈ bound` whose internally computed stage
contains `x`.  The free layout is `(fixed13, x, bound)`. -/
def boundedStageContainsFormula : FOFormula 15 :=
  .ex (.ex
    (.conj
      (.mem (15 : Fin 17) (14 : Fin 17))
      (.conj
        (Model.ordinalAt (15 : Fin 17))
        (.conj
          (FOFormula.rename boundedStageInternalRename
            Model.internalLStageAtFormula)
          (.mem (13 : Fin 17) (16 : Fin 17))))))





















end CondensationHull

end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_Condensation


/- Source module: Solutions.Work_CUGCH_CondensationAssembly -/
section GCHSource_Work_CUGCH_CondensationAssembly
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The assumption-transparent assembly step for Condensation

This file does not state the standard Condensation Lemma under disguised
hypotheses.  It isolates the last part of its usual proof after the uniform
definability of the hierarchy has supplied the following facts about an
elementary substructure `domain` of a limit level `L_theta`:

* the empty set belongs to `domain`;
* every internally indexed level `L_alpha` belongs to `domain`;
* every member of `domain` occurs in such an internally indexed level;
* at a limit index in `domain`, membership in that level has a witness at a
  smaller index which also belongs to `domain`.

These are explicit fields below.  A later theorem may use this assembly for
the standard result only after deriving every field from ordinary
elementarity at an arbitrary limit level.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

/--
The exact derived interfaces used by the collapse-induction part of the
standard Condensation proof.  This is a technical proof package, not the
definition of an elementary substructure and not the statement of
Condensation itself.
-/
structure StageCondensationInterfaces
    (theta : Ordinal.{u}) (domain : ZFSet.{u}) : Prop where
  isLimit : Order.IsSuccLimit theta
  subset_stage : domain ⊆ LStageZF theta
  satisfactionAbsolute :
    SatisfactionAbsolute (domain : Set ZFSet.{u})
      (LStageZF theta : Set ZFSet.{u})
  empty_mem : (∅ : ZFSet.{u}) ∈ domain
  stage_mem : ∀ alpha : Ordinal.{u}, alpha.toZFSet ∈ domain →
    LStageZF alpha ∈ domain
  internallyStageCovered : InternallyStageCovered domain
  smallerStageWitnesses : ∀ limit : Ordinal.{u},
    Order.IsSuccLimit limit → limit.toZFSet ∈ domain →
      HasSmallerInternalLStageWitnesses domain limit

namespace StageCondensationInterfaces

variable {theta : Ordinal.{u}} {domain : ZFSet.{u}}

















end StageCondensationInterfaces

end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_CondensationAssembly


/- Source module: Solutions.Work_CUGCH_CondensationFixedParameters -/
section GCHSource_Work_CUGCH_CondensationFixedParameters
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Canonical parameters in elementary substructures of constructible levels

The thirteen constants used by the internal stage recursion are not extra
parameters in the Condensation Lemma.  They are uniquely characterized by a
parameter-free first-order assertion: there are thirteen objects satisfying
`canonicalStageParametersFormula`.

This file first checks the exact semantics of the open matrix over every
limit level `L_theta` above `omega`.  It then existentially closes all thirteen
variables, transfers that closed sentence by full elementarity, and uses the
same semantic characterization to identify the witnesses in the elementary
substructure with the canonical constants.
-/

section

open Set

universe u

namespace Constructible

namespace Model

noncomputable section







/-- Raw external meaning of being inductive inside a carrier. -/
def IsInductiveSetIn (U w : ZFSet.{u}) : Prop :=
  (∅ : ZFSet.{u}) ∈ w /\
    forall x : ZFSet.{u}, x ∈ U -> x ∈ w -> insert x x ∈ w











/-!
The next definition is the actual sentence used for the Tarski--Vaught
transfer.  It has arity zero: none of the thirteen constants occurs as a free
parameter.  The conversion through Mathlib syntax is only a hygienic way of
binding the complete tuple with `exs`.
-/

/-- A closed, parameter-free existential assertion that the thirteen
canonical evaluator constants exist. -/
def canonicalStageParametersExistFormula : FOFormula 0 :=
  fromBoundedFormula
    ((toBoundedFormula canonicalStageParametersFormula).exs)



end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_CondensationFixedParameters


/- Source module: Solutions.Work_CUGCH_CondensationBareStage -/
section GCHSource_Work_CUGCH_CondensationBareStage
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Condensation from a locally correct relation-free stage predicate

The central hypothesis in this file is deliberately an exact semantic
contract, not a renamed reflection hypothesis.  `BareStageCorrectAt theta`
says that, for every ordinal code and candidate stage which belong to
`L_theta`, the relation-free first-order stage formula holds in `L_theta` if
and only if the candidate is the externally constructed `L_alpha`.

From that biconditional and full elementarity, this file derives the three
stage interfaces used by the usual Mostowski-collapse proof.  The remaining
task for arbitrary limit levels above `omega` is therefore stated without
ambiguity: prove `BareStageCorrectAt theta` from the ordinary limit
hypothesis.  No theorem in this file silently assumes that implication.
-/

section

open Set

universe u

namespace Constructible

namespace MostowskiCollapse

noncomputable section

namespace BareStageCondensation

/-- Raw layout `(fixed13,index,stage)`, shared with
`Model.bareStageAtFormula`. -/
def bareStageAssignment (index stage : ZFSet.{u}) : Tuple ZFSet.{u} 15 :=
  snoc
    (snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1) index)
    stage

/--
Exact local correctness of the relation-free stage predicate.

All quantifiers and membership assumptions are visible: both the ordinal
code and candidate output must be elements of `L_theta`, and satisfaction is
the raw semantics whose quantifiers range over exactly `L_theta`.
-/
def BareStageCorrectAt (theta : Ordinal.{u}) : Prop :=
  ∀ (alpha : Ordinal.{u}) (stage : ZFSet.{u}),
    alpha.toZFSet ∈ LStageZF theta → stage ∈ LStageZF theta →
      (Model.SatisfiesIn (LStageZF theta : Set ZFSet.{u})
          Model.bareStageAtFormula
          (bareStageAssignment alpha.toZFSet stage) ↔
        stage = LStageZF alpha)





/-- Layout `(fixed13,x)`. -/
def bareConstructibleParameters (x : ZFSet.{u}) : Tuple ZFSet.{u} 14 :=
  snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1) x

/-- Layout `(fixed13,x,index,stage)`. -/
def bareConstructibleWitnessAssignment
    (x index stage : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  snoc (snoc (bareConstructibleParameters x) index) stage

/-- With the fixed evaluator prefix and `x` displayed, assert that `x`
belongs to a stage at an internally recognized ordinal index. -/
def bareConstructibleFormula : FOFormula 14 :=
  .ex (.ex
    (.conj
      (Model.ordinalAt (14 : Fin 16))
      (.conj
        (FOFormula.rename Model.constructibleInternalStageRename
          Model.bareStageAtFormula)
        (.mem (13 : Fin 16) (15 : Fin 16)))))







/-! ## Bounded earlier-stage witnesses -/

/-- Layout `(fixed13,x,bound,index,stage)` projected to
`(fixed13,index,stage)`. -/
def bareBoundedStageRename : Fin 15 → Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i14 => Fin.lastCases
      (15 : Fin 17)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

/-- Layout `(fixed13,x,bound)`. -/
def bareBoundedStageParameters
    (x bound : ZFSet.{u}) : Tuple ZFSet.{u} 15 :=
  snoc
    (snoc (fun i => (Model.stageHistoryFixedParameters.{u} i).1) x)
    bound

/-- Layout `(fixed13,x,bound,index,stage)`. -/
def bareBoundedStageWitnessAssignment
    (x bound index stage : ZFSet.{u}) : Tuple ZFSet.{u} 17 :=
  snoc (snoc (bareBoundedStageParameters x bound) index) stage



/-- There is an internally indexed smaller stage containing `x`.
The free layout is `(fixed13,x,bound)`. -/
def bareBoundedStageContainsFormula : FOFormula 15 :=
  .ex (.ex
    (.conj
      (.mem (15 : Fin 17) (14 : Fin 17))
      (.conj
        (Model.ordinalAt (15 : Fin 17))
        (.conj
          (FOFormula.rename bareBoundedStageRename
            Model.bareStageAtFormula)
          (.mem (13 : Fin 17) (16 : Fin 17))))))









end BareStageCondensation

end

end MostowskiCollapse

end Constructible

end
end GCHSource_Work_CUGCH_CondensationBareStage


/- Source module: Solutions.Work_CUGCH_CanonicalBareHistoryOmega -/
section GCHSource_Work_CUGCH_CanonicalBareHistoryOmega
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The canonical history at the first infinite limit

The full evaluator prefix contains the set `omega`, so it cannot be used as
a parameter over `L_omega`.  We instead work over `L_(omega + 1)` and
restrict the displayed stage index to an element of `omega`.

Crucially, this file does not assert full evaluator correctness in that
successor level.  It isolates the exact weaker fact required here: evaluator
correctness when the predecessor is one of the finite stages `L_n`.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-! ## The exact finite-input evaluator contract -/

/-- Correctness of the internal Goedel evaluator only on actual finite
constructible stages.  No assertion is made about arbitrary inputs in `U`. -/
def FiniteBareGodelDefOutputCorrectIn (U : ZFSet.{u})
    (fixed : Tuple ZFSet.{u} 13) : Prop :=
  forall n : Nat, forall stage : ZFSet.{u},
    LStageZF (n : Ordinal.{u}) ∈ U -> stage ∈ U ->
      (BareGodelDefOutputIn (U : Set ZFSet.{u}) fixed
          (LStageZF (n : Ordinal.{u})) stage <->
        stage = Godel.godelDef (LStageZF (n : Ordinal.{u})))



/-! ## Soundness and completeness at finite indices -/













/-! ## A pair formula restricted to finite indices -/

/-- Free layout `(fixed13,pair)`.  The two hidden witnesses are an index and
a stage; unlike `canonicalBarePairFormula`, this formula explicitly requires
the index to belong to the final fixed parameter, which will be the actual
von Neumann `omega`. -/
def finiteCanonicalBarePairFormula : FOFormula 14 :=
  .ex (.ex
    (.conj
      (.mem (14 : Fin 16) (12 : Fin 16))
      (.conj
        (FOFormula.rename canonicalBarePairStageRename bareStageAtFormula)
        (Delta0Formula.kuratowskiPairEqAt
          (13 : Fin 16) (14 : Fin 16) (15 : Fin 16)).toFO)))







/-! ## Separation of the graph below `omega` -/

@[simp]
theorem stageHistoryFixedParametersRaw_last :
    stageHistoryFixedParametersRaw.{u} (12 : Fin 13) =
      Ordinal.omega0.toZFSet := by
  change (stageHistoryFixedParameters (Fin.last 12)).1 =
    Ordinal.omega0.toZFSet
  rw [stageHistoryFixedParameters_last]













end

end Constructible.Model

end
end GCHSource_Work_CUGCH_CanonicalBareHistoryOmega


