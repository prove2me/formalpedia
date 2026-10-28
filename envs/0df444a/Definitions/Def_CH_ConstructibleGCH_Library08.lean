-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library08
-- name    : CH_ConstructibleGCH_Library08
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:26:05.687352+00:00
-- url     : https://prove2.me/theorems/150beeb0-1974-4ef5-b45f-ae16b91528c3
-- title:
--   Ordinal products, finite formulas and standard omega
-- statement:
--   The library defines the ordinal product-order data, finite-variable relation syntax and standard-omega interfaces used in the internal cardinal and formula-enumeration constructions. The formulas have explicit finite parameter lists.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalOrdinalProductOrder.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookDefinability.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TransitiveZFOmega.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library07
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_InternalOrdinalProductOrder -/
section GCHSource_Work_CUGCH_InternalOrdinalProductOrder
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The maximum-lexicographic order on an internal ordinal square

For a von Neumann ordinal `kappa`, this file constructs the standard order on
`kappa x kappa`: first compare the maximum of the two coordinates, and then
compare the coordinates lexicographically.  The relation is obtained by
Separation from a fixed first-order formula, so its graph is an actual member
of the constructible universe.

This is the well-order used in the usual proof that every infinite cardinal
absorbs its square.  No ambient cardinal comparison is used as an internal
function witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## Formula and exact semantics -/

/-- `maximum` is the larger of `left` and `right` in a strict linear order. -/
def IsMaximumOf {A : Type u} (E : A -> A -> Prop)
    (left right maximum : A) : Prop :=
  ((E left right \/ left = right) /\ maximum = right) \/
    (E right left /\ maximum = left)

/-- Formula version of `IsMaximumOf`. -/
def maximumAt {n : Nat} (left right maximum : Fin n) : FOFormula n :=
  .disj
    (.conj
      (.disj (.mem left right) (.eq left right))
      (.eq maximum right))
    (.conj (.mem right left) (.eq maximum left))

@[simp]
theorem satisfies_maximumAt {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (left right maximum : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E (maximumAt left right maximum) s <->
      IsMaximumOf E (s left) (s right) (s maximum) := by
  simp [maximumAt, IsMaximumOf]







/-- Compare two coordinate pairs by maximum first and lexicographically on a
tie. -/
def MaximumLexComponents {A : Type u} (E : A -> A -> Prop)
    (leftFirst leftSecond rightFirst rightSecond leftMaximum rightMaximum : A) :
    Prop :=
  IsMaximumOf E leftFirst leftSecond leftMaximum /\
    IsMaximumOf E rightFirst rightSecond rightMaximum /\
      (E leftMaximum rightMaximum \/
        (leftMaximum = rightMaximum /\
          (E leftFirst rightFirst \/
            (leftFirst = rightFirst /\ E leftSecond rightSecond))))

/-- The maximum-lexicographic comparison embedded at arbitrary coordinates. -/
def maximumLexComponentsAt {n : Nat}
    (leftFirst leftSecond rightFirst rightSecond leftMaximum rightMaximum :
      Fin n) : FOFormula n :=
  .conj
    (maximumAt leftFirst leftSecond leftMaximum)
    (.conj
      (maximumAt rightFirst rightSecond rightMaximum)
      (.disj
        (.mem leftMaximum rightMaximum)
        (.conj
          (.eq leftMaximum rightMaximum)
          (.disj
            (.mem leftFirst rightFirst)
            (.conj
              (.eq leftFirst rightFirst)
              (.mem leftSecond rightSecond))))))

@[simp]
theorem satisfies_maximumLexComponentsAt {A : Type u}
    (E : A -> A -> Prop) {n : Nat}
    (leftFirst leftSecond rightFirst rightSecond leftMaximum rightMaximum :
      Fin n) (s : Tuple A n) :
    FOFormula.Satisfies E
        (maximumLexComponentsAt leftFirst leftSecond rightFirst rightSecond
          leftMaximum rightMaximum) s <->
      MaximumLexComponents E
        (s leftFirst) (s leftSecond) (s rightFirst) (s rightSecond)
        (s leftMaximum) (s rightMaximum) := by
  simp [maximumLexComponentsAt, MaximumLexComponents]

/-- The semantic relation on two Kuratowski pair codes. -/
def OrdinalPairMaximumLexRel {A : Type u} (E : A -> A -> Prop)
    (left right : A) : Prop :=
  exists leftFirst leftSecond rightFirst rightSecond leftMaximum rightMaximum : A,
    IsKuratowskiPairOf E left leftFirst leftSecond /\
      IsKuratowskiPairOf E right rightFirst rightSecond /\
        MaximumLexComponents E leftFirst leftSecond rightFirst rightSecond
          leftMaximum rightMaximum

/-- Layout `(leftPair,rightPair)`.  The six witnesses are the four coordinates
and their two maxima. -/
def ordinalPairMaximumLexFormula : FOFormula 2 :=
  .ex (.ex (.ex (.ex (.ex (.ex
    (.conj
      (kuratowskiPairAt (0 : Fin 8) (2 : Fin 8) (3 : Fin 8))
      (.conj
        (kuratowskiPairAt (1 : Fin 8) (4 : Fin 8) (5 : Fin 8))
        (maximumLexComponentsAt
          (2 : Fin 8) (3 : Fin 8) (4 : Fin 8) (5 : Fin 8)
          (6 : Fin 8) (7 : Fin 8)))))))))

 theorem ordinalPairMaximumLex_assignment
    (left right leftFirst leftSecond rightFirst rightSecond
      leftMaximum rightMaximum : LCarrier.{u}) :
    snoc (snoc (snoc (snoc (snoc (snoc ![left, right]
      leftFirst) leftSecond) rightFirst) rightSecond) leftMaximum) rightMaximum =
      ![left, right, leftFirst, leftSecond, rightFirst, rightSecond,
        leftMaximum, rightMaximum] := by
  simp [Model.snoc_eq_finSnoc]

@[simp]
theorem satisfies_ordinalPairMaximumLexFormula
    (left right : LCarrier.{u}) :
    FOFormula.Satisfies LMem ordinalPairMaximumLexFormula ![left, right] <->
      OrdinalPairMaximumLexRel LMem left right := by
  simp only [ordinalPairMaximumLexFormula, FOFormula.Satisfies]
  apply exists_congr
  intro leftFirst
  apply exists_congr
  intro leftSecond
  apply exists_congr
  intro rightFirst
  apply exists_congr
  intro rightSecond
  apply exists_congr
  intro leftMaximum
  apply exists_congr
  intro rightMaximum
  rw [ordinalPairMaximumLex_assignment]
  simp only [satisfies_kuratowskiPairAt,
    satisfies_maximumLexComponentsAt]
  rfl

/-! ## The represented relation -/

/-- The canonical Separation graph of the maximum-lexicographic relation on
`kappa x kappa`. -/
noncomputable def ordinalPairMaximumLexGraph (kappa : LCarrier.{u}) :
    LCarrier.{u} :=
  canonicalDefinableRelationGraph ordinalPairMaximumLexFormula
    (![] : Tuple LCarrier.{u} 0) (prodLCarrier kappa kappa)

@[simp]
theorem graphRel_ordinalPairMaximumLexGraph_iff
    (kappa left right : LCarrier.{u}) :
    GraphRel (ordinalPairMaximumLexGraph kappa) left right <->
      left.1 ∈ (prodLCarrier kappa kappa).1 /\
        right.1 ∈ (prodLCarrier kappa kappa).1 /\
          OrdinalPairMaximumLexRel LMem left right := by
  rw [ordinalPairMaximumLexGraph,
    graphRel_canonicalDefinableRelationGraph_iff]
  have htuple :
      snoc (snoc (![] : Tuple LCarrier.{u} 0) left) right =
        ![left, right] := by
    funext i
    fin_cases i <;> rfl
  rw [htuple, satisfies_ordinalPairMaximumLexFormula]

/-! ## The external presentation of the internal product -/

/-- Encode two internal members by their Kuratowski pair. -/
def encodeInternalProduct (kappa : LCarrier.{u})
    (point : InternalCarrier kappa × InternalCarrier kappa) :
    InternalCarrier (prodLCarrier kappa kappa) :=
  ⟨orderedPairLCarrier point.1.1 point.2.1, by
    change ZFSet.pair point.1.1.1 point.2.1.1 ∈
      ZFSet.prod kappa.1 kappa.1
    rw [ZFSet.pair_mem_prod]
    exact ⟨point.1.2, point.2.2⟩⟩

theorem encodeInternalProduct_injective (kappa : LCarrier.{u}) :
    Function.Injective (encodeInternalProduct kappa) := by
  intro left right heq
  have hraw := congrArg
    (fun point : InternalCarrier (prodLCarrier kappa kappa) => point.1.1)
    heq
  have hcoordinates :
      left.1.1.1 = right.1.1.1 /\ left.2.1.1 = right.2.1.1 := by
    apply ZFSet.pair_inj.mp
    simpa only [encodeInternalProduct, orderedPairLCarrier_val] using hraw
  apply Prod.ext
  · apply Subtype.ext
    exact Subtype.ext hcoordinates.1
  · apply Subtype.ext
    exact Subtype.ext hcoordinates.2

theorem encodeInternalProduct_surjective (kappa : LCarrier.{u}) :
    Function.Surjective (encodeInternalProduct kappa) := by
  intro point
  rcases ZFSet.mem_prod.mp point.2 with
    ⟨leftRaw, hleft, rightRaw, hright, hpoint⟩
  let left : LCarrier.{u} :=
    ⟨leftRaw, Constructible.mem_L_of_mem hleft kappa.2⟩
  let right : LCarrier.{u} :=
    ⟨rightRaw, Constructible.mem_L_of_mem hright kappa.2⟩
  let leftMember : InternalCarrier kappa := ⟨left, hleft⟩
  let rightMember : InternalCarrier kappa := ⟨right, hright⟩
  refine ⟨(leftMember, rightMember), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ZFSet.pair leftRaw rightRaw = point.1.1
  exact hpoint.symm

/-- The internal Kuratowski product has the expected external product
presentation. -/
noncomputable def internalProductEquiv (kappa : LCarrier.{u}) :
    (InternalCarrier kappa × InternalCarrier kappa) ≃
      InternalCarrier (prodLCarrier kappa kappa) :=
  Equiv.ofBijective (encodeInternalProduct kappa)
    ⟨encodeInternalProduct_injective kappa,
      encodeInternalProduct_surjective kappa⟩

/-! ## The represented relation is a well-order -/

/-- Membership on the internal members of a von Neumann ordinal is a
well-order. -/
theorem internalOrdinalMem_isWellOrder
    (kappa : LCarrier.{u})
    (hkappa : IsVonNeumannOrdinal LMem kappa) :
    IsWellOrder (InternalCarrier kappa)
      (fun left right => left.1.1 ∈ right.1.1) := by
  have hkappaRaw : kappa.1.IsOrdinal :=
    (isVonNeumannOrdinal_lCarrier_iff kappa).mp hkappa
  let embedding : InternalCarrier kappa ↪ ZFCarrier kappa.1 :=
    ⟨fun point => ⟨point.1.1, point.2⟩, by
      intro left right heq
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun point : ZFCarrier kappa.1 => point.1) heq⟩
  letI : IsWellOrder (ZFCarrier kappa.1)
      (fun left right => left.1 ∈ right.1) :=
    hkappaRaw.isWellOrder
  change IsWellOrder _
    (InvImage (fun left right : ZFCarrier kappa.1 => left.1 ∈ right.1)
      embedding)
  exact (RelEmbedding.preimage embedding
    (fun left right : ZFCarrier kappa.1 => left.1 ∈ right.1)).isWellOrder

/-- The Separation graph above genuinely well-orders the internal square of
every von Neumann ordinal. -/
theorem ordinalPairMaximumLexGraph_internallyWellOrders
    (kappa : LCarrier.{u})
    (hkappa : IsVonNeumannOrdinal LMem kappa) :
    InternallyWellOrders (ordinalPairMaximumLexGraph kappa)
      (prodLCarrier kappa kappa) := by
  let baseRel : InternalCarrier kappa -> InternalCarrier kappa -> Prop :=
    fun left right => left.1.1 ∈ right.1.1
  let hbaseWell : IsWellOrder (InternalCarrier kappa) baseRel :=
    internalOrdinalMem_isWellOrder kappa hkappa
  letI : IsWellOrder (InternalCarrier kappa) baseRel := hbaseWell
  let baseOrder : LinearOrder (InternalCarrier kappa) :=
    IsWellOrder.linearOrder baseRel
  letI : LinearOrder (InternalCarrier kappa) := baseOrder
  letI : LE (InternalCarrier kappa) := baseOrder.toLE
  letI : LT (InternalCarrier kappa) := baseOrder.toLT
  letI : Min (InternalCarrier kappa) := baseOrder.toMin
  letI : Max (InternalCarrier kappa) := baseOrder.toMax
  letI : Preorder (InternalCarrier kappa) := baseOrder.toPreorder
  letI : PartialOrder (InternalCarrier kappa) := baseOrder.toPartialOrder
  letI : WellFoundedLT (InternalCarrier kappa) :=
    ⟨by
      change WellFounded baseRel
      exact hbaseWell.wf⟩
  have lt_iff_mem (left right : InternalCarrier kappa) :
      left < right <-> LMem left.1 right.1 := by
    rfl
  let keyEmbedding :
      (InternalCarrier kappa × InternalCarrier kappa) ↪
        (InternalCarrier kappa ×ₗ
          (InternalCarrier kappa ×ₗ InternalCarrier kappa)) :=
    ⟨fun point => toLex (max point.1 point.2, toLex point),
      fun left right heq => congrArg Prod.snd heq⟩
  have keyEmbedding_lt_iff
      (left right : InternalCarrier kappa × InternalCarrier kappa) :
      keyEmbedding left < keyEmbedding right <->
        (max left.1 left.2 < max right.1 right.2 \/
          (max left.1 left.2 = max right.1 right.2 /\
            (left.1 < right.1 \/
              (left.1 = right.1 /\ left.2 < right.2)))) := by
    change
      toLex (max left.1 left.2, toLex left) <
          toLex (max right.1 right.2, toLex right) <-> _
    rw [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex]
  let productEquiv := internalProductEquiv kappa
  let fullEmbedding :
      InternalCarrier (prodLCarrier kappa kappa) ↪
        (InternalCarrier kappa ×ₗ
          (InternalCarrier kappa ×ₗ InternalCarrier kappa)) :=
    ⟨fun point => keyEmbedding (productEquiv.symm point),
      fun left right heq => productEquiv.symm.injective
        (keyEmbedding.injective heq)⟩
  have hwell : IsWellOrder
      (InternalCarrier (prodLCarrier kappa kappa))
      (fullEmbedding ⁻¹'o (fun left right => left < right)) :=
    (RelEmbedding.preimage fullEmbedding
      (fun left right => left < right)).isWellOrder
  have maximum_eq : forall
      (left right : InternalCarrier kappa) (maximum : LCarrier.{u}),
      IsMaximumOf LMem left.1 right.1 maximum ->
        maximum = (max left right).1 := by
    intro left right maximum hmaximum
    rcases hmaximum with ⟨hleftRight, hmaximum⟩ |
      ⟨hrightLeft, hmaximum⟩
    · rcases hleftRight with hlt | heq
      · have hlt' : left < right := hlt
        have hmax : max left right = right :=
          max_eq_right (le_of_lt hlt')
        exact hmaximum.trans (congrArg Subtype.val hmax).symm
      · have heq' : left = right := Subtype.ext heq
        subst right
        simpa using hmaximum
    · have hlt' : right < left := hrightLeft
      have hmax : max left right = left :=
        max_eq_left (le_of_lt hlt')
      exact hmaximum.trans (congrArg Subtype.val hmax).symm
  have maximum_spec : forall
      (left right : InternalCarrier kappa),
      IsMaximumOf LMem left.1 right.1 (max left right).1 := by
    intro left right
    rcases lt_trichotomy left right with hlt | heq | hgt
    · apply Or.inl
      constructor
      · exact Or.inl hlt
      · exact congrArg Subtype.val (max_eq_right (le_of_lt hlt))
    · apply Or.inl
      constructor
      · exact Or.inr (congrArg Subtype.val heq)
      · exact congrArg Subtype.val (max_eq_right (le_of_eq heq))
    · apply Or.inr
      constructor
      · exact hgt
      · exact congrArg Subtype.val (max_eq_left (le_of_lt hgt))
  have hsemantic : forall
      (left right : InternalCarrier kappa × InternalCarrier kappa),
      OrdinalPairMaximumLexRel LMem
          (encodeInternalProduct kappa left).1
          (encodeInternalProduct kappa right).1 <->
        keyEmbedding left < keyEmbedding right := by
    intro left right
    constructor
    · rintro ⟨leftFirst, leftSecond, rightFirst, rightSecond,
        leftMaximum, rightMaximum, hleftPair, hrightPair,
        hleftMaximum, hrightMaximum, hcomparison⟩
      have hleftRaw := (isKuratowskiPairOf_lCarrier_iff
        (encodeInternalProduct kappa left).1 leftFirst leftSecond).mp
          hleftPair
      have hrightRaw := (isKuratowskiPairOf_lCarrier_iff
        (encodeInternalProduct kappa right).1 rightFirst rightSecond).mp
          hrightPair
      have hleftCoordinates := ZFSet.pair_inj.mp
        (show ZFSet.pair left.1.1.1 left.2.1.1 =
            ZFSet.pair leftFirst.1 leftSecond.1 by
          simpa only [encodeInternalProduct, orderedPairLCarrier_val]
            using hleftRaw)
      have hrightCoordinates := ZFSet.pair_inj.mp
        (show ZFSet.pair right.1.1.1 right.2.1.1 =
            ZFSet.pair rightFirst.1 rightSecond.1 by
          simpa only [encodeInternalProduct, orderedPairLCarrier_val]
            using hrightRaw)
      have hleftFirst : leftFirst = left.1.1 :=
        Subtype.ext hleftCoordinates.1.symm
      have hleftSecond : leftSecond = left.2.1 :=
        Subtype.ext hleftCoordinates.2.symm
      have hrightFirst : rightFirst = right.1.1 :=
        Subtype.ext hrightCoordinates.1.symm
      have hrightSecond : rightSecond = right.2.1 :=
        Subtype.ext hrightCoordinates.2.symm
      subst leftFirst
      subst leftSecond
      subst rightFirst
      subst rightSecond
      have hleftMaximumEq := maximum_eq
        left.1 left.2 leftMaximum hleftMaximum
      have hrightMaximumEq := maximum_eq
        right.1 right.2 rightMaximum hrightMaximum
      subst leftMaximum
      subst rightMaximum
      apply (keyEmbedding_lt_iff left right).mpr
      simpa only [lt_iff_mem, Subtype.coe_injective.eq_iff] using hcomparison
    · intro hcomparison
      refine ⟨left.1.1, left.2.1, right.1.1, right.2.1,
        (max left.1 left.2).1, (max right.1 right.2).1, ?_, ?_,
        maximum_spec left.1 left.2, maximum_spec right.1 right.2, ?_⟩
      · apply (isKuratowskiPairOf_lCarrier_iff
          (encodeInternalProduct kappa left).1 left.1.1 left.2.1).mpr
        rfl
      · apply (isKuratowskiPairOf_lCarrier_iff
          (encodeInternalProduct kappa right).1 right.1.1 right.2.1).mpr
        rfl
      · have hcomparison' := (keyEmbedding_lt_iff left right).mp hcomparison
        simpa only [lt_iff_mem, Subtype.coe_injective.eq_iff] using hcomparison'
  change IsWellOrder (InternalCarrier (prodLCarrier kappa kappa))
    (graphRelOn (ordinalPairMaximumLexGraph kappa)
      (prodLCarrier kappa kappa))
  convert hwell using 1
  funext left right
  apply propext
  change GraphRel (ordinalPairMaximumLexGraph kappa) left.1 right.1 <-> _
  rw [graphRel_ordinalPairMaximumLexGraph_iff]
  simp only [left.2, right.2, true_and]
  let leftCoordinates := productEquiv.symm left
  let rightCoordinates := productEquiv.symm right
  have hleft : encodeInternalProduct kappa leftCoordinates = left := by
    change productEquiv leftCoordinates = left
    exact productEquiv.apply_symm_apply left
  have hright : encodeInternalProduct kappa rightCoordinates = right := by
    change productEquiv rightCoordinates = right
    exact productEquiv.apply_symm_apply right
  have hresult := hsemantic leftCoordinates rightCoordinates
  rw [hleft, hright] at hresult
  change OrdinalPairMaximumLexRel LMem left.1 right.1 <->
    keyEmbedding (productEquiv.symm left) <
      keyEmbedding (productEquiv.symm right)
  simpa only [leftCoordinates, rightCoordinates] using hresult

/-! ## Bounds for strict initial segments -/







end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalOrdinalProductOrder


/- Source module: Solutions.Work_CUGCH_TextbookDefinability -/
section GCHSource_Work_CUGCH_TextbookDefinability
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The textbook sets of definable relations

This file internalizes the standard-natural-number core of the definitions in
Wang Fangting, *Axiomatic Set Theory*, Section 6.4.  In contrast with the
external relation algebra in `Def.lean`, every object defined here is a
genuine `ZFSet`.  The finite arities and indices in this file are Lean
`Nat`s; the total interface on set-coded indices is supplied separately in
`TextbookDefinabilityCode`.

For a natural number `n`, `textbookTupleSpace a n` is the set-theoretic
function space `a^n`: its members are Kuratowski graphs of functions from the
von Neumann ordinal `n` to `a`.  The definitions of `textbookDInZF`,
`textbookDEqZF`, `textbookExistsProjZF`, `textbookDStageZF`, and
`textbookDfZF` follow the display on textbook page 127.  In particular, the
exceptional convention

`P_exists(a, 0, r) = empty`

is part of the definition, rather than an after-the-fact simplification.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

/-! ## Finite tuple graphs -/

/-- The textbook finite power `a^n`, represented by actual function graphs. -/
noncomputable def textbookTupleSpace (a : ZFSet.{u}) (n : Nat) : ZFSet.{u} :=
  ZFSet.funs (natCode n) a

@[simp]
theorem mem_textbookTupleSpace_iff {a s : ZFSet.{u}} {n : Nat} :
    s ∈ textbookTupleSpace a n ↔ ZFSet.IsFunc (natCode n) a s := by
  simp [textbookTupleSpace]

/-- The Kuratowski graph of an externally supplied `n`-tuple from `a`. -/
noncomputable def textbookTupleGraph {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) : ZFSet.{u} :=
  ZFSet.range fun i : Fin n => ZFSet.pair (natCode i.1) (s i).1

@[simp]
theorem mem_textbookTupleGraph_iff {a q : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) :
    q ∈ textbookTupleGraph s ↔
      ∃ i : Fin n, ZFSet.pair (natCode i.1) (s i).1 = q := by
  simp [textbookTupleGraph]

@[simp]
theorem textbookTupleGraph_value {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (i : Fin n) :
    ZFSet.pair (natCode i.1) (s i).1 ∈ textbookTupleGraph s := by
  change ZFSet.pair (natCode i.1) (s i).1 ∈
    ZFSet.range (fun j : Fin n => ZFSet.pair (natCode j.1) (s j).1)
  exact ZFSet.mem_range_self
    (f := fun j : Fin n =>
      (ZFSet.pair (natCode j.1) (s j).1 : ZFSet.{u})) i

theorem mem_natCode_iff_exists_fin (z : ZFSet.{u}) (n : Nat) :
    z ∈ (natCode n : ZFSet.{u}) ↔
      ∃ i : Fin n, z = natCode i.1 := by
  rw [IndexedSequenceZF.mem_natCode_iff_exists_lt]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, i.2, rfl⟩

theorem textbookTupleGraph_isFunc {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) :
    ZFSet.IsFunc (natCode n) a (textbookTupleGraph s) := by
  constructor
  · intro q hq
    rcases (mem_textbookTupleGraph_iff s).mp hq with ⟨i, rfl⟩
    rw [ZFSet.pair_mem_prod]
    exact ⟨(mem_natCode_iff_exists_fin _ _).mpr ⟨i, rfl⟩, (s i).2⟩
  · intro z hz
    rcases (mem_natCode_iff_exists_fin z n).mp hz with ⟨i, rfl⟩
    refine ⟨(s i).1, textbookTupleGraph_value s i, ?_⟩
    intro y hy
    rcases (mem_textbookTupleGraph_iff s).mp hy with ⟨j, hpair⟩
    have hparts := ZFSet.pair_inj.mp hpair
    have hij : i.1 = j.1 := (natCode_injective hparts.1).symm
    have hfin : i = j := Fin.ext hij
    subst j
    exact hparts.2.symm

@[simp]
theorem textbookTupleGraph_mem_tupleSpace {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) :
    textbookTupleGraph s ∈ textbookTupleSpace a n := by
  exact mem_textbookTupleSpace_iff.mpr (textbookTupleGraph_isFunc s)

theorem textbookTupleGraph_value_iff {a x : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (i : Fin n) :
    ZFSet.pair (natCode i.1) x ∈ textbookTupleGraph s ↔ x = (s i).1 := by
  constructor
  · intro hx
    rcases (mem_textbookTupleGraph_iff s).mp hx with ⟨j, hpair⟩
    have hparts := ZFSet.pair_inj.mp hpair
    have hij : i.1 = j.1 := natCode_injective hparts.1.symm
    have hfin : i = j := Fin.ext hij
    subst j
    exact hparts.2.symm
  · rintro rfl
    exact textbookTupleGraph_value s i

/-! ## Atomic relations and projection -/

/-- The standard-`Nat` core of the textbook relation `D_in(a,n,i,j)`, with
illegal indices giving `empty`. -/
noncomputable def textbookDInZF
    (a : ZFSet.{u}) (n i j : Nat) : ZFSet.{u} :=
  ZFSet.sep
    (fun s =>
      i < n ∧ j < n ∧
        ∃ x y : ZFSet.{u},
          ZFSet.pair (natCode i) x ∈ s ∧
          ZFSet.pair (natCode j) y ∈ s ∧ x ∈ y)
    (textbookTupleSpace a n)

@[simp]
theorem mem_textbookDInZF_iff {a s : ZFSet.{u}} {n i j : Nat} :
    s ∈ textbookDInZF a n i j ↔
      s ∈ textbookTupleSpace a n ∧ i < n ∧ j < n ∧
        ∃ x y : ZFSet.{u},
          ZFSet.pair (natCode i) x ∈ s ∧
          ZFSet.pair (natCode j) y ∈ s ∧ x ∈ y := by
  simp [textbookDInZF]

/-- The standard-`Nat` core of the textbook relation `D_eq(a,n,i,j)`, with
illegal indices giving `empty`. -/
noncomputable def textbookDEqZF
    (a : ZFSet.{u}) (n i j : Nat) : ZFSet.{u} :=
  ZFSet.sep
    (fun s =>
      i < n ∧ j < n ∧
        ∃ x : ZFSet.{u},
          ZFSet.pair (natCode i) x ∈ s ∧
          ZFSet.pair (natCode j) x ∈ s)
    (textbookTupleSpace a n)

@[simp]
theorem mem_textbookDEqZF_iff {a s : ZFSet.{u}} {n i j : Nat} :
    s ∈ textbookDEqZF a n i j ↔
      s ∈ textbookTupleSpace a n ∧ i < n ∧ j < n ∧
        ∃ x : ZFSet.{u},
          ZFSet.pair (natCode i) x ∈ s ∧
          ZFSet.pair (natCode j) x ∈ s := by
  simp [textbookDEqZF]

@[simp]
theorem textbookDInZF_eq_empty_of_not_lt_left {a : ZFSet.{u}}
    {n i j : Nat} (hi : ¬i < n) : textbookDInZF a n i j = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro s hs
  exact hi (mem_textbookDInZF_iff.mp hs).2.1

@[simp]
theorem textbookDInZF_eq_empty_of_not_lt_right {a : ZFSet.{u}}
    {n i j : Nat} (hj : ¬j < n) : textbookDInZF a n i j = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro s hs
  exact hj (mem_textbookDInZF_iff.mp hs).2.2.1

@[simp]
theorem textbookDEqZF_eq_empty_of_not_lt_left {a : ZFSet.{u}}
    {n i j : Nat} (hi : ¬i < n) : textbookDEqZF a n i j = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro s hs
  exact hi (mem_textbookDEqZF_iff.mp hs).2.1

@[simp]
theorem textbookDEqZF_eq_empty_of_not_lt_right {a : ZFSet.{u}}
    {n i j : Nat} (hj : ¬j < n) : textbookDEqZF a n i j = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro s hs
  exact hj (mem_textbookDEqZF_iff.mp hs).2.2.1

theorem textbookDInZF_subset_tupleSpace
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookDInZF a n i j ⊆ textbookTupleSpace a n :=
  ZFSet.sep_subset

theorem textbookDEqZF_subset_tupleSpace
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookDEqZF a n i j ⊆ textbookTupleSpace a n :=
  ZFSet.sep_subset

@[simp]
theorem textbookTupleGraph_mem_DInZF_iff {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (i j : Fin n) :
    textbookTupleGraph s ∈ textbookDInZF a n i.1 j.1 ↔
      (s i).1 ∈ (s j).1 := by
  rw [mem_textbookDInZF_iff]
  simp only [textbookTupleGraph_mem_tupleSpace, true_and, i.2, j.2]
  constructor
  · rintro ⟨x, y, hix, hjy, hxy⟩
    rw [textbookTupleGraph_value_iff s i] at hix
    rw [textbookTupleGraph_value_iff s j] at hjy
    simpa [hix, hjy] using hxy
  · intro hxy
    exact ⟨(s i).1, (s j).1,
      textbookTupleGraph_value s i, textbookTupleGraph_value s j, hxy⟩

@[simp]
theorem textbookTupleGraph_mem_DEqZF_iff {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (i j : Fin n) :
    textbookTupleGraph s ∈ textbookDEqZF a n i.1 j.1 ↔ s i = s j := by
  rw [mem_textbookDEqZF_iff]
  simp only [textbookTupleGraph_mem_tupleSpace, true_and, i.2, j.2]
  constructor
  · rintro ⟨x, hix, hjx⟩
    rw [textbookTupleGraph_value_iff s i] at hix
    rw [textbookTupleGraph_value_iff s j] at hjx
    apply Subtype.ext
    exact hix.symm.trans hjx
  · intro hij
    have hval : (s i).1 = (s j).1 := congrArg Subtype.val hij
    refine ⟨(s i).1, textbookTupleGraph_value s i, ?_⟩
    rw [hval]
    exact textbookTupleGraph_value s j

/-- Adjoin the last coordinate to a finite function graph. -/
noncomputable def textbookTupleSnocGraph
    (s : ZFSet.{u}) (n : Nat) (x : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair (natCode n) x) s

theorem textbookTupleGraph_snoc {a : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier a) n) (x : ZFCarrier a) :
    textbookTupleGraph (snoc s x) =
      textbookTupleSnocGraph (textbookTupleGraph s) n x.1 := by
  apply ZFSet.ext
  intro q
  rw [mem_textbookTupleGraph_iff]
  simp only [textbookTupleSnocGraph, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.lastCases ?_ (fun j hi => ?_) i
    · intro hi
      left
      simpa using hi.symm
    · right
      apply (mem_textbookTupleGraph_iff s).mpr
      exact ⟨j, by simpa using hi⟩
  · rintro (hq | hq)
    · exact ⟨Fin.last n, by simpa using hq.symm⟩
    · rcases (mem_textbookTupleGraph_iff s).mp hq with ⟨i, hi⟩
      exact ⟨i.castSucc, by simpa using hi⟩

/--
The textbook existential projection.  The `n = 0` branch is deliberately
empty, exactly as stipulated on page 127.
-/
noncomputable def textbookExistsProjZF
    (a : ZFSet.{u}) (n : Nat) (r : ZFSet.{u}) : ZFSet.{u} :=
  if n = 0 then ∅
  else
    ZFSet.sep
      (fun s =>
        ∃ x ∈ a, textbookTupleSnocGraph s n x ∈ r)
      (textbookTupleSpace a n)

@[simp]
theorem textbookExistsProjZF_zero (a r : ZFSet.{u}) :
    textbookExistsProjZF a 0 r = ∅ := by
  simp [textbookExistsProjZF]

theorem mem_textbookExistsProjZF_iff {a r s : ZFSet.{u}}
    {n : Nat} (hn : n ≠ 0) :
    s ∈ textbookExistsProjZF a n r ↔
      s ∈ textbookTupleSpace a n ∧
        ∃ x ∈ a, textbookTupleSnocGraph s n x ∈ r := by
  simp [textbookExistsProjZF, hn]

theorem textbookExistsProjZF_subset_tupleSpace
    (a : ZFSet.{u}) (n : Nat) (r : ZFSet.{u}) :
    textbookExistsProjZF a n r ⊆ textbookTupleSpace a n := by
  by_cases hn : n = 0
  · subst n
    simp
  · intro s hs
    exact (mem_textbookExistsProjZF_iff hn).mp hs |>.1

theorem textbookTupleGraph_mem_existsProjZF_iff
    {a r : ZFSet.{u}} {n : Nat} (hn : n ≠ 0)
    (s : Tuple (ZFCarrier a) n) :
    textbookTupleGraph s ∈ textbookExistsProjZF a n r ↔
      ∃ x : ZFCarrier a, textbookTupleGraph (snoc s x) ∈ r := by
  rw [mem_textbookExistsProjZF_iff hn]
  simp only [textbookTupleGraph_mem_tupleSpace, true_and]
  constructor
  · rintro ⟨x, hx, hsx⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rwa [textbookTupleGraph_snoc]
  · rintro ⟨x, hsx⟩
    refine ⟨x.1, x.2, ?_⟩
    rwa [← textbookTupleGraph_snoc]

/-! ## The finite stages `D(k,a,n)` -/

/-- The two finite families of atomic `n`-ary relations. -/
noncomputable def textbookDZeroZF (a : ZFSet.{u}) (n : Nat) : ZFSet.{u} :=
  ZFSet.range
      (fun p : Fin n × Fin n => textbookDInZF a n p.1.1 p.2.1) ∪
    ZFSet.range
      (fun p : Fin n × Fin n => textbookDEqZF a n p.1.1 p.2.1)

@[simp]
theorem mem_textbookDZeroZF_iff {a r : ZFSet.{u}} {n : Nat} :
    r ∈ textbookDZeroZF a n ↔
      (∃ i j : Fin n, textbookDInZF a n i.1 j.1 = r) ∨
        ∃ i j : Fin n, textbookDEqZF a n i.1 j.1 = r := by
  simp only [textbookDZeroZF, ZFSet.mem_union, ZFSet.mem_range]
  constructor
  · rintro (⟨⟨i, j⟩, h⟩ | ⟨⟨i, j⟩, h⟩)
    · exact Or.inl ⟨i, j, h⟩
    · exact Or.inr ⟨i, j, h⟩
  · rintro (⟨i, j, h⟩ | ⟨i, j, h⟩)
    · exact Or.inl ⟨(i, j), h⟩
    · exact Or.inr ⟨(i, j), h⟩

@[simp]
theorem textbookDZeroZF_zero (a : ZFSet.{u}) :
    textbookDZeroZF a 0 = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro r hr
  rcases mem_textbookDZeroZF_iff.mp hr with
    ⟨i, _, _⟩ | ⟨i, _, _⟩ <;> exact Fin.elim0 i

/-- Complements, always taken relative to the finite power `a^n`. -/
noncomputable def textbookComplementFamilyZF
    (a : ZFSet.{u}) (n : Nat) (stage : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun r : ZFCarrier stage => textbookTupleSpace a n \ r.1

@[simp]
theorem mem_textbookComplementFamilyZF_iff
    {a stage z : ZFSet.{u}} {n : Nat} :
    z ∈ textbookComplementFamilyZF a n stage ↔
      ∃ r ∈ stage, textbookTupleSpace a n \ r = z := by
  simp [textbookComplementFamilyZF]

/-- Pairwise intersections of members of one finite stage. -/
noncomputable def textbookIntersectionFamilyZF
    (stage : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun p : ZFCarrier stage × ZFCarrier stage => p.1.1 ∩ p.2.1

@[simp]
theorem mem_textbookIntersectionFamilyZF_iff
    {stage z : ZFSet.{u}} :
    z ∈ textbookIntersectionFamilyZF stage ↔
      ∃ r ∈ stage, ∃ t ∈ stage, r ∩ t = z := by
  simp only [textbookIntersectionFamilyZF, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨r, t⟩, h⟩
    exact ⟨r.1, r.2, t.1, t.2, h⟩
  · rintro ⟨r, hr, t, ht, h⟩
    exact ⟨(⟨r, hr⟩, ⟨t, ht⟩), h⟩

/-- Existential projections of every `(n+1)`-ary relation in a stage. -/
noncomputable def textbookProjectionFamilyZF
    (a : ZFSet.{u}) (n : Nat) (higherStage : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun r : ZFCarrier higherStage =>
    textbookExistsProjZF a n r.1

@[simp]
theorem mem_textbookProjectionFamilyZF_iff
    {a higherStage z : ZFSet.{u}} {n : Nat} :
    z ∈ textbookProjectionFamilyZF a n higherStage ↔
      ∃ r ∈ higherStage, textbookExistsProjZF a n r = z := by
  simp [textbookProjectionFamilyZF]

/--
The standard-`Nat` core of the textbook finite closure stages.  Recursion is
on `k` simultaneously for all arities, so the projection branch may use stage
`k` at arity `n+1`.
-/
noncomputable def textbookDStageZF (a : ZFSet.{u}) : Nat → Nat → ZFSet.{u}
  | 0, n => textbookDZeroZF a n
  | k + 1, n =>
      let current := textbookDStageZF a k n
      current ∪ textbookComplementFamilyZF a n current ∪
        textbookIntersectionFamilyZF current ∪
          textbookProjectionFamilyZF a n (textbookDStageZF a k (n + 1))

@[simp]
theorem textbookDStageZF_zero (a : ZFSet.{u}) (n : Nat) :
    textbookDStageZF a 0 n = textbookDZeroZF a n :=
  rfl

@[simp]
theorem mem_textbookDStageZF_succ_iff
    {a r : ZFSet.{u}} {k n : Nat} :
    r ∈ textbookDStageZF a (k + 1) n ↔
      r ∈ textbookDStageZF a k n ∨
      (∃ t ∈ textbookDStageZF a k n,
        textbookTupleSpace a n \ t = r) ∨
      (∃ t ∈ textbookDStageZF a k n,
        ∃ v ∈ textbookDStageZF a k n, t ∩ v = r) ∨
      (∃ t ∈ textbookDStageZF a k (n + 1),
        textbookExistsProjZF a n t = r) := by
  simp only [textbookDStageZF, ZFSet.mem_union,
    mem_textbookComplementFamilyZF_iff,
    mem_textbookIntersectionFamilyZF_iff,
    mem_textbookProjectionFamilyZF_iff]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h



theorem textbookDStageZF_subset_succ
    (a : ZFSet.{u}) (k n : Nat) :
    textbookDStageZF a k n ⊆ textbookDStageZF a (k + 1) n := by
  intro r hr
  exact mem_textbookDStageZF_succ_iff.mpr (Or.inl hr)

theorem textbookDStageZF_mono
    (a : ZFSet.{u}) {k l n : Nat} (hkl : k ≤ l) :
    textbookDStageZF a k n ⊆ textbookDStageZF a l n := by
  induction l, hkl using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ l _ ih =>
      exact ih.trans (textbookDStageZF_subset_succ a l n)

/-! ## The union of all finite stages -/

/-- The genuine ambient `ZFSet`
`Df(a,n) = union_{k in omega} D(k,a,n)` for a standard Lean `Nat` arity.
This definition alone does not assert that the result belongs to a given
transitive model; that requires the internal enumeration and Replacement. -/
noncomputable def textbookDfZF (a : ZFSet.{u}) (n : Nat) : ZFSet.{u} :=
  ZFSet.iUnion fun k : Nat => textbookDStageZF a k n

@[simp]
theorem mem_textbookDfZF_iff {a r : ZFSet.{u}} {n : Nat} :
    r ∈ textbookDfZF a n ↔
      ∃ k : Nat, r ∈ textbookDStageZF a k n := by
  simp [textbookDfZF]

theorem textbookDStageZF_subset_DfZF
    (a : ZFSet.{u}) (k n : Nat) :
    textbookDStageZF a k n ⊆ textbookDfZF a n := by
  intro r hr
  exact mem_textbookDfZF_iff.mpr ⟨k, hr⟩



/-! ## First-order formulas for finite function spaces -/

namespace TextbookDefFormula

/-- The bounded formula saying that `graph` contains `<input, output>`. -/
def graphValueDeltaAt {n : Nat}
    (graph input output : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedEx graph
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) input.castSucc output.castSucc)

/-- `graph` contains the Kuratowski pair `<input, output>`. -/
def graphValueAt {n : Nat}
    (graph input output : Fin n) : FOFormula n :=
  (graphValueDeltaAt graph input output).toFO

@[simp]
theorem satisfies_graphValueDeltaAt {n : Nat}
    (graph input output : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (graphValueDeltaAt graph input output) s ↔
      ZFSet.pair (s input) (s output) ∈ s graph := by
  simp only [graphValueDeltaAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hq
    exact ⟨ZFSet.pair (s input) (s output), hq, rfl⟩

@[simp]
theorem satisfies_graphValueAt {n : Nat}
    (graph input output : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (graphValueAt graph input output) s ↔
      ZFSet.pair (s input) (s output) ∈ s graph := by
  rw [graphValueAt, Delta0Formula.satisfies_toFO,
    satisfies_graphValueDeltaAt]

/-- Bounded graph-in-product predicate. -/
def graphBetweenDeltaAt {n : Nat}
    (graph domain codomain : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedAll graph
    (Delta0Formula.boundedEx domain.castSucc
      (Delta0Formula.boundedEx codomain.castSucc.castSucc
        (Delta0Formula.kuratowskiPairEqAt
          (Fin.last n).castSucc.castSucc
          (Fin.last (n + 1)).castSucc
          (Fin.last (n + 2)))))

/-- Every member of `graph` is a pair from `domain × codomain`. -/
def graphBetweenAt {n : Nat}
    (graph domain codomain : Fin n) : FOFormula n :=
  (graphBetweenDeltaAt graph domain codomain).toFO

@[simp]
theorem satisfies_graphBetweenDeltaAt {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (graphBetweenDeltaAt graph domain codomain) s ↔
      s graph ⊆ ZFSet.prod (s domain) (s codomain) := by
  simp only [graphBetweenDeltaAt,
    Delta0Formula.satisfies_boundedAll, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · intro h q hq
    rcases h q hq with ⟨x, hx, y, hy, hqPair⟩
    rw [ZFSet.mem_prod]
    exact ⟨x, hx, y, hy, hqPair⟩
  · intro h q hq
    rcases ZFSet.mem_prod.mp (h hq) with ⟨x, hx, y, hy, hqPair⟩
    exact ⟨x, hx, y, hy, hqPair⟩

@[simp]
theorem satisfies_graphBetweenAt {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (graphBetweenAt graph domain codomain) s ↔
      s graph ⊆ ZFSet.prod (s domain) (s codomain) := by
  rw [graphBetweenAt, Delta0Formula.satisfies_toFO,
    satisfies_graphBetweenDeltaAt]

/-- Bounded uniqueness of the graph value at one input. -/
def uniqueValueDeltaAt {n : Nat}
    (graph input codomain : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedEx codomain
    (.conj
      (graphValueDeltaAt graph.castSucc input.castSucc (Fin.last n))
      (Delta0Formula.boundedAll codomain.castSucc
        (Delta0Formula.imp
          (graphValueDeltaAt graph.castSucc.castSucc
            input.castSucc.castSucc (Fin.last (n + 1)))
          (.eq (Fin.last (n + 1)) (Fin.last n).castSucc))))

/-- At `input`, `graph` has exactly one value, and that value is in `codomain`. -/
def uniqueValueAt {n : Nat}
    (graph input codomain : Fin n) : FOFormula n :=
  (uniqueValueDeltaAt graph input codomain).toFO

@[simp]
theorem satisfies_uniqueValueDeltaAt {n : Nat}
    (graph input codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (uniqueValueDeltaAt graph input codomain) s ↔
      ∃ output ∈ s codomain,
        ZFSet.pair (s input) output ∈ s graph ∧
          ∀ other ∈ s codomain,
            ZFSet.pair (s input) other ∈ s graph → other = output := by
  simp only [uniqueValueDeltaAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_boundedAll, Delta0Formula.satisfies_imp,
    satisfies_graphValueDeltaAt,
    snoc_last, snoc_castSucc]

@[simp]
theorem satisfies_uniqueValueAt {n : Nat}
    (graph input codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (uniqueValueAt graph input codomain) s ↔
      ∃ output ∈ s codomain,
        ZFSet.pair (s input) output ∈ s graph ∧
          ∀ other ∈ s codomain,
            ZFSet.pair (s input) other ∈ s graph → other = output := by
  rw [uniqueValueAt, Delta0Formula.satisfies_toFO,
    satisfies_uniqueValueDeltaAt]

/-- Bounded predicate for a total set-theoretic function. -/
def isFunctionDeltaAt {n : Nat}
    (graph domain codomain : Fin n) : Delta0Formula n :=
  .conj
    (graphBetweenDeltaAt graph domain codomain)
    (Delta0Formula.boundedAll domain
      (uniqueValueDeltaAt graph.castSucc (Fin.last n) codomain.castSucc))

/-- `graph` is a total set-theoretic function from `domain` to `codomain`. -/
def isFunctionAt {n : Nat}
    (graph domain codomain : Fin n) : FOFormula n :=
  (isFunctionDeltaAt graph domain codomain).toFO

@[simp]
theorem satisfies_isFunctionDeltaAt {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (isFunctionDeltaAt graph domain codomain) s ↔
      ZFSet.IsFunc (s domain) (s codomain) (s graph) := by
  simp only [isFunctionDeltaAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_boundedAll,
    satisfies_graphBetweenDeltaAt, satisfies_uniqueValueDeltaAt,
    snoc_last, snoc_castSucc, ZFSet.IsFunc]
  constructor
  · rintro ⟨hsubset, htotal⟩
    refine ⟨hsubset, ?_⟩
    intro input hinput
    rcases htotal input hinput with
      ⟨output, houtput, hpair, hunique⟩
    refine ⟨output, hpair, ?_⟩
    intro other hother
    have hotherCodomain : other ∈ s codomain :=
      (ZFSet.pair_mem_prod.mp (hsubset hother)).2
    exact hunique other hotherCodomain hother
  · rintro ⟨hsubset, htotal⟩
    refine ⟨hsubset, ?_⟩
    intro input hinput
    rcases htotal input hinput with ⟨output, hpair, hunique⟩
    have houtput : output ∈ s codomain :=
      (ZFSet.pair_mem_prod.mp (hsubset hpair)).2
    exact ⟨output, houtput, hpair,
      fun other _hother => hunique other⟩

@[simp]
theorem satisfies_isFunctionAt {n : Nat}
    (graph domain codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (isFunctionAt graph domain codomain) s ↔
      ZFSet.IsFunc (s domain) (s codomain) (s graph) := by
  rw [isFunctionAt, Delta0Formula.satisfies_toFO,
    satisfies_isFunctionDeltaAt]

/-- `space` is exactly the set of all functions from `domain` to `codomain`. -/
def functionSpaceAt {n : Nat}
    (space domain codomain : Fin n) : FOFormula n :=
  FOFormula.all
    (FOFormula.biimp
      (.mem (Fin.last n) space.castSucc)
      (isFunctionAt (Fin.last n) domain.castSucc codomain.castSucc))

@[simp]
theorem satisfies_functionSpaceAt {n : Nat}
    (space domain codomain : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (functionSpaceAt space domain codomain) s ↔
      s space = ZFSet.funs (s domain) (s codomain) := by
  simp only [functionSpaceAt, FOFormula.satisfies_all,
    FOFormula.satisfies_biimp, FOFormula.Satisfies,
    satisfies_isFunctionAt, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_funs]
    exact h graph
  · intro h graph
    rw [h]
    change graph ∈ ZFSet.funs (s domain) (s codomain) ↔
      ZFSet.IsFunc (s domain) (s codomain) graph
    exact ZFSet.mem_funs

/-- The three-variable graph formula for `(domain,codomain) ↦ codomain^domain`. -/
def functionSpaceGraph : FOFormula 3 :=
  functionSpaceAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

@[simp]
theorem satisfies_functionSpaceGraph
    (domain codomain space : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem functionSpaceGraph
        ![domain, codomain, space] ↔
      space = ZFSet.funs domain codomain := by
  simp [functionSpaceGraph]

end TextbookDefFormula

end Constructible

end
end GCHSource_Work_CUGCH_TextbookDefinability


/- Source module: Solutions.Work_CUGCH_TransitiveZFOmega -/
section GCHSource_Work_CUGCH_TransitiveZFOmega
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Standard omega in transitive set models of ZF

This file proves that every transitive set model of ZF contains the ambient
von Neumann `omega`.  The proof does not assume that `omega` is already in the
model.

First, Infinity supplies an internal inductive set.  Separation inside the
model then constructs its least-inductive subset.  A second use of Separation
shows that every member of this subset is either empty or the successor of an
earlier member.  Ambient well-founded membership induction therefore rules
out nonstandard members, while ordinary natural-number induction gives the
opposite inclusion.

Both separated sets are obtained from the model's Separation scheme before
being identified with ambient `ZFSet.sep` descriptions.  No Power Set,
Replacement, Choice, or externally chosen family is used.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-! ## Elementary closure -/

/-- A transitive ZF model is closed under ambient von Neumann successor. -/
theorem successor_mem_of_isTransitiveZFModel {M x : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    insert x x ∈ M := by
  have hsingleton : ({x} : ZFSet.{u}) ∈ M :=
    singleton_mem_of_isTransitiveZFModel hM hx
  have hpair : ({{x}, x} : ZFSet.{u}) ∈ M :=
    unorderedPair_mem_of_isTransitiveZFModel hM hsingleton hx
  have hunion : ZFSet.sUnion ({{x}, x} : ZFSet.{u}) ∈ M :=
    sUnion_mem_of_isTransitiveZFModel hM hpair
  simpa only [ZFSet.sUnion_pair, ← ZFSet.insert_eq] using hunion

/-- Every standard finite ordinal belongs to a transitive ZF model. -/
theorem natOrdinal_mem_of_isTransitiveZFModel {M : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (n : Nat) :
    (n : Ordinal.{u}).toZFSet ∈ M := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, Ordinal.toZFSet_zero] using
        empty_mem_of_isTransitiveZFModel hM
  | succ n ih =>
      have hsucc := successor_mem_of_isTransitiveZFModel hM ih
      simpa only [Nat.cast_add, Nat.cast_one, ← Ordinal.toZFSet_add_one]
        using hsucc

/-! ## Independent formulas for empty set, successor, and inductiveness -/

 theorem satisfiesIn_all_iff_TransitiveZFOmega_gch
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s ↔
      ∀ x : ZFSet.{u}, x ∈ M →
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

 theorem satisfiesIn_disj_iff_TransitiveZFOmega_gch
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.disj left right) s ↔
      SatisfiesIn M left s ∨ SatisfiesIn M right s := by
  classical
  simp only [FOFormula.disj, SatisfiesIn]
  tauto

 theorem satisfiesIn_imp_iff_TransitiveZFOmega_gch
    (M : Set ZFSet.{u}) {n : Nat} (antecedent consequent : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp antecedent consequent) s ↔
      (SatisfiesIn M antecedent s → SatisfiesIn M consequent s) := by
  classical
  simp only [FOFormula.imp, satisfiesIn_disj_iff_TransitiveZFOmega_gch, SatisfiesIn]
  tauto

/-- Coordinate `i` has no members. -/
def transitiveZFEmptyAt {n : Nat} (i : Fin n) : FOFormula n :=
  FOFormula.all (.neg (.mem (Fin.last n) i.castSucc))

/-- Coordinate `successor` is the von Neumann successor of `index`. -/
def transitiveZFSuccessorAt {n : Nat}
    (successor index : Fin n) : FOFormula n :=
  .conj
    (.mem index successor)
    (.conj
      (FOFormula.all
        (FOFormula.imp
          (.mem (Fin.last n) successor.castSucc)
          (FOFormula.disj
            (.mem (Fin.last n) index.castSucc)
            (.eq (Fin.last n) index.castSucc))))
      (FOFormula.all
        (FOFormula.imp
          (.mem (Fin.last n) index.castSucc)
          (.mem (Fin.last n) successor.castSucc))))

/-- Raw meaning of being inductive relative to the carrier `M`. -/
def ZFInductiveSetIn (M w : ZFSet.{u}) : Prop :=
  (∅ : ZFSet.{u}) ∈ w ∧
    ∀ x : ZFSet.{u}, x ∈ M → x ∈ w → insert x x ∈ w

/-- Coordinate `i` is inductive, using the independent empty and successor
formulas above. -/
def transitiveZFInductiveAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (.ex (.conj
      (transitiveZFEmptyAt (Fin.last n))
      (.mem (Fin.last n) i.castSucc)))
    (FOFormula.all
      (FOFormula.imp
        (.mem (Fin.last n) i.castSucc)
        (.ex (.conj
          (transitiveZFSuccessorAt
            (Fin.last (n + 1)) (Fin.last n).castSucc)
          (.mem (Fin.last (n + 1)) i.castSucc.castSucc)))))

/-- Restricted empty-set semantics over a transitive carrier. -/
theorem satisfiesIn_transitiveZFEmptyAt_iff
    {M : ZFSet.{u}} (htrans : M.IsTransitive) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) (transitiveZFEmptyAt i) s ↔
      s i = (∅ : ZFSet.{u}) := by
  rw [transitiveZFEmptyAt, satisfiesIn_all_iff_TransitiveZFOmega_gch]
  simp only [SatisfiesIn, snoc_last, snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (h z (htrans.mem_trans hz (hs i)) hz).elim
    · intro hz
      exact (ZFSet.notMem_empty z hz).elim
  · intro h z _hzM hz
    rw [h] at hz
    exact (ZFSet.notMem_empty z hz).elim

/-- Restricted successor semantics over a transitive carrier. -/
theorem satisfiesIn_transitiveZFSuccessorAt_iff
    {M : ZFSet.{u}} (htrans : M.IsTransitive) {n : Nat}
    (successor index : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (transitiveZFSuccessorAt successor index) s ↔
      s successor = insert (s index) (s index) := by
  rw [transitiveZFSuccessorAt]
  simp only [SatisfiesIn, satisfiesIn_all_iff_TransitiveZFOmega_gch, satisfiesIn_imp_iff_TransitiveZFOmega_gch,
    satisfiesIn_disj_iff_TransitiveZFOmega_gch, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hindex, hforward, hbackward⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      have hzM : z ∈ M := htrans.mem_trans hz (hs successor)
      rcases hforward z hzM hz with hzIndex | hzEq
      · exact Or.inr hzIndex
      · exact Or.inl hzEq
    · rintro (rfl | hz)
      · exact hindex
      · exact hbackward z (htrans.mem_trans hz (hs index)) hz
  · intro hsuccessor
    rw [hsuccessor]
    refine ⟨ZFSet.mem_insert_iff.mpr (Or.inl rfl), ?_, ?_⟩
    · intro z _hzM hz
      rcases ZFSet.mem_insert_iff.mp hz with hzEq | hzIndex
      · exact Or.inr hzEq
      · exact Or.inl hzIndex
    · intro z _hzM hz
      exact ZFSet.mem_insert_iff.mpr (Or.inr hz)

/-- The independent inductive-set formula has exactly its raw meaning over a
transitive carrier containing the empty set and closed under successor. -/
theorem satisfiesIn_transitiveZFInductiveAt_iff
    {M : ZFSet.{u}} (htrans : M.IsTransitive)
    (hempty : (∅ : ZFSet.{u}) ∈ M)
    (hsuccessor : ∀ x : ZFSet.{u}, x ∈ M → insert x x ∈ M)
    {n : Nat} (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) (transitiveZFInductiveAt i) s ↔
      ZFInductiveSetIn M (s i) := by
  simp only [transitiveZFInductiveAt, SatisfiesIn, satisfiesIn_all_iff_TransitiveZFOmega_gch,
    satisfiesIn_imp_iff_TransitiveZFOmega_gch, snoc_last, snoc_castSucc, ZFInductiveSetIn]
  constructor
  · rintro ⟨⟨e, heM, heEmpty, heMem⟩, hsucc⟩
    have he : e = (∅ : ZFSet.{u}) := by
      simpa only [snoc_last] using
        (satisfiesIn_transitiveZFEmptyAt_iff htrans
          (Fin.last n) (snoc s e) (by
            intro j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using heM
            · simpa using hs k)).mp heEmpty
    constructor
    · simpa only [he] using heMem
    · intro x hxM hxw
      rcases hsucc x hxM hxw with
        ⟨next, hnextM, hnextFormula, hnextMem⟩
      have hnext : next = insert x x := by
        simpa only [snoc_last, snoc_castSucc] using
          (satisfiesIn_transitiveZFSuccessorAt_iff htrans
            (Fin.last (n + 1)) (Fin.last n).castSucc
            (snoc (snoc s x) next) (by
              intro j
              refine Fin.lastCases ?_ (fun j' => ?_) j
              · simpa using hnextM
              · refine Fin.lastCases ?_ (fun k => ?_) j'
                · simpa using hxM
                · simpa using hs k)).mp hnextFormula
      simpa only [hnext] using hnextMem
  · rintro ⟨hemptyMem, hsucc⟩
    constructor
    · refine ⟨∅, hempty, ?_, hemptyMem⟩
      apply (satisfiesIn_transitiveZFEmptyAt_iff htrans
        (Fin.last n) (snoc s (∅ : ZFSet.{u})) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · simpa using hempty
          · simpa using hs k)).mpr
      simp only [snoc_last]
    · intro x hxM hxw
      refine ⟨insert x x, hsuccessor x hxM, ?_, hsucc x hxM hxw⟩
      apply (satisfiesIn_transitiveZFSuccessorAt_iff htrans
        (Fin.last (n + 1)) (Fin.last n).castSucc
        (snoc (snoc s x) (insert x x)) (by
          intro j
          refine Fin.lastCases ?_ (fun j' => ?_) j
          · simpa using hsuccessor x hxM
          · refine Fin.lastCases ?_ (fun k => ?_) j'
            · simpa using hxM
            · simpa using hs k)).mpr
      simp only [snoc_last, snoc_castSucc]

/-! ## The internal least inductive set -/

/-- The unary predicate saying that its argument belongs to every inductive
set in the model. -/
def memberOfEveryInductiveFormula : FOFormula 1 :=
  FOFormula.all
    (FOFormula.imp
      (transitiveZFInductiveAt (Fin.last 1))
      (.mem (0 : Fin 2) (Fin.last 1)))

/-- Exact restricted semantics of `memberOfEveryInductiveFormula`. -/
theorem satisfiesIn_memberOfEveryInductiveFormula_iff
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (s : Tuple ZFSet.{u} 1) (hs : s 0 ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) memberOfEveryInductiveFormula s ↔
      ∀ w : ZFSet.{u}, w ∈ M → ZFInductiveSetIn M w → s 0 ∈ w := by
  have hempty : (∅ : ZFSet.{u}) ∈ M :=
    empty_mem_of_isTransitiveZFModel hM
  have hsuccessor : ∀ x : ZFSet.{u}, x ∈ M → insert x x ∈ M :=
    fun x hx => successor_mem_of_isTransitiveZFModel hM hx
  rw [memberOfEveryInductiveFormula, satisfiesIn_all_iff_TransitiveZFOmega_gch]
  constructor
  · intro h w hwM hwInd
    have himp :=
      (satisfiesIn_imp_iff_TransitiveZFOmega_gch (M : Set ZFSet.{u})
        (transitiveZFInductiveAt (Fin.last 1))
        (.mem (0 : Fin 2) (Fin.last 1)) (snoc s w)).mp
        (h w hwM)
    apply himp
    apply (satisfiesIn_transitiveZFInductiveAt_iff hM.1 hempty
      hsuccessor (Fin.last 1) (snoc s w) (by
        intro j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · change w ∈ M
          exact hwM
        · rw [snoc_castSucc]
          have hk : k = 0 := Fin.eq_zero k
          simpa only [hk] using hs)).mpr
    exact hwInd
  · intro h w hwM
    apply (satisfiesIn_imp_iff_TransitiveZFOmega_gch (M : Set ZFSet.{u})
      (transitiveZFInductiveAt (Fin.last 1))
      (.mem (0 : Fin 2) (Fin.last 1)) (snoc s w)).mpr
    intro hwFormula
    have hwInd : ZFInductiveSetIn M w :=
      (satisfiesIn_transitiveZFInductiveAt_iff hM.1 hempty
        hsuccessor (Fin.last 1) (snoc s w) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change w ∈ M
            exact hwM
          · rw [snoc_castSucc]
            have hk : k = 0 := Fin.eq_zero k
            simpa only [hk] using hs)).mp hwFormula
    change s 0 ∈ w
    exact h w hwM hwInd

/-- Infinity supplies an ambiently recognized inductive member of a
transitive ZF model. -/
theorem exists_zfCarrier_inductiveSetIn
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    ∃ w : ZFCarrier M, ZFInductiveSetIn M w.1 := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  rcases FirstOrder.SetTheory.ZFAxiom.toProp_of_model
      (M := ZFCarrier M) .infinity with
    ⟨w, ⟨e, hew, heEmpty⟩, hsucc⟩
  refine ⟨w, ?_⟩
  have he : e.1 = (∅ : ZFSet.{u}) := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hze
      have hzM : z ∈ M := hM.1.mem_trans hze e.2
      exact (heEmpty ⟨z, hzM⟩ hze).elim
    · intro hz
      exact (ZFSet.notMem_empty z hz).elim
  constructor
  · rw [← he]
    exact hew
  · intro x hxM hxw
    let xM : ZFCarrier M := ⟨x, hxM⟩
    rcases hsucc xM hxw with ⟨y, hyw, hy⟩
    have hyEq : y.1 = insert x x := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_insert_iff]
      constructor
      · intro hzy
        have hzM : z ∈ M := hM.1.mem_trans hzy y.2
        rcases (hy ⟨z, hzM⟩).mp hzy with hzx | hzx
        · exact Or.inr hzx
        · exact Or.inl (congrArg Subtype.val hzx)
      · rintro (rfl | hzx)
        · exact (hy xM).mpr (Or.inr rfl)
        · have hzM : z ∈ M := hM.1.mem_trans hzx hxM
          exact (hy ⟨z, hzM⟩).mpr (Or.inl hzx)
    rw [← hyEq]
    exact hyw

/-- The model contains an internally least inductive set.  Both existence and
minimality are obtained from Infinity and the model's Separation scheme. -/
theorem exists_zfCarrier_leastInductiveSet
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    ∃ omegaM : ZFCarrier M,
      ZFInductiveSetIn M omegaM.1 ∧
        ∀ w : ZFSet.{u}, w ∈ M → ZFInductiveSetIn M w → omegaM.1 ⊆ w := by
  rcases exists_zfCarrier_inductiveSetIn hM with ⟨w, hwInd⟩
  let noParams : Tuple (ZFCarrier M) 0 := fun i => Fin.elim0 i
  rcases exists_zfCarrier_eq_satisfiesIn_sep hM
      memberOfEveryInductiveFormula noParams w with ⟨omegaM, homegaM⟩
  have hspec (x : ZFSet.{u}) :
      x ∈ omegaM.1 ↔
        x ∈ w.1 ∧
          ∀ v : ZFSet.{u}, v ∈ M → ZFInductiveSetIn M v → x ∈ v := by
    rw [homegaM, ZFSet.mem_sep]
    constructor
    · rintro ⟨hxw, hxFormula⟩
      have hxM : x ∈ M := hM.1.mem_trans hxw w.2
      refine ⟨hxw, ?_⟩
      have hsemantic :=
        (satisfiesIn_memberOfEveryInductiveFormula_iff hM
          (snoc (zfCarrierTupleVal noParams) x) (by
            change x ∈ M
            exact hxM)).mp hxFormula
      change ∀ v : ZFSet.{u}, v ∈ M → ZFInductiveSetIn M v → x ∈ v at hsemantic
      exact hsemantic
    · rintro ⟨hxw, hxAll⟩
      have hxM : x ∈ M := hM.1.mem_trans hxw w.2
      refine ⟨hxw, ?_⟩
      apply (satisfiesIn_memberOfEveryInductiveFormula_iff hM
        (snoc (zfCarrierTupleVal noParams) x) (by
          change x ∈ M
          exact hxM)).mpr
      change ∀ v : ZFSet.{u}, v ∈ M → ZFInductiveSetIn M v → x ∈ v
      exact hxAll
  have homegaInd : ZFInductiveSetIn M omegaM.1 := by
    constructor
    · apply (hspec (∅ : ZFSet.{u})).mpr
      refine ⟨hwInd.1, ?_⟩
      intro v _hvM hvInd
      exact hvInd.1
    · intro x hxM hxOmega
      have hxSpec := (hspec x).mp hxOmega
      apply (hspec (insert x x)).mpr
      refine ⟨hwInd.2 x hxM hxSpec.1, ?_⟩
      intro v hvM hvInd
      exact hvInd.2 x hxM (hxSpec.2 v hvM hvInd)
  refine ⟨omegaM, homegaInd, ?_⟩
  intro v hvM hvInd x hxOmega
  exact ((hspec x).mp hxOmega).2 v hvM hvInd

/-! ## Successor decomposition of the internal omega -/

/-- With assignment `(omegaM, x)`, assert that `x` is empty or is the
successor of some member of `omegaM`. -/
def zeroOrSuccessorInFormula : FOFormula 2 :=
  FOFormula.disj
    (transitiveZFEmptyAt (1 : Fin 2))
    (.ex (.conj
      (.mem (2 : Fin 3) (0 : Fin 3))
      (transitiveZFSuccessorAt (1 : Fin 3) (2 : Fin 3))))

/-- Exact restricted semantics of the zero-or-successor formula. -/
theorem satisfiesIn_zeroOrSuccessorInFormula_iff
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (s : Tuple ZFSet.{u} 2) (hs : ∀ j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) zeroOrSuccessorInFormula s ↔
      s 1 = (∅ : ZFSet.{u}) ∨
        ∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ s 0 ∧
          s 1 = insert y y := by
  rw [zeroOrSuccessorInFormula, satisfiesIn_disj_iff_TransitiveZFOmega_gch]
  constructor
  · rintro (hzero | hsucc)
    · exact Or.inl
        ((satisfiesIn_transitiveZFEmptyAt_iff hM.1
          (1 : Fin 2) s hs).mp hzero)
    · rcases hsucc with ⟨y, hyM, hyOmega, hySucc⟩
      refine Or.inr ⟨y, hyM, hyOmega, ?_⟩
      exact (satisfiesIn_transitiveZFSuccessorAt_iff hM.1
        (1 : Fin 3) (2 : Fin 3) (snoc s y) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change y ∈ M
            exact hyM
          · rw [snoc_castSucc]
            exact hs k)).mp hySucc
  · rintro (hzero | ⟨y, hyM, hyOmega, hySucc⟩)
    · exact Or.inl
        ((satisfiesIn_transitiveZFEmptyAt_iff hM.1
          (1 : Fin 2) s hs).mpr hzero)
    · refine Or.inr ⟨y, hyM, hyOmega, ?_⟩
      apply (satisfiesIn_transitiveZFSuccessorAt_iff hM.1
        (1 : Fin 3) (2 : Fin 3) (snoc s y) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change y ∈ M
            exact hyM
          · rw [snoc_castSucc]
            exact hs k)).mpr
      exact hySucc

/-- Every member of an internally least inductive set is empty or an ambient
von Neumann successor of another member.  The auxiliary inductive subset is
obtained by a second application of the model's Separation scheme. -/
theorem mem_leastInductiveSet_zero_or_successor
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (omegaM : ZFCarrier M)
    (homegaInd : ZFInductiveSetIn M omegaM.1)
    (hminimal : ∀ w : ZFSet.{u}, w ∈ M → ZFInductiveSetIn M w →
      omegaM.1 ⊆ w)
    {x : ZFSet.{u}} (hxOmega : x ∈ omegaM.1) :
    x = (∅ : ZFSet.{u}) ∨
      ∃ y : ZFSet.{u}, y ∈ omegaM.1 ∧ x = insert y y := by
  let omegaParam : Tuple (ZFCarrier M) 1 := fun _ => omegaM
  rcases exists_zfCarrier_eq_satisfiesIn_sep hM
      zeroOrSuccessorInFormula omegaParam omegaM with ⟨closed, hclosed⟩
  have hspec (z : ZFSet.{u}) :
      z ∈ closed.1 ↔
        z ∈ omegaM.1 ∧
          (z = (∅ : ZFSet.{u}) ∨
            ∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ omegaM.1 ∧
              z = insert y y) := by
    rw [hclosed, ZFSet.mem_sep]
    constructor
    · rintro ⟨hzOmega, hzFormula⟩
      have hzM : z ∈ M := hM.1.mem_trans hzOmega omegaM.2
      refine ⟨hzOmega, ?_⟩
      have hsemantic :=
        (satisfiesIn_zeroOrSuccessorInFormula_iff hM
          (snoc (zfCarrierTupleVal omegaParam) z) (by
            intro j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · change z ∈ M
              exact hzM
            · rw [snoc_castSucc]
              exact (omegaParam k).2)).mp hzFormula
      change z = (∅ : ZFSet.{u}) ∨
        ∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ omegaM.1 ∧ z = insert y y at hsemantic
      exact hsemantic
    · rintro ⟨hzOmega, hzShape⟩
      have hzM : z ∈ M := hM.1.mem_trans hzOmega omegaM.2
      refine ⟨hzOmega, ?_⟩
      apply (satisfiesIn_zeroOrSuccessorInFormula_iff hM
        (snoc (zfCarrierTupleVal omegaParam) z) (by
          intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · change z ∈ M
            exact hzM
          · rw [snoc_castSucc]
            exact (omegaParam k).2)).mpr
      change z = (∅ : ZFSet.{u}) ∨
        ∃ y : ZFSet.{u}, y ∈ M ∧ y ∈ omegaM.1 ∧ z = insert y y
      exact hzShape
  have hclosedInd : ZFInductiveSetIn M closed.1 := by
    constructor
    · apply (hspec (∅ : ZFSet.{u})).mpr
      exact ⟨homegaInd.1, Or.inl rfl⟩
    · intro z hzM hzClosed
      have hzOmega : z ∈ omegaM.1 := (hspec z).mp hzClosed |>.1
      have hsuccOmega : insert z z ∈ omegaM.1 :=
        homegaInd.2 z hzM hzOmega
      apply (hspec (insert z z)).mpr
      exact ⟨hsuccOmega, Or.inr ⟨z, hzM, hzOmega, rfl⟩⟩
  have hxClosed : x ∈ closed.1 :=
    hminimal closed.1 closed.2 hclosedInd hxOmega
  rcases ((hspec x).mp hxClosed).2 with hzero | ⟨y, _hyM, hyOmega, hsucc⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨y, hyOmega, hsucc⟩

/-! ## Identification with the standard omega -/

/-- The ambient standard omega is inductive relative to every carrier. -/
theorem omegaToZFSet_isInductiveSetIn (M : ZFSet.{u}) :
    ZFInductiveSetIn M Ordinal.omega0.toZFSet := by
  constructor
  · rw [Ordinal.mem_toZFSet_iff]
    exact ⟨0, Ordinal.omega0_pos, Ordinal.toZFSet_zero⟩
  · intro x _hxM hxOmega
    rcases Ordinal.mem_toZFSet_iff.mp hxOmega with ⟨alpha, halpha, rfl⟩
    rw [← Ordinal.toZFSet_add_one]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (by
        rw [← Order.succ_eq_add_one]
        exact Ordinal.isSuccLimit_omega0.succ_lt halpha)

/-- Every standard finite ordinal belongs to an inductive set whose ambient
carrier contains all standard finite ordinals. -/
theorem natOrdinal_mem_of_ZFInductiveSetIn
    {M w : ZFSet.{u}} (hw : ZFInductiveSetIn M w)
    (hnM : ∀ n : Nat, (n : Ordinal.{u}).toZFSet ∈ M)
    (n : Nat) :
    (n : Ordinal.{u}).toZFSet ∈ w := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, Ordinal.toZFSet_zero] using hw.1
  | succ n ih =>
      have hnext := hw.2 (n : Ordinal.{u}).toZFSet (hnM n) ih
      simpa only [Nat.cast_add, Nat.cast_one, ← Ordinal.toZFSet_add_one]
        using hnext

/-- An internally least inductive set in a transitive ZF model is exactly the
ambient standard von Neumann omega. -/
theorem zfCarrier_leastInductiveSet_eq_omega
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (omegaM : ZFCarrier M)
    (homegaInd : ZFInductiveSetIn M omegaM.1)
    (hminimal : ∀ w : ZFSet.{u}, w ∈ M → ZFInductiveSetIn M w →
      omegaM.1 ⊆ w) :
    omegaM.1 = Ordinal.omega0.toZFSet := by
  have hnM : ∀ n : Nat, (n : Ordinal.{u}).toZFSet ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM
  have homegaSubset : Ordinal.omega0.toZFSet ⊆ omegaM.1 := by
    intro x hx
    rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨alpha, halpha, rfl⟩
    rcases Ordinal.lt_omega0.mp halpha with ⟨n, rfl⟩
    exact natOrdinal_mem_of_ZFInductiveSetIn homegaInd hnM n
  have hsubsetOmega : omegaM.1 ⊆ Ordinal.omega0.toZFSet := by
    intro x hxOmega
    refine ZFSet.inductionOn
      (p := fun x : ZFSet.{u} =>
        x ∈ omegaM.1 → x ∈ Ordinal.omega0.toZFSet) x ?_ hxOmega
    intro x ih hxInternal
    rcases mem_leastInductiveSet_zero_or_successor hM omegaM
        homegaInd hminimal hxInternal with hzero | ⟨y, hyInternal, hsucc⟩
    · rw [hzero]
      exact (omegaToZFSet_isInductiveSetIn M).1
    · have hyx : y ∈ x := by
        rw [hsucc]
        exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
      have hyOmega : y ∈ Ordinal.omega0.toZFSet :=
        ih y hyx hyInternal
      have hyM : y ∈ M := hM.1.mem_trans hyInternal omegaM.2
      rw [hsucc]
      exact (omegaToZFSet_isInductiveSetIn M).2 y hyM hyOmega
  exact ZFSet.ext fun x => ⟨fun hx => hsubsetOmega hx,
    fun hx => homegaSubset hx⟩

/-- Every transitive set model of ZF contains the ambient standard omega. -/
theorem omega_toZFSet_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) :
    Ordinal.omega0.toZFSet ∈ M := by
  rcases exists_zfCarrier_leastInductiveSet hM with
    ⟨omegaM, homegaInd, hminimal⟩
  have heq : omegaM.1 = Ordinal.omega0.toZFSet :=
    zfCarrier_leastInductiveSet_eq_omega hM omegaM homegaInd hminimal
  rw [← heq]
  exact omegaM.2

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TransitiveZFOmega


