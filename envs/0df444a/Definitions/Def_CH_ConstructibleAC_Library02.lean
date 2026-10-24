-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library02
-- name    : CH_ConstructibleAC_Library02
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T00:57:05.221172+00:00
-- url     : https://prove2.me/theorems/1bbeb895-f4b7-4fef-a4ed-a040671d7196
-- title:
--   Coding formulas and constructibility stages
-- statement:
--   Finite formulas and their parameter tuples admit set-theoretic codes. The constructible hierarchy starts with the empty set, applies parameter definability at successor stages, and takes unions at limit stages. This library provides the coding interfaces, bounds and ordinal operations, together with finite and indexed sequence representations required by later stage constructions.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Delta0Godel.lean#L1-L622; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Delta0GodelGraph.lean#L1-L516; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Bounding.lean#L1-L66; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Ordinals.lean#L1-L188; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FiniteSequenceZF.lean#L1-L140; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/IndexedSequenceZF.lean#L1-L193

import Definitions.Def_CH_ConstructibleAC_Library01
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


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0Godel -/
section CUAdapterModule3
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Bounded formulas for Gödel operations

This file supplies reusable `Δ₀` formulas for the finite set encodings used
by the Jensen--Devlin Gödel operations.  All coordinate conventions are
intrinsically checked by the `Fin` indices.
-/


open Set

universe u

namespace Constructible.Delta0Formula

/-- Ambient membership on Mathlib's internal ZFC sets. -/
abbrev ZFMem : ZFSet.{u} → ZFSet.{u} → Prop :=
  fun x y => x ∈ y

/-- Formula saying that coordinate `left` is a subset of coordinate `right`. -/
def subsetAt {n : Nat} (left right : Fin n) : Delta0Formula n :=
  .boundedAll left
    (.mem (Fin.last n) right.castSucc)

@[simp]
theorem satisfies_subsetAt {n : Nat} (left right : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (subsetAt left right) s ↔ s left ⊆ s right := by
  simp only [subsetAt, satisfies_boundedAll, Satisfies, snoc_last,
    snoc_castSucc]
  change (∀ z : ZFSet.{u}, z ∈ s left → z ∈ s right) ↔ s left ⊆ s right
  rfl

/-- Formula saying that coordinate `set` is the singleton of coordinate `x`. -/
def singletonEqAt {n : Nat} (set x : Fin n) : Delta0Formula n :=
  .conj (.mem x set)
    (.boundedAll set
      (.eq (Fin.last n) x.castSucc))

@[simp]
theorem satisfies_singletonEqAt {n : Nat} (set x : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (singletonEqAt set x) s ↔
      s set = ({s x} : ZFSet.{u}) := by
  simp only [singletonEqAt, Satisfies, satisfies_boundedAll, snoc_last,
    snoc_castSucc]
  change
    (s x ∈ s set ∧ ∀ z : ZFSet.{u}, z ∈ s set → z = s x) ↔
      s set = ({s x} : ZFSet.{u})
  constructor
  · rintro ⟨hx, hall⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact ZFSet.mem_singleton.mpr (hall z hz)
    · intro hz
      have hzx : z = s x := ZFSet.mem_singleton.mp hz
      subst z
      exact hx
  · intro h
    rw [h]
    simp

/-- Formula saying that coordinate `set` is the unordered pair `{x,y}`. -/
def unorderedPairEqAt {n : Nat} (set x y : Fin n) : Delta0Formula n :=
  .conj (.mem x set)
    (.conj (.mem y set)
      (.boundedAll set
        (.disj
          (.eq (Fin.last n) x.castSucc)
          (.eq (Fin.last n) y.castSucc))))

@[simp]
theorem satisfies_unorderedPairEqAt {n : Nat} (set x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (unorderedPairEqAt set x y) s ↔
      s set = ({s x, s y} : ZFSet.{u}) := by
  simp only [unorderedPairEqAt, Satisfies, satisfies_boundedAll,
    satisfies_disj, snoc_last, snoc_castSucc]
  change
    (s x ∈ s set ∧ s y ∈ s set ∧
      ∀ z : ZFSet.{u}, z ∈ s set → z = s x ∨ z = s y) ↔
      s set = ({s x, s y} : ZFSet.{u})
  constructor
  · rintro ⟨hx, hy, hall⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_pair]
    constructor
    · exact hall z
    · rintro (rfl | rfl)
      · exact hx
      · exact hy
  · intro h
    rw [h]
    simp

/-- Formula saying that coordinate `pair` is `⟨x,y⟩`. -/
def kuratowskiPairEqAt {n : Nat} (pair x y : Fin n) : Delta0Formula n :=
  .conj
    (.boundedEx pair
      (singletonEqAt (Fin.last n) x.castSucc))
    (.conj
      (.boundedEx pair
        (unorderedPairEqAt (Fin.last n) x.castSucc y.castSucc))
      (.boundedAll pair
        (.disj
          (singletonEqAt (Fin.last n) x.castSucc)
          (unorderedPairEqAt (Fin.last n) x.castSucc y.castSucc))))

@[simp]
theorem satisfies_kuratowskiPairEqAt {n : Nat} (pair x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (kuratowskiPairEqAt pair x y) s ↔
      s pair = ZFSet.pair (s x) (s y) := by
  simp only [kuratowskiPairEqAt, Satisfies, satisfies_boundedAll,
    satisfies_disj, satisfies_singletonEqAt, satisfies_unorderedPairEqAt]
  simp only [snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨⟨sx, hsxPair, hsx⟩, ⟨⟨pxy, hpxyPair, hpxy⟩, hall⟩⟩
    apply ZFSet.ext
    intro z
    simp only [ZFSet.pair, ZFSet.mem_pair]
    constructor
    · intro hz
      rcases hall z hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr hz
    · rintro (rfl | rfl)
      · rw [← hsx]
        exact hsxPair
      · rw [← hpxy]
        exact hpxyPair
  · intro h
    rw [h]
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨{s x}, ?_, rfl⟩
      simp [ZFSet.pair]
    · refine ⟨{s x, s y}, ?_, rfl⟩
      simp [ZFSet.pair]
    · intro z hz
      simpa [ZFSet.pair] using hz

/-- Formula saying that coordinate `out` is the right-associated triple `⟨x,y,z⟩`. -/
def tripleEqAt {n : Nat} (out x y z : Fin n) : Delta0Formula n :=
  .boundedEx out
    (.boundedEx (Fin.last n)
      (.conj
        (kuratowskiPairEqAt (Fin.last (n + 1))
          y.castSucc.castSucc z.castSucc.castSucc)
        (kuratowskiPairEqAt out.castSucc.castSucc x.castSucc.castSucc
          (Fin.last (n + 1)))))

@[simp]
theorem satisfies_tripleEqAt {n : Nat} (out x y z : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (tripleEqAt out x y z) s ↔
      s out = Godel.triple (s x) (s y) (s z) := by
  simp only [tripleEqAt, Satisfies, satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨container, hcontainer, inner, hinner, hpair, hout⟩
    rw [hout, hpair]
    rfl
  · intro h
    let inner := ZFSet.pair (s y) (s z)
    rw [h]
    refine ⟨{s x, inner}, ?_, inner, ?_, rfl, rfl⟩
    · simp [Godel.triple, ZFSet.pair, inner]
    · simp [inner]

/--
Bound five witnesses `p ∈ relation`, `leftBox ∈ p`, `left ∈ leftBox`,
`rightBox ∈ p`, and `right ∈ rightBox`.  This supplies bounded
candidates for the two components of a Kuratowski pair belonging to a
relation.
-/
def withBoundedPairComponents {n : Nat} (relation : Fin n)
    (body : Delta0Formula (n + 5)) : Delta0Formula n :=
  .boundedEx relation
    (.boundedEx (Fin.last n)
      (.boundedEx (Fin.last (n + 1))
        (.boundedEx (Fin.last n).castSucc.castSucc
          (.boundedEx (Fin.last (n + 3)) body))))

@[simp]
theorem satisfies_withBoundedPairComponents {A : Type u}
    (E : A → A → Prop) {n : Nat} (relation : Fin n)
    (body : Delta0Formula (n + 5)) (s : Tuple A n) :
    Satisfies E (withBoundedPairComponents relation body) s ↔
      ∃ p : A, E p (s relation) ∧
        ∃ leftBox : A, E leftBox p ∧
          ∃ left : A, E left leftBox ∧
            ∃ rightBox : A, E rightBox p ∧
              ∃ right : A, E right rightBox ∧
                Satisfies E body
                  (snoc (snoc (snoc (snoc (snoc s p) leftBox) left)
                    rightBox) right) := by
  simp only [withBoundedPairComponents, Satisfies, snoc_last,
    snoc_castSucc]

/--
Formula saying `q = {w | ⟨w,z⟩ ∈ x}`.  The reverse containment ranges over
`p ∈ x`, `box ∈ p`, and `w ∈ box`; these bounds are sufficient because
`{w} ∈ ⟨w,z⟩`.
-/
def fiberEqAt {n : Nat} (q x z : Fin n) : Delta0Formula n :=
  .conj
    (.boundedAll q
      (.boundedEx x.castSucc
        (kuratowskiPairEqAt
          (Fin.last (n + 1))
          (Fin.last n).castSucc
          z.castSucc.castSucc)))
    (.boundedAll x
      (.boundedAll (Fin.last n)
        (.boundedAll (Fin.last (n + 1))
          (.imp
            (kuratowskiPairEqAt
              (Fin.last n).castSucc.castSucc
              (Fin.last (n + 2))
              z.castSucc.castSucc.castSucc)
            (.mem (Fin.last (n + 2)) q.castSucc.castSucc.castSucc)))))

@[simp]
theorem satisfies_fiberEqAt {n : Nat} (q x z : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (fiberEqAt q x z) s ↔
      s q = Godel.fiber (s x) (s z) := by
  simp only [fiberEqAt, Satisfies, satisfies_boundedAll, satisfies_imp,
    satisfies_kuratowskiPairEqAt, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro w
    rw [Godel.mem_fiber_iff]
    constructor
    · intro hw
      rcases hsub w hw with ⟨p, hp, hpair⟩
      simpa [hpair] using hp
    · intro hp
      have hsingle : ({w} : ZFSet.{u}) ∈ ZFSet.pair w (s z) := by
        simp [ZFSet.pair]
      exact hsup (ZFSet.pair w (s z)) hp ({w} : ZFSet.{u}) hsingle w
        (by simp) rfl
  · intro h
    constructor
    · intro w hw
      refine ⟨ZFSet.pair w (s z), ?_, rfl⟩
      rw [h] at hw
      simpa using hw
    · intro p hp box hbox w hw hpair
      rw [h]
      change w ∈ Godel.fiber (s x) (s z)
      rw [Godel.mem_fiber_iff]
      simpa [← hpair] using hp

/-- Formula saying that `q` lies in the right-domain operation `F₆(x,-)`. -/
def f6MemAt {n : Nat} (q x : Fin n) : Delta0Formula n :=
  .boundedEx x
    (.boundedEx (Fin.last n)
      (.boundedEx (Fin.last (n + 1))
        (kuratowskiPairEqAt
          (Fin.last n).castSucc.castSucc
          (Fin.last (n + 2))
          q.castSucc.castSucc.castSucc)))

@[simp]
theorem satisfies_f6MemAt {n : Nat} (q x : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f6MemAt q x) s ↔
      ∃ w : ZFSet.{u}, ZFSet.pair w (s q) ∈ s x := by
  simp only [f6MemAt, Satisfies, satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨p, hp, box, hbox, w, hw, hpair⟩
    exact ⟨w, by simpa [← hpair] using hp⟩
  · rintro ⟨w, hw⟩
    refine ⟨ZFSet.pair w (s q), hw, ({w} : ZFSet.{u}), ?_, w, by simp, rfl⟩
    simp [ZFSet.pair]



/-- Formula saying that `q` is a fiber of `x` at some index in `y`. -/
def f8MemAt {n : Nat} (q x y : Fin n) : Delta0Formula n :=
  .boundedEx y
    (fiberEqAt q.castSucc x.castSucc (Fin.last n))

@[simp]
theorem satisfies_f8MemAt {n : Nat} (q x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (f8MemAt q x y) s ↔
      s q ∈ Godel.F8 (s x) (s y) := by
  simp only [f8MemAt, Satisfies, satisfies_fiberEqAt,
    snoc_last, snoc_castSucc]
  rw [Godel.mem_F8_iff]

end Constructible.Delta0Formula

namespace Constructible.Godel

open Constructible.Delta0Formula

/-!
The fixed assignment convention for the following formulas is `![q,x,y]`:
coordinate `0` is the candidate member and coordinates `1,2` are the two
arguments of the Gödel operation.
-/

/-- `q ∈ F₀(x,y)`. -/
def memF0Formula : Delta0Formula 3 :=
  .disj (.eq 0 1) (.eq 0 2)

@[simp]
theorem satisfies_memF0Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF0Formula ![q, x, y] ↔ q ∈ F0 x y := by
  simp [memF0Formula]

/-- `q ∈ F₁(x,y)`. -/
def memF1Formula : Delta0Formula 3 :=
  .conj (.mem 0 1) (.neg (.mem 0 2))

@[simp]
theorem satisfies_memF1Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF1Formula ![q, x, y] ↔ q ∈ F1 x y := by
  simp [memF1Formula]

/-- `q ∈ F₂(x,y) = x × y`. -/
def memF2Formula : Delta0Formula 3 :=
  .boundedEx 1
    (.boundedEx 2
      (kuratowskiPairEqAt 0 3 4))

@[simp]
theorem satisfies_memF2Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF2Formula ![q, x, y] ↔ q ∈ F2 x y := by
  rw [mem_F2_iff]
  simp only [memF2Formula, Satisfies, satisfies_kuratowskiPairEqAt]
  constructor
  · rintro ⟨a, hax, b, hby, hq⟩
    refine ⟨a, hax, b, ?_, ?_⟩
    · change b ∈ y at hby
      exact hby
    · change q = ZFSet.pair a b at hq
      exact hq
  · rintro ⟨a, hax, b, hby, hq⟩
    refine ⟨a, hax, b, ?_, ?_⟩
    · change b ∈ y
      exact hby
    · change q = ZFSet.pair a b
      exact hq

/-- `q ∈ F₃(x,y)`. -/
def memF3Formula : Delta0Formula 3 :=
  .boundedEx 1
    (withBoundedPairComponents 2
      (.conj
        (kuratowskiPairEqAt 4 6 8)
        (tripleEqAt 0 6 3 8)))

set_option maxHeartbeats 400000 in
-- Normalizing the six appended bounded witnesses requires extra kernel reduction.
@[simp]
theorem satisfies_memF3Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF3Formula ![q, x, y] ↔ q ∈ F3 x y := by
  rw [mem_F3_iff]
  change
    (∃ z : ZFSet.{u}, z ∈ x ∧
      Satisfies ZFMem
        (withBoundedPairComponents (2 : Fin 4)
          (.conj
            (kuratowskiPairEqAt 4 6 8)
            (tripleEqAt 0 6 3 8)))
        (snoc ![q, x, y] z)) ↔
      ∃ u z v, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ q = triple u z v
  simp only [satisfies_withBoundedPairComponents, Satisfies,
    satisfies_kuratowskiPairEqAt, satisfies_tripleEqAt]
  change
    (∃ z : ZFSet.{u}, z ∈ x ∧
      ∃ p : ZFSet.{u}, p ∈ y ∧
        ∃ leftBox : ZFSet.{u}, leftBox ∈ p ∧
          ∃ u : ZFSet.{u}, u ∈ leftBox ∧
            ∃ rightBox : ZFSet.{u}, rightBox ∈ p ∧
              ∃ v : ZFSet.{u}, v ∈ rightBox ∧
                (p = ZFSet.pair u v ∧ q = triple u z v)) ↔
      ∃ u z v, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ q = triple u z v
  constructor
  · rintro ⟨z, hzx, p, hpy, leftBox, hleftBox, u, hu,
        rightBox, hrightBox, v, hv, hp, hq⟩
    refine ⟨u, z, v, hzx, ?_, hq⟩
    rw [← hp]
    exact hpy
  · rintro ⟨u, z, v, hzx, huv, hq⟩
    let p := ZFSet.pair u v
    refine ⟨z, hzx, p, ?_, {u}, ?_, u, ?_, {u, v}, ?_, v, ?_, rfl, hq⟩
    · simpa [p] using huv
    · simp [p, ZFSet.pair]
    · simp
    · simp [p, ZFSet.pair]
    · simp

/-- `q ∈ F₄(x,y)`. -/
def memF4Formula : Delta0Formula 3 :=
  .boundedEx 1
    (withBoundedPairComponents 2
      (.conj
        (kuratowskiPairEqAt 4 6 8)
        (tripleEqAt 0 6 8 3)))

set_option maxHeartbeats 400000 in
-- Normalizing the six appended bounded witnesses requires extra kernel reduction.
@[simp]
theorem satisfies_memF4Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF4Formula ![q, x, y] ↔ q ∈ F4 x y := by
  rw [mem_F4_iff]
  change
    (∃ z : ZFSet.{u}, z ∈ x ∧
      Satisfies ZFMem
        (withBoundedPairComponents (2 : Fin 4)
          (.conj
            (kuratowskiPairEqAt 4 6 8)
            (tripleEqAt 0 6 8 3)))
        (snoc ![q, x, y] z)) ↔
      ∃ u v z, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ q = triple u v z
  simp only [satisfies_withBoundedPairComponents, Satisfies,
    satisfies_kuratowskiPairEqAt, satisfies_tripleEqAt]
  change
    (∃ z : ZFSet.{u}, z ∈ x ∧
      ∃ p : ZFSet.{u}, p ∈ y ∧
        ∃ leftBox : ZFSet.{u}, leftBox ∈ p ∧
          ∃ u : ZFSet.{u}, u ∈ leftBox ∧
            ∃ rightBox : ZFSet.{u}, rightBox ∈ p ∧
              ∃ v : ZFSet.{u}, v ∈ rightBox ∧
                (p = ZFSet.pair u v ∧ q = triple u v z)) ↔
      ∃ u v z, z ∈ x ∧ ZFSet.pair u v ∈ y ∧ q = triple u v z
  constructor
  · rintro ⟨z, hzx, p, hpy, leftBox, hleftBox, u, hu,
        rightBox, hrightBox, v, hv, hp, hq⟩
    refine ⟨u, v, z, hzx, ?_, hq⟩
    rw [← hp]
    exact hpy
  · rintro ⟨u, v, z, hzx, huv, hq⟩
    let p := ZFSet.pair u v
    refine ⟨z, hzx, p, ?_, {u}, ?_, u, ?_, {u, v}, ?_, v, ?_, rfl, hq⟩
    · simpa [p] using huv
    · simp [p, ZFSet.pair]
    · simp
    · simp [p, ZFSet.pair]
    · simp

/-- `q ∈ F₅(x,y) = ⋃₀ x`; the second argument is unused. -/
def memF5Formula : Delta0Formula 3 :=
  .boundedEx 1 (.mem 0 3)

@[simp]
theorem satisfies_memF5Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF5Formula ![q, x, y] ↔ q ∈ F5 x y := by
  rw [mem_F5_iff]
  simp only [memF5Formula, Satisfies]
  constructor
  · rintro ⟨w, hwx, hqw⟩
    refine ⟨w, hwx, ?_⟩
    change q ∈ w at hqw
    exact hqw
  · rintro ⟨w, hwx, hqw⟩
    refine ⟨w, hwx, ?_⟩
    change q ∈ w
    exact hqw

/-- `q ∈ F₆(x,y)`; the second argument is unused. -/
def memF6Formula : Delta0Formula 3 :=
  f6MemAt 0 1

@[simp]
theorem satisfies_memF6Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF6Formula ![q, x, y] ↔ q ∈ F6 x y := by
  simp [memF6Formula]

/-- `q ∈ F₇(x,y)`; the second argument is unused. -/
def memF7Formula : Delta0Formula 3 :=
  .boundedEx 1
    (.boundedEx 1
      (.conj (kuratowskiPairEqAt 0 3 4) (.mem 3 4)))

@[simp]
theorem satisfies_memF7Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF7Formula ![q, x, y] ↔ q ∈ F7 x y := by
  rw [mem_F7_iff]
  simp only [memF7Formula, Satisfies]
  constructor
  · rintro ⟨z, hzx, w, hwx, hpair, hzw⟩
    refine ⟨z, hzx, w, ?_, ?_, hzw⟩
    · change w ∈ x at hwx
      exact hwx
    · have hp := (satisfies_kuratowskiPairEqAt (0 : Fin 5)
          (3 : Fin 5) (4 : Fin 5) (snoc (snoc ![q, x, y] z) w)).mp hpair
      change q = ZFSet.pair z w at hp
      exact hp
  · rintro ⟨z, hzx, w, hwx, hq, hzw⟩
    refine ⟨z, hzx, w, ?_, ?_, ?_⟩
    · change w ∈ x
      exact hwx
    · apply (satisfies_kuratowskiPairEqAt (0 : Fin 5)
          (3 : Fin 5) (4 : Fin 5) (snoc (snoc ![q, x, y] z) w)).mpr
      change q = ZFSet.pair z w
      exact hq
    · change z ∈ w
      exact hzw

/-- `q ∈ F₈(x,y)`. -/
def memF8Formula : Delta0Formula 3 :=
  f8MemAt 0 1 2

@[simp]
theorem satisfies_memF8Formula (q x y : ZFSet.{u}) :
    Satisfies ZFMem memF8Formula ![q, x, y] ↔ q ∈ F8 x y := by
  simp [memF8Formula]

/-- Uniform `Δ₀` membership formula for the nine Gödel operations. -/
def memOpFormula (i : Fin 9) : Delta0Formula 3 :=
  match i.1 with
  | 0 => memF0Formula
  | 1 => memF1Formula
  | 2 => memF2Formula
  | 3 => memF3Formula
  | 4 => memF4Formula
  | 5 => memF5Formula
  | 6 => memF6Formula
  | 7 => memF7Formula
  | 8 => memF8Formula
  | _ => .neg (.eq 0 0)

/-- The uniform formula defines membership in `op i x y`. -/
@[simp]
theorem satisfies_memOpFormula (i : Fin 9) (q x y : ZFSet.{u}) :
    Satisfies ZFMem (memOpFormula i) ![q, x, y] ↔
      q ∈ op i x y := by
  fin_cases i <;> simp [memOpFormula, op]



/--
The same operation formula with the section convention used by `DefZF`:
parameters `x,y` come first and the candidate member `q` is last.
-/
def memOpSectionFormula (i : Fin 9) : Delta0Formula 3 :=
  Delta0Formula.rename ![(2 : Fin 3), (0 : Fin 3), (1 : Fin 3)]
    (memOpFormula i)

@[simp]
theorem satisfies_memOpSectionFormula (i : Fin 9) (x y q : ZFSet.{u}) :
    Satisfies ZFMem (memOpSectionFormula i) ![x, y, q] ↔
      q ∈ op i x y := by
  rw [memOpSectionFormula, Delta0Formula.satisfies_rename]
  have hassign :
      (fun j => ![x, y, q] (![(2 : Fin 3), (0 : Fin 3), (1 : Fin 3)] j)) =
        ![q, x, y] := by
    funext j
    fin_cases j <;> rfl
  rw [hassign]
  exact satisfies_memOpFormula i q x y

/--
If the operands lie in a transitive carrier and the operation value is a
subset of that carrier, its uniform `Δ₀` membership formula places the value
in `DefZF`.
-/
theorem op_mem_DefZF_of_subset {U x y : ZFSet.{u}} {i : Fin 9}
    (hU : U.IsTransitive) (hx : x ∈ U) (hy : y ∈ U)
    (hsub : op i x y ⊆ U) :
    op i x y ∈ DefZF U := by
  rw [mem_DefZF_iff_exists_satisfies]
  let sx : ZFCarrier U := ⟨x, hx⟩
  let sy : ZFCarrier U := ⟨y, hy⟩
  let params : Tuple (ZFCarrier U) 2 := ![sx, sy]
  refine ⟨hsub, 2, params, (memOpSectionFormula i).toFO, ?_⟩
  intro q
  rw [Delta0Formula.satisfies_toFO]
  have habs := Delta0Formula.satisfies_absolute hU
    (memOpSectionFormula i) (snoc params q)
  have hamb :
      Satisfies ZFMem (memOpSectionFormula i)
          (Delta0Formula.val (snoc params q)) ↔
        q.1 ∈ op i x y := by
    have hval :
        Delta0Formula.val (snoc params q) = ![x, y, q.1] := by
      funext j
      fin_cases j <;> rfl
    rw [hval]
    exact satisfies_memOpSectionFormula i x y q.1
  exact hamb.symm.trans habs.symm



end Constructible.Godel
end CUAdapterModule3



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Delta0GodelGraph -/
section CUAdapterModule4
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Bounded graph formulas for the Gödel operations

Membership in every Jensen--Devlin operation is `Δ₀`.  This file strengthens
that result to formulas for the full graphs `out = Fᵢ(x,y)`, using only bounded
quantifiers in both containment directions.
-/


open Set

universe u

namespace Constructible.Godel

open Constructible.Delta0Formula

/-- Place the uniform operation-membership formula at arbitrary coordinates. -/
def memOpAt {n : Nat} (i : Fin 9) (q x y : Fin n) : Delta0Formula n :=
  Delta0Formula.rename ![q, x, y] (memOpFormula i)

@[simp]
theorem satisfies_memOpAt {n : Nat} (i : Fin 9) (q x y : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (memOpAt i q x y) s ↔
      s q ∈ op i (s x) (s y) := by
  rw [memOpAt, Delta0Formula.satisfies_rename]
  have hassign :
      (fun j => s (![q, x, y] j)) = ![s q, s x, s y] := by
    funext j
    fin_cases j <;> rfl
  rw [hassign]
  exact satisfies_memOpFormula i (s q) (s x) (s y)

/-- The forward-containment half of an operation graph. -/
def outputSubsetOpAt {n : Nat} (i : Fin 9) (out x y : Fin n) :
    Delta0Formula n :=
  .boundedAll out
    (memOpAt i (Fin.last n) x.castSucc y.castSucc)

@[simp]
theorem satisfies_outputSubsetOpAt {n : Nat} (i : Fin 9)
    (out x y : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (outputSubsetOpAt i out x y) s ↔
      s out ⊆ op i (s x) (s y) := by
  simp only [outputSubsetOpAt, Delta0Formula.satisfies_boundedAll,
    satisfies_memOpAt, snoc_last, snoc_castSucc]
  rfl

/-! All graph formulas below use the fixed assignment `![out,x,y]`. -/

/-- The graph of `F₀(x,y) = {x,y}`. -/
def graphF0Formula : Delta0Formula 3 :=
  unorderedPairEqAt 0 1 2

@[simp]
theorem satisfies_graphF0Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF0Formula ![out, x, y] ↔ out = F0 x y := by
  simp [graphF0Formula, F0]

/-- The fully bounded graph of `F₁(x,y) = x \ y`. -/
def graphF1Formula : Delta0Formula 3 :=
  .conj
    (subsetAt 0 1)
    (.boundedAll 1
      (.biimp
        (.mem 3 0)
        (.neg (.mem 3 2))))

@[simp]
theorem satisfies_graphF1Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF1Formula ![out, x, y] ↔ out = F1 x y := by
  simp only [graphF1Formula, Satisfies, satisfies_subsetAt,
    satisfies_boundedAll, satisfies_biimp]
  rw [ZFSet.ext_iff]
  simp only [mem_F1_iff]
  constructor
  · rintro ⟨houtx, hchar⟩ z
    constructor
    · intro hzout
      have hzx : z ∈ x := houtx hzout
      exact ⟨hzx, (hchar z hzx).mp hzout⟩
    · rintro ⟨hzx, hzy⟩
      exact (hchar z hzx).mpr hzy
  · intro hext
    constructor
    · intro z hzout
      exact (hext z).mp hzout |>.1
    · intro z hzx
      constructor
      · intro hzout
        exact (hext z).mp hzout |>.2
      · intro hzy
        exact (hext z).mpr ⟨hzx, hzy⟩

/-- The fully bounded graph of `F₂(x,y) = x × y`. -/
def graphF2Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (.boundedEx 1
        (.boundedEx 2
          (kuratowskiPairEqAt 3 4 5))))
    (.boundedAll 1
      (.boundedAll 2
        (.boundedEx 0
          (kuratowskiPairEqAt 5 3 4))))

@[simp]
theorem satisfies_graphF2Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF2Formula ![out, x, y] ↔ out = F2 x y := by
  simp only [graphF2Formula, Satisfies, satisfies_boundedAll,
    satisfies_kuratowskiPairEqAt]
  change
    ((∀ q : ZFSet.{u}, q ∈ out →
        ∃ a : ZFSet.{u}, a ∈ x ∧
          ∃ b : ZFSet.{u}, b ∈ y ∧ q = ZFSet.pair a b) ∧
      ∀ a : ZFSet.{u}, a ∈ x →
        ∀ b : ZFSet.{u}, b ∈ y →
          ∃ p : ZFSet.{u}, p ∈ out ∧ p = ZFSet.pair a b) ↔
      out = F2 x y
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    rw [mem_F2_iff]
    constructor
    · exact hsub q
    · rintro ⟨a, hax, b, hby, rfl⟩
      rcases hsup a hax b hby with ⟨p, hp, hpair⟩
      simpa [hpair] using hp
  · intro h
    constructor
    · intro q hq
      rw [h] at hq
      exact mem_F2_iff.mp hq
    · intro a hax b hby
      refine ⟨ZFSet.pair a b, ?_, rfl⟩
      rw [h, mem_F2_iff]
      exact ⟨a, hax, b, hby, rfl⟩

/-- Reverse-containment formula for `F₃`. -/
def containsF3Formula : Delta0Formula 3 :=
  .boundedAll 1
    (.boundedAll 2
      (.boundedAll 4
        (.boundedAll 5
          (.boundedAll 4
            (.boundedAll 7
              (.imp
                (kuratowskiPairEqAt 4 6 8)
                (.boundedEx 0
                  (tripleEqAt 9 6 3 8))))))))

set_option maxHeartbeats 1200000 in
-- Six nested bounded witnesses require extra reduction of appended assignments.
@[simp]
theorem satisfies_containsF3Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem containsF3Formula ![out, x, y] ↔
      ∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u z v := by
  simp only [containsF3Formula, satisfies_boundedAll, satisfies_imp,
    Satisfies, satisfies_kuratowskiPairEqAt, satisfies_tripleEqAt]
  change
    (∀ z : ZFSet.{u}, z ∈ x →
      ∀ p : ZFSet.{u}, p ∈ y →
        ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
          ∀ u : ZFSet.{u}, u ∈ leftBox →
            ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
              ∀ v : ZFSet.{u}, v ∈ rightBox →
                p = ZFSet.pair u v →
                  ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u z v) ↔
      (∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u z v)
  rfl

/-- The fully bounded graph of `F₃(x,y)`. -/
def graphF3Formula : Delta0Formula 3 :=
  .conj (outputSubsetOpAt (3 : Fin 9) 0 1 2) containsF3Formula

@[simp]
theorem satisfies_graphF3Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF3Formula ![out, x, y] ↔ out = F3 x y := by
  simp only [graphF3Formula, Satisfies, satisfies_outputSubsetOpAt,
    satisfies_containsF3Formula]
  change
    (out ⊆ F3 x y ∧
      (∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u z v)) ↔
      out = F3 x y
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    constructor
    · exact fun hqout => hsub hqout
    · intro hq
      rcases mem_F3_iff.mp hq with ⟨u, z, v, hzx, huv, rfl⟩
      rcases hsup z hzx (ZFSet.pair u v) huv ({u} : ZFSet.{u})
          (by simp [ZFSet.pair]) u (by simp) ({u, v} : ZFSet.{u})
          (by simp [ZFSet.pair]) v (by simp) rfl with ⟨q', hq', hq'eq⟩
      rw [← hq'eq]
      exact hq'
  · intro h
    constructor
    · rw [h]
    · intro z hzx p hpy leftBox hleftBox u hu rightBox hrightBox v hv hp
      refine ⟨triple u z v, ?_, rfl⟩
      rw [h, mem_F3_iff]
      refine ⟨u, z, v, hzx, ?_, rfl⟩
      rw [← hp]
      exact hpy

/-- Reverse-containment formula for `F₄`. -/
def containsF4Formula : Delta0Formula 3 :=
  .boundedAll 1
    (.boundedAll 2
      (.boundedAll 4
        (.boundedAll 5
          (.boundedAll 4
            (.boundedAll 7
              (.imp
                (kuratowskiPairEqAt 4 6 8)
                (.boundedEx 0
                  (tripleEqAt 9 6 8 3))))))))

set_option maxHeartbeats 1200000 in
-- Six nested bounded witnesses require extra reduction of appended assignments.
@[simp]
theorem satisfies_containsF4Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem containsF4Formula ![out, x, y] ↔
      ∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u v z := by
  simp only [containsF4Formula, satisfies_boundedAll, satisfies_imp,
    Satisfies, satisfies_kuratowskiPairEqAt, satisfies_tripleEqAt]
  change
    (∀ z : ZFSet.{u}, z ∈ x →
      ∀ p : ZFSet.{u}, p ∈ y →
        ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
          ∀ u : ZFSet.{u}, u ∈ leftBox →
            ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
              ∀ v : ZFSet.{u}, v ∈ rightBox →
                p = ZFSet.pair u v →
                  ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u v z) ↔
      (∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u v z)
  rfl

/-- The fully bounded graph of `F₄(x,y)`. -/
def graphF4Formula : Delta0Formula 3 :=
  .conj (outputSubsetOpAt (4 : Fin 9) 0 1 2) containsF4Formula

@[simp]
theorem satisfies_graphF4Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF4Formula ![out, x, y] ↔ out = F4 x y := by
  simp only [graphF4Formula, Satisfies, satisfies_outputSubsetOpAt,
    satisfies_containsF4Formula]
  change
    (out ⊆ F4 x y ∧
      (∀ z : ZFSet.{u}, z ∈ x →
        ∀ p : ZFSet.{u}, p ∈ y →
          ∀ leftBox : ZFSet.{u}, leftBox ∈ p →
            ∀ u : ZFSet.{u}, u ∈ leftBox →
              ∀ rightBox : ZFSet.{u}, rightBox ∈ p →
                ∀ v : ZFSet.{u}, v ∈ rightBox →
                  p = ZFSet.pair u v →
                    ∃ q : ZFSet.{u}, q ∈ out ∧ q = triple u v z)) ↔
      out = F4 x y
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    constructor
    · exact fun hqout => hsub hqout
    · intro hq
      rcases mem_F4_iff.mp hq with ⟨u, v, z, hzx, huv, rfl⟩
      rcases hsup z hzx (ZFSet.pair u v) huv ({u} : ZFSet.{u})
          (by simp [ZFSet.pair]) u (by simp) ({u, v} : ZFSet.{u})
          (by simp [ZFSet.pair]) v (by simp) rfl with ⟨q', hq', hq'eq⟩
      rw [← hq'eq]
      exact hq'
  · intro h
    constructor
    · rw [h]
    · intro z hzx p hpy leftBox hleftBox u hu rightBox hrightBox v hv hp
      refine ⟨triple u v z, ?_, rfl⟩
      rw [h, mem_F4_iff]
      refine ⟨u, v, z, hzx, ?_, rfl⟩
      rw [← hp]
      exact hpy

/-- The fully bounded graph of `F₅(x,y) = ⋃₀x`. -/
def graphF5Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (.boundedEx 1
        (.mem 3 4)))
    (.boundedAll 1
      (.boundedAll 3
        (.mem 4 0)))

@[simp]
theorem satisfies_graphF5Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF5Formula ![out, x, y] ↔ out = F5 x y := by
  simp only [graphF5Formula, Satisfies, satisfies_boundedAll]
  rw [ZFSet.ext_iff]
  simp only [mem_F5_iff]
  constructor
  · rintro ⟨hforward, hback⟩ z
    constructor
    · exact hforward z
    · rintro ⟨w, hwx, hzw⟩
      exact hback w hwx z hzw
  · intro hext
    constructor
    · intro z hzout
      exact (hext z).mp hzout
    · intro w hwx z hzw
      exact (hext z).mpr ⟨w, hwx, hzw⟩

/-- The fully bounded graph of `F₆(x,y)`. -/
def graphF6Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (f6MemAt 3 1))
    (.boundedAll 1
      (.boundedAll 3
        (.boundedAll 4
          (.imp
            (f6MemAt 5 1)
            (.mem 5 0)))))

@[simp]
theorem satisfies_graphF6Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF6Formula ![out, x, y] ↔ out = F6 x y := by
  simp only [graphF6Formula, Satisfies, satisfies_boundedAll,
    satisfies_imp, satisfies_f6MemAt]
  change
    (((∀ q : ZFSet.{u}, q ∈ out →
          ∃ w : ZFSet.{u}, ZFSet.pair w q ∈ x) ∧
       (∀ p : ZFSet.{u}, p ∈ x →
          ∀ box : ZFSet.{u}, box ∈ p →
            ∀ q : ZFSet.{u}, q ∈ box →
              (∃ w : ZFSet.{u}, ZFSet.pair w q ∈ x) → q ∈ out)) ↔
      out = F6 x y)
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    rw [mem_F6_iff]
    constructor
    · exact hsub q
    · rintro ⟨w, hp⟩
      exact hsup (ZFSet.pair w q) hp ({w, q} : ZFSet.{u})
        (by simp [ZFSet.pair]) q (by simp) ⟨w, hp⟩
  · intro h
    constructor
    · intro q hq
      rw [h] at hq
      exact mem_F6_iff.mp hq
    · intro p hp box hbox q hqbox hq
      rw [h, mem_F6_iff]
      exact hq

/-- The fully bounded graph of `F₇(x,y)`. -/
def graphF7Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (.boundedEx 1
        (.boundedEx 1
          (.conj
            (kuratowskiPairEqAt 3 4 5)
            (.mem 4 5)))))
    (.boundedAll 1
      (.boundedAll 1
        (.imp (.mem 3 4)
          (.boundedEx 0
            (kuratowskiPairEqAt 5 3 4)))))

@[simp]
theorem satisfies_graphF7Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF7Formula ![out, x, y] ↔ out = F7 x y := by
  simp only [graphF7Formula, Satisfies, satisfies_boundedAll, satisfies_imp,
    satisfies_kuratowskiPairEqAt]
  change
    ((∀ q : ZFSet.{u}, q ∈ out →
        ∃ z : ZFSet.{u}, z ∈ x ∧
          ∃ w : ZFSet.{u}, w ∈ x ∧
            (q = ZFSet.pair z w ∧ z ∈ w)) ∧
      ∀ z : ZFSet.{u}, z ∈ x →
        ∀ w : ZFSet.{u}, w ∈ x →
          z ∈ w →
            ∃ p : ZFSet.{u}, p ∈ out ∧ p = ZFSet.pair z w) ↔
      out = F7 x y
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    rw [mem_F7_iff]
    constructor
    · exact hsub q
    · rintro ⟨z, hzx, w, hwx, rfl, hzw⟩
      rcases hsup z hzx w hwx hzw with ⟨p, hp, hpair⟩
      simpa [hpair] using hp
  · intro h
    constructor
    · intro q hq
      rw [h] at hq
      exact mem_F7_iff.mp hq
    · intro z hzx w hwx hzw
      refine ⟨ZFSet.pair z w, ?_, rfl⟩
      rw [h, mem_F7_iff]
      exact ⟨z, hzx, w, hwx, rfl, hzw⟩

/-- The fully bounded graph of `F₈(x,y)`. -/
def graphF8Formula : Delta0Formula 3 :=
  .conj
    (.boundedAll 0
      (f8MemAt 3 1 2))
    (.boundedAll 2
      (.boundedEx 0
        (fiberEqAt 4 1 3)))

@[simp]
theorem satisfies_graphF8Formula (out x y : ZFSet.{u}) :
    Satisfies ZFMem graphF8Formula ![out, x, y] ↔ out = F8 x y := by
  simp only [graphF8Formula, Satisfies, satisfies_boundedAll,
    satisfies_f8MemAt, satisfies_fiberEqAt]
  change
    (((∀ q : ZFSet.{u}, q ∈ out → q ∈ F8 x y) ∧
       (∀ z : ZFSet.{u}, z ∈ y →
          ∃ q : ZFSet.{u}, q ∈ out ∧ q = fiber x z)) ↔
      out = F8 x y)
  constructor
  · rintro ⟨hsub, hsup⟩
    apply ZFSet.ext
    intro q
    constructor
    · exact hsub q
    · intro hq
      rcases mem_F8_iff.mp hq with ⟨z, hzy, hqz⟩
      rcases hsup z hzy with ⟨q', hq'out, hq'z⟩
      simpa [hqz, hq'z] using hq'out
  · intro h
    constructor
    · intro q hq
      simpa [h] using hq
    · intro z hz
      refine ⟨fiber x z, ?_, rfl⟩
      rw [h, mem_F8_iff]
      exact ⟨z, hz, rfl⟩

/-- Uniform fully bounded graph formula for all nine Gödel operations. -/
def opGraphFormula (i : Fin 9) : Delta0Formula 3 :=
  match i.1 with
  | 0 => graphF0Formula
  | 1 => graphF1Formula
  | 2 => graphF2Formula
  | 3 => graphF3Formula
  | 4 => graphF4Formula
  | 5 => graphF5Formula
  | 6 => graphF6Formula
  | 7 => graphF7Formula
  | 8 => graphF8Formula
  | _ => .neg (.eq 0 0)

@[simp]
theorem satisfies_opGraphFormula (i : Fin 9) (out x y : ZFSet.{u}) :
    Satisfies ZFMem (opGraphFormula i) ![out, x, y] ↔
      out = op i x y := by
  fin_cases i <;> simp [opGraphFormula, op]



end Constructible.Godel
end CUAdapterModule4



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Bounding -/
section CUAdapterModule5
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Stage bounds in the constructible hierarchy

This file collects the external bounding facts used to turn set-indexed
families of constructible sets into constructions inside one level of `L`.
The index type of the members of a `ZFSet` is small, so a family of witnesses
in `Ordinal.{u}` has a supremum in the same universe.
-/


open Set

universe u

namespace Constructible

section ZFC

/-- A chosen level at which a constructible set first need not occur, but does occur. -/
noncomputable def stageOf (x : ZFSet.{u}) (hx : x ∈ L) : Ordinal.{u} :=
  Classical.choose hx

theorem mem_LStageZF_stageOf (x : ZFSet.{u}) (hx : x ∈ L) :
    x ∈ LStageZF (stageOf x hx) :=
  Classical.choose_spec hx

/--
All members of an internal set which are constructible occur together in one
level of the constructible hierarchy.
-/
theorem exists_LStage_for_members {a : ZFSet.{u}}
    (ha : ∀ x ∈ a, x ∈ L) :
    ∃ α : Ordinal.{u}, ∀ x ∈ a, x ∈ LStageZF α := by
  let level : a → Ordinal.{u} := fun x => stageOf x.1 (ha x.1 x.2)
  refine ⟨⨆ x : a, level x, ?_⟩
  intro x hx
  let xa : a := ⟨x, hx⟩
  exact LStageZF_mono (Ordinal.le_iSup level xa)
    (mem_LStageZF_stageOf x (ha x hx))





end ZFC

end Constructible
end CUAdapterModule5



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.Ordinals -/
section CUAdapterModule6
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Ordinals in the constructible universe

The property of being a von Neumann ordinal is expressed by a bounded
first-order formula.  Its absoluteness to a transitive level lets us prove,
simultaneously, that the ordinal elements of `LStageZF α` have rank below `α`
and that `α.toZFSet` is contained in that level.
-/


open Set

universe u

namespace Constructible

section ZFC

namespace OrdinalFormula

/-- `x` is transitive, in a context whose only free variable is `x`. -/
def transitive : FOFormula 1 :=
  FOFormula.boundedAll (0 : Fin 1)
    (FOFormula.boundedAll (Fin.last 1)
      (.mem (Fin.last 2) (0 : Fin 3)))

/-- Every member of `x` is transitive. -/
def membersTransitive : FOFormula 1 :=
  FOFormula.boundedAll (0 : Fin 1)
    (FOFormula.boundedAll (Fin.last 1)
      (FOFormula.boundedAll (Fin.last 2)
        (.mem (Fin.last 3) (1 : Fin 4))))

/-- The bounded formula saying that `x` is a von Neumann ordinal. -/
def isOrdinal : FOFormula 1 :=
  .conj transitive membersTransitive

theorem satisfies_transitive {U : ZFSet.{u}} (hU : U.IsTransitive)
    (x : ZFCarrier U) :
    FOFormula.Satisfies (zfCarrierMem U) transitive ![x] ↔
      x.1.IsTransitive := by
  simp only [transitive, FOFormula.satisfies_boundedAll,
    FOFormula.Satisfies, zfCarrierMem, Matrix.cons_val_zero,
    snoc_last]
  constructor
  · intro h y hy z hz
    have hyU : y ∈ U := hU.mem_trans hy x.2
    have hzU : z ∈ U := hU.mem_trans hz hyU
    exact h ⟨y, hyU⟩ hy ⟨z, hzU⟩ hz
  · intro hx y hy z hz
    exact hx.mem_trans hz hy

theorem satisfies_membersTransitive {U : ZFSet.{u}}
    (hU : U.IsTransitive) (x : ZFCarrier U) :
    FOFormula.Satisfies (zfCarrierMem U) membersTransitive ![x] ↔
      ∀ y ∈ x.1, y.IsTransitive := by
  simp only [membersTransitive, FOFormula.satisfies_boundedAll,
    FOFormula.Satisfies, zfCarrierMem, Matrix.cons_val_zero,
    snoc_last]
  constructor
  · intro h y hy z hz w hw
    have hyU : y ∈ U := hU.mem_trans hy x.2
    have hzU : z ∈ U := hU.mem_trans hz hyU
    have hwU : w ∈ U := hU.mem_trans hw hzU
    exact h ⟨y, hyU⟩ hy ⟨z, hzU⟩ hz ⟨w, hwU⟩ hw
  · intro h y hy z hz w hw
    exact (h y.1 hy).mem_trans hw hz

theorem satisfies_isOrdinal {U : ZFSet.{u}} (hU : U.IsTransitive)
    (x : ZFCarrier U) :
    FOFormula.Satisfies (zfCarrierMem U) isOrdinal ![x] ↔
      x.1.IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  simp only [isOrdinal, FOFormula.Satisfies, satisfies_transitive hU x,
    satisfies_membersTransitive hU x]

end OrdinalFormula

/--
If the ordinals in a transitive carrier are exactly those of rank below `α`,
then the internal code for `α` is a definable subset of that carrier.
-/
theorem ordinal_toZFSet_mem_DefZF {U : ZFSet.{u}} {α : Ordinal.{u}}
    (hU : U.IsTransitive) (hsub : α.toZFSet ⊆ U)
    (hrank : ∀ {x : ZFSet.{u}}, x.IsOrdinal → x ∈ U → x.rank < α) :
    α.toZFSet ∈ DefZF U := by
  rw [mem_DefZF_iff_exists_satisfies]
  refine ⟨hsub, 0, (fun i => Fin.elim0 i),
    OrdinalFormula.isOrdinal, ?_⟩
  intro x
  have hassign : snoc (fun i : Fin 0 => Fin.elim0 i) x = ![x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact snoc_last (fun i : Fin 0 => Fin.elim0 i) x
  have hsemantic := OrdinalFormula.satisfies_isOrdinal hU x
  rw [hassign]
  rw [hsemantic]
  constructor
  · intro hx
    exact (ZFSet.isOrdinal_toZFSet α).mem hx
  · intro hx
    rw [← hx.toZFSet_rank_eq]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hrank hx x.2)

/--
The two mutually supporting stage invariants for ordinals: ordinal elements
of `L_α` have rank below `α`, and `α` itself is a subset of `L_α`.
-/
theorem ordinal_stage_invariants (α : Ordinal.{u}) :
    (∀ {x : ZFSet.{u}}, x.IsOrdinal → x ∈ LStageZF α → x.rank < α) ∧
      α.toZFSet ⊆ LStageZF α := by
  induction α using Ordinal.limitRecOn with
  | zero =>
      constructor
      · intro x _hxOrd hx
        rw [LStageZF_zero] at hx
        exact (ZFSet.notMem_empty x hx).elim
      · simp
  | add_one α ih =>
      rw [← Order.succ_eq_add_one]
      have hαmem : α.toZFSet ∈ LStageZF (Order.succ α) := by
        rw [LStageZF_succ]
        exact ordinal_toZFSet_mem_DefZF (LStageZF_isTransitive α) ih.2 ih.1
      constructor
      · intro x hxOrd hx
        rw [LStageZF_succ] at hx
        have hxsub : x ⊆ LStageZF α := (mem_DefZF_iff.mp hx).1
        have hxsubOrdinal : x ⊆ α.toZFSet := by
          intro y hy
          have hyOrd : y.IsOrdinal := hxOrd.mem hy
          have hyrank : y.rank < α := ih.1 hyOrd (hxsub hy)
          rw [← hyOrd.toZFSet_rank_eq]
          exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hyrank
        have hrank : x.rank ≤ α := by
          simpa using
            (ZFSet.IsOrdinal.rank_le_iff_subset hxOrd
              (ZFSet.isOrdinal_toZFSet α)).mpr hxsubOrdinal
        exact Order.lt_succ_iff.mpr hrank
      · intro x hx
        rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨β, hβα, rfl⟩
        rcases (Order.lt_succ_iff.mp hβα).eq_or_lt with hEq | hlt
        · subst β
          exact hαmem
        · exact LStageZF_subset_succ α
            (ih.2 (Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt))
  | limit l hl ih =>
      constructor
      · intro x hxOrd hx
        rcases (mem_LStageZF_limit_iff hl).mp hx with ⟨β, hβl, hxβ⟩
        exact ((ih β hβl).1 hxOrd hxβ).trans hβl
      · intro x hx
        rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨β, hβl, rfl⟩
        have hβinv := ih β hβl
        have hβmem : β.toZFSet ∈ LStageZF (Order.succ β) := by
          rw [LStageZF_succ]
          exact ordinal_toZFSet_mem_DefZF
            (LStageZF_isTransitive β) hβinv.2 hβinv.1
        exact (mem_LStageZF_limit_iff hl).mpr
          ⟨Order.succ β, hl.succ_lt hβl, hβmem⟩

/-- Every ordinal code occurs at the successor of its index. -/
theorem ordinal_toZFSet_mem_LStage_succ (α : Ordinal.{u}) :
    α.toZFSet ∈ LStageZF (Order.succ α) := by
  rw [LStageZF_succ]
  exact ordinal_toZFSet_mem_DefZF (LStageZF_isTransitive α)
    (ordinal_stage_invariants α).2 (ordinal_stage_invariants α).1

/-- Every von Neumann ordinal is constructible. -/
theorem ordinal_toZFSet_mem_L (α : Ordinal.{u}) : α.toZFSet ∈ L :=
  ⟨Order.succ α, ordinal_toZFSet_mem_LStage_succ α⟩

/-- The von Neumann code of `ω` belongs to the constructible universe. -/
theorem omega_mem_L : Ordinal.omega0.toZFSet ∈ L :=
  ordinal_toZFSet_mem_L Ordinal.omega0

end ZFC

end Constructible
end CUAdapterModule6



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteSequenceZF -/
section CUAdapterModule7
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Finite sequences as ZF sets

This file gives a small, structural encoding of finite lists of `ZFSet`s.
The payload is a chain of Kuratowski ordered pairs terminated by the empty
set.  The public sequence code also stores the von Neumann ordinal coding of
the list length.

The construction is deliberately recursive.  In particular, it does not use
an external image and therefore its constructibility proof only needs the
already established closure of `L` under ordered pairs.
-/


universe u

namespace Constructible

namespace FiniteSequenceZF

/-- The von Neumann code of a natural number. -/
noncomputable def natCode (n : Nat) : ZFSet.{u} :=
  (n : Ordinal.{u}).toZFSet

/-- Every natural-number code is constructible. -/
theorem natCode_mem_L (n : Nat) : (natCode n : ZFSet.{u}) ∈ L := by
  simpa only [natCode] using
    (ordinal_toZFSet_mem_L (n : Ordinal.{u}))

/-- Natural-number codes are injective. -/
theorem natCode_injective :
    Function.Injective (natCode : Nat → ZFSet.{u}) := by
  intro m n h
  have hOrdinal : (m : Ordinal.{u}) = (n : Ordinal.{u}) :=
    Ordinal.toZFSet_injective h
  exact_mod_cast hOrdinal

@[simp]
theorem natCode_inj {m n : Nat} :
    (natCode m : ZFSet.{u}) = natCode n ↔ m = n :=
  natCode_injective.eq_iff

/--
The structural payload of a finite sequence.  The empty set is the terminator
and a cons cell is the ordered pair of its head and encoded tail.
-/
def listCode : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | x :: xs => ZFSet.pair x (listCode xs)

@[simp]
theorem listCode_nil : listCode ([] : List ZFSet.{u}) = ∅ :=
  rfl

@[simp]
theorem listCode_cons (x : ZFSet.{u}) (xs : List ZFSet.{u}) :
    listCode (x :: xs) = ZFSet.pair x (listCode xs) :=
  rfl

/-- A cons cell cannot be confused with the empty-list terminator. -/
theorem listCode_cons_ne_empty (x : ZFSet.{u}) (xs : List ZFSet.{u}) :
    listCode (x :: xs) ≠ ∅ := by
  intro h
  have hx : ({x} : ZFSet.{u}) ∈ listCode (x :: xs) := by
    simp [listCode, ZFSet.pair]
  rw [h] at hx
  exact ZFSet.notMem_empty _ hx

/-- The structural list encoding is injective. -/
theorem listCode_injective :
    Function.Injective (listCode : List ZFSet.{u} → ZFSet.{u}) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          exact (listCode_cons_ne_empty y ys h.symm).elim
  | cons x xs ih =>
      cases ys with
      | nil =>
          exact (listCode_cons_ne_empty x xs h).elim
      | cons y ys =>
          rcases ZFSet.pair_inj.mp h with ⟨hxy, htail⟩
          subst y
          have hxs : xs = ys := ih htail
          subst ys
          rfl

@[simp]
theorem listCode_inj {xs ys : List ZFSet.{u}} :
    listCode xs = listCode ys ↔ xs = ys :=
  listCode_injective.eq_iff

/-- The code records both the length and the structural list payload. -/
noncomputable def sequenceCode (xs : List ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (natCode xs.length) (listCode xs)

/-- Equality of sequence codes recovers equality of the original lists. -/
theorem sequenceCode_injective :
    Function.Injective (sequenceCode : List ZFSet.{u} → ZFSet.{u}) := by
  intro xs ys h
  apply listCode_injective
  exact (ZFSet.pair_inj.mp h).2

@[simp]
theorem sequenceCode_inj {xs ys : List ZFSet.{u}} :
    sequenceCode xs = sequenceCode ys ↔ xs = ys :=
  sequenceCode_injective.eq_iff

/-- Structural list codes are constructible when all entries are. -/
theorem listCode_mem_L {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ L) : listCode xs ∈ L := by
  induction xs with
  | nil =>
      exact empty_mem_L
  | cons x xs ih =>
      apply orderedPair_mem_L
      · exact hxs x (by simp)
      · apply ih
        intro y hy
        exact hxs y (by simp [hy])



end FiniteSequenceZF

end Constructible
end CUAdapterModule7



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceZF -/
section CUAdapterModule8
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Indexed finite-sequence codes

The structural list code in `FiniteSequenceZF` is convenient for recursion.
For first-order definitions of lexicographic order, however, direct access to
the entry at an internal natural-number index is more useful.  This file codes
a list by the finite graph

`{ <xs[i], i> | i < xs.length }`

and stores its length alongside that graph.  This indexed-sequence encoding
uses pairs `<output,input>`.  It is intentionally distinct from Mathlib's
`ZFSet.IsFunc` convention, whose function graphs use `<input,output>`.
-/


universe u

namespace Constructible

/--
For lists of equal length, lexicographic comparison occurs at a first index:
the prefixes before that index agree and the entries there satisfy `r`.
-/
theorem listLex_iff_exists_index {α : Type u} {r : α → α → Prop}
    {xs ys : List α} (hlength : xs.length = ys.length) :
    List.Lex r xs ys ↔
      ∃ k : Nat, ∃ hx : k < xs.length, ∃ hy : k < ys.length,
        xs.take k = ys.take k ∧
          r (xs.get ⟨k, hx⟩) (ys.get ⟨k, hy⟩) := by
  induction xs generalizing ys with
  | nil =>
      have hys : ys = [] := List.length_eq_zero_iff.mp hlength.symm
      subst ys
      simp
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlength
      | cons y ys =>
          have htail : xs.length = ys.length := Nat.succ.inj hlength
          constructor
          · intro hlex
            cases hlex with
            | rel hxy =>
                exact ⟨0, by simp, by simp, by simp [hxy]⟩
            | cons hrest =>
                rcases (ih htail).mp hrest with
                  ⟨k, hkx, hky, htake, hk⟩
                refine ⟨k + 1, by simp [hkx], by simp [hky], ?_, ?_⟩
                · simp [htake]
                · simpa using hk
          · rintro ⟨k, hkx, hky, htake, hk⟩
            cases k with
            | zero =>
                exact List.Lex.rel (by simpa using hk)
            | succ k =>
                have hcons : x = y ∧ xs.take k = ys.take k := by
                  simpa using List.cons.inj htake
                rcases hcons with ⟨rfl, htakeTail⟩
                apply List.Lex.cons
                apply (ih htail).mpr
                refine ⟨k, ?_, ?_, htakeTail, ?_⟩
                · simpa using hkx
                · simpa using hky
                · simpa using hk

namespace IndexedSequenceZF

open FiniteSequenceZF

/-- The indexed graph of a list, with indices beginning at `start`. -/
noncomputable def graphFrom (start : Nat) : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | x :: xs =>
      insert (ZFSet.pair x (natCode start)) (graphFrom (start + 1) xs)

@[simp]
theorem graphFrom_nil (start : Nat) :
    graphFrom start ([] : List ZFSet.{u}) = ∅ :=
  rfl

@[simp]
theorem graphFrom_cons (start : Nat) (x : ZFSet.{u})
    (xs : List ZFSet.{u}) :
    graphFrom start (x :: xs) =
      insert (ZFSet.pair x (natCode start)) (graphFrom (start + 1) xs) :=
  rfl

/-- Exact membership description of the indexed graph. -/
@[simp]
theorem mem_graphFrom_iff (start : Nat) (xs : List ZFSet.{u})
    (q : ZFSet.{u}) :
    q ∈ graphFrom start xs ↔
      ∃ i : Fin xs.length,
        q = ZFSet.pair (xs.get i) (natCode (start + i.1)) := by
  induction xs generalizing start with
  | nil =>
      simp [graphFrom]
  | cons x xs ih =>
      rw [graphFrom_cons, ZFSet.mem_insert_iff, ih]
      constructor
      · rintro (rfl | ⟨i, rfl⟩)
        · refine ⟨0, ?_⟩
          simp
        · refine ⟨i.succ, ?_⟩
          simp [Nat.add_comm, Nat.add_left_comm]
      · rintro ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · left
          simp
        · right
          refine ⟨j, ?_⟩
          simp [Nat.add_comm, Nat.add_left_comm]

/-- The indexed graph itself is constructible when all entries are. -/
theorem graphFrom_mem_L {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ L) (start : Nat) :
    graphFrom start xs ∈ L := by
  induction xs generalizing start with
  | nil =>
      exact empty_mem_L
  | cons x xs ih =>
      rw [graphFrom_cons, ZFSet.insert_eq]
      apply union_mem_L
      · apply singleton_mem_L
        exact orderedPair_mem_L
          (hxs x (by simp)) (natCode_mem_L start)
      · apply ih
        intro y hy
        exact hxs y (by simp [hy])

/-- The graph of a list, indexed from zero. -/
noncomputable def graph (xs : List ZFSet.{u}) : ZFSet.{u} :=
  graphFrom 0 xs

@[simp]
theorem mem_graph_iff (xs : List ZFSet.{u}) (q : ZFSet.{u}) :
    q ∈ graph xs ↔
      ∃ i : Fin xs.length,
        q = ZFSet.pair (xs.get i) (natCode i.1) := by
  simp [graph]

/-- A sequence code consists of its length and its indexed graph. -/
noncomputable def sequenceCode (xs : List ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (natCode xs.length) (graph xs)

/-- The indexed graph together with its length determines the list. -/
theorem sequenceCode_injective :
    Function.Injective (sequenceCode : List ZFSet.{u} → ZFSet.{u}) := by
  intro xs ys hcode
  have hparts := ZFSet.pair_inj.mp hcode
  have hlength : xs.length = ys.length :=
    natCode_injective hparts.1
  apply List.ext_get hlength
  intro k hkx hky
  let i : Fin xs.length := ⟨k, hkx⟩
  have hmemX :
      ZFSet.pair (xs.get i) (natCode k) ∈ graph xs := by
    apply (mem_graph_iff xs _).mpr
    exact ⟨i, rfl⟩
  have hmemY :
      ZFSet.pair (xs.get i) (natCode k) ∈ graph ys := by
    rw [← hparts.2]
    exact hmemX
  rcases (mem_graph_iff ys _).mp hmemY with ⟨j, hpair⟩
  have hpairParts := ZFSet.pair_inj.mp hpair
  have hindex : k = j.1 := natCode_injective hpairParts.2
  simpa only [i, hindex] using hpairParts.1

@[simp]
theorem sequenceCode_inj {xs ys : List ZFSet.{u}} :
    sequenceCode xs = sequenceCode ys ↔ xs = ys :=
  sequenceCode_injective.eq_iff

/-- Indexed sequence codes of constructible entries are constructible. -/
theorem sequenceCode_mem_L {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ L) : sequenceCode xs ∈ L := by
  exact orderedPair_mem_L (natCode_mem_L xs.length)
    (graphFrom_mem_L hxs 0)

end IndexedSequenceZF

end Constructible
end CUAdapterModule8


