-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library08
-- name    : CH_ConstructibleAC_Library08
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:15:26.023123+00:00
-- url     : https://prove2.me/theorems/76d67107-dca1-4db7-a456-af1372861026
-- title:
--   Formulas for finite program execution
-- statement:
--   Execution of a finite rudimentary stack program can be described by formulas about coded finite sequences. This library defines the formulas for ordinal successors, sequence order and lookup, trace steps, evaluation, and endpoints. These formulas provide the internal descriptions used to construct and compare well-ordering data at constructible stages.
--
--   The original formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). The Prove2Me packaging preserves the original copyright notices. This module includes supporting proofs needed by its definitions and constructor data.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FiniteOrdinalSuccessorFormula.lean#L1-L198; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/IndexedSequenceOrderFormula.lean#L1-L721; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/IndexedSequenceLookup.lean#L1-L84; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackTraceStepFormula.lean#L1-L359; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackProgramEvalFormula.lean#L1-L352; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RudimentaryStackTraceEndpoints.lean#L1-L99

import Definitions.Def_CH_ConstructibleAC_Library07
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


/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.FiniteOrdinalSuccessorFormula -/
section CUAdapterModule50
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A bounded formula for von Neumann successor

This file defines an arity-polymorphic bounded formula saying that one
coordinate is the von Neumann successor of another.  The formula is used for
the transition from index `k` to index `k + 1` in internally coded execution
traces.
-/


open Set

universe u

namespace Constructible

namespace Delta0Formula

/--
`successorAt succ index` says that `succ = index ∪ {index}`.

The three clauses state that `index ∈ succ`, every member of `succ` is either
a member of `index` or equal to `index`, and every member of `index` belongs
to `succ`.
-/
def successorAt {n : Nat} (succ index : Fin n) : Delta0Formula n :=
  .conj
    (.mem index succ)
    (.conj
      (.boundedAll succ
        (disj
          (.mem (Fin.last n) index.castSucc)
          (.eq (Fin.last n) index.castSucc)))
      (.boundedAll index
        (.mem (Fin.last n) succ.castSucc)))

/-- Ambient semantics of the bounded successor formula. -/
@[simp]
theorem satisfies_successorAt {n : Nat} (succ index : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (successorAt succ index) s ↔
      s succ = insert (s index) (s index) := by
  simp only [successorAt, Satisfies, satisfies_boundedAll,
    satisfies_disj, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hindex, hsucc, hsubset⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hx
      rcases hsucc x hx with hxIndex | hxIndex
      · exact Or.inr hxIndex
      · exact Or.inl hxIndex
    · rintro (rfl | hx)
      · exact hindex
      · exact hsubset x hx
  · intro hsuccEq
    rw [hsuccEq]
    refine ⟨ZFSet.mem_insert_iff.mpr (Or.inl rfl), ?_, ?_⟩
    · intro x hx
      rcases ZFSet.mem_insert_iff.mp hx with rfl | hx
      · exact Or.inr rfl
      · exact Or.inl hx
    · intro x hx
      exact ZFSet.mem_insert_iff.mpr (Or.inr hx)

/-- The same successor predicate in unrestricted first-order syntax. -/
def successorFOAt {n : Nat} (succ index : Fin n) : FOFormula n :=
  (successorAt succ index).toFO

/-- Ambient raw-`ZFSet` semantics of the unrestricted formula. -/
@[simp]
theorem satisfies_successorFOAt_ambient {n : Nat}
    (succ index : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies ZFMem (successorFOAt succ index) s ↔
      s succ = insert (s index) (s index) := by
  rw [successorFOAt, satisfies_toFO, satisfies_successorAt]

/-- Bounded successor semantics directly on the constructible subtype. -/
@[simp]
theorem satisfies_successorAt_lCarrier {n : Nat}
    (succ index : Fin n) (s : Tuple Model.LCarrier.{u} n) :
    Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        (successorAt succ index) s ↔
      (s succ).1 = insert (s index).1 (s index).1 := by
  rw [satisfies_lCarrier_absolute]
  exact satisfies_successorAt succ index (fun i => (s i).1)

/-- First-order successor semantics directly on `LCarrier`. -/
@[simp]
theorem satisfies_successorFOAt_lCarrier {n : Nat}
    (succ index : Fin n) (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        (successorFOAt succ index) s ↔
      (s succ).1 = insert (s index).1 (s index).1 := by
  rw [successorFOAt, satisfies_toFO,
    satisfies_successorAt_lCarrier]

/--
Raw-domain semantics with quantifiers restricted to `L`.  Constructibility of
the whole assignment is the exact hypothesis needed to invoke bounded
absoluteness.
-/
@[simp]
theorem satisfiesIn_L_successorFOAt {n : Nat}
    (succ index : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ L) :
    Model.SatisfiesIn L (successorFOAt succ index) s ↔
      s succ = insert (s index) (s index) := by
  let sL : Tuple Model.LCarrier.{u} n := fun i => ⟨s i, hs i⟩
  have hbridge :=
    Model.satisfies_lCarrier_iff_satisfiesIn_L
      (successorFOAt succ index) sL
  have hbridgeRaw :
      FOFormula.Satisfies
          (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
          (successorFOAt succ index) sL ↔
        Model.SatisfiesIn L (successorFOAt succ index) s := by
    simpa only [sL] using hbridge
  have hsemantic := satisfies_successorFOAt_lCarrier succ index sL
  have hsemanticRaw :
      FOFormula.Satisfies
          (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
          (successorFOAt succ index) sL ↔
        s succ = insert (s index) (s index) := by
    simpa only [sL] using hsemantic
  exact hbridgeRaw.symm.trans hsemanticRaw

end Delta0Formula

namespace FiniteSequenceZF

/-- The von Neumann code of `k + 1` is the successor of the code of `k`. -/
theorem natCode_succ_eq_insert (k : Nat) :
    (natCode (k + 1) : ZFSet.{u}) =
      insert (natCode k) (natCode k) := by
  simp only [natCode, Nat.cast_add, Nat.cast_one,
    Ordinal.toZFSet_add_one]











end FiniteSequenceZF

end Constructible
end CUAdapterModule50



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceOrderFormula -/
section CUAdapterModule51
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# First-order comparison of indexed finite-sequence codes

This file gives fixed object-language formulas for reading the indexed graph
stored by `IndexedSequenceZF.sequenceCode`, comparing prefixes, and building
shortlex comparisons. It uses the indexed representation throughout.
-/


universe u

namespace Constructible.IndexedSequenceZF

open FiniteSequenceZF

/-! ## Indexed access -/

/-- With assignment `[relation,output,input]`, assert `<output,input> ∈ relation`. -/
def graphPairMemAt {n : Nat} (relation output input : Fin n) :
    Delta0Formula n :=
  .boundedEx relation
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) output.castSucc input.castSucc)

@[simp]
theorem satisfies_graphPairMemAt {n : Nat} (relation output input : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (graphPairMemAt relation output input) s ↔
      ZFSet.pair (s output) (s input) ∈ s relation := by
  simp only [graphPairMemAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hq
    exact ⟨ZFSet.pair (s output) (s input), hq, rfl⟩

/--
Supply bounded candidates for the two components of a Kuratowski pair.

If coordinate `pair` is `{{left},{left,right}}`, the four witnesses are the
left singleton, `left`, the unordered pair, and `right`, respectively.
-/
def withBoundedKuratowskiComponents {n : Nat} (pair : Fin n)
    (body : Delta0Formula (n + 4)) : Delta0Formula n :=
  .boundedEx pair
    (.boundedEx (Fin.last n)
      (.boundedEx pair.castSucc.castSucc
        (.boundedEx (Fin.last (n + 2)) body)))

@[simp]
theorem satisfies_withBoundedKuratowskiComponents {A : Type u}
    (E : A → A → Prop) {n : Nat} (pair : Fin n)
    (body : Delta0Formula (n + 4)) (s : Tuple A n) :
    Delta0Formula.Satisfies E
        (withBoundedKuratowskiComponents pair body) s ↔
      ∃ leftBox : A, E leftBox (s pair) ∧
        ∃ left : A, E left leftBox ∧
          ∃ rightBox : A, E rightBox (s pair) ∧
            ∃ right : A, E right rightBox ∧
              Delta0Formula.Satisfies E body
                (snoc (snoc (snoc (snoc s leftBox) left)
                  rightBox) right) := by
  simp only [withBoundedKuratowskiComponents, Delta0Formula.Satisfies,
    snoc_last, snoc_castSucc]

/--
Read one entry from an indexed sequence code.

The assignment layout is `[sequence,index,value]`.  The formula first decodes
`sequence = <length,graph>` and then checks `<value,index> ∈ graph`.
-/
def valueAtDelta0 : Delta0Formula 3 :=
  withBoundedKuratowskiComponents 0
    (.conj
      (Delta0Formula.kuratowskiPairEqAt 0 4 6)
      (.conj (.mem 1 4) (graphPairMemAt 6 2 1)))

/-- The indexed-access predicate in the unrestricted formula syntax. -/
def valueAtFormula : FOFormula 3 :=
  valueAtDelta0.toFO

@[simp]
theorem satisfies_valueAtDelta0 (sequence index value : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem valueAtDelta0
        ![sequence, index, value] ↔
      ∃ length graph : ZFSet.{u},
        sequence = ZFSet.pair length graph ∧
          index ∈ length ∧ ZFSet.pair value index ∈ graph := by
  simp only [valueAtDelta0,
    satisfies_withBoundedKuratowskiComponents,
    Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    satisfies_graphPairMemAt]
  constructor
  · rintro ⟨leftBox, hleftBox, length, hlength,
      rightBox, hrightBox, graph, hgraph, hsequence, hindex, hvalue⟩
    exact ⟨length, graph, hsequence, hindex, hvalue⟩
  · rintro ⟨length, graph, hsequence, hindex, hvalue⟩
    refine ⟨{length}, ?_, length, ?_, {length, graph}, ?_, graph, ?_,
      ?_, ?_, ?_⟩
    · simp [hsequence, ZFSet.pair]
    · simp
    · simp [hsequence, ZFSet.pair]
    · simp
    · change sequence = ZFSet.pair length graph
      exact hsequence
    · change index ∈ length
      exact hindex
    · change ZFSet.pair value index ∈ graph
      exact hvalue

@[simp]
theorem satisfies_valueAtFormula (sequence index value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequence, index, value] ↔
      ∃ length graph : ZFSet.{u},
        sequence = ZFSet.pair length graph ∧
          index ∈ length ∧ ZFSet.pair value index ∈ graph := by
  rw [valueAtFormula, Delta0Formula.satisfies_toFO,
    satisfies_valueAtDelta0]

theorem satisfies_valueAt_sequenceCode_iff (xs : List ZFSet.{u})
    (k : Nat) (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequenceCode xs, natCode k, value] ↔
      ∃ hk : k < xs.length, value = xs.get ⟨k, hk⟩ := by
  rw [satisfies_valueAtFormula]
  constructor
  · rintro ⟨length, relation, hcode, hindex, hmem⟩
    have hparts := ZFSet.pair_inj.mp hcode
    rw [← hparts.2] at hmem
    rcases (mem_graph_iff xs _).mp hmem with ⟨i, hpair⟩
    have hpairParts := ZFSet.pair_inj.mp hpair
    have hk : k < xs.length := by
      have hki : k = i.1 := natCode_injective hpairParts.2
      simpa only [hki] using i.2
    refine ⟨hk, ?_⟩
    have hki : k = i.1 := natCode_injective hpairParts.2
    simpa only [hki] using hpairParts.1
  · rintro ⟨hk, rfl⟩
    refine ⟨natCode xs.length, graph xs, rfl,
      (natCode_mem_natCode_iff k xs.length).mpr hk, ?_⟩
    exact (mem_graph_iff xs _).mpr ⟨⟨k, hk⟩, rfl⟩

/-- Indexed access is sound for every code satisfying the representation invariant. -/
theorem satisfies_valueAt_represents_iff {sequence : ZFSet.{u}}
    {xs : List ZFSet.{u}} (hrep : Represents sequence xs)
    (k : Nat) (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequence, natCode k, value] ↔
      ∃ hk : k < xs.length, value = xs.get ⟨k, hk⟩ := by
  rcases hrep with ⟨relation, hsequence, hgraph⟩
  rw [satisfies_valueAtFormula]
  constructor
  · rintro ⟨length, graph', hcode, hindex, hvalue⟩
    have hparts := ZFSet.pair_inj.mp (hsequence.symm.trans hcode)
    rw [← hparts.1] at hindex
    rw [← hparts.2] at hvalue
    have hk : k < xs.length :=
      (natCode_mem_natCode_iff k xs.length).mp hindex
    exact ⟨hk, (hgraph ⟨k, hk⟩).2 value hvalue⟩
  · rintro ⟨hk, hvalue⟩
    refine ⟨natCode xs.length, relation, hsequence,
      (natCode_mem_natCode_iff k xs.length).mpr hk, ?_⟩
    simpa only [hvalue] using (hgraph ⟨k, hk⟩).1

/-! ## Equal prefixes -/

/-- The members of a finite von Neumann ordinal are exactly earlier codes. -/
@[simp]
theorem mem_natCode_iff (index : ZFSet.{u}) (k : Nat) :
    index ∈ natCode k ↔
      ∃ j : Nat, j < k ∧ index = natCode j := by
  constructor
  · intro hindex
    change index ∈ (k : Ordinal.{u}).toZFSet at hindex
    rcases Ordinal.mem_toZFSet_iff.mp hindex with ⟨beta, hbeta, rfl⟩
    have hbetaOmega : beta < Ordinal.omega0 :=
      hbeta.trans (Ordinal.natCast_lt_omega0 k)
    rcases Ordinal.lt_omega0.mp hbetaOmega with ⟨j, rfl⟩
    refine ⟨j, ?_, rfl⟩
    exact_mod_cast hbeta
  · rintro ⟨j, hj, rfl⟩
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (by exact_mod_cast hj)

/--
All entries before a coded bound agree.

The assignment layout is `[leftSequence,rightSequence,bound]`.  For every
internal index in `bound`, one common value must be readable from both indexed
graphs.
-/
def samePrefixFormula : FOFormula 3 :=
  FOFormula.boundedAll 2
    (.ex (.conj
      (FOFormula.rename
        ![(0 : Fin 5), (3 : Fin 5), (4 : Fin 5)] valueAtFormula)
      (FOFormula.rename
        ![(1 : Fin 5), (3 : Fin 5), (4 : Fin 5)] valueAtFormula)))

@[simp]
theorem satisfies_samePrefixFormula
    (leftSequence rightSequence bound : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem samePrefixFormula
        ![leftSequence, rightSequence, bound] ↔
      ∀ index : ZFSet.{u}, index ∈ bound →
        ∃ value : ZFSet.{u},
          FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
              ![leftSequence, index, value] ∧
            FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
              ![rightSequence, index, value] := by
  simp only [samePrefixFormula, FOFormula.satisfies_boundedAll,
    FOFormula.Satisfies, FOFormula.satisfies_rename]
  constructor
  · intro h index hindex
    rcases h index hindex with ⟨value, hleft, hright⟩
    refine ⟨value, ?_, ?_⟩
    · change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![leftSequence, index, value] at hleft
      exact hleft
    · change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![rightSequence, index, value] at hright
      exact hright
  · intro h index hindex
    rcases h index hindex with ⟨value, hleft, hright⟩
    refine ⟨value, ?_, ?_⟩
    · change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        (fun i => snoc (snoc ![leftSequence, rightSequence, bound] index) value
          (![0, 3, 4] i))
      exact hleft
    · change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        (fun i => snoc (snoc ![leftSequence, rightSequence, bound] index) value
          (![1, 3, 4] i))
      exact hright



/-- Prefix comparison is sound for arbitrary represented sequence codes. -/
theorem satisfies_samePrefix_represents_iff
    {leftSequence rightSequence : ZFSet.{u}}
    {xs ys : List ZFSet.{u}}
    (hleft : Represents leftSequence xs)
    (hright : Represents rightSequence ys) (k : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem samePrefixFormula
        ![leftSequence, rightSequence, natCode k] ↔
      ∀ j : Nat, j < k →
        ∃ hx : j < xs.length, ∃ hy : j < ys.length,
          xs.get ⟨j, hx⟩ = ys.get ⟨j, hy⟩ := by
  rw [satisfies_samePrefixFormula]
  constructor
  · intro h j hj
    rcases h (natCode j) ((mem_natCode_iff _ _).mpr ⟨j, hj, rfl⟩) with
      ⟨value, hvalueLeft, hvalueRight⟩
    rcases (satisfies_valueAt_represents_iff hleft j value).mp
        hvalueLeft with ⟨hx, hvalueX⟩
    rcases (satisfies_valueAt_represents_iff hright j value).mp
        hvalueRight with ⟨hy, hvalueY⟩
    exact ⟨hx, hy, hvalueX.symm.trans hvalueY⟩
  · intro h index hindex
    rcases (mem_natCode_iff index k).mp hindex with ⟨j, hj, rfl⟩
    rcases h j hj with ⟨hx, hy, hxy⟩
    refine ⟨xs.get ⟨j, hx⟩, ?_, ?_⟩
    · exact (satisfies_valueAt_represents_iff hleft j _).mpr ⟨hx, rfl⟩
    · exact (satisfies_valueAt_represents_iff hright j _).mpr ⟨hy, hxy⟩

/-- Pointwise agreement below `k` is equivalent to equality of `take k`. -/
theorem take_eq_take_iff_pointwise (xs ys : List ZFSet.{u}) (k : Nat)
    (hkx : k ≤ xs.length) (hky : k ≤ ys.length) :
    xs.take k = ys.take k ↔
      ∀ j : Nat, j < k →
        ∃ hx : j < xs.length, ∃ hy : j < ys.length,
          xs.get ⟨j, hx⟩ = ys.get ⟨j, hy⟩ := by
  constructor
  · intro htake j hj
    have hx : j < xs.length := hj.trans_le hkx
    have hy : j < ys.length := hj.trans_le hky
    have hjx : j < (xs.take k).length := by
      simpa only [List.length_take, Nat.min_eq_left hkx] using hj
    have hjy : j < (ys.take k).length := by
      simpa only [List.length_take, Nat.min_eq_left hky] using hj
    have hget :
        (xs.take k).get ⟨j, hjx⟩ =
          (ys.take k).get ⟨j, hjy⟩ := by
      have hoption := congrArg (fun zs : List ZFSet.{u} => zs[j]?) htake
      change (xs.take k)[j]? = (ys.take k)[j]? at hoption
      rw [List.getElem?_eq_getElem hjx,
        List.getElem?_eq_getElem hjy] at hoption
      exact Option.some.inj hoption
    refine ⟨hx, hy, ?_⟩
    simpa using hget
  · intro hpoint
    apply List.ext_get
    · simp only [List.length_take, Nat.min_eq_left hkx,
        Nat.min_eq_left hky]
    · intro j hjx hjy
      have hj : j < k := by
        simpa only [List.length_take, Nat.min_eq_left hkx] using hjx
      rcases hpoint j hj with ⟨hx, hy, hget⟩
      simpa using hget



/-! ## Shortlex -/

/-- With assignment `[sequence,length]`, decode the recorded length. -/
def hasLengthFormula : FOFormula 2 :=
  .ex (Delta0Formula.kuratowskiPairEqAt 0 1 2).toFO

@[simp]
theorem satisfies_hasLengthFormula (sequence length : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
        ![sequence, length] ↔
      ∃ graph : ZFSet.{u}, sequence = ZFSet.pair length graph := by
  simp [hasLengthFormula, Model.snoc_eq_finSnoc]



theorem satisfies_hasLength_represents_iff {sequence : ZFSet.{u}}
    {xs : List ZFSet.{u}} (hrep : Represents sequence xs)
    (length : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
        ![sequence, length] ↔
      length = natCode xs.length := by
  rcases hrep with ⟨graph, hsequence, _hgraph⟩
  rw [satisfies_hasLengthFormula]
  constructor
  · rintro ⟨graph', hcode⟩
    exact (ZFSet.pair_inj.mp (hsequence.symm.trans hcode)).1.symm
  · rintro rfl
    exact ⟨graph, hsequence⟩

/-
For `tokenLt : FOFormula (parameterCount + 2)`, the two last coordinates are
the compared values.  The resulting shortlex formula has layout

`[token parameters..., omega, leftSequence, rightSequence]`.
-/

/-- Select the omega and left-sequence coordinates for the validity formula. -/
def validityLeftRename (parameterCount : Nat) :
    Fin 2 → Fin (parameterCount + 3) :=
  ![(Fin.last parameterCount).castSucc.castSucc,
    (Fin.last (parameterCount + 1)).castSucc]

/-- Select the omega and right-sequence coordinates for the validity formula. -/
def validityRightRename (parameterCount : Nat) :
    Fin 2 → Fin (parameterCount + 3) :=
  ![(Fin.last parameterCount).castSucc.castSucc,
    Fin.last (parameterCount + 2)]

/-- Select the left sequence and its length coordinate. -/
def leftLengthRename (parameterCount : Nat) :
    Fin 2 → Fin (parameterCount + 5) :=
  ![(Fin.last (parameterCount + 1)).castSucc.castSucc.castSucc,
    (Fin.last (parameterCount + 3)).castSucc]

/-- Select the right sequence and its length coordinate. -/
def rightLengthRename (parameterCount : Nat) :
    Fin 2 → Fin (parameterCount + 5) :=
  ![(Fin.last (parameterCount + 2)).castSucc.castSucc,
    Fin.last (parameterCount + 4)]

/-- Select both sequences and the current prefix index. -/
def prefixRename (parameterCount : Nat) :
    Fin 3 → Fin (parameterCount + 6) :=
  ![(Fin.last (parameterCount + 1)).castSucc.castSucc.castSucc.castSucc,
    (Fin.last (parameterCount + 2)).castSucc.castSucc.castSucc,
    Fin.last (parameterCount + 5)]

/-- Select the left sequence, index, and decoded value. -/
def leftValueRename (parameterCount : Nat) :
    Fin 3 → Fin (parameterCount + 8) :=
  ![(Fin.last (parameterCount + 1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc,
    (Fin.last (parameterCount + 5)).castSucc.castSucc,
    (Fin.last (parameterCount + 6)).castSucc]

/-- Select the right sequence, index, and decoded value. -/
def rightValueRename (parameterCount : Nat) :
    Fin 3 → Fin (parameterCount + 8) :=
  ![(Fin.last (parameterCount + 2)).castSucc.castSucc.castSucc.castSucc.castSucc,
    (Fin.last (parameterCount + 5)).castSucc.castSucc,
    Fin.last (parameterCount + 7)]

/-- Select the two decoded token values for comparison. -/
def tokenLtRename (parameterCount : Nat) :
    Fin (parameterCount + 2) → Fin (parameterCount + 8) :=
  Fin.lastCases (Fin.last (parameterCount + 7))
    (fun j => Fin.lastCases (Fin.last (parameterCount + 6)).castSucc
      (fun i =>
        i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
      j)

theorem comp_validityLeftRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount) (omega left right : A) :
    (fun i => snoc (snoc (snoc params omega) left) right
      (validityLeftRename parameterCount i)) = ![omega, left] := by
  funext i
  fin_cases i <;> simp [validityLeftRename]

theorem comp_validityRightRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount) (omega left right : A) :
    (fun i => snoc (snoc (snoc params omega) left) right
      (validityRightRename parameterCount i)) = ![omega, right] := by
  funext i
  fin_cases i <;> simp [validityRightRename]

theorem comp_leftLengthRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength : A) :
    (fun i =>
      snoc (snoc (snoc (snoc (snoc params omega) left) right)
        leftLength) rightLength (leftLengthRename parameterCount i)) =
      ![left, leftLength] := by
  funext i
  fin_cases i <;> simp [leftLengthRename]

theorem comp_rightLengthRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength : A) :
    (fun i =>
      snoc (snoc (snoc (snoc (snoc params omega) left) right)
        leftLength) rightLength (rightLengthRename parameterCount i)) =
      ![right, rightLength] := by
  funext i
  fin_cases i <;> simp [rightLengthRename]

theorem comp_prefixRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength index : A) :
    (fun i =>
      snoc (snoc (snoc (snoc (snoc (snoc params omega) left) right)
        leftLength) rightLength) index (prefixRename parameterCount i)) =
      ![left, right, index] := by
  funext i
  fin_cases i <;> simp [prefixRename]

theorem comp_leftValueRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength index leftValue rightValue : A) :
    (fun i =>
      snoc (snoc
        (snoc (snoc (snoc (snoc (snoc (snoc params omega) left) right)
          leftLength) rightLength) index) leftValue) rightValue
        (leftValueRename parameterCount i)) =
      ![left, index, leftValue] := by
  funext i
  fin_cases i <;> simp [leftValueRename]

theorem comp_rightValueRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength index leftValue rightValue : A) :
    (fun i =>
      snoc (snoc
        (snoc (snoc (snoc (snoc (snoc (snoc params omega) left) right)
          leftLength) rightLength) index) leftValue) rightValue
        (rightValueRename parameterCount i)) =
      ![right, index, rightValue] := by
  funext i
  fin_cases i <;> simp [rightValueRename]

theorem comp_tokenLtRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength index leftValue rightValue : A) :
    (fun i =>
      snoc (snoc
        (snoc (snoc (snoc (snoc (snoc (snoc params omega) left) right)
          leftLength) rightLength) index) leftValue) rightValue
        (tokenLtRename parameterCount i)) =
      snoc (snoc params leftValue) rightValue := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [tokenLtRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [tokenLtRename]
    · simp [tokenLtRename]

/-- The body after the two recorded lengths have been decoded. -/
def shortlexCore {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2)) :
    FOFormula (parameterCount + 5) :=
  .conj
    (FOFormula.rename (leftLengthRename parameterCount) hasLengthFormula)
    (.conj
      (FOFormula.rename (rightLengthRename parameterCount) hasLengthFormula)
      (FOFormula.disj
        (.mem (Fin.last (parameterCount + 3)).castSucc
          (Fin.last (parameterCount + 4)))
        (.conj
          (.eq (Fin.last (parameterCount + 3)).castSucc
            (Fin.last (parameterCount + 4)))
          (FOFormula.boundedEx (Fin.last (parameterCount + 3)).castSucc
            (.conj
              (FOFormula.rename (prefixRename parameterCount)
                samePrefixFormula)
              (.ex (.ex
                (.conj
                  (FOFormula.rename (leftValueRename parameterCount)
                    valueAtFormula)
                  (.conj
                    (FOFormula.rename (rightValueRename parameterCount)
                      valueAtFormula)
                    (FOFormula.rename (tokenLtRename parameterCount)
                      tokenLt))))))))))

/--
Validity-guarded shortlex comparison of two indexed sequence codes.

The free assignment is `[token parameters..., omega, leftSequence,
rightSequence]`.  The final two variables of `tokenLt` receive the entries at
the first differing index.
-/
def shortlexFormula {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2)) :
    FOFormula (parameterCount + 3) :=
  .conj
    (FOFormula.rename (validityLeftRename parameterCount)
      sequenceValidityFormula)
    (.conj
      (FOFormula.rename (validityRightRename parameterCount)
        sequenceValidityFormula)
      (.ex (.ex (shortlexCore tokenLt))))

theorem satisfies_shortlexFormula {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple ZFSet.{u} parameterCount)
    (omega leftSequence rightSequence : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem (shortlexFormula tokenLt)
        (snoc (snoc (snoc params omega) leftSequence) rightSequence) ↔
      FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
          ![omega, leftSequence] ∧
        FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
          ![omega, rightSequence] ∧
        ∃ leftLength rightLength : ZFSet.{u},
          FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
              ![leftSequence, leftLength] ∧
            FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
              ![rightSequence, rightLength] ∧
            (leftLength ∈ rightLength ∨
              leftLength = rightLength ∧
                ∃ index : ZFSet.{u}, index ∈ leftLength ∧
                  FOFormula.Satisfies Delta0Formula.ZFMem samePrefixFormula
                      ![leftSequence, rightSequence, index] ∧
                    ∃ leftValue rightValue : ZFSet.{u},
                      FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
                          ![leftSequence, index, leftValue] ∧
                        FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
                          ![rightSequence, index, rightValue] ∧
                        FOFormula.Satisfies Delta0Formula.ZFMem tokenLt
                          (snoc (snoc params leftValue) rightValue)) := by
  simp only [shortlexFormula, shortlexCore, FOFormula.Satisfies,
    FOFormula.satisfies_rename, FOFormula.satisfies_disj,
    FOFormula.satisfies_boundedEx, comp_validityLeftRename,
    comp_validityRightRename, comp_leftLengthRename,
    comp_rightLengthRename, comp_prefixRename, comp_leftValueRename,
    comp_rightValueRename, comp_tokenLtRename, snoc_last, snoc_castSucc]

/--
Semantic correctness on any two valid representations.  The supplied token
formula may use the preceding parameter tuple; its final two coordinates are
interpreted by `R`.
-/
theorem satisfies_shortlexFormula_represents_iff
    {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple ZFSet.{u} parameterCount)
    (R : ZFSet.{u} → ZFSet.{u} → Prop)
    {leftSequence rightSequence : ZFSet.{u}}
    {xs ys : List ZFSet.{u}}
    (hleft : Represents leftSequence xs)
    (hright : Represents rightSequence ys)
    (htoken : ∀ leftValue rightValue : ZFSet.{u},
      FOFormula.Satisfies Delta0Formula.ZFMem tokenLt
          (snoc (snoc params leftValue) rightValue) ↔
        R leftValue rightValue) :
    FOFormula.Satisfies Delta0Formula.ZFMem (shortlexFormula tokenLt)
        (snoc (snoc (snoc params Ordinal.omega0.toZFSet)
          leftSequence) rightSequence) ↔
      List.Shortlex R xs ys := by
  rw [satisfies_shortlexFormula]
  have hvalidLeft :
      FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
        ![Ordinal.omega0.toZFSet, leftSequence] :=
    (satisfies_sequenceValidityFormula_iff_exists_represents leftSequence).mpr
      ⟨xs, hleft⟩
  have hvalidRight :
      FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
        ![Ordinal.omega0.toZFSet, rightSequence] :=
    (satisfies_sequenceValidityFormula_iff_exists_represents rightSequence).mpr
      ⟨ys, hright⟩
  constructor
  · rintro ⟨_hvalidLeft, _hvalidRight, leftLength, rightLength,
      hleftLength, hrightLength, hshort⟩
    have hleftLengthEq :=
      (satisfies_hasLength_represents_iff hleft leftLength).mp hleftLength
    have hrightLengthEq :=
      (satisfies_hasLength_represents_iff hright rightLength).mp hrightLength
    subst leftLength
    subst rightLength
    rcases hshort with hlength | ⟨hlengthCode, index, hindex,
        hprefix, leftValue, rightValue, hleftValue, hrightValue, hlt⟩
    · exact List.Shortlex.of_length_lt
        ((natCode_mem_natCode_iff xs.length ys.length).mp hlength)
    · have hlength : xs.length = ys.length :=
        natCode_injective hlengthCode
      rcases (mem_natCode_iff index xs.length).mp hindex with
        ⟨k, hk, rfl⟩
      have hpoint :=
        (satisfies_samePrefix_represents_iff hleft hright k).mp hprefix
      have hkRightLe : k ≤ ys.length := by
        rw [← hlength]
        exact hk.le
      have htake : xs.take k = ys.take k :=
        (take_eq_take_iff_pointwise xs ys k hk.le hkRightLe).mpr hpoint
      rcases (satisfies_valueAt_represents_iff hleft k leftValue).mp
          hleftValue with ⟨hkx, hleftValueEq⟩
      rcases (satisfies_valueAt_represents_iff hright k rightValue).mp
          hrightValue with ⟨hky, hrightValueEq⟩
      have hrelation :
          R (xs.get ⟨k, hkx⟩) (ys.get ⟨k, hky⟩) := by
        apply (htoken leftValue rightValue).mp at hlt
        simpa only [hleftValueEq, hrightValueEq] using hlt
      apply List.Shortlex.of_lex hlength
      apply (listLex_iff_exists_index hlength).mpr
      exact ⟨k, hkx, hky, htake, hrelation⟩
  · intro hshortlex
    refine ⟨hvalidLeft, hvalidRight, natCode xs.length,
      natCode ys.length, ?_, ?_, ?_⟩
    · exact (satisfies_hasLength_represents_iff hleft _).mpr rfl
    · exact (satisfies_hasLength_represents_iff hright _).mpr rfl
    · rcases List.shortlex_def.mp hshortlex with hlength | ⟨hlength, hlex⟩
      · exact Or.inl
          ((natCode_mem_natCode_iff xs.length ys.length).mpr hlength)
      · apply Or.inr
        refine ⟨congrArg natCode hlength, ?_⟩
        rcases (listLex_iff_exists_index hlength).mp hlex with
          ⟨k, hkx, hky, htake, hrelation⟩
        refine ⟨natCode k,
          (natCode_mem_natCode_iff k xs.length).mpr hkx, ?_,
          xs.get ⟨k, hkx⟩, ys.get ⟨k, hky⟩, ?_, ?_, ?_⟩
        · apply (satisfies_samePrefix_represents_iff hleft hright k).mpr
          exact (take_eq_take_iff_pointwise xs ys k hkx.le hky.le).mp htake
        · exact (satisfies_valueAt_represents_iff hleft k _).mpr
            ⟨hkx, rfl⟩
        · exact (satisfies_valueAt_represents_iff hright k _).mpr
            ⟨hky, rfl⟩
        · exact (htoken _ _).mpr hrelation

/-- The advertised specialization to the canonical indexed sequence codes. -/
theorem satisfies_shortlexFormula_sequenceCode_iff
    {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple ZFSet.{u} parameterCount)
    (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (htoken : ∀ leftValue rightValue : ZFSet.{u},
      FOFormula.Satisfies Delta0Formula.ZFMem tokenLt
          (snoc (snoc params leftValue) rightValue) ↔
        R leftValue rightValue)
    (xs ys : List ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem (shortlexFormula tokenLt)
        (snoc (snoc (snoc params Ordinal.omega0.toZFSet)
          (sequenceCode xs)) (sequenceCode ys)) ↔
      List.Shortlex R xs ys :=
  satisfies_shortlexFormula_represents_iff tokenLt params R
    (represents_sequenceCode xs) (represents_sequenceCode ys) htoken

end Constructible.IndexedSequenceZF
end CUAdapterModule51



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.IndexedSequenceLookup -/
section CUAdapterModule52
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Lookup semantics for represented indexed sequences

The access formula checks both that the requested index is below the recorded
length and that the corresponding graph pair is present.  Thus irrelevant
extra graph elements allowed by `Represents` cannot create out-of-range
lookups, and lookup is exactly equivalent to retrieving an entry of the
represented Lean list.
-/


universe u

namespace Constructible.IndexedSequenceZF

open FiniteSequenceZF











end Constructible.IndexedSequenceZF
end CUAdapterModule52



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackTraceStepFormula -/
section CUAdapterModule53
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# One indexed transition of a rudimentary stack trace

The outer assignment layout is

`[U, varTag, appTag, empty, op0, ..., op8, program, trace, index]`.

The formula appends witnesses `token`, `input`, `succ`, and `output`.  It reads
the token and input state at `index`, verifies that `succ` is the finite
ordinal successor of `index`, reads the output state at `succ`, and applies
`stackStepFormula` to the decoded transition.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

/-! ## Fixed coordinates and renamings -/





/-- Read `[program,index,token]` in the four-witness context. -/
def traceStepProgramValueRename : Fin 3 -> Fin 20 :=
  ![(13 : Fin 20), (15 : Fin 20), (16 : Fin 20)]

/-- Read `[trace,index,input]` in the four-witness context. -/
def traceStepInputValueRename : Fin 3 -> Fin 20 :=
  ![(14 : Fin 20), (15 : Fin 20), (17 : Fin 20)]

/-- Read `[trace,succ,output]` in the four-witness context. -/
def traceStepOutputValueRename : Fin 3 -> Fin 20 :=
  ![(14 : Fin 20), (18 : Fin 20), (19 : Fin 20)]

/--
Supply the thirteen fixed stack-step parameters followed by
`[token,input,output]`.
-/
def traceStepStackStepRename : Fin 16 -> Fin 20 :=
  Fin.lastCases (19 : Fin 20)
    (fun i15 => Fin.lastCases (17 : Fin 20)
      (fun i14 => Fin.lastCases (16 : Fin 20)
        (fun i13 =>
          i13.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        i14) i15)

/-! ## Formula -/

/-- The four-witness body in context indices zero through nineteen. -/
def traceStepBody : FOFormula 20 :=
  .conj
    (FOFormula.rename traceStepProgramValueRename
      Constructible.IndexedSequenceZF.valueAtFormula)
    (.conj
      (FOFormula.rename traceStepInputValueRename
        Constructible.IndexedSequenceZF.valueAtFormula)
      (.conj
        (Delta0Formula.successorFOAt (18 : Fin 20) (15 : Fin 20))
        (.conj
          (FOFormula.rename traceStepOutputValueRename
            Constructible.IndexedSequenceZF.valueAtFormula)
          (FOFormula.rename traceStepStackStepRename stackStepFormula))))

/-- One local transition of an indexed postfix-program execution trace. -/
def traceStepFormula : FOFormula 16 :=
  .ex (.ex (.ex (.ex traceStepBody)))

/-- The intended assignment to the fixed outer context. -/
noncomputable def traceStepAssignment
    (U program trace index : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  stackStepAssignment U program trace index

theorem comp_traceStepProgramValueRename
    (U program trace index token input succ output : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
        token) input) succ) output (traceStepProgramValueRename i)) =
      ![program, index, token] := by
  funext i
  fin_cases i <;> rfl

theorem comp_traceStepInputValueRename
    (U program trace index token input succ output : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
        token) input) succ) output (traceStepInputValueRename i)) =
      ![trace, index, input] := by
  funext i
  fin_cases i <;> rfl

theorem comp_traceStepOutputValueRename
    (U program trace index token input succ output : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
        token) input) succ) output (traceStepOutputValueRename i)) =
      ![trace, succ, output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem traceStepWitnessSucc
    (U program trace index token input succ output : ZFSet.{u}) :
    snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
      token) input) succ) output (18 : Fin 20) = succ :=
  rfl

@[simp]
theorem traceStepWitnessIndex
    (U program trace index token input succ output : ZFSet.{u}) :
    snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
    token) input) succ) output (15 : Fin 20) = index :=
  rfl

set_option maxHeartbeats 1200000 in
-- The nested `snoc` assignment has sixteen coordinates; the proof below
-- reduces it by three explicit `Fin.lastCases` layers.
theorem comp_traceStepStackStepRename
    (U program trace index token input succ output : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc (traceStepAssignment U program trace index)
        token) input) succ) output (traceStepStackStepRename i)) =
      stackStepAssignment U token input output := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rfl
      · simp [traceStepAssignment, stackStepAssignment,
          traceStepStackStepRename]

/-! ## Raw semantics -/

/-- Semantic decomposition into the four constituent checks. -/
@[simp]
theorem satisfies_traceStepFormula_components
    (U program trace index : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
        (traceStepAssignment U program trace index) <->
      exists token input succ output : ZFSet.{u},
        FOFormula.Satisfies Delta0Formula.ZFMem
            Constructible.IndexedSequenceZF.valueAtFormula
            ![program, index, token] /\
        FOFormula.Satisfies Delta0Formula.ZFMem
            Constructible.IndexedSequenceZF.valueAtFormula
            ![trace, index, input] /\
        succ = insert index index /\
        FOFormula.Satisfies Delta0Formula.ZFMem
            Constructible.IndexedSequenceZF.valueAtFormula
            ![trace, succ, output] /\
        FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
          (stackStepAssignment U token input output) := by
  simp only [traceStepFormula, traceStepBody, FOFormula.Satisfies,
    FOFormula.satisfies_rename,
    Delta0Formula.satisfies_successorFOAt_ambient,
    comp_traceStepProgramValueRename,
    comp_traceStepInputValueRename,
    comp_traceStepOutputValueRename,
    traceStepWitnessSucc, traceStepWitnessIndex,
    comp_traceStepStackStepRename]



/-! ## Genuine indexed sequence codes -/





/-- The same local-step semantics for arbitrary valid sequence representations. -/
theorem satisfies_traceStepFormula_represents_iff
    (U : ZFSet.{u})
    {programCode traceCode : ZFSet.{u}}
    {program trace : List ZFSet.{u}}
    (hprogram : Constructible.IndexedSequenceZF.Represents
      programCode program)
    (htrace : Constructible.IndexedSequenceZF.Represents traceCode trace)
    (k : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
        (traceStepAssignment U programCode traceCode
          (FiniteSequenceZF.natCode k)) ↔
      ∃ hp : k < program.length,
        ∃ hi : k < trace.length,
          ∃ ho : k + 1 < trace.length,
            FOFormula.Satisfies Delta0Formula.ZFMem stackStepFormula
              (stackStepAssignment U
                (program.get ⟨k, hp⟩)
                (trace.get ⟨k, hi⟩)
                (trace.get ⟨k + 1, ho⟩)) := by
  rw [satisfies_traceStepFormula_components]
  constructor
  · rintro ⟨token, input, succ, output,
      htoken, hinput, hsucc, houtput, hstep⟩
    rcases
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          hprogram k token).mp htoken with
      ⟨hp, htoken⟩
    rcases
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          htrace k input).mp hinput with
      ⟨hi, hinput⟩
    have hsuccCode : succ = FiniteSequenceZF.natCode (k + 1) :=
      hsucc.trans (FiniteSequenceZF.natCode_succ_eq_insert k).symm
    rw [hsuccCode] at houtput
    rcases
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          htrace (k + 1) output).mp houtput with
      ⟨ho, houtput⟩
    refine ⟨hp, hi, ho, ?_⟩
    subst token
    subst input
    subst output
    exact hstep
  · rintro ⟨hp, hi, ho, hstep⟩
    refine ⟨program.get ⟨k, hp⟩, trace.get ⟨k, hi⟩,
      FiniteSequenceZF.natCode (k + 1), trace.get ⟨k + 1, ho⟩,
      ?_, ?_, ?_, ?_, hstep⟩
    · exact
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          hprogram k _).mpr ⟨hp, rfl⟩
    · exact
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          htrace k _).mpr ⟨hi, rfl⟩
    · exact FiniteSequenceZF.natCode_succ_eq_insert k
    · exact
        (Constructible.IndexedSequenceZF.satisfies_valueAt_represents_iff
          htrace (k + 1) _).mpr ⟨ho, rfl⟩

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule53



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackProgramEvalFormula -/
section CUAdapterModule54
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# A fixed first-order evaluator for postfix rudimentary programs

Evaluation is certified by an internally quantified finite sequence of stack
states.  Both program and trace satisfy the indexed-sequence validity
predicate; their recorded lengths differ by one; the first trace state is the
empty stack; the final state is the singleton result stack; and every program
index satisfies `traceStepFormula`.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

noncomputable section

open Constructible.IndexedSequenceZF

/-! ## Fixed layout and renamings -/

/-
The free layout is

`[U,varTag,appTag,empty,op0,...,op8,omega,program,result]`.

Thus the three final indices are `13,14,15`.  The evaluator then quantifies
`trace, programLength, traceLength, finalStack`, at indices `16,...,19`.
-/

/-- The omega coordinate in the program-evaluation layout. -/
def evalOmegaIndex : Fin 16 := 13
/-- The program coordinate in the program-evaluation layout. -/
def evalProgramIndex : Fin 16 := 14


/-- Select the omega and program coordinates for program validity. -/
def evalProgramValidityRename : Fin 2 → Fin 16 :=
  ![evalOmegaIndex, evalProgramIndex]

/-- Select the omega and trace coordinates for trace validity. -/
def evalTraceValidityRename : Fin 2 → Fin 17 :=
  ![(13 : Fin 17), (16 : Fin 17)]

/-- Select the program and its length coordinate. -/
def evalProgramLengthRename : Fin 2 → Fin 20 :=
  ![(14 : Fin 20), (17 : Fin 20)]

/-- Select the trace and its length coordinate. -/
def evalTraceLengthRename : Fin 2 → Fin 20 :=
  ![(16 : Fin 20), (18 : Fin 20)]

/-- Select the coordinates describing the initial stack value. -/
def evalInitialValueRename : Fin 3 → Fin 20 :=
  Fin.cases (16 : Fin 20)
    (fun j => Fin.cases (3 : Fin 20) (fun _ => (3 : Fin 20)) j)

/-- Select the coordinates describing the final stack value. -/
def evalFinalValueRename : Fin 3 → Fin 20 :=
  ![(16 : Fin 20), (17 : Fin 20), (19 : Fin 20)]

/-- Embed the local trace-step layout into the evaluator's bounded-index body. -/
def evalTraceStepRename : Fin 16 → Fin 21 :=
  Fin.lastCases (20 : Fin 21)
    (fun i15 => Fin.lastCases (16 : Fin 21)
      (fun i14 => Fin.lastCases (14 : Fin 21)
        (fun i13 =>
          i13.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
        i14) i15)

/-! ## Formula -/

/-- The body after trace, both lengths, and the final stack have been chosen. -/
def stackProgramEvalCore : FOFormula 20 :=
  .conj
    (FOFormula.rename evalProgramLengthRename hasLengthFormula)
    (.conj
      (FOFormula.rename evalTraceLengthRename hasLengthFormula)
      (.conj
        (Delta0Formula.successorFOAt (18 : Fin 20) (17 : Fin 20))
        (.conj
          (FOFormula.rename evalInitialValueRename valueAtFormula)
          (.conj
            (FOFormula.rename evalFinalValueRename valueAtFormula)
            (.conj
              (Delta0Formula.kuratowskiPairEqAt
                (19 : Fin 20) (15 : Fin 20) (3 : Fin 20)).toFO
              (FOFormula.boundedAll (17 : Fin 20)
                (FOFormula.rename evalTraceStepRename
                  traceStepFormula)))))))

/-- The complete validity-guarded finite-trace evaluator. -/
def stackProgramEvalFormula : FOFormula 16 :=
  .conj
    (FOFormula.rename evalProgramValidityRename sequenceValidityFormula)
    (.ex
      (.conj
        (FOFormula.rename evalTraceValidityRename sequenceValidityFormula)
        (.ex (.ex (.ex stackProgramEvalCore)))))

/-- Intended assignment to the evaluator's fixed free-variable context. -/
def stackProgramEvalAssignment
    (U program result : ZFSet.{u}) : Tuple ZFSet.{u} 16 :=
  snoc (snoc (snoc (stackStepPrefixAssignment U)
    Ordinal.omega0.toZFSet) program) result

@[simp]
theorem stackProgramEvalAssignment_empty
    (U program result : ZFSet.{u}) :
    stackProgramEvalAssignment U program result (3 : Fin 16) = ∅ :=
  rfl

@[simp]
theorem stackProgramEvalAssignment_result
    (U program result : ZFSet.{u}) :
    stackProgramEvalAssignment U program result (15 : Fin 16) = result :=
  rfl

/-! ## Assignment computations -/

/-- Satisfaction depends only on the pointwise values of an assignment. -/
 theorem satisfies_congr_assignment {A : Type u}
    (E : A → A → Prop) {n : Nat} (phi : FOFormula n)
    (s t : Tuple A n) (h : ∀ i, s i = t i) :
    FOFormula.Satisfies E phi s ↔ FOFormula.Satisfies E phi t := by
  induction phi with
  | mem i j =>
      change E (s i) (s j) ↔ E (t i) (t j)
      rw [h i, h j]
  | eq i j =>
      change s i = s j ↔ t i = t j
      rw [h i, h j]
  | neg phi ih =>
      exact not_congr (ih s t h)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi s t h) (ihPsi s t h)
  | ex phi ih =>
      simp only [FOFormula.Satisfies]
      apply exists_congr
      intro x
      apply ih
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [snoc_last]
      · simpa only [snoc_castSucc] using h j

 abbrev evalCoreAssignment
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    Tuple ZFSet.{u} 20 :=
  snoc (snoc (snoc (snoc
    (stackProgramEvalAssignment U program result) trace)
    programLength) traceLength) finalStack

@[simp]
 theorem evalCoreAssignment_trace
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (16 : Fin 20) = trace := by
  rfl

@[simp]
 theorem evalCoreAssignment_programLength
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (17 : Fin 20) = programLength := by
  rfl

@[simp]
 theorem evalCoreAssignment_traceLength
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (18 : Fin 20) = traceLength := by
  rfl

@[simp]
 theorem evalCoreAssignment_finalStack
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (19 : Fin 20) = finalStack := by
  rfl

 theorem evalCoreAssignment_base
    (U program result trace programLength traceLength finalStack : ZFSet.{u})
    (i : Fin 16) :
    evalCoreAssignment U program result trace programLength traceLength
        finalStack i.castSucc.castSucc.castSucc.castSucc =
      stackProgramEvalAssignment U program result i := by
  simp only [evalCoreAssignment, snoc_castSucc]

@[simp]
 theorem evalCoreAssignment_empty
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (3 : Fin 20) = ∅ := by
  change evalCoreAssignment U program result trace programLength traceLength
    finalStack (3 : Fin 16).castSucc.castSucc.castSucc.castSucc = ∅
  rw [evalCoreAssignment_base, stackProgramEvalAssignment_empty]

@[simp]
 theorem evalCoreAssignment_result
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    evalCoreAssignment U program result trace programLength traceLength
      finalStack (15 : Fin 20) = result := by
  change evalCoreAssignment U program result trace programLength traceLength
    finalStack (15 : Fin 16).castSucc.castSucc.castSucc.castSucc = result
  rw [evalCoreAssignment_base, stackProgramEvalAssignment_result]

theorem comp_evalProgramValidityRename
    (U program result : ZFSet.{u}) :
    (fun i => stackProgramEvalAssignment U program result
      (evalProgramValidityRename i)) =
      ![Ordinal.omega0.toZFSet, program] := by
  funext i
  fin_cases i <;> rfl

theorem comp_evalTraceValidityRename
    (U program result trace : ZFSet.{u}) :
    (fun i => snoc (stackProgramEvalAssignment U program result) trace
      (evalTraceValidityRename i)) =
      ![Ordinal.omega0.toZFSet, trace] := by
  funext i
  fin_cases i <;> rfl

theorem comp_evalProgramLengthRename
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U program result) trace)
        programLength) traceLength) finalStack
        (evalProgramLengthRename i)) =
      ![program, programLength] := by
  funext i
  fin_cases i <;> rfl

theorem comp_evalTraceLengthRename
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U program result) trace)
        programLength) traceLength) finalStack
        (evalTraceLengthRename i)) =
      ![trace, traceLength] := by
  funext i
  fin_cases i <;> rfl

 theorem satisfies_evalInitialValueRename
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        (fun i => evalCoreAssignment U program result trace programLength
          traceLength finalStack (evalInitialValueRename i)) ↔
      FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![trace, (∅ : ZFSet.{u}), ∅] := by
  apply satisfies_congr_assignment
  intro i
  fin_cases i
  · change evalCoreAssignment U program result trace programLength traceLength
      finalStack (16 : Fin 20) = trace
    exact evalCoreAssignment_trace U program result trace programLength
      traceLength finalStack
  · change evalCoreAssignment U program result trace programLength traceLength
      finalStack (3 : Fin 20) = ∅
    exact evalCoreAssignment_empty U program result trace programLength
      traceLength finalStack
  · change evalCoreAssignment U program result trace programLength traceLength
      finalStack (3 : Fin 20) = ∅
    exact evalCoreAssignment_empty U program result trace programLength
      traceLength finalStack

theorem comp_evalFinalValueRename
    (U program result trace programLength traceLength finalStack : ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U program result) trace)
        programLength) traceLength) finalStack
        (evalFinalValueRename i)) =
      ![trace, programLength, finalStack] := by
  funext i
  fin_cases i <;> rfl

theorem comp_evalTraceStepRename
    (U program result trace programLength traceLength finalStack index :
      ZFSet.{u}) :
    (fun i =>
      snoc (snoc (snoc (snoc (snoc
        (stackProgramEvalAssignment U program result) trace)
        programLength) traceLength) finalStack) index
        (evalTraceStepRename i)) =
      traceStepAssignment U program trace index := by
  funext i
  refine Fin.lastCases ?_ (fun i15 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i14 => ?_) i15
    · rfl
    · refine Fin.lastCases ?_ (fun i13 => ?_) i14
      · rfl
      · simp [stackProgramEvalAssignment, traceStepAssignment,
          stackStepAssignment, evalTraceStepRename]

/-! ## Raw semantic normal form -/

/-- The evaluator decomposes into validity, length, endpoint, and local-step checks. -/
@[simp]
theorem satisfies_stackProgramEvalFormula
    (U program result : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem stackProgramEvalFormula
        (stackProgramEvalAssignment U program result) ↔
      FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
          ![Ordinal.omega0.toZFSet, program] ∧
        ∃ trace : ZFSet.{u},
          FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
              ![Ordinal.omega0.toZFSet, trace] ∧
            ∃ programLength traceLength finalStack : ZFSet.{u},
              FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
                  ![program, programLength] ∧
                FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
                  ![trace, traceLength] ∧
                traceLength = insert programLength programLength ∧
                FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
                  ![trace, (∅ : ZFSet.{u}), ∅] ∧
                FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
                  ![trace, programLength, finalStack] ∧
                finalStack = ZFSet.pair result ∅ ∧
                ∀ index : ZFSet.{u}, index ∈ programLength →
                  FOFormula.Satisfies Delta0Formula.ZFMem traceStepFormula
                    (traceStepAssignment U program trace index) := by
  simp only [stackProgramEvalFormula, stackProgramEvalCore,
    FOFormula.Satisfies, FOFormula.satisfies_rename,
    FOFormula.satisfies_boundedAll,
    Delta0Formula.satisfies_successorFOAt_ambient,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    comp_evalProgramValidityRename, comp_evalTraceValidityRename,
    comp_evalProgramLengthRename, comp_evalTraceLengthRename,
    satisfies_evalInitialValueRename, comp_evalFinalValueRename,
    comp_evalTraceStepRename, evalCoreAssignment_programLength,
    evalCoreAssignment_traceLength, evalCoreAssignment_finalStack,
    evalCoreAssignment_empty, evalCoreAssignment_result]

end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule54



/- Original module: ConstructibleUniverse.SetTheory.ZFC.Constructible.RudimentaryStackTraceEndpoints -/
section CUAdapterModule55
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/

/-!
# Endpoint semantics of raw formula-certified stack traces

For a genuine typed program, existence of a raw formula chain from the empty
stack code to the singleton output-stack code is exactly successful execution
of that program.  Soundness uses raw-chain decoding and injectivity of both
token and stack-state encodings; completeness encodes the canonical execution
trace of a successful run.
-/


universe u

namespace Constructible.Godel.RudimentaryTerm

open FiniteSequenceZF

noncomputable section

/--
A genuine program evaluates from the empty stack to `[z]` exactly when it has
a raw formula-certified state-code chain with those endpoints.
-/
theorem exists_rawStackFormulaTrace_iff_run
    (U : ZFSet.{u})
    (program : List
      (StackToken (Option (Constructible.ZFCarrier U))))
    (z : ZFSet.{u}) :
    (∃ rawStates : List ZFSet.{u},
      RawStackFormulaChain U (encodedStackProgram U program) rawStates ∧
        rawStates.head? = some (listCode []) ∧
        rawStates.getLast? = some (listCode [z])) ↔
      runStackProgram (rudimentaryGenerator U) program [] = some [z] := by
  constructor
  · rintro ⟨rawStates, hchain, hhead, hlast⟩
    rcases exists_executionTrace_decoding_of_rawStackFormulaChain
        U (encodedStackProgram U program) rawStates hhead hchain with
      ⟨decodedProgram, states, hprogramCodes, hstateCodes, htrace⟩
    have hprogramMap :
        program.map (stackTokenZFCode U) =
          decodedProgram.map (stackTokenZFCode U) := by
      simpa only [encodedStackProgram] using hprogramCodes
    have hprogram : decodedProgram = program :=
      ((stackTokenZFCode_injective U).list_map hprogramMap).symm
    subst decodedProgram
    rw [hstateCodes] at hhead hlast
    have hheadMapped :
        states.head?.map listCode = some (listCode []) := by
      simpa only [List.head?_map] using hhead
    have hheadStates : states.head? = some [] := by
      cases hstateHead : states.head? with
      | none =>
          simp only [hstateHead, Option.map_none] at hheadMapped
          cases hheadMapped
      | some first =>
          simp only [hstateHead, Option.map_some,
            Option.some.injEq] at hheadMapped
          have hfirst : first = [] :=
            listCode_injective hheadMapped
          exact congrArg some hfirst
    have hlastMapped :
        states.getLast?.map listCode = some (listCode [z]) := by
      simpa only [List.getLast?_map] using hlast
    have hlastStates : states.getLast? = some [z] := by
      cases hstateLast : states.getLast? with
      | none =>
          simp only [hstateLast, Option.map_none] at hlastMapped
          cases hlastMapped
      | some last =>
          simp only [hstateLast, Option.map_some,
            Option.some.injEq] at hlastMapped
          have hlastStack : last = [z] :=
            listCode_injective hlastMapped
          exact congrArg some hlastStack
    exact run_of_executionTrace (rudimentaryGenerator U)
      program states [] [z] htrace hheadStates hlastStates
  · intro hrun
    rcases exists_executionTrace_of_run
        (rudimentaryGenerator U) program [] [z] hrun with
      ⟨states, htrace, hhead, hlast⟩
    refine ⟨encodedStackStates states,
      htrace.encoded_rawStackFormulaChain, ?_, ?_⟩
    · simp only [encodedStackStates, List.head?_map,
        hhead, Option.map_some]
    · simp only [encodedStackStates, List.getLast?_map,
        hlast, Option.map_some]

end

end Constructible.Godel.RudimentaryTerm
end CUAdapterModule55


