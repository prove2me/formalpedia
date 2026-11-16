-- Prove2me | Definitions.Def_EditApproxScheme_15
-- name    : EditApproxScheme_15
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:50:52.89619+00:00
-- url     : https://prove2.me/theorems/ffb229dd-e968-4579-9497-3ab8ddd33338
-- title:
--   Edit-distance approximation scheme, part 15 of 20: query programs
-- statement:
--   This is **part 15 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains the query programs: physical scalar group queries and online reads, family group reads, physical children, restricted program bodies, charged reads and seeds, warmup programs, ranked normalization, the physical family program, the coarse seed table, and the family kernel work and coarse copy storage. It also proves 24 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L8720-L9444 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 15 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_14

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable (M J N n exponent F Q R B : ℕ)

open Finset

open MeasureTheory ProbabilityTheory

theorem _root_.OAI.EditApproximation.Lemmas.log_two_add_one_eq_size (N : ℕ) (hN : LT.lt.{0} 0 N) :
    Nat.log 2 N + 1 = Nat.size N := by
  apply Nat.le_antisymm
  · have h := Nat.pow_log_le_self 2 hN.ne'
    have hlt : Nat.log 2 N < Nat.size N := Nat.lt_size.mpr h
    omega
  · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N)

theorem _root_.OAI.EditApproximation.Lemmas.dyadicScalesWithWork_value (N : ℕ) :
    (OAI.EditApproximation.dyadicScalesWithWork N).1 = OAI.EditApproximation.dyadicScales N := by
  have hcount : max 1 N.bits.length = Nat.log 2 N + 1 := by
    by_cases hz : N = 0
    · subst N
      decide
    · have h := OAI.EditApproximation.Lemmas.log_two_add_one_eq_size N (Nat.pos_of_ne_zero hz)
      have hp := Nat.size_pos.mpr (Nat.pos_of_ne_zero hz)
      rw [Nat.size_eq_bits_len, max_eq_right hp, h]
  simp only [OAI.EditApproximation.dyadicScalesWithWork, OAI.EditApproximation.Lemmas.arithmeticMapWithWork_value, OAI.EditApproximation.Lemmas.powerTwoWord_value, hcount,
    OAI.EditApproximation.dyadicScales]

theorem _root_.OAI.EditApproximation.Lemmas.queryNaturalIndexWithWork_value (a : ℕ) (xs : List.{0} ℕ) :
    (OAI.EditApproximation.queryNaturalIndexWithWork a xs).1 = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [OAI.EditApproximation.queryNaturalIndexWithWork]
    by_cases hab : a = b
    · subst b
      rw [ite_eq_left ((OAI.EditApproximation.Lemmas.naturalEqualWithWork_value a a).mpr rfl)]
      simp
    · rw [ite_eq_right (fun h => hab ((OAI.EditApproximation.Lemmas.naturalEqualWithWork_value a b).mp h))]
      simp only [ih, List.idxOf_cons, beq_iff_eq]
      rw [beq_eq_false_iff_ne.mpr (Ne.symm hab), cond_false]

theorem _root_.OAI.EditApproximation.Lemmas.queryScaleDispatchWithWork_value (N : ℕ) (b : ℕ) :
    (OAI.EditApproximation.queryScaleDispatchWithWork N b).1 = (OAI.EditApproximation.dyadicScales N).idxOf b := by
  simp only [OAI.EditApproximation.queryScaleDispatchWithWork, OAI.EditApproximation.Lemmas.queryNaturalIndexWithWork_value, OAI.EditApproximation.Lemmas.dyadicScalesWithWork_value]

theorem _root_.OAI.EditApproximation.Lemmas.queryScalePresentWithWork_value (N : ℕ) (b : ℕ) :
    (OAI.EditApproximation.queryScalePresentWithWork N b).1 = true ↔ b ∈ OAI.EditApproximation.dyadicScales N := by
  simp only [OAI.EditApproximation.queryScalePresentWithWork, decide_eq_true_eq, OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt,
    OAI.EditApproximation.Lemmas.queryScaleDispatchWithWork_value]
  have hl : (OAI.EditApproximation.dyadicScales N).length = max 1 N.bits.length := by
    rw [← OAI.EditApproximation.Lemmas.dyadicScalesWithWork_value N]
    (simp only [OAI.EditApproximation.dyadicScalesWithWork, OAI.EditApproximation.Lemmas.arithmeticMapWithWork_value, List.length_map, List.length_range])
  rw [← hl]
  exact List.idxOf_lt_length_iff

theorem _root_.OAI.EditApproximation.Lemmas.queryCellValidWithWork_value (n : ℕ) (exponent : ℕ) (cell : Prod.{0, 0} ℕ ℕ) :
    (OAI.EditApproximation.queryCellValidWithWork n exponent cell).1 = true ↔
      cell.1 ≤ n * 2 ^ exponent ∧ cell.2 ≤ n * 2 ^ exponent := by
  simp only [OAI.EditApproximation.queryCellValidWithWork, Bool.and_eq_true, OAI.EditApproximation.Lemmas.wordLEWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits,
    OAI.EditApproximation.Lemmas.binaryNaturalMulWithWork_value, OAI.EditApproximation.Lemmas.powerTwoWord_value]

def queryPhysicalScalarGroupQueries (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
    (b : ℕ) (cell : ℕ × ℕ) : OAI.EditApproximation.BitPhysicalGroupQueries M J N n exponent F Q R B b := by
  exact
    if hb : (OAI.EditApproximation.queryScalePresentWithWork N b).1 = true then
      if hc : (OAI.EditApproximation.queryCellValidWithWork n exponent cell).1 = true then
        let key : OAI.EditApproximation.PhysicalLocalGroupKey M J N n exponent :=
          (node, OAI.EditApproximation.physicalScaleIndex N b ((OAI.EditApproximation.Lemmas.queryScalePresentWithWork_value N b).mp hb),
            ⟨cell.1, Nat.lt_succ_of_le ((OAI.EditApproximation.Lemmas.queryCellValidWithWork_value n exponent cell).mp hc).1⟩,
            ⟨cell.2, Nat.lt_succ_of_le ((OAI.EditApproximation.Lemmas.queryCellValidWithWork_value n exponent cell).mp hc).2⟩)
        Eq.mp (congrArg (OAI.EditApproximation.BitPhysicalGroupQueries M J N n exponent F Q R B)
          (OAI.EditApproximation.Lemmas.physicalScaleIndex_get N b ((OAI.EditApproximation.Lemmas.queryScalePresentWithWork_value N b).mp hb)))
            (OAI.EditApproximation.queryPhysicalScalarGroupQueriesAt M J N n exponent F Q R B key time)
      else fun _ _ => .done (OAI.EditApproximation.BinaryFraction.nat 0)
    else fun _ _ => .done (OAI.EditApproximation.BinaryFraction.nat 0)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable (M J N n exponent F Q R B : ℕ)

def queryPhysicalScalarGroupRead (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
    (key : OAI.EditApproximation.GroupScalarKey M F Q) : OAI.EditApproximation.BitQuery (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction :=
  .charge ((OAI.EditApproximation.queryScalePresentWithWork N key.1.1).2 +
    (OAI.EditApproximation.queryCellValidWithWork n exponent key.1.2).2 + 2)
    (OAI.EditApproximation.queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time
      key.1.1 key.1.2 key.2.1 key.2.2)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable (M J N n exponent F Q R B : ℕ)

open Finset

theorem _root_.OAI.EditApproximation.Lemmas.queryRangeValidWithWork_value (B : ℕ) (range : ℕ) :
    (OAI.EditApproximation.queryRangeValidWithWork B range).1 = true ↔ 0 < range ∧ range ≤ B := by
  simp only [OAI.EditApproximation.queryRangeValidWithWork, Bool.and_eq_true, decide_eq_true_eq,
    OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt, OAI.EditApproximation.Lemmas.wordLEWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits]

def queryPhysicalScalarOnlineRead (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × OAI.EditApproximation.TargetInterval n) (range : ℕ) :
    OAI.EditApproximation.BitQuery (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction := by
  exact
    .charge ((OAI.EditApproximation.queryScalePresentWithWork N key.1).2 + (OAI.EditApproximation.queryRangeValidWithWork B range).2 + 2)
      (if hb : (OAI.EditApproximation.queryScalePresentWithWork N key.1).1 = true then
        if hr : (OAI.EditApproximation.queryRangeValidWithWork B range).1 = true then
          OAI.EditApproximation.queryPhysicalScalarRead M J N n exponent F Q R B
            ⟨.inl ((node, OAI.EditApproximation.physicalScaleIndex N key.1 ((OAI.EditApproximation.Lemmas.queryScalePresentWithWork_value N key.1).mp hb), key.2),
              OAI.EditApproximation.positiveDrawRangeOfLE B range ((OAI.EditApproximation.Lemmas.queryRangeValidWithWork_value B range).mp hr).1
                ((OAI.EditApproximation.Lemmas.queryRangeValidWithWork_value B range).mp hr).2), time⟩
        else .done (OAI.EditApproximation.BinaryFraction.nat 0)
      else .done (OAI.EditApproximation.BinaryFraction.nat 0))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {α : Type u_1} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies pass copy : ℕ)

def queryFamilyTagWithWork
    (scalar : OAI.EditApproximation.PhysicalScalarKey M J N target.length exponent F Q R (OAI.EditApproximation.localOnlineMassBound M P H)) :
    OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies × ℕ :=
  let p := OAI.EditApproximation.queryFinOfNatWithWork (passes + 1) pass (Nat.succ_pos _)
  let c := OAI.EditApproximation.queryFinOfNatWithWork (copies + 1) copy (Nat.succ_pos _)
  let key := (p.1, c.1, scalar)
  (key, p.2 + c.2 + (OAI.EditApproximation.physicalFamilyCodeWithWork target N P F exponent H Q passes copies key).2 + 1)

def queryFamilyGroupRead (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
    (key : OAI.EditApproximation.GroupScalarKey M F Q) :
    OAI.EditApproximation.BitQuery (OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) OAI.EditApproximation.BinaryFraction :=
  OAI.EditApproximation.BitQuery.mapKeysWithWork
    (OAI.EditApproximation.queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy)
    (OAI.EditApproximation.queryPhysicalScalarGroupRead M J N target.length exponent F Q R (OAI.EditApproximation.localOnlineMassBound M P H)
      node time key)

def queryFamilyOnlineRead (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × OAI.EditApproximation.TargetInterval target.length) (range : ℕ) :
    OAI.EditApproximation.BitQuery (OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) OAI.EditApproximation.BinaryFraction :=
  OAI.EditApproximation.BitQuery.mapKeysWithWork
    (OAI.EditApproximation.queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy)
    (OAI.EditApproximation.queryPhysicalScalarOnlineRead M J N target.length exponent F Q R (OAI.EditApproximation.localOnlineMassBound M P H)
      node time key range)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {σ : Type u_1} {M J n : ℕ} (passes copies T S : ℕ) (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})

abbrev QueryPhysicalChild := Sum σ {child : OAI.EditApproximation.PhysicalTableRequest M J n //
  child.combinedRank T S < parent.val.combinedRank T S}

def querySupportedChildWithWork (key : OAI.EditApproximation.QueryPhysicalChild (σ := σ) passes copies T S parent) : Bool × ℕ :=
  match key with
  | .inl _ => (true, 1)
  | .inr child => OAI.EditApproximation.queryPhysicalBoundedWithWork passes copies T S child.val

theorem _root_.OAI.EditApproximation.Lemmas.queryPhysicalBoundedWithWork_value {M : ℕ} {J : ℕ} {n : ℕ} (passes : ℕ) (copies : ℕ) (T : ℕ) (S : ℕ) (request : OAI.EditApproximation.PhysicalTableRequest M J n) :
    (OAI.EditApproximation.queryPhysicalBoundedWithWork passes copies T S request).1 = true ↔
      request.Bounded passes copies T S := by
  simp only [OAI.EditApproximation.queryPhysicalBoundedWithWork, Bool.and_eq_true, decide_eq_true_eq,
    OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt, OAI.EditApproximation.Lemmas.wordLEWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits,
    OAI.EditApproximation.Lemmas.binaryNaturalAddWithWork_value, OAI.EditApproximation.PhysicalTableRequest.Bounded]
  tauto

theorem _root_.OAI.EditApproximation.Lemmas.querySupportedChildWithWork_value {σ : Type u_1} {M : ℕ} {J : ℕ} {n : ℕ} (passes : ℕ) (copies : ℕ) (T : ℕ) (S : ℕ) (parent : Subtype.{1} fun r => OAI.EditApproximation.PhysicalTableRequest.Bounded (M := M) (J := J) (ny := n) passes copies T S r) (key : OAI.EditApproximation.QueryPhysicalChild.{u_1} (σ := σ) passes copies T S parent) :
    (OAI.EditApproximation.querySupportedChildWithWork passes copies T S parent key).1 = true ↔
      OAI.EditApproximation.SourceRanked.supportedChild (OAI.EditApproximation.PhysicalTableRequest.combinedRank T S)
        (OAI.EditApproximation.PhysicalTableRequest.Bounded passes copies T S) parent.val key := by
  cases key with
  | inl source => exact iff_of_true rfl trivial
  | inr child => exact OAI.EditApproximation.Lemmas.queryPhysicalBoundedWithWork_value passes copies T S child.val

def queryRestrictPhysicalBody (program : OAI.EditApproximation.BitQuery (OAI.EditApproximation.QueryPhysicalChild (σ := σ) passes copies T S parent) OAI.EditApproximation.BinaryFraction) :
    OAI.EditApproximation.BitQuery (Sum σ {child : {r : OAI.EditApproximation.PhysicalTableRequest M J n // r.Bounded passes copies T S} //
      child.val.combinedRank T S < parent.val.combinedRank T S}) OAI.EditApproximation.BinaryFraction := by
  exact
    OAI.EditApproximation.BitQuery.mapKeysWithWork
      (fun key => (OAI.EditApproximation.SourceRanked.supportedChildMap (OAI.EditApproximation.PhysicalTableRequest.combinedRank T S)
        (OAI.EditApproximation.PhysicalTableRequest.Bounded passes copies T S) parent key, 1))
      (OAI.EditApproximation.BitQuery.restrictWithWork
        (OAI.EditApproximation.SourceRanked.supportedChild (OAI.EditApproximation.PhysicalTableRequest.combinedRank T S)
          (OAI.EditApproximation.PhysicalTableRequest.Bounded passes copies T S) parent.val)
        (OAI.EditApproximation.querySupportedChildWithWork passes copies T S parent)
        (OAI.EditApproximation.Lemmas.querySupportedChildWithWork_value passes copies T S parent) program)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_1} {α : Type*} (source target : List α) (N P F : ℕ) (A a : BinaryFraction) (reader : TargetInterval target.length → BitQuery ι BinaryFraction) (q : TargetInterval target.length)

def queryInitialConeProgramAt {n : ℕ} (sourceLength N P F : ℕ) (A a : OAI.EditApproximation.BinaryFraction)
    (reader : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n) :
    OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction :=
  (reader q).bind fun value =>
    (OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork N P A value q)).bind fun keys =>
      OAI.EditApproximation.BitQuery.collect reader keys fun words =>
        OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.cachedInitialProgramReadWithWork sourceLength N P F A a
          (OAI.EditApproximation.BinaryFraction.queryInitialSeedReadWithWork value q keys words) q)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J n passes copies T S : ℕ} (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})

def queryChargedRead
    (key : {child : OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (.inr parent)}) :
    OAI.EditApproximation.BitQuery {child : OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (.inr parent)} OAI.EditApproximation.BinaryFraction :=
  .charge ((OAI.EditApproximation.chargedPhysicalCodeWithWork key.val).2 + 1) (.read key .done)

def queryChargedPreviousRead (hp : 0 < parent.val.pass) (q : OAI.EditApproximation.TargetInterval n) (copy : Fin copies) :
    OAI.EditApproximation.BitQuery {child : OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (.inr parent)} OAI.EditApproximation.BinaryFraction := by
  exact
    OAI.EditApproximation.queryChargedRead parent ⟨.inr (OAI.EditApproximation.chargedPreviousPass parent q copy), by
      apply OAI.EditApproximation.Lemmas.table_rank_lt
      apply OAI.EditApproximation.Lemmas.combinedRank_lt_of_progress T S parent.val _
      exact Or.inr ⟨(OAI.EditApproximation.Lemmas.previousPassRequest_progress T S copy.val parent.val hp q).1.le,
        (OAI.EditApproximation.Lemmas.previousPassRequest_progress T S copy.val parent.val hp q).2⟩⟩

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J n passes copies T S : ℕ} (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})

open Finset

def queryChargedSeedAt (N : ℕ) (multiplier : ℕ → ℕ) (q : OAI.EditApproximation.TargetInterval n) :
    OAI.EditApproximation.BitQuery {child : OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (.inr parent)} OAI.EditApproximation.BinaryFraction := by
  exact
    .charge ((OAI.EditApproximation.naturalEqualWithWork parent.val.pass 0).2 + 1)
      (if hp : (OAI.EditApproximation.naturalEqualWithWork parent.val.pass 0).1 = true then
        OAI.EditApproximation.queryChargedRead parent ⟨.inl (parent.val.node, q), OAI.EditApproximation.Lemmas.coarse_rank_lt _ parent rfl⟩
      else .charge (copies + 1)
        (OAI.EditApproximation.BitQuery.collect (OAI.EditApproximation.queryChargedPreviousRead parent
          (Nat.pos_of_ne_zero (fun h => hp ((OAI.EditApproximation.Lemmas.naturalEqualWithWork_value _ _).mpr h))) q)
          (List.finRange copies) fun words => OAI.EditApproximation.BitQuery.compute
            (OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork N (multiplier (parent.val.pass - 1)) words)))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable (source target : List ℕ) {M J passes copies T S : ℕ} (N P F : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ) (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S}) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ) (q : TargetInterval target.length)

def queryPhysicalInitial :
    OAI.EditApproximation.BitQuery {child : OAI.EditApproximation.ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (.inr parent)} OAI.EditApproximation.BinaryFraction :=
  let interval := OAI.EditApproximation.physicalSourceInterval source.length parent.val.node
  let length := OAI.EditApproximation.saturatingSubtractWithWork interval.hi interval.lo
  let test := OAI.EditApproximation.wordLEWithWork length.1 [true]
  .charge (length.2 + test.2 + 2)
    (if test.1 then
      OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.queryIndexedSliceWithWork source interval target.length q
        occurrence symbolBits positionBits)
    else OAI.EditApproximation.queryInitialConeProgramAt (OAI.EditApproximation.bitWordValue length.1) N P F A a
      (OAI.EditApproximation.queryChargedSeedAt parent N multiplier) q)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_1} {nx ny M : ℕ} (parent : TargetInterval nx) (N P F : ℕ) (a : BinaryFraction) (initialRead : TargetInterval ny → BitQuery ι BinaryFraction) (childRead : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction) (q : TargetInterval ny)

def queryWarmupProgram : OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction :=
  (initialRead q).bind fun value =>
    (OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork N P F a value q)).bind fun centers =>
      OAI.EditApproximation.BitQuery.collect initialRead centers fun words =>
        let initial := OAI.EditApproximation.BinaryFraction.queryOverrideParentReadWithWork value q centers words
        (OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork M parent N P F a initial q)).bind
          fun inputs => OAI.EditApproximation.BitQuery.collect childRead inputs fun childWords =>
            OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.localWarmupReadKernelWithWork parent N P F a initial
              (fun input => OAI.EditApproximation.BinaryFraction.queryChildReadWithWork inputs childWords input.1 input.2) q)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J ny passes copies T S : ℕ} (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S}) (hbelow : parent.val.node.1.val < J) (hindex : 0 < parent.val.index) (input : Fin M × TargetInterval ny)

def queryChargedWarmupChild :
    OAI.EditApproximation.BitQuery {child : OAI.EditApproximation.ChargedPhysicalRequest M J ny passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (.inr parent)} OAI.EditApproximation.BinaryFraction := by
  exact
    OAI.EditApproximation.queryChargedRead parent ⟨.inr ⟨OAI.EditApproximation.PhysicalTableRequest.warmup parent.val.pass parent.val.copy
        (OAI.EditApproximation.physicalChild parent.val.node hbelow input.1) (parent.val.index - 1) input.2,
        parent.property.1, parent.property.2.1,
        (Nat.sub_le _ _).trans parent.property.2.2⟩, by
      apply OAI.EditApproximation.Lemmas.table_rank_lt
      exact OAI.EditApproximation.Lemmas.combinedRank_warmup_child parent.val.pass parent.val.copy T S
        parent.val.index parent.val.node hbelow input.1 parent.val.state input.2 hindex⟩

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable (source target : List ℕ) {M J passes copies T S : ℕ} (N P F : ℕ) (A a : BinaryFraction) (multiplier : ℕ → ℕ) (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S}) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)

open Finset

def queryChargedWarmup :
    OAI.EditApproximation.BitQuery {child : OAI.EditApproximation.ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (.inr parent)} OAI.EditApproximation.BinaryFraction := by
  exact
    .charge ((OAI.EditApproximation.naturalEqualWithWork parent.val.index 0).2 + 1)
      (if hz : (OAI.EditApproximation.naturalEqualWithWork parent.val.index 0).1 = true then
        OAI.EditApproximation.queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits
          parent.val.state
      else .charge ((OAI.EditApproximation.binaryNaturalCompareWithWork parent.val.node.1.val J).2 + 1)
        (if hb : (OAI.EditApproximation.binaryNaturalCompareWithWork parent.val.node.1.val J).1 = .lt then
          let interval := OAI.EditApproximation.physicalSourceInterval source.length parent.val.node
          let length := OAI.EditApproximation.saturatingSubtractWithWork interval.hi interval.lo
          let test := OAI.EditApproximation.wordLEWithWork length.1 [true]
          .charge (length.2 + test.2 + 1)
            (if test.1 then
              OAI.EditApproximation.queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits
                positionBits parent.val.state
            else OAI.EditApproximation.queryWarmupProgram interval N P F a
              (OAI.EditApproximation.queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits)
              (OAI.EditApproximation.queryChargedWarmupChild parent ((OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt _ _).mp hb)
                (Nat.pos_of_ne_zero (fun h => hz ((OAI.EditApproximation.Lemmas.naturalEqualWithWork_value _ _).mpr h))))
              parent.val.state)
        else OAI.EditApproximation.queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits
          parent.val.state))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R] (source target : List ℕ) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)

abbrev ChargedFamilyQueryKey (parent : OAI.EditApproximation.ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :=
  Sum (OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    {child : OAI.EditApproximation.ChargedPhysicalRequest M J target.length (passes + 1) copies T S // child.rank < parent.rank}

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {κ : Type u_1} (rank : κ → ℕ) (raw : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction) (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : κ → ℕ)

def rankedNormalizeBody (key : κ) :
    OAI.EditApproximation.BitQuery {child : κ // rank child < rank key} OAI.EditApproximation.BinaryFraction :=
  (raw key).normalize base hbase (remaining key)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {σ : Type u_1} {α : Type u_2} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q T S passes copies : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ) (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ) (initial : PhysicalEntry M J target.length → ℕ) (sourceAnswer : σ → ℚ)

noncomputable def chargedRandomMemoEvaluate (bits : ℕ)
    (encode : Sum σ (OAI.EditApproximation.ChargedPhysicalRequest M J target.length passes copies T S) → ℕ)
    (request : OAI.EditApproximation.ChargedPhysicalRequest M J target.length passes copies T S) :=
  OAI.EditApproximation.rankedMemoEvaluate (OAI.EditApproximation.SourceRanked.rank OAI.EditApproximation.ChargedPhysicalRequest.rank)
    (OAI.EditApproximation.SourceRanked.body OAI.EditApproximation.ChargedPhysicalRequest.rank
      (OAI.EditApproximation.chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger initial) sourceAnswer)
    bits encode (.inr request) .empty

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {α : Type u_1} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q T S passes copies : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (initial : PhysicalEntry M J target.length → ℕ)

noncomputable def physicalFamilyProgram :=
  OAI.EditApproximation.chargedRandomGlobalQuery source target N P F exponent H Q T S (passes + 1) copies
    factor multiplier tau eta kappa delta
    (OAI.EditApproximation.physicalFamilyGroupRead (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    (OAI.EditApproximation.physicalFamilyOnlineRead (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    initial

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

variable {α : Type u_1} [DecidableEq α] {M J : ℕ} (source target : List α) (N B : ℕ) (depth : PhysicalEntry M J target.length → ℕ)

abbrev PhysicalCoarseDraw := OAI.EditApproximation.CoarseFullSeedDraws B depth
  (fun state : OAI.EditApproximation.PhysicalEntry M J target.length => OAI.EditApproximation.physicalSource source state.1)
  (fun state : OAI.EditApproximation.PhysicalEntry M J target.length => OAI.EditApproximation.substring target state.2.lo state.2.hi)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

variable {α : Type u_1} [DecidableEq α] {M J : ℕ} (source target : List α) (N B : ℕ) (depth : PhysicalEntry M J target.length → ℕ)

open EditDistortion Finset MeasureTheory ProbabilityTheory

open Finset MeasureTheory ProbabilityTheory

theorem _root_.OAI.EditApproximation.Lemmas.coarseInitialValue_le_length {α : Type u_1} [instLocal1 : DecidableEq.{u_1 + 1} α] (B : ℕ) (D : ℕ) (Q : ℚ) (lam : ℚ) (N : ℕ) (x : List.{u_1} α) (y : List.{u_1} α) (draws : OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth.{u_1} x y) →
  OAI.EditApproximation.CoarseThresholdDraws B D) :
    OAI.EditApproximation.coarseInitialValue B D Q lam N x y draws ≤ N := by
  unfold OAI.EditApproximation.coarseInitialValue
  split_ifs
  · exact min_le_left _ _
  · exact Nat.zero_le _
  · exact min_le_left _ _

theorem _root_.OAI.EditApproximation.Lemmas.trans {Alpha : Type u_1} {s : Bool} {m : ℕ} {n : ℕ} {x : List.{u_1} Alpha} {y : List.{u_1} Alpha} {z : List.{u_1} Alpha} (h : OAI.EditDistortion.Script.{u_1} s m x y) (k : OAI.EditDistortion.Script.{u_1} s n y z) : OAI.EditDistortion.Script s (m + n) x z := by
  induction h with
  | nil => simpa using k
  | @cons l x w y e h ih =>
    simpa only [Nat.add_right_comm] using OAI.EditDistortion.Script.cons e (ih k)

theorem _root_.OAI.EditApproximation.Lemmas.to_nil {Alpha : Type u_1} {s : Bool} (x : List.{u_1} Alpha) : OAI.EditDistortion.Script s x.length x [] := by
  induction x with
  | nil => exact .nil []
  | cons a x ih => exact .cons (.delete [] x a) ih

theorem _root_.OAI.EditApproximation.Lemmas.single {Alpha : Type u_1} {s : Bool} {x : List.{u_1} Alpha} {y : List.{u_1} Alpha} (h : OAI.EditDistortion.Step.{u_1} s x y) : OAI.EditDistortion.Script s 1 x y :=
  .cons h (.nil y)

theorem _root_.OAI.EditApproximation.Lemmas.Step.symm {Alpha : Type u_1} {s : Bool} {x : List.{u_1} Alpha} {y : List.{u_1} Alpha} (h : OAI.EditDistortion.Step.{u_1} s x y) : OAI.EditDistortion.Step s y x := by
  cases h with
  | insert p q a => exact .delete p q a
  | delete p q a => exact .insert p q a
  | substitute hs p q a b => exact .substitute hs p q b a

theorem _root_.OAI.EditApproximation.Lemmas.Script.symm {Alpha : Type u_1} {s : Bool} {n : ℕ} {x : List.{u_1} Alpha} {y : List.{u_1} Alpha} (h : OAI.EditDistortion.Script.{u_1} s n x y) : OAI.EditDistortion.Script s n y x := by
  induction h with
  | nil x => exact .nil x
  | cons e h ih => exact (OAI.EditApproximation.Lemmas.trans ih (OAI.EditApproximation.Lemmas.single (OAI.EditApproximation.Lemmas.Step.symm e)))

theorem _root_.OAI.EditApproximation.Lemmas.exists_script {Alpha : Type u_1} {s : Bool} (x : List.{u_1} Alpha) (y : List.{u_1} Alpha) : ∃ n, OAI.EditDistortion.Script s n x y :=
  ⟨x.length + y.length, (OAI.EditApproximation.Lemmas.trans (OAI.EditApproximation.Lemmas.to_nil x)
  (OAI.EditApproximation.Lemmas.Script.symm (OAI.EditApproximation.Lemmas.to_nil y)))⟩

theorem _root_.OAI.EditApproximation.Lemmas.cost_spec {Alpha : Type u_1} {s : Bool} (x : List.{u_1} Alpha) (y : List.{u_1} Alpha) : OAI.EditDistortion.Script s (OAI.EditDistortion.cost s x y) x y :=
  Nat.sInf_mem (OAI.EditApproximation.Lemmas.exists_script x y)

theorem _root_.OAI.EditApproximation.Lemmas.eq_of_zero {Alpha : Type u_1} {s : Bool} {x : List.{u_1} Alpha} {y : List.{u_1} Alpha} (h : OAI.EditDistortion.Script.{u_1} s 0 x y) : x = y := by
  cases h
  rfl

theorem _root_.OAI.EditApproximation.Lemmas.cost_le {Alpha : Type u_1} {s : Bool} {n : ℕ} {x : List.{u_1} Alpha} {y : List.{u_1} Alpha} (h : OAI.EditDistortion.Script.{u_1} s n x y) : OAI.EditDistortion.cost s x y ≤ n :=
  Nat.sInf_le h

theorem _root_.OAI.EditApproximation.Lemmas.cost_refl {Alpha : Type u_1} {s : Bool} (x : List.{u_1} Alpha) : OAI.EditDistortion.cost s x x = 0 :=
  Nat.eq_zero_of_le_zero (OAI.EditApproximation.Lemmas.cost_le (.nil x))

theorem _root_.OAI.EditApproximation.Lemmas.cost_eq_zero_iff {Alpha : Type u_1} {s : Bool} {x : List.{u_1} Alpha} {y : List.{u_1} Alpha} : OAI.EditDistortion.cost s x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hc := OAI.EditApproximation.Lemmas.cost_spec (s := s) x y
    rw [h] at hc
    exact (OAI.EditApproximation.Lemmas.eq_of_zero hc)
  · rintro rfl
    exact OAI.EditApproximation.Lemmas.cost_refl _

theorem _root_.OAI.EditApproximation.Lemmas.coarseInitialValue_zero {α : Type u_1} [instLocal1 : DecidableEq.{u_1 + 1} α] (B : ℕ) (D : ℕ) (Q : ℚ) (lam : ℚ) (N : ℕ) (x : List.{u_1} α) (y : List.{u_1} α) (draws : OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth.{u_1} x y) →
  OAI.EditApproximation.CoarseThresholdDraws B D) (hzero : Eq.{1} (OAI.EditDistortion.edit.{u_1} x y) 0) : OAI.EditApproximation.coarseInitialValue B D Q lam N x y draws = 0 := by
  have hxy : x = y := (OAI.EditApproximation.Lemmas.cost_eq_zero_iff (s := true)).mp hzero
  subst y
  simp only [OAI.EditApproximation.coarseInitialValue, ite_eq_right (by omega : ¬ 2 * x.length < x.length), ite_true]

theorem _root_.OAI.EditApproximation.Lemmas.computed_fullSeedTable_range_zero (N : ℕ) (B : ℕ) {I : Type 0} {α : Type u_1} [instLocal4 : DecidableEq.{u_1 + 1} α] (depth : I → ℕ) (x : I → List.{u_1} α) (y : I → List.{u_1} α) (draws : OAI.EditApproximation.CoarseFullSeedDraws.{0, u_1} B depth x y) :
    ∀ i, OAI.EditApproximation.coarseFullSeedTable N B depth x y draws i ≤ N ∧
      (OAI.EditDistortion.edit (x i) (y i) = 0 → OAI.EditApproximation.coarseFullSeedTable N B depth x y draws i = 0) := by
  intro i
  exact ⟨OAI.EditApproximation.Lemmas.coarseInitialValue_le_length _ _ _ _ _ _ _ _,
    OAI.EditApproximation.Lemmas.coarseInitialValue_zero _ _ _ _ _ _ _ _⟩

noncomputable def physicalCoarseSeedTable (draw : OAI.EditApproximation.PhysicalCoarseDraw source target B depth) :
    OAI.EditApproximation.ClampedPhysicalSeed M J target.length N := by
  exact
    fun state =>
     ⟨OAI.EditApproximation.coarseFullSeedTable N B depth
       (fun state : OAI.EditApproximation.PhysicalEntry M J target.length => OAI.EditApproximation.physicalSource source state.1)
       (fun state : OAI.EditApproximation.PhysicalEntry M J target.length => OAI.EditApproximation.substring target state.2.lo state.2.hi) draw state,
       Nat.lt_succ_of_le ((OAI.EditApproximation.Lemmas.computed_fullSeedTable_range_zero N B depth _ _ draw state).1)⟩

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

variable {α : Type u_1} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] (source target : List α) (N P T S H : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Geometry_LocalTraceMemoOutput_5) "passes" => computedSeedPassCount N

def localFinalRootRequest (hH : 0 < H) (rootQ : OAI.EditApproximation.TargetInterval target.length) :
    OAI.EditApproximation.ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S :=
  .inr ⟨OAI.EditApproximation.PhysicalTableRequest.refinement passes 0
    (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit) T S rootQ,
    ⟨Nat.lt_succ_self _, pow_pos hH 2, le_rfl⟩⟩

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter

noncomputable def computedFamilyKernelWork (source target : List ℕ) (N : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N)
    (cost : OAI.EditApproximation.ComputedFamilyMemoKey source target N → ℕ) : ℕ :=
  OAI.EditApproximation.rankedMemoKernelWork (OAI.EditApproximation.SourceRanked.rank OAI.EditApproximation.ChargedPhysicalRequest.rank)
    (OAI.EditApproximation.SourceRanked.body OAI.EditApproximation.ChargedPhysicalRequest.rank
      (OAI.EditApproximation.physicalFamilyProgram source target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
        (40 * OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80)
        (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2)
        (OAI.EditApproximation.scheduledSeedFactor N) (OAI.EditApproximation.scheduledSeedMultiplier N)
        (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).tau (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).eta
        (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).kappa (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).delta
        (OAI.EditApproximation.clampedSeedNat input.1))
      (OAI.EditApproximation.physicalFamilyAnswer target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
        (40 * OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80)
        (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2) input.2))
    (16384 * OAI.EditApproximation.inputHeight N + 5) (OAI.EditApproximation.computedFamilyMemoCode source target N (OAI.EditApproximation.inputHeight N ^ 2)) cost
    (.inr (OAI.EditApproximation.localFinalRootRequest target N (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S
      (OAI.EditApproximation.inputHeight N) (Nat.two_pow_pos _) (OAI.EditApproximation.finalTargetState target.length))) .empty

noncomputable def computedFamilyAddressWork (source target : List ℕ) (N : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) : ℕ :=
  OAI.EditApproximation.rankedMemoAddressWork (OAI.EditApproximation.SourceRanked.rank OAI.EditApproximation.ChargedPhysicalRequest.rank)
    (OAI.EditApproximation.SourceRanked.body OAI.EditApproximation.ChargedPhysicalRequest.rank
      (OAI.EditApproximation.physicalFamilyProgram source target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
        (40 * OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80)
        (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2)
        (OAI.EditApproximation.scheduledSeedFactor N) (OAI.EditApproximation.scheduledSeedMultiplier N)
        (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).tau (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).eta
        (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).kappa (OAI.EditApproximation.rationalParameters (OAI.EditApproximation.inputSmallLog N)).delta
        (OAI.EditApproximation.clampedSeedNat input.1))
      (OAI.EditApproximation.physicalFamilyAnswer target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
        (40 * OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80)
        (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2) input.2))
    (16384 * OAI.EditApproximation.inputHeight N + 5) (OAI.EditApproximation.computedFamilyMemoCode source target N (OAI.EditApproximation.inputHeight N ^ 2))
    (fun key => (OAI.EditApproximation.computedFamilyMemoCodeWithWork source target N (OAI.EditApproximation.inputHeight N ^ 2) key).2)
    (.inr (OAI.EditApproximation.localFinalRootRequest target N (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S
      (OAI.EditApproximation.inputHeight N) (Nat.two_pow_pos _) (OAI.EditApproximation.finalTargetState target.length))) .empty

noncomputable def computedFamilyCoarseCopyStorage (source target : List ℕ) (N : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) : ℕ :=
  OAI.EditApproximation.computedFamilyKernelWork source target N input (OAI.EditApproximation.coarseHistoryKeyCost
    (OAI.EditApproximation.physicalCoarseInputStorage (M := (OAI.EditApproximation.integerParameters N).M)
      (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) source target))

noncomputable def computedFamilyCoarseArrayCapacity (source target : List ℕ) (N : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) : ℕ :=
  OAI.EditApproximation.computedFamilyKernelWork source target N input (OAI.EditApproximation.coarseHistoryKeyCost (fun _ => (N + 2) ^ 37))

noncomputable def computedFamilyCoarseScratchCapacity (source target : List ℕ) (N : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) : ℕ :=
  OAI.EditApproximation.computedFamilyKernelWork source target N input (OAI.EditApproximation.coarseHistoryKeyCost (fun _ => (N + 2) ^ 181))

noncomputable def computedFamilyCoarseControlCapacity (source target : List ℕ) (N : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) : ℕ :=
  OAI.EditApproximation.computedFamilyKernelWork source target N input (OAI.EditApproximation.coarseHistoryKeyCost (fun _ => (N + 2) ^ 182))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P T S H : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_4) "Seed" => ClampedPhysicalSeed M J target.length N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_5) "ell" => inputSmallLog N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_6) "exponent" => (40 * smallLogExponent N : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_7) "passes" => computedSeedPassCount N

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_8) "tau" => RationalParameters.tau (rationalParameters ell)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_9) "eta" => RationalParameters.eta (rationalParameters ell)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_10) "kappa" => RationalParameters.kappa (rationalParameters ell)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_11) "delta" => RationalParameters.delta (rationalParameters ell)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_12) "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_13) "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyMemo_14) "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S

noncomputable def physicalFamilyMemoResult (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (rootQ : OAI.EditApproximation.TargetInterval target.length) (input : Seed × Family) :=
  OAI.EditApproximation.chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80) T S (passes + 1) (H ^ 2)
    (OAI.EditApproximation.scheduledSeedFactor N) (OAI.EditApproximation.scheduledSeedMultiplier N) tau eta kappa delta
    (OAI.EditApproximation.physicalFamilyGroupRead target N P ell exponent H (ell ^ 80) passes (H ^ 2))
    (OAI.EditApproximation.physicalFamilyOnlineRead target N P ell exponent H (ell ^ 80) passes (H ^ 2))
    (OAI.EditApproximation.clampedSeedNat input.1)
    (OAI.EditApproximation.physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes (H ^ 2) input.2)
    bits encode (OAI.EditApproximation.localFinalRootRequest target N T S H hH rootQ)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory Finset

attribute [local instance] Classical.propDecidable

noncomputable def selectionIndicator (p : Prop) : ℝ := if p then 1 else 0

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

noncomputable def coarseIndexedEntryCostSum {M J B : ℕ} [NeZero B] (source target : List ℕ)
    (N : ℕ) (depth : OAI.EditApproximation.PhysicalEntry M J target.length → ℕ)
    (draw : OAI.EditApproximation.PhysicalCoarseDraw source target B depth)
    (selected : OAI.EditApproximation.PhysicalEntry M J target.length → Prop) : ℝ := by
  classical
  exact ∑ entry : OAI.EditApproximation.PhysicalEntry M J target.length, OAI.EditApproximation.selectionIndicator (selected entry) *
    (OAI.EditApproximation.coarseIndexedEntryBinaryCost N B (depth entry) (OAI.EditApproximation.physicalSource source entry.1)
      (OAI.EditApproximation.substring target entry.2.lo entry.2.hi) (draw entry) : ℝ)

def querySupportedChildAllocation {σ : Type u_1} {M J n : ℕ} (passes copies T S : ℕ)
    (parent : {r : OAI.EditApproximation.PhysicalTableRequest M J n // r.Bounded passes copies T S})
    (key : OAI.EditApproximation.QueryPhysicalChild (σ := σ) passes copies T S parent) : ℕ :=
  match key with
  | .inl _ => 0
  | .inr child => OAI.EditApproximation.queryPhysicalBoundedAllocation passes copies T S child.val

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

variable {ι : Type u_1} [Fintype ι] (range : ι → ℕ) [∀ i, NeZero (range i)]

open Finset

theorem _root_.OAI.EditApproximation.Lemmas.rejectionWord_range (N : ℕ) (hN : LT.lt.{0} 0 N) :
    N ≤ 2 ^ OAI.EditApproximation.rejectionBitCount N ∧ 2 ^ OAI.EditApproximation.rejectionBitCount N < 2 * N := by
  constructor
  · exact Nat.le_pow_clog (by norm_num) N
  · by_cases hNone : N = 1
    · subst N
      norm_num [OAI.EditApproximation.rejectionBitCount]
    · have hN1 : 1 < N := by omega
      have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hN1
      have hB := Nat.clog_pos (by norm_num : 1 < 2) hN1
      have hpow : 2 ^ OAI.EditApproximation.rejectionBitCount N = 2 ^ (Nat.clog 2 N).pred * 2 := by
        rw [OAI.EditApproximation.rejectionBitCount, ← pow_succ]
        congr 1
        exact (Nat.succ_pred_eq_of_pos hB).symm
      rw [hpow]
      omega

noncomputable def rejectionFailureLaw (i : ι) : Measure ℕ := by
  exact
    geometricMeasure (OAI.EditApproximation.rejectionSuccessParameter (range i) (2 ^ OAI.EditApproximation.rejectionBitCount (range i))
      (Nat.pos_of_ne_zero (NeZero.ne (range i)))
      (OAI.EditApproximation.Lemmas.rejectionWord_range (range i) (Nat.pos_of_ne_zero (NeZero.ne (range i)))).1)

end OAI.EditApproximation

end


