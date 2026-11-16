-- Prove2me | Definitions.Def_EditApproxScheme_18
-- name    : EditApproxScheme_18
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T17:01:03.301204+00:00
-- url     : https://prove2.me/theorems/05fa019d-bcc0-487a-904e-e3c7858ca967
-- title:
--   Edit-distance approximation scheme, part 18 of 20: raw-band work accounting
-- statement:
--   This is **part 18 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains the raw-band work accounting: local online scale sources, online selection, local refinement and band work, random-data requests, active family and charged family table work, memo work, local work, and the output `integerBinaryAnswerRawBand`. It also proves 13 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L10689-L11398 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 18 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_17

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {α : Type u_4} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)

def preparedLocalOnlineScaleSourceWithWorkRawBand (e : ℕ) (query : OAI.EditApproximation.TargetInterval target.length) :
    Option (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
      (Fin M × OAI.EditApproximation.TargetInterval target.length) M) × ℕ := by
  exact
    let b := 2 ^ e
    let spacing := OAI.EditApproximation.seedGridSpacingWithWork b P
    let center := OAI.EditApproximation.roundStateWithWork (OAI.EditApproximation.bitWordValue spacing.1) (OAI.EditApproximation.Lemmas.seedGridSpacingWithWork_pos b P hP) query
    let word := parentInitial center.1
    let eligible := OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork b F a word.1
    if eligible.1 then
      let sample := integer b center.1
      let selected := OAI.EditApproximation.BinaryFraction.preparedOnlineReadWithWorkRaw source target parent P F exponent H b (Nat.two_pow_pos e) hP
        tau eta kappa child initial table R hc hi t center.1 sample.1
      (selected.1, spacing.2 + center.2 + word.2 + eligible.2 + selected.2 + sample.2 + e + 5)
    else (none, spacing.2 + center.2 + word.2 + eligible.2 + e + 3)

def preparedLocalOnlineActionsSourceWithWorkRawBand (N : ℕ) (query : OAI.EditApproximation.TargetInterval target.length) :
    List (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
      (Fin M × OAI.EditApproximation.TargetInterval target.length) M) × ℕ :=
  let word := parentInitial query
  let scales := OAI.EditApproximation.BinaryFraction.queryExponentsWithWork N F a word.1
  let selected := OAI.EditApproximation.filterMapWithWork
    (fun e => OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query) scales.1
  (selected.1, word.2 + scales.2 + selected.2 + 1)

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {α : Type u_4} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)

def queryOnlineSelectWithWorkRawBand (t : ℕ)
    (integer : ℕ → OAI.EditApproximation.TargetInterval target.length → ℕ × ℕ)
    (keys : List (Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length)) (words : List OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval target.length) :=
  OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceWithWorkRawBand source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial (OAI.EditApproximation.BinaryFraction.queryHistoryReadWithWork keys words) R hc hi (t - 1) integer N q

def queryGroupSelectWithWorkRawBand (draw : OAI.EditApproximation.CountedCellGroupDraws M F Q)
    (keys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) (words : List OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval target.length) :=
  OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWorkRawBand source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial (OAI.EditApproximation.BinaryFraction.queryChildReadWithWork keys words) R hc hi N draw q

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_4} {α : Type u_5} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (t : ℕ) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R) (draw : CountedCellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ × ℕ) (q : TargetInterval target.length) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction) (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

def queryLocalRefinementRawBand : OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction :=
  OAI.EditApproximation.queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF a t parentInitial draw q
    readEarlier readCurrent
    (fun keys words => OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand source target parent N P F exponent H hP
      tau a eta kappa parentInitial child initial R hc hi t integer keys words q)
    (fun keys words => OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand source target parent N P F exponent Q
      eM eF hP hM hF tau a parentInitial child initial R hc hi draw keys words q)
    (fun earlierKeys earlierWords groups online currentKeys currentWords =>
      OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork parent N P F a delta parentInitial
        t earlierKeys earlierWords groups online currentKeys currentWords q))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_4} {α : Type u_5} (source target : List α) {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (t : ℕ) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R) (q : TargetInterval target.length) (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction) (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction) (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

def queryLocalRandomSourcesRawBand : OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction :=
  OAI.EditApproximation.queryGroupSourceGather M N F Q exponent eM eF hM hF a parentInitial q readGroup
    fun groupKeys groupWords =>
      OAI.EditApproximation.queryOnlineSourceGather parent N P F exponent H hP tau a parentInitial child q readInteger
        fun onlineKeys onlineWords =>
          OAI.EditApproximation.queryLocalRefinementRawBand source target parent N P F exponent H Q eM eF hP hM hF
            tau a eta kappa delta t parentInitial child initial R hc hi
            (OAI.EditApproximation.BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
            (OAI.EditApproximation.BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords)
            q readEarlier readCurrent

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_4} {α : Type u_5} (source target : List α) {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (t : ℕ) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction) (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction) (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction) (q : TargetInterval target.length) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction) (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

open Finset

theorem _root_.OAI.EditApproximation.Lemmas.gatheredWordLookupWithWork_cost {κ : Type 0} (equal : κ → κ → Prod.{0, 0} Bool ℕ) (C : ℕ) (hC : ∀ (a b : κ), LE.le.{0} (equal a b).2 C) (keys : List.{0} κ) (values : List.{0} OAI.EditApproximation.BinaryFraction) (query : κ) :
    (OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork equal keys values query).2 ≤ 1 + keys.length * (C + 1) := by
  induction keys generalizing values with
  | nil => simp only [OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_rfl]
  | cons key keys ih =>
    cases values with
    | nil => simp only [OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork]; omega
    | cons value values =>
      have hc := hC query key
      have hi := ih values
      simp only [OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork]
      split_ifs <;> simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega

theorem _root_.OAI.EditApproximation.Lemmas.bitCompareWithWork_cost (left : List.{0} Bool) (right : List.{0} Bool) :
    (OAI.EditApproximation.bitCompareWithWork left right).2 ≤ 4 * (left.length + right.length) + 1 := by
  induction left generalizing right with
  | nil =>
    simp only [OAI.EditApproximation.bitCompareWithWork]
    induction right with
    | nil => simp [OAI.EditApproximation.bitCompareNilLeftWithWork]
    | cons b bs ih =>
      simp only [OAI.EditApproximation.bitCompareNilLeftWithWork, List.length_cons, List.length_nil] at *
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih []
      simp only [OAI.EditApproximation.bitCompareWithWork, List.length_cons, List.length_nil] at *
      omega
    | cons b bs =>
      have h := ih bs
      simp only [OAI.EditApproximation.bitCompareWithWork, List.length_cons] at *
      omega

theorem _root_.OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_cost (a : ℕ) (b : ℕ) :
    (OAI.EditApproximation.binaryNaturalCompareWithWork a b).2 ≤ 4 * (Nat.size a + Nat.size b) + 1 := by
  simpa only [OAI.EditApproximation.binaryNaturalCompareWithWork, Nat.size_eq_bits_len] using OAI.EditApproximation.Lemmas.bitCompareWithWork_cost a.bits b.bits

theorem _root_.OAI.EditApproximation.Lemmas.naturalEqualWithWork_cost (a : ℕ) (b : ℕ) (B : ℕ) (ha : LE.le.{0} a.size B) (hb : LE.le.{0} b.size B) :
    (OAI.EditApproximation.naturalEqualWithWork a b).2 ≤ 8 * B + 2 := by
  have h := OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_cost a b
  change (OAI.EditApproximation.binaryNaturalCompareWithWork a b).2 + 1 ≤ _
  omega

theorem _root_.OAI.EditApproximation.Lemmas.coordinateEqualWithWork_cost {M : ℕ} {n : ℕ} (a : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval n)) (b : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval n)) (B : ℕ) (hM : LE.le.{0} M.size B) (hn : LE.le.{0} n.size B) :
    (OAI.EditApproximation.coordinateEqualWithWork a b).2 ≤ 24 * B + 8 := by
  have hc := OAI.EditApproximation.Lemmas.naturalEqualWithWork_cost a.1.val b.1.val B
    ((Nat.size_le_size a.1.isLt.le).trans hM) ((Nat.size_le_size b.1.isLt.le).trans hM)
  have hl := OAI.EditApproximation.Lemmas.naturalEqualWithWork_cost a.2.lo b.2.lo B
    ((Nat.size_le_size (a.2.ordered.trans a.2.valid)).trans hn)
    ((Nat.size_le_size (b.2.ordered.trans b.2.valid)).trans hn)
  have hh := OAI.EditApproximation.Lemmas.naturalEqualWithWork_cost a.2.hi b.2.hi B
    ((Nat.size_le_size a.2.valid).trans hn) ((Nat.size_le_size b.2.valid).trans hn)
  change _ + _ + _ + 2 ≤ _
  omega

theorem _root_.OAI.EditApproximation.Lemmas.queryChildReadWithWork_cost {M : ℕ} {n : ℕ} (keys : List.{0} (Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval n))) (values : List.{0} OAI.EditApproximation.BinaryFraction) (i : Fin M) (q : OAI.EditApproximation.TargetInterval n) (B : ℕ) (hM : LE.le.{0} M.size B) (hn : LE.le.{0} n.size B) :
    (OAI.EditApproximation.BinaryFraction.queryChildReadWithWork keys values i q).2 ≤ 1 + keys.length * (24 * B + 9) := by
  exact OAI.EditApproximation.Lemmas.gatheredWordLookupWithWork_cost OAI.EditApproximation.coordinateEqualWithWork (24 * B + 8)
    (fun a b => OAI.EditApproximation.Lemmas.coordinateEqualWithWork_cost a b B hM hn) keys values (i, q)

theorem _root_.OAI.EditApproximation.Lemmas.queryChildReadWithWork_budget {M : ℕ} {n : ℕ} (keys : List.{0} (Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval n))) (words : List.{0} OAI.EditApproximation.BinaryFraction) (i : Fin M) (r : OAI.EditApproximation.TargetInterval n) :
    (OAI.EditApproximation.BinaryFraction.queryChildReadWithWork keys words i r).2 ≤ OAI.EditApproximation.BinaryFraction.queryDataReadBudget M n keys := by
  exact OAI.EditApproximation.Lemmas.queryChildReadWithWork_cost keys words i r _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)

def queryLocalBandRawBand : OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction := by
  exact
    OAI.EditApproximation.queryBandGather M parent N P F exponent hP a parentInitial q readMass readInitial
      fun keys massWords initialWords =>
        OAI.EditApproximation.queryLocalRandomSourcesRawBand source target parent N P F exponent H Q eM eF hP hM hF
          tau a eta kappa delta t parentInitial
          (OAI.EditApproximation.BinaryFraction.queryChildReadWithWork keys massWords)
          (OAI.EditApproximation.BinaryFraction.queryChildReadWithWork keys initialWords)
          (OAI.EditApproximation.BinaryFraction.queryDataReadBudget M target.length keys)
          (OAI.EditApproximation.Lemmas.queryChildReadWithWork_budget keys massWords)
          (OAI.EditApproximation.Lemmas.queryChildReadWithWork_budget keys initialWords)
          q readGroup readInteger readEarlier readCurrent

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_4} {α : Type u_5} (source target : List α) {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (t : ℕ) (readParent : TargetInterval target.length → BitQuery ι BinaryFraction) (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction) (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction) (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction) (q : TargetInterval target.length) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction) (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

def queryLocalProgramRawBand : OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction :=
  OAI.EditApproximation.queryInitialGather N P F exponent hP a q readParent fun keys words =>
    OAI.EditApproximation.queryLocalBandRawBand source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t (OAI.EditApproximation.BinaryFraction.queryParentReadWithWork keys words)
      readMass readInitial readGroup readInteger q readEarlier readCurrent

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {σ : Type u_4} {α : Type u_5} (source target : List α) {M J : ℕ} [NeZero M] (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (copies pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J) (readGroup : GroupScalarKey M F Q → BitQuery σ BinaryFraction) (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery σ BinaryFraction) (q : TargetInterval target.length)

def queryPhysicalRandomDataRequestRawBand :
    OAI.EditApproximation.BitQuery (Sum σ {child : OAI.EditApproximation.PhysicalTableRequest M J target.length //
      child.combinedRank T S < (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S})
      OAI.EditApproximation.BinaryFraction :=
  OAI.EditApproximation.queryLocalProgramRawBand source target (OAI.EditApproximation.physicalSourceInterval source.length node)
    N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
    (fun r => OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (OAI.EditApproximation.queryPhysicalWarmupRead copies pass copy T S t ht node q node le_rfl 0 (Nat.zero_le T) r))
    (fun input => OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (OAI.EditApproximation.queryPhysicalMassRead copies pass copy T S t ht node hbelow q input))
    (fun input => OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (OAI.EditApproximation.queryPhysicalWarmupRead copies pass copy T S t ht node q
        (OAI.EditApproximation.physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2))
    (fun key => OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (Sum.inl key, 1)) (readGroup key))
    (fun key range => OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (Sum.inl key, 1)) (readInteger key range)) q
    (fun input => OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (OAI.EditApproximation.queryPhysicalEarlierRead copies pass copy T S t node hbelow q input))
    (fun input => OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
      (OAI.EditApproximation.queryPhysicalCurrentRead copies pass copy T S t node hbelow q input))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {α : Type u_4} {M J R : ℕ} [NeZero M] (source target : List α) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (passes copies pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J) (time : Fin R) (q : TargetInterval target.length)

def queryFamilyRefinementRawBand :
    OAI.EditApproximation.BitQuery (Sum (OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)
      {child : OAI.EditApproximation.PhysicalTableRequest M J target.length // child.combinedRank T S <
        (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S}) OAI.EditApproximation.BinaryFraction :=
  OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand source target N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta copies pass copy T S t ht node hbelow
    (OAI.EditApproximation.queryFamilyGroupRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)
    (OAI.EditApproximation.queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time) q

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {α : Type u_4} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ) (request : PhysicalTableRequest M J target.length) (hindex : T < request.index) (hbelow : request.node.1.val < J)

theorem _root_.OAI.EditApproximation.Lemmas.active_request_eqRawBand {α : Type u_4} {M : ℕ} {J : ℕ} (target : List.{u_4} α) (T : ℕ) (request : OAI.EditApproximation.PhysicalTableRequest M J (List.length.{u_4} target)) (hindex : LT.lt.{0} T request.index) :
    OAI.EditApproximation.PhysicalTableRequest.refinement request.pass request.copy request.node T (request.index - T)
      request.state = request := by
  have hi : T + (request.index - T) = request.index := by omega
  unfold OAI.EditApproximation.PhysicalTableRequest.refinement
  rw [hi]

def queryFamilyActiveRawBand :
    OAI.EditApproximation.BitQuery (Sum (OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)
      {child : OAI.EditApproximation.PhysicalTableRequest M J target.length //
        child.combinedRank T S < request.combinedRank T S}) OAI.EditApproximation.BinaryFraction := by
  exact
    OAI.EditApproximation.BitQuery.mapKeysWithWork
      (fun key => (Sum.map id (fun child => ⟨child.val, by
        simpa only [OAI.EditApproximation.Lemmas.active_request_eqRawBand (target := target) (T := T) (request := request) (hindex := hindex)] using child.property⟩) key, 1))
      (OAI.EditApproximation.queryFamilyRefinementRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
        passes copies request.pass request.copy T S (request.index - T) (Nat.sub_pos_of_lt hindex)
        request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {α : Type u_4} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ) (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S}) (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)

def queryFamilyBoundedActiveRawBand :
    OAI.EditApproximation.BitQuery (Sum (OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)
      {child : {r : OAI.EditApproximation.PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S} //
        child.val.combinedRank T S < parent.val.combinedRank T S}) OAI.EditApproximation.BinaryFraction :=
  OAI.EditApproximation.queryRestrictPhysicalBody (passes + 1) copies T S parent
    (OAI.EditApproximation.queryFamilyActiveRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
      T S passes copies parent.val hindex hbelow)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R] (source target : List ℕ) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)

theorem _root_.OAI.EditApproximation.Lemmas.queryNaturalLEWithWork_value (a : ℕ) (b : ℕ) :
    (OAI.EditApproximation.wordLEWithWork a.bits b.bits).1 = true ↔ a ≤ b := by
  simp only [OAI.EditApproximation.Lemmas.wordLEWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits]

def queryChargedFamilyTableRawBand
    (parent : {r : OAI.EditApproximation.PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S}) :
    OAI.EditApproximation.BitQuery (OAI.EditApproximation.ChargedFamilyQueryKey (R := R) target N P F exponent H Q (.inr parent)) OAI.EditApproximation.BinaryFraction := by
  exact
    let index := OAI.EditApproximation.wordLEWithWork parent.val.index.bits T.bits
    .charge (index.2 + 1)
      (if hi : index.1 = true then
        OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
          (OAI.EditApproximation.queryChargedWarmup source target N P F (A parent.val.pass) (a parent.val.pass) multiplier
            parent occurrence symbolBits positionBits)
      else let depth := OAI.EditApproximation.binaryNaturalCompareWithWork parent.val.node.1.val J
        .charge (depth.2 + 1)
          (if hb : depth.1 = .lt then
            let interval := OAI.EditApproximation.physicalSourceInterval source.length parent.val.node
            let length := OAI.EditApproximation.saturatingSubtractWithWork interval.hi interval.lo
            let short := OAI.EditApproximation.wordLEWithWork length.1 [true]
            .charge (length.2 + short.2 + 1)
              (if short.1 then
                OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
                  (OAI.EditApproximation.queryPhysicalInitial source target N P F (A parent.val.pass) (a parent.val.pass)
                    multiplier parent occurrence symbolBits positionBits parent.val.state)
              else OAI.EditApproximation.BitQuery.mapKeysWithWork
                (fun key => (Sum.map id (fun child =>
                  ⟨Sum.inr child.val, OAI.EditApproximation.Lemmas.table_rank_lt parent child.val child.property⟩)
                  key, 1))
                (OAI.EditApproximation.queryFamilyBoundedActiveRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF
                  tau (a parent.val.pass) eta kappa delta T S passes copies parent
                  (Nat.lt_of_not_ge (fun h => hi ((OAI.EditApproximation.Lemmas.queryNaturalLEWithWork_value parent.val.index T).mpr h)))
                  ((OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_lt _ _).mp hb)))
          else OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (Sum.inr key, 1))
            (OAI.EditApproximation.queryPhysicalInitial source target N P F (A parent.val.pass) (a parent.val.pass)
              multiplier parent occurrence symbolBits positionBits parent.val.state)))

def queryChargedFamilyGlobalRawBand
    (coarse : OAI.EditApproximation.PhysicalEntry M J target.length → OAI.EditApproximation.BinaryFraction × ℕ)
    (request : OAI.EditApproximation.ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    OAI.EditApproximation.BitQuery (OAI.EditApproximation.ChargedFamilyQueryKey (R := R) target N P F exponent H Q request) OAI.EditApproximation.BinaryFraction :=
  match request with
  | .inl entry => OAI.EditApproximation.BitQuery.compute (coarse entry)
  | .inr parent => OAI.EditApproximation.queryChargedFamilyTableRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R] (source target : List ℕ) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ) (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ) (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)

def queryFamilyMemoRawRawBand (key : OAI.EditApproximation.QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :=
  OAI.EditApproximation.SourceRanked.bitBody OAI.EditApproximation.ChargedPhysicalRequest.rank
    (OAI.EditApproximation.queryChargedFamilyGlobalRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse)
    (OAI.EditApproximation.queryFamilySourceWordWithWork target N P F exponent H Q draw) key

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

theorem _root_.OAI.EditApproximation.Lemmas.computedParameterP_pos (N : ℕ) : 0 < (OAI.EditApproximation.integerParameters N).P :=
  Nat.pow_pos (Nat.two_pow_pos _)

def computedQueryMemoRawRawBand (source target : List ℕ) (N : ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) (key : OAI.EditApproximation.ComputedFamilyMemoKey source target N) := by
  exact
    OAI.EditApproximation.queryFamilyMemoRawRawBand source target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
      (40 * OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80)
      (OAI.EditApproximation.heightExponent N / 20) (OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.Lemmas.computedParameterP_pos N) rfl rfl
      (fun pass => (OAI.EditApproximation.scheduledSeedWordWithWork N pass).1)
      (fun pass => (OAI.EditApproximation.computedQueryParameters N pass).factor)
      (OAI.EditApproximation.computedQueryParameters N 0).tau (OAI.EditApproximation.computedQueryParameters N 0).eta
      (OAI.EditApproximation.computedQueryParameters N 0).kappa (OAI.EditApproximation.computedQueryParameters N 0).delta
      (OAI.EditApproximation.scheduledSeedMultiplier N) occurrence symbolBits positionBits
      (fun entry => (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.clampedSeedNat input.1 entry), 0)) input.2 key

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

theorem _root_.OAI.EditApproximation.Lemmas.refinementBaseWithWork_value (ell : List.{0} Bool) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.refinementBaseWithWork ell).1 = OAI.EditApproximation.bitWordValue ell ^ 10 + 1 := by
  (simp only [OAI.EditApproximation.refinementBaseWithWork, OAI.EditApproximation.Lemmas.trimBitWordWithWork_value, OAI.EditApproximation.Lemmas.bitAddWithWork_value,
    OAI.EditApproximation.Lemmas.bitPowerWithWork_value, OAI.EditApproximation.bitWordValue, Bool.toNat_true, Bool.toNat_false])

theorem _root_.OAI.EditApproximation.Lemmas.computedQueryBase_value (N : ℕ) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.computedQueryBase N) = OAI.EditApproximation.inputSmallLog N ^ 10 + 1 := by
  simp only [OAI.EditApproximation.computedQueryBase, OAI.EditApproximation.Lemmas.refinementBaseWithWork_value, OAI.EditApproximation.Lemmas.bitWordValue_bits]

theorem _root_.OAI.EditApproximation.Lemmas.computedQueryBase_pos (N : ℕ) : 0 < OAI.EditApproximation.bitWordValue (OAI.EditApproximation.computedQueryBase N) := by
  rw [OAI.EditApproximation.Lemmas.computedQueryBase_value]
  omega

def computedQueryMemoNormalizedRawBand (source target : List ℕ) (N : ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) :
    (key : OAI.EditApproximation.ComputedFamilyMemoKey source target N) → OAI.EditApproximation.BitQuery
      {child : OAI.EditApproximation.ComputedFamilyMemoKey source target N //
        OAI.EditApproximation.SourceRanked.rank OAI.EditApproximation.ChargedPhysicalRequest.rank child < OAI.EditApproximation.SourceRanked.rank OAI.EditApproximation.ChargedPhysicalRequest.rank key}
      OAI.EditApproximation.BinaryFraction := by
  exact
    OAI.EditApproximation.rankedNormalizeBody (OAI.EditApproximation.SourceRanked.rank OAI.EditApproximation.ChargedPhysicalRequest.rank)
      (OAI.EditApproximation.computedQueryMemoRawRawBand source target N occurrence symbolBits positionBits input)
      (OAI.EditApproximation.computedQueryBase N) (OAI.EditApproximation.Lemmas.computedQueryBase_pos N)
      (OAI.EditApproximation.queryFamilyMemoRemaining target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
        (40 * OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

attribute [local instance] queryRoundsNeZero

def computedQueryMemoResultRawBand (source target : List ℕ) (N : ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) :=
  OAI.EditApproximation.rankedBitMemoEvaluate (OAI.EditApproximation.SourceRanked.rank OAI.EditApproximation.ChargedPhysicalRequest.rank)
    (OAI.EditApproximation.computedQueryMemoNormalizedRawBand source target N occurrence symbolBits positionBits input)
    (16384 * OAI.EditApproximation.inputHeight N + 5) (OAI.EditApproximation.computedFamilyMemoCode source target N (OAI.EditApproximation.inputHeight N ^ 2))
    (.inr (OAI.EditApproximation.localFinalRootRequest target N (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S
      (OAI.EditApproximation.inputHeight N) (Nat.two_pow_pos _) (OAI.EditApproximation.finalTargetState target.length))) .empty

def computedQueryLocalWorkRawBand (source target : List ℕ) (N : ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) : OAI.EditApproximation.ComputedFamilyMemoKey source target N → ℕ :=
  OAI.EditApproximation.rankedBitLocalWork (OAI.EditApproximation.SourceRanked.rank OAI.EditApproximation.ChargedPhysicalRequest.rank)
    (OAI.EditApproximation.computedQueryMemoNormalizedRawBand source target N occurrence symbolBits positionBits input)

def computedQueryAnswerWithWorkRawBand (source target : List ℕ) (N : ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) : List Bool × ℕ :=
  if source = target then ([], source.length + target.length + 1)
  else let result := OAI.EditApproximation.computedQueryMemoResultRawBand source target N occurrence symbolBits positionBits input
    let answer := OAI.EditApproximation.BinaryFraction.finalAnswerWithWork N result.value
    (answer.1, answer.2 + source.length + target.length + 1)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

def integerQueryLocalWorkRawBand (source target : List ℤ) (N : ℕ) :=
  OAI.EditApproximation.computedQueryLocalWorkRawBand (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N
    (OAI.EditApproximation.integerOccurrenceIndex source target) (OAI.EditApproximation.integerInputSymbolBits source target) (OAI.EditApproximation.integerInputPositionBits target)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def integerBinaryOutputRawBand (source target : List ℤ) (N : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N) :=
  OAI.EditApproximation.computedQueryAnswerWithWorkRawBand (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N
    (OAI.EditApproximation.integerOccurrenceIndex source target) (OAI.EditApproximation.integerInputSymbolBits source target) (OAI.EditApproximation.integerInputPositionBits target) input

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory

noncomputable def integerBinaryAnswerRawBand (source target : List ℤ) (N : ℕ) (epsilon : OAI.EditApproximation.BinaryFraction)
    (outcome : OAI.EditApproximation.ComputedFullOutcome (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N) : ℕ :=
  if OAI.EditApproximation.physicalLargeInput N epsilon then
    match outcome with
    | .inl _ => OAI.EditApproximation.exactSuffixAnswer (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode)
    | .inr execution => OAI.EditApproximation.bitWordValue (OAI.EditApproximation.integerBinaryOutputRawBand source target N
        (OAI.EditApproximation.computedExecutionAccepted _ _ N execution)).1
  else OAI.EditApproximation.exactSuffixAnswer (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {α : Type u_4} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)

open Finset

def preparedComputedCellSourceAllocationRawBand (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : OAI.EditApproximation.cellScaleReadDraw M b Q (OAI.EditApproximation.BinaryFraction.nat F).value)
    (drawAllocation : ∀ t : Fin (OAI.EditApproximation.groupDyadicScales M b (OAI.EditApproximation.BinaryFraction.nat F).value).length,
      Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b (OAI.EditApproximation.BinaryFraction.nat F).value t)) → ℕ)
    (cell : ℕ × ℕ) : ℕ := by
  exact
    OAI.EditApproximation.BinaryFraction.groupScalesAllocation eM eb eF +
      OAI.EditApproximation.BinaryFraction.preparedCellGroupSourceAllocationRaw source target parent b P F exponent Q
        (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
        R R hc hi (OAI.EditApproximation.BinaryFraction.groupScalesWithWork eM eb eF).1 (OAI.EditApproximation.Lemmas.computedGroupScales_value M b F eM eb eF hM hb hF)
        draw parentAllocation childAllocation initialAllocation currentAllocation drawAllocation cell

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {α : Type*} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)

variable (draw : CellGroupReadDraws M F Q) (drawAllocation : CellGroupSourceAllocations M F Q)

open Finset

def castGroupSourceAllocationRawBand (b : ℕ) (cell : ℕ × ℕ) :
    ∀ t : Fin (OAI.EditApproximation.groupDyadicScales M b (OAI.EditApproximation.BinaryFraction.nat F).value).length,
      Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b (OAI.EditApproximation.BinaryFraction.nat F).value t)) → ℕ := by
  exact
    Eq.mpr (congrArg (fun f => ∀ t : Fin (OAI.EditApproximation.groupDyadicScales M b f).length,
      Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b f t)) → ℕ) (OAI.EditApproximation.Lemmas.nat_value F)) (drawAllocation b cell)

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {α : Type u_4} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)

variable (draw : CellGroupReadDraws M F Q) (drawAllocation : CellGroupSourceAllocations M F Q)

open Finset

def preparedLocalGroupScaleSourceAllocationRawBand (eb : ℕ) (query : OAI.EditApproximation.TargetInterval target.length) : ℕ := by
  exact
    let b := 2 ^ eb
    let side := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat b)).1
    let radius := (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork (parentInitial query).1).1
    let cells := (OAI.EditApproximation.BinaryFraction.targetCellsWithWork side (OAI.EditApproximation.bitWordValue radius) query).1
    parentAllocation query + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat b) +
      OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation (parentInitial query).1 + OAI.EditApproximation.BinaryFraction.targetCellsAllocation side (OAI.EditApproximation.bitWordValue radius) query +
      OAI.EditApproximation.filterMapAllocation (fun cell =>
        OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand source target parent P F exponent Q eM eF hM hF hP tau a
          parentInitial child initial current R hc hi b eb rfl
          (Eq.mpr (congrArg (OAI.EditApproximation.cellScaleReadDraw M b Q) (OAI.EditApproximation.Lemmas.nat_value F)) (draw b cell)) cell)
        (fun cell => OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceAllocationRawBand source target parent P F exponent Q eM eF hM hF hP tau a
          parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
          b eb rfl (Eq.mpr (congrArg (OAI.EditApproximation.cellScaleReadDraw M b Q) (OAI.EditApproximation.Lemmas.nat_value F)) (draw b cell))
          (OAI.EditApproximation.BinaryFraction.castGroupSourceAllocationRawBand F Q drawAllocation b cell) cell) cells + eb

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {α : Type u_4} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation currentAllocation : Fin M → TargetInterval target.length → ℕ)

variable (draw : CellGroupReadDraws M F Q) (drawAllocation : CellGroupSourceAllocations M F Q)

def localGroupSourceScaleBlockRawBand (eb : ℕ) (query : OAI.EditApproximation.TargetInterval target.length) :
    List (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length) (Fin M × OAI.EditApproximation.TargetInterval target.length) M) × ℕ :=
  let guard := OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1
  if guard.1 then
    let selected := OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial current R hc hi eb draw query
    (selected.1, guard.2 + selected.2 + eb + 4)
  else ([], guard.2 + eb + 4)

def localGroupSourceScaleBlockAllocationRawBand (eb : ℕ) (query : OAI.EditApproximation.TargetInterval target.length) : ℕ :=
  OAI.EditApproximation.BinaryFraction.refinementScaleGuardAllocation F (2 ^ eb) a (parentInitial query).1 + eb +
    if (OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial query).1).1 then
      OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceAllocationRawBand source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
        draw drawAllocation eb query
    else 0

def preparedLocalCellGroupsSourceAllocationRawBand (N : ℕ) (query : OAI.EditApproximation.TargetInterval target.length) : ℕ :=
  let count := max 1 N.bits.length
  parentAllocation query + count + N.bits.length +
    OAI.EditApproximation.arithmeticFlatMapAllocation
      (fun eb => OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockRawBand source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi draw eb query)
      (fun eb => OAI.EditApproximation.BinaryFraction.localGroupSourceScaleBlockAllocationRawBand source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi parentAllocation childAllocation initialAllocation currentAllocation
        draw drawAllocation eb query) (List.range count)

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {α : Type u_4} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R) (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ) (tableAllocation : ℕ → Fin M × TargetInterval target.length → ℕ) (integerAllocation : ℕ → TargetInterval target.length → ℕ)

def preparedLocalOnlineScaleSourceAllocationRawBand (e : ℕ) (query : OAI.EditApproximation.TargetInterval target.length) : ℕ := by
  exact
    let b := 2 ^ e
    let center := (OAI.EditApproximation.roundStateWithWork (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.seedGridSpacingWithWork b P).1)
      (OAI.EditApproximation.Lemmas.seedGridSpacingWithWork_pos b P hP) query).1
    OAI.EditApproximation.seedGridSpacingAllocation b P + OAI.EditApproximation.roundStateAllocation (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.seedGridSpacingWithWork b P).1) query +
      parentAllocation center + OAI.EditApproximation.BinaryFraction.centerEligibilityAllocation b F a (parentInitial center).1 + e +
      if (OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork b F a (parentInitial center).1).1 then
        integerAllocation b center + OAI.EditApproximation.BinaryFraction.preparedOnlineReadAllocationRaw source target parent P F exponent H b
          (Nat.two_pow_pos e) hP tau eta kappa child initial table R hc hi
          childAllocation initialAllocation tableAllocation t center (integer b center).1
      else 0

def preparedLocalOnlineActionsSourceAllocationRawBand (N : ℕ) (query : OAI.EditApproximation.TargetInterval target.length) : ℕ :=
  parentAllocation query + OAI.EditApproximation.BinaryFraction.queryExponentsAllocation N F a (parentInitial query).1 +
    OAI.EditApproximation.filterMapAllocation
      (fun e => OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceWithWorkRawBand source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t integer e query)
      (fun e => OAI.EditApproximation.BinaryFraction.preparedLocalOnlineScaleSourceAllocationRawBand source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t integer parentAllocation childAllocation initialAllocation
        tableAllocation integerAllocation e query)
      (OAI.EditApproximation.BinaryFraction.queryExponentsWithWork N F a (parentInitial query).1).1

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {α : Type u_4} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R) (parentAllocation : TargetInterval target.length → ℕ) (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)

def queryOnlineSelectAllocationRawBand (t : ℕ)
    (integer : ℕ → OAI.EditApproximation.TargetInterval target.length → ℕ × ℕ)
    (integerAllocation : ℕ → OAI.EditApproximation.TargetInterval target.length → ℕ)
    (keys : List (Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length)) (words : List OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval target.length) : ℕ :=
  OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsSourceAllocationRawBand source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial (OAI.EditApproximation.BinaryFraction.queryHistoryReadWithWork keys words) R hc hi (t - 1) integer
    parentAllocation childAllocation initialAllocation (OAI.EditApproximation.BinaryFraction.queryHistoryReadAllocation keys words)
    integerAllocation N q

def queryGroupSelectAllocationRawBand (draw : OAI.EditApproximation.CountedCellGroupDraws M F Q)
    (drawAllocation : OAI.EditApproximation.CellGroupSourceAllocations M F Q)
    (keys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) (words : List OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval target.length) : ℕ :=
  OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceAllocationRawBand source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial (OAI.EditApproximation.BinaryFraction.queryChildReadWithWork keys words) R hc hi
    parentAllocation childAllocation initialAllocation (OAI.EditApproximation.BinaryFraction.queryChildReadAllocation keys words)
    draw drawAllocation N q

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

noncomputable def integerBinaryWorkRawBand (source target : List ℤ) (N : ℕ) (epsilon : OAI.EditApproximation.BinaryFraction) :=
  OAI.EditApproximation.computedFullOutputWork (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N
    (OAI.EditApproximation.integerQueryLocalWorkRawBand source target N) (OAI.EditApproximation.integerPreevaluationWork source target N epsilon)
    (OAI.EditApproximation.computedQuerySetupWithWork N).2 (fun input => (OAI.EditApproximation.integerBinaryOutputRawBand source target N input).2)
    (N + 1)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter

def integerFinalAllocationRawBand (source target : List ℤ) (N : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N) : ℕ :=
  if source.map OAI.EditApproximation.integerSymbolCode = target.map OAI.EditApproximation.integerSymbolCode then 0 else
    OAI.EditApproximation.BinaryFraction.finalAnswerAllocation N
      (OAI.EditApproximation.computedQueryMemoResultRawBand (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N
        (OAI.EditApproximation.integerOccurrenceIndex source target) (OAI.EditApproximation.integerInputSymbolBits source target)
        (OAI.EditApproximation.integerInputPositionBits target) input).value

end OAI.EditApproximation

end


