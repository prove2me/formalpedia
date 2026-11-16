-- Prove2me | Definitions.Def_EditApproxScheme_17
-- name    : EditApproxScheme_17
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:57:48.5632+00:00
-- url     : https://prove2.me/theorems/74592266-02bd-475c-bb39-ff93ef7bf1b3
-- title:
--   Edit-distance approximation scheme, part 17 of 20: read footprints
-- statement:
--   This is **part 17 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains the storage footprints of the gather and read operations of the query programs: initial, band, group-source and online-source gathers, physical table reads, mean and scalar reads, restricted bodies, initial cone programs, charged reads, warmup programs, and seeds.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L10067-L10687 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 17 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_16

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

def queryInitialGatherFootprint
    {ι : Type u_1}
    {β : Type u_2}
    {n : ℕ}
    (N P F exponent : ℕ)
    (hP : 0 < P)
    (a : OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval n)
    (reader : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (hr : (key : OAI.EditApproximation.TargetInterval n) → (reader key).Footprint)
    (next : List (OAI.EditApproximation.TargetInterval n) →
  List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery ι β)
    (hn : (keys : List (OAI.EditApproximation.TargetInterval n)) →
  (words : List OAI.EditApproximation.BinaryFraction) → (next keys words).Footprint) : (OAI.EditApproximation.queryInitialGather N P F exponent hP a q reader next).Footprint :=
(hr q).bind
  (fun (value : OAI.EditApproximation.BinaryFraction) =>
    (OAI.EditApproximation.BitQuery.compute
          (OAI.EditApproximation.BinaryFraction.queryInitialSupportWithWork N P F exponent hP a value q)).bind
      fun (keys : List (OAI.EditApproximation.TargetInterval n)) =>
      OAI.EditApproximation.BitQuery.collect reader keys (next keys))
  fun (value : OAI.EditApproximation.BinaryFraction) =>
  (OAI.EditApproximation.BitQuery.Footprint.computeOf
        (OAI.EditApproximation.BinaryFraction.queryInitialSupportWithWork N P F exponent hP a value q)
        (OAI.EditApproximation.BinaryFraction.queryInitialSupportAllocation N P F exponent hP a value q)).bind
    (fun (keys : List (OAI.EditApproximation.TargetInterval n)) =>
      OAI.EditApproximation.BitQuery.collect reader keys (next keys))
    fun (keys : List (OAI.EditApproximation.TargetInterval n)) =>
    OAI.EditApproximation.BitQuery.Footprint.collect reader hr keys (next keys) (hn keys)

def queryBandGatherFootprint
    {ι : Type u_1}
    {β : Type u_2}
    {nx ny : ℕ}
    (M : ℕ)
    (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F exponent : ℕ)
    (hP : 0 < P)
    (a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : OAI.EditApproximation.TargetInterval ny → ℕ)
    (q : OAI.EditApproximation.TargetInterval ny)
    (massReader initialReader : Fin M × OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (hm : (key : Fin M × OAI.EditApproximation.TargetInterval ny) → (massReader key).Footprint)
    (hi : (key : Fin M × OAI.EditApproximation.TargetInterval ny) → (initialReader key).Footprint)
    (next : List (Fin M × OAI.EditApproximation.TargetInterval ny) →
  List OAI.EditApproximation.BinaryFraction →
    List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery ι β)
    (hn : (keys : List (Fin M × OAI.EditApproximation.TargetInterval ny)) →
  (mass words : List OAI.EditApproximation.BinaryFraction) → (next keys mass words).Footprint) : (OAI.EditApproximation.queryBandGather M parent N P F exponent hP a initial q massReader initialReader next).Footprint :=
(OAI.EditApproximation.BitQuery.Footprint.computeOf
      (OAI.EditApproximation.BinaryFraction.queryBandInputsWithWork M parent N P F exponent hP a initial q)
      (OAI.EditApproximation.BinaryFraction.queryBandInputsAllocation M parent N P F exponent hP a initial allocation
        q)).bind
  (fun (keys : List (Fin M × OAI.EditApproximation.TargetInterval ny)) =>
    OAI.EditApproximation.BitQuery.collect massReader keys fun (mass : List OAI.EditApproximation.BinaryFraction) =>
      OAI.EditApproximation.BitQuery.collect initialReader keys (next keys mass))
  fun (keys : List (Fin M × OAI.EditApproximation.TargetInterval ny)) =>
  OAI.EditApproximation.BitQuery.Footprint.collect massReader hm keys
    (fun (mass : List OAI.EditApproximation.BinaryFraction) =>
      OAI.EditApproximation.BitQuery.collect initialReader keys (next keys mass))
    fun (mass : List OAI.EditApproximation.BinaryFraction) =>
    OAI.EditApproximation.BitQuery.Footprint.collect initialReader hi keys (next keys mass) (hn keys mass)

def queryGroupSourceGatherFootprint
    {ι : Type u_1}
    {β : Type u_2}
    {n : ℕ}
    (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : OAI.EditApproximation.TargetInterval n → ℕ)
    (q : OAI.EditApproximation.TargetInterval n)
    (reader : OAI.EditApproximation.GroupScalarKey M F Q → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (hr : (key : OAI.EditApproximation.GroupScalarKey M F Q) → (reader key).Footprint)
    (next : List (OAI.EditApproximation.GroupScalarKey M F Q) →
  List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery ι β)
    (hn : (keys : List (OAI.EditApproximation.GroupScalarKey M F Q)) →
  (words : List OAI.EditApproximation.BinaryFraction) → (next keys words).Footprint) : (OAI.EditApproximation.queryGroupSourceGather M N F Q exponent eM eF hM hF a initial q reader next).Footprint :=
OAI.EditApproximation.BitQuery.Footprint.chargeOf (allocation q)
  ((OAI.EditApproximation.BitQuery.Footprint.computeOf
        (OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (initial q).1
          q)
        (OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysAllocation M N F Q exponent eM eF hM hF a
          (initial q).1 q)).bind
    (fun (keys : List (OAI.EditApproximation.GroupScalarKey M F Q)) =>
      OAI.EditApproximation.BitQuery.collect reader keys (next keys))
    fun (keys : List (OAI.EditApproximation.GroupScalarKey M F Q)) =>
    OAI.EditApproximation.BitQuery.Footprint.collect reader hr keys (next keys) (hn keys))

def queryOnlineSourceGatherFootprint
    {ι : Type u_1}
    {β : Type u_2}
    {nx ny M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F exponent H : ℕ)
    (hP : 0 < P)
    (tau a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (initialAllocation : OAI.EditApproximation.TargetInterval ny → ℕ)
    (child : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (childAllocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ)
    (q : OAI.EditApproximation.TargetInterval ny)
    (reader : ℕ × OAI.EditApproximation.TargetInterval ny → ℕ → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (hr : (key : ℕ × OAI.EditApproximation.TargetInterval ny) → (range : ℕ) → (reader key range).Footprint)
    (next : List (ℕ × OAI.EditApproximation.TargetInterval ny) →
  List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery ι β)
    (hn : (keys : List (ℕ × OAI.EditApproximation.TargetInterval ny)) →
  (words : List OAI.EditApproximation.BinaryFraction) → (next keys words).Footprint) : (OAI.EditApproximation.queryOnlineSourceGather parent N P F exponent H hP tau a initial child q reader next).Footprint :=
OAI.EditApproximation.BitQuery.Footprint.chargeOf (initialAllocation q)
  ((OAI.EditApproximation.BitQuery.Footprint.computeOf
        (OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork N P F hP a (initial q).1 q)
        (OAI.EditApproximation.BinaryFraction.queryOnlineKeysAllocation N P F hP a (initial q).1 q)).bind
    (fun (keys : List (ℕ × OAI.EditApproximation.TargetInterval ny)) =>
      OAI.EditApproximation.BitQuery.collect
        (fun (key : ℕ × OAI.EditApproximation.TargetInterval ny) =>
          (OAI.EditApproximation.BitQuery.compute
                (OAI.EditApproximation.BinaryFraction.queryOnlineRangeWithWork parent P exponent H tau child key)).bind
            (reader key))
        keys (next keys))
    fun (keys : List (ℕ × OAI.EditApproximation.TargetInterval ny)) =>
    OAI.EditApproximation.BitQuery.Footprint.collect
      (fun (key : ℕ × OAI.EditApproximation.TargetInterval ny) =>
        (OAI.EditApproximation.BitQuery.compute
              (OAI.EditApproximation.BinaryFraction.queryOnlineRangeWithWork parent P exponent H tau child key)).bind
          (reader key))
      (fun (key : ℕ × OAI.EditApproximation.TargetInterval ny) =>
        (OAI.EditApproximation.BitQuery.Footprint.computeOf
              (OAI.EditApproximation.BinaryFraction.queryOnlineRangeWithWork parent P exponent H tau child key)
              (OAI.EditApproximation.BinaryFraction.queryOnlineRangeAllocation parent P exponent H tau child
                childAllocation key)).bind
          (reader key) (hr key))
      keys (next keys) (hn keys))

def queryPhysicalTableReadFootprint
    {M J n : ℕ}
    (copies T S : ℕ)
    (parent : OAI.EditApproximation.PhysicalTableRequest M J n)
    (child : { r : OAI.EditApproximation.PhysicalTableRequest M J n //
  OAI.EditApproximation.PhysicalTableRequest.combinedRank T S r <
    OAI.EditApproximation.PhysicalTableRequest.combinedRank T S parent }) : (OAI.EditApproximation.queryPhysicalTableRead copies T S parent child).Footprint :=
OAI.EditApproximation.BitQuery.Footprint.chargeOf (OAI.EditApproximation.physicalTableCodeAllocation (M := M) (J := J) (n := n) child.val + 1)
  (OAI.EditApproximation.BitQuery.Footprint.read child OAI.EditApproximation.BitQuery.done
    fun (word : OAI.EditApproximation.BinaryFraction) => OAI.EditApproximation.BitQuery.Footprint.done word)

def queryMeanReadFootprint
    {ι : Type u_1}
    (count : ℕ)
    (reader : Fin count → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (hr : (i : Fin count) → (reader i).Footprint) : (OAI.EditApproximation.queryMeanRead count reader).Footprint :=
OAI.EditApproximation.BitQuery.Footprint.chargeOf count
  (OAI.EditApproximation.BitQuery.Footprint.collect reader hr (List.ofFn fun (i : Fin count) => i)
    (fun (words : List OAI.EditApproximation.BinaryFraction) =>
      OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryMeanWithWork count words))
    fun (words : List OAI.EditApproximation.BinaryFraction) =>
    OAI.EditApproximation.BitQuery.Footprint.computeOf
      (OAI.EditApproximation.BinaryFraction.queryMeanWithWork count words)
      (OAI.EditApproximation.BinaryFraction.sumListAllocation words +
          (OAI.EditApproximation.BinaryFraction.sumListWithWork words).1.divAllocation
            (OAI.EditApproximation.BinaryFraction.nat count) +
        count.size))

def queryPhysicalScalarReadFootprint
    (M J N n exponent F Q R B : ℕ)
    (key : OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) : (OAI.EditApproximation.queryPhysicalScalarRead M J N n exponent F Q R B key).Footprint :=
OAI.EditApproximation.BitQuery.Footprint.chargeOf (OAI.EditApproximation.physicalScalarCodeAllocation key + 1)
  (OAI.EditApproximation.BitQuery.Footprint.read key OAI.EditApproximation.BitQuery.done
    fun (word : OAI.EditApproximation.BinaryFraction) => OAI.EditApproximation.BitQuery.Footprint.done word)

def queryRestrictPhysicalBodyFootprint
    {σ : Type u_1}
    {M J n : ℕ}
    (passes copies T S : ℕ)
    (parent : { r : OAI.EditApproximation.PhysicalTableRequest M J n //
  OAI.EditApproximation.PhysicalTableRequest.Bounded passes copies T S r })
    (program : OAI.EditApproximation.BitQuery (OAI.EditApproximation.QueryPhysicalChild (σ := σ) passes copies T S parent)
  OAI.EditApproximation.BinaryFraction)
    (heap : program.Footprint) : (OAI.EditApproximation.queryRestrictPhysicalBody passes copies T S parent program).Footprint := by
  exact
    (heap.restrictWithWork _ _ (OAI.EditApproximation.Lemmas.querySupportedChildWithWork_value passes copies T S parent)
      (OAI.EditApproximation.querySupportedChildAllocation passes copies T S parent)
      ).mapKeysWithWork _ (fun _ => 1)

def queryInitialConeProgramAtFootprint
    {ι : Type u_1}
    {n : ℕ}
    (sourceLength N P F : ℕ)
    (A a : OAI.EditApproximation.BinaryFraction)
    (reader : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval n)
    (hr : (r : OAI.EditApproximation.TargetInterval n) → (reader r).Footprint) : (OAI.EditApproximation.queryInitialConeProgramAt sourceLength N P F A a reader q).Footprint :=
(hr q).bind
  (fun (value : OAI.EditApproximation.BinaryFraction) =>
    (OAI.EditApproximation.BitQuery.compute
          (OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork N P A value q)).bind
      fun (keys : List (OAI.EditApproximation.TargetInterval n)) =>
      OAI.EditApproximation.BitQuery.collect reader keys fun (words : List OAI.EditApproximation.BinaryFraction) =>
        OAI.EditApproximation.BitQuery.compute
          (OAI.EditApproximation.BinaryFraction.cachedInitialProgramReadWithWork sourceLength N P F A a
            (value.queryInitialSeedReadWithWork q keys words) q))
  fun (value : OAI.EditApproximation.BinaryFraction) =>
  (OAI.EditApproximation.BitQuery.Footprint.computeOf
        (OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork N P A value q)
        (OAI.EditApproximation.BinaryFraction.queryInitialConeCentersAllocation N P A value q)).bind
    (fun (keys : List (OAI.EditApproximation.TargetInterval n)) =>
      OAI.EditApproximation.BitQuery.collect reader keys fun (words : List OAI.EditApproximation.BinaryFraction) =>
        OAI.EditApproximation.BitQuery.compute
          (OAI.EditApproximation.BinaryFraction.cachedInitialProgramReadWithWork sourceLength N P F A a
            (value.queryInitialSeedReadWithWork q keys words) q))
    fun (keys : List (OAI.EditApproximation.TargetInterval n)) =>
    OAI.EditApproximation.BitQuery.Footprint.collect reader hr keys
      (fun (words : List OAI.EditApproximation.BinaryFraction) =>
        OAI.EditApproximation.BitQuery.compute
          (OAI.EditApproximation.BinaryFraction.cachedInitialProgramReadWithWork sourceLength N P F A a
            (value.queryInitialSeedReadWithWork q keys words) q))
      fun (words : List OAI.EditApproximation.BinaryFraction) =>
      OAI.EditApproximation.BitQuery.Footprint.computeOf
        (OAI.EditApproximation.BinaryFraction.cachedInitialProgramReadWithWork sourceLength N P F A a
          (value.queryInitialSeedReadWithWork q keys words) q)
        (OAI.EditApproximation.BinaryFraction.cachedInitialProgramReadAllocation
          (value.queryInitialSeedReadWithWork q keys words) (value.queryInitialSeedReadAllocation q keys words)
          sourceLength N P F A a q)

def queryChargedReadFootprint
    {M J n passes copies T S : ℕ}
    (parent : { r : OAI.EditApproximation.PhysicalTableRequest M J n //
  OAI.EditApproximation.PhysicalTableRequest.Bounded passes copies T S r })
    (key : { child : OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S //
  child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (Sum.inr parent) }) : (OAI.EditApproximation.queryChargedRead parent key).Footprint :=
OAI.EditApproximation.BitQuery.Footprint.chargeOf (OAI.EditApproximation.chargedPhysicalCodeAllocation (M := M) (J := J) (n := n) (passes := passes) (copies := copies) (T := T) (S := S) key.val + 1)
  (OAI.EditApproximation.BitQuery.Footprint.read key OAI.EditApproximation.BitQuery.done
    fun (word : OAI.EditApproximation.BinaryFraction) => OAI.EditApproximation.BitQuery.Footprint.done word)

def queryWarmupProgramFootprint
    {ι : Type u_1}
    {nx ny M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F : ℕ)
    (a : OAI.EditApproximation.BinaryFraction)
    (initialRead : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (childRead : Fin M × OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval ny)
    (hi : (r : OAI.EditApproximation.TargetInterval ny) → (initialRead r).Footprint)
    (hc : (key : Fin M × OAI.EditApproximation.TargetInterval ny) → (childRead key).Footprint) : (OAI.EditApproximation.queryWarmupProgram parent N P F a initialRead childRead q).Footprint :=
(hi q).bind
  (fun (value : OAI.EditApproximation.BinaryFraction) =>
    (OAI.EditApproximation.BitQuery.compute
          (OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork N P F a value q)).bind
      fun (centers : List (OAI.EditApproximation.TargetInterval ny)) =>
      OAI.EditApproximation.BitQuery.collect initialRead centers
        fun (words : List OAI.EditApproximation.BinaryFraction) =>
        have initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ :=
          value.queryOverrideParentReadWithWork q centers words;
        (OAI.EditApproximation.BitQuery.compute
              (OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork M parent N P F a initial q)).bind
          fun (inputs : List (Fin M × OAI.EditApproximation.TargetInterval ny)) =>
          OAI.EditApproximation.BitQuery.collect childRead inputs
            fun (childWords : List OAI.EditApproximation.BinaryFraction) =>
            OAI.EditApproximation.BitQuery.compute
              (OAI.EditApproximation.BinaryFraction.localWarmupReadKernelWithWork parent N P F a initial
                (fun (input : Fin M × OAI.EditApproximation.TargetInterval ny) =>
                  OAI.EditApproximation.BinaryFraction.queryChildReadWithWork inputs childWords input.1 input.2)
                q))
  fun (value : OAI.EditApproximation.BinaryFraction) =>
  (OAI.EditApproximation.BitQuery.Footprint.computeOf
        (OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork N P F a value q)
        (OAI.EditApproximation.BinaryFraction.queryRawCentersAllocation N P F a value q)).bind
    (fun (centers : List (OAI.EditApproximation.TargetInterval ny)) =>
      OAI.EditApproximation.BitQuery.collect initialRead centers
        fun (words : List OAI.EditApproximation.BinaryFraction) =>
        have initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ :=
          value.queryOverrideParentReadWithWork q centers words;
        (OAI.EditApproximation.BitQuery.compute
              (OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork M parent N P F a initial q)).bind
          fun (inputs : List (Fin M × OAI.EditApproximation.TargetInterval ny)) =>
          OAI.EditApproximation.BitQuery.collect childRead inputs
            fun (childWords : List OAI.EditApproximation.BinaryFraction) =>
            OAI.EditApproximation.BitQuery.compute
              (OAI.EditApproximation.BinaryFraction.localWarmupReadKernelWithWork parent N P F a initial
                (fun (input : Fin M × OAI.EditApproximation.TargetInterval ny) =>
                  OAI.EditApproximation.BinaryFraction.queryChildReadWithWork inputs childWords input.1 input.2)
                q))
    fun (centers : List (OAI.EditApproximation.TargetInterval ny)) =>
    OAI.EditApproximation.BitQuery.Footprint.collect initialRead hi centers
      (fun (words : List OAI.EditApproximation.BinaryFraction) =>
        have initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ :=
          value.queryOverrideParentReadWithWork q centers words;
        (OAI.EditApproximation.BitQuery.compute
              (OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork M parent N P F a initial q)).bind
          fun (inputs : List (Fin M × OAI.EditApproximation.TargetInterval ny)) =>
          OAI.EditApproximation.BitQuery.collect childRead inputs
            fun (childWords : List OAI.EditApproximation.BinaryFraction) =>
            OAI.EditApproximation.BitQuery.compute
              (OAI.EditApproximation.BinaryFraction.localWarmupReadKernelWithWork parent N P F a initial
                (fun (input : Fin M × OAI.EditApproximation.TargetInterval ny) =>
                  OAI.EditApproximation.BinaryFraction.queryChildReadWithWork inputs childWords input.1 input.2)
                q))
      fun (words : List OAI.EditApproximation.BinaryFraction) =>
      let initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ :=
        value.queryOverrideParentReadWithWork q centers words;
      let allocation : OAI.EditApproximation.TargetInterval ny → ℕ :=
        OAI.EditApproximation.BinaryFraction.queryOverrideParentReadAllocation q centers words;
      (OAI.EditApproximation.BitQuery.Footprint.computeOf
            (OAI.EditApproximation.BinaryFraction.queryWarmupInputsWithWork M parent N P F a initial q)
            (OAI.EditApproximation.BinaryFraction.queryWarmupInputsAllocation M parent N P F a initial allocation
              q)).bind
        (fun (inputs : List (Fin M × OAI.EditApproximation.TargetInterval ny)) =>
          OAI.EditApproximation.BitQuery.collect childRead inputs
            fun (childWords : List OAI.EditApproximation.BinaryFraction) =>
            OAI.EditApproximation.BitQuery.compute
              (OAI.EditApproximation.BinaryFraction.localWarmupReadKernelWithWork parent N P F a
                (value.queryOverrideParentReadWithWork q centers words)
                (fun (input : Fin M × OAI.EditApproximation.TargetInterval ny) =>
                  OAI.EditApproximation.BinaryFraction.queryChildReadWithWork inputs childWords input.1 input.2)
                q))
        fun (inputs : List (Fin M × OAI.EditApproximation.TargetInterval ny)) =>
        OAI.EditApproximation.BitQuery.Footprint.collect childRead hc inputs
          (fun (childWords : List OAI.EditApproximation.BinaryFraction) =>
            OAI.EditApproximation.BitQuery.compute
              (OAI.EditApproximation.BinaryFraction.localWarmupReadKernelWithWork parent N P F a
                (value.queryOverrideParentReadWithWork q centers words)
                (fun (input : Fin M × OAI.EditApproximation.TargetInterval ny) =>
                  OAI.EditApproximation.BinaryFraction.queryChildReadWithWork inputs childWords input.1 input.2)
                q))
          fun (childWords : List OAI.EditApproximation.BinaryFraction) =>
          OAI.EditApproximation.BitQuery.Footprint.computeOf
            (OAI.EditApproximation.BinaryFraction.localWarmupReadKernelWithWork parent N P F a initial
              (fun (input : Fin M × OAI.EditApproximation.TargetInterval ny) =>
                OAI.EditApproximation.BinaryFraction.queryChildReadWithWork inputs childWords input.1 input.2)
              q)
            (OAI.EditApproximation.BinaryFraction.localWarmupReadAllocation parent N P F a initial allocation
              (fun (input : Fin M × OAI.EditApproximation.TargetInterval ny) =>
                OAI.EditApproximation.BinaryFraction.queryChildReadWithWork inputs childWords input.1 input.2)
              (fun (input : Fin M × OAI.EditApproximation.TargetInterval ny) =>
                OAI.EditApproximation.BinaryFraction.queryChildReadAllocation inputs childWords input.1 input.2)
              q)

def queryPhysicalEarlierReadFootprint
    {M J n : ℕ}
    (copies pass copy T S t : ℕ)
    (node : OAI.EditApproximation.PhysicalNode M J)
    (hbelow : ↑node.fst < J)
    (q : OAI.EditApproximation.TargetInterval n)
    (input : Fin M × ℕ × OAI.EditApproximation.TargetInterval n) : (OAI.EditApproximation.queryPhysicalEarlierRead copies pass copy T S t node hbelow q input).Footprint := by
  refine OAI.EditApproximation.BitQuery.Footprint.chargeOf (input.2.1.bits.length + t.bits.length) ?_
  split
  · exact OAI.EditApproximation.queryPhysicalTableReadFootprint copies T S _ _
  · exact .done _

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

open Finset

def queryPhysicalScalarOnlineReadFootprint
    (M J N n exponent F Q R B : ℕ)
    (node : OAI.EditApproximation.PhysicalInternalNode M J)
    (time : Fin R)
    (key : ℕ × OAI.EditApproximation.TargetInterval n)
    (range : ℕ) : (OAI.EditApproximation.queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range).Footprint := by
  refine OAI.EditApproximation.BitQuery.Footprint.chargeOf
    (OAI.EditApproximation.queryScalePresentAllocation N key.1 + OAI.EditApproximation.queryRangeValidAllocation B range) ?_
  split
  · split
    · exact OAI.EditApproximation.queryPhysicalScalarReadFootprint M J N n exponent F Q R B _
    · exact .done _
  · exact .done _

def queryChargedSeedAtFootprint
    {M J n passes copies T S : ℕ}
    (parent : { r : OAI.EditApproximation.PhysicalTableRequest M J n //
  OAI.EditApproximation.PhysicalTableRequest.Bounded passes copies T S r })
    (N : ℕ)
    (multiplier : ℕ → ℕ)
    (q : OAI.EditApproximation.TargetInterval n) : (OAI.EditApproximation.queryChargedSeedAt parent N multiplier q).Footprint := by
  refine OAI.EditApproximation.BitQuery.Footprint.chargeOf (OAI.EditApproximation.naturalEqualAllocation parent.val.pass 0) ?_
  split
  · exact OAI.EditApproximation.queryChargedReadFootprint parent _
  · refine OAI.EditApproximation.BitQuery.Footprint.chargeOf copies ?_
    refine OAI.EditApproximation.BitQuery.Footprint.collect _ (fun _ => OAI.EditApproximation.queryChargedReadFootprint parent _) _ _ fun words => ?_
    let factor := multiplier (parent.val.pass - 1)
    exact OAI.EditApproximation.BitQuery.Footprint.computeOf (OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork N factor words)
      (OAI.EditApproximation.BinaryFraction.seedMedianAllocation N factor words +
        (OAI.EditApproximation.BinaryFraction.seedMedianWithWork N factor words).1.length + 1)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

def queryFamilyOnlineReadFootprint
    {α : Type u_1}
    {M J R : ℕ}
    (target : List α)
    (N P F exponent H Q passes copies pass copy : ℕ)
    (node : OAI.EditApproximation.PhysicalInternalNode M J)
    (time : Fin R)
    (key : ℕ × OAI.EditApproximation.TargetInterval target.length)
    (range : ℕ) : (OAI.EditApproximation.queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key
    range).Footprint :=
OAI.EditApproximation.BitQuery.Footprint.mapKeysWithWork
  (OAI.EditApproximation.queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy)
  (OAI.EditApproximation.queryFamilyTagAllocation target N P F exponent H Q passes copies pass copy)
  (OAI.EditApproximation.queryPhysicalScalarOnlineReadFootprint M J N target.length exponent F Q R
    (OAI.EditApproximation.localOnlineMassBound M P H) node time key range)

def queryPhysicalInitialFootprint
    (source target : List ℕ)
    {M J passes copies T S : ℕ}
    (N P F : ℕ)
    (A a : OAI.EditApproximation.BinaryFraction)
    (multiplier : ℕ → ℕ)
    (parent : { r : OAI.EditApproximation.PhysicalTableRequest M J target.length //
  OAI.EditApproximation.PhysicalTableRequest.Bounded passes copies T S r })
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts)
    (symbolBits positionBits : ℕ)
    (q : OAI.EditApproximation.TargetInterval target.length) : (OAI.EditApproximation.queryPhysicalInitial source target N P F A a multiplier parent occurrence symbolBits positionBits
    q).Footprint := by
  let interval := OAI.EditApproximation.physicalSourceInterval source.length parent.val.node
  refine OAI.EditApproximation.BitQuery.Footprint.chargeOf (OAI.EditApproximation.saturatingSubtractAllocation interval.hi interval.lo +
    OAI.EditApproximation.naturalWordLEAllocation (OAI.EditApproximation.saturatingSubtractWithWork interval.hi interval.lo).1 [true]) ?_
  split
  · exact OAI.EditApproximation.BitQuery.Footprint.computeOf _
      (OAI.EditApproximation.queryIndexedSliceAllocation source interval target.length q occurrence symbolBits positionBits)
  · exact OAI.EditApproximation.queryInitialConeProgramAtFootprint _ N P F A a (OAI.EditApproximation.queryChargedSeedAt parent N multiplier) q
      (OAI.EditApproximation.queryChargedSeedAtFootprint parent N multiplier)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

open Finset

open MeasureTheory ProbabilityTheory

def queryPhysicalScalarGroupQueriesFootprint (M J N n exponent F Q R B : ℕ)
    (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R) (b : ℕ) (cell : ℕ × ℕ) :
    ∀ s j, OAI.EditApproximation.BitQuery.Footprint
      (OAI.EditApproximation.queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time b cell s j) := by
  have groupTransport (b c : ℕ) (h : b = c)
      (actual : OAI.EditApproximation.BitPhysicalGroupQueries M J N n exponent F Q R B b)
      (heap : ∀ s j, OAI.EditApproximation.BitQuery.Footprint (actual s j)) :
      ∀ s j, OAI.EditApproximation.BitQuery.Footprint
        ((Eq.mp (congrArg (OAI.EditApproximation.BitPhysicalGroupQueries M J N n exponent F Q R B) h) actual) s j) := by
    cases h
    exact heap
  intro s j
  unfold OAI.EditApproximation.queryPhysicalScalarGroupQueries
  split
  · rename_i hb
    split
    · exact groupTransport _ _
        (OAI.EditApproximation.Lemmas.physicalScaleIndex_get N b ((OAI.EditApproximation.Lemmas.queryScalePresentWithWork_value N b).mp hb)) _
        (fun _ _ => OAI.EditApproximation.queryPhysicalScalarReadFootprint M J N n exponent F Q R B _) s j
    · exact .done _
  · exact .done _

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

def queryPhysicalScalarGroupReadFootprint
    (M J N n exponent F Q R B : ℕ)
    (node : OAI.EditApproximation.PhysicalInternalNode M J)
    (time : Fin R)
    (key : OAI.EditApproximation.GroupScalarKey M F Q) : (OAI.EditApproximation.queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key).Footprint :=
OAI.EditApproximation.BitQuery.Footprint.chargeOf
  (OAI.EditApproximation.queryScalePresentAllocation N key.fst.1 +
    OAI.EditApproximation.queryCellValidAllocation n exponent key.fst.2)
  (OAI.EditApproximation.queryPhysicalScalarGroupQueriesFootprint M J N n exponent F Q R B node time key.fst.1 key.fst.2
    key.snd.fst key.snd.snd)

def queryFamilyGroupReadFootprint
    {α : Type u_1}
    {M J R : ℕ}
    (target : List α)
    (N P F exponent H Q passes copies pass copy : ℕ)
    (node : OAI.EditApproximation.PhysicalInternalNode M J)
    (time : Fin R)
    (key : OAI.EditApproximation.GroupScalarKey M F Q) : (OAI.EditApproximation.queryFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).Footprint :=
OAI.EditApproximation.BitQuery.Footprint.mapKeysWithWork
  (OAI.EditApproximation.queryFamilyTagWithWork target N P F exponent H Q passes copies pass copy)
  (OAI.EditApproximation.queryFamilyTagAllocation target N P F exponent H Q passes copies pass copy)
  (OAI.EditApproximation.queryPhysicalScalarGroupReadFootprint M J N target.length exponent F Q R
    (OAI.EditApproximation.localOnlineMassBound M P H) node time key)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

open Finset

def queryChargedWarmupFootprint
    (source target : List ℕ)
    {M J passes copies T S : ℕ}
    (N P F : ℕ)
    (A a : OAI.EditApproximation.BinaryFraction)
    (multiplier : ℕ → ℕ)
    (parent : { r : OAI.EditApproximation.PhysicalTableRequest M J target.length //
  OAI.EditApproximation.PhysicalTableRequest.Bounded passes copies T S r })
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts)
    (symbolBits positionBits : ℕ) : (OAI.EditApproximation.queryChargedWarmup source target N P F A a multiplier parent occurrence symbolBits
    positionBits).Footprint := by
  have hinit := OAI.EditApproximation.queryPhysicalInitialFootprint source target N P F A a multiplier parent occurrence
    symbolBits positionBits
  unfold OAI.EditApproximation.queryChargedWarmup
  refine OAI.EditApproximation.BitQuery.Footprint.chargeOf (OAI.EditApproximation.naturalEqualAllocation parent.val.index 0) ?_
  split
  · exact hinit _
  · refine OAI.EditApproximation.BitQuery.Footprint.chargeOf (parent.val.node.1.val.bits.length + J.bits.length) ?_
    split
    · let interval := OAI.EditApproximation.physicalSourceInterval source.length parent.val.node
      refine OAI.EditApproximation.BitQuery.Footprint.chargeOf (OAI.EditApproximation.saturatingSubtractAllocation interval.hi interval.lo +
        OAI.EditApproximation.naturalWordLEAllocation (OAI.EditApproximation.saturatingSubtractWithWork interval.hi interval.lo).1 [true]) ?_
      split
      · exact hinit _
      · apply OAI.EditApproximation.queryWarmupProgramFootprint
        · exact hinit
        · intro input
          exact OAI.EditApproximation.queryChargedReadFootprint parent _
    · exact hinit _

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {α : Type u_4} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

open Finset

def preparedComputedCellSourceWithWorkRawBand (b eb : ℕ) (hb : b = 2 ^ eb)
    (draw : ∀ t : Fin (OAI.EditApproximation.groupDyadicScales M b (OAI.EditApproximation.BinaryFraction.nat F).value).length,
      Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b (OAI.EditApproximation.BinaryFraction.nat F).value t)) → Fin M × ℕ)
    (cell : ℕ × ℕ) :
    Option (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
      (Fin M × OAI.EditApproximation.TargetInterval target.length) M) × ℕ := by
  exact
    let scales := OAI.EditApproximation.BinaryFraction.groupScalesWithWork eM eb eF
    let result := OAI.EditApproximation.BinaryFraction.preparedCellGroupSourceWithWorkRaw source target parent b P F exponent Q
      (by rw [hb]; exact Nat.two_pow_pos eb) hP tau a parentInitial child initial current
      R R hc hi scales.1 (OAI.EditApproximation.Lemmas.computedGroupScales_value M b F eM eb eF hM hb hF) draw cell
    (result.1, scales.2 + result.2 + 1)

def preparedLocalGroupScaleSourceWithWorkRawBand (eb : ℕ)
    (draw : OAI.EditApproximation.CellGroupReadDraws M F Q) (query : OAI.EditApproximation.TargetInterval target.length) :
    List (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
      (Fin M × OAI.EditApproximation.TargetInterval target.length) M) × ℕ := by
  exact
    let b := 2 ^ eb
    let word := parentInitial query
    let side := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat b)
    let radius := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork word.1
    let cells := OAI.EditApproximation.BinaryFraction.targetCellsWithWork side.1 (OAI.EditApproximation.bitWordValue radius.1) query
    let selected := OAI.EditApproximation.filterMapWithWork (fun cell =>
      OAI.EditApproximation.BinaryFraction.preparedComputedCellSourceWithWorkRawBand source target parent P F exponent Q eM eF hM hF hP tau a
        parentInitial child initial current R hc hi b eb rfl
        (Eq.mpr (congrArg (OAI.EditApproximation.cellScaleReadDraw M b Q) (OAI.EditApproximation.Lemmas.nat_value F)) (draw b cell)) cell) cells.1
    (selected.1, word.2 + side.2 + radius.2 + cells.2 + selected.2 + eb + 4)

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {α : Type u_4} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (P F exponent Q eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hP : 0 < P) (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction × ℕ) (child initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ) (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)

def preparedLocalCellGroupsSourceWithWorkRawBand (N : ℕ)
    (draw : OAI.EditApproximation.CellGroupReadDraws M F Q) (query : OAI.EditApproximation.TargetInterval target.length) :
    List (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
      (Fin M × OAI.EditApproximation.TargetInterval target.length) M) × ℕ :=
  let count := max 1 N.bits.length
  let word := parentInitial query
  let groups := OAI.EditApproximation.arithmeticFlatMapWithWork (fun eb =>
    let guard := OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork F (2 ^ eb) a word.1
    if guard.1 then
      let selected := OAI.EditApproximation.BinaryFraction.preparedLocalGroupScaleSourceWithWorkRawBand source target parent P F exponent Q eM eF
        hM hF hP tau a parentInitial child initial current R hc hi eb draw query
      (selected.1, guard.2 + selected.2 + eb + 4)
    else ([], guard.2 + eb + 4)) (List.range count)
  (groups.1, word.2 + groups.2 + count + N.bits.length + 2)

end OAI.EditApproximation.BinaryFraction

end


