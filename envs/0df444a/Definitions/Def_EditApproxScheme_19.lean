-- Prove2me | Definitions.Def_EditApproxScheme_19
-- name    : EditApproxScheme_19
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T17:02:03.61271+00:00
-- url     : https://prove2.me/theorems/b261a1ab-767b-4c38-aed2-ebe69db23cfa
-- title:
--   Edit-distance approximation scheme, part 19 of 20: local raw-band footprints
-- statement:
--   This is **part 19 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains the raw-band storage footprints of local refinement, local random sources, and local bands.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L11400-L11779 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 19 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_18

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

def queryLocalRefinementFootprintRawBand
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (t : ℕ)
    (parentInitial : OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
    (child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
    (R : ℕ)
    (hc : ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval target.length), (child i r).2 ≤ R)
    (hi : ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval target.length), (initial i r).2 ≤ R)
    (draw : OAI.EditApproximation.CountedCellGroupDraws M F Q)
    (integer : ℕ → OAI.EditApproximation.TargetInterval target.length → ℕ × ℕ)
    (parentAllocation : OAI.EditApproximation.TargetInterval target.length → ℕ)
    (childAllocation initialAllocation : Fin M → OAI.EditApproximation.TargetInterval target.length → ℕ)
    (drawAllocation : OAI.EditApproximation.CountedCellGroupAllocations M F Q)
    (integerAllocation : ℕ → OAI.EditApproximation.TargetInterval target.length → ℕ)
    (q : OAI.EditApproximation.TargetInterval target.length)
    (readEarlier : Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readCurrent : Fin M × OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (he : (key : Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × OAI.EditApproximation.TargetInterval target.length) → (readCurrent key).Footprint) : (OAI.EditApproximation.queryLocalRefinementRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
    t parentInitial child initial R hc hi draw integer q readEarlier readCurrent).Footprint :=
(OAI.EditApproximation.BitQuery.Footprint.computeOf
      (OAI.EditApproximation.BinaryFraction.queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q)
      (OAI.EditApproximation.BinaryFraction.queryEarlierInputsAllocation M parent N P F exponent t hP a parentInitial
        parentAllocation q)).bind
  (fun (earlierKeys : List (Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length)) =>
    OAI.EditApproximation.BitQuery.collect readEarlier earlierKeys
      fun (earlierWords : List OAI.EditApproximation.BinaryFraction) =>
      (OAI.EditApproximation.BitQuery.compute
            (OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand source target parent N P F exponent H hP tau
              a eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)).bind
        fun
          (onlineActions :
            List
              (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
                (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
        have word : OAI.EditApproximation.BinaryFraction × ℕ := parentInitial q;
        OAI.EditApproximation.BitQuery.charge word.2
          ((OAI.EditApproximation.BitQuery.compute
                (OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                  word.1 q draw)).bind
            fun (sharedKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
            OAI.EditApproximation.BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List OAI.EditApproximation.BinaryFraction) =>
              (OAI.EditApproximation.BitQuery.compute
                    (OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
                        (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
                (OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.queryNeededInputsWithWork selectedActions onlineActions)).bind
                  fun (currentKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
                  OAI.EditApproximation.BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List OAI.EditApproximation.BinaryFraction) =>
                    OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions onlineActions currentKeys currentWords
                        q)))
  fun (earlierKeys : List (Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length)) =>
  OAI.EditApproximation.BitQuery.Footprint.collect readEarlier he earlierKeys
    (fun (earlierWords : List OAI.EditApproximation.BinaryFraction) =>
      (OAI.EditApproximation.BitQuery.compute
            (OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand source target parent N P F exponent H hP tau
              a eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)).bind
        fun
          (onlineActions :
            List
              (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
                (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
        have word : OAI.EditApproximation.BinaryFraction × ℕ := parentInitial q;
        OAI.EditApproximation.BitQuery.charge word.2
          ((OAI.EditApproximation.BitQuery.compute
                (OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                  word.1 q draw)).bind
            fun (sharedKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
            OAI.EditApproximation.BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List OAI.EditApproximation.BinaryFraction) =>
              (OAI.EditApproximation.BitQuery.compute
                    (OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
                        (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
                (OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.queryNeededInputsWithWork selectedActions onlineActions)).bind
                  fun (currentKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
                  OAI.EditApproximation.BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List OAI.EditApproximation.BinaryFraction) =>
                    OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions onlineActions currentKeys currentWords
                        q)))
    fun (earlierWords : List OAI.EditApproximation.BinaryFraction) =>
    (OAI.EditApproximation.BitQuery.Footprint.compute
          (OAI.EditApproximation.BinaryFraction.queryOnlineSelectWithWorkRawBand source target parent N P F exponent H hP tau a
            eta kappa parentInitial child initial R hc hi t integer earlierKeys earlierWords q)
          (OAI.EditApproximation.BinaryFraction.queryOnlineSelectAllocationRawBand source target parent N P F exponent H hP tau
            a eta kappa parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation t integer
            integerAllocation earlierKeys earlierWords q)).bind
      (fun
          (onlineActions :
            List
              (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
                (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
        have word : OAI.EditApproximation.BinaryFraction × ℕ := parentInitial q;
        OAI.EditApproximation.BitQuery.charge word.2
          ((OAI.EditApproximation.BitQuery.compute
                (OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                  word.1 q draw)).bind
            fun (sharedKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
            OAI.EditApproximation.BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List OAI.EditApproximation.BinaryFraction) =>
              (OAI.EditApproximation.BitQuery.compute
                    (OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
                        (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
                (OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.queryNeededInputsWithWork selectedActions onlineActions)).bind
                  fun (currentKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
                  OAI.EditApproximation.BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List OAI.EditApproximation.BinaryFraction) =>
                    OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions onlineActions currentKeys currentWords
                        q)))
      fun
        (online :
          List
            (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
              (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
      OAI.EditApproximation.BitQuery.Footprint.chargeOf (parentAllocation q)
        ((OAI.EditApproximation.BitQuery.Footprint.computeOf
              (OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
                (parentInitial q).1 q draw)
              (OAI.EditApproximation.BinaryFraction.querySharedInputsAllocation M N F Q exponent eM eF hM hF parent a
                (parentInitial q).1 q draw drawAllocation)).bind
          (fun (sharedKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
            OAI.EditApproximation.BitQuery.collect readCurrent sharedKeys
              fun (sharedWords : List OAI.EditApproximation.BinaryFraction) =>
              (OAI.EditApproximation.BitQuery.compute
                    (OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
                        (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
                (OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.queryNeededInputsWithWork selectedActions online)).bind
                  fun (currentKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
                  OAI.EditApproximation.BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List OAI.EditApproximation.BinaryFraction) =>
                    OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions online currentKeys currentWords q))
          fun (sharedKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
          OAI.EditApproximation.BitQuery.Footprint.collect readCurrent hr sharedKeys
            (fun (sharedWords : List OAI.EditApproximation.BinaryFraction) =>
              (OAI.EditApproximation.BitQuery.compute
                    (OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand source target parent N P F exponent Q
                      eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)).bind
                fun
                  (selectedActions :
                    List
                      (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
                        (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
                (OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.queryNeededInputsWithWork selectedActions online)).bind
                  fun (currentKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
                  OAI.EditApproximation.BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List OAI.EditApproximation.BinaryFraction) =>
                    OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions online currentKeys currentWords q))
            fun (sharedWords : List OAI.EditApproximation.BinaryFraction) =>
            (OAI.EditApproximation.BitQuery.Footprint.computeOf
                  (OAI.EditApproximation.BinaryFraction.queryGroupSelectWithWorkRawBand source target parent N P F exponent Q
                    eM eF hP hM hF tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q)
                  (OAI.EditApproximation.BinaryFraction.queryGroupSelectAllocationRawBand source target parent N P F exponent Q
                    eM eF hP hM hF tau a parentInitial child initial R hc hi parentAllocation childAllocation
                    initialAllocation draw drawAllocation sharedKeys sharedWords q)).bind
              (fun
                  (selectedActions :
                    List
                      (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
                        (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
                (OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.queryNeededInputsWithWork selectedActions online)).bind
                  fun (currentKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
                  OAI.EditApproximation.BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List OAI.EditApproximation.BinaryFraction) =>
                    OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords selectedActions online currentKeys currentWords q))
              fun
                (groups :
                  List
                    (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
                      (Fin M × OAI.EditApproximation.TargetInterval target.length) M)) =>
              (OAI.EditApproximation.BitQuery.Footprint.computeOf
                    (OAI.EditApproximation.queryNeededInputsWithWork groups online)
                    (OAI.EditApproximation.queryNeededInputsAllocation groups online)).bind
                (fun (currentKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
                  OAI.EditApproximation.BitQuery.collect readCurrent currentKeys
                    fun (currentWords : List OAI.EditApproximation.BinaryFraction) =>
                    OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords groups online currentKeys currentWords q))
                fun (currentKeys : List (Fin M × OAI.EditApproximation.TargetInterval target.length)) =>
                OAI.EditApproximation.BitQuery.Footprint.collect readCurrent hr currentKeys
                  (fun (currentWords : List OAI.EditApproximation.BinaryFraction) =>
                    OAI.EditApproximation.BitQuery.compute
                      (OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                        parentInitial t earlierKeys earlierWords groups online currentKeys currentWords q))
                  fun (currentWords : List OAI.EditApproximation.BinaryFraction) =>
                  OAI.EditApproximation.BitQuery.Footprint.computeOf
                    (OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork parent N P F a delta
                      parentInitial t earlierKeys earlierWords groups online currentKeys currentWords q)
                    (OAI.EditApproximation.BinaryFraction.queryRefinementFinishAllocation parent N P F a delta
                      parentInitial parentAllocation t earlierKeys earlierWords groups online currentKeys currentWords
                      q))

def queryLocalRandomSourcesFootprintRawBand
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    [NeZero M]
    (parent : OAI.EditApproximation.TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (t : ℕ)
    (parentInitial : OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
    (child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
    (R : ℕ)
    (hc : ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval target.length), (child i r).2 ≤ R)
    (hi : ∀ (i : Fin M) (r : OAI.EditApproximation.TargetInterval target.length), (initial i r).2 ≤ R)
    (parentAllocation : OAI.EditApproximation.TargetInterval target.length → ℕ)
    (childAllocation initialAllocation : Fin M → OAI.EditApproximation.TargetInterval target.length → ℕ)
    (q : OAI.EditApproximation.TargetInterval target.length)
    (readGroup : OAI.EditApproximation.GroupScalarKey M F Q → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readInteger : ℕ × OAI.EditApproximation.TargetInterval target.length →
  ℕ → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readEarlier : Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readCurrent : Fin M × OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (hg : (key : OAI.EditApproximation.GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × OAI.EditApproximation.TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint)
    (he : (key : Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × OAI.EditApproximation.TargetInterval target.length) → (readCurrent key).Footprint) : (OAI.EditApproximation.queryLocalRandomSourcesRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
    delta t parentInitial child initial R hc hi q readGroup readInteger readEarlier readCurrent).Footprint :=
OAI.EditApproximation.queryGroupSourceGatherFootprint M N F Q exponent eM eF hM hF a parentInitial parentAllocation q
  readGroup hg
  (fun (groupKeys : List (OAI.EditApproximation.GroupScalarKey M F Q))
      (groupWords : List OAI.EditApproximation.BinaryFraction) =>
    OAI.EditApproximation.queryOnlineSourceGather parent N P F exponent H hP tau a parentInitial child q readInteger
      fun (onlineKeys : List (ℕ × OAI.EditApproximation.TargetInterval target.length))
        (onlineWords : List OAI.EditApproximation.BinaryFraction) =>
      OAI.EditApproximation.queryLocalRefinementRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
        delta t parentInitial child initial R hc hi
        (OAI.EditApproximation.BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
        (OAI.EditApproximation.BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords) q readEarlier
        readCurrent)
  fun (groupKeys : List (OAI.EditApproximation.GroupScalarKey M F Q))
    (groupWords : List OAI.EditApproximation.BinaryFraction) =>
  OAI.EditApproximation.queryOnlineSourceGatherFootprint parent N P F exponent H hP tau a parentInitial parentAllocation
    child childAllocation q readInteger hz
    (fun (onlineKeys : List (ℕ × OAI.EditApproximation.TargetInterval target.length))
        (onlineWords : List OAI.EditApproximation.BinaryFraction) =>
      OAI.EditApproximation.queryLocalRefinementRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
        delta t parentInitial child initial R hc hi
        (OAI.EditApproximation.BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
        (OAI.EditApproximation.BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords) q readEarlier
        readCurrent)
    fun (onlineKeys : List (ℕ × OAI.EditApproximation.TargetInterval target.length))
      (onlineWords : List OAI.EditApproximation.BinaryFraction) =>
    OAI.EditApproximation.queryLocalRefinementFootprintRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta
      kappa delta t parentInitial child initial R hc hi
      (OAI.EditApproximation.BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
      (OAI.EditApproximation.BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords) parentAllocation
      childAllocation initialAllocation
      (OAI.EditApproximation.BinaryFraction.queryGroupDrawReadAllocation groupKeys groupWords)
      (OAI.EditApproximation.BinaryFraction.queryOnlineIntegerReadAllocation onlineKeys onlineWords) q readEarlier
      readCurrent he hr

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

open Finset

def queryLocalBandFootprintRawBand
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    [NeZero M]
    (parent : OAI.EditApproximation.TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (t : ℕ)
    (parentInitial : OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
    (parentAllocation : OAI.EditApproximation.TargetInterval target.length → ℕ)
    (readMass readInitial : Fin M × OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readGroup : OAI.EditApproximation.GroupScalarKey M F Q → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readInteger : ℕ × OAI.EditApproximation.TargetInterval target.length →
  ℕ → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval target.length)
    (readEarlier : Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readCurrent : Fin M × OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (hm : (key : Fin M × OAI.EditApproximation.TargetInterval target.length) → (readMass key).Footprint)
    (hi : (key : Fin M × OAI.EditApproximation.TargetInterval target.length) → (readInitial key).Footprint)
    (hg : (key : OAI.EditApproximation.GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × OAI.EditApproximation.TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint)
    (he : (key : Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × OAI.EditApproximation.TargetInterval target.length) → (readCurrent key).Footprint) : (OAI.EditApproximation.queryLocalBandRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
    parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).Footprint := by
  exact
    OAI.EditApproximation.queryBandGatherFootprint M parent N P F exponent hP a parentInitial parentAllocation q readMass
      readInitial hm hi
      (fun (keys : List (Fin M × OAI.EditApproximation.TargetInterval target.length))
          (massWords initialWords : List OAI.EditApproximation.BinaryFraction) =>
        OAI.EditApproximation.queryLocalRandomSourcesRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
          delta t parentInitial (OAI.EditApproximation.BinaryFraction.queryChildReadWithWork keys massWords)
          (OAI.EditApproximation.BinaryFraction.queryChildReadWithWork keys initialWords)
          (OAI.EditApproximation.BinaryFraction.queryDataReadBudget M target.length keys) (OAI.EditApproximation.Lemmas.queryChildReadWithWork_budget keys massWords) (OAI.EditApproximation.Lemmas.queryChildReadWithWork_budget keys initialWords) q readGroup
          readInteger readEarlier readCurrent)
      fun (keys : List (Fin M × OAI.EditApproximation.TargetInterval target.length))
        (massWords initialWords : List OAI.EditApproximation.BinaryFraction) =>
      OAI.EditApproximation.queryLocalRandomSourcesFootprintRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a
        eta kappa delta t parentInitial (OAI.EditApproximation.BinaryFraction.queryChildReadWithWork keys massWords)
        (OAI.EditApproximation.BinaryFraction.queryChildReadWithWork keys initialWords)
        (OAI.EditApproximation.BinaryFraction.queryDataReadBudget M target.length keys) (OAI.EditApproximation.Lemmas.queryChildReadWithWork_budget keys massWords) (OAI.EditApproximation.Lemmas.queryChildReadWithWork_budget keys initialWords)
        parentAllocation (OAI.EditApproximation.BinaryFraction.queryChildReadAllocation keys massWords)
        (OAI.EditApproximation.BinaryFraction.queryChildReadAllocation keys initialWords) q readGroup readInteger
        readEarlier readCurrent hg hz he hr

end OAI.EditApproximation

end


