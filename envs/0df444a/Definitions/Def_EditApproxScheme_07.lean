-- Prove2me | Definitions.Def_EditApproxScheme_07
-- name    : EditApproxScheme_07
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:36:20.67221+00:00
-- url     : https://prove2.me/theorems/1ca4744f-7703-4816-b228-10418189740a
-- title:
--   Edit-distance approximation scheme, part 7 of 20: bands, connections and representatives
-- statement:
--   This is **part 7 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains sums over lists, band coordinates, rounded group states, initial cone centers, online integer reads, cell states, connection and endpoint-connection costs, local representatives, group keys, band vertices, and prefix minima.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L3315-L4100 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 7 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_06

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

def sumListWithWork (values : List OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let result := OAI.EditApproximation.BinaryFraction.bandMassTotalWithWork (Vector.ofFn values.get)
  (result.1, result.2 + 6 * values.length)

def connectionTermsWithWork {n : ℕ} (start : OAI.EditApproximation.BinaryFraction) :
    List (OAI.EditApproximation.TargetInterval n) → OAI.EditApproximation.BinaryFraction → List OAI.EditApproximation.BinaryFraction × ℕ
  | [], finish =>
    let result := OAI.EditApproximation.BinaryFraction.distanceWithWork start finish
    ([result.1], result.2 + 2)
  | state :: rest, finish =>
    let current := OAI.EditApproximation.BinaryFraction.distanceWithWork start (OAI.EditApproximation.BinaryFraction.nat state.lo)
    let tail := connectionTermsWithWork (OAI.EditApproximation.BinaryFraction.nat state.hi) rest finish
    (current.1 :: tail.1,
      current.2 + tail.2 + Nat.size state.lo + Nat.size state.hi + 6)

def bandEnvelopeReadWithWork {M n : ℕ} (b : ℕ) (band : List (Fin M → OAI.EditApproximation.TargetInterval n))
    (read : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) (i : Fin M) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let values := OAI.EditApproximation.arithmeticMapWithWork (fun action => read i (action i)) band
  let floor := OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat b) (OAI.EditApproximation.BinaryFraction.nat M)
  let maximum := OAI.EditApproximation.BinaryFraction.maximumWithWork OAI.EditApproximation.BinaryFraction.zero values.1
  let input := OAI.EditApproximation.BinaryFraction.maxWithWork floor.1 maximum.1
  let result := OAI.EditApproximation.BinaryFraction.dyadicCeilingWithWork input.1
  (result.1, values.2 + floor.2 + maximum.2 + input.2 + result.2 + band.length + 4)

def onlineLinearReadWithWork {β : Type u_1} {σ : Type u_2} (mass : β → OAI.EditApproximation.BinaryFraction)
    (read : ℕ → β × σ → OAI.EditApproximation.BinaryFraction × ℕ) (eta kappa : OAI.EditApproximation.BinaryFraction)
    (t : ℕ) (i : β × σ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let coefficient := OAI.EditApproximation.BinaryFraction.coefficientWithWork kappa
  let terms := OAI.EditApproximation.vectorMapWithWork t fun s => OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork mass read coefficient.1 s.val i
  let history := OAI.EditApproximation.BinaryFraction.bandMassTotalWithWork terms.1
  let current := OAI.EditApproximation.BinaryFraction.gainReadWithWork mass read t i
  let total := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork history.1 current.1
  let result := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork eta total.1
  (result.1, coefficient.2 + terms.2 + history.2 + current.2 + total.2 + result.2 + 3)

def targetCellsWithWork {n : ℕ} (side : OAI.EditApproximation.BinaryFraction) (radius : ℕ)
    (q : OAI.EditApproximation.TargetInterval n) : List (ℕ × ℕ) × ℕ :=
  let left := OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork side q.lo radius
  let right := OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork side q.hi radius
  let cells := OAI.EditApproximation.arithmeticFlatMapWithWork (fun lo =>
    OAI.EditApproximation.arithmeticMapWithWork (fun hi => ((lo, hi), 1)) right.1) left.1
  (cells.1, left.2 + right.2 + cells.2 + 2)

def cellStatesWithWork (n g : ℕ) (side : OAI.EditApproximation.BinaryFraction) (cell : ℕ × ℕ) :
    List (OAI.EditApproximation.TargetInterval n) × ℕ :=
  let left := OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork side g cell.1
  let right := OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork side g cell.2
  let states := OAI.EditApproximation.arithmeticFlatMapWithWork (fun lo =>
    OAI.EditApproximation.filterMapWithWork (OAI.EditApproximation.makeStateWithWork n lo) right.1) left.1
  (states.1, left.2 + right.2 + states.2 + 2)

def bandCoordinatesWithWork {M n : ℕ} (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) :
    List (Fin M × OAI.EditApproximation.TargetInterval n) × ℕ :=
  let raw := OAI.EditApproximation.arithmeticFlatMapWithWork (fun action =>
    OAI.EditApproximation.arithmeticMapWithWork (fun i : Fin M => ((i, action i), 1)) (List.finRange M)) band
  let unique := OAI.EditApproximation.dedupByWithWork OAI.EditApproximation.coordinateEqualWithWork raw.1
  (unique.1, raw.2 + unique.2 + 1)

def countedBandCoordinateWithWork {M n : ℕ} (mass : Vector OAI.EditApproximation.BinaryFraction M)
    (total : OAI.EditApproximation.BinaryFraction) (action : Fin M → OAI.EditApproximation.TargetInterval n)
    (coordinate : Fin M × OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let test := OAI.EditApproximation.coordinateEqualWithWork coordinate (coordinate.1, action coordinate.1)
  let result := if test.1 then OAI.EditApproximation.BinaryFraction.divWithWork (mass.get coordinate.1) total else (OAI.EditApproximation.BinaryFraction.zero, 1)
  (result.1, test.2 + result.2 + 1)

def representativeScaleReadWithWork {n : ℕ} (P F : ℕ) (a : OAI.EditApproximation.BinaryFraction)
    (read : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) (radius : List Bool)
    (query : OAI.EditApproximation.TargetInterval n) (e : ℕ) : List (ℕ × OAI.EditApproximation.TargetInterval n) × ℕ :=
  let b := 2 ^ e
  let spacing := OAI.EditApproximation.seedGridSpacingWithWork b P
  let points := OAI.EditApproximation.gridStateBoxWithWork n (OAI.EditApproximation.bitWordValue spacing.1) (OAI.EditApproximation.bitWordValue radius) query.lo query.hi
  let selected := OAI.EditApproximation.filterWithWork (fun r =>
    let word := read r
    let guard := OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork b F a word.1
    (guard.1, guard.2 + word.2)) points.1
  let labeled := OAI.EditApproximation.arithmeticMapWithWork (fun r => ((b, r), 1)) selected.1
  (labeled.1, spacing.2 + points.2 + selected.2 + labeled.2 + e + 5)

def queryRawCentersWithWork {n : ℕ} (N P F : ℕ) (a value : OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval n) : List (OAI.EditApproximation.TargetInterval n) × ℕ :=
  let scales := OAI.EditApproximation.BinaryFraction.queryScalesWithWork N F a value
  let radius := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value
  let centers := OAI.EditApproximation.arithmeticFlatMapWithWork (fun b =>
    let spacing := OAI.EditApproximation.seedGridSpacingWithWork b P
    let states := OAI.EditApproximation.gridStateBoxWithWork n (OAI.EditApproximation.bitWordValue spacing.1) (OAI.EditApproximation.bitWordValue radius.1) q.lo q.hi
    (states.1, spacing.2 + states.2 + 1)) scales.1
  let unique := OAI.EditApproximation.queryEraseWithWork OAI.EditApproximation.queryIntervalEqualWithWork centers.1
  (unique.1, scales.2 + radius.2 + centers.2 + unique.2 + 3)

def queryWideInputsWithWork {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx) (P : ℕ)
    (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) : List (Fin M × OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let raw := OAI.EditApproximation.arithmeticFlatMapWithWork (fun br =>
    OAI.EditApproximation.arithmeticFlatMapWithWork (fun i : Fin M =>
      let states := OAI.EditApproximation.wideChildGridWithWork parent br.2 br.1 P i
      let labeled := OAI.EditApproximation.arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
      (labeled.1, states.2 + labeled.2 + 1)) (List.finRange M)) representatives
  let unique := OAI.EditApproximation.queryEraseWithWork OAI.EditApproximation.coordinateEqualWithWork raw.1
  (unique.1, raw.2 + unique.2 + M + 2)

def queryRawHistoryInputsWithWork {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (P history : ℕ) (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) :
    List (Fin M × ℕ × OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let inputs := OAI.EditApproximation.arithmeticFlatMapWithWork (fun br =>
    OAI.EditApproximation.arithmeticFlatMapWithWork (fun i : Fin M =>
      let states := OAI.EditApproximation.wideChildGridWithWork parent br.2 br.1 P i
      let times := OAI.EditApproximation.arithmeticFlatMapWithWork (fun t =>
        OAI.EditApproximation.arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1) (List.range history)
      (times.1, states.2 + times.2 + history + 2)) (List.finRange M)) representatives
  (inputs.1, inputs.2 + M + 1)

def queryGroupRoundedStatesWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (b exponent : ℕ) (cell : ℕ × ℕ) (i : Fin M) (h : OAI.EditApproximation.BinaryFraction) :
    List (OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let theta := OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent
  let spacing := OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork theta h
  let child := OAI.EditApproximation.sourceChildWithWork parent i
  let offset := OAI.EditApproximation.saturatingSubtractWithWork child.1.lo parent.lo
  let base := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat cell.1) theta
  let position := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork base.1 (OAI.EditApproximation.BinaryFraction.nat b)
  let floor := OAI.EditApproximation.BinaryFraction.naturalFloorWithWork position.1
  let anchor := OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue floor.1) (OAI.EditApproximation.bitWordValue offset.1)
  let radius := OAI.EditApproximation.binaryNaturalMulWithWork 12 b
  let length := OAI.EditApproximation.saturatingSubtractWithWork child.1.hi child.1.lo
  let twice := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 2) h
  let gap := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork twice.1
  let states := OAI.EditApproximation.queryGapStatesWithWork ny (OAI.EditApproximation.bitWordValue spacing.1) (OAI.EditApproximation.bitWordValue anchor.1)
    (OAI.EditApproximation.bitWordValue radius.1) (OAI.EditApproximation.bitWordValue length.1) (OAI.EditApproximation.bitWordValue gap.1)
  (states.1, spacing.2 + child.2 + offset.2 + base.2 + position.2 + floor.2 + anchor.2 +
    radius.2 + length.2 + twice.2 + gap.2 + states.2 + exponent + 12)

def queryOnlineIntegerReadWithWork {n : ℕ} (keys : List (ℕ × OAI.EditApproximation.TargetInterval n))
    (values : List OAI.EditApproximation.BinaryFraction) (b : ℕ) (q : OAI.EditApproximation.TargetInterval n) : ℕ × ℕ :=
  let word := OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork OAI.EditApproximation.queryOnlineKeyEqualWithWork keys values (b, q)
  let floor := OAI.EditApproximation.BinaryFraction.naturalFloorWithWork word.1
  (OAI.EditApproximation.bitWordValue floor.1, word.2 + floor.2 + 1)

def queryChildReadWithWork {M n : ℕ} (keys : List (Fin M × OAI.EditApproximation.TargetInterval n))
    (values : List OAI.EditApproximation.BinaryFraction) (i : Fin M) (q : OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork OAI.EditApproximation.coordinateEqualWithWork keys values (i, q)

def queryHistoryReadWithWork {M n : ℕ} (keys : List (Fin M × ℕ × OAI.EditApproximation.TargetInterval n))
    (values : List OAI.EditApproximation.BinaryFraction) (s : ℕ) (input : Fin M × OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork OAI.EditApproximation.queryHistoryEqualWithWork keys values (input.1, s, input.2)

def queryParentReadWithWork {n : ℕ} (keys : List (OAI.EditApproximation.TargetInterval n))
    (words : List OAI.EditApproximation.BinaryFraction) (r : OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork OAI.EditApproximation.queryIntervalEqualWithWork keys words r

def initialGridReadWithWork {n : ℕ} (P : ℕ) (A : OAI.EditApproximation.BinaryFraction)
    (read : OAI.EditApproximation.TargetInterval n → List Bool × ℕ) (radius : ℕ) (q : OAI.EditApproximation.TargetInterval n) (b : ℕ) :
    List (OAI.EditApproximation.TargetInterval n) × ℕ :=
  let spacing := OAI.EditApproximation.seedGridSpacingWithWork b P
  let points := OAI.EditApproximation.gridStateBoxWithWork n (OAI.EditApproximation.bitWordValue spacing.1) radius q.lo q.hi
  let selected := OAI.EditApproximation.filterWithWork (fun r =>
    let word := read r
    let guard := OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork b (OAI.EditApproximation.bitWordValue word.1) A
    (guard.1, guard.2 + word.2)) points.1
  (selected.1, spacing.2 + points.2 + selected.2 + 2)

def queryInitialConeCentersWithWork {n : ℕ} (N P : ℕ) (A value : OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval n) : List (OAI.EditApproximation.TargetInterval n) × ℕ :=
  let radius := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value
  let scales := OAI.EditApproximation.dyadicScalesWithWork N
  let active := OAI.EditApproximation.filterWithWork (fun b => OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork (OAI.EditApproximation.bitWordValue radius.1) b A) scales.1
  let centers := OAI.EditApproximation.arithmeticFlatMapWithWork (fun b =>
    let spacing := OAI.EditApproximation.seedGridSpacingWithWork b P
    let states := OAI.EditApproximation.gridStateBoxWithWork n (OAI.EditApproximation.bitWordValue spacing.1) (OAI.EditApproximation.bitWordValue radius.1) q.lo q.hi
    (states.1, spacing.2 + states.2 + 1)) active.1
  (centers.1, radius.2 + scales.2 + active.2 + centers.2 + 2)

def connectionTermsAllocation {n : ℕ} (start : OAI.EditApproximation.BinaryFraction) :
    List (OAI.EditApproximation.TargetInterval n) → OAI.EditApproximation.BinaryFraction → ℕ
  | [], finish => OAI.EditApproximation.BinaryFraction.distanceAllocation start finish + 1
  | state :: rest, finish => OAI.EditApproximation.BinaryFraction.distanceAllocation start (OAI.EditApproximation.BinaryFraction.nat state.lo) +
    connectionTermsAllocation (OAI.EditApproximation.BinaryFraction.nat state.hi) rest finish + Nat.size state.lo + Nat.size state.hi + 3

def endpointDistanceAllocation {n : ℕ} (q r : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.BinaryFraction.distanceAllocation (OAI.EditApproximation.BinaryFraction.nat q.lo) (OAI.EditApproximation.BinaryFraction.nat r.lo) + OAI.EditApproximation.BinaryFraction.distanceAllocation (OAI.EditApproximation.BinaryFraction.nat q.hi) (OAI.EditApproximation.BinaryFraction.nat r.hi) +
    OAI.EditApproximation.BinaryFraction.canonicalAddAllocation (OAI.EditApproximation.BinaryFraction.distanceWithWork (OAI.EditApproximation.BinaryFraction.nat q.lo) (OAI.EditApproximation.BinaryFraction.nat r.lo)).1
      (OAI.EditApproximation.BinaryFraction.distanceWithWork (OAI.EditApproximation.BinaryFraction.nat q.hi) (OAI.EditApproximation.BinaryFraction.nat r.hi)).1 + Nat.size q.lo + Nat.size q.hi + Nat.size r.lo + Nat.size r.hi

def stateGapAllocation {n : ℕ} (sourceLength : ℕ) (r : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.BinaryFraction.subAllocation (OAI.EditApproximation.BinaryFraction.nat r.hi) (OAI.EditApproximation.BinaryFraction.nat r.lo) +
    OAI.EditApproximation.BinaryFraction.subAllocation (OAI.EditApproximation.BinaryFraction.subWithWork (OAI.EditApproximation.BinaryFraction.nat r.hi) (OAI.EditApproximation.BinaryFraction.nat r.lo)).1 (OAI.EditApproximation.BinaryFraction.nat sourceLength) + Nat.size r.hi + Nat.size r.lo + Nat.size sourceLength

def queryChildReadAllocation {M n : ℕ} (keys : List (Fin M × OAI.EditApproximation.TargetInterval n))
    (values : List OAI.EditApproximation.BinaryFraction) (i : Fin M) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.BinaryFraction.gatheredLookupAllocation OAI.EditApproximation.coordinateEqualWithWork OAI.EditApproximation.coordinateEqualAllocation keys values (i, q)

def queryHistoryReadAllocation {M n : ℕ} (keys : List (Fin M × ℕ × OAI.EditApproximation.TargetInterval n))
    (values : List OAI.EditApproximation.BinaryFraction) (s : ℕ) (input : Fin M × OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.BinaryFraction.gatheredLookupAllocation OAI.EditApproximation.queryHistoryEqualWithWork OAI.EditApproximation.queryHistoryEqualAllocation keys values (input.1, s, input.2)

def queryOnlineIntegerReadAllocation {n : ℕ} (keys : List (ℕ × OAI.EditApproximation.TargetInterval n))
    (values : List OAI.EditApproximation.BinaryFraction) (b : ℕ) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  let word := (OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork OAI.EditApproximation.queryOnlineKeyEqualWithWork keys values (b, q)).1
  OAI.EditApproximation.BinaryFraction.gatheredLookupAllocation OAI.EditApproximation.queryOnlineKeyEqualWithWork OAI.EditApproximation.queryOnlineKeyEqualAllocation keys values (b, q) +
    OAI.EditApproximation.BinaryFraction.naturalFloorAllocation word

def bandCoordinatesAllocation {M n : ℕ} (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) : ℕ :=
  let build := fun action : Fin M → OAI.EditApproximation.TargetInterval n =>
    OAI.EditApproximation.arithmeticMapWithWork (fun i : Fin M => ((i, action i), 1)) (List.finRange M)
  let raw := (OAI.EditApproximation.arithmeticFlatMapWithWork build band).1
  OAI.EditApproximation.arithmeticFlatMapAllocation build
    (fun _ => OAI.EditApproximation.arithmeticMapAllocation (fun _ : Fin M => 1) (List.finRange M) + M) band +
    OAI.EditApproximation.dedupByAllocation OAI.EditApproximation.coordinateEqualWithWork OAI.EditApproximation.coordinateEqualAllocation raw

def scoredArgmaxAllocation {α : Type u_1} (score : α → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: rest =>
    scoredArgmaxAllocation score allocation rest + allocation a +
      match (OAI.EditApproximation.BinaryFraction.scoredArgmaxWithWork score rest).1 with
      | none => 1
      | some best => OAI.EditApproximation.BinaryFraction.ltAllocation (score a).1 best.2 + 1

def anchorGuardAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (r : OAI.EditApproximation.TargetInterval ny)
    (b : ℕ) (states : Fin M → OAI.EditApproximation.TargetInterval ny) (i : Fin M) : ℕ :=
  let left := (OAI.EditApproximation.translatedEndpointWithWork r.lo parent.lo (OAI.EditApproximation.sourceChild parent i).lo).1
  let right := (OAI.EditApproximation.translatedEndpointWithWork r.lo parent.lo (OAI.EditApproximation.sourceChild parent i).hi).1
  let radius := OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalMulWithWork 6 b).1
  OAI.EditApproximation.translatedEndpointAllocation r.lo parent.lo (OAI.EditApproximation.sourceChild parent i).lo +
    OAI.EditApproximation.translatedEndpointAllocation r.lo parent.lo (OAI.EditApproximation.sourceChild parent i).hi + OAI.EditApproximation.binaryNaturalMulAllocation 6 b +
    OAI.EditApproximation.BinaryFraction.naturalDistanceLeAllocation left (states i).lo radius + OAI.EditApproximation.BinaryFraction.naturalDistanceLeAllocation right (states i).hi radius

def bandEnvelopeReadAllocation {M n : ℕ} (b : ℕ) (band : List (Fin M → OAI.EditApproximation.TargetInterval n))
    (read : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (footprint : Fin M → OAI.EditApproximation.TargetInterval n → ℕ) (i : Fin M) : ℕ :=
  let values := (OAI.EditApproximation.arithmeticMapWithWork (fun action => read i (action i)) band).1
  let floor := (OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat b) (OAI.EditApproximation.BinaryFraction.nat M)).1
  let maximum := (OAI.EditApproximation.BinaryFraction.maximumWithWork OAI.EditApproximation.BinaryFraction.zero values).1
  OAI.EditApproximation.arithmeticMapAllocation (fun action => footprint i (action i)) band +
    OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.nat b) (OAI.EditApproximation.BinaryFraction.nat M) + OAI.EditApproximation.BinaryFraction.maximumAllocation OAI.EditApproximation.BinaryFraction.zero values + OAI.EditApproximation.BinaryFraction.maxAllocation floor maximum +
    OAI.EditApproximation.BinaryFraction.dyadicCeilingAllocation (OAI.EditApproximation.BinaryFraction.maxWithWork floor maximum).1 + 0

def targetCellsAllocation {n : ℕ} (side : OAI.EditApproximation.BinaryFraction) (radius : ℕ) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  let left := (OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork side q.lo radius).1
  let right := (OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork side q.hi radius).1
  OAI.EditApproximation.BinaryFraction.cellCoordinatesAllocation side q.lo radius + OAI.EditApproximation.BinaryFraction.cellCoordinatesAllocation side q.hi radius +
    OAI.EditApproximation.arithmeticFlatMapAllocation (fun lo => OAI.EditApproximation.arithmeticMapWithWork (fun hi => ((lo, hi), 1)) right)
      (fun _ => OAI.EditApproximation.arithmeticMapAllocation (fun _ => 1) right) left

def cellStatesAllocation (n g : ℕ) (side : OAI.EditApproximation.BinaryFraction) (cell : ℕ × ℕ) : ℕ :=
  let left := (OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork side g cell.1).1
  let right := (OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork side g cell.2).1
  OAI.EditApproximation.BinaryFraction.cellGridPointsAllocation side g cell.1 + OAI.EditApproximation.BinaryFraction.cellGridPointsAllocation side g cell.2 +
    OAI.EditApproximation.arithmeticFlatMapAllocation (fun lo => OAI.EditApproximation.filterMapWithWork (OAI.EditApproximation.makeStateWithWork n lo) right)
      (fun lo => OAI.EditApproximation.filterMapAllocation (OAI.EditApproximation.makeStateWithWork n lo) (OAI.EditApproximation.makeStateAllocation n lo) right) left

def queryRawCentersAllocation {n : ℕ} (N P F : ℕ) (a value : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  let build := fun b =>
    let spacing := OAI.EditApproximation.seedGridSpacingWithWork b P
    let states := OAI.EditApproximation.gridStateBoxWithWork n (OAI.EditApproximation.bitWordValue spacing.1) (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value).1) q.lo q.hi
    (states.1, spacing.2 + states.2 + 1)
  let allocation := fun b => OAI.EditApproximation.seedGridSpacingAllocation b P +
    OAI.EditApproximation.gridStateBoxAllocation n (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.seedGridSpacingWithWork b P).1)
      (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value).1) q.lo q.hi
  let centers := (OAI.EditApproximation.arithmeticFlatMapWithWork build (OAI.EditApproximation.BinaryFraction.queryScalesWithWork N F a value).1).1
  OAI.EditApproximation.BinaryFraction.queryScalesAllocation N F a value + OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation value +
    OAI.EditApproximation.arithmeticFlatMapAllocation build allocation (OAI.EditApproximation.BinaryFraction.queryScalesWithWork N F a value).1 +
    OAI.EditApproximation.queryEraseAllocation OAI.EditApproximation.queryIntervalEqualWithWork OAI.EditApproximation.queryIntervalEqualAllocation centers

def queryOnlineKeysAllocation {n : ℕ} (N P F : ℕ) (_hP : 0 < P)
    (a value : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.BinaryFraction.queryScalesAllocation N F a value + OAI.EditApproximation.arithmeticMapAllocation (fun b =>
    OAI.EditApproximation.seedGridSpacingAllocation b P + OAI.EditApproximation.roundStateAllocation (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.seedGridSpacingWithWork b P).1) q + 1)
      (OAI.EditApproximation.BinaryFraction.queryScalesWithWork N F a value).1

def representativeScaleReadAllocation {n : ℕ} (P F : ℕ) (a : OAI.EditApproximation.BinaryFraction)
    (read : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) (allocation : OAI.EditApproximation.TargetInterval n → ℕ)
    (radius : List Bool) (query : OAI.EditApproximation.TargetInterval n) (e : ℕ) : ℕ :=
  let b := 2 ^ e
  let spacing := (OAI.EditApproximation.seedGridSpacingWithWork b P).1
  let points := (OAI.EditApproximation.gridStateBoxWithWork n (OAI.EditApproximation.bitWordValue spacing) (OAI.EditApproximation.bitWordValue radius) query.lo query.hi).1
  let test := fun r => ((OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork b F a (read r).1).1,
    (OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork b F a (read r).1).2 + (read r).2)
  let selected := (OAI.EditApproximation.filterWithWork test points).1
  OAI.EditApproximation.seedGridSpacingAllocation b P + OAI.EditApproximation.gridStateBoxAllocation n (OAI.EditApproximation.bitWordValue spacing) (OAI.EditApproximation.bitWordValue radius) query.lo query.hi +
    OAI.EditApproximation.filterAllocation test (fun r => OAI.EditApproximation.BinaryFraction.centerEligibilityAllocation b F a (read r).1 + allocation r) points +
    OAI.EditApproximation.arithmeticMapAllocation (fun _ => 1) selected + e + 1

def queryWideInputsAllocation {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx) (P : ℕ)
    (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) : ℕ :=
  let build := fun br : ℕ × OAI.EditApproximation.TargetInterval ny =>
    OAI.EditApproximation.arithmeticFlatMapWithWork (fun i : Fin M =>
      let states := OAI.EditApproximation.wideChildGridWithWork parent br.2 br.1 P i
      let labeled := OAI.EditApproximation.arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
      (labeled.1, states.2 + labeled.2 + 1)) (List.finRange M)
  let one := fun (br : ℕ × OAI.EditApproximation.TargetInterval ny) (i : Fin M) =>
    OAI.EditApproximation.wideChildGridAllocation parent br.2 br.1 P i +
      OAI.EditApproximation.arithmeticMapAllocation (fun _ => 1) (OAI.EditApproximation.wideChildGridWithWork parent br.2 br.1 P i).1
  OAI.EditApproximation.arithmeticFlatMapAllocation build
    (fun br => OAI.EditApproximation.arithmeticFlatMapAllocation (fun i : Fin M =>
      let states := OAI.EditApproximation.wideChildGridWithWork parent br.2 br.1 P i
      let labeled := OAI.EditApproximation.arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
      (labeled.1, states.2 + labeled.2 + 1)) (one br) (List.finRange M)) representatives +
    OAI.EditApproximation.queryEraseAllocation OAI.EditApproximation.coordinateEqualWithWork OAI.EditApproximation.coordinateEqualAllocation (OAI.EditApproximation.arithmeticFlatMapWithWork build representatives).1 + M

def queryRawHistoryInputsAllocation {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (P history : ℕ) (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) : ℕ :=
  let child := fun (br : ℕ × OAI.EditApproximation.TargetInterval ny) (i : Fin M) =>
    let states := OAI.EditApproximation.wideChildGridWithWork parent br.2 br.1 P i
    let times := OAI.EditApproximation.arithmeticFlatMapWithWork (fun t =>
      OAI.EditApproximation.arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1) (List.range history)
    (times.1, states.2 + times.2 + history + 2)
  let one := fun (br : ℕ × OAI.EditApproximation.TargetInterval ny) (i : Fin M) =>
    OAI.EditApproximation.wideChildGridAllocation parent br.2 br.1 P i + history +
      OAI.EditApproximation.arithmeticFlatMapAllocation (fun t => OAI.EditApproximation.arithmeticMapWithWork (fun r => ((i, t, r), 1))
        (OAI.EditApproximation.wideChildGridWithWork parent br.2 br.1 P i).1)
        (fun _ => OAI.EditApproximation.arithmeticMapAllocation (fun _ => 1) (OAI.EditApproximation.wideChildGridWithWork parent br.2 br.1 P i).1)
        (List.range history)
  OAI.EditApproximation.arithmeticFlatMapAllocation (fun br => OAI.EditApproximation.arithmeticFlatMapWithWork (child br) (List.finRange M))
    (fun br => OAI.EditApproximation.arithmeticFlatMapAllocation (child br) (one br) (List.finRange M)) representatives + M

def queryGroupRoundedStatesAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (b exponent : ℕ) (cell : ℕ × ℕ) (i : Fin M) (h : OAI.EditApproximation.BinaryFraction) : ℕ :=
  let theta := OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent
  let spacing := (OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork theta h).1
  let child := (OAI.EditApproximation.sourceChildWithWork parent i).1
  let offset := (OAI.EditApproximation.saturatingSubtractWithWork child.lo parent.lo).1
  let base := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat cell.1) theta).1
  let position := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork base (OAI.EditApproximation.BinaryFraction.nat b)).1
  let floor := (OAI.EditApproximation.BinaryFraction.naturalFloorWithWork position).1
  let anchor := (OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue floor) (OAI.EditApproximation.bitWordValue offset)).1
  let radius := (OAI.EditApproximation.binaryNaturalMulWithWork 12 b).1
  let length := (OAI.EditApproximation.saturatingSubtractWithWork child.hi child.lo).1
  let twice := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 2) h).1
  let gap := (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork twice).1
  OAI.EditApproximation.BinaryFraction.roundedSpacingAllocation theta h + OAI.EditApproximation.sourceChildAllocation parent i + OAI.EditApproximation.saturatingSubtractAllocation child.lo parent.lo +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat cell.1) theta + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation base (OAI.EditApproximation.BinaryFraction.nat b) + OAI.EditApproximation.BinaryFraction.naturalFloorAllocation position +
    OAI.EditApproximation.binaryNaturalAddAllocation (OAI.EditApproximation.bitWordValue floor) (OAI.EditApproximation.bitWordValue offset) + OAI.EditApproximation.binaryNaturalMulAllocation 12 b +
    OAI.EditApproximation.saturatingSubtractAllocation child.hi child.lo + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 2) h + OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation twice +
    OAI.EditApproximation.queryGapStatesAllocation ny (OAI.EditApproximation.bitWordValue spacing) (OAI.EditApproximation.bitWordValue anchor) (OAI.EditApproximation.bitWordValue radius)
      (OAI.EditApproximation.bitWordValue length) (OAI.EditApproximation.bitWordValue gap) + exponent + 2

def groupIndexAllocation {M : ℕ} (h : OAI.EditApproximation.BinaryFraction) (envelope values : Vector OAI.EditApproximation.BinaryFraction M)
    (indices : List (Fin M)) : ℕ :=
  OAI.EditApproximation.BinaryFraction.groupTermsAllocation h envelope indices +
    OAI.EditApproximation.BinaryFraction.sumListAllocation (OAI.EditApproximation.BinaryFraction.groupTermsWithWork h envelope values indices).1 + 0

def queryParentReadAllocation {n : ℕ} (keys : List (OAI.EditApproximation.TargetInterval n))
    (words : List OAI.EditApproximation.BinaryFraction) (r : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.BinaryFraction.gatheredLookupAllocation OAI.EditApproximation.queryIntervalEqualWithWork OAI.EditApproximation.queryIntervalEqualAllocation keys words r

def onlineLinearReadAllocation {β : Type u_1} {σ : Type u_2} (mass : β → OAI.EditApproximation.BinaryFraction)
    (read : ℕ → β × σ → OAI.EditApproximation.BinaryFraction × ℕ) (footprint : ℕ → β × σ → ℕ)
    (eta kappa : OAI.EditApproximation.BinaryFraction) (t : ℕ) (i : β × σ) : ℕ :=
  let coefficient := (OAI.EditApproximation.BinaryFraction.coefficientWithWork kappa).1
  let terms := (OAI.EditApproximation.vectorMapWithWork t fun s => OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork mass read coefficient s.val i).1
  let history := (OAI.EditApproximation.BinaryFraction.bandMassTotalWithWork terms).1
  let current := (OAI.EditApproximation.BinaryFraction.gainReadWithWork mass read t i).1
  OAI.EditApproximation.BinaryFraction.coefficientAllocation kappa +
    OAI.EditApproximation.vectorMapAllocation t (fun s => OAI.EditApproximation.BinaryFraction.optimisticTermReadAllocation mass read footprint coefficient s.val i) +
    OAI.EditApproximation.BinaryFraction.bandMassAllocation terms + OAI.EditApproximation.BinaryFraction.gainReadAllocation mass read footprint t i + OAI.EditApproximation.BinaryFraction.canonicalAddAllocation history current +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation eta (OAI.EditApproximation.BinaryFraction.canonicalAddWithWork history current).1 + 0

def countedBandCoordinateAllocation {M n : ℕ} (mass : Vector OAI.EditApproximation.BinaryFraction M)
    (total : OAI.EditApproximation.BinaryFraction) (action : Fin M → OAI.EditApproximation.TargetInterval n) (coordinate : Fin M × OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.coordinateEqualAllocation coordinate (coordinate.1, action coordinate.1) +
    if (OAI.EditApproximation.coordinateEqualWithWork coordinate (coordinate.1, action coordinate.1)).1 then
      OAI.EditApproximation.BinaryFraction.divAllocation (mass.get coordinate.1) total else 0

def queryInitialConeCentersAllocation {n : ℕ} (N P : ℕ) (A value : OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  let radius := (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value).1
  let active := (OAI.EditApproximation.filterWithWork (fun b => OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork (OAI.EditApproximation.bitWordValue radius) b A) (OAI.EditApproximation.dyadicScalesWithWork N).1).1
  let build := fun b =>
    let spacing := (OAI.EditApproximation.seedGridSpacingWithWork b P).1
    let states := OAI.EditApproximation.gridStateBoxWithWork n (OAI.EditApproximation.bitWordValue spacing) (OAI.EditApproximation.bitWordValue radius) q.lo q.hi
    (states.1, (OAI.EditApproximation.seedGridSpacingWithWork b P).2 + states.2 + 1)
  OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation value + OAI.EditApproximation.dyadicScalesAllocation N +
    OAI.EditApproximation.filterAllocation (fun b => OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork (OAI.EditApproximation.bitWordValue radius) b A)
      (fun b => OAI.EditApproximation.BinaryFraction.initialScaleGuardAllocation (OAI.EditApproximation.bitWordValue radius) b A) (OAI.EditApproximation.dyadicScalesWithWork N).1 +
    OAI.EditApproximation.arithmeticFlatMapAllocation build
      (fun b => OAI.EditApproximation.seedGridSpacingAllocation b P + OAI.EditApproximation.gridStateBoxAllocation n
        (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.seedGridSpacingWithWork b P).1) (OAI.EditApproximation.bitWordValue radius) q.lo q.hi) active

def connectionWithWork {n : ℕ} (start finish : OAI.EditApproximation.BinaryFraction)
    (states : List (OAI.EditApproximation.TargetInterval n)) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let terms := OAI.EditApproximation.BinaryFraction.connectionTermsWithWork start states finish
  let result := OAI.EditApproximation.BinaryFraction.sumListWithWork terms.1
  (result.1, terms.2 + result.2 + 1)

def envelopeVectorReadWithWork {M n : ℕ} (b : ℕ) (band : List (Fin M → OAI.EditApproximation.TargetInterval n))
    (read : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) : Vector OAI.EditApproximation.BinaryFraction M × ℕ :=
  OAI.EditApproximation.vectorMapWithWork M (OAI.EditApproximation.BinaryFraction.bandEnvelopeReadWithWork b band read)

def bellmanActionReadWithWork {Parent : Type u_1} {Child : Type u_2} {M : ℕ}
    (distance : Parent → Parent → OAI.EditApproximation.BinaryFraction × ℕ) (L : OAI.EditApproximation.BinaryFraction)
    (read : Child → OAI.EditApproximation.BinaryFraction × ℕ) (query : Parent)
    (action : OAI.EditApproximation.BinaryBellmanAction Parent Child M) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let words := OAI.EditApproximation.arithmeticMapWithWork (fun i => read (action.childState i)) (List.finRange M)
  let dist := distance query action.center
  let spatial := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork L dist.1
  let connection := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork spatial.1 action.connection
  let children := OAI.EditApproximation.BinaryFraction.sumListWithWork words.1
  let result := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork connection.1 children.1
  (result.1, words.2 + dist.2 + spatial.2 + connection.2 + children.2 + result.2 + 3)

def cellCentersReadWithWork {n : ℕ} (P F b : ℕ) (a theta : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) (cell : ℕ × ℕ) :
    List (OAI.EditApproximation.TargetInterval n) × ℕ :=
  let spacing := OAI.EditApproximation.seedGridSpacingWithWork b P
  let side := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork theta (OAI.EditApproximation.BinaryFraction.nat b)
  let states := OAI.EditApproximation.BinaryFraction.cellStatesWithWork n (OAI.EditApproximation.bitWordValue spacing.1) side.1 cell
  let selected := OAI.EditApproximation.filterWithWork (fun r =>
    let word := initial r
    let tested := OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork b F a word.1
    (tested.1, word.2 + tested.2)) states.1
  (selected.1, spacing.2 + side.2 + states.2 + selected.2 + 3)

def countedBandVerticesWithWork {M n d : ℕ} (coordinates : Vector (Fin M × OAI.EditApproximation.TargetInterval n) d)
    (mass : Vector OAI.EditApproximation.BinaryFraction M) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) :
    List ((Fin M → OAI.EditApproximation.TargetInterval n) × Vector OAI.EditApproximation.BinaryFraction d) × ℕ :=
  let total := OAI.EditApproximation.BinaryFraction.bandMassTotalWithWork mass
  let vertices := band.map fun action =>
    let vertex := OAI.EditApproximation.vectorMapWithWork d fun i =>
      OAI.EditApproximation.BinaryFraction.countedBandCoordinateWithWork mass total.1 action (coordinates.get i)
    ((action, vertex.1), vertex.2)
  (vertices.map Prod.fst, total.2 + (vertices.map Prod.snd).sum + 8 * band.length)

def onlineIndexSetupWithWork {M n : ℕ} (H : ℕ) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) :
    ℕ × ℕ :=
  let coordinates := OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork band
  let sum := OAI.EditApproximation.binaryNaturalAddWithWork H coordinates.1.length
  let offset := OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue sum.1) 2
  let power := OAI.EditApproximation.bitPowerWithWork offset.1 80
  (OAI.EditApproximation.bitWordValue offset.1, coordinates.2 + sum.2 + offset.2 + power.2 + 3)

def localRepresentativeReadWithWork {n : ℕ} (N P F : ℕ) (a : OAI.EditApproximation.BinaryFraction)
    (read : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) (query : OAI.EditApproximation.TargetInterval n) :
    List (ℕ × OAI.EditApproximation.TargetInterval n) × ℕ :=
  let queryWord := read query
  let scales := OAI.EditApproximation.BinaryFraction.queryExponentsWithWork N F a queryWord.1
  let radius := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork queryWord.1
  let result := OAI.EditApproximation.arithmeticFlatMapWithWork
    (OAI.EditApproximation.BinaryFraction.representativeScaleReadWithWork P F a read radius.1 query) scales.1
  (result.1, queryWord.2 + scales.2 + radius.2 + result.2 + 3)

def queryGroupKeysWithWork {n : ℕ} (N F exponent : ℕ) (a value : OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval n) : List (ℕ × (ℕ × ℕ)) × ℕ :=
  let scales := OAI.EditApproximation.BinaryFraction.queryScalesWithWork N F a value
  let radius := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value
  let keys := OAI.EditApproximation.arithmeticFlatMapWithWork (fun b =>
    let side := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat b)
    let cells := OAI.EditApproximation.BinaryFraction.targetCellsWithWork side.1 (OAI.EditApproximation.bitWordValue radius.1) q
    let labeled := OAI.EditApproximation.arithmeticMapWithWork (fun cell => ((b, cell), 1)) cells.1
    (labeled.1, side.2 + cells.2 + labeled.2 + 2)) scales.1
  (keys.1, scales.2 + radius.2 + keys.2 + exponent + 4)

def queryMeanWithWork (count : ℕ) (words : List OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let total := OAI.EditApproximation.BinaryFraction.sumListWithWork words
  let result := OAI.EditApproximation.BinaryFraction.divWithWork total.1 (OAI.EditApproximation.BinaryFraction.nat count)
  (result.1, total.2 + result.2 + Nat.size count + 2)

def initialCentersReadWithWork {n : ℕ} (N P : ℕ) (A : OAI.EditApproximation.BinaryFraction)
    (read : OAI.EditApproximation.TargetInterval n → List Bool × ℕ) (q : OAI.EditApproximation.TargetInterval n) :
    List (OAI.EditApproximation.TargetInterval n) × ℕ :=
  let queryWord := read q
  let Uq := OAI.EditApproximation.bitWordValue queryWord.1
  let scales := OAI.EditApproximation.dyadicScalesWithWork N
  let active := OAI.EditApproximation.filterWithWork (fun b => OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork Uq b A) scales.1
  let centers := OAI.EditApproximation.arithmeticFlatMapWithWork (OAI.EditApproximation.BinaryFraction.initialGridReadWithWork P A read Uq q) active.1
  (centers.1, queryWord.2 + scales.2 + active.2 + centers.2 + 3)

def queryInitialSeedReadWithWork {n : ℕ} (value : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n)
    (keys : List (OAI.EditApproximation.TargetInterval n)) (words : List OAI.EditApproximation.BinaryFraction) (r : OAI.EditApproximation.TargetInterval n) : List Bool × ℕ :=
  let test := OAI.EditApproximation.queryIntervalEqualWithWork r q
  if test.1 then
    let result := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value
    (result.1, test.2 + result.2 + 1)
  else
    let found := OAI.EditApproximation.BinaryFraction.queryParentReadWithWork keys words r
    let result := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork found.1
    (result.1, test.2 + found.2 + result.2 + 1)

def queryOverrideParentReadWithWork {n : ℕ} (value : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n)
    (keys : List (OAI.EditApproximation.TargetInterval n)) (words : List OAI.EditApproximation.BinaryFraction) (r : OAI.EditApproximation.TargetInterval n) :
    OAI.EditApproximation.BinaryFraction × ℕ :=
  let test := OAI.EditApproximation.queryIntervalEqualWithWork r q
  if test.1 then (value, test.2 + 1)
  else
    let found := OAI.EditApproximation.BinaryFraction.queryParentReadWithWork keys words r
    (found.1, test.2 + found.2 + 1)

def connectionAllocation {n : ℕ} (start finish : OAI.EditApproximation.BinaryFraction)
    (states : List (OAI.EditApproximation.TargetInterval n)) : ℕ :=
  OAI.EditApproximation.BinaryFraction.connectionTermsAllocation start states finish +
    OAI.EditApproximation.BinaryFraction.sumListAllocation (OAI.EditApproximation.BinaryFraction.connectionTermsWithWork start states finish).1 + 0

def coordinateVectorAllocation {M n : ℕ} (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) : ℕ :=
  OAI.EditApproximation.BinaryFraction.bandCoordinatesAllocation band + (OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork band).1.length

def maximizerAllocation {d : ℕ} (gradient : Vector OAI.EditApproximation.BinaryFraction d)
    (vertices : List (Vector OAI.EditApproximation.BinaryFraction d)) : ℕ :=
  OAI.EditApproximation.BinaryFraction.scoredArgmaxAllocation (OAI.EditApproximation.BinaryFraction.dotWithWork gradient)
    (fun v => OAI.EditApproximation.BinaryFraction.dotListAllocation gradient v (List.finRange d)) vertices + d

def onlineIndexSetupAllocation {M n : ℕ} (H : ℕ) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) : ℕ :=
  let coordinates := (OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork band).1
  let sum := (OAI.EditApproximation.binaryNaturalAddWithWork H coordinates.length).1
  let offset := (OAI.EditApproximation.binaryNaturalAddWithWork (OAI.EditApproximation.bitWordValue sum) 2).1
  OAI.EditApproximation.BinaryFraction.bandCoordinatesAllocation band + OAI.EditApproximation.binaryNaturalAddAllocation H coordinates.length +
    OAI.EditApproximation.binaryNaturalAddAllocation (OAI.EditApproximation.bitWordValue sum) 2 + OAI.EditApproximation.bitPowerAllocation offset 80

def envelopeVectorReadAllocation {M n : ℕ} (b : ℕ) (band : List (Fin M → OAI.EditApproximation.TargetInterval n))
    (read : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (footprint : Fin M → OAI.EditApproximation.TargetInterval n → ℕ) : ℕ :=
  OAI.EditApproximation.vectorMapAllocation M (OAI.EditApproximation.BinaryFraction.bandEnvelopeReadAllocation b band read footprint)

def roundedBandReadAllocation {n M : ℕ} (exponent b : ℕ) (band : List (Fin M → OAI.EditApproximation.TargetInterval n))
    (hne : band ≠ []) (read : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : Fin M → OAI.EditApproximation.TargetInterval n → ℕ) : ℕ :=
  OAI.EditApproximation.vectorMapAllocation M fun i =>
    let envelope := (OAI.EditApproximation.BinaryFraction.bandEnvelopeReadWithWork b band read i).1
    let spacing := OAI.EditApproximation.bitWordValue (OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) envelope).1
    OAI.EditApproximation.BinaryFraction.bandEnvelopeReadAllocation b band read allocation i +
      OAI.EditApproximation.BinaryFraction.roundedSpacingAllocation (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) envelope +
      OAI.EditApproximation.roundStateAllocation spacing (band.head hne i) + exponent + 2

def queryGroupKeysAllocation {n : ℕ} (N F exponent : ℕ) (a value : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  let radius := (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value).1
  let build := fun b =>
    let side := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat b)
    let cells := OAI.EditApproximation.BinaryFraction.targetCellsWithWork side.1 (OAI.EditApproximation.bitWordValue radius) q
    let labeled := OAI.EditApproximation.arithmeticMapWithWork (fun cell => ((b, cell), 1)) cells.1
    (labeled.1, side.2 + cells.2 + labeled.2 + 2)
  OAI.EditApproximation.BinaryFraction.queryScalesAllocation N F a value + OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation value +
    OAI.EditApproximation.arithmeticFlatMapAllocation build (fun b =>
      let side := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat b)).1
      OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat b) + OAI.EditApproximation.BinaryFraction.targetCellsAllocation side (OAI.EditApproximation.bitWordValue radius) q +
        OAI.EditApproximation.arithmeticMapAllocation (fun _ => 1) (OAI.EditApproximation.BinaryFraction.targetCellsWithWork side (OAI.EditApproximation.bitWordValue radius) q).1)
      (OAI.EditApproximation.BinaryFraction.queryScalesWithWork N F a value).1 + exponent + 2

def initialCellAllocation (n P exponent : ℕ) (key : ℕ × ℕ × ℕ) : ℕ :=
  OAI.EditApproximation.seedGridSpacingAllocation key.1 P + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat key.1) +
    OAI.EditApproximation.BinaryFraction.cellStatesAllocation n (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.seedGridSpacingWithWork key.1 P).1)
      (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat key.1)).1 key.2 + exponent + 2

def localRepresentativeReadAllocation {n : ℕ} (N P F : ℕ) (a : OAI.EditApproximation.BinaryFraction)
    (read : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) (allocation : OAI.EditApproximation.TargetInterval n → ℕ)
    (query : OAI.EditApproximation.TargetInterval n) : ℕ :=
  allocation query + OAI.EditApproximation.BinaryFraction.queryExponentsAllocation N F a (read query).1 + OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation (read query).1 +
    OAI.EditApproximation.arithmeticFlatMapAllocation
      (OAI.EditApproximation.BinaryFraction.representativeScaleReadWithWork P F a read (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork (read query).1).1 query)
      (OAI.EditApproximation.BinaryFraction.representativeScaleReadAllocation P F a read allocation (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork (read query).1).1 query)
      (OAI.EditApproximation.BinaryFraction.queryExponentsWithWork N F a (read query).1).1

def cellCentersReadAllocation {n : ℕ} (P F b : ℕ) (a theta : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) (allocation : OAI.EditApproximation.TargetInterval n → ℕ)
    (cell : ℕ × ℕ) : ℕ :=
  let spacing := (OAI.EditApproximation.seedGridSpacingWithWork b P).1
  let side := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork theta (OAI.EditApproximation.BinaryFraction.nat b)).1
  let states := (OAI.EditApproximation.BinaryFraction.cellStatesWithWork n (OAI.EditApproximation.bitWordValue spacing) side cell).1
  let test := fun r => ((OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork b F a (initial r).1).1,
    (initial r).2 + (OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork b F a (initial r).1).2)
  OAI.EditApproximation.seedGridSpacingAllocation b P + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation theta (OAI.EditApproximation.BinaryFraction.nat b) +
    OAI.EditApproximation.BinaryFraction.cellStatesAllocation n (OAI.EditApproximation.bitWordValue spacing) side cell +
    OAI.EditApproximation.filterAllocation test (fun r => allocation r + OAI.EditApproximation.BinaryFraction.centerEligibilityAllocation b F a (initial r).1) states

def selectGroupAllocation {ι : Type u_1} (members : List ι) (estimate : ι → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : ι → ℕ) : ℕ :=
  OAI.EditApproximation.BinaryFraction.scoredArgmaxAllocation (fun member => ((estimate member).1.neg, (estimate member).2 + 1)) allocation members

def bellmanActionReadAllocation {Parent : Type u_1} {Child : Type u_2} {M : ℕ}
    (distance : Parent → Parent → OAI.EditApproximation.BinaryFraction × ℕ) (distanceAllocation : Parent → Parent → ℕ)
    (L : OAI.EditApproximation.BinaryFraction) (read : Child → OAI.EditApproximation.BinaryFraction × ℕ) (footprint : Child → ℕ)
    (query : Parent) (action : OAI.EditApproximation.BinaryBellmanAction Parent Child M) : ℕ :=
  let words := (OAI.EditApproximation.arithmeticMapWithWork (fun i => read (action.childState i)) (List.finRange M)).1
  let dist := (distance query action.center).1
  let spatial := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork L dist).1
  let connection := (OAI.EditApproximation.BinaryFraction.canonicalAddWithWork spatial action.connection).1
  let children := (OAI.EditApproximation.BinaryFraction.sumListWithWork words).1
  OAI.EditApproximation.arithmeticMapAllocation (fun i => footprint (action.childState i)) (List.finRange M) +
    distanceAllocation query action.center + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation L dist +
    OAI.EditApproximation.BinaryFraction.canonicalAddAllocation spatial action.connection + OAI.EditApproximation.BinaryFraction.sumListAllocation words +
    OAI.EditApproximation.BinaryFraction.canonicalAddAllocation connection children

def countedBandVerticesAllocation {M n d : ℕ} (coordinates : Vector (Fin M × OAI.EditApproximation.TargetInterval n) d)
    (mass : Vector OAI.EditApproximation.BinaryFraction M) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) : ℕ :=
  OAI.EditApproximation.BinaryFraction.bandMassAllocation mass +
    (band.map fun action => OAI.EditApproximation.vectorMapAllocation d fun i =>
      OAI.EditApproximation.BinaryFraction.countedBandCoordinateAllocation mass (OAI.EditApproximation.BinaryFraction.bandMassTotalWithWork mass).1 action (coordinates.get i)).sum +
    4 * band.length

def queryInitialSeedReadAllocation {n : ℕ} (value : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n)
    (keys : List (OAI.EditApproximation.TargetInterval n)) (words : List OAI.EditApproximation.BinaryFraction) (r : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.queryIntervalEqualAllocation r q +
    if (OAI.EditApproximation.queryIntervalEqualWithWork r q).1 then OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation value
    else OAI.EditApproximation.BinaryFraction.queryParentReadAllocation keys words r + OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation (OAI.EditApproximation.BinaryFraction.queryParentReadWithWork keys words r).1

def queryOverrideParentReadAllocation {n : ℕ} (q : OAI.EditApproximation.TargetInterval n)
    (keys : List (OAI.EditApproximation.TargetInterval n)) (words : List OAI.EditApproximation.BinaryFraction) (r : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.queryIntervalEqualAllocation r q +
    if (OAI.EditApproximation.queryIntervalEqualWithWork r q).1 then 0 else OAI.EditApproximation.BinaryFraction.queryParentReadAllocation keys words r

def prefixReadWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (r : OAI.EditApproximation.TargetInterval ny)
    (states : Fin M → OAI.EditApproximation.TargetInterval ny) (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (j : ℕ) (p : OAI.EditApproximation.BinaryFraction) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let words := OAI.EditApproximation.arithmeticMapWithWork (fun i : Fin M =>
    if i.val < j then read i (states i) else (OAI.EditApproximation.BinaryFraction.zero, 1)) (List.finRange M)
  let finish := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.balancedCut parent.lo (parent.hi - parent.lo) M j)) p
  let connection := OAI.EditApproximation.BinaryFraction.connectionWithWork (OAI.EditApproximation.BinaryFraction.nat r.lo) finish.1 ((List.ofFn states).take j)
  let total := OAI.EditApproximation.BinaryFraction.sumListWithWork words.1
  let result := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork connection.1 total.1
  (result.1, words.2 + finish.2 + connection.2 + total.2 + result.2 +
    Nat.size (OAI.EditApproximation.balancedCut parent.lo (parent.hi - parent.lo) M j) + Nat.size r.lo + 6 * M + 5)

def bellmanReadWithWork {Parent : Type u_1} {Child : Type u_2} {M : ℕ}
    (distance : Parent → Parent → OAI.EditApproximation.BinaryFraction × ℕ) (L fallback : OAI.EditApproximation.BinaryFraction)
    (read : Child → OAI.EditApproximation.BinaryFraction × ℕ) (query : Parent)
    (actions : List (OAI.EditApproximation.BinaryBellmanAction Parent Child M)) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let scores := OAI.EditApproximation.arithmeticMapWithWork (OAI.EditApproximation.BinaryFraction.bellmanActionReadWithWork distance L read query) actions
  let result := OAI.EditApproximation.BinaryFraction.minimumWithWork fallback scores.1
  (result.1, scores.2 + result.2 + 1)

def queryWarmupInputsWithWork {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F : ℕ) (a : OAI.EditApproximation.BinaryFraction) (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (q : OAI.EditApproximation.TargetInterval ny) : List (Fin M × OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let representatives := OAI.EditApproximation.BinaryFraction.localRepresentativeReadWithWork N P F a initial q
  let inputs := OAI.EditApproximation.BinaryFraction.queryWideInputsWithWork M parent P representatives.1
  (inputs.1, representatives.2 + inputs.2 + 1)

def endpointConnectionAllocation {n M : ℕ} (r : OAI.EditApproximation.TargetInterval n)
    (states : Fin M → OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.BinaryFraction.connectionAllocation (OAI.EditApproximation.BinaryFraction.nat r.lo) (OAI.EditApproximation.BinaryFraction.nat r.hi) (List.ofFn states) + Nat.size r.lo + Nat.size r.hi + M

def prefixReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (r : OAI.EditApproximation.TargetInterval ny)
    (states : Fin M → OAI.EditApproximation.TargetInterval ny) (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ) (j : ℕ) (p : OAI.EditApproximation.BinaryFraction) : ℕ :=
  let words := (OAI.EditApproximation.arithmeticMapWithWork (fun i : Fin M =>
    if i.val < j then read i (states i) else (OAI.EditApproximation.BinaryFraction.zero, 1)) (List.finRange M)).1
  let finish := (OAI.EditApproximation.BinaryFraction.canonicalAddWithWork (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.balancedCut parent.lo (parent.hi - parent.lo) M j)) p).1
  OAI.EditApproximation.arithmeticMapAllocation (fun i : Fin M => if i.val < j then allocation i (states i) else 0)
      (List.finRange M) +
    OAI.EditApproximation.BinaryFraction.canonicalAddAllocation (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.balancedCut parent.lo (parent.hi - parent.lo) M j)) p +
    OAI.EditApproximation.BinaryFraction.connectionAllocation (OAI.EditApproximation.BinaryFraction.nat r.lo) finish ((List.ofFn states).take j) + OAI.EditApproximation.BinaryFraction.sumListAllocation words +
    OAI.EditApproximation.BinaryFraction.canonicalAddAllocation (OAI.EditApproximation.BinaryFraction.connectionWithWork (OAI.EditApproximation.BinaryFraction.nat r.lo) finish ((List.ofFn states).take j)).1
      (OAI.EditApproximation.BinaryFraction.sumListWithWork words).1 +
    Nat.size (OAI.EditApproximation.balancedCut parent.lo (parent.hi - parent.lo) M j) + Nat.size r.lo + 2 * M

def optimizerAllocation {d : ℕ} (vertices : List (Vector OAI.EditApproximation.BinaryFraction d))
    (linear : Vector OAI.EditApproximation.BinaryFraction d) (G : ℕ) : ℕ → ℕ
  | 0 => d
  | j + 1 =>
    let previous := (OAI.EditApproximation.BinaryFraction.finiteOptimizerWithWork vertices linear G j).1
    let gradient := (OAI.EditApproximation.BinaryFraction.gradientWithWork G linear previous).1
    let selected := (OAI.EditApproximation.BinaryFraction.maximizerWithWork gradient vertices).1
    optimizerAllocation vertices linear G j + OAI.EditApproximation.BinaryFraction.gradientAllocation G linear previous +
      OAI.EditApproximation.BinaryFraction.maximizerAllocation gradient vertices + OAI.EditApproximation.BinaryFraction.optimizerUpdateAllocation j previous selected

def queryEarlierRepresentativesAllocation {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a : OAI.EditApproximation.BinaryFraction) (initial : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : OAI.EditApproximation.TargetInterval n → ℕ) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  let groups := (OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork N F exponent a (initial q).1 q).1
  let build := fun key : ℕ × ℕ × ℕ =>
    let centers := OAI.EditApproximation.BinaryFraction.cellCentersReadWithWork P F key.1 a (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) initial key.2
    let labeled := OAI.EditApproximation.arithmeticMapWithWork (fun r => ((key.1, r), 1)) centers.1
    (labeled.1, centers.2 + labeled.2 + 1)
  allocation q + OAI.EditApproximation.BinaryFraction.localRepresentativeReadAllocation N P F a initial allocation q +
    OAI.EditApproximation.BinaryFraction.queryGroupKeysAllocation N F exponent a (initial q).1 q +
    OAI.EditApproximation.arithmeticFlatMapAllocation build (fun key =>
      OAI.EditApproximation.BinaryFraction.cellCentersReadAllocation P F key.1 a (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) initial allocation key.2 +
      OAI.EditApproximation.arithmeticMapAllocation (fun _ => 1)
        (OAI.EditApproximation.BinaryFraction.cellCentersReadWithWork P F key.1 a (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) initial key.2).1) groups +
    OAI.EditApproximation.BinaryFraction.queryOnlineKeysAllocation N P F hP a (initial q).1 q +
    2 * (OAI.EditApproximation.BinaryFraction.localRepresentativeReadWithWork N P F a initial q).1.length +
    (OAI.EditApproximation.arithmeticFlatMapWithWork build groups).1.length

def queryWarmupInputsAllocation {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F : ℕ) (a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (allocation : OAI.EditApproximation.TargetInterval ny → ℕ)
    (q : OAI.EditApproximation.TargetInterval ny) : ℕ :=
  OAI.EditApproximation.BinaryFraction.localRepresentativeReadAllocation N P F a initial allocation q +
    OAI.EditApproximation.BinaryFraction.queryWideInputsAllocation M parent P (OAI.EditApproximation.BinaryFraction.localRepresentativeReadWithWork N P F a initial q).1

def bellmanReadAllocation {Parent : Type u_1} {Child : Type u_2} {M : ℕ}
    (distance : Parent → Parent → OAI.EditApproximation.BinaryFraction × ℕ) (distanceAllocation : Parent → Parent → ℕ)
    (L fallback : OAI.EditApproximation.BinaryFraction) (read : Child → OAI.EditApproximation.BinaryFraction × ℕ) (footprint : Child → ℕ)
    (query : Parent) (actions : List (OAI.EditApproximation.BinaryBellmanAction Parent Child M)) : ℕ :=
  let scores := (OAI.EditApproximation.arithmeticMapWithWork (OAI.EditApproximation.BinaryFraction.bellmanActionReadWithWork distance L read query) actions).1
  OAI.EditApproximation.arithmeticMapAllocation (OAI.EditApproximation.BinaryFraction.bellmanActionReadAllocation distance distanceAllocation L read footprint query) actions +
    OAI.EditApproximation.BinaryFraction.minimumAllocation fallback scores

def prefixMinimumReadWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (r : OAI.EditApproximation.TargetInterval ny)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (j : ℕ) (p : OAI.EditApproximation.BinaryFraction) :
    OAI.EditApproximation.BinaryFraction × ℕ :=
  let fallback := OAI.EditApproximation.BinaryFraction.prefixReadWithWork parent r (actions.head hne) read j p
  let scores := OAI.EditApproximation.arithmeticMapWithWork (fun action => OAI.EditApproximation.BinaryFraction.prefixReadWithWork parent r action read j p) actions
  let result := OAI.EditApproximation.BinaryFraction.minimumWithWork fallback.1 scores.1
  (result.1, fallback.2 + scores.2 + result.2 + 1)

def localContinuationReadWithWork {Parent : Type u_1} {Child : Type u_2} {M : ℕ}
    (distance : Parent → Parent → OAI.EditApproximation.BinaryFraction × ℕ) (L delta fallback : OAI.EditApproximation.BinaryFraction)
    (old current : Child → OAI.EditApproximation.BinaryFraction × ℕ) (query : Parent)
    (wide groups online : List (OAI.EditApproximation.BinaryBellmanAction Parent Child M)) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let warm := OAI.EditApproximation.BinaryFraction.bellmanReadWithWork distance L fallback old query wide
  let cone := OAI.EditApproximation.BinaryFraction.bellmanReadWithWork distance L warm.1 current query groups
  let scores := OAI.EditApproximation.arithmeticMapWithWork (OAI.EditApproximation.BinaryFraction.bellmanActionReadWithWork distance L current query) online
  let onlineMin := OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork scores.1
  let result := OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork delta cone.1 onlineMin.1
  (result.1, warm.2 + cone.2 + scores.2 + onlineMin.2 + result.2 + 3)

def prefixMinimumReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (r : OAI.EditApproximation.TargetInterval ny)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ) (j : ℕ) (p : OAI.EditApproximation.BinaryFraction) : ℕ :=
  let fallback := (OAI.EditApproximation.BinaryFraction.prefixReadWithWork parent r (actions.head hne) read j p).1
  let scores := (OAI.EditApproximation.arithmeticMapWithWork (fun action => OAI.EditApproximation.BinaryFraction.prefixReadWithWork parent r action read j p) actions).1
  OAI.EditApproximation.BinaryFraction.prefixReadAllocation parent r (actions.head hne) read allocation j p +
    OAI.EditApproximation.arithmeticMapAllocation (fun action => OAI.EditApproximation.BinaryFraction.prefixReadAllocation parent r action read allocation j p) actions +
    OAI.EditApproximation.BinaryFraction.minimumAllocation fallback scores

def localContinuationReadAllocation {Parent : Type u_1} {Child : Type u_2} {M : ℕ}
    (distance : Parent → Parent → OAI.EditApproximation.BinaryFraction × ℕ) (distanceAllocation : Parent → Parent → ℕ)
    (L delta fallback : OAI.EditApproximation.BinaryFraction) (old current : Child → OAI.EditApproximation.BinaryFraction × ℕ)
    (oldAllocation currentAllocation : Child → ℕ) (query : Parent)
    (wide groups online : List (OAI.EditApproximation.BinaryBellmanAction Parent Child M)) : ℕ :=
  let warm := (OAI.EditApproximation.BinaryFraction.bellmanReadWithWork distance L fallback old query wide).1
  let cone := (OAI.EditApproximation.BinaryFraction.bellmanReadWithWork distance L warm current query groups).1
  let scores := (OAI.EditApproximation.arithmeticMapWithWork (OAI.EditApproximation.BinaryFraction.bellmanActionReadWithWork distance L current query) online).1
  let onlineMin := (OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork scores).1
  OAI.EditApproximation.BinaryFraction.bellmanReadAllocation distance distanceAllocation L fallback old oldAllocation query wide +
    OAI.EditApproximation.BinaryFraction.bellmanReadAllocation distance distanceAllocation L warm current currentAllocation query groups +
    OAI.EditApproximation.arithmeticMapAllocation (OAI.EditApproximation.BinaryFraction.bellmanActionReadAllocation distance distanceAllocation L current currentAllocation query) online +
    OAI.EditApproximation.BinaryFraction.onlineMinimumAllocation scores + OAI.EditApproximation.BinaryFraction.refinementUpdateAllocation delta cone onlineMin

def endpointActionAllocation {ny M : ℕ} (center : OAI.EditApproximation.TargetInterval ny)
    (states : Fin M → OAI.EditApproximation.TargetInterval ny) : ℕ := OAI.EditApproximation.BinaryFraction.endpointConnectionAllocation center states + M + 1

def selectionAllocation {α : Type u_1} {d : ℕ}
    (vertices : List (α × Vector OAI.EditApproximation.BinaryFraction d)) (linear : Vector OAI.EditApproximation.BinaryFraction d) (G j : ℕ) : ℕ :=
  let iterate := (OAI.EditApproximation.BinaryFraction.finiteOptimizerWithWork (vertices.map Prod.snd) linear G j).1
  let gradient := (OAI.EditApproximation.BinaryFraction.gradientWithWork G linear iterate).1
  vertices.length + OAI.EditApproximation.BinaryFraction.optimizerAllocation (vertices.map Prod.snd) linear G j +
    OAI.EditApproximation.BinaryFraction.gradientAllocation G linear iterate +
    OAI.EditApproximation.BinaryFraction.scoredArgmaxAllocation (fun vertex => OAI.EditApproximation.BinaryFraction.dotWithWork gradient vertex.2)
      (fun vertex => OAI.EditApproximation.BinaryFraction.dotListAllocation gradient vertex.2 (List.finRange d)) vertices

def cutGuardReadWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (r : OAI.EditApproximation.TargetInterval ny)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (states : Fin M → OAI.EditApproximation.TargetInterval ny)
    (velocity tolerance : OAI.EditApproximation.BinaryFraction) (j : Fin M) : Bool × ℕ :=
  if j.val = 0 then (true, 1) else
    let shift := OAI.EditApproximation.BinaryFraction.subWithWork (OAI.EditApproximation.BinaryFraction.nat (states j).lo) (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.sourceChild parent j).lo)
    let offset := OAI.EditApproximation.BinaryFraction.subWithWork (OAI.EditApproximation.BinaryFraction.nat r.lo) (OAI.EditApproximation.BinaryFraction.nat parent.lo)
    let prediction := OAI.EditApproximation.BinaryFraction.prefixMinimumReadWithWork parent r actions hne read j.val shift.1
    let result := OAI.EditApproximation.BinaryFraction.affineErrorWithWork shift.1 offset.1 velocity prediction.1 tolerance
    (result.1, shift.2 + offset.2 + prediction.2 + result.2 +
      Nat.size (states j).lo + Nat.size (OAI.EditApproximation.sourceChild parent j).lo + Nat.size r.lo + Nat.size parent.lo + 5)

def cutGuardReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (r : OAI.EditApproximation.TargetInterval ny)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ) (states : Fin M → OAI.EditApproximation.TargetInterval ny)
    (velocity tolerance : OAI.EditApproximation.BinaryFraction) (j : Fin M) : ℕ :=
  if j.val = 0 then 0 else
    let shift := (OAI.EditApproximation.BinaryFraction.subWithWork (OAI.EditApproximation.BinaryFraction.nat (states j).lo) (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.sourceChild parent j).lo)).1
    let offset := (OAI.EditApproximation.BinaryFraction.subWithWork (OAI.EditApproximation.BinaryFraction.nat r.lo) (OAI.EditApproximation.BinaryFraction.nat parent.lo)).1
    OAI.EditApproximation.BinaryFraction.subAllocation (OAI.EditApproximation.BinaryFraction.nat (states j).lo) (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.sourceChild parent j).lo) +
      OAI.EditApproximation.BinaryFraction.subAllocation (OAI.EditApproximation.BinaryFraction.nat r.lo) (OAI.EditApproximation.BinaryFraction.nat parent.lo) +
      OAI.EditApproximation.BinaryFraction.prefixMinimumReadAllocation parent r actions hne read allocation j.val shift +
      OAI.EditApproximation.BinaryFraction.affineErrorAllocation shift offset velocity
        (OAI.EditApproximation.BinaryFraction.prefixMinimumReadWithWork parent r actions hne read j.val shift).1 tolerance +
      Nat.size (states j).lo + Nat.size (OAI.EditApproximation.sourceChild parent j).lo + Nat.size r.lo + Nat.size parent.lo

def bandPredicateReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (r : OAI.EditApproximation.TargetInterval ny)
    (b : ℕ) (tau theta velocity : OAI.EditApproximation.BinaryFraction)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ) (states : Fin M → OAI.EditApproximation.TargetInterval ny) : ℕ :=
  OAI.EditApproximation.zeroConnectionAllocation r.lo (List.ofFn states) r.hi + M +
    OAI.EditApproximation.allAllocation (OAI.EditApproximation.BinaryFraction.anchorGuardAllocation parent r b states) (List.finRange M) +
    OAI.EditApproximation.BinaryFraction.bandToleranceAllocation tau theta b M +
    OAI.EditApproximation.allAllocation (OAI.EditApproximation.BinaryFraction.cutGuardReadAllocation parent r actions hne read allocation states velocity
      (OAI.EditApproximation.BinaryFraction.bandToleranceWithWork tau theta b M).1) (List.finRange M)

end OAI.EditApproximation.BinaryFraction

end


