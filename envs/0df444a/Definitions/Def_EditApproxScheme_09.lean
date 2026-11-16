-- Prove2me | Definitions.Def_EditApproxScheme_09
-- name    : EditApproxScheme_09
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:38:58.512997+00:00
-- url     : https://prove2.me/theorems/fc8cd6a5-e3bd-44d0-9bda-69001e9991b0
-- title:
--   Edit-distance approximation scheme, part 9 of 20: group scales and band reads
-- statement:
--   This is **part 9 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains group scales, bands built from actions, band inputs, physical initial queries, global seed reads, inverses, endpoint action connections, state gaps, endpoint scores, group-member sources, and wide actions built from representatives. It also proves 2 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L4751-L5424 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 9 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_08

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

def groupScalesWithWork (eM eb eF : ℕ) : List OAI.EditApproximation.BinaryFraction × ℕ :=
  let exponents := OAI.EditApproximation.integerClosedRange ((eb : ℤ) - eM) ((6 + eF + eb : ℕ) : ℤ)
  let values := OAI.EditApproximation.arithmeticMapWithWork OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork exponents
  (values.1, values.2 + exponents.length + Nat.size eM + Nat.size eb + Nat.size eF + 8)

def bandPredicateReadWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (r : OAI.EditApproximation.TargetInterval ny)
    (b : ℕ) (tau theta velocity : OAI.EditApproximation.BinaryFraction)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (states : Fin M → OAI.EditApproximation.TargetInterval ny) :
    Bool × ℕ :=
  let connection := OAI.EditApproximation.zeroConnectionWithWork r.lo (List.ofFn states) r.hi
  let anchors := OAI.EditApproximation.allWithWork (fun i : Fin M =>
    let leftAnchor := OAI.EditApproximation.translatedEndpointWithWork r.lo parent.lo (OAI.EditApproximation.sourceChild parent i).lo
    let rightAnchor := OAI.EditApproximation.translatedEndpointWithWork r.lo parent.lo (OAI.EditApproximation.sourceChild parent i).hi
    let radius := OAI.EditApproximation.binaryNaturalMulWithWork 6 b
    let left := OAI.EditApproximation.BinaryFraction.naturalDistanceLeWithWork leftAnchor.1 (states i).lo (OAI.EditApproximation.bitWordValue radius.1)
    let right := OAI.EditApproximation.BinaryFraction.naturalDistanceLeWithWork rightAnchor.1 (states i).hi (OAI.EditApproximation.bitWordValue radius.1)
    (left.1 && right.1, leftAnchor.2 + rightAnchor.2 + radius.2 + left.2 + right.2 + 3)) (List.finRange M)
  let tolerance := OAI.EditApproximation.BinaryFraction.bandToleranceWithWork tau theta b M
  let cuts := OAI.EditApproximation.allWithWork (OAI.EditApproximation.BinaryFraction.cutGuardReadWithWork parent r actions hne read states velocity tolerance.1)
    (List.finRange M)
  (connection.1 && anchors.1 && cuts.1, connection.2 + anchors.2 + tolerance.2 + cuts.2 + 4)

def indexedGroupScales (raw : List OAI.EditApproximation.BinaryFraction) (M b : ℕ) (F : ℚ)
    (h : raw.map OAI.EditApproximation.BinaryFraction.value = OAI.EditApproximation.groupDyadicScales M b F) :
    Fin (OAI.EditApproximation.groupDyadicScales M b F).length → OAI.EditApproximation.BinaryFraction :=
  fun i => raw.get ⟨i.val, by
    have hlen := congrArg List.length h
    simp only [List.length_map] at hlen
    omega⟩

theorem _root_.OAI.EditApproximation.Lemmas.seedGridSpacingWithWork_value (b : ℕ) (P : ℕ) (hP : LT.lt.{0} 0 P) :
    OAI.EditApproximation.bitWordValue (OAI.EditApproximation.seedGridSpacingWithWork b P).1 = OAI.EditApproximation.seedGridSpacing b P := by
  have hv := (OAI.EditApproximation.Lemmas.binaryNaturalDivModWithWork_spec b P hP).1
  unfold OAI.EditApproximation.seedGridSpacingWithWork OAI.EditApproximation.seedGridSpacing
  dsimp only
  split_ifs with ht
  · have hq : b / P ≤ 1 := by
      have h := (OAI.EditApproximation.Lemmas.wordLEWithWork_value _ _).mp ht
      change OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalDivModWithWork b P).1 ≤ 1 at h
      rwa [hv] at h
    rw [max_eq_left hq]
    rfl
  · have hq : 1 ≤ b / P := by
      have h := mt (OAI.EditApproximation.Lemmas.wordLEWithWork_value _ _).mpr ht
      change ¬ OAI.EditApproximation.bitWordValue (OAI.EditApproximation.binaryNaturalDivModWithWork b P).1 ≤ 1 at h
      rw [hv] at h
      exact Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [max_eq_right hq]
    exact hv

theorem _root_.OAI.EditApproximation.Lemmas.seedGridSpacingWithWork_pos (b : ℕ) (P : ℕ) (hP : LT.lt.{0} 0 P) :
    0 < OAI.EditApproximation.bitWordValue (OAI.EditApproximation.seedGridSpacingWithWork b P).1 := by
  rw [OAI.EditApproximation.Lemmas.seedGridSpacingWithWork_value b P hP]
  unfold OAI.EditApproximation.seedGridSpacing
  omega

def queryOnlineKeysWithWork {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a value : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n) : List (ℕ × OAI.EditApproximation.TargetInterval n) × ℕ := by
  exact
    let scales := OAI.EditApproximation.BinaryFraction.queryScalesWithWork N F a value
    let keys := OAI.EditApproximation.arithmeticMapWithWork (fun b =>
      let spacing := OAI.EditApproximation.seedGridSpacingWithWork b P
      let center := OAI.EditApproximation.roundStateWithWork (OAI.EditApproximation.bitWordValue spacing.1) (OAI.EditApproximation.Lemmas.seedGridSpacingWithWork_pos b P hP) q
      ((b, center.1), spacing.2 + center.2 + 2)) scales.1
    (keys.1, scales.2 + keys.2 + 1)

def groupScalesAllocation (eM eb eF : ℕ) : ℕ :=
  let exponents := OAI.EditApproximation.integerClosedRange ((eb : ℤ) - eM) ((6 + eF + eb : ℕ) : ℤ)
  OAI.EditApproximation.arithmeticMapAllocation OAI.EditApproximation.BinaryFraction.signedPowerTwoAllocation exponents + exponents.length +
    Nat.size eM + Nat.size eb + Nat.size eF

def bandFromActionsReadWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b : ℕ) (tau theta velocity : OAI.EditApproximation.BinaryFraction)
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hne : actions ≠ []) :
    List (Fin M → OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let margin := OAI.EditApproximation.BinaryFraction.subWithWork OAI.EditApproximation.BinaryFraction.one tau
  let guard := OAI.EditApproximation.BinaryFraction.leWithWork velocity.absolute margin.1
  if guard.1 then
    let filtered := OAI.EditApproximation.filterWithWork
      (OAI.EditApproximation.BinaryFraction.bandPredicateReadWithWork parent r b tau theta velocity actions hne read) actions
    (filtered.1, margin.2 + guard.2 + filtered.2 + 2)
  else ([], margin.2 + guard.2 + 1)

def queryInitialSupportWithWork {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a value : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n) : List (OAI.EditApproximation.TargetInterval n) × ℕ :=
  let raw := OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork N P F a value q
  let groups := OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork N F exponent a value q
  let cells := OAI.EditApproximation.arithmeticFlatMapWithWork (fun key =>
    let spacing := OAI.EditApproximation.seedGridSpacingWithWork key.1 P
    let side := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat key.1)
    let states := OAI.EditApproximation.BinaryFraction.cellStatesWithWork n (OAI.EditApproximation.bitWordValue spacing.1) side.1 key.2
    (states.1, spacing.2 + side.2 + states.2 + exponent + 3)) groups.1
  let online := OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork N P F hP a value q
  let onlineStates := OAI.EditApproximation.arithmeticMapWithWork (fun key => (key.2, 1)) online.1
  (q :: (raw.1 ++ cells.1 ++ onlineStates.1),
    raw.2 + groups.2 + cells.2 + online.2 + onlineStates.2 + 2 * raw.1.length + cells.1.length + 5)

def queryEarlierRepresentativesWithWork {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a : OAI.EditApproximation.BinaryFraction) (initial : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (q : OAI.EditApproximation.TargetInterval n) : List (ℕ × OAI.EditApproximation.TargetInterval n) × ℕ :=
  let query := initial q
  let reps := OAI.EditApproximation.BinaryFraction.localRepresentativeReadWithWork N P F a initial q
  let groups := OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork N F exponent a query.1 q
  let cells := OAI.EditApproximation.arithmeticFlatMapWithWork (fun key =>
    let centers := OAI.EditApproximation.BinaryFraction.cellCentersReadWithWork P F key.1 a (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) initial key.2
    let labeled := OAI.EditApproximation.arithmeticMapWithWork (fun r => ((key.1, r), 1)) centers.1
    (labeled.1, centers.2 + labeled.2 + 1)) groups.1
  let online := OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork N P F hP a query.1 q
  (reps.1 ++ cells.1 ++ online.1,
    query.2 + reps.2 + groups.2 + cells.2 + online.2 + 2 * reps.1.length + cells.1.length + 4)

def bandFromActionsReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (b : ℕ) (tau theta velocity : OAI.EditApproximation.BinaryFraction)
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) (hne : actions ≠ []) : ℕ :=
  let margin := (OAI.EditApproximation.BinaryFraction.subWithWork OAI.EditApproximation.BinaryFraction.one tau).1
  OAI.EditApproximation.BinaryFraction.subAllocation OAI.EditApproximation.BinaryFraction.one tau + OAI.EditApproximation.BinaryFraction.leAllocation velocity.absolute margin +
    if (OAI.EditApproximation.BinaryFraction.leWithWork velocity.absolute margin).1 then
      OAI.EditApproximation.filterAllocation (OAI.EditApproximation.BinaryFraction.bandPredicateReadWithWork parent r b tau theta velocity actions hne read)
        (OAI.EditApproximation.BinaryFraction.bandPredicateReadAllocation parent r b tau theta velocity actions hne read allocation) actions
    else 0

def queryInitialSupportAllocation {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a value : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  let raw := (OAI.EditApproximation.BinaryFraction.queryRawCentersWithWork N P F a value q).1
  let groups := (OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork N F exponent a value q).1
  let build := fun key =>
    let spacing := OAI.EditApproximation.seedGridSpacingWithWork key.1 P
    let side := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat key.1)
    let states := OAI.EditApproximation.BinaryFraction.cellStatesWithWork n (OAI.EditApproximation.bitWordValue spacing.1) side.1 key.2
    (states.1, spacing.2 + side.2 + states.2 + exponent + 3)
  let cells := (OAI.EditApproximation.arithmeticFlatMapWithWork build groups).1
  let online := (OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork N P F hP a value q).1
  OAI.EditApproximation.BinaryFraction.queryRawCentersAllocation N P F a value q + OAI.EditApproximation.BinaryFraction.queryGroupKeysAllocation N F exponent a value q +
    OAI.EditApproximation.arithmeticFlatMapAllocation build (OAI.EditApproximation.BinaryFraction.initialCellAllocation n P exponent) groups +
    OAI.EditApproximation.BinaryFraction.queryOnlineKeysAllocation N P F hP a value q + OAI.EditApproximation.arithmeticMapAllocation (fun _ => 1) online +
    2 * raw.length + cells.length + 1

def queryBandInputsWithWork {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F exponent : ℕ) (hP : 0 < P) (a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (q : OAI.EditApproximation.TargetInterval ny) :
    List (Fin M × OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let representatives := OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork N P F exponent hP a initial q
  let inputs := OAI.EditApproximation.BinaryFraction.queryWideInputsWithWork M parent P representatives.1
  (inputs.1, representatives.2 + inputs.2 + 1)

def queryEarlierInputsWithWork {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F exponent history : ℕ) (hP : 0 < P) (a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (q : OAI.EditApproximation.TargetInterval ny) :
    List (Fin M × ℕ × OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let representatives := OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork N P F exponent hP a initial q
  let raw := OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork M parent P history representatives.1
  let ordered := OAI.EditApproximation.queryOrderedHistoryInputsWithWork raw.1
  (ordered.1, representatives.2 + raw.2 + ordered.2 + 2)

def queryEarlierInputsAllocation {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F exponent history : ℕ) (hP : 0 < P) (a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (allocation : OAI.EditApproximation.TargetInterval ny → ℕ)
    (q : OAI.EditApproximation.TargetInterval ny) : ℕ :=
  let reps := (OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1
  OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesAllocation N P F exponent hP a initial allocation q +
    OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsAllocation M parent P history reps +
    OAI.EditApproximation.queryOrderedHistoryInputsAllocation (OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork M parent P history reps).1

def queryBandInputsAllocation {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F exponent : ℕ) (hP : 0 < P) (a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (allocation : OAI.EditApproximation.TargetInterval ny → ℕ)
    (q : OAI.EditApproximation.TargetInterval ny) : ℕ :=
  OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesAllocation N P F exponent hP a initial allocation q +
    OAI.EditApproximation.BinaryFraction.queryWideInputsAllocation M parent P (OAI.EditApproximation.BinaryFraction.queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.FiniteQuery

def run {ι : Type u_1} {κ : Type u_2} (ask : ι → OAI.EditApproximation.BinaryMemo ℚ → OAI.EditApproximation.RecursiveMemoResult κ) :
    OAI.EditApproximation.FiniteQuery ι → OAI.EditApproximation.BinaryMemo ℚ → OAI.EditApproximation.RecursiveMemoResult κ
  | .done result, memory => ⟨result, memory, [], 0, 0⟩
  | .read key next, memory =>
    let first := ask key memory
    let rest := run ask (next first.value) first.memory
    ⟨rest.value, rest.memory, first.freshKeys ++ rest.freshKeys,
      first.dictionaryVisits + rest.dictionaryVisits, first.requests + rest.requests⟩

def bind {ι : Type u_1} : OAI.EditApproximation.FiniteQuery ι → (ℚ → OAI.EditApproximation.FiniteQuery ι) → OAI.EditApproximation.FiniteQuery ι
  | .done result, next => next result
  | .read key continuation, next => .read key (fun result => bind (continuation result) next)

def mapKeys {ι : Type u_1} {κ : Type u_2} (f : ι → κ) : OAI.EditApproximation.FiniteQuery ι → OAI.EditApproximation.FiniteQuery κ
  | .done result => .done result
  | .read key next => .read (f key) (fun answer => mapKeys f (next answer))

def restrict {ι : Type u_1} (P : ι → Prop) [DecidablePred P] : OAI.EditApproximation.FiniteQuery ι → OAI.EditApproximation.FiniteQuery {key // P key}
  | .done result => .done result
  | .read key next => if h : P key then
      .read ⟨key, h⟩ (fun answer => restrict P (next answer))
    else restrict P (next 0)

def requestWork {ι : Type u_1} {κ : Type u_2} (ask : ι → OAI.EditApproximation.BinaryMemo ℚ → OAI.EditApproximation.RecursiveMemoResult κ)
    (cost : ι → OAI.EditApproximation.BinaryMemo ℚ → ℕ) : OAI.EditApproximation.FiniteQuery ι → OAI.EditApproximation.BinaryMemo ℚ → ℕ
  | .done _, _ => 0
  | .read key next, memory =>
      let first := ask key memory
      cost key memory + requestWork ask cost (next first.value) first.memory

def collect {ι : Type u_1} {κ : Type u_2} (reader : κ → OAI.EditApproximation.FiniteQuery ι) :
    List κ → (List ℚ → OAI.EditApproximation.FiniteQuery ι) → OAI.EditApproximation.FiniteQuery ι
  | [], next => next []
  | key :: keys, next => OAI.EditApproximation.FiniteQuery.bind (reader key) fun result =>
      collect reader keys (fun results => next (result :: results))

end OAI.EditApproximation.FiniteQuery

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def physicalInitialQuery {ι : Type u_1} {α : Type u_2} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F : ℕ) (A : ℚ)
    (seedRead : OAI.EditApproximation.PhysicalEntry M J target.length → OAI.EditApproximation.FiniteQuery ι)
    (state : OAI.EditApproximation.PhysicalEntry M J target.length) : OAI.EditApproximation.FiniteQuery ι :=
  let piece := OAI.EditApproximation.physicalSource source state.1
  if piece.length ≤ 1 then .done (OAI.EditApproximation.shortSourceCost piece (OAI.EditApproximation.substring target state.2.lo state.2.hi))
  else OAI.EditApproximation.FiniteQuery.bind (seedRead state) fun answer =>
    let value := ⌈answer⌉₊
    let keys := OAI.EditApproximation.rawInitialConeCenters N P A value state.2
    OAI.EditApproximation.FiniteQuery.collect (fun q => seedRead (state.1, q)) keys fun answers =>
      let localTable := fun q => if q = state.2 then value
        else ⌈OAI.EditApproximation.finiteAnswerTable keys answers q⌉₊
      .done (OAI.EditApproximation.localInitialConeTable piece target localTable N P F A (OAI.EditApproximation.refinementFactor A F) state.2)

def queryInitialGather {ι : Type u_1} {β : Type u_2} {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n)
    (reader : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (next : List (OAI.EditApproximation.TargetInterval n) → List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery ι β) : OAI.EditApproximation.BitQuery ι β :=
  (reader q).bind fun value =>
    (OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryInitialSupportWithWork N P F exponent hP a value q)).bind
      fun keys => OAI.EditApproximation.BitQuery.collect reader keys (next keys)

def queryBandGather {ι : Type u_1} {β : Type u_2} {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F exponent : ℕ) (hP : 0 < P) (a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (q : OAI.EditApproximation.TargetInterval ny)
    (massReader initialReader : (Fin M × OAI.EditApproximation.TargetInterval ny) → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (next : List (Fin M × OAI.EditApproximation.TargetInterval ny) → List OAI.EditApproximation.BinaryFraction → List OAI.EditApproximation.BinaryFraction →
      OAI.EditApproximation.BitQuery ι β) : OAI.EditApproximation.BitQuery ι β :=
  (OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryBandInputsWithWork M parent N P F exponent hP a initial q)).bind
    fun keys => OAI.EditApproximation.BitQuery.collect massReader keys fun mass =>
      OAI.EditApproximation.BitQuery.collect initialReader keys (next keys mass)

def physicalRefinementMassQuery {M J ny : ℕ} (pass copy T S t : ℕ) (ht : 0 < t)
    (node : OAI.EditApproximation.PhysicalNode M J) (hbelow : node.1.val < J) (q : OAI.EditApproximation.TargetInterval ny)
    (input : Fin M × OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J ny //
      child.combinedRank T S < (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S} :=
  OAI.EditApproximation.FiniteQuery.collect (fun j : Fin T => OAI.EditApproximation.physicalRefinementWarmupRead pass copy T S t ht node q
    (OAI.EditApproximation.physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
    j.val (Nat.le_of_lt j.isLt) input.2) (List.ofFn fun j : Fin T => j)
    (fun values => .done (values.sum / T))

def physicalMedianSeedQuery {M J ny : ℕ} (N T S copies multiplier : ℕ)
    (parent : OAI.EditApproximation.PhysicalTableRequest M J ny) (hpass : 0 < parent.pass) (state : OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J ny //
      child.combinedRank T S < parent.combinedRank T S} :=
  OAI.EditApproximation.FiniteQuery.collect (fun copy : Fin copies => OAI.EditApproximation.previousPassRead T S parent hpass state copy.val)
    (List.finRange copies) fun values =>
      .done (min N (OAI.EditApproximation.upperMedian (values.map fun value => ⌈(multiplier : ℚ) * value⌉₊)) : ℕ)

def globalSeedRead {M J ny : ℕ} (N T S copies : ℕ) (multiplier : ℕ → ℕ)
    (initial : OAI.EditApproximation.PhysicalEntry M J ny → ℕ) (parent : OAI.EditApproximation.PhysicalTableRequest M J ny)
    (state : OAI.EditApproximation.PhysicalEntry M J ny) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J ny //
      child.combinedRank T S < parent.combinedRank T S} :=
  if state.1 = parent.node then
    if hp : parent.pass = 0 then .done (initial state : ℚ)
    else OAI.EditApproximation.physicalMedianSeedQuery N T S copies (multiplier (parent.pass - 1)) parent
      (Nat.pos_of_ne_zero hp) state.2
  else .done 0

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.UnreducedRational

def value (a : OAI.EditApproximation.UnreducedRational) : ℚ := (a.num : ℚ) / a.den

def zero : OAI.EditApproximation.UnreducedRational := ⟨0, 1, by decide⟩

def mul (a b : OAI.EditApproximation.UnreducedRational) : OAI.EditApproximation.UnreducedRational :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def lt (a b : OAI.EditApproximation.UnreducedRational) : Bool := decide (a.num * b.den < b.num * a.den)

def inv (a : OAI.EditApproximation.UnreducedRational) : OAI.EditApproximation.UnreducedRational :=
  if h : a.num = 0 then OAI.EditApproximation.UnreducedRational.zero else
    ⟨a.num.sign * a.den, a.num.natAbs, Int.natAbs_pos.mpr h⟩

def div (a b : OAI.EditApproximation.UnreducedRational) : OAI.EditApproximation.UnreducedRational := a.mul b.inv

end OAI.EditApproximation.UnreducedRational

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset EditDistortion

inductive CoarseSourceTree (B : ℕ) (α : Type u) : ℕ → Type u
  | leaf (letter : Option α) : CoarseSourceTree B α 0
  | branch {D : ℕ} (children : Fin B → CoarseSourceTree B α D) : CoarseSourceTree B α (D + 1)

def coarseTargetFrame {α : Type u} (k : ℕ) (target : List α) : List (Option α) :=
  (List.replicate k none ++ target.map some) ++ List.replicate k none

def coarseRootShift (k : ℕ) : Fin (2 * k + 1) := ⟨k, by omega⟩

def endpointActionConnection {n M : ℕ} (q : OAI.EditApproximation.TargetInterval n)
    (states : Fin M → OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.connectionBudget q.lo (List.ofFn states) q.hi

def coarseSourceTreeOfList (B : ℕ) {α : Type u} :
    (D : ℕ) → List α → OAI.EditApproximation.CoarseSourceTree B α D
  | 0, source => .leaf source.head?
  | D + 1, source => .branch (fun i =>
      coarseSourceTreeOfList B D ((source.drop (i.val * B ^ D)).take (B ^ D)))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

open Finset

def groupIndexWithWork {M : ℕ} (h : OAI.EditApproximation.BinaryFraction) (envelope values : Vector OAI.EditApproximation.BinaryFraction M)
    (indices : List (Fin M)) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let terms := OAI.EditApproximation.BinaryFraction.groupTermsWithWork h envelope values indices
  let total := OAI.EditApproximation.BinaryFraction.sumListWithWork terms.1
  (total.1, terms.2 + total.2 + 1)

def endpointDistanceWithWork {n : ℕ} (q r : OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let left := OAI.EditApproximation.BinaryFraction.distanceWithWork (OAI.EditApproximation.BinaryFraction.nat q.lo) (OAI.EditApproximation.BinaryFraction.nat r.lo)
  let right := OAI.EditApproximation.BinaryFraction.distanceWithWork (OAI.EditApproximation.BinaryFraction.nat q.hi) (OAI.EditApproximation.BinaryFraction.nat r.hi)
  let result := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork left.1 right.1
  (result.1, left.2 + right.2 + result.2 + Nat.size q.lo + Nat.size q.hi +
    Nat.size r.lo + Nat.size r.hi + 3)

def endpointConnectionWithWork {n M : ℕ} (r : OAI.EditApproximation.TargetInterval n)
    (states : Fin M → OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let result := OAI.EditApproximation.BinaryFraction.connectionWithWork (OAI.EditApproximation.BinaryFraction.nat r.lo) (OAI.EditApproximation.BinaryFraction.nat r.hi) (List.ofFn states)
  (result.1, result.2 + Nat.size r.lo + Nat.size r.hi + M + 2)

def stateGapWithWork {n : ℕ} (sourceLength : ℕ) (r : OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let targetLength := OAI.EditApproximation.BinaryFraction.subWithWork (OAI.EditApproximation.BinaryFraction.nat r.hi) (OAI.EditApproximation.BinaryFraction.nat r.lo)
  let result := OAI.EditApproximation.BinaryFraction.subWithWork targetLength.1 (OAI.EditApproximation.BinaryFraction.nat sourceLength)
  (result.1, targetLength.2 + result.2 + Nat.size r.hi + Nat.size r.lo + Nat.size sourceLength + 2)

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

def groupScaleSourceWithWork {M : ℕ} (k : ℕ) (h : OAI.EditApproximation.BinaryFraction)
    (envelope values : Vector OAI.EditApproximation.BinaryFraction M) (draw : Fin k → Fin M × ℕ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let indices := if k = M then (List.finRange M, 0) else OAI.EditApproximation.arithmeticMapWithWork draw (List.finRange k)
  let subtotal := OAI.EditApproximation.BinaryFraction.groupIndexWithWork h envelope values indices.1
  let factor := if k = M then (OAI.EditApproximation.BinaryFraction.one, 1) else OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat M) (OAI.EditApproximation.BinaryFraction.nat k)
  let result := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork factor.1 subtotal.1
  (result.1, indices.2 + subtotal.2 + factor.2 + result.2 + Nat.size M + Nat.size k + 3)

def endpointScoreReadWithWork {n M : ℕ} (r : OAI.EditApproximation.TargetInterval n)
    (read : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) (states : Fin M → OAI.EditApproximation.TargetInterval n) :
    OAI.EditApproximation.BinaryFraction × ℕ :=
  let words := OAI.EditApproximation.arithmeticMapWithWork (fun i => read i (states i)) (List.finRange M)
  let connection := OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork r states
  let children := OAI.EditApproximation.BinaryFraction.sumListWithWork words.1
  let result := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork connection.1 children.1
  (result.1, words.2 + connection.2 + children.2 + result.2 + 2)

def initialConeWithWork {n : ℕ} (sourceLength : ℕ) (U : OAI.EditApproximation.TargetInterval n → ℕ)
    (a L : OAI.EditApproximation.BinaryFraction) (query center : OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let gap := OAI.EditApproximation.BinaryFraction.stateGapWithWork sourceLength center
  let seed := OAI.EditApproximation.BinaryFraction.scaledSeedWithWork (U center) a gap.1
  let distance := OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork query center
  let spatial := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork L distance.1
  let result := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork seed.1 spatial.1
  (result.1, gap.2 + seed.2 + distance.2 + spatial.2 + result.2 + 4)

def endpointActionWithWork {ny M : ℕ} (center : OAI.EditApproximation.TargetInterval ny)
    (states : Fin M → OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval ny) (Fin M × OAI.EditApproximation.TargetInterval ny) M × ℕ :=
  let connection := OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork center states
  (⟨center, connection.1, fun i => (i, states i)⟩, connection.2 + M + 1)

def endpointScoreReadAllocation {n M : ℕ} (r : OAI.EditApproximation.TargetInterval n)
    (read : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (footprint : Fin M → OAI.EditApproximation.TargetInterval n → ℕ) (states : Fin M → OAI.EditApproximation.TargetInterval n) : ℕ :=
  let words := (OAI.EditApproximation.arithmeticMapWithWork (fun i => read i (states i)) (List.finRange M)).1
  OAI.EditApproximation.arithmeticMapAllocation (fun i => footprint i (states i)) (List.finRange M) +
    OAI.EditApproximation.BinaryFraction.endpointConnectionAllocation r states + OAI.EditApproximation.BinaryFraction.sumListAllocation words +
    OAI.EditApproximation.BinaryFraction.canonicalAddAllocation (OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork r states).1 (OAI.EditApproximation.BinaryFraction.sumListWithWork words).1 + 0

def initialConeAllocation {n : ℕ} (sourceLength U : ℕ) (a L : OAI.EditApproximation.BinaryFraction)
    (query center : OAI.EditApproximation.TargetInterval n) : ℕ :=
  let gap := (OAI.EditApproximation.BinaryFraction.stateGapWithWork sourceLength center).1
  let seed := (OAI.EditApproximation.BinaryFraction.scaledSeedWithWork U a gap).1
  let distance := (OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork query center).1
  let spatial := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork L distance).1
  OAI.EditApproximation.BinaryFraction.stateGapAllocation sourceLength center + OAI.EditApproximation.BinaryFraction.scaledSeedAllocation U a gap +
    OAI.EditApproximation.BinaryFraction.endpointDistanceAllocation query center + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation L distance + OAI.EditApproximation.BinaryFraction.canonicalAddAllocation seed spatial

def groupScaleSourceAllocation {M : ℕ} (k : ℕ) (h : OAI.EditApproximation.BinaryFraction)
    (envelope values : Vector OAI.EditApproximation.BinaryFraction M) (draw : Fin k → Fin M × ℕ)
    (allocation : Fin k → ℕ) : ℕ :=
  let indices := if k = M then (List.finRange M, 0) else OAI.EditApproximation.arithmeticMapWithWork draw (List.finRange k)
  let factor := if k = M then (OAI.EditApproximation.BinaryFraction.one, 1) else OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.nat M) (OAI.EditApproximation.BinaryFraction.nat k)
  (if k = M then 0 else OAI.EditApproximation.arithmeticMapAllocation allocation (List.finRange k)) +
    OAI.EditApproximation.BinaryFraction.groupIndexAllocation h envelope values indices.1 +
    (if k = M then 0 else OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.nat M) (OAI.EditApproximation.BinaryFraction.nat k)) +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation factor.1 (OAI.EditApproximation.BinaryFraction.groupIndexWithWork h envelope values indices.1).1 +
    Nat.size M + Nat.size k

def gapGuardAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (envelope : Vector OAI.EditApproximation.BinaryFraction M) (rounded : Vector (OAI.EditApproximation.TargetInterval ny) M) (i : Fin M) : ℕ :=
  let sourceLength := (OAI.EditApproximation.binaryNaturalSubtractWithWork (OAI.EditApproximation.sourceChild parent i).hi (OAI.EditApproximation.sourceChild parent i).lo).1
  let gap := (OAI.EditApproximation.BinaryFraction.stateGapWithWork (OAI.EditApproximation.bitWordValue sourceLength) (rounded.get i)).1
  let bound := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 2) (envelope.get i)).1
  OAI.EditApproximation.bitSubtractAllocation (OAI.EditApproximation.sourceChild parent i).hi.bits (OAI.EditApproximation.sourceChild parent i).lo.bits false +
    OAI.EditApproximation.BinaryFraction.stateGapAllocation (OAI.EditApproximation.bitWordValue sourceLength) (rounded.get i) +
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 2) (envelope.get i) + OAI.EditApproximation.BinaryFraction.leAllocation gap.absolute bound

def wideMinimumReadWithWork {n M : ℕ} (r : OAI.EditApproximation.TargetInterval n)
    (read : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval n)) (hne : actions ≠ []) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let fallback := OAI.EditApproximation.BinaryFraction.endpointScoreReadWithWork r read (actions.head hne)
  let scores := OAI.EditApproximation.arithmeticMapWithWork (OAI.EditApproximation.BinaryFraction.endpointScoreReadWithWork r read) actions
  let result := OAI.EditApproximation.BinaryFraction.minimumWithWork fallback.1 scores.1
  (result.1, fallback.2 + scores.2 + result.2 + 2)

def groupMemberSourceWithWork {M T : ℕ} (scales : Fin T → OAI.EditApproximation.BinaryFraction) (count : Fin T → ℕ)
    (connection : OAI.EditApproximation.BinaryFraction) (envelope values : Vector OAI.EditApproximation.BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M × ℕ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let terms := OAI.EditApproximation.arithmeticMapWithWork (fun s => OAI.EditApproximation.BinaryFraction.groupScaleSourceWithWork (count s) (scales s)
    envelope values (draw s)) (List.finRange T)
  let subtotal := OAI.EditApproximation.BinaryFraction.sumListWithWork terms.1
  let result := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork connection subtotal.1
  (result.1, terms.2 + subtotal.2 + result.2 + 1)

def wideActionsFromRepresentativesWithWork {nx ny : ℕ} (M : ℕ)
    (parent : OAI.EditApproximation.TargetInterval nx) (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) (P : ℕ) :
    List (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval ny) (Fin M × OAI.EditApproximation.TargetInterval ny) M) × ℕ :=
  OAI.EditApproximation.arithmeticFlatMapWithWork (fun br =>
    let grids := OAI.EditApproximation.wideActionGridWithWork M parent br.2 br.1 P
    let actions := OAI.EditApproximation.arithmeticMapWithWork (fun states => OAI.EditApproximation.BinaryFraction.endpointActionWithWork br.2 states.get) grids.1
    (actions.1, grids.2 + actions.2 + 1)) representatives

def initialConeReadWithWork {n : ℕ} (sourceLength : ℕ)
    (read : OAI.EditApproximation.TargetInterval n → List Bool × ℕ) (a L : OAI.EditApproximation.BinaryFraction)
    (query center : OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let seed := read center
  let result := OAI.EditApproximation.BinaryFraction.initialConeWithWork sourceLength (fun _ => OAI.EditApproximation.bitWordValue seed.1) a L query center
  (result.1, seed.2 + result.2)

def wideMinimumReadAllocation {n M : ℕ} (r : OAI.EditApproximation.TargetInterval n)
    (read : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (footprint : Fin M → OAI.EditApproximation.TargetInterval n → ℕ)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval n)) (hne : actions ≠ []) : ℕ :=
  let fallback := (OAI.EditApproximation.BinaryFraction.endpointScoreReadWithWork r read (actions.head hne)).1
  let scores := (OAI.EditApproximation.arithmeticMapWithWork (OAI.EditApproximation.BinaryFraction.endpointScoreReadWithWork r read) actions).1
  OAI.EditApproximation.BinaryFraction.endpointScoreReadAllocation r read footprint (actions.head hne) +
    OAI.EditApproximation.arithmeticMapAllocation (OAI.EditApproximation.BinaryFraction.endpointScoreReadAllocation r read footprint) actions +
    OAI.EditApproximation.BinaryFraction.minimumAllocation fallback scores + 0

def groupMemberSourceAllocation {M T : ℕ} (scales : Fin T → OAI.EditApproximation.BinaryFraction) (count : Fin T → ℕ)
    (connection : OAI.EditApproximation.BinaryFraction) (envelope values : Vector OAI.EditApproximation.BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M × ℕ)
    (allocation : ∀ s : Fin T, Fin (count s) → ℕ) : ℕ :=
  let terms := (OAI.EditApproximation.arithmeticMapWithWork (fun s => OAI.EditApproximation.BinaryFraction.groupScaleSourceWithWork (count s) (scales s)
    envelope values (draw s)) (List.finRange T)).1
  OAI.EditApproximation.arithmeticMapAllocation (fun s => OAI.EditApproximation.BinaryFraction.groupScaleSourceAllocation (count s) (scales s) envelope values (draw s) (allocation s)) (List.finRange T) +
    OAI.EditApproximation.BinaryFraction.sumListAllocation terms + OAI.EditApproximation.BinaryFraction.canonicalAddAllocation connection (OAI.EditApproximation.BinaryFraction.sumListWithWork terms).1

def wideActionsFromRepresentativesAllocation {nx ny : ℕ} (M : ℕ) (parent : OAI.EditApproximation.TargetInterval nx)
    (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) (P : ℕ) : ℕ :=
  OAI.EditApproximation.arithmeticFlatMapAllocation (fun br =>
    let grids := OAI.EditApproximation.wideActionGridWithWork M parent br.2 br.1 P
    let actions := OAI.EditApproximation.arithmeticMapWithWork (fun states => OAI.EditApproximation.BinaryFraction.endpointActionWithWork br.2 states.get) grids.1
    (actions.1, grids.2 + actions.2 + 1))
    (fun br => OAI.EditApproximation.wideActionGridAllocation M parent br.2 br.1 P +
      OAI.EditApproximation.arithmeticMapAllocation (fun states => OAI.EditApproximation.BinaryFraction.endpointActionAllocation br.2 states.get)
        (OAI.EditApproximation.wideActionGridWithWork M parent br.2 br.1 P).1) representatives

def representativeFromActionsReadWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (sourceLength b : ℕ) (tau theta : OAI.EditApproximation.BinaryFraction)
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) : List (Fin M → OAI.EditApproximation.TargetInterval ny) × ℕ :=
  if hne : actions = [] then ([], 1) else
    let Z := OAI.EditApproximation.BinaryFraction.wideMinimumReadWithWork r read actions hne
    let positive := OAI.EditApproximation.BinaryFraction.ltWithWork OAI.EditApproximation.BinaryFraction.zero Z.1
    if positive.1 then
      let gap := OAI.EditApproximation.BinaryFraction.stateGapWithWork sourceLength r
      let velocity := OAI.EditApproximation.BinaryFraction.divWithWork gap.1 Z.1
      let result := OAI.EditApproximation.BinaryFraction.bandFromActionsReadWithWork parent r b tau theta velocity.1 read actions hne
      (result.1, Z.2 + positive.2 + gap.2 + velocity.2 + result.2 + 3)
    else ([], Z.2 + positive.2 + 2)

def physicalContinuationReadWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) (P F : ℕ)
    (delta fallback : OAI.EditApproximation.BinaryFraction)
    (old current : Fin M × OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (groups online : List (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval ny) (Fin M × OAI.EditApproximation.TargetInterval ny) M))
    (query : OAI.EditApproximation.TargetInterval ny) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let wide := OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork M parent representatives P
  let L := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 128) (OAI.EditApproximation.BinaryFraction.nat F)
  let result := OAI.EditApproximation.BinaryFraction.localContinuationReadWithWork OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork L.1 delta fallback
    old current query wide.1 groups online
  (result.1, wide.2 + L.2 + result.2 + 1)

def initialMinimumReadWithWork {n : ℕ} (sourceLength : ℕ)
    (read : OAI.EditApproximation.TargetInterval n → List Bool × ℕ) (N F : ℕ) (a : OAI.EditApproximation.BinaryFraction)
    (query : OAI.EditApproximation.TargetInterval n) (centers : List (OAI.EditApproximation.TargetInterval n)) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let queryWord := read query
  let zeroTest := OAI.EditApproximation.naturalEqualWithWork (OAI.EditApproximation.bitWordValue queryWord.1) 0
  if zeroTest.1 then (OAI.EditApproximation.BinaryFraction.zero, queryWord.2 + zeroTest.2 + 1) else
    let L := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 32) (OAI.EditApproximation.BinaryFraction.nat F)
    let coefficient := OAI.EditApproximation.BinaryFraction.canonicalAddWithWork L.1 OAI.EditApproximation.BinaryFraction.one
    let fallback := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork coefficient.1 (OAI.EditApproximation.BinaryFraction.nat N)
    let scores := OAI.EditApproximation.arithmeticMapWithWork (OAI.EditApproximation.BinaryFraction.initialConeReadWithWork sourceLength read a L.1 query) centers
    let result := OAI.EditApproximation.BinaryFraction.minimumWithWork fallback.1 scores.1
    (result.1, queryWord.2 + zeroTest.2 + L.2 + coefficient.2 + fallback.2 + scores.2 + result.2 +
      Nat.size F + Nat.size N + 6)

def localWarmupReadKernelWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F : ℕ) (a : OAI.EditApproximation.BinaryFraction) (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (child : Fin M × OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) (query : OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.BinaryFraction × ℕ :=
  let fallback := initial query
  let representatives := OAI.EditApproximation.BinaryFraction.localRepresentativeReadWithWork N P F a initial query
  let actions := OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork M parent representatives.1 P
  let L := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 128) (OAI.EditApproximation.BinaryFraction.nat F)
  let result := OAI.EditApproximation.BinaryFraction.bellmanReadWithWork OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork L.1 fallback.1 child query actions.1
  (result.1, fallback.2 + representatives.2 + actions.2 + L.2 + result.2 + 3)

def representativeFromActionsReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (r : OAI.EditApproximation.TargetInterval ny) (sourceLength b : ℕ) (tau theta : OAI.EditApproximation.BinaryFraction)
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ)
    (actions : List (Fin M → OAI.EditApproximation.TargetInterval ny)) : ℕ :=
  if hne : actions = [] then 0 else
    let Z := (OAI.EditApproximation.BinaryFraction.wideMinimumReadWithWork r read actions hne).1
    OAI.EditApproximation.BinaryFraction.wideMinimumReadAllocation r read allocation actions hne + OAI.EditApproximation.BinaryFraction.ltAllocation OAI.EditApproximation.BinaryFraction.zero Z +
      if (OAI.EditApproximation.BinaryFraction.ltWithWork OAI.EditApproximation.BinaryFraction.zero Z).1 then
        OAI.EditApproximation.BinaryFraction.stateGapAllocation sourceLength r + OAI.EditApproximation.BinaryFraction.divAllocation (OAI.EditApproximation.BinaryFraction.stateGapWithWork sourceLength r).1 Z +
          OAI.EditApproximation.BinaryFraction.bandFromActionsReadAllocation parent r b tau theta
            (OAI.EditApproximation.BinaryFraction.divWithWork (OAI.EditApproximation.BinaryFraction.stateGapWithWork sourceLength r).1 Z).1 read allocation actions hne
      else 0

def physicalContinuationReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (representatives : List (ℕ × OAI.EditApproximation.TargetInterval ny)) (P F : ℕ) (delta fallback : OAI.EditApproximation.BinaryFraction)
    (old current : Fin M × OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (oldAllocation currentAllocation : Fin M × OAI.EditApproximation.TargetInterval ny → ℕ)
    (groups online : List (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval ny) (Fin M × OAI.EditApproximation.TargetInterval ny) M))
    (query : OAI.EditApproximation.TargetInterval ny) : ℕ :=
  OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesAllocation M parent representatives P + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 128) (OAI.EditApproximation.BinaryFraction.nat F) +
    OAI.EditApproximation.BinaryFraction.localContinuationReadAllocation OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork OAI.EditApproximation.BinaryFraction.endpointDistanceAllocation
      (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 128) (OAI.EditApproximation.BinaryFraction.nat F)).1 delta fallback old current oldAllocation currentAllocation query
      (OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork M parent representatives P).1 groups online

def localWarmupReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (N P F : ℕ) (a : OAI.EditApproximation.BinaryFraction) (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (initialAllocation : OAI.EditApproximation.TargetInterval ny → ℕ) (child : Fin M × OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (childAllocation : Fin M × OAI.EditApproximation.TargetInterval ny → ℕ) (query : OAI.EditApproximation.TargetInterval ny) : ℕ :=
  let representatives := (OAI.EditApproximation.BinaryFraction.localRepresentativeReadWithWork N P F a initial query).1
  let actions := (OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork M parent representatives P).1
  initialAllocation query + OAI.EditApproximation.BinaryFraction.localRepresentativeReadAllocation N P F a initial initialAllocation query +
    OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesAllocation M parent representatives P + OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 128) (OAI.EditApproximation.BinaryFraction.nat F) +
    OAI.EditApproximation.BinaryFraction.bellmanReadAllocation OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork OAI.EditApproximation.BinaryFraction.endpointDistanceAllocation
      (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 128) (OAI.EditApproximation.BinaryFraction.nat F)).1 (initial query).1 child childAllocation query actions

def preparedRepresentativeReadWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (center : OAI.EditApproximation.TargetInterval ny) (sourceLength b P : ℕ) (tau theta : OAI.EditApproximation.BinaryFraction)
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ) : List (Fin M → OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let wide := OAI.EditApproximation.wideActionGridWithWork M parent center b P
  let result := OAI.EditApproximation.BinaryFraction.representativeFromActionsReadWithWork parent center sourceLength b tau theta read
    (wide.1.map Vector.get)
  (result.1, wide.2 + result.2 + wide.1.length + 1)

def initialProgramReadWithWork {n : ℕ} (sourceLength N P F : ℕ) (A a : OAI.EditApproximation.BinaryFraction)
    (read : OAI.EditApproximation.TargetInterval n → List Bool × ℕ) (query : OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let centers := OAI.EditApproximation.BinaryFraction.initialCentersReadWithWork N P A read query
  let result := OAI.EditApproximation.BinaryFraction.initialMinimumReadWithWork sourceLength read N F a query centers.1
  (result.1, centers.2 + result.2 + 1)

def preparedRepresentativeReadAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (center : OAI.EditApproximation.TargetInterval ny) (sourceLength b P : ℕ) (tau theta : OAI.EditApproximation.BinaryFraction)
    (read : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ) : ℕ :=
  let wide := (OAI.EditApproximation.wideActionGridWithWork M parent center b P).1
  OAI.EditApproximation.wideActionGridAllocation M parent center b P + wide.length +
    OAI.EditApproximation.BinaryFraction.representativeFromActionsReadAllocation parent center sourceLength b tau theta read allocation (wide.map Vector.get)

def queryRefinementFinishAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx) (N P F : ℕ)
    (a delta : OAI.EditApproximation.BinaryFraction) (initial : OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (initialAllocation : OAI.EditApproximation.TargetInterval ny → ℕ) (t : ℕ)
    (earlierKeys : List (Fin M × ℕ × OAI.EditApproximation.TargetInterval ny)) (earlierWords : List OAI.EditApproximation.BinaryFraction)
    (groups online : List (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval ny) (Fin M × OAI.EditApproximation.TargetInterval ny) M))
    (currentKeys : List (Fin M × OAI.EditApproximation.TargetInterval ny)) (currentWords : List OAI.EditApproximation.BinaryFraction)
    (query : OAI.EditApproximation.TargetInterval ny) : ℕ :=
  initialAllocation query + OAI.EditApproximation.BinaryFraction.localRepresentativeReadAllocation N P F a initial initialAllocation query +
    OAI.EditApproximation.BinaryFraction.physicalContinuationReadAllocation parent (OAI.EditApproximation.BinaryFraction.localRepresentativeReadWithWork N P F a initial query).1 P F delta (initial query).1
      (OAI.EditApproximation.BinaryFraction.queryHistoryReadWithWork earlierKeys earlierWords (t - 1))
      (fun input => OAI.EditApproximation.BinaryFraction.queryChildReadWithWork currentKeys currentWords input.1 input.2)
      (OAI.EditApproximation.BinaryFraction.queryHistoryReadAllocation earlierKeys earlierWords (t - 1))
      (fun input => OAI.EditApproximation.BinaryFraction.queryChildReadAllocation currentKeys currentWords input.1 input.2) groups online query

def queryOnlineRangeWithWork {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (P exponent H : ℕ) (tau : OAI.EditApproximation.BinaryFraction)
    (child : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (key : ℕ × OAI.EditApproximation.TargetInterval ny) : ℕ × ℕ :=
  let width := OAI.EditApproximation.saturatingSubtractWithWork parent.hi parent.lo
  let band := OAI.EditApproximation.BinaryFraction.preparedRepresentativeReadWithWork parent key.2 (OAI.EditApproximation.bitWordValue width.1) key.1 P
    tau (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) child
  let setup := OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork H band.1
  let power := OAI.EditApproximation.bitPowerWithWork setup.1.bits 80
  let mass := OAI.EditApproximation.triangularMassWithWork (OAI.EditApproximation.bitWordValue power.1)
  (OAI.EditApproximation.bitWordValue mass.1, width.2 + band.2 + setup.2 + power.2 + mass.2 + 4)

def cachedInitialProgramReadWithWork {n : ℕ} (sourceLength N P F : ℕ) (A a : OAI.EditApproximation.BinaryFraction)
    (read : OAI.EditApproximation.TargetInterval n → List Bool × ℕ) (query : OAI.EditApproximation.TargetInterval n) : OAI.EditApproximation.BinaryFraction × ℕ :=
  OAI.EditApproximation.BinaryFraction.finishCachedWithWork (OAI.EditApproximation.BinaryFraction.initialProgramReadWithWork sourceLength N P F A a read query)
    [true] (by decide) 0

def queryOnlineRangeAllocation {nx ny M : ℕ} (parent : OAI.EditApproximation.TargetInterval nx)
    (P exponent H : ℕ) (tau : OAI.EditApproximation.BinaryFraction)
    (child : Fin M → OAI.EditApproximation.TargetInterval ny → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : Fin M → OAI.EditApproximation.TargetInterval ny → ℕ) (key : ℕ × OAI.EditApproximation.TargetInterval ny) : ℕ :=
  let width := (OAI.EditApproximation.saturatingSubtractWithWork parent.hi parent.lo).1
  let band := (OAI.EditApproximation.BinaryFraction.preparedRepresentativeReadWithWork parent key.2 (OAI.EditApproximation.bitWordValue width) key.1 P
    tau (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) child).1
  let setup := (OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork H band).1
  let power := (OAI.EditApproximation.bitPowerWithWork setup.bits 80).1
  OAI.EditApproximation.saturatingSubtractAllocation parent.hi parent.lo +
    OAI.EditApproximation.BinaryFraction.preparedRepresentativeReadAllocation parent key.2 (OAI.EditApproximation.bitWordValue width) key.1 P
      tau (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) child allocation + OAI.EditApproximation.BinaryFraction.onlineIndexSetupAllocation H band +
    OAI.EditApproximation.bitPowerAllocation setup.bits 80 + OAI.EditApproximation.triangularMassAllocation (OAI.EditApproximation.bitWordValue power)

end OAI.EditApproximation.BinaryFraction

end


