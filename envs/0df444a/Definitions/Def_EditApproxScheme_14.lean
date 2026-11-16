-- Prove2me | Definitions.Def_EditApproxScheme_14
-- name    : EditApproxScheme_14
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:49:12.958593+00:00
-- url     : https://prove2.me/theorems/46860496-e9f7-4793-a4cd-327825d40c44
-- title:
--   Edit-distance approximation scheme, part 14 of 20: the physical family answer
-- statement:
--   This is **part 14 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains the choice of a cell-group action, local online and random-source step queries, physical scalar codes, random-data requests, entry capacities, supported child maps, charged global random queries, the physical family answer, family memo keys, computed family seeds and codes, and coarse initial values. It also proves 4 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L8007-L8718 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 14 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_13

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset

def chooseCellGroupAction {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (b P F thetaExponent Q : ℕ) (tau a : ℚ)
    (parentInitial : OAI.EditApproximation.TargetInterval target.length → ℚ)
    (child initial value : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length,
      Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) → Fin M) :
    Option (OAI.EditApproximation.RationalBellmanAction (OAI.EditApproximation.TargetInterval target.length) (Fin M × OAI.EditApproximation.TargetInterval target.length) M) :=
  let members := OAI.EditApproximation.cellUnskippedBands source target parent b P F thetaExponent tau a parentInitial child initial cell
  if h : members = [] then none else some (OAI.EditApproximation.chooseUnskippedGroup Q value members h draw).rationalAction

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {α : Type u_1} {M : ℕ} (source target : List α) (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ) (parentInitial : TargetInterval target.length → ℚ) (child initial current : Fin M → TargetInterval target.length → ℚ) (draw : CellGroupDraws M F Q)

local notation (name := source_Combinatorics_EditApproximation_Geometry_LocalGroupCones_8) "theta" => (2 : ℚ) ^ (-(exponent : ℤ))

def localCellGroupActions (q : OAI.EditApproximation.TargetInterval target.length) : List (OAI.EditApproximation.PhysicalRationalAction M target.length) :=
  ((OAI.EditApproximation.dyadicScales N).filter fun (b : ℕ) => decide
    (parentInitial q / (16 * F) ≤ b ∧ (b : ℚ) ≤ 8 * a * parentInitial q)).flatMap fun (b : ℕ) =>
      (OAI.EditApproximation.localTargetCells (theta * b) ⌈parentInitial q⌉₊ q).filterMap fun cell =>
        OAI.EditApproximation.chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial
          child initial current cell (draw b cell)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_1} {α : Type u_2} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ) (t : ℕ) (parentInitial : TargetInterval target.length → ℚ) (child initial : Fin M → TargetInterval target.length → ℚ) (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι) (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

theorem _root_.OAI.EditApproximation.Lemmas.mixedRadix_injective {radix : ℕ} {lo : ℕ} {lo' : ℕ} {hi : ℕ} {hi' : ℕ} (hlo : LT.lt.{0} lo radix) (hlo' : LT.lt.{0} lo' radix) (heq : Eq.{1} (HAdd.hAdd.{0, 0, 0} lo (HMul.hMul.{0, 0, 0} radix hi)) (HAdd.hAdd.{0, 0, 0} lo' (HMul.hMul.{0, 0, 0} radix hi'))) : lo = lo' ∧ hi = hi' := by
  have hmod := congrArg (fun n => n % radix) heq
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hlo'] at hmod
  refine ⟨hmod, ?_⟩
  apply Nat.mul_left_cancel (by omega : 0 < radix)
  omega

theorem _root_.OAI.EditApproximation.Lemmas.childInputCode_injective (M : ℕ) (n : ℕ) :
    Function.Injective (@OAI.EditApproximation.childInputCode M n) := by
  rintro ⟨i, q⟩ ⟨i', q'⟩ heq
  obtain ⟨hi, hq⟩ := OAI.EditApproximation.Lemmas.mixedRadix_injective i.isLt i'.isLt heq
  have hqlo : q.lo < n + 1 := by have := q.ordered.trans q.valid; omega
  have hqlo' : q'.lo < n + 1 := by have := q'.ordered.trans q'.valid; omega
  obtain ⟨hlo, hhi⟩ := OAI.EditApproximation.Lemmas.mixedRadix_injective hqlo hqlo' hq
  have hqeq : q = q' := by cases q; cases q'; cases hlo; cases hhi; rfl
  exact Prod.ext (Fin.ext hi) hqeq

theorem _root_.OAI.EditApproximation.Lemmas.historyInputCode_injective (M : ℕ) (n : ℕ) :
    Function.Injective (OAI.EditApproximation.historyInputCode (M := M) (n := n)) := by
  rintro ⟨i, s, q⟩ ⟨i', s', q'⟩ heq
  have h := Nat.pair_eq_pair.mp heq
  have hc := OAI.EditApproximation.Lemmas.childInputCode_injective M n h.2
  cases hc
  cases h.1
  rfl

def localRefinementStepQuery : OAI.EditApproximation.FiniteQuery ι := by
  exact
    let earlierKeys := OAI.EditApproximation.orderedInputs OAI.EditApproximation.historyInputCode (OAI.EditApproximation.Lemmas.historyInputCode_injective M target.length)
      (OAI.EditApproximation.queryEarlierInputCover parent N P F exponent t a parentInitial q)
    OAI.EditApproximation.FiniteQuery.collect readEarlier earlierKeys fun earlierAnswers =>
      let earlier := fun i s r => OAI.EditApproximation.finiteAnswerTable earlierKeys earlierAnswers (i, s, r)
      let online := OAI.EditApproximation.localOnlineCandidates source target parent N P F exponent H tau a eta kappa
        parentInitial child initial earlier (t - 1) integer q
      let sharedKeys := OAI.EditApproximation.orderedInputs OAI.EditApproximation.childInputCode (OAI.EditApproximation.Lemmas.childInputCode_injective M target.length)
        (OAI.EditApproximation.querySharedInputCover source target parent N F exponent Q a parentInitial q draw)
      OAI.EditApproximation.FiniteQuery.collect readCurrent sharedKeys fun sharedAnswers =>
        let current := fun i r => OAI.EditApproximation.finiteAnswerTable sharedKeys sharedAnswers (i, r)
        let selected := OAI.EditApproximation.localCellGroupActions source target parent N P F exponent Q tau a
          parentInitial child initial current draw q
        let needed := OAI.EditApproximation.actionCurrentInputCover selected ∪ OAI.EditApproximation.actionCurrentInputCover online
        let currentKeys := OAI.EditApproximation.orderedInputs OAI.EditApproximation.childInputCode (OAI.EditApproximation.Lemmas.childInputCode_injective M target.length) needed
        OAI.EditApproximation.FiniteQuery.collect readCurrent currentKeys fun currentAnswers =>
          let value := OAI.EditApproximation.rationalActionValue (fun q r => OAI.EditApproximation.targetEndpointDistance q r) (128 * F)
            (OAI.EditApproximation.finiteAnswerTable currentKeys currentAnswers) q
          let fallback := OAI.EditApproximation.rationalBellman parentInitial (fun q r => OAI.EditApproximation.targetEndpointDistance q r) (128 * F)
            (OAI.EditApproximation.rationalActualWideActions parent (OAI.EditApproximation.localRefinementRepresentatives N P F a parentInitial q) P)
            (fun input => earlier input.1 (t - 1) input.2) q
          .done (OAI.EditApproximation.rationalRefinementUpdate delta (OAI.EditApproximation.rationalMinimum fallback (selected.map value))
            (OAI.EditApproximation.rationalOnlineMinimum (online.map value)))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_1} {α : Type u_2} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ) (t : ℕ) (parentInitial : TargetInterval target.length → ℚ) (child initial : Fin M → TargetInterval target.length → ℚ) (draw : CellGroupDraws M F Q) (q : TargetInterval target.length) (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι) (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

def localOnlineSourceStepQuery : OAI.EditApproximation.FiniteQuery ι :=
  let keys := OAI.EditApproximation.localOnlineSourceKeys N P F a parentInitial q
  OAI.EditApproximation.FiniteQuery.collect
    (fun key => readInteger key (OAI.EditApproximation.keyedOnlineSourceRange source target parent P exponent H tau child key))
    keys fun values =>
      OAI.EditApproximation.localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
        parentInitial child initial draw (fun b r => ⌊OAI.EditApproximation.finiteAnswerTable keys values (b, r)⌋₊) q
        readEarlier readCurrent

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_1} {β : Type u_2} {α : Type u_3} (source target : List α) {M : ℕ} (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a : BinaryFraction) (t : ℕ) (initial : TargetInterval target.length → BinaryFraction × ℕ) (draw : CountedCellGroupDraws M F Q) (q : TargetInterval target.length) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction) (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction) (online : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ) (selected : List (Fin M × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ) (next : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)

def queryRefinementGather : OAI.EditApproximation.BitQuery ι β :=
  (OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.queryEarlierInputsWithWork M parent N P F exponent t hP a initial q)).bind
    fun earlierKeys => OAI.EditApproximation.BitQuery.collect readEarlier earlierKeys fun earlierWords =>
      (OAI.EditApproximation.BitQuery.compute (online earlierKeys earlierWords)).bind fun onlineActions =>
        let word := initial q
        .charge word.2 ((OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.BinaryFraction.querySharedInputsWithWork M N F Q exponent
          eM eF hM hF parent a word.1 q draw)).bind fun sharedKeys =>
            OAI.EditApproximation.BitQuery.collect readCurrent sharedKeys fun sharedWords =>
              (OAI.EditApproximation.BitQuery.compute (selected sharedKeys sharedWords)).bind fun selectedActions =>
                (OAI.EditApproximation.BitQuery.compute (OAI.EditApproximation.queryNeededInputsWithWork selectedActions onlineActions)).bind
                  fun currentKeys => OAI.EditApproximation.BitQuery.collect readCurrent currentKeys
                    (next earlierKeys earlierWords selectedActions onlineActions currentKeys))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {nx ny M : ℕ} (parent : TargetInterval nx) (N P F : ℕ) (a delta : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ) (t : ℕ) (earlierKeys : List (Fin M × ℕ × TargetInterval ny)) (earlierWords : List BinaryFraction) (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M)) (currentKeys : List (Fin M × TargetInterval ny)) (currentWords : List BinaryFraction) (query : TargetInterval ny)

def queryRefinementFinishWithWork : OAI.EditApproximation.BinaryFraction × ℕ :=
  let fallback := initial query
  let representatives := OAI.EditApproximation.BinaryFraction.localRepresentativeReadWithWork N P F a initial query
  let result := OAI.EditApproximation.BinaryFraction.physicalContinuationReadWithWork parent representatives.1 P F delta fallback.1
    (OAI.EditApproximation.BinaryFraction.queryHistoryReadWithWork earlierKeys earlierWords (t - 1))
    (fun input => OAI.EditApproximation.BinaryFraction.queryChildReadWithWork currentKeys currentWords input.1 input.2)
    groups online query
  (result.1, fallback.2 + representatives.2 + result.2 + 2)

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_1} {α : Type u_2} (source target : List α) {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ) (t : ℕ) (parentInitial : TargetInterval target.length → ℚ) (child initial : Fin M → TargetInterval target.length → ℚ) (q : TargetInterval target.length) (readGroup : GroupScalarKey M F Q → FiniteQuery ι) (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι) (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

noncomputable def localRandomSourceStepQuery : OAI.EditApproximation.FiniteQuery ι :=
  let keys := OAI.EditApproximation.groupScalarKeys M F Q (OAI.EditApproximation.localGroupQueryKeys N F exponent a parentInitial q)
  OAI.EditApproximation.FiniteQuery.collect readGroup keys fun values =>
    OAI.EditApproximation.localOnlineSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial (OAI.EditApproximation.groupDrawFromValues keys values) q readInteger readEarlier readCurrent

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_1} {α : Type u_2} (source target : List α) {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ) (t : ℕ) (parentInitial : TargetInterval target.length → ℚ) (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι) (readGroup : GroupScalarKey M F Q → FiniteQuery ι) (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι) (q : TargetInterval target.length) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι) (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

noncomputable def localRandomBandDataQuery : OAI.EditApproximation.FiniteQuery ι :=
  let keys := OAI.EditApproximation.refinementBandInputList (M := M) parent N P F exponent a parentInitial q
  OAI.EditApproximation.FiniteQuery.collect readMass keys fun massValues =>
    OAI.EditApproximation.FiniteQuery.collect readInitial keys fun initialValues =>
      OAI.EditApproximation.localRandomSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
        parentInitial (fun i r => OAI.EditApproximation.finiteAnswerTable keys massValues (i, r))
        (fun i r => OAI.EditApproximation.finiteAnswerTable keys initialValues (i, r)) q readGroup readInteger readEarlier readCurrent

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {ι : Type u_1} {α : Type u_2} (source target : List α) {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ) (t : ℕ) (readParentInitial : TargetInterval target.length → FiniteQuery ι) (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι) (readGroup : GroupScalarKey M F Q → FiniteQuery ι) (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι) (q : TargetInterval target.length) (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι) (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)

noncomputable def localRandomDataQuery : OAI.EditApproximation.FiniteQuery ι :=
  OAI.EditApproximation.FiniteQuery.bind (readParentInitial q) fun value =>
    let keys := OAI.EditApproximation.refinementInitialSupport N P F exponent a value q
    OAI.EditApproximation.FiniteQuery.collect readParentInitial keys fun initialValues =>
      OAI.EditApproximation.localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
        (OAI.EditApproximation.finiteAnswerTable keys initialValues) readMass readInitial readGroup readInteger q readEarlier readCurrent

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J N n exponent F Q R B : ℕ}

def physicalScalarCode (key : OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) : ℕ :=
  match key with
  | ⟨.inl online, time⟩ => 2 * Nat.pair (OAI.EditApproximation.physicalEntryCode (online.1.1.val, online.1.2.2))
      (Nat.pair online.1.2.1.val (Nat.pair online.2.val.val time.val))
  | ⟨.inr group, index⟩ => 2 * Nat.pair (OAI.EditApproximation.physicalNodeCode group.1.val)
      (Nat.pair group.2.1.val (Nat.pair group.2.2.1.val (Nat.pair group.2.2.2.val
        (Nat.pair index.1.val (Nat.pair index.2.1.val index.2.2.val))))) + 1

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable (M J N n exponent F Q R B : ℕ) [NeZero M]

open MeasureTheory ProbabilityTheory

theorem _root_.OAI.EditApproximation.Lemmas.physicalScaleIndex_get (N : ℕ) (b : ℕ) (hb : Membership.mem.{0, 0} (OAI.EditApproximation.dyadicScales N) b) :
    (OAI.EditApproximation.dyadicScales N).get (OAI.EditApproximation.physicalScaleIndex N b hb) = b :=
  List.getElem_idxOf (List.idxOf_lt_length_of_mem hb)

def physicalScalarGroupQueries (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
    (b : ℕ) (cell : ℕ × ℕ) : OAI.EditApproximation.PhysicalGroupQueries M J N n exponent F Q R B b := by
  exact
    if hb : b ∈ OAI.EditApproximation.dyadicScales N then
      if hc : cell.1 ≤ n * 2 ^ exponent ∧ cell.2 ≤ n * 2 ^ exponent then
        let key : OAI.EditApproximation.PhysicalLocalGroupKey M J N n exponent :=
          (node, OAI.EditApproximation.physicalScaleIndex N b hb,
            ⟨cell.1, Nat.lt_succ_of_le hc.1⟩, ⟨cell.2, Nat.lt_succ_of_le hc.2⟩)
        Eq.mp (congrArg (OAI.EditApproximation.PhysicalGroupQueries M J N n exponent F Q R B)
          (OAI.EditApproximation.Lemmas.physicalScaleIndex_get N b hb)) (OAI.EditApproximation.physicalScalarGroupQueriesAt M J N n exponent F Q R B key time)
      else fun _ _ => .done 0
    else fun _ _ => .done 0

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable (M J N n exponent F Q R B : ℕ) [NeZero M]

def physicalScalarGroupRead (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
    (key : OAI.EditApproximation.GroupScalarKey M F Q) : OAI.EditApproximation.FiniteQuery (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) :=
  OAI.EditApproximation.physicalScalarGroupQueries M J N n exponent F Q R B node time key.1.1 key.1.2 key.2.1 key.2.2

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {σ : Type u_1} {α : Type u_2} (source target : List α) {M J : ℕ} [NeZero M] (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ) (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J) (readGroup : GroupScalarKey M F Q → FiniteQuery σ) (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ) (q : TargetInterval target.length)

noncomputable def physicalRandomDataRequestQuery :
    OAI.EditApproximation.FiniteQuery (Sum σ {child : OAI.EditApproximation.PhysicalTableRequest M J target.length //
      child.combinedRank T S < (OAI.EditApproximation.PhysicalTableRequest.refinement pass copy node T t q).combinedRank T S}) :=
  OAI.EditApproximation.localRandomDataQuery source target (OAI.EditApproximation.physicalSourceInterval source.length node)
    N P F exponent H Q tau a eta kappa delta t
    (fun r => OAI.EditApproximation.FiniteQuery.mapKeys Sum.inr
      (OAI.EditApproximation.physicalRefinementWarmupRead pass copy T S t ht node q node le_rfl 0 (Nat.zero_le T) r))
    (fun input => OAI.EditApproximation.FiniteQuery.mapKeys Sum.inr
      (OAI.EditApproximation.physicalRefinementMassQuery pass copy T S t ht node hbelow q input))
    (fun input => OAI.EditApproximation.FiniteQuery.mapKeys Sum.inr
      (OAI.EditApproximation.physicalRefinementWarmupRead pass copy T S t ht node q
        (OAI.EditApproximation.physicalChild node hbelow input.1) (by change node.1.val ≤ node.1.val + 1; omega)
        0 (Nat.zero_le T) input.2))
    (fun key => OAI.EditApproximation.FiniteQuery.mapKeys Sum.inl (readGroup key))
    (fun key range => OAI.EditApproximation.FiniteQuery.mapKeys Sum.inl (readInteger key range)) q
    (fun input => OAI.EditApproximation.FiniteQuery.mapKeys Sum.inr
      (OAI.EditApproximation.physicalRefinementEarlierQuery pass copy T S t node hbelow q input))
    (fun input => OAI.EditApproximation.FiniteQuery.mapKeys Sum.inr
      (OAI.EditApproximation.physicalRefinementCurrentQuery pass copy T S t node hbelow q input))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {σ : Type*} {α : Type u_2} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q T S copies : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ) (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ) (initial : PhysicalEntry M J target.length → ℕ)

def physicalInactiveGlobalQuery (request : OAI.EditApproximation.PhysicalTableRequest M J target.length) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.PhysicalTableRequest M J target.length //
      child.combinedRank T S < request.combinedRank T S} :=
  if request.index ≤ T then
    OAI.EditApproximation.physicalWarmupRequestQuery source target N P F (factor request.pass)
      request.pass request.copy T S request.index request.node request.state
      (OAI.EditApproximation.globalSeedRead N T S copies multiplier initial request)
  else OAI.EditApproximation.physicalInitialQuery source target N P F (factor request.pass)
    (OAI.EditApproximation.globalSeedRead N T S copies multiplier initial request) (request.node, request.state)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {σ : Type u_1} {α : Type u_2} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q T S copies : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ) (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ) (initial : PhysicalEntry M J target.length → ℕ)

noncomputable def physicalRandomGlobalQuery (request : OAI.EditApproximation.PhysicalTableRequest M J target.length) :
    OAI.EditApproximation.FiniteQuery (Sum σ {child : OAI.EditApproximation.PhysicalTableRequest M J target.length //
      child.combinedRank T S < request.combinedRank T S}) := by
  by_cases hactive : T < request.index ∧ request.node.1.val < J ∧
      ¬ (OAI.EditApproximation.physicalSourceInterval source.length request.node).hi -
        (OAI.EditApproximation.physicalSourceInterval source.length request.node).lo ≤ 1
  · have ht : 0 < request.index - T := Nat.sub_pos_of_lt hactive.1
    have hrequest : OAI.EditApproximation.PhysicalTableRequest.refinement request.pass request.copy request.node
        T (request.index - T) request.state = request := by
      have hi : T + (request.index - T) = request.index := by omega
      unfold OAI.EditApproximation.PhysicalTableRequest.refinement
      rw [hi]
    let node : OAI.EditApproximation.PhysicalInternalNode M J := ⟨request.node, hactive.2.1⟩
    let time : Fin R := Fin.ofNat R (request.index - T - 1)
    exact OAI.EditApproximation.FiniteQuery.mapKeys
      (Sum.map id (fun child => ⟨child.val, by simpa only [hrequest] using child.property⟩))
      (OAI.EditApproximation.physicalRandomDataRequestQuery source target N P F exponent H Q tau
        (OAI.EditApproximation.refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
        (request.index - T) ht request.node hactive.2.1
        (readGroup request.pass request.copy node time)
        (readInteger request.pass request.copy node time) request.state)
  · exact OAI.EditApproximation.FiniteQuery.mapKeys Sum.inr
      (OAI.EditApproximation.physicalInactiveGlobalQuery source target N P F T S copies factor multiplier initial request)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.PhysicalTableRequest

def entryCapacity (M J n : ℕ) : ℕ := (n + 1) ^ 2 * (M ^ J * (J + 1))

def code {M J n : ℕ} (copies T S : ℕ) (request : OAI.EditApproximation.PhysicalTableRequest M J n) : ℕ :=
  request.index + (T + S + 1) * (request.copy + copies *
    (OAI.EditApproximation.physicalEntryCode (request.node, request.state) + OAI.EditApproximation.PhysicalTableRequest.entryCapacity M J n * request.pass))

end OAI.EditApproximation.PhysicalTableRequest

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.SourceRanked

variable {σ : Type u_1} {κ : Type u_2} (tableRank : κ → ℕ) (supported : κ → Prop)

def supportedChild (parent : κ) : Sum σ {key : κ // tableRank key < tableRank parent} → Prop
  | .inl _ => True
  | .inr table => supported table.val

def supportedChildMap (parent : {key : κ // supported key}) :
    {key : Sum σ {key : κ // tableRank key < tableRank parent.val} //
      OAI.EditApproximation.SourceRanked.supportedChild tableRank supported parent.val key} →
    Sum σ {key : {key : κ // supported key} // tableRank key.val < tableRank parent.val}
  | ⟨.inl source, _⟩ => .inl source
  | ⟨.inr table, hs⟩ => .inr ⟨⟨table.val, hs⟩, table.property⟩

noncomputable def restrictBody
    (tableBody : (parent : κ) → OAI.EditApproximation.FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (parent : {key : κ // supported key}) :
    OAI.EditApproximation.FiniteQuery (Sum σ {key : {key : κ // supported key} // tableRank key.val < tableRank parent.val}) := by
  classical
  exact OAI.EditApproximation.FiniteQuery.mapKeys (OAI.EditApproximation.SourceRanked.supportedChildMap tableRank supported parent)
    (OAI.EditApproximation.FiniteQuery.restrict (OAI.EditApproximation.SourceRanked.supportedChild tableRank supported parent.val) (tableBody parent.val))

end OAI.EditApproximation.SourceRanked

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {σ : Type u_1} {α : Type u_2} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q T S passes copies : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ) (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ) (initial : PhysicalEntry M J target.length → ℕ)

noncomputable def physicalRandomBoundedQuery
    (request : {request : OAI.EditApproximation.PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    OAI.EditApproximation.FiniteQuery (Sum σ {child : {child : OAI.EditApproximation.PhysicalTableRequest M J target.length //
      child.Bounded passes copies T S} // child.val.combinedRank T S < request.val.combinedRank T S}) :=
  OAI.EditApproximation.SourceRanked.restrictBody (OAI.EditApproximation.PhysicalTableRequest.combinedRank T S)
    (OAI.EditApproximation.PhysicalTableRequest.Bounded passes copies T S)
    (OAI.EditApproximation.physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial) request

noncomputable def chargedRandomGlobalQuery
    (request : OAI.EditApproximation.ChargedPhysicalRequest M J target.length passes copies T S) :
    OAI.EditApproximation.FiniteQuery (Sum σ {child : OAI.EditApproximation.ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < request.rank}) := by
  exact
    match request with
    | .inl entry => .done (initial entry)
    | .inr parent =>
      if parent.val.index ≤ T then
        OAI.EditApproximation.FiniteQuery.mapKeys Sum.inr (OAI.EditApproximation.chargedWarmupQuery source target N P F factor multiplier parent)
      else if parent.val.node.1.val < J then
        if (OAI.EditApproximation.physicalSourceInterval source.length parent.val.node).hi -
            (OAI.EditApproximation.physicalSourceInterval source.length parent.val.node).lo ≤ 1 then
          OAI.EditApproximation.FiniteQuery.mapKeys Sum.inr
            (OAI.EditApproximation.physicalInitialQuery source target N P F (factor parent.val.pass)
              (OAI.EditApproximation.chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state))
        else OAI.EditApproximation.FiniteQuery.mapKeys
          (Sum.map id (fun child =>
            ⟨Sum.inr child.val, OAI.EditApproximation.Lemmas.table_rank_lt parent child.val child.property⟩))
          (OAI.EditApproximation.physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
            tau eta kappa delta readGroup readInteger initial parent)
      else OAI.EditApproximation.FiniteQuery.mapKeys Sum.inr
        (OAI.EditApproximation.physicalInitialQuery source target N P F (factor parent.val.pass)
          (OAI.EditApproximation.chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {α : Type u_1} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q T S passes copies : ℕ)

abbrev PhysicalFamilyScalarKey := Fin (passes + 1) × Fin (copies + 1) ×
  OAI.EditApproximation.PhysicalScalarKey M J N target.length exponent F Q R (OAI.EditApproximation.localOnlineMassBound M P H)

abbrev PhysicalFamilyScalarDraw := ∀ key : OAI.EditApproximation.PhysicalFamilyScalarKey
    (M := M) (J := J) (R := R) target N P F exponent H Q passes copies,
  Fin (OAI.EditApproximation.physicalScalarRange M J N target.length exponent F Q R (OAI.EditApproximation.localOnlineMassBound M P H) key.2.2)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {α : Type u_1} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α) (N P F exponent H Q T S passes copies : ℕ)

variable (draw : PhysicalFamilyScalarDraw
  (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)

def physicalFamilyAnswer (key : OAI.EditApproximation.PhysicalFamilyScalarKey
    (M := M) (J := J) (R := R) target N P F exponent H Q passes copies) : ℚ :=
  (draw key).val

def physicalFamilyGroupRead (pass copy : ℕ) (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
    (key : OAI.EditApproximation.GroupScalarKey M F Q) : OAI.EditApproximation.FiniteQuery (OAI.EditApproximation.PhysicalFamilyScalarKey
      (M := M) (J := J) (R := R) target N P F exponent H Q passes copies) :=
  OAI.EditApproximation.FiniteQuery.mapKeys (fun scalar => (Fin.ofNat (passes + 1) pass, Fin.ofNat (copies + 1) copy, scalar))
    (OAI.EditApproximation.physicalScalarGroupRead M J N target.length exponent F Q R (OAI.EditApproximation.localOnlineMassBound M P H) node time key)

def physicalFamilyOnlineRead (pass copy : ℕ) (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × OAI.EditApproximation.TargetInterval target.length) (range : ℕ) : OAI.EditApproximation.FiniteQuery (OAI.EditApproximation.PhysicalFamilyScalarKey
      (M := M) (J := J) (R := R) target N P F exponent H Q passes copies) :=
  OAI.EditApproximation.FiniteQuery.mapKeys (fun scalar => (Fin.ofNat (passes + 1) pass, Fin.ofNat (copies + 1) copy, scalar))
    (OAI.EditApproximation.physicalScalarOnlineRead M J N target.length exponent F Q R (OAI.EditApproximation.localOnlineMassBound M P H) node time key range)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R] (source target : List ℕ) (N P F exponent H Q eM eF : ℕ) (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ) (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ) (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ) (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)

abbrev QueryFamilyMemoKey :=
  Sum (OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    (OAI.EditApproximation.ChargedPhysicalRequest M J target.length (passes + 1) copies T S)

def queryFamilySourceWordWithWork
    (key : OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) : OAI.EditApproximation.BinaryFraction × ℕ :=
  (OAI.EditApproximation.BinaryFraction.nat (draw key).val, Nat.size (draw key).val + 3)

def queryFamilyMemoRemaining : OAI.EditApproximation.QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q → ℕ
  | .inl _ => 0
  | .inr request => OAI.EditApproximation.chargedPhysicalRemaining request

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

abbrev ComputedFamilySeed (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.ClampedPhysicalSeed (OAI.EditApproximation.integerParameters N).M
    (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) target.length N

abbrev ComputedFamilyDraw (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.PhysicalFamilyScalarDraw (M := (OAI.EditApproximation.integerParameters N).M)
    (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) (R := OAI.EditApproximation.inputHeight N ^ 2)
    target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N) (40 * OAI.EditApproximation.smallLogExponent N)
    (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80) (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2)

abbrev ComputedFamilyInput (source target : List ℕ) (N : ℕ) :=
  OAI.EditApproximation.ComputedFamilySeed source target N × OAI.EditApproximation.ComputedFamilyDraw source target N

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {α : Type u_1} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)

local notation (name := source_Combinatorics_EditApproximation_Refinement_PhysicalFamilyEncoding_3) "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P F exponent H Q passes copies

def physicalFamilyCode (key : Key) : ℕ :=
  Nat.pair key.1.val (Nat.pair key.2.1.val (OAI.EditApproximation.physicalScalarCode key.2.2))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.ChargedPhysicalRequest

def code {M J ny passes copies T S : ℕ} : OAI.EditApproximation.ChargedPhysicalRequest M J ny passes copies T S → ℕ
  | .inl entry => 2 * OAI.EditApproximation.physicalEntryCode entry
  | .inr request => 2 * OAI.EditApproximation.PhysicalTableRequest.code copies T S request.val + 1

end OAI.EditApproximation.ChargedPhysicalRequest

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

abbrev ComputedFamilyScalarKey (source target : List ℕ) (N R : ℕ) :=
  OAI.EditApproximation.PhysicalFamilyScalarKey (M := (OAI.EditApproximation.integerParameters N).M)
    (J := OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) (R := R)
    target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N) (40 * OAI.EditApproximation.smallLogExponent N)
    (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80) (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2)

def computedFamilyMemoCode (source target : List ℕ) (N R : ℕ) :
    Sum (OAI.EditApproximation.ComputedFamilyScalarKey source target N R) (OAI.EditApproximation.ComputedFamilyTableKey source target N) → ℕ :=
  OAI.EditApproximation.SourceRanked.keyCode
    (OAI.EditApproximation.physicalFamilyCode target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N) (40 * OAI.EditApproximation.smallLogExponent N)
      (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80) (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2))
    OAI.EditApproximation.ChargedPhysicalRequest.code

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open EditDistortion Finset MeasureTheory ProbabilityTheory

def coarseInitialCandidate {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (x y : List α)
    (i : OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth x y)) (draws : OAI.EditApproximation.CoarseThresholdDraws B D) : ℚ :=
  let k := OAI.EditApproximation.coarseGuess (OAI.EditApproximation.coarseEntryWidth x y) i
  2 * (OAI.EditApproximation.coarseThresholdEstimate k Q lam
    (OAI.EditApproximation.coarseTargetFrame k (OAI.EditApproximation.coarsePadTo (OAI.EditApproximation.coarseEntryWidth x y) y))
    (OAI.EditApproximation.coarseEntryTree B D x y) draws k 0 (OAI.EditApproximation.coarseRootShift k) + k)

def coarseInitialMinimum {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (x y : List α)
    (draws : OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth x y) → OAI.EditApproximation.CoarseThresholdDraws B D) : ℚ :=
  univ.inf' univ_nonempty (fun i => OAI.EditApproximation.coarseInitialCandidate B D Q lam x y i (draws i))

def coarseInitialValue {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (N : ℕ) (x y : List α)
    (draws : OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth x y) → OAI.EditApproximation.CoarseThresholdDraws B D) : ℕ :=
  if 2 * x.length < y.length then min N y.length
  else if x = y then 0
  else min N ⌈OAI.EditApproximation.coarseInitialMinimum B D Q lam x y draws⌉₊

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset MeasureTheory ProbabilityTheory

def coarseActiveArrayWork {B : ℕ} {α : Type u} (k : ℕ) (Q lam : ℚ) :
    {D : ℕ} → OAI.EditApproximation.CoarseSourceTree B α D → OAI.EditApproximation.CoarseThresholdDraws B D → ℚ → ℕ
  | _, tree, draws, allowance =>
    if (tree.word.length : ℚ) ≤ allowance then 0 else
    match tree, draws with
    | .leaf _, _ => B * (2 * k + 1)
    | .branch children, (draws, below) =>
      B * (2 * k + 1) +
        OAI.EditApproximation.coarseActiveChildrenWork Q lam allowance (fun child => coarseActiveArrayWork k Q lam child)
          (List.ofFn fun i => (children i, draws i, below i))

def coarseFullSeedTable (N B : ℕ) {I : Type u_1} {α : Type u_2} [DecidableEq α]
    (depth : I → ℕ) (x y : I → List α)
    (draws : OAI.EditApproximation.CoarseFullSeedDraws B depth x y) : I → ℕ :=
  fun i => OAI.EditApproximation.coarseInitialValue B (depth i) (OAI.EditApproximation.initialThresholdQ N) (OAI.EditApproximation.initialLambda N) N (x i) (y i) (draws i)

def coarseInitialArrayWork {α : Type u} [DecidableEq α]
    (B D : ℕ) (Q lam : ℚ) (x y : List α)
    (draws : OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth x y) → OAI.EditApproximation.CoarseThresholdDraws B D) : ℕ :=
  if 2 * x.length < y.length then 0
  else if x = y then 0
  else ∑ i, OAI.EditApproximation.coarseActiveArrayWork (OAI.EditApproximation.coarseGuess (OAI.EditApproximation.coarseEntryWidth x y) i) Q lam
    (OAI.EditApproximation.coarseEntryTree B D x y) (draws i) (OAI.EditApproximation.coarseGuess (OAI.EditApproximation.coarseEntryWidth x y) i)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter

open scoped Topology

def integerEqualWithWork : List ℤ → List ℤ → Bool × ℕ
  | [], [] => (true, 1)
  | [], _ :: _ => (false, 1)
  | _ :: _, [] => (false, 1)
  | x :: xs, y :: ys =>
    if x = y then
      let tail := integerEqualWithWork xs ys
      (tail.1, tail.2 + 1)
    else (false, 1)

def integerPreprocessingWork (source target : List ℤ) : ℕ :=
  (OAI.EditApproximation.integerInputInspectionWithWork source target).2 +
  (OAI.EditApproximation.encodeIntegerSymbolsWithWork source).2 + (OAI.EditApproximation.encodeIntegerSymbolsWithWork target).2 +
  (OAI.EditApproximation.integerOccurrenceBuildWithWork source target).2 + (OAI.EditApproximation.integerEqualWithWork source target).2 + 1

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter

abbrev ComputedFamilyMemoKey (source target : List ℕ) (N : ℕ) :=
  Sum (OAI.EditApproximation.ComputedFamilyScalarKey source target N (OAI.EditApproximation.inputHeight N ^ 2))
    (OAI.EditApproximation.ComputedFamilyTableKey source target N)

def integerPreevaluationWork (source target : List ℤ) (N : ℕ) (epsilon : OAI.EditApproximation.BinaryFraction) : ℕ :=
  OAI.EditApproximation.integerPreprocessingWork source target + OAI.EditApproximation.globalParameterWork N +
    (OAI.EditApproximation.physicalLargeInputWithWork N epsilon).2

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable {α : Type u_1} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)

def physicalFamilyCodeWithWork
    (key : OAI.EditApproximation.PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) : ℕ × ℕ :=
  let scalar := OAI.EditApproximation.physicalScalarCodeWithWork key.2.2
  let copy := OAI.EditApproximation.naturalPairWithWork key.2.1.val scalar.1
  let pass := OAI.EditApproximation.naturalPairWithWork key.1.val copy.1
  (pass.1, scalar.2 + copy.2 + pass.2 + 2)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def computedFamilyMemoCodeWithWork (source target : List ℕ) (N R : ℕ) :
    Sum (OAI.EditApproximation.ComputedFamilyScalarKey source target N R) (OAI.EditApproximation.ComputedFamilyTableKey source target N) → ℕ × ℕ
  | .inl key =>
      let result := OAI.EditApproximation.physicalFamilyCodeWithWork target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
        (40 * OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80)
        (OAI.EditApproximation.computedSeedPassCount N) (OAI.EditApproximation.inputHeight N ^ 2) key
      (2 * result.1, result.2 + 2)
  | .inr key => let result := OAI.EditApproximation.chargedPhysicalCodeWithWork key
      (2 * result.1 + 1, result.2 + 3)

end OAI.EditApproximation

end


