-- Prove2me | Definitions.Def_EditApproxScheme_13
-- name    : EditApproxScheme_13
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:48:14.382963+00:00
-- url     : https://prove2.me/theorems/e4acf05d-9a1f-479c-b803-06c45d9fd361
-- title:
--   Edit-distance approximation scheme, part 13 of 20: group scalar keys and draws
-- statement:
--   This is **part 13 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains finiteness of target intervals, dyadic group scales, group scalar keys, counted cell-group allocations, group draws and key samples, shared inputs, the cost of coarse threshold children, the coarse depth, and the physical scalar range. It also proves 8 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L7313-L8005 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 13 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_12

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset

open EditDistortion

theorem _root_.OAI.EditApproximation.Lemmas.targetStates_complete (n : ℕ) (q : OAI.EditApproximation.TargetInterval n) : q ∈ OAI.EditApproximation.targetStates n := by
  apply List.mem_flatMap.mpr
  refine ⟨q.lo, List.mem_range.mpr (Nat.lt_succ_of_le (q.ordered.trans q.valid)), ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨q.hi, List.mem_range.mpr (Nat.lt_succ_of_le q.valid), ?_⟩
  rw [OAI.EditApproximation.makeTargetState, dite_eq_left (show q.lo ≤ q.hi ∧ q.hi ≤ n from ⟨q.ordered, q.valid⟩)]

instance targetIntervalFintype (n : ℕ) : Fintype (OAI.EditApproximation.TargetInterval n) := by
  exact
    Fintype.ofList (OAI.EditApproximation.targetStates n) (OAI.EditApproximation.Lemmas.targetStates_complete n)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.UnskippedBand

open Finset

def actions {α : Type u_1} {source target : List α} {M : ℕ}
    {parent : OAI.EditApproximation.TargetInterval source.length} {b P thetaExponent : ℕ}
    {tau F : ℚ} {child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ}
    (member : OAI.EditApproximation.UnskippedBand source target parent b P thetaExponent tau F child initial) :=
  OAI.EditApproximation.representativeBandActions source target parent member.center b P tau
    ((2 : ℚ) ^ (-(thetaExponent : ℤ))) child

def envelope {α : Type u_1} {source target : List α} {M : ℕ}
    {parent : OAI.EditApproximation.TargetInterval source.length} {b P thetaExponent : ℕ}
    {tau F : ℚ} {child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ}
    (member : OAI.EditApproximation.UnskippedBand source target parent b P thetaExponent tau F child initial) (i : Fin M) : ℚ :=
  OAI.EditApproximation.bandChildEnvelope b member.actions initial i

def rounded {α : Type u_1} {source target : List α} {M : ℕ}
    {parent : OAI.EditApproximation.TargetInterval source.length} {b P thetaExponent : ℕ}
    {tau F : ℚ} {child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ}
    (member : OAI.EditApproximation.UnskippedBand source target parent b P thetaExponent tau F child initial) :
    Fin M → OAI.EditApproximation.TargetInterval target.length :=
  OAI.EditApproximation.canonicalRoundedBandAction thetaExponent b member.actions member.nonempty initial

def rationalAction {α : Type u_1} {source target : List α} {M b P thetaExponent : ℕ}
    {parent : OAI.EditApproximation.TargetInterval source.length} {tau F : ℚ}
    {child initial : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ}
    (member : OAI.EditApproximation.UnskippedBand source target parent b P thetaExponent tau F child initial) :
    OAI.EditApproximation.RationalBellmanAction (OAI.EditApproximation.TargetInterval target.length) (Fin M × OAI.EditApproximation.TargetInterval target.length) M :=
  ⟨member.center, OAI.EditApproximation.endpointActionConnection member.center member.rounded, fun i => (i, member.rounded i)⟩

end OAI.EditApproximation.UnskippedBand

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset MeasureTheory ProbabilityTheory

variable {α : Type u_1} {source target : List α} {M b P thetaExponent : ℕ} {parent : TargetInterval source.length} {tau F : ℚ} {child initial : Fin M → TargetInterval target.length → ℚ}

def unskippedGroupEstimate {T : ℕ} (scales : Fin T → ℚ) (count : Fin T → ℕ)
    (value : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ)
    (member : OAI.EditApproximation.UnskippedBand source target parent b P thetaExponent tau F child initial)
    (draw : ∀ scale : Fin T, Fin (count scale) → Fin M) : ℚ :=
  OAI.EditApproximation.groupMemberEstimate scales count (OAI.EditApproximation.endpointActionConnection member.center member.rounded)
    member.envelope (fun i => value i (member.rounded i)) draw

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset MeasureTheory ProbabilityTheory

variable {α : Type*} {source target : List α} {M b P thetaExponent : ℕ} {parent : TargetInterval source.length} {tau F : ℚ} {child initial : Fin M → TargetInterval target.length → ℚ}

def groupDyadicScaleAt (M b : ℕ) (F : ℚ) (i : Fin (OAI.EditApproximation.groupDyadicScales M b F).length) : ℚ :=
  (OAI.EditApproximation.groupDyadicScales M b F).get i

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

abbrev CellGroupDraws (M F Q : ℕ) := ∀ b : ℕ, (ℕ × ℕ) →
  ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length,
    Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) → Fin M

abbrev cellScaleReadDraw (M b Q : ℕ) (F : ℚ) :=
  ∀ (t : Fin (OAI.EditApproximation.groupDyadicScales M b F).length),
    Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F t)) → Fin M × ℕ

abbrev GroupScalarKey (M F Q : ℕ) :=
  Σ key : ℕ × (ℕ × ℕ), Σ scale : Fin (OAI.EditApproximation.groupDyadicScales M key.1 F).length,
    Fin (OAI.EditApproximation.groupSampleCount M Q key.1 (OAI.EditApproximation.groupDyadicScaleAt M key.1 F scale))

abbrev CountedCellGroupDraws (M F Q : ℕ) :=
  ∀ b : ℕ, ∀ _cell : ℕ × ℕ, ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length,
    Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) → Fin M × ℕ

abbrev CellGroupSourceAllocations (M F Q : ℕ) := ∀ (b : ℕ) (_cell : ℕ × ℕ),
  ∀ t : Fin (OAI.EditApproximation.groupDyadicScales M b F).length,
    Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F t)) → ℕ

abbrev CountedCellGroupAllocations (M F Q : ℕ) :=
  ∀ b : ℕ, ∀ _cell : ℕ × ℕ, ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length,
    Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) → ℕ

abbrev CellGroupReadDraws (M F Q : ℕ) := ∀ (b : ℕ) (_cell : ℕ × ℕ),
  OAI.EditApproximation.cellScaleReadDraw M b Q F

def groupScalarKeys (M F Q : ℕ) (groups : List (ℕ × (ℕ × ℕ))) : List (OAI.EditApproximation.GroupScalarKey M F Q) :=
  groups.flatMap fun (key : ℕ × (ℕ × ℕ)) =>
    (List.finRange (OAI.EditApproximation.groupDyadicScales M key.1 F).length).flatMap
      fun (scale : Fin (OAI.EditApproximation.groupDyadicScales M key.1 F).length) =>
        (List.finRange (OAI.EditApproximation.groupSampleCount M Q key.1 (OAI.EditApproximation.groupDyadicScaleAt M key.1 F scale))).map
          fun sample => Sigma.mk key (Sigma.mk scale sample)

noncomputable def groupDrawFromValues {M F Q : ℕ} [NeZero M]
    (keys : List (OAI.EditApproximation.GroupScalarKey M F Q)) (values : List ℚ) : OAI.EditApproximation.CellGroupDraws M F Q := by
  classical
  exact fun b cell scale sample => Fin.ofNat M ⌊OAI.EditApproximation.finiteAnswerTable keys values ⟨(b, cell), scale, sample⟩⌋₊

def queryGroupKeyEqualWithWork {M F Q : ℕ} (a b : OAI.EditApproximation.GroupScalarKey M F Q) : Bool × ℕ :=
  let scale := OAI.EditApproximation.naturalEqualWithWork a.1.1 b.1.1
  let lo := OAI.EditApproximation.naturalEqualWithWork a.1.2.1 b.1.2.1
  let hi := OAI.EditApproximation.naturalEqualWithWork a.1.2.2 b.1.2.2
  let label := OAI.EditApproximation.naturalEqualWithWork a.2.1.val b.2.1.val
  let sample := OAI.EditApproximation.naturalEqualWithWork a.2.2.val b.2.2.val
  (scale.1 && lo.1 && hi.1 && label.1 && sample.1,
    scale.2 + lo.2 + hi.2 + label.2 + sample.2 + 4)

def queryGroupKeyEqualAllocation {M F Q : ℕ} (a b : OAI.EditApproximation.GroupScalarKey M F Q) : ℕ :=
  OAI.EditApproximation.naturalEqualAllocation a.1.1 b.1.1 + OAI.EditApproximation.naturalEqualAllocation a.1.2.1 b.1.2.1 +
    OAI.EditApproximation.naturalEqualAllocation a.1.2.2 b.1.2.2 + OAI.EditApproximation.naturalEqualAllocation a.2.1.val b.2.1.val +
    OAI.EditApproximation.naturalEqualAllocation a.2.2.val b.2.2.val + 4

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

open Finset

theorem _root_.OAI.EditApproximation.Lemmas.inversePowerTwo_value (n : ℕ) : (OAI.EditApproximation.BinaryFraction.inversePowerTwo n).value = (2 : ℚ) ^ (-(n : ℤ)) := by
  (simp only [OAI.EditApproximation.BinaryFraction.inversePowerTwo, OAI.EditApproximation.BinaryFraction.value, OAI.EditApproximation.SignedBinary.value, OAI.EditApproximation.signedMagnitude, Bool.false_eq_true,
    ↓reduceIte, OAI.EditApproximation.bitWordValue, Bool.toNat_true,
    Int.cast_natCast, OAI.EditApproximation.Lemmas.powerTwoWord_value, Nat.cast_pow, Nat.cast_ofNat, zpow_neg, zpow_natCast])
  norm_num [one_div]

theorem _root_.OAI.EditApproximation.Lemmas.signedPowerTwoWithWork_value (e : ℤ) :
    (OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork e).1.value = (2 : ℚ) ^ e := by
  unfold OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork
  split_ifs with h
  · change (OAI.EditApproximation.bitWordValue (OAI.EditApproximation.powerTwoWord e.toNat) : ℚ) / 1 = (2 : ℚ) ^ e
    rw [div_one, OAI.EditApproximation.Lemmas.powerTwoWord_value, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
      Int.toNat_of_nonneg h]
  · rw [OAI.EditApproximation.Lemmas.inversePowerTwo_value, Int.toNat_of_nonneg
      (show 0 ≤ -e from neg_nonneg.mpr (le_of_lt (lt_of_not_ge h))), neg_neg]

theorem _root_.OAI.EditApproximation.Lemmas.groupScalesWithWork_value (eM : ℕ) (eb : ℕ) (eF : ℕ) :
    ((OAI.EditApproximation.BinaryFraction.groupScalesWithWork eM eb eF).1.map OAI.EditApproximation.BinaryFraction.value) =
      OAI.EditApproximation.groupDyadicScales (2 ^ eM) (2 ^ eb) ((2 : ℚ) ^ eF) := by
  have hlower : ((2 ^ eb : ℕ) : ℚ) / (2 ^ eM : ℕ) = (2 : ℚ) ^ ((eb : ℤ) - eM) := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_natCast]
  have hupper : (64 : ℚ) * (2 : ℚ) ^ eF * (2 ^ eb : ℕ) =
      (2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast, pow_add, pow_add]
    norm_num
  have hlog : Int.log 2 ((2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ)) = ((6 + eF + eb : ℕ) : ℤ) := by
    simpa only [Nat.cast_ofNat] using Int.log_zpow (R := ℚ) (by decide : 1 < 2) ((6 + eF + eb : ℕ) : ℤ)
  have hclog : Int.clog 2 ((2 : ℚ) ^ ((eb : ℤ) - eM)) = (eb : ℤ) - eM := by
    simpa only [Nat.cast_ofNat] using Int.clog_zpow (R := ℚ) (by decide : 1 < 2) ((eb : ℤ) - eM)
  simp only [OAI.EditApproximation.BinaryFraction.groupScalesWithWork, OAI.EditApproximation.Lemmas.arithmeticMapWithWork_value, List.map_map,
    Function.comp_def, OAI.EditApproximation.Lemmas.signedPowerTwoWithWork_value, OAI.EditApproximation.groupDyadicScales, hlower, hupper, hlog, hclog]

theorem _root_.OAI.EditApproximation.Lemmas.computedGroupScales_value (M : ℕ) (b : ℕ) (F : ℕ) (eM : ℕ) (eb : ℕ) (eF : ℕ) (hM : Eq.{1} M (HPow.hPow.{0, 0, 0} 2 eM)) (hb : Eq.{1} b (HPow.hPow.{0, 0, 0} 2 eb)) (hF : Eq.{1} F (HPow.hPow.{0, 0, 0} 2 eF)) :
    (OAI.EditApproximation.BinaryFraction.groupScalesWithWork eM eb eF).1.map OAI.EditApproximation.BinaryFraction.value = OAI.EditApproximation.groupDyadicScales M b (OAI.EditApproximation.BinaryFraction.nat F).value := by
  rw [OAI.EditApproximation.Lemmas.nat_value, hM, hb, hF, Nat.cast_pow, Nat.cast_ofNat]
  exact OAI.EditApproximation.Lemmas.groupScalesWithWork_value eM eb eF

theorem _root_.OAI.EditApproximation.Lemmas.queryScaleAt_value (words : List.{0} OAI.EditApproximation.BinaryFraction) (scales : List.{0} ℚ) (h : Eq.{1} (List.map.{0, 0} OAI.EditApproximation.BinaryFraction.value words) scales) (i : Fin (List.length.{0} scales)) :
    (OAI.EditApproximation.BinaryFraction.queryScaleAt words scales h i).value = scales[i.val] := by
  subst scales
  simp only [OAI.EditApproximation.BinaryFraction.queryScaleAt, List.getElem_map]

def queryGroupKeySamplesWithWork (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (cell : ℕ × ℕ) :
    List (OAI.EditApproximation.GroupScalarKey M F Q) × ℕ := by
  exact
    let b := 2 ^ eb
    let scales := OAI.EditApproximation.BinaryFraction.groupScalesWithWork eM eb eF
    let hs : scales.1.map OAI.EditApproximation.BinaryFraction.value = OAI.EditApproximation.groupDyadicScales M b F := by
      simpa only [OAI.EditApproximation.Lemmas.nat_value] using OAI.EditApproximation.Lemmas.computedGroupScales_value M b F eM eb eF hM rfl hF
    let hlen : scales.1.length = (OAI.EditApproximation.groupDyadicScales M b F).length := by
      simpa only [List.length_map] using congrArg List.length hs
    let indices := OAI.EditApproximation.queryFinRange scales.1.length (OAI.EditApproximation.groupDyadicScales M b F).length hlen
    let samples := OAI.EditApproximation.arithmeticFlatMapWithWork (fun scale =>
      let word := OAI.EditApproximation.BinaryFraction.queryScaleAt scales.1 (OAI.EditApproximation.groupDyadicScales M b F) hs scale
      let count := OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork M Q b word
      let hc : OAI.EditApproximation.bitWordValue count.1 = OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale) := by
        rw [OAI.EditApproximation.Lemmas.groupSampleCountWithWork_value, OAI.EditApproximation.Lemmas.queryScaleAt_value]
        rfl
      let coordinates := OAI.EditApproximation.queryFinRange (OAI.EditApproximation.bitWordValue count.1)
        (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) hc
      let labeled := OAI.EditApproximation.arithmeticMapWithWork (fun sample =>
        ((⟨(b, cell), scale, sample⟩ : OAI.EditApproximation.GroupScalarKey M F Q), 2)) coordinates
      (labeled.1, scales.1.length + count.2 + labeled.2 + coordinates.length + 3)) indices
    (samples.1, scales.2 + 4 * scales.1.length + samples.2 + eb + 4)

theorem _root_.OAI.EditApproximation.Lemmas.queryGroupScaleAt_value (M : ℕ) (b : ℕ) (F : ℕ) (words : List.{0} OAI.EditApproximation.BinaryFraction) (h : Eq.{1} (List.map.{0, 0} OAI.EditApproximation.BinaryFraction.value words)
  (OAI.EditApproximation.groupDyadicScales M b ↑F)) (i : Fin (List.length.{0} (OAI.EditApproximation.groupDyadicScales M b ↑F))) :
    (OAI.EditApproximation.BinaryFraction.queryScaleAt words (OAI.EditApproximation.groupDyadicScales M b F) h i).value = OAI.EditApproximation.groupDyadicScaleAt M b F i :=
  OAI.EditApproximation.Lemmas.queryScaleAt_value words (OAI.EditApproximation.groupDyadicScales M b F) h i

def querySharedCellInputsWithWork {nx ny : ℕ} (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (parent : OAI.EditApproximation.TargetInterval nx)
    (exponent : ℕ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M (2 ^ eb) F).length,
      Fin (OAI.EditApproximation.groupSampleCount M Q (2 ^ eb) (OAI.EditApproximation.groupDyadicScaleAt M (2 ^ eb) F scale)) → Fin M × ℕ) :
    List (Fin M × OAI.EditApproximation.TargetInterval ny) × ℕ := by
  exact
    let b := 2 ^ eb
    let scales := OAI.EditApproximation.BinaryFraction.groupScalesWithWork eM eb eF
    let hs : scales.1.map OAI.EditApproximation.BinaryFraction.value = OAI.EditApproximation.groupDyadicScales M b F := by
      simpa only [OAI.EditApproximation.Lemmas.nat_value] using OAI.EditApproximation.Lemmas.computedGroupScales_value M b F eM eb eF hM rfl hF
    let hlen : scales.1.length = (OAI.EditApproximation.groupDyadicScales M b F).length := by
      simpa only [List.length_map] using congrArg List.length hs
    let indices := OAI.EditApproximation.queryFinRange scales.1.length (OAI.EditApproximation.groupDyadicScales M b F).length hlen
    let inputs := OAI.EditApproximation.arithmeticFlatMapWithWork (fun scale =>
      let word := OAI.EditApproximation.BinaryFraction.queryScaleAt scales.1 (OAI.EditApproximation.groupDyadicScales M b F) hs scale
      let hv : word.value = OAI.EditApproximation.groupDyadicScaleAt M b F scale := OAI.EditApproximation.Lemmas.queryGroupScaleAt_value M b F _ hs scale
      let states := OAI.EditApproximation.BinaryFraction.queryGroupInputsTransportWithWork (ny := ny) parent b exponent Q cell word
        (OAI.EditApproximation.groupDyadicScaleAt M b F scale) hv (draw scale)
      (states.1, states.2 + scales.1.length + 1)) indices
    (inputs.1, scales.2 + 4 * scales.1.length + inputs.2 + eb + 4)

def groupKeySampleBlock {M F Q : ℕ} (b : ℕ) (raw : List OAI.EditApproximation.BinaryFraction)
    (hs : raw.map OAI.EditApproximation.BinaryFraction.value = OAI.EditApproximation.groupDyadicScales M b F) (cell : ℕ × ℕ)
    (scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length) : List (OAI.EditApproximation.GroupScalarKey M F Q) × ℕ := by
  exact
    let word := OAI.EditApproximation.BinaryFraction.queryScaleAt raw (OAI.EditApproximation.groupDyadicScales M b F) hs scale
    let count := OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork M Q b word
    let hc : OAI.EditApproximation.bitWordValue count.1 = OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale) := by
      rw [OAI.EditApproximation.Lemmas.groupSampleCountWithWork_value, OAI.EditApproximation.Lemmas.queryScaleAt_value]
      rfl
    let coordinates := OAI.EditApproximation.queryFinRange (OAI.EditApproximation.bitWordValue count.1)
      (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) hc
    let labeled := OAI.EditApproximation.arithmeticMapWithWork (fun sample =>
      ((⟨(b, cell), scale, sample⟩ : OAI.EditApproximation.GroupScalarKey M F Q), 2)) coordinates
    (labeled.1, raw.length + count.2 + labeled.2 + coordinates.length + 3)

def groupKeySampleBlockAllocation {M F Q : ℕ} (b : ℕ) (raw : List OAI.EditApproximation.BinaryFraction)
    (hs : raw.map OAI.EditApproximation.BinaryFraction.value = OAI.EditApproximation.groupDyadicScales M b F) (_cell : ℕ × ℕ)
    (scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length) : ℕ := by
  exact
    let word := OAI.EditApproximation.BinaryFraction.queryScaleAt raw (OAI.EditApproximation.groupDyadicScales M b F) hs scale
    let count := OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork M Q b word
    let hc : OAI.EditApproximation.bitWordValue count.1 = OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale) := by
      rw [OAI.EditApproximation.Lemmas.groupSampleCountWithWork_value, OAI.EditApproximation.Lemmas.queryScaleAt_value]
      rfl
    let coordinates := OAI.EditApproximation.queryFinRange (OAI.EditApproximation.bitWordValue count.1)
      (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) hc
    OAI.EditApproximation.BinaryFraction.groupSampleCountAllocation M Q b word + OAI.EditApproximation.arithmeticMapAllocation (fun _ => 2) coordinates +
      2 * coordinates.length

def querySharedCellInputsAllocation {nx ny : ℕ} (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (parent : OAI.EditApproximation.TargetInterval nx)
    (exponent : ℕ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M (2 ^ eb) F).length,
      Fin (OAI.EditApproximation.groupSampleCount M Q (2 ^ eb) (OAI.EditApproximation.groupDyadicScaleAt M (2 ^ eb) F scale)) → Fin M × ℕ)
    (allocation : ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M (2 ^ eb) F).length,
      Fin (OAI.EditApproximation.groupSampleCount M Q (2 ^ eb) (OAI.EditApproximation.groupDyadicScaleAt M (2 ^ eb) F scale)) → ℕ) : ℕ := by
  exact
    let b := 2 ^ eb
    let scales := OAI.EditApproximation.BinaryFraction.groupScalesWithWork eM eb eF
    let hs : scales.1.map OAI.EditApproximation.BinaryFraction.value = OAI.EditApproximation.groupDyadicScales M b F := by
      simpa only [OAI.EditApproximation.Lemmas.nat_value] using OAI.EditApproximation.Lemmas.computedGroupScales_value M b F eM eb eF hM rfl hF
    let hlen : scales.1.length = (OAI.EditApproximation.groupDyadicScales M b F).length := by
      simpa only [List.length_map] using congrArg List.length hs
    let indices := OAI.EditApproximation.queryFinRange scales.1.length (OAI.EditApproximation.groupDyadicScales M b F).length hlen
    let build := fun scale =>
      let word := OAI.EditApproximation.BinaryFraction.queryScaleAt scales.1 (OAI.EditApproximation.groupDyadicScales M b F) hs scale
      let hv : word.value = OAI.EditApproximation.groupDyadicScaleAt M b F scale := OAI.EditApproximation.Lemmas.queryGroupScaleAt_value M b F _ hs scale
      let states := OAI.EditApproximation.BinaryFraction.queryGroupInputsTransportWithWork (ny := ny) parent b exponent Q cell word
        (OAI.EditApproximation.groupDyadicScaleAt M b F scale) hv (draw scale)
      (states.1, states.2 + scales.1.length + 1)
    OAI.EditApproximation.BinaryFraction.groupScalesAllocation eM eb eF + 2 * scales.1.length + eb + 1 +
      OAI.EditApproximation.arithmeticFlatMapAllocation build (fun scale =>
        let word := OAI.EditApproximation.BinaryFraction.queryScaleAt scales.1 (OAI.EditApproximation.groupDyadicScales M b F) hs scale
        let hv : word.value = OAI.EditApproximation.groupDyadicScaleAt M b F scale := OAI.EditApproximation.Lemmas.queryGroupScaleAt_value M b F _ hs scale
        OAI.EditApproximation.BinaryFraction.queryGroupInputsTransportAllocation (ny := ny) parent b exponent Q cell word
          (OAI.EditApproximation.groupDyadicScaleAt M b F scale) hv (draw scale) (allocation scale)) indices

def queryGroupKeySamplesAllocation (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (cell : ℕ × ℕ) : ℕ := by
  exact
    let b := 2 ^ eb
    let scales := OAI.EditApproximation.BinaryFraction.groupScalesWithWork eM eb eF
    let hs : scales.1.map OAI.EditApproximation.BinaryFraction.value = OAI.EditApproximation.groupDyadicScales M b F := by
      simpa only [OAI.EditApproximation.Lemmas.nat_value] using OAI.EditApproximation.Lemmas.computedGroupScales_value M b F eM eb eF hM rfl hF
    let hlen : scales.1.length = (OAI.EditApproximation.groupDyadicScales M b F).length := by
      simpa only [List.length_map] using congrArg List.length hs
    let indices := OAI.EditApproximation.queryFinRange scales.1.length (OAI.EditApproximation.groupDyadicScales M b F).length hlen
    OAI.EditApproximation.BinaryFraction.groupScalesAllocation eM eb eF + 2 * scales.1.length + eb + 1 +
      OAI.EditApproximation.arithmeticFlatMapAllocation (OAI.EditApproximation.BinaryFraction.groupKeySampleBlock (Q := Q) b scales.1 hs cell)
        (OAI.EditApproximation.BinaryFraction.groupKeySampleBlockAllocation (Q := Q) b scales.1 hs cell) indices

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

def querySharedInputsWithWork {nx ny : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (parent : OAI.EditApproximation.TargetInterval nx)
    (a value : OAI.EditApproximation.BinaryFraction) (query : OAI.EditApproximation.TargetInterval ny) (draw : OAI.EditApproximation.CountedCellGroupDraws M F Q) :
    List (Fin M × OAI.EditApproximation.TargetInterval ny) × ℕ :=
  let scales := OAI.EditApproximation.BinaryFraction.queryExponentsWithWork N F a value
  let radius := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value
  let inputs := OAI.EditApproximation.arithmeticFlatMapWithWork (fun eb =>
    let side := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat (2 ^ eb))
    let cells := OAI.EditApproximation.BinaryFraction.targetCellsWithWork side.1 (OAI.EditApproximation.bitWordValue radius.1) query
    let states := OAI.EditApproximation.arithmeticFlatMapWithWork (fun cell =>
      OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork M F Q eM eb eF hM hF parent exponent cell (draw (2 ^ eb) cell)) cells.1
    (states.1, side.2 + cells.2 + states.2 + eb + exponent + 4)) scales.1
  let sorted := OAI.EditApproximation.queryOrderedChildInputsWithWork inputs.1
  (sorted.1, scales.2 + radius.2 + inputs.2 + sorted.2 + 3)

def queryGroupDrawReadWithWork {M F Q : ℕ} [NeZero M]
    (keys : List (OAI.EditApproximation.GroupScalarKey M F Q)) (values : List OAI.EditApproximation.BinaryFraction)
    (b : ℕ) (cell : ℕ × ℕ) (scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length)
    (sample : Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale))) : Fin M × ℕ := by
  exact
    let word := OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork OAI.EditApproximation.queryGroupKeyEqualWithWork keys values ⟨(b, cell), scale, sample⟩
    let floor := OAI.EditApproximation.BinaryFraction.naturalFloorWithWork word.1
    let reduced := OAI.EditApproximation.binaryNaturalDivModWithWork (OAI.EditApproximation.bitWordValue floor.1) M
    (⟨OAI.EditApproximation.bitWordValue reduced.2.1, by
      rw [(OAI.EditApproximation.Lemmas.binaryNaturalDivModWithWork_spec _ M (NeZero.pos M)).2]
      exact Nat.mod_lt _ (NeZero.pos M)⟩,
      word.2 + floor.2 + reduced.2.2 + 3)

def queryGroupSourceKeysWithWork {n : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a value : OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval n) : List (OAI.EditApproximation.GroupScalarKey M F Q) × ℕ :=
  let scales := OAI.EditApproximation.BinaryFraction.queryExponentsWithWork N F a value
  let radius := OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value
  let keys := OAI.EditApproximation.arithmeticFlatMapWithWork (fun eb =>
    let side := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat (2 ^ eb))
    let cells := OAI.EditApproximation.BinaryFraction.targetCellsWithWork side.1 (OAI.EditApproximation.bitWordValue radius.1) q
    let sources := OAI.EditApproximation.arithmeticFlatMapWithWork
      (OAI.EditApproximation.BinaryFraction.queryGroupKeySamplesWithWork M F Q eM eb eF hM hF) cells.1
    (sources.1, side.2 + cells.2 + sources.2 + eb + exponent + 4)) scales.1
  (keys.1, scales.2 + radius.2 + keys.2 + 2)

def queryGroupDrawReadAllocation {M F Q : ℕ} [NeZero M]
    (keys : List (OAI.EditApproximation.GroupScalarKey M F Q)) (values : List OAI.EditApproximation.BinaryFraction)
    (b : ℕ) (cell : ℕ × ℕ) (scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length)
    (sample : Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale))) : ℕ :=
  let key : OAI.EditApproximation.GroupScalarKey M F Q := ⟨(b, cell), scale, sample⟩
  let word := (OAI.EditApproximation.BinaryFraction.gatheredWordLookupWithWork OAI.EditApproximation.queryGroupKeyEqualWithWork keys values key).1
  let floor := (OAI.EditApproximation.BinaryFraction.naturalFloorWithWork word).1
  OAI.EditApproximation.BinaryFraction.gatheredLookupAllocation OAI.EditApproximation.queryGroupKeyEqualWithWork OAI.EditApproximation.queryGroupKeyEqualAllocation keys values key +
    OAI.EditApproximation.BinaryFraction.naturalFloorAllocation word + OAI.EditApproximation.bitDivModAllocation M.bits (OAI.EditApproximation.bitWordValue floor).bits

def queryGroupSourceKeysAllocation {n : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a value : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  let radius := (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value).1
  let build := fun eb =>
    let side := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat (2 ^ eb))
    let cells := OAI.EditApproximation.BinaryFraction.targetCellsWithWork side.1 (OAI.EditApproximation.bitWordValue radius) q
    let sources := OAI.EditApproximation.arithmeticFlatMapWithWork (OAI.EditApproximation.BinaryFraction.queryGroupKeySamplesWithWork M F Q eM eb eF hM hF) cells.1
    (sources.1, side.2 + cells.2 + sources.2 + eb + exponent + 4)
  let allocation := fun eb =>
    let side := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat (2 ^ eb))).1
    let cells := (OAI.EditApproximation.BinaryFraction.targetCellsWithWork side (OAI.EditApproximation.bitWordValue radius) q).1
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat (2 ^ eb)) + OAI.EditApproximation.BinaryFraction.targetCellsAllocation side (OAI.EditApproximation.bitWordValue radius) q +
      OAI.EditApproximation.arithmeticFlatMapAllocation (OAI.EditApproximation.BinaryFraction.queryGroupKeySamplesWithWork M F Q eM eb eF hM hF)
        (OAI.EditApproximation.BinaryFraction.queryGroupKeySamplesAllocation M F Q eM eb eF hM hF) cells + eb + exponent + 2
  OAI.EditApproximation.BinaryFraction.queryExponentsAllocation N F a value + OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation value +
    OAI.EditApproximation.arithmeticFlatMapAllocation build allocation (OAI.EditApproximation.BinaryFraction.queryExponentsWithWork N F a value).1

def querySharedInputsAllocation {nx ny : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (parent : OAI.EditApproximation.TargetInterval nx)
    (a value : OAI.EditApproximation.BinaryFraction) (query : OAI.EditApproximation.TargetInterval ny) (draw : OAI.EditApproximation.CountedCellGroupDraws M F Q)
    (allocation : OAI.EditApproximation.CountedCellGroupAllocations M F Q) : ℕ :=
  let scales := (OAI.EditApproximation.BinaryFraction.queryExponentsWithWork N F a value).1
  let radius := (OAI.EditApproximation.BinaryFraction.naturalCeilingWithWork value).1
  let build := fun eb =>
    let side := OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat (2 ^ eb))
    let cells := OAI.EditApproximation.BinaryFraction.targetCellsWithWork side.1 (OAI.EditApproximation.bitWordValue radius) query
    let states := OAI.EditApproximation.arithmeticFlatMapWithWork (fun cell =>
      OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hM hF parent exponent cell (draw (2 ^ eb) cell)) cells.1
    (states.1, side.2 + cells.2 + states.2 + eb + exponent + 4)
  let alloc := fun eb =>
    let side := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat (2 ^ eb))).1
    let cells := (OAI.EditApproximation.BinaryFraction.targetCellsWithWork side (OAI.EditApproximation.bitWordValue radius) query).1
    OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) (OAI.EditApproximation.BinaryFraction.nat (2 ^ eb)) + OAI.EditApproximation.BinaryFraction.targetCellsAllocation side (OAI.EditApproximation.bitWordValue radius) query +
      OAI.EditApproximation.arithmeticFlatMapAllocation
        (fun cell => OAI.EditApproximation.BinaryFraction.querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hM hF parent exponent cell (draw (2 ^ eb) cell))
        (fun cell => OAI.EditApproximation.BinaryFraction.querySharedCellInputsAllocation (ny := ny) M F Q eM eb eF hM hF parent exponent cell
          (draw (2 ^ eb) cell) (allocation (2 ^ eb) cell)) cells + eb + exponent + 2
  let inputs := (OAI.EditApproximation.arithmeticFlatMapWithWork build scales).1
  OAI.EditApproximation.BinaryFraction.queryExponentsAllocation N F a value + OAI.EditApproximation.BinaryFraction.naturalCeilingAllocation value +
    OAI.EditApproximation.arithmeticFlatMapAllocation build alloc scales + OAI.EditApproximation.queryOrderedChildInputsAllocation inputs

theorem _root_.OAI.EditApproximation.Lemmas.indexedGroupScales_value (raw : List.{0} OAI.EditApproximation.BinaryFraction) (M : ℕ) (b : ℕ) (F : ℚ) (h : Eq.{1} (List.map.{0, 0} OAI.EditApproximation.BinaryFraction.value raw) (OAI.EditApproximation.groupDyadicScales M b F)) (i : Fin (List.length.{0} (OAI.EditApproximation.groupDyadicScales M b F))) :
    (OAI.EditApproximation.BinaryFraction.indexedGroupScales raw M b F h i).value = OAI.EditApproximation.groupDyadicScaleAt M b F i := by
  unfold OAI.EditApproximation.BinaryFraction.indexedGroupScales OAI.EditApproximation.groupDyadicScaleAt
  simp only [List.get_eq_getElem]
  rw [← List.getElem_map OAI.EditApproximation.BinaryFraction.value (l := raw) (i := i.val) (h := by rw [h]; exact i.isLt)]
  simp only [h]

def preparedCellGroupSourceAllocationRaw {α : Type u_1} (source target : List α) {M : ℕ}
  (parent : OAI.EditApproximation.TargetInterval source.length) (b P F exponent Q : ℕ) (_hb : 0 < b) (_hP : 0 < P)
  (tau a : OAI.EditApproximation.BinaryFraction)
  (parentInitial : OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
  (child initial current : Fin M → OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
  (R C : ℕ) (_hr : ∀ i q, (child i q).2 ≤ R) (_hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List OAI.EditApproximation.BinaryFraction) (hraw : raw.map OAI.EditApproximation.BinaryFraction.value = OAI.EditApproximation.groupDyadicScales M b (OAI.EditApproximation.BinaryFraction.nat F).value)
  (draw : ∀ t : Fin (OAI.EditApproximation.groupDyadicScales M b (OAI.EditApproximation.BinaryFraction.nat F).value).length,
    Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b (OAI.EditApproximation.BinaryFraction.nat F).value t)) → Fin M × ℕ)
  (parentAllocation : OAI.EditApproximation.TargetInterval target.length → ℕ)
  (childAllocation initialAllocation currentAllocation : Fin M → OAI.EditApproximation.TargetInterval target.length → ℕ)
  (drawAllocation : ∀ t : Fin (OAI.EditApproximation.groupDyadicScales M b (OAI.EditApproximation.BinaryFraction.nat F).value).length,
    Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b (OAI.EditApproximation.BinaryFraction.nat F).value t)) → ℕ)


    (cell : ℕ × ℕ) : ℕ := by
  exact
    let centers := (OAI.EditApproximation.BinaryFraction.cellCentersReadWithWork P F b a (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) parentInitial cell).1
    let members := (OAI.EditApproximation.filterMapWithWork
      (OAI.EditApproximation.BinaryFraction.preparedUnskippedReadWithWorkRaw parent b P exponent tau (OAI.EditApproximation.BinaryFraction.nat F) child initial) centers).1
    OAI.EditApproximation.BinaryFraction.cellCentersReadAllocation P F b a (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) parentInitial parentAllocation cell +
      OAI.EditApproximation.filterMapAllocation (OAI.EditApproximation.BinaryFraction.preparedUnskippedReadWithWorkRaw parent b P exponent tau (OAI.EditApproximation.BinaryFraction.nat F) child initial)
        (fun center => OAI.EditApproximation.BinaryFraction.preparedUnskippedReadAllocation parent center b P exponent tau (OAI.EditApproximation.BinaryFraction.nat F)
          child initial childAllocation initialAllocation) centers +
      if hempty : members = [] then 0 else
        OAI.EditApproximation.BinaryFraction.sampledGroupActionSourceAllocationRaw b exponent Q initial current initialAllocation currentAllocation
          (OAI.EditApproximation.BinaryFraction.indexedGroupScales raw M b (OAI.EditApproximation.BinaryFraction.nat F).value hraw)
          (fun t j => draw t (Fin.cast (congrArg (OAI.EditApproximation.groupSampleCount M Q b)
            (OAI.EditApproximation.Lemmas.indexedGroupScales_value raw M b (OAI.EditApproximation.BinaryFraction.nat F).value hraw t)) j))
          (fun t j => drawAllocation t (Fin.cast (congrArg (OAI.EditApproximation.groupSampleCount M Q b)
            (OAI.EditApproximation.Lemmas.indexedGroupScales_value raw M b (OAI.EditApproximation.BinaryFraction.nat F).value hraw t)) j)) members hempty + 1

def preparedCellGroupSourceWithWorkRaw {α : Type u_1} (source target : List α) {M : ℕ}
  (parent : OAI.EditApproximation.TargetInterval source.length) (b P F exponent Q : ℕ) (_hb : 0 < b) (_hP : 0 < P)
  (tau a : OAI.EditApproximation.BinaryFraction)
  (parentInitial : OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
  (child initial current : Fin M → OAI.EditApproximation.TargetInterval target.length → OAI.EditApproximation.BinaryFraction × ℕ)
  (R C : ℕ) (_hr : ∀ i q, (child i q).2 ≤ R) (_hi : ∀ i q, (initial i q).2 ≤ C)
  (raw : List OAI.EditApproximation.BinaryFraction) (hraw : raw.map OAI.EditApproximation.BinaryFraction.value = OAI.EditApproximation.groupDyadicScales M b (OAI.EditApproximation.BinaryFraction.nat F).value)
  (draw : ∀ t : Fin (OAI.EditApproximation.groupDyadicScales M b (OAI.EditApproximation.BinaryFraction.nat F).value).length,
    Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b (OAI.EditApproximation.BinaryFraction.nat F).value t)) → Fin M × ℕ)
    (cell : ℕ × ℕ) :
    Option (OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval target.length)
      (Fin M × OAI.EditApproximation.TargetInterval target.length) M) × ℕ := by
  exact
    let centers := OAI.EditApproximation.BinaryFraction.cellCentersReadWithWork P F b a (OAI.EditApproximation.BinaryFraction.inversePowerTwo exponent) parentInitial cell
    let members := OAI.EditApproximation.filterMapWithWork
      (OAI.EditApproximation.BinaryFraction.preparedUnskippedReadWithWorkRaw parent b P exponent tau (OAI.EditApproximation.BinaryFraction.nat F) child initial) centers.1
    if h : members.1 = [] then (none, centers.2 + members.2 + 1) else
      let selected := OAI.EditApproximation.BinaryFraction.sampledGroupActionSourceWithWorkRaw b exponent Q initial current (OAI.EditApproximation.BinaryFraction.indexedGroupScales raw M b (OAI.EditApproximation.BinaryFraction.nat F).value hraw)
        (fun t j => draw t (Fin.cast (congrArg (OAI.EditApproximation.groupSampleCount M Q b)
          (OAI.EditApproximation.Lemmas.indexedGroupScales_value raw M b (OAI.EditApproximation.BinaryFraction.nat F).value hraw t)) j)) members.1 h
      (some selected.1, centers.2 + members.2 + selected.2 + 2)

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset

def querySharedInputCover {α : Type u_1} (source target : List α) {M : ℕ}
    (parent : OAI.EditApproximation.TargetInterval source.length) (N F exponent Q : ℕ) (a : ℚ)
    (initial : OAI.EditApproximation.TargetInterval target.length → ℚ) (q : OAI.EditApproximation.TargetInterval target.length)
    (draw : OAI.EditApproximation.CellGroupDraws M F Q) : Finset (Fin M × OAI.EditApproximation.TargetInterval target.length) :=
  (OAI.EditApproximation.localGroupQueryKeys N F exponent a initial q).toFinset.biUnion fun key =>
    Finset.univ.biUnion fun scale : Fin (OAI.EditApproximation.groupDyadicScales M key.1 F).length =>
      OAI.EditApproximation.groupCurrentInputCover source target parent key.1 exponent Q key.2
        (OAI.EditApproximation.groupDyadicScaleAt M key.1 F scale) (draw key.1 key.2 scale)

def coarseThresholdChildrenCost {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam : ℚ)
    (value : OAI.EditApproximation.CoarseSourceTree B α D → OAI.EditApproximation.CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (allowance : ℚ) :
    List (OAI.EditApproximation.CoarseSourceTree B α D × Fin B × OAI.EditApproximation.CoarseThresholdDraws B D) → ℕ → Fin (2 * k + 1) → ℚ
  | [], _, _ => 0
  | (child, draw, below) :: rest, start, shift =>
    let threshold := OAI.EditApproximation.coarseChildThreshold B Q allowance draw
    let childMinimum := univ.inf' univ_nonempty (fun next =>
      value child below (lam * threshold) start next + (2 * Nat.dist shift.val next.val : ℕ))
    OAI.EditApproximation.coarseThresholdContribution threshold (allowance / Q) childMinimum +
      coarseThresholdChildrenCost k Q lam value allowance rest (start + child.word.length) shift

def coarseThresholdEstimate {B : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α)) :
    {D : ℕ} → OAI.EditApproximation.CoarseSourceTree B α D → OAI.EditApproximation.CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ
  | _, tree, draws, allowance, start, shift =>
    if (tree.word.length : ℚ) ≤ allowance then 0 else
    match tree, draws with
    | .leaf letter, _ => (OAI.EditApproximation.coarseShiftCost k frame (.leaf (B := B) letter) start shift : ℚ)
    | .branch children, (draws, below) =>
      OAI.EditApproximation.coarseThresholdChildrenCost k Q lam
        (fun child => coarseThresholdEstimate k Q lam frame child) allowance
        (List.ofFn fun i => (children i, draws i, below i)) start shift

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

abbrev PhysicalScalarIndex (M J N n exponent F Q R B : ℕ)
    (key : OAI.EditApproximation.PhysicalCommonKey M J N n exponent B) : Type :=
  match key with
  | .inl _ => Fin R
  | .inr group => Σ _time : Fin R,
      Σ scale : Fin (OAI.EditApproximation.groupDyadicScales M ((OAI.EditApproximation.dyadicScales N).get group.2.1) F).length,
        Fin (OAI.EditApproximation.groupSampleCount M Q ((OAI.EditApproximation.dyadicScales N).get group.2.1)
          (OAI.EditApproximation.groupDyadicScaleAt M ((OAI.EditApproximation.dyadicScales N).get group.2.1) F scale))

def computedPhysicalCoarseDepth (source target : List ℕ) (N : ℕ)
    (entry : OAI.EditApproximation.PhysicalEntry (OAI.EditApproximation.integerParameters N).M
      (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M source.length) target.length) : ℕ :=
  OAI.EditApproximation.computedCoarseDepth N (OAI.EditApproximation.coarseEntryWidth (OAI.EditApproximation.physicalSource source entry.1)
    (OAI.EditApproximation.substring target entry.2.lo entry.2.hi))

abbrev PhysicalScalarKey (M J N n exponent F Q R B : ℕ) :=
  Σ key : OAI.EditApproximation.PhysicalCommonKey M J N n exponent B, OAI.EditApproximation.PhysicalScalarIndex M J N n exponent F Q R B key

instance physicalScalarIndexFintype (M J N n exponent F Q R B : ℕ)
    (key : OAI.EditApproximation.PhysicalCommonKey M J N n exponent B) :
    Fintype (OAI.EditApproximation.PhysicalScalarIndex M J N n exponent F Q R B key) := by
  cases key <;> dsimp only [OAI.EditApproximation.PhysicalScalarIndex] <;> infer_instance

def physicalScalarRange (M J N n exponent F Q R B : ℕ)
    (key : OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) : ℕ :=
  match key.1 with
  | .inl online => online.2.val.val
  | .inr _ => M

instance physicalScalarRangeNeZero (M J N n exponent F Q R B : ℕ) [NeZero M]
    (key : OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) :
    NeZero (OAI.EditApproximation.physicalScalarRange M J N n exponent F Q R B key) := by
  rcases key with ⟨key, index⟩
  cases key <;> dsimp only [OAI.EditApproximation.physicalScalarRange] <;> infer_instance

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def queryGroupSourceGather {ι : Type u_1} {β : Type u_2} {n : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a : OAI.EditApproximation.BinaryFraction)
    (initial : OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ) (q : OAI.EditApproximation.TargetInterval n)
    (reader : OAI.EditApproximation.GroupScalarKey M F Q → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (next : List (OAI.EditApproximation.GroupScalarKey M F Q) → List OAI.EditApproximation.BinaryFraction → OAI.EditApproximation.BitQuery ι β) : OAI.EditApproximation.BitQuery ι β :=
  let query := initial q
  .charge query.2 ((OAI.EditApproximation.BitQuery.compute
    (OAI.EditApproximation.BinaryFraction.queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a query.1 q)).bind
      fun keys => OAI.EditApproximation.BitQuery.collect reader keys (next keys))

def physicalScalarCodeWithWork {M J N n exponent F Q R B : ℕ}
    (key : OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) : ℕ × ℕ :=
  match key with
  | ⟨.inl online, time⟩ =>
      let entry := OAI.EditApproximation.physicalEntryCodeWithWork (online.1.1.val, online.1.2.2)
      let first := OAI.EditApproximation.naturalPairWithWork online.2.val.val time.val
      let second := OAI.EditApproximation.naturalPairWithWork online.1.2.1.val first.1
      let last := OAI.EditApproximation.naturalPairWithWork entry.1 second.1
      (2 * last.1, entry.2 + first.2 + second.2 + last.2 + 2)
  | ⟨.inr group, index⟩ =>
      let node := OAI.EditApproximation.physicalNodeCodeWithWork group.1.val
      let a := OAI.EditApproximation.naturalPairWithWork index.2.1.val index.2.2.val
      let b := OAI.EditApproximation.naturalPairWithWork index.1.val a.1
      let c := OAI.EditApproximation.naturalPairWithWork group.2.2.2.val b.1
      let d := OAI.EditApproximation.naturalPairWithWork group.2.2.1.val c.1
      let e := OAI.EditApproximation.naturalPairWithWork group.2.1.val d.1
      let f := OAI.EditApproximation.naturalPairWithWork node.1 e.1
      (2 * f.1 + 1, node.2 + a.2 + b.2 + c.2 + d.2 + e.2 + f.2 + 3)

def physicalScalarCodeAllocation {M J N n exponent F Q R B : ℕ}
    (key : OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) : ℕ :=
  match key with
  | ⟨.inl online, _⟩ => 2 * online.1.1.val.1.val + J + 20
  | ⟨.inr group, _⟩ => 2 * group.1.val.1.val + J + 25

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable (M J N n exponent F Q R B : ℕ) [NeZero M]

abbrev PhysicalGroupQueries (b : ℕ) :=
  ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length,
    Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) →
      OAI.EditApproximation.FiniteQuery (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B)

def physicalScalarOnlineRead (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × OAI.EditApproximation.TargetInterval n) (range : ℕ) : OAI.EditApproximation.FiniteQuery (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) :=
  if hb : key.1 ∈ OAI.EditApproximation.dyadicScales N then
    if hr : 0 < range ∧ range ≤ B then
      .read ⟨.inl ((node, OAI.EditApproximation.physicalScaleIndex N key.1 hb, key.2),
        OAI.EditApproximation.positiveDrawRangeOfLE B range hr.1 hr.2), time⟩ .done
    else .done 0
  else .done 0

def physicalScalarGroupQueriesAt (key : OAI.EditApproximation.PhysicalLocalGroupKey M J N n exponent) (time : Fin R) :
    OAI.EditApproximation.PhysicalGroupQueries M J N n exponent F Q R B ((OAI.EditApproximation.dyadicScales N).get key.2.1) :=
  fun scale sample => .read ⟨.inr key, ⟨time, scale, sample⟩⟩ .done

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

variable (M J N n exponent F Q R B : ℕ)

abbrev BitPhysicalGroupQueries (b : ℕ) :=
  ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length,
    Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) →
      OAI.EditApproximation.BitQuery (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction

def queryPhysicalScalarRead (key : OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) :
    OAI.EditApproximation.BitQuery (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction :=
  .charge ((OAI.EditApproximation.physicalScalarCodeWithWork key).2 + 1) (.read key .done)

def queryPhysicalScalarGroupQueriesAt (key : OAI.EditApproximation.PhysicalLocalGroupKey M J N n exponent) (time : Fin R) :
    OAI.EditApproximation.BitPhysicalGroupQueries M J N n exponent F Q R B ((OAI.EditApproximation.dyadicScales N).get key.2.1) :=
  fun scale sample => OAI.EditApproximation.queryPhysicalScalarRead M J N n exponent F Q R B
    ⟨.inr key, ⟨time, scale, sample⟩⟩

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset MeasureTheory ProbabilityTheory

variable {α : Type u_1} {source target : List α} {M b P thetaExponent : ℕ} {parent : TargetInterval source.length} {tau F : ℚ} {child initial : Fin M → TargetInterval target.length → ℚ}

def dyadicUnskippedGroupEstimate (Q : ℕ)
    (value : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ)
    (member : OAI.EditApproximation.UnskippedBand source target parent b P thetaExponent tau F child initial)
    (draw : ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length,
      Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) → Fin M) : ℚ :=
  OAI.EditApproximation.unskippedGroupEstimate (OAI.EditApproximation.groupDyadicScaleAt M b F)
    (fun scale => OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) value member draw

def chooseUnskippedGroup (Q : ℕ)
    (value : Fin M → OAI.EditApproximation.TargetInterval target.length → ℚ)
    (members : List (OAI.EditApproximation.UnskippedBand source target parent b P thetaExponent tau F child initial))
    (hnonempty : members ≠ [])
    (draw : ∀ scale : Fin (OAI.EditApproximation.groupDyadicScales M b F).length,
      Fin (OAI.EditApproximation.groupSampleCount M Q b (OAI.EditApproximation.groupDyadicScaleAt M b F scale)) → Fin M) :
    OAI.EditApproximation.UnskippedBand source target parent b P thetaExponent tau F child initial :=
  OAI.EditApproximation.selectGroupMember members hnonempty (fun member => OAI.EditApproximation.dyadicUnskippedGroupEstimate Q value member draw)

end OAI.EditApproximation

end


