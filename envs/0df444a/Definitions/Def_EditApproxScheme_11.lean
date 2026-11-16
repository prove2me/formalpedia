-- Prove2me | Definitions.Def_EditApproxScheme_11
-- name    : EditApproxScheme_11
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T16:43:18.193194+00:00
-- url     : https://prove2.me/theorems/ba65841d-7ea4-4077-b3a3-0d5ddc251ba2
-- title:
--   Edit-distance approximation scheme, part 11 of 20: prepared kernels and coarse entries
-- statement:
--   This is **part 11 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains coordinate vectors, prepared action kernels, sampled online reads, ranked program bodies, charged warmup children, coarse entry widths and trees, the full coarse seed draws, rejection-sampling runtime arrays, and indexed leaves and slices. It also proves 10 supporting lemmas (namespace `OAI.EditApproximation.Lemmas`) that these definitions use.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope. A description of the whole scheme is given in part 20.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L6052-L6611 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 11 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_10

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

open Finset

theorem _root_.OAI.EditApproximation.Lemmas.arithmeticFlatMapWithWork_value {α : Type 0} {β : Type 0} (f : α → Prod.{0, 0} (List.{0} β) ℕ) (values : List.{0} α) :
    (OAI.EditApproximation.arithmeticFlatMapWithWork f values).1 = values.flatMap (fun a => (f a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih => simp only [OAI.EditApproximation.arithmeticFlatMapWithWork, ih, List.flatMap_cons]

theorem _root_.OAI.EditApproximation.Lemmas.arithmeticMapWithWork_value {α : Type 0} {β : Type 0} (f : α → Prod.{0, 0} β ℕ) (values : List.{0} α) :
    (OAI.EditApproximation.arithmeticMapWithWork f values).1 = values.map (fun a => (f a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih => simp only [OAI.EditApproximation.arithmeticMapWithWork, ih, List.map_cons]

theorem _root_.OAI.EditApproximation.Lemmas.memberByWithWork_value {α : Type 0} (equal : α → α → Prod.{0, 0} Bool ℕ) (heq : ∀ (a b : α), Eq.{1} (equal a b).1 Bool.true ↔ Eq.{0 + 1} a b) (a : α) (xs : List.{0} α) :
    (OAI.EditApproximation.memberByWithWork equal a xs).1 = true ↔ a ∈ xs := by
  induction xs with
  | nil => simp only [OAI.EditApproximation.memberByWithWork, Bool.false_eq_true, List.not_mem_nil]
  | cons b xs ih => simp only [OAI.EditApproximation.memberByWithWork, Bool.or_eq_true, heq, ih, List.mem_cons]

theorem _root_.OAI.EditApproximation.Lemmas.dedupByWithWork_value {α : Type 0} [instLocal1 : DecidableEq.{0 + 1} α] (equal : α → α → Prod.{0, 0} Bool ℕ) (heq : ∀ (a b : α), Eq.{1} (equal a b).1 Bool.true ↔ Eq.{0 + 1} a b) (xs : List.{0} α) :
    (OAI.EditApproximation.dedupByWithWork equal xs).1 = xs.dedup := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have hm := OAI.EditApproximation.Lemmas.memberByWithWork_value equal heq a rest
    have ht : (OAI.EditApproximation.memberByWithWork equal a rest).1 = decide (a ∈ rest) :=
      Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hm)
    simp only [OAI.EditApproximation.dedupByWithWork, ht, ih, List.dedup_cons, decide_eq_true_eq]

theorem _root_.OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_eq (a : ℕ) (b : ℕ) :
    (OAI.EditApproximation.binaryNaturalCompareWithWork a b).1 = .eq ↔ a = b := by
  simpa only [OAI.EditApproximation.binaryNaturalCompareWithWork, OAI.EditApproximation.Lemmas.bitWordValue_bits] using OAI.EditApproximation.Lemmas.bitCompareWithWork_eq a.bits b.bits

theorem _root_.OAI.EditApproximation.Lemmas.naturalEqualWithWork_value (a : ℕ) (b : ℕ) :
    (OAI.EditApproximation.naturalEqualWithWork a b).1 = true ↔ a = b := by
  simp only [OAI.EditApproximation.naturalEqualWithWork, decide_eq_true_eq, OAI.EditApproximation.Lemmas.binaryNaturalCompareWithWork_eq]

theorem _root_.OAI.EditApproximation.Lemmas.coordinateEqualWithWork_value {M : ℕ} {n : ℕ} (a : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval n)) (b : Prod.{0, 0} (Fin M) (OAI.EditApproximation.TargetInterval n)) :
    (OAI.EditApproximation.coordinateEqualWithWork a b).1 = true ↔ a = b := by
  simp only [OAI.EditApproximation.coordinateEqualWithWork, Bool.and_eq_true, OAI.EditApproximation.Lemmas.naturalEqualWithWork_value]
  constructor
  · rintro ⟨⟨hc, hl⟩, hh⟩
    have hi : a.1 = b.1 := Fin.ext hc
    have hq : a.2 = b.2 := by
      rcases a with ⟨i, q⟩
      rcases b with ⟨j, r⟩
      cases q
      cases r
      cases hl
      cases hh
      rfl
    exact Prod.ext hi hq
  · intro h
    subst b
    exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem _root_.OAI.EditApproximation.Lemmas.bandCoordinatesWithWork_value {M : ℕ} {n : ℕ} (band : List.{0} (Fin M → OAI.EditApproximation.TargetInterval n)) :
    (OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork band).1 = OAI.EditApproximation.listedBandCoordinates band := by
  simp only [OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork, OAI.EditApproximation.Lemmas.dedupByWithWork_value _ OAI.EditApproximation.Lemmas.coordinateEqualWithWork_value,
    OAI.EditApproximation.Lemmas.arithmeticFlatMapWithWork_value, OAI.EditApproximation.Lemmas.arithmeticMapWithWork_value, OAI.EditApproximation.listedBandCoordinates,
    List.ofFn_eq_map]

def coordinateVectorWithWork {M n : ℕ} (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) :
    Vector (Fin M × OAI.EditApproximation.TargetInterval n) (OAI.EditApproximation.listedBandCoordinates band).length × ℕ := by
  exact
    let coordinates := OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork band
    (Vector.ofFn (fun i => coordinates.1.get ⟨i.val, by
      rw [OAI.EditApproximation.Lemmas.bandCoordinatesWithWork_value]
      exact i.isLt⟩), coordinates.2 + coordinates.1.length + 1)

def reduceOnlineIntegerWithWork (K : ℕ) (hK : 0 < K) (integer : ℕ) :
    Fin (OAI.EditApproximation.optimizerTriangularMass K) × ℕ := by
  exact
    let mass := OAI.EditApproximation.triangularMassWithWork K
    let divided := OAI.EditApproximation.binaryNaturalDivModWithWork integer (OAI.EditApproximation.bitWordValue mass.1)
    (⟨OAI.EditApproximation.bitWordValue divided.2.1, by
      rw [(OAI.EditApproximation.Lemmas.binaryNaturalDivModWithWork_spec integer (OAI.EditApproximation.bitWordValue mass.1)
        (by rw [OAI.EditApproximation.Lemmas.triangularMassWithWork_value]; exact OAI.EditApproximation.Lemmas.optimizerTriangularMass_positive K hK)).2]
      rw [OAI.EditApproximation.Lemmas.triangularMassWithWork_value]
      exact Nat.mod_lt _ (OAI.EditApproximation.Lemmas.optimizerTriangularMass_positive K hK)⟩,
      mass.2 + divided.2.2 + Nat.size integer + 2)

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

def countedPreparedActionReadWithWork {M n : ℕ} (mass : Vector OAI.EditApproximation.BinaryFraction M)
    (read : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (eta kappa : OAI.EditApproximation.BinaryFraction) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) (G j t : ℕ) :
    Option (Fin M → OAI.EditApproximation.TargetInterval n) × ℕ :=
  let coordinates := OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork band
  let vertices := OAI.EditApproximation.BinaryFraction.countedBandVerticesWithWork coordinates.1 mass band
  let linear := OAI.EditApproximation.vectorMapWithWork _ fun i =>
    OAI.EditApproximation.BinaryFraction.onlineLinearReadWithWork (fun child => mass.get child) read eta kappa t (coordinates.1.get i)
  let selected := OAI.EditApproximation.BinaryFraction.selectionWithWork vertices.1 linear.1 G j
  (selected.1, coordinates.2 + vertices.2 + linear.2 + selected.2 + 3)

def countedPreparedActionKernelAllocation {M n : ℕ} (mass : Vector OAI.EditApproximation.BinaryFraction M)
    (read : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → ℕ)
    (eta kappa : OAI.EditApproximation.BinaryFraction) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) (G j t : ℕ) : ℕ :=
  let coordinates := (OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork band).1
  let vertices := (OAI.EditApproximation.BinaryFraction.countedBandVerticesWithWork coordinates mass band).1
  let linear := (OAI.EditApproximation.vectorMapWithWork _ fun i =>
    OAI.EditApproximation.BinaryFraction.onlineLinearReadWithWork (fun child => mass.get child) read eta kappa t (coordinates.get i)).1
  OAI.EditApproximation.BinaryFraction.countedBandVerticesAllocation coordinates mass band +
    OAI.EditApproximation.vectorMapAllocation _ (fun i => OAI.EditApproximation.BinaryFraction.onlineLinearReadAllocation (fun child => mass.get child)
      read footprint eta kappa t (coordinates.get i)) + OAI.EditApproximation.BinaryFraction.selectionAllocation vertices linear G j

def countedBandActionReadWithWork {M n : ℕ} (b : ℕ)
    (initial : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (read : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (eta kappa : OAI.EditApproximation.BinaryFraction) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) (G j t : ℕ) :
    Option (Fin M → OAI.EditApproximation.TargetInterval n) × ℕ :=
  let mass := OAI.EditApproximation.BinaryFraction.envelopeVectorReadWithWork b band initial
  let selected := OAI.EditApproximation.BinaryFraction.countedPreparedActionReadWithWork mass.1 read eta kappa band G j t
  (selected.1, mass.2 + selected.2 + 1)

def countedPreparedActionAllocation {M n : ℕ} (mass : Vector OAI.EditApproximation.BinaryFraction M)
    (read : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → ℕ)
    (eta kappa : OAI.EditApproximation.BinaryFraction) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) (G j t : ℕ) : ℕ :=
  OAI.EditApproximation.BinaryFraction.coordinateVectorAllocation band + OAI.EditApproximation.BinaryFraction.countedPreparedActionKernelAllocation mass read footprint eta kappa band G j t

def countedSampledOnlineReadWithWork {n M : ℕ} (center : OAI.EditApproximation.TargetInterval n) (b : ℕ)
    (initial : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (read : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (eta kappa : OAI.EditApproximation.BinaryFraction) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) (hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (OAI.EditApproximation.optimizerTriangularMass K)) :
    OAI.EditApproximation.BinaryBellmanAction (OAI.EditApproximation.TargetInterval n) (Fin M × OAI.EditApproximation.TargetInterval n) M × ℕ :=
  let chosen := OAI.EditApproximation.triangularChoiceWithWork K integer
  let selected := OAI.EditApproximation.BinaryFraction.countedBandActionReadWithWork b initial read eta kappa band G chosen.1.val t
  let states := selected.1.getD (band.head hne)
  (⟨center, OAI.EditApproximation.BinaryFraction.zero, fun i => (i, states i)⟩, chosen.2 + selected.2 + M + 2)

def countedBandActionAllocation {M n : ℕ} (b : ℕ)
    (initial : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (initialAllocation : Fin M → OAI.EditApproximation.TargetInterval n → ℕ)
    (read : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (footprint : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → ℕ)
    (eta kappa : OAI.EditApproximation.BinaryFraction) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) (G j t : ℕ) : ℕ :=
  OAI.EditApproximation.BinaryFraction.envelopeVectorReadAllocation b band initial initialAllocation +
    OAI.EditApproximation.BinaryFraction.countedPreparedActionAllocation (OAI.EditApproximation.BinaryFraction.envelopeVectorReadWithWork b band initial).1
      read footprint eta kappa band G j t

def countedSampledOnlineAllocation {n M : ℕ} (_center : OAI.EditApproximation.TargetInterval n) (b : ℕ)
    (initial : Fin M → OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (initialAllocation : Fin M → OAI.EditApproximation.TargetInterval n → ℕ)
    (read : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → OAI.EditApproximation.BinaryFraction × ℕ)
    (readAllocation : ℕ → Fin M × OAI.EditApproximation.TargetInterval n → ℕ)
    (eta kappa : OAI.EditApproximation.BinaryFraction) (band : List (Fin M → OAI.EditApproximation.TargetInterval n)) (_hne : band ≠ [])
    (G K t : ℕ) (integer : Fin (OAI.EditApproximation.optimizerTriangularMass K)) : ℕ :=
  let chosen := (OAI.EditApproximation.triangularChoiceWithWork K integer).1
  OAI.EditApproximation.triangularChoiceAllocation K integer +
    OAI.EditApproximation.BinaryFraction.countedBandActionAllocation b initial initialAllocation read readAllocation eta kappa band G chosen.val t + M + 1

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.SourceRanked

variable {σ : Type u_1} {κ : Type u_2}

def rank (tableRank : κ → ℕ) : Sum σ κ → ℕ
  | .inl _ => 0
  | .inr key => tableRank key + 1

def keyCode (sourceCode : σ → ℕ) (tableCode : κ → ℕ) : Sum σ κ → ℕ
  | .inl source => 2 * sourceCode source
  | .inr table => 2 * tableCode table + 1

def child (tableRank : κ → ℕ) (parent : κ) :
    Sum σ {key : κ // tableRank key < tableRank parent} →
      {key : Sum σ κ // OAI.EditApproximation.SourceRanked.rank tableRank key < OAI.EditApproximation.SourceRanked.rank (σ := σ) tableRank (.inr parent)}
  | .inl source => ⟨.inl source, Nat.zero_lt_succ _⟩
  | .inr table => ⟨.inr table.val, Nat.add_lt_add_right table.property 1⟩

def body (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → OAI.EditApproximation.FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (key : Sum σ κ) :
    OAI.EditApproximation.FiniteQuery {next : Sum σ κ // OAI.EditApproximation.SourceRanked.rank tableRank next < OAI.EditApproximation.SourceRanked.rank tableRank key} :=
  match key with
  | .inl source => .done (sourceValue source)
  | .inr table => OAI.EditApproximation.FiniteQuery.mapKeys (OAI.EditApproximation.SourceRanked.child tableRank table) (tableBody table)

def bitBody (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → OAI.EditApproximation.BitQuery (Sum σ {key : κ // tableRank key < tableRank parent}) OAI.EditApproximation.BinaryFraction)
    (sourceValue : σ → OAI.EditApproximation.BinaryFraction × ℕ) (key : Sum σ κ) :
    OAI.EditApproximation.BitQuery {next : Sum σ κ // OAI.EditApproximation.SourceRanked.rank tableRank next < OAI.EditApproximation.SourceRanked.rank tableRank key} OAI.EditApproximation.BinaryFraction :=
  match key with
  | .inl source => OAI.EditApproximation.BitQuery.compute (sourceValue source)
  | .inr table => OAI.EditApproximation.BitQuery.mapKeysWithWork (fun key => (OAI.EditApproximation.SourceRanked.child tableRank table key, 1)) (tableBody table)

end OAI.EditApproximation.SourceRanked

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.ChargedPhysicalRequest

def depth {M J ny passes copies T S : ℕ} : OAI.EditApproximation.ChargedPhysicalRequest M J ny passes copies T S → ℕ
  | .inl entry => J - entry.1.1.val
  | .inr request => request.val.remainingDepth

def index {M J ny passes copies T S : ℕ} : OAI.EditApproximation.ChargedPhysicalRequest M J ny passes copies T S → ℕ
  | .inl _ => 0
  | .inr request => request.val.rank T S + 1

def rank {M J ny passes copies T S : ℕ}
    (request : OAI.EditApproximation.ChargedPhysicalRequest M J ny passes copies T S) : ℕ :=
  request.depth + request.index

end OAI.EditApproximation.ChargedPhysicalRequest

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

theorem _root_.OAI.EditApproximation.Lemmas.table_rank_lt {M : ℕ} {J : ℕ} {ny : ℕ} {passes : ℕ} {copies : ℕ} {T : ℕ} {S : ℕ} (parent : Subtype.{1} fun request => OAI.EditApproximation.PhysicalTableRequest.Bounded (M := M) (J := J) (ny := ny) passes copies T S request) (child : Subtype.{1} fun request => OAI.EditApproximation.PhysicalTableRequest.Bounded (M := M) (J := J) (ny := ny) passes copies T S request) (h : LT.lt.{0} (OAI.EditApproximation.PhysicalTableRequest.combinedRank T S child.val)
  (OAI.EditApproximation.PhysicalTableRequest.combinedRank T S parent.val)) :
    OAI.EditApproximation.ChargedPhysicalRequest.rank (Sum.inr child : OAI.EditApproximation.ChargedPhysicalRequest M J ny passes copies T S) < OAI.EditApproximation.ChargedPhysicalRequest.rank (Sum.inr parent) := by
  simpa only [OAI.EditApproximation.ChargedPhysicalRequest.rank, OAI.EditApproximation.ChargedPhysicalRequest.depth, OAI.EditApproximation.ChargedPhysicalRequest.index, ← Nat.add_assoc, OAI.EditApproximation.PhysicalTableRequest.combinedRank] using
    Nat.add_lt_add_right h 1

def chargedPreviousRead {M J ny passes copies T S : ℕ}
    (parent : {r : OAI.EditApproximation.PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (hpass : 0 < parent.val.pass) (state : OAI.EditApproximation.TargetInterval ny) (copy : Fin copies) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.ChargedPhysicalRequest M J ny passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (Sum.inr parent)} := by
  exact
    .read ⟨Sum.inr (OAI.EditApproximation.chargedPreviousPass parent state copy), by
      apply OAI.EditApproximation.Lemmas.table_rank_lt
      apply OAI.EditApproximation.Lemmas.combinedRank_lt_of_progress T S parent.val _
      exact Or.inr ⟨(OAI.EditApproximation.Lemmas.previousPassRequest_progress T S copy.val parent.val hpass state).1.le,
        (OAI.EditApproximation.Lemmas.previousPassRequest_progress T S copy.val parent.val hpass state).2⟩⟩ .done

def chargedWarmupChild {M J ny passes copies T S : ℕ}
    (parent : {r : OAI.EditApproximation.PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (hbelow : parent.val.node.1.val < J) (hindex : 0 < parent.val.index)
    (input : Fin M × OAI.EditApproximation.TargetInterval ny) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.ChargedPhysicalRequest M J ny passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (Sum.inr parent)} := by
  exact
    .read ⟨Sum.inr ⟨OAI.EditApproximation.PhysicalTableRequest.warmup parent.val.pass parent.val.copy
        (OAI.EditApproximation.physicalChild parent.val.node hbelow input.1) (parent.val.index - 1) input.2,
        parent.property.1, parent.property.2.1,
        (Nat.sub_le _ _).trans parent.property.2.2⟩, by
      apply OAI.EditApproximation.Lemmas.table_rank_lt
      exact OAI.EditApproximation.Lemmas.combinedRank_warmup_child parent.val.pass parent.val.copy T S
        parent.val.index parent.val.node hbelow input.1 parent.val.state input.2 hindex⟩ .done

theorem _root_.OAI.EditApproximation.Lemmas.coarse_rank_lt {M : ℕ} {J : ℕ} {ny : ℕ} {passes : ℕ} {copies : ℕ} {T : ℕ} {S : ℕ} (entry : OAI.EditApproximation.PhysicalEntry M J ny) (request : Subtype.{1} fun request => OAI.EditApproximation.PhysicalTableRequest.Bounded (M := M) (J := J) (ny := ny) passes copies T S request) (hnode : Eq.{1} entry.1 request.val.node) :
    OAI.EditApproximation.ChargedPhysicalRequest.rank (Sum.inl entry : OAI.EditApproximation.ChargedPhysicalRequest M J ny passes copies T S) < OAI.EditApproximation.ChargedPhysicalRequest.rank (Sum.inr request) := by
  change J - entry.1.1.val + 0 < request.val.remainingDepth + (request.val.rank T S + 1)
  rw [hnode]
  unfold OAI.EditApproximation.PhysicalTableRequest.remainingDepth
  omega

def chargedSeedQuery {M J ny passes copies T S : ℕ} (N : ℕ) (multiplier : ℕ → ℕ)
    (parent : {r : OAI.EditApproximation.PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (state : OAI.EditApproximation.PhysicalEntry M J ny) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.ChargedPhysicalRequest M J ny passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (Sum.inr parent)} := by
  exact
    if hn : state.1 = parent.val.node then
      if hp : parent.val.pass = 0 then
        .read ⟨Sum.inl state, OAI.EditApproximation.Lemmas.coarse_rank_lt state parent hn⟩ .done
      else OAI.EditApproximation.FiniteQuery.collect (OAI.EditApproximation.chargedPreviousRead parent (Nat.pos_of_ne_zero hp) state.2)
        (List.finRange copies) fun values =>
          .done (min N (OAI.EditApproximation.upperMedian (values.map fun value =>
            ⌈(multiplier (parent.val.pass - 1) : ℚ) * value⌉₊)) : ℕ)
    else .done 0

def chargedWarmupQuery {α : Type u_1} [DecidableEq α] {M J passes copies T S : ℕ}
    (source target : List α) (N P F : ℕ) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : OAI.EditApproximation.PhysicalTableRequest M J target.length // r.Bounded passes copies T S}) :
    OAI.EditApproximation.FiniteQuery {child : OAI.EditApproximation.ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < OAI.EditApproximation.ChargedPhysicalRequest.rank (Sum.inr parent)} :=
  if hz : parent.val.index = 0 then
    OAI.EditApproximation.physicalInitialQuery source target N P F (factor parent.val.pass)
      (OAI.EditApproximation.chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)
  else if hbelow : parent.val.node.1.val < J then
    if (OAI.EditApproximation.physicalSourceInterval source.length parent.val.node).hi -
        (OAI.EditApproximation.physicalSourceInterval source.length parent.val.node).lo ≤ 1 then
      OAI.EditApproximation.physicalInitialQuery source target N P F (factor parent.val.pass)
        (OAI.EditApproximation.chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)
    else OAI.EditApproximation.physicalWarmupStepQuery source target N P F (factor parent.val.pass)
      (OAI.EditApproximation.chargedSeedQuery N multiplier parent)
      (OAI.EditApproximation.chargedWarmupChild parent hbelow (Nat.pos_of_ne_zero hz)) parent.val.node parent.val.state
  else OAI.EditApproximation.physicalInitialQuery source target N P F (factor parent.val.pass)
    (OAI.EditApproximation.chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open EditDistortion Finset MeasureTheory ProbabilityTheory

abbrev coarseEntryWidth {α : Type u} (x y : List α) : ℕ := max x.length y.length

abbrev CoarseGuessIndex (n : ℕ) := Fin (Nat.clog 2 n + 1)

def coarseGuess (n : ℕ) (i : OAI.EditApproximation.CoarseGuessIndex n) : ℕ := 2 ^ i.val

def coarseEntryTree (B D : ℕ) {α : Type u} (x y : List α) : OAI.EditApproximation.CoarseSourceTree B (Option α) D :=
  OAI.EditApproximation.coarseSourceTreeOfList B D (OAI.EditApproximation.coarsePadTo (OAI.EditApproximation.coarseEntryWidth x y) x)

noncomputable def coarseInitialMeasure (B D n : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    Measure (OAI.EditApproximation.CoarseGuessIndex n → OAI.EditApproximation.CoarseThresholdDraws B D) :=
  Measure.pi fun _ => OAI.EditApproximation.coarseDrawMeasure B D

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Finset MeasureTheory ProbabilityTheory

def coarseActiveChildrenWork {B D : ℕ} {α : Type u}
    (Q lam allowance : ℚ)
    (work : OAI.EditApproximation.CoarseSourceTree B α D → OAI.EditApproximation.CoarseThresholdDraws B D → ℚ → ℕ) :
    List (OAI.EditApproximation.CoarseSourceTree B α D × Fin B × OAI.EditApproximation.CoarseThresholdDraws B D) → ℕ
  | [] => 0
  | (child, draw, below) :: rest =>
    work child below (lam * OAI.EditApproximation.coarseChildThreshold B Q allowance draw) +
      coarseActiveChildrenWork Q lam allowance work rest

abbrev CoarseFullSeedDraws (B : ℕ) {I : Type u_1} {α : Type u_2} (depth : I → ℕ) (x y : I → List α) :=
  ∀ i, OAI.EditApproximation.CoarseGuessIndex (OAI.EditApproximation.coarseEntryWidth (x i) (y i)) → OAI.EditApproximation.CoarseThresholdDraws B (depth i)

noncomputable def coarseFullSeedMeasure (B : ℕ) [NeZero B]
    {I : Type u_1} {α : Type u_2} [Fintype I] (depth : I → ℕ) (x y : I → List α)
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    Measure (OAI.EditApproximation.CoarseFullSeedDraws B depth x y) :=
  Measure.pi fun i => OAI.EditApproximation.coarseInitialMeasure B (depth i) (OAI.EditApproximation.coarseEntryWidth (x i) (y i))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open MeasureTheory ProbabilityTheory

variable {ι : Type u_1} [Fintype ι] (range : ι → ℕ) [∀ i, NeZero (range i)]

noncomputable def rejectionAcceptedLaw : Measure (∀ i, Fin (range i)) :=
  Measure.pi fun i => (PMF.uniformOfFintype (Fin (range i))).toMeasure

abbrev RejectionRuntimeArray := (ι → ℕ) × (∀ i, Fin (range i))

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryMemo

def fractionStorage : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.BinaryFraction → ℕ
  | .empty => 0
  | .node value left right =>
    3 + (value.map fun word => word.numerator.bits.length + word.denominator.length + 1).getD 0 +
      left.fractionStorage + right.fractionStorage

def valueStorage {α : Type u_1} (bits : α → ℕ) : OAI.EditApproximation.BinaryMemo α → ℕ
  | .empty => 0
  | .node value l r => 3 + (value.map bits).getD 0 + valueStorage bits l + valueStorage bits r

end OAI.EditApproximation.BinaryMemo

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter

def indexedLeafWithWork (table : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) : ℕ × ℕ :=
  match symbol with
  | none => (hi - lo, 2)
  | some a => OAI.EditApproximation.indexedSingletonCostWithWork table symbolBits positionBits a lo hi

def integerOccurrenceStorage (source target : List ℤ) : ℕ :=
  OAI.EditApproximation.BinaryMemo.valueStorage OAI.EditApproximation.PositionCounts.storageBits (OAI.EditApproximation.integerOccurrenceIndex source target)

def integerStoredDataSpace (source target : List ℤ) : ℕ :=
  OAI.EditApproximation.storedIntegerBits source + OAI.EditApproximation.storedIntegerBits target +
    OAI.EditApproximation.storedNaturalBits (source.map OAI.EditApproximation.integerSymbolCode) + OAI.EditApproximation.storedNaturalBits (target.map OAI.EditApproximation.integerSymbolCode) +
    OAI.EditApproximation.integerOccurrenceStorage source target

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

def binaryIndexedLeafWithWork (table : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let result := OAI.EditApproximation.indexedLeafWithWork table symbolBits positionBits symbol lo hi
  (OAI.EditApproximation.BinaryFraction.nat result.1, result.2 + Nat.size result.1 + 2)

def binaryIndexedLeafAllocation (table : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) : ℕ :=
  OAI.EditApproximation.indexedLeafAllocation symbolBits positionBits symbol lo hi +
    Nat.size (OAI.EditApproximation.indexedLeafWithWork table symbolBits positionBits symbol lo hi).1 + 2

def queryIndexedSliceWithWork (source : List ℕ) (interval : OAI.EditApproximation.TargetInterval source.length)
    (targetLength : ℕ) (q : OAI.EditApproximation.TargetInterval targetLength)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ) : OAI.EditApproximation.BinaryFraction × ℕ :=
  let symbol := OAI.EditApproximation.querySliceHeadWithWork source interval
  let result := OAI.EditApproximation.binaryIndexedLeafWithWork occurrence symbolBits positionBits symbol.1 q.lo q.hi
  (result.1, symbol.2 + result.2 + 1)

def queryIndexedSliceAllocation (source : List ℕ) (interval : OAI.EditApproximation.TargetInterval source.length)
    (targetLength : ℕ) (q : OAI.EditApproximation.TargetInterval targetLength)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ) : ℕ :=
  interval.lo.bits.length + interval.hi.bits.length + 1 +
    OAI.EditApproximation.binaryIndexedLeafAllocation occurrence symbolBits positionBits (OAI.EditApproximation.querySliceHeadWithWork source interval).1 q.lo q.hi

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

variable {n : ℕ} (read : TargetInterval n → List Bool × ℕ) (allocation : TargetInterval n → ℕ)

def initialGridReadAllocation (P : ℕ) (A : OAI.EditApproximation.BinaryFraction) (radius : ℕ) (q : OAI.EditApproximation.TargetInterval n) (b : ℕ) : ℕ :=
  let spacing := (OAI.EditApproximation.seedGridSpacingWithWork b P).1
  let points := (OAI.EditApproximation.gridStateBoxWithWork n (OAI.EditApproximation.bitWordValue spacing) radius q.lo q.hi).1
  OAI.EditApproximation.seedGridSpacingAllocation b P + OAI.EditApproximation.gridStateBoxAllocation n (OAI.EditApproximation.bitWordValue spacing) radius q.lo q.hi +
    OAI.EditApproximation.filterAllocation (fun r => ((OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork b (OAI.EditApproximation.bitWordValue (read r).1) A).1,
      (OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork b (OAI.EditApproximation.bitWordValue (read r).1) A).2 + (read r).2))
      (fun r => OAI.EditApproximation.BinaryFraction.initialCenterGuardAllocation b (OAI.EditApproximation.bitWordValue (read r).1) A + allocation r) points

def initialConeReadAllocation (sourceLength : ℕ) (a L : OAI.EditApproximation.BinaryFraction) (query center : OAI.EditApproximation.TargetInterval n) : ℕ :=
  allocation center + OAI.EditApproximation.BinaryFraction.initialConeAllocation sourceLength (OAI.EditApproximation.bitWordValue (read center).1) a L query center

def initialCentersReadAllocation (N P : ℕ) (A : OAI.EditApproximation.BinaryFraction) (q : OAI.EditApproximation.TargetInterval n) : ℕ :=
  let Uq := OAI.EditApproximation.bitWordValue (read q).1
  let scales := (OAI.EditApproximation.dyadicScalesWithWork N).1
  let active := (OAI.EditApproximation.filterWithWork (fun b => OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork Uq b A) scales).1
  allocation q + OAI.EditApproximation.dyadicScalesAllocation N +
    OAI.EditApproximation.filterAllocation (fun b => OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork Uq b A) (fun b => OAI.EditApproximation.BinaryFraction.initialScaleGuardAllocation Uq b A) scales +
    OAI.EditApproximation.arithmeticFlatMapAllocation (OAI.EditApproximation.BinaryFraction.initialGridReadWithWork P A read Uq q)
      (OAI.EditApproximation.BinaryFraction.initialGridReadAllocation read allocation P A Uq q) active

def initialMinimumReadAllocation (sourceLength N F : ℕ) (a : OAI.EditApproximation.BinaryFraction)
    (query : OAI.EditApproximation.TargetInterval n) (centers : List (OAI.EditApproximation.TargetInterval n)) : ℕ :=
  let Uq := OAI.EditApproximation.bitWordValue (read query).1
  allocation query + OAI.EditApproximation.naturalEqualAllocation Uq 0 +
    if (OAI.EditApproximation.naturalEqualWithWork Uq 0).1 then 0 else
      let L := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork (OAI.EditApproximation.BinaryFraction.nat 32) (OAI.EditApproximation.BinaryFraction.nat F)).1
      let coefficient := (OAI.EditApproximation.BinaryFraction.canonicalAddWithWork L OAI.EditApproximation.BinaryFraction.one).1
      let fallback := (OAI.EditApproximation.BinaryFraction.canonicalMulWithWork coefficient (OAI.EditApproximation.BinaryFraction.nat N)).1
      let scores := (OAI.EditApproximation.arithmeticMapWithWork (OAI.EditApproximation.BinaryFraction.initialConeReadWithWork sourceLength read a L query) centers).1
      OAI.EditApproximation.BinaryFraction.canonicalMulAllocation (OAI.EditApproximation.BinaryFraction.nat 32) (OAI.EditApproximation.BinaryFraction.nat F) + OAI.EditApproximation.BinaryFraction.canonicalAddAllocation L OAI.EditApproximation.BinaryFraction.one +
        OAI.EditApproximation.BinaryFraction.canonicalMulAllocation coefficient (OAI.EditApproximation.BinaryFraction.nat N) +
        OAI.EditApproximation.arithmeticMapAllocation (OAI.EditApproximation.BinaryFraction.initialConeReadAllocation read allocation sourceLength a L query) centers +
        OAI.EditApproximation.BinaryFraction.minimumAllocation fallback scores + Nat.size F + Nat.size N

def initialProgramReadAllocation (sourceLength N P F : ℕ) (A a : OAI.EditApproximation.BinaryFraction) (query : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.BinaryFraction.initialCentersReadAllocation read allocation N P A query + OAI.EditApproximation.BinaryFraction.initialMinimumReadAllocation read allocation sourceLength N F a
    query (OAI.EditApproximation.BinaryFraction.initialCentersReadWithWork N P A read query).1

def cachedInitialProgramReadAllocation (sourceLength N P F : ℕ) (A a : OAI.EditApproximation.BinaryFraction) (query : OAI.EditApproximation.TargetInterval n) : ℕ :=
  OAI.EditApproximation.BinaryFraction.finishCachedAllocation (OAI.EditApproximation.BinaryFraction.initialProgramReadWithWork sourceLength N P F A a read query)
    (OAI.EditApproximation.BinaryFraction.initialProgramReadAllocation read allocation sourceLength N P F A a query) [true] (by decide) 0

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.BinaryFraction

open BinaryFraction

def onlineParametersAllocation (word : List Bool) : ℕ :=
  OAI.EditApproximation.bitPowerAllocation word 5 + OAI.EditApproximation.bitPowerAllocation word 4 + 2

def refinementDecrementAllocation (word : List Bool) : ℕ := OAI.EditApproximation.bitPowerAllocation word 10 + 1

end OAI.EditApproximation.BinaryFraction

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BinaryFraction

def scheduledRefinementAllocation (N pass : ℕ) : ℕ :=
  if pass < OAI.EditApproximation.computedSeedPassCount N then
    OAI.EditApproximation.BinaryFraction.signedPowerTwoAllocation ((OAI.EditApproximation.dyadicSeedExponent (OAI.EditApproximation.smallLogExponent N)
      (OAI.EditApproximation.computedSeedInitialExponent N) pass - OAI.EditApproximation.smallLogExponent N : ℕ) : ℤ) + 2
  else 2

def refinementBaseAllocation (word : List Bool) : ℕ :=
  let power := OAI.EditApproximation.bitPowerWithWork word 10
  let increment := OAI.EditApproximation.bitAddWithWork power.1 [true] false
  OAI.EditApproximation.bitPowerAllocation word 10 + OAI.EditApproximation.bitAddAllocation power.1 [true] false +
    OAI.EditApproximation.trimBitWordAllocation increment.1 + 2

def refinementParameterAllocation (N pass : ℕ) (word : List Bool) : ℕ :=
  OAI.EditApproximation.BinaryFraction.onlineParametersAllocation word + OAI.EditApproximation.scheduledRefinementAllocation N pass +
    OAI.EditApproximation.BinaryFraction.refinementDecrementAllocation word + 5

def computedQueryPassAllocation (N pass : ℕ) : ℕ :=
  OAI.EditApproximation.BinaryFraction.signedPowerTwoAllocation ((OAI.EditApproximation.dyadicSeedExponent (OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.computedSeedInitialExponent N) pass : ℕ) : ℤ) +
    OAI.EditApproximation.refinementParameterAllocation N pass (OAI.EditApproximation.inputSmallLog N).bits + 2

def computedQuerySetupAllocation (N : ℕ) : ℕ :=
  OAI.EditApproximation.vectorMapAllocation (OAI.EditApproximation.computedSeedPassCount N + 1) (fun i => OAI.EditApproximation.computedQueryPassAllocation N i.val) +
    OAI.EditApproximation.refinementBaseAllocation (OAI.EditApproximation.inputSmallLog N).bits + 5

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation.UnreducedRational

open Finset

def nat (n : ℕ) : OAI.EditApproximation.UnreducedRational := ⟨n, 1, by decide⟩

end OAI.EditApproximation.UnreducedRational

end


