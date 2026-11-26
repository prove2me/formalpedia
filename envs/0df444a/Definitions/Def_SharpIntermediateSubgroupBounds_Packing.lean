-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_Packing
-- name    : SharpIntermediateSubgroupBounds_Packing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:43:34.54488+00:00
-- url     : https://prove2.me/theorems/f0c3ae2c-ea67-4c9d-b294-167d47e3f04d
-- title:
--   Packing
-- statement:
--   Definitions and structural lemmas for Packing, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Packing.lean

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons


set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
local instance packingSubgroupDecidableEq : DecidableEq (Subgroup G) := Classical.decEq _
local instance subgroupFinite : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective
def interval (H : Subgroup G) : Type u :=
  {K : Subgroup G // H ≤ K}
def band (H : Subgroup G) (q r : ℕ) : Type u :=
  {K : Subgroup G // H ≤ K ∧ q ^ r ≤ H.relIndex K ∧
    H.relIndex K < q ^ (r + 1)}
def layer (H : Subgroup G) (m : ℕ) : Type u :=
  {K : Subgroup G // H ≤ K ∧ H.relIndex K = m}
instance intervalFintype (H : Subgroup G) : Fintype (interval H) := by
  letI : Finite (interval H) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _
instance bandFintype (H : Subgroup G) (q r : ℕ) : Fintype (band H q r) := by
  letI : Finite (band H q r) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _
instance layerFintype (H : Subgroup G) (m : ℕ) : Fintype (layer H m) := by
  letI : Finite (layer H m) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _
instance rawRelGenFintype (H K : Subgroup G) (r : ℕ) :
    Fintype (RawRelGen H K r) := by
  letI : Finite (RawRelGen H K r) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _
def packedRawMap (H : Subgroup G) (q r : ℕ) :
    (Σ K : band H q r, RawRelGen H K.1 r) → (Fin r → G) :=
  fun z => z.2.1
def intervalToBandSigma (H : Subgroup G) (q : ℕ) (hn : 1 < H.index)
    (hq : 1 < q) :
    interval H → Σ r : Fin (Nat.log q H.index + 1), band H q r.1 :=
  fun K => by
    let m := H.relIndex K.1
    have hm0 : m ≠ 0 := by
      letI : H.IsFiniteRelIndex K.1 := H.isFiniteRelIndex_of_finiteIndex
      exact Subgroup.relIndex_ne_zero
    have hmn : m ≤ H.index :=
      Nat.le_of_dvd (by omega) (H.relIndex_dvd_index_of_le K.2)
    have hrle : Nat.log q m ≤ Nat.log q H.index := Nat.log_mono_right hmn
    let r : Fin (Nat.log q H.index + 1) :=
      ⟨Nat.log q m, Nat.lt_succ_of_le hrle⟩
    exact ⟨r, ⟨K.1, K.2, Nat.pow_log_le_self q hm0,
      Nat.lt_pow_succ_log_self hq m⟩⟩
def bandSigmaToInterval (H : Subgroup G) (q : ℕ) :
    (Σ r : Fin (Nat.log q H.index + 1), band H q r.1) → interval H :=
  fun z => ⟨z.2.1, z.2.2.1⟩
@[simp]
theorem bandSigmaToInterval_intervalToBandSigma (H : Subgroup G) (q : ℕ)
    (hn : 1 < H.index) (hq : 1 < q) (K : interval H) :
    bandSigmaToInterval H q (intervalToBandSigma H q hn hq K) = K := by
  apply Subtype.ext
  rfl
def finiteUQ (n q : ℕ) : ℚ :=
  ∑ r : Fin (Nat.log q n + 1),
    (n : ℚ) ^ (r : ℕ) /
      (gammaQ q (r : ℕ) * (q : ℚ) ^ ((r : ℕ) * (r : ℕ)))
def packedLayerRawMap (H : Subgroup G) (m r : ℕ) :
    (Σ K : layer H m, RawRelGen H K.1 r) → (Fin r → G) :=
  fun z => z.2.1
def rawHTranslate {H K : Subgroup G} {r : ℕ} (hHK : H ≤ K)
    (x : RawRelGen H K r) : (Fin r → H) → RawRelGen H K r :=
  fun h => ⟨fun i => x.1 i * (h i : G),
    fun i => K.mul_mem (x.2.1 i) (hHK (h i).2), by
      rw [generatedFrom_mul_right H x.1 h, x.2.2]⟩
theorem escapePath_nonempty (K : Subgroup G) (r : ℕ) (s : EscapeState K) :
    Nonempty (EscapePath K r s) := by
  induction r generalizing s with
  | zero => exact ⟨PUnit.unit⟩
  | succ r ih =>
      obtain ⟨x⟩ := escapeChoiceNonempty K s
      obtain ⟨z⟩ := ih (escapeNext K s x)
      exact ⟨escapeCons K x z⟩
def elementaryRawTuple (H : Subgroup G) (hn : 1 < H.index)
    (K : interval H) :
    RawRelGen H K.1 (Nat.log 2 H.index) := by
  let r := Nat.log 2 H.index
  let z : EscapePath K.1 r ⟨H, K.2⟩ :=
    Classical.choice (escapePath_nonempty K.1 r ⟨H, K.2⟩)
  have hmle : H.relIndex K.1 ≤ H.index :=
    Nat.le_of_dvd (by omega) (H.relIndex_dvd_index_of_le K.2)
  have hnlt : H.index < 2 ^ (r + 1) := by
    exact Nat.lt_pow_succ_log_self (by omega) H.index
  have hp2 : 2 ≤ H.index.minFac :=
    (Nat.minFac_prime (by omega : H.index ≠ 1)).two_le
  have hupper : H.relIndex K.1 < H.index.minFac ^ (r + 1) :=
    (hmle.trans_lt hnlt).trans_le (pow_le_pow_left' hp2 _)
  exact ⟨escapeTuple K.1 z, escapeTuple_mem K.1 z, by
    rw [← escapeEnd_eq_generatedFrom K.1 K.2 z]
    exact escapeEnd_eq_target K.2 hupper z⟩
def packedIntervalRawMap (H : Subgroup G) (r : ℕ) :
    (Σ K : interval H, RawRelGen H K.1 r) → (Fin r → G) :=
  fun z => z.2.1
def strictIntermediate (H : Subgroup G) : Type u :=
  {K : Subgroup G // H < K ∧ K < ⊤}
instance strictIntermediateFintype (H : Subgroup G) :
    Fintype (strictIntermediate H) := by
  letI : Finite (strictIntermediate H) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _
def intervalStrictEncode (H : Subgroup G) (K : interval H) :
    strictIntermediate H ⊕ Bool :=
  if hKH : K.1 = H then Sum.inr false
  else if hKG : K.1 = ⊤ then Sum.inr true
  else Sum.inl ⟨K.1, lt_of_le_of_ne K.2 (Ne.symm hKH),
    lt_of_le_of_ne le_top hKG⟩
def intervalStrictDecode (H : Subgroup G) :
    strictIntermediate H ⊕ Bool → interval H
  | Sum.inl K => ⟨K.1, K.2.1.le⟩
  | Sum.inr false => ⟨H, le_rfl⟩
  | Sum.inr true => ⟨⊤, le_top⟩
theorem intervalStrictDecode_encode (H : Subgroup G) (K : interval H) :
    intervalStrictDecode H (intervalStrictEncode H K) = K := by
  by_cases hKH : K.1 = H
  · rw [intervalStrictEncode, dif_pos hKH]
    change (⟨H, le_rfl⟩ : interval H) = K
    exact Subtype.ext hKH.symm
  · by_cases hKG : K.1 = ⊤
    · rw [intervalStrictEncode, dif_neg hKH, dif_pos hKG]
      change (⟨⊤, le_top⟩ : interval H) = K
      exact Subtype.ext hKG.symm
    · rw [intervalStrictEncode, dif_neg hKH, dif_neg hKG]
      rfl
theorem intervalStrictEncode_decode (H : Subgroup G) (hHt : H < ⊤)
    (z : strictIntermediate H ⊕ Bool) :
    intervalStrictEncode H (intervalStrictDecode H z) = z := by
  cases z with
  | inl K =>
      have hKH : K.1 ≠ H := K.2.1.ne'
      have hKG : K.1 ≠ ⊤ := K.2.2.ne
      change (if hKH' : K.1 = H then Sum.inr false
        else if hKG' : K.1 = ⊤ then Sum.inr true
        else Sum.inl ⟨K.1, lt_of_le_of_ne K.2.1.le (Ne.symm hKH'),
          lt_of_le_of_ne le_top hKG'⟩) = Sum.inl K
      rw [dif_neg hKH, dif_neg hKG]
      congr
  | inr b =>
      cases b
      · simp [intervalStrictEncode, intervalStrictDecode]
      · simp [intervalStrictEncode, intervalStrictDecode, hHt.ne.symm]
def intervalStrictEquiv (H : Subgroup G) (hHt : H < ⊤) :
    interval H ≃ strictIntermediate H ⊕ Bool where
  toFun := intervalStrictEncode H
  invFun := intervalStrictDecode H
  left_inv := intervalStrictDecode_encode H
  right_inv := intervalStrictEncode_decode H hHt
end
end SharpIntermediateSubgroupBounds


