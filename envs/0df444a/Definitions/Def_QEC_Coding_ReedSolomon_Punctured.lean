-- Prove2me | Definitions.Def_QEC_Coding_ReedSolomon_Punctured
-- name    : QEC_Coding_ReedSolomon_Punctured
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:13:33.24759+00:00
-- url     : https://prove2.me/theorems/3e98f945-bc26-48f8-a691-950aff220b0a
-- title:
--   Punctured
-- statement:
--   Definitions and structural lemmas for Punctured, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ReedSolomon/Punctured.lean

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Coding
namespace KT19ReedSolomon
open scoped BigOperators
local instance instNeZeroOfPrime (p : Nat) [Fact p.Prime] : NeZero p :=
  ⟨(Fact.out : Nat.Prime p).ne_zero⟩
def selectedPunctureLocations (p k : Nat) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.filter fun point => point.val < k
def keptPunctureLocations (p k : Nat) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ \ selectedPunctureLocations p k
abbrev SelectedPunctureLocation (p k : Nat) [Fact p.Prime] :=
  ↥(selectedPunctureLocations p k)
abbrev KeptPunctureLocation (p k : Nat) [Fact p.Prime] :=
  ↥(keptPunctureLocations p k)
noncomputable def selectedPunctureEquivFin (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) : SelectedPunctureLocation p k ≃ Fin k := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine
    { toFun := fun point => ⟨point.1.val, by
        exact (Finset.mem_filter.mp point.2).2⟩
      invFun := fun index => ⟨(index.1 : ZMod p), by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (index.2.trans_le hkp)]
        exact index.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro point
    apply Subtype.ext
    exact ZMod.natCast_zmod_val point.1
  · intro index
    apply Fin.ext
    change ((index.1 : ZMod p).val) = index.1
    exact ZMod.val_natCast_of_lt (index.2.trans_le hkp)
theorem selectedPunctureLocations_card (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    (selectedPunctureLocations p k).card = k := by
  have hcard := Fintype.card_congr (selectedPunctureEquivFin p k hkp)
  simpa using hcard
theorem keptPunctureLocations_card (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    (keptPunctureLocations p k).card = p - k := by
  rw [keptPunctureLocations, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, ZMod.card, selectedPunctureLocations_card p k hkp]
def restrictSelected (p k : Nat) [Fact p.Prime] :
    Word (ZMod p) (ZMod p) →ₗ[ZMod p]
      Word (ZMod p) (SelectedPunctureLocation p k) where
  toFun word point := word point.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def restrictKept (p k : Nat) [Fact p.Prime] :
    Word (ZMod p) (ZMod p) →ₗ[ZMod p]
      Word (ZMod p) (KeptPunctureLocation p k) where
  toFun word point := word point.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp]
theorem restrictSelected_apply {p k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (ZMod p)) (point : SelectedPunctureLocation p k) :
    restrictSelected p k word point = word point.1 :=
  rfl
@[simp]
theorem restrictKept_apply {p k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (ZMod p)) (point : KeptPunctureLocation p k) :
    restrictKept p k word point = word point.1 :=
  rfl
def zeroExtendKept (p k : Nat) [Fact p.Prime] :
    Word (ZMod p) (KeptPunctureLocation p k) →ₗ[ZMod p]
      Word (ZMod p) (ZMod p) where
  toFun word point :=
    if hpoint : point ∈ keptPunctureLocations p k then word ⟨point, hpoint⟩ else 0
  map_add' left right := by
    funext point
    by_cases hpoint : point ∈ keptPunctureLocations p k <;> simp [hpoint]
  map_smul' scalar word := by
    funext point
    by_cases hpoint : point ∈ keptPunctureLocations p k <;> simp [hpoint]
@[simp]
theorem restrictKept_zeroExtendKept {p k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (KeptPunctureLocation p k)) :
    restrictKept p k (zeroExtendKept p k word) = word := by
  ext point
  simp [zeroExtendKept, point.2]
@[simp]
theorem restrictSelected_zeroExtendKept {p k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (KeptPunctureLocation p k)) :
    restrictSelected p k (zeroExtendKept p k word) = 0 := by
  ext point
  simp [zeroExtendKept, keptPunctureLocations, point.2]
def puncturedReedSolomonCode (p l k : Nat) [Fact p.Prime] :
    LinearCode (ZMod p) (KeptPunctureLocation p k) where
  carrier := (reedSolomonCode p l).carrier.map (restrictKept p k)
@[simp]
theorem mem_puncturedReedSolomonCode {p l k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (KeptPunctureLocation p k)) :
    word ∈ (puncturedReedSolomonCode p l k).carrier ↔
      ∃ full : Word (ZMod p) (ZMod p),
        full ∈ (reedSolomonCode p l).carrier ∧ restrictKept p k full = word := by
  simp [puncturedReedSolomonCode]
def shortenedReedSolomonDomain (p l k : Nat) [Fact p.Prime] :
    Submodule (ZMod p) (Word (ZMod p) (ZMod p)) :=
  (reedSolomonCode p l).carrier ⊓ LinearMap.ker (restrictSelected p k)
def shortenedReedSolomonCode (p l k : Nat) [Fact p.Prime] :
    LinearCode (ZMod p) (KeptPunctureLocation p k) where
  carrier := (shortenedReedSolomonDomain p l k).map (restrictKept p k)
@[simp]
theorem mem_shortenedReedSolomonCode {p l k : Nat} [Fact p.Prime]
    (word : Word (ZMod p) (KeptPunctureLocation p k)) :
    word ∈ (shortenedReedSolomonCode p l k).carrier ↔
      ∃ full : Word (ZMod p) (ZMod p),
        full ∈ (reedSolomonCode p l).carrier ∧
          restrictSelected p k full = 0 ∧ restrictKept p k full = word := by
  simp [shortenedReedSolomonCode, shortenedReedSolomonDomain, and_assoc]
def degreeLTEmbed (p a b : Nat) (hab : a ≤ b) :
    Polynomial.degreeLT (ZMod p) a →ₗ[ZMod p] Polynomial.degreeLT (ZMod p) b :=
  Submodule.inclusion (Polynomial.degreeLT_mono (R := ZMod p) hab)
noncomputable def selectedInterpolation (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) (word : Word (ZMod p) (SelectedPunctureLocation p k)) :
    Polynomial.degreeLT (ZMod p) k := by
  let equivalence := Lagrange.funEquivDegreeLT
    (s := selectedPunctureLocations p k) (v := fun point : ZMod p => point)
    (by
      intro left hleft right hright heq
      exact heq)
  let raw := equivalence.symm word
  refine ⟨raw.1, ?_⟩
  simpa [selectedPunctureLocations_card p k hkp] using raw.2
def shortenedDomainEquivRestrictSelectedKernel {p l k : Nat} [Fact p.Prime] :
    shortenedReedSolomonDomain p l k ≃ₗ[ZMod p]
      LinearMap.ker ((restrictSelected p k).domRestrict (reedSolomonCode p l).carrier) where
  toFun word :=
    ⟨⟨word.1, word.property.1⟩, by
      change restrictSelected p k word.1 = 0
      exact word.property.2⟩
  invFun word :=
    ⟨word.1.1, ⟨word.1.property, by
      change restrictSelected p k word.1.1 = 0
      exact word.property⟩⟩
  left_inv word := Subtype.ext rfl
  right_inv word := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def MinimumDistanceAtLeast {F : Type} {ι : Type} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι] (code : LinearCode F ι) (d : Nat) : Prop :=
  ∀ word : Word F ι, word ∈ code.carrier → word ≠ 0 → d ≤ HammingWeight word
noncomputable def complementaryWitnessRoots
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) : Finset (ZMod p) :=
  Classical.choose (Finset.exists_subset_card_eq
    (s := keptPunctureLocations p k) (n := p - l - 1) (by
      rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
      rw [keptPunctureLocations_card p k (hkl.trans hlp)]
      omega))
theorem complementaryWitnessRoots_card
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    (complementaryWitnessRoots p l k h).card = p - l - 1 :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := keptPunctureLocations p k) (n := p - l - 1) (by
      rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
      rw [keptPunctureLocations_card p k (hkl.trans hlp)]
      omega))).2
noncomputable def complementaryWitnessPolynomial
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    Polynomial.degreeLT (ZMod p) (p - l) :=
  ⟨Lagrange.nodal (complementaryWitnessRoots p l k h) (fun point : ZMod p => point), by
    have hpTwo : 2 ≤ p := h.1.two_le
    have hk : 1 ≤ k := h.2.1
    have hkl : k ≤ l := h.2.2.1
    have hlp : l ≤ p := h.2.2.2.1
    have hproduct : 3 * l ≤ p + 1 := h.2.2.2.2
    have hcomplementPos : 0 < p - l := by omega
    rw [Polynomial.mem_degreeLT, Lagrange.degree_nodal,
      complementaryWitnessRoots_card p l k h]
    exact_mod_cast (by omega : p - l - 1 < p - l)⟩
noncomputable def kt19Length (p k : Nat) [Fact p.Prime] : Nat :=
  Length (ZMod p) (KeptPunctureLocation p k)
noncomputable def kt19LogicalDimension (p l k : Nat) [Fact p.Prime] : Nat :=
  kt19Length p k - Dimension (shortenedReedSolomonCode p l k) -
    Dimension (shortenedReedSolomonCode p (p - l) k)
def kt19SafeDistance (p l k : Nat) : Nat := l - k
end KT19ReedSolomon
end Coding
end QEC


