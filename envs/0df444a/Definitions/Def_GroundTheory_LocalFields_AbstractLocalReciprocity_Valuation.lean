-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:10.242815+00:00
-- url     : https://prove2.me/theorems/187adb3c-397f-4c7d-8ca8-c314f087711d
-- title:
--   Valuation
-- statement:
--   Definitions and structural lemmas for Valuation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_eq_multiples_index
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_mem_multiples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
section Degrees
variable {G : Type*} [Group G]
variable (d : G →* Multiplicative ℤ̂)
noncomputable def relInertiaDegree (K L : Subgroup G) : ℕ :=
  (L.map d).relIndex (K.map d)
noncomputable def relRamificationIndex (K L : Subgroup G) : ℕ :=
  L.relIndex (d.ker ⊓ K)
variable {d}
end Degrees
section PowProfinite
namespace ProfiniteInteger
theorem pow_left_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun x : Multiplicative ℤ̂ => x ^ n) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  have h' : n • Multiplicative.toAdd x = n • Multiplicative.toAdd y := by
    rw [← toAdd_pow, ← toAdd_pow]
    exact congrArg Multiplicative.toAdd h
  exact nsmul_right_injective hn h'
theorem pow_left_inj {n : ℕ} (hn : n ≠ 0) {x y : Multiplicative ℤ̂} : x ^ n = y ^ n ↔ x = y :=
  (pow_left_injective hn).eq_iff
theorem mem_of_index_ne_zero {H : Subgroup (Multiplicative ℤ̂)} (hH : H.index ≠ 0)
    {x : Multiplicative ℤ̂} : x ∈ H ↔ ∃ y, y ^ H.index = x := by
  have hi : (Subgroup.toAddSubgroup' H).index = H.index := rfl
  have h := eq_multiples_index (H := Subgroup.toAddSubgroup' H) (by rwa [hi])
  rw [hi] at h
  have hx : x ∈ H ↔ Multiplicative.toAdd x ∈ Subgroup.toAddSubgroup' H := Iff.rfl
  rw [hx, h, mem_multiples]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Multiplicative.ofAdd y, Multiplicative.toAdd.injective ?_⟩
    rw [toAdd_pow, toAdd_ofAdd, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨Multiplicative.toAdd y, by rw [toAdd_pow]⟩
end ProfiniteInteger
end PowProfinite
namespace ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)
theorem inertiaDegree_ne_zero (K : OpenSubgroup G) : inertiaDegree D.deg K ≠ 0 :=
  fun h => Subgroup.FiniteIndex.index_ne_zero (H := (K : Subgroup G))
    (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_map_dvd _ D.surjective_deg))
theorem mem_map_deg_iff (K : OpenSubgroup G) {x : Multiplicative ℤ̂} :
    x ∈ (K : Subgroup G).map D.deg ↔ ∃ y, y ^ inertiaDegree D.deg K = x :=
  mem_of_index_ne_zero (D.inertiaDegree_ne_zero K)
theorem exists_pow_eq_deg (K : OpenSubgroup G) (σ : (K : Subgroup G)) :
    ∃ x, x ^ inertiaDegree D.deg K = D.deg σ :=
  (D.mem_map_deg_iff K).1 ⟨σ, σ.2, rfl⟩
noncomputable def relDeg (K : OpenSubgroup G) : (K : Subgroup G) →* Multiplicative ℤ̂ where
  toFun σ := (D.exists_pow_eq_deg K σ).choose
  map_one' := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_pow_eq_deg K 1).choose_spec, one_pow, OneMemClass.coe_one, map_one]
  map_mul' σ τ := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_pow_eq_deg K (σ * τ)).choose_spec, mul_pow, (D.exists_pow_eq_deg K σ).choose_spec,
      (D.exists_pow_eq_deg K τ).choose_spec, Subgroup.coe_mul, map_mul]
theorem exists_valuation (K : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) :
    ∃ z ∈ D.val.range, z ^ inertiaDegree D.deg K = D.val (norm A ⊤ (K : Subgroup G) a) := by
  have h : D.val (norm A ⊤ (K : Subgroup G) a) ∈ (D.val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range :=
    ⟨a, rfl⟩
  rw [D.range_val_comp_norm K] at h
  obtain ⟨z, hz, hza⟩ := h
  exact ⟨z, hz, hza⟩
noncomputable def valuation (K : OpenSubgroup G) : fixedModule A (K : Subgroup G) →* Multiplicative ℤ̂ where
  toFun a := (D.exists_valuation K a).choose
  map_one' := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_valuation K 1).choose_spec.2, one_pow, map_one, map_one]
  map_mul' a b := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_valuation K (a * b)).choose_spec.2, mul_pow, (D.exists_valuation K a).choose_spec.2,
      (D.exists_valuation K b).choose_spec.2, map_mul, map_mul]
noncomputable def units (K : OpenSubgroup G) : Subgroup (fixedModule A (K : Subgroup G)) :=
  (D.valuation K).ker
end ClassFieldData
end GroundTheory.LocalField.Abstract


