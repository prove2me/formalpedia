-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:06:20.7205+00:00
-- url     : https://prove2.me/theorems/246ed2c9-f3b7-4e50-9108-a9619f297449
-- title:
--   Unramified
-- statement:
--   Definitions and structural lemmas for Unramified, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Unramified.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mem_map_relDeg_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_range_valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relDeg_pow
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relDeg_surjective
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relInertiaDegree_ne_zero
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_mem_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_proj_eq_zero_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_relIndex_eq_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk


set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
section Unramified
variable {G : Type*} [Group G] (d : G →* Multiplicative ℤ̂)
def IsUnramified (K L : Subgroup G) : Prop :=
  relRamificationIndex d K L = 1
variable {d}
theorem isUnramified_iff {K L : Subgroup G} : IsUnramified d K L ↔ K ⊓ d.ker ≤ L := by
  rw [IsUnramified, relRamificationIndex, Subgroup.relIndex_eq_one, inf_comm]
theorem relIndex_eq_relInertiaDegree {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L) :
    L.relIndex K = relInertiaDegree d K L := by
  rw [relIndex_eq_mul (d := d) hLK, (isUnramified_iff.2 hu : relRamificationIndex d K L = 1), one_mul]
theorem mem_iff_map_mem_of_unramified {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L)
    {σ : G} (hσ : σ ∈ K) : σ ∈ L ↔ d σ ∈ L.map d := by
  refine ⟨fun h => ⟨σ, h, rfl⟩, ?_⟩
  rintro ⟨τ, hτ, hτσ⟩
  have h : τ⁻¹ * σ ∈ L := hu (Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem (hLK hτ)) hσ,
    MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hτσ, inv_mul_cancel])⟩)
  simpa using L.mul_mem hτ h
theorem normal_of_unramified {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L) :
    (L.subgroupOf K).Normal := by
  have h : L.subgroupOf K = (L.map d).comap (d.comp K.subtype) := by
    ext σ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact mem_iff_map_mem_of_unramified hLK hu σ.2
  rw [h]
  exact Subgroup.Normal.comap inferInstance _
end Unramified
namespace ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)
section Frobenius
variable {K L : OpenSubgroup G}
theorem exists_pow_mul_mem_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) (τ : (K : Subgroup G)) :
    ∃ m : ℕ, ((φ ^ m)⁻¹ * τ : G) ∈ (L : Subgroup G) := by
  set n : ℕ+ := ⟨relInertiaDegree D.deg K L, Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)⟩
  set x : ℤ̂ := Multiplicative.toAdd (D.relDeg K τ)
  set m : ℕ := (proj n x).val
  have hx : x - (m : ℤ̂) ∈ multiples n := by
    rw [← proj_eq_zero_iff, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := mem_multiples.1 hx
  obtain ⟨ρ, hρ, hρw⟩ := (D.mem_map_relDeg_iff hLK).2 ⟨Multiplicative.ofAdd w, rfl⟩
  refine ⟨m, ?_⟩
  have hdeg : D.relDeg K (ρ⁻¹ * ((φ ^ m)⁻¹ * τ)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, hφ, hρw]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, toAdd_one]
    have hw' : relInertiaDegree D.deg K L • w = x - m := hw.symm
    rw [hw', nsmul_one]
    abel
  have hker : ((ρ⁻¹ * ((φ ^ m)⁻¹ * τ) : (K : Subgroup G)) : G) ∈ (K : Subgroup G) ⊓ D.deg.ker := by
    refine Subgroup.mem_inf.2 ⟨Subtype.coe_prop _, MonoidHom.mem_ker.2 ?_⟩
    rw [← relDeg_pow, hdeg, one_pow]
  have h := (L : Subgroup G).mul_mem (Subgroup.mem_subgroupOf.1 hρ) (hu hker)
  simpa using h
theorem zpowers_eq_top_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    [((L : Subgroup G).subgroupOf K).Normal]
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) :
    Subgroup.zpowers ((φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) = ⊤ := by
  refine eq_top_iff.2 fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H τ =>
    obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hLK hu hφ τ
    refine ⟨m, ?_⟩
    change ((φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) ^ (m : ℤ) = τ
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hm
theorem isCyclic_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K (Multiplicative.ofAdd 1)
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨_, D.zpowers_eq_top_of_unramified hLK hu hφ⟩
end Frobenius
section TateZero
variable {K L : OpenSubgroup G}
noncomputable def valuationMod (K : OpenSubgroup G) (n : ℕ+) :
    fixedModule A (K : Subgroup G) →* Multiplicative (ZMod n) :=
  (AddMonoidHom.toMultiplicative (proj n).toAddMonoidHom).comp (D.valuation K)
theorem valuationMod_apply (K : OpenSubgroup G) (n : ℕ+) (a : fixedModule A (K : Subgroup G)) :
    D.valuationMod K n a = Multiplicative.ofAdd (proj n (Multiplicative.toAdd (D.valuation K a))) :=
  rfl
theorem valuationMod_surjective (K : OpenSubgroup G) (n : ℕ+) :
    Function.Surjective (D.valuationMod K n) := by
  intro z
  have h : Multiplicative.ofAdd ((Multiplicative.toAdd z).val : ℤ̂) ∈ (D.valuation K).range := by
    rw [range_valuation]
    exact_mod_cast D.intCast_mem_range_val ((Multiplicative.toAdd z).val : ℤ)
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [valuationMod_apply, ha, toAdd_ofAdd, map_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd]
noncomputable def relInertiaDegreePNat (hLK : L ≤ K) : ℕ+ :=
  ⟨relInertiaDegree D.deg K L, Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)⟩
@[simp] theorem coe_relInertiaDegreePNat (hLK : L ≤ K) :
    (D.relInertiaDegreePNat hLK : ℕ) = relInertiaDegree D.deg K L :=
  rfl
theorem range_norm_le_ker_valuationMod (hLK : L ≤ K) :
    (norm A (K : Subgroup G) (L : Subgroup G)).range ≤
      (D.valuationMod K (D.relInertiaDegreePNat hLK)).ker := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker, valuationMod_apply, D.valuation_norm hLK, toAdd_pow, map_nsmul,
    nsmul_eq_mul]
  change Multiplicative.ofAdd (((D.relInertiaDegreePNat hLK : ℕ) : ZMod (D.relInertiaDegreePNat hLK)) *
    _) = 1
  rw [ZMod.natCast_self, zero_mul, ofAdd_zero]
noncomputable def tateZeroVal (hLK : L ≤ K) :
    tateZero A (K : Subgroup G) (L : Subgroup G) →*
      Multiplicative (ZMod (D.relInertiaDegreePNat hLK)) :=
  QuotientGroup.lift _ (D.valuationMod K (D.relInertiaDegreePNat hLK))
    (D.range_norm_le_ker_valuationMod hLK)
theorem tateZeroVal_surjective (hLK : L ≤ K) : Function.Surjective (D.tateZeroVal hLK) := by
  intro z
  obtain ⟨a, ha⟩ := D.valuationMod_surjective K (D.relInertiaDegreePNat hLK) z
  exact ⟨a, ha⟩
theorem tateZeroVal_bijective (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) : Function.Bijective (D.tateZeroVal hLK) := by
  have := normal_of_unramified (d := D.deg) hLK hu
  have hcyc := D.isCyclic_of_unramified hLK hu
  have hcard := (hax K L hLK hcyc).1
  rw [relIndex_eq_relInertiaDegree hLK hu] at hcard
  have : Finite (tateZero A (K : Subgroup G) (L : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact D.relInertiaDegree_ne_zero hLK)
  refine (D.tateZeroVal_surjective hLK).bijective_of_nat_card_le ?_
  rw [hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, coe_relInertiaDegreePNat]
noncomputable def tateZeroEquiv (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) :
    tateZero A (K : Subgroup G) (L : Subgroup G) ≃*
      Multiplicative (ZMod ((L : Subgroup G).relIndex K)) :=
  (MulEquiv.ofBijective _ (D.tateZeroVal_bijective hax hLK hu)).trans
    (AddEquiv.toMultiplicative
      (ZMod.ringEquivCongr (m := (D.relInertiaDegreePNat hLK : ℕ))
        (relIndex_eq_relInertiaDegree (d := D.deg) hLK hu).symm).toAddEquiv)
end TateZero
section Units
variable {K L : OpenSubgroup G}
end Units
end ClassFieldData
end GroundTheory.LocalField.Abstract


