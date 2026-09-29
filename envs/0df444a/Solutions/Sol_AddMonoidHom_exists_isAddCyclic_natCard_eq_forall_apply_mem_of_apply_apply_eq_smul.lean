-- Prove2me | solution 1 for AddMonoidHom.exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/153916f1-2435-591b-b717-52d2fa4c613f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidHom_exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul

set_option autoImplicit false

theorem solution
    {G : Type*} [AddCommGroup G] {M : ℕ} (hM : M ≠ 0)
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ G (M : ℤ))
    (f : G →+ G) (u v : ℤ) (huv : (M : ℤ) ∣ u * v - 1)
    (hf : ∀ x : G, (M : ℤ) • x = 0 → f (f x) = u • f x) :
    ∃ C : AddSubgroup G, IsAddCyclic C ∧ Nat.card C = M ∧ ∀ x ∈ C, f x ∈ C := by
  haveI : NeZero M := ⟨hM⟩
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM

  set X : G := ((e (1, 0) : Submodule.torsionBy ℤ G (M : ℤ)) : G) with hX
  have hXM : (M : ℤ) • X = 0 := (Submodule.mem_torsionBy_iff _ _).mp (e (1, 0)).2
  have hXord : addOrderOf X = M := by
    have h1 : addOrderOf ((1, 0) : ZMod M × ZMod M) = M := by
      rw [Prod.addOrderOf_mk, ZMod.addOrderOf_one, addOrderOf_zero, Nat.lcm_one_right]
    have h2 : addOrderOf (e (1, 0)) = M := by rw [AddEquiv.addOrderOf_eq, h1]
    have h3 := addOrderOf_injective (Submodule.torsionBy ℤ G (M : ℤ)).toAddSubgroup.subtype
      Subtype.val_injective (e (1, 0))
    rw [h2] at h3
    rw [hX]
    exact h3

  have hMf : ∀ x : G, (M : ℤ) • x = 0 → (M : ℤ) • f x = 0 := fun x hx => by
    rw [← map_zsmul, hx, map_zero]
  obtain ⟨c, hc⟩ := huv
  have hunit : ∀ x : G, (M : ℤ) • x = 0 → (v * u) • x = x := fun x hx => by
    have : (v * u) • x = x + c • ((M : ℤ) • x) := by
      rw [smul_smul, mul_comm c, ← hc, show v * u = 1 + (u * v - 1) by ring, add_smul, one_smul]
    rw [this, hx, smul_zero, add_zero]

  set X₀ : G := v • (u • X - f X) with hX₀
  set X₁ : G := v • f X with hX₁
  have hsum : X₀ + X₁ = X := by
    rw [hX₀, hX₁, smul_sub, sub_add_cancel, smul_smul]
    exact hunit X hXM
  have hfX₁ : f X₁ = u • X₁ := by
    rw [hX₁, map_zsmul, hf X hXM, smul_comm]
  have hfX₀ : f X₀ = 0 := by
    rw [hX₀, map_zsmul, map_sub, map_zsmul, hf X hXM, sub_self, smul_zero]
  have hMX₁ : (M : ℤ) • X₁ = 0 := by rw [hX₁, smul_comm, hMf X hXM, smul_zero]
  have hMX₀ : (M : ℤ) • X₀ = 0 := by
    rw [hX₀, smul_comm, smul_sub, smul_comm, hXM, smul_zero, hMf X hXM, sub_zero, smul_zero]

  have hfin : ∀ y : G, (M : ℤ) • y = 0 → IsOfFinAddOrder y := fun y hy =>
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨M, hMpos, by rw [← natCast_zsmul, hy]⟩
  have hdvdM : ∀ y : G, (M : ℤ) • y = 0 → addOrderOf y ∣ M := fun y hy =>
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by rw [← natCast_zsmul, hy])
  set o₀ := addOrderOf X₀ with ho₀
  set o₁ := addOrderOf X₁ with ho₁
  have ho₀0 : o₀ ≠ 0 := ((hfin X₀ hMX₀).addOrderOf_pos).ne'
  have ho₁0 : o₁ ≠ 0 := ((hfin X₁ hMX₁).addOrderOf_pos).ne'
  have hlcm : Nat.lcm o₀ o₁ = M := by
    apply Nat.dvd_antisymm (Nat.lcm_dvd (hdvdM X₀ hMX₀) (hdvdM X₁ hMX₁))
    rw [← hXord, ← hsum]
    exact (AddCommute.all X₀ X₁).addOrderOf_add_dvd_lcm

  set a := Nat.factorizationLCMLeft o₀ o₁ with ha
  set b := Nat.factorizationLCMRight o₀ o₁ with hb
  have hab : a * b = M := by rw [ha, hb, Nat.factorizationLCMLeft_mul_factorizationLCMRight ho₀0 ho₁0, hlcm]
  have hcop : a.Coprime b := Nat.coprime_factorizationLCMLeft_factorizationLCMRight o₀ o₁
  have hao : a ∣ o₀ := Nat.factorizationLCMLeft_dvd_left o₀ o₁
  have hbo : b ∣ o₁ := Nat.factorizationLCMRight_dvd_right o₀ o₁
  set P₀ : G := (o₀ / a) • X₀ with hP₀
  set P₁ : G := (o₁ / b) • X₁ with hP₁
  have hP₀ord : addOrderOf P₀ = a := addOrderOf_nsmul_addOrderOf_sub ho₀0 hao
  have hP₁ord : addOrderOf P₁ = b := addOrderOf_nsmul_addOrderOf_sub ho₁0 hbo
  have hfP₀ : f P₀ = 0 := by rw [hP₀, map_nsmul, hfX₀, smul_zero]
  have hfP₁ : f P₁ = u • P₁ := by rw [hP₁, map_nsmul, hfX₁, smul_comm]
  set Z : G := P₀ + P₁ with hZ
  have hZord : addOrderOf Z = M := by
    rw [hZ, (AddCommute.all P₀ P₁).addOrderOf_add_eq_mul_addOrderOf_of_coprime
      (by rw [hP₀ord, hP₁ord]; exact hcop), hP₀ord, hP₁ord, hab]

  have hP₁mem : P₁ ∈ AddSubgroup.zmultiples Z := by
    obtain ⟨x, y, hxy⟩ := hcop.isCoprime
    have haP₀ : (a : ℤ) • P₀ = 0 := by rw [natCast_zsmul, ← hP₀ord, addOrderOf_nsmul_eq_zero]
    have hbP₁ : (b : ℤ) • P₁ = 0 := by rw [natCast_zsmul, ← hP₁ord, addOrderOf_nsmul_eq_zero]
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨x * a, ?_⟩
    rw [hZ, smul_add, mul_smul, haP₀, smul_zero, zero_add, show x * (a : ℤ) = 1 - y * b by rw [← hxy]; ring,
      sub_smul, one_smul, mul_smul, hbP₁, smul_zero, sub_zero]
  refine ⟨AddSubgroup.zmultiples Z, inferInstance, by rw [Nat.card_zmultiples, hZord], ?_⟩
  intro x hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  rw [map_zsmul, hZ, map_add, hfP₀, zero_add, hfP₁, smul_smul]
  exact AddSubgroup.zsmul_mem _ hP₁mem _

end S_AddMonoidHom_exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul
end P2MW
export P2MW.S_AddMonoidHom_exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul (solution)
