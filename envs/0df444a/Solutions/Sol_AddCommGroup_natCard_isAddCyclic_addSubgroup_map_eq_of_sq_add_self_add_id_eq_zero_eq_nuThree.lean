-- Prove2me | solution 1 for AddCommGroup.natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/bd4d0fff-00b0-52f9-86ac-7957cfc05baa

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree

set_option autoImplicit false
set_option maxHeartbeats 6400000

open ModularCurve

theorem l3x_transport {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    {M : Type*} [AddCommGroup M]
    (ι : M →+ A) (hι : Function.Injective ι) (hιr : ∀ a : A, n • a = 0 → ∃ m, ι m = a)
    (σ : A →+ A) (T : M →+ M) (hT : ∀ m, ι (T m) = σ (ι m)) :
    Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H}
      = Nat.card {H : AddSubgroup M // IsAddCyclic H ∧ Nat.card H = n ∧ H.map T = H} := by
  have hcomm : σ.comp ι = ι.comp T := AddMonoidHom.ext fun m => (hT m).symm

  have hΦ : ∀ L : AddSubgroup M, IsAddCyclic L ∧ Nat.card L = n ∧ L.map T = L →
      IsAddCyclic (L.map ι) ∧ Nat.card (L.map ι) = n ∧ (L.map ι).map σ = L.map ι := by
    rintro L ⟨hc, hcard, hst⟩
    haveI := hc
    refine ⟨isAddCyclic_of_surjective _ (L.equivMapOfInjective ι hι).surjective, ?_, ?_⟩
    · rw [← Nat.card_congr (L.equivMapOfInjective ι hι).toEquiv, hcard]
    · rw [AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map, hst]

  have hΨ : ∀ H : AddSubgroup A, IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H →
      (H.comap ι).map ι = H ∧
      (IsAddCyclic (H.comap ι) ∧ Nat.card (H.comap ι) = n ∧ (H.comap ι).map T = H.comap ι) := by
    rintro H ⟨hc, hcard, hst⟩
    have hle : H ≤ ι.range := by
      intro a ha
      have hdvd : addOrderOf a ∣ n := hcard ▸ H.addOrderOf_dvd_natCard ha
      obtain ⟨m, hm⟩ := hιr a (addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd)
      exact ⟨m, hm⟩
    have hmc : (H.comap ι).map ι = H := AddSubgroup.map_comap_eq_self hle
    haveI := hc
    refine ⟨hmc, ?_, ?_, ?_⟩
    · have e := (H.comap ι).equivMapOfInjective ι hι
      rw [hmc] at e
      exact isAddCyclic_of_surjective _ e.symm.surjective
    · have h := Nat.card_congr ((H.comap ι).equivMapOfInjective ι hι).toEquiv
      rw [hmc] at h
      rw [h, hcard]
    · apply AddSubgroup.map_injective hι
      rw [AddSubgroup.map_map, ← hcomm, ← AddSubgroup.map_map, hmc, hst]
  symm
  refine Nat.card_eq_of_bijective
    (fun L : {H : AddSubgroup M // IsAddCyclic H ∧ Nat.card H = n ∧ H.map T = H} =>
      (⟨L.1.map ι, hΦ L.1 L.2⟩ : {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H}))
    ⟨?_, ?_⟩
  · intro L₁ L₂ h
    exact Subtype.ext (AddSubgroup.map_injective hι (congrArg Subtype.val h))
  · intro H
    obtain ⟨hmc, hrest⟩ := hΨ H.1 H.2
    exact ⟨⟨H.1.comap ι, hrest⟩, Subtype.ext hmc⟩

theorem solution
    {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n)
    (σ : A →+ A) (hσ : ∀ a : A, σ (σ a) + σ a + a = 0)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H}
      = nuThree n := by

  have memV : ∀ a : A, a ∈ Submodule.torsionBy ℤ A n ↔ n • a = 0 := fun a => by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  have σV : ∀ a ∈ Submodule.torsionBy ℤ A n, σ a ∈ Submodule.torsionBy ℤ A n := fun a ha => by
    rw [memV] at ha ⊢; rw [← map_nsmul, ha, map_zero]

  let ι : ZMod n × ZMod n →+ A :=
    (Submodule.torsionBy ℤ A n).subtype.toAddMonoidHom.comp e.toAddMonoidHom
  have ι_apply : ∀ m, ι m = (e m : A) := fun m => rfl
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιr : ∀ a : A, n • a = 0 → ∃ m, ι m = a := fun a ha =>
    ⟨e.symm ⟨a, (memV a).mpr ha⟩, by rw [ι_apply, AddEquiv.apply_symm_apply]⟩

  let σr : Submodule.torsionBy ℤ A n →+ Submodule.torsionBy ℤ A n :=
    (σ.comp (Submodule.torsionBy ℤ A n).subtype.toAddMonoidHom).codRestrict
      (Submodule.torsionBy ℤ A n) (fun x => σV x.1 x.2)
  have σr_apply : ∀ x, ((σr x : Submodule.torsionBy ℤ A n) : A) = σ x := fun x => rfl
  let T : ZMod n × ZMod n →+ ZMod n × ZMod n := e.symm.toAddMonoidHom.comp (σr.comp e.toAddMonoidHom)
  have T_apply : ∀ m, T m = e.symm (σr (e m)) := fun m => rfl
  have hT : ∀ m, ι (T m) = σ (ι m) := fun m => by
    simp only [T_apply, ι_apply, AddEquiv.apply_symm_apply, σr_apply]
  have hT2 : ∀ m, T (T m) + T m + m = 0 := fun m =>
    hι (by rw [map_add, map_add, hT, hT, hσ, map_zero])

  have hnsT : ∀ p : ℕ, p.Prime → p ∣ n →
      ∃ v : ZMod n × ZMod n, addOrderOf v = p ∧ ∀ k : ℕ, T v ≠ k • v := by
    intro p hp hpn
    obtain ⟨a, ha, hane⟩ := hns p hp hpn
    obtain ⟨m, rfl⟩ := hιr a (by
      rw [← ha] at hpn
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hpn)
    refine ⟨m, by rwa [addOrderOf_injective ι hι] at ha, fun k hk => hane k ?_⟩
    rw [← hT, hk, map_nsmul]
  rw [l3x_transport n ι hι hιr σ T hT]
  exact ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree n T hT2 hnsT

end S_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree
end P2MW
export P2MW.S_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree (solution)
