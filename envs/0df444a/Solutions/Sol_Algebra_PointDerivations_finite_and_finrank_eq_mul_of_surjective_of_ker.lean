-- Prove2me | solution 1 for Algebra.PointDerivations.finite_and_finrank_eq_mul_of_surjective_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6fea6c28-acf0-5356-87ca-39cb4c1a05bc

import Mathlib
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_PointDerivations_finite_and_finrank_eq_mul_of_surjective_of_ker

set_option autoImplicit false

universe u v w w'

open Algebra

theorem solution
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] (ev : A →+* k)
    (hev : ev.comp (algebraMap k A) = RingHom.id k)
    (Ω : Type w) [AddCommGroup Ω] [Module k Ω] [Module.Finite k Ω]
    (π : ↥((RingHom.ker ev).restrictScalars k) →ₗ[k] Ω) (hπ : Function.Surjective π)
    (hπker : ∀ x : ↥((RingHom.ker ev).restrictScalars k), π x = 0 ↔ (x : A) ∈ (RingHom.ker ev) ^ 2)
    (M : Type w') [AddCommGroup M] [Module k M] [Module.Finite k M] :
    Module.Finite k ↥(Algebra.PointDerivations k A ev M) ∧
      Module.finrank k ↥(Algebra.PointDerivations k A ev M) = Module.finrank k Ω * Module.finrank k M := by
  have hevc : ∀ c : k, ev (algebraMap k A c) = c := fun c => RingHom.congr_fun hev c

  let evₗ : A →ₗ[k] k :=
    { toFun := ev, map_add' := ev.map_add, map_smul' := fun c a => by
        rw [PointDerivations.ev_smul hev, RingHom.id_apply, smul_eq_mul] }
  let ρ' : A →ₗ[k] A := LinearMap.id - (Algebra.linearMap k A).comp evₗ
  have hρ' : ∀ a : A, ρ' a ∈ (RingHom.ker ev).restrictScalars k := fun a => by
    show a - algebraMap k A (ev a) ∈ RingHom.ker ev
    rw [RingHom.mem_ker, map_sub, hevc, sub_self]
  let ρ : A →ₗ[k] ↥((RingHom.ker ev).restrictScalars k) := ρ'.codRestrict _ hρ'
  have hρ : ∀ a : A, (ρ a : A) = a - algebraMap k A (ev a) := fun a => rfl
  have hρmem : ∀ m : ↥((RingHom.ker ev).restrictScalars k), ρ (m : A) = m := fun m => by
    apply Subtype.ext
    have hm : ev (m : A) = 0 := m.2
    rw [hρ, hm, map_zero, sub_zero]

  have hD2 : ∀ (D : ↥(PointDerivations k A ev M)) (y : A), y ∈ RingHom.ker ev ^ 2 → (D : A →ₗ[k] M) y = 0 := by
    intro D y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy (fun m hm n hn => ?_) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
    rw [D.2 m n, show ev m = 0 from hm, show ev n = 0 from hn, zero_smul, zero_smul, add_zero]

  have hkey : ∀ a b : A, π (ρ (a * b)) = ev a • π (ρ b) + ev b • π (ρ a) := by
    intro a b
    have hX : ((ρ (a * b) - ev a • ρ b - ev b • ρ a : ↥((RingHom.ker ev).restrictScalars k)) : A) ∈ RingHom.ker ev ^ 2 := by
      have hcalc : ((ρ (a * b) - ev a • ρ b - ev b • ρ a : ↥((RingHom.ker ev).restrictScalars k)) : A) = (ρ a : A) * (ρ b : A) := by
        simp only [Submodule.coe_sub, Submodule.coe_smul, hρ, Algebra.smul_def, map_mul]
        ring
      rw [hcalc, pow_two]
      exact Ideal.mul_mem_mul (ρ a).2 (ρ b).2
    have h0 := (hπker _).mpr hX
    rw [map_sub, map_sub, map_smul, map_smul] at h0
    rw [← sub_eq_zero, ← h0]
    abel

  let Ψ : (Ω →ₗ[k] M) →ₗ[k] ↥(PointDerivations k A ev M) :=
    { toFun := fun φ => ⟨φ ∘ₗ π ∘ₗ ρ, fun a b => by
        simp only [LinearMap.comp_apply]
        rw [hkey, map_add, map_smul, map_smul]⟩
      map_add' := fun φ φ' => by apply Subtype.ext; ext a; rfl
      map_smul' := fun c φ => by apply Subtype.ext; ext a; rfl }
  have hΨ : ∀ (φ : Ω →ₗ[k] M) (a : A), (Ψ φ : A →ₗ[k] M) a = φ (π (ρ a)) := fun φ a => rfl
  have hinj : Function.Injective Ψ := by
    intro φ φ' hφ
    ext ω
    obtain ⟨m, rfl⟩ := hπ ω
    have : (Ψ φ : A →ₗ[k] M) (m : A) = (Ψ φ' : A →ₗ[k] M) (m : A) := by rw [hφ]
    rw [hΨ, hΨ, hρmem] at this
    exact this
  have hsurj : Function.Surjective Ψ := by
    intro D
    obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective π (LinearMap.range_eq_top.mpr hπ)
    refine ⟨(D : A →ₗ[k] M) ∘ₗ ((RingHom.ker ev).restrictScalars k).subtype ∘ₗ σ, ?_⟩
    apply Subtype.ext
    ext a
    rw [hΨ]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have h1 : (D : A →ₗ[k] M) ((σ (π (ρ a)) - ρ a : ↥((RingHom.ker ev).restrictScalars k)) : A) = 0 := by
      refine hD2 D _ ((hπker _).mp ?_)
      have hc := LinearMap.congr_fun hσ (π (ρ a))
      rw [LinearMap.comp_apply, LinearMap.id_apply] at hc
      rw [map_sub, hc, sub_self]
    rw [Submodule.coe_sub, map_sub, sub_eq_zero] at h1
    rw [h1, hρ, map_sub, PointDerivations.apply_algebraMap D.2, sub_zero]
  let e : (Ω →ₗ[k] M) ≃ₗ[k] ↥(PointDerivations k A ev M) := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_linearMap]

end S_Algebra_PointDerivations_finite_and_finrank_eq_mul_of_surjective_of_ker
end P2MW
export P2MW.S_Algebra_PointDerivations_finite_and_finrank_eq_mul_of_surjective_of_ker (solution)
