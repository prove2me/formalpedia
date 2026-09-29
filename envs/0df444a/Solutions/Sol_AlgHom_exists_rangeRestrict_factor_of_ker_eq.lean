-- Prove2me | solution 1 for AlgHom.exists_rangeRestrict_factor_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/771e851e-c985-5a08-8e2e-5c64165bc633

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_exists_rangeRestrict_factor_of_ker_eq

set_option autoImplicit false

theorem solution
    {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing K] [Algebra A K]
    (φ₁ φ₂ : B →ₐ[A] K) (h : RingHom.ker φ₁.toRingHom = RingHom.ker φ₂.toRingHom) :
    ∃ (ψ : B →ₐ[A] ↥φ₁.range) (κ₂ : ↥φ₁.range →ₐ[A] K),
      Function.Surjective ψ ∧ Function.Injective κ₂ ∧
      (∀ b : B, ((ψ b : ↥φ₁.range) : K) = φ₁ b) ∧ (∀ b : B, κ₂ (ψ b) = φ₂ b) := by
  classical
  have hsurj : Function.Surjective φ₁.rangeRestrict := φ₁.rangeRestrict_surjective
  have hker : ∀ b : B, b ∈ RingHom.ker φ₁.rangeRestrict.toRingHom ↔ φ₂ b = 0 := by
    intro b
    have h2 : b ∈ RingHom.ker φ₂.toRingHom ↔ φ₂ b = 0 := RingHom.mem_ker
    rw [← h2, ← h, RingHom.mem_ker, RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [← Subtype.coe_inj]
    simp
  let I := RingHom.ker φ₁.rangeRestrict.toRingHom
  let e : (B ⧸ I) ≃ₐ[A] ↥φ₁.range := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let lam : (B ⧸ I) →ₐ[A] K := Ideal.Quotient.liftₐ I φ₂ (fun b hb => (hker b).mp hb)
  refine ⟨φ₁.rangeRestrict, lam.comp (e.symm : ↥φ₁.range →ₐ[A] B ⧸ I), hsurj, ?_, fun b => rfl, ?_⟩
  ·
    have hlam : Function.Injective lam := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
      have : φ₂ b = 0 := by simpa [lam] using hz
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (hker b).mpr this
    exact hlam.comp e.symm.injective
  · intro b
    have he : e (Ideal.Quotient.mk I b) = φ₁.rangeRestrict b := by
      show Ideal.kerLiftAlg φ₁.rangeRestrict (Ideal.Quotient.mk _ b) = _
      exact Ideal.kerLiftAlg_mk _ _
    show lam (e.symm (φ₁.rangeRestrict b)) = φ₂ b
    rw [← he, AlgEquiv.symm_apply_apply]
    simp [lam]

end S_AlgHom_exists_rangeRestrict_factor_of_ker_eq
end P2MW
export P2MW.S_AlgHom_exists_rangeRestrict_factor_of_ker_eq (solution)
