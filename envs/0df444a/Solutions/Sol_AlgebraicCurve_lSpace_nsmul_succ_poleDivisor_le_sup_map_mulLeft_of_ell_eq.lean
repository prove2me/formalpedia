-- Prove2me | solution 1 for AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ce9e9415-84a1-5386-bd3a-d5f75ef487e0

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (M₀ d g₀ : ℕ)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀)
    (m : ℕ) (hm : M₀ + 1 ≤ m) :
    (LSpace ((m + 1) • D) : Submodule K F)
      ≤ LSpace (m • D) ⊔ (LSpace (m • D)).map (LinearMap.mulLeft K x) := by
  set φ : F →ₗ[K] F := LinearMap.mulLeft K x with hφdef

  rcases eq_or_ne x 0 with hx0 | hx0
  · intro g hg
    refine Submodule.mem_sup_left
      ((mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor x D hD m).2 g hg ?_)
    simp [hx0]

  have hφinj : Function.Injective φ := fun a b h =>
    mul_left_cancel₀ hx0 (by simpa [hφdef, LinearMap.mulLeft_apply] using h)

  obtain ⟨hsh1m, _⟩ := mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor x D hD m
  have hm1 : m - 1 + 1 = m := by omega
  obtain ⟨hsh1p, hsh2p⟩ := mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor x D hD (m - 1)
  rw [hm1] at hsh1p hsh2p

  have hD0 : 0 ≤ D := fun v => by simp [hD v]
  have hmono : ∀ {a b : ℕ}, a ≤ b → (LSpace (a • D) : Submodule K F) ≤ LSpace (b • D) := by
    intro a b hab
    refine lSpace_mono ?_
    intro v
    have : a • (D v) ≤ b • (D v) := nsmul_le_nsmul_left (hD0 v) hab
    simpa using this

  have hW_le : (LSpace (m • D) : Submodule K F) ⊔ (LSpace (m • D)).map φ ≤ LSpace ((m + 1) • D) :=
    sup_le (hmono m.le_succ)
      (Submodule.map_le_iff_le_comap.2 fun g hg => hsh1m g hg)

  haveI := hFD m; haveI := hFD (m + 1); haveI := hFD (m - 1)
  haveI : FiniteDimensional K ↥((LSpace (m • D) : Submodule K F).map φ) :=
    (Submodule.equivMapOfInjective φ hφinj _).symm.finiteDimensional

  have hinf : (LSpace (m • D) : Submodule K F) ⊓ (LSpace (m • D)).map φ
            = (LSpace ((m - 1) • D)).map φ := by
    apply le_antisymm
    · rintro z ⟨hzVm, g, hgVm, rfl⟩
      exact ⟨g, hsh2p g hgVm hzVm, rfl⟩
    · rintro z ⟨g, hgVp, rfl⟩
      exact ⟨hsh1p g hgVp, g, hmono (Nat.sub_le _ _) hgVp, rfl⟩

  have hfr_map : ∀ (V : Submodule K F), FiniteDimensional K ↥V →
      Module.finrank K ↥(V.map φ) = Module.finrank K ↥V := fun V _ =>
    (Submodule.equivMapOfInjective φ hφinj V).symm.finrank_eq

  have h1m : 1 ≤ m := by omega
  have hfr_m  : (Module.finrank K ↥(LSpace (m • D) : Submodule K F) : ℤ) = m * d + 1 - g₀ :=
    by have := hell m (by omega); exact_mod_cast this
  have hfr_m1 : (Module.finrank K ↥(LSpace ((m + 1) • D) : Submodule K F) : ℤ)
              = (m + 1) * d + 1 - g₀ :=
    by have := hell (m + 1) (by omega); exact_mod_cast this
  have hfr_p  : (Module.finrank K ↥(LSpace ((m - 1) • D) : Submodule K F) : ℤ)
              = (m - 1 : ℕ) * d + 1 - g₀ :=
    by have := hell (m - 1) (by omega); exact_mod_cast this
  have hsi := Submodule.finrank_sup_add_finrank_inf_eq
    (LSpace (m • D) : Submodule K F) ((LSpace (m • D)).map φ)
  rw [hinf] at hsi
  have hfr_W : (Module.finrank K ↥((LSpace (m • D) : Submodule K F) ⊔ (LSpace (m • D)).map φ) : ℤ)
             = Module.finrank K ↥(LSpace ((m + 1) • D) : Submodule K F) := by
    rw [hfr_map _ (hFD (m - 1)), hfr_map _ (hFD m)] at hsi
    have hsiZ : (Module.finrank K ↥((LSpace (m • D) : Submodule K F) ⊔ (LSpace (m • D)).map φ) : ℤ)
              + Module.finrank K ↥(LSpace ((m - 1) • D) : Submodule K F)
              = Module.finrank K ↥(LSpace (m • D) : Submodule K F)
              + Module.finrank K ↥(LSpace (m • D) : Submodule K F) := by
      exact_mod_cast hsi
    have hmnat : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
      have : ((m - 1 : ℕ) : ℤ) + 1 = (m : ℤ) := by exact_mod_cast hm1
      linarith
    have hpZ : ((m - 1 : ℕ) : ℤ) * d = (m : ℤ) * d - d := by
      rw [hmnat]; ring
    rw [hfr_m1]
    have h1 := hfr_m; have h2 := hfr_p
    rw [hpZ] at h2
    linarith [h1, h2, hsiZ]

  have heq := Submodule.eq_of_le_of_finrank_le hW_le (by exact_mod_cast hfr_W.ge)
  exact heq.ge

end S_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
end P2MW
export P2MW.S_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq (solution)
