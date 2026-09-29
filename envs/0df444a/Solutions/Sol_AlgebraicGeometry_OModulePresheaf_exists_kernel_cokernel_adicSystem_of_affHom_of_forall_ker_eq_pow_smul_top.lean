-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/32743978-e928-5caf-be03-fcc3a074f13e

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [LocallyOfFiniteType q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U) :
    ∃ (Ks : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (Ks (k + 1)) (Ks k))
      (j : ∀ k, OModulePresheaf.AffHom (Ks k) (F k))
      (Cs : ℕ → OModulePresheaf q) (γ : ∀ k, OModulePresheaf.AffHom (Cs (k + 1)) (Cs k))
      (θ : ∀ k, OModulePresheaf.AffHom (Ps k) (Cs k)),

      (∀ k, (Ks k).IsCoherent) ∧ (∀ k, (Ks k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + 1)).obj U.1))) ∧

      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (u k).app U ∘ₗ (j k).app U = 0) ∧

      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
        LinearMap.ker ((u (k + c)).app U)
          ≤ LinearMap.range ((j (k + c)).app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj U.1)) ∧
        LinearMap.ker ((j (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ks (k + c)).obj U.1))) ∧

      ((∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((u k).app U)) →
        ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((u k).app U)) ∧

      (∀ k, (Cs k).IsCoherent) ∧ (∀ k, (Cs k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((γ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((γ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Cs (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U ∘ₗ (π k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.ker ((θ k).app U) = LinearMap.range ((u k).app U)) := by
  classical

  obtain ⟨L, ι, lam, hLc, hLq, hιi, hls, hlc, huι, hAR, hsurj⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_subsystem_ker_le_range_sup_pow_smul_top_of_affHom_of_forall_ker_eq_pow_smul_top
      I F hFc hFq φ hφs hφk Ps hPsc hPsq π hπs hπk u huc

  obtain ⟨Ks, κ, j, hKc, hKq, hκs, hκk, hjc, hjr, hjAR⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_adicSystem_range_eq_range_of_forall_pow_smul_top_inf_range_le
      I F φ hφs hφk L hLc hLq ι hιi lam hls hlc (fun U => by
        obtain ⟨c, hc⟩ := hAR U
        exact ⟨c, fun k n hkn => (hc k n hkn).2⟩)

  obtain ⟨Cs, γ, θ, hCc, hCq, hγs, hγk, hγc, hθs, hθk⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
      I F hFq φ hφs Ps hPsc hPsq π hπs hπk u huc
  refine ⟨Ks, κ, j, Cs, γ, θ, hKc, hKq, hκs, hκk, hjc, ?_, ?_, ?_, hCc, hCq, hγs, hγk, hγc, hθs, hθk⟩
  ·
    intro k U
    apply LinearMap.ext
    intro x
    have hx : (j k).app U x ∈ LinearMap.range ((ι k).app U) := by
      rw [← hjr k U]; exact LinearMap.mem_range_self _ x
    obtain ⟨y, hy⟩ := hx
    rw [LinearMap.comp_apply, ← hy, ← LinearMap.comp_apply, huι k U, LinearMap.zero_apply, LinearMap.zero_apply]
  ·
    intro U
    obtain ⟨c₁, hc₁⟩ := hAR U
    obtain ⟨c₂, hc₂⟩ := hjAR U
    refine ⟨c₁ + c₂, fun k => ⟨?_, ?_⟩⟩
    · rw [hjr (k + (c₁ + c₂)) U]
      exact (hc₁ k (k + (c₁ + c₂)) (by omega)).1
    · exact hc₂ k (k + (c₁ + c₂)) (by omega)
  ·
    intro hus k U
    rw [hjr k U]
    exact hsurj hus k U

end S_AlgebraicGeometry_OModulePresheaf_exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_kernel_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top (solution)
