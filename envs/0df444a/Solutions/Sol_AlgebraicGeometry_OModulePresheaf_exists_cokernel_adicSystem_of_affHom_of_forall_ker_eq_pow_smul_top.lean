-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/80753e6f-d337-55fd-b62c-b3d78c309bd5

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace CokerAdic29

section LinAlg

variable {R : Type u} [CommRing R] {M N Q : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q]

noncomputable def descend (f : M →ₗ[R] Q) (hf : Function.Surjective f) (g : M →ₗ[R] N)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : Q →ₗ[R] N :=
  (LinearMap.ker f).liftQ g h ∘ₗ (f.quotKerEquivOfSurjective hf).symm.toLinearMap

theorem descend_apply (f : M →ₗ[R] Q) (hf : Function.Surjective f) (g : M →ₗ[R] N)
    (h : LinearMap.ker f ≤ LinearMap.ker g) (m : M) : descend f hf g h (f m) = g m := by
  simp only [descend, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_toLinearMap]
  have : (f.quotKerEquivOfSurjective hf).symm (f m) = Submodule.Quotient.mk m := by
    apply (f.quotKerEquivOfSurjective hf).injective
    simp [LinearMap.quotKerEquivOfSurjective]
  rw [this, Submodule.liftQ_apply]

theorem descend_comp (f : M →ₗ[R] Q) (hf : Function.Surjective f) (g : M →ₗ[R] N)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : descend f hf g h ∘ₗ f = g :=
  LinearMap.ext (descend_apply f hf g h)

end LinAlg

section Main

variable {A : Type u} [CommRing A] {I : Ideal A} {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
  {F : ℕ → OModulePresheaf q}
  {φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k)}
  {Ps : ℕ → OModulePresheaf q}
  {π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k)}
  {u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k)}
  (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U)
  {Cs : ℕ → OModulePresheaf q} {θ : ∀ k, OModulePresheaf.AffHom (Ps k) (Cs k)}
  (hθs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U))
  (hθk : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.ker ((θ k).app U) = LinearMap.range ((u k).app U))

include huc hθk in

theorem ker_le (k : ℕ) (U : P.affineOpens) :
    LinearMap.ker ((θ (k + 1)).app U) ≤ LinearMap.ker ((θ k).app U ∘ₗ (π k).app U) := by
  intro x hx
  rw [hθk] at hx
  obtain ⟨y, rfl⟩ := hx
  have hy : (π k).app U ((u (k + 1)).app U y) = (u k).app U ((φ k).app U y) := by
    simpa using LinearMap.congr_fun (huc k U) y
  rw [LinearMap.mem_ker, LinearMap.comp_apply, hy, ← LinearMap.mem_ker, hθk]
  exact ⟨_, rfl⟩

noncomputable def gamma (k : ℕ) : OModulePresheaf.AffHom (Cs (k + 1)) (Cs k) where
  app U := descend ((θ (k + 1)).app U) (hθs (k + 1) U) ((θ k).app U ∘ₗ (π k).app U) (ker_le huc hθk k U)
  app_smul U a x := by
    obtain ⟨m, rfl⟩ := hθs (k + 1) U x
    rw [← (θ (k + 1)).app_smul, descend_apply, descend_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      (π k).app_smul, (θ k).app_smul]
  naturality {U U'} h := by
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := hθs (k + 1) U' x
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← OModulePresheaf.AffHom.naturality_apply, descend_apply, descend_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      OModulePresheaf.AffHom.naturality_apply, OModulePresheaf.AffHom.naturality_apply]

theorem gamma_app_theta (k : ℕ) (U : P.affineOpens) (m : (Ps (k + 1)).obj U.1) :
    (gamma huc hθs hθk k).app U ((θ (k + 1)).app U m) = (θ k).app U ((π k).app U m) :=
  descend_apply _ _ _ _ m

theorem gamma_comp (k : ℕ) (U : P.affineOpens) :
    (gamma huc hθs hθk k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U ∘ₗ (π k).app U :=
  descend_comp _ _ _ _

include hθs in
theorem gamma_surjective (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (k : ℕ) (U : P.affineOpens) : Function.Surjective ((gamma huc hθs hθk k).app U) := by
  intro c
  obtain ⟨p, rfl⟩ := hθs k U c
  obtain ⟨p', rfl⟩ := hπs k U p
  exact ⟨(θ (k + 1)).app U p', gamma_app_theta huc hθs hθk k U p'⟩

include hθk huc in

theorem ker_comp_eq (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (k : ℕ) (U : P.affineOpens) :
    LinearMap.ker ((θ k).app U ∘ₗ (π k).app U) =
      LinearMap.range ((u (k + 1)).app U) ⊔ LinearMap.ker ((π k).app U) := by
  apply le_antisymm
  · intro p hp
    rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, hθk] at hp
    obtain ⟨x, hx⟩ := hp
    obtain ⟨y, rfl⟩ := hφs k U x
    have hy : (π k).app U ((u (k + 1)).app U y) = (u k).app U ((φ k).app U y) := by
      rw [← LinearMap.comp_apply, huc, LinearMap.comp_apply]
    refine Submodule.mem_sup.2 ⟨(u (k + 1)).app U y, ⟨y, rfl⟩, p - (u (k + 1)).app U y, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hy, hx, sub_self]
  · refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact ker_le huc hθk k U (by rw [hθk]; exact ⟨y, rfl⟩)
    · intro p hp
      rw [LinearMap.mem_ker] at hp
      rw [LinearMap.mem_ker, LinearMap.comp_apply, hp, map_zero]

include hθs hθk huc in
theorem ker_gamma (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (k : ℕ) (U : P.affineOpens) :
    LinearMap.ker ((gamma huc hθs hθk k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Cs (k + 1)).obj U.1)) := by

  have h1 : LinearMap.ker ((gamma huc hθs hθk k).app U) =
      (LinearMap.ker ((θ k).app U ∘ₗ (π k).app U)).map ((θ (k + 1)).app U) := by
    ext c
    constructor
    · intro hc
      obtain ⟨p, rfl⟩ := hθs (k + 1) U c
      refine ⟨p, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply]
      rw [LinearMap.mem_ker, gamma_app_theta huc hθs hθk] at hc
      exact hc
    · rintro ⟨p, hp, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply] at hp
      rw [LinearMap.mem_ker, gamma_app_theta huc hθs hθk]
      exact hp
  rw [h1, ker_comp_eq huc hθk hφs k U, Submodule.map_sup, hπk, Submodule.map_smul'',
    Submodule.map_top, LinearMap.range_eq_top.2 (hθs (k + 1) U)]
  have h2 : (LinearMap.range ((u (k + 1)).app U)).map ((θ (k + 1)).app U) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨p, hp, rfl⟩
    rw [← hθk] at hp
    exact hp
  rw [h2, bot_sup_eq]

end Main

end CokerAdic29

open CokerAdic29 in
theorem solution
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf q) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U) :
    ∃ (Cs : ℕ → OModulePresheaf q) (γ : ∀ k, OModulePresheaf.AffHom (Cs (k + 1)) (Cs k))
      (θ : ∀ k, OModulePresheaf.AffHom (Ps k) (Cs k)),
      (∀ k, (Cs k).IsCoherent) ∧ (∀ k, (Cs k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((γ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((γ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Cs (k + 1)).obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (γ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U ∘ₗ (π k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.ker ((θ k).app U) = LinearMap.range ((u k).app U)) := by
  classical

  have hlev : ∀ k, ∃ (C : OModulePresheaf q) (ρ : OModulePresheaf.AffHom (Ps k) C),
      C.IsCoherent ∧ C.IsQuasicoherent ∧ (∀ U : P.affineOpens, Function.Surjective (ρ.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.ker (ρ.app U) = LinearMap.range ((u k).app U)) := by
    intro k
    obtain ⟨C, ρ, hc, hq, hs, hk⟩ :=
      OModulePresheaf.AffHom.exists_isQuasicoherent_surjective_ker_eq_range (hFq k) (hPsq k) (u k)
    exact ⟨C, ρ, hc (hPsc k), hq, hs, hk⟩
  choose Cs θ hCc hCq hθs hθk using hlev
  refine ⟨Cs, fun k => gamma huc hθs hθk k, θ, hCc, hCq,
    fun k U => gamma_surjective huc hθs hθk hπs k U,
    fun k U => ker_gamma huc hθs hθk hφs hπk k U,
    fun k U => gamma_comp huc hθs hθk k U, hθs, hθk⟩

end S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cokernel_adicSystem_of_affHom_of_forall_ker_eq_pow_smul_top (solution)
