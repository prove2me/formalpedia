-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7b0c0b6d-259b-5b12-ab52-d4cf6ee6b389

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace CoimageAdic29

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

end LinAlg

section Aff

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
  {G G' H : OModulePresheaf q}

noncomputable def descendAff (ρ : OModulePresheaf.AffHom G G') (hρ : ∀ U : P.affineOpens, Function.Surjective (ρ.app U))
    (ψ : OModulePresheaf.AffHom G H) (h : ∀ U : P.affineOpens, LinearMap.ker (ρ.app U) ≤ LinearMap.ker (ψ.app U)) :
    OModulePresheaf.AffHom G' H where
  app U := descend (ρ.app U) (hρ U) (ψ.app U) (h U)
  app_smul U a x := by
    obtain ⟨m, rfl⟩ := hρ U x
    rw [← ρ.app_smul, descend_apply, descend_apply, ψ.app_smul]
  naturality {U U'} hle := by
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := hρ U' x
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← ρ.naturality_apply, descend_apply, descend_apply, ψ.naturality_apply]

theorem descendAff_app (ρ : OModulePresheaf.AffHom G G') (hρ : ∀ U : P.affineOpens, Function.Surjective (ρ.app U))
    (ψ : OModulePresheaf.AffHom G H) (h : ∀ U : P.affineOpens, LinearMap.ker (ρ.app U) ≤ LinearMap.ker (ψ.app U))
    (U : P.affineOpens) (m : G.obj U.1) : (descendAff ρ hρ ψ h).app U (ρ.app U m) = ψ.app U m :=
  descend_apply _ _ _ _ m

theorem descendAff_comp (ρ : OModulePresheaf.AffHom G G') (hρ : ∀ U : P.affineOpens, Function.Surjective (ρ.app U))
    (ψ : OModulePresheaf.AffHom G H) (h : ∀ U : P.affineOpens, LinearMap.ker (ρ.app U) ≤ LinearMap.ker (ψ.app U))
    (U : P.affineOpens) : (descendAff ρ hρ ψ h).app U ∘ₗ ρ.app U = ψ.app U :=
  LinearMap.ext (descendAff_app ρ hρ ψ h U)

theorem range_descendAff (ρ : OModulePresheaf.AffHom G G') (hρ : ∀ U : P.affineOpens, Function.Surjective (ρ.app U))
    (ψ : OModulePresheaf.AffHom G H) (h : ∀ U : P.affineOpens, LinearMap.ker (ρ.app U) ≤ LinearMap.ker (ψ.app U))
    (U : P.affineOpens) : LinearMap.range ((descendAff ρ hρ ψ h).app U) = LinearMap.range (ψ.app U) := by
  rw [← descendAff_comp ρ hρ ψ h U, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (hρ U))]

theorem ker_descendAff (ρ : OModulePresheaf.AffHom G G') (hρ : ∀ U : P.affineOpens, Function.Surjective (ρ.app U))
    (ψ : OModulePresheaf.AffHom G H) (h : ∀ U : P.affineOpens, LinearMap.ker (ρ.app U) ≤ LinearMap.ker (ψ.app U))
    (U : P.affineOpens) : LinearMap.ker ((descendAff ρ hρ ψ h).app U) = (LinearMap.ker (ψ.app U)).map (ρ.app U) := by
  ext c
  constructor
  · intro hc
    obtain ⟨p, rfl⟩ := hρ U c
    rw [LinearMap.mem_ker, descendAff_app] at hc
    exact ⟨p, hc, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    have hp' : ψ.app U p = 0 := hp
    rw [LinearMap.mem_ker, descendAff_app, hp']

end Aff

theorem map_smul_top_of_surjective {A : Type u} [CommRing A] {M M' : Type u} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (J : Ideal A) (g : M →ₗ[A] M') (hg : Function.Surjective g) :
    (J • (⊤ : Submodule A M)).map g = J • (⊤ : Submodule A M') := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]

end CoimageAdic29

open CoimageAdic29 in
theorem solution
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (hKq : ∀ k, (K k).IsQuasicoherent)
    (κ : ∀ k, OModulePresheaf.AffHom (K (k + 1)) (K k))
    (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (j : ∀ k, OModulePresheaf.AffHom (K k) (F k))
    (hjc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U)
    (Ps : ℕ → OModulePresheaf q) (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (u (k + 1)).app U = (u k).app U ∘ₗ (φ k).app U)
    (huj : ∀ (k : ℕ) (U : P.affineOpens), (u k).app U ∘ₗ (j k).app U = 0)
    (hAR : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((u (k + c)).app U)
        ≤ LinearMap.range ((j (k + c)).app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj U.1))) :
    ∃ (E : ℕ → OModulePresheaf q) (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k)),
      (∀ k, (E k).IsCoherent) ∧ (∀ k, (E k).IsQuasicoherent) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1))) ∧
      ∃ ε : ∀ k, OModulePresheaf.AffHom (F k) (E k),
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.ker ((ε k).app U) = LinearMap.range ((j k).app U)) ∧
      ∃ uE : ∀ k, OModulePresheaf.AffHom (E k) (Ps k),
      (∀ (k : ℕ) (U : P.affineOpens), (uE k).app U ∘ₗ (ε k).app U = (u k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (π k).app U ∘ₗ (uE (k + 1)).app U = (uE k).app U ∘ₗ (τ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((uE k).app U) = LinearMap.range ((u k).app U)) ∧
      (∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
        LinearMap.ker ((uE (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((E (k + c)).obj U.1))) := by
  classical

  have hlev : ∀ k, ∃ (E : OModulePresheaf q) (ε : OModulePresheaf.AffHom (F k) E),
      E.IsCoherent ∧ E.IsQuasicoherent ∧ (∀ U : P.affineOpens, Function.Surjective (ε.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.ker (ε.app U) = LinearMap.range ((j k).app U)) := by
    intro k
    obtain ⟨E, ε, hc, hq, hs, hk⟩ :=
      AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_surjective_ker_eq_range (hKq k) (hFq k) (j k)
    exact ⟨E, ε, hc (hFc k), hq, hs, hk⟩
  choose E ε hEc hEq hεs hεk using hlev

  have hτker : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ε (k + 1)).app U) ≤ LinearMap.ker (((ε k).comp (φ k)).app U) := by
    intro k U x hx
    rw [hεk] at hx
    obtain ⟨y, rfl⟩ := hx
    show (ε k).app U ((φ k).app U ((j (k + 1)).app U y)) = 0
    rw [← LinearMap.comp_apply ((φ k).app U), hjc, LinearMap.comp_apply, ← LinearMap.mem_ker, hεk]
    exact ⟨_, rfl⟩
  let τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k) := fun k =>
    descendAff (ε (k + 1)) (hεs (k + 1)) ((ε k).comp (φ k)) (hτker k)
  have hτε : ∀ (k : ℕ) (U : P.affineOpens) (x : (F (k + 1)).obj U.1),
      (τ k).app U ((ε (k + 1)).app U x) = (ε k).app U ((φ k).app U x) :=
    fun k U x => descendAff_app _ _ _ _ U x

  have huker : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.ker ((ε k).app U) ≤ LinearMap.ker ((u k).app U) := by
    intro k U x hx
    rw [hεk] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, huj, LinearMap.zero_apply]
  let uE : ∀ k, OModulePresheaf.AffHom (E k) (Ps k) := fun k => descendAff (ε k) (hεs k) (u k) (huker k)
  have huE : ∀ (k : ℕ) (U : P.affineOpens) (x : (F k).obj U.1), (uE k).app U ((ε k).app U x) = (u k).app U x :=
    fun k U x => descendAff_app _ _ _ _ U x
  refine ⟨E, τ, hEc, hEq, ?_, ?_, ε, hεs, ?_, hεk, uE, ?_, ?_, ?_, ?_⟩
  ·
    intro k U z
    obtain ⟨y, rfl⟩ := hεs k U z
    obtain ⟨x, rfl⟩ := hφs k U y
    exact ⟨(ε (k + 1)).app U x, hτε k U x⟩
  ·
    intro k U
    rw [show (τ k) = descendAff (ε (k + 1)) (hεs (k + 1)) ((ε k).comp (φ k)) (hτker k) from rfl, ker_descendAff,
      ← map_smul_top_of_surjective (I ^ (k + 1)) _ (hεs (k + 1) U), ← hφk k U]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (ε k).app U ((φ k).app U x) = 0 := hx
      rw [← LinearMap.mem_ker, hεk] at hx'
      obtain ⟨z, hz⟩ := hx'
      obtain ⟨w, rfl⟩ := hκs k U z
      rw [← LinearMap.comp_apply, ← hjc, LinearMap.comp_apply] at hz

      have h1 : x - (j (k + 1)).app U w ∈ LinearMap.ker ((φ k).app U) := by
        rw [LinearMap.mem_ker, map_sub, hz, sub_self]
      have h2 : (ε (k + 1)).app U ((j (k + 1)).app U w) = 0 := by
        rw [← LinearMap.mem_ker, hεk]; exact ⟨w, rfl⟩
      refine ⟨x - (j (k + 1)).app U w, h1, ?_⟩
      rw [map_sub, h2, sub_zero]
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (φ k).app U x = 0 := hx
      refine ⟨x, ?_, rfl⟩
      show (ε k).app U ((φ k).app U x) = 0
      rw [hx', map_zero]
  ·
    intro k U
    exact LinearMap.ext fun x => hτε k U x
  ·
    intro k U
    exact LinearMap.ext fun x => huE k U x
  ·
    intro k U
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := hεs (k + 1) U z
    rw [LinearMap.comp_apply, LinearMap.comp_apply, huE, hτε, huE, ← LinearMap.comp_apply, huc, LinearMap.comp_apply]
  ·
    intro k U
    exact range_descendAff _ _ _ _ U
  ·
    intro U
    obtain ⟨c, hc⟩ := hAR U
    refine ⟨c, fun k => ?_⟩
    intro z hz
    obtain ⟨x, rfl⟩ := hεs (k + c) U z
    rw [LinearMap.mem_ker, huE] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp (hc k hz)
    have hy0 : (ε (k + c)).app U y = 0 := by
      rw [← LinearMap.mem_ker, hεk]; exact hy
    rw [map_add, hy0, zero_add, ← map_smul_top_of_surjective _ _ (hεs (k + c) U)]
    exact ⟨w, hw, rfl⟩

end S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coimage_adicSystem_of_forall_ker_le_range_sup_pow_smul_top (solution)
