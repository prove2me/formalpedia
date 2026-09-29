-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b9dca631-ac25-5397-ab52-3a1c6d2d0e3b

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_surjective_ker_eq_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mPresentSol

p2m_open "AlgebraicGeometry.OModulePresheaf"

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (.of A)}

section Lin

variable {M M' N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
  [AddCommGroup N] [Module A N]

noncomputable def desc (ρ : M →ₗ[A] M') (hρ : Function.Surjective ρ) (ψ : M →ₗ[A] N)
    (hk : LinearMap.ker ρ ≤ LinearMap.ker ψ) : M' →ₗ[A] N :=
  (LinearMap.ker ρ).liftQ ψ hk ∘ₗ (ρ.quotKerEquivOfSurjective hρ).symm.toLinearMap

theorem desc_apply (ρ : M →ₗ[A] M') (hρ : Function.Surjective ρ) (ψ : M →ₗ[A] N)
    (hk : LinearMap.ker ρ ≤ LinearMap.ker ψ) (x : M) : desc ρ hρ ψ hk (ρ x) = ψ x := by
  have hx : (ρ.quotKerEquivOfSurjective hρ).symm (ρ x) = Submodule.Quotient.mk x :=
    (LinearEquiv.symm_apply_eq _).mpr (LinearMap.quotKerEquivOfSurjective_apply_mk ρ hρ x).symm
  simp only [desc, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hx, Submodule.liftQ_apply]

theorem desc_comp (ρ : M →ₗ[A] M') (hρ : Function.Surjective ρ) (ψ : M →ₗ[A] N)
    (hk : LinearMap.ker ρ ≤ LinearMap.ker ψ) : desc ρ hρ ψ hk ∘ₗ ρ = ψ :=
  LinearMap.ext (desc_apply ρ hρ ψ hk)

theorem ker_desc (ρ : M →ₗ[A] M') (hρ : Function.Surjective ρ) (ψ : M →ₗ[A] N)
    (hk : LinearMap.ker ρ ≤ LinearMap.ker ψ) :
    LinearMap.ker (desc ρ hρ ψ hk) = (LinearMap.ker ψ).map ρ := by
  ext z
  obtain ⟨x, rfl⟩ := hρ z
  rw [LinearMap.mem_ker, desc_apply]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨x', hx', hxx'⟩
    have hd : x - x' ∈ LinearMap.ker ρ := by rw [LinearMap.mem_ker, map_sub, hxx', sub_self]
    have := hk hd
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    rw [this]; exact hx'

end Lin

section Card

variable (I : Ideal A) {H G : OModulePresheaf q}
  (hHq : H.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
  (h : OModulePresheaf.AffHom H G)
  (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
  (ψ : ∀ k, OModulePresheaf.AffHom G (F k))
  (hψs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U))
  (hψk : ∀ (k : ℕ) (U : P.affineOpens),
    LinearMap.ker ((ψ k).app U)
      = LinearMap.range (h.app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1)))
  (hψc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U)

include hHq hGc hGq hψs hψk hψc in
theorem main :
    ∃ (G' : OModulePresheaf q) (ρ : OModulePresheaf.AffHom G G')
      (ψ' : ∀ k, OModulePresheaf.AffHom G' (F k)),
      G'.IsCoherent ∧ G'.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Surjective (ρ.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.ker (ρ.app U) = LinearMap.range (h.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ' k).app U ∘ₗ ρ.app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ' k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ' k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ' (k + 1)).app U = (ψ' k).app U) := by
  obtain ⟨G', ρ, hc, hq, hρs, hρk⟩ :=
    AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_surjective_ker_eq_range hHq hGq h

  have hker : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.ker (ρ.app U) ≤ LinearMap.ker ((ψ k).app U) :=
    fun k U => by rw [hρk, hψk]; exact le_sup_left

  let d : ∀ (k : ℕ) (U : P.affineOpens), G'.obj U.1 →ₗ[A] (F k).obj U.1 :=
    fun k U => desc (ρ.app U) (hρs U) ((ψ k).app U) (hker k U)
  have d_ρ : ∀ (k : ℕ) (U : P.affineOpens) (x : G.obj U.1), d k U (ρ.app U x) = (ψ k).app U x :=
    fun k U x => desc_apply _ _ _ _ x
  let ψ' : ∀ k, OModulePresheaf.AffHom G' (F k) := fun k =>
    { app := d k
      app_smul := fun U a z => by
        obtain ⟨x, rfl⟩ := hρs U z
        rw [← ρ.app_smul, d_ρ, d_ρ, (ψ k).app_smul]
      naturality := fun {U U'} hle => LinearMap.ext fun z => by
        obtain ⟨x, rfl⟩ := hρs U' z
        show d k U (G'.res hle (ρ.app U' x)) = (F k).res hle (d k U' (ρ.app U' x))
        rw [← ρ.naturality_apply hle x, d_ρ, d_ρ, (ψ k).naturality_apply hle x] }
  have ψ'_app : ∀ (k : ℕ) (U : P.affineOpens), (ψ' k).app U = d k U := fun _ _ => rfl
  refine ⟨G', ρ, ψ', hc hGc, hq, hρs, hρk, fun k U => desc_comp _ _ _ _, ?_, ?_, ?_⟩
  ·
    intro k U y
    obtain ⟨x, rfl⟩ := hψs k U y
    exact ⟨ρ.app U x, d_ρ k U x⟩
  ·
    intro k U
    have hb : (LinearMap.range (h.app U)).map (ρ.app U) = ⊥ :=
      le_bot_iff.mp (Submodule.map_le_iff_le_comap.mpr (by rw [Submodule.comap_bot, hρk]))
    rw [ψ'_app, show d k U = desc (ρ.app U) (hρs U) ((ψ k).app U) (hker k U) from rfl, ker_desc, hψk,
      Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hρs U),
      hb, bot_sup_eq]
  ·
    intro k U
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := hρs U z
    show (φ k).app U (d (k + 1) U (ρ.app U x)) = d k U (ρ.app U x)
    rw [d_ρ, d_ρ, ← hψc k U, LinearMap.comp_apply]

end Card

end P2mPresentSol

theorem solution
    {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    {H G : OModulePresheaf q} (hHq : H.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (h : OModulePresheaf.AffHom H G)
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (ψ : ∀ k, OModulePresheaf.AffHom G (F k))
    (hψs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U))
    (hψk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψ k).app U)
        = LinearMap.range (h.app U) ⊔ I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1)))
    (hψc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) :
    ∃ (G' : OModulePresheaf q) (ρ : OModulePresheaf.AffHom G G')
      (ψ' : ∀ k, OModulePresheaf.AffHom G' (F k)),
      G'.IsCoherent ∧ G'.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Surjective (ρ.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.ker (ρ.app U) = LinearMap.range (h.app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (ψ' k).app U ∘ₗ ρ.app U = (ψ k).app U) ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ' k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ' k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ' (k + 1)).app U = (ψ' k).app U) :=
  P2mPresentSol.main I hHq hGc hGq h F φ ψ hψs hψk hψc

end S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup (solution)
