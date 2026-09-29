-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d5b6307e-36dc-588b-92b2-a5b69645715a

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace PG3KerAnnih

open AlgebraicGeometry.OModulePresheaf

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

noncomputable def iter (K : ℕ → OModulePresheaf q) (κ : ∀ k, AffHom (K (k + 1)) (K k))
    (U : P.affineOpens) (k : ℕ) : ∀ m : ℕ, (K (k + m)).obj U.1 →ₗ[A] (K k).obj U.1
  | 0 => LinearMap.id
  | m + 1 => iter K κ U k m ∘ₗ (κ (k + m)).app U

theorem iter_surjective (K : ℕ → OModulePresheaf q) (κ : ∀ k, AffHom (K (k + 1)) (K k))
    (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (U : P.affineOpens) (k : ℕ) : ∀ m : ℕ, Function.Surjective (iter K κ U k m)
  | 0 => fun y => ⟨y, rfl⟩
  | m + 1 => (iter_surjective K κ hκs U k m).comp (hκs (k + m) U)

theorem iter_smul (K : ℕ → OModulePresheaf q) (κ : ∀ k, AffHom (K (k + 1)) (K k))
    (U : P.affineOpens) (k : ℕ) :
    ∀ (m : ℕ) (a : Γ(P, U.1)) (x : (K (k + m)).obj U.1),
      iter K κ U k m (a • x) = a • iter K κ U k m x
  | 0, _, _ => rfl
  | m + 1, a, x => by
    show iter K κ U k m ((κ (k + m)).app U (a • x)) = a • iter K κ U k m ((κ (k + m)).app U x)
    rw [(κ (k + m)).app_smul]
    exact iter_smul K κ U k m a _

theorem iter_comm (K F : ℕ → OModulePresheaf q) (κ : ∀ k, AffHom (K (k + 1)) (K k))
    (φ : ∀ k, AffHom (F (k + 1)) (F k)) (j : ∀ k, AffHom (K k) (F k))
    (hjc : ∀ (k : ℕ) (U : P.affineOpens),
      (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U)
    (U : P.affineOpens) (k : ℕ) :
    ∀ (m : ℕ) (x : (K (k + m)).obj U.1),
      (j k).app U (iter K κ U k m x) = iter F φ U k m ((j (k + m)).app U x)
  | 0, _ => rfl
  | m + 1, x => by
    show (j k).app U (iter K κ U k m ((κ (k + m)).app U x)) =
      iter F φ U k m ((φ (k + m)).app U ((j (k + m + 1)).app U x))
    rw [iter_comm K F κ φ j hjc U k m]
    exact congrArg (iter F φ U k m) (LinearMap.congr_fun (hjc (k + m) U) x).symm

theorem iter_map_smul_top_le (K : ℕ → OModulePresheaf q) (κ : ∀ k, AffHom (K (k + 1)) (K k))
    (U : P.affineOpens) (k m : ℕ) (J : Ideal A) (x : (K (k + m)).obj U.1)
    (hx : x ∈ J • (⊤ : Submodule A ((K (k + m)).obj U.1))) :
    iter K κ U k m x ∈ J • (⊤ : Submodule A ((K k).obj U.1)) := by
  have := Submodule.mem_map_of_mem (f := iter K κ U k m) hx
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem stage_killed (I : Ideal A) (K : ℕ → OModulePresheaf q) (κ : ∀ k, AffHom (K (k + 1)) (K k))
    (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (hκk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((K (k + 1)).obj U.1)))
    (k : ℕ) (U : P.affineOpens) (z : (K k).obj U.1)
    (hz : z ∈ I ^ (k + 1) • (⊤ : Submodule A ((K k).obj U.1))) : z = 0 := by
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr w _
    obtain ⟨w', rfl⟩ := hκs k U w
    rw [← map_smul, ← LinearMap.mem_ker, hκk]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy; rw [hx, hy, add_zero]

end PG3KerAnnih

open PG3KerAnnih AlgebraicGeometry.OModulePresheaf in
theorem solution
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (K (k + 1)) (K k))
    (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (hκk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((K (k + 1)).obj U.1)))
    (j : ∀ k, OModulePresheaf.AffHom (K k) (F k))
    (hjc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U)
    (hji : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((j (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((K (k + c)).obj U.1)))
    (Ps : ℕ → OModulePresheaf q) (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huj : ∀ (k : ℕ) (U : P.affineOpens), (u k).app U ∘ₗ (j k).app U = 0)
    (𝓙 : P.IdealSheafData) (N : ℕ)
    (hker : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ (k : ℕ) (x : (F (k + c)).obj U.1), (u (k + c)).app U x = 0 →
      ∀ a : Γ(P, U.1), a ∈ 𝓙.ideal U ^ N → a • x ∈ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj U.1))) :
    ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙.ideal U ^ N, ∀ y : (K k).obj U.1, a • y = 0 := by
  intro k U a ha y
  obtain ⟨c, hc⟩ := hji U
  obtain ⟨c', hc'⟩ := hker U
  obtain ⟨y₁, rfl⟩ := iter_surjective K κ hκs U k c y
  obtain ⟨y₂, rfl⟩ := iter_surjective K κ hκs U (k + c) c' y₁
  rw [← iter_smul, ← iter_smul]

  have hu : (u (k + c + c')).app U ((j (k + c + c')).app U y₂) = 0 := by
    rw [← LinearMap.comp_apply, huj]; rfl
  have h1 : a • (j (k + c + c')).app U y₂ ∈
      I ^ (k + c + 1) • (⊤ : Submodule A ((F (k + c + c')).obj U.1)) := hc' (k + c) _ hu a ha

  have h2 : (j (k + c)).app U (iter K κ U (k + c) c' (a • y₂)) = 0 := by
    rw [iter_comm K F κ φ j hjc U (k + c) c', (j (k + c + c')).app_smul]
    exact stage_killed I F φ hφs hφk (k + c) U _ (iter_map_smul_top_le F φ U (k + c) c' _ _ h1)

  have h3 : iter K κ U (k + c) c' (a • y₂) ∈ I ^ (k + 1) • (⊤ : Submodule A ((K (k + c)).obj U.1)) :=
    hc k (LinearMap.mem_ker.mpr h2)
  exact stage_killed I K κ hκs hκk k U _ (iter_map_smul_top_le K κ U k c _ _ h3)

end S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_comp_eq_zero_of_forall_smul_mem_pow_smul_top (solution)
