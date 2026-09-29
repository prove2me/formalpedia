-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5b179cd6-5300-582f-8655-4b17b8332ed1

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace PG1Body

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
  (K : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (K (k + 1)) (K k)) (U : P.affineOpens)

private noncomputable def _root_.PG1Body.trans (k : ℕ) : (m : ℕ) → ((K (k + m)).obj U.1 →ₗ[A] (K k).obj U.1)
  | 0 => LinearMap.id
  | m + 1 => trans k m ∘ₗ (κ (k + m)).app U

p2m_export "PG1Body" "trans"
theorem trans_succ_apply (k m : ℕ) (z : (K (k + (m + 1))).obj U.1) :
    trans K κ U k (m + 1) z = trans K κ U k m ((κ (k + m)).app U z) := rfl

theorem trans_surjective (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (k : ℕ) : ∀ m, Function.Surjective (trans K κ U k m)
  | 0 => fun y => ⟨y, rfl⟩
  | m + 1 => (trans_surjective hκs k m).comp (hκs (k + m) U)

theorem trans_smul (k : ℕ) : ∀ (m : ℕ) (a : Γ(P, U.1)) (z : (K (k + m)).obj U.1),
    trans K κ U k m (a • z) = a • trans K κ U k m z
  | 0 => fun _ _ => rfl
  | m + 1 => fun a z => by
    rw [trans_succ_apply, trans_succ_apply, (κ (k + m)).app_smul, trans_smul k m]

theorem trans_succ_eq_zero (I : Ideal A)
    (hκk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((K (k + 1)).obj U.1)))
    (k : ℕ) : ∀ (m : ℕ) (z : (K (k + (m + 1))).obj U.1),
    z ∈ I ^ (k + 1) • (⊤ : Submodule A ((K (k + (m + 1))).obj U.1)) → trans K κ U k (m + 1) z = 0
  | 0 => fun z hz => by
    rw [trans_succ_apply]
    show (κ k).app U z = 0
    rw [← LinearMap.mem_ker, hκk]
    exact hz
  | m + 1 => fun z hz => by
    rw [trans_succ_apply]
    apply trans_succ_eq_zero I hκk k m
    have h := Submodule.mem_map_of_mem (f := (κ (k + (m + 1))).app U) hz
    rw [Submodule.map_smul''] at h
    exact Submodule.smul_mono le_rfl le_top h

end PG1Body

open PG1Body in
theorem solution
    {A : Type u} [CommRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    (S : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (S (k + 1)) (S k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((S (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (κ : ∀ k, OModulePresheaf.AffHom (K (k + 1)) (K k))
    (hκs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((κ k).app U))
    (hκk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((κ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((K (k + 1)).obj U.1)))
    (j : ∀ k, OModulePresheaf.AffHom (K k) (S k))
    (hjc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (j (k + 1)).app U = (j k).app U ∘ₗ (κ k).app U)
    (𝓙 𝓙₁ 𝓙₂ : P.IdealSheafData) (s t : ℕ)
    (hjr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((j k).app U) = OModulePresheaf.idealPowSub q 𝓙₁ (S k) 1 U.1)
    (hji : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((j (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A ((K (k + c)).obj U.1)))
    (hle : ∀ U : P.affineOpens, 𝓙₂.ideal U ^ t * 𝓙₁.ideal U ≤ 𝓙.ideal U ^ s)
    (hS : ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙.ideal U ^ s, ∀ x : (S k).obj U.1, a • x = 0) :
    ∀ (k : ℕ) (U : P.affineOpens), ∀ a ∈ 𝓙₂.ideal U ^ t, ∀ y : (K k).obj U.1, a • y = 0 := by
  intro k U a ha y
  obtain ⟨c, hc⟩ := hji U
  have hc' : LinearMap.ker ((j (k + (c + 1))).app U) ≤
      I ^ (k + 1) • (⊤ : Submodule A ((K (k + (c + 1))).obj U.1)) := by
    have h := hc (k + 1)
    rw [show k + 1 + c = k + (c + 1) by omega] at h
    exact h.trans (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)))
  obtain ⟨z, rfl⟩ := trans_surjective K κ U hκs k (c + 1) y
  rw [← trans_smul]
  apply trans_succ_eq_zero K κ U I hκk k c
  apply hc'
  rw [LinearMap.mem_ker, (j _).app_smul]

  have key : ∀ (n : ℕ) (x : (S n).obj U.1), x ∈ OModulePresheaf.idealPowSub q 𝓙₁ (S n) 1 U.1 → a • x = 0 := by
    intro n x hx
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom q U.1).toModule
    haveI := (S n).isScalarTower U.1
    rw [OModulePresheaf.idealPowSub, Submodule.restrictScalars_mem, pow_one,
      OModulePresheaf.idealSections_eq_ideal] at hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro b hb x _
      rw [← mul_smul]
      exact hS n U _ (hle U (Ideal.mul_mem_mul ha hb)) x
    · intro x y hx hy
      rw [smul_add, hx, hy, add_zero]
  apply key
  rw [← hjr]
  exact ⟨z, rfl⟩

end S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top (solution)
