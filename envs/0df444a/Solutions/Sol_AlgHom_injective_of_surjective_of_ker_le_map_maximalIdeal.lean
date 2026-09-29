-- Prove2me | solution 1 for AlgHom.injective_of_surjective_of_ker_le_map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b798eccd-056c-51d1-8b05-f3e39545f09b

import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_injective_of_surjective_of_ker_le_map_maximalIdeal

open IsLocalRing

theorem solution
    {𝒪 : Type*} {A : Type*} {B : Type*} [CommRing 𝒪] [IsLocalRing 𝒪]
    [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsNoetherianRing A] [IsLocalHom (algebraMap 𝒪 A)]
    [CommRing B] [Algebra 𝒪 B] [Module.Free 𝒪 B]
    (f : A →ₐ[𝒪] B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ (maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :
    Function.Injective f := by
  classical
  set K : Ideal A := RingHom.ker f with hK
  set I : Ideal A := (maximalIdeal 𝒪).map (algebraMap 𝒪 A) with hI

  obtain ⟨s, hs⟩ : ∃ s : B →ₗ[𝒪] A, f.toLinearMap ∘ₗ s = LinearMap.id :=
    Module.projective_lifting_property f.toLinearMap LinearMap.id hf
  have hfs : ∀ b, f (s b) = b := fun b => by
    simpa using LinearMap.congr_fun hs b

  let r : A →ₗ[𝒪] A := LinearMap.id - s ∘ₗ f.toLinearMap
  have hr_mem : ∀ a, r a ∈ K := fun a => by
    simp [r, hK, RingHom.mem_ker, hfs]
  have hr_id : ∀ x ∈ K, r x = x := fun x hx => by
    have hx0 : f x = 0 := hx
    simp [r, hx0]

  have hKIK : K ≤ I * K := by
    intro x hx
    have hxI : x ∈ (I.restrictScalars 𝒪) := hker hx
    rw [hI, ← Ideal.smul_top_eq_map] at hxI
    have h1 : r x ∈ (maximalIdeal 𝒪 • (⊤ : Submodule 𝒪 A)).map r := Submodule.mem_map_of_mem hxI
    rw [Submodule.map_smul''] at h1
    have h2 : maximalIdeal 𝒪 • (⊤ : Submodule 𝒪 A).map r ≤ (I * K).restrictScalars 𝒪 := by
      refine Submodule.smul_le.mpr fun m hm a ha => ?_
      obtain ⟨a', -, rfl⟩ := Submodule.mem_map.mp ha
      change m • r a' ∈ I * K
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hm) (hr_mem a')
    have h3 : r x ∈ I * K := h2 h1
    rwa [hr_id x hx] at h3

  have hIjac : I ≤ Ideal.jacobson ⊥ :=
    (map_maximalIdeal_le (algebraMap 𝒪 A)).trans (maximalIdeal_le_jacobson _)
  have hKbot : K = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I K (IsNoetherian.noetherian K)
      (by rwa [Ideal.smul_eq_mul]) hIjac
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : a ∈ K := ha
  rw [hKbot] at this
  exact (Submodule.mem_bot A).mp this

end S_AlgHom_injective_of_surjective_of_ker_le_map_maximalIdeal
end P2MW
export P2MW.S_AlgHom_injective_of_surjective_of_ker_le_map_maximalIdeal (solution)
