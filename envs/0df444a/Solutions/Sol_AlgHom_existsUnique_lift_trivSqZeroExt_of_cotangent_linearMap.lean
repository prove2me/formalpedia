-- Prove2me | solution 1 for AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/66c933d9-a563-5ed6-b576-8a50a8460c99

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap

universe u v x

theorem solution
    {𝒪 : Type u} [CommRing 𝒪] {R : Type v} [CommRing R] [Algebra 𝒪 R] (πR : R →ₐ[𝒪] 𝒪)
    {N : Type x} [AddCommGroup N] [Module 𝒪 N] [Module 𝒪ᵐᵒᵖ N] [IsCentralScalar 𝒪 N]
    (f : (RingHom.ker πR).Cotangent →ₗ[𝒪] N) :
    ∃! ψ : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N, (∀ r : R, (ψ r).fst = πR r) ∧
      ∀ a : RingHom.ker πR, (ψ (a : R)).snd = f ((RingHom.ker πR).toCotangent a) := by

  have hmem : ∀ r : R, r - algebraMap 𝒪 R (πR r) ∈ RingHom.ker πR := fun r => by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]

  let E : R →ₗ[𝒪] RingHom.ker πR :=
    { toFun := fun r => ⟨r - algebraMap 𝒪 R (πR r), hmem r⟩
      map_add' := fun r s => Subtype.ext (by
        show r + s - algebraMap 𝒪 R (πR (r + s)) =
          (r - algebraMap 𝒪 R (πR r)) + (s - algebraMap 𝒪 R (πR s))
        simp only [map_add]
        ring)
      map_smul' := fun c r => Subtype.ext (by
        show c • r - algebraMap 𝒪 R (πR (c • r)) = c • (r - algebraMap 𝒪 R (πR r))
        rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def, Algebra.smul_def, mul_sub]) }
  have hE : ∀ r : R, ((E r : RingHom.ker πR) : R) = r - algebraMap 𝒪 R (πR r) := fun _ => rfl

  let F : R → N := fun r => f ((RingHom.ker πR).toCotangent (E r))
  have hF : ∀ r : R, F r = f ((RingHom.ker πR).toCotangent (E r)) := fun _ => rfl
  have hF_add : ∀ r s : R, F (r + s) = F r + F s := fun r s => by
    rw [hF, hF, hF, map_add, map_add, map_add]
  have hF_zero : F 0 = 0 := by
    rw [hF, map_zero, map_zero, map_zero]
  have hF_alg : ∀ c : 𝒪, F (algebraMap 𝒪 R c) = 0 := fun c => by
    have h0 : E (algebraMap 𝒪 R c) = 0 := Subtype.ext (by
      rw [hE, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self, Submodule.coe_zero])
    rw [hF, h0, map_zero, map_zero]
  have hF_one : F 1 = 0 := by
    simpa only [map_one] using hF_alg 1

  have hF_mul : ∀ r s : R, F (r * s) = πR r • F s + πR s • F r := fun r s => by
    have hprod : (r - algebraMap 𝒪 R (πR r)) * (s - algebraMap 𝒪 R (πR s)) ∈ RingHom.ker πR :=
      (RingHom.ker πR).mul_mem_left _ (hmem s)
    have hsplit : E (r * s) = πR r • E s + πR s • E r + ⟨_, hprod⟩ := Subtype.ext (by
      simp only [hE, Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul]
      ring)
    have hsq : (RingHom.ker πR).toCotangent ⟨_, hprod⟩ = 0 :=
      ((RingHom.ker πR).toCotangent_eq_zero _).mpr (by
        rw [pow_two]
        exact Ideal.mul_mem_mul (hmem r) (hmem s))
    rw [hF, hF, hF, hsplit]
    simp only [map_add, LinearMap.map_smul_of_tower, hsq, add_zero, map_smul]

  let ψ : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N :=
    { toFun := fun r => TrivSqZeroExt.inl (πR r) + TrivSqZeroExt.inr (F r)
      map_one' := by
        ext
        · simp
        · simp [hF_one]
      map_mul' := fun r s => by
        ext
        · simp
        · simp [hF_mul r s, op_smul_eq_smul]
      map_zero' := by
        ext
        · simp
        · simp [hF_zero]
      map_add' := fun r s => by
        ext
        · simp
        · simp [hF_add r s]
      commutes' := fun c => by
        ext
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
        · simp [TrivSqZeroExt.algebraMap_eq_inl, hF_alg] }
  have hψ : ∀ r : R, ψ r = TrivSqZeroExt.inl (πR r) + TrivSqZeroExt.inr (F r) := fun _ => rfl
  have hψ_fst : ∀ r : R, (ψ r).fst = πR r := fun r => by rw [hψ]; simp
  have hψ_snd : ∀ r : R, (ψ r).snd = F r := fun r => by rw [hψ]; simp

  have hE_ker : ∀ a : RingHom.ker πR, E (a : R) = a := fun a => Subtype.ext (by
    rw [hE, RingHom.mem_ker.mp a.2, map_zero, sub_zero])

  have hsnd : ∀ ψ' : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N,
      (∀ a : RingHom.ker πR, (ψ' (a : R)).snd = f ((RingHom.ker πR).toCotangent a)) →
      ∀ r : R, (ψ' r).snd = F r := fun ψ' h2 r => by
    have hr : algebraMap 𝒪 R (πR r) + ((E r : RingHom.ker πR) : R) = r := by
      rw [hE]; ring
    calc (ψ' r).snd = (ψ' (algebraMap 𝒪 R (πR r) + ((E r : RingHom.ker πR) : R))).snd := by rw [hr]
      _ = F r := by
          rw [map_add, TrivSqZeroExt.snd_add, AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl,
            TrivSqZeroExt.snd_inl, zero_add, h2 (E r), hF]
  refine ⟨ψ, ⟨hψ_fst, fun a => ?_⟩, fun ψ' ⟨h1', h2'⟩ => ?_⟩
  · rw [hψ_snd, hF, hE_ker]
  · refine AlgHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
    · rw [h1' r, hψ_fst r]
    · rw [hsnd ψ' h2' r, hψ_snd r]

end S_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
end P2MW
export P2MW.S_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap (solution)
