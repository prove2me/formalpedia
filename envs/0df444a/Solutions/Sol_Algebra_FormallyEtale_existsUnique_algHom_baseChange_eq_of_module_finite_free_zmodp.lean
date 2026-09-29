-- Prove2me | solution 1 for Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c37e5534-2cd6-5766-93f2-f2dc3b1f0d00

import Mathlib
import Theorems.Thm_Algebra_FormallySmooth_exists_algHom_baseChange_eq_of_isAdicComplete
import Theorems.Thm_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace EtqLiftE96

theorem mem_span_of_one_tmul_eq_zero {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)]
    (hk : Function.Surjective (algebraMap 𝓞 (ZMod p)))
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (T : Type w) [CommRing T] [Algebra 𝓞 T] (x : T) (hx : (1 : ZMod p) ⊗ₜ[𝓞] x = 0) :
    x ∈ Ideal.span {(p : T)} := by
  set I : Ideal 𝓞 := Ideal.span {(p : 𝓞)} with hI

  have hker' : RingHom.ker (Algebra.ofId 𝓞 (ZMod p) : 𝓞 →+* ZMod p) = I := hker
  let e₀ : (𝓞 ⧸ RingHom.ker (Algebra.ofId 𝓞 (ZMod p) : 𝓞 →+* ZMod p)) ≃ₐ[𝓞] ZMod p :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId 𝓞 (ZMod p)) hk
  let e₁ : ZMod p ≃ₐ[𝓞] 𝓞 ⧸ I := e₀.symm.trans (Ideal.quotientEquivAlgOfEq 𝓞 hker')
  let e₂ : ZMod p ⊗[𝓞] T ≃ₐ[𝓞] (𝓞 ⧸ I) ⊗[𝓞] T := Algebra.TensorProduct.congr e₁ AlgEquiv.refl
  let e₃ : (𝓞 ⧸ I) ⊗[𝓞] T ≃ₗ[𝓞] T ⧸ (I • ⊤ : Submodule 𝓞 T) := TensorProduct.quotTensorEquivQuotSMul T I
  have h1 : e₂ ((1 : ZMod p) ⊗ₜ[𝓞] x) = (1 : 𝓞 ⧸ I) ⊗ₜ[𝓞] x := by
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]; rfl
  have h2 : e₃ ((1 : 𝓞 ⧸ I) ⊗ₜ[𝓞] x) = Submodule.Quotient.mk x := by
    rw [← map_one (Ideal.Quotient.mk I), TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have h3 : (Submodule.Quotient.mk x : T ⧸ (I • ⊤ : Submodule 𝓞 T)) = 0 := by
    rw [← h2, ← h1, hx, map_zero, map_zero]
  rw [Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] at h3
  rw [hI, Ideal.map_span, Set.image_singleton, map_natCast] at h3
  exact h3

end EtqLiftE96

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [Algebra 𝓞 H] [Module.Free 𝓞 H] [Module.Finite 𝓞 H] [Algebra.FormallyEtale 𝓞 H]
    (T : Type w) [CommRing T] [Algebra 𝓞 T] [Module.Free 𝓞 T] [Module.Finite 𝓞 T]
    (ψbar : ZMod p ⊗[𝓞] H →ₐ[ZMod p] ZMod p ⊗[𝓞] T) :
    ∃! ψ : H →ₐ[𝓞] T, Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) ψ = ψbar := by
  have hk : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.exists_algHom_baseChange_eq_of_isAdicComplete (𝓞 := 𝓞) (k := ZMod p) p hk hker H T ψbar
  refine ⟨ψ, hψ, fun ψ' hψ' => ?_⟩
  haveI : IsAdicComplete (Ideal.span {(p : T)}) T := IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p T
  apply AlgHom.eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified (Ideal.span {(p : T)})
    (IsAdicComplete.le_jacobson_bot _)
  intro a
  have h := congrArg (fun F => F ((1 : ZMod p) ⊗ₜ[𝓞] a)) (hψ'.trans hψ.symm)
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at h
  apply EtqLiftE96.mem_span_of_one_tmul_eq_zero p hk hker T
  rw [TensorProduct.tmul_sub, h, sub_self]

#print axioms solution

end S_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
end P2MW
export P2MW.S_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp (solution)
