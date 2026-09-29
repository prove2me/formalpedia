-- Prove2me | solution 1 for Algebra.TensorProduct.ker_lift_le_jacobson_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/23b4e622-97d4-5795-8cfe-fa093efe85a6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_ker_lift_le_jacobson_of_isLocalRing

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace E89C2
open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem map_maximalIdeal_le (D : Type w) [CommRing D] [Algebra R D] [Module.Finite R D]
    [IsLocalRing D] : (maximalIdeal R).map (algebraMap R D) ≤ maximalIdeal D := by
  rw [Ideal.map_le_iff_le_comap]
  have : (Ideal.comap (algebraMap R D) (maximalIdeal D)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (maximalIdeal D)
  rw [IsLocalRing.eq_maximalIdeal this]

theorem exists_maximalIdeal_pow_le (D : Type w) [CommRing D] [Algebra R D] [Module.Finite R D]
    [IsLocalRing D] : ∃ N : ℕ, (maximalIdeal D) ^ N ≤ (maximalIdeal R).map (algebraMap R D) := by
  set J : Ideal D := (maximalIdeal R).map (algebraMap R D) with hJ
  have hJle : J ≤ maximalIdeal D := map_maximalIdeal_le D
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal D).ne_top (top_le_iff.mp (h ▸ hJle))
  haveI : Nontrivial (D ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  haveI : IsLocalRing (D ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : Module.Finite (R ⧸ maximalIdeal R) (D ⧸ J) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ maximalIdeal R) (D ⧸ J)
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  haveI : IsArtinianRing (D ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (D ⧸ J)
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := D ⧸ J)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
  refine ⟨N, ?_⟩
  have hmap : (maximalIdeal D).map (Ideal.Quotient.mk J) ≤ maximalIdeal (D ⧸ J) := by
    apply IsLocalRing.le_maximalIdeal
    intro htop
    have h1 := Ideal.comap_map_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (maximalIdeal D)
    rw [htop, Ideal.comap_top] at h1
    have h2 : maximalIdeal D ⊔ Ideal.comap (Ideal.Quotient.mk J) ⊥ ≤ maximalIdeal D :=
      sup_le le_rfl (by rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]; exact hJle)
    rw [← h1] at h2
    exact (maximalIdeal.isMaximal D).ne_top (top_le_iff.mp h2)
  have h0 : ((maximalIdeal D) ^ N).map (Ideal.Quotient.mk J) = ⊥ := by
    rw [Ideal.map_pow]
    exact le_bot_iff.mp ((Ideal.pow_right_mono hmap N).trans (le_of_eq hN))
  rwa [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h0

theorem main {C : Type v} [CommRing C] [Algebra R C] [Module.Finite R C]
    {D : Type w} [CommRing D] [Algebra R D] [Module.Finite R D] [IsLocalRing D]
    (ε : D →ₐ[R] R) :
    RingHom.ker (Algebra.TensorProduct.lift (AlgHom.id R C) ((Algebra.ofId R C).comp ε)
        (fun _ _ => Commute.all _ _) : C ⊗[R] D →ₐ[R] C) ≤ Ideal.jacobson ⊥ := by
  set f : C ⊗[R] D →ₐ[R] C := Algebra.TensorProduct.lift (AlgHom.id R C)
    ((Algebra.ofId R C).comp ε) (fun _ _ => Commute.all _ _) with hfdef
  have hε : Function.Surjective ε := fun r => ⟨algebraMap R D r, AlgHom.commutes ε r⟩

  have hf : ∀ x, f x = Algebra.TensorProduct.rid R R C
      (Algebra.TensorProduct.map (AlgHom.id R C) ε x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
        simp only [hfdef, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
          Algebra.ofId_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul,
          Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  have hker : RingHom.ker f = (RingHom.ker ε).map
      (Algebra.TensorProduct.includeRight : D →ₐ[R] C ⊗[R] D) := by
    rw [← Algebra.TensorProduct.lTensor_ker ε hε]
    ext x
    rw [RingHom.mem_ker, RingHom.mem_ker, hf, map_eq_zero_iff _ (Algebra.TensorProduct.rid R R C).injective]

  have hI : RingHom.ker ε ≤ maximalIdeal D := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ε)
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le (R := R) D
  have hK : (RingHom.ker f) ^ N ≤ (maximalIdeal R).map (algebraMap R (C ⊗[R] D)) := by
    rw [hker, ← Ideal.map_pow]
    refine (Ideal.map_mono ((Ideal.pow_right_mono hI N).trans hN)).trans ?_
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have : (Algebra.TensorProduct.includeRight : D →ₐ[R] C ⊗[R] D) (algebraMap R D r) =
        algebraMap R (C ⊗[R] D) r := AlgHom.commutes _ r
    rw [this]
    exact Ideal.mem_map_of_mem _ hr

  intro x hx
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  have hcomap : (M.comap (algebraMap R (C ⊗[R] D))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) M
  have hle : (maximalIdeal R).map (algebraMap R (C ⊗[R] D)) ≤ M := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hcomap]
  exact hM.isPrime.mem_of_pow_mem N (hle (hK (Ideal.pow_mem_pow hx N)))

end E89C2

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {C : Type v} [CommRing C] [Algebra R C] [Module.Finite R C]
    {D : Type w} [CommRing D] [Algebra R D] [Module.Finite R D] [IsLocalRing D]
    (ε : D →ₐ[R] R) :
    RingHom.ker (Algebra.TensorProduct.lift (AlgHom.id R C) ((Algebra.ofId R C).comp ε)
        (fun _ _ => Commute.all _ _) : C ⊗[R] D →ₐ[R] C) ≤ Ideal.jacobson ⊥ :=
  E89C2.main ε

end S_Algebra_TensorProduct_ker_lift_le_jacobson_of_isLocalRing
end P2MW
export P2MW.S_Algebra_TensorProduct_ker_lift_le_jacobson_of_isLocalRing (solution)
