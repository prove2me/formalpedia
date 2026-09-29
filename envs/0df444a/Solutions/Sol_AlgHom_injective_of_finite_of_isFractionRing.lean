-- Prove2me | solution 1 for AlgHom.injective_of_finite_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/347f1923-4c3f-5085-9187-dca787f9daa4

import Mathlib
import Theorems.Thm_Algebra_trdeg_quotient_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_injective_of_finite_of_isFractionRing

set_option autoImplicit false

universe u

theorem solution {k A B K : Type u} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Field K] [Algebra k K] [Algebra A K] [IsFractionRing A K] [IsScalarTower k A K]
    [Algebra B K] [IsFractionRing B K] [IsScalarTower k B K]
    (φ : A →ₐ[k] B) (hφ : φ.toRingHom.Finite) : Function.Injective φ := by

  haveI : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  haveI : FaithfulSMul k B := (faithfulSMul_iff_algebraMap_injective k B).mpr (algebraMap k B).injective
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr (IsFractionRing.injective A K)
  haveI : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr (IsFractionRing.injective B K)
  have algAK : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have algBK : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
  have h1 := trdeg_add_eq k A (A := K)
  have h2 := trdeg_add_eq k B (A := K)
  rw [trdeg_eq_zero_iff.mpr algAK, add_zero] at h1
  rw [trdeg_eq_zero_iff.mpr algBK, add_zero] at h2
  have hAB : Algebra.trdeg k A = Algebra.trdeg k B := h1.trans h2.symm

  by_contra hnot
  set I : Ideal A := RingHom.ker φ.toRingHom with hIdef
  have hI : I ≠ ⊥ := by
    intro hbot
    apply hnot
    intro x y hxy
    have : x - y ∈ I := by rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, hxy, sub_self]
    rw [hbot, Ideal.mem_bot, sub_eq_zero] at this
    exact this
  have hI' : I ≠ ⊤ := RingHom.ker_ne_top φ.toRingHom
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI'

  letI algAB : Algebra A B := φ.toRingHom.toAlgebra
  haveI : Module.Finite A B := hφ
  letI : Algebra (A ⧸ I) B := (RingHom.kerLift φ.toRingHom).toAlgebra
  haveI : IsScalarTower A (A ⧸ I) B :=
    IsScalarTower.of_algebraMap_eq (fun a => (RingHom.kerLift_mk φ.toRingHom a).symm)
  haveI : IsScalarTower k (A ⧸ I) B := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap k B x = RingHom.kerLift φ.toRingHom (Ideal.Quotient.mk I (algebraMap k A x))
    rw [RingHom.kerLift_mk]
    exact (φ.commutes x).symm)
  haveI : FaithfulSMul (A ⧸ I) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ.toRingHom)
  haveI : FaithfulSMul k (A ⧸ I) :=
    (faithfulSMul_iff_algebraMap_injective k _).mpr (algebraMap k (A ⧸ I)).injective
  haveI : Module.Finite (A ⧸ I) B := Module.Finite.of_restrictScalars_finite A (A ⧸ I) B
  have algB : Algebra.IsAlgebraic (A ⧸ I) B := Algebra.IsIntegral.isAlgebraic
  have h3 := trdeg_add_eq k (A ⧸ I) (A := B)
  rw [trdeg_eq_zero_iff.mpr algB, add_zero] at h3
  have hlt : Algebra.trdeg k (A ⧸ I) < Algebra.trdeg k A := Algebra.trdeg_quotient_lt (K := k) I hI hI'
  rw [h3, ← hAB] at hlt
  exact lt_irrefl _ hlt

end S_AlgHom_injective_of_finite_of_isFractionRing
end P2MW
export P2MW.S_AlgHom_injective_of_finite_of_isFractionRing (solution)
