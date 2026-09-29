-- Prove2me | solution 1 for Algebra.FormallyUnramified.of_forall_isAlgClosed_formallyUnramified_tensorProduct_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c2ad913b-27b6-5f51-aa61-031c9d2cdf57

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_FormallyUnramified_of_forall_isAlgClosed_formallyUnramified_tensorProduct_map

set_option autoImplicit false

universe u

open TensorProduct

namespace Alpha1rSol

theorem subsingleton_baseChange_kaehler
    {S : Type u} [CommRing S] {A B : Type u} [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] [Algebra A B] [IsScalarTower S A B]
    (k : Type u) [Field k] [Algebra S k]
    (h : (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S A B) (AlgHom.id S k)).toRingHom.FormallyUnramified) :
    Subsingleton ((B ⊗[S] k) ⊗[B] Ω[B⁄A]) := by
  let f := Algebra.TensorProduct.map (IsScalarTower.toAlgHom S A B) (AlgHom.id S k)
  letI : Algebra (A ⊗[S] k) (B ⊗[S] k) := f.toRingHom.toAlgebra
  haveI : IsScalarTower A (A ⊗[S] k) (B ⊗[S] k) :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := A ⊗[S] k) (A := B ⊗[S] k) (fun a => by
    rw [RingHom.algebraMap_toAlgebra]
    show algebraMap A (B ⊗[S] k) a = f (algebraMap A (A ⊗[S] k) a)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    show algebraMap A B a ⊗ₜ[S] (1 : k) = f (a ⊗ₜ 1)
    rw [Algebra.TensorProduct.map_tmul]
    rfl)
  haveI : Algebra.IsPushout A (A ⊗[S] k) B (B ⊗[S] k) := by
    refine (Algebra.IsPushout.tensorProduct_tensorProduct S k A B ?_).symm
    ext x
    show f ((1 : A) ⊗ₜ[S] x) = (1 : B) ⊗ₜ[S] x
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  haveI : Algebra.FormallyUnramified (A ⊗[S] k) (B ⊗[S] k) := h
  haveI : Subsingleton Ω[(B ⊗[S] k)⁄(A ⊗[S] k)] := Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  exact (KaehlerDifferential.tensorKaehlerEquiv A (A ⊗[S] k) B (B ⊗[S] k)).toEquiv.subsingleton

theorem subsingleton_tensor_of_subsingleton_baseChange
    {S : Type u} [CommRing S] {B : Type u} [CommRing B] [Algebra S B]
    (k : Type u) [Field k] [Algebra S k] [Algebra B k] [IsScalarTower S B k]
    (M : Type*) [AddCommGroup M] [Module B M] [h : Subsingleton ((B ⊗[S] k) ⊗[B] M)] :
    Subsingleton (k ⊗[B] M) := by
  let ψ : B ⊗[S] k →ₐ[S] k := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S B k) (AlgHom.id S k)
    (fun _ _ => Commute.all _ _)
  letI : Algebra (B ⊗[S] k) k := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower B (B ⊗[S] k) k :=
    IsScalarTower.of_algebraMap_eq (R := B) (S := B ⊗[S] k) (A := k) (fun b => by
    rw [RingHom.algebraMap_toAlgebra]
    show algebraMap B k b = ψ (b ⊗ₜ 1)
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl)
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⊗[S] k) k k M).symm.toEquiv.subsingleton

theorem subsingleton_tensor_of_field_ext
    {B : Type u} [CommRing B] (κ : Type u) [Field κ] [Algebra B κ] (k : Type u) [Field k] [Algebra κ k] [Algebra B k]
    [IsScalarTower B κ k] (M : Type*) [AddCommGroup M] [Module B M] [h : Subsingleton (k ⊗[B] M)] :
    Subsingleton (κ ⊗[B] M) := by
  haveI : Subsingleton (k ⊗[κ] (κ ⊗[B] M)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B κ k k M).toEquiv.subsingleton
  exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right κ k).mp this

theorem not_mem_support_of_subsingleton_quotient_tensor
    {B : Type u} [CommRing B] (M : Type*) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (m : Ideal B) [hm : m.IsMaximal] [h : Subsingleton ((B ⧸ m) ⊗[B] M)] :
    (⟨m, hm.isPrime⟩ : PrimeSpectrum B) ∉ Module.support B M := by
  have hsub : Subsingleton (M ⧸ (m • (⊤ : Submodule B M))) :=
    (TensorProduct.quotTensorEquivQuotSMul M m).symm.toEquiv.subsingleton
  have htop : m • (⊤ : Submodule B M) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact (Submodule.Quotient.mk_eq_zero _).mp (Subsingleton.elim _ _)
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m (⊤ : Submodule B M)
    Module.Finite.fg_top (by rw [htop])
  rw [Module.mem_support_iff_of_finite]
  intro hle
  have hrann : r ∈ Module.annihilator B M := by
    rw [Module.mem_annihilator]
    intro x; exact hr x trivial
  have hrm : r ∈ m := hle hrann
  have : (1 : B) ∈ m := by
    have := m.sub_mem hrm hr1
    rwa [sub_sub_cancel] at this
  exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr this)

end Alpha1rSol

open Alpha1rSol in
theorem solution
    {S : Type u} [CommRing S] {A B : Type u} [CommRing A] [CommRing B]
    [Algebra S A] [Algebra S B] [Algebra A B] [IsScalarTower S A B] [Algebra.FiniteType S B]
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra S k],
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S A B) (AlgHom.id S k)).toRingHom.FormallyUnramified) :
    Algebra.FormallyUnramified A B := by
  classical
  haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType S A B
  haveI : Module.Finite B Ω[B⁄A] := inferInstance
  suffices hs : Subsingleton Ω[B⁄A] from ⟨hs⟩
  rw [← Module.support_eq_empty_iff (R := B), Set.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  haveI := hm
  have hmsupp : (⟨m, hm.isPrime⟩ : PrimeSpectrum B) ∈ Module.support B Ω[B⁄A] := Module.mem_support_mono hpm hp

  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Subsingleton ((B ⊗[S] AlgebraicClosure (B ⧸ m)) ⊗[B] Ω[B⁄A]) :=
    subsingleton_baseChange_kaehler (AlgebraicClosure (B ⧸ m)) (h (AlgebraicClosure (B ⧸ m)))
  haveI : Subsingleton (AlgebraicClosure (B ⧸ m) ⊗[B] Ω[B⁄A]) :=
    subsingleton_tensor_of_subsingleton_baseChange (S := S) (AlgebraicClosure (B ⧸ m)) Ω[B⁄A]
  haveI : Subsingleton ((B ⧸ m) ⊗[B] Ω[B⁄A]) := subsingleton_tensor_of_field_ext (B ⧸ m) (AlgebraicClosure (B ⧸ m)) Ω[B⁄A]
  exact not_mem_support_of_subsingleton_quotient_tensor Ω[B⁄A] m hmsupp

end S_Algebra_FormallyUnramified_of_forall_isAlgClosed_formallyUnramified_tensorProduct_map
end P2MW
export P2MW.S_Algebra_FormallyUnramified_of_forall_isAlgClosed_formallyUnramified_tensorProduct_map (solution)
