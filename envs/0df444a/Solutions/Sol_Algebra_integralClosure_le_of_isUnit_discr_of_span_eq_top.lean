-- Prove2me | solution 1 for Algebra.integralClosure_le_of_isUnit_discr_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7ea8a5f5-d652-5c66-bc48-956e46901b5f

import Mathlib
import Theorems.Thm_Algebra_isIntegral_trace_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open Matrix
open scoped nonZeroDivisors

namespace Algebra
p2m_export "Algebra" "isIntegral_iff trace algebraMap discr_def mem_top traceMatrix_of_basis_mulVec algebraMapSubmonoid IsIntegral.isIntegral smul_def traceMatrix discr traceMatrix_localizationLocalization isIntegral_trace_of_finiteDimensional"
namespace IntegralClosureLeOfIsUnitDiscr
p2m_open "Algebra"

variable {R : Type*} [CommRing R] [IsDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]

theorem isLocalization_of_span_eq_top (S : Subalgebra R A)
    (hS : Submodule.span K ((S : Subalgebra R A) : Set A) = ⊤) :
    IsLocalization (Algebra.algebraMapSubmonoid S R⁰) A := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, r, hr, rfl⟩
    have hr0 : (r : R) ≠ 0 := nonZeroDivisors.ne_zero hr
    have : algebraMap S A (algebraMap R S r) = algebraMap K A (algebraMap R K r) := by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [this]
    exact ((IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr hr0 |> isUnit_iff_ne_zero.mpr).map _
  · intro a
    have ha : a ∈ Submodule.span K ((S : Subalgebra R A) : Set A) := by rw [hS]; exact Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha => exact ⟨⟨⟨a, ha⟩, 1⟩, by simp⟩
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | add a a' _ _ iha iha' =>
      obtain ⟨⟨s, m, hm⟩, h⟩ := iha
      obtain ⟨⟨s', m', hm'⟩, h'⟩ := iha'
      refine ⟨⟨m' * s + m * s', ⟨m * m', mul_mem hm hm'⟩⟩, ?_⟩
      simp only [map_mul, map_add] at h h' ⊢
      rw [← h, ← h']
      ring
    | smul k a _ iha =>
      obtain ⟨⟨s, m, hm⟩, h⟩ := iha
      obtain ⟨⟨n, d⟩, hk⟩ := IsLocalization.surj R⁰ k

      refine ⟨⟨algebraMap R S n * s, ⟨algebraMap R S d * m, mul_mem ⟨d, d.2, rfl⟩ hm⟩⟩, ?_⟩
      simp only at h ⊢
      rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply R S A, ← IsScalarTower.algebraMap_apply R S A,
        IsScalarTower.algebraMap_apply R K A, IsScalarTower.algebraMap_apply R K A,
        show k • a * (algebraMap K A (algebraMap R K d) * algebraMap S A m) =
          algebraMap K A (k * algebraMap R K d) * (a * algebraMap S A m) by
            rw [Algebra.smul_def, map_mul]; ring,
        hk, h]
  · intro a a' h
    exact ⟨1, by simpa using Subtype.val_injective h⟩

end Algebra.IntegralClosureLeOfIsUnitDiscr

open Algebra.IntegralClosureLeOfIsUnitDiscr in
theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [FiniteDimensional K A]
    (S : Subalgebra R A) (hS : Submodule.span K ((S : Subalgebra R A) : Set A) = ⊤)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (hdisc : IsUnit (Algebra.discr R b)) :
    integralClosure R A ≤ S := by
  classical
  intro x hx
  rw [mem_integralClosure_iff] at hx
  haveI : Module.Finite R S := Module.Finite.of_basis b
  haveI : Module.Free R S := Module.Free.of_basis b
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) A := isLocalization_of_span_eq_top S hS

  let bK : Module.Basis ι K A := b.localizationLocalization K R⁰ A
  have hbK : ∀ i, bK i = ((b i : S) : A) := fun i => Module.Basis.localizationLocalization_apply K R⁰ A b i

  have htr : ∀ j, ∃ r : R, algebraMap R K r = Algebra.trace K A (x * bK j) := by
    intro j
    refine IsIntegrallyClosed.isIntegral_iff.mp ?_
    refine Algebra.isIntegral_trace_of_finiteDimensional (hx.mul ?_)
    rw [hbK]
    exact (Algebra.IsIntegral.isIntegral (R := R) (b j)).map (IsScalarTower.toAlgHom R S A)
  choose t ht using htr

  set TR : Matrix ι ι R := Algebra.traceMatrix R b with hTRdef
  set TK : Matrix ι ι K := Algebra.traceMatrix K bK with hTKdef
  have hTK : TK = (algebraMap R K).mapMatrix TR := Algebra.traceMatrix_localizationLocalization R R⁰ A b
  have hdetR : IsUnit TR.det := by rwa [hTRdef, ← Algebra.discr_def]
  have hdetK : IsUnit TK.det := by
    rw [hTK, ← RingHom.map_det]
    exact hdetR.map _

  have hmul : TK *ᵥ (bK.equivFun x) = fun j => algebraMap R K (t j) := by
    rw [hTKdef, Algebra.traceMatrix_of_basis_mulVec]
    ext j
    exact (ht j).symm

  let cR : ι → R := TR⁻¹ *ᵥ t
  have hTc : TR *ᵥ cR = t := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetR, Matrix.one_mulVec]
  have hmap : TK *ᵥ (fun i => algebraMap R K (cR i)) = fun j => algebraMap R K (t j) := by
    rw [hTK, RingHom.mapMatrix_apply]
    ext j
    rw [show (fun i => algebraMap R K (cR i)) = algebraMap R K ∘ cR from rfl, ← RingHom.map_mulVec, hTc]
  have hcoord : bK.equivFun x = fun i => algebraMap R K (cR i) := by
    have h1 := congrArg (fun w => TK⁻¹ *ᵥ w) (hmul.trans hmap.symm)
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetK, Matrix.one_mulVec] using h1

  rw [← bK.sum_equivFun x, hcoord]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [hbK, algebraMap_smul, ← Subalgebra.coe_smul]
  exact (cR i • b i).2

end S_Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top
end P2MW
export P2MW.S_Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top (solution)
