-- Prove2me | solution 1 for AlgHom.length_cotangent_mul_eq_length_quotient_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/222e40b7-0247-5791-baa2-72234bfebf04

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorems.Thm_AlgHom_length_cotangent_eq_of_exists_presentation
import Theorems.Thm_Module_length_quotient_torsionBySet_sup_eq_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_length_cotangent_mul_eq_length_quotient_of_free

universe u v w x

namespace FrobDictPAIR

section Transport

variable {𝒪 : Type u} [CommRing 𝒪] {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra 𝒪 A] [Algebra 𝒪 B]

theorem length_cotangent_comp_equiv (E : A ≃ₐ[𝒪] B) (πB : B →ₐ[𝒪] 𝒪) :
    Module.length 𝒪 (RingHom.ker (πB.comp (E : A →ₐ[𝒪] B))).Cotangent =
      Module.length 𝒪 (RingHom.ker πB).Cotangent := by
  set πA : A →ₐ[𝒪] 𝒪 := πB.comp (E : A →ₐ[𝒪] B) with hπA
  have hA : ∀ x, x ∈ RingHom.ker πA ↔ E x ∈ RingHom.ker πB := fun x => by
    simp only [RingHom.mem_ker, hπA, AlgHom.comp_apply, AlgEquiv.coe_algHom]
  have h12 : RingHom.ker πA ≤ (RingHom.ker πB).comap (E : A →ₐ[𝒪] B) := fun x hx => (hA x).mp hx
  have h21 : RingHom.ker πB ≤ (RingHom.ker πA).comap (E.symm : B →ₐ[𝒪] A) := fun y hy => by
    change E.symm y ∈ RingHom.ker πA
    rw [hA, AlgEquiv.apply_symm_apply]
    exact hy
  let L₁ := (RingHom.ker πA).mapCotangent (RingHom.ker πB) (E : A →ₐ[𝒪] B) h12
  let L₂ := (RingHom.ker πB).mapCotangent (RingHom.ker πA) (E.symm : B →ₐ[𝒪] A) h21
  have h₁ : L₂.comp L₁ = LinearMap.id := by
    apply LinearMap.ext
    intro m
    obtain ⟨x, rfl⟩ := (RingHom.ker πA).toCotangent_surjective m
    rw [LinearMap.comp_apply, LinearMap.id_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    congr 1
    apply Subtype.ext
    exact E.symm_apply_apply x
  have h₂ : L₁.comp L₂ = LinearMap.id := by
    apply LinearMap.ext
    intro m
    obtain ⟨y, rfl⟩ := (RingHom.ker πB).toCotangent_surjective m
    rw [LinearMap.comp_apply, LinearMap.id_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    congr 1
    apply Subtype.ext
    exact E.apply_symm_apply y
  exact (LinearEquiv.ofLinear L₁ L₂ h₂ h₁).length_eq

end Transport

section Saturation

variable {T : Type w} [CommRing T] (℘ : Ideal T) (M : Type x) [AddCommGroup M] [Module T M]

theorem torsionBySet_eq_annihilator_smul_top_of_free [Module.Free T M] :
    Submodule.torsionBySet T M ↑℘ = ℘.annihilator • (⊤ : Submodule T M) := by
  apply le_antisymm
  · intro m hm
    rw [Submodule.mem_torsionBySet_iff] at hm
    let c := Module.Free.chooseBasis T M
    have hrepr : ∀ k, c.repr m k ∈ ℘.annihilator := by
      intro k
      rw [Submodule.mem_annihilator]
      intro p hp
      have h0 : c.repr (p • m) k = 0 := by rw [hm ⟨p, hp⟩]; simp
      have h1 : p * c.repr m k = 0 := by simpa [map_smul, Finsupp.smul_apply, smul_eq_mul] using h0
      simpa [mul_comm] using h1
    rw [← c.linearCombination_repr m, Finsupp.linearCombination_apply, Finsupp.sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (hrepr k) Submodule.mem_top
  · rw [Submodule.smul_le]
    intro i hi m _
    rw [Submodule.mem_torsionBySet_iff]
    rintro ⟨p, hp⟩
    change p • i • m = 0
    have hip : i * p = 0 := Submodule.mem_annihilator.mp hi p hp
    rw [← mul_smul, mul_comm, hip]
    exact zero_smul _ _

end Saturation

end FrobDictPAIR

open FrobDictPAIR in
theorem solution
    {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {R : Type v} [CommRing R] [Algebra 𝒪 R]
    {T : Type w} [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Bijective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (hCI : ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T))
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M] [Module.Free T M] :
    (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (RingHom.ker πR).Cotangent =
      Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) := by

  have hΦ : Module.length 𝒪 (RingHom.ker πR).Cotangent = Module.length 𝒪 (RingHom.ker πT).Cotangent := by
    have h := length_cotangent_comp_equiv (AlgEquiv.ofBijective φ hφ) πT
    have hcomp : πT.comp ((AlgEquiv.ofBijective φ hφ : R ≃ₐ[𝒪] T) : R →ₐ[𝒪] T) = πR := by
      rw [← hπ]; rfl
    rw [hcomp] at h
    exact h

  rw [hΦ, AlgHom.length_cotangent_eq_of_exists_presentation πT hCI]
  exact ((Module.length_quotient_torsionBySet_sup_eq_iff πT hη M).mpr
    (torsionBySet_eq_annihilator_smul_top_of_free (RingHom.ker πT) M)).symm

end S_AlgHom_length_cotangent_mul_eq_length_quotient_of_free
end P2MW
export P2MW.S_AlgHom_length_cotangent_mul_eq_length_quotient_of_free (solution)
