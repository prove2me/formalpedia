-- Prove2me | solution 1 for AlgHom.bijective_and_torsionBySet_eq_smul_of_length_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ca459d4f-1f32-5959-a642-296336e14dd8

import Theorems.Thm_AlgHom_bijective_and_exists_presentation_of_length_cotangent_le
import Theorems.Thm_AlgHom_length_quotient_congruenceIdeal_le_length_cotangent
import Theorems.Thm_Module_length_quotient_torsionBySet_sup_le
import Theorems.Thm_Module_length_quotient_torsionBySet_sup_eq_iff
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_bijective_and_torsionBySet_eq_smul_of_length_le

set_option autoImplicit false

universe u v w x

namespace M4cP4NCMOD2

theorem finrank_ne_zero_of_ne_bot {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪]
    [IsPrincipalIdealRing 𝒪] [CommRing T] [Algebra 𝒪 T]
    {M : Type x} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M] (N : Submodule T M) (hN : N ≠ ⊥) :
    Module.finrank 𝒪 N ≠ 0 := by
  intro h0
  let e : N ≃ₗ[𝒪] N.restrictScalars 𝒪 :=
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => ⟨p.1, p.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hP0 : Module.finrank 𝒪 (N.restrictScalars 𝒪) = 0 := by rw [← e.finrank_eq]; exact h0
  have hP : Subsingleton (N.restrictScalars 𝒪) := Module.finrank_zero_iff.mp hP0
  apply hN
  rw [Submodule.eq_bot_iff]
  intro n hn
  have : (⟨n, hn⟩ : N.restrictScalars 𝒪) = 0 := Subsingleton.elim _ _
  exact congrArg Subtype.val this

end M4cP4NCMOD2

theorem solution
    {𝒪 : Type u} {R : Type v} {T : Type w}
    [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Algebra 𝒪 R]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (hM : Submodule.torsionBySet T M ↑(RingHom.ker πT) ≠ ⊥)
    (hle : (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (RingHom.ker πR).Cotangent ≤
      Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator))) :
    Function.Bijective φ ∧
      (∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T)) ∧
      Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤ := by
  have h1a := Module.length_quotient_torsionBySet_sup_le πT hη M
  have h1b := Module.length_quotient_torsionBySet_sup_eq_iff πT hη M
  have hineq := AlgHom.length_quotient_congruenceIdeal_le_length_cotangent φ hφ πR πT hπ
    (IsNoetherian.noetherian (RingHom.ker πR))
  have hd0 : ((Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ) : ℕ∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (M4cP4NCMOD2.finrank_ne_zero_of_ne_bot _ hM)
  have hΩ := le_antisymm h1a ((mul_le_mul_right hineq _).trans hle)
  have hle' := (ENat.mul_le_mul_left_iff hd0 (ENat.coe_ne_top _)).mp (hle.trans h1a)
  obtain ⟨hbij, hpres⟩ :=
    AlgHom.bijective_and_exists_presentation_of_length_cotangent_le φ hφ πR πT hπ hη hle'
  exact ⟨hbij, hpres, h1b.mp hΩ⟩

end S_AlgHom_bijective_and_torsionBySet_eq_smul_of_length_le
end P2MW
export P2MW.S_AlgHom_bijective_and_torsionBySet_eq_smul_of_length_le (solution)
