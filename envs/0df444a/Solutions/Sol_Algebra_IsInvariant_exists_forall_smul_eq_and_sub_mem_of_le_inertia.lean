-- Prove2me | solution 1 for Algebra.IsInvariant.exists_forall_smul_eq_and_sub_mem_of_le_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1007d5e1-d730-5bb8-b704-d637fb5fb1a7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsInvariant_exists_forall_smul_eq_and_sub_mem_of_le_inertia

set_option autoImplicit false

open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

theorem residueFixed_algebraMap_quotient_surjective_of_forall_smul_sub_mem
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)]
    (hG : ∀ (g : G) (b : B), g • b - b ∈ Q) :
    Function.Surjective (algebraMap (A ⧸ P) (B ⧸ Q)) := by
  haveI : IsGalois (A ⧸ P) (B ⧸ Q) := { __ := Ideal.Quotient.normal (A := A) G P Q }
  haveI : FiniteDimensional (A ⧸ P) (B ⧸ Q) := Ideal.Quotient.finite_of_isInvariant G P Q
  intro x
  have hx : x ∈ Set.range (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    obtain ⟨g, rfl⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q f
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq.mpr (hG g b)
  exact hx

theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]
    [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)]
    (H : Subgroup G) (hH : H ≤ Q.inertia G) (b : B) :
    ∃ b' : B, (∀ h ∈ H, h • b' = b') ∧ b - b' ∈ Q := by
  let B' : Subalgebra A B := FixedPoints.subalgebra A B H
  haveI : SMulCommClass H B' B := ⟨fun h x y => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    exact congrArg (· * h • y) (x.2 h)⟩
  haveI : Algebra.IsInvariant B' B H := ⟨fun x hx => ⟨⟨x, hx⟩, rfl⟩⟩
  haveI : Algebra.IsIntegral B' B := Algebra.IsInvariant.isIntegral B' B H
  haveI : (Q.under B').IsMaximal := Ideal.IsMaximal.under B' Q
  haveI : IsScalarTower (A ⧸ P) (B' ⧸ Q.under B') (B ⧸ Q) :=
    IsScalarTower.of_algebraMap_eq (Quotient.ind fun x ↦ rfl)
  haveI : Algebra.IsSeparable (B' ⧸ Q.under B') (B ⧸ Q) :=
    Algebra.isSeparable_tower_top_of_isSeparable (A ⧸ P) (B' ⧸ Q.under B') (B ⧸ Q)
  have hH' : ∀ (h : H) (x : B), h • x - x ∈ Q := fun h x => hH h.2 x
  obtain ⟨y, hy⟩ := residueFixed_algebraMap_quotient_surjective_of_forall_smul_sub_mem
    (Q.under B') Q hH' (Ideal.Quotient.mk Q b)
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨b', fun h hh => b'.2 ⟨h, hh⟩, ?_⟩
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at hy
  exact Ideal.Quotient.eq.mp hy.symm

end S_Algebra_IsInvariant_exists_forall_smul_eq_and_sub_mem_of_le_inertia
end P2MW
export P2MW.S_Algebra_IsInvariant_exists_forall_smul_eq_and_sub_mem_of_le_inertia (solution)
