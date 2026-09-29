-- Prove2me | solution 1 for AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/38ec0f19-1dcb-5cd2-95f7-af2557cbbb73

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace P2mFlfDescAF

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

theorem hmono {T : Scheme.{u}} (a b : T ⟶ pullback p p)
    (h₁ : a ≫ pullback.fst p p = b ≫ pullback.fst p p) (h₂ : a ≫ pullback.snd p p = b ≫ pullback.snd p p) :
    a = b :=
  pullback.hom_ext h₁ h₂

theorem rel_iff {T : Scheme.{u}} (x y : T ⟶ X) :
    (∃ φ : T ⟶ pullback p p, φ ≫ pullback.fst p p = x ∧ φ ≫ pullback.snd p p = y) ↔ x ≫ p = y ≫ p := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  · intro h
    exact ⟨pullback.lift x y h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem hequiv (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ X =>
      ∃ φ : T ⟶ pullback p p, φ ≫ pullback.fst p p = x ∧ φ ≫ pullback.snd p p = y := by
  constructor
  · intro x
    exact (rel_iff p x x).2 rfl
  · intro x y h
    exact (rel_iff p y x).2 ((rel_iff p x y).1 h).symm
  · intro x y z h h'
    exact (rel_iff p x z).2 (((rel_iff p x y).1 h).trans ((rel_iff p y z).1 h'))

end P2mFlfDescAF

open P2mFlfDescAF in
theorem solution
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (S : Finset Y) (W : X.Opens) (hW : IsAffineOpen W) (hSW : ∀ x : X, p.base x ∈ S → x ∈ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ ∀ y ∈ S, y ∈ V := by
  classical

  have hfin : (p.base ⁻¹' (S : Set Y)).Finite := p.finite_preimage S.finite_toSet

  obtain ⟨W', hW'aff, hSW', -, hinv⟩ :=
    AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst p p) (pullback.snd p p) (hequiv p) hfin hW (fun x hx r hr => by
        apply hSW
        have hc : p.base ((pullback.snd p p).base r) = p.base ((pullback.fst p p).base r) := by
          change (pullback.snd p p ≫ p).base r = (pullback.fst p p ≫ p).base r
          rw [pullback.condition]
        rw [hc]
        have hr' : (pullback.fst p p).base r = x := hr
        rw [hr']
        exact hx)

  obtain ⟨V, hV, hpV⟩ :=
    AlgebraicGeometry.Scheme.exists_isAffineOpen_preimage_eq_of_invariant (pullback.fst p p) (pullback.snd p p)
      (fun a b h₁ h₂ => hmono p a b h₁ h₂) (hequiv p) p pullback.condition (IsPullback.of_hasPullback p p)
      W' hW'aff hinv
  refine ⟨V, hV, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := p.surjective y
  have hx : x ∈ (W' : Set X) := hSW' (show x ∈ p.base ⁻¹' (S : Set Y) from hy)
  have hx' : x ∈ p ⁻¹ᵁ V := by rw [hpV]; exact hx
  exact hx'

end S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective (solution)
