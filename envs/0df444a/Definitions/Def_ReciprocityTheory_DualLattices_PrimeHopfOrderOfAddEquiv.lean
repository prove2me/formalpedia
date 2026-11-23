-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
-- name    : ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:26.327835+00:00
-- url     : https://prove2.me/theorems/d1c5f21d-4811-42c4-bf2b-5db1658712c5
-- title:
--   Prime Hopf Order Of Add Equiv
-- statement:
--   Definitions and structural lemmas for Prime Hopf Order Of Add Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PrimeHopfOrderOfAddEquiv.lean

import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section Transport
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]
abbrev pbE (e : X ≃+ Y) : (Y → C) ≃ₗ[R] (X → C) := LinearEquiv.funCongrLeft R C e.toEquiv
lemma pbE_apply (e : X ≃+ Y) (f : Y → C) (x : X) : pbE (C := C) (R := R) e f x = f (e x) := rfl
lemma pbE_symm_apply (e : X ≃+ Y) (f : X → C) (y : Y) :
    (pbE (C := C) (R := R) e).symm f y = f (e.symm y) := by
  rfl
lemma det_sub (e : X ≃+ Y) (B : Matrix Y Y C) : (B.submatrix e e).det = B.det :=
  Matrix.det_submatrix_equiv_self e.toEquiv B
lemma map_cols (e : X ≃+ Y) (B : Matrix Y Y C) :
    (Submodule.span R (Set.range fun j y => B y j)).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      Submodule.span R (Set.range fun j x => (B.submatrix e e) x j) := by
  rw [Submodule.map_span, ← Set.range_comp]
  have h : (fun j x => (B.submatrix e e) x j) =
      ((pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) ∘ fun j y => B y j) ∘ e := by
    funext j x
    rfl
  rw [h, e.surjective.range_comp]
def hopfPull (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) : HopfOrder (C := C) R X where
  carrier := A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))
  lat := by
    obtain ⟨B, hB, hA⟩ := A.lat
    exact ⟨B.submatrix e e, by rwa [det_sub], by rw [hA, map_cols]⟩
  le_int := by
    intro f hf
    rw [Submodule.mem_map_equiv] at hf
    have h := A.le_int hf
    intro x
    obtain ⟨r, hr⟩ := h (e x)
    exact ⟨r, by rw [hr, pbE_symm_apply, AddEquiv.symm_apply_apply]⟩
  one_mem := by
    rw [Submodule.mem_map_equiv]
    convert A.one_mem using 1
    funext y
    simp [pbE_symm_apply]
  mul_mem := fun f g hf hg => by
    rw [Submodule.mem_map_equiv] at hf hg ⊢
    convert A.mul_mem _ _ hf hg using 1
    funext y
    simp only [pbE_symm_apply, Pi.mul_apply]
  comul := by
    intro f hf
    rw [Submodule.mem_map_equiv] at hf
    set g := (pbE (C := C) (R := R) e).symm f with hg
    have hfg : f = pbE (C := C) (R := R) e g := by rw [hg, LinearEquiv.apply_symm_apply]
    let pb2 : (Y × Y → C) →ₗ[R] (X × X → C) :=
      LinearMap.funLeft R C (fun q : X × X => (e q.1, e q.2))
    have h1 : addPull R X f = pb2 (addPull R Y g) := by
      funext q
      rw [hfg]
      simp only [addPull, pb2, LinearMap.funLeft_apply, pbE_apply, map_add]
    rw [h1]
    have h2 := A.comul g hf
    have h3 : (tensorSpan R A.carrier).map pb2 ≤ tensorSpan R (A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
      rw [tensorSpan, Submodule.map_span_le]
      rintro F ⟨g1, hg1, h1', hh1, rfl⟩
      exact Submodule.subset_span ⟨pbE (C := C) (R := R) e g1, Submodule.mem_map_of_mem hg1,
        pbE (C := C) (R := R) e h1', Submodule.mem_map_of_mem hh1, rfl⟩
    exact h3 (Submodule.mem_map_of_mem h2)
  antipode := fun f hf => by
    rw [Submodule.mem_map_equiv] at hf ⊢
    convert A.antipode _ hf using 1
    funext y
    simp only [pbE_symm_apply, map_neg]
end Transport
end ReciprocityTheory.PGsh.Up


