-- Prove2me | Definitions.Def_TC433_LinearAlgebra_BilinearForm_DualLattice_bca734aede
-- name    : TC433_LinearAlgebra_BilinearForm_DualLattice_bca734aede
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:11:03.424983+00:00
-- url     : https://prove2.me/theorems/2f8293a5-0202-4306-8c19-fa65cb07cf06
-- title:
--   TauCeti: LinearAlgebra / BilinearForm / DualLattice
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.LinearAlgebra.BilinearForm.DualLattice for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/LinearAlgebra/BilinearForm/DualLattice.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Definitions.Def_TC433_Algebra_Module_Lattice_a0302caa43

/-!
# Dual submodules of lattices

This file develops the duality theory for free full lattices in vector spaces equipped with a
nondegenerate bilinear form over a fraction field.

## Main declarations

* `LinearMap.BilinForm.dualSubmoduleToDual_surjective`: surjectivity of
  `dualSubmoduleToDual` for a free full lattice and nondegenerate bilinear form.
* `LinearMap.BilinForm.dualSubmoduleEquivDual`: the perfect linear equivalence
  `B.dualSubmodule N ≃ₗ[R] Module.Dual R N`.
* `LinearMap.BilinForm.dualSubmoduleEquivDual_apply`: evaluation of
  `dualSubmoduleEquivDual` is `B.dualSubmoduleToDual N`.
* `LinearMap.BilinForm.dualSubmodule_dualSubmodule_flip`: double duality for general
  full lattices using `B.flip`.
* `LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule`: double duality for general
  full lattices with `B.flip` on the outside.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open Module

namespace TauCeti

universe u

variable {R K V : Type*} [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [Module.IsTorsionFree R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- Surjectivity of Mathlib's canonical pairing `dualSubmoduleToDual` for a free full lattice
and a nondegenerate bilinear form. -/
theorem _root_.LinearMap.BilinForm.dualSubmoduleToDual_surjective
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    Function.Surjective (B.dualSubmoduleToDual N) := by
  intro f
  let b := Module.Free.chooseBasis R N
  let b_ext := b.extendOfIsLattice K
  let bd := B.dualBasis hB b_ext
  let x : V := ∑ i, (algebraMap R K (f (b i))) • bd i
  have hx : x ∈ B.dualSubmodule N := by
    rw [← b.span_range_extendOfIsLattice, B.dualSubmodule_span_of_basis hB b_ext]
    exact Submodule.sum_mem _ fun i _ => by
      simpa only [algebraMap_smul] using
        Submodule.smul_mem _ (f (b i)) (Submodule.subset_span (Set.mem_range_self i))
  refine ⟨⟨x, hx⟩, ?_⟩
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨i, rfl⟩
  apply FaithfulSMul.algebraMap_injective R K
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply,
    LinearMap.BilinForm.dualSubmoduleParing_spec]
  have hform (j) : B (bd j) ((b i : N) : V) = if i = j then 1 else 0 := by
    calc
      B (bd j) ((b i : N) : V) = B (bd j) (b_ext i) := by
        rw [Basis.extendOfIsLattice_apply K b i]
      _ = _ := B.apply_dualBasis_left hB b_ext j i
  dsimp only [Submodule.coe_mk]
  have hx_eq : x = ∑ j, (algebraMap R K (f (b j))) • bd j := rfl
  rw [hx_eq, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [hform, Algebra.smul_def]
  · intro j _ hji
    simp [hform, Ne.symm hji]
  · simp

/-- The canonical pairing between the dual submodule of a free full lattice and the lattice
itself is a linear equivalence over `R` whenever the ambient bilinear form is nondegenerate. -/
noncomputable def _root_.LinearMap.BilinForm.dualSubmoduleEquivDual
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [hN : N.IsLattice K] [Module.Free R N] :
    B.dualSubmodule N ≃ₗ[R] Module.Dual R N :=
  LinearEquiv.ofBijective (B.dualSubmoduleToDual N)
    ⟨B.dualSubmoduleToDual_injective hB N hN.span_eq_top,
      LinearMap.BilinForm.dualSubmoduleToDual_surjective B hB N⟩

/-- The underlying linear map of `dualSubmoduleEquivDual` is `B.dualSubmoduleToDual N`. -/
@[simp]
theorem _root_.LinearMap.BilinForm.dualSubmoduleEquivDual_apply
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [N.IsLattice K] [Module.Free R N] (x : B.dualSubmodule N) :
    LinearMap.BilinForm.dualSubmoduleEquivDual B hB N x = B.dualSubmoduleToDual N x :=
  LinearEquiv.ofBijective_apply (B.dualSubmoduleToDual N) x

omit [IsDomain R] [Module.IsTorsionFree R K] in
/-- Dualizing by `B.flip` and then by `B` recovers the original free full lattice. -/
theorem _root_.LinearMap.BilinForm.dualSubmodule_dualSubmodule_flip
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    B.dualSubmodule (B.flip.dualSubmodule N) = N := by
  let b := Module.Free.chooseBasis R N
  let b_ext := b.extendOfIsLattice K
  calc
    B.dualSubmodule (B.flip.dualSubmodule N) =
        B.dualSubmodule (B.flip.dualSubmodule (Submodule.span R (Set.range b_ext))) :=
      congrArg (fun S => B.dualSubmodule (B.flip.dualSubmodule S))
        b.span_range_extendOfIsLattice.symm
    _ = Submodule.span R (Set.range b_ext) :=
      B.dualSubmodule_dualSubmodule_flip_of_basis hB b_ext
    _ = N := b.span_range_extendOfIsLattice

omit [IsDomain R] [Module.IsTorsionFree R K] in
/-- Dualizing by `B` and then by `B.flip` recovers the original free full lattice. -/
theorem _root_.LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (N : Submodule R V) [N.IsLattice K] [Module.Free R N] :
    B.flip.dualSubmodule (B.dualSubmodule N) = N := by
  have h := LinearMap.BilinForm.dualSubmodule_dualSubmodule_flip B.flip hB.flip N
  have hflip : B.flip.flip = B := by ext; rfl
  rwa [hflip] at h

end TauCeti


