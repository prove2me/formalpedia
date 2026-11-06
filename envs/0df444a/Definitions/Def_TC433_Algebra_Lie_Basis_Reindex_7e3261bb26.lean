-- Prove2me | Definitions.Def_TC433_Algebra_Lie_Basis_Reindex_7e3261bb26
-- name    : TC433_Algebra_Lie_Basis_Reindex_7e3261bb26
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T15:19:40.865908+00:00
-- url     : https://prove2.me/theorems/7fd039a6-1bca-4d40-ac73-665f7b34d6aa
-- title:
--   TauCeti: Algebra / Lie / Basis / Reindex
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.Lie.Basis.Reindex for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/Lie/Basis/Reindex.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basis.Basic

/-!
# Renumbering the nodes of a Lie algebra basis

A `LieAlgebra.Basis ι H` is a Chevalley-style presentation of a Lie algebra: a Cartan matrix
indexed by `ι`, three families `h`, `e`, `f` of elements indexed by `ι`, and the relations between
them. Nothing in the structure depends on which index type is used, so a bijection `ι ≃ ι'`
transports the whole package.

This is what lets a construction whose index set arises from the construction itself — Geck's, for
instance, whose nodes are the support of a base, a subtype of the root index type — be read against
an index type fixed in advance, such as `Fin n` in a pinned Bourbaki numbering. The Cartan matrix
is renumbered by `Matrix.submatrix`, so the entry at renumbered nodes is by definition the entry at
the corresponding original nodes and no reindexed copy of the matrix has to be compared with the
original one.

## Main definitions

* `LieAlgebra.Basis.reindex`: the basis obtained by renumbering the nodes along a bijection.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open Function Set

namespace LieAlgebra.Basis

variable {ι ι' R L : Type*} [Finite ι] [Finite ι']
  [CommRing R] [LieRing L] [LieAlgebra R L] {H : LieSubalgebra R L}

/-- **Renumber the nodes of a Lie algebra basis along a bijection.** The Cartan matrix is
renumbered by `Matrix.submatrix`, and each of the three families of elements is precomposed with
the bijection. -/
def reindex (b : Basis ι H) (σ : ι ≃ ι') : Basis ι' H where
  A := b.A.submatrix σ.symm σ.symm
  h := b.h ∘ σ.symm
  e := b.e ∘ σ.symm
  f := b.f ∘ σ.symm
  cartan_eq_lieSpan := by
    rw [σ.symm.surjective.range_comp]
    exact b.cartan_eq_lieSpan
  span_ef := by
    rw [σ.symm.surjective.range_comp, σ.symm.surjective.range_comp]
    exact b.span_ef
  linInd := b.linInd.comp σ.symm σ.symm.injective
  nondegen := by
    classical
    let _ := Fintype.ofFinite ι
    let _ := Fintype.ofFinite ι'
    rw [Matrix.nondegenerate_iff_det_ne_zero, Matrix.det_submatrix_equiv_self,
      ← Matrix.nondegenerate_iff_det_ne_zero]
    exact b.nondegen
  sl2 i := b.sl2 (σ.symm i)
  lie_h_h i j := b.lie_h_h (σ.symm i) (σ.symm j)
  lie_h_e i j := b.lie_h_e (σ.symm i) (σ.symm j)
  lie_h_f i j := b.lie_h_f (σ.symm i) (σ.symm j)
  lie_e_f_ne i j hij :=
    b.lie_e_f_ne (σ.symm i) (σ.symm j) fun h => hij (σ.symm.injective h)

/-- Reindexing transports the Cartan matrix along the given equivalence. -/
@[simp] theorem reindex_A (b : Basis ι H) (σ : ι ≃ ι') :
    (b.reindex σ).A = b.A.submatrix σ.symm σ.symm := by rfl

/-- Reindexing precomposes the Cartan generators with the given equivalence. -/
@[simp] theorem reindex_h (b : Basis ι H) (σ : ι ≃ ι') :
    (b.reindex σ).h = b.h ∘ σ.symm := by rfl

/-- Reindexing precomposes the raising generators with the given equivalence. -/
@[simp] theorem reindex_e (b : Basis ι H) (σ : ι ≃ ι') :
    (b.reindex σ).e = b.e ∘ σ.symm := by rfl

/-- Reindexing precomposes the lowering generators with the given equivalence. -/
@[simp] theorem reindex_f (b : Basis ι H) (σ : ι ≃ ι') :
    (b.reindex σ).f = b.f ∘ σ.symm := by rfl

end LieAlgebra.Basis


