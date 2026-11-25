-- Prove2me | Definitions.Def_MatrixTreeLib_MatrixTree
-- name    : MatrixTreeLib_MatrixTree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:50:38.496877+00:00
-- url     : https://prove2.me/theorems/85305f3d-f26e-5822-a08a-535e9e7ad63d
-- title:
--   Matrix Tree
-- statement:
--   Definitions and structural lemmas for Matrix Tree, from Juan Pablo Traverso Gianini (jtraverso/matrix-tree; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Cauchy-Binet formula, Kirchhoff's matrix-tree theorem and Cayley's formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/matrix-tree/blob/aeab0f267c523dd3cac9a287b589f65a99d20d01/MatrixTreeLib/MatrixTree.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Matrix Finset
namespace MatrixTree
section Incidence
variable {V : Type*}
noncomputable def tl (e : Sym2 V) : V := (Quot.out e).1
noncomputable def hd (e : Sym2 V) : V := (Quot.out e).2
variable [DecidableEq V]
noncomputable def inc (e : Sym2 V) (x : V) : ℤ :=
  if x = tl e then 1 else if x = hd e then -1 else 0
end Incidence
section Key
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def incMat (v : V) (g : {u // u ≠ v} → Sym2 V) :
    Matrix {u // u ≠ v} {u // u ≠ v} ℤ :=
  Matrix.of fun u w => inc (g w) u
end Key
end MatrixTree


