-- Prove2me | Definitions.Def_HatAffineGenericCore_G3A
-- name    : HatAffineGenericCore_G3A
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:06:21.146245+00:00
-- url     : https://prove2.me/theorems/14977ded-1c91-5e9f-b462-f058ce1e2d86
-- title:
--   G3 A
-- statement:
--   Definitions and structural lemmas for G3 A, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/Lean/HatAffineGenericCore/G3A.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
namespace HatAffineGenericCore
universe u
open Finset
open MvPolynomial
noncomputable def linearForm {K : Type u} [CommRing K] {m : Nat}
    (a : Fin m → K) : MvPolynomial (Fin m) K :=
  ∑ j, C (a j) * X j
noncomputable def diagonalForm {K : Type u} [CommRing K] [Fintype K] {m : Nat}
    (lambda : Fin m → K) : MvPolynomial (Fin m) K :=
  ∑ j, C (lambda j) * X j ^ (Fintype.card K - 1)
noncomputable def coeffSupport {K : Type u} [Zero K] {m : Nat}
    (a : Fin m → K) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => a j ≠ 0)
end HatAffineGenericCore


