-- Prove2me | Definitions.Def_HatAffineGenericCore_G2
-- name    : HatAffineGenericCore_G2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:06:26.101891+00:00
-- url     : https://prove2.me/theorems/07fe2836-37fd-4894-97d6-9246e5a5759b
-- title:
--   G2
-- statement:
--   Definitions and structural lemmas for G2, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/Lean/HatAffineGenericCore/G2.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators MonomialOrder
namespace HatAffineGenericCore
universe u
open Finset
open MvPolynomial
noncomputable def puncturedValues {K : Type u} [Fintype K] (g : K) : Finset K := by
  classical
  exact Finset.univ.erase g
noncomputable def puncturedSet {K : Type u} [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) : Finset K :=
  puncturedValues (g j)
noncomputable def puncturedGrid {K : Type u} [CommRing K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) : MvPolynomial (Fin m) K :=
  ∏ x ∈ puncturedSet g j, (X j - C x)
noncomputable def puncturedPower {K : Type u} [CommRing K] [Fintype K] {m : Nat}
    (g : Fin m → K) (j : Fin m) : MvPolynomial (Fin m) K :=
  (X j - C (g j)) ^ (Fintype.card K - 1) - 1
end HatAffineGenericCore


