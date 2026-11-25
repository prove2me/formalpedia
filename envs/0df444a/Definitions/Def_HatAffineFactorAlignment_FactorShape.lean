-- Prove2me | Definitions.Def_HatAffineFactorAlignment_FactorShape
-- name    : HatAffineFactorAlignment_FactorShape
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:06:46.428999+00:00
-- url     : https://prove2.me/theorems/f0f00966-ab36-5be3-ac4b-421f57ff4c5c
-- title:
--   Factor Shape
-- statement:
--   Definitions and structural lemmas for Factor Shape, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/Lean/HatAffineFactorAlignment/FactorShape.lean

import Definitions.Def_HatAffineGenericCore_G3A
set_option autoImplicit true
open scoped BigOperators
namespace HatAffineFactorAlignment
universe u
open Finset
open MvPolynomial
open HatAffineGenericCore
noncomputable def GenericTypeI
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (lambda : Fin m → K) : Prop :=
  ∃ (r : Fin m)
      (alpha : Fin (Fintype.card K - 1) → K)
      (mu : K),
    mu ≠ 0 ∧
    (∀ i, alpha i ≠ 0) ∧
    (∀ i, A i = fun j => if j = r then alpha i else 0) ∧
    lambda = fun j => if j = r then mu else 0
noncomputable def GenericTypeIIShape
    {K : Type u} [Field K] [Fintype K] {m : Nat}
    (A : Fin (Fintype.card K - 1) → Fin m → K)
    (lambda : Fin m → K) : Prop :=
  ∃ (u v : Fin m)
      (alpha c : Fin (Fintype.card K - 1) → K)
      (mu : K),
    u ≠ v ∧
    mu ≠ 0 ∧
    (∀ i, alpha i ≠ 0) ∧
    (∀ i, c i ≠ 0) ∧
    (∀ i, A i = fun j =>
      if j = u then alpha i
      else if j = v then -alpha i * c i
      else 0) ∧
    lambda = fun j =>
      if j = u then mu
      else if j = v then -mu
      else 0
end HatAffineFactorAlignment


