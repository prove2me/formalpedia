-- Prove2me | Definitions.Def_HatAffineConstantRows_ConstantRows
-- name    : HatAffineConstantRows_ConstantRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:07:59.655649+00:00
-- url     : https://prove2.me/theorems/bb436345-8f65-4ccb-bf7a-596d92ce45e1
-- title:
--   Constant Rows
-- statement:
--   Definitions and structural lemmas for Constant Rows, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/Lean/HatAffineConstantRows/ConstantRows.lean

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
set_option autoImplicit true
open scoped BigOperators
namespace HatAffineConstantRows
universe u v
open Finset
open MvPolynomial
def AffineRealizes
    {K : Type u} [Semiring K] {m : Nat} {I : Type v}
    (A : I → Fin m → K) (b : I → K)
    (F : (Fin m → K) → I → K) : Prop :=
  ∀ y i, F y i = (∑ j, A i j * y j) + b i
noncomputable def linearForm
    {K : Type u} [CommRing K] {m : Nat}
    (a : Fin m → K) : MvPolynomial (Fin m) K :=
  ∑ j, C (a j) * X j
noncomputable def affineObstructionFactor
    {K : Type u} [CommRing K] {m : Nat} {I : Type v}
    (A : I → Fin m → K) (b x : I → K) (i : I) :
    MvPolynomial (Fin m) K :=
  linearForm (A i) + C (b i - x i)
noncomputable def affineObstruction
    {K : Type u} [CommRing K] {m : Nat} {I : Type v} [Fintype I]
    (A : I → Fin m → K) (b x : I → K) : MvPolynomial (Fin m) K := by
  classical
  exact ∏ i, affineObstructionFactor A b x i
noncomputable def rowSeparatingOffset
    {K : Type u} [Field K] {m : Nat} {I : Type v}
    (A : I → Fin m → K) (b : I → K) : I → K := by
  classical
  exact fun i => if A i = 0 then b i + 1 else b i
noncomputable def rowDegree
    {K : Type u} [Field K] {m : Nat}
    (a : Fin m → K) : Nat := by
  classical
  exact if a = 0 then 0 else 1
noncomputable def nonzeroRowCount
    {K : Type u} [Field K] {m : Nat} {I : Type v} [Fintype I]
    (A : I → Fin m → K) : Nat := by
  classical
  exact (Finset.univ.filter fun i => A i ≠ 0).card
end HatAffineConstantRows


