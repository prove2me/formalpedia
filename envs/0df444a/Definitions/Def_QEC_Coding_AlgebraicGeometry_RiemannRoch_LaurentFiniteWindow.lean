-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:02:51.421204+00:00
-- url     : https://prove2.me/theorems/54c7d09e-9eeb-440f-a8c4-8057fbcd7728
-- title:
--   Laurent Finite Window
-- statement:
--   Definitions and structural lemmas for Laurent Finite Window, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/LaurentFiniteWindow.lean

import Mathlib
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
noncomputable def directCoordinate : k[X] →ₐ[k] LaurentPolynomial k :=
  Polynomial.toLaurentAlg
noncomputable def inverseCoordinate : k[X] →ₐ[k] LaurentPolynomial k :=
  (LaurentPolynomial.invert (R := k)).toAlgHom.comp Polynomial.toLaurentAlg
def laurentWindow (lower upper : ℤ) : Submodule k (LaurentPolynomial k) where
  carrier := {f | f.coeff.support ⊆ Finset.Icc lower upper}
  zero_mem' := by
    change (∅ : Finset ℤ) ⊆ Finset.Icc lower upper
    exact Finset.empty_subset _
  add_mem' := by
    intro f g hf hg
    exact Finsupp.support_add.trans (Finset.union_subset hf hg)
  smul_mem' := by
    intro c f hf
    exact Finsupp.support_smul.trans hf
noncomputable def laurentWindowFamily (lower upper : ℤ) : Finset (LaurentPolynomial k) :=
  by
    classical
    exact (Finset.Icc lower upper).image (fun n : ℤ => LaurentPolynomial.T (R := k) n)
def directScaledLocus (a : k[X]) : Set (LaurentPolynomial k) :=
  {z | ∃ p : k[X], directCoordinate k a * z = directCoordinate k p}
def inverseScaledLocus (b : k[X]) : Set (LaurentPolynomial k) :=
  {z | ∃ q : k[X], inverseCoordinate k b * z = inverseCoordinate k q}
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow


