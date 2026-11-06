-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
-- name    : QEC_Coding_AlgebraicGeometry_Places_AffinePlace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:08:07.548368+00:00
-- url     : https://prove2.me/theorems/5724006b-3e9b-49ca-aaaf-411943091f68
-- title:
--   Affine Place
-- statement:
--   Definitions and structural lemmas for Affine Place, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlace.lean

import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
namespace AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
abbrev carrier : Type _ :=
  IsDedekindDomain.HeightOneSpectrum (_root_.FunctionField.ringOfIntegers k F)
abbrev residueField (P : carrier k F) : Type _ := P.asIdeal.ResidueField
noncomputable def valuation (P : carrier k F) : Valuation F ℤᵐ⁰ := P.valuation F
noncomputable def residue (P : carrier k F) :
    _root_.FunctionField.ringOfIntegers k F →+ residueField k F P :=
  (algebraMap (_root_.FunctionField.ringOfIntegers k F) (residueField k F P)).toAddMonoidHom
end AffinePlace
end QEC.Coding.AlgebraicGeometry


