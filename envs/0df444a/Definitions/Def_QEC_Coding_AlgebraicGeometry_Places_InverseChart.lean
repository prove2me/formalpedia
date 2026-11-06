-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
-- name    : QEC_Coding_AlgebraicGeometry_Places_InverseChart
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:41:13.4515+00:00
-- url     : https://prove2.me/theorems/b58c106b-1d2f-445f-b83f-c683e1c52dff
-- title:
--   Inverse Chart
-- statement:
--   Definitions and structural lemmas for Inverse Chart, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseChart.lean

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.NumberTheory.FunctionField
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace InverseChart
open scoped IntermediateField Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k k⟮X⟯ F]
variable [_root_.FunctionField k F]
noncomputable def coordinate : F := algebraMap k⟮X⟯ F RatFunc.X
noncomputable def inverseCoordinate : F := (coordinate k F)⁻¹
theorem coordinate_transcendental : Transcendental k (coordinate k F) := by
  apply (transcendental_algebraMap_iff (algebraMap k⟮X⟯ F).injective).mpr
  exact RatFunc.transcendental_X
theorem inverseCoordinate_transcendental :
    Transcendental k (inverseCoordinate k F) := by
  intro h
  apply coordinate_transcendental k F
  apply IsAlgebraic.inv_iff.mp
  simpa only [inverseCoordinate] using h
noncomputable def rationalEquiv :
    RatFunc k ≃ₐ[k] k⟮(inverseCoordinate k F)⟯ :=
  RatFunc.algEquivOfTranscendental (inverseCoordinate k F)
    (inverseCoordinate_transcendental k F)
noncomputable def rationalMap : RatFunc k →ₐ[k] F :=
  (k⟮(inverseCoordinate k F)⟯).val.comp
    (rationalEquiv k F).toAlgHom
noncomputable def polynomialMap : k[X] →+* F :=
  (rationalMap k F).toRingHom.comp (algebraMap k[X] (RatFunc k))
@[reducible] noncomputable def polynomialAlgebra : Algebra k[X] F :=
  (polynomialMap k F).toAlgebra
end InverseChart
end QEC.Coding.AlgebraicGeometry


