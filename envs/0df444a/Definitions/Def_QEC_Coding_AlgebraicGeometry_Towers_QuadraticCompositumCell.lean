-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
-- name    : QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:07:39.342267+00:00
-- url     : https://prove2.me/theorems/33868522-073a-4cb0-8ecc-ae08b065c30a
-- title:
--   Quadratic Compositum Cell
-- statement:
--   Definitions and structural lemmas for Quadratic Compositum Cell, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticCompositumCell.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalNormalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_TrivialFieldExtension
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
set_option autoImplicit false
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
section IntegralModels
variable (A B C D K L E : Type*)
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [_root_.Field K] [_root_.Field L] [_root_.Field E]
    [IsDomain A] [IsLocalRing A]
    [IsDedekindDomain B] [IsDedekindDomain C] [IsDedekindDomain D]
    [Algebra F256 K] [Algebra F256 L] [Algebra F256 E]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra A C] [Algebra.IsIntegral A C] [Module.IsTorsionFree A C]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra B C] [Algebra C L] [IsFractionRing C L] [IsScalarTower B C L]
    [IsIntegralClosure C B L] [Module.IsTorsionFree B C]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    [Algebra C E] [IsScalarTower C L E]
    [Algebra C D] [Algebra D E] [IsScalarTower C D E]
    [IsIntegralClosure D C E] [Module.IsTorsionFree C D]
    [FiniteDimensional L E] [Algebra.IsSeparable L E]
    [Module.IsTorsionFree C E]
end IntegralModels
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


