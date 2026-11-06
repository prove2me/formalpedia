-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalRecursionOrders
-- name    : QEC_Coding_AlgebraicGeometry_Towers_RationalRecursionOrders
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:08:29.269103+00:00
-- url     : https://prove2.me/theorems/c2003793-3f8e-4a95-91c8-901e167daee5
-- title:
--   Rational Recursion Orders
-- statement:
--   Definitions and structural lemmas for Rational Recursion Orders, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalRecursionOrders.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Mathlib.FieldTheory.RatFunc.AsPolynomial
set_option autoImplicit false
open IntermediateField
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
section SourceBasicRationalPlaces
open scoped BigOperators
local instance sourceBasicRationalF256CharTwo : CharP F256 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
attribute [local instance] sourceBasicRationalF256CharTwo
end SourceBasicRationalPlaces
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


