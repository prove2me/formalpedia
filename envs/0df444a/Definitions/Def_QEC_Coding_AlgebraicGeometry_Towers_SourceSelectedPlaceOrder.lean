-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaceOrder
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaceOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:47:29.24729+00:00
-- url     : https://prove2.me/theorems/5ffc001b-0a77-4f2a-bc5c-5fe13b61d39c
-- title:
--   Source Selected Place Order
-- statement:
--   Definitions and structural lemmas for Source Selected Place Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSelectedPlaceOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitOrder
set_option autoImplicit false
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
noncomputable def sourceSelectedSplitPolynomial : Polynomial F256 :=
  (Polynomial.X ^ 16 + Polynomial.X) ^ 15 - 1
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


