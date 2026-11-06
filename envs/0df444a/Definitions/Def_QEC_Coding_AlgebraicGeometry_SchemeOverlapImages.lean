-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_SchemeOverlapImages
-- name    : QEC_Coding_AlgebraicGeometry_SchemeOverlapImages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:01:27.879203+00:00
-- url     : https://prove2.me/theorems/8967526a-0cd5-438a-a439-27804d69ef98
-- title:
--   Scheme Overlap Images
-- statement:
--   Definitions and structural lemmas for Scheme Overlap Images, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/SchemeOverlapImages.lean

import Mathlib.AlgebraicGeometry.Gluing
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
local instance schemeGlueOverlapOpenImmersion (D : Scheme.GlueData.{u}) (i j : D.J) :
    IsOpenImmersion (D.f i j) := D.f_open i j
end
end QEC.Coding.AlgebraicGeometry


