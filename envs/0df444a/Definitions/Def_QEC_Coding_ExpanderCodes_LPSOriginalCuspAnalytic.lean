-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:38:16.949066+00:00
-- url     : https://prove2.me/theorems/d1a2cfaf-8a72-4f16-8c71-fc4c10967066
-- title:
--   LPSOriginal Cusp Analytic
-- statement:
--   Definitions and structural lemmas for LPSOriginal Cusp Analytic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspAnalytic.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
end
end QEC.Coding.TannerLiftedProduct


