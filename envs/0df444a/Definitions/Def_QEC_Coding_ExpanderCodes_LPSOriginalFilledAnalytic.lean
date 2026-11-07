-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:57:40.683434+00:00
-- url     : https://prove2.me/theorems/ffd47c98-e59f-468c-8ee1-8fb8108d635f
-- title:
--   LPSOriginal Filled Analytic
-- statement:
--   Definitions and structural lemmas for LPSOriginal Filled Analytic, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
end
end QEC.Coding.TannerLiftedProduct


