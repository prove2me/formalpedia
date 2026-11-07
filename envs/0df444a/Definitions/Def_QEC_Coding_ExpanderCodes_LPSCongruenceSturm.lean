-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
-- name    : QEC_Coding_ExpanderCodes_LPSCongruenceSturm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:18:31.162191+00:00
-- url     : https://prove2.me/theorems/e729fdc6-438d-44da-8add-a6c09c34ad0c
-- title:
--   LPSCongruence Sturm
-- statement:
--   Definitions and structural lemmas for LPSCongruence Sturm, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
end QEC.Coding.TannerLiftedProduct


