-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
-- name    : QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:15:40.251459+00:00
-- url     : https://prove2.me/theorems/0cc3e983-97d7-4419-a725-9392b4dc1ca5
-- title:
--   LPSPetersson Measure
-- statement:
--   Definitions and structural lemmas for LPSPetersson Measure, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonMeasure.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
end
end QEC.Coding.TannerLiftedProduct


