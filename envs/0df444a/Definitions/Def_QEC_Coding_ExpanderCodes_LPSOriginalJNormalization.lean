-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:52:04.235209+00:00
-- url     : https://prove2.me/theorems/07a420d8-0faf-4dd3-a65d-8d4e97ea7758
-- title:
--   LPSOriginal JNormalization
-- statement:
--   Definitions and structural lemmas for LPSOriginal JNormalization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalFilledJReciprocal (N : ℕ) (a : ℂ) : LPSOriginalFilledCurve N → ℂ :=
  Sum.elim (fun y => (lpsOriginalJQuotient N y-a)⁻¹) (fun _ => 0)
end
end QEC.Coding.TannerLiftedProduct


