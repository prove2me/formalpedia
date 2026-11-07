-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:45:42.227203+00:00
-- url     : https://prove2.me/theorems/c1c70524-3083-4611-b9d1-adc1fe2c65cc
-- title:
--   LPSOriginal Differential Gluing
-- statement:
--   Definitions and structural lemmas for LPSOriginal Differential Gluing, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
def lpsOriginalFilledCoordinateCoefficient (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    LPSOriginalFilledCurve N → ℂ → ℂ :=
  Sum.elim (fun _ => (f : ℍ→ℂ)∘UpperHalfPlane.ofComplex)
    (fun c => lpsOriginalCuspQCoefficient N f (lpsOriginalCuspRepresentative N c))
end
end QEC.Coding.TannerLiftedProduct


