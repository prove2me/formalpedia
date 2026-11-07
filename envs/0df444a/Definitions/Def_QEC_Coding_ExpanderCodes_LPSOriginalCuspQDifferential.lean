-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:39:58.295092+00:00
-- url     : https://prove2.me/theorems/da4184f6-33ba-439c-8768-e33b982eee32
-- title:
--   LPSOriginal Cusp QDifferential
-- statement:
--   Definitions and structural lemmas for LPSOriginal Cusp QDifferential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspQDifferential.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
def lpsOriginalCuspQCoefficient (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (q : ℂ) : ℂ :=
  ((lpsOriginalCuspGroup N ρ).strictWidthInfty:ℂ) / ((2:ℂ)*Real.pi*I) *
    dslope (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
      ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ)) 0 q
end
end QEC.Coding.TannerLiftedProduct


