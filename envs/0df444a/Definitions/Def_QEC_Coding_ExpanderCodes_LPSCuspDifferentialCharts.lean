-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
-- name    : QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:20:42.37017+00:00
-- url     : https://prove2.me/theorems/c64ec420-169a-45fa-aac7-2bcbc3207fd6
-- title:
--   LPSCusp Differential Charts
-- statement:
--   Definitions and structural lemmas for LPSCusp Differential Charts, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferentialCharts.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section
def lpsCuspQDifferentialCoefficient (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (q : ℂ) : ℂ :=
  ((2:ℂ)*Real.pi*I)⁻¹*dslope (UpperHalfPlane.cuspFunction 1 f) 0 q
def lpsCuspTranslateQDifferentialCoefficient (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (q : ℂ) : ℂ :=
  (N:ℂ) / ((2:ℂ)*Real.pi*I) *
    dslope (UpperHalfPlane.cuspFunction (N:ℝ)
      ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ)) 0 q
end
end QEC.Coding.TannerLiftedProduct


