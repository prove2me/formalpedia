-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:26:58.598381+00:00
-- url     : https://prove2.me/theorems/36d28d26-27d3-4e02-859d-3141d1fd4bcc
-- title:
--   LPSOriginal Native Differential Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Native Differential Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNativeDifferentialComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicKaehlerRegularity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Modular
attribute [local instance] originalNativeGlobalComplexModule
def lpsOriginalNativeH0HolomorphicLinearEquiv :
    Γ(lpsOriginalComplexNormalDifferentialSheaf N hpos, ⊤) ≃ₗ[ℂ]
      LPSOriginalHolomorphicCovectorSections N hN :=
  (lpsOriginalNativeH0RegularCovectorLinearEquiv N hpos hN).trans
    (lpsOriginalHolomorphicRegularKaehlerLinearEquiv N hpos hN).symm
def lpsOriginalNativeH0CuspFormLinearEquiv :
    Γ(lpsOriginalComplexNormalDifferentialSheaf N hpos, ⊤) ≃ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact (lpsOriginalNativeH0HolomorphicLinearEquiv N hpos hN).trans
    (lpsOriginalFilledDifferentialLinearEquiv N hN).symm
end
end QEC.Coding.TannerLiftedProduct


