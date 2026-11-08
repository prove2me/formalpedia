-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:30:42.817098+00:00
-- url     : https://prove2.me/theorems/7fd3c2dc-037b-4559-a2c3-88a2ccebebe8
-- title:
--   LPSOriginal Rational Chart Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Rational Chart Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
set_option autoImplicit false
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
noncomputable section
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
def lpsOriginalRatFuncToJ : RatFunc ℂ ≃ₐ[ℂ] J :=
  (IsLocalization.algEquiv (nonZeroDivisors P) (RatFunc ℂ) J).restrictScalars ℂ
variable (N : ℕ) (hpos : 0 < N)
local instance _p2m_local_instance_3d79f03ea9_67 : Algebra J LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local instance _p2m_local_instance_3d79f03ea9_70 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_3d79f03ea9_71 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_3d79f03ea9_72 : IsScalarTower P J K := .of_algebraMap_eq' rfl
local instance _p2m_local_instance_3d79f03ea9_73 : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl
@[reducible] def lpsOriginalRatFuncAlgebra : Algebra (RatFunc ℂ) K :=
  ((algebraMap J K).comp lpsOriginalRatFuncToJ.toRingHom).toAlgebra
local instance _p2m_local_instance_3d79f03ea9_77 : Algebra (RatFunc ℂ) K := lpsOriginalRatFuncAlgebra N hpos
variable [NeZero N]
end
end QEC.Coding.TannerLiftedProduct


