-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroPointCoverage
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalZeroPointCoverage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:59:59.255238+00:00
-- url     : https://prove2.me/theorems/75339318-3252-40f0-9ac3-5196797856dc
-- title:
--   LPSOriginal Zero Point Coverage
-- statement:
--   Definitions and structural lemmas for LPSOriginal Zero Point Coverage, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroPointCoverage.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_PolynomialMaximalPoints
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPoleClearingAway
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Mathlib.RingTheory.Ideal.GoingUp
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance lpsOriginalZeroCoverageDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance lpsOriginalZeroCoverageDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance lpsOriginalZeroCoverageDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance lpsOriginalZeroCoverageDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
end
end QEC.Coding.TannerLiftedProduct


