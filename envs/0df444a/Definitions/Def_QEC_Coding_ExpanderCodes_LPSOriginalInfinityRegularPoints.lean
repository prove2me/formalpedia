-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:56:05.316272+00:00
-- url     : https://prove2.me/theorems/cc9ac19e-026e-4c29-b29c-13934c707b11
-- title:
--   LPSOriginal Infinity Regular Points
-- statement:
--   Definitions and structural lemmas for LPSOriginal Infinity Regular Points, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityRegularPoints.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalInfinityRegularPointsDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local instance LPSOriginalInfinityRegularPointsDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalInfinityRegularPointsDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalInfinityRegularPointsDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
def lpsOriginalInfinityRegularPoints : Type :=
  {x : LPSOriginalFilledCurve N // 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
    (algebraMap P K Polynomial.X)⁻¹}
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
def lpsOriginalInfinityPolynomialChartMap : P →+* R := by
  letI : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
  exact algebraMap P R
def lpsOriginalInfinityCoordinate (x : S) : ℂ :=
  lpsOriginalInfinityNormalChartEvaluation N hpos hN x.val x.property
    (lpsOriginalInfinityPolynomialChartMap N hpos Polynomial.X)
end
end QEC.Coding.TannerLiftedProduct


