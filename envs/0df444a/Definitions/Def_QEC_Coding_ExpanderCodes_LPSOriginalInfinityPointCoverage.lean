-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPointCoverage
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalInfinityPointCoverage
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:17:13.596724+00:00
-- url     : https://prove2.me/theorems/e623b8b0-8e73-4db3-8a72-9eb412ad095a
-- title:
--   LPSOriginal Infinity Point Coverage
-- statement:
--   Definitions and structural lemmas for LPSOriginal Infinity Point Coverage, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityPointCoverage.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPoleClearingAway
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_PolynomialMaximalPoints
import Mathlib.RingTheory.Ideal.GoingUp
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.PolynomialMaximalPoints
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalInfinityPointCoverageDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance LPSOriginalInfinityPointCoverageDictionary002 : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
end
end QEC.Coding.TannerLiftedProduct


