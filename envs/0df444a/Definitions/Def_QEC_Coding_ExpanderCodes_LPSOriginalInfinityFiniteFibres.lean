-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:00:58.175848+00:00
-- url     : https://prove2.me/theorems/e8b36fc3-fc32-4897-bcae-c81db212a476
-- title:
--   LPSOriginal Infinity Finite Fibres
-- statement:
--   Definitions and structural lemmas for LPSOriginal Infinity Finite Fibres, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityFiniteFibres.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityRegularPoints
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance LPSOriginalInfinityFiniteFibresDictionary001 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance LPSOriginalInfinityFiniteFibresDictionary002 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance LPSOriginalInfinityFiniteFibresDictionary003 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance LPSOriginalInfinityFiniteFibresDictionary004 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
local notation "C" => CuspOrbits
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
end
end QEC.Coding.TannerLiftedProduct


