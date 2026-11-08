-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroDifferentialLattice
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalZeroDifferentialLattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T12:30:51.520095+00:00
-- url     : https://prove2.me/theorems/caf59b54-862a-44df-a702-417b55792901
-- title:
--   LPSOriginal Zero Differential Lattice
-- statement:
--   Definitions and structural lemmas for LPSOriginal Zero Differential Lattice, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroDifferentialLattice.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
attribute [local instance]
  LPSOriginalLocalKaehlerFinitenessDictionary001
  LPSOriginalLocalKaehlerFinitenessDictionary002
  LPSOriginalLocalKaehlerFinitenessDictionary003
  LPSOriginalLocalKaehlerFinitenessDictionary004
  LPSOriginalLocalKaehlerFinitenessDictionary005
  LPSOriginalLocalKaehlerFinitenessDictionary006
  LPSOriginalLocalKaehlerFinitenessDictionary007
  LPSOriginalLocalKaehlerFinitenessDictionary008
  LPSOriginalLocalKaehlerFinitenessDictionary009
  LPSOriginalLocalKaehlerFinitenessDictionary010
  LPSOriginalLocalKaehlerFinitenessDictionary011
  LPSOriginalLocalKaehlerFinitenessDictionary012
  LPSOriginalLocalKaehlerFinitenessDictionary013
  LPSOriginalLocalKaehlerFinitenessDictionary014
  LPSOriginalLocalKaehlerFinitenessDictionary015
  LPSOriginalLocalKaehlerFinitenessDictionary016
  LPSOriginalLocalKaehlerFinitenessDictionary017
  LPSOriginalLocalKaehlerFinitenessDictionary018
def lpsOriginalZeroDifferentialCoefficientMap : KaehlerDifferential ℂ R →ₗ[P] K :=
  ((lpsOriginalGenericKaehlerCoefficientEquiv N hpos).restrictScalars P).toLinearMap.comp
    ((KaehlerDifferential.map ℂ ℂ R K).restrictScalars P)
end
end QEC.Coding.TannerLiftedProduct


