-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
-- name    : QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:22:30.422682+00:00
-- url     : https://prove2.me/theorems/22df3819-5acd-49a9-a105-0945ae3edcc9
-- title:
--   LPSTheta Rankin Density
-- statement:
--   Definitions and structural lemmas for LPSTheta Rankin Density, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
def lpsThetaRankinDensity (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (τ : ℍ) : ℝ :=
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  lpsCuspPeterssonDensity ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) τ
def lpsThetaRankinMass (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) : ℝ :=
  ∫τ in ModularGroup.fd,lpsThetaRankinDensity q hq4 τ
end
end QEC.Coding.TannerLiftedProduct


