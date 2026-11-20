-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaHecke
-- name    : QEC_Coding_ExpanderCodes_LPSThetaHecke
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:23:01.303218+00:00
-- url     : https://prove2.me/theorems/7966b104-4807-4efe-b9f6-15a43471e3ba
-- title:
--   LPSTheta Hecke
-- statement:
--   Definitions and structural lemmas for LPSTheta Hecke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaHecke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_coprime_thetaLevel

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
noncomputable def lpsThetaHeckePrimePower (p : ℕ) (a : LPSResiduePrime p) (r : ℕ) :
    CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) : Subgroup (GL (Fin 2) ℝ)) 2 := by
  letI : Fact p.Prime := ⟨a.degreePrime⟩
  have hNp : p.Coprime ((4*a.q)^2) := by
    convert a.coprime_thetaLevel using 1
    ring
  exact lpsHeckePrimePowerLinearMap ((4*a.q)^2) p hNp r
    (lpsThetaCuspidalRemainder a.q a.modFour)
end QEC.Coding.TannerLiftedProduct


