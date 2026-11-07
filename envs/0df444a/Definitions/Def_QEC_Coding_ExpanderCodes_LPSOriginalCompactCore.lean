-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:36:47.215392+00:00
-- url     : https://prove2.me/theorems/a2ce62bf-3e94-4fe8-9250-bfee944950d7
-- title:
--   LPSOriginal Compact Core
-- statement:
--   Definitions and structural lemmas for LPSOriginal Compact Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
def lpsOriginalGamma0CosetRepresentative (N : ℕ)
    (x : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : SL(2,ℤ) := x.out⁻¹
def lpsOriginalGamma0Projected (N : ℕ) (ρ : SL(2,ℤ)) (τ : ℍ) :
    MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ :=
  ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧
def lpsOriginalGamma0CompactCore (N : ℕ) (Y : ℝ) :
    Set (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :=
  ⋃ x : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    lpsOriginalGamma0Projected N (lpsOriginalGamma0CosetRepresentative N x) ''
      ModularGroup.truncatedFundamentalDomain Y
end
end QEC.Coding.TannerLiftedProduct


