-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:18:44.774231+00:00
-- url     : https://prove2.me/theorems/a02c6ec3-70d7-4fb5-9540-3cb6e64e9532
-- title:
--   LPSOriginal Reciprocal E4 Equation
-- statement:
--   Definitions and structural lemmas for LPSOriginal Reciprocal E4 Equation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalMeromorphicE4PowerAtLevel (N k : ℕ) :
    LPSOriginalMeromorphicLevelForm N k :=
  let D : ModularForm 𝒮ℒ ((k : ℤ)*12) :=
    (lpsOriginalE4CubePower k).mcast (by ring)
  let hle : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
    intro g hg
    obtain ⟨γ, hγ, he⟩ := hg
    exact ⟨γ, he⟩
  { toFun := D
    slash_action_eq' g hg := D.slash_action_eq' g (hle hg)
    holo' := D.holo'
    bdd_at_cusps' hc := D.bdd_at_cusps' (hc.mono hle) }
def lpsOriginalReciprocalE4NormalizedEquation
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    Polynomial (Polynomial ℂ) :=
  Polynomial.C (Polynomial.C (((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N))⁻¹)) *
    lpsOriginalMeromorphicRatioEquation N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k)
def lpsOriginalReciprocalE4MonicEquation
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    Polynomial (Polynomial ℂ) :=
  QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients
    (k * Nat.card (LPSOriginalMeromorphicCosets N))
    (lpsOriginalReciprocalE4NormalizedEquation N k A)
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "P" => Polynomial ℂ
def lpsOriginalE4PowerHolomorphic (k : ℕ) : R :=
  ⟨lpsOriginalE4CubePower k, ModularFormClass.holo (lpsOriginalE4CubePower k)⟩
def lpsOriginalLevelFormHolomorphic (N k : ℕ)
    (A : LPSOriginalMeromorphicLevelForm N k) : R :=
  ⟨A, ModularFormClass.holo A⟩
end
end QEC.Coding.TannerLiftedProduct


