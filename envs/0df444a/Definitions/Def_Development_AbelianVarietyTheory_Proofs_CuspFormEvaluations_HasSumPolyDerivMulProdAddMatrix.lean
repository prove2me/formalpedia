-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:43:39.204876+00:00
-- url     : https://prove2.me/theorems/72ee4ec3-693b-5e5b-93b9-94cf1c01d12c
-- title:
--   Has Sum Poly Deriv Mul Prod Add Matrix
-- statement:
--   Definitions and structural lemmas for Has Sum Poly Deriv Mul Prod Add Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasSumPolyDerivMulProdAddMatrix.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemThetaDomainIffIsSiegelAddTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMulDotProductLeOfIsCompactThetaDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnThetaProdOfNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
namespace GlobalTheory.CanTh
section Operators
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
end Operators
variable {g : ℕ}
def thTerm (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (ζ : Fin g → ℂ) (m : Fin g → ℤ) : ℂ :=
  cexp (π * I * (((fun i => (m i : ℂ)) + fun i => (a i : ℂ)) ⬝ᵥ
      τ *ᵥ ((fun i => (m i : ℂ)) + fun i => (a i : ℂ))) +
    2 * π * I * (((fun i => (m i : ℂ)) + fun i => (a i : ℂ)) ⬝ᵥ (ζ + fun i => (b i : ℂ))))
section Continuous
variable {W : Type*} [TopologicalSpace W] [LocallyCompactSpace W]
end Continuous
section Holomorphic
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable [FiniteDimensional ℂ W] {κ : Type*} [Fintype κ]
end Holomorphic
def imInv (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)
def canTh (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (ζ : Fin g → ℂ) : ℂ :=
  cexp (π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ)) * thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ζ
def canMult (a b : Fin g → ℝ) (m n : Fin g → ℤ) : ℂ :=
  cexp (π * I * ((m ⬝ᵥ n : ℤ) : ℂ) + 2 * π * I *
    (((a ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ) - ((b ⬝ᵥ fun i => (n i : ℝ) : ℝ) : ℂ)))
def translConst (b a' b' : Fin g → ℝ) : ℂ :=
  cexp (-(π * I * ((a' ⬝ᵥ b' : ℝ) : ℂ)) - 2 * π * I * ((a' ⬝ᵥ b : ℝ) : ℂ))
variable {τ : Matrix (Fin g) (Fin g) ℂ}
end GlobalTheory.CanTh


