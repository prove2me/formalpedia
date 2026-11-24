-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegral
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:28.516269+00:00
-- url     : https://prove2.me/theorems/abd085a4-b874-44af-a025-7d548e9985e6
-- title:
--   Gaussian Det Levi Integral
-- statement:
--   Definitions and structural lemmas for Gaussian Det Levi Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetLeviIntegral.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
namespace GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
open Matrix
variable {β : Type} [Fintype β] [DecidableEq β]
def rk (f : β → ℂ) : Matrix β β ℂ := vecMulVec f (star f)
def nS (f : β → ℂ) : ℝ := 1 + ∑ j, ‖f j‖ ^ 2
def pM (f : β → ℂ) : Matrix β β ℂ := 1 + ((1 / (1 + √(nS f)) : ℝ) : ℂ) • rk f
def rM (f : β → ℂ) : Matrix β β ℂ := 1 - ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) • rk f
end GlobalTheory.CompanionTheory.FSCrofton.GaussLevi


