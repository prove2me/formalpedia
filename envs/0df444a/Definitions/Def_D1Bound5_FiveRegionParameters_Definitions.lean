-- Prove2me | Definitions.Def_D1Bound5_FiveRegionParameters_Definitions
-- name    : D1Bound5_FiveRegionParameters_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:06:17.097884+00:00
-- url     : https://prove2.me/theorems/92632e5d-362a-4e93-b48f-db6ced2cb32f
-- title:
--   Five Region Parameters
-- statement:
--   The five norm alternatives, before any approximation or interval result. The named objects in this bundle include `fiveRegionMinB`, `fiveRegionMinNorm`, `fiveRegionMaxA`, `fiveRegionFrontier`, `fiveRegionQ`, `fiveRegionPhase`, `fiveRegionGap`, `fiveRegionCoupledGap` and 9 further declarations.
-- source:
--   D1Bound5/FiveRegionParameters.lean, lines 13-13, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 14-14, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 15-15, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 16-16, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 17-17, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 18-18, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 19-19, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 20-20, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 21-21, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 23-23, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 24-24, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 25-25, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 26-26, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 27-27, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 29-29, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 30-32, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9; D1Bound5/FiveRegionParameters.lean, lines 34-36, SHA-256 a07134efef48fc000eda95bf528689560963839c8d258ce350b766ac14e559a9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions

section
noncomputable section

namespace D1Bound5

def fiveRegionMinB : Fin 5 → ℝ := ![8,4,3,3,3]
def fiveRegionMinNorm : Fin 5 → ℝ := ![1,2,3,4,5]
def fiveRegionMaxA : Fin 5 → ℝ := ![1,3/2,7/4,2,17/6]
def fiveRegionFrontier : Fin 5 → ℝ := ![27/8,3,11/4,29/10,3]
def fiveRegionQ : Fin 5 → ℝ := ![8,8/3,12/7,3/2,18/17]
def fiveRegionPhase : Fin 5 → ℝ := ![269,368,540,637,1121]
def fiveRegionGap : Fin 5 → ℝ := ![7495,1771,598,624,375]
def fiveRegionCoupledGap : Fin 5 → ℝ := ![20687,7973,3226,3507,2217]
def fiveRegionPResidual : Fin 5 → ℝ := ![7/50,7/20,18/25,47/50,201/100]

def fiveRegionN2Residual (r : Fin 5) : ℝ := (101/2560)*(1+fiveRegionAnchorRatio r)^4
def fiveRegionN3Residual (r : Fin 5) : ℝ := (3535/409600)*(1+fiveRegionAnchorRatio r)^6
def fiveRegionA3Residual (r : Fin 5) : ℝ := (707/40960)*(1+fiveRegionAnchorRatio r)^6
def fiveRegionA4Residual (r : Fin 5) : ℝ := (6363/409600)*(1+fiveRegionAnchorRatio r)^8
def fiveRegionA5Residual (r : Fin 5) : ℝ := (9999/2621440)*(1+fiveRegionAnchorRatio r)^10

def fiveRegionTriangle (r : Fin 5) : ℝ := 2*(1+fiveRegionAnchorRatio r)^2
def fiveRegionRetained (r : Fin 5) : ℝ :=
  (9999/10000 : ℝ)*(200/19)^2*(fiveRegionFrontier r)^5*
    (1-(51051/400000 : ℝ)*fiveRegionTriangle r/(fiveRegionMinB r)^2)^2

/-- The five norm alternatives, before any approximation or interval result. -/
def FiveRegionCase (r : Fin 5) (A B : ℝ) : Prop :=
  (if r=4 then 5 ≤ A^2 else A^2=fiveRegionMinNorm r) ∧ fiveRegionMinB r ≤ B







end D1Bound5
end


