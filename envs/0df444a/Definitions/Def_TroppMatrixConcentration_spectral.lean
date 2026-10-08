-- Prove2me | Definitions.Def_TroppMatrixConcentration_spectral
-- name    : TroppMatrixConcentration_spectral
-- status  : Definition
-- author  : @tc
-- created : 2026-10-07T13:42:58.538985+00:00
-- url     : https://prove2.me/theorems/b2b5eb20-49ee-4e95-9087-214cb82abd58
-- title:
--   Spectral functions and semidefinite order
-- statement:
--   For finite complex matrices, define the Euclidean operator norm; the largest and smallest real spectral values; the matrix power-series exponential; the spectral logarithm via continuous functional calculus; the real part of the trace exponential; and the order $A\preceq B$ meaning that $B-A$ is positive semidefinite. Extreme spectral values are used on nonempty Hermitian matrices, and the logarithm on positive-definite matrices. These are concrete Mathlib operations, with no axioms or theorem assumptions. Outside those intended domains the operations retain Mathlib's total-function conventions, as detailed in the read-back.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Sections 2.1.6–2.1.14, printed pp. 19–24.

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace TroppMatrixConcentration

def spectralNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ := ‖A‖

def lambdaMax {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := sSup (spectrum ℝ A)

def lambdaMin {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := sInf (spectrum ℝ A)

def matrixExp {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : Matrix d d ℂ := NormedSpace.exp A

def matrixLog {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : Matrix d d ℂ := cfc Real.log A

def traceExp {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := (Matrix.trace (matrixExp A)).re

def loewnerLE {d : Type*} [Fintype d]
    (A B : Matrix d d ℂ) : Prop := (B - A).PosSemidef

end TroppMatrixConcentration


