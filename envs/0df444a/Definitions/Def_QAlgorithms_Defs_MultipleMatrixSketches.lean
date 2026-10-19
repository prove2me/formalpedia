-- Prove2me | Definitions.Def_QAlgorithms_Defs_MultipleMatrixSketches
-- name    : QAlgorithms_Defs_MultipleMatrixSketches
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:04.620133+00:00
-- url     : https://prove2.me/theorems/7ac6623b-5eb6-4f31-96e9-4b1cdc4dcfcf
-- title:
--   MultipleMatrixSketches
-- statement:
--   MultipleMatrixSketches
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MultipleMatrixSketches.lean

import Definitions.Def_QAlgorithms_Defs_FiniteVectorMoments
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.MatrixSketch

variable {n k c : ℕ}

/-- Uniform independent Boolean sign bits, interpreted true/false as +1 or -1 with one choice fixed. Independent coordinates and separate interface sketches. Source: arxiv-2510.08509v1 PDF p.5; arxiv-2510.08509v1 PDF p.15; arxiv-2510.08509v1 PDF p.19; arxiv-2510.08509v1 PDF p.22. -/
def signLaw (n : ℕ) : PMF (Fin n → Bool) := PMF.uniformOfFintype _

/-- c by n matrix with independently uniform signs divided by sqrt(c), c>=1. Mean orthogonality is supporting theorem, not assumed identity. Source: arxiv-2510.08509v1 PDF p.5; arxiv-2510.08509v1 PDF p.15; arxiv-2510.08509v1 PDF p.19; arxiv-2510.08509v1 PDF p.22. -/
def rowSketch (c n : ℕ) (_hc : 0 < c) (signs : Fin c → Fin n → Bool) : Matrix (Fin c) (Fin n) ℝ :=
  Matrix.of fun i j => (if signs i j then 1 else -1)/Real.sqrt c

/-- Ordered random X=A1 s1 s1 transpose A2 ... s_(k-1) s_(k-1) transpose Ak. k=1 yields A1. Source: arxiv-2510.08509v1 PDF p.13; arxiv-2510.08509v1 PDF p.19; arxiv-2510.08509v1 PDF p.20; arxiv-2510.08509v1 PDF p.22. -/
def vectorProduct (A : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ)
    (signs : Fin k → Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  A 0 * (List.ofFn fun i : Fin k =>
    let s : Fin n → ℝ := fun j => if signs i j then 1 else -1
    Matrix.vecMulVec s s*A i.succ).prod

/-- Ordered random Z=A1 S1 transpose S1 A2 ... S_(k-1) transpose S_(k-1) Ak. k=1 yields A1; for k>2 not a c-sample empirical mean of X. Source: arxiv-2510.08509v1 PDF p.13; arxiv-2510.08509v1 PDF p.19; arxiv-2510.08509v1 PDF p.20; arxiv-2510.08509v1 PDF p.22. -/
def matrixProduct (A : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ) (hc : 0 < c)
    (signs : Fin k → Fin c → Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  A 0 * (List.ofFn fun i : Fin k =>
    (rowSketch c n hc (signs i)).transpose * rowSketch c n hc (signs i)*A i.succ).prod

/-- Fixed bijection (i,j) -> real Euclidean coordinate in Fin n times Fin n (or finProdFinEquiv). Its Euclidean norm is real Frobenius norm; use same indexing in covariance. Source: arxiv-2510.08509v1 PDF p.13; arxiv-2510.08509v1 PDF p.19; arxiv-2510.08509v1 PDF p.20; arxiv-2510.08509v1 PDF p.22. -/
def vectorize (A : Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (Fin (n*n)) :=
  WithLp.toLp 2 fun i => A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

example (A : Fin 1 → Matrix (Fin n) (Fin n) ℝ) (signs : Fin 0 → Fin n → Bool) :
    vectorProduct A signs = A 0 := by simp [vectorProduct]

example (A : Fin 1 → Matrix (Fin n) (Fin n) ℝ) (hc : 0 < c)
    (signs : Fin 0 → Fin c → Fin n → Bool) : matrixProduct A hc signs = A 0 := by
  simp [matrixProduct]

end QAlgorithms.MatrixSketch


