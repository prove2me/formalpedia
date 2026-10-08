-- Prove2me | Definitions.Def_TroppMatrixConcentration_ch8_entropy
-- name    : TroppMatrixConcentration_ch8_entropy
-- status  : Definition
-- author  : @tc
-- created : 2026-10-07T13:51:08.98847+00:00
-- url     : https://prove2.me/theorems/98ed111f-e694-4e4c-a27c-ad31cd22c52c
-- title:
--   Matrix relative entropy, operator convexity, and perspective
-- statement:
--   For a scalar function $f:\mathbb R\to\mathbb R$, write $f(A)$ for its real continuous-functional-calculus value on a complex square matrix $A$. For positive-definite $A,H$, define
--   $$D(A;H)=\operatorname{Re}\operatorname{tr}[A(\log A-\log H)-(A-H)].$$
--   For a convex set $I\subseteq\mathbb R$, operator convexity means that $f(tA+(1-t)H)\preceq tf(A)+(1-t)f(H)$ for every positive finite matrix dimension, Hermitian $A,H$ with spectra in $I$, and $0\le t\le1$. Define the matrix perspective by
--   $$\Psi_f(A;H)=A^{1/2}f(A^{-1/2}HA^{-1/2})A^{1/2}.$$
--   These provide the deterministic interfaces for Lieb’s theorem. No trace-one normalization is imposed. On positive-definite inputs the inverse square root is the inverse of the positive square root.
--
--   **Formalization Note.** The operations themselves are total. Continuous functional calculus returns zero for non-Hermitian matrices; on Hermitian matrices it applies the given real function to the finite spectrum. The logarithm retains the existing spectral definition, including its values outside the intended positive-definite domain. The square root takes value zero on nonpositive real inputs, and its inverse uses total real inversion, with $0^{-1}=0$. Theorems restrict entropy and perspective inputs to positive-definite matrices.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Definitions 8.1.2, 8.4.5, and 8.6.1, printed pp. 120, 129, 134.

import Definitions.Def_TroppMatrixConcentration_spectral
import Mathlib.Analysis.Convex.Function

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace TroppMatrixConcentration

def ch8_matrixFunction {d : Type*} [Fintype d] [DecidableEq d]
    (f : ℝ → ℝ) (A : Matrix d d ℂ) : Matrix d d ℂ := cfc f A

def ch8_relativeEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (A H : Matrix d d ℂ) : ℝ :=
  (Matrix.trace (A * (matrixLog A - matrixLog H) - (A - H))).re

def ch8_operatorConvexOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  Convex ℝ I ∧ ∀ (d : ℕ) (_ : NeZero d) (A H : Matrix (Fin d) (Fin d) ℂ),
    A.IsHermitian → H.IsHermitian → spectrum ℝ A ⊆ I → spectrum ℝ H ⊆ I →
    ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
      loewnerLE (ch8_matrixFunction f (t • A + (1 - t) • H))
        (t • ch8_matrixFunction f A + (1 - t) • ch8_matrixFunction f H)

def ch8_perspective {d : Type*} [Fintype d] [DecidableEq d]
    (f : ℝ → ℝ) (A H : Matrix d d ℂ) : Matrix d d ℂ :=
  let S := ch8_matrixFunction Real.sqrt A
  let R := ch8_matrixFunction (fun x => (Real.sqrt x)⁻¹) A
  S * ch8_matrixFunction f (R * H * R) * S

end TroppMatrixConcentration


