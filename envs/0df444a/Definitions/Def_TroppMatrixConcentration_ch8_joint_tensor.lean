-- Prove2me | Definitions.Def_TroppMatrixConcentration_ch8_joint_tensor
-- name    : TroppMatrixConcentration_ch8_joint_tensor
-- status  : Definition
-- author  : @tc
-- created : 2026-10-07T14:47:20.503292+00:00
-- url     : https://prove2.me/theorems/34fbfe02-d63b-4a7c-95ec-09fdf7f7e2d2
-- title:
--   Tensor lifts and the vectorized-identity functional
-- statement:
--   For complex $d\times d$ matrices, set $$L(A)=A\otimes I,\qquad R(H)=I\otimes H^{\mathsf T},\qquad \Phi(M)=\operatorname{Re}(\operatorname{vec}(I)^*M\operatorname{vec}(I)).$$ The transpose makes the contraction agree with $\operatorname{Re}\operatorname{tr}(AH)$. Tensor indices are reindexed as a set of $d^2$ elements.
-- source:
--   Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, Sections 8.7–8.8, corrected complex tensor coordinates for the trace map and equation (8.8.1).

import Definitions.Def_TroppMatrixConcentration_ch8_entropy
import Mathlib.Logic.Equiv.Fin.Basic

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
open Matrix
noncomputable section
namespace TroppMatrixConcentration

def ch8_joint_left {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  (A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

def ch8_joint_right {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ H.transpose).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

def ch8_joint_vec {d : ℕ} (i : Fin (d * d)) : ℂ :=
  if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm i).2 then 1 else 0

def ch8_joint_eval {d : ℕ} (M : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) : ℝ :=
  (star ch8_joint_vec ⬝ᵥ (M *ᵥ ch8_joint_vec)).re

end TroppMatrixConcentration


