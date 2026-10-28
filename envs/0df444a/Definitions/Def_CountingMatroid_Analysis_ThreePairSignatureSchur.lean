-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
-- name    : CountingMatroid_Analysis_ThreePairSignatureSchur
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T08:54:30.380001+00:00
-- url     : https://prove2.me/theorems/c63cca63-7c7e-48f2-b321-d1023f09ea18
-- title:
--   Three-pair Hessian matrix
-- statement:
--   For rational numbers $a,c,d,e,z$, define the real symmetric matrix
--
--   $$H=\begin{pmatrix}2a&z&2d\\z&2c&2e\\2d&2e&0\end{pmatrix}.$$
--
--   The rational entries are viewed as real numbers. This is the matrix shape used for the extracted three-pair quadratic in the proof of Lemma 3.2 of the counting paper. The definition itself places no sign or spectral restrictions on the coefficients.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ThreePairSignatureSchur.lean#L16-L21 — threePairMatrix; paper Lemma 3.2, p. 6, Hessian (8).

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

section


set_option autoImplicit false

/-!
The real quadratic signature implies the rational Schur-complement bound
used by the operational three-pair partition comparison.
-/

namespace CountingMatroid.Analysis.ThreePairSignatureSchur

open scoped Matrix

/-- INTERNAL: The paper's extracted Hessian, in the order i,j,k.
TEXLINE: main.tex:415-449 -/
noncomputable def threePairMatrix (a c d e z : ℚ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2 * (a : ℝ), (z : ℝ), 2 * (d : ℝ);
     (z : ℝ), 2 * (c : ℝ), 2 * (e : ℝ);
     2 * (d : ℝ), 2 * (e : ℝ), 0]



end CountingMatroid.Analysis.ThreePairSignatureSchur

end


