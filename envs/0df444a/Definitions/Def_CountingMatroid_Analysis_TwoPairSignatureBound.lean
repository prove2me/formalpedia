-- Prove2me | Definitions.Def_CountingMatroid_Analysis_TwoPairSignatureBound
-- name    : CountingMatroid_Analysis_TwoPairSignatureBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T09:43:17.665985+00:00
-- url     : https://prove2.me/theorems/15bef0e3-25d4-4b37-94fa-f52b38903eca
-- title:
--   Two-pair Hessian matrix
-- statement:
--   For rational numbers $a,c,z$, define the real symmetric matrix
--
--   $$H=\begin{pmatrix}2a&z\\z&2c\end{pmatrix}.$$
--
--   The rational entries are viewed as real numbers. This definition imposes no sign or spectral restrictions. It gives the matrix shape used for the two-pair Hessian in Lemma 3.2 of the counting paper.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/TwoPairSignatureBound.lean#L11-L14 — twoPairMatrix; paper Lemma 3.2, p. 6.

import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic

section


set_option autoImplicit false

/-! The elementary determinant consequence of the two-pair Hessian signature. -/

namespace CountingMatroid.Analysis.TwoPairSignatureBound

open scoped Matrix

/-- INTERNAL: The two-pair Hessian, ordered by the retained pair variables.
TEXLINE: main.tex:408-412 -/
noncomputable def twoPairMatrix (a c z : ℚ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * (a : ℝ), (z : ℝ); (z : ℝ), 2 * (c : ℝ)]



end CountingMatroid.Analysis.TwoPairSignatureBound

end


