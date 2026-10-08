-- Prove2me | Definitions.Def_TroppMatrixConcentration_ch7_intrinsic
-- name    : TroppMatrixConcentration_ch7_intrinsic
-- status  : Definition
-- author  : @tc
-- created : 2026-10-07T13:51:02.403419+00:00
-- url     : https://prove2.me/theorems/2b5c9bd9-da7e-4908-90e9-72fe9290efae
-- title:
--   Intrinsic dimension and traces of spectral functions
-- statement:
--   For a finite complex square matrix $A$, define $r(A)=\operatorname{Re}(\operatorname{tr}A)/\|A\|$, using the spectral norm. On nonzero positive semidefinite matrices this is intrinsic dimension (Definition 7.1.1). The definition is total and gives $r(0)=0$. For a real scalar function $\varphi$, define $\operatorname{tr}_\varphi(A)=\operatorname{Re}(\operatorname{tr}(\varphi(A)))$ through Mathlib's real continuous functional calculus. For Hermitian matrices it applies $\varphi$ to each real eigenvalue. Non-Hermitian inputs retain the functional calculus's zero-default convention. No concentration conclusion is encoded in either definition.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Definition 7.1.1, printed p. 106; spectral functions Section 2.1.10, printed pp. 21–22; Sections 7.4–7.5, printed pp. 111–113.

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace TroppMatrixConcentration

def intrinsicDimension {d : Type*} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) : ℝ := (Matrix.trace A).re / spectralNorm A

def traceFunction {d : Type*} [Fintype d] [DecidableEq d]
    (φ : ℝ → ℝ) (A : Matrix d d ℂ) : ℝ := (Matrix.trace (cfc φ A)).re

end TroppMatrixConcentration


