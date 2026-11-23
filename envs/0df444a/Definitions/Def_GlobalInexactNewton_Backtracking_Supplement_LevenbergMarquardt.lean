-- Prove2me | Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_LevenbergMarquardt
-- name    : GlobalInexactNewton_Backtracking_Supplement_LevenbergMarquardt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:49:59.414256+00:00
-- url     : https://prove2.me/theorems/1a2d8932-fcc9-4dfd-9664-c11334094fd6
-- title:
--   Levenberg–Marquardt points and continuous equality subcurves
-- statement:
--   For a linear map $A$ on a finite-dimensional real inner product space and a residual $b$, a positive-damping point $s$ satisfies
--
--   $$A^*(As)+\mu s=-A^*b\quad\text{for some }\mu>0.$$
--
--   The Levenberg–Marquardt curve consists of these points and their limit endpoints. A subcurve at $x$ lies in this set for $A=F'(x)$ and $b=F(x)$; the ECMR/ECTL run supplies continuity, the zero endpoint and equality (7.1). If $F(x)=0$, the subcurve is zero.
--
--   This agrees with (8.1) for positive damping and with its attained zero-damping limit. **Formalization Note** Closure supplies endpoints without evaluating a total inverse at a singular derivative. It excludes arbitrary least-squares minimizers with a kernel component. When $F'(x)$ is invertible the zero-damping endpoint is the Newton step; at singular derivatives only attainable equality subcurves are allowed, and an unattainable requested level corresponds to breakdown. No global invertibility is assumed. Finite-dimensional real inner product spaces are coordinate-free Euclidean spaces; the adjoint is the transpose in an orthonormal basis.
--
--   The endpoint notation in the paragraph following (8.1) is completed explicitly: for singular $A$ the zero-damping residual need not be zero, and for $b=0$ the normalized residual is undefined. The regularization branch has the minimum-norm least-squares endpoint and becomes the zero curve when $b=0$. Requested levels below the attainable residual correspond to breakdown.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 418, Levenberg-Marquardt equality curve (8.1); DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_EqualityCurves

namespace GlobalInexactNewton.Backtracking.Supplement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Positive-damping normal equations, equivalent to (8.1) without a total inverse at μ=0. -/
def IsRegularizedPoint (A : E →L[ℝ] E) (b s : E) : Prop :=
  ∃ μ > 0, A.adjoint (A s) + μ • s = - A.adjoint b

/-- The regularization curve with its attained limit endpoints. Closure excludes arbitrary
least-squares minimizers containing a component in ker A. -/
def IsLMPoint (A : E →L[ℝ] E) (b s : E) : Prop :=
  s ∈ closure {v | IsRegularizedPoint A b v}

/-- Subcurve of the Euclidean LM curve; equality/continuity are supplied separately by the run.
The zero-residual case uses the zero curve, including at singular derivatives. -/
def IsLMCurve (F : E → E) (x : E) (ηbar : ℝ) (σ : ℝ → E) : Prop :=
  (F x = 0 → ∀ η ∈ Set.Icc ηbar 1, σ η = 0) ∧
    (F x ≠ 0 → ∀ η ∈ Set.Icc ηbar 1, IsLMPoint (fderiv ℝ F x) (F x) (σ η))

end GlobalInexactNewton.Backtracking.Supplement


