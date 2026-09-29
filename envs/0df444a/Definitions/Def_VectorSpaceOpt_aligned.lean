-- Prove2me | Definitions.Def_VectorSpaceOpt_aligned
-- name    : VectorSpaceOpt_aligned
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-24T15:48:00.719247+00:00
-- url     : https://prove2.me/theorems/e811837d-7c83-4210-a160-5102fcb41e11
-- title:
--   Alignment of a vector with a functional
-- statement:
--   In a real normed space $X$ with dual $X^*$, the bound $\langle x, x^*\rangle \le \|x^*\|\,\|x\|$ always holds. The vectors $x \in X$ and $x^* \in X^*$ are said to be **aligned** when that bound is attained:
--
--   $$\langle x, x^*\rangle = \|x^*\|\,\|x\|.$$
--
--   Alignment is the normed-space substitute for the Hilbert-space notion of a functional being represented by a nonnegative multiple of $x$. In $L_p[a,b]$ with $1 < p < \infty$ it is exactly the equality case of Hölder's inequality: $x$ and $y \in L_q$ are aligned precisely when $x(t) = K\,[\operatorname{sgn} y(t)]\,|y(t)|^{q/p}$ for some constant $K$. In $C[a,b]$, a functional $x^*(x) = \int x\,dv$ is aligned with $x$ exactly when $v$ varies only on the set where $|x(t)| = \|x\|$, increasing where $x > 0$ and decreasing where $x < 0$.
--
--   The notion is what replaces orthogonality in the duality theory of minimum norm problems: in the projection theorem the error is orthogonal to the subspace, while in a general normed space the optimal dual functional is aligned with the error.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.7, pp. 116–117

import Mathlib

/-- Luenberger §5.7: `x ∈ X` and `f ∈ X*` are *aligned* when the Cauchy–Schwarz-type
bound `⟨x, f⟩ ≤ ‖f‖ ‖x‖` holds with equality. -/
def VectorSpaceOpt_aligned {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x : X) (f : X →L[ℝ] ℝ) : Prop :=
  f x = ‖f‖ * ‖x‖


