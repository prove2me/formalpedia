-- Prove2me | Definitions.Def_GenEmpLik_Expansion_AssumptionA
-- name    : GenEmpLik_Expansion_AssumptionA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:01:31.417775+00:00
-- url     : https://prove2.me/theorems/2eb01593-d832-4b09-b55e-9e9ec6f8513c
-- title:
--   Assumption A — smoothness of the f-divergence: f convex, three times differentiable near 1, f(1) = f′(1) = 0, f″(1) = 2
-- statement:
--   Let $f:[0,\infty)\to(-\infty,+\infty]$ be the function generating an $f$-divergence $D_f(P\|Q)=\int f(dP/dQ)\,dQ$. **Assumption A** requires:
--
--   1. $f$ is convex on $[0,\infty)$, never $-\infty$, finite on $(0,\infty)$, and satisfies $f(1)=0$; the value $f(0)$ may be $+\infty$ (as for $f(t)=-2\log t+2t-2$, the empirical-likelihood divergence); as for every divergence generator in the paper (p. 2), $f$ is lower semicontinuous on $[0,\infty)$;
--   2. $f$ is three times differentiable on an open interval $(a,b)$ with $0<a<1<b$;
--   3. $f'(1)=0$ and $f''(1)=2$.
--
--   The normalisations $f(1)=f'(1)=0$ lose no generality, since $t\mapsto f(t)+c(t-1)$ defines the same divergence between probability measures, and $f''(1)=2$ fixes the scale so that the divergence ball of radius $\rho/n$ has asymptotic $\chi^2_1$ calibration. Every result of the mission is stated under this assumption.
--
--   **Formalization Note** $f$ is a function $\mathbb R\to\overline{\mathbb R}$ (Lean `EReal`) satisfying the published structure `PhiDivRobust.Counterpart.IsPhiDivergenceFunction` (clause 1; values at negative arguments are never used). The derivatives in clauses 2–3 are those of the real-valued function $t\mapsto f(t)$, read through `EReal.toReal`, which agrees with $f$ on $(a,b)\subseteq(0,\infty)$. "Three times differentiable" is stated as differentiability of $g$, $g'$ and $g''$ on $(a,b)$; no continuity of $g'''$ is required.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 6, Assumption A (with the standing lower semicontinuity of f, p. 2)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction

namespace GenEmpLik.Expansion

/-- Assumption A (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 6): the divergence function
`f : ℝ → EReal` is a φ-divergence function in the sense of the published
`IsPhiDivergenceFunction` (never `-∞`, finite on `(0, ∞)`, `f 1 = 0`, convex on `[0, ∞)`,
`f 0 = +∞` allowed, values at negative arguments unused), lower semicontinuous on `[0, ∞)` (the standing
condition on divergence generators, p. 2), and it is three times differentiable
in a neighbourhood `(a, b)` of `1` with `f'(1) = 0` and `f''(1) = 2`. The derivatives are those
of the real-valued function `g t = (f t).toReal`, which equals `f` on `(a, b) ⊆ (0, ∞)`. -/
def AssumptionA (f : ℝ → EReal) : Prop :=
  PhiDivRobust.Counterpart.IsPhiDivergenceFunction f ∧
    LowerSemicontinuousOn f (Set.Ici 0) ∧
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧
      DifferentiableOn ℝ (fun t => (f t).toReal) (Set.Ioo a b) ∧
      DifferentiableOn ℝ (deriv (fun t => (f t).toReal)) (Set.Ioo a b) ∧
      DifferentiableOn ℝ (deriv (deriv (fun t => (f t).toReal))) (Set.Ioo a b) ∧
      deriv (fun t => (f t).toReal) 1 = 0 ∧
      deriv (deriv (fun t => (f t).toReal)) 1 = 2

end GenEmpLik.Expansion


