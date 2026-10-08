-- Prove2me | Definitions.Def_GenEmpLik_Coverage_AssumptionA
-- name    : GenEmpLik_Coverage_AssumptionA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:03:54.611493+00:00
-- url     : https://prove2.me/theorems/ac70bf09-10a4-4980-9f1a-f3f78a042ea0
-- title:
--   Assumption A — lower semicontinuous smooth normalized divergence
-- statement:
--   An **admissible divergence generator** is a function $f:\mathbb R\to\mathbb R\cup\{\pm\infty\}$ that is never $-\infty$, is finite on $(0,\infty)$, is lower semicontinuous and convex on $[0,\infty)$, and satisfies $f(1)=0$. Assumption A adds a neighborhood $(a,b)$ of $1$, with $0<a<1<b$, on which $f$ is three times continuously differentiable and
--
--   $$f'(1)=0,\qquad f''(1)=2.$$
--
--   The normalization fixes the scale of the divergence balls used throughout the mission. The value $f(0)=+\infty$ is allowed, as for the Kullback–Leibler generator $f(t)=-2\log t+2t-2$ and the empirical likelihood generator $f(t)=-2\log t$ (shifted to $f'(1)=0$).
--
--   **Formalization Note** The generator is `EReal` valued; finiteness on $(0,\infty)$, $f(1)=0$ and convexity on $[0,\infty)$ (written out in `EReal`) come from the published `PhiDivRobust.Counterpart.IsPhiDivergenceFunction`. The lower semicontinuity clause comes from the paper's initial definition of an $f$-divergence generator (p. 2). Its real restriction $t\mapsto f(t)$ near $1$ is differentiated. The smoothness is read as $C^3$ on $(a,b)$: the statement of Assumption A on p. 6 says "three times differentiable in a neighborhood of 1", while the paper describes the assumption as "$f\in C^3$ near 1" (p. 2) and its proof of Lemma 1 uses "f is $C^3$ in a neighborhood of 1" (p. 32, before (30)).
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 2, f-divergence definition; p. 6, Assumption A

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction

namespace GenEmpLik.Coverage

/-- Assumption A, p. 6, for the lower semicontinuous divergence generators fixed on p. 2. -/
def AssumptionA (f : ℝ → EReal) : Prop :=
  PhiDivRobust.Counterpart.IsPhiDivergenceFunction f ∧
  LowerSemicontinuousOn f (Set.Ici 0) ∧
  ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧
    ContDiffOn ℝ 3 (fun t : ℝ => (f t).toReal) (Set.Ioo a b) ∧
    deriv (fun t : ℝ => (f t).toReal) 1 = 0 ∧
    iteratedDeriv 2 (fun t : ℝ => (f t).toReal) 1 = 2

end GenEmpLik.Coverage


