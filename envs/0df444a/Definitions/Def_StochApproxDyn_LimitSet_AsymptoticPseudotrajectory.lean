-- Prove2me | Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
-- name    : StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:42:33.483431+00:00
-- url     : https://prove2.me/theorems/1f8988b2-73f9-4e61-8ee0-52c328ada4fe
-- title:
--   Asymptotic pseudotrajectories and the limit set $L(X)$
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $(M,d)$. A continuous function $X:\mathbb R_+\to M$ is an **asymptotic pseudotrajectory** for $\Phi$ if
--   $$\lim_{t\to\infty}\ \sup_{0\le h\le T} d\big(X(t+h),\Phi_h(X(t))\big)=0\qquad\text{for every }T>0 .$$
--   Thus for each fixed $T>0$ the curve $h\mapsto X(t+h)$, $h\in[0,T]$, shadows the $\Phi$-trajectory of $X(t)$ with arbitrary accuracy for $t$ large.
--
--   The **limit set** of $X$ is
--   $$L(X)=\bigcap_{t\ge0}\overline{X([t,\infty))},$$
--   the set of limits of convergent sequences $X(t_k)$ with $t_k\to\infty$.
--
--   Interpolated stochastic approximation processes are, under standard step-size and noise conditions, asymptotic pseudotrajectories of the flow of the mean vector field, so their long-run behaviour is described by $L(X)$.
--
--   **Formalization Note** Time is `ℝ≥0`. Continuity of $X$ is part of the definition. The limit of the supremum is written without a real supremum: for every $T>0$ and $\varepsilon>0$ there is $t_0$ such that $d(X(t+h),\Phi_h(X(t)))<\varepsilon$ for all $t\ge t_0$ and $0\le h\le T$, which is equivalent.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 9, Section 3 (asymptotic pseudotrajectory); p. 24, Section 5.2 (limit set L(X))

import Mathlib

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- An *asymptotic pseudotrajectory* of the semiflow `Φ` (Benaïm 1999, p. 9): a continuous
`X : ℝ₊ → M` with `lim_{t→∞} sup_{0 ≤ h ≤ T} d(X(t+h), Φ_h(X(t))) = 0` for every `T > 0`,
written with `ε`: for all `T > 0` and `ε > 0` there is `t₀` such that
`d(X(t+h), Φ_h(X(t))) < ε` for all `t ≥ t₀` and `0 ≤ h ≤ T`. -/
def IsAsymptoticPseudotrajectory {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → M) :
    Prop :=
  Continuous X ∧
    ∀ T : ℝ≥0, 0 < T → ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℝ≥0, ∀ t : ℝ≥0, t₀ ≤ t → ∀ h : ℝ≥0, h ≤ T →
      dist (X (t + h)) (Φ h (X t)) < ε

/-- The limit set `L(X) = ⋂_{t ≥ 0} closure (X([t, ∞)))` (p. 24). -/
def limitSet {M : Type*} [MetricSpace M] (X : ℝ≥0 → M) : Set M :=
  ⋂ t : ℝ≥0, closure (X '' Set.Ici t)

end StochApproxDyn.LimitSet


