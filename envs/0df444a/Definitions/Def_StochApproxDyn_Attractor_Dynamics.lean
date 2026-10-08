-- Prove2me | Definitions.Def_StochApproxDyn_Attractor_Dynamics
-- name    : StochApproxDyn_Attractor_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:09:17.163335+00:00
-- url     : https://prove2.me/theorems/1827b3a3-118c-4244-8682-6fa06c14d549
-- title:
--   Invariant sets, asymptotic pseudotrajectories, the limit set $L(X)$, attractors, basins and $d_X(T)$
-- statement:
--   Let $\Phi=(\Phi_t)_{t\ge0}$ be a **semiflow** on a metric space $(M,d)$: a continuous map $\mathbb R_+\times M\to M$, $(t,x)\mapsto\Phi_t(x)$, with $\Phi_0=\mathrm{Id}$ and $\Phi_{t+s}=\Phi_t\circ\Phi_s$ for all $t,s\ge0$. This file introduces the deterministic objects used in Sections 6.3 and 7 of the notes; it defines positive invariance (item 1, second half) and $d_X(T)$ (item 5) and imports the others, which are recalled here for reference, from the series' shared definitions.
--
--   1. A set $A\subset M$ is **invariant** if $\Phi_t(A)=A$ for all $t\ge0$ (equality, not inclusion), and **positively invariant** if $\Phi_t(A)\subset A$ for all $t\ge0$.
--   2. A continuous map $X:\mathbb R_+\to M$ is an **asymptotic pseudotrajectory** of $\Phi$ if for every $T>0$
--   $$\lim_{t\to\infty}\ \sup_{0\le h\le T} d\big(X(t+h),\Phi_h(X(t))\big)=0 .$$
--   3. The **limit set** of $X$ is $L(X)=\bigcap_{t\ge0}\overline{X([t,\infty))}$.
--   4. A set $A\subset M$ is an **attractor** if it is nonempty, compact and invariant, and it has a neighbourhood $W$ (a fundamental neighbourhood) such that $\operatorname{dist}(\Phi_t x,A)\to0$ as $t\to\infty$ uniformly in $x\in W$. Its **basin** $B(A)$ is the set of all $x$ with $\operatorname{dist}(\Phi_t x,A)\to0$.
--   5. For $T>0$,
--   $$d_X(T)=\sup_{k\in\mathbb N} d\big(\Phi_T(X(kT)),X(kT+T)\big)\in[0,\infty],$$
--   the largest error made by $X$ when it is compared with the flow over the successive windows $[kT,kT+T]$.
--
--   These notions express when a perturbed trajectory inherits the long-run behaviour of the semiflow: $d_X(T)$ small and $X(0)$ in a compact part of a basin keeps $L(X)$ inside the attractor.
--
--   **Formalization Note** A semiflow is Mathlib's `Flow ℝ≥0 M`, time is `ℝ≥0`. The asymptotic pseudotrajectory condition is written with $\varepsilon$ and $t_0$. $\operatorname{dist}(y,A)$ is `Metric.infDist`. The supremum $d_X(T)$ is computed in `ℝ≥0∞` with the extended distance, so an unbounded supremum is $+\infty$, not a junk value. The paper writes $X:\mathbb R\to M$ in (23); only $t\ge0$ is used, and $X$ is defined on $\mathbb R_+$ here.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 9 (semiflow, asymptotic pseudotrajectory), p. 20 (invariant, positively invariant), p. 22 (attractor, basin), p. 24 (limit set L(X)), p. 28, Section 6.3, Eq. (23) (d_X(T))

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_Attractor
import Definitions.Def_StochApproxDyn_LimitSet_Invariance

open scoped NNReal ENNReal

namespace StochApproxDyn.Attractor

/-- Positive invariance (p. 20): `Φ_t(A) ⊆ A` for every `t ≥ 0`. -/
def IsPositivelyInvariant {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (A : Set M) : Prop :=
  ∀ t : ℝ≥0, Φ t '' A ⊆ A

/-- `d_X(T) = sup_{k ∈ ℕ} d(Φ_T(X(kT)), X(kT + T))` (p. 28, Eq. (23)), computed in `ℝ≥0∞` so that
an unbounded supremum is `∞` rather than a junk value. -/
noncomputable def stepDeviation {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → M)
    (T : ℝ≥0) : ℝ≥0∞ :=
  ⨆ k : ℕ, edist (Φ T (X (k * T))) (X (k * T + T))

end StochApproxDyn.Attractor


