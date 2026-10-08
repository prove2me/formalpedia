-- Prove2me | Definitions.Def_BellmanDP_Variational_DiscreteExample
-- name    : BellmanDP_Variational_DiscreteExample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T19:04:30.947444+00:00
-- url     : https://prove2.me/theorems/9b35c7be-05b3-435e-8ce6-926686f701d3
-- title:
--   The discrete example of § 11: $u_{N+1}(c)=\max_{0\le v\le c}[c-v+u_N(c+b(v))]$ with concave $b$
-- statement:
--   This file sets up the discrete version (Chapter IX, § 11) of Bellman's example of § 10: maximize $\sum_{k=0}^{N}(x_k-y_k)$ subject to $x_{k+1}=x_k+b(y_k)$, $0\le y_k\le x_k$.
--
--   1. The **gain function** $b:[0,\infty)\to\mathbb R$ satisfies Bellman's conditions (10.4):
--      (a) $b(0)=0$ and $b'(0)=\infty$, i.e. $b(y)/y\to+\infty$ as $y\to 0^+$;
--      (b) $b'(y)>0$ for $y>0$ and $b'(y)\to 0$ as $y\to\infty$;
--      (c) $b''(y)<0$ for $y>0$.
--      The function is continuous on $[0,\infty)$ and twice differentiable on $(0,\infty)$. A function with these properties is $b(y)=y^{1/2}$.
--   2. The **value functions** $u_N(c)$, $c\ge 0$, are given by the recurrence (11.4):
--   $$u_0(c)=c,\qquad u_{N+1}(c)=\max_{0\le v\le c}\bigl[c-v+u_N(c+b(v))\bigr],\quad N=0,1,\dots$$
--
--   These are the objects of Chapter IX, Theorem 1.
--
--   **Formalization Note** The maximum is written as the supremum of the values over $0\le v\le c$; for $c\ge 0$ it is attained, since the bracket is continuous in $v$. Only $c\ge 0$ is meaningful. The condition $b'(0)=\infty$ is stated through the difference quotient $b(y)/y$ because $b$ has no finite derivative at $0$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IX, § 10, conditions (10.4), p. 256; § 11, Eqs. (11.1)-(11.4), p. 258

import Mathlib

namespace BellmanDP.Variational

open Set Filter Topology

/-- Bellman, *Dynamic Programming*, Ch. IX, § 10, conditions (10.4), p. 256, on the function
`b (y)` for `y ≥ 0`:
(a) `b (0) = 0`, `b′ (0) = ∞` (the difference quotient `b (y) / y` tends to `+∞` as `y → 0⁺`);
(b) `b′ (y) > 0`, `b′ (y) → 0` as `y → ∞`;
(c) `b″ (y) < 0`.
Continuity at `0` from the right and (twice) differentiability on `y > 0` are the regularity the
conditions presuppose. -/
def IsGainFunction (b : ℝ → ℝ) : Prop :=
  b 0 = 0 ∧ ContinuousOn b (Ici 0) ∧
    Tendsto (fun y => b y / y) (𝓝[>] 0) atTop ∧
    DifferentiableOn ℝ b (Ioi 0) ∧ (∀ y : ℝ, 0 < y → 0 < deriv b y) ∧
    Tendsto (deriv b) atTop (𝓝 0) ∧
    DifferentiableOn ℝ (deriv b) (Ioi 0) ∧ (∀ y : ℝ, 0 < y → deriv (deriv b) y < 0)

/-- Ch. IX, § 11, recurrence (11.4), p. 258:
`u_0 (c) = c`, `u_{N+1} (c) = Max_{0 ≤ v ≤ c} [c − v + u_N (c + b (v))]`, `N = 0, 1, …`.
The maximum is the supremum of the values over `0 ≤ v ≤ c`; only `c ≥ 0` is meaningful. -/
noncomputable def uSeq (b : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun c => c
  | N + 1 => fun c => sSup ((fun v => c - v + uSeq b N (c + b v)) '' Icc 0 c)

end BellmanDP.Variational


