-- Prove2me | Definitions.Def_BellmanDP_Allocation_PolicyReturn
-- name    : BellmanDP_Allocation_PolicyReturn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T04:33:07.231944+00:00
-- url     : https://prove2.me/theorems/677fa3e0-c7f2-4354-aea3-0b2459755990
-- title:
--   Return of a stationary allocation policy $y_0(x)$
-- statement:
--   Let $y_0$ be a policy, that is, a rule assigning to each quantity $x \ge 0$ an allocation $y_0(x)$ with $0 \le y_0(x) \le x$. Starting from $x_0 = x$, using $y_0$ at every stage produces the quantities
--   $$x_{n+1} = a\,y_0(x_n) + b\,\big(x_n - y_0(x_n)\big), \qquad n = 0,1,2,\dots$$
--   The total return of the policy is the series
--   $$f_0(x) = \sum_{n=0}^{\infty} \Big[ g\big(y_0(x_n)\big) + h\big(x_n - y_0(x_n)\big) \Big],$$
--   which is the solution, obtained iteratively, of the equation $f_0(x) = T(f_0, y_0(x))$ (Bellman's (11.5) and (11.10)).
--
--   This is the initial function of "approximation in policy space" in Chapter I, Theorem 3.
--
--   **Formalization Note** The series is a Lean `tsum`, which equals $0$ when the series is not summable. Under the hypotheses of Theorem 1 each term is bounded by $2m(c^n x)$ with $c = \max(a,b)$, so the series converges absolutely whenever it is used.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 11, Eqs. (11.5), (11.10), pp. 18-19

import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model

namespace BellmanDP.Allocation

/-- Ch. I, § 11, p. 17–19: the quantities left at the successive stages when the stationary
policy `y₀` is used from the initial quantity `x`: `x₀ = x`,
`x_{n+1} = a y₀(x_n) + b (x_n − y₀(x_n))`. -/
def policyTrajectory (a b : ℝ) (y₀ : ℝ → ℝ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      a * y₀ (policyTrajectory a b y₀ x n) + b * (policyTrajectory a b y₀ x n - y₀ (policyTrajectory a b y₀ x n))

/-- Ch. I, § 11, Eqs. (11.5) and (11.10), pp. 18–19: the total return of the stationary policy
`y₀`, the series `f₀(x) = g(y₀) + h(x − y₀) + …` obtained by iterating
`f₀(x) = T(f₀, y₀(x))`. -/
noncomputable def policyReturn (g h : ℝ → ℝ) (a b : ℝ) (y₀ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, (g (y₀ (policyTrajectory a b y₀ x n)) +
    h (policyTrajectory a b y₀ x n - y₀ (policyTrajectory a b y₀ x n)))

end BellmanDP.Allocation


