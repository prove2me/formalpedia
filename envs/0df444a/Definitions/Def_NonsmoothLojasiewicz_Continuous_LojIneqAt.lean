-- Prove2me | Definitions.Def_NonsmoothLojasiewicz_Continuous_LojIneqAt
-- name    : NonsmoothLojasiewicz_Continuous_LojIneqAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:50:50.149129+00:00
-- url     : https://prove2.me/theorems/f943ffea-6e0a-4744-a4b3-d103191b7f0a
-- title:
--   The nonsmooth Łojasiewicz inequality (8) at a point, with exponent $\theta$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R} \cup \{+\infty\}$, let $a$ be a point where $f(a)$ is finite, let $\theta \ge 0$, and let $\partial f$ and $m_f$ be the limiting subdifferential and the nonsmooth slope. We say that $f$ satisfies the **Łojasiewicz inequality at $a$ with exponent $\theta$** if the function
--   $$
--   x \longmapsto \frac{|f(x) - f(a)|^{\theta}}{m_f(x)}
--   $$
--   is bounded on a neighbourhood of $a$, with the conventions $0^0 = 1$, $\infty/\infty = 0/0 = 0$ and $\lambda/0 = +\infty$ for $\lambda > 0$. Equivalently: there are a constant $C$ and a neighbourhood $U$ of $a$ such that
--   $$
--   |f(x) - f(a)|^{\theta} \le C\, \|x^*\| \qquad \text{for all } x \in U \text{ and all } x^* \in \partial f(x).
--   $$
--
--   At points with $\partial f(x) = \emptyset$ the ratio is $0$ by convention and nothing is required. The inequality controls how flat $f$ can be near $a$ relative to the size of its subgradients; it is the key ingredient for finite length and convergence of subgradient trajectories.
--
--   **Formalization Note.** Lean's `Real.rpow` has `0 ^ 0 = 1`, as in the paper, so with $\theta = 0$ the inequality fails at any critical point (take $x = a$, $x^* = 0$), exactly as the page's $1/0 = +\infty$. Where $\partial f(x) \ne \emptyset$ the value $f(x)$ is finite, so the real parts `(f x).toReal` used in the formula are the true values. The division-free form is used deliberately: a product $C \cdot m_f(x)$ in $[0, +\infty]$ would turn the vacuous case $m_f(x) = +\infty$ into a false one via $0 \cdot \infty = 0$.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1213 (PDF p. 9), Theorem 3.1, expression (8) and the conventions following it

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open Filter Topology

namespace NonsmoothLojasiewicz.Continuous

/-- The Łojasiewicz inequality (8) of Bolte–Daniilidis–Lewis (p. 1213) at `a` with exponent `θ`:
the ratio `|f − f(a)|^θ / m_f` is bounded around `a`, under the paper's conventions
`0^0 = 1`, `∞/∞ = 0/0 = 0` and `λ/0 = +∞` for `λ > 0`. Written without division: there are a
constant `C` and a neighbourhood `U` of `a` such that `|f(x) − f(a)|^θ ≤ C ‖v‖` for every
`x ∈ U` and every limiting subgradient `v ∈ ∂f(x)`. Where `∂f(x) = ∅` (so `m_f(x) = +∞`) nothing
is required; where `∂f(x) ≠ ∅`, `f x` is finite, so `toReal` is faithful there. `Real.rpow`
has `0 ^ 0 = 1`, as on the page. -/
def LojIneqAt {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (a : EuclideanSpace ℝ (Fin n))
    (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∃ U ∈ 𝓝 a, ∀ x ∈ U, ∀ v ∈ NonconvexSplitting.Shared.LimitingSubdiff f x,
    |(f x).toReal - (f a).toReal| ^ θ ≤ C * ‖v‖

end NonsmoothLojasiewicz.Continuous


