-- Prove2me | Definitions.Def_TeschlODE_SturmLiouville_SLQuadForm
-- name    : TeschlODE_SturmLiouville_SLQuadForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:24:06.117211+00:00
-- url     : https://prove2.me/theorems/81b179cb-2588-4219-82c9-56c24b8afbdb
-- title:
--   Quadratic form Q(f, g) of L (5.71)–(5.72)
-- statement:
--   The **quadratic form** associated with $L$ is
--   $$Q(f, g) = \int_a^b \bigl( p(x) f'(x)^* g'(x) + q(x) f(x)^* g(x) \bigr)\, dx + Q_{\alpha,a}(f, g) - Q_{\beta,b}(f, g), \qquad (5.71)$$
--   where
--   $$Q_{\gamma,c}(f,g) = \begin{cases} 0, & \gamma = 0,\\ \cot(\gamma)\, f(c)^* g(c), & \gamma \ne 0. \end{cases} \qquad (5.72)$$
--   One writes $Q(f) = Q(f, f)$. For $f, g \in D(L)$, integration by parts gives $Q(f, g) = \langle f, L g\rangle$ (5.73).
--
--   **Formalization Note.** The case split of (5.72) is on $\sin\gamma = 0$; under the book's normalisation $\gamma \in [0,\pi)$ this is exactly $\gamma = 0$, and for general $\gamma$ it is the Dirichlet case, where the boundary term vanishes on $D(L)$ anyway. $\cot\gamma$ is written $\cos\gamma / \sin\gamma$. Derivatives are within $[a,b]$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 161, §5.4, Eq. (5.71)–(5.72)

import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.4, p. 161, (5.71)–(5.72): the quadratic form of `L`,
`Q(f, g) = ∫_a^b (p f′* g′ + q f* g) dx + Q_{α,a}(f, g) − Q_{β,b}(f, g)`, where
`Q_{γ,c}(f, g) = 0` if `γ = 0` and `cot(γ) f(c)* g(c)` otherwise. The case distinction is taken on
`sin γ = 0` (for the book's normalisation `γ ∈ [0, π)` this is `γ = 0`); derivatives within
`[a, b]`. -/
noncomputable def SLQuadForm (p q : ℝ → ℝ) (a b α β : ℝ) (f g : ℝ → ℂ) : ℂ :=
  (∫ x in a..b, (p x : ℂ) * starRingEnd ℂ (derivWithin f (Set.Icc a b) x) *
      derivWithin g (Set.Icc a b) x + (q x : ℂ) * starRingEnd ℂ (f x) * g x) +
    (if Real.sin α = 0 then 0
      else ((Real.cos α / Real.sin α : ℝ) : ℂ) * starRingEnd ℂ (f a) * g a) -
    (if Real.sin β = 0 then 0
      else ((Real.cos β / Real.sin β : ℝ) : ℂ) * starRingEnd ℂ (f b) * g b)

end TeschlODE.SturmLiouville


