-- Prove2me | Definitions.Def_TeschlODE_SturmLiouville_SLDomain
-- name    : TeschlODE_SturmLiouville_SLDomain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:21:19.739512+00:00
-- url     : https://prove2.me/theorems/d79c5e25-cbae-412c-b332-521f36e81132
-- title:
--   Domain D(L) of the Sturm–Liouville operator (5.54)–(5.55)
-- statement:
--   Fix $\alpha, \beta \in \mathbb{R}$. The **domain** of the Sturm–Liouville operator is
--   $$D(L) = \{ f \in C^2([a,b], \mathbb{C}) \mid BC_a(f) = BC_b(f) = 0 \}, \qquad (5.54)$$
--   with the separated boundary conditions
--   $$BC_a(f) = \cos(\alpha) f(a) - \sin(\alpha) p(a) f'(a), \qquad BC_b(f) = \cos(\beta) f(b) - \sin(\beta) p(b) f'(b). \qquad (5.55)$$
--   $\alpha = 0$ is the Dirichlet condition $f(a) = 0$ and $\alpha = \pi/2$ the Neumann condition $f'(a) = 0$. The book notes that one may assume $\alpha, \beta \in [0, \pi)$ without loss of generality; here they are arbitrary reals (the condition only depends on $\alpha$ modulo $\pi$).
--
--   **Formalization Note.** $C^2([a,b],\mathbb{C})$ is `ContDiffOn ℝ 2 f (Set.Icc a b)`; $f'(a)$, $f'(b)$ are `derivWithin f (Set.Icc a b)` at the endpoints (one-sided).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 156, §5.4, Eq. (5.54)–(5.55)

import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.4, p. 156, (5.54)–(5.55): the domain `D(L)` of the Sturm–Liouville operator,
`f ∈ C²([a, b], ℂ)` with `BC_a(f) = cos(α) f(a) − sin(α) p(a) f′(a) = 0` and
`BC_b(f) = cos(β) f(b) − sin(β) p(b) f′(b) = 0`. Derivatives are taken within `[a, b]`. -/
def SLDomain (p : ℝ → ℝ) (a b α β : ℝ) (f : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ 2 f (Set.Icc a b) ∧
    (Real.cos α : ℂ) * f a - (Real.sin α : ℂ) * (p a : ℂ) * derivWithin f (Set.Icc a b) a = 0 ∧
    (Real.cos β : ℂ) * f b - (Real.sin β : ℂ) * (p b : ℂ) * derivWithin f (Set.Icc a b) b = 0

end TeschlODE.SturmLiouville


