-- Prove2me | Definitions.Def_NonlinSSD_DualFunctional_Basic
-- name    : NonlinSSD_DualFunctional_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:49:50.672116+00:00
-- url     : https://prove2.me/theorems/b6e40fbf-2082-4178-9107-6ab5d633ea67
-- title:
--   Left derivative v′₋(a), concave conjugate v^*, dual functional D_i (34) and f(v,ζ) = −E v^*(ζ) (35)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and let $a\le b$ be real numbers. This file fixes the objects of §4 of Dentcheva and Ruszczyński's paper on dominance-constrained stochastic optimization, using the shared utility class $\mathcal U_1([a,b])$.
--
--   1. **The imported utility class** $\mathcal U_1([a,b])$ (p. 7) is the set of functions $u:\mathbb R\to\mathbb R$ such that $u$ is concave and nondecreasing, $u(t)=0$ for all $t\ge b$, and
--   $$u(t)=u(a)+c\,(t-a)\qquad\text{for all } t\le a,$$
--   with some constant $c\ge 0$.
--   2. **The left derivative** $v'_-(a)$ of $v$ at $a$ is the derivative of $v$ at $a$ within the half-line $(-\infty,a]$. For $v\in\mathcal U_1([a,b])$ it equals the slope $c$ of $v$ on $(-\infty,a]$.
--   3. **The concave conjugate** (p. 12) of $v:\mathbb R\to\mathbb R$ is
--   $$v^*(\xi)=\inf_{t\in\mathbb R}\,[\xi t-v(t)]\in[-\infty,+\infty),$$
--   and for a random variable $\zeta$, $v^*(\zeta)$ is the extended-real random variable $\omega\mapsto v^*(\zeta(\omega))$.
--   4. **The dual functional** of a dominance constraint with reference outcome $Y$ (eq. (34), p. 12) is
--   $$D(w,\zeta)=\sup_{X\in\mathcal L_1}\mathbb E\big[w(X)-w(Y)-\zeta X\big]\in\overline{\mathbb R}.$$
--   5. **The functional** $f$ of eq. (35), p. 13, is $f(v,\zeta)=-\mathbb E\,v^*(\zeta)$. Since $-v^*(\zeta(\omega))=\sup_t[v(t)-\zeta(\omega)t]\ge v(0)$, this expectation is a well-defined element of $(-\infty,+\infty]$.
--
--   These objects carry the paper's decomposition of the Lagrangian dual of a stochastic-dominance-constrained problem: $D$ is the part of the dual functional contributed by one dominance constraint, with utility multiplier $w$ and almost-sure multiplier $\zeta$.
--
--   **Formalization Note** The paper prints "with some $c>0$" in the definition of $\mathcal U_1([a,b])$; the imported shared definition uses $c\ge 0$. The page itself calls $\mathcal U_1([a,b])$ a convex cone, which must contain $u=0$, and Theorem 2 of the paper is false with $c>0$. The left derivative is Lean's `derivWithin v (Set.Iic a) a`. Both $v^*$ and $D$ take values in `EReal`, so an infimum that is $-\infty$ is $\bot$ and an unbounded supremum is $\top$, never a junk real $0$. The supremum in $D$ runs over integrable $X$ (the page's $\mathcal L_1$). The expectation in $f$ is the Bochner integral of the real part of $-v^*(\zeta)$ when $v^*(\zeta)$ is almost surely finite and its real part is integrable, and $+\infty$ otherwise; because $-v^*(\zeta)\ge v(0)$, this is exactly the extended-real expectation.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), pp. 7, 12–13, definition of 𝒰₁([a,b]), concave conjugate (p. 12), Eqs. (34), (35)

import Mathlib
import Definitions.Def_NonlinSSD_Optimality_Basic

namespace NonlinSSD.DualFunctional

open MeasureTheory

/-- The left derivative `v′₋(a)`: the derivative of `v` at `a` within `(−∞, a]`. For `v ∈ 𝒰₁([a, b])`
it is the slope `c` of `v` on `(−∞, a]`. -/
noncomputable def leftDeriv (v : ℝ → ℝ) (a : ℝ) : ℝ :=
  derivWithin v (Set.Iic a) a

/-- p. 12: the concave conjugate `v^*(ξ) = inf_t [ξ t − v(t)]`, with values in `[−∞, +∞)`, computed in
`EReal` so that an unbounded-below infimum is `⊥ = −∞`. -/
noncomputable def concaveConj (v : ℝ → ℝ) (ξ : ℝ) : EReal :=
  ⨅ t : ℝ, ((ξ * t - v t : ℝ) : EReal)

/-- (34), p. 12: the dual functional of the `i`-th dominance constraint,
`D_i(w, ζ) = sup_{X ∈ 𝓛₁} 𝔼[w(X) − w(Y_i) − ζ X]`, in `EReal`. The supremum ranges over integrable
random variables `X` (the page's `𝓛₁`); `Y` is the reference outcome `Y_i`. -/
noncomputable def dualD {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ)
    (w : ℝ → ℝ) (ζ : Ω → ℝ) : EReal :=
  ⨆ (X : Ω → ℝ) (_ : Integrable X P), ((∫ ω, (w (X ω) - w (Y ω) - ζ ω * X ω) ∂P : ℝ) : EReal)

/-- (35), p. 13: `f(v, ζ) = −𝔼 v^*(ζ)`. The random variable `−v^*(ζ(ω)) = sup_t [v(t) − ζ(ω) t]` takes
values in `(−∞, +∞]` and is bounded below by `v(0)`, so its expectation is a well-defined element of
`(−∞, +∞]`: it is the (finite) Bochner integral when `v^*(ζ)` is a.s. finite with integrable real part,
and `+∞` otherwise. -/
noncomputable def fFun {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (v : ℝ → ℝ) (ζ : Ω → ℝ) :
    EReal :=
  open Classical in
  if (∀ᵐ ω ∂P, concaveConj v (ζ ω) ≠ ⊥) ∧ Integrable (fun ω => (concaveConj v (ζ ω)).toReal) P then
    ((-∫ ω, (concaveConj v (ζ ω)).toReal ∂P : ℝ) : EReal)
  else ⊤

end NonlinSSD.DualFunctional


