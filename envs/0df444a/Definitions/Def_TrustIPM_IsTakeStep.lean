-- Prove2me | Definitions.Def_TrustIPM_IsTakeStep
-- name    : TrustIPM_IsTakeStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:56.252207+00:00
-- url     : https://prove2.me/theorems/74b70dde-e79b-4b12-8680-acee2a0ad245
-- title:
--   Algorithm 1 (Trust-IPM, Take-step) and Definitions 2–3 ((SIP1), corrected (SIP2))
-- statement:
--   **Take-step** at $x\in\mathcal X$ with parameter $\eta$: set $S=\mathrm{diag}(a(x))$, $y=\mu S^{-1}\mathbf 1$, radius $r=\frac\eta2\sqrt{\mu/(L_1(1+\|y\|_1))}$, pick
--
--   $$
--   d_x\in\operatorname*{argmin}_{u\in B_r(0)}\mathcal M^{\psi_\mu}_x(u),
--   $$
--
--   set $d_s=\nabla a(x)d_x$, $d_y=-\mu S^{-2}d_s$, step size $\alpha=\min\{\eta/\|S^{-1}d_s\|_2,1\}$, and return $x^+=x+\alpha d_x$, $y^+=y+\alpha d_y$.
--
--   **Trust-IPM** starts at $x^{(0)}$ and, for $k=0,1,\dots$, calls Take-step at the current $x$; it returns $(x^+,y^+)$ as soon as this pair satisfies (SIP1) and (SIP2), and otherwise continues from $x^+$.
--
--   A pair $(x,y)$ is a **$(\mu,\tau_l,\tau_c)$-approximate first-order SIP** (SIP1) if $(a(x),y)>0$, $|y_ia_i(x)-\mu|\le\tau_c\mu/2$ for every $i$, and $\|\nabla_x\mathcal L(x,y)\|_2\le\tau_l\mu\sqrt{\|y\|_1+1}$. It is **second-order** if moreover
--
--   $$
--   \nabla^2_{xx}\mathcal L(x,y)+\mu\nabla a(x)^TS^{-2}\nabla a(x)\succeq-\tau_c^{1/2}L_1(1+\|y\|_1)I .\qquad\text{(SIP2)}
--   $$
--
--   **Formalization Note** Take-step is a relation, because the argmin can have several elements; a run is a sequence of iterates, directions and dual outputs with each step a Take-step, continuing past termination (Trust-IPM returns at the first index $k$ where $(x_{k+1},y_k)$ passes the test, after $k+1$ calls). The step size is $1$ when $S^{-1}d_s=0$ ($\eta/0=+\infty$ on the page). $A\succeq cI$ is the quadratic-form inequality $u^TAu\ge c\|u\|_2^2$ for all $u$. The page prints (SIP2) with $+\tau_c^{1/2}L_1(1+\|y\|_1)I$; the sign here is the one the proofs of Lemma 3 (p.7) and Lemma 11 (p.19) use and derive, since with the printed sign Theorem 1 is false (see Theorem 1).
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Algorithm 1, p.5; Definition 2 and Definition 3, p.7 ((SIP2) sign corrected per the proofs of Lemma 3, p.7, and Lemma 11, p.19)

import Mathlib
import Definitions.Def_TrustIPM_barrier
open scoped InnerProductSpace RealInnerProductSpace

namespace TrustIPM

/-- The **trust-region radius** of Take-step, `r = (η/2)·(µ/(L₁(1 + ‖y‖₁)))^{1/2}` with
`y = µS⁻¹1` (Hinder & Ye, *Worst-case iteration bounds for log barrier methods on problems with
nonconvex constraints*, arXiv:1807.00404v5, Algorithm 1, line 16, p.5). -/
noncomputable def trRadius {n m : ℕ} (a : Fin m → E n → ℝ) (μ L₁ η : ℝ) (x : E n) : ℝ :=
  η / 2 * Real.sqrt (μ / (L₁ * (1 + norm1 (centralDual a μ x))))

/-- `d` is a **trust-region direction** of Take-step at `x`:
`d ∈ argmin_{u ∈ B_r(0)} M^{ψµ}_x(u)` with `r` from line 16 (Hinder & Ye, arXiv:1807.00404v5,
Algorithm 1, line 17, p.5).

**Formalization Note** The argmin is a set; Take-step picks any element of it, so the algorithm is a
relation. `d ∈ argmin` is `d ∈ B_r(0)` together with `IsMinOn` over the closed Euclidean ball. -/
def IsTRDirection {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (μ L₁ η : ℝ) (x d : E n) :
    Prop :=
  d ∈ Metric.closedBall (0 : E n) (trRadius a μ L₁ η x) ∧
    IsMinOn (model f a μ x) (Metric.closedBall (0 : E n) (trRadius a μ L₁ η x)) d

/-- The dual direction `d_y = −µS⁻²d_s`, `d_s = ∇a(x)d`, i.e. `(d_y)ᵢ = −µ ∇aᵢ(x)ᵀd / aᵢ(x)²`
(Hinder & Ye, arXiv:1807.00404v5, Algorithm 1, lines 18–19, p.5). -/
noncomputable def dualDir {n m : ℕ} (a : Fin m → E n → ℝ) (μ : ℝ) (x d : E n) : Fin m → ℝ :=
  fun i => -μ * jac a x d i / a i x ^ 2

/-- The **step size** `α = min{η/‖S⁻¹d_s‖₂, 1}` (Hinder & Ye, arXiv:1807.00404v5, Algorithm 1,
line 20, p.5).

**Formalization Note** On the page `η/0 = +∞`, so `α = 1` when `S⁻¹d_s = 0`; this is written out,
since Lean's `η/0 = 0` would give `α = 0`. -/
noncomputable def stepSize {n m : ℕ} (a : Fin m → E n → ℝ) (η : ℝ) (x d : E n) : ℝ :=
  if norm2 (scaledSlackDir a x d) = 0 then 1 else min (η / norm2 (scaledSlackDir a x d)) 1

/-- **Take-step** as a relation (Hinder & Ye, arXiv:1807.00404v5, Algorithm 1, lines 13–24, p.5):
`(x⁺, y⁺)` is a possible output of `Take-step(f, a, µ, x, η)` when the direction `d` chosen on line 17
is `d`. With `S = diag(a(x))`, `y = µS⁻¹1`, `d_s = ∇a(x)d`, `d_y = −µS⁻²d_s` and `α` from line 20,
`x⁺ = x + αd` and `y⁺ = y + αd_y`.

**Formalization Note** `L₁` enters through the radius of line 16. The direction is an explicit
argument so that statements can quantify over every argmin selection. -/
def IsTakeStep {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (μ L₁ η : ℝ) (x d xp : E n)
    (yp : Fin m → ℝ) : Prop :=
  IsTRDirection f a μ L₁ η x d ∧ xp = x + stepSize a η x d • d ∧
    yp = centralDual a μ x + stepSize a η x d • dualDir a μ x d

/-- **Definition 2: `(µ, τ_l, τ_c)`-approximate first-order SIP** (Hinder & Ye, arXiv:1807.00404v5,
Definition 2, p.7): `(a(x), y) > 0` (SIP1.a), `|yᵢaᵢ(x) − µ| ≤ τ_cµ/2` for all `i` (SIP1.b), and
`‖∇ₓL(x, y)‖₂ ≤ τ_lµ(‖y‖₁ + 1)^{1/2}` (SIP1.c). -/
def SIP1 {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (μ τl τc : ℝ) (x : E n)
    (y : Fin m → ℝ) : Prop :=
  (∀ i, 0 < a i x) ∧ (∀ i, 0 < y i) ∧ (∀ i, |y i * a i x - μ| ≤ τc * μ / 2) ∧
    ‖gradLag f a x y‖ ≤ τl * μ * Real.sqrt (norm1 y + 1)

/-- **(SIP2), sign corrected** (Hinder & Ye, arXiv:1807.00404v5, Definition 3, p.7, with the sign the
proofs of Lemma 3, p.7, and Lemma 11, p.19, establish and use):
`∇²ₓₓL(x, y) + µ∇a(x)ᵀS⁻²∇a(x) ⪰ −τ_c^{1/2} L₁(1 + ‖y‖₁) I` with `S = diag(a(x))`.

**Formalization Note** `A ⪰ cI` is the quadratic-form inequality `uᵀAu ≥ c‖u‖₂²` for every `u`, and
`uᵀ∇a(x)ᵀS⁻²∇a(x)u = Σᵢ (∇aᵢ(x)ᵀu)²/aᵢ(x)²`. The page prints `+τ_c^{1/2}L₁(1 + ‖y‖₁)I`, under which
Theorem 1 is false (see the mission's Differences); the `−` sign is what Lemma 11's proof derives. -/
def SIP2 {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (μ τc L₁ : ℝ) (x : E n)
    (y : Fin m → ℝ) : Prop :=
  ∀ u : E n, -(Real.sqrt τc * L₁ * (1 + norm1 y)) * ‖u‖ ^ 2 ≤
    ⟪hessLag f a x y u, u⟫_ℝ + μ * ∑ i, jac a x u i ^ 2 / a i x ^ 2

/-- A **run of Trust-IPM** (Hinder & Ye, arXiv:1807.00404v5, Algorithm 1, lines 1–12, p.5): iterates
`xs k`, chosen directions `ds k` and dual outputs `ys k` with `xs 0 = x⁽⁰⁾` and, for every `k`,
`(xs (k+1), ys k)` an output of `Take-step(f, a, µ, xs k, η)` with direction `ds k`.

**Formalization Note** The sequence ignores the termination test, so it continues past the first `k`
at which `(xs (k+1), ys k)` satisfies (SIP1) and (SIP2); Trust-IPM returns that pair at loop index
`k`, after `k + 1` calls of Take-step. Line 9 keeps only `x⁺`, so the next Take-step depends on
`xs (k+1)` alone. -/
def IsRun {n m : ℕ} (f : E n → ℝ) (a : Fin m → E n → ℝ) (μ L₁ η : ℝ) (x₀ : E n)
    (xs ds : ℕ → E n) (ys : ℕ → Fin m → ℝ) : Prop :=
  xs 0 = x₀ ∧ ∀ k, IsTakeStep f a μ L₁ η (xs k) (ds k) (xs (k + 1)) (ys k)

end TrustIPM


