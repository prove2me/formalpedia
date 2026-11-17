-- Prove2me | Definitions.Def_ThinShellSampling_Supplement_psExpAttempt
-- name    : ThinShellSampling_Supplement_psExpAttempt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:38:41.368195+00:00
-- url     : https://prove2.me/theorems/e5b4cf49-546d-4e31-bc76-ba7976edb5ef
-- title:
--   One attempt of $\mathsf{PS}_{\exp}$ (proximal sampler on the exponential lift with rejection cap $\tau$)
-- statement:
--   Let $V:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be given by an evaluation oracle. The **exponential lift** of $\pi\propto e^{-V}$ is
--
--   $$
--   \pi^{X,T}(dx\,dt)\propto e^{-nt}\,1_{\mathcal K}(x,t)\,dx\,dt,\qquad \mathcal K=\{(x,t)\in\mathbb R^n\times\mathbb R:\ V(x)\le nt\},
--   $$
--
--   whose $X$-marginal is $\pi$. Fix $h>0$, $\tau\in\mathbb N$, $N$ and an initial distribution $\pi_0$. One **attempt of $\mathsf{PS}_{\exp}$**:
--
--   1. **Initialization:** draw $X'\sim\pi_0$, query $V(X')$, and set $T'=V(X')/n+E/n$ with $E\sim\mathrm{Exp}(1)$, i.e. $T'\sim\pi^{T|X=X'}\propto e^{-nt}$ on $[V(X')/n,\infty)$; put $z_0=(X',T')$.
--   2. For $k=0,\dots,N-1$: **forward** $y\sim\mathcal N(z_k,hI_{n+1})$; **backward** propose $z'=(x',t')\sim\mathcal N(y-hn\,e_{n+1},hI_{n+1})$, query $V(x')$ and accept iff $V(x')\le nt'$, i.e. $z'\in\mathcal K$; after $\tau$ rejected proposals the attempt declares failure.
--   3. Return the $X$-component of $z_N$.
--
--   Each evaluation of $V$ costs one query. This is the attempt of Theorem 1.6; the algorithm of that theorem is its restart-until-success wrapper.
--
--   **Formalization Note** $\pi_0$ enters through a measurable $g:\mathbb R\to\mathbb R^n$ with $g_\#\mathrm{Uniform}[0,1]=\pi_0$; $E=-\log u$ for a uniform $u$; Gaussians come from Box–Muller. If $V(X')=+\infty$ (a $\pi_0$-null event when $\pi_0\ll\pi$) the attempt declares failure. The lift is the untruncated one of (exp-lifting), not the truncated $\bar{\mathcal K}$ of §6.2.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §6.1, p.34 (PDF p.36): (exp-lifting), the definition of PS_exp and the initialization T′ ∼ π^{T|X=X′}; Theorem 1.6, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_ThinShellSampling_psAnnAttempt

set_option autoImplicit false

namespace ThinShellSampling.Supplement

open MeasureTheory

/-- **The rejection loop of the backward step of `PS_exp`** from `y = (y_x, y_t) ∈ ℝⁿ × ℝ`, with at
most `k` trials remaining. Each trial draws `z' = (x', t') ∼ N(y − h n e_{n+1}, h I_{n+1})`, spends
**one** evaluation query on `V(x')`, and accepts iff `z' ∈ K = {V(x) ≤ nt}`. After `k` rejected
trials it declares failure (`none`).

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §6.1, p.34 (PDF p.36):
"`z ∼ π^{Z|Y=y} ∝ N(y − hα, hI_{n+1})|_K` for `α = n e_{n+1}`, where the second step is implemented
via rejection sampling, using the proposal `N(y − hα, hI_{n+1})` with threshold `τ`". -/
noncomputable def expBackward (n : ℕ) (h : ℝ) (y : EuclideanSpace ℝ (Fin n) × ℝ) :
    ℕ → Prog n (Option (EuclideanSpace ℝ (Fin n) × ℝ))
  | 0 => .pure none
  | k + 1 =>
    (gaussVec n).bind fun G => (stdNormal n).bind fun g =>
      let x := y.1 + Real.sqrt h • G
      let t := y.2 - h * n + Real.sqrt h * g
      .query x fun v =>
        if v ≤ (((n : ℝ) * t : ℝ) : WithTop ℝ) then .pure (some (x, t))
        else expBackward n h y k

/-- `N` iterations of `PS_exp` from `z = (x, t)`: forward `y ∼ N(z, h I_{n+1})`, then the capped
backward rejection loop with `τ` trials; `none` as soon as one backward step fails. -/
noncomputable def expLoop (n : ℕ) (h : ℝ) (τ : ℕ) :
    ℕ → EuclideanSpace ℝ (Fin n) × ℝ → Prog n (Option (EuclideanSpace ℝ (Fin n) × ℝ))
  | 0, z => .pure (some z)
  | N + 1, z =>
    (gaussVec n).bind fun G => (stdNormal n).bind fun g =>
      (expBackward n h (z.1 + Real.sqrt h • G, z.2 + Real.sqrt h * g) τ).bind fun o =>
        match o with
        | none => .pure none
        | some z' => expLoop n h τ N z'

/-- **One attempt of `PS_exp`** (the proximal sampler on the exponential lift
`π^{X,T}(dx dt) ∝ e^{−nt} 1_K(x, t) dx dt`, `K = {(x, t) : V(x) ≤ nt}`) with step size `h`,
threshold `τ` and `N` iterations, returning the `X`-component of `z_N`, or `none` on failure.

Initialization: `X' = g(u)` for one uniform `u` (no query), one evaluation query of `V(X')`, and
`T' = V(X')/n + E/n` with `E = −log u' ∼ Exp(1)`, i.e. `T' ∼ π^{T|X=X'} ∝ e^{−nt}` on
`[V(X')/n, ∞)`.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with
Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256 25a041a9…), §6.1,
p.34 (PDF p.36), (exp-lifting) and "one can generate a sample `(X', T')` whose joint law is also
`M_q`-warm with respect to `π^{X,T}` by first drawing `X' ∼ π₀^X` and then sampling
`T' ∼ π^{T|X=X'} ∝ e^{−nt}|_{[V(X')/n, ∞)}`"; Theorem 1.6, p.5 (PDF p.7).

**Formalization Note.** `π₀` enters through a measurable `g : ℝ → ℝⁿ` with push-forward of
`Uniform[0, 1]` equal to `π₀`. If `V(X') = ∞` (a `π₀`-null event when `π₀ ≪ π`) the attempt
declares failure. The lift is the untruncated one of (exp-lifting), not the truncated `K̄` of §6.2.
Gaussians and the exponential variable come from the uniform stream at no query cost. -/
noncomputable def psExpAttempt (n : ℕ) (h : ℝ) (τ N : ℕ) (g : ℝ → EuclideanSpace ℝ (Fin n)) :
    Prog n (Option (EuclideanSpace ℝ (Fin n))) :=
  .sample fun u =>
    .query (g u) fun v =>
      if hv : v = ⊤ then .pure none
      else
        .sample fun u' =>
          (expLoop n h τ N (g u, v.untop hv / n + (-Real.log u') / n)).bind fun o =>
            .pure (o.map Prod.fst)

end ThinShellSampling.Supplement


