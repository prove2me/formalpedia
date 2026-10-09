-- Prove2me | Definitions.Def_DistCov_Hilbert_Setting
-- name    : DistCov_Hilbert_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:00.753342+00:00
-- url     : https://prove2.me/theorems/229889d2-2897-4c62-9674-ccc58094a37d
-- title:
--   pp. 3, 9, 11, 18–19 — finite first moment, D(µ₁ − µ₂), (strong) negative type, ℓ²(ℤ⁺), ρ, c, w(u), ϕ(u), (v, w), β_ϕ(µ₁ − µ₂)
-- statement:
--   This file fixes the objects of Lyons, *Distance covariance in metric spaces*, used in the proof that separable Hilbert spaces have strong negative type.
--
--   **Metric-space objects (§2–§3).** Let $(\mathscr X,d)$ be a metric space with its Borel $\sigma$-field.
--
--   1. A finite (positive) Borel measure $\mu$ on $\mathscr X$ has a **finite first moment** if $\int d(o,x)\,d\mu(x)<\infty$ for some $o\in\mathscr X$ (p. 3).
--   2. For two finite measures $\mu_1,\mu_2$, the **energy** is $E(\mu_1,\mu_2)=\iint d(x,x')\,d\mu_1(x)\,d\mu_2(x')$, and
--   $$D(\mu_1-\mu_2) := E(\mu_1,\mu_1) - 2E(\mu_1,\mu_2) + E(\mu_2,\mu_2),$$
--   the bilinear expansion of $D(\mu)=\int d(x,x')\,d\mu^2(x,x')$ at the signed measure $\mu=\mu_1-\mu_2$ (p. 3).
--   3. $(\mathscr X,d)$ has **negative type** (3.1) if for all $n$, all $x_1,\dots,x_n\in\mathscr X$ and all $\alpha_1,\dots,\alpha_n\in\mathbb R$ with $\sum_i\alpha_i=0$,
--   $$\sum_{i,j\le n}\alpha_i\alpha_j\,d(x_i,x_j)\le 0 .$$
--   4. $(\mathscr X,d)$ has **strong negative type** (p. 11) if it has negative type and, for probability measures $\mu_1,\mu_2$ with finite first moments, $D(\mu_1-\mu_2)=0$ only when $\mu_1=\mu_2$.
--
--   **Gaussian objects (p. 18).** Let $\ell^2(\mathbb Z^+)$ be the space of square-summable real sequences with its Borel $\sigma$-field. Let $\rho$ be the law on $\mathbb R^\infty$ of an IID sequence $Z_1,Z_2,\dots$ of standard normal variables, $\lambda$ Lebesgue measure on $\mathbb R$, and $c:=\mathbf E|Z_1|$. For $w,u\in\mathbb R^\infty$ put
--   $$w(u):=\limsup_N\sum_{n=1}^N u_nw_n ,$$
--   and for $u\in\mathbb R^\infty$ let $\phi(u)$ be the function on $\mathbb R^\infty\times\mathbb R$
--   $$\phi(u):(w,s)\mapsto \mathbf 1_{[w(u)/c,\infty)}(s)-\mathbf 1_{[0,\infty)}(s).$$
--   For $K\ge0$, $v\in\mathbb R^K$ and $w\in\mathbb R^\infty$, $(v,w)\in\mathbb R^\infty$ is the sequence whose first $K$ coordinates are those of $v$ and whose remaining coordinates are those of $w$ (p. 19). Finally, for probability measures $\mu_1,\mu_2$ on $\ell^2(\mathbb Z^+)$,
--   $$\beta_\phi(\mu_1-\mu_2):(w,s)\mapsto \mu_1\{u\,;\,w(u)\le cs\}-\mu_2\{u\,;\,w(u)\le cs\},$$
--   the barycenter of $\mu_1-\mu_2$ under $\phi$, written as a function (p. 18).
--
--   These are the objects in which the paper proves Theorem 3.16 and the milestones of this mission are stated.
--
--   **Formalization Note.** $D(\mu_1-\mu_2)$ is the three-term energy expansion because Mathlib's Bochner integral does not integrate against signed measures; the cross terms $E(\mu_1,\mu_2)$ and $E(\mu_2,\mu_1)$ agree by symmetry of $d$ and Fubini. Bochner integrals of non-integrable functions are $0$ in Lean, so every theorem using $D$ carries finite-first-moment hypotheses. The case $n=0$ of (3.1) is harmless (both sides are $0$). Sequences are indexed from $0$: the paper's $Z_1,Z_2,\dots$ and $\ell^2(\mathbb Z^+)$ are `ℕ`-indexed, $\sum_{n=1}^N$ is `Finset.range N`, and $(v,w)$ takes coordinates $0,\dots,K-1$ from $v$. $\ell^2(\mathbb Z^+)$ is Mathlib's `lp (fun _ : ℕ => ℝ) 2`, which carries no $\sigma$-field in Mathlib; the file declares the Borel one. $\limsup$ is taken in $\mathbb R$ (a conditionally complete lattice), so on a divergent or unbounded sequence it returns a junk value instead of $\pm\infty$; for $u\in\ell^2$ the series converges $\rho$-a.s., so the junk affects only null sets, and every statement about $w(u)$ is made $\rho$-a.e. or under an integral. $c$ is defined as the integral $\int|z|\,dN(0,1)(z)$, not by its closed form $\sqrt{2/\pi}$. $\phi(u)$ is a plain function rather than an element of $L^2(\rho\times\lambda)$; the $L^2$ norms of the paper are written as integrals of these functions. $\mu\{\cdot\}$ is the real-valued measure `μ.real`.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 3 (§2), p. 9 (3.1), p. 11 (3.3) and strong negative type, pp. 18–19 (proof of Theorem 3.16); Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Hilbert

open MeasureTheory ProbabilityTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The Borel σ-field on ℓ²(ℤ⁺) (Mathlib supplies none on `lp`). -/
noncomputable instance : MeasurableSpace DistCov.Indep.L2N := borel DistCov.Indep.L2N

instance : BorelSpace DistCov.Indep.L2N := ⟨rfl⟩

/-- ρ: the law of an IID standard normal sequence on ℝ^∞ (p. 18). -/
noncomputable def rho : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

/-- c := E|Z₁| (p. 18). Defined as the integral, not as its closed form √(2/π). -/
noncomputable def cGauss : ℝ := ∫ z, |z| ∂(gaussianReal 0 1)

/-- w(u) := limsup_N Σ_{n<N} u_n w_n (p. 18; 0-based). -/
noncomputable def wEval (w u : ℕ → ℝ) : ℝ :=
  Filter.limsup (fun N : ℕ => ∑ n ∈ Finset.range N, u n * w n) Filter.atTop

/-- ϕ(u)(w, s) := 𝟏_{[w(u)/c, ∞)}(s) − 𝟏_{[0, ∞)}(s) (p. 18), as a plain function on ℝ^∞ × ℝ. -/
noncomputable def gaussEmb (u : ℕ → ℝ) (p : (ℕ → ℝ) × ℝ) : ℝ :=
  Set.indicator (Set.Ici (wEval p.1 u / cGauss)) (fun _ => (1 : ℝ)) p.2
    - Set.indicator (Set.Ici 0) (fun _ => (1 : ℝ)) p.2

/-- (v, w): the first K coordinates from v ∈ ℝ^K, the rest from w (p. 19). -/
def splice (K : ℕ) (v : Fin K → ℝ) (w : ℕ → ℝ) : ℕ → ℝ := fun n => if h : n < K then v ⟨n, h⟩ else w n

/-- F(w, s) := µ₁{u ; w(u) ≤ cs} − µ₂{u ; w(u) ≤ cs}: β_ϕ(µ₁ − µ₂) as a function (p. 18). -/
noncomputable def baryDiff (μ₁ μ₂ : Measure DistCov.Indep.L2N) (p : (ℕ → ℝ) × ℝ) : ℝ :=
  μ₁.real {u | wEval p.1 u ≤ cGauss * p.2} - μ₂.real {u | wEval p.1 u ≤ cGauss * p.2}

end DistCov.Hilbert


