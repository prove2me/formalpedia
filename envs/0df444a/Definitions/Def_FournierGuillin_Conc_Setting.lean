-- Prove2me | Definitions.Def_FournierGuillin_Conc_Setting
-- name    : FournierGuillin_Conc_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:22:21.515256+00:00
-- url     : https://prove2.me/theorems/6221b220-dbe5-4d86-a2e7-86b1e11549bd
-- title:
--   pp. 1–2, Notation 4 (pp. 5–6), Notation 7 (p. 9), pp. 10, 14, 19 — 𝒯_p, M_q, ℰ_{α,γ}, κ_{p,d}, 𝒫_ℓ, B_n, ℛ_{B_n}, 𝒟_p, f, g, Π_N, Z^p_N, V^p_N, rates
-- statement:
--   Throughout, $\mathbb R^d$ ($d\ge 1$) carries the Euclidean norm $|x|$, and $\mathcal P(\mathbb R^d)$ is the set of Borel probability measures on it. For a sample $X_1,\dots,X_N$ the **empirical measure** is $\mu_N=\frac1N\sum_{k=1}^N\delta_{X_k}$ (the published definition `WassersteinDRO.Duality.empiricalDistribution`).
--
--   1. **Transport cost.** For $p>0$ and measures $\mu,\nu$,
--   $$\mathcal T_p(\mu,\nu)=\inf\Big\{\int_{\mathbb R^d\times\mathbb R^d}|x-y|^p\,\xi(dx,dy):\ \xi\in\mathcal H(\mu,\nu)\Big\},$$
--   where $\mathcal H(\mu,\nu)$ is the set of couplings (measures on $\mathbb R^d\times\mathbb R^d$ with marginals $\mu$ and $\nu$). No $1/p$ root is taken.
--   2. **Moments.** $M_q(\mu)=\int|x|^q\,\mu(dx)$ and $\mathcal E_{\alpha,\gamma}(\mu)=\int e^{\gamma|x|^\alpha}\,\mu(dx)$.
--   3. **The constant** $\kappa_{p,d}=2^{p(1+d/2)}(2^p+1)/(2^p-1)$ of Lemma 5.
--   4. **Dyadic cubes and shells (Notation 4).** For $\ell\ge0$, $\mathcal P_\ell$ is the partition of $(-1,1]^d$ into the $2^{d\ell}$ translates of $(-2^{-\ell},2^{-\ell}]^d$. $B_0=(-1,1]^d$ and $B_n=(-2^n,2^n]^d\setminus(-2^{n-1},2^{n-1}]^d$ for $n\ge1$. $\mathcal R_{B_n}\mu$ is the image of $\mu|_{B_n}/\mu(B_n)$ under $x\mapsto x/2^n$.
--   5. **The distances $\mathcal D_p$.** For measures on $(-1,1]^d$,
--   $$\mathcal D_p(\mu,\nu)=\frac{2^p-1}{2}\sum_{\ell\ge1}2^{-p\ell}\sum_{F\in\mathcal P_\ell}|\mu(F)-\nu(F)|$$
--   (called `Dcube`), and for measures on $\mathbb R^d$
--   $$\mathcal D_p(\mu,\nu)=\sum_{n\ge0}2^{pn}\Big(|\mu(B_n)-\nu(B_n)|+(\mu(B_n)\wedge\nu(B_n))\,\mathcal D_p(\mathcal R_{B_n}\mu,\mathcal R_{B_n}\nu)\Big)$$
--   (called `Dp`).
--   6. **Notation 7.** $f(x)=(1+x)\log(1+x)-x$ and $g(x)=(x\log x-x+1)\mathbf 1_{\{x\ge1\}}$.
--   7. **Poisson measure.** $\Pi_N$ is a Poisson random measure with intensity $N\mu$: it has a Poisson($N$)-distributed number $n$ of points, which given $n$ are i.i.d. with law $\mu$. `poissonProb N μ E` is the probability that the configuration lies in $E$, i.e. $\sum_{n\ge0}\mathbb P(\mathrm{Poisson}(N)=n)\,\mu^{\otimes n}(E_n)$.
--   8. **The two parts of $\mathcal D_p(\mu_N,\mu)$ (pp. 14, 19).** $Z^p_N=\sum_{n\ge0}2^{pn}|\mu_N(B_n)-\mu(B_n)|$ and $V^p_N=\sum_{n\ge0}2^{pn}\mu(B_n)\,\mathcal D_p(\mathcal R_{B_n}\mu_N,\mathcal R_{B_n}\mu)$.
--   9. **Rates.** $a(N,x)/C$ of Theorem 2: $e^{-cNx^2}$ if $p>d/2$, $e^{-cN(x/\log(2+1/x))^2}$ if $p=d/2$, $e^{-cNx^{d/p}}$ otherwise (`rateA`); and the right side of Proposition 8 divided by $C$: $e^{-Nf(cx)}$, $e^{-Nf(cx/\log(2+1/x))}$, $e^{-Nf(cx)}+e^{-cNx^{d/p}}$ in the same three cases (`rate8`).
--
--   These are the objects of Theorem 2 and of the lemmas and propositions of §§2, 4–6 on which its proof rests.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. Costs, moments, $\mathcal D_p$, $Z^p_N$, $V^p_N$ and Poisson probabilities are valued in $[0,\infty]$, so a divergent integral or series is $+\infty$ and never a junk $0$. The sum over $\ell\ge1$ in `Dcube` is a sum over all $\ell\in\mathbb N$ whose $\ell=0$ term is $0$. Masses enter the absolute values through `toReal`, which is faithful because every measure involved is finite. When $\mu(B_n)=0$ the page leaves $\mathcal R_{B_n}\mu$ undefined; here it is the zero measure, and every use multiplies it by $\mu(B_n)$ or $\mu(B_n)\wedge\nu(B_n)$. The page uses one symbol $\mathcal D_p$ for both distances; the formalization uses two names. The third branch of the rates is the page's "if $p\in[1,d/2)$" in Theorem 2, display (6) and Proposition 8, which assume $p\ge d/2$ or $p\ge1$, so there it is reached only for $p\in[1,d/2)$; Proposition 10 prints it as "if $p\in(0,d/2)$" and is posed for every $p>0$.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, §1.1 p. 1 (μ_N, 𝒯_p, ℋ); p. 2 (M_q, ℰ_{α,γ}); Lemma 5 p. 6 (κ_{p,d}); Notation 4, pp. 5–6; Notation 7, p. 9; Proposition 8, p. 10 (Π_N, Ψ_N) and proof of Proposition 10, Step 1, p. 13; Lemma 13, p. 14 (Z^p_N); proof of Theorem 2, p. 19 (V^p_N); Theorem 2, p. 3 (a(N, x))

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Moment_Setting
open MeasureTheory
open scoped ENNReal NNReal

namespace FournierGuillin.Conc

variable {d : ℕ}

/-- The exponential FournierGuillin.Moment.moment `ℰ_{α,γ}(μ) = ∫ e^{γ|x|^α} μ(dx)` (p. 2), valued in `ℝ≥0∞`. -/
noncomputable def expMoment (α γ : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (γ * ‖x‖ ^ α)) ∂μ

/-- The constant `κ_{p,d} = 2^{p(1+d/2)}(2^p + 1)/(2^p - 1)` of Lemma 5 (p. 6). -/
noncomputable def kappa (d : ℕ) (p : ℝ) : ℝ :=
  (2 : ℝ) ^ (p * (1 + (d : ℝ) / 2)) * ((2 : ℝ) ^ p + 1) / ((2 : ℝ) ^ p - 1)

/-- `f(x) = (1 + x) log(1 + x) - x` (Notation 7, p. 9); only `x > 0` is used. -/
noncomputable def bennettF (x : ℝ) : ℝ :=
  (1 + x) * Real.log (1 + x) - x

/-- `g(x) = (x log x - x + 1) 1_{x ≥ 1}` (Notation 7, p. 9); only `x > 0` is used. -/
noncomputable def bennettG (x : ℝ) : ℝ :=
  if 1 ≤ x then x * Real.log x - x + 1 else 0

/-- `ℙ(Π_N ∈ E)` for the Poisson measure `Π_N` on `ℝ^d` with intensity `N·μ` (Proposition 8, p. 10),
for a probability measure `μ`. `Π_N` is described by its law: it has Poisson(`N`)-many points and,
given that there are `n` of them, they are i.i.d. with law `μ` (the representation the page uses on
p. 13). `E n` is the event for a configuration `ω : Fin n → ℝ^d` of `n` points; for such a
configuration `Π_N(ℝ^d) = n`, `Π_N(F) = #{i : ω i ∈ F}` and `Ψ_N` is the empirical measure of `ω`. -/
noncomputable def poissonProb (N : ℝ≥0) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (E : (n : ℕ) → Set (Fin n → EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∑' n : ℕ, ProbabilityTheory.poissonMeasure N {n} * Measure.pi (fun _ : Fin n => μ) (E n)

/-- `Z^p_N = Σ_{n ≥ 0} 2^{pn} |μ_N(B_n) - μ(B_n)|` (Lemma 13, p. 14), as a function of the sample
`ω = (X_1, …, X_N)`; `μ_N` is the empirical measure of `ω`. -/
noncomputable def Zp {N : ℕ} (p : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (ω : Fin N → EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (p * (n : ℝ))) *
    ENNReal.ofReal
      |(WassersteinDRO.Duality.empiricalDistribution ω (FournierGuillin.Moment.shell n)).toReal - (μ (FournierGuillin.Moment.shell n)).toReal|

/-- `V^p_N = Σ_{n ≥ 0} 2^{pn} μ(B_n) 𝒟_p(ℛ_{B_n}μ_N, ℛ_{B_n}μ)` (proof of Theorem 2, p. 19), as a
function of the sample `ω`; the inner `𝒟_p` is the compact one, `Dcube`. -/
noncomputable def Vp {N : ℕ} (p : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (ω : Fin N → EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (p * (n : ℝ))) * μ (FournierGuillin.Moment.shell n) *
    FournierGuillin.Moment.Dcube p (FournierGuillin.Moment.rescale n (WassersteinDRO.Duality.empiricalDistribution ω)) (FournierGuillin.Moment.rescale n μ)

/-- `a(N, x)/C` of Theorem 2 (p. 3):
`exp(-cNx²)` if `p > d/2`, `exp(-cN(x/log(2 + 1/x))²)` if `p = d/2`, `exp(-cNx^{d/p})` otherwise.
Theorem 2 and display (6) print the third case as "if `p ∈ [1, d/2)`" and assume `p ≥ d/2` or
`p ≥ 1`, so there the third branch is only reached for `p ∈ [1, d/2)`; Proposition 10 prints it as
"if `p ∈ (0, d/2)`" and is posed for every `p > 0`. -/
noncomputable def rateA (d : ℕ) (p c : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if (d : ℝ) / 2 < p then Real.exp (-(c * N * x ^ 2))
  else if p = (d : ℝ) / 2 then Real.exp (-(c * N * (x / Real.log (2 + 1 / x)) ^ 2))
  else Real.exp (-(c * N * x ^ ((d : ℝ) / p)))

/-- The right side of Proposition 8 (p. 10) divided by `C`:
`exp(-N f(cx))` if `p > d/2`, `exp(-N f(cx/log(2 + 1/x)))` if `p = d/2`,
`exp(-N f(cx)) + exp(-cNx^{d/p})` otherwise (printed: "if `p ∈ [1, d/2)`"). -/
noncomputable def rate8 (d : ℕ) (p c : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if (d : ℝ) / 2 < p then Real.exp (-(N * bennettF (c * x)))
  else if p = (d : ℝ) / 2 then Real.exp (-(N * bennettF (c * x / Real.log (2 + 1 / x))))
  else Real.exp (-(N * bennettF (c * x))) + Real.exp (-(c * N * x ^ ((d : ℝ) / p)))

end FournierGuillin.Conc


