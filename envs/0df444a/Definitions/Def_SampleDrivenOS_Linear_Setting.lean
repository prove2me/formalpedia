-- Prove2me | Definitions.Def_SampleDrivenOS_Linear_Setting
-- name    : SampleDrivenOS_Linear_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:42.884014+00:00
-- url     : https://prove2.me/theorems/e832d245-895a-4d9b-95e3-e3da141aa282
-- title:
--   (19), Theorem 8 preamble, B.7 and B.9 — the equations for $\tilde\alpha(p)$ and $\alpha^*$, the functions $f(p,\alpha)$, $g(p,\alpha)$, $a(p)$, $b(p)$, $c(p)$
-- statement:
--   This file fixes the real-valued objects that Theorem 9 of Correa, Cristi, Epstein and Soto and its proof (Appendix B.9) are about. Throughout, $p\in(0,1)$ is the sampling probability of the $p$-sample-driven optimal stopping problem, and every series runs over $i=1,2,\dots$.
--
--   **The root $\tilde\alpha(p)$.** A number $a$ is a root of (19) when $0<a<1$ and
--   $$\ln p+\frac{a(1-p)^2}{p}=\sum_{i=1}^{\infty}\frac{\ln\bigl(1-a+a[(i+1)p^i-ip^{i+1}]\bigr)}{i(i+1)}.$$
--   Lemma 7 of the paper shows that for each $p\in(0,1)$ there is exactly one such root, called $\tilde\alpha(p)$; it is the competitive ratio guaranteed by the explicit threshold rule of §4.3.
--
--   **The constant $\alpha^*$.** A number $s$ is an $\alpha^*$ when $0<s<1$ and
--   $$\int_0^1\frac{dy}{y(1-\ln y)+1/s-1}=1.$$
--   This is the equation defining $\alpha^*\approx 0.745$, the optimal constant of the i.i.d. prophet inequality.
--
--   **The two sides of (19)** (Appendix B.7). For $p\in(0,1)$ and $\alpha\in\mathbb R$,
--   $$f(p,\alpha)=\ln p+\frac{\alpha(1-p)^2}{p},\qquad g(p,\alpha)=\sum_{i=1}^{\infty}\frac{\ln\bigl(1+\alpha(p^i(1+i(1-p))-1)\bigr)}{i(i+1)}.$$
--   Since $(i+1)p^i-ip^{i+1}=p^i(1+i(1-p))$, equation (19) for $a$ reads $f(p,a)=g(p,a)$.
--
--   **The auxiliary functions of B.9.** With a parameter $s$ in the role of $\alpha^*$,
--   $$a(p)=\sum_{i=1}^{\infty}\frac{\ln\bigl(\tfrac1p-s(1-p^i(1+i(1-p)))\bigr)}{i(i+1)}+s(2p-p^2),$$
--   $$b(p)=\frac1{p^2}\sum_{i=1}^{\infty}\frac{1}{i(i+1)\bigl(\tfrac1p-s(1-p^i(1+i(1-p)))\bigr)},\qquad c(p)=\sum_{i=1}^{\infty}\frac{p^{i-1}-p^i}{\tfrac1{ps}-1+p^i(1+i(1-p))}.$$
--
--   These are the only objects needed: Theorem 9 and all its milestones are inequalities between real numbers built from them.
--
--   **Formalization Note** Every series is a Lean `tsum` over `i : ℕ` with the paper's index $i\ge 1$ shifted to `i + 1`. For $s,p\in(0,1)$ each series is absolutely summable (the logarithms' arguments lie in $[1-s,1]$, resp. $[1/p-s,1/p]$ with $1/p-s>0$; the terms of $c$ are bounded by a geometric series), so the `tsum` is the true sum there; outside that range the functions carry Lean's default values and are never used. $\tilde\alpha(p)$ and $\alpha^*$ enter as predicates (`IsAlphaTilde p a`, `IsAlphaStar s`), not as chosen values; their existence and uniqueness are not assumed. In the $\alpha^*$ integral the integrand at $y=0$ equals $1/(1/s-1)$ in Lean (as `Real.log 0 = 0`), which is also its limit, so the interval integral is the true one. The paper also writes $f(p)=\tilde\alpha(p)/p$ in B.9, clashing with B.7's $f(p,\alpha)$; that ratio is not defined here (the statements use $s\,p\le a$ directly), and B.7's two-argument functions are named `fB7`, `gB7`.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 17, (19) and the preamble of Theorem 8; p. 34, B.7 (definitions of f, g); p. 36, B.9 (definitions of a(p), b(p), c(p))

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

namespace SampleDrivenOS.Linear

/-- B.7, p. 34: the left-hand side `f(p, α) = ln p + α (1 - p)² / p` of (19). -/
noncomputable def fB7 (p α : ℝ) : ℝ :=
  Real.log p + α * (1 - p) ^ 2 / p

/-- B.7, p. 34: the right-hand side
`g(p, α) = ∑_{i ≥ 1} ln(1 + α (p^i (1 + i (1 - p)) - 1)) / (i (i + 1))` of (19)
(index shifted by one). -/
noncomputable def gB7 (p α : ℝ) : ℝ :=
  ∑' i : ℕ, Real.log (1 + α * (p ^ (i + 1) * (1 + (i + 1) * (1 - p)) - 1)) /
    ((i + 1) * (i + 2))

/-- B.9, p. 36: `a(p) = ∑_{i ≥ 1} ln(1/p - α*(1 - p^i (1 + i (1 - p)))) / (i (i + 1)) + α*(2p - p²)`,
with `α*` a parameter `s` (index shifted by one). -/
noncomputable def aB9 (s p : ℝ) : ℝ :=
  (∑' i : ℕ, Real.log (1 / p - s * (1 - p ^ (i + 1) * (1 + (i + 1) * (1 - p)))) /
    ((i + 1) * (i + 2))) + s * (2 * p - p ^ 2)

/-- B.9, p. 36: `b(p) = (1/p²) ∑_{i ≥ 1} 1 / (i (i + 1) (1/p - α*(1 - p^i (1 + i (1 - p)))))`,
with `α*` a parameter `s` (index shifted by one). -/
noncomputable def bB9 (s p : ℝ) : ℝ :=
  1 / p ^ 2 *
    ∑' i : ℕ, 1 / ((i + 1) * (i + 2) * (1 / p - s * (1 - p ^ (i + 1) * (1 + (i + 1) * (1 - p)))))

/-- B.9, p. 36: `c(p) = ∑_{i ≥ 1} (p^{i-1} - p^i) / (1/(p α*) - 1 + p^i (1 + i (1 - p)))`,
with `α*` a parameter `s` (index shifted by one). -/
noncomputable def cB9 (s p : ℝ) : ℝ :=
  ∑' i : ℕ, (p ^ i - p ^ (i + 1)) / (1 / (p * s) - 1 + p ^ (i + 1) * (1 + (i + 1) * (1 - p)))

end SampleDrivenOS.Linear


