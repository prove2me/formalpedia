-- Prove2me | Definitions.Def_SuperRamanujan227_Main_Jacobi
-- name    : SuperRamanujan227_Main_Jacobi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:29:26.420104+00:00
-- url     : https://prove2.me/theorems/e7989d12-b351-44a8-b9ba-21bdf032592a
-- title:
--   Jacobi polynomials $P_r^{(\alpha,\beta)}$, symmetric Jacobi polynomials and $Q_{n,d}$
-- statement:
--   For real $\alpha,\beta$ and an integer $r\ge 0$, the **Jacobi polynomial** of degree $r$ is
--   $$P_r^{(\alpha,\beta)}(x)=\sum_{s=0}^{r}\binom{r+\alpha}{r-s}\binom{r+\beta}{s}\Big(\frac{x-1}{2}\Big)^{s}\Big(\frac{x+1}{2}\Big)^{r-s},$$
--   where $\binom{a}{k}=a(a-1)\cdots(a-k+1)/k!$ is the generalized binomial coefficient. The **symmetric Jacobi polynomials** are $P_r^{(\gamma,\gamma)}$; for $\gamma>-1$ they are orthogonal on $[-1,1]$ with respect to the weight $(1-x^2)^\gamma$, and $P_r^{(\gamma,\gamma)}$ has degree exactly $r$.
--
--   For integers $n,d$ with $nd$ even put $j=n(d-1)$ and $m=nd/2$, and define
--   $$Q_{n,d}(x)=\frac{\partial^{j}}{\partial x^{j}}\,(x^2-1)^m,$$
--   a polynomial of degree $2m-j=n$. It is the polynomial whose largest root controls $\lambda_2$ in the proof of Theorem 1.1.
--
--   **Formalization Note** The Jacobi family uses the classical normalization (the paper characterizes $P_r^{(\gamma,\gamma)}$ only up to a nonzero scalar, which changes no root and no proportionality). $Q_{n,d}$ is the actual iterated formal derivative; for odd $nd$ the natural-number division makes it a junk polynomial, and every statement assumes $nd$ even.
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, pp. 19–20 (Jacobi polynomials and their characterization; definition of $Q_{n,d}$ on p. 19)

import Mathlib

open Polynomial

namespace SuperRamanujan227.Main

/-- The generalized binomial coefficient `binom(a, k) = a(a-1)⋯(a-k+1)/k!` for real `a`. -/
noncomputable def gbinom (a : ℝ) (k : ℕ) : ℝ :=
  (descPochhammer ℝ k).eval a / (k.factorial : ℝ)

/-- The classical Jacobi polynomial of degree `r` with real parameters `α, β`:
`P_r^{(α,β)}(x) = ∑_{s=0}^{r} binom(r+α, r-s) binom(r+β, s) ((x-1)/2)^s ((x+1)/2)^{r-s}`. -/
noncomputable def jacobi (α β : ℝ) (r : ℕ) : ℝ[X] :=
  ∑ s ∈ Finset.range (r + 1),
    C (gbinom ((r : ℝ) + α) (r - s) * gbinom ((r : ℝ) + β) s) *
      (C (1 / 2 : ℝ) * (X - 1)) ^ s * (C (1 / 2 : ℝ) * (X + 1)) ^ (r - s)

/-- The symmetric Jacobi polynomial `P_r^{(γ,γ)}` (p. 19), orthogonal on `[-1, 1]` for the weight
`(1 - x²)^γ` when `γ > -1`. -/
noncomputable def jacobiSym (γ : ℝ) (r : ℕ) : ℝ[X] :=
  jacobi γ γ r

/-- `Q_{n,d}(x) = (d/dx)^j (x² - 1)^m` with `j = n(d-1)` and `m = nd/2` (p. 19). Meaningful
when `nd` is even; it has degree `n`. -/
noncomputable def Q (n d : ℕ) : ℝ[X] :=
  derivative^[n * (d - 1)] ((X ^ 2 - 1) ^ (n * d / 2))

end SuperRamanujan227.Main


