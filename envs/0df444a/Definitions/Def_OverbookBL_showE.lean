-- Prove2me | Definitions.Def_OverbookBL_showE
-- name    : OverbookBL_showE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:38.027657+00:00
-- url     : https://prove2.me/theorems/4c4926e0-e760-45e9-9baf-0a08f3db2332
-- title:
--   Show-up law of an acceptance vector: $\mathbb E[f(\sum_j X_{j,x_j})]$, $V_B$, tails, CDF and quantile
-- statement:
--   Let $p\in[0,1]^k$ and let $x\in\mathbb N^k$ be an acceptance vector. Write $X_{j,x_j}\sim\mathrm{Bin}(x_j,p_j)$, $j\in[k]$, for independent binomial variables (the number of accepted type-$j$ customers who show up), so that $\sum_j X_{j,x_j}\sim PBin(x_1,p_1;\dots;x_k,p_k)$. For $f:\mathbb N\to\mathbb R$,
--
--   $$
--   \mathbb E\Big[f\Big(\sum_j X_{j,x_j}\Big)\Big]=\sum_{y\le x}\ \prod_{j}\binom{x_j}{y_j}p_j^{y_j}(1-p_j)^{x_j-y_j}\, f\Big(\sum_j y_j\Big).
--   $$
--
--   The module defines, for a capacity $B\in\mathbb N$:
--
--   1. the expected compensation $V_B(x)=\mathbb E\big[(\sum_j X_{j,x_j}-B)^+\big]$;
--   2. the tail $\mathbb P[\sum_j X_{j,x_j}\ge B]$;
--   3. the distribution function $F(s)=\mathbb P[\sum_j X_{j,x_j}\le s]$ and the quantile $F^{-1}(r)=\min\{s\in\mathbb N: F(s)\ge r\}$;
--   4. the binomial tail $\mathbb P[\mathrm{Bin}(n,r)\ge m]$.
--
--   These are the probabilistic quantities of the model: the objective subtracts $V_B$, local optimality is characterized by tails (Lemma 1), and the Lipschitz bound is proved through quantiles (Claim 1).
--
--   **Formalization Note** The law is a finite sum over show-up vectors $y\le x$; no probability space is used. The quantile is the lower quantile, the inverse used on p.18; it is a genuine minimum for $r\le1$.
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, §2, p.9 (V_B); §2.2, p.12 (PBin, CDF, quantile); Lemma 1, p.13; Proposition 2, p.43

import Mathlib

namespace OverbookBL

/-- The binomial probability mass function `P[Bin(n, r) = y] = C(n, y) rʸ (1 − r)ⁿ⁻ʸ`
(Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, §2, p.9, "Bin(x, p)").

**Formalization Note** For `y > n` the factor `C(n, y)` is `0`, so the truncated `n − y` is
harmless. -/
noncomputable def binomPMF (n : ℕ) (r : ℝ) (y : ℕ) : ℝ :=
  (n.choose y : ℝ) * r ^ y * (1 - r) ^ (n - y)

/-- Expectation `E[f(∑ⱼ X_{j,xⱼ})]` of a function of the number of show-ups of the acceptance
vector `x`, where the `X_{j,xⱼ} ∼ Bin(xⱼ, pⱼ)` are independent (arXiv:2204.11148v2, §2, p.9;
the Poisson binomial law `PBin(x₁, p₁; …; xₖ, pₖ)` of §2.2, p.12).

**Formalization Note** The law is written out as a finite sum over the show-up vectors
`y ≤ x` with the product of the binomial masses as weight; no probability space is needed. -/
noncomputable def showE {k : ℕ} (p : Fin k → ℝ) (x : Fin k → ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ y ∈ Fintype.piFinset (fun j => Finset.range (x j + 1)),
    (∏ j, binomPMF (x j) (p j) (y j)) * f (∑ j, y j)

/-- Expected compensation `V_B(x) = E[(∑ⱼ X_{j,xⱼ} − B)⁺]` (arXiv:2204.11148v2, p.9). -/
noncomputable def VB {k : ℕ} (p : Fin k → ℝ) (B : ℕ) (x : Fin k → ℕ) : ℝ :=
  showE p x (fun s => max ((s : ℝ) - (B : ℝ)) 0)

/-- Tail probability `P[∑ⱼ X_{j,xⱼ} ≥ B]` (arXiv:2204.11148v2, Lemma 1, p.13). -/
noncomputable def tailProb {k : ℕ} (p : Fin k → ℝ) (B : ℕ) (x : Fin k → ℕ) : ℝ :=
  showE p x (fun s => if B ≤ s then 1 else 0)

/-- Cumulative distribution function `F(s) = P[∑ⱼ X_{j,xⱼ} ≤ s]` (arXiv:2204.11148v2, §2.2,
p.12). -/
noncomputable def showCDF {k : ℕ} (p : Fin k → ℝ) (x : Fin k → ℕ) (s : ℕ) : ℝ :=
  showE p x (fun t => if t ≤ s then 1 else 0)

/-- Quantile function `F⁻¹(r) = min {s ∈ ℕ | F(s) ≥ r}` of the number of show-ups
(arXiv:2204.11148v2, §2.2, p.12, "the quantile function (i.e., the inverse of CDF)").

**Formalization Note** This is the lower quantile, the inverse used in the proof of Lemma 2
(p.18, "`F_Ȳ(B−1) ≥ q̄ⱼ` … equivalently `F⁻¹_Ȳ(q̄ⱼ) ≤ B − 1`"). For `r ≤ 1` and `pⱼ ∈ [0, 1]`
the set is nonempty (`F(∑ xⱼ) = 1`), so the `sInf` is a minimum; `sInf ∅ = 0` occurs only for
`r > 1`, which is never used. -/
noncomputable def showQuantile {k : ℕ} (p : Fin k → ℝ) (x : Fin k → ℕ) (r : ℝ) : ℕ :=
  sInf {s : ℕ | r ≤ showCDF p x s}

/-- Upper tail `P[Y ≥ m]` of `Y ∼ Bin(n, r)` (arXiv:2204.11148v2, Proposition 2, p.43). -/
noncomputable def binTail (n : ℕ) (r : ℝ) (m : ℕ) : ℝ :=
  ∑ y ∈ (Finset.range (n + 1)).filter (fun y => m ≤ y), binomPMF n r y

end OverbookBL


