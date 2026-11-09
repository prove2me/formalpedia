-- Prove2me | Definitions.Def_HopRamsey_Fig2Params
-- name    : HopRamsey_Fig2Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:48.182804+00:00
-- url     : https://prove2.me/theorems/c1a5f3dc-ff07-4834-98f5-878d499561ab
-- title:
--   The parameters of Figure 2: $L,\delta,k,\mu_\ell,p_\ell,r_\ell,q_\ell$ and the bounds $f(n,\Delta)$, $g(n,\Delta)$
-- statement:
--   Fix $N=|V|$, a scale $\Phi$ and $\varepsilon\in(0,1)$. Writing $\log$ for $\log_2$ and $\ln$ for the natural logarithm, Figure 2 sets
--
--   1. $L=\lceil\log\log(N+1)\rceil$ (number of phases) and $\delta=(\log(N+1))^{-2}$;
--   2. $k=\Bigl\lceil\frac4\varepsilon(1+2\delta)^{\log\Phi}\bigl(\ln N+\ln\frac2\delta\cdot\log\Phi\bigr)\Bigr\rceil$ (truncation parameter);
--   3. $\mu_\ell=2^{2^{L-\ell}}$ for $0\le\ell\le L$ and $p_\ell=\frac2k\ln\frac{2\mu_\ell}{\delta}$;
--   4. at scale $\Delta$: $r_0=\Delta/2^{L+4}$, $r_\ell=r_{\ell-1}+\Delta/2^{L-\ell+4}+\Delta/(8L)$ for $1\le\ell\le L$, and $q_\ell=(r_\ell-r_{\ell-1})/k$.
--
--   The analysis uses, for $n\ge 1$ and $\Delta>0$,
--
--   $$
--   f(n,\Delta)=\frac4k(1+2\delta)^{\log\Delta}\Bigl(\ln n+\ln\frac2\delta\cdot\log\Delta\Bigr),\qquad g(n,\Delta)=2^8\,L\,\log n\,(1+2\delta)^{\log\Delta}.
--   $$
--
--   $L,\delta,k,\mu_\ell,p_\ell$ are global; $r_\ell,q_\ell$ depend on the scale $\Delta$ of the current call; $f$ and $g$ are the bounds of Lemmas 1 and 2.
--
--   **Formalization Note** The global parameters are packaged by `Fig2Params` with fields $N,\Phi,\varepsilon$; the radii are also available for an arbitrary number of phases as `radius L Δ ℓ`. Powers with exponent $\log\Phi$ or $\log\Delta$ are real powers.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Figure 2, p.17 (PDF p.19); f before Lemma 1, p.19 (PDF p.21); g before Lemma 2, p.22 (PDF p.24)

import Mathlib

namespace HopRamsey

/-- The radii of Figure 2 for `L` phases at scale `∆`: `r_0 = ∆/2^{L+4}` and
`r_ℓ = r_{ℓ−1} + ∆/2^{L−ℓ+4} + ∆/(8L)` for `1 ≤ ℓ ≤ L` (p.17, PDF p.19). Values at `ℓ > L` are not
used. -/
noncomputable def radius (L : ℕ) (Δ : ℝ) : ℕ → ℝ
  | 0 => Δ / 2 ^ (L + 4)
  | ℓ + 1 => radius L Δ ℓ + Δ / 2 ^ (L - (ℓ + 1) + 4) + Δ / (8 * L)

/-- The global parameters of Figure 2, determined by `N = |V|`, `Φ` and `ε`.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), Figure 2,
p.17 (PDF p.19): "L := ⌈log log(|V|+1)⌉ [...] δ := (log(|V|+1))^{−2} [...]
k := ⌈(4/ε)·(1+2δ)^{log Φ}·(ln|V| + ln(2/δ)·log Φ)⌉ [...] r_0 := ∆/2^{L+4} and
r_ℓ := r_{ℓ−1} + ∆/2^{L−ℓ+4} + ∆/(8L) (for 1 ≤ ℓ ≤ L) [...] q_ℓ := (r_ℓ − r_{ℓ−1})/k [...]
µ_ℓ := 2^{2^{L−ℓ}} (for 0 ≤ ℓ ≤ L) [...] p_ℓ := (2/k)·ln(2µ_ℓ/δ)". The functions `f` and `g` are
those fixed before Lemma 1 (p.19, PDF p.21) and before Lemma 2 (p.22, PDF p.24).

**Formalization Note.**
1. `log` is `log₂` (`Real.logb 2`) and `ln` is the natural logarithm (`Real.log`): the paper uses
   `log µ_ℓ = 2^{L−ℓ}` (proof of Lemma 2, p.24) and `g(n, ∆/2) = g(n, ∆)/(1+2δ)`, which need base 2.
2. `(1+2δ)^{log Φ}` and `(1+2δ)^{log ∆}` are real powers (`Real.rpow`).
3. In the paper `Φ = diam^{(h)}_G(V)`; here `Φ` is a field, and the statements that need the
   equality assume it. `N` is `|V|`, while the `n` of `f(n, ∆)`, `g(n, ∆)` is the size `|X|` of the
   current active set. -/
structure Fig2Params where
  /-- `N = |V|`. -/
  N : ℕ
  /-- `Φ`, the scale of the root call. -/
  Φ : ℝ
  /-- `ε`, the target exclusion probability. -/
  ε : ℝ

namespace Fig2Params

variable (P : Fig2Params)

/-- `L = ⌈log₂ log₂(|V|+1)⌉`, the number of phases. -/
noncomputable def L : ℕ := ⌈Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1))⌉₊

/-- `δ = (log₂(|V|+1))^{−2}`, the truncation error parameter. -/
noncomputable def delta : ℝ := ((Real.logb 2 ((P.N : ℝ) + 1)) ^ 2)⁻¹

/-- `k = ⌈(4/ε)·(1+2δ)^{log₂ Φ}·(ln|V| + ln(2/δ)·log₂ Φ)⌉`, the truncation parameter. -/
noncomputable def k : ℕ :=
  ⌈(4 / P.ε) * (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) *
    (Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ)⌉₊

/-- `µ_ℓ = 2^{2^{L−ℓ}}` for `0 ≤ ℓ ≤ L`, the density parameter. -/
noncomputable def mu (ℓ : ℕ) : ℕ := 2 ^ (2 ^ (P.L - ℓ))

/-- `p_ℓ = (2/k)·ln(2µ_ℓ/δ)`, the parameter of the geometric law in phase `ℓ`. -/
noncomputable def p (ℓ : ℕ) : ℝ := (2 / P.k) * Real.log (2 * (P.mu ℓ : ℝ) / P.delta)

/-- `r_ℓ` at scale `∆`. -/
noncomputable def r (Δ : ℝ) (ℓ : ℕ) : ℝ := radius P.L Δ ℓ

/-- `q_ℓ = (r_ℓ − r_{ℓ−1})/k` at scale `∆`, for `1 ≤ ℓ ≤ L`. -/
noncomputable def q (Δ : ℝ) (ℓ : ℕ) : ℝ := (P.r Δ ℓ - P.r Δ (ℓ - 1)) / P.k

/-- `f(n, ∆) = (4/k)·(1+2δ)^{log₂ ∆}·(ln n + ln(2/δ)·log₂ ∆)`, the bound of Lemma 1. -/
noncomputable def f (n : ℕ) (Δ : ℝ) : ℝ :=
  (4 / P.k) * (1 + 2 * P.delta) ^ (Real.logb 2 Δ) *
    (Real.log n + Real.log (2 / P.delta) * Real.logb 2 Δ)

/-- `g(n, ∆) = 2⁸·L·log₂ n·(1+2δ)^{log₂ ∆}`, the bound of Lemma 2. -/
noncomputable def g (n : ℕ) (Δ : ℝ) : ℝ :=
  2 ^ 8 * P.L * Real.logb 2 n * (1 + 2 * P.delta) ^ (Real.logb 2 Δ)

end Fig2Params

end HopRamsey


