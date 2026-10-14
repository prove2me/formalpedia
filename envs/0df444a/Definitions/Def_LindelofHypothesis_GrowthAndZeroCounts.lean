-- Prove2me | Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
-- name    : LindelofHypothesis_GrowthAndZeroCounts
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T16:34:02.838438+00:00
-- url     : https://prove2.me/theorems/23b5d3a5-e99c-4668-b239-d1ceae259203
-- title:
--   The growth exponent $\mu(\sigma)$, zero counts $N(\sigma,T)$ and prime gaps $g_n$
-- statement:
--   This file fixes the objects in terms of which the Lindelöf hypothesis, its reformulations and its consequences are stated. Throughout, $\zeta$ is the Riemann zeta function (analytically continued to $\mathbb C\setminus\{1\}$), and the **multiplicity** $m_\rho\ge1$ of a zero $\rho$ of $\zeta$ is its order of vanishing.
--
--   1. **The growth exponent.** For real $\sigma$,
--   $$\mu(\sigma)=\inf\bigl\{a\in\mathbb R:\ \zeta(\sigma+iT)=O(T^{a})\ \text{as } T\to+\infty\bigr\},$$
--   the infimum being taken in the extended reals $[-\infty,+\infty]$ (so $\mu(\sigma)=+\infty$ if no such $a$ exists).
--
--   2. **Zeros in a unit window.** For real $\sigma$ and $T$, the number of zeros $\rho$ of $\zeta$ with $\operatorname{Re}\rho\ge\sigma$ and $T\le\operatorname{Im}\rho\le T+1$, counted with multiplicity; and the number of **all** zeros $\rho$ of $\zeta$ with $T\le\operatorname{Im}\rho\le T+1$, counted with multiplicity.
--
--   3. **The zero-density count.** For real $\sigma$ and $T$,
--   $$N(\sigma,T)=\sum_{\substack{\zeta(\rho)=0\\ \operatorname{Re}\rho\ge\sigma,\ |\operatorname{Im}\rho|\le T}} m_\rho .$$
--
--   4. **Prime gaps.** Writing $p_n$ for the $n$-th prime, $g_n=p_{n+1}-p_n$.
--
--   These are the objects of the sections "The μ function", "Relation to the Riemann hypothesis", "Other consequences" and "The density hypothesis" of the source.
--
--   **Formalization Note** $\mu(\sigma)$ is `LindelofHypothesis.mu σ : EReal`, an `sInf` in `EReal`, so the degenerate cases are $\pm\infty$ rather than a junk value. The zero counts `zeroCountWindow σ T`, `zeroCountWindowAll T` and `zeroDensityCount σ T` are sums in `ℕ∞` of `analyticOrderAt riemannZeta ρ` over the zero set; an infinite count would be $\top$, never $0$, so upper bounds on them cannot hold vacuously. Primes are indexed from $0$ (`Nat.nth Nat.Prime 0 = 2`), which is immaterial for the asymptotic statements. The Lindelöf hypothesis itself is reused from the published definition `RiemannVonMangoldt.LindelofHypothesis`: for every $\varepsilon>0$, $\zeta(\tfrac12+it)=O(t^{\varepsilon})$ as $t\to+\infty$.
-- source:
--   Wikipedia, "Lindelöf hypothesis" (snapshot supplied as Lindelöf_hypothesis.pdf, printed 12 Oct 2026), https://en.wikipedia.org/wiki/Lindel%C3%B6f_hypothesis; sections "The μ function" (definition of μ(σ)), "Relation to the Riemann hypothesis" (zeros with real part at least 1/2+ε and imaginary part between T and T+1), "Other consequences" (p_n, g_n), "The density hypothesis" (N(σ,T)).

import Mathlib

/-!
# Growth exponent of `ζ`, zero counts and prime gaps for the Lindelöf hypothesis

* `mu σ` is `μ(σ)`: the infimum, in the extended reals, of all real `a` such that
  `ζ(σ + iT) = O(T^a)` as `T → +∞` (`⊤` if there is no such `a`).
* `zeroCountWindow σ T` is the number of zeros `ρ` of `ζ` with `Re ρ ≥ σ` and
  `T ≤ Im ρ ≤ T + 1`, counted with multiplicity.
* `zeroCountWindowAll T` is the number of zeros `ρ` of `ζ` with `T ≤ Im ρ ≤ T + 1`,
  counted with multiplicity.
* `zeroDensityCount σ T` is `N(σ, T)`: the number of zeros `ρ` of `ζ` with `Re ρ ≥ σ` and
  `|Im ρ| ≤ T`, counted with multiplicity.
* `primeGap n` is `g_n = p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n` (so `p_0 = 2`).

All zero counts take values in `ℕ∞`, so an infinite count would be `⊤` rather than a junk value.
-/

namespace LindelofHypothesis

open Complex Filter Asymptotics

/-- `μ(σ)`: the infimum of all real `a` with `ζ(σ + iT) = O(T^a)` as `T → +∞`, taken in `EReal`
(it is `⊤` if no such `a` exists and `⊥` if every real `a` works). -/
noncomputable def mu (σ : ℝ) : EReal :=
  sInf ((fun a : ℝ => (a : EReal)) ''
    {a : ℝ | (fun T : ℝ => riemannZeta (σ + T * I)) =O[atTop] (fun T : ℝ => T ^ a)})

/-- The number of zeros `ρ` of `ζ` with `Re ρ ≥ σ` and `T ≤ Im ρ ≤ T + 1`, counted with
multiplicity (order of vanishing), as an element of `ℕ∞`. -/
noncomputable def zeroCountWindow (σ T : ℝ) : ℕ∞ :=
  ∑' s : {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ T ≤ s.im ∧ s.im ≤ T + 1},
    analyticOrderAt riemannZeta (s : ℂ)

/-- The number of zeros `ρ` of `ζ` with `T ≤ Im ρ ≤ T + 1`, counted with multiplicity,
as an element of `ℕ∞`. -/
noncomputable def zeroCountWindowAll (T : ℝ) : ℕ∞ :=
  ∑' s : {s : ℂ | riemannZeta s = 0 ∧ T ≤ s.im ∧ s.im ≤ T + 1},
    analyticOrderAt riemannZeta (s : ℂ)

/-- `N(σ, T)`: the number of zeros `ρ` of `ζ` with `Re ρ ≥ σ` and `|Im ρ| ≤ T`, counted with
multiplicity, as an element of `ℕ∞`. -/
noncomputable def zeroDensityCount (σ T : ℝ) : ℕ∞ :=
  ∑' s : {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T},
    analyticOrderAt riemannZeta (s : ℂ)

/-- The `n`-th prime gap `g_n = p_{n+1} - p_n`, with `p_n = Nat.nth Nat.Prime n`
(`p_0 = 2`, `p_1 = 3`, …). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

end LindelofHypothesis


