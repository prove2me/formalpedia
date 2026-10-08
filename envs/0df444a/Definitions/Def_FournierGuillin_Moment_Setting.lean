-- Prove2me | Definitions.Def_FournierGuillin_Moment_Setting
-- name    : FournierGuillin_Moment_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:25.059109+00:00
-- url     : https://prove2.me/theorems/bda37df5-e58c-45a7-91e4-5343bbeebc28
-- title:
--   p. 1, p. 2, Notation 4 (pp. 5–6) — transport cost 𝒯_p, moments M_q, dyadic cubes 𝒫_ℓ, shells B_n, ℛ_{B_n}, distances 𝒟_p, rates
-- statement:
--   Fix a dimension $d \ge 1$ and equip $\mathbb R^d$ with the Euclidean norm $|\cdot|$. All measures below are Borel measures on $\mathbb R^d$.
--
--   1. **Transport cost.** For $p > 0$ and probability measures $\mu,\nu$,
--   $$\mathcal T_p(\mu,\nu) = \inf\Big\{\int_{\mathbb R^d\times\mathbb R^d} |x-y|^p\,\xi(dx,dy) \;:\; \xi\in\mathcal H(\mu,\nu)\Big\},$$
--   where $\mathcal H(\mu,\nu)$ is the set of couplings of $\mu$ and $\nu$, i.e. measures on $\mathbb R^d\times\mathbb R^d$ with marginals $\mu$ and $\nu$. There is no $1/p$ root: for $p>1$ the Wasserstein distance is $\mathcal T_p^{1/p}$, and for $p\le 1$ it is $\mathcal T_p$ itself. The value lies in $[0,\infty]$.
--   2. **Moments.** For $q>0$, $M_q(\mu) = \int_{\mathbb R^d}|x|^q\,\mu(dx)\in[0,\infty]$.
--   3. **Dyadic cubes.** For $\ell\ge 0$, $\mathcal P_\ell$ is the natural partition of $(-1,1]^d$ into the $2^{d\ell}$ translates of $(-2^{-\ell},2^{-\ell}]^d$; the cube with index $k\in\{0,\dots,2^\ell-1\}^d$ is $\prod_i\big(-1+2k_i2^{-\ell},\,-1+2(k_i+1)2^{-\ell}\big]$.
--   4. **Shells.** $B_0=(-1,1]^d$ and $B_n=(-2^n,2^n]^d\setminus(-2^{n-1},2^{n-1}]^d$ for $n\ge 1$. For a probability measure $\mu$, $\mathcal R_{B_n}\mu$ is the image of $\mu|_{B_n}/\mu(B_n)$ under $x\mapsto x/2^n$, a probability measure on $(-1,1]^d$.
--   5. **The distances $\mathcal D_p$.** For probability measures $\mu,\nu$ on $(-1,1]^d$,
--   $$\mathcal D_p(\mu,\nu) = \frac{2^p-1}{2}\sum_{\ell\ge1}2^{-p\ell}\sum_{F\in\mathcal P_\ell}|\mu(F)-\nu(F)|,$$
--   and for probability measures $\mu,\nu$ on $\mathbb R^d$,
--   $$\mathcal D_p(\mu,\nu) = \sum_{n\ge0}2^{pn}\Big(|\mu(B_n)-\nu(B_n)| + \big(\mu(B_n)\wedge\nu(B_n)\big)\,\mathcal D_p(\mathcal R_{B_n}\mu,\mathcal R_{B_n}\nu)\Big)\in[0,\infty].$$
--   6. **Cells.** For $n,\ell\ge0$ and $F\in\mathcal P_\ell$, $2^nF\cap B_n$ with $2^nF=\{2^nx: x\in F\}$.
--   7. **Rates.** The rate of Theorem 1 is $N^{-1/2}+N^{-(q-p)/q}$ if $p>d/2$, $N^{-1/2}\log(1+N)+N^{-(q-p)/q}$ if $p=d/2$, and $N^{-p/d}+N^{-(q-p)/q}$ if $p<d/2$. The rate of Step 1 of its proof is $\min\{\varepsilon,(\varepsilon/N)^{1/2}\}$, $\min\{\varepsilon,(\varepsilon/N)^{1/2}\log(2+\varepsilon N)\}$, $\min\{\varepsilon,\varepsilon(\varepsilon N)^{-p/d}\}$ in the same three regimes.
--
--   The empirical measure $\mu_N=\frac1N\sum_{k=1}^N\delta_{X_k}$ is the published definition `WassersteinDRO.Duality.empiricalDistribution`, and the coupling set $\mathcal H(\mu,\nu)$ is the published `WassersteinLinOpt.Ball.couplings`.
--
--   These are the objects of Fournier and Guillin's moment estimates: $\mathcal D_p$ dominates $\mathcal T_p$ up to a constant (Lemma 5) and is a weighted sum of mass differences over dyadic cells, which is what makes the expectation of $\mathcal T_p(\mu_N,\mu)$ computable.
--
--   **Formalization Note** Costs, moments, sums of nonnegative series and $\mathcal D_p$ are valued in $[0,\infty]$ (`ℝ≥0∞`), so divergence is $+\infty$, never a junk real. Mass differences use `toReal`, which is faithful for the finite measures of every use. The sum over $\ell\ge1$ is an $\mathbb N$-indexed sum with the $\ell=0$ term set to $0$. When $\mu(B_n)=0$ the page leaves $\mathcal R_{B_n}\mu$ undefined; here it is the zero measure, and it is always multiplied by $\mu(B_n)\wedge\nu(B_n)=0$. The page writes one symbol $\mathcal D_p$ for both distances; Lean uses `Dcube` (compact case) and `Dp`. The transport cost is defined for every real $p$ (the display on p. 1 says $p\ge1$, but the paper uses it for all $p>0$). The rate functions carry no admissibility condition on $q$; those are hypotheses of the theorems.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, §1.1 p. 1 (μ_N, 𝒯_p, ℋ(μ, ν)); p. 2 (M_q, Theorem 1 rates); Notation 4, pp. 5–6; Lemma 6, p. 7 (2ⁿF); Proof of Theorem 1, Step 1, p. 8

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution

open MeasureTheory
open scoped ENNReal

namespace FournierGuillin.Moment

/-- The optimal transport cost `𝒯_p(μ, ν)` of Fournier & Guillin, arXiv:1312.2128v1, §1.1, p. 1:
`𝒯_p(μ, ν) = inf { ∫ |x − y|^p ξ(dx, dy) : ξ ∈ ℋ(μ, ν) }`, where `ℋ(μ, ν)` is the set of couplings
(measures on `ℝᵈ × ℝᵈ` with marginals `μ` and `ν`; the published `WassersteinLinOpt.Ball.couplings`).
`|·|` is the Euclidean norm. There is no `1/p` root. The page's display says `p ≥ 1`, but the next
sentence uses `𝒯_p` for `p ∈ (0, 1]` and every result is stated for `p > 0`, so the formula is taken for
every real `p`. The value lies in `ℝ≥0∞`: an infinite cost is `⊤`, never a junk real. -/
noncomputable def transportCost {d : ℕ} (p : ℝ) (μ ν : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨅ γ ∈ WassersteinLinOpt.Ball.couplings μ ν, ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂γ

/-- The `q`-th moment `M_q(μ) = ∫ |x|^q μ(dx)` (p. 2), valued in `ℝ≥0∞`; "`M_q(μ) < ∞`" is
`moment q μ < ⊤`. -/
noncomputable def moment {d : ℕ} (q : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖x‖ ^ q) ∂μ

/-- The dyadic cube of level `ℓ` with index `k` (Notation 4(a), p. 5):
`∏ᵢ (−1 + 2kᵢ/2^ℓ, −1 + 2(kᵢ + 1)/2^ℓ]`. As `k` ranges over `Fin d → Fin (2^ℓ)` these are the `2^{dℓ}`
translations of `(−2^{−ℓ}, 2^{−ℓ}]ᵈ` forming the natural partition `𝒫_ℓ` of `(−1, 1]ᵈ`; a sum over
`F ∈ 𝒫_ℓ` is a sum over `k`. -/
def cube {d : ℕ} (ℓ : ℕ) (k : Fin d → Fin (2 ^ ℓ)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, -1 + 2 * (k i : ℝ) / 2 ^ ℓ < x i ∧ x i ≤ -1 + 2 * ((k i : ℝ) + 1) / 2 ^ ℓ}

/-- The box `(−r, r]ᵈ`. -/
def box {d : ℕ} (r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, -r < x i ∧ x i ≤ r}

/-- The shells of Notation 4(b), p. 5: `B₀ = (−1, 1]ᵈ` and, for `n ≥ 1`,
`B_n = (−2ⁿ, 2ⁿ]ᵈ \ (−2^{n−1}, 2^{n−1}]ᵈ`. They partition `ℝᵈ`. -/
def shell {d : ℕ} (n : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  if n = 0 then box 1 else box ((2 : ℝ) ^ n) \ box ((2 : ℝ) ^ (n - 1))

/-- `ℛ_{B_n}μ` (Notation 4(b), p. 5): the image of `μ|_{B_n}/μ(B_n)` under `x ↦ x/2ⁿ`, a probability
measure on `(−1, 1]ᵈ` when `0 < μ(B_n) < ∞`. When `μ(B_n) = 0` the page leaves it undefined; here it is
`⊤ • 0 = 0`, and every use multiplies it by `μ(B_n) ∧ ν(B_n) = 0`. -/
noncomputable def rescale {d : ℕ} (n : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (μ (shell n))⁻¹ • (μ.restrict (shell n)).map (fun x => ((2 : ℝ) ^ n)⁻¹ • x)

/-- The compact-case distance `𝒟_p` of Notation 4(a), p. 5:
`𝒟_p(μ, ν) = ((2^p − 1)/2) Σ_{ℓ≥1} 2^{−pℓ} Σ_{F∈𝒫_ℓ} |μ(F) − ν(F)|`.
The sum over `ℓ ≥ 1` is the `ℕ`-indexed sum with the `ℓ = 0` term set to `0`. The masses are turned into
reals with `toReal`, which is faithful for the finite measures of every use (probability measures, or `0`). -/
noncomputable def Dcube {d : ℕ} (p : ℝ) (μ ν : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 ^ p - 1) / 2) *
    ∑' ℓ : ℕ, (if 1 ≤ ℓ then
      ENNReal.ofReal (2 ^ (-(p * ℓ))) *
        ∑ k : Fin d → Fin (2 ^ ℓ), ENNReal.ofReal |(μ (cube ℓ k)).toReal - (ν (cube ℓ k)).toReal|
      else 0)

/-- The distance `𝒟_p` on `P(ℝᵈ)` of Notation 4(b), pp. 5–6:
`𝒟_p(μ, ν) = Σ_{n≥0} 2^{pn} (|μ(B_n) − ν(B_n)| + (μ(B_n) ∧ ν(B_n)) 𝒟_p(ℛ_{B_n}μ, ℛ_{B_n}ν))`,
where the inner `𝒟_p` is `Dcube`. Valued in `ℝ≥0∞`, so a divergent series is `⊤`, never a junk `0`. -/
noncomputable def Dp {d : ℕ} (p : ℝ) (μ ν : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (2 ^ (p * n)) *
    (ENNReal.ofReal |(μ (shell n)).toReal - (ν (shell n)).toReal| +
      min (μ (shell n)) (ν (shell n)) * Dcube p (rescale n μ) (rescale n ν))

/-- The set `2ⁿF ∩ B_n` of Lemma 6 (p. 7), for `F` the cube of level `ℓ` and index `k`. -/
def scaledCell {d : ℕ} (n ℓ : ℕ) (k : Fin d → Fin (2 ^ ℓ)) : Set (EuclideanSpace ℝ (Fin d)) :=
  ((fun x => (2 : ℝ) ^ n • x) '' cube ℓ k) ∩ shell n

/-- The rate of Theorem 1, p. 2, without the factor `C M_q^{p/q}(μ)`:
* `N^{−1/2} + N^{−(q−p)/q}` if `p > d/2`;
* `N^{−1/2} log(1 + N) + N^{−(q−p)/q}` if `p = d/2`;
* `N^{−p/d} + N^{−(q−p)/q}` if `p ∈ (0, d/2)`.
The excluded values of `q` (`q ≠ 2p`, resp. `q ≠ dp/(d − p)`) are hypotheses of the theorem, not branches
here. Every base `N` is positive in every use (`N ≥ 1`). -/
noncomputable def rateT1 (d : ℕ) (p q : ℝ) (N : ℕ) : ℝ :=
  if (d : ℝ) / 2 < p then (N : ℝ) ^ (-(1 / 2 : ℝ)) + (N : ℝ) ^ (-((q - p) / q))
  else if p = (d : ℝ) / 2 then
    (N : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (1 + N) + (N : ℝ) ^ (-((q - p) / q))
  else (N : ℝ) ^ (-(p / d)) + (N : ℝ) ^ (-((q - p) / q))

/-- The right side of Step 1 of the proof of Theorem 1 (p. 8), without the constant `C`:
* `min{ε, (ε/N)^{1/2}}` if `p > d/2`;
* `min{ε, (ε/N)^{1/2} log(2 + εN)}` if `p = d/2`;
* `min{ε, ε(εN)^{−p/d}}` if `p ∈ (0, d/2)`.
Every base is positive in every use (`ε > 0`, `N ≥ 1`). -/
noncomputable def rateStep1 (d : ℕ) (p ε : ℝ) (N : ℕ) : ℝ :=
  if (d : ℝ) / 2 < p then min ε ((ε / N) ^ (1 / 2 : ℝ))
  else if p = (d : ℝ) / 2 then min ε ((ε / N) ^ (1 / 2 : ℝ) * Real.log (2 + ε * N))
  else min ε (ε * (ε * N) ^ (-(p / d)))

end FournierGuillin.Moment


