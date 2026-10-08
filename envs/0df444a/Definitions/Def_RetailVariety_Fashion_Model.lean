-- Prove2me | Definitions.Def_RetailVariety_Fashion_Model
-- name    : RetailVariety_Fashion_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:17.13184+00:00
-- url     : https://prove2.me/theorems/1f31379d-6045-47fb-a280-845bc06bf28a
-- title:
--   §2.2–2.4, (1), (6)–(8): prefix sets $A_i$, MNL shares, critical fractile $z$, and the profit functions $\pi_I$, $\pi_T$
-- statement:
--   This module fixes the single-category retail assortment model of van Ryzin and Mahajan (1999), §§2.2–2.4 and §3.1, pp. 1499–1503.
--
--   **Variants and preferences.** A category has $n$ variants $N=\{1,\dots,n\}$ with preferences $v_j\ge 0$, and a no-purchase option with preference $v_0>0$. Following §3.1, the variants are ordered by decreasing preference, and the **prefix set** of the $i$ most popular variants is
--   $$A_i=\{1,\dots,i\},\qquad A_0=\emptyset,\quad A_n=N.$$
--
--   **Multinomial logit shares** (1). For an assortment $S\subseteq N$ and $j\in S$,
--   $$q_j(S)=\frac{v_j}{\sum_{i\in S}v_i+v_0}.$$
--
--   **Critical fractile** (6). For a price $p$ and unit cost $c$ with $0<c<p$, $z=\Phi^{-1}(1-c/p)$, where $\Phi$ is the standard normal distribution function.
--
--   **Profit functions.** For a store volume $\lambda>0$, a variability scale $\sigma>0$ and an exponent $0\le\beta<1$, the optimal expected profit of assortment $S$ is, in the independent population model (7),
--   $$\pi_I(S,v)=(p-c)\lambda\sum_{j\in S}q_j-\frac{p\sigma\lambda^{\beta}e^{-z^2/2}}{\sqrt{2\pi}}\sum_{j\in S}q_j^{\beta},$$
--   and in the trend-following population model (8),
--   $$\pi_T(S,v)=\sum_{j\in S}(pq_j-c)^{+}\lambda .$$
--   Both vanish on the empty assortment.
--
--   These are the objects compared across two categories in Theorem 3.
--
--   **Formalization Note.** Variants are indexed by `Fin n`, 0-based: variant $j$ of the paper is index $j-1$, and `A n i` is the set of indices below $i$. The no-purchase preference is a separate real `v0`, not a variant. Mathlib has no normal quantile, so `zCrit p c` is the least $x$ with $1-c/p\le\Phi(x)$; for $0<c<p$ it is the unique $x$ with $\Phi(x)=1-c/p$. Powers $\lambda^\beta$ and $q_j^\beta$ are real powers (`Real.rpow`), for which $0^0=1$. $(x)^+$ is `max x 0`. The closed forms (7) and (8) are taken as the definitions; their derivation as newsvendor optima is not part of this mission.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1499, (1); p. 1502, (6), (7), (8); p. 1503, §3.1 (ordering and A_i)

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model
import Definitions.Def_RetailVariety_Structure_Model

namespace RetailVariety.Fashion

open ProbabilityTheory

/-- The critical fractile `z = Φ⁻¹(1 − c/p)` of (6), p. 1502, with `Φ` the standard normal c.d.f.
Mathlib has no normal quantile, so `z` is the least `x` with `1 − c/p ≤ Φ(x)`; for `0 < c < p` this
is the unique `x` with `Φ(x) = 1 − c/p`. -/
noncomputable def zCrit (p c : ℝ) : ℝ :=
  sInf {x : ℝ | 1 - c / p ≤ cdf (gaussianReal 0 1) x}

/-- The safety-stock coefficient `p σ λ^β e^{−z²/2} / √(2π)` of (7), p. 1502. -/
noncomputable def safetyCoeff (p c lam σ β : ℝ) : ℝ :=
  p * σ * lam ^ β * Real.exp (-(zCrit p c) ^ 2 / 2) / Real.sqrt (2 * Real.pi)

/-- The optimal expected profit (7), p. 1502, of the independent population model:
`π_I(S, v) = (p − c)λ ∑_{j∈S} q_j − (pσλ^β e^{−z²/2}/√(2π)) ∑_{j∈S} q_j^β`,
with `q_j^β` the real power `Real.rpow`. -/
noncomputable def profitI (p c lam σ β : ℝ) {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (p - c) * lam * ∑ j ∈ S, RetailVariety.Structure.share v v0 S j
    - safetyCoeff p c lam σ β * ∑ j ∈ S, RetailVariety.Structure.share v v0 S j ^ β

/-- The optimal expected profit (8), p. 1502, of the trend-following population model:
`π_T(S, v) = ∑_{j∈S} (p q_j − c)^+ λ`. -/
noncomputable def profitT (p c lam : ℝ) {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, max (p * RetailVariety.Structure.share v v0 S j - c) 0 * lam

end RetailVariety.Fashion


