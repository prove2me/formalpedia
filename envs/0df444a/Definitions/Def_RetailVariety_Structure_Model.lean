-- Prove2me | Definitions.Def_RetailVariety_Structure_Model
-- name    : RetailVariety_Structure_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:18.453281+00:00
-- url     : https://prove2.me/theorems/a73f10ad-df67-49b2-840d-a4f1d109523b
-- title:
--   van Ryzin–Mahajan assortment model: MNL shares, critical fractile, profits (7)–(8), and Lemma 1's $f, g_I, g_T, h_I, h_T$
-- statement:
--   This file fixes the single-category retail assortment model of van Ryzin and Mahajan (1999).
--
--   1. **Variants and preferences.** The category has variants $N=\{1,\dots,n\}$. Variant $j$ has MNL preference $v_j>0$ and the no-purchase option has preference $v_0>0$. An **assortment** is a subset $S\subseteq N$. The **most-popular sets** are $A_i=\{1,\dots,i\}$; once the variants are sorted so that $v_1\ge v_2\ge\cdots\ge v_n$, $A_i$ consists of the $i$ most popular variants. Here $A_0=\emptyset$ and $A_n=N$.
--   2. **MNL shares** (1): for $j\in S$,
--   $$q_j(S)=\frac{v_j}{\sum_{i\in S}v_i+v_0}.$$
--   3. **Critical fractile** (6): with $\Phi$ the standard normal distribution function,
--   $$z=\Phi^{-1}\Bigl(1-\frac cp\Bigr),$$
--   defined as the least $x$ with $\Phi(x)\ge 1-c/p$.
--   4. **Store profits** for price $p$, unit cost $c$, store volume $\lambda$, and demand-variability parameters $\sigma,\beta$. In the independent population model, (7),
--   $$\pi_I(S,v)=(p-c)\lambda\sum_{j\in S}q_j-\frac{p\sigma\lambda^\beta e^{-z^2/2}}{\sqrt{2\pi}}\sum_{j\in S}q_j^\beta .$$
--   In the trend-following population model, (8),
--   $$\pi_T(S,v)=\sum_{j\in S}(pq_j-c)^+\lambda .$$
--   Both profits of the empty assortment are $0$.
--   5. **The functions of Lemma 1** (9)–(11), for a fixed $S$ and a real variable $\delta$ (the preference of a variant added to $S$):
--   $$f(\delta)=\sum_{j\in S}v_j+\delta+v_0,$$
--   $$g_I(\delta)=(p-c)\lambda\Bigl(\sum_{j\in S}v_j+\delta\Bigr)-\frac{p\sigma\lambda^\beta e^{-z^2/2}}{\sqrt{2\pi}}\Bigl(\sum_{j\in S}v_j^\beta+\delta^\beta\Bigr)f(\delta)^{1-\beta},$$
--   $$g_T(\delta)=\lambda\Bigl[\sum_{j\in S}(pv_j-cf(\delta))^++(p\delta-cf(\delta))^+\Bigr],$$
--   and $h_I=g_I/f$, $h_T=g_T/f$.
--
--   These are the objects of Theorem 1 and Lemma 1 of the paper; the profits (7) and (8) are the closed forms of the stocking problems (4) under the normal and the trend-following demand laws, as derived on p. 1502. The same objects serve all three missions of the series (Theorems 1, 2 and 3).
--
--   **Formalization Note** Variants are indexed by `Fin n`, 0-based: the paper's variant $j$ is index $j-1$, so $A_i$ is the set of indices below $i$ and the paper's $v_1$ is `v ⟨0, _⟩`; the no-purchase preference $v_0$ is the separate real `v0`. Powers $\lambda^\beta$, $q_j^\beta$, $\delta^\beta$, $f^{1-\beta}$ are `Real.rpow`, so $0^0=1$. The positive part is `max · 0`. $z$ is an infimum; for $0<c<p$ the set is nonempty and bounded below, and the theorem `criticalFractile_spec` states $\Phi(z)=1-c/p$. As printed, (11) has $\lambda$ multiplying only the sum; here $\lambda$ multiplies both terms, which is what makes $h_T(v_j)=\pi_T(S\cup\{j\},v)$ hold as stated on p. 1503 (quasi-convexity is unaffected). The shares and profits are total functions; every result using them assumes $v_j>0$ and $v_0>0$, so no denominator vanishes.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1499, eq. (1); p. 1501, §2.3.1 (σ > 0, 0 ≤ β < 1); p. 1502, eqs. (6)–(8); p. 1503, §3.1 (A_i), Lemma 1, eqs. (9)–(11)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RetailVariety.Structure

/-- The most-popular sets `A_i = {1, …, i}` (§3.1, p. 1503). Variant `j` of the paper is
`⟨j - 1, _⟩ : Fin n`, so `A_i` is the set of indices with `val < i`; `A_0 = ∅`, `A_n = N`. -/
def popularSet (n i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => j.val < i)

/-- MNL choice probability (1), p. 1499: `q_j(S) = v_j / (∑_{i ∈ S} v_i + v_0)`.
The no-purchase preference `v0` is a separate real number, not a variant. -/
noncomputable def share {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n)) (j : Fin n) : ℝ :=
  v j / (∑ i ∈ S, v i + v0)

/-- The critical fractile `z = Φ⁻¹(1 - c/p)` of (6), p. 1502, with `Φ` the standard normal
c.d.f.; written as the least `x` with `Φ(x) ≥ 1 - c/p`. -/
noncomputable def criticalFractile (p c : ℝ) : ℝ :=
  sInf {x : ℝ | 1 - c / p ≤ cdf (gaussianReal 0 1) x}

/-- Independent-population store profit (7), p. 1502:
`π_I(S, v) = (p - c) λ ∑_{j∈S} q_j - (p σ λ^β e^{-z²/2} / √(2π)) ∑_{j∈S} q_j^β`. -/
noncomputable def profitI {n : ℕ} (p c lam σ β : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (p - c) * lam * ∑ j ∈ S, share v v0 S j
    - (p * σ * lam ^ β * Real.exp (-(criticalFractile p c) ^ 2 / 2) / Real.sqrt (2 * Real.pi))
      * ∑ j ∈ S, share v v0 S j ^ β

/-- Trend-following store profit (8), p. 1502: `π_T(S, v) = ∑_{j∈S} (p q_j - c)⁺ λ`. -/
noncomputable def profitT {n : ℕ} (p c lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, max (p * share v v0 S j - c) 0 * lam

/-- `f(δ) = ∑_{j∈S} v_j + δ + v_0`, (9), p. 1503. -/
noncomputable def fDen {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n)) (δ : ℝ) : ℝ :=
  ∑ j ∈ S, v j + δ + v0

/-- `g_I(δ)` of (10), p. 1503:
`(p - c) λ (∑_{j∈S} v_j + δ) - (p σ λ^β e^{-z²/2}/√(2π)) (∑_{j∈S} v_j^β + δ^β) f(δ)^{1-β}`. -/
noncomputable def gI {n : ℕ} (p c lam σ β : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (δ : ℝ) : ℝ :=
  (p - c) * lam * (∑ j ∈ S, v j + δ)
    - (p * σ * lam ^ β * Real.exp (-(criticalFractile p c) ^ 2 / 2) / Real.sqrt (2 * Real.pi))
      * (∑ j ∈ S, v j ^ β + δ ^ β) * fDen v v0 S δ ^ (1 - β)

/-- `g_T(δ)` of (11), p. 1503, with `λ` multiplying both terms:
`λ [∑_{j∈S} (p v_j - c f(δ))⁺ + (p δ - c f(δ))⁺]`. (As printed, `λ` multiplies only the sum.) -/
noncomputable def gT {n : ℕ} (p c lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (δ : ℝ) : ℝ :=
  lam * (∑ j ∈ S, max (p * v j - c * fDen v v0 S δ) 0 + max (p * δ - c * fDen v v0 S δ) 0)

/-- `h_I(δ) = g_I(δ) / f(δ)` (Lemma 1, p. 1503). -/
noncomputable def hI {n : ℕ} (p c lam σ β : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (δ : ℝ) : ℝ :=
  gI p c lam σ β v v0 S δ / fDen v v0 S δ

/-- `h_T(δ) = g_T(δ) / f(δ)` (Lemma 1, p. 1503). -/
noncomputable def hT {n : ℕ} (p c lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (δ : ℝ) : ℝ :=
  gT p c lam v v0 S δ / fDen v v0 S δ

end RetailVariety.Structure


