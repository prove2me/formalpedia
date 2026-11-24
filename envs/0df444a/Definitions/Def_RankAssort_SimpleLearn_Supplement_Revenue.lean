-- Prove2me | Definitions.Def_RankAssort_SimpleLearn_Supplement_Revenue
-- name    : RankAssort_SimpleLearn_Supplement_Revenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:23:30.384109+00:00
-- url     : https://prove2.me/theorems/7e2cb546-b19b-4ede-b829-a62d0bccb8cd
-- title:
--   §6, pp. 40–42 — the revenue model (3)–(4) with a general purchase law, E[R(π)], and Algorithm 4
-- statement:
--   **Revenue model (§6).** Each product $i\in[n]$ earns a per-unit revenue $r_i\ge0$; write $r_{\max}=\max_i r_i$. A customer of type $\theta\sim\mathcal D$ browses her first $k(\theta)$ ranks and clicks each product $i$ with probability $p_i(\theta)$, with no bias ($f\equiv0$, footnote 14). If she is hooked (clicks at least one product in her window) she purchases product $i$ with probability $\varphi_\theta(i)\ge0$, where $\sum_i\varphi_\theta(i)\le1$ and the remaining probability is no purchase. The revenue of a ranking $\pi$ is $R(\pi)=H(\pi)\sum_i r_i\varphi_\theta(i)$ (3), and its expectation (4) is
--   $$\mathbb E[R(\pi)]=\mathbb E_{\theta\sim\mathcal D}\Big[\Big(1-\prod_{j\le\min(k(\theta),|\pi|)}\big(1-p_{\pi^{-1}(j)}(\theta)\big)\Big)\sum_{i\in[n]}r_i\varphi_\theta(i)\Big],$$
--   defined for every, possibly partial, ranking $\pi$. For Lemma 4, the revenue-weighted joint term at rank $r$ is
--   $$\mathbb E_\theta\Big[\Pr\big(\bar C(r-1,\tilde\pi)\,C_{\pi^{*-1}(r)}(\pi^*)=1\big)\sum_i r_i\varphi_\theta(i)\Big],$$
--   the probability over the independent likes of the products in the window.
--
--   **Threshold Acceptance Algorithm for Revenue Maximization (Algorithm 4).** A learning-phase customer is a type $\theta\sim\mathcal D$, a like-profile with independent $\mathrm{Bernoulli}(p_i(\theta))$ coordinates and, independently given $\theta$, a purchase outcome with law $\varphi_\theta$. The algorithm is Algorithm 3's loop with $\tau^{\max}=r_{\max}$, $\tau^{\min}=\epsilon/n$, sample size
--   $$L=\Big\lceil\frac{n^2r_{\max}^2}{\epsilon^2}\log\frac{n}{\sqrt\delta}\Big\rceil,$$
--   and $\Delta=S/L$, where $S$ is the total revenue from the displayed customers whose first click is the candidate product $i$ at the current rank.
--
--   **Formalization Note** `IsRevenueModel τ rev φ` bundles $f\equiv0$, $r_i\ge0$, measurability of $\theta\mapsto\varphi_\theta(i)$, $\varphi\ge0$ and $\sum_i\varphi_\theta(i)\le1$. The purchase outcome is an element of `Fin (n + 1)`, `Fin.last n` meaning no purchase. $r_{\max}$ is `⨆ i, rev i`. The paper's printed logit $\varphi_t(i,[n])=\exp(-\nu_{it}/(\nu_{0t}+\sum_j\nu_{jt}))$ is not a probability distribution (for $n=2$ and $\nu\equiv1$ each value is $e^{-1/3}\approx0.72$), so the purchase law is a general one; both logit readings, $\nu_i/(\nu_0+\sum_j\nu_j)$ and $e^{\nu_i}/(e^{\nu_0}+\sum_je^{\nu_j})$, are instances. The products of $U\setminus\{i\}$ that Algorithm 4 places after rank $r$ do not affect the observed first clicks and purchases, so they are not modelled. Probabilities of click events use the coupled like-profile, which under zero bias is the joint law of the clicks.
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, pp. 40–41, §6, (3)–(4) and footnote 14; p. 42, Algorithm 4; p. 67, Lemma 4

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model
import Definitions.Def_RankAssort_SimpleLearn_Supplement_Threshold

namespace RankAssort.SimpleLearn.Supplement
open MeasureTheory

/-! # The revenue model of §6 and Algorithm 4

Ferreira, Parthasarathy, Sekar, *Learning to Rank an Assortment of Products*, SSRN 3395992 author
manuscript, §6 (pp. 40–42), (3)–(4), footnote 14, Algorithm 4 (p. 42). A purchase outcome is an
element of `Fin (n + 1)`: `⟨j, _⟩` with `j < n` is the purchase of product `j`, and `Fin.last n`
is "no purchase". -/

variable {n : ℕ}

/-- The standing assumptions of the revenue model (§6): zero bias `f ≡ 0` (footnote 14),
nonnegative per-unit revenues `rᵢ ≥ 0`, and a type-dependent purchase law `φ θ i ≥ 0`,
measurable in `θ`, with `Σᵢ φ θ i ≤ 1` (the rest is the no-purchase probability). -/
def IsRevenueModel {Θ : Type*} [MeasurableSpace Θ] (τ : Θ → CustomerType n)
    (rev : Fin n → ℝ) (φ : Θ → Fin n → ℝ) : Prop :=
  (∀ θ i S, (τ θ).f i S = 0) ∧ (∀ i, 0 ≤ rev i) ∧ (∀ i, Measurable fun θ => φ θ i) ∧
    (∀ θ i, 0 ≤ φ θ i) ∧ ∀ θ, ∑ i, φ θ i ≤ 1

/-- `rmax = max_{i ∈ [n]} rᵢ`. -/
noncomputable def rmax (rev : Fin n → ℝ) : ℝ := ⨆ i, rev i

/-- `Σᵢ rᵢ φ_θ(i)`: the expected revenue from a hooked customer of type `θ`. -/
def revWeight {Θ : Type*} (rev : Fin n → ℝ) (φ : Θ → Fin n → ℝ) (θ : Θ) : ℝ :=
  ∑ i, rev i * φ θ i

/-- `E[R(π)]` ((3)–(4), p. 41): the hook probability of `l` times the expected purchase revenue,
averaged over types `θ ∼ D`. Defined for every (partial) ranking `l`. -/
noncomputable def expRevenue {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (rev : Fin n → ℝ) (φ : Θ → Fin n → ℝ) (l : List (Fin n)) : ℝ :=
  ∫ θ, hookProb (τ θ) l * revWeight rev φ θ ∂D

/-- `E_t[Pr(C̄(r, π̃) C_{π∗⁻¹(r+1)}(π∗) = 1) Σᵢ rᵢ φ_t(i)]` (0-based `r`; the paper's term for
rank `r + 1` in Lemma 4, p. 67), the probability taken under the coupled like-profile. -/
noncomputable def revJointTerm {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (rev : Fin n → ℝ) (φ : Θ → Fin n → ℝ) (piT piStar : List (Fin n))
    (r : ℕ) : ℝ :=
  ∫ θ, coupledProb (τ θ) (fun L => noClickTop (τ θ) piT r L ∧ clicksAt (τ θ) piStar r L) *
    revWeight rev φ θ ∂D

/-- Probability of the purchase outcome `j` for a hooked customer of type `θ`. -/
def purchaseWeight {Θ : Type*} (φ : Θ → Fin n → ℝ) (θ : Θ) (j : Fin (n + 1)) : ℝ :=
  if h : (j : ℕ) < n then φ θ ⟨j, h⟩ else 1 - ∑ i, φ θ i

/-- Revenue of the purchase outcome `j` (`0` for no purchase). -/
def saleRevenue (rev : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  if h : (j : ℕ) < n then rev ⟨j, h⟩ else 0

/-- Law of one arriving customer for Algorithm 4: type `θ ∼ D`; given `θ`, a like-profile `L`
from the coupled first-click law and, independently, a purchase outcome `j` with law
`purchaseWeight φ θ`. -/
noncomputable def customerLawRev {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (φ : Θ → Fin n → ℝ) :
    Measure (Θ × (Fin n → Bool) × Fin (n + 1)) :=
  ∑ L : Fin n → Bool, ∑ j : Fin (n + 1),
    (D.withDensity fun θ => ENNReal.ofReal (likeWeight (τ θ) L * purchaseWeight φ θ j)).prod
      (Measure.dirac (L, j))

/-- Algorithm 4's sample size `L = (n² rmax²/ϵ²) log(n/√δ)`, rounded up. -/
noncomputable def sampleSizeRev (n : ℕ) (eps delta R : ℝ) : ℕ :=
  ⌈((n : ℝ) ^ 2 * R ^ 2 / eps ^ 2) * Real.log (n / Real.sqrt delta)⌉₊

open Classical in
/-- A run of the Threshold Acceptance Algorithm for Revenue Maximization (Algorithm 4, p. 42)
with `τmax = rmax`, `τmin = ϵ/n`, scan order `order`, on the realized stream `z` (customer `s` has
type `(z s).1`, like-profile `(z s).2.1` and purchase outcome `(z s).2.2`). For a candidate `i` at
the current rank, customer `s` contributes the revenue of her purchase when her first click is `i`
and `0` otherwise; `Δ = S/L`. The products of `U \ {i}` placed after rank `r` do not affect these
observations and are not modelled. -/
noncomputable def thresholdAcceptanceRev {Θ : Type*} (τ : Θ → CustomerType n)
    (rev : Fin n → ℝ) (eps delta α : ℝ) (order : List (Fin n))
    (z : ℕ → Θ × (Fin n → Bool) × Fin (n + 1)) : TAState n :=
  taOutput
    (fun σ i s => if firstClick (τ (z s).1) σ i (z s).2.1 then saleRevenue rev (z s).2.2 else 0)
    (sampleSizeRev n eps delta (rmax rev)) (rmax rev) (eps / n) α order

end RankAssort.SimpleLearn.Supplement


