-- Prove2me | Definitions.Def_RetailerMarketplace_Entry_Model
-- name    : RetailerMarketplace_Entry_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:51.935885+00:00
-- url     : https://prove2.me/theorems/08f91ea6-e74a-44d3-9291-a5fadb511bc9
-- title:
--   §2–§4 and App. A, pp. 4–7, 14 — products μ on [c, ∞), marketplace set, Proposition 1 payoffs, Δπ, v*, k̲, allocations and M's profit
-- statement:
--   This file fixes the model of §2–§4 of Hervas-Drane and Shelegia, *Retailer-Led Marketplaces*.
--
--   **Products.** A unit mass of products is indexed by its consumer valuation $v$; the valuations are distributed according to a probability measure $\mu$ on $\mathbb R$ (in the theorems: supported on $[c,\infty)$, with a density). Its CDF is
--   $$G(v)=\mu\big((-\infty,v]\big).$$
--   Every unit costs $c$ to supply; $f$ is the ad valorem fee, $\lambda$ the share of inattentive consumers the monopolist $M$ can steer, $k$ the fraction of products $M$ can supply.
--
--   **Marketplace products.** The third-party seller $T$ of product $v$ enters when she can break even, i.e. on
--   $$\mathrm{mp}(c,f)=\{v : v(1-f)\ge c\},$$
--   which for $f<1$ is the set $v\ge v_T$ with $v_T=c/(1-f)$, display (1).
--
--   **Payoffs of Proposition 1** (per product market):
--   1. SBM (only $M$): $\pi_M^{SBM}(v)=v-c$.
--   2. SBT (only $T$): $\pi_M^{SBT}(v)=fv$ and $\pi_T^{SBT}(v)=(1-f)v-c$.
--   3. SBMT (both): with $\bar p_T(v)=\dfrac{\lambda v+c(1-\lambda)}{1-f(1-\lambda)}$, $\pi_M^{SBMT}(v)=\lambda(v-c)+(1-\lambda)f\bar p_T(v)$ and $\pi_T^{SBMT}(v)=(1-\lambda)\big(\bar p_T(v)(1-f)-c\big)$.
--
--   **Entry quantities of the proof of Proposition 2** (p. 14): the marginal profitability $\Delta\pi_M^{SBMT-SBT}(v)=\pi_M^{SBMT}(v)-\pi_M^{SBT}(v)$, the valuation
--   $$v^*=\frac{c\lambda}{(1-f)^2(\lambda-f(1-\lambda))}\qquad\text{(A.2)},$$
--   and the capacity threshold $\underline k=1-G(v^*)$.
--
--   **Allocations.** An allocation of $M$ is any measurable set $A$ of products with $\mu(A)\le k$ (admissible). Given the fee, $T$ enters $\mathrm{mp}(c,f)$ and $M$ enters $A$, so $M$'s total profit is
--   $$\Pi(A)=\int_{A\setminus \mathrm{mp}}\pi_M^{SBM}\,d\mu+\int_{A\cap \mathrm{mp}}\pi_M^{SBMT}\,d\mu+\int_{\mathrm{mp}\setminus A}\pi_M^{SBT}\,d\mu,$$
--   and $A$ is an optimal allocation if it is admissible and no admissible set yields a larger $\Pi$.
--
--   These objects are shared by every statement of the mission; the theorems add the standing hypotheses on $c,f,\lambda,k,\mu$.
--
--   **Formalization Note** The marketplace set is written $\{v : c\le v(1-f)\}$ rather than $\{v\ge c/(1-f)\}$ so that it stays meaningful at $f=1$, where Lean's $c/0=0$ would be junk. $v_T$, $\bar p_T$, $\Delta\pi$ and $v^*$ are plain real formulas; every theorem that uses them assumes $f<1$ (and $\lambda\ge 1/2$ for $v^*$), so no denominator vanishes. Allocations are arbitrary measurable sets, never intervals: that optimal allocations are intervals is the content of Proposition 2.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, pp. 4–7 and 14 (PDF pp. 6–9, 16), §2–§4, Proposition 1, display (1), proof of Proposition 2 (Δπ display, (A.2), definition of k̲)

import Mathlib

open MeasureTheory

namespace RetailerMarketplace.Entry

/-- The CDF of product valuations, `G(v) = μ((-∞, v])` (p. 4). -/
noncomputable def G (μ : Measure ℝ) (v : ℝ) : ℝ := (μ (Set.Iic v)).toReal

/-- Marketplace products: the products `v` with `v(1 - f) ≥ c`, which T enters (Lemma 1, (1)). -/
def mp (c f : ℝ) : Set ℝ := {v | c ≤ v * (1 - f)}

/-- The entry threshold `v_T = c/(1 - f)` of (1); used only under `f < 1`. -/
noncomputable def vT (c f : ℝ) : ℝ := c / (1 - f)

/-- Proposition 1, SBM: M's monopoly profit `π_M^SBM = v - c`. -/
def piSBM (c v : ℝ) : ℝ := v - c

/-- Proposition 1, SBT: M's fee revenue `π_M^SBT = f v`. -/
def piSBT_M (f v : ℝ) : ℝ := f * v

/-- Proposition 1, SBMT: T's price `p̄_T = (λ v + c(1 - λ))/(1 - f(1 - λ))`. -/
noncomputable def pbarT (c f lam v : ℝ) : ℝ := (lam * v + c * (1 - lam)) / (1 - f * (1 - lam))

/-- Proposition 1, SBMT: M's profit `π_M^SBMT = λ(v - c) + (1 - λ) f p̄_T`. -/
noncomputable def piSBMT_M (c f lam v : ℝ) : ℝ := lam * (v - c) + (1 - lam) * f * pbarT c f lam v

/-- Proposition 1, SBT: T's profit `π_T^SBT = (1 - f) v - c`. -/
def piSBT_T (c f v : ℝ) : ℝ := (1 - f) * v - c

/-- Proposition 1, SBMT: T's profit `π_T^SBMT = (1 - λ)(p̄_T (1 - f) - c)`. -/
noncomputable def piSBMT_T (c f lam v : ℝ) : ℝ := (1 - lam) * (pbarT c f lam v * (1 - f) - c)

/-- M's marginal profitability of entering a marketplace product,
`Δπ_M^{SBMT-SBT}(v) = π_M^SBMT - π_M^SBT` (proof of Proposition 2, p. 14). -/
noncomputable def dPi (c f lam v : ℝ) : ℝ := piSBMT_M c f lam v - piSBT_M f v

/-- `v* = cλ/((1 - f)^2 (λ - f(1 - λ)))`, display (A.2). -/
noncomputable def vStar (c f lam : ℝ) : ℝ := c * lam / ((1 - f) ^ 2 * (lam - f * (1 - lam)))

/-- The capacity threshold `k̲ = 1 - G(v*)` (proof of Proposition 2, p. 14). -/
noncomputable def kbar (μ : Measure ℝ) (c f lam : ℝ) : ℝ := 1 - G μ (vStar c f lam)

/-- An admissible capacity allocation of M: a measurable set of products of mass at most `k`. -/
def Admissible (μ : Measure ℝ) (k : ℝ) (A : Set ℝ) : Prop :=
  MeasurableSet A ∧ μ A ≤ ENNReal.ofReal k

/-- M's total profit when he enters the products in `A` and T enters the marketplace products
`mp c f`: SBM on `A \ mp`, SBMT on `A ∩ mp`, SBT on `mp \ A`. -/
noncomputable def profitM (μ : Measure ℝ) (c f lam : ℝ) (A : Set ℝ) : ℝ :=
  (∫ v in A \ mp c f, piSBM c v ∂μ) + (∫ v in A ∩ mp c f, piSBMT_M c f lam v ∂μ)
    + (∫ v in mp c f \ A, piSBT_M f v ∂μ)

/-- `A` is an optimal Stage-2 allocation for M: admissible, and no admissible set yields more. -/
def IsOptimalAlloc (μ : Measure ℝ) (c f lam k : ℝ) (A : Set ℝ) : Prop :=
  Admissible μ k A ∧ ∀ B, Admissible μ k B → profitM μ c f lam B ≤ profitM μ c f lam A

end RetailerMarketplace.Entry


