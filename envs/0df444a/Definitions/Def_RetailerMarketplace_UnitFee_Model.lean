-- Prove2me | Definitions.Def_RetailerMarketplace_UnitFee_Model
-- name    : RetailerMarketplace_UnitFee_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:12.711216+00:00
-- url     : https://prove2.me/theorems/9adeeb11-33ac-4049-afe4-e2704792f973
-- title:
--   §2–§4, App. B.3, pp. 4–7, 18 — products μ on [c, ∞), fees f and t, steering λ, capacity k, marketplace set, unit-fee payoffs (B.1), allocations, Π_M(k, f, t)
-- statement:
--   This file fixes the model of Hervas-Drane and Shelegia's retailer-led marketplace with an additional **per-unit fee** (Appendix B.3), and the monopolist's profit as a function of the two fees.
--
--   **Primitives.** There is a unit mass of products, indexed by their consumer valuation $v$, distributed according to a probability measure $\mu$ on $\mathbb R$ (the CDF $G$ of the paper), concentrated on $[c,\infty)$, where $c$ is the firms' common marginal cost. The monopolist $M$ charges an ad valorem fee $f\in[0,1]$ on the third-party sellers' revenue and a per-unit fee $t\ge 0$ on every unit a third-party seller sells, steers a share $\lambda$ of the consumers in each product market, and can supply at most a fraction $k\in[0,1]$ of the products.
--
--   **Marketplace products.** The third-party seller $T$ of product $v$ enters the marketplace exactly when she does not make a loss there:
--   $$\mathrm{mp}(c,f,t)=\{v\in\mathbb R : v(1-f)\ge c+t\}.$$
--   For $f<1$ this is $\{v\ge v_T\}$ with $v_T=(c+t)/(1-f)$ (Appendix B.3); for $f=1$ and $c>0$, $t \ge 0$ it is empty.
--
--   **Per-market payoffs with a unit fee.** For a product $v$:
--   1. SBM (monopolist alone): $\pi_M^{SBM}(v)=v-c$.
--   2. SBT (third-party seller alone, price $v$, one unit sold): $M$ earns $\pi_M^{SBT}(v)=fv+t$, and $T$ earns $\pi_T^{SBT}(v)=(1-f)v-c-t$.
--   3. SBMT (both): $T$ charges the price (B.1)
--   $$\bar p_T=\frac{\lambda v+(1-\lambda)(c+t)}{1-f(1-\lambda)},$$
--   $M$ sells $\lambda$ units at $v$ and collects $f\bar p_T+t$ on each of the $1-\lambda$ units $T$ sells, so $\pi_M^{SBMT}(v)=\lambda(v-c)+(1-\lambda)(f\bar p_T+t)$, while $\pi_T^{SBMT}(v)=(1-\lambda)(\bar p_T(1-f)-c-t)$.
--
--   **Allocations and profit.** An allocation is any measurable set $A$ of products of $\mu$-mass at most $k$ (the products $M$ enters). $M$'s total profit from $A$ is
--   $$\mathrm{profit}_M(A)=\int_{A\setminus \mathrm{mp}}(v-c)\,d\mu+\int_{A\cap \mathrm{mp}}\pi_M^{SBMT}(v)\,d\mu+\int_{\mathrm{mp}\setminus A} (fv+t)\,d\mu .$$
--   An allocation is optimal if no admissible allocation earns more.
--
--   **Fee-stage value and optimal fees.** $M$'s profit as a function of the fees is the value of his allocation problem,
--   $$\Pi_M(k,f,t)=\sup\{\mathrm{profit}_M(A) : A \text{ measurable},\ \mu(A)\le k\},$$
--   and a pair $(f^*,t^*)$ is an optimal fee pair if $f^*\in[0,1]$, $t^*\ge 0$ and $\Pi_M(k,f,t)\le\Pi_M(k,f^*,t^*)$ for every $f\in[0,1]$, $t\ge0$.
--
--   These objects are the backward-induction input of the fee stage: Stage 3 is the pricing equilibrium, the sellers' Stage-2 entry is the set $\mathrm{mp}$, and the monopolist's Stage-2 entry is the optimisation inside $\Pi_M$.
--
--   **Formalization Note.** The paper states (B.1) and the other unit-fee payoffs without proof ("the remaining properties of the price competition equilibrium derived in our baseline analysis are unaffected"); here they are definitions, the Stage-3 payoffs that backward induction plugs in. The marketplace set is written $v(1-f)\ge c+t$ rather than $v\ge (c+t)/(1-f)$, so it is also correct at $f=1$, where Lean's division by zero would return $0$; entry at zero profit follows the convention of the paper's Lemma 1. The supremum ranges over all measurable sets of mass at most $k$, not only intervals, and $M$'s allocation is re-optimised at every fee pair. The hypotheses on $\mu$ (probability, support in $[c,\infty)$, a density, finite mean, full support) are carried by the theorems, not by this file; under a finite mean the set of profits is nonempty and bounded above, so $\Pi_M$ is a genuine supremum.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, pp. 4–7 (PDF pp. 6–9), §2, Proposition 1, display (1); p. 18 (PDF p. 20), App. B.3, display (B.1)

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model
open MeasureTheory

namespace RetailerMarketplace.UnitFee

/-! Hervas-Drane & Shelegia, *Retailer-Led Marketplaces*, Management Science (2025), Articles in
Advance: the model of §2–§4 (printed pp. 4–7) with the per-unit fee `t` of App. B.3 (printed
p. 18). Parameters: marginal cost `c`, ad valorem fee `f`, per-unit fee `t` (paid per unit the
third-party seller T sells), steering share `lam` (λ), capacity `k`. Products are indexed by their
valuation `v`; their distribution `G` is a measure `μ : Measure ℝ` (hypotheses on `μ` are stated
in each theorem). -/

/-- The marketplace products: T enters product `v` iff `v (1 - f) - c - t ≥ 0`
(entry at zero profit, B.3 with Lemma 1's convention). Equals `[v_T, ∞)` for `f < 1`. -/
def mp (c f t : ℝ) : Set ℝ := {v | c + t ≤ v * (1 - f)}

/-- `v_T ≡ (c + t) / (1 - f)` (B.3, p. 18); only meaningful for `f < 1`. -/
noncomputable def vT (c f t : ℝ) : ℝ := (c + t) / (1 - f)

/-- T's SBMT price (B.1): `p̄_T = (λ v + (1 - λ)(c + t)) / (1 - f (1 - λ))`. -/
noncomputable def pbarT (c f t lam v : ℝ) : ℝ :=
  (lam * v + (1 - lam) * (c + t)) / (1 - f * (1 - lam))

/-- M's fee revenue in an SBT product market: T sells one unit at price `v`, so `f v + t`. -/
def piSBT_M (f t v : ℝ) : ℝ := f * v + t

/-- M's profit in an SBMT product market: he sells `λ` units at `v`, T sells `1 - λ` units at
`p̄_T`, each paying the fee `f p̄_T + t`. -/
noncomputable def piSBMT_M (c f t lam v : ℝ) : ℝ :=
  lam * (v - c) + (1 - lam) * (f * pbarT c f t lam v + t)

/-- T's profit in an SBT product market: `(1 - f) v - c - t`. -/
def piSBT_T (c f t v : ℝ) : ℝ := (1 - f) * v - c - t

/-- T's profit in an SBMT product market: `(1 - λ)(p̄_T (1 - f) - c - t)`. -/
noncomputable def piSBMT_T (c f t lam v : ℝ) : ℝ :=
  (1 - lam) * (pbarT c f t lam v * (1 - f) - c - t)

/-- M's total profit when he enters the products `A`: SBM on `A \ mp`, SBMT on `A ∩ mp`,
SBT on `mp \ A`. -/
noncomputable def profitM (μ : Measure ℝ) (c f t lam : ℝ) (A : Set ℝ) : ℝ :=
  (∫ v in A \ mp c f t, RetailerMarketplace.Entry.piSBM c v ∂μ) + (∫ v in A ∩ mp c f t, piSBMT_M c f t lam v ∂μ)
    + (∫ v in mp c f t \ A, piSBT_M f t v ∂μ)

/-- `A` is an optimal Stage-2 allocation of M. -/
def IsOptimalAlloc (μ : Measure ℝ) (c f t lam k : ℝ) (A : Set ℝ) : Prop :=
  RetailerMarketplace.Entry.Admissible μ k A ∧ ∀ B, RetailerMarketplace.Entry.Admissible μ k B → profitM μ c f t lam B ≤ profitM μ c f t lam A

/-- M's profit as a function of the fees `(f, t)`: the value of his Stage-2 problem,
`Π_M(k, f, t) = sup { profitM A | A admissible }`. -/
noncomputable def PiM (μ : Measure ℝ) (c f t lam k : ℝ) : ℝ :=
  sSup (profitM μ c f t lam '' {A | RetailerMarketplace.Entry.Admissible μ k A})

/-- `(fs, ts)` is an optimal fee pair: `fs ∈ [0, 1]`, `ts ≥ 0`, and it maximises `PiM` over
all `(f, t) ∈ [0, 1] × [0, ∞)`. -/
def IsOptimalFee (μ : Measure ℝ) (c lam k fs ts : ℝ) : Prop :=
  fs ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ ts ∧
    ∀ f ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, 0 ≤ t → PiM μ c f t lam k ≤ PiM μ c fs ts lam k

end RetailerMarketplace.UnitFee


