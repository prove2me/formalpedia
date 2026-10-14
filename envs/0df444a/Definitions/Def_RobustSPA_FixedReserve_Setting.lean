-- Prove2me | Definitions.Def_RobustSPA_FixedReserve_Setting
-- name    : RobustSPA_FixedReserve_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:16.943779+00:00
-- url     : https://prove2.me/theorems/94eb699d-6b0e-4fd6-88fd-f99310f7365d
-- title:
--   §2, §4.1–4.2, §5.2.1, pp. 9–24 — regret (2), the classes 𝓕_iid, 𝓕_aff, 𝓕_mix, the second-price auction SPA(r) with reserve r, and the closed form of Proposition 5
-- statement:
--   This file fixes the model of Anunrojwong, Balseiro and Besbes for one item sold to $n$ buyers whose valuations $v=(v_1,\dots,v_n)$ lie in the **type cube** $[0,1]^n$.
--
--   1. A **direct mechanism** $m=(x,p)$ assigns to each buyer $i$ an allocation probability $x_i(v)$ and a payment $p_i(v)$.
--   2. With $v^{(1)}=\max_i v_i$ the highest and $v^{(2)}$ the second-highest valuation, the **regret** of $m$ under a joint law $\mathbf F$ of $v$ is
--   $$R_n(m,\mathbf F)=\mathbb E_{v\sim\mathbf F}\Big[v^{(1)}-\sum_{i=1}^n p_i(v)\Big],$$
--   the revenue lost relative to a seller who knows the valuations (display (2)).
--   3. **Classes of distributions** (all supported on $[0,1]^n$):
--      - $\mathcal F_{\mathrm{all}}$: all probability laws on $[0,1]^n$;
--      - $\mathcal F_{\mathrm{iid}}$ (Definition 1): the product laws $G^{\otimes n}$ with $G$ a probability law on $[0,1]$;
--      - $\mathcal F_{\mathrm{exc}}$ (Definition 3): the laws invariant under every permutation of the buyers;
--      - **affiliation** (Definition 4): $\Pr(A\cap B\mid S)\ge \Pr(A\mid S)\Pr(B\mid S)$ for all increasing sets $A,B$ and every sublattice $S$ (a set closed under coordinatewise $\min$ and $\max$); $\mathcal F_{\mathrm{aff}}$ is the set of exchangeable affiliated laws on $[0,1]^n$ (p. 19);
--      - $\mathcal F_{\mathrm{mix}}$ (Definition 6): the laws whose joint CDF is $\mathbf F(v)=\int\prod_{i=1}^n G(v_i)\,d\mu(G)$ for a probability measure $\mu$ on the set of distributions, i.e. mixtures of i.i.d. laws.
--   4. For a law $\rho$ of reserve prices, **$\mathrm{SPA}(\rho)$** allocates the item to the highest bidder and, for a reserve $q\sim\rho$, sells if the highest bid is at least $q$, at price $\max(v^{(2)},q)$. The winner's expected payment is $\mathbb E_{q\sim\rho}[\max(v^{(2)},q)\mathbf 1(v^{(1)}\ge q)]$. **$\mathrm{SPA}(r)$**, the second-price auction with fixed deterministic reserve $r$, is $\mathrm{SPA}(\delta_r)$.
--   5. The closed form of Proposition 5:
--   $$W_n(r)=\begin{cases}\max(1-r,\,r), & n=1,\\[2pt] \dfrac{(1-r)^n(n-1)^{n-1}}{((1-r)n-r)^{n-1}}, & n\ge 2,\ r\le \tfrac12,\\[4pt] r, & n\ge 2,\ r>\tfrac12.\end{cases}$$
--
--   These are the objects of the paper's §5.2.1 benchmark: the worst-case regret of a second-price auction with a fixed reserve, to be compared with the optimal random-reserve auction of Theorem 1.
--
--   **Formalization Note** Buyers are indexed by `Fin n`. Laws on $[0,1]^n$ are probability measures on $\mathbb R^n$ giving the complement of the cube measure $0$. $v^{(2)}$ is the largest $\min(v_i,v_j)$ over pairs $i\ne j$ (it is $0$ when $n=1$, where it never matters since the price is then $\max(0,q)=q$). Ties for the highest bid go to the lowest index; the paper breaks ties arbitrarily, and the revenue, hence the regret, does not depend on the rule. Affiliation is stated cross-multiplied, $\mu(A\cap S)\mu(B\cap S)\le\mu(A\cap B\cap S)\mu(S)$, so that a null sublattice imposes nothing, and only for measurable $A,B,S$. In $\mathcal F_{\mathrm{mix}}$ the mixing measure lives on the space of measures on $\mathbb R$ with the Giry σ-algebra, almost every $G$ is a probability law on $[0,1]$ (which the CDF identity forces anyway), and $\mathbf F(v)$ is the measure of $\{u: u_i\le v_i\ \forall i\}$. The mechanism-class constraints (IR), (IC), (AC) are not needed by any statement of this mission and are not encoded.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, pp. 9–10 (2), Definition 1 and SPA with random reserve (p. 13), Definitions 3–4 (p. 18), p. 19 (𝓕_aff), Definition 6 (p. 21), Proposition 5 (p. 24)

import Mathlib

namespace RobustSPA.FixedReserve

open MeasureTheory
open scoped Classical

/-- The type cube `[0,1]ⁿ`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Icc 0 1

/-- A direct mechanism for `n` buyers: allocation probabilities `x i v` and payments `p i v`. -/
structure Mechanism (n : ℕ) where
  x : Fin n → (Fin n → ℝ) → ℝ
  p : Fin n → (Fin n → ℝ) → ℝ

/-- The highest valuation `v^(1) = max v`. -/
noncomputable def top {n : ℕ} (v : Fin n → ℝ) : ℝ := ⨆ i, v i

/-- The second-highest valuation `v^(2)` (the largest minimum over pairs of distinct buyers;
`0` when `n = 1`). -/
noncomputable def second {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ⨆ q : {q : Fin n × Fin n // q.1 ≠ q.2}, min (v q.1.1) (v q.1.2)

/-- The regret (2): `E_{v∼μ}[max v − Σᵢ pᵢ(v)]`. -/
noncomputable def regret {n : ℕ} (m : Mechanism n) (μ : Measure (Fin n → ℝ)) : ℝ :=
  ∫ v, (top v - ∑ i, m.p i v) ∂μ

/-- `𝓕_all`: all probability distributions supported on `[0,1]ⁿ`. -/
def Fall (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | IsProbabilityMeasure μ ∧ μ (cube n)ᶜ = 0}

/-- `𝓕_iid` (Definition 1): `n` i.i.d. valuations drawn from a law `G` supported on `[0,1]`. -/
def Fiid (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | ∃ G : ProbabilityMeasure ℝ, (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0 ∧
    μ = Measure.pi (fun _ : Fin n => (G : Measure ℝ))}

/-- `𝓕_exc` (Definition 3): the exchangeable distributions in `𝓕_all`. -/
def Fexc (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | μ ∈ Fall n ∧ ∀ σ : Equiv.Perm (Fin n), μ.map (fun v => v ∘ σ) = μ}

/-- Affiliation (Definition 4): for all increasing sets `A`, `B` and every sublattice `S`,
`Pr(A ∩ B | S) ≥ Pr(A | S) Pr(B | S)`, cross-multiplied by `μ(S)²` (so a null `S` imposes
nothing) and restricted to measurable sets. -/
def Affiliated {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  ∀ A B S : Set (Fin n → ℝ), MeasurableSet A → MeasurableSet B → MeasurableSet S →
    IsUpperSet A → IsUpperSet B → (∀ v ∈ S, ∀ w ∈ S, v ⊓ w ∈ S ∧ v ⊔ w ∈ S) →
    μ (A ∩ S) * μ (B ∩ S) ≤ μ (A ∩ B ∩ S) * μ S

/-- `𝓕_aff`: the exchangeable and affiliated distributions supported on `[0,1]ⁿ` (p. 19). -/
def Faff (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | μ ∈ Fexc n ∧ Affiliated μ}

/-- The CDF of a law on `ℝ`. -/
noncomputable def cdfOf (G : Measure ℝ) (t : ℝ) : ℝ := (G (Set.Iic t)).toReal

/-- `𝓕_mix` (Definition 6): the laws `F` on `[0,1]ⁿ` for which there is a probability measure
`M` on the set of distributions (with the Giry σ-algebra), almost every `G` a probability law
on `[0,1]`, such that the joint CDF is `F(v) = ∫ ∏ᵢ G(vᵢ) dM(G)` for every `v`. -/
def Fmix (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | μ ∈ Fall n ∧ ∃ M : Measure (Measure ℝ), IsProbabilityMeasure M ∧
    (∀ᵐ G ∂M, IsProbabilityMeasure G ∧ G (Set.Icc 0 1)ᶜ = 0) ∧
    ∀ v : Fin n → ℝ, (μ (Set.Iic v)).toReal = ∫ G, ∏ i, cdfOf G (v i) ∂M}

/-- Buyer `i` wins: a highest bid, ties broken in favour of the lowest index. -/
def isWinner {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : Prop :=
  (∀ j, v j ≤ v i) ∧ ∀ j, j < i → v j < v i

/-- `SPA(ρ)`: second-price auction with random reserve `q ∼ ρ`. The winner is allocated with
probability `ρ((-∞, v_i])` and pays `E_{q∼ρ}[max(v^(2), q) 1(v_i ≥ q)]`. With
`ρ = δ_r` this is `SPA(r)`, the second-price auction with fixed deterministic reserve `r`. -/
noncomputable def SPA {n : ℕ} (ρ : Measure ℝ) : Mechanism n where
  x i v := if isWinner v i then (ρ (Set.Iic (v i))).toReal else 0
  p i v := if isWinner v i then
    ∫ q, (Set.Iic (v i)).indicator (fun q => max (second v) q) q ∂ρ else 0

/-- The closed form of Proposition 5 for the worst-case regret of `SPA(r)`:
`max(1 − r, r)` for `n = 1`; for `n ≥ 2`,
`(1−r)ⁿ(n−1)^{n−1}/((1−r)n−r)^{n−1}` if `r ≤ 1/2` and `r` if `r > 1/2`. -/
noncomputable def wcFixed (n : ℕ) (r : ℝ) : ℝ :=
  if n = 1 then max (1 - r) r
  else if r ≤ 1 / 2 then
    (1 - r) ^ n * ((n : ℝ) - 1) ^ (n - 1) / ((1 - r) * n - r) ^ (n - 1)
  else r

end RobustSPA.FixedReserve


