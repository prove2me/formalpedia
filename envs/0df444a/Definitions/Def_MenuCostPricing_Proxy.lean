-- Prove2me | Definitions.Def_MenuCostPricing_Proxy
-- name    : MenuCostPricing_Proxy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:22.832108+00:00
-- url     : https://prove2.me/theorems/14fc33e6-b5f9-4ed1-95b1-dda084dbee2a
-- title:
--   §3.3–§3.4, pp.15–17 — change set $\Gamma(x)$, proxy demand, rewards $\hat{\mathcal R}^i_{\alpha,\beta}$ (7) and $\hat{\mathcal R}_{\alpha,\beta}$, APX$(\alpha,\beta)$, the coupling of B.2
-- statement:
--   For a strategy $x$, $\Gamma(x)=\{t\in[2,T]:\Delta_{t-1,t}(x)>0\}$ is the set of periods with a price change (the paper's $\Gamma^*$ for $x=x^*$).
--
--   Given guesses $\hat w_1,\dots,\hat w_T$ and $\beta\ge0$, the **proxy demand** of product $i$ under its price vector $x_i$ is $\hat D^t_i(x_i;\beta)=\sum_{\nu=1}^{N_t}\hat Y^t_i(x_i,\nu;\beta)$ with independent
--   $$
--   \hat Y^t_i(x_i,\nu;\beta)\sim\mathrm{Bernoulli}\Big(\frac{w^t_{i,x^t_i}}{1+(1+\beta)\hat w_t}\Big),
--   $$
--   and $\hat U^t_i(x_i;\beta)=[u^1_i-\sum_{\tau<t}\hat D^\tau_i(x_i;\beta)]^+$. The **expected reward** of product $i$ and of the strategy are
--   $$
--   \hat{\mathcal R}^i_{\alpha,\beta}(x_i)=\sum_{t\in[T]}\mathbb E\big[\min\{\hat U^t_i,\hat D^t_i\}\big]\cdot p_{i,x^t_i},\qquad \hat{\mathcal R}_{\alpha,\beta}(x)=\sum_{t\in[T]}\sum_{i\in[n]}\mathbb E\big[\min\{\hat U^t_i,\hat D^t_i\}\big]\cdot p_{i,x^t_i};
--   $$
--   neither depends on $\alpha$. A strategy is **feasible to APX$(\alpha,\beta)$** for $(\Gamma,\hat w)$ when (1) $C_{\mathrm{var}}(x)\le B-|\Gamma|f$, (2) $\Delta_{t-1,t}(x)=0$ for $t\notin\Gamma$, and (3) $(1-\alpha)\hat w_t\le w_t(x)\le(1+\beta)\hat w_t$ for every $t$.
--
--   For Claim B.2, along one realization of arrivals $N_t$, interest indicators $Y^t_i(x,\nu)$ and coupling variables $B^t_{i,\nu}$, the true demand is $D^t_i=\sum_{\nu\le N_t}Y^t_i(x,\nu)$ and the coupled proxy demand is $\hat D^t_i=\sum_{\nu\le N_t}B^t_{i,\nu}Y^t_i(x,\nu)$.
--
--   These are the objects of the proxy problem through which the FPTAS works.
--
--   **Formalization Note** The Bernoulli parameter is clamped to $[0,1]$; for strategies feasible to APX$(\alpha,\beta)$ it already lies there. Per product, the proxy demand path has independent periods (`Measure.pi`). $\Gamma$ is a set of Lean periods with $t\ge1$. Customers in the coupling are indexed $0,\dots,N_t-1$.
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), §3.3, p.15 (Γ∗, (3)–(4)); §3.4, pp.16–17 (APX(α, β), R̂, D̂, Û); §3.5, (7), p.18; App. B.2, p.46 (coupling)

import Mathlib
import Definitions.Def_MenuCostPricing_Model

namespace MenuCostPricing

open MeasureTheory

variable {n L T : ℕ}

/-- The set `Γ(x) = {t ∈ [2, T] : ∆_{t−1,t}(x) > 0}` of periods whose prices differ from the previous
period under `x` (§3.3, p.15, where it is written `Γ∗` for `x = x∗`). -/
def changeSet (x : Strategy n L T) : Finset (Fin T) :=
  Finset.univ.filter (fun t => 1 ≤ t.val ∧ 0 < Delta x t)

/-- The number `[0, 1]`-clamp `max 0 (min 1 q)` of a real `q`. -/
def clampUnit (q : ℝ) : ℝ := max 0 (min 1 q)

lemma clampUnit_nonneg (q : ℝ) : 0 ≤ clampUnit q := le_max_left _ _

lemma clampUnit_le_one (q : ℝ) : clampUnit q ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- The Bernoulli law with success probability `clampUnit q` (`true` is a success). -/
noncomputable def bern (q : ℝ) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ENNReal.ofReal (clampUnit q) else ENNReal.ofReal (1 - clampUnit q))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, Bool.false_eq_true, if_false]
      rw [← ENNReal.ofReal_add (clampUnit_nonneg q) (by linarith [clampUnit_le_one q])]
      simp)

/-- The law of the sum of `k` independent Bernoulli variables with success probability
`clampUnit q`. -/
noncomputable def bernSum (q : ℝ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | k + 1 => (bernSum q k).bind fun s => (bern q).map fun b => s + if b then 1 else 0

namespace Instance

variable (I : Instance n L T)

/-- The proxy choice probability of §3.4, p.16, of product `i` priced at level `ℓ` in period `t`:
`q̂ = (1/(1 + (1 + β)·ŵₜ)) · wᵗ_{iℓ}`. -/
noncomputable def qhat (ŵ : Fin T → ℝ) (β : ℝ) (t : Fin T) (i : Fin n) (ℓ : Fin L) : ℝ :=
  I.w t i ℓ / (1 + (1 + β) * ŵ t)

/-- **The law of the proxy demand `D̂ᵗᵢ(xᵢ; β)`** of §3.4, p.16:
`D̂ᵗᵢ(xᵢ; β) = Σ_{ν=1}^{Nₜ} Ŷᵗᵢ(xᵢ, ν; β)` with `Ŷᵗᵢ(xᵢ, ν; β) ∼ Bernoulli(q̂)` independent, and `Nₜ`
drawn from `arrLaw`.

**Formalization Note.** The Bernoulli parameter is `q̂` clamped to `[0, 1]` (`bern`). For a strategy
feasible to `APX(α, β)` and under `Standing`, `0 ≤ q̂ ≤ 1`, so the clamp changes nothing there; it
only makes the law defined for every strategy (§3.6 evaluates `R̂ⁱ` on all single-product
strategies). -/
noncomputable def proxyLaw (ŵ : Fin T → ℝ) (β : ℝ) (i : Fin n) (xi : Fin T → Fin L) (t : Fin T) :
    PMF ℕ :=
  (I.arrLaw t).bind (bernSum (I.qhat ŵ β t i (xi t)))

/-- The law of the proxy demand path `(D̂ᵗᵢ(xᵢ; β))_t` of product `i`, independent across periods. -/
noncomputable def proxyPathLaw (ŵ : Fin T → ℝ) (β : ℝ) (i : Fin n) (xi : Fin T → Fin L) :
    Measure (Fin T → ℕ) :=
  Measure.pi fun t => (I.proxyLaw ŵ β i xi t).toMeasure

/-- **The expected reward of product `i`**, equation (7), p.18:
`R̂ⁱ_{α,β}(xᵢ) = Σ_{t∈[T]} E[min{Ûᵗᵢ(xᵢ; β), D̂ᵗᵢ(xᵢ; β)}] · Σ_ℓ p_{iℓ} xᵗ_{iℓ}`, with
`Ûᵗᵢ(xᵢ; β) = [u¹ᵢ − Σ_{τ∈[t−1]} D̂^τᵢ(xᵢ; β)]⁺` (p.16). It does not depend on `α` (p.17). -/
noncomputable def Rhati (ŵ : Fin T → ℝ) (β : ℝ) (i : Fin n) (xi : Fin T → Fin L) : ℝ :=
  ∑ t, (∫ d, min (invLevel (I.u i) d t) (d t : ℝ) ∂(I.proxyPathLaw ŵ β i xi)) * I.p i (xi t)

/-- **The expected reward** `R̂_{α,β}(x)` of §3.4, p.16:
`R̂_{α,β}(x) = Σ_{t∈[T]} Σ_{i∈[n]} E[min{Ûᵗᵢ(xᵢ; β), D̂ᵗᵢ(xᵢ; β)}] · Σ_ℓ p_{iℓ} xᵗ_{iℓ}`,
`xᵢ = (x t i)_t` being product `i`'s prices. It does not depend on `α` (p.17). -/
noncomputable def Rhat (ŵ : Fin T → ℝ) (β : ℝ) (x : Strategy n L T) : ℝ :=
  ∑ t, ∑ i, (∫ d, min (invLevel (I.u i) d t) (d t : ℝ) ∂(I.proxyPathLaw ŵ β i (fun s => x s i))) *
    I.price x t i

/-- **Feasibility to `APX(α, β)`**, §3.4, p.16, for the guesses `Γ` and `ŵ`:
(1) `Cvar(x) ≤ B − |Γ|·f`; (2) `∆_{t−1,t}(x) = 0` for every `t ∈ [2, T]` not in `Γ`;
(3) `(1 − α)·ŵₜ ≤ wₜ(x) ≤ (1 + β)·ŵₜ` for every `t ∈ [T]`.

**Formalization Note.** `Γ` is a set of Lean periods with `1 ≤ t.val` (paper periods in `[2, T]`);
constraint (2) ranges over those periods only, where `∆` is defined. -/
def APX (Γ : Finset (Fin T)) (ŵ : Fin T → ℝ) (α β : ℝ) (x : Strategy n L T) : Prop :=
  I.Cvar x ≤ I.B - Γ.card * I.f ∧
  (∀ t : Fin T, 1 ≤ t.val → t ∉ Γ → Delta x t = 0) ∧
  ∀ t : Fin T, (1 - α) * ŵ t ≤ I.wt x t ∧ I.wt x t ≤ (1 + β) * ŵ t

end Instance

/-- The number of customers `ν < N` (paper customers `1, …, N`) for whom the indicator `Z ν` is
`true`: `Σ_{ν=1}^{N} Z_ν`. -/
def countUpTo (N : ℕ) (Z : ℕ → Bool) : ℕ := ((Finset.range N).filter (fun ν => Z ν = true)).card

/-- **The coupled demands of App. B.2, p.46**, along one realization. `N t` is the number of
arrivals in period `t`, `Y t i ν` is `Yᵗᵢ(x, ν)` (customer `ν` of period `t` is interested in product
`i`) and `Bc t i ν` is the coupling variable `Bᵗ_{i,ν}`. The true demand is
`Dᵗᵢ(x) = Σ_{ν=1}^{Nₜ} Yᵗᵢ(x, ν)`. -/
def coupledDemand (N : Fin T → ℕ) (Y : Fin T → Fin n → ℕ → Bool) (t : Fin T) (i : Fin n) : ℕ :=
  countUpTo (N t) (Y t i)

/-- The coupled proxy demand of App. B.2, p.46: `Ŷᵗᵢ(xᵢ, ν; β) = Bᵗ_{i,ν} · Yᵗᵢ(x, ν)` and
`D̂ᵗᵢ(xᵢ; β) = Σ_{ν=1}^{Nₜ} Ŷᵗᵢ(xᵢ, ν; β)`, along one realization. -/
def coupledProxyDemand (N : Fin T → ℕ) (Y Bc : Fin T → Fin n → ℕ → Bool) (t : Fin T) (i : Fin n) :
    ℕ :=
  countUpTo (N t) (fun ν => Bc t i ν && Y t i ν)

end MenuCostPricing


