-- Prove2me | Definitions.Def_SubstitutePricing_Unified_Model
-- name    : SubstitutePricing_Unified_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:54.959445+00:00
-- url     : https://prove2.me/theorems/695ef028-d3e3-4983-be39-1e77af3b0af6
-- title:
--   The MNL pricing model of §2 under unified (common-price) dynamic pricing: choice probabilities (1)–(2), optimality equation (23), a_w and Δʷπ
-- statement:
--   This file sets up the model of Dong, Kouvelis and Tian (2009, §2) for **unified dynamic pricing** (§5.1.2): a retailer sells $n$ substitutable variates of a product over a finite season with no replenishment, and in every period charges one common price to all variates.
--
--   **Data.** The variates are $\mathfrak n=\{1,\dots,n\}$. Variate $i$ has quality index $a_i\in\mathbb R$; the no-purchase option has utility $u_0\in\mathbb R$; $\mu>0$ is the scale of the Gumbel noise of the multinomial logit (MNL) model; and $\lambda\in(0,1]$ is the probability that one customer arrives in a period. Time $t$ counts the remaining periods.
--
--   **Inventory.** An inventory level is $x\in\mathbb N^n$. The in-stock set is $S(x)=\{i: x^i>0\}$, and for $i\in S(x)$, $x-e^i$ is the inventory after one unit of variate $i$ is sold.
--
--   **Choice probabilities.** For a price vector $r\in\mathbb R^n$ the MNL purchase and no-purchase probabilities are, for $i\in S(x)$,
--   $$
--   P^i(r)=\frac{\exp((a_i-r^i)/\mu)}{\sum_{j\in S(x)}\exp((a_j-r^j)/\mu)+\exp(u_0/\mu)},\qquad
--   P^0(r)=\frac{\exp(u_0/\mu)}{\sum_{j\in S(x)}\exp((a_j-r^j)/\mu)+\exp(u_0/\mu)}.
--   $$
--   Out-of-stock variates are not in the choice set.
--
--   **Optimality equation.** For a continuation value $V$ and a price vector $r$, the one-period objective of (3) is
--   $$
--   \lambda\sum_{i\in S(x)} r^iP^i(r)+\lambda\sum_{i\in S(x)}P^i(r)\,V(x-e^i)+\bigl(\lambda P^0(r)+1-\lambda\bigr)V(x).
--   $$
--   Under unified pricing every variate is charged the same price $r\ge 0$; the objective at the common price $r$ is written $\mathrm{obj}^u_V(x,r)$. The unified-pricing value function is
--   $$
--   \pi_0(x)=0,\qquad \pi_t(x)=\sup_{r\in\mathbb R_+}\mathrm{obj}^u_{\pi_{t-1}}(x,r)\quad(t\ge1),
--   $$
--   and $\Delta^i\pi_t(x)=\pi_t(x)-\pi_t(x-e^i)$ is the marginal value of a unit of variate $i$.
--
--   **Auxiliary quantities.** For marginal values $\delta\in\mathbb R^n$, the static objective of the common price is $\xi(x,\delta;r)=\sum_{i\in S(x)}\lambda P^i(r,\dots,r)\,(r-\delta_i)$; with $\delta_i=V(x)-V(x-e^i)$ this is the paper's $\xi^u_t(x,r)$ of (24). Further,
--   $$
--   a_w=\mu\ln\sum_{i\in S(x)}e^{a_i/\mu},\qquad
--   \Delta^w\pi_{t-1}(x)=\frac{\sum_{i\in S(x)}e^{a_i/\mu}\Delta^i\pi_{t-1}(x)}{\sum_{i\in S(x)}e^{a_i/\mu}},
--   $$
--   $\sigma_t(x)=\exp((a_w-\Delta^w\pi_{t-1}(x))/\mu)$, and the margin function is $h(m)=(m/\mu-1)\exp((m+u_0)/\mu)$.
--
--   These objects are shared by every statement of the mission on the optimal unified dynamic price (Proposition 1).
--
--   **Formalization Note.** The null price $r^i=\infty$ of an out-of-stock variate is modelled by removing the variate from the sums, so every price that enters is a finite real; `P x r i` is set to $0$ for $i\notin S(x)$ and never used there. $x-e^i$ uses natural-number subtraction and is only evaluated for $i\in S(x)$, where it is exact. Equation (3) is read with the no-sale term outside the sum over $i$, as the paper's (5) and (22) use it. The value function is a real `sSup` over $r\in[0,\infty)$; the theorems of the mission assert attainment, so they never rely on the value `sSup` takes on an unbounded set. $a_w$ and $\Delta^w\pi$ involve $\ln$ and a division by $\sum_{i\in S(x)}e^{a_i/\mu}$ and are meaningful only when $S(x)\neq\emptyset$, which every statement using them assumes.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), pp. 321–323, §2, (1)–(4); p. 329, §5.1.2 and Proposition 1; p. 336, (23)–(24)

import Mathlib

noncomputable section

namespace SubstitutePricing.Unified

/-- Data of the finite-horizon substitute-product pricing model in §2. -/
structure Model where
  n : ℕ
  a : Fin n → ℝ
  u0 : ℝ
  μ : ℝ
  lam : ℝ

/-- The scale and arrival probability assumptions in §2 (p. 322: `μ > 0`;
p. 321: `λ` is the probability of one arrival in a period, and the proofs divide by it). -/
structure Model.Assumptions (M : Model) : Prop where
  mu_pos : 0 < M.μ
  lam_pos : 0 < M.lam
  lam_le_one : M.lam ≤ 1

/-- Variates with positive remaining inventory, `S(x) = {i : xⁱ > 0}`. -/
def Model.S (M : Model) (x : Fin M.n → ℕ) : Finset (Fin M.n) :=
  Finset.univ.filter (fun i => 0 < x i)

/-- Remove one unit of an in-stock variate, `x − eⁱ` (used only for `i ∈ S x`). -/
def Model.sell (M : Model) (x : Fin M.n → ℕ) (i : Fin M.n) : Fin M.n → ℕ :=
  Function.update x i (x i - 1)

/-- The denominator of the MNL probabilities (1)–(2); out-of-stock variates are
removed from the choice set (the null price `rⁱ = ∞`). -/
def Model.den (M : Model) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : ℝ :=
  (∑ j ∈ M.S x, Real.exp ((M.a j - r j) / M.μ)) + Real.exp (M.u0 / M.μ)

/-- The purchase probability (1), set to zero outside the in-stock set. -/
def Model.P (M : Model) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) (i : Fin M.n) : ℝ :=
  if i ∈ M.S x then Real.exp ((M.a i - r i) / M.μ) / M.den x r else 0

/-- The no-purchase probability (2). -/
def Model.P0 (M : Model) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : ℝ :=
  Real.exp (M.u0 / M.μ) / M.den x r

/-- One-period objective of (3), with the no-sale term counted once. -/
def Model.obj (M : Model) (V : (Fin M.n → ℕ) → ℝ)
    (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : ℝ :=
  M.lam * (∑ i ∈ M.S x, r i * M.P x r i) +
  M.lam * (∑ i ∈ M.S x, M.P x r i * V (M.sell x i)) +
  (M.lam * M.P0 x r + 1 - M.lam) * V x

/-- The price vector charging the common price `r` for every variate (§5.1.2). -/
def Model.const (M : Model) (r : ℝ) : Fin M.n → ℝ :=
  fun _ => r

/-- The objective of (3) at the common price `r`. -/
def Model.objU (M : Model) (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ) (r : ℝ) : ℝ :=
  M.obj V x (M.const r)

/-- The unified-pricing value function: optimality equation (23) over `r ∈ ℝ₊`,
with the boundary condition (4) `π₀ = 0`; `t` counts remaining periods. -/
def Model.piU (M : Model) : ℕ → (Fin M.n → ℕ) → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun x => sSup ((M.objU (M.piU t) x) '' Set.Ici (0 : ℝ))

/-- Marginal value `Δⁱπₜ(x) = πₜ(x) − πₜ(x − eⁱ)` of the unified-pricing DP,
used only for an in-stock `i`. -/
def Model.deltaU (M : Model) (t : ℕ) (i : Fin M.n) (x : Fin M.n → ℕ) : ℝ :=
  M.piU t x - M.piU t (M.sell x i)

/-- The static objective of the common price `r`,
`Σ_{i∈S(x)} λ Pⁱ(r) (r − δᵢ)`, for arbitrary marginal values `δ`. -/
def Model.xiS (M : Model) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ M.S x, M.lam * M.P x (M.const r) i * (r - δ i)

/-- The paper's `ξᵘₜ(x, r)` of (24), for an arbitrary continuation value `V`
(with `V = π_{t−1}` it is (24)). -/
def Model.xiU (M : Model) (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ M.S x, M.lam * M.P x (M.const r) i * (r - (V x - V (M.sell x i)))

/-- `Σ_{i∈S(x)} exp(aᵢ/μ)`. -/
def Model.wsum (M : Model) (x : Fin M.n → ℕ) : ℝ :=
  ∑ i ∈ M.S x, Real.exp (M.a i / M.μ)

/-- `a_w = μ ln Σ_{i∈S(x)} exp(aᵢ/μ)` (Proposition 1). -/
def Model.aW (M : Model) (x : Fin M.n → ℕ) : ℝ :=
  M.μ * Real.log (M.wsum x)

/-- The `exp(aᵢ/μ)`-weighted average of `δ` over `S(x)`. -/
def Model.wavg (M : Model) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) : ℝ :=
  (∑ i ∈ M.S x, Real.exp (M.a i / M.μ) * δ i) / M.wsum x

/-- `Δʷπ_{t−1}(x)` of Proposition 1, computed from the unified value function. -/
def Model.deltaW (M : Model) (t : ℕ) (x : Fin M.n → ℕ) : ℝ :=
  M.wavg x (fun i => M.deltaU (t - 1) i x)

/-- The right side `exp((a_w − Δʷπ_{t−1}(x))/μ)` of the margin equation. -/
def Model.sigmaU (M : Model) (t : ℕ) (x : Fin M.n → ℕ) : ℝ :=
  Real.exp ((M.aW x - M.deltaW t x) / M.μ)

/-- The left side `(m/μ − 1) exp((m + u₀)/μ)` of the margin equation. -/
def Model.marginLHS (M : Model) (m : ℝ) : ℝ :=
  (m / M.μ - 1) * Real.exp ((m + M.u0) / M.μ)

end SubstitutePricing.Unified


