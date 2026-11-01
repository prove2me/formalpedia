-- Prove2me | Definitions.Def_ProactiveUpgrade_Model
-- name    : ProactiveUpgrade_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:07.382033+00:00
-- url     : https://prove2.me/theorems/5b433347-6ad9-47ab-98f4-af62a5d13763
-- title:
--   The proactive-upgrade model: data and the operators (11), (12) and (10)
-- statement:
--   A seller holds a fixed stock of $m$ products, ordered by price $p_1<p_2<\dots<p_m$, over a selling season of $T$ periods. In each period one customer arrives with probability $\lambda$ and none with probability $1-\lambda$; an arriving customer requests product $i$ with probability $\beta_i$ and nothing with probability $\beta_0$. A customer who requests product $i<m$ may be offered a free upgrade to product $i+1$ at price $p_i$, which they accept with probability $q_i$ ($\bar q_i=1-q_i$).
--
--   The model records the data $(p,\beta,\beta_0,q,\lambda)$ and the one-period operators. For a continuation value $f=\hat v_{t+1}$ and inventory $x$, the value of not offering to a customer who requests $i$ is $f(x)$ if $x_i=0$ and $f(x-e_i)+p_i$ if $x_i>0$; the value of offering is $q_i[f(x-e_{i+1})+p_i]+\bar q_i\cdot(\text{no-offer value})$. The operator $\hat T_i$ of (11), (12) is the no-offer value when no choice exists ($i=m$, or $x_{i+1}=0$) and the larger of the two values otherwise:
--
--   $$
--   \hat T_i[\hat v_t(x)]=\begin{cases}\hat v_{t+1}(x) & x_i=0,\ x_{i+1}=0\\ \max\{\hat v_{t+1}(x),\ q_i[\hat v_{t+1}(x-e_{i+1})+p_i]+\bar q_i\hat v_{t+1}(x)\} & x_i=0,\ x_{i+1}>0\\ \hat v_{t+1}(x-e_i)+p_i & x_i>0,\ x_{i+1}=0\\ \max\{\hat v_{t+1}(x-e_i)+p_i,\ q_i[\hat v_{t+1}(x-e_{i+1})+p_i]+\bar q_i[\hat v_{t+1}(x-e_i)+p_i]\} & x_i>0,\ x_{i+1}>0.\end{cases}
--   $$
--
--   The step operator is the right side of the optimality equation (10): $\sum_{i}\lambda\beta_i\hat T_i[\cdot]+[\lambda\beta_0+(1-\lambda)]f(x)$.
--
--   **Formalization Note** Products are indexed by `Fin m` (0-based); `succIdx i h` is product $i+1$ and exists only when `i.val + 1 < m`. Inventories are `Fin m → ℕ`, and `dec x i` ($x-e_i$) is used only under the guard $x_i>0$. The acceptance probability of the last product is never read (the paper sets $q_m=0$).
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, §3, eqs. (10)–(12), pp.12–13

import Mathlib

namespace ProactiveUpgrade

/-- **The proactive-upgrade model** (Chen, Tang, Wang, Wang & Yu, *Offering Free Upgrades Even
before Stocks Run out*, SSRN 3777846, §3, pp.6–13).

There are `m` products indexed by `Fin m` (product `i` of the paper is index `i - 1`). The data are
the selling prices `p`, the request probabilities `β i` of an arriving customer (eq. (1), p.7), the
no-request probability `β0` (eq. (2), p.7), the upgrade acceptance probabilities `q i` (eq. (3), p.9)
and the arrival probability `lam` of one customer per period (p.7).

**Formalization Note** The data are kept abstract here; `mnlModel` builds them from (1)–(3) and
`IsValid` states the properties used. `q` on the last product is never used (the paper sets
`q_m = 0`). -/
structure Model (m : ℕ) where
  /-- selling prices `p₁ < ⋯ < p_m` -/
  p : Fin m → ℝ
  /-- request probabilities `βᵢ` -/
  β : Fin m → ℝ
  /-- no-request probability `β₀` -/
  β0 : ℝ
  /-- upgrade acceptance probabilities `qᵢ` -/
  q : Fin m → ℝ
  /-- arrival probability `λ` -/
  lam : ℝ

/-- The inventory vector `x − eᵢ`. **Formalization Note** On `ℕ` the subtraction is truncated, so
`dec x i` is used only under the guard `0 < x i`, as in (11), (12). -/
def dec {m : ℕ} (x : Fin m → ℕ) (i : Fin m) : Fin m → ℕ :=
  Function.update x i (x i - 1)

/-- The index of product `i + 1` (0-based `i.val + 1`), defined when `i` is not the last product. -/
def succIdx {m : ℕ} (i : Fin m) (h : i.val + 1 < m) : Fin m :=
  ⟨i.val + 1, h⟩

/-- The value of not offering an upgrade to a customer who requests product `i`, given the
continuation value `f = v̂_{t+1}`: `f(x)` if `xᵢ = 0`, and `f(x − eᵢ) + pᵢ` if `xᵢ > 0` (first
branches of the maxima in (12), and (11), p.12–13). -/
def noOfferVal {m : ℕ} (M : Model m) (f : (Fin m → ℕ) → ℝ) (x : Fin m → ℕ) (i : Fin m) : ℝ :=
  if x i = 0 then f x else f (dec x i) + M.p i

/-- The value of offering a free upgrade from `i` to `i + 1`: with probability `qᵢ` the customer
accepts and buys `i + 1` at price `pᵢ`; otherwise the no-offer outcome occurs. This is
`qᵢ[v̂_{t+1}(x − e_{i+1}) + pᵢ] + q̄ᵢ v̂_{t+1}(x)` when `xᵢ = 0` and
`qᵢ[v̂_{t+1}(x − e_{i+1}) + pᵢ] + q̄ᵢ[v̂_{t+1}(x − eᵢ) + pᵢ]` when `xᵢ > 0` (eq. (12), p.13).
Used only when `x_{i+1} > 0`. -/
def offerVal {m : ℕ} (M : Model m) (f : (Fin m → ℕ) → ℝ) (x : Fin m → ℕ) (i : Fin m)
    (h : i.val + 1 < m) : ℝ :=
  M.q i * (f (dec x (succIdx i h)) + M.p i) + (1 - M.q i) * noOfferVal M f x i

/-- The operator `T̂ᵢ[v̂ₜ(x)]` of (11) and (12) (pp.12–13), applied to the continuation value
`f = v̂_{t+1}`. For the last product (11): sell if in stock. For `i < m` (12): if `x_{i+1} = 0` no
upgrade is possible and the outcome is the no-offer value; if `x_{i+1} > 0` the seller takes the
better of not offering and offering. -/
def reqOp {m : ℕ} (M : Model m) (f : (Fin m → ℕ) → ℝ) (x : Fin m → ℕ) (i : Fin m) : ℝ :=
  if h : i.val + 1 < m then
    if x (succIdx i h) = 0 then noOfferVal M f x i
    else max (noOfferVal M f x i) (offerVal M f x i h)
  else noOfferVal M f x i

/-- The right-hand side of the optimality equation (10), p.12:
`Σ_{i∈M} λβᵢ T̂ᵢ[·] + [λβ₀ + (1 − λ)] f(x)` with `f = v̂_{t+1}`. -/
def step {m : ℕ} (M : Model m) (f : (Fin m → ℕ) → ℝ) (x : Fin m → ℕ) : ℝ :=
  ∑ i, M.lam * M.β i * reqOp M f x i + (M.lam * M.β0 + (1 - M.lam)) * f x

end ProactiveUpgrade


