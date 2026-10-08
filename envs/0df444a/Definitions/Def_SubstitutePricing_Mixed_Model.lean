-- Prove2me | Definitions.Def_SubstitutePricing_Mixed_Model
-- name    : SubstitutePricing_Mixed_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:48.36797+00:00
-- url     : https://prove2.me/theorems/5c177945-f246-451e-8012-64fa139d2c62
-- title:
--   The MNL dynamic pricing model of §2 with a fixed-price subset (§5.1.3): choice probabilities (1)–(2), the optimality equation (3)–(4) under mixed pricing, and the objects of Proposition 2
-- statement:
--   A retailer sells $n$ substitutable variates $i \in \mathfrak n = \{1,\dots,n\}$ over a finite season without replenishment. Time counts down: $t$ is the number of remaining periods. Variate $i$ has quality index $a_i$, the no-purchase option has utility $u_0$, the multinomial logit scale is $\mu > 0$, and in each period one customer arrives with probability $0 < \lambda \le 1$. Inventory is a vector $x \in \mathbb N^n$, and $S(x) = \{i : x^i > 0\}$ is the in-stock set.
--
--   **Mixed pricing** (§5.1.3). The variates are split into the dynamic-pricing set $\mathfrak n_1$ and the fixed-pricing set $\mathfrak n_2 = \mathfrak n \setminus \mathfrak n_1$; each $j \in \mathfrak n_2$ is sold at a fixed price $r^j \ge 0$. Write $S_1(x) = S(x) \cap \mathfrak n_1$ and $S_2(x) = S(x) \cap \mathfrak n_2$. For a vector $r$ of dynamic prices, the full price vector uses $r^i$ on $\mathfrak n_1$ and the fixed prices on $\mathfrak n_2$, and the choice probabilities (1)–(2) are, for $i \in S(x)$,
--
--   $$
--   P^i(r) = \frac{e^{(a_i - r^i)/\mu}}{\sum_{j \in S(x)} e^{(a_j - r^j)/\mu} + e^{u_0/\mu}}, \qquad P^0(r) = \frac{e^{u_0/\mu}}{\sum_{j \in S(x)} e^{(a_j - r^j)/\mu} + e^{u_0/\mu}}.
--   $$
--
--   The mixed-pricing value function is $\pi_0 \equiv 0$ and
--
--   $$
--   \pi_t(x) = \sup_{r \in \mathbb R^{n_1}_+} \Big\{ \lambda \sum_{i\in S(x)} r^i P^i(r) + \lambda \sum_{i \in S(x)} P^i(r)\, \pi_{t-1}(x - e^i) + \big(\lambda P^0(r) + 1 - \lambda\big)\, \pi_{t-1}(x) \Big\},
--   $$
--
--   with marginal values $\Delta^i\pi_t(x) = \pi_t(x) - \pi_t(x - e^i)$. The file also defines the price objective $\xi^m$ of (29) (for an arbitrary continuation value, or for arbitrary marginal values $\delta_i$), the quantities $\theta_j = e^{(a_j - r^j - u_0)/\mu}$ and $\Theta = \sum_{j \in S_2(x)} \theta_j$, $v_j = r^j - \Delta^j\pi_{t-1}(x)$ and $u_j = a_j - r^j$, both sides of the margin equation (15) (with the $j = 0$ term, $v_0 = 0$, written out), the candidate prices $\Delta^i\pi_{t-1}(x) + m$ on $S_1(x)$, and the objective (31) as a function of the dynamic choice probabilities after substituting (30).
--
--   These are the objects in which Proposition 2 and the steps of its proof are stated.
--
--   **Formalization Note** An out-of-stock variate carries the paper's null price $r^i = \infty$; here it is removed from the choice set (the sums run over $S(x)$), so every in-stock price is a finite real. The no-sale term of (3) is counted once, as (5) and the proofs use it, despite the printed bracket placement. The price set of the supremum is $\{r : r^i \ge 0 \ \forall i \in \mathfrak n_1\}$; coordinates outside $\mathfrak n_1$ are ignored. The fixed prices are assumed nonnegative (the allowable price set of p. 322). $x - e^i$ uses natural-number subtraction and is only used for in-stock $i$, where it is exact. Off $S(x)$ the probabilities and off $S_1(x)$ the candidate prices are set to $0$; these values are never used. In the probability domain of (31) the coordinates outside $S_1(x)$ are pinned to $0$.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), pp. 321–323, §2, (1)–(4); p. 329, §5.1.3, Proposition 2 and (15); p. 337, App. A, proof of Proposition 2, (29)–(31)

import Mathlib

noncomputable section

namespace SubstitutePricing.Mixed

/-- Data of the substitute-product pricing model of §2, with the mixed pricing data of §5.1.3:
the dynamic-pricing variates `dyn` (the paper's 𝔫₁) and the fixed prices `rfix j` of the
variates `j ∉ dyn` (the paper's 𝔫₂ and `r^j`; values of `rfix` on `dyn` are never used). -/
structure Model where
  n : ℕ
  a : Fin n → ℝ
  u0 : ℝ
  μ : ℝ
  lam : ℝ
  dyn : Finset (Fin n)
  rfix : Fin n → ℝ

/-- Standing assumptions: `μ > 0` (p. 322), `0 < λ ≤ 1` (λ is a probability, p. 321), and the
fixed prices are allowable, i.e. nonnegative (p. 322). -/
structure Model.Assumptions (M : Model) : Prop where
  mu_pos : 0 < M.μ
  lam_pos : 0 < M.lam
  lam_le_one : M.lam ≤ 1
  rfix_nonneg : ∀ j, j ∉ M.dyn → 0 ≤ M.rfix j

/-- The in-stock set `S(x) = {i : xⁱ > 0}` (p. 322). -/
def Model.S (M : Model) (x : Fin M.n → ℕ) : Finset (Fin M.n) :=
  Finset.univ.filter (fun i => 0 < x i)

/-- In-stock dynamic-pricing variates `S₁(x)` (p. 329). -/
def Model.S1 (M : Model) (x : Fin M.n → ℕ) : Finset (Fin M.n) :=
  M.S x ∩ M.dyn

/-- In-stock fixed-pricing variates `S₂(x)` (p. 329). -/
def Model.S2 (M : Model) (x : Fin M.n → ℕ) : Finset (Fin M.n) :=
  M.S x \ M.dyn

/-- `x − eⁱ`: remove one unit of variate `i` (used only for in-stock `i`, where the
natural-number subtraction is exact). -/
def Model.sell (M : Model) (x : Fin M.n → ℕ) (i : Fin M.n) : Fin M.n → ℕ :=
  Function.update x i (x i - 1)

/-- The denominator of the MNL probabilities (1)–(2); out-of-stock variates (null price) are
removed from the choice set. -/
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

/-- The full price vector: the decision `r` on the dynamic variates, the fixed prices elsewhere. -/
def Model.mix (M : Model) (r : Fin M.n → ℝ) : Fin M.n → ℝ :=
  fun i => if i ∈ M.dyn then r i else M.rfix i

/-- The objective of (3) under mixed pricing: only the coordinates in `dyn` are decisions. -/
def Model.objM (M : Model) (V : (Fin M.n → ℕ) → ℝ)
    (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : ℝ :=
  M.obj V x (M.mix r)

/-- Allowable dynamic prices: `R^{n₁}_+` of (29); coordinates off `dyn` are ignored. -/
def Model.feasibleM (M : Model) : Set (Fin M.n → ℝ) :=
  {r | ∀ i ∈ M.dyn, 0 ≤ r i}

/-- The mixed-pricing value function, (3)–(4) with the prices of 𝔫₂ fixed. -/
def Model.piM (M : Model) : ℕ → (Fin M.n → ℕ) → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun x => sSup ((M.objM (M.piM t) x) '' M.feasibleM)

/-- Marginal value `Δⁱπₜ(x) = πₜ(x) − πₜ(x − eⁱ)` of the mixed-pricing DP. -/
def Model.deltaM (M : Model) (t : ℕ) (i : Fin M.n) (x : Fin M.n → ℕ) : ℝ :=
  M.piM t x - M.piM t (M.sell x i)

/-- The price objective with marginal values `δ`: the bracket of (29), with `δ i` for `Δⁱπₜ₋₁`. -/
def Model.xiD (M : Model) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (r : Fin M.n → ℝ) : ℝ :=
  (∑ i ∈ M.S1 x, M.lam * M.P x (M.mix r) i * (r i - δ i)) +
  ∑ j ∈ M.S2 x, M.lam * M.P x (M.mix r) j * (M.rfix j - δ j)

/-- The price objective of (29) for an arbitrary continuation value `V` (`V = πₜ₋₁`). -/
def Model.xiM (M : Model) (V : (Fin M.n → ℕ) → ℝ)
    (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : ℝ :=
  M.xiD x (fun i => V x - V (M.sell x i)) r

/-- `θⱼ = exp((aⱼ − rʲ − u₀)/μ)` (p. 337). -/
def Model.θ (M : Model) (j : Fin M.n) : ℝ :=
  Real.exp ((M.a j - M.rfix j - M.u0) / M.μ)

/-- `Θ = Σ_{j ∈ S₂(x)} θⱼ` (p. 337). -/
def Model.Θ (M : Model) (x : Fin M.n → ℕ) : ℝ :=
  ∑ j ∈ M.S2 x, M.θ j

/-- `vⱼ = rʲ − Δʲπₜ₋₁(x)` for `j ∈ S₂(x)` (Proposition 2). -/
def Model.v (M : Model) (t : ℕ) (j : Fin M.n) (x : Fin M.n → ℕ) : ℝ :=
  M.rfix j - M.deltaM (t - 1) j x

/-- `uⱼ = aⱼ − rʲ` for `j ∈ S₂(x)` (Proposition 2). -/
def Model.uf (M : Model) (j : Fin M.n) : ℝ :=
  M.a j - M.rfix j

/-- Left side of (15); the `j = 0` term (`v₀ = 0`, utility `u₀`) is written out. -/
def Model.lhs15 (M : Model) (t : ℕ) (x : Fin M.n → ℕ) (m : ℝ) : ℝ :=
  (m / M.μ - 1) * Real.exp ((m + M.u0) / M.μ) +
  ∑ j ∈ M.S2 x, ((m - M.v t j x) / M.μ - 1) * Real.exp ((m + M.uf j) / M.μ)

/-- Right side of (15). -/
def Model.rhs15 (M : Model) (t : ℕ) (x : Fin M.n → ℕ) : ℝ :=
  ∑ i ∈ M.S1 x, Real.exp ((M.a i - M.deltaM (t - 1) i x) / M.μ)

/-- Candidate dynamic prices of Proposition 2, `Δⁱπₜ₋₁(x) + m` on `S₁(x)`; other coordinates are
set to zero (off `dyn` they are ignored by `mix`, on `dyn \ S₁(x)` the variate is out of stock). -/
def Model.rstarM (M : Model) (t : ℕ) (x : Fin M.n → ℕ) (m : ℝ) : Fin M.n → ℝ :=
  fun i => if i ∈ M.S1 x then M.deltaM (t - 1) i x + m else 0

/-- `P⁰` as a function of the dynamic choice probabilities `p`, by (30). -/
def Model.P0of (M : Model) (x : Fin M.n → ℕ) (p : Fin M.n → ℝ) : ℝ :=
  (1 - ∑ i ∈ M.S1 x, p i) / (1 + M.Θ x)

/-- The objective (31) in the dynamic choice probabilities `p` (marginal values `δ`), with `P⁰`
and `Pʲ = θⱼ P⁰`, `j ∈ S₂(x)`, substituted from (30). -/
def Model.xiProb (M : Model) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (p : Fin M.n → ℝ) : ℝ :=
  (∑ i ∈ M.S1 x, M.lam * p i *
    (M.a i - M.u0 - M.μ * Real.log (p i) + M.μ * Real.log (M.P0of x p) - δ i)) +
  ∑ j ∈ M.S2 x, M.lam * (M.θ j * M.P0of x p) * (M.rfix j - δ j)

/-- Open domain of dynamic choice probabilities on `S₁(x)`; the other coordinates are pinned to 0. -/
def Model.probDomain (M : Model) (x : Fin M.n → ℕ) : Set (Fin M.n → ℝ) :=
  {p | (∀ i ∈ M.S1 x, 0 < p i) ∧ (∑ i ∈ M.S1 x, p i) < 1 ∧ ∀ i, i ∉ M.S1 x → p i = 0}

end SubstitutePricing.Mixed


