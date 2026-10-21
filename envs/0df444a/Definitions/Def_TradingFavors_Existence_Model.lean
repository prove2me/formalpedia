-- Prove2me | Definitions.Def_TradingFavors_Existence_Model
-- name    : TradingFavors_Existence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:37.267801+00:00
-- url     : https://prove2.me/theorems/264cb896-8e9c-4748-b6a3-79440884e6a5
-- title:
--   §3–§4.2, pp. 6–16 — two-firm trading-favors game: uniformized payoffs πᵢ(·|σ), condition (4), TFE, σᴸ, Bᵢ, α₁, α, β, β₂, ρ̂ᵢ, πᴺᶜᵢ, (15), first-passage Γ
-- statement:
--   This module sets up the trading-favors game of Hu and Caldentey between two service firms that share capacity without monetary transfers.
--
--   **Model.** Firm $i\in\{1,2\}$ receives its own (type-$i$) customers according to a Poisson process with rate $\lambda_i>0$ and serves one customer at a time, with exponential service times of rate $\mu_i>0$; it has no queue. Let $x_i\in\{0,1\}$ be firm $i$'s state (idle or busy) and let $k=T_2-T_1\in\mathbb Z$ be the net number of favors firm 1 has done for firm 2. A type-$i$ customer who finds firm $i$ idle is served by it and earns it $p_i-l_i$, where $l_i$ is the service cost. A type-$i$ customer who finds firm $i$ busy and firm $j=3-i$ idle is transferred to $j$ if $j$ is willing; firm $i$ then earns $q_i$ and firm $j$ pays the service cost $l_j$. The transfer of a type-1 customer moves $k$ to $k-1$, that of a type-2 customer moves $k$ to $k+1$. Payoffs are discounted at rate $\gamma>0$. The standing assumptions are
--   $$
--   \lambda_i,\mu_i,\gamma>0,\qquad p_i,q_i,l_i\ge0,\qquad q_i<p_i\qquad(i=1,2).
--   $$
--
--   **Strategies.** A trading-favors strategy profile is $\sigma=(\sigma_1,\sigma_2)$ with $\sigma_i:\mathbb Z\to\{0,1\}$; $\sigma_i(k)=0$ means that firm $i$ accepts a transfer when the favor balance is $k$. The state $(x_1,x_2,k)$ is then a continuous-time Markov chain. The no-collaboration profile $\sigma^{NC}$ has $\sigma_1\equiv\sigma_2\equiv1$. For an integer $L\ge0$, the profile $\sigma^L$ (Definition 3) has firm 1 accept exactly when $0\le k\le L-1$ and firm 2 accept exactly when $1\le k\le L$; its core region is $\{0,1,\dots,L\}$, and $\sigma^0=\sigma^{NC}$.
--
--   **Payoffs.** Firm $i$'s expected discounted payoff $\pi_i(x_i,x_j,k\mid\sigma)$, with firm $i$'s own state written first, is defined from the uniformized chain. With $\Lambda=\lambda_1+\lambda_2+\mu_1+\mu_2$, which bounds every out-rate, let $P$ be the one-step operator that moves along each transition with probability (rate)$/\Lambda$ and stays put with the remaining probability. Then
--   $$
--   \pi_i(\cdot\mid\sigma)=\sum_{n\ge0}\Big(\frac{\Lambda}{\Lambda+\gamma}\Big)^{n}P^{n}\Big(\frac{\mathcal R_i}{\Lambda+\gamma}\Big),
--   $$
--   where $\mathcal R_i$ is the reward rate of (5): $\mathcal R_1=\lambda_1(1-x_1)(p_1-l_1)+\lambda_1x_1(1-x_2)(1-\sigma_2(k))q_1-\lambda_2x_2(1-x_1)(1-\sigma_1(k))l_1$, and symmetrically for firm 2. The jump epochs of the uniformized chain form a Poisson process of rate $\Lambda$, so the $n$-th epoch has discount factor $(\Lambda/(\Lambda+\gamma))^n$ in expectation, and this sum is the discounted payoff (1). Adding $(\Lambda-\text{out-rate})\,\pi_i$ to both sides of the balance equations (5) shows that it is the same $\pi_i$ as there. Write $v_i(k\mid\sigma)=\pi_i(1,1,k\mid\sigma)$.
--
--   **Equilibrium.** Condition (4) for firm $i$ at $k$ reads
--   $$
--   \sigma_i(k)=0\iff \pi_i\big(1,1,k-(-1)^i\mid\sigma\big)-l_i>\pi_i(0,1,k\mid\sigma).
--   $$
--   A trading-favors equilibrium (TFE, Definition 1) is a profile for which (4) holds for both firms at every $k\in\mathbb Z$. The module also defines (4) on a set $K$ of balances and the predicate "$\sigma^L$ is a TFE on its core region": (4) for both firms at every $k\in\{0,\dots,L\}$.
--
--   **Constants.** $B_i(k\mid\sigma)$ is the $4\times4$ matrix of Lemma 2, with diagonal entries $\mathcal Q_i(0,0)=\gamma+\lambda_i+\lambda_j$, $\mathcal Q_i(1,0)=\gamma+\mu_i+\lambda_i(1-\sigma_j(k))+\lambda_j$, $\mathcal Q_i(0,1)=\gamma+\mu_j+\lambda_j(1-\sigma_i(k))+\lambda_i$, $\mathcal Q_i(1,1)=\gamma+\mu_i+\mu_j$. The coefficients of Lemma 3 are matrix-inverse entries: $\alpha_1=\lambda_2[B_1^{-1}]_{4,3}$ when $(\sigma_1(k),\sigma_2(k))=(0,1)$, $\alpha=\lambda_2[B_1^{-1}]_{4,3}$ and $\beta=\lambda_1[B_1^{-1}]_{4,2}$ when $(0,0)$, and $\beta_2=\lambda_1[B_1^{-1}]_{4,2}$ when $(1,0)$. Further, $\hat\rho_i=\lambda_i/(\lambda_i+\mu_i+\gamma)$ (Definition 4), the no-collaboration payoffs $\pi_i^{NC}(0)$, $\pi_i^{NC}(1)$ of (7), the intercepts $\underline r_1,r_1,\overline r_1$ of (11)–(13) and their firm-2 counterparts $\underline r_2,r_2,\overline r_2$ from the proof of Lemma 3, and condition (15):
--   $$
--   \beta_2q_1>\hat\rho_1(p_1-l_1)+l_1\quad\text{and}\quad\alpha_1q_2>\hat\rho_2(p_2-l_2)+l_2 .
--   $$
--   Finally, the positive-rate one-step transition relation of the chain, and the first-passage discount factor $\Gamma=E[e^{-\gamma\tau}]$ from a state $s$ to a target $t$, computed on the uniformized chain killed at $t$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The state is `(x₁, x₂, k)` in physical order, `Fin 2 × Fin 2 × ℤ`; `pi1 θ σ x1 x2 k` and `pi2 θ σ x2 x1 k` take their arguments in the paper's order (own state first), so `pi2 θ σ 0 1 k` is the payoff at $x_2=0$, $x_1=1$. Strategy values are `Fin 2` with `0` = accept; `fr` casts them to the reals $0,1$. The payoff is the explicit discounted series, not "a solution of (5)"; (5)/(6) is Lemma 2. The series is summable since $P$ is a Markov operator and $\Lambda/(\Lambda+\gamma)<1$ (for bounded rewards). The matrix indices are 0-based in Lean: the paper's $(4,3)$ is `3 2` and $(4,2)$ is `3 1`. `B2 θ s1 s2` is firm 2's matrix in its own coordinates $(x_2,x_1)$, with physical arguments $s_1=\sigma_1(k)$, $s_2=\sigma_2(k)$. The positivity of $\lambda_i,\mu_i$ is added to the paper's standing assumptions (they are the rates of a Poisson process and of an exponential law).
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), pp. 6–16 (PDF 6–16), §3, §4–4.2, eqs. (1)–(7), (11)–(13), (15), Definitions 1, 3, 4, Lemmas 2–3; proof of Lemma 3 p. A3 (PDF 33); Lemma A.3 p. A5 (PDF 35)

import Mathlib

namespace TradingFavors.Existence

open Matrix

/-- The primitive data of the two-firm capacity-sharing game (Hu & Caldentey, §3):
arrival rates `lam1 lam2` (λ₁, λ₂), service rates `mu1 mu2` (µ₁, µ₂), discount rate `gam` (γ),
revenue per own customer `p1 p2`, revenue per transferred-out customer `q1 q2`, and service cost
per served customer `l1 l2`. The per-rejection cost `cᵢ` is normalized to `0` as on p. 7. -/
structure Params where
  lam1 : ℝ
  lam2 : ℝ
  mu1 : ℝ
  mu2 : ℝ
  gam : ℝ
  p1 : ℝ
  p2 : ℝ
  q1 : ℝ
  q2 : ℝ
  l1 : ℝ
  l2 : ℝ

/-- Standing assumptions (pp. 6–7): positive rates (positivity of `λᵢ`, `µᵢ` is added: they are
the rates of a Poisson process and of an exponential law), `γ > 0`, nonnegative `pᵢ, qᵢ, lᵢ`,
and `qᵢ < pᵢ`. -/
def Params.Standing (θ : Params) : Prop :=
  0 < θ.lam1 ∧ 0 < θ.lam2 ∧ 0 < θ.mu1 ∧ 0 < θ.mu2 ∧ 0 < θ.gam ∧
  0 ≤ θ.p1 ∧ 0 ≤ θ.p2 ∧ 0 ≤ θ.q1 ∧ 0 ≤ θ.q2 ∧ 0 ≤ θ.l1 ∧ 0 ≤ θ.l2 ∧
  θ.q1 < θ.p1 ∧ θ.q2 < θ.p2

/-- A trading-favors strategy profile σ = (σ₁, σ₂), σᵢ : ℤ → {0,1}:
`s1 k = 0` means firm 1 accepts a type-2 transfer when the favor balance is `k` ("open"),
`s1 k = 1` means it refuses. Likewise `s2` for firm 2. -/
structure Profile where
  s1 : ℤ → Fin 2
  s2 : ℤ → Fin 2

/-- System state `(x₁, x₂, k)` in physical order: `x₁, x₂ ∈ {0 = idle, 1 = busy}` and
`k = T₂ − T₁` the net number of favors done by firm 1. -/
abbrev State := Fin 2 × Fin 2 × ℤ

/-- `b ∈ {0,1}` as the real number `0` or `1`. -/
def fr (b : Fin 2) : ℝ := ((b : ℕ) : ℝ)

/-- Total rate at which the chain leaves state `s` (`𝒬ᵢ − γ` in (5); the same for both firms),
physical coordinates. -/
def outRate (θ : Params) (σ : Profile) (s : State) : ℝ :=
  let x1 := fr s.1
  let x2 := fr s.2.1
  let k := s.2.2
  θ.mu1 * x1 + θ.mu2 * x2
    + θ.lam1 * (1 - x1 + x1 * (1 - x2) * (1 - fr (σ.s2 k)))
    + θ.lam2 * (1 - x2 + x2 * (1 - x1) * (1 - fr (σ.s1 k)))

/-- Uniformization rate Λ = λ₁ + λ₂ + µ₁ + µ₂, an upper bound on every out-rate. -/
def Lam (θ : Params) : ℝ := θ.lam1 + θ.lam2 + θ.mu1 + θ.mu2

/-- One step of the uniformized chain acting on a function `f`: every transition of Figure 2
(p. 10) with probability rate/Λ, and a self-loop with the remaining probability.
A type-1 transfer is `(1,0,k) → (1,1,k−1)`, a type-2 transfer is `(0,1,k) → (1,1,k+1)`. -/
noncomputable def step (θ : Params) (σ : Profile) (f : State → ℝ) (s : State) : ℝ :=
  let x1 := fr s.1
  let x2 := fr s.2.1
  let k := s.2.2
  (θ.lam1 * (1 - x1) * f (1, s.2.1, k)
    + θ.lam1 * x1 * (1 - x2) * (1 - fr (σ.s2 k)) * f (1, 1, k - 1)
    + θ.lam2 * (1 - x2) * f (s.1, 1, k)
    + θ.lam2 * x2 * (1 - x1) * (1 - fr (σ.s1 k)) * f (1, 1, k + 1)
    + θ.mu1 * x1 * f (0, s.2.1, k)
    + θ.mu2 * x2 * f (s.1, 0, k)
    + (Lam θ - outRate θ σ s) * f s) / Lam θ

/-- Firm 1's reward rate `ℛ₁` of (5), physical coordinates:
λ₁(1−x₁)(p₁−l₁) + λ₁x₁(1−x₂)(1−σ₂(k))q₁ − λ₂x₂(1−x₁)(1−σ₁(k))l₁. -/
def R1 (θ : Params) (σ : Profile) (s : State) : ℝ :=
  let x1 := fr s.1
  let x2 := fr s.2.1
  let k := s.2.2
  θ.lam1 * (1 - x1) * (θ.p1 - θ.l1)
    + θ.lam1 * x1 * (1 - x2) * (1 - fr (σ.s2 k)) * θ.q1
    - θ.lam2 * x2 * (1 - x1) * (1 - fr (σ.s1 k)) * θ.l1

/-- Firm 2's reward rate `ℛ₂` of (5), physical coordinates:
λ₂(1−x₂)(p₂−l₂) + λ₂x₂(1−x₁)(1−σ₁(k))q₂ − λ₁x₁(1−x₂)(1−σ₂(k))l₂. -/
def R2 (θ : Params) (σ : Profile) (s : State) : ℝ :=
  let x1 := fr s.1
  let x2 := fr s.2.1
  let k := s.2.2
  θ.lam2 * (1 - x2) * (θ.p2 - θ.l2)
    + θ.lam2 * x2 * (1 - x1) * (1 - fr (σ.s1 k)) * θ.q2
    - θ.lam1 * x1 * (1 - x2) * (1 - fr (σ.s2 k)) * θ.l2

/-- Firm 1's expected discounted payoff (1) from state `s`, as the expected discounted reward of
the uniformized chain: `∑ₙ (Λ/(Λ+γ))ⁿ (Pⁿ (ℛ₁/(Λ+γ)))(s)`. -/
noncomputable def pay1 (θ : Params) (σ : Profile) (s : State) : ℝ :=
  ∑' n : ℕ, (Lam θ / (Lam θ + θ.gam)) ^ n *
    ((step θ σ)^[n] (fun u => R1 θ σ u / (Lam θ + θ.gam))) s

/-- Firm 2's expected discounted payoff (1) from state `s` (physical coordinates). -/
noncomputable def pay2 (θ : Params) (σ : Profile) (s : State) : ℝ :=
  ∑' n : ℕ, (Lam θ / (Lam θ + θ.gam)) ^ n *
    ((step θ σ)^[n] (fun u => R2 θ σ u / (Lam θ + θ.gam))) s

/-- The paper's `π₁(x₁, x₂, k | σ)` (firm 1's own state first). -/
noncomputable def pi1 (θ : Params) (σ : Profile) (x1 x2 : Fin 2) (k : ℤ) : ℝ :=
  pay1 θ σ (x1, x2, k)

/-- The paper's `π₂(x₂, x₁, k | σ)`: firm 2's OWN state comes first, so `pi2 θ σ 0 1 k` is the
payoff at `x₂ = 0`, `x₁ = 1`. -/
noncomputable def pi2 (θ : Params) (σ : Profile) (x2 x1 : Fin 2) (k : ℤ) : ℝ :=
  pay2 θ σ (x1, x2, k)

/-- `v₁(k|σ) ≡ π₁(1,1,k|σ)`. -/
noncomputable def v1 (θ : Params) (σ : Profile) (k : ℤ) : ℝ := pi1 θ σ 1 1 k

/-- `v₂(k|σ) ≡ π₂(1,1,k|σ)`. -/
noncomputable def v2 (θ : Params) (σ : Profile) (k : ℤ) : ℝ := pi2 θ σ 1 1 k

/-- Firm 1's reward vector `R₁(k|σ)` of Lemma 2, ordered `(0,0), (1,0), (0,1), (1,1)` in firm 1's
coordinates `(x₁, x₂)`. -/
def R1vec (θ : Params) (σ : Profile) (k : ℤ) : Fin 4 → ℝ :=
  ![R1 θ σ (0, 0, k), R1 θ σ (1, 0, k), R1 θ σ (0, 1, k), R1 θ σ (1, 1, k)]

/-- Firm 2's reward vector `R₂(k|σ)` of Lemma 2, ordered `(0,0), (1,0), (0,1), (1,1)` in firm 2's
coordinates `(x₂, x₁)`. -/
def R2vec (θ : Params) (σ : Profile) (k : ℤ) : Fin 4 → ℝ :=
  ![R2 θ σ (0, 0, k), R2 θ σ (0, 1, k), R2 θ σ (1, 0, k), R2 θ σ (1, 1, k)]

/-- Condition (4) for firm 1 at `k`:
σ₁(k) = 0 ⇔ π₁(1,1,k+1|σ) − l₁ > π₁(0,1,k|σ). -/
def Cond4Firm1 (θ : Params) (σ : Profile) (k : ℤ) : Prop :=
  σ.s1 k = 0 ↔ pi1 θ σ 1 1 (k + 1) - θ.l1 > pi1 θ σ 0 1 k

/-- Condition (4) for firm 2 at `k`:
σ₂(k) = 0 ⇔ π₂(1,1,k−1|σ) − l₂ > π₂(0,1,k|σ). -/
def Cond4Firm2 (θ : Params) (σ : Profile) (k : ℤ) : Prop :=
  σ.s2 k = 0 ↔ pi2 θ σ 1 1 (k - 1) - θ.l2 > pi2 θ σ 0 1 k

/-- Definition 1: σ is a Trading-Favors Equilibrium if (4) holds for both firms at every `k ∈ ℤ`. -/
def IsTFE (θ : Params) (σ : Profile) : Prop :=
  ∀ k : ℤ, Cond4Firm1 θ σ k ∧ Cond4Firm2 θ σ k

/-- Condition (4) for both firms at every `k ∈ K`. -/
def IsTFEOn (θ : Params) (σ : Profile) (K : Set ℤ) : Prop :=
  ∀ k ∈ K, Cond4Firm1 θ σ k ∧ Cond4Firm2 θ σ k

/-- The no-collaboration profile σᴺᶜ: both firms always refuse. -/
def sigmaNC : Profile := ⟨fun _ => 1, fun _ => 1⟩

/-- Definition 3: σᴸ, the bounded-strategy profile with K̲₁ = 0, K̄₁ = L − 1, K̲₂ = 1, K̄₂ = L:
firm 1 accepts iff `0 ≤ k ≤ L − 1`, firm 2 accepts iff `1 ≤ k ≤ L`. -/
def sigmaL (L : ℕ) : Profile :=
  ⟨fun k => if 0 ≤ k ∧ k ≤ (L : ℤ) - 1 then 0 else 1,
   fun k => if 1 ≤ k ∧ k ≤ (L : ℤ) then 0 else 1⟩

/-- σᴸ is a TFE on its core region `{0, …, L}`: condition (4) for both firms at every
`k ∈ {0,…,L}`. -/
def IsCoreTFE (θ : Params) (L : ℕ) : Prop :=
  IsTFEOn θ (sigmaL L) (Set.Icc 0 (L : ℤ))

/-- The matrix `Bᵢ(k|σ)` of Lemma 2 in firm i's coordinates, rows/columns ordered
`(0,0), (1,0), (0,1), (1,1)` for `(xᵢ, xⱼ)`; `si`, `sj` are `σᵢ(k)`, `σⱼ(k)` as reals. -/
def Bmat (lami lamj mui muj gam si sj : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![gam + lami + lamj, -lami, -lamj, 0;
     -mui, gam + mui + lami * (1 - sj) + lamj, 0, -lamj;
     -muj, 0, gam + muj + lamj * (1 - si) + lami, -lami;
     0, -muj, -mui, gam + mui + muj]

/-- Firm 1's matrix `B₁` with `σ₁(k) = s1`, `σ₂(k) = s2`. -/
def B1 (θ : Params) (s1 s2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Bmat θ.lam1 θ.lam2 θ.mu1 θ.mu2 θ.gam s1 s2

/-- Firm 2's matrix `B₂` in its own coordinates, with `σ₁(k) = s1`, `σ₂(k) = s2`. -/
def B2 (θ : Params) (s1 s2 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Bmat θ.lam2 θ.lam1 θ.mu2 θ.mu1 θ.gam s2 s1

/-- α₁: the (4,3) entry of `λ₂ B₁⁻¹` when `σ₁(k) = 0, σ₂(k) = 1` (case (8)). -/
noncomputable def alpha1 (θ : Params) : ℝ := θ.lam2 * (B1 θ 0 1)⁻¹ 3 2

/-- α: the (4,3) entry of `λ₂ B₁⁻¹` when `σ₁(k) = σ₂(k) = 0` (case (9)). -/
noncomputable def alpha (θ : Params) : ℝ := θ.lam2 * (B1 θ 0 0)⁻¹ 3 2

/-- β: the (4,2) entry of `λ₁ B₁⁻¹` when `σ₁(k) = σ₂(k) = 0` (case (9)). -/
noncomputable def beta (θ : Params) : ℝ := θ.lam1 * (B1 θ 0 0)⁻¹ 3 1

/-- β₂: the (4,2) entry of `λ₁ B₁⁻¹` when `σ₁(k) = 1, σ₂(k) = 0` (case (10)). -/
noncomputable def beta2 (θ : Params) : ℝ := θ.lam1 * (B1 θ 1 0)⁻¹ 3 1

/-- Definition 4: ρ̂₁ = λ₁/(λ₁ + µ₁ + γ). -/
noncomputable def rhoHat1 (θ : Params) : ℝ := θ.lam1 / (θ.lam1 + θ.mu1 + θ.gam)

/-- Definition 4: ρ̂₂ = λ₂/(λ₂ + µ₂ + γ). -/
noncomputable def rhoHat2 (θ : Params) : ℝ := θ.lam2 / (θ.lam2 + θ.mu2 + θ.gam)

/-- (7): πᴺᶜ₁(0) = (µ₁+γ)λ₁(p₁−l₁)/((λ₁+µ₁+γ)γ), πᴺᶜ₁(1) = λ₁µ₁(p₁−l₁)/((λ₁+µ₁+γ)γ). -/
noncomputable def piNC1 (θ : Params) (x : Fin 2) : ℝ :=
  if x = 0 then (θ.mu1 + θ.gam) * θ.lam1 * (θ.p1 - θ.l1) / ((θ.lam1 + θ.mu1 + θ.gam) * θ.gam)
  else θ.lam1 * θ.mu1 * (θ.p1 - θ.l1) / ((θ.lam1 + θ.mu1 + θ.gam) * θ.gam)

/-- (7) for firm 2: πᴺᶜ₂(0), πᴺᶜ₂(1). -/
noncomputable def piNC2 (θ : Params) (x : Fin 2) : ℝ :=
  if x = 0 then (θ.mu2 + θ.gam) * θ.lam2 * (θ.p2 - θ.l2) / ((θ.lam2 + θ.mu2 + θ.gam) * θ.gam)
  else θ.lam2 * θ.mu2 * (θ.p2 - θ.l2) / ((θ.lam2 + θ.mu2 + θ.gam) * θ.gam)

/-- (11): r̲₁ = πᴺᶜ₁(1) − α₁πᴺᶜ₁(0) − α₁l₁. -/
noncomputable def rLow1 (θ : Params) : ℝ :=
  piNC1 θ 1 - alpha1 θ * piNC1 θ 0 - alpha1 θ * θ.l1

/-- (12): r₁ = (1 − β)πᴺᶜ₁(1) − απᴺᶜ₁(0) − αl₁ + βq₁. -/
noncomputable def rMid1 (θ : Params) : ℝ :=
  (1 - beta θ) * piNC1 θ 1 - alpha θ * piNC1 θ 0 - alpha θ * θ.l1 + beta θ * θ.q1

/-- (13): r̄₁ = (1 − β₂)πᴺᶜ₁(1) + β₂q₁. -/
noncomputable def rBar1 (θ : Params) : ℝ :=
  (1 - beta2 θ) * piNC1 θ 1 + beta2 θ * θ.q1

/-- Proof of Lemma 3, p. A3: r̲₂ = πᴺᶜ₂(1) − β₂πᴺᶜ₂(0) − β₂l₂. -/
noncomputable def rLow2 (θ : Params) : ℝ :=
  piNC2 θ 1 - beta2 θ * piNC2 θ 0 - beta2 θ * θ.l2

/-- Proof of Lemma 3, p. A3: r₂ = (1 − α)πᴺᶜ₂(1) − βπᴺᶜ₂(0) − βl₂ + αq₂. -/
noncomputable def rMid2 (θ : Params) : ℝ :=
  (1 - alpha θ) * piNC2 θ 1 - beta θ * piNC2 θ 0 - beta θ * θ.l2 + alpha θ * θ.q2

/-- Proof of Lemma 3, p. A3: r̄₂ = (1 − α₁)πᴺᶜ₂(1) + α₁q₂. -/
noncomputable def rBar2 (θ : Params) : ℝ :=
  (1 - alpha1 θ) * piNC2 θ 1 + alpha1 θ * θ.q2

/-- Condition (15): β₂q₁ > ρ̂₁(p₁ − l₁) + l₁ and α₁q₂ > ρ̂₂(p₂ − l₂) + l₂. -/
def Cond15 (θ : Params) : Prop :=
  beta2 θ * θ.q1 > rhoHat1 θ * (θ.p1 - θ.l1) + θ.l1 ∧
  alpha1 θ * θ.q2 > rhoHat2 θ * (θ.p2 - θ.l2) + θ.l2

/-- One positive-rate transition `s → t` of the chain under σ (Figure 2): own arrival to an idle
firm, a type-1 transfer `(1,0,k) → (1,1,k−1)` if σ₂(k) = 0, a type-2 transfer
`(0,1,k) → (1,1,k+1)` if σ₁(k) = 0, or a service completion. (All rates are positive under
`Standing`.) -/
def Trans (σ : Profile) (s t : State) : Prop :=
  (s.1 = 0 ∧ t = (1, s.2.1, s.2.2)) ∨
  (s.1 = 1 ∧ s.2.1 = 0 ∧ σ.s2 s.2.2 = 0 ∧ t = (1, 1, s.2.2 - 1)) ∨
  (s.2.1 = 0 ∧ t = (s.1, 1, s.2.2)) ∨
  (s.2.1 = 1 ∧ s.1 = 0 ∧ σ.s1 s.2.2 = 0 ∧ t = (1, 1, s.2.2 + 1)) ∨
  (s.1 = 1 ∧ t = (0, s.2.1, s.2.2)) ∨
  (s.2.1 = 1 ∧ t = (s.1, 0, s.2.2))

/-- The uniformized step killed at the target `t` (the value at `t` is set to `0`). -/
noncomputable def killStep (θ : Params) (σ : Profile) (t : State) (f : State → ℝ) (s : State) :
    ℝ :=
  if s = t then 0 else step θ σ f s

/-- `Γ = E[e^{−γτ}]`, τ the first-passage time from `s` to `t` under σ, computed on the
uniformized chain: `∑ₙ (Λ/(Λ+γ))ⁿ · P(first hit of t at jump n)`. The paper's Γ(x₁,x₂,k′,k)
(target `(1,0,k)`) is `Gam θ σ (1, 0, k) (x₁, x₂, k′)`. -/
noncomputable def Gam (θ : Params) (σ : Profile) (t s : State) : ℝ :=
  ∑' n : ℕ, (Lam θ / (Lam θ + θ.gam)) ^ n *
    ((killStep θ σ t)^[n] (fun u => if u = t then 1 else 0)) s

end TradingFavors.Existence


