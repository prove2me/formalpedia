-- Prove2me | Definitions.Def_FragLOB_Collapse_Model
-- name    : FragLOB_Collapse_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:08.677993+00:00
-- url     : https://prove2.me/theorems/69e38b9d-b80d-4dca-a5d2-40f37264c9bd
-- title:
--   §2–§3.2, pp. 1328–1331 — fragmented LOB: rates, attraction model (4)–(5), delay (1)/(12), workload, routing decisions (9), Definition 1, problem (13), lifting map (15)
-- statement:
--   This file sets up the static model of a fragmented limit order book market of Maglaras, Moallemi and Zheng.
--
--   **Market.** There are $N$ exchanges $i = 1,\dots,N$. Dedicated limit orders arrive to exchange $i$ at rate $\lambda_i \ge 0$; optimizing limit-order investors arrive at total rate $\Lambda > 0$; market orders arrive at aggregate rate $\mu > 0$; exchange $i$ has attraction coefficient $\beta_i > 0$. Each routing option $i \in \{0,1,\dots,N\}$ carries an effective rebate $\tilde r_i \in \mathbb R$, where option $0$ means trading with a market order instead of posting a limit order. The rebates are not constrained.
--
--   **Workload, market-order rates and delays.** For a vector of queue lengths $Q \in \mathbb R^N_+$ the workload is $W = \beta^\top Q = \sum_{i=1}^N \beta_i Q_i$, and the market orders are split by the linear attraction model (4)–(5):
--   $$\mu_i(Q) = \mu\,\frac{\beta_i Q_i}{\sum_{j=1}^N \beta_j Q_j}.$$
--   The expected delay at exchange $i$ is $\mathrm{ED}_i = Q_i/\mu_i(Q)$, as in (1), when $Q_i > 0$; at an empty exchange, where (1) reads $0/0$, it is $W/(\mu\beta_i)$, the value of (12).
--
--   **Routing decisions.** A routing decision assigns to every type $\gamma \ge 0$ a probability vector $\pi(\gamma) = (\pi_0(\gamma),\dots,\pi_N(\gamma))$, i.e. $\pi_i(\gamma) \ge 0$ and $\sum_{i=0}^N \pi_i(\gamma) = 1$ (constraint (9)), such that each $\gamma \mapsto \pi_i(\gamma)$ is measurable; this is the set $\mathcal P$. A type-$\gamma$ investor facing delays $d_1,\dots,d_N$ and choosing $p$ in the simplex earns
--   $$p_0\,\gamma\tilde r_0 + \sum_{i=1}^N p_i\,(\gamma\tilde r_i - d_i),$$
--   the objective of (10); a best response is a maximizer of it over the simplex.
--
--   **Equilibrium (Definition 1).** Let $F$ be the distribution of investor types. A pair $(\pi^*, Q^*)$ with $\pi^* \in \mathcal P$, $Q^* \in \mathbb R^N_+$ and $\beta^\top Q^* > 0$ is an equilibrium if (i) for $F$-almost every type $\gamma$, $\pi^*(\gamma)$ is a best response to the delays $\mathrm{ED}_i(Q^*)$, and (ii) for every exchange $i$,
--   $$\lambda_i + \Lambda \int_0^\infty \pi^*_i(\gamma)\,dF(\gamma) = \mu_i(Q^*).$$
--
--   **The aggregated problem.** For a workload $W$, the aggregated objective of (13) is $\int_0^\infty \{\pi_0(\gamma)\gamma\tilde r_0 + \sum_{i=1}^N \pi_i(\gamma)(\gamma\tilde r_i - W/(\mu\beta_i))\}\,dF(\gamma)$, and $\pi$ is optimal for (13) if it maximizes this over $\mathcal P$. The aggregate balance (14) is $\sum_{i=1}^N(\lambda_i + \Lambda\int_0^\infty \pi_i\,dF) = \mu$, and the lifting map (15) sends $(\pi, W)$ to the queue lengths
--   $$Q_i = \Big(\lambda_i + \Lambda\int_0^\infty \pi_i(\gamma)\,dF(\gamma)\Big)\frac{W}{\mu\beta_i}.$$
--
--   These are the objects of the paper's state-space-collapse theorem (Theorem 1), which says that equilibria are exactly the liftings of solutions of the one-dimensional workload problem.
--
--   **Formalization Note.** Exchanges are indexed by `Fin N` and routing options by `Fin (N+1)`, option `0` being the market order and option `i.succ` exchange `i`. Types live in $\mathbb R$; a routing decision is a function on all of $\mathbb R$, constrained only for $\gamma \ge 0$, and integrals are taken over $\mathbb R$ against $F$ (equal to $\int_0^\infty$ when $F$ charges no negative type). Two deliberate departures from the printed Definition 1: individual rationality is required for $F$-almost every type rather than every type (as printed, Theorem 1's forward direction is false: changing $\pi^*$ on an $F$-null set of types leaves (13)–(14) intact), and $\beta^\top Q^* > 0$ is required, since (4) is undefined at $Q^* = 0$. The empty-exchange delay $W/(\mu\beta_i)$ is a convention that (12) fixes; Lean's $0/0 = 0$ would make an empty exchange delay-free.
-- source:
--   Maglaras, Moallemi & Zheng, Operations Research 69(4):1324–1348 (2021), doi:10.1287/opre.2020.1989, pp. 1328–1331, §2.1–§3.2, eqs. (1), (4), (5), (9)–(15), Definition 1

import Mathlib

namespace FragLOB.Collapse

open MeasureTheory

/-- The parameters of the fragmented limit order book of §2 (pp. 1328–1330):
`N` exchanges indexed by `Fin N`; dedicated limit-order rates `lam i` (λ_i), the optimized
limit-order rate `Lam` (Λ), the aggregate market-order rate `mu` (μ), the attraction
coefficients `beta i` (β_i) of (5), and the effective rebates `r` (r̃_0, …, r̃_N).
Routing options are indexed by `Fin (N+1)`: option `0` is the market order, option `i.succ`
is exchange `i`. -/
structure Market (N : ℕ) where
  lam : Fin N → ℝ
  Lam : ℝ
  mu : ℝ
  beta : Fin N → ℝ
  r : Fin (N + 1) → ℝ

/-- Standing assumptions on the rates (pp. 1328–1330): λ_i ≥ 0, Λ > 0, μ > 0, β_i > 0.
The rebates are unconstrained. -/
def Market.Standing {N : ℕ} (M : Market N) : Prop :=
  (∀ i, 0 ≤ M.lam i) ∧ 0 < M.Lam ∧ 0 < M.mu ∧ ∀ i, 0 < M.beta i

/-- A feasible routing decision for one type, constraint (9): a point of the simplex over the
`N + 1` options. -/
def IsSimplexPoint {N : ℕ} (p : Fin (N + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The set 𝒫 of routing decisions (p. 1331): every `γ ↦ π_i(γ)` is measurable and `π(γ)`
satisfies (9) for every type `γ ≥ 0`. Values at `γ < 0` are unconstrained. -/
def IsRouting {N : ℕ} (pi : ℝ → Fin (N + 1) → ℝ) : Prop :=
  (∀ i, Measurable fun γ => pi γ i) ∧ ∀ γ, 0 ≤ γ → IsSimplexPoint (pi γ)

/-- The workload `W = Σ_i β_i Q_i` (§3.2, p. 1331). -/
def workload {N : ℕ} (M : Market N) (Q : Fin N → ℝ) : ℝ :=
  ∑ j, M.beta j * Q j

/-- The market-order rate of exchange `i`, (4) with the linear attraction (5):
`μ_i(Q) = μ β_i Q_i / Σ_j β_j Q_j`. -/
noncomputable def marketRate {N : ℕ} (M : Market N) (Q : Fin N → ℝ) (i : Fin N) : ℝ :=
  M.mu * M.beta i * Q i / workload M Q

/-- The expected delay at exchange `i`: `ED_i = Q_i / μ_i(Q)` by (1) when `Q_i > 0`, and the
value `W / (μ β_i)` of (12) at an empty exchange (where (1) reads `0/0`). -/
noncomputable def delay {N : ℕ} (M : Market N) (Q : Fin N → ℝ) (i : Fin N) : ℝ :=
  if 0 < Q i then Q i / marketRate M Q i else workload M Q / (M.mu * M.beta i)

/-- The payoff of a type-`γ` investor using the randomized routing `p` when the delays are
`d`, the objective of (10): `p_0 γ r̃_0 + Σ_i p_i (γ r̃_i − d_i)`. -/
def payoff {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ) (p : Fin (N + 1) → ℝ) : ℝ :=
  p 0 * (γ * M.r 0) + ∑ i : Fin N, p i.succ * (γ * M.r i.succ - d i)

/-- `p` is an optimal solution of (10) for type `γ` under delays `d`. -/
def IsBestResponse {N : ℕ} (M : Market N) (d : Fin N → ℝ) (γ : ℝ)
    (p : Fin (N + 1) → ℝ) : Prop :=
  IsSimplexPoint p ∧ ∀ q, IsSimplexPoint q → payoff M d γ q ≤ payoff M d γ p

/-- Definition 1 (Equilibrium), p. 1331, with individual rationality (i) read for `F`-almost
every type, and with a nonzero book (`β^⊤Q > 0`, without which (4) is undefined).
(ii) is the flow balance (11). -/
def IsEquilibrium {N : ℕ} (M : Market N) (F : Measure ℝ) (pi : ℝ → Fin (N + 1) → ℝ)
    (Q : Fin N → ℝ) : Prop :=
  IsRouting pi ∧ (∀ i, 0 ≤ Q i) ∧ 0 < workload M Q ∧
    (∀ᵐ γ ∂F, IsBestResponse M (delay M Q) γ (pi γ)) ∧
    ∀ i, M.lam i + M.Lam * ∫ γ, pi γ i.succ ∂F = marketRate M Q i

/-- The objective of the aggregated problem (13) at workload `W`:
`∫ {π_0(γ) γ r̃_0 + Σ_i π_i(γ)(γ r̃_i − W/(μ β_i))} dF(γ)`. -/
noncomputable def aggObjective {N : ℕ} (M : Market N) (F : Measure ℝ) (W : ℝ)
    (pi : ℝ → Fin (N + 1) → ℝ) : ℝ :=
  ∫ γ, payoff M (fun i => W / (M.mu * M.beta i)) γ (pi γ) ∂F

/-- `pi` is an optimal solution of (13) over the routing decisions 𝒫. -/
def IsAggOptimal {N : ℕ} (M : Market N) (F : Measure ℝ) (W : ℝ)
    (pi : ℝ → Fin (N + 1) → ℝ) : Prop :=
  IsRouting pi ∧ ∀ pi', IsRouting pi' → aggObjective M F W pi' ≤ aggObjective M F W pi

/-- The aggregate flow balance (14): `Σ_i (λ_i + Λ ∫ π_i dF) = μ`. -/
def AggBalance {N : ℕ} (M : Market N) (F : Measure ℝ) (pi : ℝ → Fin (N + 1) → ℝ) : Prop :=
  ∑ i, (M.lam i + M.Lam * ∫ γ, pi γ i.succ ∂F) = M.mu

/-- The lifting map (15): `Q_i = (λ_i + Λ ∫ π_i dF) W / (μ β_i)`. -/
noncomputable def lift {N : ℕ} (M : Market N) (F : Measure ℝ) (pi : ℝ → Fin (N + 1) → ℝ)
    (W : ℝ) (i : Fin N) : ℝ :=
  (M.lam i + M.Lam * ∫ γ, pi γ i.succ ∂F) * W / (M.mu * M.beta i)

end FragLOB.Collapse


