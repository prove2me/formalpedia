-- Prove2me | Definitions.Def_SystemicDiv_SellOff_Model
-- name    : SystemicDiv_SellOff_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:47.10769+00:00
-- url     : https://prove2.me/theorems/1eafa142-b269-48fc-8405-aa7497568fe1
-- title:
--   §2–§3, pp. 8–24 — fire-sale game: leverage-threshold deleveraging, proportional liquidation with price impact, expected costs, potential, Nash equilibrium, liquidation events
-- statement:
--   This file sets up the fire-sale game of Capponi and Weber.
--
--   **Banks.** There are $N$ banks and $K$ assets, each with initial price one. Bank $i$ has total initial assets $w_i$, leverage ratio $\lambda_i = d_i/e_i$ and leverage threshold $\lambda_{M,i}$; its debt is $d_i = \frac{\lambda_i}{1+\lambda_i} w_i$. The standing assumptions are $w_i > 0$, $\lambda_i > 0$, $\lambda_{M,i} > 0$ and $\lambda_i \le \lambda_{M,i}$. The **distance to liquidation** is
--   $$\ell_i = \frac{\lambda_{M,i} - \lambda_i}{(1+\lambda_i)\lambda_{M,i}}.$$
--
--   **Shocks and liquidation.** The vector of asset price changes $Z = (Z_1,\dots,Z_K)$ has law $\mu$ on $\mathbb{R}^K$. A bank holding the weight vector $\pi_i$ earns $R_i = \pi_i^\top Z$. Its post-shock leverage is $\lambda_i^{post} = d_i/(w_i(1+R_i) - d_i)$, and it liquidates when $\lambda_i^{post} > \lambda_{M,i}$. It then sells the amount $x_i$ solving
--   $$\frac{d_i - x_i}{w_i(1+R_i) - d_i} = \lambda_{M,i}.$$
--
--   **Costs.** Liquidation is proportional to holdings, and the execution price of asset $k$ is depressed by $\gamma_k$ times the total dollar amount of asset $k$ sold. The realized cost of bank $i$ is
--   $$\mathrm{cost}_i(\pi_i,\pi_{-i},Z) = x_i \mathbf 1_{\{\lambda_i^{post} > \lambda_{M,i}\}}\, \pi_i^\top \mathrm{Diag}[\gamma] \sum_{j=1}^N \pi_j x_j \mathbf 1_{\{\lambda_j^{post} > \lambda_{M,j}\}},$$
--   and $\mathrm{EC}_i = E[\mathrm{cost}_i]$. The idiosyncratic and systemic components are
--   $$S_i(\pi_i) = E[\pi_i^\top \mathrm{Diag}[\gamma]\pi_i\, x_i^2 \mathbf 1_i], \qquad M_{i,j}(\pi_i,\pi_j) = E[\pi_i^\top \mathrm{Diag}[\gamma]\pi_j\, x_i x_j \mathbf 1_i \mathbf 1_j],$$
--   and the potential is $P(\pi) = \sum_{m=1}^N \big(S_m(\pi_m) + \sum_{j<m} M_{m,j}(\pi_m,\pi_j)\big)$.
--
--   **Game.** The action set is the simplex $\Pi = \{\pi \in [0,1]^K : \sum_k \pi_k = 1\}$. A pure-strategy Nash equilibrium is a profile in $\Pi^N$ from which no bank lowers $\mathrm{EC}_i$ by a unilateral deviation in $\Pi$. A single-bank benchmark portfolio $\pi^S_i \in \Pi$ minimizes $S_i$ on $\Pi$.
--
--   **Assumption 3.3.** $Z$ is spherically symmetric, and each $Z_k$ has a continuous density that is increasing on $(-\infty, 0]$. **Second moment.** $E\|Z\|^2 < \infty$.
--
--   **Events** (two banks). $A_{liq}(\pi_1,\pi_2)$ is the event that at least one bank liquidates, and $A_{sim}(\pi_1,\pi_2)$ the event that both do.
--
--   This is the shared model of every statement in the mission.
--
--   **Formalization Note.** Banks are records `Bank` with fields `w`, `lev` ($\lambda_i$) and `levM` ($\lambda_{M,i}$). Bank $1$ and asset $1$ are index `0`. The liquidation rule is written cross-multiplied, $\lambda_{M,i} w_i(1+R_i) < (1+\lambda_{M,i}) d_i$; this agrees with $\lambda^{post}_i > \lambda_{M,i}$ whenever post-shock equity is positive. `sold` is $x_i \mathbf 1_i$, built from (2.1) and that rule; the closed form of Lemma A.1 is a theorem, not the definition. The shock law is a measure on `EuclideanSpace ℝ (Fin K)`. Spherical symmetry is invariance under every linear isometry, and "increasing" is read weakly (`MonotoneOn`). `SecondMoment` is an added hypothesis used by the theorems: without it, Lean's integral of a non-integrable cost would be $0$. `IsBenchmark` requires the minimizer to lie in $\Pi$. `two t` is the two-asset weight vector $(t, 1-t)$.
-- source:
--   Capponi & Weber, Systemic Portfolio Diversification, SSRN 3345399 (version of June 15, 2023), pp. 8–16 and 24, §2, §3, Definitions 3.1, 3.5, Assumption 3.3, eqs. (2.1), (3.2), p. 10 cost display, p. 13 displays of S_i and M_i,j, p. 24 events A_liq, A_sim

import Mathlib

open MeasureTheory

namespace SystemicDiv.SellOff

/-- The space of asset price changes `Z = (Z_1, …, Z_K)`, Euclidean `ℝ^K` (p. 9). -/
abbrev Shock (K : ℕ) := EuclideanSpace ℝ (Fin K)

/-- The primitives of one bank (p. 8): total initial asset value `w_i`, leverage ratio
`λ_i = d_i / e_i` and leverage threshold `λ_{M,i}`. -/
structure Bank where
  /-- total initial asset value `w_i = d_i + e_i` -/
  w : ℝ
  /-- leverage ratio `λ_i = d_i / e_i` -/
  lev : ℝ
  /-- leverage threshold `λ_{M,i}` -/
  levM : ℝ

/-- Standing assumptions on a bank (§2, p. 8): `w_i > 0`, `λ_i > 0` (debt and equity are positive),
`λ_{M,i} > 0`, and `λ_i ≤ λ_{M,i}` (the bank starts at or below its target threshold; equivalently
`ℓ_i ≥ 0`). -/
def Bank.Standing (b : Bank) : Prop :=
  0 < b.w ∧ 0 < b.lev ∧ b.lev ≤ b.levM ∧ 0 < b.levM

/-- Initial debt `d_i = λ_i / (1 + λ_i) · w_i` (p. 8). -/
noncomputable def Bank.d (b : Bank) : ℝ := b.lev / (1 + b.lev) * b.w

/-- Distance to liquidation `ℓ_i = (λ_{M,i} − λ_i) / ((1 + λ_i) λ_{M,i})` (Definition 3.5, p. 15). -/
noncomputable def Bank.ell (b : Bank) : ℝ := (b.levM - b.lev) / ((1 + b.lev) * b.levM)

/-- Portfolio return `R = πᵀ Z = ∑_k π_k Z_k` of a weight vector `p` at the shock `z` (p. 9). -/
def portRet {K : ℕ} (p : Fin K → ℝ) (z : Shock K) : ℝ := ∑ k, p k * z k

/-- Return `R_i = π_iᵀ Z` of bank `i` in the profile `π` (p. 9). -/
def ret {N K : ℕ} (π : Fin N → Fin K → ℝ) (i : Fin N) (z : Shock K) : ℝ := portRet (π i) z

/-- The bank liquidates when its post-shock leverage exceeds the threshold,
`λ_i^post = d_i / (w_i (1 + R_i) − d_i) > λ_{M,i}` (p. 9), written cross-multiplied as
`λ_{M,i} · w_i (1 + R_i) < (1 + λ_{M,i}) d_i`. -/
def Liquidates (b : Bank) (R : ℝ) : Prop :=
  b.levM * (b.w * (1 + R)) < (1 + b.levM) * b.d

/-- The amount `x_i` solving (2.1), `(d_i − x_i) / (w_i (1 + R_i) − d_i) = λ_{M,i}`, i.e.
`x_i = d_i − λ_{M,i} (w_i (1 + R_i) − d_i)` (p. 9). -/
noncomputable def amount (b : Bank) (R : ℝ) : ℝ := b.d - b.levM * (b.w * (1 + R) - b.d)

/-- The amount actually sold, `x_i · 1{λ_i^post > λ_{M,i}}` (p. 10). -/
noncomputable def sold (b : Bank) (R : ℝ) : ℝ := by
  classical
  exact if Liquidates b R then amount b R else 0

/-- Realized liquidation cost of bank `i` (p. 10):
`cost_i(π_i, π_{−i}, Z) = x_i 1_i · π_iᵀ Diag[γ] ∑_j π_j x_j 1_j`. -/
noncomputable def cost {N K : ℕ} (B : Fin N → Bank) (γ : Fin K → ℝ) (π : Fin N → Fin K → ℝ)
    (i : Fin N) (z : Shock K) : ℝ :=
  sold (B i) (ret π i z) * ∑ k, π i k * γ k * ∑ j, π j k * sold (B j) (ret π j z)

/-- Expected liquidation cost `EC_i(π_i, π_{−i}) = E[cost_i(π_i, π_{−i}, Z)]` (p. 10). -/
noncomputable def EC {N K : ℕ} (μ : Measure (Shock K)) (B : Fin N → Bank) (γ : Fin K → ℝ)
    (π : Fin N → Fin K → ℝ) (i : Fin N) : ℝ :=
  ∫ z, cost B γ π i z ∂μ

/-- Idiosyncratic cost `S_i(π_i) = E[π_iᵀ Diag[γ] π_i x_i² 1{λ_i^post > λ_{M,i}}]` (p. 13); it depends
on bank `i`'s primitives only. -/
noncomputable def S {K : ℕ} (μ : Measure (Shock K)) (γ : Fin K → ℝ) (b : Bank) (p : Fin K → ℝ) : ℝ :=
  ∫ z, (∑ k, p k * γ k * p k) * sold b (portRet p z) ^ 2 ∂μ

/-- Systemic cost `M_{i,j}(π_i, π_j) = E[π_iᵀ Diag[γ] π_j x_i x_j 1{λ_i^post > λ_{M,i}} ∩ {λ_j^post > λ_{M,j}}]`
(p. 13), for banks `b = B i`, `b' = B j`. -/
noncomputable def M {K : ℕ} (μ : Measure (Shock K)) (γ : Fin K → ℝ) (b b' : Bank)
    (p q : Fin K → ℝ) : ℝ :=
  ∫ z, (∑ k, p k * γ k * q k) * sold b (portRet p z) * sold b' (portRet q z) ∂μ

/-- The potential (3.2), p. 14: `P(π) = ∑_m (S_m(π_m) + ∑_{j<m} M_{m,j}(π_m, π_j))`. -/
noncomputable def Pot {N K : ℕ} (μ : Measure (Shock K)) (B : Fin N → Bank) (γ : Fin K → ℝ)
    (π : Fin N → Fin K → ℝ) : ℝ :=
  ∑ m, (S μ γ (B m) (π m) + ∑ j ∈ Finset.univ.filter (· < m), M μ γ (B m) (B j) (π m) (π j))

/-- Admissible profiles `Π^N`, where `Π = {π ∈ [0,1]^K : ∑_k π_k = 1}` (p. 13). -/
def Admissible (N K : ℕ) : Set (Fin N → Fin K → ℝ) :=
  Set.pi Set.univ (fun _ => stdSimplex ℝ (Fin K))

/-- Pure-strategy Nash equilibrium (Definition 3.1, p. 13): every `π_i` is admissible and no bank
lowers its expected liquidation cost by a unilateral admissible deviation. -/
def IsNash {N K : ℕ} (μ : Measure (Shock K)) (B : Fin N → Bank) (γ : Fin K → ℝ)
    (π : Fin N → Fin K → ℝ) : Prop :=
  π ∈ Admissible N K ∧
    ∀ i, ∀ p ∈ stdSimplex ℝ (Fin K), EC μ B γ π i ≤ EC μ B γ (Function.update π i p) i

/-- Single-bank benchmark (p. 18): `p ∈ Π` minimizes the bank's own idiosyncratic cost `S` on `Π`. -/
def IsBenchmark {K : ℕ} (μ : Measure (Shock K)) (γ : Fin K → ℝ) (b : Bank) (p : Fin K → ℝ) : Prop :=
  p ∈ stdSimplex ℝ (Fin K) ∧ IsMinOn (S μ γ b) (stdSimplex ℝ (Fin K)) p

/-- Assumption 3.3 (p. 15): `Z` is spherically symmetric (its law is invariant under every linear
isometry of `ℝ^K`), and each `Z_k` has a continuous probability density, increasing on `(−∞, 0]`. -/
def Assumption33 {K : ℕ} (μ : Measure (Shock K)) : Prop :=
  (∀ A : Shock K ≃ₗᵢ[ℝ] Shock K, μ.map A = μ) ∧
    ∀ k : Fin K, ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ MonotoneOn f (Set.Iic 0) ∧
      μ.map (fun z : Shock K => z k) = volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- Finite second moment of the shock, `E‖Z‖² < ∞` (added, so that expected costs are genuine
integrals). -/
def SecondMoment {K : ℕ} (μ : Measure (Shock K)) : Prop :=
  Integrable (fun z : Shock K => ‖z‖ ^ 2) μ

/-- `A_liq(π_1, π_2)`: at least one of the two banks liquidates (p. 24). -/
def Aliq {K : ℕ} (B : Fin 2 → Bank) (π : Fin 2 → Fin K → ℝ) : Set (Shock K) :=
  {z | Liquidates (B 0) (ret π 0 z) ∨ Liquidates (B 1) (ret π 1 z)}

/-- `A_sim(π_1, π_2)`: both banks liquidate (p. 24). -/
def Asim {K : ℕ} (B : Fin 2 → Bank) (π : Fin 2 → Fin K → ℝ) : Set (Shock K) :=
  {z | Liquidates (B 0) (ret π 0 z) ∧ Liquidates (B 1) (ret π 1 z)}

/-- Two-asset weights `(t, 1 − t)`, i.e. `π_{i,1} = t`, `π_{i,2} = 1 − t`. -/
def two (t : ℝ) : Fin 2 → ℝ := ![t, 1 - t]

end SystemicDiv.SellOff


