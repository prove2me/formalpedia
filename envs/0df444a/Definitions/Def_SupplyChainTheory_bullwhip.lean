-- Prove2me | Definitions.Def_SupplyChainTheory_bullwhip
-- name    : SupplyChainTheory_bullwhip
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-23T23:59:36.96774+00:00
-- url     : https://prove2.me/theorems/a45f8637-a997-49e0-b2a1-43817a3f10ea
-- title:
--   The bullwhip-effect models of Chapter 13: AR(1) demand with moving-average base-stock levels, order batching, and the rationing game
-- statement:
--   The three models of Sect. 13.2 of Snyder and Shen in which a rational retailer's orders are more
--   variable than its demands.
--
--   **Demand signal processing (Sect. 13.2.2).** An `AR1Demand` is a demand process
--   $D_t$, $t \in \mathbb{Z}$, following the first-order autoregressive model (13.1),
--   $$ D_t \;=\; d + \rho D_{t-1} + \epsilon_t, $$
--   with a constant $d \ge 0$, a correlation constant $-1 < \rho < 1$, and errors $\epsilon_t$
--   that are i.i.d. $N(0, \sigma^2)$, each independent of the whole past $(D_s)_{s < t}$; the
--   process is in steady state, every $D_t$ having the stationary law $N(d/(1-\rho), \sigma^2/(1-\rho^2))$.
--   The retailer follows a base-stock policy with lead time $L$ and estimates the lead-time
--   demand parameters by a moving average of the previous $m$ demands:
--   `muHat L m t` is $\hat\mu^L_t = L\big(\sum_{i=1}^m D_{t-i}\big)/m$ (Eq. 13.7),
--   `err m t` is the one-period forecast error $e_t = D_t - \hat\mu^1_t$, and
--   `sigmaHat C m t` is $\hat\sigma^L_{et} = C\sqrt{\sum_{i=1}^m e_{t-i}^2/m}$ (Eq. 13.8), where the
--   book's constant $C_{L\rho}$, whose exact form it omits, is the parameter $C$. The base-stock
--   level is `baseStock C z L m t` $= \hat\mu^L_t + z_\alpha\hat\sigma^L_{et}$ (Eq. 13.9), and the
--   order placed in period $t$ is `order C z L m t` $= S_t - S_{t-1} + D_{t-1}$.
--
--   **Order batching (Sect. 13.2.4).** A `BatchOrders P N R mu sigma` has $N$ retailers with
--   i.i.d. $N(\mu, \sigma^2)$ demands `D i k` over the $R$ periods of a reorder interval, and a
--   random number `X` of retailers ordering in the period considered, independent of the demands;
--   `supplierOrder` is the total order received by the supplier, the sum of the last $R$ demands
--   of the $X$ ordering retailers (retailers $1, \dots, X$ without loss of generality). The three
--   ordering patterns of the book (random, positively correlated, balanced) are the three
--   distributions of $X$ and enter the theorems as hypotheses.
--
--   **Rationing game (Sect. 13.2.3).** `rationingCost h p r A1 Dlaw Q2 Q1` is retailer 1's expected
--   cost (13.14) when it orders $Q_1$, retailer 2 orders $Q_2$, and the available supply is $A_1$
--   with probability $r$ (allocated pro rata, $a(Q_1) = A_1Q_1/(Q_1+Q_2)$) and unlimited with
--   probability $1-r$; each term is the newsvendor cost with holding cost $h$ and stockout penalty
--   $p$ under the demand law.
--
--   **Formalization Note** Time is indexed by $\mathbb{Z}$ so that $D_{t-m-1}$ exists for every $t$.
--   Stationarity and the independence of $\epsilon_t$ from the past are fields of the structure, as
--   the book's "steady-state values" require; the moments (13.2)-(13.4) are then theorems. The
--   order $Q_t$ may be negative, as the book allows (returns are refunded). Divisions by $m$, $R$
--   and $Q_1 + Q_2$ are Lean's total division and are guarded in the theorems.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, Sect. 13.2.2 pp. 542-544 (Eq. 13.1-13.9 and the order Qt = St - St-1 + Dt-1), Sect. 13.2.3 pp. 546-547 (Eq. 13.14), Sect. 13.2.4 pp. 548-551

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

/-- A stationary Gaussian AR(1) demand process, Snyder-Shen Eq. (13.1): `D t = d + ρ D (t-1) + ε t`
with `ε t` i.i.d. `N(0, σ²)`, each independent of the past demands, and every `D t` distributed
as the stationary law `N(d/(1-ρ), σ²/(1-ρ²))`. -/
structure AR1Demand {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  d : ℝ
  rho : ℝ
  sigma : ℝ
  d_nonneg : 0 ≤ d
  rho_lt : |rho| < 1
  sigma_pos : 0 < sigma
  eps : ℤ → Ω → ℝ
  D : ℤ → Ω → ℝ
  measurable_D : ∀ t, Measurable (D t)
  eps_indep : iIndepFun eps P
  eps_law : ∀ t, P.map (eps t) = gaussianReal 0 (Real.toNNReal (sigma ^ 2))
  eps_indep_past : ∀ t : ℤ, IndepFun (eps t) (fun ω (k : ℕ) => D (t - 1 - k) ω) P
  recursion : ∀ t : ℤ, ∀ ω, D t ω = d + rho * D (t - 1) ω + eps t ω
  stationary : ∀ t, P.map (D t) =
    gaussianReal (d / (1 - rho)) (Real.toNNReal (sigma ^ 2 / (1 - rho ^ 2)))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Eq. (13.7): the moving-average estimate `μ̂ᴸₜ = L (∑_{i=1}^m D_{t-i}) / m`. -/
noncomputable def AR1Demand.muHat (X : AR1Demand P) (L m : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  L * ((∑ i ∈ Finset.Icc 1 m, X.D (t - i) ω) / m)

/-- The one-period forecast error `eₜ = Dₜ − μ̂¹ₜ`. -/
noncomputable def AR1Demand.err (X : AR1Demand P) (m : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.D t ω - X.muHat 1 m t ω

/-- Eq. (13.8): `σ̂ᴸₑₜ = C √(∑_{i=1}^m e_{t-i}² / m)`, the book's constant `C_{Lρ}` being the
parameter `C`. -/
noncomputable def AR1Demand.sigmaHat (X : AR1Demand P) (C : ℝ) (m : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  C * Real.sqrt ((∑ i ∈ Finset.Icc 1 m, (X.err m (t - i) ω) ^ 2) / m)

/-- Eq. (13.9): the base-stock level `Sₜ = μ̂ᴸₜ + z_α σ̂ᴸₑₜ`. -/
noncomputable def AR1Demand.baseStock (X : AR1Demand P) (C z : ℝ) (L m : ℕ) (t : ℤ) (ω : Ω) :
    ℝ :=
  X.muHat L m t ω + z * X.sigmaHat C m t ω

/-- The order placed in period `t`: `Qₜ = Sₜ − Sₜ₋₁ + Dₜ₋₁` (p. 544). -/
noncomputable def AR1Demand.order (X : AR1Demand P) (C z : ℝ) (L m : ℕ) (t : ℤ) (ω : Ω) : ℝ :=
  X.baseStock C z L m t ω - X.baseStock C z L m (t - 1) ω + X.D (t - 1) ω

/-- Order batching, Sect. 13.2.4: `N` retailers with i.i.d. `N(μ, σ²)` period demands `D i k`
over a reorder interval of `R` periods, and `X` the number of retailers ordering in the period
considered, independent of the demands. -/
structure BatchOrders {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N R : ℕ) (mu sigma : ℝ)
    where
  D : Fin N → Fin R → Ω → ℝ
  X : Ω → ℕ
  measurable_D : ∀ i k, Measurable (D i k)
  measurable_X : Measurable X
  D_indep : iIndepFun (fun p : Fin N × Fin R => D p.1 p.2) P
  D_law : ∀ i k, P.map (D i k) = gaussianReal mu (Real.toNNReal (sigma ^ 2))
  X_indep : IndepFun X (fun ω (p : Fin N × Fin R) => D p.1 p.2 ω) P
  X_le : ∀ ω, X ω ≤ N

/-- The total order received by the supplier: the last `R` demands of each of the `X` ordering
retailers, taken to be retailers `1, …, X` without loss of generality. -/
noncomputable def BatchOrders.supplierOrder {N R : ℕ} {mu sigma : ℝ}
    (B : BatchOrders P N R mu sigma) (ω : Ω) : ℝ :=
  ∑ i : Fin N, if i.val < B.X ω then ∑ k : Fin R, B.D i k ω else 0

/-- Rationing game, Sect. 13.2.3, Eq. (13.14): retailer 1's expected cost when it orders `Q1`,
retailer 2 orders `Q2`, and the supply is `A1` with probability `r` (allocated pro rata) and
unlimited with probability `1 - r`. -/
noncomputable def rationingCost (h p r A1 : ℝ) (Dlaw : Measure ℝ) (Q2 Q1 : ℝ) : ℝ :=
  (1 - r) * (∫ d, (h * max (Q1 - d) 0 + p * max (d - Q1) 0) ∂Dlaw)
    + r * (∫ d, (h * max (A1 * Q1 / (Q1 + Q2) - d) 0
                   + p * max (d - A1 * Q1 / (Q1 + Q2)) 0) ∂Dlaw)

end SupplyChainTheory


