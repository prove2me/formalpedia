-- Prove2me | Definitions.Def_SupplyChainTheory_disruptions
-- name    : SupplyChainTheory_disruptions
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T00:47:29.952814+00:00
-- url     : https://prove2.me/theorems/e656a614-29f8-43e3-b490-0b53250001cc
-- title:
--   The supply-disruption models of Chapter 9: the two-state disruption chain, the newsvendor with disruptions, and the reliable fixed-charge location problem
-- statement:
--   The disruption models of Chapter 9 of Snyder and Shen.
--
--   **The disruption process (Sect. 9.2.2).** A supplier is up or down; from an up period it is
--   disrupted next period with the disruption probability $\alpha$, and from a down period it
--   recovers with the recovery probability $\beta$. The granular chain has state $0$ (up) and
--   state $n \ge 1$ (the $n$-th consecutive period of a disruption). `disruptionPmf α β` is the
--   explicit distribution of Lemma 9.2, $\pi_0 = \beta/(\alpha+\beta)$ and
--   $\pi_n = \frac{\alpha\beta}{\alpha+\beta}(1-\beta)^{n-1}$ for $n \ge 1$; `disruptionCdf α β n`
--   is $F(n) = \sum_{i \le n} \pi_i$ of (9.10); `IsStationary α β π` is the system of
--   stationary equations of the chain, $\pi_0 = (1-\alpha)\pi_0 + \beta\sum_{n \ge 1}\pi_n$,
--   $\pi_1 = \alpha\pi_0$, $\pi_{n+1} = (1-\beta)\pi_n$ for $n \ge 1$.
--
--   **The newsvendor with disruptions (Sect. 9.2.2).** With deterministic demand $d$ per period,
--   holding cost $h$ and backorder cost $p$ per unit per period, and base-stock level $S$ ordered
--   up to in every up period, `periodCost h p d S n` is (9.13), the cost
--   $\hat g(S, n) = h[S - (n+1)d]^+ + p[(n+1)d - S]^+$ incurred in the $n$-th period of a
--   disruption; `meanCost α β h p d S` is the expected cost per period $g(S) = \sum_n \pi_n \hat g(S, n)$
--   of (9.14), and `varCost` its variance over the disruption state (Sect. 9.5.2).
--
--   **The reliable fixed-charge location problem (Sect. 9.6).** Customers `Fin n` with demands
--   $h_i$, sites `Fin m` with fixed costs $f_j$ and costs $c_{ij}$, each site disrupted
--   independently with probability $q$; a designated emergency site $u$ never fails, has $f_u = 0$,
--   and $c_{iu} = \theta_i$ is the penalty for not serving $i$. Customer $i$ is assigned to a
--   facility at each level $r$ (served by it when its $r$ closer facilities are all disrupted)
--   until it is assigned to $u$. `rflpPsi` is the coefficient $\psi_{ijr} = h_i c_{ij} q^r(1-q)$,
--   or $h_i c_{ij} q^r$ for $j = u$; `rflpCost` is the objective (9.61); `RFLPFeasible u x y` is
--   (9.62)-(9.67); `RFLPOptimal` is feasibility plus minimality.
--
--   **Formalization Note** Infinite sums are `tsum`; under $0 < \beta$ the distribution is
--   geometric and every series in the theorems is summable, which the theorems' hypotheses
--   guarantee. Levels run over `Fin m`, the book's $r = 0, \dots, |J| - 1$, and the sum
--   $\sum_{s < r} y_{ius}$ of (9.62) is over the levels below $r$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, Sect. 9.2.2 pp. 360-363 (Eq. 9.8-9.14, Lemma 9.2), Sect. 9.5.2 pp. 384-385, Sect. 9.6.2-9.6.3 pp. 390-391 (Eq. 9.61-9.67)

import Mathlib

namespace SupplyChainTheory

/-! ### The disruption process, Sect. 9.2.2 -/

/-- Lemma 9.2's steady-state probabilities of the disruption chain with disruption probability
`α` and recovery probability `β`: `π₀ = β/(α+β)` and `πₙ = αβ/(α+β) (1−β)^(n−1)` for `n ≥ 1`. -/
noncomputable def disruptionPmf (α β : ℝ) : ℕ → ℝ
  | 0 => β / (α + β)
  | n + 1 => α * β / (α + β) * (1 - β) ^ n

/-- (9.10): `F(n) = ∑_{i=0}^n πᵢ`, the steady-state probability of a disruption of at most `n`
periods (or none). -/
noncomputable def disruptionCdf (α β : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), disruptionPmf α β i

/-- The stationary equations of the disruption chain whose state is `0` (up) or `n ≥ 1` (the
`n`-th period of a disruption): from `0` go to `1` w.p. `α`, from `n ≥ 1` go to `0` w.p. `β`
and to `n + 1` w.p. `1 − β`. -/
def IsStationary (α β : ℝ) (π : ℕ → ℝ) : Prop :=
  π 0 = (1 - α) * π 0 + β * ∑' n, π (n + 1)
    ∧ π 1 = α * π 0 ∧ ∀ n, 1 ≤ n → π (n + 1) = (1 - β) * π n

/-! ### The newsvendor problem with disruptions, Sect. 9.2.2 -/

/-- (9.13): `ĝ(S, n) = h [S − (n+1)d]⁺ + p [(n+1)d − S]⁺`, the cost of a period in the `n`-th
period of a disruption (`n = 0`: not disrupted) under base-stock level `S` and demand `d`. -/
noncomputable def periodCost (h p d S : ℝ) (n : ℕ) : ℝ :=
  h * max (S - (n + 1) * d) 0 + p * max ((n + 1) * d - S) 0

/-- (9.14): the expected cost per period `g(S) = ∑ₙ πₙ ĝ(S, n)`. -/
noncomputable def meanCost (α β h p d : ℝ) (S : ℝ) : ℝ :=
  ∑' n, disruptionPmf α β n * periodCost h p d S n

/-- The variance of the per-period cost over the disruption state (Sect. 9.5.2). -/
noncomputable def varCost (α β h p d : ℝ) (S : ℝ) : ℝ :=
  (∑' n, disruptionPmf α β n * (periodCost h p d S n) ^ 2) - (meanCost α β h p d S) ^ 2

/-! ### The reliable fixed-charge location problem, Sect. 9.6 -/

/-- The coefficient `ψᵢⱼᵣ` of (RFLP): `hᵢ cᵢⱼ qʳ (1 − q)`, or `hᵢ cᵢⱼ qʳ` for the emergency
facility `u`. -/
def rflpPsi {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (q : ℝ) (u : Fin m) (i : Fin n)
    (j : Fin m) (r : ℕ) : ℝ :=
  h i * c i j * q ^ r * (if j = u then 1 else 1 - q)

/-- (9.61): the RFLP objective, fixed cost plus expected transportation cost over levels
`r = 0, …, |J| − 1`. -/
def rflpCost {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ) (q : ℝ)
    (u : Fin m) (x : Fin m → ℝ) (y : Fin n → Fin m → Fin m → ℝ) : ℝ :=
  ∑ j, f j * x j + ∑ i, ∑ j, ∑ r : Fin m, rflpPsi h c q u i j r.val * y i j r

/-- (9.62)-(9.67): feasibility for (RFLP); `y i j r = 1` means `i` is assigned to `j` at level `r`. -/
def RFLPFeasible {n m : ℕ} (u : Fin m) (x : Fin m → ℝ) (y : Fin n → Fin m → Fin m → ℝ) : Prop :=
  (∀ i (r : Fin m), ∑ j, y i j r + ∑ s ∈ Finset.univ.filter (fun s : Fin m => s < r), y i u s = 1)
    ∧ (∀ i j r, y i j r ≤ x j) ∧ (∀ i j, ∑ r, y i j r ≤ 1) ∧ x u = 1
    ∧ (∀ j, x j = 0 ∨ x j = 1) ∧ (∀ i j r, y i j r = 0 ∨ y i j r = 1)

/-- An optimal solution of (RFLP). -/
def RFLPOptimal {n m : ℕ} (h : Fin n → ℝ) (c : Fin n → Fin m → ℝ) (f : Fin m → ℝ) (q : ℝ)
    (u : Fin m) (x : Fin m → ℝ) (y : Fin n → Fin m → Fin m → ℝ) : Prop :=
  RFLPFeasible u x y ∧ ∀ x' y', RFLPFeasible u x' y' → rflpCost h c f q u x y ≤ rflpCost h c f q u x' y'
end SupplyChainTheory


