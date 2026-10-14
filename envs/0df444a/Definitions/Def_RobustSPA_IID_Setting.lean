-- Prove2me | Definitions.Def_RobustSPA_IID_Setting
-- name    : RobustSPA_IID_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:17.204729+00:00
-- url     : https://prove2.me/theorems/0d9ae883-cc6e-4cd3-b77d-409c3c0c9da4
-- title:
--   §2–§3, pp. 9–17 — DSIC mechanisms (IR), (IC), (AC), regret (2), minimax regret (3), 𝓕_iid, SPA with random reserve, the r*-equation, Φ*_n, the value and the isorevenue CDF
-- statement:
--   This file fixes the model of Anunrojwong, Balseiro and Besbes for selling one indivisible item to $n$ buyers whose valuations $v = (v_1,\dots,v_n)$ lie in the cube $[0,1]^n$.
--
--   1. **Mechanisms.** A (direct, possibly randomized) mechanism $m = (x, p)$ consists of allocation probabilities $x_i(v)$ and expected payments $p_i(v)$, $i = 1,\dots,n$. It is **DSIC**, i.e. belongs to the class $\mathcal M$ of (1), if for all $v \in [0,1]^n$, all $i$ and every misreport $\hat v_i \in [0,1]$:
--   $$x_i(v) \in [0,1],\qquad v_i x_i(v) - p_i(v) \ge 0 \;\text{(IR)},\qquad v_i x_i(v) - p_i(v) \ge v_i x_i(\hat v_i, v_{-i}) - p_i(\hat v_i, v_{-i}) \;\text{(IC)},\qquad \sum_{i=1}^n x_i(v) \le 1 \;\text{(AC)}.$$
--   2. **Regret.** For a distribution $F$ of $v$, the regret (2) is $\mathrm{Regret}(m, F) = \mathbb E_{v\sim F}\big[\max(v) - \sum_{i=1}^n p_i(v)\big]$, and the minimax regret (3) over a class $\mathcal F$ is
--   $$\mathcal R^*_n(\mathcal F) = \inf_{m \in \mathcal M} \sup_{F \in \mathcal F} \mathrm{Regret}(m, F).$$
--   3. **Distribution classes.** $\mathcal F_{\mathrm{all}}$ is the set of probability laws on $[0,1]^n$; $\mathcal F_{\mathrm{iid}}$ (Definition 1) is the set of product laws $G^{\otimes n}$ with a marginal $G$ supported on $[0,1]$. $F^{(1)}_n(t) = \Pr_F(v^{(1)} \le t)$ and $F^{(2)}_n(t) = \Pr_F(v^{(2)} \le t)$ are the CDFs of the highest and second-highest valuations, and $G(t) = G((-\infty, t])$ is the CDF of a law on $\mathbb R$.
--   4. **Second-price auction with random reserve.** $\mathrm{SPA}(\Phi)$ draws a reserve $q \sim \Phi$; the highest bidder wins if $v^{(1)} \ge q$ and pays $\max(v^{(2)}, q)$. Hence the winner is allocated with probability $\Phi(v^{(1)})$ and pays $\mathbb E_{q\sim\Phi}[\max(v^{(2)}, q)\,\mathbf 1(v^{(1)} \ge q)]$.
--   5. **The i.i.d. solution.** For $r > 0$,
--   $$\mathrm{rEq}_n(r) = (1-r)^{n-1} + \log r + \sum_{k=1}^{n-1} \frac{(1-r)^k}{k},$$
--   $$\Phi^*_n(v) = \Big(\frac{v}{v-r}\Big)^{n-1}\log\Big(\frac{v}{r}\Big) - \sum_{k=1}^{n-1}\frac1k\Big(\frac{v}{v-r}\Big)^{n-1-k} \quad (r < v \le 1),$$
--   with $\Phi^*_n(v) = 0$ for $v \le r$ and $\Phi^*_n(v) = 1$ for $v > 1$; the value
--   $$V_n(r) = (1-r)^{n-1} - \int_r^1 \Big(1 - \frac rv\Big)^{n-1} dv;$$
--   and the isorevenue CDF $F^*(t) = 0$ for $t < r$, $1 - r/t$ for $r \le t < 1$, $1$ for $t \ge 1$ (F-IsoRevenue).
--
--   These are the objects of Theorem 1 and of every milestone of this mission.
--
--   **Formalization Note.** Buyers are indexed by `Fin n`. (IR), (IC) and (AC) are imposed for types in $[0,1]^n$ (the seller only knows that valuations lie there; values outside the cube never enter a regret). Two conditions are added to make the expectation (2) meaningful: measurable allocation and payment rules, and payments bounded on the cube (without them the Lean integral of a non-integrable payment would be $0$). Ties in $\mathrm{SPA}$ go to the lowest index; the page breaks ties arbitrarily and the revenue does not depend on the rule. $v^{(2)}$ is $0$ when $n = 1$. $\mathcal F_{\mathrm{iid}}$ is stated as an equality of product measures, which on $[0,1]^n$ is the page's product-CDF condition. $\Phi^*_n$ is defined piecewise so that the closed form is never evaluated at $v = r$, where it is a $0/0$ expression. The minimax regret is a real infimum over the nonempty class of DSIC mechanisms of real suprema; for DSIC mechanisms the regret over $\mathcal F_{\mathrm{iid}}$ lies in $[0, 1 + nB]$ ($B$ the payment bound), so neither the infimum nor the suprema is a junk value.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, pp. 9–17, (IR), (IC), (AC), (1)–(3), Definition 1, §3 (SPA with reserve), Theorem 1, Proposition 1; p. App-1 (F-IsoRevenue)

import Mathlib

namespace RobustSPA.IID

open MeasureTheory
open scoped Classical

/-- The type cube `[0,1]ⁿ`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Icc 0 1

/-- A direct mechanism for `n` buyers: allocation probabilities `x i v` and payments `p i v`. -/
structure Mechanism (n : ℕ) where
  x : Fin n → (Fin n → ℝ) → ℝ
  p : Fin n → (Fin n → ℝ) → ℝ

/-- The class `𝓜` of (1): (IR), (IC), (AC) for types in `[0,1]ⁿ`, allocations in `[0,1]`, plus
measurable allocation and payment rules with bounded payments (so that the expectation (2) is
meaningful). -/
structure Mechanism.IsDSIC {n : ℕ} (m : Mechanism n) : Prop where
  x_mem : ∀ v ∈ cube n, ∀ i, m.x i v ∈ Set.Icc (0 : ℝ) 1
  ir : ∀ v ∈ cube n, ∀ i, 0 ≤ v i * m.x i v - m.p i v
  ic : ∀ v ∈ cube n, ∀ i, ∀ w ∈ Set.Icc (0 : ℝ) 1,
    v i * m.x i (Function.update v i w) - m.p i (Function.update v i w) ≤
      v i * m.x i v - m.p i v
  ac : ∀ v ∈ cube n, ∑ i, m.x i v ≤ 1
  meas_x : ∀ i, Measurable (m.x i)
  meas_p : ∀ i, Measurable (m.p i)
  p_bdd : ∃ B : ℝ, ∀ v ∈ cube n, ∀ i, |m.p i v| ≤ B

/-- The highest valuation `v^(1) = max v`. -/
noncomputable def top {n : ℕ} (v : Fin n → ℝ) : ℝ := ⨆ i, v i

/-- The second-highest valuation `v^(2)` (the largest minimum over pairs of distinct buyers;
`0` when `n = 1`). -/
noncomputable def second {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ⨆ q : {q : Fin n × Fin n // q.1 ≠ q.2}, min (v q.1.1) (v q.1.2)

/-- The regret (2): `E_{v∼μ}[max v − Σᵢ pᵢ(v)]`. -/
noncomputable def regret {n : ℕ} (m : Mechanism n) (μ : Measure (Fin n → ℝ)) : ℝ :=
  ∫ v, (top v - ∑ i, m.p i v) ∂μ

/-- The minimax regret (3): `inf_{m ∈ 𝓜} sup_{F ∈ 𝓕} Regret(m, F)`. -/
noncomputable def minimaxRegret (n : ℕ) (𝓕 : Set (Measure (Fin n → ℝ))) : ℝ :=
  ⨅ m : {m : Mechanism n // m.IsDSIC}, ⨆ μ : 𝓕, regret m.1 (μ : Measure (Fin n → ℝ))

/-- `𝓕_all`: all probability distributions supported on `[0,1]ⁿ`. -/
def Fall (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | IsProbabilityMeasure μ ∧ μ (cube n)ᶜ = 0}

/-- `𝓕_iid` (Definition 1): `n` i.i.d. valuations drawn from a law `G` supported on `[0,1]`. -/
def Fiid (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | ∃ G : ProbabilityMeasure ℝ, (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0 ∧
    μ = Measure.pi (fun _ : Fin n => (G : Measure ℝ))}

/-- The CDF of a law on `ℝ`. -/
noncomputable def cdfOf (G : Measure ℝ) (t : ℝ) : ℝ := (G (Set.Iic t)).toReal

/-- CDF of the highest order statistic, `F^(1)_n(t) = Pr(v^(1) ≤ t)`. -/
noncomputable def F1 {n : ℕ} (μ : Measure (Fin n → ℝ)) (t : ℝ) : ℝ :=
  (μ {u | top u ≤ t}).toReal

/-- CDF of the second-highest order statistic, `F^(2)_n(t) = Pr(v^(2) ≤ t)`. -/
noncomputable def F2 {n : ℕ} (μ : Measure (Fin n → ℝ)) (t : ℝ) : ℝ :=
  (μ {u | second u ≤ t}).toReal

/-- Buyer `i` wins: a highest bid, ties broken in favour of the lowest index. -/
def isWinner {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : Prop :=
  (∀ j, v j ≤ v i) ∧ ∀ j, j < i → v j < v i

/-- `SPA(ρ)`: second-price auction with random reserve `q ∼ ρ`. The winner is allocated with
probability `ρ((-∞, v_i])` and pays `E_{q∼ρ}[max(v^(2), q) 1(v_i ≥ q)]`. -/
noncomputable def SPA {n : ℕ} (ρ : Measure ℝ) : Mechanism n where
  x i v := if isWinner v i then (ρ (Set.Iic (v i))).toReal else 0
  p i v := if isWinner v i then
    ∫ q, (Set.Iic (v i)).indicator (fun q => max (second v) q) q ∂ρ else 0

/-- Left side of the `r*`-equation of Theorem 1:
`(1 − r)^{n−1} + log r + Σ_{k=1}^{n−1} (1 − r)^k / k`. -/
noncomputable def rEq (n : ℕ) (r : ℝ) : ℝ :=
  (1 - r) ^ (n - 1) + Real.log r + ∑ k ∈ Finset.Ico 1 n, (1 - r) ^ k / k

/-- The reserve CDF `Φ*_n` of Theorem 1 with parameter `r`: `0` for `v ≤ r`, the closed form
`(v/(v−r))^{n−1} log(v/r) − Σ_{k=1}^{n−1} (1/k)(v/(v−r))^{n−1−k}` for `r < v ≤ 1`, and `1` for
`v > 1`. -/
noncomputable def PhiStar (n : ℕ) (r v : ℝ) : ℝ :=
  if v ≤ r then 0
  else if v ≤ 1 then
    (v / (v - r)) ^ (n - 1) * Real.log (v / r) -
      ∑ k ∈ Finset.Ico 1 n, (1 / (k : ℝ)) * (v / (v - r)) ^ (n - 1 - k)
  else 1

/-- The minimax value of Theorem 1: `(1 − r)^{n−1} − ∫_r^1 (1 − r/v)^{n−1} dv`. -/
noncomputable def value (n : ℕ) (r : ℝ) : ℝ :=
  (1 - r) ^ (n - 1) - ∫ v in r..1, (1 - r / v) ^ (n - 1)

/-- CDF of the isorevenue law (F-IsoRevenue) starting at `r`: `0` below `r`, `1 − r/t` on
`[r, 1)`, and `1` from `1` on (an atom of mass `r` at `1`). -/
noncomputable def isoCDF (r t : ℝ) : ℝ :=
  if t < r then 0 else if t < 1 then 1 - r / t else 1

end RobustSPA.IID


