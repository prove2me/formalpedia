-- Prove2me | Definitions.Def_EndogBudgetAds_Equilibrium_Proof
-- name    : EndogBudgetAds_Equilibrium_Proof
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:22.741575+00:00
-- url     : https://prove2.me/theorems/2ee0ea06-845e-4d5d-bf20-4594b0b3dfee
-- title:
--   Proof objects, pp. 14, 22, 24, 25 — dual (10), slack Ξ_k(σ_j) (7), event E_j(σ_j) (9), greedy allocation (Definition 1), no ties
-- statement:
--   The objects the proof of Theorem 1 is organized around. Throughout, $b$ is the bid vector of the profile $(\sigma_j, \sigma^*_{-j})$, in which bidder $j$ deviates to $\sigma_j$ and every other bidder bids $W_k = V_k/(1+r_k)$; $B^*_k = B^*_k(V_k)$; $W^{(q)}_i$ is the $q$-th highest of $(W_{ik})_k$, $W^{(2)}_{i,-j}$ the second highest excluding bidder $j$, and $U^x_{k,q}$ the set of items on which bidder $k$ has the $q$-th highest entry of $x$.
--
--   1. **The dual (10)** of the ad network's LP (2):
--   $$\min_{\mu,\nu} \sum_{i} \nu_i + \sum_{k} B_k \mu_k + \delta n \quad \text{s.t.} \quad \nu_i + \mu_k p^b(i,k) \ge p^b(i,k) - \delta \ \ \forall i,k, \qquad \mu \ge 0,\ \nu \ge 0.$$
--
--   2. **The slack term (7).** For bidders $j$ and $k$,
--   $$\Xi_k(\sigma_j) = \sum_i \big(b_{ij} - W^{(2)}_i\big)\mathbf 1\{i \in U^W_{k,1} \cap U^b_{j,2}\} - \sum_i W^{(2)}_{i,-j}\mathbf 1\{i \in U^W_{k,1} \cap U^b_{j,1}\} + \sum_i W^{(2)}_i \mathbf 1\{i \in U^W_{j,1} \cap U^W_{k,2}\}.$$
--
--   3. **The event (9).**
--   $$E_j(\sigma_j) = \{\bar\Psi_k + \Xi_k(\sigma_j) < B^*_k \text{ for all } k \ne j\} \cap \{\bar\Psi_j < B^*_j\},$$
--   a set of valuation profiles $V$.
--
--   4. **Greedy allocation (Definition 1).** $Y$ is greedy for bids $b$ if $Y_{ij} = \mathbf 1\{i \in U^b_{j,1},\ b^{(2)}_i \ge \delta\}$.
--
--   5. **No ties.** The bids $b$ have no ties if on every item the bids of distinct bidders differ (the paper's convention on p. 14; it holds almost surely for the strategies considered).
--
--   These are the proof-level objects of §3.2: the event $E_j(\sigma_j)$ is where a deviation cannot profit, and the dual multipliers measure which budget constraint is most active.
--
--   **Formalization Note** On p. 24 the text calls $E_j(\sigma_j)$ "the union" of the events $E_{jk}(\sigma_j)$ but the display (9) and Appendix A (p. 42) take the intersection; the intersection is used. The strict inequality $\bar\Psi_j < B^*_j$ of (9) is used (the restatement on p. 41 has $\le$). Second order statistics of fewer than two entries are $0$; the main statements force $m \ge 55$.
-- source:
--   Ciocan & Iyer, SSRN 3240995: Definition 1 and the no-ties convention, p. 14; (7), p. 22; (8)–(9), p. 24; dual (10), p. 25

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model

namespace EndogBudgetAds.Equilibrium

open MeasureTheory ProbabilityTheory

/-! ### The dual (10) of the LP (2), p. 25. `μ k` is the multiplier of bidder `k`'s budget constraint,
`ν i` that of item `i`'s supply constraint. -/

/-- Feasibility in (10): `μ, ν ≥ 0` and `ν_i + μ_k p^b(i, k) ≥ p^b(i, k) − δ` for all `i, k`. -/
def DualFeasible (M : Market) (b : Fin M.m → Fin M.n → ℝ) (μ : Fin M.m → ℝ) (ν : Fin M.n → ℝ) :
    Prop :=
  (∀ k, 0 ≤ μ k) ∧ (∀ i, 0 ≤ ν i) ∧ ∀ i k, pay b i k - M.δ ≤ ν i + μ k * pay b i k

/-- The objective of (10): `Σ_i ν_i + Σ_k B_k μ_k + δ n`. -/
noncomputable def dualObj (M : Market) (B : Fin M.m → ℝ) (μ : Fin M.m → ℝ) (ν : Fin M.n → ℝ) : ℝ :=
  ∑ i, ν i + ∑ k, B k * μ k + M.δ * M.n

/-- `(μ, ν)` is an optimal solution of the dual (10) (a minimizer). -/
def DualOptimal (M : Market) (B : Fin M.m → ℝ) (b : Fin M.m → Fin M.n → ℝ) (μ : Fin M.m → ℝ)
    (ν : Fin M.n → ℝ) : Prop :=
  DualFeasible M b μ ν ∧
    ∀ μ' ν', DualFeasible M b μ' ν' → dualObj M B μ ν ≤ dualObj M B μ' ν'

/-! ### The slack term (7), p. 22, and the events (8)–(9), p. 24. Throughout, `b` is the bid vector of
the profile `(σ_j, σ*_{−j})`, `W = V/(1+r)` the bids of σ*, and `B*_k = B*_k(V_k)`. -/

/-- The slack term (7), p. 22, for a deviation `σj` of bidder `j` and a bidder `k`:
`Ξ_k(σ_j) = Σ_i (b_ij − W_i^{(2)}) 1{i ∈ U^W_{k,1} ∩ U^b_{j,2}} − Σ_i W^{(2)}_{i,−j} 1{i ∈ U^W_{k,1} ∩ U^b_{j,1}}
+ Σ_i W_i^{(2)} 1{i ∈ U^W_{j,1} ∩ U^W_{k,2}}`. -/
noncomputable def Xi (M : Market) (j k : Fin M.m) (σj : Strategy M.n) (V : Valuations M) : ℝ :=
  (∑ i, if IsTop (fun l => W M V l i) k ∧
        IsSecond (fun l => bidsOf (deviate (sigmaStar M) j σj) V l i) j then
      bidsOf (deviate (sigmaStar M) j σj) V j i - top2 (fun l => W M V l i) else 0)
  - (∑ i, if IsTop (fun l => W M V l i) k ∧
        IsTop (fun l => bidsOf (deviate (sigmaStar M) j σj) V l i) j then
      top2Excl (fun l => W M V l i) j else 0)
  + (∑ i, if IsTop (fun l => W M V l i) j ∧ IsSecond (fun l => W M V l i) k then
      top2 (fun l => W M V l i) else 0)

/-- The event (9), p. 24, as a set of valuation profiles:
`E_j(σ_j) = {Ψ̄_k + Ξ_k(σ_j) < B*_k for all k ≠ j} ∩ {Ψ̄_j < B*_j}`. -/
def EventJ (M : Market) (j : Fin M.m) (σj : Strategy M.n) : Set (Valuations M) :=
  {V | (∀ k, k ≠ j → PsiBar M k V + Xi M j k σj V < Bstar M k (V k)) ∧
    PsiBar M j V < Bstar M j (V j)}

/-! ### Greedy allocations (Definition 1, p. 14) and the no-ties convention (p. 14). -/

/-- Definition 1, p. 14: `Y` is greedy for bids `b` when `Y_ij = 1{i ∈ U^b_{j,1}, b_i^{(2)} ≥ δ}`. -/
def IsGreedy (M : Market) (b : Fin M.m → Fin M.n → ℝ) (Y : Fin M.n → Fin M.m → ℝ) : Prop :=
  ∀ i j, Y i j =
    if IsTop (fun l => b l i) j ∧ M.δ ≤ top2 (fun l => b l i) then 1 else 0

/-- No ties (p. 14): on every item, the bids of distinct bidders are distinct. -/
def NoTies {m n : ℕ} (b : Fin m → Fin n → ℝ) : Prop :=
  ∀ i k l, k ≠ l → b k i ≠ b l i

end EndogBudgetAds.Equilibrium


