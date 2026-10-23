-- Prove2me | Definitions.Def_EndogBudgetAds_Equilibrium_Model
-- name    : EndogBudgetAds_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:39.415632+00:00
-- url     : https://prove2.me/theorems/7ecba827-61c7-4ce2-a0c5-b06c8585589a
-- title:
--   §2–§3.1, pp. 11–18 — sponsored-search market with endogenous budgets: payments (1), ad network LP (2), strategies, payoffs, Definitions 2–3, the strategy σ* (3)–(4)
-- statement:
--   The sponsored-search market of Ciocan and Iyer with endogenous budgets.
--
--   1. **Market.** There are $m$ bidders (advertisers) $j \in [m]$ and $n$ items (impressions) $i \in [n]$. Bidder $j$ has a valuation vector $V_j = (V_{ij})_{i \in [n]}$; all $V_{ij}$ are independent and $V_{ij} \sim \mathrm{Exp}(\lambda_j)$. Bidder $j$ pays $r_j B_j$ for committing a budget $B_j$, and the ad network earns an outside value $\delta$ per unit of unallocated item. With $\theta_j = \lambda_j(1+r_j)$, the **standing assumptions** (p. 18) are $\lambda_j > 0$, $r_j \ge 0$, $\theta_j \in [\theta_{\min}, \theta_{\max}]$ for a fixed interval with $0 < \theta_{\min} \le \theta_{\max}$, and
--   $$0 < \delta \le \frac{\log(4/3)}{\theta_{\max}}.$$
--   The heterogeneity degree is $\vartheta = \theta_{\max}/\theta_{\min}$ and the slack factor is $\beta(m) = 2\vartheta/m^{1/\vartheta}$.
--
--   2. **Payments (1).** For a bid vector $b = (b_{ik})$, bidder $j$'s price on item $i$ is $p^b(i,j) = \max_{k \ne j,\ b_{ik} \le b_{ij}} b_{ik}$ if $b_{ij} \ne \min_k b_{ik}$, and $0$ otherwise.
--
--   3. **The ad network's LP (2).** Given budgets $B$ and bids $b$, the network picks
--   $$Y(B,b) \in \arg\max_{Y \ge 0} \sum_{i}\sum_{j} p^b(i,j) Y_{ij} + \delta \sum_i \Big(1 - \sum_j Y_{ij}\Big)$$
--   subject to $\sum_i p^b(i,j) Y_{ij} \le B_j$ for every $j$ and $\sum_j Y_{ij} \le 1$ for every $i$. An **allocation rule** is a measurable map $(B,b) \mapsto Y(B,b)$ that returns an optimal solution of (2) for every nonnegative budget vector $B$.
--
--   4. **Strategies and outcomes.** A strategy $\sigma_j$ maps $V_j$ to a budget $B_j(V_j) \ge 0$ and bids $b_j(V_j)$, both measurable. Under a profile $\sigma$, bidder $j$'s spend, payoff and modified profit are
--   $$\Psi_j(\sigma) = \sum_i p^b(i,j) Y_{ij}, \qquad \pi_j(\sigma) = \sum_i (V_{ij} - p^b(i,j)) Y_{ij} - r_j B_j, \qquad \tilde\pi_j(\sigma) = \pi_j(\sigma) + r_j(B_j - \Psi_j(\sigma)).$$
--
--   5. **Approximate equilibrium (Definitions 2–3).** $\sigma_j$ is an $\epsilon$-approximate best response to $\sigma_{-j}$ if $\mathbb E[\pi_j(\sigma'_j, \sigma_{-j})] \le \mathbb E[\pi_j(\sigma)](1+\epsilon)$ for every strategy $\sigma'_j$; $\sigma$ is an $\epsilon$-equilibrium if this holds for every $j$.
--
--   6. **The strategy profile σ* ((3)–(4)).** With shaded valuations $W_{ij} = V_{ij}/(1+r_j)$, let $W^{(2)}_i$ be the second highest of $(W_{ik})_k$ and $U^W_{j,1}$ the items on which $j$ has the highest $W$. Then
--   $$\bar\Psi_j = \sum_i W^{(2)}_i \mathbf 1\{i \in U^W_{j,1}\}, \qquad b^*_j = W_j, \qquad B^*_j = \mathbb E_{-j}[\bar\Psi_j]\,(1+\beta(m)),$$
--   where $\mathbb E_{-j}$ averages over the other bidders' valuations with $V_j$ fixed.
--
--   This file is the model every statement of the mission is phrased in.
--
--   **Formalization Note** Valuations are bidder-major (`V j i` $= V_{ij}$), allocations item-major (`Y i j` $= Y_{ij}$). `IsTop x k` means $k$ has the strictly highest entry, so a bidder tied for the top is on top of nothing (a null event); `top2` is the largest pairwise minimum, i.e. the second order statistic with multiplicity. $\theta_{\min}, \theta_{\max}$ are parameters of the market, not the extreme $\theta_j$, as on p. 18. Strategies are deterministic: a randomized deviation is a mixture of deterministic ones and cannot do better. The budget is a finite real number. $B^*_j$ is the integral of $\bar\Psi_j$ under the full product law with bidder $j$'s coordinate replaced by her own vector, which by independence is $\mathbb E[\bar\Psi_j \mid V_j]$; no conditional expectation is used, so σ* is a canonical function. The supremum in Definition 2 is written as "for every admissible deviation", so no real `sSup` appears. For $B \ge 0$ the feasible set of (2) contains $Y = 0$ and is compact, and a measurable selection of optimal solutions exists, so the allocation-rule condition is satisfiable.
-- source:
--   Ciocan & Iyer, SSRN 3240995, pp. 11–18: §2 (valuations p. 11, δ, budget costs and strategies p. 12, payments (1) and LP (2) p. 13, Ψ_j, π_j, π̃_j, U^b_{k,q} p. 14, Definitions 2–3 p. 17, θ_j, ϑ, E_{−j}, δ ≤ log(4/3)/θmax p. 18), §3.1 (3)–(4), p. 18

import Mathlib

namespace EndogBudgetAds.Equilibrium

open MeasureTheory ProbabilityTheory

/-- A sponsored-search market (Ciocan–Iyer, §2, p. 11; p. 18): `m` bidders `Fin m`, `n` items `Fin n`,
exponential rates `lam j` (λ_j), budget cost rates `r j` (r_j), the interval `[θmin, θmax]` containing
every `θ_j = λ_j (1 + r_j)`, and the ad network's outside value `δ`. -/
structure Market where
  m : ℕ
  n : ℕ
  lam : Fin m → ℝ
  r : Fin m → ℝ
  θmin : ℝ
  θmax : ℝ
  δ : ℝ

namespace Market

/-- `θ_j = λ_j (1 + r_j)` (p. 18). -/
def θ (M : Market) (j : Fin M.m) : ℝ := M.lam j * (1 + M.r j)

/-- The standing assumptions of the paper (p. 11, p. 12, p. 18): positive exponential rates, nonnegative
budget cost rates, every `θ_j` in a fixed interval `[θmin, θmax]` with `θmin > 0`, and an outside value
`0 < δ ≤ log(4/3)/θmax`. -/
structure Standing (M : Market) : Prop where
  lam_pos : ∀ j, 0 < M.lam j
  r_nonneg : ∀ j, 0 ≤ M.r j
  θmin_pos : 0 < M.θmin
  θmin_le_θmax : M.θmin ≤ M.θmax
  θ_mem : ∀ j, M.θmin ≤ M.θ j ∧ M.θ j ≤ M.θmax
  δ_pos : 0 < M.δ
  δ_le : M.δ ≤ Real.log (4 / 3) / M.θmax

end Market

/-- The heterogeneity degree `ϑ = θmax / θmin` (p. 18). -/
noncomputable def vt (M : Market) : ℝ := M.θmax / M.θmin

/-- The slack factor `β(m) = 2ϑ / m^{1/ϑ}` of (3), p. 18 (`Real.rpow`). -/
noncomputable def beta (M : Market) : ℝ := 2 * vt M / (M.m : ℝ) ^ (1 / vt M)

/-- A valuation profile `V`: `V j i` is bidder `j`'s valuation `V_ij` for item `i` (bidder-major, so
`V j` is bidder `j`'s private vector `V_j`). -/
abbrev Valuations (M : Market) := Fin M.m → Fin M.n → ℝ

/-- The law of the valuations (p. 11): all `V_ij` independent, `V_ij ∼ Exp(λ_j)`. -/
noncomputable def valLaw (M : Market) : Measure (Valuations M) :=
  Measure.pi fun j => Measure.pi fun _ : Fin M.n => expMeasure (M.lam j)

/-- The shaded valuations `W_ij = V_ij / (1 + r_j)` (the bids of σ*, (3), p. 18). -/
noncomputable def W (M : Market) (V : Valuations M) (j : Fin M.m) (i : Fin M.n) : ℝ :=
  V j i / (1 + M.r j)

/-! ### Order notation on one item (p. 14). A vector `x : Fin m → ℝ` is the bids of all bidders on
one item. -/

/-- Bidder `k` has the (strictly) highest value in `x`: `k` is the unique top bidder. -/
def IsTop {m : ℕ} (x : Fin m → ℝ) (k : Fin m) : Prop := ∀ l, l ≠ k → x l < x k

/-- Bidder `k` has the (strictly) second highest value in `x`. -/
def IsSecond {m : ℕ} (x : Fin m → ℝ) (k : Fin m) : Prop :=
  ∃ l, l ≠ k ∧ x k < x l ∧ ∀ l', l' ≠ l → l' ≠ k → x l' < x k

noncomputable instance {m : ℕ} (x : Fin m → ℝ) (k : Fin m) : Decidable (IsTop x k) := by
  unfold IsTop; infer_instance

noncomputable instance {m : ℕ} (x : Fin m → ℝ) (k : Fin m) : Decidable (IsSecond x k) := by
  unfold IsSecond; infer_instance

/-- The highest value `x^{(1)}` (`0` when there are no bidders). -/
noncomputable def top1 {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin m)).Nonempty then Finset.univ.sup' h x else 0

/-- The second highest value `x^{(2)}`, counted with multiplicity: the largest `min (x k) (x l)` over
pairs `k ≠ l` (`0` when `m < 2`). -/
noncomputable def top2 {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  if h : ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2)).Nonempty then
    ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2)).sup' h
      (fun p => min (x p.1) (x p.2))
  else 0

/-- The second highest value `x^{(2)}_{−j}` among the entries other than `x j` (`0` when fewer than two
such entries exist). -/
noncomputable def top2Excl {m : ℕ} (x : Fin m → ℝ) (j : Fin m) : ℝ :=
  if h : ((Finset.univ : Finset (Fin m × Fin m)).filter
      (fun p => p.1 ≠ p.2 ∧ p.1 ≠ j ∧ p.2 ≠ j)).Nonempty then
    ((Finset.univ : Finset (Fin m × Fin m)).filter
      (fun p => p.1 ≠ p.2 ∧ p.1 ≠ j ∧ p.2 ≠ j)).sup' h (fun p => min (x p.1) (x p.2))
  else 0

/-- The payment (1), p. 13: for bids `b` (`b k i` = bidder `k`'s bid on item `i`), `p^b(i, j)` is the
highest bid `b_ik` with `k ≠ j` and `b_ik ≤ b_ij` when `b_ij` is not the minimum bid on item `i`, and `0`
otherwise. "`b_ij ≠ min_k b_ik`" is `∃ k, b_ik < b_ij`. -/
noncomputable def pay {m n : ℕ} (b : Fin m → Fin n → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  if h : ∃ k, b k i < b j i then
    ((Finset.univ : Finset (Fin m)).filter (fun k => k ≠ j ∧ b k i ≤ b j i)).sup'
      ⟨h.choose, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun hk => by have := h.choose_spec; rw [hk] at this; exact lt_irrefl _ this,
          le_of_lt h.choose_spec⟩⟩
      (fun k => b k i)
  else 0

/-! ### The ad network's LP (2), p. 13. `Y i j` is the share of item `i` won by bidder `j`
(item-major, as printed). -/

/-- The objective of (2): revenue plus the outside value `δ` of unallocated shares. -/
noncomputable def objective (M : Market) (b : Fin M.m → Fin M.n → ℝ) (Y : Fin M.n → Fin M.m → ℝ) : ℝ :=
  ∑ i, ∑ j, pay b i j * Y i j + M.δ * ∑ i, (1 - ∑ j, Y i j)

/-- The feasible set of (2) for budgets `B` and bids `b`. -/
def AllocFeasible (M : Market) (B : Fin M.m → ℝ) (b : Fin M.m → Fin M.n → ℝ)
    (Y : Fin M.n → Fin M.m → ℝ) : Prop :=
  (∀ i j, 0 ≤ Y i j) ∧ (∀ j, ∑ i, pay b i j * Y i j ≤ B j) ∧ (∀ i, ∑ j, Y i j ≤ 1)

/-- `Y` is an optimal solution of (2). -/
def AllocOptimal (M : Market) (B : Fin M.m → ℝ) (b : Fin M.m → Fin M.n → ℝ)
    (Y : Fin M.n → Fin M.m → ℝ) : Prop :=
  AllocFeasible M B b Y ∧
    ∀ Y', AllocFeasible M B b Y' → objective M b Y' ≤ objective M b Y

/-- An allocation rule maps budgets `B` and bids `b` to an allocation `Y(B, b)`. -/
abbrev AllocRule (M : Market) :=
  (Fin M.m → ℝ) → (Fin M.m → Fin M.n → ℝ) → (Fin M.n → Fin M.m → ℝ)

/-- The ad network's rule: a measurable selection `Y(B, b) ∈ argmax (2)` for every nonnegative budget
vector `B` (for `B ≥ 0` the feasible set contains `Y = 0` and is compact, so (2) has an optimum). -/
def IsAllocRule (M : Market) (alloc : AllocRule M) : Prop :=
  Measurable (fun p : (Fin M.m → ℝ) × (Fin M.m → Fin M.n → ℝ) => alloc p.1 p.2) ∧
    ∀ (B : Fin M.m → ℝ) (b : Fin M.m → Fin M.n → ℝ), (∀ j, 0 ≤ B j) → AllocOptimal M B b (alloc B b)

/-! ### Strategies (p. 12). -/

/-- A (deterministic) strategy of a bidder: a budget `B_j(V_j)` and a bid vector `b_j(V_j)` for each
realization `V_j` of her own valuations. -/
structure Strategy (n : ℕ) where
  budget : (Fin n → ℝ) → ℝ
  bid : (Fin n → ℝ) → Fin n → ℝ

/-- An admissible strategy: measurable budget and bids, and a finite nonnegative budget. -/
def Strategy.Admissible {n : ℕ} (σ : Strategy n) : Prop :=
  Measurable σ.budget ∧ Measurable σ.bid ∧ ∀ v, 0 ≤ σ.budget v

/-- The bid vector `b` induced by a strategy profile `σ` at valuations `V`. -/
def bidsOf {M : Market} (σ : Fin M.m → Strategy M.n) (V : Valuations M) : Fin M.m → Fin M.n → ℝ :=
  fun k => (σ k).bid (V k)

/-- The budget vector `B` induced by a strategy profile `σ` at valuations `V`. -/
def budgetsOf {M : Market} (σ : Fin M.m → Strategy M.n) (V : Valuations M) : Fin M.m → ℝ :=
  fun k => (σ k).budget (V k)

/-- The profile `(σ_j, σ_{−j})`: bidder `j` switches to `σj`, everybody else keeps `σ`. -/
def deviate {M : Market} (σ : Fin M.m → Strategy M.n) (j : Fin M.m) (σj : Strategy M.n) :
    Fin M.m → Strategy M.n :=
  Function.update σ j σj

/-! ### The strategy profile σ* ((3)–(4), p. 18). -/

/-- `Ψ̄_j = Σ_i W_i^{(2)} 1{i ∈ U^W_{j,1}}` ((4), p. 18): the second highest shaded valuation on every
item on which `j` has the highest shaded valuation. -/
noncomputable def PsiBar (M : Market) (j : Fin M.m) (V : Valuations M) : ℝ :=
  ∑ i, if IsTop (fun l => W M V l i) j then top2 (fun l => W M V l i) else 0

/-- `B*_j = E_{−j}[Ψ̄_j] (1 + β(m))` ((3), p. 18) as a function of bidder `j`'s own valuation vector
`v`: the expectation of `Ψ̄_j` over the other bidders' valuations with `V_j = v` held fixed. -/
noncomputable def Bstar (M : Market) (j : Fin M.m) (v : Fin M.n → ℝ) : ℝ :=
  (∫ V, PsiBar M j (Function.update V j v) ∂ valLaw M) * (1 + beta M)

/-- The strategy profile σ* ((3), p. 18): bid `b*_j = W_j = V_j / (1 + r_j)`, budget `B*_j`. -/
noncomputable def sigmaStar (M : Market) : Fin M.m → Strategy M.n :=
  fun j => ⟨Bstar M j, fun v i => v i / (1 + M.r j)⟩

/-! ### Outcomes (p. 14), under the allocation `Y(B, b)` of the rule `alloc`. -/

/-- The realized spend `Ψ_j(σ) = Σ_i p^b(i, j) Y_ij(B, b)`. -/
noncomputable def spend (M : Market) (alloc : AllocRule M) (σ : Fin M.m → Strategy M.n)
    (j : Fin M.m) (V : Valuations M) : ℝ :=
  ∑ i, pay (bidsOf σ V) i j * alloc (budgetsOf σ V) (bidsOf σ V) i j

/-- The payoff `π_j(σ) = Σ_i (V_ij − p^b(i, j)) Y_ij(B, b) − r_j B_j`. -/
noncomputable def payoff (M : Market) (alloc : AllocRule M) (σ : Fin M.m → Strategy M.n)
    (j : Fin M.m) (V : Valuations M) : ℝ :=
  ∑ i, (V j i - pay (bidsOf σ V) i j) * alloc (budgetsOf σ V) (bidsOf σ V) i j
    - M.r j * budgetsOf σ V j

/-- The modified profit `π̃_j(σ) = π_j(σ) + r_j (B_j − Ψ_j(σ))`. -/
noncomputable def modProfit (M : Market) (alloc : AllocRule M) (σ : Fin M.m → Strategy M.n)
    (j : Fin M.m) (V : Valuations M) : ℝ :=
  payoff M alloc σ j V + M.r j * (budgetsOf σ V j - spend M alloc σ j V)

/-! ### Approximate best responses and equilibria (Definitions 2–3, p. 17). -/

/-- Definition 2: `σ_j` is an `ε`-approximate best response to `σ_{−j}` when no admissible deviation
`σ'_j` has expected payoff above `E[π_j(σ)] (1 + ε)` (the supremum condition, stated pointwise). -/
def IsEpsBestResponse (M : Market) (alloc : AllocRule M) (σ : Fin M.m → Strategy M.n)
    (j : Fin M.m) (ε : ℝ) : Prop :=
  ∀ σj : Strategy M.n, σj.Admissible →
    ∫ V, payoff M alloc (deviate σ j σj) j V ∂ valLaw M ≤
      (∫ V, payoff M alloc σ j V ∂ valLaw M) * (1 + ε)

/-- Definition 3: `σ` is an `ε`-equilibrium when each `σ_j` is an `ε`-approximate best response. -/
def IsEpsEquilibrium (M : Market) (alloc : AllocRule M) (σ : Fin M.m → Strategy M.n) (ε : ℝ) :
    Prop :=
  ∀ j, IsEpsBestResponse M alloc σ j ε

end EndogBudgetAds.Equilibrium


