-- Prove2me | Definitions.Def_BudgetCournot_Equilibrium_Model
-- name    : BudgetCournot_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:12.696112+00:00
-- url     : https://prove2.me/theorems/b4177173-047c-4e66-8220-9bf2e92afe09
-- title:
--   §2, §3, Definitions 2.1, 3.1, 3.2, (2), (4)–(7), (B-4), (B-12), (B-13) — budget-constrained multimarket Cournot game, augmented and cutoff budgets, H, closed form
-- statement:
--   There are $N$ firms and $M$ markets. Firm $i$ has a budget $B_i$ and chooses an allocation $(x_{ij})_{j}$ with $x_{ij}\ge 0$ and $\sum_{j=1}^M x_{ij}\le B_i$. Market $j$ has linear inverse demand $r_j(X)=R_j-X/\beta_j$ in the total allocation $X_j=\sum_{i=1}^N x_{ij}$, and firm $i$ earns
--
--   $$\pi_i(x)=\sum_{j=1}^M\Big(R_j-\frac{X_j}{\beta_j}\Big)x_{ij}.$$
--
--   The **standing assumptions** are $0\le R_1\le\cdots\le R_M$, $\beta_j>0$ for every $j$, and $B_1\ge B_2\ge\cdots\ge B_N>0$. A **Cournot equilibrium** (Definition 2.1) is a profile of feasible allocations such that no firm can raise its profit by switching to another feasible allocation while the other firms keep theirs.
--
--   The file also defines:
--
--   1. the **augmented budget** $\mathcal B_i=i\,B_i+\sum_{k=i}^N B_k$ of firm $i$, equation (4);
--   2. the **cutoff budget** $\mathbb B_j=\sum_{k=j}^M\beta_k(R_k-R_j)$ of market $j$, equation (5);
--   3. the function $H(x)=\inf\{z\ge 0:\sum_{j=1}^M\beta_j(R_j-z)^+\le x\}$ of Definition 3.2;
--   4. the threshold index $n^*_j=\max\{i\in[N]:\mathcal B_i>\mathbb B_j\}$ of equation (7), equal to $0$ when no firm qualifies;
--   5. the closed form (6),
--   $$x^*_{ij}=\beta_j\Big[\frac{R_j}{1+n^*_j}-\frac{H(\mathcal B_i)}{i+1}+\sum_{k=1}^{n^*_j}\frac{H(\mathcal B_k)}{k(k+1)}-\sum_{k=1}^{i}\frac{H(\mathcal B_k)}{k(k+1)}\Big]^+;$$
--   6. for levels $\alpha_1,\dots,\alpha_N$, the counts $n_j=\max\{i\in\{0\}\cup[N]:\alpha_i\le R_j\}$ of (B-13) and the allocations of (B-12), which are (6) with $H(\mathcal B_k)$ replaced by $\alpha_k$ and $n^*_j$ by $n_j$;
--   7. the number of firms with a positive allocation in market $j$;
--   8. the best-response condition (B-4) with multiplier $\lambda\ge 0$: $x_{ij}=(\beta_jR_j-\beta_j\lambda-X_{ij-})^+/2$ for every $j$, where $X_{ij-}=X_j-x_{ij}$ is the others' total, together with $\sum_j x_{ij}\le B_i$ and complementary slackness ($\lambda=0$ or $\sum_j x_{ij}=B_i$).
--
--   These are the objects of Theorem 1 and of its proof in Appendix B.
--
--   **Formalization Note** Firms are `Fin N` and markets `Fin M`; the paper's firm $i$ is the Lean index $i.\mathrm{val}+1$, so $i+1$ in (6) is `i + 2` and $k(k+1)$ is `(k+1)(k+2)`. Profiles are firm-first, `x i j`. The price $R_j-X_j/\beta_j$ is not truncated at zero. The equilibrium uses the published `CarbonDoubleCount.Planner.IsPureNash`, which compares against every feasible unilateral deviation; the fixed-point condition (3) of Definition 2.1 is the statement that the other firms' totals are computed from their actual allocations. $H$ is a real `sInf`; the set is nonempty and bounded below for $x\ge 0$, and $H$ is only used at such points. The empty maximum in (7) and (B-13) is $0$ (`Finset.sup` with bottom $0$). The orderings that §2 adopts "without loss of generality" are hypotheses (`Standing`), since (5) and (6) depend on them. At the allowed boundary $R_j=0$, $n^*_j$ can be positive although every firm's allocation to that market is zero; the displayed formula remains valid.
-- source:
--   Caldentey & Haugh, Multimarket Cournot equilibria with heterogeneous resource-constrained firms, Operations Research (2024), author version of January 20, 2024, pp. 4, 7–8, 18–19, §2 (1), (2), Definition 2.1, Definitions 3.1 (4), (5), Definition 3.2, Theorem 1 (6), (7), Appendix B (B-4), (B-12), (B-13)

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace BudgetCournot.Equilibrium

open Finset

/-- Standing assumptions of §2, p. 4: markets ranked `0 ≤ R₁ ≤ ⋯ ≤ R_M`, slopes `β_j > 0`,
budgets ranked as in (1), `B₁ ≥ ⋯ ≥ B_N > 0`. Firm `i : Fin N` is the paper's firm `i.val + 1`. -/
def Standing {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) : Prop :=
  Monotone R ∧ (∀ j, 0 ≤ R j) ∧ (∀ j, 0 < β j) ∧ Antitone B ∧ ∀ i, 0 < B i

/-- Total budget allocated to market `j`, `X_j = ∑_i x_ij`. -/
def total {N M : ℕ} (x : Fin N → Fin M → ℝ) (j : Fin M) : ℝ :=
  ∑ i, x i j

/-- Firm `i`'s net profit `∑_j r_j(X_j) x_ij` with `r_j(X) = R_j - X/β_j`, the objective of (2)
(the price is not truncated at zero). -/
noncomputable def payoff {N M : ℕ} (R β : Fin M → ℝ) (i : Fin N) (x : Fin N → Fin M → ℝ) : ℝ :=
  ∑ j, (R j - total x j / β j) * x i j

/-- Firm `i`'s feasible allocations in (2): `y_j ≥ 0` and `∑_j y_j ≤ B_i`. -/
def feasible {N M : ℕ} (B : Fin N → ℝ) (i : Fin N) : Set (Fin M → ℝ) :=
  {y | (∀ j, 0 ≤ y j) ∧ ∑ j, y j ≤ B i}

/-- Definition 2.1: a Cournot equilibrium is a profile of feasible allocations from which no firm
gains by a feasible unilateral deviation, the others' allocations held fixed. -/
def IsCournotEq {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (x : Fin N → Fin M → ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (strategy := fun _ : Fin N => Fin M → ℝ)
    (feasible B) (payoff R β) x

/-- Augmented budget (4): `𝓑_i = i B_i + ∑_{k=i}^N B_k` with the paper's 1-based index `i`. -/
def augBudget {N : ℕ} (B : Fin N → ℝ) (i : Fin N) : ℝ :=
  ((i : ℕ) + 1 : ℝ) * B i + ∑ k ∈ univ.filter (fun k => i ≤ k), B k

/-- Cutoff budget (5): `𝔹_j = ∑_{k=j}^M β_k (R_k - R_j)`. -/
def cutoffBudget {M : ℕ} (R β : Fin M → ℝ) (j : Fin M) : ℝ :=
  ∑ k ∈ univ.filter (fun k => j ≤ k), β k * (R k - R j)

/-- Definition 3.2: `H(x) = inf {z ≥ 0 : ∑_j β_j (R_j - z)⁺ ≤ x}`, used for `x ≥ 0`. -/
noncomputable def H {M : ℕ} (R β : Fin M → ℝ) (x : ℝ) : ℝ :=
  sInf {z : ℝ | 0 ≤ z ∧ ∑ j, β j * max (R j - z) 0 ≤ x}

/-- (7): the threshold index `n*_j = max {i ∈ [N] : 𝓑_i > 𝔹_j}`, with the maximum
of the empty set read as `0`. At `R_j = 0` it need not equal the number of positive allocations. -/
noncomputable def nStar {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (j : Fin M) : ℕ :=
  (univ.filter fun i : Fin N => cutoffBudget R β j < augBudget B i).sup fun i => (i : ℕ) + 1

/-- The bracketed expression of (6) and (B-12), for levels `a_k` and market counts `n_j`:
`β_j [R_j/(1+n_j) - a_i/(i+1) + ∑_{k=1}^{n_j} a_k/(k(k+1)) - ∑_{k=1}^{i} a_k/(k(k+1))]⁺`,
written with 0-based `Fin` indices (paper index `k = k.val + 1`). -/
noncomputable def closedForm {N M : ℕ} (R β : Fin M → ℝ) (a : Fin N → ℝ) (n : Fin M → ℕ)
    (i : Fin N) (j : Fin M) : ℝ :=
  β j * max 0 (R j / (1 + (n j : ℝ)) - a i / ((i : ℕ) + 2 : ℝ)
    + ∑ k ∈ univ.filter (fun k : Fin N => (k : ℕ) < n j),
        a k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ))
    - ∑ k ∈ univ.filter (fun k : Fin N => k ≤ i),
        a k / (((k : ℕ) + 1 : ℝ) * ((k : ℕ) + 2 : ℝ)))

/-- The closed form (6) of Theorem 1: `x*_ij` with levels `H(𝓑_k)` and counts `n*_j`. -/
noncomputable def xStar {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) : Fin N → Fin M → ℝ :=
  closedForm R β (fun k => H R β (augBudget B k)) (nStar R β B)

/-- (B-13): `n_j = max {i ∈ {0} ∪ [N] : α_i ≤ R_j}` (with `α_0 := 0`, so the empty case is `0`). -/
noncomputable def nAlpha {N M : ℕ} (R : Fin M → ℝ) (α : Fin N → ℝ) (j : Fin M) : ℕ :=
  (univ.filter fun i : Fin N => α i ≤ R j).sup fun i => (i : ℕ) + 1

/-- The allocations of the last line of (B-12), built from levels `α` and `n_j` of (B-13). -/
noncomputable def xAlpha {N M : ℕ} (R β : Fin M → ℝ) (α : Fin N → ℝ) : Fin N → Fin M → ℝ :=
  closedForm R β α (nAlpha R α)

/-- Number of firms with a positive allocation in market `j` (the `n_j` of (B-5)–(B-7)). -/
noncomputable def nActive {N M : ℕ} (x : Fin N → Fin M → ℝ) (j : Fin M) : ℕ :=
  (univ.filter fun i : Fin N => 0 < x i j).card

/-- (B-4) with its multiplier: firm `i`'s allocation in `x` is the water-filling response
`x_ij = (β_j R_j - β_j λ - X_{ij-})⁺ / 2` to the others' totals `X_{ij-} = X_j - x_ij`, with
`λ ≥ 0`, the budget constraint, and complementary slackness (`λ = 0` or the budget binds). -/
def IsBR {N M : ℕ} (R β : Fin M → ℝ) (B : Fin N → ℝ) (i : Fin N) (x : Fin N → Fin M → ℝ)
    (lam : ℝ) : Prop :=
  0 ≤ lam ∧
    (∀ j, x i j = max 0 (β j * R j - β j * lam - (total x j - x i j)) / 2) ∧
    ∑ j, x i j ≤ B i ∧ (lam = 0 ∨ ∑ j, x i j = B i)

end BudgetCournot.Equilibrium


