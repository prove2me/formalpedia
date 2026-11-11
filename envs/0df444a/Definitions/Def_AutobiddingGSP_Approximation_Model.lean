-- Prove2me | Definitions.Def_AutobiddingGSP_Approximation_Model
-- name    : AutobiddingGSP_Approximation_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:26:42.889106+00:00
-- url     : https://prove2.me/theorems/e117338b-fe0a-4524-ae74-abdf3325bf61
-- title:
--   GSP sponsored-shopping auctions without self-pricing, and the γ-approximate autobidding equilibria ABE-B and ABE-R
-- statement:
--   An **auction** lists, for each bidder $i$, the values $v_{i,1},\dots,v_{i,m_i}$ of its items, the number $K$ of slots, the click-through rates $c_1,\dots,c_K$ and (budget model) the budgets $B_i$; all data are rational. The items are the pairs $(i,j)$; $M=\sum_i m_i$. Positions $k>K$ get click-through rate $0$.
--
--   An **allocation** $a$ is a bijection from the ranks to the items. Under the multiplier profile $\alpha$ the bid of item $(i,j)$ is $b_{ij}=\alpha_i v_{ij}$ (uniform bidding, Def. 2.1); $a$ is **valid** if $b_{a(1)}\ge\dots\ge b_{a(M)}$. The **GSP price without self-pricing** of the item at rank $k$ is
--   $\tau_{ij}(a,b)=\max\{b_{i'j'}:(i',j')=a(k'),\,k'>k,\,i'\ne i\}$ (the maximum of the empty set is $0$), its payment is $c_k\tau_{ij}$, $P_i(a,b)=\sum_j p_{ij}$, and $V_i(a)=\sum_{k\le K,\,a(k)=(i,j)}c_kv_{ij}$. For a randomized allocation $\pi$ (a probability distribution on all allocations), $P_i(\pi,b)$ and $V_i(\pi)$ are expectations.
--
--   **γ-approximate ABE-B** (Defs. 2.2–2.3): $\alpha\in[0,1]^n$, $\pi$ a distribution, (a) every allocation in the support of $\pi$ is valid, (b) $P_i(\pi,b)\le B_i$, (c') $P_i(\pi,b)<(1-\gamma)B_i\Rightarrow\alpha_i=1$.
--
--   **γ-approximate ABE-R** (Defs. 2.4–2.5) with the cap $A_0=1+\sum_{i,j}v_{ij}/\min_{i,j}v_{ij}$ (p. 8): $\alpha\in[1,A_0]^n$, (a) as above, (b) $P_i(\pi,b)\le V_i(\pi)$, (c') $P_i(\pi,b)<(1-\gamma)V_i(\pi)\Rightarrow\alpha_i=A_0$.
--
--   At $\gamma=0$ these are the exact equilibria. `Model` names the two constraint models.
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], §2, pp. 6–8 (PDF 6–8), Definitions 2.1–2.5

import Mathlib

namespace AutobiddingGSP.Approximation

open scoped BigOperators

/-- **A GSP sponsored-shopping position auction** (Hansen, Li and Nie, *Complexity of Autobidding
Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF
SHA256 40ce53fb…c73c8f], §2, p. 6 (PDF 6), and Definitions 2.2, 2.4, pp. 7–8).

`vals` lists, for every bidder `i` (0-based), the values `v_{i,1}, …, v_{i,m_i}` of its items in
the given order; `K` is the number of slots, `ctr = [c_1, …, c_K]` the click-through rates, and
`budgets = [B_1, …, B_n]` the budgets (used by the budget model only; the ROI model has none).

**Formalization Note** The data are rational, as in every computational statement of the paper.
The standing assumptions of §2 (`m_i ≥ 1`, `v_{i,1} ≥ ⋯ ≥ v_{i,m_i} > 0`, `1 ≥ c_1 ≥ ⋯ ≥ c_K > 0`,
`1 ≤ K ≤ M`, `B_i > 0`) are the separate predicates `Auction.WellFormed` and `Auction.ValidFor`. -/
structure Auction where
  vals : List (List ℚ)
  K : ℕ
  ctr : List ℚ
  budgets : List ℚ

namespace Auction

variable (A : Auction)

/-- The number `n` of bidders. -/
abbrev n : ℕ := A.vals.length

/-- The items: pairs `(i, j)` of a bidder `i` and the index `j` of one of its items (0-based). -/
abbrev Item : Type := (i : Fin A.n) × Fin (A.vals.get i).length

/-- The value `v_{ij}` of an item. -/
def val (x : A.Item) : ℚ := (A.vals.get x.1).get x.2

/-- The total number `M = ∑_i m_i` of items. -/
abbrev numItems : ℕ := Fintype.card A.Item

/-- An allocation `a ∈ Ω` (§2.1, p. 6): a bijection from the ranks `0, …, M − 1` to the items;
`a k` is the item at rank `k`. (The paper's rank `k` is the Lean rank `k − 1`.) -/
abbrev Alloc : Type := Fin A.numItems ≃ A.Item

/-- The click-through rate of the (0-based) rank `k`: `c_{k+1}` when `k < K`, and `0` for the
positions `K < p ≤ M`, which are ranked but receive no clicks (§2, p. 6). -/
def ctrAt (k : ℕ) : ℚ := if k < A.K then A.ctr.getD k 0 else 0

/-- The bid `b_{ij} = α_i v_{ij}` of an item under the uniform bidding strategy (Definition 2.1,
p. 7) with multiplier profile `α`. -/
def bid (α : Fin A.n → ℝ) (x : A.Item) : ℝ := α x.1 * (A.val x : ℝ)

/-- `a` is **valid** under the bids induced by `α` (§2.1, p. 6): `b_{a(1)} ≥ b_{a(2)} ≥ ⋯ ≥ b_{a(M)}`. -/
def IsValidAlloc (α : Fin A.n → ℝ) (a : A.Alloc) : Prop :=
  ∀ k k' : Fin A.numItems, k ≤ k' → A.bid α (a k') ≤ A.bid α (a k)

/-- The **GSP per-click price without self-pricing** (§2.1, p. 6):
`τ_{ij}(a, b) = max {b_{i'j'} : (i', j') = a(k'), k' > k, i' ≠ i}`, where `k` is the rank of
`(i, j)` in `a`, with the maximum of the empty set equal to `0`. Every later item of the same
bidder is excluded, not only the adjacent one.

**Formalization Note** The maximum is taken over the set together with `0`; as all bids in the
paper are nonnegative (`α_i ≥ 0`, `v_{ij} > 0`) this is the paper's convention. -/
noncomputable def price (α : Fin A.n → ℝ) (a : A.Alloc) (x : A.Item) : ℝ :=
  (insert (0 : ℝ) ((Finset.univ.filter (fun k' : Fin A.numItems => a.symm x < k' ∧ (a k').1 ≠ x.1)).image
    (fun k' => A.bid α (a k')))).max' (Finset.insert_nonempty _ _)

/-- The total GSP payment `P_i(a, b) = ∑_j p_{ij}(a, b)` of bidder `i`, where
`p_{ij}(a, b) = c_k τ_{ij}(a, b)` for the rank `k` of `(i, j)` (§2.1, p. 6). -/
noncomputable def payment (α : Fin A.n → ℝ) (a : A.Alloc) (i : Fin A.n) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : A.Item => x.1 = i), (A.ctrAt (a.symm x) : ℝ) * A.price α a x

/-- The value `V_i(a) = ∑_{k ∈ [K] : a(k) = (i, j)} c_k v_{ij}` of bidder `i` (§2.1, p. 6). -/
def value (a : A.Alloc) (i : Fin A.n) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : A.Item => x.1 = i), (A.ctrAt (a.symm x) : ℝ) * (A.val x : ℝ)

/-- `π` is a **randomized allocation**: a probability distribution over all allocations `Ω`
(§2.1, p. 7). -/
def IsDist (π : A.Alloc → ℝ) : Prop := (∀ a, 0 ≤ π a) ∧ ∑ a, π a = 1

/-- The expected payment `P_i(π, b) = E_{a∼π}[P_i(a, b)]` (§2.1, p. 7). -/
noncomputable def expPayment (α : Fin A.n → ℝ) (π : A.Alloc → ℝ) (i : Fin A.n) : ℝ :=
  ∑ a, π a * A.payment α a i

/-- The expected value `V_i(π) = E_{a∼π}[V_i(a)]` (§2.1, p. 7). -/
def expValue (π : A.Alloc → ℝ) (i : Fin A.n) : ℝ :=
  ∑ a, π a * A.value a i

/-- The budget `B_i` of bidder `i` (budget model). -/
def budget (i : Fin A.n) : ℝ := (A.budgets.getD i.val 0 : ℚ)

/-- The **multiplier cap** `A₀ = 1 + (∑_{i,j} v_{ij}) / (min_{i,j} v_{ij})` (§2.2, p. 8), computed
from all item values of the instance. -/
def capA0 : ℚ :=
  1 + A.vals.flatten.sum / A.vals.flatten.foldr min (A.vals.flatten.headD 1)

/-- **γ-approximate autobidding equilibrium under budget constraints** (Definitions 2.2 and 2.3,
pp. 7–8): `α ∈ [0, 1]ⁿ`, `π` a distribution over all allocations, and

* (a) every allocation in the support of `π` is valid under the induced bids;
* (b) `P_i(π, b) ≤ B_i` for every bidder;
* (c') `P_i(π, b) < (1 − γ) B_i ⟹ α_i = 1` for every bidder.

At `γ = 0` this is the exact equilibrium of Definition 2.2. -/
def IsApproxABEB (γ : ℝ) (α : Fin A.n → ℝ) (π : A.Alloc → ℝ) : Prop :=
  (∀ i, 0 ≤ α i ∧ α i ≤ 1) ∧ A.IsDist π ∧ (∀ a, 0 < π a → A.IsValidAlloc α a) ∧
    (∀ i, A.expPayment α π i ≤ A.budget i) ∧
    ∀ i, A.expPayment α π i < (1 - γ) * A.budget i → α i = 1

/-- **γ-approximate autobidding equilibrium under ROI constraints** (Definitions 2.4 and 2.5,
p. 8), with the cap `A = A₀` of p. 8: `α ∈ [1, A₀]ⁿ`, `π` a distribution over all allocations, and

* (a) every allocation in the support of `π` is valid under the induced bids;
* (b) `V_i(π) ≥ P_i(π, b)` for every bidder;
* (c') `(1 − γ) V_i(π) > P_i(π, b) ⟹ α_i = A₀` for every bidder.

At `γ = 0` this is the exact equilibrium of Definition 2.4. -/
def IsApproxABER (γ : ℝ) (α : Fin A.n → ℝ) (π : A.Alloc → ℝ) : Prop :=
  (∀ i, 1 ≤ α i ∧ α i ≤ (A.capA0 : ℝ)) ∧ A.IsDist π ∧ (∀ a, 0 < π a → A.IsValidAlloc α a) ∧
    (∀ i, A.expPayment α π i ≤ A.expValue π i) ∧
    ∀ i, A.expPayment α π i < (1 - γ) * A.expValue π i → α i = (A.capA0 : ℝ)

end Auction

/-- The two constraint models of the paper: budget constraints (ABE-B) and ROI constraints
(ABE-R). -/
inductive Model where
  | budget
  | roi
  deriving DecidableEq

/-- The γ-approximate autobidding equilibrium of the given constraint model (Definitions 2.3 and
2.5, pp. 7–8). -/
def Auction.IsApproxABE (A : Auction) : Model → ℝ → (Fin A.n → ℝ) → (A.Alloc → ℝ) → Prop
  | Model.budget, γ, α, π => A.IsApproxABEB γ α π
  | Model.roi, γ, α, π => A.IsApproxABER γ α π

end AutobiddingGSP.Approximation


