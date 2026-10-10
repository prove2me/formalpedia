-- Prove2me | Definitions.Def_MultiPriceOnline_Balance_Algorithm
-- name    : MultiPriceOnline_Balance_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:13.758424+00:00
-- url     : https://prove2.me/theorems/c1e440a8-c892-4074-9bed-a1330655a2ba
-- title:
--   Algorithm 1, p. 19, and App. B.3, pp. 44–45 — Multi-price Balance, its expected revenue, and the per-item modes of Theorem 1
-- statement:
--   This module defines Algorithm 1 of Ma and Simchi-Levi, **Multi-price Balance**, and its expected revenue. It also defines the per-item modes used to prove Theorem 1.
--
--   **Algorithm 1.** Each item $i$ (inventory $k_i$, prices $r_i^{(1)}<\dots<r_i^{(m_i)}$) draws a configuration $\tilde L_i^{(0)},\dots,\tilde L_i^{(m_i)}$ and value function $\tilde\Phi_i$ from its randomized procedure, independently across items (Line 1). $N_i$ counts the units of item $i$ sold, starting at $0$. When customer $t$ arrives, the algorithm computes
--   $$
--   \max_{i,\ j\in[m_i]}\ p^{(j)}_{t,i}\Big(\tilde\Phi_i\big(\tilde L_i^{(j)}\big)-\tilde\Phi_i\big(N_i/k_i\big)\Big).\tag{16}
--   $$
--   If this value is strictly positive, it offers an item $i^*_t$ at a price $j^*_t$ attaining the maximum. The customer accepts with probability $p^{(j^*_t)}_{t,i^*_t}$; a sale earns $r_{i^*_t}^{(j^*_t)}$ and increments $N_{i^*_t}$. The decision at customer $t$ uses only the initialization, the counts $N$ and the present customer's probabilities. Ties are broken by a **tie-breaking rule**: a function that, given the customer's index, the counts and the scores of all candidate offers, returns an offer of maximal score.
--
--   **Expected revenue.** $\mathbb E[\mathrm{ALG}]$ averages over the configurations of Line 1, weighted by the product of the items' probabilities, and over the customers' independent accept/reject decisions. Given an initialization, it is computed customer by customer: the expected revenue from customer $t$ on is $p\,(r+V_{t+1}(N+e_{i^*}))+(1-p)\,V_{t+1}(N)$ if an offer is made, and $V_{t+1}(N)$ otherwise.
--
--   **Modes** (App. B.3). Each item is in mode *perturb* or *split*. A perturbed item keeps inventory $k_i$ and uses the procedure of Definition 3. A split item is replaced by $k_i$ items with inventory $1$; each copy has item $i$'s prices and purchase probabilities and uses the procedure (45). *Multi-price Balance with modes* is Algorithm 1 run on this derived setup. The guaranteed ratio of an item is
--   $$
--   b_i=\begin{cases}G(\mathcal P_i)/2&\text{split},\\[2pt]\dfrac{1-1/e}{(1+k_i)(1-e^{-1/k_i})}&\text{perturb},\ m_i=1,\\[8pt]\dfrac{F(\mathcal P_i)}{(1+k_i)(e^{1/k_i}-1)}&\text{perturb},\ m_i\ge2.\end{cases}
--   $$
--
--   **Formalization Note** Items form an arbitrary finite type; customers are indexed $0,\dots,T-1$; a candidate offer is a pair $(i,j)$ with $j\in[1,m_i]$, so price $0$ is never a candidate. In (16) the count is read as $\min(N_i,k_i)$. This is the paper's $N_i$, since the algorithm never offers a stocked-out item (p. 18), but it keeps the function total. The tie-breaking rule may depend on the customer's index, the counts and the scores; theorems quantify over every such rule that returns a maximizer. The expectation is a finite sum over configurations and a backward recursion over customers. It is never an integral against an unconstrained measure.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 11 (online algorithms, ALG), p. 18, p. 19 (Algorithm 1, (16)), p. 16 (Theorem 1, bounds (i)–(iii)), pp. 44–45 (App. B.3)

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_Procedure

namespace MultiPriceOnline.Balance

/-! Algorithm 1, Multi-price Balance (Ma–Simchi-Levi, arXiv:1905.04770v1, p. 19), its expected
revenue, and the per-item modes used for Theorem 1 (p. 16; App. B.3, pp. 44–45).

Items form a finite type `ι`; item `i` has inventory `k i`, prices `r i 1, …, r i (m i)` and a
randomized procedure `P i` (Line 1). Customers are `Fin T` (customer `t` of the paper is index
`t − 1`); `p t i j` is the probability that customer `t` buys item `i` at price `j`. -/

section Algorithm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The candidate offers of (16): pairs `(i, j)` with `j ∈ [mᵢ]`; the pair `⟨i, j'⟩` stands for
item `i` at price `j = j' + 1`. -/
abbrev Cand (m : ι → ℕ) := Σ i : ι, Fin (m i)

/-- The score (16) of offer `a = (i, j)` to the present customer, whose purchase probabilities are
`pt i j`, when `N i` units of item `i` have been sold and item `i` was initialized with
configuration `cfg i`: `p⁽ʲ⁾_{t,i} (Φ̃ᵢ(L̃ᵢ⁽ʲ⁾) − Φ̃ᵢ(Nᵢ/kᵢ))`. The count is read as `min (N i) (k i)`
(the algorithm never sells more than `kᵢ` units, p. 18, so this is the paper's `Nᵢ`). -/
noncomputable def score (k m : ι → ℕ) (P : ∀ i, Procedure (k i) (m i))
    (cfg : ∀ i, Config (k i) (m i)) (pt : ι → ℕ → ℝ) (N : ι → ℕ) (a : Cand m) : ℝ :=
  pt a.1 (a.2.val + 1) *
    ((P a.1).Φ (cfg a.1) (cv (cfg a.1) (a.2.val + 1)) - (P a.1).Φ (cfg a.1) (min (N a.1) (k a.1)))

/-- A tie-breaking rule for Line 6: given the index `t` of the present customer, the sales counts
`N` and the scores of all candidate offers, it returns an offer. -/
abbrev Selector (m : ι → ℕ) := ℕ → (ι → ℕ) → (Cand m → ℝ) → Cand m

/-- `sel` always returns an offer maximizing the scores (16) ("offer any item `i*ₜ` and price `j*ₜ`
maximizing (16)", Line 6). -/
def IsArgmaxSelector {m : ι → ℕ} (sel : Selector m) : Prop :=
  ∀ t N (s : Cand m → ℝ) (a : Cand m), s a ≤ s (sel t N s)

/-- Expected revenue of Algorithm 1 from customer index `t` on, given the initialization `cfg`
and the sales counts `N`, with `s` customers left to process (the expectation over the customers'
independent accept/reject decisions). At customer `t` the algorithm reads only `p t` (the present
customer) and `N`: it computes the scores (16), lets `a = (i*, j*)` be the selector's maximizer, and
if the score of `a` is strictly positive offers `a`; the customer accepts with probability
`p⁽ʲ*⁾_{t,i*}`, earning `r_{i*}^{(j*)}` and incrementing `N_{i*}`. -/
noncomputable def runValue (k m : ι → ℕ) (r : ι → ℕ → ℝ) (P : ∀ i, Procedure (k i) (m i))
    (cfg : ∀ i, Config (k i) (m i)) (sel : Selector m) {T : ℕ} (p : Fin T → ι → ℕ → ℝ) :
    ℕ → ℕ → (ι → ℕ) → ℝ
  | 0, _, _ => 0
  | s + 1, t, N =>
    if h : t < T then
      if 0 < score k m P cfg (p ⟨t, h⟩) N (sel t N (score k m P cfg (p ⟨t, h⟩) N)) then
        p ⟨t, h⟩ (sel t N (score k m P cfg (p ⟨t, h⟩) N)).1
            ((sel t N (score k m P cfg (p ⟨t, h⟩) N)).2.val + 1) *
          (r (sel t N (score k m P cfg (p ⟨t, h⟩) N)).1
              ((sel t N (score k m P cfg (p ⟨t, h⟩) N)).2.val + 1) +
            runValue k m r P cfg sel p s (t + 1)
              (Function.update N (sel t N (score k m P cfg (p ⟨t, h⟩) N)).1
                (N (sel t N (score k m P cfg (p ⟨t, h⟩) N)).1 + 1))) +
        (1 - p ⟨t, h⟩ (sel t N (score k m P cfg (p ⟨t, h⟩) N)).1
            ((sel t N (score k m P cfg (p ⟨t, h⟩) N)).2.val + 1)) *
          runValue k m r P cfg sel p s (t + 1) N
      else runValue k m r P cfg sel p s (t + 1) N
    else 0

/-- `𝔼[ALG(𝒮, 𝒜)]` for Algorithm 1 with procedures `P` and tie-breaking rule `sel`: Line 1 draws
the configurations of the items independently (`cfg i` with probability `ρᵢ(cfg i)`), then the
customers `0, …, T − 1` are processed from `N = 0`. -/
noncomputable def expRevenue (k m : ι → ℕ) (r : ι → ℕ → ℝ) (P : ∀ i, Procedure (k i) (m i))
    (sel : Selector m) {T : ℕ} (p : Fin T → ι → ℕ → ℝ) : ℝ :=
  ∑ cfg : (∀ i, Config (k i) (m i)),
    (∏ i, (P i).ρ (cfg i)) * runValue k m r P cfg sel p T 0 (fun _ => 0)

end Algorithm

section Modes

/-! Theorem 1 (App. B.3): each item `i` is run either in mode `perturb` (`split i = false`), keeping
inventory `kᵢ` and the procedure of Definition 3, or in mode `split` (`split i = true`), where its
`kᵢ` units become `kᵢ` separate items with inventory `1`, the same prices and the same purchase
probabilities, each using the procedure (45). -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Number of items that item `i` becomes in the derived setup: `kᵢ` if split, else `1`. -/
def copies (k : ι → ℕ) (split : ι → Bool) (i : ι) : ℕ := cond (split i) (k i) 1

/-- Items of the derived setup: pairs `(i, u)` with `u` a copy of item `i`. -/
abbrev SplitItem (k : ι → ℕ) (split : ι → Bool) := Σ i : ι, Fin (copies k split i)

/-- Inventory of a derived item: `1` for a copy of a split item, `kᵢ` otherwise. -/
abbrev splitK (k : ι → ℕ) (split : ι → Bool) (x : SplitItem k split) : ℕ :=
  cond (split x.1) 1 (k x.1)

/-- The procedure of an item in a mode: (45) if split (inventory `1`), Definition 3 with its own
`k` and `α` otherwise. -/
noncomputable def modeProc (k m : ℕ) (r α σ : ℕ → ℝ) : (b : Bool) → Procedure (cond b 1 k) m
  | true => proc45 m r σ
  | false => def3Proc k m r α

/-- Multi-price Balance with modes `split`: `𝔼[ALG]` of Algorithm 1 run on the derived setup, every
derived item `(i, u)` having the prices and purchase probabilities of item `i` and the procedure of
its mode. -/
noncomputable def balanceRevenue (k m : ι → ℕ) (r α σ : ι → ℕ → ℝ) (split : ι → Bool)
    (sel : Selector (fun x : SplitItem k split => m x.1)) {T : ℕ} (p : Fin T → ι → ℕ → ℝ) : ℝ :=
  expRevenue (splitK k split) (fun x => m x.1) (fun x => r x.1)
    (fun x => modeProc (k x.1) (m x.1) (r x.1) (α x.1) (σ x.1) (split x.1)) sel
    (fun t x j => p t x.1 j)

/-- The ratio guaranteed for an item with inventory `k`, `m` prices, booking limits `α` and values
`σ` in a mode (Theorem 1, p. 16): `G(𝒫)/2` (bound (ii)) if split; otherwise
`(1 − 1/e)/((1+k)(1 − e^{−1/k}))` (bound (iii)) if `m = 1`, and `F(𝒫)/((1+k)(e^{1/k} − 1))`
(bound (i)) if `m ≥ 2`. -/
noncomputable def modeBound (k m : ℕ) (α σ : ℕ → ℝ) (b : Bool) : ℝ :=
  cond b (Gval σ / 2)
    (if m = 1 then (1 - 1 / Real.exp 1) / ((1 + k) * (1 - Real.exp (-1 / k)))
      else Fval α / ((1 + k) * (Real.exp (1 / k) - 1)))

end Modes

end MultiPriceOnline.Balance


